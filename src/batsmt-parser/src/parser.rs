
use {
    std::{error, result, fmt::{self,Display}, io, ops::Deref},
    fxhash::{FxHashMap,FxHashSet},
    types::*,
};

/// Error messages
#[derive(Debug)]
pub struct Error(String);

impl fmt::Display for Error {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        Display::fmt(&self.0, fmt)
    }
}

impl error::Error for Error {
  fn description(&self) -> &str { &self.0 }
  fn cause(&self) -> Option<&error::Error> { None }
}

pub type Result<T> = result::Result<T, Box<error::Error>>;

fn mk_err(s: String) -> Box<error::Error> {
    Box::new(Error(s))
}

// parser's buffer size
const BUF_SIZE : usize = 1_024 * 16;

// A basic SMT-LIB parser
struct ParserState<'a, R : io::Read, B : TermBuilder> {
    r: R, // underlying reader
    eof: bool,
    buf: [u8; BUF_SIZE], // internal buffer
    i: usize, // offset in buf
    len: usize, // current size of buf
    line: u32,
    col: u32,
    build: &'a mut B,
    sorts: FxHashMap<String, B::Sort>,
    funs: FxHashMap<String, B::Fun>,
    vars: FxHashSet<String>, // set of bound variables
}

impl<'a, R : io::Read, B : TermBuilder> ParserState<'a, R, B> {
    // allocate new parser
    fn new(build: &'a mut B, r: R) -> Self {
        ParserState {
            r, build, eof: false, buf: [0; BUF_SIZE], len: 0,
            i: 0, line: 1, col: 1,
            vars: FxHashSet::default(),
            funs: FxHashMap::default(),
            sorts: FxHashMap::default(),
        }
    }

    // refill internal buffer
    fn refill(&mut self) -> Result<()> {
        debug!("refill internal buffer (size {})", BUF_SIZE);
        debug_assert!(self.i >= self.len);
        self.i = 0;
        self.len = self.r.read(&mut self.buf)?;
        if self.len == 0 {
            self.eof = true;
        }
        Ok(())
    }

    fn err_with<T>(&self, s: impl Deref<Target=str>) -> Result<T> {
        let s: &str = &*s;
        Err(mk_err(format!("{} (line {}, col {})", s, self.line, self.col)))
    }

    fn err_eof<T>(&self) -> Result<T> {
        self.err_with("unexpected end-of-file")
    }

    // get current char, or EOF
    fn try_get(&mut self) -> Result<Option<u8>> {
        if self.eof {
            Ok(None)
        } else if self.i < self.len {
            let c = self.buf[self.i];
            Ok(Some(c))
        } else {
            self.refill()?;
            debug_assert_eq!(self.i, 0);
            Ok(if self.eof { None } else { Some(self.buf[0]) })
        }
    }

    // get current char, or fail
    fn get(&mut self) -> Result<u8> {
        if self.eof {
            self.err_eof()
        } else if self.i < self.len {
            let c = self.buf[self.i];
            Ok(c)
        } else {
            self.refill()?;
            debug_assert_eq!(self.i, 0);
            if self.eof { self.err_eof() } else { Ok(self.buf[0]) }
        }
    }

    // discard current char (must be valid!)
    fn junk(&mut self) {
        // update pos
        if self.buf[self.i] == b'\n' {
            self.line += 1;
            self.col = 0;
        } else {
            self.col += 1;
        }
        //debug!("junk {:?}", self.buf[self.i] as char);

        self.i += 1;
    }

    // skip chars until EOL is reached
    fn skip_to_eol(&mut self) -> Result<()> {
        while let Some(c) = self.try_get()? {
            if c == b'\n' { break }
            self.junk();
        }
        Ok(())
    }

    // skip whitespaces, including new lines
    fn skip_spaces(&mut self) -> Result<()> {
        while let Some(c) = self.try_get()? {
            match c {
                b' ' | b'\n' | b'\t' => self.junk(),
                b';' => {
                    // skip whole line, it's commented away
                    self.skip_to_eol()?;
                },
                _ => break,
            }
        }
        Ok(())
    }

    // expect and consume `c`, or fail
    fn expect_char(&mut self, c: u8) -> Result<()> {
        let c2 = self.get()?;
        if c2 != c {
            self.err_with(format!("expected '{}', got '{}'", c as char, c2 as char))
        } else {
            self.junk();
            Ok(())
        }
    }

    // parse an atom
    fn atom(&mut self) -> Result<String> {
        self.skip_spaces()?;

        let mut s = Vec::new();

        let c = self.get()?;
        if c == b'|' {
            // escaped atom
            loop {
                self.junk();
                let c = self.get()?;
                if c == b'|' {
                    self.junk();
                    break
                } else {
                    s.push(c);
                }
            }
        } else {
            s.push(c);
            loop {
                self.junk();
                let c = self.get()?;
                match c {
                    b' ' | b'(' | b')' | b'\t' | b'\n' => break,
                    _ => s.push(c),
                }
            }
        }

        let s = String::from_utf8(s)?; // now convert to utf8
        Ok(s)
    }

    // parse a list of `A`, then consume closing parenthesis
    fn many_until_paren<A, F>(&mut self, mut f: F) -> Result<Vec<A>>
        where F: FnMut(&mut Self) -> Result<A>
    {
        let mut v = Vec::new();
        loop {
            self.skip_spaces()?;
            if self.get()? == b')' {
                // done, exit
                self.junk();
                break;
            } else {
                let a = f(self)?;
                v.push(a);
            }
        }
        Ok(v)
    }

    // parse many `A` between parenthesis
    fn within_parens<A, F>(&mut self, f: F) -> Result<Vec<A>>
        where F: FnMut(&mut Self) -> Result<A>
    {
        self.skip_spaces()?;
        self.expect_char(b'(')?;
        self.many_until_paren(f)
    }

    // parse a sort
    fn sort(&mut self) -> Result<B::Sort> {
        let a = self.atom()?;
        if a == "Bool" { return Ok(self.build.get_bool()) }; // builtin
        match self.sorts.get(&a) {
            Some(s) => Ok(s.clone()),
            None => self.err_with(format!("{} is not a known sort", &a).to_string()),
        }
    }

    // find function with this name
    fn find_fun(&self, s: &str) -> Result<B::Fun> {
        match s {
            "and" => Ok(self.build.get_builtin(Op::And)),
            "or" => Ok(self.build.get_builtin(Op::Or)),
            "not" => Ok(self.build.get_builtin(Op::Not)),
            "=>" => Ok(self.build.get_builtin(Op::Imply)),
            "=" => Ok(self.build.get_builtin(Op::Eq)),
            "distinct" => Ok(self.build.get_builtin(Op::Distinct)),
            _ => {
                self.funs.get(s).ok_or_else(|| {
                    mk_err(format!("{} is not a known function", &s))
                }).map(|f| f.clone())
            }
        }
    }

    // parse one `(var term)` pair
    fn parse_binding(&mut self) -> Result<(String,B::Term)> {
        self.skip_spaces()?;
        self.expect_char(b'(')?;
        let v = self.atom()?;
        let t = self.term()?;
        self.skip_spaces()?;
        self.expect_char(b')')?;
        Ok((v,t))
    }

    // parse a term
    fn term(&mut self) -> Result<B::Term> {
        self.skip_spaces()?;
        match self.get()? {
            b'(' => {
                self.junk();
                let a = self.atom()?;
                match a.as_str() {
                    "ite" => {
                        let t1 = self.term()?;
                        let t2 = self.term()?;
                        let t3 = self.term()?;
                        self.expect_char(b')')?;
                        Ok(self.build.ite(t1,t2,t3))
                    },
                    "let" => {
                        // parse series of bindings and enter scope
                        let bs = self.within_parens(|m| m.parse_binding())?;
                        // variables that are added into scope (for shadowing)
                        let not_yet_in_scope =
                            bs.iter().filter(|(s,_)| ! self.vars.contains(s))
                            .map(|(s,_)| s.clone()).collect::<Vec<_>>();
                        debug!("enter scope {:#?} (newly bound: {:#?})",
                            &bs, &not_yet_in_scope);
                        self.vars.extend(not_yet_in_scope.iter().map(|s| s.clone()));
                        // tell builder we enter the scope of this "let"
                        self.build.enter_let(&bs);
                        let body = self.term()?;
                        self.expect_char(b')')?;
                        // exit scope
                        let t = self.build.exit_let(body);
                        for s in not_yet_in_scope {
                            self.vars.remove(&s);
                        }
                        Ok(t)
                    },
                    _ => {
                        // function application
                        let f = self.find_fun(&a)?;
                        let args = self.many_until_paren(|m| m.term())?;
                        Ok(self.build.app_fun(f.clone(), &args))
                    }
                }
            },
            _ => {
                let a = self.atom()?;
                if self.vars.contains(&a) {
                    self.build.var(&a).ok_or_else(|| {
                        mk_err(format!("{} is not a valid variable", &a))
                    })
                } else {
                    let f = self.find_fun(&a)?;
                    Ok(self.build.app_fun(f.clone(), &[]))
                }
            }
        }
    }

    // entry point for a toplevel statement, or None (for EOF)
    fn statement(&mut self) -> Result<Option<Statement<B::Term, B::Sort>>> {
        self.skip_spaces()?;

        if self.eof {
            Ok(None)
        } else {
            self.expect_char(b'(')?;
            let dir = self.atom()?;
            let st = match dir.as_str() {
                "set-info" => {
                    let a = self.atom()?;
                    let b = self.atom()?;
                    Statement::SetInfo(a,b)
                },
                "set-logic" => {
                    let a = self.atom()?;
                    Statement::SetLogic(a)
                },
                "declare-sort" => {
                    let a = self.atom()?;
                    let n = self.atom()?.parse::<u8>()?;
                    // make a sort and store it
                    let sort = self.build.declare_sort(a.clone(), n);
                    self.sorts.insert(a.clone(), sort);
                    Statement::DeclareSort(a, n)
                },
                "declare-fun" => {
                    let a = self.atom()?;
                    let tys = self.within_parens(|m| m.sort())?;
                    let ret = self.sort()?;
                    // store function
                    let f = self.build.declare_fun(a.clone(), &tys, ret.clone());
                    self.funs.insert(a.clone(), f);
                    Statement::DeclareFun(a, tys, ret)
                },
                "assert" => {
                    let t = self.term()?;
                    Statement::Assert(t)
                },
                "check-sat" => Statement::CheckSat,
                "exit" => Statement::Exit,
                _ => {
                    self.err_with(format!("unknown directive {:?}", dir))?
                }
            };
            self.expect_char(b')')?;
            debug!("parsed statement {:?}", &st);
            Ok(Some(st))
        }
    }

    // parse a bunch of statements until the EOF
    fn statements(&mut self) -> Result<Vec<Statement<B::Term, B::Sort>>> {
        let mut res = Vec::new();

        loop {
            match self.statement() {
                Ok(None) => break,
                Ok(Some(st)) => {
                    res.push(st);
                },
                Err(e) => return Err(e),
            }
        }
        Ok(res)
    }
}

/// Parse a set of statements from `r`, allocating terms in `m`
pub fn parse<R,B>(b: &mut B, r: R) -> Result<Vec<Statement<B::Term, B::Sort>>>
    where R : io::Read, B: TermBuilder
{
    let mut p = ParserState::new(b, r);
    p.statements()
}

/// Parse from given string
pub fn parse_str<B>(b: &mut B, s: &str) -> Result<Vec<Statement<B::Term, B::Sort>>>
    where B: TermBuilder
{
    let c = io::Cursor::new(s.as_bytes());
    parse(b, c)
}

/// Parse from stdin
pub fn parse_stdin<B>(b: &mut B) -> Result<Vec<Statement<B::Term, B::Sort>>>
    where B: TermBuilder
{
    let r = io::BufReader::new(io::stdin());
    parse(b, r)
}
