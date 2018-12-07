
use {
    std::{error, result, fmt, io, ops::Deref},
    fxhash::{FxHashMap,FxHashSet},
    types::*,
};

/// Error messages
#[derive(Debug)]
pub struct Error(String);

impl fmt::Display for Error {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(fmt)
    }
}

impl error::Error for Error {
  fn description(&self) -> &str { &self.0 }
  fn cause(&self) -> Option<&error::Error> { None }
}

pub type Result<T> = result::Result<T, Box<error::Error>>;

fn ret_err<T>(s: String) -> Result<T> {
    Err(Box::new(Error(s)))
}

// parser's buffer size
const BUF_SIZE : usize = 1_024;

// A basic SMT-LIB parser
struct ParserState<'a, R : io::Read, B : TermBuilder> {
    r: R, // underlying reader
    eof: bool,
    buf: [u8; BUF_SIZE], // internal buffer
    i: usize, // offset in buf
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
            r, build, eof: false, buf: [0; BUF_SIZE],
            i: BUF_SIZE + 1, line: 1, col: 1,
            vars: FxHashSet::default(),
            funs: FxHashMap::default(),
            sorts: FxHashMap::default(),
        }
    }

    // refill internal buffer
    fn refill(&mut self) -> Result<()> {
        debug!("refill internal buffer (size {})", BUF_SIZE);
        debug_assert!(self.i >= self.buf.len());
        self.i = 0;
        let n = self.r.read(&mut self.buf)?;
        if n == 0 {
            self.eof = true;
        }
        Ok(())
    }

    fn err_with<T>(&self, s: impl Deref<Target=str>) -> Result<T> {
        let s: &str = &*s;
        ret_err(format!("{} (line {}, col {})", s, self.line, self.col))
    }

    fn err_eof<T>(&self) -> Result<T> {
        self.err_with("unexpected end-of-file")
    }

    // get current char, or EOF
    fn try_get(&mut self) -> Result<Option<u8>> {
        if self.eof {
            Ok(None)
        } else if self.i < self.buf.len() {
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
        match self.try_get()? {
            Some(c) => Ok(c),
            None => self.err_eof(),
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

        // FIXME: remove
        debug!("junk {:?}", self.buf[self.i] as char);

        self.i += 1;
    }

    // skip chars until EOL is reached
    fn skip_to_eol(&mut self) -> Result<()> {
        while let Some(c) = self.try_get()? {
            if c == b'\n' { break }
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
    fn expect(&mut self, c: u8) -> Result<()> {
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

    // entry point for a toplevel statement, or None (for EOF)
    fn statement(&mut self) -> Result<Option<Statement<B::Term, B::Sort>>> {
        self.skip_spaces()?;

        if self.eof {
            Ok(None)
        } else {
            self.expect(b'(')?;
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
                _ => {
                    self.err_with(format!("unknown directive {:?}", dir))?
                }
            };
            self.expect(b')')?;
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
