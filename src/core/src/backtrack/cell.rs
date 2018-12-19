
/// A backtrackable reference.
///
/// Its content must be clonable because a copy of it is saved
/// every time `push_level` is called.
#[derive(Clone)]
pub struct Ref<T:Clone> {
    cur: T,
    st: Vec<T>,
}

impl<T:Clone> Ref<T> {
    /// New reference, containing `x` initially.
    pub fn new(x:T) -> Self {
        Ref {cur: x, st: vec!(), }
    }

    /// Access the current content.
    pub fn get(&self) -> &T { &self.cur }

    /// Access mutably the current content.
    ///
    /// This will never modify the copies saved by calls to `push_level`.
    pub fn get_mut(&mut self) -> &mut T { &mut self.cur }

    /// Push a backtracking point.
    pub fn push_level(&mut self) { self.st.push(self.cur.clone()) }

    /// Remove `n` backtracking points.
    pub fn pop_levels(&mut self, n: usize) {
        if n > self.st.len() { panic!("cannot pop {} levels", n) }

        let idx = self.st.len() - n;
        std::mem::swap(&mut self.cur, &mut self.st[idx]); // restore
        self.st.resize(idx, self.cur.clone());
    }

    /// Number of levels.
    pub fn n_levels(&self) -> usize { self.st.len() }
}

impl<T:Clone> std::ops::Deref for Ref<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target { self.get() }
}

impl<T:Clone> std::ops::DerefMut for Ref<T> {
    fn deref_mut(&mut self) -> &mut Self::Target { self.get_mut() }
}
