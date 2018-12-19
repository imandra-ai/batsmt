
use {
    std::{hash::Hash, u32, },
    fxhash::FxHashMap,
};

/// Backtrackable hashmap.
///
/// Note that keys must be clonable as well as comparable and hashable,
/// because we will store old versions of them in an undo stack.
#[derive(Clone)]
pub struct HashMap<K:Eq+Hash,V> {
    map: FxHashMap<K,V>,
    undo: Vec<Undo<K,V>>,
    levels: Vec<u32>,
}

#[derive(Clone)]
enum Undo<K,V> {
    Remove(K),
    Restore(K,V), // restore k->v binding
}

/// A hashset is just a Hashmap with `()` as values.
pub type HashSet<T> = HashMap<T,()>;

impl<K:Eq+Hash+Clone,V> HashMap<K,V> {
    /// Create a new backtrackable hashmap.
    pub fn new() -> Self {
        HashMap {
            map: FxHashMap::default(),
            undo: vec!(), levels: vec!(),
        }
    }

    /// Insert the binding `k -> v` into the map.
    ///
    /// This binding will be removed when we backtrack.
    /// Returns `true` if there was a binding before.
    pub fn insert(&mut self, k: K, v: V) -> bool {
        if self.levels.len() == 0 {
            self.map.insert(k,v).is_some() // never backtracked
        } else {
            let k2 = k.clone();
            let old_v = self.map.insert(k,v);
            match old_v {
                None => {
                    self.undo.push(Undo::Remove(k2));
                    false
                },
                Some(old_v) => {
                    self.undo.push(Undo::Restore(k2, old_v));
                    true
                },
            }
        }
    }

    /// Remove binding.
    ///
    /// Returns `true` if there was a binding.
    pub fn remove(&mut self, k: &K) -> bool {
        if self.levels.len() == 0 {
            self.map.remove(k).is_some() // never backtracked
        } else {
            match self.map.remove(k) {
                None => false, // nop
                Some(v2) => {
                    // remember to re-insert when we backtrack
                    self.undo.push(Undo::Restore(k.clone(),v2));
                    true
                }
            }
        }
    }

    #[inline(always)]
    pub fn n_levels(&self) -> usize { self.levels.len() }

    /// Push a backtracking point.
    pub fn push_level(&mut self) {
        let cur_size = self.undo.len();
        if cur_size > u32::MAX as usize { panic!("backtrack stack is too deep") };
        self.levels.push(cur_size as u32);
    }

    /// Pop `n` backtracking levels, restoring the table to its former state.
    pub fn pop_levels(&mut self, n: usize) {
        if n > self.levels.len() {
            panic!("cannot backtrack {} levels in a stack with only {}", n, self.levels.len());
        }
        // obtain offset in `self.undo` and resize the `levels` stack
        let offset = {
            let idx = self.levels.len() - n;
            let offset = self.levels[idx];
            self.levels.resize(idx, 0);
            offset as usize
        };
        // perform undo operations
        while self.undo.len() > offset {
            let op = self.undo.pop().unwrap();
            match op {
                Undo::Remove(k) => {
                    self.map.remove(&k);
                },
                Undo::Restore(k,v) => {
                    self.map.insert(k,v);
                },
            }
        }
    }
}

impl<K:Eq+Hash,V> std::ops::Deref for HashMap<K,V> {
    type Target = FxHashMap<K,V>;
    fn deref(&self) -> &Self::Target { &self.map }
}
