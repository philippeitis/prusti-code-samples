extern crate prusti_contracts;
use prusti_contracts::*;

struct PrustiVec {
    v: Vec<u8>
}

impl PrustiVec {
    /// Returns the length of self.
    #[trusted]
    #[pure]
    #[ensures(0 <= result)]
    fn len(&self) -> usize {
        self.v.len()
    }

    /// Returns the item at `index`. `index` must be less than
    /// the length of `self`.
    #[trusted]
    #[pure] // automatically detect if used in specs
    #[requires(0 <= index && index < self.len())]
    pub fn lookup(&self, index: usize) -> u8 {
        self.v[index]
    }

    // /// Returns the last item from the list. `self.len()` must be
    // /// greater than 1.
    // #[trusted]
    // #[pure]
    // #[requires(self.len() >= 1)]
    // fn last(&self) -> u8 {
    //     self.v.last().unwrap()
    // }

    /// The list's length increases by one, and the last value 
    /// is now val. Items at indexes 0 through `old(self.len())`
    /// remain the same.
    #[trusted]
    #[ensures(self.len() == old(self.len()) + 1)]
    #[ensures(self.len() >= 1)]
    #[ensures(self.lookup(self.len() - 1) == val)]
    #[ensures(
        forall(|i: usize| 
            (0 <= i && i < old(self.len())) ==> self.lookup(i) == old(self.lookup(i))
        )
    )]
    fn push(&mut self, val: u8) {
        self.v.push(val)
    }


    #[trusted]
    #[requires(0 <= index && index < self.len())]
    #[ensures(self.len() == old(self.len()) - 1)]
    #[ensures(self.len() >= 0)]
    #[ensures(result == old(self.lookup(index)))]
    /// check everything beforehand is unchanged
    #[ensures(
        forall(|i: usize| 
            (0 <= i && i < index && i < old(self.len()) && i < self.len()) ==> self.lookup(i) == old(self.lookup(i))
        )
    )]
    /// check that everything after index is moved over by one.
    #[ensures(
        forall(|i: usize| 
            (1 <= i && index <= i && i < old(self.len()) && i < self.len()) ==> self.lookup(i - 1) == old(self.lookup(i))
        )
    )]
    fn remove(&mut self, index: usize) -> u8 {
        self.v.remove(index)
    }

    #[requires(self.len() >= 1)]
    #[ensures(self.len() == old(self.len()) - 1)]
    #[ensures(self.len() >= 0)]
    #[ensures(result == old({
        let l = self.len() - 1;
        self.lookup(l)
    }))]
    /// check everything beforehand is unchanged
    #[ensures(
        forall(|i: usize| 
            (0 <= i && i < index && i < old(self.len()) && i < self.len()) ==> self.lookup(i) == old(self.lookup(i))
        )
    )]
    fn pop(&mut self, index: usize) -> u8 {
        let l = self.len() - 1;
        self.remove(l)
    }

    #[ensures(self.len() == old(self.len()) + other.len())]
    #[ensures(
        forall(|i: usize| 
            (0 <= i && i < other.len()) ==> 
                self.lookup(i + old(self.len())) == other.lookup(i)
        )
    )]
    #[ensures(
        forall(|i: usize| 
            (0 <= i && i < old(self.len())) ==> self.lookup(i) == old(self.lookup(i))
        )
    )]
    // For each index from self.len() to self.len() + other.len()
    fn append(&mut self, other: &PrustiVec) {
        let mut i = 0;
        let old_len = self.len();
        while i < other.len() {
            body_invariant!(0 <= i && i < other.len());
            // The length of `self` is equal the old length of self plus i
            body_invariant!(self.len() == old(self.len()) + i);

            body_invariant!(
                forall(|j: usize|
                    (0 <= j && j < i)
                     && (0 <= j + old(self.len()) && j + old(self.len()) < self.len())
                     && j < other.len() ==>
                        self.lookup(j + old(self.len())) == other.lookup(j)
                )
            );
            body_invariant!(        forall(|j: usize| 
                (0 <= j && j < old(self.len())) ==> self.lookup(j) == old(self.lookup(j))
            )
    );
            self.push(other.lookup(i));
            i += 1;
        }
    }

    #[predicate]
    fn not_contains(&self, val: u8) -> bool {
        forall(|i: usize| 
            (0 <= i && i < self.len()) ==> self.lookup(i) != val
        )
    }

    #[predicate]
    fn contains(&self, val: u8) -> bool {
        !self.not_contains(val)
    }
}

#[predicate]
fn not_contains(s: &PrustiVec, val: u8) -> bool {
    forall(|i: usize| 
        (0 <= i && i < s.len()) ==> s.lookup(i) != val
    )
}

#[predicate]
fn contains(s: &PrustiVec, val: u8) -> bool {
    !s.not_contains(val)
}
