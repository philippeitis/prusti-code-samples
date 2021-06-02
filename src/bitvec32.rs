extern crate prusti_contracts;
use prusti_contracts::*;

pub struct BitVec32 {
    v: u32
}

impl BitVec32 {
    /// Returns a BitVec32. For each index `i` from 0, up to and not including 32,
    /// the value at index `i` in the result is false.
    #[trusted]
    #[ensures(
        forall(|i: usize|
            (0 <= i && i < 32 ==> !result.lookup(i))
        )
    )]
    pub fn zero() -> Self {
        BitVec32 { v: 0 }
    }

    /// Returns the length of BitVec32.
    #[trusted]
    #[pure]
    #[ensures(result == 32)]
    pub fn len(&self) -> usize {
        32
    }

    /// Returns the value at `index`.
    /// A ghost function for specifying values stored in the vector.
    /// Acts like `v >> index`.
    #[trusted]
    #[pure]
    #[requires(0 <= index && index < self.len())]
    pub fn lookup(&self, index: usize) -> bool {
        if ((self.v >> index) & 1) == 1 {
            true
        } else {
            false
        }
    }

    #[trusted]
    #[requires(0 <= index && index < self.len())]
    #[ensures(self.lookup(index) == val)]
    #[ensures(
        forall(|i: usize| 
            (0 <= i && i < 32 && i != index)
            ==> self.lookup(i) == old(self.lookup(i))
        )
    )]
    pub fn set_bit(&mut self, index: usize, val: bool) {
        if val {
            self.v |= 1 << index;
        } else {
            self.v &= !(1 << index);
        }
    }

    /// Does this thing.
    /// # Panics
    ///
    /// # Specification
    /// ...
    // #[panics_under("...")]
    // #[specification_doc("For all ... ")]
    #[ensures(
        forall(|i: usize|
            (0 <= i && i < 32 ==> result.lookup(i) == self.lookup(31 - i))
        )
    )]
    fn reverse_bits_v(&self) -> BitVec32 {
        let mut out = BitVec32::zero();
        let mut i = 0;
        // forall!(|i: usize|
        //     (0 <= i && i < 32 => *out.index_mut(i) == a.lookup(31 - i))
        // )

        while i < 32usize {
            // body_invariant_doc!("...");
            body_invariant!(0 <= i && i < 32);
            // Can these be automatically generated from pre/post conditions?
            body_invariant!(
                forall(|j: usize|
                    (0 <= j && j < i ==> out.lookup(j) == self.lookup(31 - j))
                )
            );
            out.set_bit(i, self.lookup(31 - i));
            i += 1;
        }
        out
    }

    /// For each index `i` from 0, up to and not including 32, the value at index
    /// `i` in the resulting BitVec32 is equal to the value at index `31 - i` in 
    /// self.
    #[trusted]
    #[ensures(
        forall(|i: usize|
            (0 <= i && i < 32 ==> result.lookup(i) == self.lookup(31 - i))
        )
    )]
    fn reverse_bits(&self) -> BitVec32 {
        BitVec32 { v: self.v.reverse_bits() }
    }

    #[requires(0 <= amt)]
    #[ensures(
        forall(|i: usize|
            (0 <= i && i < 32)
            && (amt <= i && (i - amt) >= 0 && (i - amt) < 32)
            ==> result.lookup(i) == self.lookup(i - amt)
        )
    )]
    #[ensures(
        forall(|i: usize|
            (0 <= i && i < amt && i < 32 ==> !result.lookup(i))
        )
    )]
    /// 01 << 1 : 10
    fn shl_v(&self, amt: usize) -> BitVec32 {
        let mut out = BitVec32::zero();
        let mut i = amt;
        // forall!(|i: usize|
        //     (0 <= i && i < 32 => *out.index_mut(i) == a.lookup(31 - i))
        // )

        while i < 32usize {
            // body_invariant_doc!("...");
            body_invariant!(0 <= i && i < 32);
            body_invariant!(amt <= i && (i - amt) >= 0 && (i - amt) < 32);
            // Can these be automatically generated from pre/post conditions?
            body_invariant!(
                forall(|j: usize|
                    (0 <= j && j < i && j >= amt)
                    && (amt <= j && (j - amt) >= 0 && (j - amt) < 32)
                    ==> out.lookup(j) == self.lookup(j - amt)
                )
            );
            body_invariant!(
                forall(|j: usize|
                    (0 <= j && j < amt && j < 32)
                    ==> !out.lookup(j)
                )
            );
            
            out.set_bit(i, self.lookup(i - amt));
            i += 1;
        }
        out
    }

    /// At each index `i` from 0, up to and not including the minimum of amt and 32,
    /// the value at bit `i` in the resulting BitVec32 is equal to to 0. 
    /// At each index `i` from amt, up to, and not including 32, the value at bit
    /// `i` in the result is equal to the value at bit `i - amt` in `self`.
    #[trusted]
    #[requires(0 <= amt)]
    #[ensures(
        forall(|i: usize|
            (0 <= i && i < 32)
            && (amt <= i && (i - amt) >= 0 && (i - amt) < 32)
            ==> result.lookup(i) == self.lookup(i - amt)
        )
    )]
    #[ensures(
        forall(|i: usize|
            (0 <= i && i < amt && i < 32 ==> !result.lookup(i))
        )
    )]
    /// 01 << 1 : 10
    fn shl(&self, amt: usize) -> BitVec32 {
        BitVec32 { v: self.v >> amt }
    }

    // #[requires(0 <= amt)]
    // // #[ensures(
    // //     forall(|i: usize|
    // //         (0 <= i && i < 32)
    // //         && (amt <= i && (i - amt) >= 0 && (i - amt) < 32)
    // //         ==> result.lookup(i - amt) == self.lookup(i)
    // //     )
    // // )]
    // #[ensures(
    //     forall(|i: usize|
    //         (0 <= i && i < 32 && i <= 32 - amt && 0 <= i - amt && i - amt < 32) ==>
    //             result.lookup(i - amt) == self.lookup(i)
    //     )
    // )]
    // #[ensures(
    //     forall(|i: usize|
    //         (0 <= i && i < 32 && i > 32 - amt ==> !result.lookup(i))
    //     )
    // )]
    // /// 10 >> 1 : 01
    // /// High bits are zero: >> 1 means that bit 31 is clear
    // // if amt is 1 -> 31-31 / if amt > 31: 0-31
    // fn shr_v(&self, amt: usize) -> BitVec32 {
    //     let mut out = BitVec32::zero();
    //     let mut i = amt;
    //     // forall!(|i: usize|
    //     //     (0 <= i && i < 32 => *out.index_mut(i) == a.lookup(31 - i))
    //     // )
        
    //     // 0101 >> 1 -> 0010
    //     // 3210         3210
    //     // forall i > amt, out(i - amt) = 
    //     while i < 32 {
    //         // body_invariant_doc!("...");
    //         body_invariant!(0 <= i && i < 32);
    //         body_invariant!(i >= amt && (i - amt) >= 0 && (i - amt) < 32);
    //         body_invariant!(
    //             forall(|j: usize|
    //                 (0 <= j && j > 32 - amt && j < 32)
    //                 ==> !out.lookup(j)
    //             )
    //         );
    //         body_invariant!(
    //             forall(|j: usize|
    //                 (0 <= j && j < 32)
    //                 && (j <= 32 - amt && 0 <= j - amt && j - amt < 32)
    //                 && (j < i) ==>
    //                     out.lookup(j - amt) == self.lookup(j)
    //                 )                    
    //         );

    //         out.set_bit(i - amt, self.lookup(i));
    //         i += 1;
    //     }
    //     out
    // }

    #[ensures(
        forall(|i: usize|
            0 <= i && i < 32 ==> result.lookup(i) == (self.lookup(i) | other.lookup(i))
        ) 
    )]
    fn or_v(&self, other: &BitVec32) -> BitVec32 {
        let mut out = BitVec32::zero();
        let mut i = 0;
        while i < 32 {
            body_invariant!(0 <= i && i < 32);
            body_invariant!(forall(|j: usize|
                (0 <= j && j < i) ==> 
                    out.lookup(j) == (self.lookup(j) | other.lookup(j))
            ));
            out.set_bit(i, self.lookup(i) | other.lookup(i));
            i += 1;
        }

        out
    }

    #[trusted]
    #[ensures(
        forall(|i: usize|
            0 <= i && i < 32 ==> result.lookup(i) == (self.lookup(i) | other.lookup(i))
        ) 
    )]
    fn or(&self, other: &BitVec32) -> BitVec32 {
        BitVec32 { v: self.v | other.v }
    }


    #[ensures(
        forall(|i: usize|
            0 <= i && i < 32 ==> result.lookup(i) == (self.lookup(i) & other.lookup(i))
        ) 
    )]
    fn and_v(&self, other: &BitVec32) -> BitVec32 {
        let mut out = BitVec32::zero();
        let mut i = 0;
        while i < 32 {
            body_invariant!(0 <= i && i < 32);
            body_invariant!(forall(|j: usize|
                (0 <= j && j < i) ==> 
                    out.lookup(j) == (self.lookup(j) & other.lookup(j))
            ));
            out.set_bit(i, self.lookup(i) & other.lookup(i));
            i += 1;
        }

        out
    }

    #[trusted]
    #[ensures(
        forall(|i: usize|
            0 <= i && i < 32 ==> result.lookup(i) == (self.lookup(i) & other.lookup(i))
        ) 
    )]
    fn and(&self, other: &BitVec32) -> BitVec32 {
        BitVec32 { v: self.v & other.v }
    }

    #[ensures(
        forall(|i: usize|
            0 <= i && i < 32 ==> result.lookup(i) == (self.lookup(i) ^ other.lookup(i))
        ) 
    )]
    fn xor_v(&self, other: &BitVec32) -> BitVec32 {
        let mut out = BitVec32::zero();
        let mut i = 0;
        while i < 32 {
            body_invariant!(0 <= i && i < 32);
            body_invariant!(forall(|j: usize|
                (0 <= j && j < i) ==> 
                    out.lookup(j) == (self.lookup(j) ^ other.lookup(j))
            ));
            out.set_bit(i, self.lookup(i) ^ other.lookup(i));
            i += 1;
        }

        out
    }

    /// Each bit in the resulting BitVec32 is equal to the corresponding
    /// bit in `self`, xor the corresponding bit in `other`.
    /// For each <-
    #[trusted]
    #[ensures(
        forall(|i: usize|
            0 <= i && i < 32 ==> result.lookup(i) == (self.lookup(i) ^ other.lookup(i))
        ) 
    )]
    fn xor(&self, other: &BitVec32) -> BitVec32 {
        BitVec32 { v: self.v ^ other.v }
    }

    /// Returns a BitVec32 containing `self.v * other.v`. 
    #[ensures(result.v == self.v * other.v)]
    fn mul(&self, other: &BitVec32) -> BitVec32 {
        BitVec32 { v: self.v * other.v }
    }

    #[requires(other.v != 0)]
    #[ensures(result.v == self.v / other.v)]
    fn div(&self, other: &BitVec32) -> BitVec32 {
        BitVec32 { v: self.v / other.v }
    }

    /// Returns a BitVec32 containing `self.v / other.v`. `other.v`
    /// must not be equal to 0. 
    #[requires(other.v != 0)]
    #[ensures(result.v == self.v / other.v)]
    fn checked_div(&self, other: &BitVec32) -> BitVec32 {
        BitVec32 { v: self.v / other.v }
    }

}
