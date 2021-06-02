extern crate prusti_contracts;
use prusti_contracts::*;

#[pure]
#[ensures(result >= a && result >= b)]
#[ensures(result == a || result == b)]
fn max(a: u32, b: u32) -> u32 {
    if a > b {
        a
    } else {
        b
    }
}

// Prusti can not handle assert_eq!
// #[ensures(result == max(a, max(b, c)))]
// fn max3(a: i32, b: i32, c: i32) -> i32 {
//     if a > b && a > c {
//         a
//     } else {
//         if b > c {
//             assert_eq!(max(b, c), b); // FAILS
//             b
//         } else {
//             c
//         }
//     }
// }

// Prusti can not handle loops that are not annotated.
// #[ensures(result == max(0, max(a, b)))]
// fn max_range(a: i32, b: i32) -> i32 {
//     let mut i = 0;
//     // Will perform max(0, max(a, b)) iterations
//     for _ in 0..max(0, max(a, b)) {
//         i = i + 1;
//     }
//     // Will be equal to max(0, max(a, b))
//     i
// }
// #[ensures(result <= max(0, max(a, b)))]
// fn max_range(a: i32, b: i32) -> i32 {
//     let mut i = 0;
//     // Will perform max(0, max(a, b)) iterations
//     for _ in 0..max(0, max(a, b)) {
//         assert!(max(0, max(a, b)) != 0);
//         body_invariant!(i >= 0);
//         // This should hold, since entering the loop requires
//         // max(0, max(a, b)) to be 1.
//         // body_invariant!(i < max(0, max(a, b)));
//         i = i + 1;
//         body_invariant!(i <= max(0, max(a, b)));
//         body_invariant!(i > 0);
//     }
//     // Will be equal to max(0, max(a, b))
//     // assert!(i == max(0, max(a, b)));
//     i
// }

// #[ensures(result <= max(0, max(a, b)))]
// fn max_range(a: u32, b: u32) -> u32 {
//     if max(a, b) <= 0 {
//         0
//     } else {
//         let mut i = 0;
//         // Will perform max(a, b) iterations
//         assert!(max(a, b) > 0);
//         for _ in 0..max(a, b) {
//             // This must be true, as the only other case is == 0,
//             // handled above. Using `if max(a, b) == 0` fails,
//             // as Prusti believes that this loop can take on
//             // negative values.
//             assert!(max(a, b) > 0);
//             body_invariant!(i >= 0);

//             // This should hold, since entering the loop requires
//             // max(a, b) > 0, which means that since i starts at 0,
//             // this will hold for the first iteration, and since
//             // we only execute max(a, b) iterations, this will hold
//             // for all subsequent iterations
//             body_invariant!(i < max(a, b));
//             i = i + 1;
//             body_invariant!(i <= max(a, b));
//             body_invariant!(i > 0);
//         }
//         // Will be equal to max(0, max(a, b))
//         // assert!(i == max(0, max(a, b)));
//         i
//     }
// }


// fn main() {
//     println!("{}", max_range(0, 1))
// }

#[derive(PartialEq, Copy, Clone)]
enum U32Opt {
    Some(u32),
    None
}

// #[pure]
// #[requires(a >= 0 && a <= u32::MAX)]
// #[requires(b >= 0 && b <= u32::MAX)]
// #[ensures(result == if a <= u32::MAX - b { (true, a + b) } else { (false, 0) })]
// fn checked_add(a: u32, b: u32) -> (bool, u32) {
//     if a <= u32::MAX - b {
//         (true, a + b)
//     } else {
//         (false, 0)
//     }
// }

// #[requires(0 <= i && i < 32)]
// #[ensures(result == 0 || result == 1)]
// fn look_up_bit(x: u32, i: u8) -> u8 {
//     if (x & (1 << i)) != 0 {
//         1
//     } else {
//         0
//     }
// }

// #[pure]
// #[ensures(
//     forall(|i: u8|
//         (0 <= i && i < 32 ==> look_up_bit(result, i) == look_up_bit(a, 32 - i))
//     )
// )]
// fn flip_bits(a: u32) -> u32 {
//     let mut out = 0;
//     let mut i = 0u32;
//     while i < 32 {
//         out = out | ((a >> i) << (32 - i));
//         i += 1;
//     }
//     out
// }

pub struct BoolArr32 {
    v: Vec<bool>
}

impl BoolArr32 {
    #[trusted]
    #[ensures(
        forall(|i: usize|
            (0 <= i && i < 32 ==> !result.lookup(i))
        )
    )]
    pub fn zero() -> Self {
        BoolArr32 { v: vec![false; 32] }
    }

    #[trusted]
    #[pure]
    #[ensures(result == 32)]
    pub fn len(&self) -> usize {
        self.v.len()
    }

    /// A ghost function for specifying values stored in the vector.
    /// Acts like `v >> index`.
    #[trusted]
    #[pure]
    #[requires(0 <= index && index < self.len())]
    pub fn lookup(&self, index: usize) -> bool {
        self.v[index]
    }

    #[trusted]
    #[requires(0 <= index && index < self.len())]
    #[ensures(*result == old(self.lookup(index)))]
    #[after_expiry(
        self.len() == old(self.len()) &&
        self.lookup(index) == before_expiry(*result) &&
        forall(
            |i: usize| (0 <= i && i < self.len() && i != index) ==>
            self.lookup(i) == old(self.lookup(i))
        )
    )]
    pub fn index_mut(&mut self, index: usize) -> &mut bool {
        self.v.get_mut(index).unwrap()
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
    fn flip_bits(self: BoolArr32) -> BoolArr32 {
        let mut out = BoolArr32::zero();
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
        
            *out.index_mut(i) = self.lookup(31 - i);
            i += 1;
        }
        out
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
    fn shl(&self, amt: usize) -> BoolArr32 {
        let mut out = BoolArr32::zero();
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

            *out.index_mut(i) = self.lookup(i - amt);
            i += 1;
        }
        out
    }

    #[requires(0 <= amt)]
    // #[ensures(
    //     forall(|i: usize|
    //         (0 <= i && i < 32)
    //         && (amt <= i && (i - amt) >= 0 && (i - amt) < 32)
    //         ==> result.lookup(i - amt) == self.lookup(i)
    //     )
    // )]
    #[ensures(
        forall(|i: usize|
            (0 <= i && i > 32 - amt && i < 32 ==> !result.lookup(i))
        )
    )]
    /// 10 >> 1 : 01
    /// High bits are zero: >> 1 means that bit 31 is clear
    // if amt is 1 -> 31-31 / if amt > 31: 0-31
    fn shr(&self, amt: usize) -> BoolArr32 {
        let mut out = BoolArr32::zero();
        let mut i = amt;
        // forall!(|i: usize|
        //     (0 <= i && i < 32 => *out.index_mut(i) == a.lookup(31 - i))
        // )
        
        // 0101 >> 1 -> 0010
        // 3210         3210
        // forall i > amt, out(i - amt) = 
        while i < 32 {
            // body_invariant_doc!("...");
            body_invariant!(0 <= i && i < 32);
            body_invariant!(i >= amt && (i - amt) >= 0 && (i - amt) < 32);
            body_invariant!(
                forall(|j: usize|
                    (0 <= j && j > 32 - amt && j < 32)
                    ==> !out.lookup(j)
                )
            );
            // body_invariant!(
            //     forall(|j: usize|
            //         (0 <= j && j < 32)
            //         && (amt <= j && j < i)
            //         && (j - amt) < 32
            //         ==> out.lookup(j - amt) == self.lookup(j)
            //     )
            // );

            *out.index_mut(i - amt) = self.lookup(i);
            i += 1;
        }
        out
    }

    #[ensures(
        forall(|i: usize|
            0 <= i && i < 32 ==> result.lookup(i) == (self.lookup(i) | other.lookup(i))
        ) 
    )]
    fn or(&self, other: &BoolArr32) -> BoolArr32 {
        let mut out = BoolArr32::zero();
        let mut i = 0;
        while i < 32 {
            body_invariant!(0 <= i && i < 32);
            body_invariant!(forall(|j: usize|
                (0 <= j && j < i) ==> 
                    out.lookup(j) == (self.lookup(j) | other.lookup(j))
            ));
            *out.index_mut(i) = self.lookup(i) | other.lookup(i);
            i += 1;
        }

        out
    }

    #[ensures(
        forall(|i: usize|
            0 <= i && i < 32 ==> result.lookup(i) == (self.lookup(i) & other.lookup(i))
        ) 
    )]
    fn and(&self, other: &BoolArr32) -> BoolArr32 {
        let mut out = BoolArr32::zero();
        let mut i = 0;
        while i < 32 {
            body_invariant!(0 <= i && i < 32);
            body_invariant!(forall(|j: usize|
                (0 <= j && j < i) ==> 
                    out.lookup(j) == (self.lookup(j) & other.lookup(j))
            ));
            *out.index_mut(i) = self.lookup(i) & other.lookup(i);
            i += 1;
        }

        out
    }

    #[ensures(
        forall(|i: usize|
            0 <= i && i < 32 ==> result.lookup(i) == (self.lookup(i) ^ other.lookup(i))
        ) 
    )]
    fn xor(&self, other: &BoolArr32) -> BoolArr32 {
        let mut out = BoolArr32::zero();
        let mut i = 0;
        while i < 32 {
            body_invariant!(0 <= i && i < 32);
            body_invariant!(forall(|j: usize|
                (0 <= j && j < i) ==> 
                    out.lookup(j) == (self.lookup(j) ^ other.lookup(j))
            ));
            *out.index_mut(i) = self.lookup(i) ^ other.lookup(i);
            i += 1;
        }

        out
    }

    // missing mir, user guide unclear
    // #[requires(f |= |a: bool, b: bool| [
    //     requires(a | !a),
    //     requires(b | !b),
    //     ensures(result | !result)
    // ])]
    // #[ensures(
    //     forall(|i: usize|
    //         0 <= i && i < 32 ==> result.lookup(i) == f(self.lookup(i), other.lookup(i))
    //     ) 
    // )]
    // fn map_bits<F: Fn(bool, bool) -> bool>(&self, other: &BoolArr32, f: F) -> BoolArr32 {
    //     let mut out = BoolArr32::zero();
    //     let mut i = 0;
    //     while i < 32 {
    //         body_invariant!(0 <= i && i < 32);
    //         body_invariant!(forall(|j: usize|
    //             (0 <= j && j < i) ==> 
    //                 out.lookup(j) == f(self.lookup(j), other.lookup(j))
    //         ));
    //         *out.index_mut(i) = f(self.lookup(i), other.lookup(i));
    //         i += 1;
    //     }

    //     out
    // }

    // #[ensures(
    //     forall(|i: usize|
    //         0 <= i && i < 32 ==> result.lookup(i) == (self.lookup(i) ^ other.lookup(i))
    //     ) 
    // )]
    // fn xorc(&self, other: &BoolArr32) -> BoolArr32 {
    //     let cl = closure!(
    //         ensures(result == a ^ b),
    //         |a: bool, b: bool| -> bool { a ^ b }
    //     );
    //     self.map_bits(other, cl)
    // }


}

fn closure() {
    let _cl = closure! (
        requires (a > b),
        ensures (result > b),
        |a: u8, b: u8| -> u8 { a }
    );
}
// take a look at vec & linked list as datastructure examples 
// & use STL documentation
// and/or custom implementations
// minify pure example




// Test that if precondition false, program panics & if true, does not
// Self-referential definitions

// test mutual reference?
// test if function is pure (eg. no reference to interior mutability in Rust, no unsafe, asm, or syscalls)