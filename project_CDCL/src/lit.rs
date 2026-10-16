//! Literal representation.
//!
//! Variables are 0-based internally (`x1` in DIMACS is var 0). A literal is
//! packed as `2 * var + sign`, where sign 0 = positive and 1 = negative, so
//! negation is a single XOR and literals can index watch lists directly.

use std::fmt;
use std::ops::Not;

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Lit(u32);

impl Lit {
    pub fn new(var: usize, positive: bool) -> Lit {
        Lit(((var as u32) << 1) | (!positive) as u32)
    }

    /// Build from a non-zero DIMACS integer (`3` -> x3, `-3` -> ¬x3).
    pub fn from_dimacs(x: i64) -> Lit {
        debug_assert!(x != 0);
        Lit::new(x.unsigned_abs() as usize - 1, x > 0)
    }

    pub fn to_dimacs(self) -> i64 {
        let v = self.var() as i64 + 1;
        if self.is_positive() {
            v
        } else {
            -v
        }
    }

    pub fn var(self) -> usize {
        (self.0 >> 1) as usize
    }

    pub fn is_positive(self) -> bool {
        self.0 & 1 == 0
    }

    /// Dense index for literal-indexed arrays (watch lists, counters).
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

impl Not for Lit {
    type Output = Lit;
    fn not(self) -> Lit {
        Lit(self.0 ^ 1)
    }
}

impl fmt::Debug for Lit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_dimacs())
    }
}

impl fmt::Display for Lit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_dimacs())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roundtrip_and_negation() {
        for x in [1i64, -1, 7, -7, 1000] {
            let l = Lit::from_dimacs(x);
            assert_eq!(l.to_dimacs(), x);
            assert_eq!((!l).to_dimacs(), -x);
            assert_eq!(l.var(), (x.unsigned_abs() - 1) as usize);
        }
    }
}
