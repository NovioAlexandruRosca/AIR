//! Exact rationals over i128 for the Simplex tableau. Overflow panics with
//! a clear message (the server turns a panic into an error response);
//! teaching-size problems stay far from the i128 range.

use std::cmp::Ordering;
use std::fmt;
use std::ops::{Add, Div, Mul, Neg, Sub};

pub fn gcd(a: i128, b: i128) -> i128 {
    let (mut a, mut b) = (a.abs(), b.abs());
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

/// Floor division for integers.
pub fn div_floor(a: i128, b: i128) -> i128 {
    let q = a / b;
    if (a % b != 0) && ((a < 0) != (b < 0)) {
        q - 1
    } else {
        q
    }
}

pub fn div_ceil(a: i128, b: i128) -> i128 {
    -div_floor(-a, b)
}

const OVERFLOW: &str = "integer overflow in LIA arithmetic (coefficients or bounds too large)";

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Rat {
    n: i128,
    d: i128,
}

impl Rat {
    pub const ZERO: Rat = Rat { n: 0, d: 1 };
    pub const ONE: Rat = Rat { n: 1, d: 1 };

    pub fn int(n: i128) -> Rat {
        Rat { n, d: 1 }
    }

    pub fn new(n: i128, d: i128) -> Rat {
        assert!(d != 0, "division by zero");
        let g = gcd(n, d).max(1);
        let (mut n, mut d) = (n / g, d / g);
        if d < 0 {
            n = n.checked_neg().expect(OVERFLOW);
            d = d.checked_neg().expect(OVERFLOW);
        }
        Rat { n, d }
    }

    pub fn numer(self) -> i128 {
        self.n
    }

    pub fn is_int(self) -> bool {
        self.d == 1
    }

    pub fn is_zero(self) -> bool {
        self.n == 0
    }

    pub fn floor(self) -> i128 {
        div_floor(self.n, self.d)
    }

    pub fn ceil(self) -> i128 {
        div_ceil(self.n, self.d)
    }
}

fn mul(a: i128, b: i128) -> i128 {
    a.checked_mul(b).expect(OVERFLOW)
}

impl Add for Rat {
    type Output = Rat;
    fn add(self, o: Rat) -> Rat {
        if self.d == o.d {
            return Rat::new(self.n.checked_add(o.n).expect(OVERFLOW), self.d);
        }
        Rat::new(
            mul(self.n, o.d)
                .checked_add(mul(o.n, self.d))
                .expect(OVERFLOW),
            mul(self.d, o.d),
        )
    }
}

impl Sub for Rat {
    type Output = Rat;
    fn sub(self, o: Rat) -> Rat {
        self + (-o)
    }
}

impl Neg for Rat {
    type Output = Rat;
    fn neg(self) -> Rat {
        Rat {
            n: self.n.checked_neg().expect(OVERFLOW),
            d: self.d,
        }
    }
}

impl Mul for Rat {
    type Output = Rat;
    fn mul(self, o: Rat) -> Rat {
        // Cross-cancel first to keep numbers small.
        let g1 = gcd(self.n, o.d).max(1);
        let g2 = gcd(o.n, self.d).max(1);
        Rat::new(mul(self.n / g1, o.n / g2), mul(self.d / g2, o.d / g1))
    }
}

impl Div for Rat {
    type Output = Rat;
    fn div(self, o: Rat) -> Rat {
        assert!(o.n != 0, "division by zero");
        self * Rat::new(o.d, o.n)
    }
}

impl Ord for Rat {
    fn cmp(&self, o: &Rat) -> Ordering {
        mul(self.n, o.d).cmp(&mul(o.n, self.d))
    }
}

impl PartialOrd for Rat {
    fn partial_cmp(&self, o: &Rat) -> Option<Ordering> {
        Some(self.cmp(o))
    }
}

impl fmt::Display for Rat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.d == 1 {
            write!(f, "{}", self.n)
        } else {
            write!(f, "{}/{}", self.n, self.d)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn arithmetic_and_rounding() {
        let a = Rat::new(5, 2);
        assert_eq!(a.floor(), 2);
        assert_eq!(a.ceil(), 3);
        assert_eq!((-a).floor(), -3);
        assert_eq!((-a).ceil(), -2);
        assert_eq!(a + Rat::new(1, 2), Rat::int(3));
        assert_eq!(a * Rat::new(2, 5), Rat::ONE);
        assert_eq!(a / Rat::new(5, 4), Rat::int(2));
        assert!(Rat::new(1, 3) < Rat::new(1, 2));
        assert_eq!(Rat::new(4, -6).to_string(), "-2/3");
        assert_eq!(div_floor(-7, 2), -4);
        assert_eq!(div_ceil(-7, 2), -3);
        assert_eq!(div_ceil(7, 2), 4);
    }
}
