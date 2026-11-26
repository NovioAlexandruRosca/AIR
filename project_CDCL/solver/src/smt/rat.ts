//! Exact rationals over i128 for the Simplex tableau. Overflow panics with
//! a clear message (the server turns a panic into an error response);
//! teaching-size problems stay far from the i128 range.
// (port of src/smt/rat.rs; i128 -> bigint, range-checked like Rust's checked_* ops)

const I128_MAX = (1n << 127n) - 1n;
const I128_MIN = -(1n << 127n);

const abs = (x: bigint): bigint => (x < 0n ? -x : x);

export function gcd(a: bigint, b: bigint): bigint {
  [a, b] = [abs(a), abs(b)];
  while (b !== 0n) {
    [a, b] = [b, a % b];
  }
  return a;
}

/** Floor division for integers. */
export function div_floor(a: bigint, b: bigint): bigint {
  const q = a / b;
  if (a % b !== 0n && a < 0n !== b < 0n) {
    return q - 1n;
  } else {
    return q;
  }
}

export function div_ceil(a: bigint, b: bigint): bigint {
  return -div_floor(-a, b);
}

const OVERFLOW = "integer overflow in LIA arithmetic (coefficients or bounds too large)";

/** `checked_*(..).expect(OVERFLOW)`: the result must fit in an i128. */
function checked(x: bigint): bigint {
  if (x > I128_MAX || x < I128_MIN) throw new Error(OVERFLOW);
  return x;
}

function mul(a: bigint, b: bigint): bigint {
  return checked(a * b);
}

const max1 = (g: bigint): bigint => (g > 1n ? g : 1n);

export class Rat {
  constructor(
    public n: bigint,
    public d: bigint,
  ) {}

  static readonly ZERO: Rat = new Rat(0n, 1n);
  static readonly ONE: Rat = new Rat(1n, 1n);

  static int(n: bigint): Rat {
    return new Rat(n, 1n);
  }

  static new(n: bigint, d: bigint): Rat {
    if (d === 0n) throw new Error("division by zero");
    const g = max1(gcd(n, d));
    [n, d] = [n / g, d / g];
    if (d < 0n) {
      n = checked(-n);
      d = checked(-d);
    }
    return new Rat(n, d);
  }

  numer(): bigint {
    return this.n;
  }

  is_int(): boolean {
    return this.d === 1n;
  }

  is_zero(): boolean {
    return this.n === 0n;
  }

  floor(): bigint {
    return div_floor(this.n, this.d);
  }

  ceil(): bigint {
    return div_ceil(this.n, this.d);
  }

  // impl Add for Rat
  add(o: Rat): Rat {
    if (this.d === o.d) {
      return Rat.new(checked(this.n + o.n), this.d);
    }
    return Rat.new(checked(mul(this.n, o.d) + mul(o.n, this.d)), mul(this.d, o.d));
  }

  // impl Sub for Rat
  sub(o: Rat): Rat {
    return this.add(o.neg());
  }

  // impl Neg for Rat
  neg(): Rat {
    return new Rat(checked(-this.n), this.d);
  }

  // impl Mul for Rat
  mul(o: Rat): Rat {
    // Cross-cancel first to keep numbers small.
    const g1 = max1(gcd(this.n, o.d));
    const g2 = max1(gcd(o.n, this.d));
    return Rat.new(mul(this.n / g1, o.n / g2), mul(this.d / g2, o.d / g1));
  }

  // impl Div for Rat
  div(o: Rat): Rat {
    if (o.n === 0n) throw new Error("division by zero");
    return this.mul(Rat.new(o.d, o.n));
  }

  // impl Ord for Rat: -1 / 0 / 1 for Less / Equal / Greater
  cmp(o: Rat): number {
    const a = mul(this.n, o.d);
    const b = mul(o.n, this.d);
    return a < b ? -1 : a > b ? 1 : 0;
  }

  // impl PartialOrd for Rat
  partial_cmp(o: Rat): number {
    return this.cmp(o);
  }

  lt(o: Rat): boolean {
    return this.cmp(o) < 0;
  }
  le(o: Rat): boolean {
    return this.cmp(o) <= 0;
  }
  gt(o: Rat): boolean {
    return this.cmp(o) > 0;
  }
  ge(o: Rat): boolean {
    return this.cmp(o) >= 0;
  }

  /** Ord::max (returns `o` when equal, like Rust). */
  max(o: Rat): Rat {
    return this.cmp(o) > 0 ? this : o;
  }

  /** Ord::min (returns `this` when equal, like Rust). */
  min(o: Rat): Rat {
    return this.cmp(o) <= 0 ? this : o;
  }

  // derive(PartialEq): fields are normalized, so structural equality
  eq(o: Rat): boolean {
    return this.n === o.n && this.d === o.d;
  }

  ne(o: Rat): boolean {
    return !this.eq(o);
  }

  // derive(Clone, Copy)
  clone(): Rat {
    return new Rat(this.n, this.d);
  }

  // impl Display for Rat
  to_string(): string {
    if (this.d === 1n) {
      return `${this.n}`;
    } else {
      return `${this.n}/${this.d}`;
    }
  }

  toString(): string {
    return this.to_string();
  }
}
