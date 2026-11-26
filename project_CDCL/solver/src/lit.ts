// Literal representation (port of src/lit.rs).
//
// Variables are 0-based internally (`x1` in DIMACS is var 0). A literal is
// packed as `2 * var + sign`, where sign 0 = positive and 1 = negative, so
// negation is a single XOR and literals can index watch lists directly.
// In TypeScript a Lit is just that number.

export type Lit = number;

export function lit_new(v: number, positive: boolean): Lit {
  return (v << 1) | (positive ? 0 : 1);
}

/** Build from a non-zero DIMACS integer (`3` -> x3, `-3` -> ¬x3). */
export function lit_from_dimacs(x: number): Lit {
  return lit_new(Math.abs(x) - 1, x > 0);
}

export function lit_to_dimacs(l: Lit): number {
  const v = lit_var(l) + 1;
  return lit_is_positive(l) ? v : -v;
}

export function lit_var(l: Lit): number {
  return l >> 1;
}

export function lit_is_positive(l: Lit): boolean {
  return (l & 1) === 0;
}

/** `!l` in Rust. */
export function lit_not(l: Lit): Lit {
  return l ^ 1;
}

/** Dense index for literal-indexed arrays (watch lists, counters). */
export function lit_index(l: Lit): number {
  return l;
}
