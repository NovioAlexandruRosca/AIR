// Small linear-algebra helpers for drawing LIA checks in the plane:
// inequalities Σ aᵢ·vᵢ ≤ c, Fourier–Motzkin elimination of the variables
// that are not on the picture, and half-plane clipping of polygons.

export type Pt = [number, number];

export interface Ineq {
  /** Σ a[v]·v ≤ c */
  a: Map<string, number>;
  c: number;
}

export const parseRat = (s: string): number => {
  const [n, d] = s.split("/");
  return Number(n) / (d ? Number(d) : 1);
};

export function toIneq(form: [string, number][], op: "<=" | ">=", bound: number): Ineq {
  const s = op === "<=" ? 1 : -1;
  return { a: new Map(form.map(([v, k]) => [v, s * k])), c: s * bound };
}

const gcd = (a: number, b: number): number => (b === 0 ? Math.abs(a) : gcd(b, a % b));

/** Fourier–Motzkin: combine p (coefficient of v > 0) with n (< 0) so v cancels. */
export function combine(p: Ineq, n: Ineq, v: string): Ineq {
  const kp = p.a.get(v)!;
  const kn = -n.a.get(v)!;
  const a = new Map<string, number>();
  for (const [x, k] of p.a) a.set(x, (a.get(x) ?? 0) + kn * k);
  for (const [x, k] of n.a) a.set(x, (a.get(x) ?? 0) + kp * k);
  a.delete(v);
  for (const [x, k] of [...a]) if (k === 0) a.delete(x);
  let c = kn * p.c + kp * n.c;
  // keep small integers: divide by the gcd (over ℤ the bound may be rounded down)
  const g = [...a.values()].reduce((g, k) => gcd(g, Math.round(k)), 0);
  if (g > 1) {
    for (const [x, k] of a) a.set(x, k / g);
    c = Math.floor(c / g);
  }
  return { a, c };
}

/** "x − y ≥ 1": the first coefficient made positive, ⇔ readable. */
export function ineqText(q: Ineq, order?: string[]): string {
  const vars = [...q.a.keys()].sort((x, y) => (order ? order.indexOf(x) - order.indexOf(y) : x.localeCompare(y)));
  if (!vars.length) return `0 ≤ ${q.c}`;
  const flip = q.a.get(vars[0])! < 0;
  const s = flip ? -1 : 1;
  let out = "";
  vars.forEach((v, i) => {
    const k = s * q.a.get(v)!;
    const mag = Math.abs(k);
    const term = (mag === 1 ? "" : `${mag}·`) + v;
    out += i === 0 ? (k < 0 ? "−" : "") + term : (k < 0 ? " − " : " + ") + term;
  });
  const c = s * q.c;
  return `${out} ${flip ? "≥" : "≤"} ${c < 0 ? "−" + -c : c}`;
}

/** Keep the part of a convex polygon with a·x + b·y ≤ c (Sutherland–Hodgman). */
export function clip(poly: Pt[], a: number, b: number, c: number): Pt[] {
  const out: Pt[] = [];
  const inside = (p: Pt) => a * p[0] + b * p[1] <= c + 1e-9;
  for (let i = 0; i < poly.length; i++) {
    const p = poly[i];
    const q = poly[(i + 1) % poly.length];
    const ip = inside(p);
    const iq = inside(q);
    if (ip) out.push(p);
    if (ip !== iq) {
      const fp = a * p[0] + b * p[1] - c;
      const fq = a * q[0] + b * q[1] - c;
      const t = fp / (fp - fq);
      out.push([p[0] + t * (q[0] - p[0]), p[1] + t * (q[1] - p[1])]);
    }
  }
  return out;
}

/** Intersection of two lines a·x + b·y = c, if they are not parallel. */
export function meet(l1: [number, number, number], l2: [number, number, number]): Pt | null {
  const [a1, b1, c1] = l1;
  const [a2, b2, c2] = l2;
  const det = a1 * b2 - a2 * b1;
  if (Math.abs(det) < 1e-12) return null;
  return [(c1 * b2 - c2 * b1) / det, (a1 * c2 - a2 * c1) / det];
}

export const area = (poly: Pt[]): number => {
  let s = 0;
  for (let i = 0; i < poly.length; i++) {
    const [x1, y1] = poly[i];
    const [x2, y2] = poly[(i + 1) % poly.length];
    s += x1 * y2 - x2 * y1;
  }
  return Math.abs(s) / 2;
};

/** Display a number: integers plain, otherwise a short decimal. */
export const num = (x: number) => (Number.isInteger(x) ? String(x) : String(Math.round(x * 100) / 100));
