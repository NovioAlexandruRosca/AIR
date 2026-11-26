//! Linear Integer Arithmetic.
//!
//! - Atoms `t ⋈ c` are normalised to bounds on a single column: an input
//!   variable, or a slack variable `s = Σ aᵢxᵢ` for a linear form. Integer
//!   coefficients are divided by their gcd and the bound rounded
//!   (`2x - 2y ≤ 1` becomes `x - y ≤ 0`), which is how the GCD test shows up.
//! - `a = b` is defined by axioms over the two bound atoms `a ≤ b`, `a ≥ b`
//!   so that disequalities (non-convex) are handled by the SAT solver.
//! - Consistency of the asserted bounds over ℚ: general Simplex
//!   (Dutertre & de Moura) with Bland's rule; an infeasible row yields the
//!   bounds of that row as the explanation (a Farkas certificate).
//! - Integrality: branch and bound via splitting on demand: the final check
//!   asks the SAT solver to decide a new atom `x ≤ ⌊v⌋`.
//! - Bound propagation: a new bound on a column implies or refutes other
//!   atoms on the same column (`x ≤ 3` implies `x ≤ 5`).
//! - Nelson–Oppen: if both sides of an equality atom are fixed by bounds,
//!   the equality (or disequality) is propagated; `eq_hint` reports
//!   equalities in the current Simplex model to guide arrangement splits.
// (port of src/smt/lia.rs)

import { div_ceil, div_floor, gcd, Rat } from "./rat";
import { BOOL, TermId, Terms, TheoryId, Value } from "./term";
import { Check, Ctx, Implied, Inconsistent, Theory } from "./theory";
import { Lit, lit_is_positive, lit_new, lit_not, lit_to_dimacs, lit_var } from "../lit";
import { json_string } from "../trace";
import { RustErr } from "../util";

const MAX_BRANCHES = 5_000;
const MAX_PIVOTS_PER_CHECK = 100_000;
const SNAPSHOT_COLS = 200;
/// Limits of the per-check record shown by the playground.
const RECORD_CONSTRAINTS = 60;
const RECORD_STEPS = 40;

// i128 range, for the checked arithmetic of the Rust code.
const I128_MAX = (1n << 127n) - 1n;
const I128_MIN = -(1n << 127n);
/** `checked_*` on i128: null when the result leaves the i128 range. */
function checked(x: bigint): bigint | null {
  return x > I128_MAX || x < I128_MIN ? null : x;
}

interface Bound {
  val: Rat;
  lit: Lit;
  level: number;
}

interface Col {
  name: string;
  /** Input (or purification) variable; None for slack columns. */
  term: TermId | null;
  value: Rat;
  lower: Bound | null;
  upper: Bound | null;
  /** Row index when the column is basic. */
  row: number | null;
}

/** `basic = Σ coeffs[j] · x_j` over non-basic columns. (BTreeMap: iterate with `sorted_entries`.) */
interface Row {
  basic: number;
  coeffs: Map<number, Rat>;
}

/** BTreeMap iteration order: entries sorted by key. */
function sorted_entries<V>(m: Map<number, V>): [number, V][] {
  return [...m.entries()].sort((x, y) => x[0] - y[0]);
}

type Atom =
  /** `col ≤ k` (upper) or `col ≥ k` (lower). */
  | { kind: "Bound"; var: number; col: number; upper: boolean; k: bigint }
  /** `a = b`; its meaning is given by axioms. Columns kept when both
   *  sides are variables, for Nelson–Oppen equality propagation. */
  | { kind: "Eq"; var: number; cols: [number, number] | null }
  /** Variable-free atom, fixed by an axiom. */
  | { kind: "Const" };

type Undo =
  | { kind: "Bound"; level: number; col: number; upper: boolean; old: Bound | null }
  | { kind: "Assign"; level: number; atom: number };

function Undo_level(u: Undo): number {
  return u.level;
}

interface PendingProp {
  implied: Lit;
  because: Lit;
  level: number;
}

/// What one check did, for the playground's picture of Simplex: the
/// asserted bounds in order, and after every pivot the values of the input
/// variables and the whole tableau.
class CheckRecord {
  /** (literal, column, is_upper, bound) */
  constraints: [Lit, number, boolean, bigint][] = [];
  steps: RecStep[] = [];
  conflict: Inconsistent | null = null;
  /** basic variable of the row Simplex got stuck on */
  stuck: string | null = null;
}

export interface RecStep {
  note: string;
  /** values of the input columns */
  values: Rat[];
  /** the pivot that led here: (leaving basic variable, entering variable) */
  pivot: [string, string] | null;
  /** rows `basic = expr` */
  rows: [string, string][];
  cols: RecCol[];
}

/** A tableau column at one recorded step: (name, value, lower, upper, basic). */
export type RecCol = [string, Rat, Rat | null, Rat | null, boolean];

interface PendingConflict {
  lits: Lit[];
  why: string;
  level: number;
}

function mk_inconsistent(lits: Lit[], why: string): Inconsistent {
  const c = new Inconsistent();
  c.lits = lits;
  c.why = why;
  return c;
}

function mk_implied(implied: Lit, because: Lit[], why: string): Implied {
  const p = new Implied();
  p.implied = implied;
  p.because = because;
  p.why = why;
  return p;
}

/** `Rat` comparison helpers (Rust operators on Rat). */
const lt = (a: Rat, b: Rat) => a.cmp(b) < 0;
const le = (a: Rat, b: Rat) => a.cmp(b) <= 0;
const gt = (a: Rat, b: Rat) => a.cmp(b) > 0;
const ge = (a: Rat, b: Rat) => a.cmp(b) >= 0;
const req = (a: Rat, b: Rat) => a.eq(b); // derived PartialEq

export class Lia extends Theory {
  me: TheoryId = 0;
  int = 0;
  atoms: Atom[] = [];
  atom_of_var: Map<number, number> = new Map();
  term_of_var: Map<number, TermId> = new Map();
  assigned: (boolean | null)[] = [];
  cols: Col[] = [];
  rows: Row[] = [];
  col_of_term: Map<TermId, number> = new Map();
  /** key: the form `Vec<(usize, i128)>` as "c:a,c:a,..." */
  slack_of_form: Map<string, number> = new Map();
  col_atoms: number[][] = [];
  undo: Undo[] = [];
  pending_conflict: PendingConflict | null = null;
  pending_props: PendingProp[] = [];
  branches = 0;
  changed = true;
  /** Last conflict explanation, for the snapshot. */
  last_event: string | null = null;
  /** Slack column -> its linear form over input columns. */
  form_of_slack: Map<number, [number, bigint][]> = new Map();
  /** Record checks (only while tracing). */
  record = false;
  last_check: CheckRecord | null = null;

  static new(): Lia {
    return new Lia();
  }

  lit_label(terms: Terms, l: Lit): string {
    const t = this.term_of_var.get(lit_var(l));
    if (t !== undefined && lit_is_positive(l)) return terms.display(t);
    if (t !== undefined) return terms.display_neg(t);
    return `literal ${lit_to_dimacs(l)}`;
  }

  col_for_term(terms: Terms, t: TermId): number {
    const c0 = this.col_of_term.get(t);
    if (c0 !== undefined) {
      return c0;
    }
    const c = this.new_col(terms.display(t), t);
    this.col_of_term.set(t, c);
    return c;
  }

  new_col(name: string, term: TermId | null): number {
    this.cols.push({
      name,
      term,
      value: Rat.ZERO,
      lower: null,
      upper: null,
      row: null,
    });
    this.col_atoms.push([]);
    return this.cols.length - 1;
  }

  /// Slack column for `Σ a·x` (form sorted by column).
  slack_for(form: [number, bigint][]): number {
    const key = form.map(([c, a]) => `${c}:${a}`).join(",");
    const s0 = this.slack_of_form.get(key);
    if (s0 !== undefined) {
      return s0;
    }
    let name = "";
    form.forEach(([c, a], i) => {
      const v = this.cols[c].name;
      if (i === 0 && a === 1n) name += v;
      else if (i === 0 && a === -1n) name += `-${v}`;
      else if (i === 0) name += `${a}·${v}`;
      else if (a === 1n) name += ` + ${v}`;
      else if (a === -1n) name += ` - ${v}`;
      else if (a < 0n) name += ` - ${-a}·${v}`;
      else name += ` + ${a}·${v}`;
    });
    // Express the form over the current non-basic columns.
    const coeffs: Map<number, Rat> = new Map();
    let value = Rat.ZERO;
    for (const [c, a0] of form) {
      const a = Rat.int(a0);
      value = value.add(a.mul(this.cols[c].value));
      const r = this.cols[c].row;
      if (r !== null) {
        for (const [m, b] of sorted_entries(this.rows[r].coeffs)) {
          const e = coeffs.get(m) ?? Rat.ZERO;
          coeffs.set(m, e.add(a.mul(b)));
        }
      } else {
        const e = coeffs.get(c) ?? Rat.ZERO;
        coeffs.set(c, e.add(a));
      }
    }
    for (const [m, v] of [...coeffs.entries()]) {
      if (v.is_zero()) coeffs.delete(m);
    }
    const s = this.new_col(name, null);
    this.cols[s].value = value;
    this.cols[s].row = this.rows.length;
    this.rows.push({ basic: s, coeffs });
    this.form_of_slack.set(s, form.map(([c, a]) => [c, a] as [number, bigint]));
    this.slack_of_form.set(key, s);
    return s;
  }

  push_atom(var_: number, atom: Atom): number {
    const idx = this.atoms.length;
    if (atom.kind === "Bound") {
      this.col_atoms[atom.col].push(idx);
    }
    this.atoms.push(atom);
    this.assigned.push(null);
    this.atom_of_var.set(var_, idx);
    return idx;
  }

  // ------------------------------------------------------------ bounds

  conflict(lits: Lit[], why: string, level: number): void {
    if (this.pending_conflict === null) {
      this.pending_conflict = { lits, why, level };
    }
  }

  assert_upper(col: number, v: Rat, lit: Lit, level: number): void {
    const u0 = this.cols[col].upper;
    if (u0 !== null && le(u0.val, v)) {
      return;
    }
    const l = this.cols[col].lower;
    if (l !== null) {
      if (lt(v, l.val)) {
        const why = `${this.cols[col].name} cannot be ≤ ${v.to_string()} and ≥ ${l.val.to_string()} at the same time`;
        this.conflict([lit, l.lit], why, Math.max(level, l.level));
        return;
      }
    }
    const old = this.cols[col].upper;
    this.undo.push({ kind: "Bound", level, col, upper: true, old });
    this.cols[col].upper = { val: v, lit, level };
    if (this.cols[col].row === null && gt(this.cols[col].value, v)) {
      this.update(col, v);
    }
  }

  assert_lower(col: number, v: Rat, lit: Lit, level: number): void {
    const l0 = this.cols[col].lower;
    if (l0 !== null && ge(l0.val, v)) {
      return;
    }
    const u = this.cols[col].upper;
    if (u !== null) {
      if (gt(v, u.val)) {
        const why = `${this.cols[col].name} cannot be ≥ ${v.to_string()} and ≤ ${u.val.to_string()} at the same time`;
        this.conflict([lit, u.lit], why, Math.max(level, u.level));
        return;
      }
    }
    const old = this.cols[col].lower;
    this.undo.push({ kind: "Bound", level, col, upper: false, old });
    this.cols[col].lower = { val: v, lit, level };
    if (this.cols[col].row === null && lt(this.cols[col].value, v)) {
      this.update(col, v);
    }
  }

  /// Atoms on the same column decided by the new bound `col ≤ b` / `col ≥ b`.
  unate(col: number, is_upper: boolean, b: bigint, lit: Lit, level: number, me: number): void {
    for (const j of this.col_atoms[col]) {
      if (j === me || this.assigned[j] !== null) {
        continue;
      }
      const atom = this.atoms[j];
      if (atom.kind === "Bound") {
        const { var: var_, upper, k } = atom;
        let implied: boolean | null = null;
        if (is_upper && upper && b <= k) implied = true;
        else if (is_upper && !upper && b < k) implied = false;
        else if (!is_upper && !upper && b >= k) implied = true;
        else if (!is_upper && upper && b > k) implied = false;
        if (implied !== null) {
          this.pending_props.push({
            implied: lit_new(var_, implied),
            because: lit,
            level,
          });
        }
      }
    }
  }

  // ------------------------------------------------------------ simplex

  update(j: number, v: Rat): void {
    const delta = v.sub(this.cols[j].value);
    for (let r = 0; r < this.rows.length; r++) {
      const a = this.rows[r].coeffs.get(j);
      if (a !== undefined) {
        const b = this.rows[r].basic;
        this.cols[b].value = this.cols[b].value.add(a.mul(delta));
      }
    }
    this.cols[j].value = v;
  }

  pivot_and_update(r: number, j: number, v: Rat): void {
    const i = this.rows[r].basic;
    const a_ij = this.rows[r].coeffs.get(j)!;
    const theta = v.sub(this.cols[i].value).div(a_ij);
    this.cols[i].value = v;
    this.cols[j].value = this.cols[j].value.add(theta);
    for (let k = 0; k < this.rows.length; k++) {
      if (k === r) {
        continue;
      }
      const a = this.rows[k].coeffs.get(j);
      if (a !== undefined) {
        const b = this.rows[k].basic;
        this.cols[b].value = this.cols[b].value.add(a.mul(theta));
      }
    }
    this.pivot(r, j);
  }

  /// Make `j` basic in row `r` (whose basic variable leaves).
  pivot(r: number, j: number): void {
    const i = this.rows[r].basic;
    const coeffs = this.rows[r].coeffs;
    this.rows[r].coeffs = new Map();
    const a = coeffs.get(j);
    if (a === undefined) throw new Error("entering column is in the row");
    coeffs.delete(j);
    // i = a·j + Σ c·k   ⇒   j = (1/a)·i - Σ (c/a)·k
    const neu: Map<number, Rat> = new Map();
    neu.set(i, Rat.ONE.div(a));
    for (const [k, c] of sorted_entries(coeffs)) {
      neu.set(k, c.div(a).neg());
    }
    const neu_sorted = sorted_entries(neu);
    for (let k = 0; k < this.rows.length; k++) {
      if (k === r) {
        continue;
      }
      const rc = this.rows[k].coeffs;
      const c = rc.get(j);
      if (c !== undefined) {
        rc.delete(j);
        for (const [m, b] of neu_sorted) {
          const e = rc.get(m) ?? Rat.ZERO;
          rc.set(m, e.add(c.mul(b)));
        }
        for (const [m, v] of [...rc.entries()]) {
          if (v.is_zero()) rc.delete(m);
        }
      }
    }
    this.rows[r] = { basic: j, coeffs: neu };
    this.cols[i].row = null;
    this.cols[j].row = r;
  }

  /// Bland-rule Simplex. Err(conflict) when the bounds are infeasible over ℚ.
  simplex(terms: Terms): void {
    for (let iter = 0; iter < MAX_PIVOTS_PER_CHECK; iter++) {
      let viol: [number, number, boolean] | null = null;
      for (let r = 0; r < this.rows.length; r++) {
        const row = this.rows[r];
        const i = row.basic;
        const c = this.cols[i];
        const below = c.lower !== null && lt(c.value, c.lower.val);
        const above = c.upper !== null && gt(c.value, c.upper.val);
        if ((below || above) && (viol === null || i < viol[0])) {
          viol = [i, r, below];
        }
      }
      if (viol === null) {
        return;
      }
      const [i, r, below] = viol;
      let entering: number | null = null;
      for (const [j, a] of sorted_entries(this.rows[r].coeffs)) {
        const cj = this.cols[j];
        const can_inc = cj.upper === null || lt(cj.value, cj.upper.val);
        const can_dec = cj.lower === null || gt(cj.value, cj.lower.val);
        const positive = gt(a, Rat.ZERO);
        const ok = below ? (positive && can_inc) || (!positive && can_dec) : (!positive && can_inc) || (positive && can_dec);
        if (ok) {
          entering = j;
          break;
        }
      }
      if (entering === null) {
        const stuck = this.cols[i].name;
        if (this.last_check !== null) {
          this.last_check.stuck = stuck;
        }
        throw new RustErr(this.explain_row(terms, r, below));
      } else {
        const j = entering;
        const target = below ? this.cols[i].lower!.val : this.cols[i].upper!.val;
        const note = this.record
          ? `${this.col_ref(i)} = ${this.cols[i].value.to_string()} but must be ${below ? "≥" : "≤"} ${target.to_string()}: change ${this.cols[j].name} until it is (pivot)`
          : null;
        const pivot: [string, string] = [this.cols[i].name, this.cols[j].name];
        this.pivot_and_update(r, j, target);
        if (note !== null) {
          this.record_step(note, pivot);
        }
      }
    }
  }

  /// Row `r` cannot reach its bound: the bound of the basic variable and
  /// the blocking bounds of the row's variables are jointly infeasible.
  explain_row(terms: Terms, r: number, below: boolean): Inconsistent {
    const row = this.rows[r];
    const i = row.basic;
    const own = below ? this.cols[i].lower! : this.cols[i].upper!;
    const lits: Lit[] = [own.lit];
    let extreme = Rat.ZERO;
    const used: string[] = [];
    for (const [j, a] of sorted_entries(row.coeffs)) {
      const b = below === gt(a, Rat.ZERO) ? this.cols[j].upper! : this.cols[j].lower!;
      extreme = extreme.add(a.mul(b.val));
      if (!lits.includes(b.lit)) {
        lits.push(b.lit);
      }
      used.push(this.lit_label(terms, b.lit));
    }
    const expr = this.row_expr(row.coeffs);
    const why = below
      ? `Simplex row ${this.col_ref(i)} = ${expr}: it must be ≥ ${own.val.to_string()} (from ${this.lit_label(terms, own.lit)}), but with ${used.join(", ")} it is at most ${extreme.to_string()}`
      : `Simplex row ${this.col_ref(i)} = ${expr}: it must be ≤ ${own.val.to_string()} (from ${this.lit_label(terms, own.lit)}), but with ${used.join(", ")} it is at least ${extreme.to_string()}`;
    return mk_inconsistent(lits, why);
  }

  /// Column name, parenthesised when it is a slack (a linear form).
  col_ref(j: number): string {
    if (this.cols[j].term === null) {
      return `(${this.cols[j].name})`;
    } else {
      return this.cols[j].name;
    }
  }

  /// `Σ a·x` with readable signs: `x - (y - z) + 1/2·w`.
  row_expr(coeffs: Map<number, Rat>): string {
    let out = "";
    sorted_entries(coeffs).forEach(([j, a], n) => {
      const neg = lt(a, Rat.ZERO);
      const mag = neg ? a.neg() : a;
      if (n === 0 && neg) out += "-";
      else if (n === 0) {
        // nothing
      } else if (neg) out += " - ";
      else out += " + ";
      if (!req(mag, Rat.ONE)) {
        out += `${mag.to_string()}·`;
      }
      out += this.col_ref(j);
    });
    return out;
  }

  input_values(): Rat[] {
    return this.cols.filter((c) => c.term !== null).map((c) => c.value);
  }

  record_step(note: string, pivot: [string, string] | null): void {
    if (this.last_check === null || this.last_check.steps.length >= RECORD_STEPS) {
      return;
    }
    const values = this.input_values();
    const rows: [string, string][] = this.rows
      .slice(0, SNAPSHOT_COLS)
      .map((r) => [this.cols[r.basic].name, this.row_expr(r.coeffs)] as [string, string]);
    const cols: RecCol[] = this.cols
      .slice(0, SNAPSHOT_COLS)
      .map((c) => [c.name, c.value, c.lower === null ? null : c.lower.val, c.upper === null ? null : c.upper.val, c.row !== null] as RecCol);
    this.last_check.steps.push({ note, values, pivot, rows, cols });
  }

  /// Start the record of a check: the asserted bounds, in assertion order.
  start_record(): void {
    const rec = new CheckRecord();
    for (const u of this.undo) {
      if (u.kind !== "Assign") {
        continue;
      }
      const atom = this.atoms[u.atom];
      const value = this.assigned[u.atom];
      if (atom.kind !== "Bound" || value === null) {
        continue;
      }
      const { var: var_, col, upper, k } = atom;
      let is_upper: boolean;
      let b: bigint;
      if (upper && value) [is_upper, b] = [true, k];
      else if (upper && !value) [is_upper, b] = [false, k + 1n];
      else if (!upper && value) [is_upper, b] = [false, k];
      else [is_upper, b] = [true, k - 1n];
      if (rec.constraints.length < RECORD_CONSTRAINTS) {
        rec.constraints.push([lit_new(var_, value), col, is_upper, b]);
      }
    }
    this.last_check = rec;
    this.record_step("start: the current values", null);
  }

  record_json(terms: Terms, s: { v: string }): void {
    const rec = this.last_check;
    if (rec === null) {
      s.v += "null";
      return;
    }
    s.v += '{"vars":[';
    this.cols
      .filter((c) => c.term !== null)
      .forEach((c, i) => {
        if (i > 0) {
          s.v += ",";
        }
        json_string(s, c.name);
      });
    s.v += '],"constraints":[';
    rec.constraints.forEach(([lit, col, upper, b], i) => {
      if (i > 0) {
        s.v += ",";
      }
      s.v += `{"lit":${lit_to_dimacs(lit)},"label":`;
      json_string(s, this.lit_label(terms, lit));
      s.v += ',"form":[';
      const f = this.form_of_slack.get(col);
      const form: [number, bigint][] = f !== undefined ? f : [[col, 1n]];
      form.forEach(([c, a], j) => {
        if (j > 0) {
          s.v += ",";
        }
        s.v += "[";
        json_string(s, this.cols[c].name);
        s.v += `,${a}]`;
      });
      s.v += `],"op":"${upper ? "<=" : ">="}","bound":${b}}`;
    });
    s.v += '],"steps":[';
    rec.steps.forEach((st, i) => {
      if (i > 0) {
        s.v += ",";
      }
      s.v += '{"note":';
      json_string(s, st.note);
      s.v += ',"values":[';
      st.values.forEach((v, j) => {
        if (j > 0) {
          s.v += ",";
        }
        s.v += `"${v.to_string()}"`;
      });
      s.v += '],"pivot":';
      if (st.pivot !== null) {
        const [leave, enter] = st.pivot;
        s.v += "[";
        json_string(s, leave);
        s.v += ",";
        json_string(s, enter);
        s.v += "]";
      } else {
        s.v += "null";
      }
      s.v += ',"rows":[';
      st.rows.forEach(([basic, expr], j) => {
        if (j > 0) {
          s.v += ",";
        }
        s.v += "[";
        json_string(s, basic);
        s.v += ",";
        json_string(s, expr);
        s.v += "]";
      });
      s.v += '],"cols":[';
      st.cols.forEach(([name, value, lo, hi, basic], j) => {
        if (j > 0) {
          s.v += ",";
        }
        s.v += '{"name":';
        json_string(s, name);
        const opt = (r: Rat | null) => (r === null ? "null" : `"${r.to_string()}"`);
        s.v += `,"value":"${value.to_string()}","lo":${opt(lo)},"hi":${opt(hi)},"basic":${basic}}`;
      });
      s.v += "]}";
    });
    s.v += '],"stuck":';
    if (rec.stuck !== null) json_string(s, rec.stuck);
    else s.v += "null";
    s.v += ',"conflict":';
    if (rec.conflict !== null) {
      const c = rec.conflict;
      s.v += '{"lits":[';
      c.lits.forEach((l, j) => {
        if (j > 0) {
          s.v += ",";
        }
        s.v += `${lit_to_dimacs(l)}`;
      });
      s.v += '],"why":';
      json_string(s, c.why);
      s.v += "}";
    } else {
      s.v += "null";
    }
    s.v += "}";
  }

  fixed(c: number): [Rat, Lit, Lit] | null {
    const col = this.cols[c];
    const l = col.lower;
    const u = col.upper;
    if (l !== null && u !== null && req(l.val, u.val)) return [l.val, l.lit, u.lit];
    return null;
  }

  // ------------------------------------------------------------ Theory

  name(): string {
    return "LIA";
  }

  init(terms: Terms, me: TheoryId): void {
    this.me = me;
    this.int = terms.add_sort("Int", me);
    for (const s of ["+", "-", "*", "<=", "<", ">=", ">"]) {
      terms.add_fun(s, me);
    }
  }

  mk_app(sym: string, args: TermId[], terms: Terms): TermId {
    for (const a of args) {
      if (terms.sort(a) !== this.int) {
        throw new RustErr(`'${sym}' expects Int arguments, got ${terms.display(a)} : ${terms.sort_name(terms.sort(a))}`);
      }
    }
    if ((sym === "+" || sym === "*") && args.length >= 2) return terms.app(sym, args, this.int);
    if (sym === "-" && args.length > 0) {
      // Fold negative numerals: (- 3) is the literal -3.
      if (args.length === 1) {
        const op = terms.node(args[0]).op;
        if (op.kind === "Num") {
          return terms.num(-op._0, this.int);
        }
      }
      return terms.app(sym, args, this.int);
    }
    const cmp = sym === "<=" || sym === "<" || sym === ">=" || sym === ">";
    if (cmp && args.length === 2) return terms.app(sym, args, BOOL);
    if (cmp) throw new RustErr(`'${sym}' takes exactly two arguments`);
    throw new RustErr(`'${sym}' needs at least two arguments`);
  }

  register_atom(var_: number, atom: TermId, ctx: Ctx): void {
    const node = ctx.terms.node(atom);
    let sym: string;
    if (node.op.kind === "App" && node.args.length === 2) sym = node.op._0;
    else throw new RustErr(`LIA cannot interpret ${ctx.terms.display(atom)}`);
    const [a, b] = [node.args[0], node.args[1]];
    const acc: Map<TermId, bigint> = new Map();
    const k = { v: 0n };
    linearize(ctx.terms, a, 1n, acc, k);
    linearize(ctx.terms, b, -1n, acc, k);
    for (const [t, c] of [...acc.entries()]) {
      if (c === 0n) acc.delete(t);
    }
    this.term_of_var.set(var_, atom);
    this.changed = true;
    const label = ctx.terms.display(atom);

    if (sym === "=") {
      if (acc.size === 0) {
        this.push_atom(var_, { kind: "Const" });
        const truth = k.v === 0n;
        ctx.axiom([lit_new(var_, truth)], "LIA", `${label} is ${truth} (no variables)`);
        return;
      }
      const le_t = ctx.terms.app("<=", [a, b], BOOL);
      const ge_t = ctx.terms.app(">=", [a, b], BOOL);
      const lel = lit_new(ctx.atom(le_t), true);
      const gel = lit_new(ctx.atom(ge_t), true);
      const e = lit_new(var_, true);
      const why = `LIA definition: ${label} ⇔ ${ctx.terms.display(le_t)} ∧ ${ctx.terms.display(ge_t)}`;
      ctx.axiom([lit_not(e), lel], "LIA", why);
      ctx.axiom([lit_not(e), gel], "LIA", why);
      ctx.axiom([e, lit_not(lel), lit_not(gel)], "LIA", why);
      let cols: [number, number] | null;
      if (ctx.terms.is_var(a) && ctx.terms.is_var(b)) {
        const ca = this.col_for_term(ctx.terms, a);
        const cb = this.col_for_term(ctx.terms, b);
        cols = [ca, cb];
      } else {
        cols = null;
      }
      this.push_atom(var_, { kind: "Eq", var: var_, cols });
      return;
    }

    // Σ acc·x + k ⋈ 0  ⇒  Σ acc·x ≤ bound (upper) or ≥ bound (lower)
    let upper: boolean;
    let bound: bigint;
    switch (sym) {
      case "<=":
        [upper, bound] = [true, -k.v];
        break;
      case "<":
        [upper, bound] = [true, -k.v - 1n];
        break;
      case ">=":
        [upper, bound] = [false, -k.v];
        break;
      case ">":
        [upper, bound] = [false, -k.v + 1n];
        break;
      default:
        throw new RustErr(`LIA cannot interpret ${label}`);
    }
    if (acc.size === 0) {
      this.push_atom(var_, { kind: "Const" });
      const truth = upper ? 0n <= bound : 0n >= bound;
      ctx.axiom([lit_new(var_, truth)], "LIA", `${label} is ${truth} (no variables)`);
      return;
    }
    // Divide by the gcd of the coefficients and round the bound
    // (sound over the integers: the left side is a multiple of g).
    const acc_sorted = [...acc.entries()].sort((x, y) => x[0] - y[0]);
    const g = acc_sorted.reduce((g, [, c]) => gcd(g, c), 0n);
    const form: [TermId, bigint][] = acc_sorted.map(([t, c]) => [t, c / g]);
    bound = upper ? div_floor(bound, g) : div_ceil(bound, g);
    if (form[0][1] < 0n) {
      for (const e of form) {
        e[1] = -e[1];
      }
      upper = !upper;
      bound = -bound;
    }
    let col: number;
    if (form.length === 1) {
      col = this.col_for_term(ctx.terms, form[0][0]);
    } else {
      const by_col: [number, bigint][] = form.map(([t, c]) => [this.col_for_term(ctx.terms, t), c]);
      by_col.sort((x, y) => (x[0] !== y[0] ? x[0] - y[0] : x[1] < y[1] ? -1 : x[1] > y[1] ? 1 : 0));
      col = this.slack_for(by_col);
    }
    this.push_atom(var_, { kind: "Bound", var: var_, col, upper, k: bound });
  }

  assert_lit(var_: number, value: boolean, level: number): void {
    const idx = this.atom_of_var.get(var_);
    if (idx === undefined) {
      return;
    }
    if (this.assigned[idx] !== null) {
      return;
    }
    this.assigned[idx] = value;
    this.undo.push({ kind: "Assign", level, atom: idx });
    this.changed = true;
    const atom = this.atoms[idx];
    if (atom.kind === "Bound") {
      const { col, upper, k } = atom;
      const lit = lit_new(var_, value);
      // A false atom is the integer complement: ¬(x ≤ k) is x ≥ k+1.
      let is_upper: boolean;
      let b: bigint;
      if (upper && value) [is_upper, b] = [true, k];
      else if (upper && !value) [is_upper, b] = [false, k + 1n];
      else if (!upper && value) [is_upper, b] = [false, k];
      else [is_upper, b] = [true, k - 1n];
      if (is_upper) {
        this.assert_upper(col, Rat.int(b), lit, level);
      } else {
        this.assert_lower(col, Rat.int(b), lit, level);
      }
      this.unate(col, is_upper, b, lit, level, idx);
    }
  }

  backtrack(level: number): void {
    while (this.undo.length > 0) {
      const u = this.undo[this.undo.length - 1];
      if (Undo_level(u) <= level) {
        break;
      }
      this.undo.pop();
      if (u.kind === "Bound") {
        if (u.upper) {
          this.cols[u.col].upper = u.old;
        } else {
          this.cols[u.col].lower = u.old;
        }
      } else {
        this.assigned[u.atom] = null;
      }
    }
    if (this.pending_conflict !== null && this.pending_conflict.level > level) {
      this.pending_conflict = null;
    }
    this.pending_props = this.pending_props.filter((p) => p.level <= level);
    this.changed = true;
  }

  check(ctx: Ctx, final_check: boolean): Check {
    const out = new Check();
    if (this.record) {
      this.start_record();
    }
    if (this.pending_conflict !== null) {
      const c = this.pending_conflict;
      this.last_event = c.why;
      const conflict = mk_inconsistent([...c.lits], c.why);
      if (this.last_check !== null) {
        this.last_check.conflict = mk_inconsistent([...conflict.lits], conflict.why);
      }
      out.conflict = conflict;
      return out;
    }
    try {
      this.simplex(ctx.terms);
    } catch (x) {
      if (!(x instanceof RustErr)) throw x;
      const conflict = x.value as Inconsistent;
      this.last_event = conflict.why;
      if (this.last_check !== null) {
        this.last_check.conflict = mk_inconsistent([...conflict.lits], conflict.why);
      }
      out.conflict = conflict;
      return out;
    }

    const props = this.pending_props;
    this.pending_props = [];
    for (const p of props) {
      const idx = this.atom_of_var.get(lit_var(p.implied))!;
      if (this.assigned[idx] !== null) {
        continue;
      }
      const [from, to] = [this.lit_label(ctx.terms, p.because), this.lit_label(ctx.terms, p.implied)];
      const why =
        from === to
          ? `bound propagation: ${from} — another atom states the same bound, so it gets the same value`
          : `bound propagation: ${from} implies ${to}`;
      out.propagations.push(mk_implied(p.implied, [p.because], why));
    }

    // Nelson–Oppen: equalities between variables fixed by their bounds.
    for (let idx = 0; idx < this.atoms.length; idx++) {
      if (this.assigned[idx] !== null) {
        continue;
      }
      const atom = this.atoms[idx];
      if (atom.kind === "Eq" && atom.cols !== null) {
        const var_ = atom.var;
        const [ca, cb] = atom.cols;
        const fa = this.fixed(ca);
        const fb = this.fixed(cb);
        if (fa !== null && fb !== null) {
          const [va, la, ua] = fa;
          const [vb, lb, ub] = fb;
          let because = dedup([la, ua, lb, ub]);
          because.sort((x, y) => x - y);
          because = dedup(because);
          const why = `${this.cols[ca].name} and ${this.cols[cb].name} are fixed to ${va.to_string()} and ${vb.to_string()} by their bounds, so ${this.lit_label(ctx.terms, lit_new(var_, req(va, vb)))}`;
          out.propagations.push(mk_implied(lit_new(var_, req(va, vb)), because, why));
        }
      }
    }
    if (out.propagations.length > 0 || !final_check) {
      return out;
    }

    // Branch and bound: the first input column with a fractional value.
    const frac = this.cols.findIndex((c) => c.term !== null && !c.value.is_int());
    if (frac !== -1) {
      const c = frac;
      if (this.branches >= MAX_BRANCHES) {
        out.unknown = `LIA: gave up after ${MAX_BRANCHES} branch-and-bound splits`;
        return out;
      }
      this.branches += 1;
      const v = this.cols[c].value;
      const t = this.cols[c].term!;
      const k = ctx.terms.num(v.floor(), this.int);
      const atom = ctx.terms.app("<=", [t, k], BOOL);
      const lit = ctx.lit(atom, true);
      const why = `branch and bound: the rational solution has ${this.cols[c].name} = ${v.to_string()}, which is not an integer; every integer solution has ${this.cols[c].name} ≤ ${v.floor()} or ${this.cols[c].name} ≥ ${v.ceil()}`;
      this.last_event = why;
      out.split = [lit, why];
    }
    return out;
  }

  eq_hint(a: TermId, b: TermId): boolean | null {
    const ca = this.col_of_term.get(a);
    if (ca === undefined) return null;
    const cb = this.col_of_term.get(b);
    if (cb === undefined) return null;
    return req(this.cols[ca].value, this.cols[cb].value);
  }

  model(_terms: Terms, known: Map<TermId, Value>): void {
    for (const c of this.cols) {
      if (c.term !== null) {
        known.set(c.term, { kind: "Int", _0: c.value.floor() });
      }
    }
  }

  snapshot(terms: Terms): string {
    const s = { v: '{"cols":[' };
    this.cols.slice(0, SNAPSHOT_COLS).forEach((c, i) => {
      if (i > 0) {
        s.v += ",";
      }
      s.v += '{"name":';
      json_string(s, c.name);
      s.v += `,"slack":${c.term === null},"basic":${c.row !== null},"value":"${c.value.to_string()}","int":${c.value.is_int()}`;
      if (c.lower !== null) {
        s.v += `,"lo":"${c.lower.val.to_string()}","loLit":${lit_to_dimacs(c.lower.lit)}`;
      } else {
        s.v += ',"lo":null,"loLit":null';
      }
      if (c.upper !== null) {
        s.v += `,"hi":"${c.upper.val.to_string()}","hiLit":${lit_to_dimacs(c.upper.lit)}`;
      } else {
        s.v += ',"hi":null,"hiLit":null';
      }
      s.v += "}";
    });
    s.v += '],"rows":[';
    this.rows.slice(0, SNAPSHOT_COLS).forEach((r, i) => {
      if (i > 0) {
        s.v += ",";
      }
      const expr = this.row_expr(r.coeffs);
      s.v += '{"basic":';
      json_string(s, this.cols[r.basic].name);
      s.v += ',"expr":';
      json_string(s, expr);
      s.v += "}";
    });
    s.v += `],"branches":${this.branches},"check":`;
    this.record_json(terms, s);
    s.v += ',"last":';
    if (this.last_event !== null) json_string(s, this.last_event);
    else s.v += "null";
    s.v += "}";
    return s.v;
  }

  eval_app(sym: string, args: Value[], _terms: Terms): Value | null {
    const a: bigint[] = [];
    for (const v of args) {
      if (v.kind === "Int") a.push(v._0);
      else return null;
    }
    const fold = (init: bigint, xs: bigint[], f: (s: bigint, x: bigint) => bigint): bigint | null => {
      let s = init;
      for (const x of xs) {
        const r = checked(f(s, x));
        if (r === null) return null;
        s = r;
      }
      return s;
    };
    let r: bigint | null;
    switch (sym) {
      case "+":
        r = fold(0n, a, (s, x) => s + x);
        return r === null ? null : { kind: "Int", _0: r };
      case "*":
        r = fold(1n, a, (s, x) => s * x);
        return r === null ? null : { kind: "Int", _0: r };
      case "-":
        if (a.length === 1) {
          r = checked(-a[0]);
        } else {
          r = fold(a[0], a.slice(1), (s, x) => s - x);
        }
        return r === null ? null : { kind: "Int", _0: r };
      case "<=":
        return { kind: "Bool", _0: a[0] <= a[1] };
      case "<":
        return { kind: "Bool", _0: a[0] < a[1] };
      case ">=":
        return { kind: "Bool", _0: a[0] >= a[1] };
      case ">":
        return { kind: "Bool", _0: a[0] > a[1] };
      default:
        return null;
    }
  }

  default_value(_sort: number, _terms: Terms): Value | null {
    return { kind: "Int", _0: 0n };
  }

  take_changed(): boolean {
    const c = this.changed;
    this.changed = false;
    return c;
  }

  set_recording(on: boolean): void {
    this.record = on;
    if (!on) {
      this.last_check = null;
    }
  }
}

/** `Vec::dedup`: drop consecutive duplicates. */
function dedup(xs: Lit[]): Lit[] {
  return xs.filter((x, i) => i === 0 || xs[i - 1] !== x);
}

/// Integer value of a variable-free term, if it is one.
function const_value(terms: Terms, t: TermId): bigint | null {
  const n = terms.node(t);
  const op = n.op;
  if (op.kind === "Num") return op._0;
  if (op.kind === "App") {
    const vals: bigint[] = [];
    for (const a of n.args) {
      const v = const_value(terms, a);
      if (v === null) return null;
      vals.push(v);
    }
    const fold = (init: bigint, xs: bigint[], f: (s: bigint, x: bigint) => bigint): bigint | null => {
      let s = init;
      for (const x of xs) {
        const r = checked(f(s, x));
        if (r === null) return null;
        s = r;
      }
      return s;
    };
    switch (op._0) {
      case "+":
        return fold(0n, vals, (s, v) => s + v);
      case "*":
        return fold(1n, vals, (s, v) => s * v);
      case "-":
        if (vals.length === 1) return checked(-vals[0]);
        return fold(vals[0], vals.slice(1), (s, v) => s - v);
      default:
        return null;
    }
  }
  return null;
}

/// Add `c · t` to the linear form `acc + k`.
/// (`acc` is a BTreeMap in Rust; callers sort its keys when iterating.)
function linearize(terms: Terms, t: TermId, c: bigint, acc: Map<TermId, bigint>, k: { v: bigint }): void {
  const ovf = (x: bigint | null): bigint => {
    if (x === null) throw new RustErr("integer overflow while normalising a linear term");
    return x;
  };
  const n = terms.node(t);
  const op = n.op;
  if (op.kind === "Num") {
    k.v = ovf(checked(k.v + ovf(checked(c * op._0))));
  } else if (op.kind === "App" && op._0 === "+") {
    for (const a of n.args) {
      linearize(terms, a, c, acc, k);
    }
  } else if (op.kind === "App" && op._0 === "-") {
    if (n.args.length === 1) {
      linearize(terms, n.args[0], -c, acc, k);
    } else {
      linearize(terms, n.args[0], c, acc, k);
      for (const a of n.args.slice(1)) {
        linearize(terms, a, -c, acc, k);
      }
    }
  } else if (op.kind === "App" && op._0 === "*") {
    let factor = c;
    let var_part: TermId | null = null;
    for (const a of n.args) {
      const v = const_value(terms, a);
      if (v !== null) factor = ovf(checked(factor * v));
      else if (var_part === null) var_part = a;
      else throw new RustErr(`non-linear term ${terms.display(t)}: LIA only allows multiplication by constants`);
    }
    if (var_part === null) k.v = ovf(checked(k.v + factor));
    else linearize(terms, var_part, factor, acc, k);
  } else {
    // Constants, and alien terms (which purification replaced by
    // constants anyway), are columns.
    const e = acc.get(t) ?? 0n;
    acc.set(t, ovf(checked(e + c)));
  }
}
