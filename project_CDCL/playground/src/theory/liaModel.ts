// One LIA check as pictures: the constraints as lines (2 variables) or
// planes (3 variables), Fourier–Motzkin elimination of any further variable,
// and Simplex's moves with its tableau. Both the plane and the 3D view draw
// the frames built here.

import type { LiaCheck } from "../api";
import { litText, type Labels } from "../model";
import { combine, ineqText, meet, num, parseRat, toIneq, type Ineq } from "./linear";

/** A constraint of the picture: an input literal, or one derived by eliminating a variable. */
export interface Item extends Ineq {
  id: number;
  /** literal it comes from (input constraints) */
  lit?: number;
  /** as written in the formula, e.g. "x + 1 > 0" */
  label: string;
  /** normalised, e.g. "x ≥ 0" */
  text: string;
  /** only uses the variables on the axes */
  flat: boolean;
  derived: boolean;
  parents: number[];
  eliminated?: string;
}

/** What one step shows. */
export interface Frame {
  title: string;
  text: string;
  /** constraints drawn (each rules out its red side) */
  drawn: number[];
  /** the constraint this step adds */
  fresh?: number;
  /** Simplex's candidate point, and where it has been */
  point?: number[];
  path?: number[][];
  final?: "unsat" | "sat";
  /** Simplex frames: index into check.steps (the tableau shown) */
  simplex?: number;
}

export interface LiaModel {
  items: Item[];
  /** the variables on the axes: 2 (the second may be "" when only one occurs) or 3 */
  axes: string[];
  geometry: Frame[];
  simplex: Frame[];
  /** constraints to blame in the conflict (red at the end) */
  conflictIds: Set<number>;
  /** first geometry step that mentions each constraint */
  firstSeen: Map<number, number>;
  /** world box: [lo, hi] per axis */
  box: [number, number][];
}

/** Position of variable `v` as a whole word in `s` (or the end). */
function pos(s: string, v: string): number {
  const word = /[\w']/;
  for (let i = s.indexOf(v); i >= 0; i = s.indexOf(v, i + 1)) {
    if ((i === 0 || !word.test(s[i - 1])) && !word.test(s[i + v.length] ?? "")) return i;
  }
  return s.length;
}

const EXPLAIN_COLOURS =
  " It rules out the red side. Green is what every literal so far still allows; where several literals rule a point out, the red gets darker.";

export function buildLia(check: LiaCheck, L: Labels): LiaModel | null {
  if (!check.constraints.length) return null;
  const used = new Set<string>();
  check.constraints.forEach((c) => c.form.forEach(([v]) => used.add(v)));
  const conflictLits = new Set(check.conflict?.lits ?? []);

  // axes: the variables that occur most, preferring the conflict's; three of them give a 3D view
  const dims = used.size >= 3 ? 3 : 2;
  const score = new Map<string, number>();
  check.constraints.forEach((c) => c.form.forEach(([v]) => score.set(v, (score.get(v) ?? 0) + 1 + (conflictLits.has(c.lit) ? 10 : 0))));
  const ranked = [...used].sort((a, b) => score.get(b)! - score.get(a)! || check.vars.indexOf(a) - check.vars.indexOf(b));
  const axes = ranked.slice(0, dims).sort((a, b) => check.vars.indexOf(a) - check.vars.indexOf(b));
  while (axes.length < 2) axes.push("");
  const onAxes = (q: Ineq) => [...q.a.keys()].every((v) => axes.includes(v));
  const order = [...check.vars];
  const space = dims === 3 ? `the ${axes.join("–")} space` : `the ${axes[0]}–${axes[1]} plane`;
  const shape = dims === 3 ? "plane" : "line";

  const items: Item[] = check.constraints.map((c, id) => {
    const q = toIneq(c.form, c.op, c.bound);
    const label = litText(L, c.lit);
    // variables in the order the literal mentions them: z > y stays "z − y ≥ 1"
    const mine = [...order].sort((a, b) => pos(label, a) - pos(label, b));
    return { ...q, id, lit: c.lit, label, text: ineqText(q, mine), flat: onAxes(q), derived: false, parents: [] };
  });

  const geometry: Frame[] = [];
  const drawn: number[] = [];
  const firstSeen = new Map<number, number>();
  geometry.push({
    title: "What LIA receives",
    text:
      `The theory solver gets the arithmetic literals of the context (${items.length}). ` +
      (axes[1]
        ? `Each one is a ${shape} in ${space}: one side of it is allowed, the other is ruled out.`
        : `Only ${axes[0]} occurs, so each literal allows one side of a point on the line.`) +
      " Before any literal, every point is allowed (green). The context is LIA-satisfiable exactly when some integer point stays green.",
    drawn: [],
  });
  items.forEach((it, i) => {
    if (it.flat) drawn.push(i);
    firstSeen.set(i, geometry.length);
    const rewritten = it.text.replace(/\s/g, "") !== it.label.replace(/\s/g, "");
    const negated = it.label.startsWith("¬");
    const strict = /[<>]/.test(it.label);
    const meaning = !rewritten
      ? `${it.label}.`
      : negated
        ? `${it.label} says that ${it.label.replace(/^¬\(?|\)$/g, "")} is false, so ${it.text}.`
        : strict
          ? `Over the integers ${it.label} is the same as ${it.text}: a strict inequality just moves the bound by one.`
          : `${it.label} is ${it.text}.`;
    geometry.push({
      title: `Literal ${i + 1}: ${it.label}`,
      text:
        meaning +
        (it.flat
          ? EXPLAIN_COLOURS
          : ` It also uses ${[...it.a.keys()].filter((v) => !axes.includes(v)).join(", ")}, which is not on this picture; it is used when that variable is eliminated below.`),
      drawn: [...drawn],
      fresh: it.flat ? i : undefined,
    });
  });

  // Fourier–Motzkin: eliminate every variable that is not on an axis
  let pool = items.map((it) => it.id);
  for (const v of [...used].filter((v) => !axes.includes(v))) {
    const up = pool.filter((i) => (items[i].a.get(v) ?? 0) > 0);
    const down = pool.filter((i) => (items[i].a.get(v) ?? 0) < 0);
    const rest = pool.filter((i) => !items[i].a.has(v));
    const made: number[] = [];
    for (const p of up)
      for (const n of down) {
        if (items.length > 80) break;
        const q = combine(items[p], items[n], v);
        const it: Item = { ...q, id: items.length, label: "", text: ineqText(q, order), flat: onAxes(q), derived: true, parents: [p, n], eliminated: v };
        items.push(it);
        made.push(it.id);
        if (it.flat) drawn.push(it.id);
        firstSeen.set(it.id, geometry.length);
        geometry.push({
          title: `Eliminate ${v}`,
          text:
            `${items[p].text} and ${items[n].text} bound ${v} from both sides, so they can only both hold if ${it.text}. ` +
            `This is Fourier–Motzkin elimination: ${v} disappears, and the new ${shape} (purple) can be drawn.` +
            (q.a.size === 0 && q.c < 0 ? ` It says 0 ≤ ${q.c}, which is false on its own.` : ""),
          drawn: [...drawn],
          fresh: it.flat ? it.id : undefined,
        });
      }
    if (!up.length || !down.length) {
      geometry.push({
        title: `Eliminate ${v}`,
        text: `${v} is bounded on ${up.length ? "one side only (from above)" : down.length ? "one side only (from below)" : "no side"}, so it can always be chosen to fit: the constraints with ${v} are dropped from the picture.`,
        drawn: [...drawn],
      });
    }
    pool = [...rest, ...made];
  }

  const conflictIds = new Set(items.filter((it) => it.lit !== undefined && conflictLits.has(it.lit)).map((it) => it.id));
  // derived constraints whose parents are all blamed share the blame
  for (const it of items) if (it.derived && it.parents.every((p) => conflictIds.has(p))) conflictIds.add(it.id);

  const proj = (vals: string[]) => axes.map((name) => (name ? parseRat(vals[check.vars.indexOf(name)] ?? "0") : 0));
  const at = (vals: string[]) =>
    check.vars
      .filter((v) => used.has(v))
      .map((v) => `${v} = ${num(parseRat(vals[check.vars.indexOf(v)]))}`)
      .join(", ");
  const lastValues = check.steps[check.steps.length - 1]?.values;
  const blamedLits = check.constraints.filter((c) => conflictLits.has(c.lit)).map((c) => c.lit);
  const lemma = "(" + blamedLits.map((l) => litText(L, -l)).join(" ∨ ") + ")";

  if (check.conflict) {
    geometry.push({
      title: "LIA-unsatisfiable",
      text:
        `No point is allowed by every literal: nothing green is left. ${blamedLits.map((l) => litText(L, l)).join(", ")} cannot hold together ` +
        `(red lines), so LIA answers "unsat" with exactly these literals; the SAT solver adds the lemma ${lemma}: at least one of them must be false.`,
      drawn: [...drawn],
      final: "unsat",
    });
  } else {
    geometry.push({
      title: "Consistent",
      text: `Some points stay green. Simplex found one of them: ${lastValues ? at(lastValues) : "—"} (orange). LIA accepts the context; the dots in the green part are its integer solutions.`,
      drawn: [...drawn],
      point: lastValues ? proj(lastValues) : undefined,
      final: "sat",
    });
  }

  // Simplex: the candidate point and the tableau after every pivot
  const simplex: Frame[] = [];
  const path: number[][] = [];
  check.steps.forEach((s, i) => {
    const p = proj(s.values);
    path.push(p);
    const next = check.steps[i + 1]?.pivot;
    const upcoming = next
      ? ` Next: ${next[0]} is outside its bounds (red row), so Simplex swaps it with ${next[1]} (blue column) and changes ${next[1]} until ${next[0]} is back at its bound.`
      : "";
    simplex.push({
      title: i === 0 ? "Simplex: the start" : `Simplex: pivot ${i}`,
      text:
        (i === 0
          ? `Simplex keeps one candidate point and repairs it. The tableau defines every sum (a slack such as x + y) by a row in terms of the other variables; ` +
            `a literal only puts a bound on one variable. It starts at ${at(s.values)} (orange).`
          : `${s.note.replace(" (pivot)", "")}. After the pivot the point is at ${at(s.values)}.`) + upcoming,
      drawn: [...drawn],
      point: p,
      path: path.slice(),
      simplex: i,
    });
  });
  const lastIdx = check.steps.length - 1;
  if (check.conflict) {
    simplex.push({
      title: "Simplex is stuck",
      text:
        (check.stuck
          ? `${check.stuck} is outside its bounds, but every variable in its row is already at the bound that would help: no pivot can repair it. `
          : "The bounds contradict each other directly, without any pivot. ") +
        `${cap(check.conflict.why)}. So LIA answers "unsat" and the SAT solver adds the lemma ${lemma}.`,
      drawn: [...drawn],
      point: path[path.length - 1],
      path: path.slice(),
      final: "unsat",
      simplex: lastIdx,
    });
  } else if (lastValues) {
    simplex.push({
      title: "Every bound holds",
      text: `No variable is outside its bounds any more, so the point ${at(lastValues)} satisfies every literal: LIA accepts the context.`,
      drawn: [...drawn],
      point: path[path.length - 1],
      path: path.slice(),
      final: "sat",
      simplex: lastIdx,
    });
  }

  return { items, axes, geometry, simplex, conflictIds, firstSeen, box: viewBox(items, drawn, axes, path) };
}

const cap = (s: string) => s.charAt(0).toUpperCase() + s.slice(1);

/** A box around the interesting points: corners of the drawn constraints, the path, the origin. */
function viewBox(items: Item[], drawn: number[], axes: string[], path: number[][]): [number, number][] {
  const d = axes.filter(Boolean).length;
  const rows = drawn.map((i) => [...axes.map((v) => (v ? items[i].a.get(v) ?? 0 : 0)), items[i].c]);
  const cand: number[][] = [axes.map(() => 0), ...path];
  for (const r of rows) {
    const n2 = r.slice(0, -1).reduce((s, k) => s + k * k, 0);
    if (n2) cand.push(r.slice(0, -1).map((k) => (r[r.length - 1] * k) / n2));
  }
  if (d <= 2) {
    for (let i = 0; i < rows.length; i++)
      for (let j = i + 1; j < rows.length; j++) {
        const p = meet(rows[i] as [number, number, number], rows[j] as [number, number, number]);
        if (p && Math.abs(p[0]) < 1e6 && Math.abs(p[1]) < 1e6) cand.push(p);
      }
  } else {
    for (let i = 0; i < rows.length; i++)
      for (let j = i + 1; j < rows.length; j++)
        for (let k = j + 1; k < rows.length; k++) {
          const p = solve3(rows[i], rows[j], rows[k]);
          if (p && p.every((x) => Math.abs(x) < 1e6)) cand.push(p);
        }
  }
  const n = axes.length;
  const lo = Array.from({ length: n }, (_, k) => Math.min(...cand.map((p) => p[k] ?? 0)));
  const hi = Array.from({ length: n }, (_, k) => Math.max(...cand.map((p) => p[k] ?? 0)));
  const real = Array.from({ length: n }, (_, k) => k < d);
  const s = Math.max(8, ...lo.map((l, k) => (real[k] ? hi[k] - l + 4 : 0)));
  return lo.map((l, k) => {
    if (!real[k]) return [-3, 3];
    const c = (l + hi[k]) / 2;
    return [Math.floor(c - s / 2), Math.ceil(c + s / 2)];
  });
}

/** Intersection point of three planes a·x + b·y + c·z = d (Cramer's rule). */
export function solve3(p: number[], q: number[], r: number[]): number[] | null {
  const det = (m: number[][]) =>
    m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1]) - m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0]) + m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0]);
  const A = [p.slice(0, 3), q.slice(0, 3), r.slice(0, 3)];
  const D = det(A);
  if (Math.abs(D) < 1e-12) return null;
  const b = [p[3], q[3], r[3]];
  return [0, 1, 2].map((k) => det(A.map((row, i) => row.map((v, j) => (j === k ? b[i] : v)))) / D);
}
