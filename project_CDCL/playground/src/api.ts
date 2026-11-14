// Types of the JSON returned by `POST /api/playground` (see src/smt/mod.rs)
// and the request helper.

export type Lit = number; // DIMACS literal: +v / -v, v is 1-based

export interface VarInfo {
  var: number;
  label: string;
  neg: string;
  kind: "atom" | "definition" | "interface" | "theory" | "bool" | "aux" | "true";
  theories: string[];
  def: string | null;
}

export type FormulaNode =
  | { const: boolean }
  | { atom: number; label: string }
  | { op: "and" | "or" | "not" | "=>" | "xor" | "ite" | "iff"; args: FormulaNode[] };

export type TraceEvent =
  | { type: "Decide"; lit: Lit; level: number; origin?: { by: string; why: string } }
  | { type: "Propagate"; lit: Lit; reason: number; level: number }
  | { type: "Conflict"; clause: number; level: number }
  | { type: "Resolve" }
  | { type: "Learn"; clause: number; lits: Lit[]; uip: Lit; backjump_level: number }
  | { type: "Backjump"; from: number; to: number; unassigned: Lit[] }
  | { type: "TheoryClause"; clause: number; lits: Lit[]; kind: "explanation" | "conflict" | "lemma" | "axiom"; theory: string; why: string }
  | { type: "NewVar"; var: number; label: string; neg: string; kind: VarInfo["kind"]; theories: string }
  | { type: "Theory"; theory: string; kind: string; message: string; lits: Lit[]; data: unknown }
  | { type: "Result"; status: string; model: Lit[] };

export interface TrailEntry {
  lit: Lit;
  level: number;
  reason: number | null;
}

/** One LIA check: the asserted bounds in order and Simplex's moves. */
export interface LiaCheck {
  vars: string[];
  /** Σ form ⋈ bound, after integer normalisation (x + 1 > 0 is x ≥ 0) */
  constraints: { lit: Lit; label: string; form: [string, number][]; op: "<=" | ">="; bound: number }[];
  /** after each step: values of `vars` (rationals as "p/q"), the pivot that led
   * here (leaving, entering) and the whole tableau */
  steps: {
    note: string;
    values: string[];
    pivot: [string, string] | null;
    rows: [string, string][];
    cols: { name: string; value: string; lo: string | null; hi: string | null; basic: boolean }[];
  }[];
  /** the basic variable whose row Simplex got stuck on */
  stuck: string | null;
  conflict: { lits: Lit[]; why: string } | null;
}

export interface LiaSnapshot {
  cols: { name: string; slack: boolean; basic: boolean; value: string; int: boolean; lo: string | null; loLit: Lit | null; hi: string | null; hiLit: Lit | null }[];
  rows: { basic: string; expr: string }[];
  branches: number;
  check: LiaCheck | null;
  last: string | null;
}

export interface DtSnapshot {
  classes: { members: string[]; sort: string; ctor: string | null; excluded: string[] }[];
  diseqs: [string, string][];
  merges: number;
  /** the congruence-closure graph: terms with their arguments */
  nodes?: { term: string; kind: "leaf" | "ctor" | "sel"; children: number[] }[];
  /** merges in order, with the rule that made them */
  history?: { a: number; b: number; rule: string; lits: Lit[] }[];
  diseqNodes?: [number, number, Lit][];
  datatypes: { name: string; ctors: string; finite: boolean }[];
  last: string | null;
}

export interface PlaygroundResponse {
  num_vars: number;
  num_original: number;
  clauses: Lit[][];
  events: TraceEvent[];
  formula?: FormulaNode[];
  smt?: {
    theories: string[];
    assertions: string[];
    purified: string[];
    definitions: string[];
    fresh: string[];
    shared: { name: string; theories: string[] }[];
    interface: { x: string; y: string; var: number }[];
    vars: VarInfo[];
    clause_origin: string[];
    model: { name: string; sort: string; value: string }[];
  };
  replay: {
    outcome: "open" | "conflict" | "sat" | "unsat" | "split" | "units" | "unknown";
    /** for "units": the unit clauses waiting, each with the literal it forces */
    units: { clause: number; lit: Lit }[];
    applied: number;
    conflict: number | null;
    skipped: [number, boolean][];
    split: { lit: Lit; by: string; why: string } | null;
    learned: Lit[] | null;
    finish_from: number | null;
    note: string | null;
    trail: TrailEntry[];
    db: Lit[][];
    /** variables still to decide (open literals of unsatisfied problem clauses) */
    open: number[];
    num_vars: number;
    theories: { LIA?: LiaSnapshot; DT?: DtSnapshot } | null;
  };
  error?: string;
}

export interface Request {
  src: string;
  decisions: Lit[];
  /** unit clauses you chose to propagate, after `after` decisions */
  picks?: Pick[];
  lemmas: Lit[][];
  theoryPropagation: boolean;
  finish: boolean;
}

export interface Pick {
  after: number;
  lit: Lit;
}

/** Decisions with the unit-clause picks in between (`u<lit>`), in order. */
function actionList(decisions: Lit[], picks: Pick[]): string[] {
  const out: string[] = [];
  for (let i = 0; i <= decisions.length; i++) {
    for (const p of picks) if (p.after === i) out.push(`u${p.lit}`);
    if (i < decisions.length) out.push(String(decisions[i]));
  }
  return out;
}

export async function playground(req: Request): Promise<PlaygroundResponse> {
  const opts = [req.theoryPropagation ? "" : "no-theory-propagation", req.finish ? "finish" : ""].join(" ");
  const body =
    `DECISIONS ${actionList(req.decisions, req.picks ?? []).join(" ")}\n` +
    `LEMMAS ${req.lemmas.map((c) => c.join(" ") + " 0").join(" ")}\n` +
    `OPTIONS ${opts}\n${req.src}`;
  const res = await fetch("api/playground", { method: "POST", body, headers: { "Content-Type": "text/plain" } }).catch(() => {
    throw new Error("The playground needs the local server: run `cdcl serve` and open http://127.0.0.1:8080/");
  });
  const data = (await res.json()) as PlaygroundResponse;
  if (data.error) throw new Error(data.error);
  return data;
}

export interface Example {
  group: string;
  name: string;
  text: string;
}

// The .smt2 files in examples/smt are bundled into the page (Vite `?raw`).
const files = import.meta.glob("../../examples/smt/*.smt2", { query: "?raw", import: "default", eager: true }) as Record<string, string>;

/** The example list, in the order shown; `file` is a name in examples/smt. */
const LIST: [group: string, file: string, name: string][] = [
  ["LIA", "dpllt_intro", "DPLL(T) intro: (x+1>0 ∨ x+y>0) ∧ (x<0 ∨ x+y>4) ∧ ¬x+y>0 — UNSAT"],
  ["LIA", "learn_backtrack", "Exercise: (x>y ∨ x>z) ∧ (x+1<y ∨ ¬x>y) ∧ (x>y ∨ z>y) — UNSAT"],
  ["LIA", "several_decisions", "Several decisions, 7 clauses — SAT"],
  ["LIA", "lia_simplex", "Simplex conflict — UNSAT"],
  ["LIA", "lia_gcd", "GCD test (2x − 2y = 1) — UNSAT"],
  ["LIA", "lia_branch", "Branch and bound — UNSAT"],
  ["LIA", "lia_sat", "Scheduling with Boolean structure — SAT"],
  ["DT", "dt_intro", "DT intro: y = green ∧ (x = red ∨ x ≠ y) ∧ cons(x, nil) = cons(y, z) — UNSAT"],
  ["DT", "dt_colors", "Finite sort, 4 colours — UNSAT"],
  ["LIA + DT", "dt_lists", "Lists and selectors — SAT"],
  ["LIA + DT", "dt_cycle", "Acyclicity (l = cons(1, l)) — UNSAT"],
  ["LIA + DT", "no_lists", "Two lists, x + y = 10, with decisions — SAT"],
  ["LIA + DT", "combo_injectivity", "Equality exchange (injectivity) — UNSAT"],
  ["LIA + DT", "combo_purify", "Purification of head(l) = x + 1 — UNSAT"],
  ["LIA + DT", "nonconvex", "Non-convex: arrangement guessing — UNSAT"],
  ["LIA + DT", "combo_sat", "Lists with arithmetic — SAT"],
];

export function loadExamples(): Example[] {
  const byName = new Map(Object.entries(files).map(([path, text]) => [path.replace(/^.*\/|\.smt2$/g, ""), text]));
  return LIST.filter(([, f]) => byName.has(f)).map(([group, f, name]) => ({ group, name, text: byName.get(f)! }));
}

/** Solve SMT-LIB text (`POST /api/solve`): the status and, when sat, the model. */
export async function solveSmt(src: string): Promise<{ status: string; model: { name: string; value: string }[] }> {
  const res = await fetch("api/solve", { method: "POST", body: src, headers: { "Content-Type": "text/plain" } }).catch(() => {
    throw new Error("The playground needs the local server: run `cdcl serve` and open http://127.0.0.1:8080/");
  });
  const data = await res.json();
  if (data.error) throw new Error(data.error);
  return { status: data.status, model: data.smt?.model ?? [] };
}
