// The levels of the educational mode. Each one practises one idea of
// DPLL(T) on a small, hand-picked example.

/** A propositional literal: a name, with "¬" in front when negated. */
export type PLit = string;

export interface PropagationLevel {
  kind: "propagation";
  id: string;
  title: string;
  intro: string;
  clauses: PLit[][];
  /** the decisions already made, in order */
  decisions: PLit[];
}

/** a·x + b·y ≤ c, drawn in the plane */
export interface PlotConstraint {
  label: string;
  a: number;
  b: number;
  c: number;
  /** shown on that step, e.g. what a strict inequality means over the integers */
  hint?: string;
}

export interface PlotLevel {
  kind: "plot";
  id: string;
  title: string;
  intro: string;
  constraints: PlotConstraint[];
  box: [number, number, number, number];
  /** no hints: a wrong point is only called wrong, without the line's equation */
  noHints?: boolean;
  /** after the drawing: prove there is no integer point by branch and bound */
  branch?: boolean;
}

export interface LemmaLevel {
  kind: "lemma";
  id: string;
  title: string;
  intro: string;
  /** the context: literals as shown, and as SMT-LIB */
  literals: { label: string; smt: string }[];
  vars: string[];
}

export interface GraphLevel {
  kind: "graph";
  id: string;
  title: string;
  intro: string;
  /** SMT-LIB input and the decisions to make (atom labels; "¬" for false) */
  src: string;
  decisions: string[];
  theoryPropagation: boolean;
}

export interface ConflictLevel {
  kind: "conflict";
  id: string;
  title: string;
  intro: string;
  src: string;
  decisions: string[];
  theoryPropagation: boolean;
}

export interface SimplexLevel {
  kind: "simplex";
  id: string;
  title: string;
  intro: string;
  /** the original variables (nonbasic at first, value 0) */
  vars: string[];
  /** slack rows: name = Σ coefficient·variable */
  rows: { name: string; sum: Record<string, number> }[];
  bounds: { v: string; lo?: number; hi?: number }[];
}

export interface ClosureLevel {
  kind: "closure";
  id: string;
  title: string;
  intro: string;
  ctors: string[];
  eqs: [string, string][];
  diseqs: [string, string][];
}

export interface ExchangeLevel {
  kind: "exchange";
  id: string;
  title: string;
  intro: string;
  shared: string[];
  liaVars: string[];
  lia: { label: string; smt: string }[];
  ctors: string[];
  dt: { eqs: [string, string][]; diseqs: [string, string][] };
}

export interface PurifyLevel {
  kind: "purify";
  id: string;
  title: string;
  intro: string;
  /** mixed literals, e.g. "head(l) + 1 ≤ x" */
  literals: string[];
  /** constructors, selectors and constructor constants (everything DT) */
  dtSymbols: string[];
}

export type Level = PropagationLevel | PlotLevel | LemmaLevel | GraphLevel | ConflictLevel | SimplexLevel | ClosureLevel | PurifyLevel | ExchangeLevel;

// In the order a course meets them: the SAT engine first, then LIA, then
// DT, then the combination.
export const TOPICS: { name: string; kind: Level["kind"]; about: string }[] = [
  { name: "Unit propagation", kind: "propagation", about: "Find every literal that unit propagation sets, step by step, until nothing more follows (or a clause becomes false)." },
  { name: "Implication graphs", kind: "graph", about: "Given the run of DPLL(T), connect each propagated literal to the literals that caused it." },
  { name: "Conflict analysis", kind: "conflict", about: "From the implication graph of a conflict: find the First UIP, the clause CDCL learns, and the level it jumps back to." },
  { name: "LIA in the plane", kind: "plot", about: "Draw each constraint as a line, choose the side it allows, and see what is left." },
  { name: "Simplex", kind: "simplex", about: "Run the general Simplex yourself: repair a basic variable that breaks its bound by pivoting, until every bound holds or a row is stuck." },
  { name: "Theory lemmas", kind: "lemma", about: "LIA says the context is unsatisfiable: find the literals that conflict, which gives the lemma the SAT solver learns." },
  { name: "DT: congruence closure", kind: "closure", about: "Derive the equalities DT gets from its literals (given, congruence, injectivity), one at a time, then look for a conflict." },
  { name: "LIA + DT: purification", kind: "purify", about: "Before Nelson–Oppen can start, every literal must belong to one theory: replace each alien subterm by a fresh constant, then find the constants both parts share." },
  { name: "LIA + DT: Nelson–Oppen", kind: "exchange", about: "The two theories only share constants: find the equalities each one tells the other, and who finds the conflict." },
];

const DECL = (names: string[]) => names.map((n) => `(declare-const ${n} Bool)`).join("\n");
const CLAUSE = (lits: string[]) => (lits.length === 1 ? lit(lits[0]) : `(or ${lits.map(lit).join(" ")})`);
const lit = (l: string) => (l.startsWith("¬") ? `(not ${l.slice(1)})` : l);
const BOOL = (names: string[], clauses: string[][]) => `${DECL(names)}\n${clauses.map((c) => `(assert ${CLAUSE(c)})`).join("\n")}\n(check-sat)`;

const ALL: Level[] = [
  // ---------------------------------------------------------------- propagation
  {
    kind: "propagation",
    id: "prop-none",
    title: "1. Nothing to propagate",
    intro:
      "A clause is unit when every literal but one is false: that last literal must then be true. Here p was decided true. Is any clause unit? If nothing is forced, change nothing and press Check.",
    clauses: [["p", "q", "r"], ["¬p", "s", "t"], ["q", "¬s", "u"]],
    decisions: ["p"],
  },
  {
    kind: "propagation",
    id: "prop-one",
    title: "2. One unit clause",
    intro: "p was decided true. Which clause becomes unit, and which literal must be true because of it? Click that literal in your copy of the formula to set it.",
    clauses: [["¬p", "q"], ["q", "r", "s"], ["¬r", "s", "t"]],
    decisions: ["p"],
  },
  {
    kind: "propagation",
    id: "prop-chain",
    title: "3. A chain of propagations",
    intro:
      "One propagation can make another clause unit. Keep going until no clause is unit any more: set every literal that is forced, not only the first one.",
    clauses: [["¬p", "q"], ["¬q", "r"], ["¬r", "¬s"], ["s", "t", "¬q"], ["t", "u", "v"]],
    decisions: ["p"],
  },
  {
    kind: "propagation",
    id: "prop-two",
    title: "4. Two decisions, many consequences",
    intro: "p was decided true and u false. Follow every consequence. Some clauses stay open: they are not unit, so nothing follows from them.",
    clauses: [["¬p", "q", "u"], ["¬q", "r"], ["u", "¬r", "s"], ["¬s", "t", "¬p"], ["p", "v"], ["v", "w"], ["¬t", "w", "x"]],
    decisions: ["p", "¬u"],
  },
  {
    kind: "propagation",
    id: "prop-conflict",
    title: "5. Propagation until a conflict",
    intro:
      "p was decided true. Set every literal that is forced; if a clause ends up with all its literals false, say which one.",
    clauses: [["¬p", "q"], ["¬p", "r"], ["¬q", "¬r", "s"], ["¬s", "¬q"], ["s", "t"]],
    decisions: ["p"],
  },

  // ---------------------------------------------------------------- LIA in the plane
  {
    kind: "plot",
    id: "plot-box",
    title: "1. A triangle of solutions",
    intro:
      "Each constraint is a line; one side of it is allowed. For every constraint: click two grid points on its line, then click a point on the side it allows. What stays green is allowed by every constraint so far.",
    constraints: [
      { label: "x ≥ 1", a: -1, b: 0, c: -1 },
      { label: "y ≥ 0", a: 0, b: -1, c: 0 },
      { label: "x + y ≤ 4", a: 1, b: 1, c: 4 },
    ],
    box: [-2, 6, -2, 6],
  },
  {
    kind: "plot",
    id: "plot-slides",
    title: "2. The lecture's conflict",
    intro: "The literals x > y and x + 1 < y from the lecture's exercise. Draw them and see whether any point survives.",
    constraints: [
      { label: "x > y", a: -1, b: 1, c: -1 },
      { label: "x + 1 < y", a: 1, b: -1, c: -2 },
    ],
    noHints: true,
    box: [-3, 5, -3, 5],
  },
  {
    kind: "plot",
    id: "plot-simplex",
    title: "3. Too far for the bounds",
    intro: "x + y must reach 6, but x ≤ 2 and y ≤ 3. Draw the three constraints: is there room left?",
    constraints: [
      { label: "x ≤ 2", a: 1, b: 0, c: 2 },
      { label: "y ≤ 3", a: 0, b: 1, c: 3 },
      { label: "x + y ≥ 6", a: -1, b: -1, c: -6 },
    ],
    box: [-1, 7, -1, 7],
  },
  {
    kind: "plot",
    id: "plot-branch",
    title: "4. A triangle without integers (branch and bound)",
    intro:
      "Five constraints this time. Draw them all, then look closely at what is left: is there really an integer point in it?",
    constraints: [
      { label: "x ≥ 1", a: -1, b: 0, c: -1 },
      { label: "y ≤ 4", a: 0, b: 1, c: 4 },
      { label: "3x + 1 ≤ 4y", a: 3, b: -4, c: -1 },
      { label: "4y ≤ x + 8", a: -1, b: 4, c: 8 },
      { label: "x + 2y ≥ 7", a: -1, b: -2, c: -7 },
    ],
    box: [-1, 6, -1, 6],
    branch: true,
  },

  // ---------------------------------------------------------------- theory lemmas
  {
    kind: "lemma",
    id: "lemma-slides",
    title: "1. The lecture's first conflict",
    intro:
      "The SAT solver hands LIA the context below (from the DPLL(T) intro example), and LIA answers \"unsat\". Pick the literals that cannot hold together; leave out the ones that do not matter. Their negations form the theory lemma.",
    literals: [
      { label: "x + 1 > 0", smt: "(> (+ x 1) 0)" },
      { label: "¬(x + y > 0)", smt: "(not (> (+ x y) 0))" },
      { label: "x < 0", smt: "(< x 0)" },
    ],
    vars: ["x", "y"],
  },
  {
    kind: "lemma",
    id: "lemma-chain",
    title: "2. A chain of bounds",
    intro: "Five literals, and LIA says \"unsat\". Which of them really conflict?",
    literals: [
      { label: "x ≥ 3", smt: "(>= x 3)" },
      { label: "z ≥ 0", smt: "(>= z 0)" },
      { label: "y ≥ x", smt: "(>= y x)" },
      { label: "z ≤ 10", smt: "(<= z 10)" },
      { label: "y ≤ 2", smt: "(<= y 2)" },
    ],
    vars: ["x", "y", "z"],
  },
  {
    kind: "lemma",
    id: "lemma-sum",
    title: "3. A sum that cannot be reached",
    intro: "The Simplex example: x + y must reach 10. Find the smallest set of literals that LIA can blame.",
    literals: [
      { label: "x ≥ 0", smt: "(>= x 0)" },
      { label: "x + y ≥ 10", smt: "(>= (+ x y) 10)" },
      { label: "y ≥ 0", smt: "(>= y 0)" },
      { label: "x ≤ 3", smt: "(<= x 3)" },
      { label: "y ≤ 6", smt: "(<= y 6)" },
    ],
    vars: ["x", "y"],
  },

  // ---------------------------------------------------------------- implication graphs
  {
    kind: "graph",
    id: "graph-chain",
    title: "1. One decision",
    intro:
      "p was decided; everything else was propagated. Each propagated literal has incoming edges from the literals that made its clause unit. Click a propagated literal, then click its causes.",
    src: BOOL(["p", "q", "r", "s"], [["¬p", "q"], ["¬q", "r"], ["¬p", "¬r", "s"]]),
    decisions: ["p"],
    theoryPropagation: false,
  },
  {
    kind: "graph",
    id: "graph-conflict",
    title: "2. Two levels and a conflict",
    intro: "Two decisions, and the second one leads to a conflict. The conflict node κ gets an edge from every literal of the clause that became false.",
    src: BOOL(["p", "q", "r", "s"], [["¬p", "q"], ["¬q", "r"], ["¬q", "¬r", "¬s"], ["s", "p", "r"]]),
    decisions: ["s", "p"],
    theoryPropagation: false,
  },
  {
    kind: "graph",
    id: "graph-lia",
    title: "3. DPLL(LIA): a theory conflict",
    intro: "The lecture's exercise after deciding x > y. A theory conflict is a clause too (the theory lemma), so κ gets edges from the literals LIA blames.",
    src: "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(assert (or (> x y) (> x z)))\n(assert (or (< (+ x 1) y) (not (> x y))))\n(assert (or (> x y) (> z y)))\n(check-sat)",
    decisions: ["x > y"],
    theoryPropagation: false,
  },
  {
    kind: "graph",
    id: "graph-dt",
    title: "4. DPLL(DT): theory propagation",
    intro:
      "The DT intro example, with theory propagation on: DT derives x = y from cons(x, nil) = cons(y, z) (injectivity). A theory propagation is an edge too, from the literals DT used.",
    src: "(declare-datatypes ((Color 0)) (((red) (green) (blue))))\n(declare-datatypes ((List 0)) (((nil) (cons (head Color) (tail List)))))\n(declare-const x Color)\n(declare-const y Color)\n(declare-const z List)\n(assert (= y green))\n(assert (or (= x red) (not (= x y))))\n(assert (= (cons x nil) (cons y z)))\n(check-sat)",
    decisions: [],
    theoryPropagation: true,
  },

  // ---------------------------------------------------------------- conflict analysis
  {
    kind: "conflict",
    id: "conflict-decision",
    title: "1. The decision is the UIP",
    intro: "s was decided at level 1, p at level 2, and propagation ran into a conflict. Analyse it the way CDCL does.",
    src: BOOL(["p", "q", "r", "s"], [["¬p", "q"], ["¬p", "r"], ["¬q", "¬r", "¬s"]]),
    decisions: ["s", "p"],
    theoryPropagation: false,
  },
  {
    kind: "conflict",
    id: "conflict-uip",
    title: "2. A UIP below the decision",
    intro: "Three decisions: p, then q, then a.",
    src: BOOL(["p", "q", "a", "b", "c", "d"], [["¬a", "b"], ["¬b", "¬p", "c"], ["¬b", "d"], ["¬c", "¬d", "¬q"]]),
    decisions: ["p", "q", "a"],
    theoryPropagation: false,
  },
  {
    kind: "conflict",
    id: "conflict-jump",
    title: "3. Jumping over levels",
    intro: "Four decisions, but the conflict only involves two of the levels. How far back can CDCL jump?",
    src: BOOL(["p", "q", "r", "a", "b", "c"], [["¬a", "b"], ["¬a", "c"], ["¬b", "¬c", "¬p"], ["q", "r", "a"]]),
    decisions: ["p", "q", "r", "a"],
    theoryPropagation: false,
  },
  {
    kind: "conflict",
    id: "conflict-lia",
    title: "4. A theory conflict",
    intro: "The lecture's DPLL(LIA) exercise after deciding x > y: the conflict clause is a theory lemma. Analysis treats it like any other clause.",
    src: "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(assert (or (> x y) (> x z)))\n(assert (or (< (+ x 1) y) (not (> x y))))\n(assert (or (> x y) (> z y)))\n(check-sat)",
    decisions: ["x > y"],
    theoryPropagation: false,
  },

  // ---------------------------------------------------------------- simplex
  {
    kind: "simplex",
    id: "simplex-sat",
    title: "1. Two pivots to a solution",
    intro: "s is the slack of x + y. At the start every original variable is 0, so s = 0, which breaks s ≥ 4. Repair it.",
    vars: ["x", "y"],
    rows: [{ name: "s", sum: { x: 1, y: 1 } }],
    bounds: [
      { v: "s", lo: 4 },
      { v: "x", hi: 3 },
      { v: "y", hi: 2 },
    ],
  },
  {
    kind: "simplex",
    id: "simplex-unsat",
    title: "2. The lecture's Simplex conflict",
    intro: "x + y must reach 10 (the slack s), but x ≤ 3 and y ≤ 6.",
    vars: ["x", "y"],
    rows: [{ name: "s", sum: { x: 1, y: 1 } }],
    bounds: [
      { v: "s", lo: 10 },
      { v: "x", lo: 0, hi: 3 },
      { v: "y", lo: 0, hi: 6 },
    ],
  },
  {
    kind: "simplex",
    id: "simplex-two",
    title: "3. Two rows",
    intro: "Two slacks: s₁ = x − y and s₂ = x + y. One repair can break the other row, so keep checking every row.",
    vars: ["x", "y"],
    rows: [
      { name: "s1", sum: { x: 1, y: -1 } },
      { name: "s2", sum: { x: 1, y: 1 } },
    ],
    bounds: [
      { v: "s1", lo: 1 },
      { v: "s2", hi: 3 },
      { v: "y", lo: 1 },
    ],
  },

  // ---------------------------------------------------------------- DT closure
  {
    kind: "closure",
    id: "closure-inj",
    title: "1. Injectivity",
    intro: "One equality between two lists. What else must be equal?",
    ctors: ["cons", "nil"],
    eqs: [["cons(x, nil)", "cons(y, z)"]],
    diseqs: [],
  },
  {
    kind: "closure",
    id: "closure-cong",
    title: "2. Congruence",
    intro: "x = y, and two lists are built from them.",
    ctors: ["cons", "nil"],
    eqs: [
      ["x", "y"],
      ["l", "cons(x, nil)"],
      ["m", "cons(y, nil)"],
    ],
    diseqs: [["l", "m"]],
  },
  {
    kind: "closure",
    id: "closure-clash",
    title: "3. Colours",
    intro: "A list of colours, and what we know about its head.",
    ctors: ["cons", "nil", "red", "green", "blue"],
    eqs: [
      ["cons(x, l)", "cons(green, nil)"],
      ["x", "y"],
      ["y", "red"],
    ],
    diseqs: [],
  },
  {
    kind: "closure",
    id: "closure-cycle",
    title: "4. Two lists in a loop",
    intro: "l starts with x and continues with m; m starts with y and continues with …",
    ctors: ["cons", "nil"],
    eqs: [
      ["l", "cons(x, m)"],
      ["m", "cons(y, k)"],
      ["k", "l"],
    ],
    diseqs: [],
  },

  // ---------------------------------------------------------------- purification
  {
    kind: "purify",
    id: "purify-head",
    title: "1. A head in a sum",
    intro: "One literal that mixes both theories.",
    literals: ["head(l) + 1 ≤ x"],
    dtSymbols: ["cons", "nil", "head", "tail"],
  },
  {
    kind: "purify",
    id: "purify-cons",
    title: "2. A sum in a list",
    intro: "Two literals. Not every constant ends up shared.",
    literals: ["l = cons(x + 1, nil)", "x ≥ 0"],
    dtSymbols: ["cons", "nil", "head", "tail"],
  },
  {
    kind: "purify",
    id: "purify-two",
    title: "3. Two heads",
    intro: "Three literals over one list.",
    literals: ["head(tail(l)) + head(l) = 3", "tail(l) = cons(y, m)", "y > 2"],
    dtSymbols: ["cons", "nil", "head", "tail"],
  },
  {
    kind: "purify",
    id: "purify-nested",
    title: "4. Aliens inside aliens",
    intro: "A list whose head is computed from its own head.",
    literals: ["cons(head(l) + 1, nil) = l"],
    dtSymbols: ["cons", "nil", "head", "tail"],
  },

  // ---------------------------------------------------------------- LIA + DT
  {
    kind: "exchange",
    id: "exchange-lia",
    title: "1. LIA tells DT",
    intro: "The heads of two one-element lists must differ (DT), and LIA knows about the heads.",
    shared: ["x", "y", "z"],
    liaVars: ["x", "y", "z"],
    lia: [
      { label: "x ≥ 2", smt: "(>= x 2)" },
      { label: "y ≤ 2", smt: "(<= y 2)" },
      { label: "x ≤ y", smt: "(<= x y)" },
      { label: "z ≥ 5", smt: "(>= z 5)" },
    ],
    ctors: ["cons", "nil"],
    dt: { eqs: [], diseqs: [["cons(x, nil)", "cons(y, nil)"]] },
  },
  {
    kind: "exchange",
    id: "exchange-dt",
    title: "2. DT tells LIA",
    intro: "Two lists are equal (DT), and LIA has bounds on their heads.",
    shared: ["x", "y"],
    liaVars: ["x", "y"],
    lia: [
      { label: "x ≥ 3", smt: "(>= x 3)" },
      { label: "y ≤ 1", smt: "(<= y 1)" },
    ],
    ctors: ["cons", "nil"],
    dt: { eqs: [["cons(x, l)", "cons(y, m)"]], diseqs: [] },
  },
  {
    kind: "exchange",
    id: "exchange-sat",
    title: "3. Nothing to exchange?",
    intro: "Three heads, a sum, and a list equality.",
    shared: ["x", "y", "z"],
    liaVars: ["x", "y", "z"],
    lia: [
      { label: "x + y = 4", smt: "(= (+ x y) 4)" },
      { label: "x ≥ 1", smt: "(>= x 1)" },
      { label: "z ≥ 0", smt: "(>= z 0)" },
    ],
    ctors: ["cons", "nil"],
    dt: { eqs: [["cons(y, nil)", "cons(z, l)"]], diseqs: [["l", "cons(x, nil)"]] },
  },
];

/** The levels, topic by topic ("Next level" follows this order). */
export const LEVELS: Level[] = TOPICS.flatMap((t) => ALL.filter((l) => l.kind === t.kind));
