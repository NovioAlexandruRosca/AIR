// Turns a playground response into a sequence of small, teachable steps and
// computes the state (assignment, conflict, visible lemmas) after each step.
//
// A unit propagation takes two steps on purpose:
//   1. "unit"      — this clause has one open literal left, all others false;
//   2. "propagate" — so that literal must be true: it is assigned.
// Theory propagations and Nelson–Oppen exchanges are split the same way
// ("derive" then "propagate"), and a theory conflict is shown as: invoke the
// theory solver, context unsatisfiable, add the lemma, conflicting clause.

import type { FormulaNode, Lit, PlaygroundResponse, TraceEvent, VarInfo } from "./api";

export type StepKind =
  | "decide"
  | "unit"
  | "derive"
  | "propagate"
  | "invoke"
  | "theory-unsat"
  | "lemma"
  | "conflict"
  | "learn"
  | "backjump"
  | "sat"
  | "unsat";

export interface Step {
  kind: StepKind;
  /** events[0..stateEnd] are applied in the state shown at this step */
  stateEnd: number;
  /** short line for the history, in the slides' wording */
  line: string;
  /** big heading and explanation for the current-step card */
  head: string;
  body: string;
  /** clause id to highlight (unit clause, conflicting clause, lemma) */
  clause?: number;
  /** literals to highlight */
  lits: Lit[];
  theory?: string;
  /** decision number this step belongs to (for greying old steps) */
  group: number;
  bySolver: boolean;
}

export interface Labels {
  vars: (VarInfo | undefined)[];
  /** var -> label as written in the input formula */
  written: string[];
}

export function makeLabels(r: PlaygroundResponse): Labels {
  const vars: (VarInfo | undefined)[] = [];
  if (r.smt) for (const v of r.smt.vars) vars[v.var] = v;
  for (const ev of r.events) {
    if (ev.type === "NewVar")
      vars[ev.var] = { var: ev.var, label: ev.label, neg: ev.neg, kind: ev.kind, theories: ev.theories ? ev.theories.split(",") : [], def: null };
  }
  const written: string[] = [];
  const walk = (n: FormulaNode) => {
    if ("atom" in n) {
      if (!written[n.atom]) written[n.atom] = n.label;
    } else if ("args" in n) n.args.forEach(walk);
  };
  (r.formula || []).forEach(walk);
  return { vars, written };
}

export const atomText = (L: Labels, v: number) => L.written[v] || L.vars[v]?.label || `x${v}`;

/** Literal as on the slides: x>y, ¬(x + 1 < y). */
export function litText(L: Labels, l: Lit): string {
  const a = atomText(L, Math.abs(l));
  if (l > 0) return a;
  return /\s/.test(a) ? `¬(${a})` : `¬${a}`;
}

export const assignText = (L: Labels, l: Lit) => `${atomText(L, Math.abs(l))} → ${l > 0 ? "true" : "false"}`;
export const clauseText = (L: Labels, c: Lit[]) => "(" + c.map((l) => litText(L, l)).join(" ∨ ") + ")";

/** Tseitin variables are pure encoding: never shown. */
export function visibleVar(L: Labels, v: number): boolean {
  const k = L.vars[v]?.kind;
  return k !== "aux" && k !== "true";
}

export interface ClauseInfo {
  /** "F3", "the learned clause", "LIA's definition of x = y", ... */
  name: string;
  /** index of the assertion it encodes, if any */
  assertion?: number;
  kind: "assertion" | "learned" | "lemma" | "definition" | "encoding" | "explanation";
}

/** Where a clause comes from. `learnedKeys` marks kept clauses learned by conflict analysis. */
export function clauseInfo(r: PlaygroundResponse, theoryClause: Map<number, TraceEvent & { type: "TheoryClause" }>, learnedKeys: Set<string>, id: number): ClauseInfo {
  const tc = theoryClause.get(id);
  if (tc) {
    if (tc.kind === "axiom") return { name: definitionName(tc.theory, tc.why), kind: "definition" };
    if (tc.kind === "conflict") return { name: `the ${tc.theory} lemma`, kind: "lemma" };
    return { name: `${tc.theory}'s explanation`, kind: "explanation" };
  }
  if (id < r.num_original) {
    if (!r.smt) return { name: `F${id + 1}`, assertion: id, kind: "assertion" };
    const o = r.smt.clause_origin[id] || "";
    const m = o.match(/^assert #(\d+)/);
    if (m) return { name: `F${m[1]}`, assertion: Number(m[1]) - 1, kind: "assertion" };
    if (o.startsWith("clause learned earlier")) {
      return learnedKeys.has(keyOf(r.replay.db[id] || [])) ? { name: "the learned clause", kind: "learned" } : { name: "the theory lemma", kind: "lemma" };
    }
    const ax = o.match(/^axiom \((\w+)\)/);
    if (ax) return { name: definitionName(ax[1], o), kind: "definition" };
    if (o.startsWith("purification")) return { name: "the purification definition", kind: "definition" };
    return { name: "a clause of the CNF encoding", kind: "encoding" };
  }
  return { name: "a learned clause", kind: "learned" };
}

function definitionName(theory: string, text: string): string {
  const m = text.match(/definition: (.*?) ⇔/);
  return m ? `${theory}'s definition of ${m[1]}` : `a ${theory} definition`;
}

/** The theories the formula actually uses, e.g. "LIA" or "LIA+DT" (empty for SAT input). */
export function theoryName(r: PlaygroundResponse): string {
  if (!r.smt) return "";
  const used = new Set(r.smt.vars.filter((v) => v.kind !== "aux").flatMap((v) => v.theories));
  const names = r.smt.theories.filter((t) => used.has(t));
  return (names.length ? names : r.smt.theories).join("+");
}

export const keyOf = (c: Lit[]) => c.slice().sort((a, b) => a - b).join(",");

export type TheoryClauseEvent = TraceEvent & { type: "TheoryClause" };

export function theoryClauses(r: PlaygroundResponse): Map<number, TheoryClauseEvent> {
  const m = new Map<number, TheoryClauseEvent>();
  for (const ev of r.events) if (ev.type === "TheoryClause") m.set(ev.clause, ev);
  return m;
}

const cap = (s: string) => s.charAt(0).toUpperCase() + s.slice(1);

export function buildSteps(r: PlaygroundResponse, L: Labels, learnedKeys: Set<string>): Step[] {
  const tcs = theoryClauses(r);
  const steps: Step[] = [];
  const ctx: Lit[] = [];
  let group = 0;
  const from = r.replay.finish_from;
  const push = (s: Omit<Step, "group" | "bySolver">, i: number) =>
    steps.push({ ...s, group, bySolver: from !== null && i >= from });

  r.events.forEach((ev, i) => {
    switch (ev.type) {
      case "Decide": {
        group++;
        ctx.push(ev.lit);
        const user = ev.origin?.by === "user";
        const solverSplit = ev.origin && !user;
        push(
          {
            kind: "decide",
            stateEnd: i,
            line: `Decide : ${assignText(L, ev.lit)}` + (user ? "" : solverSplit ? `  (${ev.origin!.by} split)` : "  (solver)"),
            head: user ? `You decide ${assignText(L, ev.lit)}` : solverSplit ? `${ev.origin!.by} asks for a case split: ${assignText(L, ev.lit)}` : `The solver decides ${assignText(L, ev.lit)}`,
            body: user
              ? "A decision is a guess: it opens a new decision level. Now unit propagation and the theory solver work out what follows."
              : solverSplit
                ? ev.origin!.why
                : "No clause forces anything, so the solver guesses (MOMS heuristic: the most frequent literal of the shortest open clauses).",
            lits: [ev.lit],
          },
          i,
        );
        break;
      }
      case "Propagate": {
        ctx.push(ev.lit);
        const v = Math.abs(ev.lit);
        if (!visibleVar(L, v)) break;
        const tc = tcs.get(ev.reason);
        const lit = litText(L, ev.lit);
        if (tc && tc.kind !== "axiom") {
          // theory propagation / Nelson–Oppen exchange: derive, then assign
          const nelsonOppen = L.vars[v]?.kind === "interface";
          const why = nelsonOppen && tc.why.includes(". ") ? tc.why.slice(tc.why.indexOf(". ") + 2) : tc.why;
          push(
            {
              kind: "derive",
              stateEnd: i - 1,
              line: nelsonOppen ? `${tc.theory} derives ${lit}  (Nelson–Oppen)` : `${tc.theory} derives ${lit}`,
              head: nelsonOppen ? `${tc.theory} derives ${lit} — an equality between shared constants` : `${tc.theory} derives ${lit}`,
              body: cap(why) + (nelsonOppen ? ". Both theories use these constants, so the other theory must learn it too (Nelson–Oppen exchange)." : "."),
              lits: [ev.lit],
              theory: tc.theory,
            },
            i,
          );
          push(
            {
              kind: "propagate",
              stateEnd: i,
              line: `Propagate : ${assignText(L, ev.lit)}  (by ${tc.theory})`,
              head: `Propagate : ${assignText(L, ev.lit)}`,
              body: nelsonOppen ? `Added to the context, where every theory sees it.` : `Added to the context because ${tc.theory} says so.`,
              lits: [ev.lit],
              theory: tc.theory,
            },
            i,
          );
        } else {
          const ci = clauseInfo(r, tcs, learnedKeys, ev.reason);
          const c = r.replay.db[ev.reason] || [];
          const others = c.filter((l) => l !== ev.lit);
          push(
            {
              kind: "unit",
              stateEnd: i - 1,
              line: `${cap(ci.name)} is unit`,
              head: others.length ? `${cap(ci.name)} has a single open literal` : `${cap(ci.name)} is a single literal`,
              body: others.length
                ? `In ${ci.name} ${clauseText(L, c)} every literal except ${lit} is already false. A clause needs one true literal, so ${lit} must be true.`
                : `${cap(ci.name)} is just ${lit}, so it must be true.`,
              clause: ev.reason,
              lits: [ev.lit],
            },
            i,
          );
          push(
            {
              kind: "propagate",
              stateEnd: i,
              line: `Propagate : ${assignText(L, ev.lit)}`,
              head: `Propagate : ${assignText(L, ev.lit)}`,
              body: `${lit} is added to the context (because of ${ci.name}).`,
              clause: ev.reason,
              lits: [ev.lit],
            },
            i,
          );
        }
        break;
      }
      case "Theory": {
        if (ev.kind !== "conflict") break;
        const shown = ctx.filter((l) => visibleVar(L, Math.abs(l))).map((l) => litText(L, l));
        const ctxText = `{ ${shown.join(", ")} }`;
        push(
          {
            kind: "invoke",
            stateEnd: i,
            line: `Invoke theory solver for ${ev.theory} on: ${shown.length <= 6 ? ctxText : `${shown.length} literals`}`,
            head: `Invoke the theory solver for ${ev.theory}`,
            body: `Unlike plain SAT, the context must also make sense in ${ev.theory}. Is ${ctxText} satisfiable?`,
            lits: [],
            theory: ev.theory,
          },
          i,
        );
        const ones = ev.lits.map((l) => litText(L, l));
        push(
          {
            kind: "theory-unsat",
            stateEnd: i,
            line: `${ones.join(" ∧ ")} is ${ev.theory}-unsatisfiable`,
            head: `Context is ${ev.theory}-unsatisfiable!`,
            body: `One of ${ones.join(", ")} must be false. ${ev.message}.`,
            lits: ev.lits,
            theory: ev.theory,
          },
          i,
        );
        break;
      }
      case "TheoryClause": {
        if (ev.kind !== "conflict") break;
        push(
          {
            kind: "lemma",
            stateEnd: i,
            line: `Add theory lemma ${clauseText(L, ev.lits)}`,
            head: `Add the theory lemma ${clauseText(L, ev.lits)}`,
            body: `"Not all of them can hold", written as a clause. It is valid in ${ev.theory}, so it is added to F — and it stays there.`,
            clause: ev.clause,
            lits: ev.lits,
            theory: ev.theory,
          },
          i,
        );
        break;
      }
      case "Conflict": {
        const c = r.replay.db[ev.clause] || [];
        const ci = clauseInfo(r, tcs, learnedKeys, ev.clause);
        push(
          {
            kind: "conflict",
            stateEnd: i,
            line: ev.level > 0 ? "Conflicting clause! … backtrack on a decision" : "Conflicting clause! … no decision to backtrack",
            head: "Conflicting clause!",
            body:
              `Every literal of ${ci.name} ${clauseText(L, c)} is false. ` +
              (ev.level > 0 ? "One of the decisions was wrong: backtrack on a decision." : "There is no decision left to undo."),
            clause: ev.clause,
            lits: c,
          },
          i,
        );
        break;
      }
      case "Learn":
        push(
          {
            kind: "learn",
            stateEnd: i,
            line: `Learn ${clauseText(L, ev.lits)}`,
            head: `Learn ${clauseText(L, ev.lits)}`,
            body: "Conflict analysis (First UIP) turns the conflict into a clause, so the same mistake cannot happen again.",
            lits: ev.lits,
          },
          i,
        );
        break;
      case "Backjump":
        ctx.length = Math.max(0, ctx.length - ev.unassigned.length);
        push(
          {
            kind: "backjump",
            stateEnd: i,
            line: `Backjump to level ${ev.to}`,
            head: `Backjump to level ${ev.to}`,
            body: `Undo ${ev.unassigned.length} assignment(s). The learned clause now has one open literal.`,
            lits: [],
          },
          i,
        );
        break;
    }
  });
  const last = r.events.length - 1;
  if (steps.length) steps[steps.length - 1].stateEnd = Math.max(steps[steps.length - 1].stateEnd, last);
  if (r.replay.outcome === "sat") {
    steps.push({
      kind: "sat", stateEnd: last, group, bySolver: false, lits: [],
      line: "Invoke the theory solvers on the full context: consistent ⇒ input is satisfiable",
      head: "Satisfiable!",
      body: "Every clause is true and the theory solvers accept the context.",
    });
  }
  const noDecisionLeft = r.replay.outcome === "unsat" || (r.replay.outcome === "conflict" && conflictAtLevelZero(r));
  if (noDecisionLeft) {
    steps.push({
      kind: "unsat", stateEnd: last, group, bySolver: false, lits: [],
      line: `⇒ Input is ${r.smt ? theoryName(r) + "-" : ""}unsat`,
      head: `Input is ${r.smt ? theoryName(r) + "-" : ""}unsat`,
      body: "A conflict with no decision to backtrack: no assignment satisfies the formula and the theories at the same time.",
    });
  }
  return steps;
}

function conflictAtLevelZero(r: PlaygroundResponse): boolean {
  for (let i = r.events.length - 1; i >= 0; i--) {
    const e = r.events[i];
    if (e.type === "Conflict") return e.level === 0;
  }
  return false;
}

export interface State {
  value: Map<number, 1 | -1>;
  trail: { lit: Lit; level: number; reason: number | null; origin?: string }[];
  conflict: number | null;
  /** events applied */
  end: number;
}

export function stateAt(r: PlaygroundResponse, end: number): State {
  const value = new Map<number, 1 | -1>();
  const trail: State["trail"] = [];
  let conflict: number | null = null;
  for (let i = 0; i <= end; i++) {
    const ev = r.events[i];
    if (ev.type === "Decide" || ev.type === "Propagate") {
      value.set(Math.abs(ev.lit), ev.lit > 0 ? 1 : -1);
      trail.push({ lit: ev.lit, level: ev.level, reason: ev.type === "Decide" ? null : ev.reason, origin: ev.type === "Decide" ? ev.origin?.by : undefined });
      if (ev.type === "Decide") conflict = null;
    } else if (ev.type === "Backjump") {
      for (const l of ev.unassigned) value.delete(Math.abs(l));
      trail.length -= ev.unassigned.length;
      conflict = null;
    } else if (ev.type === "Conflict") conflict = ev.clause;
  }
  return { value, trail, conflict, end };
}

/** Truth of a literal under a state: 1, -1 or 0 (open). */
export const truth = (s: State, l: Lit): 0 | 1 | -1 => {
  const v = s.value.get(Math.abs(l));
  if (!v) return 0;
  return (l > 0 ? v : -v) as 1 | -1;
};

/** Three-valued evaluation of an assertion tree. */
export function evalNode(n: FormulaNode, s: State): 0 | 1 | -1 {
  if ("const" in n) return n.const ? 1 : -1;
  if ("atom" in n) return truth(s, n.atom);
  const a = n.args.map((x) => evalNode(x, s));
  switch (n.op) {
    case "not": return (-a[0]) as 0 | 1 | -1;
    case "and": return a.includes(-1) ? -1 : a.every((x) => x === 1) ? 1 : 0;
    case "or": return a.includes(1) ? 1 : a.every((x) => x === -1) ? -1 : 0;
    case "=>": return a[0] === -1 || a[1] === 1 ? 1 : a[0] === 1 && a[1] === -1 ? -1 : 0;
    case "iff": return a[0] && a[1] ? (a[0] === a[1] ? 1 : -1) : 0;
    case "xor": return a[0] && a[1] ? (a[0] !== a[1] ? 1 : -1) : 0;
    case "ite": return a[0] === 1 ? a[1] : a[0] === -1 ? a[2] : a[1] && a[1] === a[2] ? a[1] : 0;
  }
}
