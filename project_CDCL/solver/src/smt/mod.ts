//! CDCL(T): satisfiability modulo theories on top of the CDCL solver.
//!
//! Pipeline: SMT-LIB text → terms ([`parser`]) → purification + Tseitin
//! ([`preprocess`]) → CDCL search where the [`combine::Combination`] of
//! theories is the solver's theory hook → model built by the theories and
//! verified by evaluating every assertion.
//!
//! Adding a theory: implement [`theory::Theory`] and add it to
//! [`default_theories`]. Parsing, purification, Nelson–Oppen combination and
//! the SAT solver need no change.
// (port of src/smt/mod.rs)

import { Action, Replay, Solver, Status } from "../solver";
import { json_string, Tracer } from "../trace";
import { DEFAULT_TRACE_LIMIT, Limits, run_json_ext, Timing } from "../lib";
import { Cnf, parse } from "../dimacs";
import { Lit, lit_from_dimacs, lit_new, lit_to_dimacs, lit_var } from "../lit";
import { Combination, HookAdapter } from "./combine";
import { looks_like_smtlib, parse_problem, Problem } from "./parser";
import { preprocess, Prep } from "./preprocess";
import { BOOL, TermId, Value, Value_to_string } from "./term";
import { Theory } from "./theory";
import { Lia } from "./lia";
import { Dt } from "./dt";
import { now, RustErr } from "../util";

export { looks_like_smtlib } from "./parser";

/** The theories every SMT problem is solved with, in registration order.
 * To add a theory, implement `Theory` and list it here. */
export function default_theories(): Theory[] {
  return [Lia.new(), Dt.new()];
}

export class Prepared {
  constructor(
    public comb: Combination,
    public problem: Problem,
    public prep: Prep,
    public parse_ms: number,
  ) {}
}

/** Parse and preprocess an SMT-LIB problem. Throws `RustErr<SmtError>`. */
export function prepare(text: string): Prepared {
  const start = now();
  const comb = Combination.new(default_theories());
  const problem = parse_problem(text, comb.terms, comb.theories);
  const prep = preprocess(problem, comb);
  return new Prepared(comb, problem, prep, now() - start);
}

export class ModelEntry {
  constructor(
    public name: string,
    public sort: string,
    public value: string,
  ) {}
}

export class SmtResult {
  constructor(
    public status: Status,
    public solver: Solver,
    public prepared: Prepared,
    public model: ModelEntry[],
    /** Every assertion evaluates to true under the model (SAT only). */
    public verified: boolean | null,
    public timing: Timing,
  ) {}
}

/** `Display` of `SmtError` / `ParseError` (`line N: msg`, or just `msg` on line 0). */
function err_to_string(e: unknown): string {
  if (typeof e === "string") return e;
  const x = e as { line: number; message: string };
  return x.line === 0 ? x.message : `line ${x.line}: ${x.message}`;
}

function value_is_true(v: Value | null): boolean {
  return v !== null && v.kind === "Bool" && v._0 === true;
}

function configure(s: Solver, limits: Limits, start: number): void {
  s.max_conflicts = limits.max_conflicts;
  s.deadline = limits.timeout !== null ? start + limits.timeout : null;
  s.cancel = limits.cancel;
  s.reduce_db = !limits.no_reduce;
}

/** Throws `RustErr<SmtError>`. */
export function solve(text: string, trace_limit: number | null, limits: Limits): SmtResult {
  const prepared = prepare(text);
  const tracer = trace_limit !== null ? Tracer.with_limit(trace_limit) : Tracer.disabled();
  const solver = Solver.with_tracer(prepared.prep.cnf, tracer);
  const start = now();
  configure(solver, limits, start);
  solver.hook = new HookAdapter(prepared.comb);
  const status = solver.solve();
  const solve_ms = now() - start;
  const [model, verified] = status === "Sat" ? extract_model(prepared, solver) : [[], null];
  const timing = new Timing();
  timing.parse_ms = prepared.parse_ms;
  timing.solve_ms = solve_ms;
  timing.solve_untraced_ms = null;
  return new SmtResult(status, solver, prepared, model, verified, timing);
}

function extract_model(p: Prepared, solver: Solver): [ModelEntry[], boolean | null] {
  const comb = p.comb;
  const sat_model = solver.model();
  const bools = (t: TermId): boolean | null => {
    // After a full solve the SAT model is set; after a playground replay
    // read the current assignment instead.
    const v = p.prep.bool_vars.get(t);
    let r: boolean | null = null;
    if (v !== undefined) {
      if (sat_model.length === 0) {
        r = solver.value(lit_new(v, true));
      } else {
        r = v < sat_model.length ? sat_model[v] : null;
      }
    }
    return r ?? false;
  };
  const entries: ModelEntry[] = [];
  for (const c of p.problem.consts) {
    const terms = comb.terms;
    const value: Value | null =
      terms.sort(c) === BOOL ? { kind: "Bool", _0: bools(c) ?? false } : comb.eval(c, bools);
    entries.push(
      new ModelEntry(terms.var_name(c) ?? "?", terms.sort_name(terms.sort(c)), value !== null ? Value_to_string(value) : "?"),
    );
  }
  const verified = comb.model_ready && p.problem.assertions.every((a) => value_is_true(comb.eval(a, bools)));
  return [entries, verified];
}

function json_list(out: { v: string }, items: Iterable<string>): void {
  out.v += "[";
  let i = 0;
  for (const s of items) {
    if (i > 0) out.v += ",";
    json_string(out, s);
    i++;
  }
  out.v += "]";
}

/** The `"smt":{...},` section of a trace. */
function smt_section(
  p: Prepared,
  solver: Solver,
  model: ModelEntry[],
  verified: boolean | null,
  all_vars: boolean,
): string {
  const comb = p.comb;
  const terms = comb.terms;
  const s = { v: '"smt":{"theories":' };
  json_list(
    s,
    comb.theories.map((t) => t.name()),
  );
  s.v += ',"assertions":';
  json_list(s, p.prep.assertions);
  s.v += ',"purified":';
  json_list(s, p.prep.purified);
  s.v += ',"definitions":';
  json_list(
    s,
    p.prep.definitions.map((d) => terms.display(d)),
  );
  s.v += ',"fresh":';
  json_list(
    s,
    p.prep.fresh.map((f) => terms.display(f)),
  );
  s.v += ',"shared":[';
  comb.shared.forEach((v, i) => {
    if (i > 0) s.v += ",";
    s.v += '{"name":';
    json_string(s, terms.display(v));
    s.v += ',"theories":';
    json_list(
      s,
      (comb.uses.get(v) ?? []).map((t) => comb.theory_name(t)),
    );
    s.v += "}";
  });
  s.v += '],"interface":[';
  comb.interface.forEach(([x, y, v], i) => {
    if (i > 0) s.v += ",";
    s.v += '{"x":';
    json_string(s, terms.display(x));
    s.v += ',"y":';
    json_string(s, terms.display(y));
    s.v += `,"var":${v + 1}}`;
  });
  s.v += '],"vars":[';
  const n = all_vars ? comb.vars.length : p.prep.cnf.num_vars;
  comb.vars.slice(0, n).forEach((info, i) => {
    if (i > 0) s.v += ",";
    info.write_json(i, s);
  });
  s.v += '],"clause_origin":';
  json_list(s, p.prep.clause_origin);
  s.v += ',"model":[';
  model.forEach((m, i) => {
    if (i > 0) s.v += ",";
    s.v += '{"name":';
    json_string(s, m.name);
    s.v += ',"sort":';
    json_string(s, m.sort);
    s.v += ',"value":';
    json_string(s, m.value);
    s.v += "}";
  });
  s.v += `],"model_verified":${verified === null ? "null" : `${verified}`},"incomplete":`;
  if (solver.incomplete_reason !== null) json_string(s, solver.incomplete_reason);
  else s.v += "null";
  s.v += ',"final":';
  s.v += comb.snapshot_all();
  s.v += "},";
  return s.v;
}

/** Full trace JSON of an SMT run (same format as SAT traces plus "smt"). */
export function result_json(r: SmtResult): string {
  const extra = smt_section(r.prepared, r.solver, r.model, r.verified, false);
  return run_json_ext(r.prepared.prep.cnf, r.solver, r.status, r.timing, extra);
}

/** Solve and return the JSON trace (used by the web server).
 * Throws `RustErr<SmtError>`. */
export function solve_to_json(text: string, trace_limit: number, limits: Limits): string {
  const r = solve(text, trace_limit, limits);
  return result_json(r);
}

function replay_section(solver: Solver, r: Replay, theories: string | null): string {
  const s = {
    v: `"replay":{"outcome":"${r.outcome}","applied":${r.applied},"conflict":${
      r.conflict === null ? "null" : `${r.conflict}`
    },"skipped":[`,
  };
  r.skipped.forEach(([idx, v], i) => {
    if (i > 0) s.v += ",";
    s.v += `[${idx},${v}]`;
  });
  s.v += '],"split":';
  if (r.split !== null) {
    const [lit, by, why] = r.split;
    s.v += `{"lit":${lit_to_dimacs(lit)},"by":`;
    json_string(s, by);
    s.v += ',"why":';
    json_string(s, why);
    s.v += "}";
  } else {
    s.v += "null";
  }
  s.v += `,"finish_from":${r.finish_from === null ? "null" : `${r.finish_from}`}`;
  s.v += ',"learned":';
  if (r.learned !== null) {
    s.v += "[";
    r.learned.forEach((l, i) => {
      if (i > 0) s.v += ",";
      s.v += `${lit_to_dimacs(l)}`;
    });
    s.v += "]";
  } else {
    s.v += "null";
  }
  s.v += ',"units":[';
  r.units.forEach(([cid, l], i) => {
    if (i > 0) s.v += ",";
    s.v += `{"clause":${cid},"lit":${lit_to_dimacs(l)}}`;
  });
  s.v += '],"note":';
  if (r.note !== null) json_string(s, r.note);
  else s.v += "null";
  s.v += ',"trail":[';
  solver.trail().forEach((l, i) => {
    if (i > 0) s.v += ",";
    const reason = solver.var_reason(lit_var(l));
    s.v += `{"lit":${lit_to_dimacs(l)},"level":${solver.var_level(lit_var(l))},"reason":${
      reason === null ? "null" : `${reason}`
    }}`;
  });
  s.v += '],"db":[';
  solver.clauses().forEach((c, i) => {
    if (i > 0) s.v += ",";
    s.v += "[";
    c.lits.forEach((l, j) => {
      if (j > 0) s.v += ",";
      s.v += `${lit_to_dimacs(l)}`;
    });
    s.v += "]";
  });
  s.v += '],"open":[';
  open_vars(solver).forEach((v, i) => {
    if (i > 0) s.v += ",";
    s.v += `${v + 1}`;
  });
  s.v += `],"num_vars":${solver.num_vars()},"theories":`;
  s.v += theories ?? "null";
  s.v += "},";
  return s.v;
}

/** Playground: replay the user's decisions on a fresh solver (SAT or SMT
 * input) and report the resulting state. Stateless, so every click is an
 * independent, reproducible request.
 * The assertions as written, as JSON trees whose leaves point at the
 * Boolean variables of their (purified) atoms: what the playground shows
 * and lets the user click. */
function formula_json(p: Prepared): string {
  const tree = (comb: Combination, prep: Prep, t: TermId, out: { v: string }): void => {
    const terms = comb.terms;
    const node = terms.node(t);
    const sym = terms.sym(t);
    let connective: string | null = null;
    if (sym !== null && ["and", "or", "not", "=>", "xor", "ite"].includes(sym)) connective = sym;
    else if (sym === "=" && terms.sort(node.args[0]) === BOOL) connective = "iff";
    if (node.op.kind === "True") {
      out.v += '{"const":true}';
    } else if (node.op.kind === "False") {
      out.v += '{"const":false}';
    } else if (connective !== null) {
      out.v += `{"op":"${connective}","args":[`;
      node.args.forEach((a, i) => {
        if (i > 0) out.v += ",";
        tree(comb, prep, a, out);
      });
      out.v += "]}";
    } else {
      let v: number | undefined;
      if (node.op.kind === "Var") {
        v = prep.bool_vars.get(t);
      } else {
        const pure = prep.atom_map.get(t) ?? t;
        v = comb.atom_of.get(pure);
      }
      out.v += `{"atom":${v === undefined ? 0 : v + 1},"label":`;
      json_string(out, terms.display(t));
      out.v += "}";
    }
  };
  const comb = p.comb;
  const s = { v: '"formula":[' };
  p.problem.assertions.forEach((a, i) => {
    if (i > 0) s.v += ",";
    tree(comb, p.prep, a, s);
  });
  s.v += "],";
  return s.v;
}

/** Lemmas the playground keeps across replays (only over variables that
 * exist before search starts, so they mean the same thing every time). */
function add_lemmas(cnf: Cnf, origin: string[] | null, lemmas: number[][]): void {
  const n = cnf.num_vars;
  for (const c of lemmas) {
    if (c.length === 0 || c.some((l) => l === 0 || Math.abs(l) > n)) {
      continue;
    }
    cnf.clauses.push(c.map((l) => lit_from_dimacs(l)));
    if (origin !== null) {
      origin.push("clause learned earlier in the playground");
    }
  }
}

/** Is every unsatisfied problem clause open only in atoms a theory created
 * for itself (bound atoms defining an equality, branch atoms, testers)? */
export function only_helpers_open(solver: Solver, comb: Combination): boolean {
  let any = false;
  for (const c of solver.clauses()) {
    if (c.learnt || c.deleted || c.lits.some((l) => solver.value(l) === true)) {
      continue;
    }
    for (const l of c.lits) {
      if (solver.value(l) === null) {
        any = true;
        const v = comb.vars[lit_var(l)];
        if (v === undefined || v.kind !== "TheoryAtom") {
          return false;
        }
      }
    }
  }
  return any;
}

/** The variables still to decide: unassigned literals of the problem clauses
 * (input clauses and theory axioms) that are not satisfied yet. */
export function open_vars(solver: Solver): number[] {
  const out: number[] = [];
  const seen = new Set<number>();
  for (const c of solver.clauses()) {
    if (c.learnt || c.deleted || c.lits.some((l) => solver.value(l) === true)) {
      continue;
    }
    for (const l of c.lits) {
      if (solver.value(l) === null && !seen.has(lit_var(l))) {
        seen.add(lit_var(l));
        out.push(lit_var(l));
      }
    }
  }
  return out;
}

/** "Let the solver finish": continue with ordinary CDCL(T) search from the
 * user's decisions (it may backjump over them) until SAT or UNSAT. */
export function finish_search(solver: Solver, replay: Replay): void {
  if (!(replay.outcome === "open" || replay.outcome === "split" || replay.outcome === "units")) {
    return;
  }
  solver.flush_pending_units();
  replay.split = null;
  replay.units.length = 0;
  replay.finish_from = solver.tracer.events.length;
  const st = solver.solve();
  replay.outcome = st === "Sat" ? "sat" : st === "Unsat" ? "unsat" : "unknown";
}

/** Throws `RustErr<string>`. */
export function playground_json(
  text: string,
  decisions: number[],
  lemmas: number[][],
  theory_propagation: boolean,
  finish: boolean,
): string {
  const actions: [boolean, number][] = decisions.map((d) => [false, d]);
  return playground_actions_json(text, actions, lemmas, theory_propagation, finish);
}

/** Like `playground_json`, but `actions` also holds picks `(true, lit)`: which
 * unit clause to propagate when several are unit at once.
 * Throws `RustErr<string>`. */
export function playground_actions_json(
  text: string,
  actions: [boolean, number][],
  lemmas: number[][],
  theory_propagation: boolean,
  finish: boolean,
): string {
  const to_actions = (n: number): Action[] =>
    actions
      .filter(([, d]) => d !== 0 && Math.abs(d) <= n)
      .map(([pick, d]): Action => {
        const l = lit_from_dimacs(d);
        return pick ? { kind: "Pick", _0: l } : { kind: "Decide", _0: l };
      });
  const timing = new Timing();
  if (looks_like_smtlib(text)) {
    let prepared: Prepared;
    try {
      prepared = prepare(text);
    } catch (e) {
      if (!(e instanceof RustErr)) throw e;
      throw new RustErr(err_to_string(e.value));
    }
    add_lemmas(prepared.prep.cnf, prepared.prep.clause_origin, lemmas);
    const solver = Solver.with_tracer(prepared.prep.cnf, Tracer.with_limit(DEFAULT_TRACE_LIMIT));
    prepared.comb.theory_propagation = theory_propagation;
    solver.hook = new HookAdapter(prepared.comb);
    // Decisions may name variables created during earlier replays (e.g.
    // split atoms); those are only valid once they exist again.
    const acts = to_actions(Infinity);
    // Unit clauses over atoms the user sees are chosen by the user;
    // those over helper atoms are propagated automatically.
    const comb = prepared.comb;
    const choosable = (l: Lit): boolean => {
      const v = comb.vars[lit_var(l)];
      return v !== undefined && (v.kind === "Atom" || v.kind === "Bool");
    };
    const replay = solver.replay_actions(acts, !finish, choosable);
    // When the only open choices are the theories' own helper atoms
    // (e.g. which side of x ≠ y), nothing instructive is left to decide
    // by hand: let the solver complete them. The page shows such an
    // equality split into its two halves.
    const auto = !finish && replay.outcome === "open" && only_helpers_open(solver, prepared.comb);
    if (auto) {
      replay.note =
        "only the theories' helper atoms were left (an equality is decided through ≤ and ≥), so the solver decided them";
    }
    if (finish || auto) {
      // The solver's own run uses theory propagation: much shorter.
      prepared.comb.theory_propagation = true;
      finish_search(solver, replay);
    }
    const theories = prepared.comb.snapshot_all();
    const [model, verified] = replay.outcome === "sat" ? extract_model(prepared, solver) : [[], null];
    let extra = smt_section(prepared, solver, model, verified, true);
    extra += formula_json(prepared);
    extra += replay_section(solver, replay, theories);
    return run_json_ext(prepared.prep.cnf, solver, "Unknown", timing, extra);
  } else {
    let cnf: Cnf;
    try {
      cnf = parse(text);
    } catch (e) {
      if (!(e instanceof RustErr)) throw e;
      throw new RustErr(err_to_string(e.value));
    }
    add_lemmas(cnf, null, lemmas);
    const solver = Solver.with_tracer(cnf, Tracer.with_limit(DEFAULT_TRACE_LIMIT));
    const acts = to_actions(cnf.num_vars);
    const replay = solver.replay_actions(acts, !finish, (_) => true);
    if (finish) {
      finish_search(solver, replay);
    }
    const extra = replay_section(solver, replay, null);
    return run_json_ext(cnf, solver, "Unknown", timing, extra);
  }
}

/** SMT-LIB style model: `(define-fun x () Int 3)` lines. */
export function model_smtlib(model: ModelEntry[]): string {
  let s = "(\n";
  for (const m of model) {
    s += `  (define-fun ${m.name} () ${m.sort} ${m.value})\n`;
  }
  s += ")";
  return s;
}
