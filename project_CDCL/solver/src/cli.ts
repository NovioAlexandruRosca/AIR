// Command-line solver (port of src/main.rs without the `serve` mode: the
// playground now runs the solver in the browser).
//
//   npx tsx src/cli.ts <file.cnf|file.smt2|-> [--trace out.json] ...
//   (from the project root: npm run solve -- <file> ...)

import { readFileSync, writeFileSync } from "node:fs";
import { resolve } from "node:path";
import { parse } from "./dimacs";
import { DEFAULT_TRACE_LIMIT, Limits, run_json, Timing } from "./lib";
import { looks_like_smtlib, model_smtlib, result_json, solve as smt_solve } from "./smt/mod";
import { Solver, Status_as_str, StopReason_as_str, verify_model } from "./solver";
import { Tracer } from "./trace";
import { now, RustErr } from "./util";

const USAGE = `\
CDCL SAT solver (MOMS decisions, First-UIP learning, backjumping) and
CDCL(T) SMT solver for LIA + algebraic datatypes (Nelson–Oppen)

USAGE:
  npm run solve -- <file.cnf|file.smt2> [--trace <out.json>] [--trace-limit <N>] [--max-conflicts <N>] [--timeout <T>]

  <file>              DIMACS CNF, or SMT-LIB 2 (.smt2 or text starting with '(');
                      '-' reads stdin
  --trace <out.json>  write the solver's step-by-step trace as JSON
  --trace-limit <N>   stop recording after N events (default 20000)
  --max-conflicts <N> give up (s UNKNOWN) after N conflicts
  --timeout <T>       give up (s UNKNOWN) after T: 30, 30s, 500ms, 2m, or none
  --no-reduce         never delete learned clauses (by default the worse half is
                      deleted once 8000+ are kept; never happens inside a trace)

Exit code: 10 = SAT, 20 = UNSAT, 0 = UNKNOWN, 1 = error.`;

interface Args {
  input: string | null;
  trace: string | null;
  trace_limit: number;
  max_conflicts: number | null;
  /** ms; null = no limit */
  timeout: number | null;
  no_reduce: boolean;
}

function parse_timeout(s: string): number | null {
  const bad = () => new RustErr(`--timeout expects e.g. 30, 30s, 500ms, 2m or none, got "${s}"`);
  if (s === "none" || s === "0") return null;
  let num = s;
  let scale = 1;
  if (s.endsWith("ms")) [num, scale] = [s.slice(0, -2), 0.001];
  else if (s.endsWith("s")) [num, scale] = [s.slice(0, -1), 1];
  else if (s.endsWith("m")) [num, scale] = [s.slice(0, -1), 60];
  const secs = Number(num) * scale;
  if (num.trim() === "" || !(Number.isFinite(secs) && secs > 0)) throw bad();
  return secs * 1000;
}

function parse_args(argv: string[]): Args {
  const args: Args = { input: null, trace: null, trace_limit: DEFAULT_TRACE_LIMIT, max_conflicts: null, timeout: null, no_reduce: false };
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    const value = (name: string) => {
      if (i + 1 >= argv.length) throw new RustErr(`${name} needs a value`);
      return argv[++i];
    };
    const int = (name: string) => {
      const v = value(name);
      if (!/^\d+$/.test(v)) throw new RustErr(`${name} expects a number`);
      return Number(v);
    };
    if (a === "-h" || a === "--help") throw new RustErr("");
    else if (a === "--trace") args.trace = value(a);
    else if (a === "--trace-limit") args.trace_limit = int(a);
    else if (a === "--max-conflicts") args.max_conflicts = int(a);
    else if (a === "--timeout") args.timeout = parse_timeout(value(a));
    else if (a === "--no-reduce") args.no_reduce = true;
    else if (a.startsWith("--")) throw new RustErr(`unknown option ${a}`);
    else if (args.input === null) args.input = a;
    else throw new RustErr(`unexpected argument ${a}`);
  }
  if (args.input === null) throw new RustErr("");
  return args;
}

function main(): number {
  let args: Args;
  try {
    args = parse_args(process.argv.slice(2));
  } catch (e) {
    const msg = e instanceof RustErr ? String(e.value) : String(e);
    if (msg) console.error(`error: ${msg}\n`);
    console.error(USAGE);
    return 1;
  }
  const path = args.input!;
  let text: string;
  try {
    // `npm run solve` runs in solver/: read paths relative to where npm was started
    text = readFileSync(path === "-" ? 0 : resolve(process.env.INIT_CWD ?? ".", path), "utf8");
  } catch (e) {
    console.error(path === "-" ? `error: reading stdin: ${e}` : `error: cannot read ${path}: ${(e as Error).message}`);
    return 1;
  }

  if (path.endsWith(".smt2") || looks_like_smtlib(text)) return run_smt(text, path, args);

  const parse_start = now();
  let cnf;
  try {
    cnf = parse(text);
  } catch (e) {
    console.error(`error: ${path}: ${e instanceof RustErr ? String(e.value) : e}`);
    return 1;
  }
  const parse_ms = now() - parse_start;
  console.log(`c parsed ${cnf.num_vars} variables, ${cnf.clauses.length} clauses`);
  for (const w of cnf.warnings) console.log(`c warning: ${w}`);

  const tracer = args.trace !== null ? Tracer.with_limit(args.trace_limit) : Tracer.disabled();
  const start = now();
  const solver = Solver.with_tracer(cnf, tracer);
  solver.max_conflicts = args.max_conflicts;
  solver.deadline = args.timeout === null ? null : start + args.timeout;
  solver.reduce_db = !args.no_reduce;
  const status = solver.solve();
  const elapsed = now() - start;

  const st = solver.stats;
  console.log(`c decisions ${st.decisions}  propagations ${st.propagations}  conflicts ${st.conflicts}  learned ${st.learned}  deleted ${st.deleted}  max level ${st.max_level}`);
  console.log(`c time ${elapsed.toFixed(3)} ms (parse ${parse_ms.toFixed(3)} ms)${args.trace !== null ? ", tracing on" : ""}`);

  if (args.trace !== null) {
    // This run recorded the trace, so its time includes tracing overhead.
    const timing = new Timing({ parse_ms, solve_ms: elapsed, solve_untraced_ms: null });
    try {
      writeFileSync(resolve(process.env.INIT_CWD ?? ".", args.trace), run_json(cnf, solver, status, timing));
    } catch (e) {
      console.error(`error: cannot write ${args.trace}: ${(e as Error).message}`);
      return 1;
    }
    console.log(`c trace: ${solver.tracer.events.length} events written to ${args.trace}${solver.tracer.truncated ? " (truncated)" : ""}`);
  }

  switch (status) {
    case "Sat": {
      if (!verify_model(cnf, solver.model())) {
        console.error("c ERROR: model does not satisfy the formula");
        return 1;
      }
      console.log(`c model verified against all ${cnf.clauses.length} clauses`);
      console.log("s SATISFIABLE");
      let line = "v";
      for (const x of solver.model_dimacs()) {
        const tok = ` ${x}`;
        if (line.length + tok.length > 78) {
          console.log(line);
          line = "v";
        }
        line += tok;
      }
      console.log(`${line} 0`);
      return 10;
    }
    case "Unsat":
      console.log("s UNSATISFIABLE");
      return 20;
    default:
      if (solver.stop_reason !== null) console.log(`c stopped: ${StopReason_as_str(solver.stop_reason)}`);
      console.log("s UNKNOWN");
      return 0;
  }
}

/** SMT-LIB input: CDCL(T) with the LIA and DT theories. */
function run_smt(text: string, path: string, args: Args): number {
  const limits = new Limits({ max_conflicts: args.max_conflicts, timeout: args.timeout, cancel: null, no_reduce: args.no_reduce });
  const trace_limit = args.trace !== null ? args.trace_limit : null;
  let r;
  try {
    r = smt_solve(text, trace_limit, limits);
  } catch (e) {
    const v = e instanceof RustErr ? (e.value as { to_string?: () => string }) : null;
    console.error(`error: ${path}: ${v && typeof v.to_string === "function" ? v.to_string() : e instanceof Error ? e.message : String(e)}`);
    return 1;
  }
  const p = r.prepared;
  const comb = p.comb;
  const names = comb.theories.map((t) => t.name());
  console.log(`; ${p.problem.assertions.length} assertions, theories ${names.join(" + ")}, ${p.prep.cnf.num_vars} Boolean variables, ${p.prep.cnf.clauses.length} clauses`);
  for (const d of p.prep.definitions) console.log(`; purification: ${comb.terms.display(d)}`);
  if (comb.shared.length > 0) console.log(`; shared constants (Nelson–Oppen): ${comb.shared.map((t) => comb.terms.display(t)).join(", ")}`);
  const st = r.solver.stats;
  console.log(
    `; decisions ${st.decisions}  propagations ${st.propagations}  conflicts ${st.conflicts}  theory propagations ${st.theory_propagations}  theory conflicts ${st.theory_conflicts}  theory splits ${st.theory_splits}`,
  );
  console.log(`; time ${r.timing.solve_ms.toFixed(3)} ms (parse ${r.timing.parse_ms.toFixed(3)} ms)`);

  if (args.trace !== null) {
    try {
      writeFileSync(resolve(process.env.INIT_CWD ?? ".", args.trace), result_json(r));
    } catch (e) {
      console.error(`error: cannot write ${args.trace}: ${(e as Error).message}`);
      return 1;
    }
    console.log(`; trace: ${r.solver.tracer.events.length} events written to ${args.trace}`);
  }

  switch (r.status) {
    case "Sat":
      if (r.verified !== true) {
        console.error("; ERROR: the model does not satisfy every assertion");
        return 1;
      }
      console.log("sat");
      console.log(model_smtlib(r.model));
      console.log(`; model verified against all ${p.problem.assertions.length} assertions`);
      return 10;
    case "Unsat":
      console.log("unsat");
      return 20;
    default:
      if (r.solver.incomplete_reason !== null) console.log(`; ${r.solver.incomplete_reason}`);
      else if (r.solver.stop_reason !== null) console.log(`; stopped: ${StopReason_as_str(r.solver.stop_reason)}`);
      console.log("unknown");
      return 0;
  }
}

void Status_as_str;
process.exitCode = main();
