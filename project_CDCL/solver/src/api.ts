// The solver's entry points for the browser (port of the request handlers
// in src/server.rs). Each takes the text the Rust server received as an HTTP
// body and returns the JSON text it answered with; failures become
// `{"error": "..."}`, as with the server's 400 responses.

import { parse } from "./dimacs";
import { DEFAULT_TRACE_LIMIT, Limits, solve_to_json as solve_cnf_to_json } from "./lib";
import { looks_like_smtlib, playground_actions_json, solve_to_json as solve_smt_to_json } from "./smt/mod";
import { json_string } from "./trace";
import { now, RustErr } from "./util";

/** The server's defaults: 60 s per request, the default trace limit. */
const SERVE_TIMEOUT_MS = 60_000;

function limits(): Limits {
  const l = new Limits();
  l.timeout = SERVE_TIMEOUT_MS;
  return l;
}

/** The error as Rust's `Display` prints it (SmtError: "line N: ..."). */
function display(v: unknown): string {
  if (typeof v === "string") return v;
  const o = v as { to_string?: () => string };
  return typeof o?.to_string === "function" ? o.to_string() : String(v);
}

const message = (e: unknown): string => (e instanceof RustErr ? display(e.value) : e instanceof Error ? `solver error: ${e.message}` : String(e));

/** Run a handler; anything thrown becomes `{"error": ...}` (the server's `guarded`). */
function guarded(f: () => string): string {
  try {
    return f();
  } catch (e) {
    const out = { v: '{"error":' };
    json_string(out, message(e));
    return out.v + "}";
  }
}

/** `POST /api/solve`: SMT-LIB or DIMACS text → the run as JSON. */
export function api_solve(text: string): string {
  return guarded(() => {
    if (looks_like_smtlib(text)) return solve_smt_to_json(text, DEFAULT_TRACE_LIMIT, limits());
    const start = now();
    const cnf = parse(text);
    return solve_cnf_to_json(cnf, DEFAULT_TRACE_LIMIT, limits(), now() - start);
  });
}

/**
 * `POST /api/playground`. Body: a `DECISIONS 3 -5 u7 ...` line (`u<lit>` =
 * propagate the unit clause forcing lit), optionally a `LEMMAS 1 -2 0 3 4 0`
 * line (clauses kept from earlier conflicts), optionally an
 * `OPTIONS [no-theory-propagation] [finish]` line, then the formula.
 */
export function api_playground(body: string): string {
  return guarded(() => {
    const split = (s: string): [string, string | null] => {
      const i = s.indexOf("\n");
      return i < 0 ? [s, null] : [s.slice(0, i), s.slice(i + 1)];
    };
    let [first, rest] = split(body);
    rest ??= "";
    const dec = first.trim();
    if (!dec.startsWith("DECISIONS")) throw new RustErr("playground request must start with a DECISIONS line");
    const actions: [boolean, number][] = [];
    for (const t of dec.slice("DECISIONS".length).split(/\s+/).filter(Boolean)) {
      const pick = t.startsWith("u");
      const n = Number(pick ? t.slice(1) : t);
      if (/^-?\d+$/.test(pick ? t.slice(1) : t)) actions.push([pick, n]);
    }
    const lemmas: number[][] = [];
    let [line, after] = split(rest);
    if (after !== null && line.trim().startsWith("LEMMAS")) {
      let cur: number[] = [];
      for (const t of line.trim().slice("LEMMAS".length).split(/\s+/).filter((x) => /^-?\d+$/.test(x))) {
        const x = Number(t);
        if (x === 0) {
          lemmas.push(cur);
          cur = [];
        } else cur.push(x);
      }
      rest = after;
    }
    let theory_propagation = true;
    let finish = false;
    [line, after] = split(rest);
    if (after !== null && line.trim().startsWith("OPTIONS")) {
      const opts = line.trim().slice("OPTIONS".length).split(/\s+/);
      theory_propagation = !opts.includes("no-theory-propagation");
      finish = opts.includes("finish");
      rest = after;
    }
    return playground_actions_json(rest, actions, lemmas, theory_propagation, finish);
  });
}
