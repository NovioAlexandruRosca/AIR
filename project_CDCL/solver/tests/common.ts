// Shared test helper: replay a solver trace and check that every recorded
// step is legal. This is exactly what the visualizer relies on.
// (Port of tests/common/mod.rs.)

import type { Cnf } from "../src/dimacs";
import { lit_to_dimacs } from "../src/lit";
import { Status, Status_as_str } from "../src/solver";
import type { Event } from "../src/trace";

function fail(msg: string): never {
  throw new Error(msg);
}

/** `assert!(cond, msg)` */
export function assert(cond: boolean, msg = "assertion failed"): asserts cond {
  if (!cond) fail(msg);
}

/** `assert_eq!(a, b, msg)` (structural, via JSON for arrays). */
export function assert_eq<T>(a: T, b: T, msg = ""): void {
  const same = Array.isArray(a) || Array.isArray(b) ? JSON.stringify(a) === JSON.stringify(b) : a === b;
  if (!same) fail(`assertion \`left == right\` failed${msg ? ": " + msg : ""}\n  left: ${JSON.stringify(a)}\n right: ${JSON.stringify(b)}`);
}

/** Replay a trace of a DIMACS run and check it against the clause database. */
export function check_trace(cnf: Cnf, events: Event[], status: Status): void {
  const clauses: number[][] = cnf.clauses.map((c) => c.map((l) => lit_to_dimacs(l)));
  check_trace_raw(cnf.num_vars, clauses, events, Status_as_str(status));
}

/** Replay any trace (SAT or SMT): `clauses` are the original clauses,
 * learned and theory clauses are taken from the events. */
export function check_trace_raw(num_vars: number, clauses: number[][], events: Event[], status: string): void {
  clauses = clauses.slice();
  const num_original = clauses.length;
  const value: (boolean | null)[] = new Array(num_vars + 1).fill(null);
  const level_of: number[] = new Array(num_vars + 1).fill(0);
  const trail: number[] = [];
  let level = 0;
  const val = (value: (boolean | null)[], l: number): boolean | null => {
    const v = value[Math.abs(l)];
    return v === null || v === undefined ? null : v === l > 0;
  };

  for (const e of events) {
    switch (e.kind) {
      case "Decide": {
        const lit = e.lit;
        assert_eq(val(value, lit), null, "decision on assigned var");
        level += 1;
        assert_eq(e.level, level);
        value[Math.abs(lit)] = lit > 0;
        level_of[Math.abs(lit)] = level;
        trail.push(lit);
        break;
      }
      case "Propagate": {
        const lit = e.lit;
        assert_eq(e.level, level);
        const c = clauses[e.reason];
        assert(c.includes(lit), "reason clause lacks the literal");
        for (const o of c.filter((o) => o !== lit)) {
          assert_eq(val(value, o), false, "reason clause not unit");
        }
        assert_eq(val(value, lit), null);
        value[Math.abs(lit)] = lit > 0;
        level_of[Math.abs(lit)] = level;
        trail.push(lit);
        break;
      }
      case "Conflict": {
        assert_eq(e.level, level);
        for (const o of clauses[e.clause]) {
          assert_eq(val(value, o), false, "conflict clause not falsified");
        }
        break;
      }
      case "Resolve": {
        assert(!e.resolvent.some((l) => Math.abs(l) === e.pivot));
        break;
      }
      case "Learn": {
        const { lits, uip } = e;
        assert_eq(e.clause, clauses.length);
        assert(lits.includes(-uip));
        // Exactly one literal at the conflict level: the negated UIP.
        const at_cur = lits.filter((l) => level_of[Math.abs(l)] === level);
        assert_eq(at_cur, [-uip]);
        for (const l of lits) {
          assert_eq(val(value, l), false);
        }
        const bt = lits
          .filter((l) => l !== -uip)
          .map((l) => level_of[Math.abs(l)])
          .reduce((a, b) => Math.max(a, b), 0);
        assert_eq(e.backjump_level, bt);
        clauses.push(lits.slice());
        break;
      }
      case "Backjump": {
        const { from, to, unassigned } = e;
        assert_eq(from, level);
        assert(to < from);
        const keep = trail.length - unassigned.length;
        assert_eq(trail.slice(keep), unassigned);
        for (const l of unassigned) {
          assert(level_of[Math.abs(l)] > to);
          value[Math.abs(l)] = null;
        }
        trail.length = keep;
        level = to;
        break;
      }
      case "TheoryClause": {
        assert_eq(e.clause, clauses.length, "theory clause ids are sequential");
        clauses.push(e.lits.slice());
        break;
      }
      case "NewVar": {
        assert_eq(e.var, value.length, "new variables are numbered consecutively");
        value.push(null);
        level_of.push(0);
        break;
      }
      case "Theory":
        break;
      case "Result": {
        assert_eq(e.status, status);
        if (status === "SAT") {
          const model = new Set(e.model);
          for (const c of clauses.slice(0, num_original)) {
            assert(
              c.some((l) => model.has(l)),
              "model violates an original clause",
            );
          }
        }
        break;
      }
    }
  }
}
