// What a decision would do, worked out before you make it: the run with the
// decision added, compared with the current state.

import type { Lit, PlaygroundResponse } from "./api";
import { stateAt, visibleVar, type Labels, type State } from "./model";

export interface Preview {
  /** the decision previewed, or the unit clause's literal for a pick */
  lit: Lit;
  pick: boolean;
  /** literals that would get a value as a consequence (not the decision itself) */
  changes: Lit[];
  /** how the run would end */
  outcome: PlaygroundResponse["replay"]["outcome"];
  /** the theory that would reject the context, if one does */
  theory: string | null;
}

export function previewOf(lit: Lit, pick: boolean, r: PlaygroundResponse, now: State, L: Labels): Preview {
  const after = stateAt(r, r.events.length - 1);
  const changes = after.trail
    .map((t) => t.lit)
    .filter((l) => Math.abs(l) !== Math.abs(lit) && Math.abs(l) <= r.num_vars && !now.value.has(Math.abs(l)) && visibleVar(L, Math.abs(l)));
  // the last theory conflict after the decision
  let theory: string | null = null;
  const start = r.events.findIndex((e) => (e.type === "Decide" || e.type === "Propagate") && e.lit === lit);
  for (let i = r.events.length - 1; i > start && start >= 0; i--) {
    const e = r.events[i];
    if (e.type === "TheoryClause" && e.kind === "conflict") {
      theory = e.theory;
      break;
    }
  }
  return { lit, pick, changes, outcome: r.replay.outcome, theory };
}

/** One line for the decision pop-up: what follows the decision. */
export function previewText(p: Preview): string {
  const n = p.changes.length;
  const what = n === 0 ? "nothing else changes" : `${n} more literal${n === 1 ? "" : "s"} get${n === 1 ? "s" : ""} a value (dashed)`;
  const end =
    p.outcome === "conflict" || p.outcome === "unsat"
      ? p.theory
        ? `, then ${p.theory} rejects the context: a conflict`
        : ", then a clause becomes false: a conflict"
      : p.outcome === "sat"
        ? ", and the formula is satisfied"
        : p.outcome === "split"
          ? ", then a theory asks for a case split"
          : p.outcome === "units"
            ? ", then several unit clauses wait for your choice again"
            : "";
  return what + end + ".";
}
