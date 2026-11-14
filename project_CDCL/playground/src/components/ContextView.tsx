import type { Lit, PlaygroundResponse } from "../api";
import { clauseInfo, litText, visibleVar, type Labels, type State, type TheoryClauseEvent } from "../model";

interface Props {
  resp: PlaygroundResponse;
  L: Labels;
  state: State;
  tcs: Map<number, TheoryClauseEvent>;
  learnedKeys: Set<string>;
  focusLits: Lit[];
}

/** The context M as on the slides: one literal per line, decisions marked. */
export function ContextView({ resp, L, state, tcs, learnedKeys, focusLits }: Props) {
  const focus = new Set(focusLits.map(Math.abs));
  const rows = state.trail.filter((t) => visibleVar(L, Math.abs(t.lit)));
  if (!rows.length) return <p className="empty">Empty — nothing is assigned yet.</p>;

  const why = (t: State["trail"][number]): string => {
    if (t.reason === null) return t.origin === "user" ? "your decision" : t.origin ? `${t.origin} split` : "solver's decision";
    const tc = tcs.get(t.reason);
    if (tc && tc.kind !== "axiom") return `by ${tc.theory}`;
    return clauseInfo(resp, tcs, learnedKeys, t.reason).name.replace(/^the /, "");
  };

  let level = -1;
  return (
    <ul className="context">
      {rows.map((t) => {
        const sep = t.level !== level && level !== -1;
        level = t.level;
        const decision = t.reason === null && t.level > 0;
        return (
          <li key={t.lit} className={`${sep ? "level-start" : ""} ${focus.has(Math.abs(t.lit)) ? "focus" : ""}`}>
            <span className={`chip ${t.lit > 0 ? "t" : "f"} static`}>{litText(L, t.lit)}</span>
            {decision && <span className="d" title="decision">d</span>}
            <span className="why">{why(t)}</span>
          </li>
        );
      })}
    </ul>
  );
}
