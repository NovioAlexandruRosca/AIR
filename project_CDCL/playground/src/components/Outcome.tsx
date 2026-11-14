import type { Lit, PlaygroundResponse } from "../api";
import { assignText, clauseText, litText, theoryName, visibleVar, type Labels, type State } from "../model";
import { previewText, type Preview } from "../preview";

interface Props {
  resp: PlaygroundResponse;
  L: Labels;
  state: State;
  hasDecisions: boolean;
  onBacktrack: () => void;
  onDecide: (l: Lit) => void;
  onFinish: () => void;
  /** this literal already led to a conflict under the current decisions */
  refuted: (l: Lit) => boolean;
  preview: Preview | null;
  onPreview: (l: Lit | null, pick?: boolean) => void;
  onPick: (l: Lit) => void;
}

/** What to do now that every step has been shown. */
export function Outcome({ resp, L, state, hasDecisions, onBacktrack, onDecide, onFinish, refuted, preview, onPreview, onPick }: Props) {
  const rp = resp.replay;
  const theories = resp.smt ? theoryName(resp) + "-" : "";

  if (rp.outcome === "unsat" || (rp.outcome === "conflict" && !hasDecisions)) {
    return (
      <div className="outcome">
        <div className="burst unsat">⇒ Input is {theories}unsat</div>
        <p className="outcome-text">A conflict that no decision can explain: nothing to backtrack, so the formula has no model.</p>
      </div>
    );
  }

  if (rp.outcome === "conflict") {
    const learned = rp.learned && rp.learned.every((l) => Math.abs(l) <= resp.num_vars) ? rp.learned : null;
    return (
      <div className="outcome">
        <div className="callout conflict">
          <b>⇒ Conflicting clause!</b> One of your decisions was wrong.
          {learned && (
            <p>
              CDCL learns <span className="mono">{clauseText(L, learned)}</span> and keeps it, so backtracking flips the last decision for you.
            </p>
          )}
          <button className="primary" onClick={onBacktrack}>Backtrack on the last decision</button>
        </div>
      </div>
    );
  }

  if (rp.outcome === "split" && rp.split) {
    const v = Math.abs(rp.split.lit);
    const tried = [v, -v].filter(refuted);
    // both cases failed and no decision is left to undo: no model at all
    if (tried.length === 2 && !hasDecisions) {
      return (
        <div className="outcome">
          <div className="burst unsat">⇒ Input is {theories}unsat</div>
          <p className="outcome-text">
            {rp.split.by} split on {L.written[v] || L.vars[v]?.label}: both {assignText(L, v)} and {assignText(L, -v)} led to a conflict, and no decision is left to undo. Every case fails, so the formula has no model.
          </p>
        </div>
      );
    }
    return (
      <div className="outcome">
        <div className="callout split">
          <b>{rp.split.by} needs a case split.</b> {rp.split.why}
          {tried.length === 2 ? (
            <>
              <p>Both cases were already tried with these decisions and both led to a conflict: backtrack on a decision.</p>
              <button className="primary" onClick={onBacktrack}>Backtrack on the last decision</button>
            </>
          ) : (
            <>
              {tried.length === 1 && (
                <p>
                  {assignText(L, tried[0])} was already tried and led to a conflict, so only the other case is left.
                </p>
              )}
              <div className="row">
                {[v, -v].map((l) =>
                  refuted(l) ? null : (
                    <button
                      key={l}
                      className={l > 0 ? "true" : "false"}
                      onClick={() => onDecide(l)}
                      onMouseEnter={() => onPreview(l)}
                      onMouseLeave={() => onPreview(null)}
                      onFocus={() => onPreview(l)}
                      onBlur={() => onPreview(null)}
                    >
                      {assignText(L, l)}
                    </button>
                  ),
                )}
              </div>
              <p className="pop-preview">
                {preview && Math.abs(preview.lit) === v ? previewText(preview) : "Point at a case to see what it changes in the formula."}
              </p>
            </>
          )}
        </div>
      </div>
    );
  }

  if (rp.outcome === "units") {
    return (
      <div className="outcome">
        <div className="callout units">
          <b>Several unit clauses at once.</b> {rp.applied === 0 && rp.units.every((u) => (rp.db[u.clause] ?? []).length === 1)
            ? "The input's facts (clauses with one literal) are all unit from the start, so each of them must become true."
            : "The flashing clauses in the formula each have every literal false except one, so that literal must become true."}{" "}
          Click one of them (or its flashing literal) to propagate it first. (The others follow, unless the first one makes them false: a conflict.)
          {rp.units.some((u) => u.clause >= resp.num_original) && (
            <div className="unit-list">
              {rp.units
                .filter((u) => u.clause >= resp.num_original)
                .map((u) => (
                  <button
                    key={u.clause}
                    className={u.lit > 0 ? "true" : "false"}
                    onClick={() => onPick(u.lit)}
                    onMouseEnter={() => onPreview(u.lit, true)}
                    onMouseLeave={() => onPreview(null)}
                  >
                    <span className="mono">{clauseText(L, rp.db[u.clause] ?? [])}</span> forces {assignText(L, u.lit)}
                  </button>
                ))}
            </div>
          )}
          <p className="pop-preview">
            {preview?.pick && rp.units.some((u) => u.lit === preview.lit) ? previewText(preview) : "Point at a flashing clause to see what propagating it changes."}
          </p>
        </div>
      </div>
    );
  }

  if (rp.outcome === "sat") {
    const model = resp.smt?.model ?? [];
    return (
      <div className="outcome">
        <div className="burst sat">⇒ Input is {theories}satisfiable</div>
        {model.length > 0 ? (
          <div className="model">
            {model.map((m) => (
              <span key={m.name} className="model-item"><b>{m.name}</b> = {m.value}</span>
            ))}
          </div>
        ) : (
          <div className="model">
            {state.trail.filter((t) => visibleVar(L, Math.abs(t.lit))).map((t) => (
              <span key={t.lit} className={`chip ${t.lit > 0 ? "t" : "f"} static`}>{litText(L, t.lit)}</span>
            ))}
          </div>
        )}
      </div>
    );
  }

  if (rp.outcome === "unknown") {
    return (
      <div className="outcome">
        <div className="callout">{rp.note ?? "The solver gave up (unknown)."}</div>
      </div>
    );
  }

  // open: the user's turn
  return (
    <div className="outcome">
      <div className="callout hint">
        <b>Your turn:</b> click an open (grey) literal in the formula to decide it
        {rp.note ? <> — {rp.note}</> : "."}
        <button className="ghost" onClick={onFinish}>or let the solver finish</button>
      </div>
    </div>
  );
}
