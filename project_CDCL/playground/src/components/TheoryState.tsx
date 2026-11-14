import type { PlaygroundResponse } from "../api";
import { litText, type Labels } from "../model";

interface Props {
  resp: PlaygroundResponse;
  L: Labels;
}

/** The solvers' raw state at the end of the run, for the curious; folded away. */
export function TheoryState({ resp, L }: Props) {
  const smt = resp.smt!;
  const th = resp.replay.theories;
  return (
    <details className="raw">
        <summary>Raw solver state at the end of the run (Simplex tableau, DT classes)</summary>
        <div className="theory-grid">
          {smt.purified.some((p, i) => p !== smt.assertions[i]) && (
            <div>
              <h4>Purified input</h4>
              <ul className="mono-list">
                {smt.purified.map((p, i) => <li key={i}>{p}</li>)}
                {smt.definitions.map((d, i) => <li key={`d${i}`} className="def">{d}</li>)}
              </ul>
              {smt.shared.length > 0 && (
                <p className="note">Shared constants: {smt.shared.map((s) => `${s.name} (${s.theories.join(", ")})`).join(", ")}</p>
              )}
            </div>
          )}
          {th?.LIA && (
            <div>
              <h4>LIA — Simplex</h4>
              <table>
                <thead><tr><th>variable</th><th>lower</th><th>value</th><th>upper</th></tr></thead>
                <tbody>
                  {th.LIA.cols.filter((c) => !c.slack || c.lo !== null || c.hi !== null).map((c) => (
                    <tr key={c.name}>
                      <td className="mono">{c.name}{c.basic ? " (basic)" : ""}</td>
                      <td title={c.loLit ? litText(L, c.loLit) : ""}>{c.lo ?? "−∞"}</td>
                      <td><b>{c.value}</b></td>
                      <td title={c.hiLit ? litText(L, c.hiLit) : ""}>{c.hi ?? "+∞"}</td>
                    </tr>
                  ))}
                </tbody>
              </table>
              {th.LIA.rows.length > 0 && (
                <ul className="mono-list">{th.LIA.rows.map((r) => <li key={r.basic}>{r.basic} = {r.expr}</li>)}</ul>
              )}
              {th.LIA.last && <p className="note">{th.LIA.last}</p>}
            </div>
          )}
          {th?.DT && (
            <div>
              <h4>DT — congruence closure</h4>
              <ul className="mono-list">
                {th.DT.classes.map((c, i) => (
                  <li key={i}>
                    {"{ "}{c.members.join(", ")}{" }"}
                    {c.ctor && <span className="note"> is {c.ctor}</span>}
                    {c.excluded.length > 0 && <span className="note"> not {c.excluded.join(", ")}</span>}
                  </li>
                ))}
                {th.DT.diseqs.map(([a, b], i) => <li key={`n${i}`}>{a} ≠ {b}</li>)}
              </ul>
              {th.DT.last && <p className="note">{th.DT.last}</p>}
            </div>
          )}
        </div>
    </details>
  );
}
