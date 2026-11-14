import { useEffect, useMemo, useState } from "react";
import type { LiaCheck } from "../api";
import type { Labels } from "../model";
import { num, parseRat } from "./linear";
import { buildLia, type Frame, type LiaModel } from "./liaModel";
import { Plane2D } from "./Plane2D";
import { Space3D } from "./Space3D";

type View = "constraints" | "simplex";

/**
 * One LIA check, in two separate pictures: the constraints one by one (what
 * area each literal rules out), and Simplex's moves with its tableau.
 */
export function LiaView({ check, L }: { check: LiaCheck; L: Labels }) {
  const model = useMemo(() => buildLia(check, L), [check, L]);
  const [view, setView] = useState<View>("constraints");
  const [kc, setKc] = useState(0);
  const [ks, setKs] = useState(0);
  useEffect(() => {
    setKc(0);
    setKs(0);
  }, [check]);
  if (!model) return <p className="empty">No arithmetic literal is in the context yet, so LIA has nothing to check.</p>;
  const frames = view === "constraints" ? model.geometry : model.simplex;
  const k = Math.min(view === "constraints" ? kc : ks, frames.length - 1);
  const setK = view === "constraints" ? setKc : setKs;
  const frame = frames[k];
  const threeD = model.axes.length === 3;

  return (
    <div className="lia">
      <div className="subtabs" role="tablist">
        <button role="tab" aria-selected={view === "constraints"} className={view === "constraints" ? "subtab on" : "subtab"} onClick={() => setView("constraints")}>
          Constraints {threeD ? "in space (3D)" : "in the plane"}
        </button>
        <button role="tab" aria-selected={view === "simplex"} className={view === "simplex" ? "subtab on" : "subtab"} onClick={() => setView("simplex")}>
          Simplex: tableau and pivots
        </button>
      </div>
      <div className="plane">
        <div className="plane-fig">{threeD ? <Space3D model={model} frame={frame} /> : <Plane2D model={model} frame={frame} />}</div>
        <div className="plane-side">
          <div className={`plane-step ${frame.final ?? ""}`}>
            <span className="step-kind">{frame.title}</span>
            <p>{frame.text}</p>
            <div className="mini-nav">
              <button className="ghost" onClick={() => setK((k) => Math.max(0, k - 1))} disabled={k === 0}>← Back</button>
              <span className="counter">{k + 1} / {frames.length}</span>
              <button className="primary" onClick={() => setK((k) => Math.min(frames.length - 1, k + 1))} disabled={k >= frames.length - 1}>Next →</button>
            </div>
          </div>
          {view === "constraints" ? <Inequalities model={model} frame={frame} k={k} /> : <Tableau check={check} frame={frame} />}
          <ul className="legend inline-legend">
            <li><span className="sw space" /> allowed by every literal so far</li>
            <li><span className="sw out" /> ruled out (darker: by several)</li>
            {view === "simplex" && <li><span className="sw pt" /> Simplex's candidate point</li>}
          </ul>
        </div>
      </div>
    </div>
  );
}

function Inequalities({ model, frame, k }: { model: LiaModel; frame: Frame; k: number }) {
  const blameNow = frame.final === "unsat";
  return (
    <ul className="ineqs">
      {model.items.map((it, i) => {
        const seen = frame.drawn.includes(i) || (!it.flat && k >= (model.firstSeen.get(i) ?? 1e9));
        if (!seen) return null;
        return (
          <li key={i} className={`${i === frame.fresh ? "fresh" : ""} ${it.derived ? "derived" : ""} ${blameNow && model.conflictIds.has(i) ? "blame" : ""}`}>
            {it.derived ? (
              <span><b>{it.text}</b> <span className="note">eliminating {it.eliminated}</span></span>
            ) : (
              <span>
                <span className="mono">{it.label}</span> <span className="arrow">⇒</span> <b>{it.text}</b>
                {!it.flat && <span className="note"> (not drawn: uses {[...it.a.keys()].filter((v) => !model.axes.includes(v)).join(", ")})</span>}
              </span>
            )}
          </li>
        );
      })}
    </ul>
  );
}

/** The tableau at this Simplex step; the next pivot's row (red) and column (blue) are marked. */
function Tableau({ check, frame }: { check: LiaCheck; frame: Frame }) {
  const i = frame.simplex ?? 0;
  const st = check.steps[i];
  if (!st) return null;
  const next = frame.final ? null : check.steps[i + 1]?.pivot ?? null;
  const leave = next?.[0] ?? (frame.final === "unsat" ? check.stuck : null);
  const enter = next?.[1] ?? null;
  const show = (s: string | null) => (s === null ? "—" : num(parseRat(s)));
  const outside = (c: (typeof st.cols)[number]) => {
    const v = parseRat(c.value);
    return (c.lo !== null && v < parseRat(c.lo)) || (c.hi !== null && v > parseRat(c.hi));
  };
  return (
    <div className="tableau">
      <h5>Rows: each basic variable in terms of the others</h5>
      <ul className="rows">
        {st.rows.map(([b, e]) => (
          <li key={b} className={b === leave ? "leave" : ""}>
            <span className="mono">{b} = {e}</span>
          </li>
        ))}
      </ul>
      <h5>Variables: value and bounds (from the literals)</h5>
      <table>
        <thead>
          <tr><th>variable</th><th>value</th><th>lower</th><th>upper</th><th></th></tr>
        </thead>
        <tbody>
          {st.cols.map((c) => (
            <tr key={c.name} className={`${c.name === leave ? "leave" : ""} ${c.name === enter ? "enter" : ""}`}>
              <td className="mono">{c.name}</td>
              <td className={outside(c) ? "bad" : ""}>{show(c.value)}</td>
              <td>{show(c.lo)}</td>
              <td>{show(c.hi)}</td>
              <td className="role">{c.basic ? "basic" : "non-basic"}{outside(c) ? " · out of bounds" : ""}</td>
            </tr>
          ))}
        </tbody>
      </table>
    </div>
  );
}
