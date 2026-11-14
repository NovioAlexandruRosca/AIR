import { useState } from "react";
import { clip, meet, type Pt } from "../theory/linear";
import type { PlotConstraint, PlotLevel } from "./levels";

const W = 520;
const H = 460;
const M = 34;

type Phase = "line" | "side" | "question" | "branch" | "done";

/** a node of the branch-and-bound tree: the extra bounds of its branch */
interface BNode {
  bounds: { a: number; b: number; c: number; label: string }[];
  parent: number;
  status: "open" | "split" | "empty" | "int";
}

const near = (v: number) => Math.abs(v - Math.round(v)) < 1e-7;
const fmt = (v: number) => {
  if (near(v)) return String(Math.round(v)).replace("-", "−");
  for (let d = 2; d <= 60; d++) if (near(v * d)) return `${Math.round(v * d)}/${d}`.replace("-", "−");
  return v.toFixed(2);
};

/** Draw each constraint: two points on its line, then a point on the allowed side. */
export function Plot({ level, onSolved }: { level: PlotLevel; onSolved: () => void }) {
  const [done, setDone] = useState(0);
  const [phase, setPhase] = useState<Phase>("line");
  const [picks, setPicks] = useState<Pt[]>([]);
  const [msg, setMsg] = useState<{ ok: boolean; text: string } | null>(null);
  const [x0, x1, y0, y1] = level.box;
  const cur: PlotConstraint | undefined = level.constraints[done];
  const [tree, setTree] = useState<BNode[]>([]);
  const [sel, setSel] = useState(0);

  const sx = (x: number) => M + ((x - x0) / (x1 - x0)) * (W - 2 * M);
  const sy = (y: number) => H - M - ((y - y0) / (y1 - y0)) * (H - 2 * M);
  const pts = (p: Pt[]) => p.map(([x, y]) => `${sx(x)},${sy(y)}`).join(" ");
  const big: Pt[] = [
    [x0 - 1, y0 - 1],
    [x1 + 1, y0 - 1],
    [x1 + 1, y1 + 1],
    [x0 - 1, y1 + 1],
  ];
  const drawn = level.constraints.slice(0, done);
  let region: Pt[] = big;
  for (const k of drawn) if (region.length) region = clip(region, k.a, k.b, k.c);
  const segment = (a: number, b: number, c: number): [Pt, Pt] | null => {
    const ends: Pt[] = [];
    for (const e of [[1, 0, x0], [1, 0, x1], [0, 1, y0], [0, 1, y1]] as [number, number, number][]) {
      const p = meet([a, b, c], e);
      if (p && p[0] >= x0 - 1e-9 && p[0] <= x1 + 1e-9 && p[1] >= y0 - 1e-9 && p[1] <= y1 + 1e-9) ends.push(p);
    }
    if (ends.length < 2) return null;
    ends.sort((p, q) => p[0] - q[0] || p[1] - q[1]);
    return [ends[0], ends[ends.length - 1]];
  };
  // the line through the two points you picked
  const yourLine = (): [number, number, number] | null => {
    if (picks.length < 2) return null;
    const [[ax, ay], [bx, by]] = picks;
    return [by - ay, ax - bx, (by - ay) * ax + (ax - bx) * ay];
  };

  const commit = () => {
    setDone((d) => d + 1);
    setPicks([]);
    setPhase(done + 1 < level.constraints.length ? "line" : "question");
  };

  const click = (e: React.MouseEvent<SVGSVGElement>) => {
    if (!cur || (phase !== "line" && phase !== "side")) return;
    const svg = e.currentTarget;
    const pt = svg.createSVGPoint();
    pt.x = e.clientX;
    pt.y = e.clientY;
    const p = pt.matrixTransform(svg.getScreenCTM()!.inverse());
    const wx = Math.round(x0 + ((p.x - M) / (W - 2 * M)) * (x1 - x0));
    const wy = Math.round(y0 + ((H - M - p.y) / (H - 2 * M)) * (y1 - y0));
    if (wx < x0 || wx > x1 || wy < y0 || wy > y1) return;
    const lhs = cur.a * wx + cur.b * wy;
    if (phase === "line") {
      if (lhs !== cur.c) {
        setMsg({
          ok: false,
          text: level.noHints
            ? `(${wx}, ${wy}) is not on the line of ${cur.label}. Try another point.`
            : `(${wx}, ${wy}) is not on the line of ${cur.label}: there ${eq(cur)} would give ${lhs}, not ${cur.c}. Try another point.`,
        });
        return;
      }
      if (picks.some(([x, y]) => x === wx && y === wy)) return;
      const next = [...picks, [wx, wy] as Pt];
      setPicks(next);
      if (next.length === 2) {
        setPhase("side");
        setMsg({ ok: true, text: `Both points are on ${eq(cur)}: that is the line. Now click a point on the side that ${cur.label} allows.` });
      } else setMsg({ ok: true, text: `(${wx}, ${wy}) is on the line. One more point.` });
      return;
    }
    if (lhs === cur.c) {
      setMsg({ ok: false, text: "That point is on the line itself; click one clearly on one side." });
      return;
    }
    if (lhs < cur.c) {
      setMsg({ ok: true, text: `Right: (${wx}, ${wy}) satisfies ${cur.label}. The other side is ruled out (red).` });
      commit();
    } else setMsg({ ok: false, text: `(${wx}, ${wy}) does not satisfy ${cur.label}: that is the side it rules out. Try the other side.` });
  };

  const showMe = () => {
    if (!cur) return;
    setMsg({ ok: true, text: `${cur.label}: the line is ${eq(cur)}, and the allowed side is where ${ineq(cur)}.` });
    commit();
  };

  // ---------------------------------------------------------------- branch and bound
  const regionOf = (n: BNode) => {
    let r = region;
    for (const k of n.bounds) if (r.length) r = clip(r, k.a, k.b, k.c);
    return r;
  };
  /** what Simplex would return for a branch: a vertex, preferably a fractional one */
  const pointOf = (n: BNode): Pt | null => {
    const r = regionOf(n);
    if (!r.length) return null;
    const sorted = [...r].sort((p, q) => p[0] - q[0] || p[1] - q[1]);
    return sorted.find(([x, y]) => !near(x) || !near(y)) ?? sorted[0];
  };
  const statusOf = (n: BNode): BNode["status"] => {
    const p = pointOf(n);
    return !p ? "empty" : near(p[0]) && near(p[1]) ? "int" : "open";
  };
  const startBranch = () => {
    const root: BNode = { bounds: [], parent: -1, status: "open" };
    root.status = statusOf(root);
    setTree([root]);
    setSel(0);
    setPhase("branch");
  };
  const split = (axis: 0 | 1) => {
    const n = tree[sel];
    if (!n || n.status !== "open") {
      setMsg({ ok: false, text: "Pick an open branch first (a yellow one in the tree)." });
      return;
    }
    const p = pointOf(n)!;
    const v = p[axis];
    const name = axis === 0 ? "x" : "y";
    if (near(v)) {
      setMsg({ ok: false, text: `${name} = ${fmt(v)} is already an integer at this point: splitting on it changes nothing. Split on a variable whose value is fractional.` });
      return;
    }
    const lo = Math.floor(v);
    const hi = lo + 1;
    const ax = axis === 0 ? 1 : 0;
    const by = axis === 1 ? 1 : 0;
    const kids: BNode[] = [
      { bounds: [...n.bounds, { a: ax, b: by, c: lo, label: `${name} ≤ ${fmt(lo)}` }], parent: sel, status: "open" },
      { bounds: [...n.bounds, { a: -ax, b: -by, c: -hi, label: `${name} ≥ ${fmt(hi)}` }], parent: sel, status: "open" },
    ];
    kids.forEach((k) => (k.status = statusOf(k)));
    const next = tree.map((m, i) => (i === sel ? { ...m, status: "split" as const } : m)).concat(kids);
    setTree(next);
    const open = next.findIndex((m) => m.status === "open");
    const found = kids.find((k) => k.status === "int");
    if (found) {
      const q = pointOf(found)!;
      setMsg({ ok: true, text: `(${fmt(q[0])}, ${fmt(q[1])}) is an integer point: branch and bound found a solution.` });
      setPhase("done");
      onSolved();
    } else if (open < 0) {
      setMsg({
        ok: true,
        text: `Every branch is empty: each split cut away a strip between two neighbouring integers, and in the end nothing was left. Branch and bound has proved that there is no integer point, although Simplex alone (over the rationals) found one.`,
      });
      setPhase("done");
      onSolved();
    } else {
      setSel(open);
      setMsg({ ok: true, text: `Split on ${name} = ${fmt(v)}: ${kids.map((k) => `${k.bounds[k.bounds.length - 1].label} is ${k.status === "empty" ? "empty" : "still open"}`).join(", ")}.` });
    }
  };
  const nodeLabel = (i: number) => (tree[i].bounds.length ? tree[i].bounds.map((k) => k.label).join(", ") : "the constraints");
  const depth = (j: number): number => (tree[j].parent < 0 ? 0 : 1 + depth(tree[j].parent));

  const anyInteger = () => {
    for (let x = -60; x <= 60; x++) for (let y = -60; y <= 60; y++) if (level.constraints.every((k) => k.a * x + k.b * y <= k.c)) return true;
    return false;
  };
  const answer = (yes: boolean) => {
    const truth = anyInteger();
    if (yes === truth) {
      if (level.branch && !truth) {
        setMsg({ ok: true, text: "Right, no grid dot is green. But Simplex works over the rationals and happily finds a point in the triangle. Branch and bound has to prove that there is no integer one: pick an open branch and split on a variable whose value is fractional, until every branch is empty." });
        startBranch();
        return;
      }
      setMsg({ ok: true, text: truth ? "Right: green integer points are left, so LIA would accept these literals." : "Right: nothing green is left, so LIA would answer \"unsat\"." });
      setPhase("done");
      onSolved();
    } else setMsg({ ok: false, text: truth ? "Look again: some grid points are still green." : "Look again: is any grid point inside the green part?" });
  };

  const ints = (lo: number, hi: number) => Array.from({ length: hi - lo + 1 }, (_, i) => lo + i);
  const line = yourLine();
  const yours = line ? segment(...line) : null;

  return (
    <div className="edu-body plot-level">
      <div className="plane-fig">
        <svg viewBox={`0 0 ${W} ${H}`} onClick={click} className={phase === "line" || phase === "side" ? "clickable" : ""}>
          <defs>
            <clipPath id="edu-plot">
              <rect x={M} y={M} width={W - 2 * M} height={H - 2 * M} />
            </clipPath>
          </defs>
          <g clipPath="url(#edu-plot)">
            {region.length >= 3 && <polygon points={pts(region)} className="region" />}
            {drawn.map((k, i) => {
              const out = clip(big, -k.a, -k.b, -k.c);
              return out.length >= 3 ? <polygon key={i} points={pts(out)} className="out" /> : null;
            })}
          </g>
          {ints(x0, x1).map((x) => (
            <g key={`gx${x}`}>
              <line x1={sx(x)} x2={sx(x)} y1={M} y2={H - M} className={x === 0 ? "axis" : "grid"} />
              <text x={sx(x)} y={H - M + 16} className="tick">{x}</text>
            </g>
          ))}
          {ints(y0, y1).map((y) => (
            <g key={`gy${y}`}>
              <line y1={sy(y)} y2={sy(y)} x1={M} x2={W - M} className={y === 0 ? "axis" : "grid"} />
              <text x={M - 8} y={sy(y) + 4} className="tick end">{y}</text>
            </g>
          ))}
          <text x={W - M} y={H - 6} className="axis-name end">x →</text>
          <text x={M - 4} y={M - 12} className="axis-name">↑ y</text>
          <g clipPath="url(#edu-plot)">
            {ints(x0, x1).flatMap((x) => ints(y0, y1).map((y) => <circle key={`${x},${y}`} cx={sx(x)} cy={sy(y)} r={2.2} className="lat" />))}
            {drawn.map((k, i) => {
              const s = segment(k.a, k.b, k.c);
              return s ? <line key={i} x1={sx(s[0][0])} y1={sy(s[0][1])} x2={sx(s[1][0])} y2={sy(s[1][1])} className="bline" /> : null;
            })}
            {yours && <line x1={sx(yours[0][0])} y1={sy(yours[0][1])} x2={sx(yours[1][0])} y2={sy(yours[1][1])} className="bline fresh" />}
            {picks.map(([x, y], i) => <circle key={i} cx={sx(x)} cy={sy(y)} r={7} className="pt" />)}
            {tree[sel] &&
              (phase === "branch" || phase === "done") &&
              (() => {
                const n = tree[sel];
                const r = regionOf(n);
                const p = pointOf(n);
                return (
                  <g>
                    {n.bounds.map((k, i) => {
                      const sg = segment(k.a, k.b, k.c);
                      return sg ? <line key={i} x1={sx(sg[0][0])} y1={sy(sg[0][1])} x2={sx(sg[1][0])} y2={sy(sg[1][1])} className="bline branch" /> : null;
                    })}
                    {r.length >= 3 && <polygon points={pts(r)} className="branch-region" />}
                    {p && <circle cx={sx(p[0])} cy={sy(p[1])} r={6} className="simplex-pt" />}
                  </g>
                );
              })()}
          </g>
          {drawn.map((k, i) => {
            const s = segment(k.a, k.b, k.c);
            if (!s) return null;
            const at: Pt = [s[0][0] + (s[1][0] - s[0][0]) * 0.8, s[0][1] + (s[1][1] - s[0][1]) * 0.8];
            return <text key={i} x={Math.min(W - M - 4, sx(at[0]) + 6)} y={Math.max(M + 12, sy(at[1]) - 6)} className="bl-label">{k.label}</text>;
          })}
        </svg>
      </div>
      <div className="plane-side">
        <ol className="edu-steps">
          {level.constraints.map((k, i) => (
            <li key={i} className={i < done ? "done" : i === done && phase !== "question" && phase !== "done" ? "now" : ""}>
              <b>{k.label}</b>
              {i === done && (phase === "line" || phase === "side") && (
                <p>
                  {phase === "line" ? `Click two grid points on its line (${picks.length}/2).` : "Now click a point on the side it allows."}
                  {k.hint && <span className="hint"> {k.hint}</span>}
                </p>
              )}
            </li>
          ))}
        </ol>
        {(phase === "line" || phase === "side") && <button className="ghost small" onClick={showMe}>Show me this one</button>}
        {phase === "question" && (
          <div className="edu-question column">
            <span>Every constraint is drawn. Is any <b>integer</b> point (a grid dot) still green?</span>
            <div className="row">
              <button className="true" onClick={() => answer(true)}>Yes: LIA says sat</button>
              <button className="false" onClick={() => answer(false)}>No: LIA says unsat</button>
            </div>
          </div>
        )}
        {(phase === "branch" || (phase === "done" && tree.length > 0)) && (
          <div className="bb">
            <h4>Branch and bound</h4>
            <ul className="bb-tree">
              {tree.map((n, i) => {
                const p = pointOf(n);
                return (
                  <li key={i} style={{ paddingLeft: depth(i) * 18 }}>
                    <button className={`bb-node ${n.status} ${i === sel ? "on" : ""}`} onClick={() => setSel(i)}>
                      {nodeLabel(i)}
                      <span className="note">
                        {" "}
                        {n.status === "empty" ? "— empty" : n.status === "split" ? "— split" : p ? `— Simplex: (${fmt(p[0])}, ${fmt(p[1])})` : ""}
                      </span>
                    </button>
                  </li>
                );
              })}
            </ul>
            {phase === "branch" && (
              <div className="row">
                <button onClick={() => split(0)}>Split on x</button>
                <button onClick={() => split(1)}>Split on y</button>
              </div>
            )}
          </div>
        )}
        {msg && <div className={`edu-verdict ${msg.ok ? "ok" : "no"}`}>{msg.text}</div>}
        {(phase !== "line" || done > 0) && (
          <button className="ghost small" onClick={() => { setDone(0); setPicks([]); setPhase("line"); setMsg(null); setTree([]); setSel(0); }}>Start again</button>
        )}
      </div>
    </div>
  );
}

const term = (k: number, v: string, first: boolean) => {
  if (k === 0) return "";
  const sign = k < 0 ? (first ? "−" : " − ") : first ? "" : " + ";
  const mag = Math.abs(k) === 1 ? "" : `${Math.abs(k)}·`;
  return `${sign}${mag}${v}`;
};
const lhsText = (k: PlotConstraint) => term(k.a, "x", true) + term(k.b, "y", k.a === 0);
const eq = (k: PlotConstraint) => `${lhsText(k)} = ${k.c}`;
const ineq = (k: PlotConstraint) => `${lhsText(k)} ≤ ${k.c}`;
