import { area, clip, meet, num, type Pt } from "./linear";
import type { Frame, LiaModel } from "./liaModel";

const W = 560;
const H = 440;
const M = 34;

/**
 * One frame of an LIA check in the plane. The whole plane starts green;
 * every constraint lays a transparent red over the side it rules out, so a
 * point several constraints rule out is darker red. Green stays only where
 * every constraint allows the point.
 */
export function Plane2D({ model, frame }: { model: LiaModel; frame: Frame }) {
  const { items, axes, conflictIds } = model;
  const last = frame.final !== undefined;
  const [[x0, x1], [y0, y1]] = model.box;
  const sx = (x: number) => M + ((x - x0) / (x1 - x0)) * (W - 2 * M);
  const sy = (y: number) => H - M - ((y - y0) / (y1 - y0)) * (H - 2 * M);
  const pts = (p: Pt[]) => p.map(([x, y]) => `${sx(x)},${sy(y)}`).join(" ");
  const big: Pt[] = [
    [x0 - 1, y0 - 1],
    [x1 + 1, y0 - 1],
    [x1 + 1, y1 + 1],
    [x0 - 1, y1 + 1],
  ];
  const coeffs = (i: number): [number, number, number] => [items[i].a.get(axes[0]) ?? 0, axes[1] ? items[i].a.get(axes[1]) ?? 0 : 0, items[i].c];
  // the side a constraint rules out: a·x + b·y > c
  const ruledOut = (i: number): Pt[] => {
    const [a, b, c] = coeffs(i);
    if (a === 0 && b === 0) return c >= 0 ? [] : big;
    return clip(big, -a, -b, -c);
  };
  let region: Pt[] = big;
  for (const i of frame.drawn) {
    const [a, b, c] = coeffs(i);
    if (a === 0 && b === 0) region = c >= 0 ? region : [];
    else if (region.length) region = clip(region, a, b, c);
  }
  // a segment or a single point (area 0) is still a solution set
  const empty = frame.drawn.length > 0 && region.length === 0;
  const thin = !empty && area(region) < 1e-9;

  const segment = (i: number): [Pt, Pt] | null => {
    const [a, b, c] = coeffs(i);
    if (a === 0 && b === 0) return null;
    const ends: Pt[] = [];
    for (const e of [
      [1, 0, x0],
      [1, 0, x1],
      [0, 1, y0],
      [0, 1, y1],
    ] as [number, number, number][]) {
      const p = meet([a, b, c], e);
      if (p && p[0] >= x0 - 1e-9 && p[0] <= x1 + 1e-9 && p[1] >= y0 - 1e-9 && p[1] <= y1 + 1e-9) ends.push(p);
    }
    if (ends.length < 2) return null;
    ends.sort((p, q) => p[0] - q[0] || p[1] - q[1]);
    return [ends[0], ends[ends.length - 1]];
  };

  const span = Math.max(x1 - x0, y1 - y0);
  const ints = (lo: number, hi: number) => {
    const out: number[] = [];
    const stepI = span > 30 ? 5 : span > 16 ? 2 : 1;
    for (let v = Math.ceil(lo / stepI) * stepI; v <= hi; v += stepI) out.push(v);
    return out;
  };
  const lattice: Pt[] = [];
  if (span <= 24) for (let x = Math.ceil(x0); x <= x1; x++) for (let y = Math.ceil(y0); y <= y1; y++) lattice.push([x, y]);
  const inRegion = ([x, y]: Pt) =>
    frame.drawn.every((i) => {
      const [a, b, c] = coeffs(i);
      return a * x + b * y <= c + 1e-9;
    });
  const oneVar = axes[1] === "";
  const point = frame.point as Pt | undefined;
  const path = frame.path as Pt[] | undefined;

  return (
    <svg viewBox={`0 0 ${W} ${H}`} role="img" aria-label="constraints in the plane">
      <defs>
        <clipPath id="plot">
          <rect x={M} y={M} width={W - 2 * M} height={H - 2 * M} />
        </clipPath>
      </defs>
      <g clipPath="url(#plot)">
        {/* green: what every constraint so far allows (everything, before the first) */}
        {region.length >= 2 && <polygon points={pts(region)} className={`region ${last ? "final" : ""} ${thin ? "thin" : ""}`} />}
        {frame.drawn.map((i) => {
          const p = ruledOut(i);
          return p.length >= 3 ? <polygon key={`r${i}`} points={pts(p)} className={`out ${i === frame.fresh ? "fresh" : ""}`} /> : null;
        })}
      </g>
      {/* grid and axes */}
      {ints(x0, x1).map((x) => (
        <g key={`gx${x}`}>
          <line x1={sx(x)} x2={sx(x)} y1={M} y2={H - M} className={x === 0 ? "axis" : "grid"} />
          <text x={sx(x)} y={H - M + 16} className="tick">{x}</text>
        </g>
      ))}
      {!oneVar &&
        ints(y0, y1).map((y) => (
          <g key={`gy${y}`}>
            <line y1={sy(y)} y2={sy(y)} x1={M} x2={W - M} className={y === 0 ? "axis" : "grid"} />
            <text x={M - 8} y={sy(y) + 4} className="tick end">{y}</text>
          </g>
        ))}
      <text x={W - M} y={H - 6} className="axis-name end">{axes[0]} →</text>
      {!oneVar && <text x={M - 4} y={M - 12} className="axis-name">↑ {axes[1]}</text>}

      <g clipPath="url(#plot)">
        {lattice.map((p) => (
          <circle key={p.join()} cx={sx(p[0])} cy={sy(p[1])} r={last && frame.final === "sat" && inRegion(p) ? 3.2 : 1.6} className={last && frame.final === "sat" && inRegion(p) ? "lat in" : "lat"} />
        ))}
        {frame.drawn.map((i) => {
          const seg = segment(i);
          if (!seg) return null;
          const cls = ["bline", items[i].derived ? "derived" : "", i === frame.fresh ? "fresh" : "", last && frame.final === "unsat" && conflictIds.has(i) ? "blame" : ""].join(" ");
          return <line key={`l${i}`} x1={sx(seg[0][0])} y1={sy(seg[0][1])} x2={sx(seg[1][0])} y2={sy(seg[1][1])} className={cls} />;
        })}
        {path && path.length > 1 && <polyline points={pts(path)} className="path" />}
        {path && path.slice(0, -1).map((p, i) => <circle key={`p${i}`} cx={sx(p[0])} cy={sy(p[1])} r={3.5} className="path-dot" />)}
        {point && (
          <g>
            <circle cx={sx(point[0])} cy={sy(point[1])} r={7} className="pt" />
            <text x={sx(point[0]) + 10} y={sy(point[1]) - 10} className="pt-label">
              ({num(point[0])}
              {oneVar ? "" : `, ${num(point[1])}`})
            </text>
          </g>
        )}
      </g>
      {/* line labels, near the end of each line */}
      {frame.drawn.map((i) => {
        const seg = segment(i);
        if (!seg) return null;
        const [p, q] = seg;
        const at: Pt = [p[0] + (q[0] - p[0]) * 0.82, p[1] + (q[1] - p[1]) * 0.82];
        return (
          <text key={`t${i}`} x={Math.min(W - M - 4, sx(at[0]) + 6)} y={Math.max(M + 12, sy(at[1]) - 6)} className={`bl-label ${i === frame.fresh ? "fresh" : ""} ${items[i].derived ? "derived" : ""}`}>
            {items[i].text}
          </text>
        );
      })}
      {empty && (
        <g>
          <rect x={W / 2 - 92} y={H - M - 44} width={184} height={32} rx={8} className="empty-box" />
          <text x={W / 2} y={H - M - 22} className="empty-mark">no point is left</text>
        </g>
      )}
    </svg>
  );
}
