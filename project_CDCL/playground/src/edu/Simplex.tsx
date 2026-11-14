import { useMemo, useState } from "react";
import type { SimplexLevel } from "./levels";

// ---------------------------------------------------------------- rationals
type Q = [number, number]; // numerator, denominator > 0
const gcd = (a: number, b: number): number => (b === 0 ? Math.abs(a) : gcd(b, a % b));
const q = (n: number, d = 1): Q => {
  const g = gcd(n, d) || 1;
  return d < 0 ? [-n / g, -d / g] : [n / g, d / g];
};
const add = (a: Q, b: Q) => q(a[0] * b[1] + b[0] * a[1], a[1] * b[1]);
const sub = (a: Q, b: Q) => q(a[0] * b[1] - b[0] * a[1], a[1] * b[1]);
const mul = (a: Q, b: Q) => q(a[0] * b[0], a[1] * b[1]);
const div = (a: Q, b: Q) => q(a[0] * b[1], a[1] * b[0]);
const cmp = (a: Q, b: Q) => a[0] * b[1] - b[0] * a[1];
const isZero = (a: Q) => a[0] === 0;
const qs = (a: Q) => (a[1] === 1 ? `${a[0]}` : `${a[0]}/${a[1]}`).replace("-", "−");

// ---------------------------------------------------------------- the tableau
interface Tab {
  /** basic variable → its row over the nonbasic variables */
  rows: Map<string, Map<string, Q>>;
  nonbasic: string[];
  value: Map<string, Q>;
}
interface Bounds {
  lo: Map<string, Q>;
  hi: Map<string, Q>;
}

function start(level: SimplexLevel): { tab: Tab; bounds: Bounds } {
  const lo = new Map<string, Q>();
  const hi = new Map<string, Q>();
  for (const b of level.bounds) {
    if (b.lo !== undefined) lo.set(b.v, q(b.lo));
    if (b.hi !== undefined) hi.set(b.v, q(b.hi));
  }
  // nonbasic variables start at 0, or at the nearest bound
  const value = new Map<string, Q>();
  for (const v of level.vars) value.set(v, lo.has(v) && lo.get(v)![0] > 0 ? lo.get(v)! : hi.has(v) && hi.get(v)![0] < 0 ? hi.get(v)! : q(0));
  const rows = new Map<string, Map<string, Q>>();
  for (const r of level.rows) {
    const row = new Map<string, Q>();
    let val = q(0);
    for (const [v, c] of Object.entries(r.sum)) {
      row.set(v, q(c));
      val = add(val, mul(q(c), value.get(v)!));
    }
    rows.set(r.name, row);
    value.set(r.name, val);
  }
  return { tab: { rows, nonbasic: [...level.vars], value }, bounds: { lo, hi } };
}

const below = (B: Bounds, v: string, x: Q) => B.lo.has(v) && cmp(x, B.lo.get(v)!) < 0;
const above = (B: Bounds, v: string, x: Q) => B.hi.has(v) && cmp(x, B.hi.get(v)!) > 0;
const violated = (t: Tab, B: Bounds) => [...t.rows.keys()].filter((b) => below(B, b, t.value.get(b)!) || above(B, b, t.value.get(b)!));

/** can nonbasic n move basic b towards its violated bound? */
function canFix(t: Tab, B: Bounds, b: string, n: string): boolean {
  const c = t.rows.get(b)!.get(n);
  if (!c || isZero(c)) return false;
  const up = below(B, b, t.value.get(b)!); // b must go up
  const nUp = up === c[0] > 0; // then n must go up
  const x = t.value.get(n)!;
  return nUp ? !B.hi.has(n) || cmp(x, B.hi.get(n)!) < 0 : !B.lo.has(n) || cmp(x, B.lo.get(n)!) > 0;
}

/** Pivot basic b with nonbasic n, and set b to the bound it violated. */
function pivot(t: Tab, B: Bounds, b: string, n: string): Tab {
  const target = below(B, b, t.value.get(b)!) ? B.lo.get(b)! : B.hi.get(b)!;
  const row = t.rows.get(b)!;
  const c = row.get(n)!;
  // the change of n that brings b to its bound, and its effect on every row
  const dn = div(sub(target, t.value.get(b)!), c);
  const value = new Map(t.value);
  value.set(n, add(value.get(n)!, dn));
  for (const [bb, r] of t.rows) value.set(bb, add(value.get(bb)!, mul(r.get(n) ?? q(0), dn)));
  // n = (b − Σ_{m≠n} c_m·m) / c
  const nRow = new Map<string, Q>([[b, div(q(1), c)]]);
  for (const [m, cm] of row) if (m !== n) nRow.set(m, div(q(-cm[0], cm[1]), c));
  const rows = new Map<string, Map<string, Q>>();
  for (const [bb, r] of t.rows) {
    if (bb === b) continue;
    const cn = r.get(n);
    if (!cn) {
      rows.set(bb, r);
      continue;
    }
    const nr = new Map<string, Q>();
    for (const [m, cm] of r) if (m !== n) nr.set(m, cm);
    for (const [m, cm] of nRow) {
      const s = add(nr.get(m) ?? q(0), mul(cn, cm));
      if (isZero(s)) nr.delete(m);
      else nr.set(m, s);
    }
    rows.set(bb, nr);
  }
  rows.set(n, nRow);
  return { rows, nonbasic: t.nonbasic.map((m) => (m === n ? b : m)), value };
}

const rowText = (r: Map<string, Q>, order: string[]) => {
  const parts = order.filter((m) => r.has(m)).map((m, i) => {
    const c = r.get(m)!;
    const neg = c[0] < 0;
    const mag = qs(q(Math.abs(c[0]), c[1]));
    return `${i === 0 ? (neg ? "−" : "") : neg ? " − " : " + "}${mag === "1" ? "" : `${mag}·`}${m}`;
  });
  return parts.join("") || "0";
};
const boundText = (B: Bounds, v: string) => {
  const l = B.lo.get(v);
  const h = B.hi.get(v);
  return l && h ? `${qs(l)} ≤ ${v} ≤ ${qs(h)}` : l ? `${v} ≥ ${qs(l)}` : h ? `${v} ≤ ${qs(h)}` : "no bound";
};

/** Run the general Simplex yourself: pick the violated basic variable, then the nonbasic one to pivot with. */
export function Simplex({ level, onSolved }: { level: SimplexLevel; onSolved: () => void }) {
  const init = useMemo(() => start(level), [level]);
  const B = init.bounds;
  const [tab, setTab] = useState<Tab>(init.tab);
  const [basic, setBasic] = useState<string | null>(null);
  const [log, setLog] = useState<string[]>([]);
  const [msg, setMsg] = useState<{ ok: boolean; text: string } | null>(null);
  const [done, setDone] = useState(false);
  const bad = violated(tab, B);
  const all = [...level.vars, ...level.rows.map((r) => r.name)];

  const chooseBasic = (b: string) => {
    if (done) return;
    if (!bad.includes(b)) {
      setMsg({ ok: false, text: `${b} = ${qs(tab.value.get(b)!)} respects its bound (${boundText(B, b)}): nothing to repair there.` });
      return;
    }
    setBasic(b);
    setMsg({ ok: true, text: `${b} = ${qs(tab.value.get(b)!)} breaks ${boundText(B, b)}: it must go ${below(B, b, tab.value.get(b)!) ? "up" : "down"}. Which nonbasic variable of its row can move it there?` });
  };

  const chooseNonbasic = (n: string) => {
    if (done) return;
    if (!basic) {
      setMsg({ ok: false, text: "First pick the basic variable (a row) that breaks its bound." });
      return;
    }
    if (!canFix(tab, B, basic, n)) {
      const c = tab.rows.get(basic)!.get(n);
      setMsg({
        ok: false,
        text: !c
          ? `${n} is not in the row of ${basic}: changing it does not move ${basic}.`
          : `To move ${basic} the right way, ${n} would have to go ${(below(B, basic, tab.value.get(basic)!) === c[0] > 0) ? "up" : "down"}, but it is already at its bound (${boundText(B, n)}).`,
      });
      return;
    }
    const next = pivot(tab, B, basic, n);
    setLog((l) => [...l, `pivot ${basic} with ${n}: ${basic} goes to its bound ${qs(next.value.get(basic)!)}, ${n} becomes ${qs(next.value.get(n)!)} and is now basic`]);
    setTab(next);
    setBasic(null);
    setMsg({ ok: true, text: `Pivoted: ${n} is basic now (${n} = ${rowText(next.rows.get(n)!, all)}), ${basic} is nonbasic at its bound. Check the bounds again.` });
  };

  const sayDone = (answer: "sat" | "unsat") => {
    if (done) return;
    if (answer === "sat") {
      if (bad.length) setMsg({ ok: false, text: `${bad[0]} = ${qs(tab.value.get(bad[0])!)} still breaks ${boundText(B, bad[0])}.` });
      else {
        setMsg({ ok: true, text: `Right: every variable respects its bounds, so the constraints are satisfiable (over the rationals): ${level.vars.map((v) => `${v} = ${qs(tab.value.get(v)!)}`).join(", ")}.` });
        setDone(true);
        onSolved();
      }
      return;
    }
    const stuck = bad.find((b) => !tab.nonbasic.some((n) => canFix(tab, B, b, n)));
    if (!stuck)
      setMsg({ ok: false, text: bad.length ? `Not stuck: ${bad[0]} can still be repaired by a nonbasic variable of its row.` : "Every bound holds: nothing is in conflict." });
    else {
      const r = tab.rows.get(stuck)!;
      const why = [...r.keys()].map((n) => boundText(B, n)).join(", ");
      setMsg({
        ok: true,
        text: `Right: ${stuck} = ${rowText(r, all)} must go ${below(B, stuck, tab.value.get(stuck)!) ? "up" : "down"}, but every variable of its row is stuck at a bound. The row and those bounds (${why}, and ${boundText(B, stuck)}) are the conflict: that is the explanation LIA turns into a lemma.`,
      });
      setDone(true);
      onSolved();
    }
  };

  return (
    <div className="edu-body">
      <h4>The tableau</h4>
      <table className="edu-tableau">
        <thead>
          <tr>
            <th>basic</th>
            <th>row</th>
            <th>value</th>
            <th>bounds</th>
          </tr>
        </thead>
        <tbody>
          {[...tab.rows].map(([b, r]) => (
            <tr key={b} className={`${basic === b ? "on" : ""} ${done && bad.includes(b) ? "bad" : ""}`} onClick={() => chooseBasic(b)}>
              <td className="mono"><b>{b}</b></td>
              <td className="mono">= {rowText(r, all)}</td>
              <td className="mono">{qs(tab.value.get(b)!)}</td>
              <td className="mono">{boundText(B, b)}</td>
            </tr>
          ))}
        </tbody>
      </table>
      <h4>Nonbasic variables</h4>
      <div className="lemma-lits">
        {tab.nonbasic.map((n) => (
          <button key={n} className="chip u" onClick={() => chooseNonbasic(n)} title={boundText(B, n)}>
            {n} = {qs(tab.value.get(n)!)} <span className="note">({boundText(B, n)})</span>
          </button>
        ))}
      </div>
      <p className="note">
        {basic ? <>Now click the nonbasic variable to pivot with <b>{basic}</b>.</> : <>Click a row whose basic variable breaks its bound, or decide:</>}
      </p>
      <div className="row">
        <button className="true" onClick={() => sayDone("sat")} disabled={done}>Every bound holds: sat</button>
        <button className="false" onClick={() => sayDone("unsat")} disabled={done}>A row is stuck: unsat</button>
        <button className="ghost" onClick={() => { setTab(init.tab); setBasic(null); setLog([]); setMsg(null); setDone(false); }}>Start again</button>
      </div>
      {msg && <div className={`edu-verdict ${msg.ok ? "ok" : "no"}`}>{msg.text}</div>}
      {log.length > 0 && (
        <ol className="edu-solution">
          {log.map((l, i) => <li key={i}>{l}</li>)}
        </ol>
      )}
    </div>
  );
}
