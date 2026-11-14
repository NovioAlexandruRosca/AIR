import { useEffect, useMemo, useRef, useState } from "react";
import type { FormulaNode, Lit, PlaygroundResponse } from "../api";
import { atomText, evalNode, litText, truth, visibleVar, type Labels, type State, type StepKind } from "../model";
import { previewText, type Preview } from "../preview";

export interface ExtraClause {
  id: number;
  lits: Lit[];
  tag: string;
}

interface Props {
  resp: PlaygroundResponse;
  L: Labels;
  state: State;
  extras: ExtraClause[];
  highlight: { assertion: number; extra: number };
  focusLits: Lit[];
  stepKind?: StepKind;
  canDecide: boolean;
  atEnd: boolean;
  decisions: Lit[];
  onDecide: (l: Lit) => void;
  onUndo: (index: number) => void;
  /** the effect of the decision being hovered */
  preview: Preview | null;
  onPreview: (l: Lit | null, pick?: boolean) => void;
  onPrefetch: (v: number) => void;
  /** this literal already led to a conflict under the current decisions */
  refuted: (l: Lit) => boolean;
  /** several unit clauses at once: the formula's clauses to choose from */
  units: { clause: number; lit: Lit; assertion: number }[];
  onPick: (l: Lit) => void;
}

interface Pop {
  v: number;
  x: number;
  y: number;
}

const badgeFor: Partial<Record<StepKind, string>> = {
  unit: "unit clause",
  propagate: "unit clause",
  conflict: "every literal false",
  lemma: "new theory lemma",
};

export function FormulaView(p: Props) {
  const [pop, setPop] = useState<Pop | null>(null);
  const root = useRef<HTMLDivElement>(null);
  const focus = new Set(p.focusLits.map(Math.abs));

  useEffect(() => {
    const close = (e: MouseEvent) => {
      if (!(e.target as HTMLElement).closest(".pop, .chip")) setPop(null);
    };
    window.addEventListener("mousedown", close);
    return () => window.removeEventListener("mousedown", close);
  }, []);
  useEffect(() => setPop(null), [p.state.end]);
  useEffect(() => {
    if (!pop) p.onPreview(null);
    else if (p.canDecide && p.atEnd && p.state.value.get(pop.v) === undefined) p.onPrefetch(pop.v);
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [pop]);
  // An LIA equality a = b is decided through two helper atoms a ≤ b and a ≥ b
  // (axiom: a ≤ b ∧ a ≥ b → a = b). Found here so the chip can show them.
  const halves = useMemo(() => {
    const m = new Map<number, [number, number]>();
    for (const c of p.resp.replay.db) {
      if (c.length !== 3) continue;
      const pos = c.filter((l) => l > 0);
      const neg = c.filter((l) => l < 0).map((l) => -l);
      if (pos.length === 1 && neg.length === 2 && neg.every((v) => p.L.vars[v]?.kind === "theory") && p.L.vars[pos[0]]?.label.includes("="))
        m.set(pos[0], [neg[0], neg[1]]);
    }
    return m;
  }, [p.resp, p.L]);
  const pv = new Map<number, Lit>();
  if (p.preview) for (const l of [p.preview.lit, ...p.preview.changes]) pv.set(Math.abs(l), l);

  const assertions: FormulaNode[] =
    p.resp.formula ??
    p.resp.clauses
      .slice(0, p.resp.clauses.length - p.extras.filter((e) => e.id < p.resp.num_original).length)
      .map((c) => ({
        op: "or" as const,
        args: c.map((l): FormulaNode => (l > 0 ? { atom: l, label: `x${l}` } : { op: "not", args: [{ atom: -l, label: `x${-l}` }] })),
      }));

  const unitLits = new Set(p.units.map((u) => u.lit));
  const unitsOf = (assertion: number, extra: number) => p.units.filter((u) => u.clause === extra || (assertion >= 0 && u.assertion === assertion));
  const open = (e: React.MouseEvent, v: number) => {
    const box = root.current!.getBoundingClientRect();
    const r = (e.currentTarget as HTMLElement).getBoundingClientRect();
    setPop({ v, x: r.left - box.left, y: r.bottom - box.top + 6 });
  };

  const chip = (lit: Lit, text: string, key: string) => {
    const t = truth(p.state, lit);
    const f = focus.has(Math.abs(lit));
    // while previewing: the value this literal would get
    const w = pv.get(Math.abs(lit));
    const wt = t === 0 && w !== undefined ? ((lit > 0) === (w > 0) ? "pv pv-t" : "pv pv-f") : "";
    const dec = w !== undefined && Math.abs(w) === Math.abs(p.preview!.lit) ? "pv-dec" : "";
    const isUnit = unitLits.has(lit);
    // a literal a waiting unit clause forces: click it to propagate it first
    const c = isUnit ? (
      <span
        key={key}
        className={`chip u unit-lit ${wt} ${wt && dec}`}
        onClick={(e) => {
          e.stopPropagation();
          p.onPreview(null);
          p.onPick(lit);
        }}
        onMouseEnter={() => p.onPreview(lit, true)}
        onMouseLeave={() => p.onPreview(null)}
        title={`Unit clause: click to make ${litText(p.L, lit)} true`}
      >
        {text}
      </span>
    ) : (
      <span key={key} className={`chip ${t > 0 ? "t" : t < 0 ? "f" : "u"} ${f ? "focus" : ""} ${wt} ${wt && dec}`} onClick={(e) => open(e, Math.abs(lit))}>
        {text}
      </span>
    );
    // an equality the theory has split: show its two halves under it
    const h = halves.get(Math.abs(lit));
    if (!h || h.every((v) => truth(p.state, v) === 0)) return c;
    return (
      <span key={key} className="eqsplit" title={`${atomText(p.L, Math.abs(lit))} holds exactly when both halves hold; LIA decides it through them`}>
        {c}
        <span className="halves">
          <span className="split-mark">split into</span>
          {h.map((v) => {
            const hv = truth(p.state, v);
            return (
              <span key={v} className={`half-chip ${hv > 0 ? "t" : hv < 0 ? "f" : "u"}`}>
                {atomText(p.L, v)}
              </span>
            );
          })}
        </span>
      </span>
    );
  };

  // A tree as text; ¬atom becomes one chip (as on the slides).
  const node = (n: FormulaNode, key: string, top = false): React.ReactNode => {
    if ("const" in n) return <span key={key} className="conn">{String(n.const)}</span>;
    if ("atom" in n) return chip(n.atom, n.label, key);
    if (n.op === "not" && "atom" in n.args[0]) {
      const a = n.args[0] as { atom: number; label: string };
      return chip(-a.atom, /\s/.test(a.label) ? `¬(${a.label})` : `¬${a.label}`, key);
    }
    const sep = { and: "∧", or: "∨", "=>": "⇒", iff: "⇔", xor: "⊕", ite: ",", not: "" }[n.op];
    const parts: React.ReactNode[] = [];
    if (n.op === "not") parts.push(<span key="n" className="conn">¬</span>);
    if (n.op === "ite") parts.push(<span key="i" className="conn">ite</span>);
    const paren = !top || n.op === "not" || n.op === "ite";
    if (paren) parts.push(<span key="(" className="paren">(</span>);
    n.args.forEach((a, i) => {
      if (i > 0) parts.push(<span key={`s${i}`} className="conn">{sep}</span>);
      parts.push(node(a, `${key}.${i}`));
    });
    if (paren) parts.push(<span key=")" className="paren">)</span>);
    return <span key={key} className="group">{parts}</span>;
  };

  const clauseBox = (content: React.ReactNode, key: string, highlighted: boolean, sat: 0 | 1 | -1, tag?: string, units: { lit: Lit }[] = []) => {
    // one unit clause in the box: click anywhere on it; several (an `and` of
    // facts): click the flashing literal
    const unit = units.length === 1 ? units[0] : undefined;
    return (
    <span
      key={key}
      className={`clause ${highlighted ? "hl" : ""} ${sat > 0 ? "sat" : sat < 0 ? "unsat" : ""} ${tag ? "extra" : ""} ${units.length ? "unit-choice" : ""}`}
      onClickCapture={
        unit
          ? (e) => {
              e.stopPropagation();
              p.onPreview(null);
              p.onPick(unit.lit);
            }
          : undefined
      }
      onMouseEnter={unit ? () => p.onPreview(unit.lit, true) : undefined}
      onMouseLeave={unit ? () => p.onPreview(null) : undefined}
      title={unit ? `Unit clause: click to make ${litText(p.L, unit.lit)} true` : undefined}
    >
      {unit && <span className="clause-badge unit-badge">click: {litText(p.L, unit.lit)} → true</span>}
      {units.length > 1 && <span className="clause-badge unit-badge">{units.length} unit clauses: click a flashing literal</span>}
      {!units.length && highlighted && p.stepKind && badgeFor[p.stepKind] && <span className="clause-badge">{badgeFor[p.stepKind]}</span>}
      {tag && <span className="clause-tag">{tag}</span>}
      {content}
    </span>
    );
  };

  const items: React.ReactNode[] = [];
  assertions.forEach((a, i) => {
    if (i > 0) items.push(<span key={`and${i}`} className="and">∧</span>);
    const isClause = "op" in a && a.op === "or";
    const inner = isClause ? node(a, `a${i}`, false) : node(a, `a${i}`, true);
    items.push(clauseBox(inner, `c${i}`, p.highlight.assertion === i, evalNode(a, p.state), undefined, unitsOf(i, -1)));
  });
  p.extras.forEach((x) => {
    items.push(<span key={`and-x${x.id}`} className="and">∧</span>);
    const sat = x.lits.some((l) => truth(p.state, l) > 0) ? 1 : x.lits.every((l) => truth(p.state, l) < 0) ? -1 : 0;
    const inner = (
      <span className="group">
        <span className="paren">(</span>
        {x.lits.map((l, j) => [j > 0 && <span key={`s${j}`} className="conn">∨</span>, chip(l, litText(p.L, l), `x${x.id}.${j}`)])}
        <span className="paren">)</span>
      </span>
    );
    items.push(clauseBox(inner, `x${x.id}`, p.highlight.extra === x.id, sat as 0 | 1 | -1, x.tag, unitsOf(-1, x.id)));
  });

  // Open atoms the formula does not show but that still need a value: the
  // Nelson–Oppen arrangement of shared constants. (The theories' own helper
  // atoms are decided by the solver; a split equality shows its halves.)
  const shown = new Set<number>();
  const collect = (n: FormulaNode) => {
    if ("atom" in n) shown.add(n.atom);
    else if ("args" in n) n.args.forEach(collect);
  };
  assertions.forEach(collect);
  p.extras.forEach((x) => x.lits.forEach((l) => shown.add(Math.abs(l))));
  const pending =
    p.atEnd && p.resp.replay.outcome === "open"
      ? (p.resp.replay.open ?? []).filter((v) => !shown.has(v) && truth(p.state, v) === 0 && visibleVar(p.L, v) && p.L.vars[v]?.kind !== "theory")
      : [];

  const popVar = pop ? pop.v : 0;
  const assigned = pop ? p.state.trail.find((t) => Math.abs(t.lit) === popVar) : undefined;
  const decisionIdx = pop ? p.decisions.findIndex((d) => Math.abs(d) === popVar) : -1;

  return (
    <div className="formula" ref={root}>
      <div className="formula-line">{items}</div>
      {pending.length > 0 && (
        <div className="pending">
          <span className="pending-label">Still to decide:</span>
          {pending.slice(0, 12).map((v) => chip(v, atomText(p.L, v), `p${v}`))}
          {pending.some((v) => p.L.vars[v]?.kind === "interface") && <p className="pending-why">Are the shared constants equal? Nelson–Oppen needs both theories to agree on it.</p>}
        </div>
      )}
      {pop && (
        <div className="pop" style={{ left: pop.x, top: pop.y }}>
          {!p.atEnd ? (
            <p>There are still steps to see. Press <b>Next</b> (or <b>Show all</b>) before deciding.</p>
          ) : assigned ? (
            <>
              <p>
                <b>{litText(p.L, assigned.lit)}</b> is already {assigned.lit > 0 ? "true" : "false"}
                {assigned.reason === null ? (assigned.level === 0 ? "." : " — a decision.") : " — it was propagated."}
              </p>
              {decisionIdx >= 0 && assigned.reason === null && (
                <button onClick={() => p.onUndo(decisionIdx)}>Undo this decision</button>
              )}
            </>
          ) : !p.canDecide ? (
            <p>The context is inconsistent: backtrack first.</p>
          ) : (
            <>
              <p className="pop-title">Decide</p>
              {[popVar, -popVar].map((l) =>
                p.refuted(l) ? null : (
                  <button
                    key={l}
                    className={l > 0 ? "true" : "false"}
                    onClick={() => p.onDecide(l)}
                    onMouseEnter={() => p.onPreview(l)}
                    onMouseLeave={() => p.onPreview(null)}
                    onFocus={() => p.onPreview(l)}
                    onBlur={() => p.onPreview(null)}
                  >
                    {atomText(p.L, popVar)} → {l > 0 ? "true" : "false"}
                  </button>
                ),
              )}
              {p.refuted(popVar) && p.refuted(-popVar) ? (
                <p className="pop-note">Both values were already tried with these decisions and both led to a conflict.</p>
              ) : (
                [popVar, -popVar].filter(p.refuted).map((l) => (
                  <p key={l} className="pop-note">
                    {atomText(p.L, popVar)} → {l > 0 ? "true" : "false"} was already tried with these decisions and led to a conflict, so only the other value is left.
                  </p>
                ))
              )}
              <p className="pop-preview">
                {p.preview && Math.abs(p.preview.lit) === popVar ? previewText(p.preview) : "Point at a choice to see what it changes."}
              </p>
            </>
          )}
        </div>
      )}
    </div>
  );
}
