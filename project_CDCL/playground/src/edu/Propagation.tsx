import { useMemo, useState } from "react";
import type { PLit, PropagationLevel } from "./levels";

type Assign = Map<string, boolean>;

const name = (l: PLit) => l.replace(/^¬/, "");
const neg = (l: PLit) => l.startsWith("¬");
/** 1 true, -1 false, 0 open */
const val = (a: Assign, l: PLit): 0 | 1 | -1 => {
  const v = a.get(name(l));
  if (v === undefined) return 0;
  return v !== neg(l) ? 1 : -1;
};
const setTrue = (a: Assign, l: PLit) => a.set(name(l), !neg(l));

/** the open literal of a unit clause, or null */
function unitLit(c: PLit[], a: Assign): PLit | null {
  if (c.some((l) => val(a, l) > 0)) return null;
  const open = c.filter((l) => val(a, l) === 0);
  return open.length === 1 ? open[0] : null;
}
const isFalse = (c: PLit[], a: Assign) => c.every((l) => val(a, l) < 0);

/** Unit propagation from the decisions: the steps, and the clause that became false (if any). */
function solve(level: PropagationLevel) {
  const a: Assign = new Map();
  level.decisions.forEach((d) => setTrue(a, d));
  const steps: { lit: PLit; clause: number }[] = [];
  for (;;) {
    const conflict = level.clauses.findIndex((c) => isFalse(c, a));
    if (conflict >= 0) return { steps, conflict };
    const i = level.clauses.findIndex((c) => unitLit(c, a) !== null);
    if (i < 0) return { steps, conflict: -1 };
    const l = unitLit(level.clauses[i], a)!;
    setTrue(a, l);
    steps.push({ lit: l, clause: i });
  }
}

interface Verdict {
  ok: boolean;
  /** literals you set, with the clause that forces them (or -1: not forced) */
  reasons: Map<string, number>;
  missing: { lit: PLit; clause: number }[];
  falseClauses: number[];
  message: string;
}

export function Propagation({ level, onSolved }: { level: PropagationLevel; onSolved: () => void }) {
  const decided = useMemo(() => new Set(level.decisions.map(name)), [level]);
  const [mine, setMine] = useState<Assign>(new Map());
  const [conflictAnswer, setConflictAnswer] = useState<number>(-1);
  const [verdict, setVerdict] = useState<Verdict | null>(null);
  const [solution, setSolution] = useState(false);
  const sol = useMemo(() => solve(level), [level]);

  const start: Assign = new Map();
  level.decisions.forEach((d) => setTrue(start, d));
  const all: Assign = new Map([...start, ...mine]);

  // click a literal: open → true → false → open
  const cycle = (l: PLit) => {
    if (decided.has(name(l))) return;
    setMine((old) => {
      const m = new Map(old);
      const v = val(m, l);
      if (v === 0) setTrue(m, l);
      else if (v > 0) m.set(name(l), neg(l));
      else m.delete(name(l));
      return m;
    });
    setVerdict(null);
  };

  const check = () => {
    // replay your literals in an order unit propagation could take
    const a: Assign = new Map(start);
    const reasons = new Map<string, number>();
    const todo = [...mine].map(([n, v]) => (v ? n : `¬${n}`));
    let progress = true;
    while (progress) {
      progress = false;
      for (const l of todo) {
        if (val(a, l) !== 0) continue;
        if (level.clauses.some((c) => isFalse(c, a))) break; // propagation stops at a conflict
        const i = level.clauses.findIndex((c) => unitLit(c, a) === l);
        if (i >= 0) {
          setTrue(a, l);
          reasons.set(name(l), i);
          progress = true;
        }
      }
    }
    for (const l of todo) if (!reasons.has(name(l))) reasons.set(name(l), -1);
    const wrong = todo.filter((l) => reasons.get(name(l)) === -1);
    const falseClauses = level.clauses.map((c, i) => (isFalse(c, a) ? i : -1)).filter((i) => i >= 0);
    const missing = falseClauses.length
      ? []
      : level.clauses.map((c, i) => ({ lit: unitLit(c, a), clause: i })).filter((u): u is { lit: PLit; clause: number } => u.lit !== null);
    let message: string;
    let ok = false;
    if (wrong.length) message = `${wrong.join(", ")} ${wrong.length === 1 ? "is" : "are"} not forced by any unit clause.`;
    else if (missing.length) message = `Not finished: C${missing[0].clause + 1} is still unit, so ${missing[0].lit} must be true too.`;
    else if (falseClauses.length && !falseClauses.includes(conflictAnswer))
      message = conflictAnswer < 0 ? `Look again: C${falseClauses[0] + 1} has every literal false. That is a conflict.` : `C${conflictAnswer + 1} is not false; C${falseClauses[0] + 1} is.`;
    else if (!falseClauses.length && conflictAnswer >= 0) message = `C${conflictAnswer + 1} still has a literal that is not false, so there is no conflict.`;
    else {
      ok = true;
      message = falseClauses.length
        ? `Right! Propagation ends in a conflict on C${falseClauses[0] + 1}: CDCL would now analyse it and backjump.`
        : todo.length
          ? "Right! Nothing more is forced: the solver would now make its next decision."
          : "Right! No clause is unit, so nothing is propagated.";
    }
    setVerdict({ ok, reasons, missing, falseClauses, message });
    if (ok) onSolved();
  };

  const clauseView = (interactive: boolean) => (
    <div className="edu-formula">
      {level.clauses.map((c, i) => {
        const a = interactive ? all : start;
        const status = isFalse(c, a) ? "unsat" : c.some((l) => val(a, l) > 0) ? "sat" : "";
        return (
          <span key={i} className="edu-clause-wrap">
            {i > 0 && <span className="and">∧</span>}
            <span className={`clause ${status}`}>
              <span className="clause-name">C{i + 1}</span>
              <span className="paren">(</span>
              {c.map((l, j) => {
                const v = val(a, l);
                const isDecision = decided.has(name(l));
                const r = interactive && verdict ? verdict.reasons.get(name(l)) : undefined;
                const mark = r === undefined || isDecision ? "" : r >= 0 ? "right" : "wrong";
                return (
                  <span key={j}>
                    {j > 0 && <span className="conn">∨</span>}
                    <span
                      className={`chip ${v > 0 ? "t" : v < 0 ? "f" : "u"} ${isDecision ? "decided static" : ""} ${interactive && !isDecision ? "" : "static"} ${mark}`}
                      onClick={interactive ? () => cycle(l) : undefined}
                      title={isDecision ? "a decision" : interactive ? "click: true → false → open" : undefined}
                    >
                      {l}
                    </span>
                  </span>
                );
              })}
              <span className="paren">)</span>
            </span>
          </span>
        );
      })}
    </div>
  );

  return (
    <div className="edu-body">
      <h4>The formula, with the decisions ({level.decisions.map((d) => `${name(d)} = ${neg(d) ? "false" : "true"}`).join(", ")})</h4>
      {clauseView(false)}
      <h4>Your answer: click the literals that propagation makes true or false</h4>
      {clauseView(true)}
      <div className="edu-question">
        <span>Does a clause become false (a conflict)?</span>
        <label>
          <input type="radio" checked={conflictAnswer < 0} onChange={() => { setConflictAnswer(-1); setVerdict(null); }} /> no
        </label>
        {level.clauses.map((_, i) => (
          <label key={i}>
            <input type="radio" checked={conflictAnswer === i} onChange={() => { setConflictAnswer(i); setVerdict(null); }} /> C{i + 1}
          </label>
        ))}
      </div>
      <div className="row">
        <button className="primary" onClick={check}>Check</button>
        <button className="ghost" onClick={() => { setMine(new Map()); setConflictAnswer(-1); setVerdict(null); }}>Start again</button>
        <button className="ghost" onClick={() => setSolution((s) => !s)}>{solution ? "Hide" : "Show"} the solution</button>
      </div>
      {verdict && <div className={`edu-verdict ${verdict.ok ? "ok" : "no"}`}>{verdict.message}</div>}
      {solution && (
        <ol className="edu-solution">
          {sol.steps.length === 0 && sol.conflict < 0 && <li>No clause is unit: nothing is propagated.</li>}
          {sol.steps.map((s, i) => (
            <li key={i}>
              C{s.clause + 1} is unit, so <b>{s.lit}</b> becomes true.
            </li>
          ))}
          {sol.conflict >= 0 && <li>Every literal of C{sol.conflict + 1} is false: <b>conflict</b>.</li>}
        </ol>
      )}
    </div>
  );
}
