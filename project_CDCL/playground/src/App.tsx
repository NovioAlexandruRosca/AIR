import { useCallback, useEffect, useMemo, useRef, useState } from "react";
import { loadExamples, playground, type Example, type Lit, type Pick, type PlaygroundResponse } from "./api";
import { buildSteps, clauseInfo, keyOf, makeLabels, stateAt, theoryClauses, theoryName } from "./model";
import { FormulaView, type ExtraClause } from "./components/FormulaView";
import { ContextView } from "./components/ContextView";
import { StepCard } from "./components/StepCard";
import { History } from "./components/History";
import { Outcome } from "./components/Outcome";
import { ImplicationGraph } from "./components/ImplicationGraph";
import { TheoryPanel } from "./theory/TheoryPanel";
import { EditDialog } from "./components/EditDialog";
import { FormattedEditDialog } from "./components/FormattedEditDialog";
import { previewOf, type Preview } from "./preview";
import { EduMode, levelName, loadSolved } from "./edu/EduMode";
import { LEVELS, TOPICS } from "./edu/levels";

interface Session {
  src: string;
  decisions: Lit[];
  /** which unit clause you propagated first when several were unit */
  picks: Pick[];
  /** clauses kept across backtracking (theory lemmas and learned clauses) */
  lemmas: Lit[][];
  learnedKeys: Set<string>;
  /** decisions that ended in a conflict, with the decisions made before them */
  refuted: { prefix: Lit[]; lit: Lit }[];
}

const emptySession = (src: string): Session => ({ src, decisions: [], picks: [], lemmas: [], learnedKeys: new Set(), refuted: [] });

/** Was `lit` refuted under (a subset of) these decisions? Then it fails here too. */
const isRefuted = (refuted: Session["refuted"], decisions: Lit[], lit: Lit) =>
  refuted.some((r) => r.lit === lit && r.prefix.every((d) => decisions.includes(d)));

export default function App() {
  const [examples, setExamples] = useState<Example[]>([]);
  const [exampleIdx, setExampleIdx] = useState(0);
  const [session, setSession] = useState<Session>(emptySession(""));
  const [theoryProp, setTheoryProp] = useState(false);
  const [resp, setResp] = useState<PlaygroundResponse | null>(null);
  const [cursor, setCursor] = useState(0);
  const [error, setError] = useState<string | null>(null);
  const [editing, setEditing] = useState(false);
  const [writing, setWriting] = useState(false);
  // educational mode: levels instead of examples (remembered per browser)
  const [solved, setSolved] = useState(loadSolved);
  const [edu, setEdu] = useState(() => {
    try {
      return localStorage.getItem("playground.edu") === "1";
    } catch {
      return false;
    }
  });
  const [levelIdx, setLevelIdx] = useState(0);
  const [busy, setBusy] = useState(false);
  const [preview, setPreview] = useState<Preview | null>(null);
  const previews = useRef(new Map<string, Promise<PlaygroundResponse>>());
  const hovered = useRef<Lit | null>(null);
  const prevEvents = useRef<string[]>([]);
  const theoryRef = useRef<HTMLElement>(null);

  const run = useCallback(
    async (s: Session, finish = false, prop = theoryProp) => {
      setBusy(true);
      try {
        const r = await playground({ src: s.src, decisions: s.decisions, picks: s.picks, lemmas: s.lemmas, theoryPropagation: prop, finish });
        // Theory lemmas found by your own conflicts stay in F when you backtrack.
        const lemmas = s.lemmas.slice();
        if (!finish) {
          r.events.forEach((ev) => {
            if (ev.type !== "TheoryClause" || ev.kind !== "conflict") return;
            if (ev.lits.some((l) => Math.abs(l) > r.num_vars)) return; // atoms made during this run
            const k = keyOf(ev.lits);
            if (!lemmas.some((c) => keyOf(c) === k)) lemmas.push(ev.lits.slice());
          });
        }
        const next = { ...s, lemmas };
        // Steps already seen (identical events) stay shown; your own new
        // decision is shown at once; everything after it waits for "Next".
        const events = r.events.map((e) => JSON.stringify(e));
        let same = 0;
        while (same < prevEvents.current.length && same < events.length && prevEvents.current[same] === events[same]) same++;
        prevEvents.current = events;
        const steps = buildSteps(r, makeLabels(r), next.learnedKeys);
        // ("unit"/"derive" show the state just before their propagation event)
        const eventOf = (st: (typeof steps)[number]) => (st.kind === "unit" || st.kind === "derive" ? st.stateEnd + 1 : st.stateEnd);
        let c = steps.filter((st) => eventOf(st) < same).length;
        if (steps[c]?.kind === "decide" && !steps[c].bySolver) c++;
        setSession(next);
        setResp(r);
        setCursor(c);
        setError(null);
      } catch (e) {
        setError((e as Error).message);
      } finally {
        setBusy(false);
      }
    },
    [theoryProp],
  );

  // load examples, start with the slides' introduction example (x+1>0 ∨ x+y>0) ∧ …
  useEffect(() => {
    const ex = loadExamples();
    setExamples(ex);
    const i = Math.max(0, ex.findIndex((e) => /DPLL\(T\) intro/.test(e.name)));
    setExampleIdx(i);
    if (ex[i]) {
      prevEvents.current = [];
      run(emptySession(ex[i].text));
    }
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, []);

  const L = useMemo(() => (resp ? makeLabels(resp) : null), [resp]);
  const steps = useMemo(() => (resp && L ? buildSteps(resp, L, session.learnedKeys) : []), [resp, L, session.learnedKeys]);
  const tcs = useMemo(() => (resp ? theoryClauses(resp) : new Map()), [resp]);
  const step = cursor > 0 ? steps[cursor - 1] : null;
  const state = useMemo(() => (resp ? stateAt(resp, step ? step.stateEnd : -1) : null), [resp, step]);
  const atEnd = cursor >= steps.length;

  const go = useCallback((c: number) => setCursor(Math.max(0, Math.min(steps.length, c))), [steps.length]);

  useEffect(() => {
    const onKey = (e: KeyboardEvent) => {
      if ((e.target as HTMLElement).closest("textarea, input, select")) return;
      if (e.key === "ArrowRight") { go(cursor + 1); e.preventDefault(); }
      else if (e.key === "ArrowLeft") { go(cursor - 1); e.preventDefault(); }
      else if (e.key === "End") { go(steps.length); e.preventDefault(); }
    };
    window.addEventListener("keydown", onKey);
    return () => window.removeEventListener("keydown", onKey);
  }, [cursor, go, steps.length]);

  // ---------------------------------------------------------------- actions
  const decide = (lit: Lit) => run({ ...session, decisions: [...session.decisions, lit] });
  const pickUnit = (lit: Lit) => run({ ...session, picks: [...session.picks, { after: session.decisions.length, lit }] });
  // picks made after a removed decision go with it
  const keepPicks = (n: number) => session.picks.filter((p) => p.after <= n);
  const undoTo = (i: number) => run({ ...session, decisions: session.decisions.slice(0, i), picks: keepPicks(i) });
  const backtrack = () => {
    const rp = resp?.replay;
    let { lemmas, learnedKeys, refuted } = session;
    const decisions = session.decisions.slice();
    if (rp?.outcome === "conflict") {
      // the last decision is refuted under the ones before it; if the other
      // case was refuted too, those earlier decisions cannot all hold either
      let d = decisions.pop()!;
      refuted = [...refuted, { prefix: decisions.slice(), lit: d }];
      while (decisions.length && isRefuted(refuted, decisions, -d)) {
        d = decisions.pop()!;
        refuted.push({ prefix: decisions.slice(), lit: d });
      }
    } else decisions.pop();
    // keep the clause CDCL learns from the conflict: it then forces the opposite value
    if (rp && rp.outcome === "conflict" && rp.learned && rp.learned.every((l) => Math.abs(l) <= (resp?.num_vars ?? 0))) {
      const k = keyOf(rp.learned);
      if (!lemmas.some((c) => keyOf(c) === k)) lemmas = [...lemmas, rp.learned];
      learnedKeys = new Set(learnedKeys).add(k);
    }
    run({ ...session, lemmas, learnedKeys, refuted, decisions, picks: keepPicks(decisions.length) });
  };
  const restart = (src = session.src) => {
    prevEvents.current = [];
    run(emptySession(src));
  };
  const finish = () => run(session, true);
  const refutedHere = (l: Lit) => isRefuted(session.refuted, session.decisions, l);

  // ---------------------------------------------------------------- decision preview
  // Runs the decision ahead of time (cached), so hovering a choice shows its effect.
  const fetchPreview = useCallback(
    (lit: Lit, pick = false) => {
      const k = JSON.stringify([session.src, session.decisions, session.picks, session.lemmas, theoryProp, lit, pick]);
      let p = previews.current.get(k);
      if (!p) {
        const picks = pick ? [...session.picks, { after: session.decisions.length, lit }] : session.picks;
        const decisions = pick ? session.decisions : [...session.decisions, lit];
        p = playground({ src: session.src, decisions, picks, lemmas: session.lemmas, theoryPropagation: theoryProp, finish: false });
        p.catch(() => previews.current.delete(k));
        previews.current.set(k, p);
      }
      return p;
    },
    [session, theoryProp],
  );
  const prefetch = useCallback((v: number) => [v, -v].forEach((l) => fetchPreview(l).catch(() => {})), [fetchPreview]);
  const hover = useCallback(
    (lit: Lit | null, pick = false) => {
      hovered.current = lit;
      if (lit === null || !L || !state) return setPreview(null);
      const now = state;
      fetchPreview(lit, pick)
        .then((r) => {
          if (hovered.current === lit) setPreview(previewOf(lit, pick, r, now, L));
        })
        .catch(() => {});
    },
    [fetchPreview, L, state],
  );
  useEffect(() => {
    hovered.current = null;
    setPreview(null);
    if (resp?.replay.outcome === "split" && resp.replay.split) prefetch(Math.abs(resp.replay.split.lit));
    for (const u of resp?.replay.units ?? []) fetchPreview(u.lit, true).catch(() => {});
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [resp]);

  // ---------------------------------------------------------------- derived view data
  const extras: ExtraClause[] = useMemo(() => {
    if (!resp || !state) return [];
    const out: ExtraClause[] = [];
    resp.replay.db.forEach((c, id) => {
      if (!c.length) return;
      const info = clauseInfo(resp, tcs, session.learnedKeys, id);
      const kept = id < resp.num_original && (info.kind === "learned" || info.kind === "lemma");
      const fresh = id >= resp.num_original && tcs.get(id)?.kind === "conflict";
      if (!kept && !fresh) return;
      // a lemma found in this run appears once its step has been shown
      if (fresh && resp.events.findIndex((e) => e.type === "TheoryClause" && e.clause === id) > state.end) return;
      out.push({ id, lits: c, tag: info.kind === "learned" ? "learned" : `${tcs.get(id)?.theory ?? "theory"} lemma` });
    });
    return out;
  }, [resp, state, tcs, session.learnedKeys]);

  const highlight = useMemo(() => {
    // while pointing at a unit clause to pick: that clause
    const unit = preview?.pick ? resp?.replay.units.find((u) => u.lit === preview.lit)?.clause : undefined;
    const clause = unit ?? step?.clause;
    if (!resp || clause === undefined) return { assertion: -1, extra: -1 };
    const info = clauseInfo(resp, tcs, session.learnedKeys, clause);
    return { assertion: info.assertion ?? -1, extra: clause };
  }, [resp, step, tcs, session.learnedKeys, preview]);

  // several unit clauses at once: where each one is in the formula
  const units = useMemo(
    () =>
      atEnd && resp?.replay.outcome === "units"
        ? resp.replay.units.map((u) => ({ ...u, assertion: clauseInfo(resp, tcs, session.learnedKeys, u.clause).assertion ?? -1 }))
        : [],
    [atEnd, resp, tcs, session.learnedKeys],
  );

  const canDecide = atEnd && resp?.replay.outcome !== "conflict" && resp?.replay.outcome !== "units" && !busy;

  return (
    <div className="page">
      <header className="topbar">
        <div className="title">
          <h1>DPLL(T) Playground</h1>
          <p>
            {edu ? "Educational mode: one idea per level. Solve it, then go to the next." : <>Click a literal in the formula to decide it, then press <b>Next</b> to watch what follows.</>}
          </p>
        </div>
        <div className="controls">
          <label className="toggle edu-toggle" title="Levels that teach one part of DPLL(T) at a time, instead of the examples">
            <input
              type="checkbox"
              checked={edu}
              onChange={(e) => {
                setEdu(e.target.checked);
                try {
                  localStorage.setItem("playground.edu", e.target.checked ? "1" : "0");
                } catch {
                  /* remembered only when possible */
                }
              }}
            />
            Educational mode
          </label>
          {edu ? (
            <select value={levelIdx} onChange={(e) => { setLevelIdx(Number(e.target.value)); e.target.blur(); }}>
              {TOPICS.map((t) => (
                <optgroup key={t.kind} label={t.name}>
                  {LEVELS.map((l, i) => (l.kind === t.kind ? <option key={l.id} value={i}>{levelName(i, solved)}</option> : null))}
                </optgroup>
              ))}
            </select>
          ) : (
          <>
          <select
            value={exampleIdx}
            onChange={(e) => {
              const i = Number(e.target.value);
              e.target.blur(); // so ← → End step through the example, not the list
              setExampleIdx(i);
              restart(examples[i].text);
            }}
          >
            {[...new Set(examples.map((e) => e.group))].map((g) => (
              <optgroup key={g} label={g}>
                {examples.map((e, i) => (e.group === g ? <option key={i} value={i}>{e.name}</option> : null))}
              </optgroup>
            ))}
          </select>
          <button className="ghost" onClick={() => setEditing(true)}>Edit formula</button>
          <button className="ghost" onClick={() => setWriting(true)}>Write a formula</button>
          <label className="toggle" title="On: theories also derive literals (e.g. x ≤ 3 gives x ≤ 5). Off: they only check the context, as in the textbook DPLL(T) loop.">
            <input
              type="checkbox"
              checked={theoryProp}
              onChange={(e) => {
                setTheoryProp(e.target.checked);
                run(session, false, e.target.checked);
              }}
            />
            theory propagation
          </label>
          </>
          )}
        </div>
      </header>

      {error && <div className="error">{error}</div>}

      {edu && <EduMode index={levelIdx} solved={solved} setSolved={setSolved} onGo={(i) => { setLevelIdx(i); window.scrollTo({ top: 0 }); }} />}

      {!edu && resp && L && state && (
        <>
          <main className="board">
            <section className="card formula-card">
              <h2>Formula</h2>
              <FormulaView
                resp={resp}
                L={L}
                state={state}
                extras={extras}
                highlight={highlight}
                focusLits={step?.lits ?? []}
                stepKind={step?.kind}
                canDecide={canDecide}
                decisions={session.decisions}
                onDecide={decide}
                onUndo={undoTo}
                preview={preview}
                onPreview={hover}
                onPrefetch={prefetch}
                refuted={refutedHere}
                units={units}
                onPick={pickUnit}
                atEnd={atEnd}
              />
            </section>
            <section className="card context-card">
              <h2>Context</h2>
              <ContextView resp={resp} L={L} state={state} tcs={tcs} learnedKeys={session.learnedKeys} focusLits={step?.lits ?? []} />
              <div className="context-actions">
                <button onClick={backtrack} disabled={!session.decisions.length || busy}>Backtrack on a decision</button>
                <button className="ghost" onClick={finish} disabled={busy || resp.replay.outcome === "sat" || resp.replay.outcome === "unsat"}>Let the solver finish</button>
                <button className="ghost" onClick={() => restart()} disabled={busy}>Start over</button>
              </div>
            </section>
          </main>

          <section className="stepper">
            <StepCard
              step={step}
              index={cursor}
              total={steps.length}
              atEnd={atEnd}
              onPrev={() => go(cursor - 1)}
              onNext={() => go(cursor + 1)}
              onAll={() => go(steps.length)}
              onShowTheory={resp.smt ? () => theoryRef.current?.scrollIntoView({ behavior: "smooth", block: "start" }) : undefined}
            />
          </section>

          {atEnd && <Outcome resp={resp} L={L} state={state} hasDecisions={session.decisions.length > 0} onBacktrack={backtrack} onDecide={decide} onFinish={finish} refuted={refutedHere} preview={preview} onPreview={hover} onPick={pickUnit} />}

          <section className="lower">
            <section className="card history-card">
              <h2>DPLL({resp.smt ? theoryName(resp) : "SAT"}) algorithm</h2>
              <History steps={steps} cursor={cursor} onPick={go} />
            </section>
            <section className="card graph-card">
              <h2>Implication graph</h2>
              <ImplicationGraph resp={resp} L={L} state={state} tcs={tcs} learnedKeys={session.learnedKeys} focusLits={step?.lits ?? []} />
            </section>
          </section>

          {resp.smt && <TheoryPanel ref={theoryRef} resp={resp} L={L} end={state.end} step={step} />}
        </>
      )}

      {writing && (
        <FormattedEditDialog
          onCancel={() => setWriting(false)}
          onUse={(text) => {
            setWriting(false);
            restart(text);
          }}
        />
      )}

      {editing && (
        <EditDialog
          initial={session.src}
          onCancel={() => setEditing(false)}
          onUse={(text) => {
            setEditing(false);
            restart(text);
          }}
        />
      )}
    </div>
  );
}
