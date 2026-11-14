import { LEVELS, TOPICS } from "./levels";
import { Propagation } from "./Propagation";
import { Plot } from "./Plot";
import { Lemma } from "./Lemma";
import { Graph } from "./Graph";
import { Conflict } from "./Conflict";
import { Simplex } from "./Simplex";
import { Closure } from "./Closure";
import { Exchange } from "./Exchange";
import { Purify } from "./Purify";

const STORE = "playground.solved";
export const loadSolved = (): Set<string> => {
  try {
    return new Set(JSON.parse(localStorage.getItem(STORE) ?? "[]"));
  } catch {
    return new Set();
  }
};

/** A level's name gives the exercise away, so it shows only once solved. */
export const levelName = (i: number, solved: Set<string>) => {
  const l = LEVELS[i];
  const n = LEVELS.slice(0, i + 1).filter((m) => m.kind === l.kind).length;
  return solved.has(l.id) ? l.title : `Level ${n}`;
};

/** One level of the educational mode: only what this exercise needs is on screen. */
export function EduMode({ index, onGo, solved, setSolved }: { index: number; onGo: (i: number) => void; solved: Set<string>; setSolved: (s: Set<string>) => void }) {
  const level = LEVELS[index];
  const topic = TOPICS.find((t) => t.kind === level.kind)!;
  const done = () => {
    const s = new Set(solved).add(level.id);
    setSolved(s);
    try {
      localStorage.setItem(STORE, JSON.stringify([...s]));
    } catch {
      /* progress is a convenience */
    }
  };
  const body = (() => {
    switch (level.kind) {
      case "propagation":
        return <Propagation key={level.id} level={level} onSolved={done} />;
      case "plot":
        return <Plot key={level.id} level={level} onSolved={done} />;
      case "lemma":
        return <Lemma key={level.id} level={level} onSolved={done} />;
      case "graph":
        return <Graph key={level.id} level={level} onSolved={done} />;
      case "conflict":
        return <Conflict key={level.id} level={level} onSolved={done} />;
      case "simplex":
        return <Simplex key={level.id} level={level} onSolved={done} />;
      case "closure":
        return <Closure key={level.id} level={level} onSolved={done} />;
      case "purify":
        return <Purify key={level.id} level={level} onSolved={done} />;
      case "exchange":
        return <Exchange key={level.id} level={level} onSolved={done} />;
    }
  })();

  return (
    <main className="edu">
      <nav className="edu-levels card">
        {TOPICS.map((t) => (
          <div key={t.kind}>
            <h5>{t.name}</h5>
            {LEVELS.map((l, i) =>
              l.kind === t.kind ? (
                <button key={l.id} className={`edu-level ${i === index ? "on" : ""}`} onClick={() => onGo(i)}>
                  <span className="tick-mark">{solved.has(l.id) ? "✓" : ""}</span>
                  {levelName(i, solved)}
                </button>
              ) : null,
            )}
          </div>
        ))}
      </nav>
      <section className="card edu-card">
        <span className="step-kind">{topic.name}</span>
        <h2 className="edu-title">{levelName(index, solved)}</h2>
        <p className="edu-about">{topic.about}</p>
        <p className="edu-intro">{level.intro}</p>
        {body}
        {solved.has(level.id) && index + 1 < LEVELS.length && (
          <div className="row end">
            <button className="primary" onClick={() => onGo(index + 1)}>Next level →</button>
          </div>
        )}
      </section>
    </main>
  );
}
