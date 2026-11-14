import type { Step, StepKind } from "../model";

interface Props {
  step: Step | null;
  index: number;
  total: number;
  atEnd: boolean;
  onPrev: () => void;
  onNext: () => void;
  onAll: () => void;
  /** scroll to the theory panel (theory steps only) */
  onShowTheory?: () => void;
}

const kindName: Record<StepKind, string> = {
  decide: "Decide",
  unit: "Unit clause",
  derive: "Theory reasoning",
  propagate: "Propagate",
  invoke: "Theory check",
  "theory-unsat": "Theory conflict",
  lemma: "Theory lemma",
  conflict: "Conflict",
  learn: "Learn",
  backjump: "Backjump",
  sat: "Satisfiable",
  unsat: "Unsatisfiable",
};

const theoryKinds: StepKind[] = ["invoke", "theory-unsat", "derive", "lemma"];

export function StepCard({ step, index, total, atEnd, onPrev, onNext, onAll, onShowTheory }: Props) {
  return (
    <div className={`step-card ${step ? `k-${step.kind}` : ""}`}>
      <div className="step-text">
        {step ? (
          <>
            <span className="step-kind">
              {kindName[step.kind]}
              {step.bySolver && <span className="by-solver"> · solver finishing</span>}
            </span>
            <h3>{step.head}</h3>
            <p>{step.body}</p>
            {onShowTheory && theoryKinds.includes(step.kind) && step.theory && (
              <button className="link" onClick={onShowTheory}>See how {step.theory} decides this, step by step ↓</button>
            )}
          </>
        ) : (
          <>
            <span className="step-kind">Start</span>
            <h3>{total ? "Press Next to see what happens" : "Nothing is assigned yet"}</h3>
            <p>{total ? "Each press shows one small step." : "Click a literal in the formula and choose true or false."}</p>
          </>
        )}
      </div>
      <div className="step-nav">
        <button className="ghost" onClick={onPrev} disabled={index === 0}>← Back</button>
        <span className="counter">{total ? `${index} / ${total}` : "—"}</span>
        <button className="primary" onClick={onNext} disabled={atEnd}>Next →</button>
        <button className="ghost small" onClick={onAll} disabled={atEnd}>Show all</button>
      </div>
    </div>
  );
}
