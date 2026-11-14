import { useEffect, useRef } from "react";
import type { Step } from "../model";

interface Props {
  steps: Step[];
  cursor: number;
  onPick: (cursor: number) => void;
}

/** Steps seen so far, worded like the slides' "DPLL(T) algorithm" list. */
export function History({ steps, cursor, onPick }: Props) {
  const box = useRef<HTMLOListElement>(null);
  useEffect(() => {
    box.current?.querySelector(".current")?.scrollIntoView({ block: "nearest" });
  }, [cursor]);

  const shown = steps.slice(0, cursor);
  if (!shown.length) return <p className="empty">Your steps will appear here.</p>;
  return (
    <ol className="history" ref={box}>
      {shown.map((s, i) => (
        <li
          key={i}
          className={`k-${s.kind} ${i === cursor - 1 ? "current" : ""} ${i > 0 && s.group !== shown[i - 1].group ? "group-start" : ""}`}
          onClick={() => onPick(i + 1)}
        >
          {s.kind === "unsat" || s.kind === "sat" ? <b>{s.line}</b> : s.line}
          {s.bySolver && <span className="by-solver"> · solver</span>}
        </li>
      ))}
    </ol>
  );
}
