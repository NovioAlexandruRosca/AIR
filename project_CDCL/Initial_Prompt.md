# Task: CDCL SAT Solver in Rust + Step-by-Step Visualizer

## 1. Context
University project (SMT / SAT solving course). Background concepts:
- SMT = Boolean constraint solver + theory solver; CDCL(T) is the long-term direction, but **this task is pure propositional CDCL only**.
- DPLL → Davis-Putnam lineage; **CDCL = DPLL + clause learning + non-chronological backjumping**.
- Core loop: **BCP (Boolean Constraint Propagation) + SEARCH (decide / analyze / backjump)**.
Reference for the kind of visualizer I want: https://cse442-17f.github.io/Conflict-Driven-Clause-Learning/

## 2. Goal
Build two parts:
1. **A CDCL solver in Rust** that is correct and reasonably efficient on SAT Competition instances.
2. **An interactive UI** that replays the solver's run step by step, forward and backward, so I can see exactly what the algorithm does.

## 3. Solver Requirements

### 3.1 Input: DIMACS CNF
- Lines starting with `c` are comments → ignore.
- Header: `p cnf <num_vars> <num_clauses>`.
- Each clause is a list of non-zero integers terminated by `0` (a clause may span lines).
- Literal `k` = variable k true, `-k` = variable k false.
- Handle malformed input with a clear error message, not a panic.

Example:
```
c This is a comment line
p cnf 5 3
1 -5 4 0
-1 5 3 4 0
-3 -4 0
```

### 3.2 Algorithm
- **BCP:** unit propagation, recording for each implied literal its **reason clause** and **decision level**.
- **Decision heuristic: MOMS** (Maximum Occurrences in clauses of Minimum Size). It is used only when BCP has nothing left to propagate.
  - Look only at clauses that are **not yet satisfied** and find the minimum number of unassigned literals among them.
  - Score each unassigned variable x as `(f(x) + f(¬x)) * 2^k + f(x) * f(¬x)`, where f counts occurrences in those minimum-size clauses (k = a constant, e.g. 1). Pick the highest score.
  - Polarity: assign the literal with more occurrences.
  - Tie-break deterministically (lowest variable index) so runs are reproducible.
- **Conflict analysis:** build the implication graph and learn the **First-UIP clause**. This is my definition of "not too general, not too strict": stricter than the all-decisions clause and more general than the clause at the conflict itself.
- **Backjumping:** jump non-chronologically to the second-highest decision level in the learned clause, then the learned clause becomes unit and propagates.
- **Termination:** report SAT with a satisfying assignment (verify it against the original clauses), or UNSAT (conflict at decision level 0).

### 3.3 Output
- CLI: `solver <file.cnf>` → prints `s SATISFIABLE` / `s UNSATISFIABLE` and a `v ...` line with the model (SAT Competition output format).
- CLI flag `--trace <out.json>` → writes the full step-by-step event trace for the UI.

## 4. Trace Format (solver → UI contract)
The solver emits an ordered list of events. Each event must contain enough data to rebuild the full UI state at that step:
| Event | Data |
|---|---|
| `Decide` | variable, value, new decision level, MOMS scores of the candidates |
| `Propagate` | literal, reason clause id, decision level |
| `Conflict` | conflicting clause id |
| `Resolve` | each resolution step during analysis (clause A, clause B, pivot, resolvent) |
| `Learn` | learned clause, UIP literal, implication-graph node ids involved |
| `Backjump` | from level → to level, literals unassigned |
| `Result` | SAT + model, or UNSAT |

## 5. UI Requirements
- Load a `.cnf` file (or paste text), run the solver, show the trace.
- Controls: **Step forward, step back, jump to start/end, play/pause**, plus a step counter. Stepping back must restore the exact earlier state.
- Panels:
  1. **Formula view:** every clause, colored by status (satisfied / unsatisfied / unit / conflicting). Learned clauses appear in a separate, labeled group.
  2. **Trail / assignment stack:** literals grouped by decision level, with decisions marked differently from propagations.
  3. **Implication graph:** nodes = assigned literals (labeled `x@level`), edges come from reason clauses, the conflict node is highlighted, and the UIP and the cut that produces the learned clause are shown during analysis.
  4. **Event log:** a plain-language explanation of the current step (e.g. "x3 = false propagated by clause C2", "Backjump from level 4 to level 1").
- Must handle small teaching examples comfortably. For large instances, the UI can refuse or truncate past a step limit.

## 6. Decisions You May Make (tell me what you chose and why)
- UI technology. Suggested: Rust compiled to **WASM** + a web frontend, so it runs in a browser like the reference site. A Rust CLI that writes JSON plus a standalone HTML viewer would also work.
- Data structures: e.g. **two-watched-literals** for BCP vs. simple occurrence lists, trail representation, how clauses are stored (arena / `Vec<Vec<Lit>>`).
- Any extras worth having (restarts, clause deletion). These must stay **off by default** so the visualization stays faithful to plain CDCL.

## 7. Deliverables
1. A Cargo project with a `solver` library crate, a CLI binary, and the UI.
2. Unit tests: parser, BCP, First-UIP analysis on a hand-checked example, and SAT/UNSAT on small known instances.
3. A README covering how to build and run, the design decisions from §6, and a short walkthrough of the example above.

## 8. Process
1. Write a plan (modules, data structures, trace schema) and show it to me before implementing.
2. Implement the solver and CLI first, then test them on the example plus a few SAT Competition files.
3. Implement the UI on top of the trace.
4. Report what was verified and what wasn't.

## 9. Acceptance Criteria
- Correct SAT/UNSAT on the test set, and every SAT model checks out against the input.
- In the UI, stepping forward then back returns an identical state.
- The learned clause at each conflict is the First-UIP clause, and it can be checked by hand on the example.