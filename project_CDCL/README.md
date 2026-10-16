# CDCL SAT solver in Rust + step-by-step visualizer

A Conflict-Driven Clause Learning solver: **DPLL + First-UIP clause learning + non-chronological backjumping**, with **MOMS** as the decision heuristic. It reads DIMACS CNF files (the SAT Competition format) and can record every step in a trace. A browser UI replays the trace forward and backward.

No external crates: the solver, the JSON output and the small HTTP server for the UI use only `std`.

## Build and run

```bash
cargo build --release
```

Solve a file (SAT Competition output; exit code 10 = SAT, 20 = UNSAT):

```bash
cargo run --release -- examples/spec_example.cnf
```

```
c parsed 5 variables, 3 clauses
c decisions 3  propagations 0  conflicts 0  learned 0  max level 3
c model verified against all 3 clauses
s SATISFIABLE
v 1 -2 -3 4 -5 0
```

Write a trace for the UI:

```bash
cargo run --release -- examples/uip_moms.cnf --trace uip.trace.json
```

Options:

| Option | Effect |
|---|---|
| `--trace-limit N` | Stop recording after N events (default 20 000). The solver still finishes, and the result is still recorded. |
| `--timeout T` | Give up with `s UNKNOWN` after `T` (`30`, `30s`, `500ms`, `2m`, or `none`). `serve` defaults to 60 s per request. |
| `--max-conflicts N` | Give up with `s UNKNOWN` after N conflicts. |
| `--no-reduce` | Never delete learned clauses (see "Learned-clause deletion" below). |

To stop a run early: press Ctrl+C in the terminal, or rely on `--timeout`. A solve started from the web page ends at the server's time limit.

### The visualizer

```bash
cargo run --release -- serve
```

Then open <http://127.0.0.1:8080/>. Pick an example, paste a formula or open a `.cnf` file, and press **Solve & visualize**. You can also open `ui/index.html` directly from disk and load a trace `.json` written by `--trace`. Solving inside the page needs the server.

Controls: **← / →** step, **Shift+← / →** jump to the previous/next conflict, **Space** play/pause, **Home/End**. You can also drag the slider or click any line in the event log.

Panels:

| Panel | Shows |
|---|---|
| Explanation | What the current step does and why: the MOMS score table for decisions, the reason clause for propagations, the running resolution chain during analysis |
| Formula | Every clause coloured satisfied / unit / conflicting / open; literal chips green (true), red (false) or grey; learned clauses `L1, L2…` in their own group; the clause involved in the current step is outlined |
| Implication graph | One row per decision level; nodes `lit@level` (decisions blue); edges come from reason clauses; κ is the conflict node. During analysis: resolved nodes are orange (conflict side), the First UIP is purple, and dashed red **cut edges** come from exactly the literals of the current resolvent |
| Trail | The assignment stack grouped by level; `d` marks decisions, the subscript names the reason clause |
| Event log | Every event, clickable |

Stepping back rebuilds the state by replaying events from a checkpoint (one every 250 events). So it is the same deterministic computation as stepping forward. This was checked by comparing every step's rendered state forward and backward on all examples and on a 1 000-event trace.

## Project layout

```
src/lit.rs       literal encoding (2·var + sign)
src/dimacs.rs    DIMACS parser with line-numbered errors and warnings
src/solver.rs    CDCL: 2WL BCP, MOMS, First-UIP analysis, backjumping
src/trace.rs     trace events and their JSON encoding
src/lib.rs       solve_to_json(): the full run as JSON
src/main.rs      CLI
src/server.rs    std-only HTTP server for the UI (127.0.0.1 only, one thread per connection)
ui/index.html    the visualizer (single file, no build step, embedded into the binary)
examples/*.cnf   teaching examples
tests/           end-to-end and trace-consistency tests
```

## Design decisions

**Literals.** A literal is a `u32` holding `2·var + sign`. Negation is `^ 1`, and a literal indexes watch lists and counters directly. DIMACS `x3` is internal var 2.

**Clause storage.** `Vec<Clause>` with `lits: Vec<Lit>`. Original clauses come first, learned clauses are appended, and a clause's index is its permanent id. The trace and UI rely on this (`C1…` originals, `L1…` learned). Duplicate literals are merged on load. An arena would be faster, but stable ids matter more here.

**BCP: two watched literals.** Each clause with ≥ 2 literals watches `lits[0]` and `lits[1]`. When a watched literal becomes false, the solver looks for a replacement. If there is none, the clause is unit (propagate) or conflicting. Nothing needs undoing on backjump, which keeps backjumping cheap. Each watch entry also stores a *blocker*, another literal of the clause. If the blocker is true, the clause is satisfied and BCP skips it without reading it. Unit and empty input clauses are handled at level 0 before search.

**Trail.** `trail: Vec<Lit>` in assignment order. `trail_lim[d]` is where level `d+1` starts. Each variable stores `value`, `level` and `reason` (clause id, or none for a decision). The implication graph is implicit in these reasons, and the UI draws it from them.

**MOMS decisions.** Used only when BCP has nothing left to propagate.
1. Among clauses with no true literal, find the minimum number of unassigned literals `m` (always ≥ 2 after BCP).
2. Count `f(x)` and `f(¬x)` over the unassigned literals of the clauses with exactly `m` open literals.
3. The score is `(f(x)+f(¬x))·2^k + f(x)·f(¬x)` with `k = 1` (`MOMS_K`).
4. The highest score wins, ties go to the lowest variable index, and the polarity is the more frequent literal (positive on a tie). The solver is fully deterministic.
5. If no clause is open, the formula is satisfied (free variables are reported false).

MOMS scores **only the original clauses**. Learned clauses follow from the originals, so "every original clause satisfied" already means the formula is solved. An earlier version also scanned the learned clauses: with tens of thousands of them, every decision got slower and the solver became quadratic. On 250-variable files, 3 of 12 hit a 60 s limit that way.

**First-UIP learning.** This is the "not too general, not too strict" choice. Analysis starts at the conflict clause. It repeatedly resolves on the most recently assigned conflict-level literal, using that literal's reason clause, until exactly one conflict-level literal remains. That literal's node is the First UIP, the dominator of the conflict closest to it.
- The all-decisions clause (cutting at the decisions) is more general and weaker for pruning.
- Stopping at the conflict clause learns nothing new.

The solver uses the standard `seen`-flag/counter method. When tracing, it also builds every intermediate resolvent explicitly, so the UI can show the resolution chain. A debug assertion checks that the explicit resolvent equals the learned clause. Literals from level 0 are kept in the learned clause rather than dropped, so it matches the hand-resolution exactly.

**Backjumping.** Learned clause `[¬uip, rest…]`. The solver jumps to the highest level among `rest` (0 for a unit clause), undoes everything above it, adds the clause, and propagates `¬uip` with the new clause as its reason. When `rest` is empty or comes from much older levels, this skips levels (non-chronological).

**Learned-clause deletion (big inputs only).** Every learned clause sits in two watch lists. Without deletion, the cost of each conflict grows with the number of learned clauses, so total time grows quadratically: on one 250-variable file, 20k conflicts took 1 s and 120k took 32 s. Reduction runs once more than 8 000 learned clauses are alive:
- It keeps "glue" clauses, whose literals span ≤ 2 decision levels (LBD, the *literal block distance*).
- It keeps clauses that are currently the reason for an assignment.
- Of the rest, it deletes the worse half, ranked by LBD and then by length.
- The threshold then grows by 10%.

Deleted clauses keep their id, with empty literals, so ids stay stable. **A recorded trace never contains a deletion.** Each learned clause costs at least 3 trace events, so a traced run raises the threshold above `trace limit / 3`, which is more than the trace can ever record. Everything the UI shows is plain CDCL. `--no-reduce` turns deletion off completely.

**Not included (on purpose).** There are no restarts, no VSIDS and no learned-clause minimisation. They would change the decisions or learned clauses the trace shows, and the task asked for MOMS and plain First-UIP CDCL. They would be the next steps for speed.

**Performance.** Measured on random 3-SAT, release build, with 6 files per size:

| Instances | Result | Time |
|---|---|---|
| 100–150 vars, ratio 4.26 | all solved | ≤ 0.1 s |
| 250 vars, 1000 clauses (ratio 4.0) | 6/6 SAT | 1 ms – 0.7 s |
| 250 vars, 1065 clauses (ratio 4.26, hardest) | 3 SAT, 3 UNSAT | SAT ≤ 1.2 s; UNSAT 4.4 – 8.9 s (80k–130k conflicts) |

The hard UNSAT files need over 100k conflicts with MOMS and no restarts. That's the heuristic's limit, not a bug. In the web UI a solve also records the trace. When the solve takes under 1 s it is run a second time, without tracing, to report the "solver" time; longer solves report their single traced time.

**UI technology.** A Rust binary with a built-in `std` HTTP server plus one static HTML/JS page. WASM was the other option. It would need the `wasm32` target and `wasm-bindgen`/`wasm-pack`, which weren't installed, and it would add a build step. With this design the browser never re-implements solver logic: it only replays the trace. The page also works offline from a `.json` trace.

## Trace format

`solve_to_json` / `--trace` produce:

```json
{ "num_vars": 5, "num_original": 3, "clauses": [[1,-5,4], [-1,5,3,4], [-3,-4]],
  "warnings": [], "status": "SAT", "stop_reason": null, "verified": true, "truncated": false,
  "model": [1,-2,-3,4,-5], "moms_k": 1,
  "stats": {"decisions": 3, "propagations": 0, "conflicts": 0, "learned": 0, "deleted": 0, "max_level": 3},
  "timing": {"parse_ms": 0.011, "solve_ms": 0.019, "solve_untraced_ms": 0.006},
  "events": [ ... ] }
```

`timing` is wall-clock time in milliseconds:
- `solve_ms` is the run that recorded the trace, so it includes the tracing cost.
- In `serve` mode the formula is then solved a second time without tracing. Its time goes in `solve_untraced_ms`, which is the solver's real speed. The solver is deterministic, so both runs take identical steps.
- `--trace` from the CLI only does the traced run, so `solve_untraced_ms` is `null` there.

The UI header shows these times, plus the browser's round-trip time and propagations / conflicts / decisions per second (from the untraced time). On tiny formulas the times are a few microseconds and dominated by timer noise.

Literals are DIMACS integers, variables are 1-based, and clause ids are 0-based (`C1` = id 0; learned clauses continue after the originals).

| Event | Fields |
|---|---|
| `Decide` | `lit`, `level` (new level), `min_size` (MOMS `m`), `candidates` (top 8: `var`, `pos`=f(x), `neg`=f(¬x), `score`) |
| `Propagate` | `lit`, `reason` (clause id), `level` |
| `Conflict` | `clause`, `level` |
| `Resolve` | `clause_a` (current resolvent; on the first step the conflict clause, then `clause_a_id` is its id), `clause_b` (reason clause id), `pivot` (var), `resolvent` |
| `Learn` | `clause` (new id), `lits`, `uip` (the UIP node's literal on the trail; the clause contains its negation), `conflict_side` (resolved vars), `reason_side` (vars of the learned clause), `backjump_level` |
| `Backjump` | `from`, `to`, `unassigned` (in trail order) |
| `Result` | `status` (`SAT`/`UNSAT`/`UNKNOWN`), `model` |

## Walkthrough 1: the example from the task

```
p cnf 5 3
1 -5 4 0        C1
-1 5 3 4 0      C2
-3 -4 0         C3
```

1. **Decide ¬x3 @1.** The smallest open clause is C3 (size 2). Both x3 and x4 score `(0+1)·2 + 0 = 2`. The tie goes to x3, and since f(¬x3) > f(x3) it is set to false. C3 is now satisfied.
2. **Decide x1 @2.** C1 and C2 both have 3 open literals (x3 is false in C2). Scores: x1 `(1+1)·2+1 = 5`, x5 `5`, x4 `(2+0)·2 = 4`. The tie goes to x1 and the polarity is positive, which satisfies C1.
3. **Decide x4 @3.** Only C2 = (x5 ∨ x4) is open (size 2). x4 and x5 tie at 2, so x4 = true.
4. **SAT.** All clauses are satisfied, and the free variables x2 and x5 are reported false. Model `1 -2 -3 4 -5`.

There is no conflict here. The examples below show learning.

## Walkthrough 2: First UIP ≠ decision (`examples/uip_moms.cnf`, as MOMS runs it)

```
C2: 4 ∨ ¬1 ∨ 6     C3: 1 ∨ ¬2 ∨ ¬4    C6: 4 ∨ 3     C7: 4 ∨ 5 ∨ ¬3    C8: ¬7 ∨ 2    C10: ¬5 ∨ 4 ∨ ¬3   (+6 more)
```

| step | event |
|---|---|
| 1–2 | Decide x7 @1 → x2 (C8) |
| 3 | Decide ¬x1 @2 (MOMS: x1 and x4 both score 8; lowest index wins) |
| 4–6 | ¬x4 (C3: x1 and ¬x2 false), x3 (C6), x5 (C7) |
| 7 | **Conflict** on C10 = (¬x5 ∨ x4 ∨ ¬x3) |
| 8 | C10 ⊗ C7 on x5 → (¬x3 ∨ x4) |
| 9 | ⊗ C6 on x3 → (x4): only one level-2 literal left |
| 10 | **Learn L1 = (x4)**. The First UIP is ¬x4, an implied node, not the decision ¬x1. Every path from ¬x1 to κ passes through ¬x4. |
| 11 | **Backjump 2 → 0.** L1 is unit, so level 1 (x7, x2) is undone as well, even though it had nothing to do with the conflict. |
| 12 | x4 @0 (L1), then search continues to SAT |

## Walkthrough 3: hand-checked First UIP (`examples/uip.cnf`, unit test `first_uip_hand_checked`)

```
C1: ¬1 ∨ 6    C2: ¬6 ∨ 2    C3: ¬6 ∨ 3 ∨ 5    C4: ¬2 ∨ 4    C5: ¬3 ∨ ¬4    C6: 7 ∨ 8
```

The unit test forces the decisions ¬x5 @1, x7 @2, x1 @3. MOMS would choose differently on this file. Level 3 then propagates x6 (C1), x2 (C2), x3 (C3, because x5 is false) and x4 (C4), and C5 conflicts.

| resolution | result | level-3 literals left |
|---|---|---|
| start C5 | (¬3 ∨ ¬4) | 2 |
| ⊗ C4 on x4 | (¬2 ∨ ¬3) | 2 |
| ⊗ C3 on x3 | (¬2 ∨ ¬6 ∨ 5) | 2 |
| ⊗ C2 on x2 | (¬6 ∨ 5) | **1 → First UIP x6** |

The learned clause is **(¬x6 ∨ x5)**. Its other literal is from level 1, so the solver backjumps from 3 to 1 (skipping level 2, the unrelated x7) and propagates ¬x6. The all-decisions clause would have been (¬x1 ∨ x5), which is weaker: it only blocks x1, while the learned clause blocks every way of reaching x6.

## Tests

```bash
cargo test
```

- **Parser:** the task example, clauses spanning or sharing lines, SATLIB `%` terminator, empty clause, warnings, line-numbered errors.
- **BCP:** reasons and levels along an implication chain; conflict detection.
- **MOMS:** the score and the tie-break on a hand-computed example.
- **First UIP:** the hand-checked example above, including each resolution step, the conflict side and the backjump level.
- **End-to-end:**
  - 600 random 3-SAT instances (3–12 vars, mixed SAT/UNSAT) cross-checked against brute force, with every model verified.
  - Pigeonhole PHP(n+1, n) for n ≤ 6 is UNSAT.
  - All example files.
- **Trace consistency:** every trace from the tests above is replayed and checked:
  - every propagation's reason clause is really unit;
  - every conflict clause is really all-false;
  - every learned clause has exactly one conflict-level literal and the right backjump level;
  - every backjump undoes exactly the trail suffix.
- **UI examples:** the formulas embedded in `ui/index.html` must match the files in `examples/`.

- **Clause deletion:** 400 random instances plus pigeonhole files are solved with deletion forced after only 4–20 learned clauses, and the answers still match brute force. A traced run never deletes.
- **Limits:** the time limit, cancellation and the conflict limit each stop the solver with the right reason.

Not yet tested on actual SAT Competition benchmark files. Timing used generated random 3-SAT with up to 250 variables and 1065 clauses.
