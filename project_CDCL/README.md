# CDCL(T) solver in Rust + DPLL(T) playground

A Conflict-Driven Clause Learning solver: **DPLL + First-UIP clause learning + non-chronological backjumping**, with **MOMS** as the decision heuristic. It reads DIMACS CNF files (the SAT Competition format) and can record every step in a trace.

The same solver is also the SAT engine of an **SMT solver (CDCL(T))** for **linear integer arithmetic (LIA)** and **algebraic datatypes (DT)**, combined with **Nelson–Oppen** and input **purification**. See [SMT: LIA + datatypes](#smt-lia--datatypes-cdclt). The **Playground** web page lets you make the decisions yourself, watch the propagation step by step, and see inside the theory solvers (Simplex, congruence closure, purification).

No external crates: the solver, the JSON output and the small HTTP server for the UI use only `std`.

## Build and run

```bash
cargo build --release
```

Solve a file (SAT Competition output; exit code 10 = SAT, 20 = UNSAT):

```bash
printf 'p cnf 5 3\n1 -5 4 0\n-1 5 3 4 0\n-3 -4 0\n' | cargo run --release -- -
```

```
c parsed 5 variables, 3 clauses
c decisions 3  propagations 0  conflicts 0  learned 0  max level 3
c model verified against all 3 clauses
s SATISFIABLE
v 1 -2 -3 4 -5 0
```

Write the step-by-step trace as JSON:

```bash
cargo run --release -- examples/smt/dpllt_intro.smt2 --trace intro.trace.json
```

Options:

| Option | Effect |
|---|---|
| `--trace-limit N` | Stop recording after N events (default 20 000). The solver still finishes, and the result is still recorded. |
| `--timeout T` | Give up with `s UNKNOWN` after `T` (`30`, `30s`, `500ms`, `2m`, or `none`). `serve` defaults to 60 s per request. |
| `--max-conflicts N` | Give up with `s UNKNOWN` after N conflicts. |
| `--no-reduce` | Never delete learned clauses (see "Learned-clause deletion" below). |

To stop a run early: press Ctrl+C in the terminal, or rely on `--timeout`.

### The playground

```bash
cargo run --release -- serve
```

Then open <http://127.0.0.1:8080/>. See [Playground](#playground) below.

## Project layout

```
src/lit.rs       literal encoding (2·var + sign)
src/dimacs.rs    DIMACS parser with line-numbered errors and warnings
src/solver.rs    CDCL: 2WL BCP, MOMS, First-UIP analysis, backjumping
src/trace.rs     trace events and their JSON encoding
src/lib.rs       solve_to_json(): the full run as JSON
src/main.rs      CLI
src/server.rs    std-only HTTP server for the playground (127.0.0.1 only, one thread per connection)
src/smt/         CDCL(T): see "SMT: LIA + datatypes"
  sexp.rs        s-expression reader
  term.rs        hash-consed terms, sorts, symbol ownership, pretty printing, model values
  parser.rs      SMT-LIB 2 subset (theory commands and symbols are delegated to theories)
  theory.rs      the Theory trait, the only thing a new theory implements
  lia.rs, rat.rs linear integer arithmetic: Simplex over exact rationals, branch and bound
  dt.rs          algebraic datatypes: congruence closure with explanations
  preprocess.rs  purification, shared constants, Tseitin CNF, atom registration
  combine.rs     Nelson–Oppen combination, implemented as the SAT solver's TheoryHook
  mod.rs         pipeline, model verification, JSON, playground replay
playground/      the Playground page: React + TypeScript sources (Vite)
ui/playground/   its build output, embedded into the binary
examples/smt/    SMT-LIB examples (LIA, DT, combination), also the playground's example list
tests/           end-to-end and trace-consistency tests (SAT and SMT)
```

## Design decisions

**Literals.** A literal is a `u32` holding `2·var + sign`. Negation is `^ 1`, and a literal indexes watch lists and counters directly. DIMACS `x3` is internal var 2.

**Clause storage.** `Vec<Clause>` with `lits: Vec<Lit>`. Original clauses come first, learned clauses are appended, and a clause's index is its permanent id. The trace relies on this (`C1…` originals, `L1…` learned). Duplicate literals are merged on load. An arena would be faster, but stable ids matter more here.

**BCP: two watched literals.** Each clause with ≥ 2 literals watches `lits[0]` and `lits[1]`. When a watched literal becomes false, the solver looks for a replacement. If there is none, the clause is unit (propagate) or conflicting. Nothing needs undoing on backjump, which keeps backjumping cheap. Each watch entry also stores a *blocker*, another literal of the clause. If the blocker is true, the clause is satisfied and BCP skips it without reading it. Unit and empty input clauses are handled at level 0 before search.

**Trail.** `trail: Vec<Lit>` in assignment order. `trail_lim[d]` is where level `d+1` starts. Each variable stores `value`, `level` and `reason` (clause id, or none for a decision). The implication graph is implicit in these reasons, and the playground draws it from them.

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

The solver uses the standard `seen`-flag/counter method. When tracing, it also builds every intermediate resolvent explicitly, so the trace contains the resolution chain. A debug assertion checks that the explicit resolvent equals the learned clause. Literals from level 0 are kept in the learned clause rather than dropped, so it matches the hand-resolution exactly.

**Backjumping.** Learned clause `[¬uip, rest…]`. The solver jumps to the highest level among `rest` (0 for a unit clause), undoes everything above it, adds the clause, and propagates `¬uip` with the new clause as its reason. When `rest` is empty or comes from much older levels, this skips levels (non-chronological).

**Learned-clause deletion (big inputs only).** Every learned clause sits in two watch lists. Without deletion, the cost of each conflict grows with the number of learned clauses, so total time grows quadratically: on one 250-variable file, 20k conflicts took 1 s and 120k took 32 s. Reduction runs once more than 8 000 learned clauses are alive:
- It keeps "glue" clauses, whose literals span ≤ 2 decision levels (LBD, the *literal block distance*).
- It keeps clauses that are currently the reason for an assignment.
- Of the rest, it deletes the worse half, ranked by LBD and then by length.
- The threshold then grows by 10%.

Deleted clauses keep their id, with empty literals, so ids stay stable. **A recorded trace never contains a deletion.** Each learned clause costs at least 3 trace events, so a traced run raises the threshold above `trace limit / 3`, which is more than the trace can ever record. Everything a trace shows is plain CDCL. `--no-reduce` turns deletion off completely.

**Not included (on purpose).** There are no restarts, no VSIDS and no learned-clause minimisation. They would change the decisions or learned clauses the trace shows, and the task asked for MOMS and plain First-UIP CDCL. They would be the next steps for speed.

**Performance.** Measured on random 3-SAT, release build, with 6 files per size:

| Instances | Result | Time |
|---|---|---|
| 100–150 vars, ratio 4.26 | all solved | ≤ 0.1 s |
| 250 vars, 1000 clauses (ratio 4.0) | 6/6 SAT | 1 ms – 0.7 s |
| 250 vars, 1065 clauses (ratio 4.26, hardest) | 3 SAT, 3 UNSAT | SAT ≤ 1.2 s; UNSAT 4.4 – 8.9 s (80k–130k conflicts) |

The hard UNSAT files need over 100k conflicts with MOMS and no restarts. That's the heuristic's limit, not a bug. (The benchmark files are not part of the repository.)

**UI technology.** A Rust binary with a built-in `std` HTTP server serves one page, written in React. WASM was the other option. It would need the `wasm32` target and `wasm-bindgen`/`wasm-pack`, and a second build step. With this design the browser never re-implements solver logic: it only turns the solver's trace into pictures.

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
- `POST /api/solve` (in `serve` mode) solves the formula a second time without tracing. Its time goes in `solve_untraced_ms`, which is the solver's real speed. The solver is deterministic, so both runs take identical steps.
- `--trace` from the CLI only does the traced run, so `solve_untraced_ms` is `null` there.

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
| `TheoryClause` | (SMT) `clause` (new id), `lits`, `kind` (`explanation` / `conflict` / `axiom` / `lemma`), `theory`, `why` (human-readable argument) |
| `NewVar` | (SMT) `var`, `label`, `neg` (label of the negation), `kind`, `theories`: an atom created during search |
| `Theory` | (SMT) `theory`, `kind` (`conflict`, `nelson-oppen`, or `state` with a JSON snapshot in `data`), `message`, `lits` |

In SMT traces, `Decide` also carries `origin: {by, why}` for theory splits. An extra top-level `smt` object holds the assertions, the purified assertions, the definitions, the shared constants, the interface equalities, the label of every variable, the origin of every clause, and the verified model.

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

## Walkthrough 2: First UIP ≠ decision (as MOMS runs it)

```
p cnf 7 12
-2 -5 3 0       C1
4 -1 6 0        C2
1 -2 -4 0       C3
4 -7 -1 0       C4
-5 7 0          C5
4 3 0           C6
4 5 -3 0        C7
-7 2 0          C8
2 -5 1 0        C9
-5 4 -3 0       C10
4 -1 6 0        C11
-2 3 -1 0       C12
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

## Walkthrough 3: hand-checked First UIP (unit test `first_uip_hand_checked`)

```
C1: ¬1 ∨ 6    C2: ¬6 ∨ 2    C3: ¬6 ∨ 3 ∨ 5    C4: ¬2 ∨ 4    C5: ¬3 ∨ ¬4    C6: 7 ∨ 8
```

The unit test forces the decisions ¬x5 @1, x7 @2, x1 @3. MOMS would choose differently on this formula. Level 3 then propagates x6 (C1), x2 (C2), x3 (C3, because x5 is false) and x4 (C4), and C5 conflicts.

| resolution | result | level-3 literals left |
|---|---|---|
| start C5 | (¬3 ∨ ¬4) | 2 |
| ⊗ C4 on x4 | (¬2 ∨ ¬3) | 2 |
| ⊗ C3 on x3 | (¬2 ∨ ¬6 ∨ 5) | 2 |
| ⊗ C2 on x2 | (¬6 ∨ 5) | **1 → First UIP x6** |

The learned clause is **(¬x6 ∨ x5)**. Its other literal is from level 1, so the solver backjumps from 3 to 1 (skipping level 2, the unrelated x7) and propagates ¬x6. The all-decisions clause would have been (¬x1 ∨ x5), which is weaker: it only blocks x1, while the learned clause blocks every way of reaching x6.

## SMT: LIA + datatypes (CDCL(T))

### Running it

Any input whose first non-comment character is `(` (or any `.smt2` file) is treated as SMT-LIB 2:

```bash
cargo run --release -- examples/smt/combo_sat.smt2
```

```
; 5 assertions, theories LIA + DT, 29 Boolean variables, 31 clauses
; purification: k1 = 5
; purification: k2 = head(r)
; shared constants (Nelson–Oppen): x, y, k1, k2
sat
(
  (define-fun l () List (cons 3 (cons 5 nil)))
  (define-fun r () List (cons 9 (cons 110 nil)))
  (define-fun x () Int 3)
  (define-fun y () Int 5)
)
; model verified against all 5 assertions
```

The output is `sat` (with a model, exit code 10), `unsat` (20) or `unknown`. Every model is checked by evaluating every assertion before it is printed. `--trace`, `--timeout` and `--max-conflicts` work as for DIMACS. In the playground, pick one of the examples or paste SMT-LIB text with *Edit formula*.

Supported input:
- `declare-const` / `declare-fun` with no arguments, sorts `Int`, `Bool` and declared datatypes;
- `declare-datatypes` (SMT-LIB 2.6 and 2.5 syntax) and `declare-datatype`;
- `assert`, `check-sat`, `define-fun` without arguments, `let`, `!` annotations;
- `and or not => xor ite = distinct` (`ite` only on Bool);
- `+ - *` (multiplication by constants only), `<= < >= >`;
- constructors, selectors, `(_ is C)` testers.

Not supported: uninterpreted functions, parametric datatypes, `push`/`pop`, `ite` on Int terms, non-linear arithmetic. Each of these gives a line-numbered error.

### Architecture

```
SMT-LIB text
  └─ parser.rs ──► terms (hash-consed DAG; each function symbol and sort is owned by one theory)
       └─ preprocess.rs
            1. purification: alien subterms → fresh constants kᵢ, definitions kᵢ = t asserted
            2. shared constants (used by ≥ 2 theories) → interface equalities x = y for every pair
            3. Tseitin: Boolean structure → CNF; every theory atom is a Boolean variable
            4. registration: each atom is handed to its theory, which may add axioms
       └─ solver.rs (unchanged CDCL) ── TheoryHook ──► combine.rs (Nelson–Oppen)
                                                         ├── lia.rs
                                                         └── dt.rs
```

The SAT solver only knows about a `TheoryHook`. After every round of unit propagation it asks the hook for a **partial check**. When every problem clause is satisfied, it asks for a **final check**. The hook answers with clauses only:

| Answer | What the SAT solver does |
|---|---|
| propagation `l` because `e₁ … eₙ` | adds the explanation clause `(l ∨ ¬e₁ ∨ … ∨ ¬eₙ)` and enqueues `l` with that clause as its reason |
| conflict `e₁ … eₙ` | adds `(¬e₁ ∨ … ∨ ¬eₙ)`, which is falsified, and runs ordinary First-UIP analysis (backjumping first if the clause is falsified below the current level) |
| axiom | adds a permanent clause, e.g. the definition of a newly created atom |
| split `l` (final check only) | decides `l`: splitting on demand |
| nothing (final check) | SAT |

So conflict analysis, backjumping, the implication graph and the playground all work unchanged for theory reasoning. Theory propagations simply show up as clause-based propagations. The solver itself gained only:
- dynamic variables, for atoms a theory creates;
- adding clauses during search;
- an `origin` on split decisions;
- a playground `replay`, which can stop where the user has a choice (several unit clauses at once).

### Adding a theory

Implement `smt::theory::Theory` and add the theory to `smt::default_theories()`. Nothing else changes.

| Method | Purpose |
|---|---|
| `init`, `command`, `mk_app` | Declare sorts and symbols, handle theory commands (e.g. `declare-datatypes`), type-check applications. Ownership of symbols is what drives purification. |
| `register_atom` | Interpret an atom; may create further atoms and axioms through `Ctx`. |
| `assert_lit`, `backtrack` | Follow the SAT assignment. |
| `check(final)` | Return conflict / propagations (with explanations) / split / unknown. |
| `eq_hint` | Optional: guidance for Nelson–Oppen splits. |
| `model`, `eval_app`, `default_value` | Model construction and verification. |
| `snapshot` | JSON state for the UI. |

### LIA

- **Normal form.**
  - Every atom `t ⋈ c` becomes a bound on one *column*: an input variable, or a slack `s = Σ aᵢxᵢ`.
  - Coefficients are divided by their gcd and the bound is rounded. That makes the GCD test automatic: `2x − 2y = 1` becomes `x − y ≤ 0` and `x − y ≥ 1`.
  - Strict bounds are turned into non-strict integer ones (`x < 3` becomes `x ≤ 2`). A false atom is its integer complement: `¬(x ≤ 3)` means `x ≥ 4`.
- **Equalities.** `a = b` is not interpreted by Simplex. It is defined by axioms over two bound atoms, `a = b ⇔ a ≤ b ∧ a ≥ b`. This makes `a ≠ b` (a disjunction, so non-convex) a job for the SAT solver.
- **Consistency over ℚ.** This uses general Simplex (Dutertre–de Moura) with Bland's rule over exact rationals (`i128`; overflow is reported, not wrapped).
  - An infeasible row is the explanation: the violated bound of the basic variable plus the blocking bounds of the row's variables.
  - The UI prints it as an argument, e.g. *"Simplex row x = z + (x − y) + (y − z): it must be ≤ 2 (from x ≤ 2), but with z ≥ 1, x > y, y > z it is at least 3"*.
- **Integrality.** Branch and bound by splitting on demand. If a variable has a fractional value `v`, the final check creates the atom `x ≤ ⌊v⌋` and asks the SAT solver to decide it. Its negation is `x ≥ ⌈v⌉`. Learning then works on the branches like on any other decision. After 5 000 branches the answer is `unknown`.
- **Propagation.** A new bound on a column implies or refutes the other atoms on the same column (`x ≤ 3` ⇒ `x ≤ 5`, `¬(x ≥ 4)`). When both sides of an equality are fixed by their bounds, the equality (or disequality) is propagated: this is LIA's part of the Nelson–Oppen exchange.

### DT

- **Congruence closure.** The closure covers the datatype terms of the asserted literals. It is rebuilt from scratch at each check, so backtracking costs nothing. Every merge records its justification, so every conflict and propagation is explained by input literals only. The rules:
  - **clash**: `C(..) = D(..)` with `C ≠ D` is a conflict;
  - **injectivity**: `C(a) = C(b)` implies `a = b`;
  - **selectors**: `t = C(a₁…aₙ)` implies `selᵢ(t) = aᵢ`;
  - **testers**: `is-C(t)` instantiates `t = C(sel₁(t), …)`, `¬is-C(t)` excludes `C`, and the last remaining constructor is used;
  - **acyclicity**: an occurs check, so `l = cons(x, l)` is a conflict;
  - **disequalities**.
- **Propagation.** Equalities and testers that follow from the classes are propagated, including interface equalities between shared Int constants (DT's part of the Nelson–Oppen exchange).
- **Final check.** A class with no constructor is split on a tester (`is-C(t)`, non-recursive constructors first) when its sort is finite (e.g. `Color = red | green | blue`) or when a selector is applied to it.
- **Models.** Each class gets a value. Int classes take the LIA value where one exists; unconstrained classes get fresh values that differ from all the others.

### Purification and Nelson–Oppen

- **Purification.** A term owned by one theory inside a term of another theory is *alien*. It is replaced by a fresh constant, and the definition is asserted:
  - `head(l) = x + 1` becomes `head(l) = k1` (DT) with `k1 = x + 1` (LIA);
  - `cons(1, l)` becomes `cons(k1, l)` with `k1 = 1`.
  The UI's Purification tab shows every assertion before and after, the definitions and the shared constants.
- **Shared constants and interface equalities.** A constant used by atoms of two theories is shared (here always of sort Int). Every pair of shared constants of the same sort gets an *interface equality* atom `x = y`, registered with every theory that uses `x` or `y`. LIA gets it through its equality axioms, DT as an equality in the congruence closure.
- **Deterministic exchange.** A theory that derives an interface equality propagates it, and the other theories receive it as an ordinary literal. Examples: DT through injectivity, `cons(x,nil) = cons(y,nil)` ⇒ `x = y`; LIA when both sides are fixed. The trace marks these steps as *Nelson–Oppen*.
- **Non-convex case.** LIA and DT are not convex: a theory can imply `x = y ∨ x = z` without implying either. Interface equalities nobody derives are therefore *guessed*, by MOMS (they occur in LIA's equality axioms) or by a Nelson–Oppen split in the final check. The split polarity follows LIA's current model (`eq_hint`). `examples/smt/nonconvex.smt2` needs exactly this.
- **Soundness argument.** SAT is reported only when every interface atom is assigned and every theory accepts its literals together with that arrangement. That is the Nelson–Oppen condition: the theories share only the sort Int, which is infinite, so both theories are stably infinite there. The model is then verified against the original assertions anyway.

### Playground

<http://127.0.0.1:8080/> (after `cdcl serve`) is a teaching page written in **React** (TypeScript, Vite) with a light theme and large type. It follows the DPLL(T) presentation of Reynolds' VTSA 2017 lectures (slides 38–50) and opens on the slides' introduction example, `examples/smt/dpllt_intro.smt2`: `(x+1>0 ∨ x+y>0) ∧ (x<0 ∨ x+y>4) ∧ ¬(x+y>0)`. The slides' exercise `(x>y ∨ x>z) ∧ (x+1<y ∨ ¬x>y) ∧ (x>y ∨ z>y)` is the "Exercise" right below it. The example list has three groups: LIA, DT (opening with `dt_intro.smt2`) and LIA + DT. *Edit formula* takes any SMT-LIB or DIMACS text; *Write a formula* takes a formula as you would write it on paper, `(x + 1 > 0 or x + y > 0) and not (x + y > 0)` or `((x <= y) \/ (z < y)) /\ (x <= y)`, and shows the SMT-LIB it becomes (`src/formulaText.ts`: `and or not -> <->`, also `/\ \/ !`, `\and \or \not`, `∧ ∨ ¬`; `< <= > >= = !=`; sums and constant multiples; a compared name is an `Int`, a name used on its own a `Bool`; one assertion per line or top-level `and`).

| Part | What it shows |
|---|---|
| Formula | The assertions as written, each literal a chip: green when true, orange when false, grey while open. Click an open literal to decide it true or false; click a decision to undo it. The clause the current step talks about is outlined ("unit clause", "every literal false"). Theory lemmas and learned clauses are appended to the formula and stay when you backtrack. Atoms the formula does not show but that still need a value (the Nelson–Oppen arrangement of shared constants) appear under "Still to decide". LIA decides an equality `a = b` through two helper atoms, `a ≤ b` and `a ≥ b`; once the solver has given them values, the equality's chip shows "split into" with both halves underneath. |
| Context | The literals assigned so far, one per line, grouped by decision level; `d` marks decisions, the others say where they came from (F1, the learned clause, LIA, DT). |
| Current step | A large card with the step in the slides' wording and one sentence of explanation, plus *Back*, *Next* and *Show all* (← → End keys). |
| Outcome | Once every step is shown: "Your turn"; a conflict callout with the clause CDCL learns and a *Backtrack* button; the case split a theory asks for; the unit clauses to choose from; or a starburst "⇒ Input is LIA-unsat" / "satisfiable" with the model. |
| Algorithm | The steps seen so far as the slides' bullet list (*Decide*, *Propagate*, *Invoke theory solver for LIA on {…}*, *… is LIA-unsatisfiable*, *Add theory lemma*, *Conflicting clause!*); click one to go back to it. |
| Implication graph | Drawn with React Flow and laid out left to right by dagre: decisions with a thick border, unit propagations solid, theory propagations and Nelson–Oppen exchanges dashed purple, the conflict in red. The node of the current step is outlined. |

**Every propagation takes two clicks of Next.** First the reason (*F2 is unit*: every other literal of F2 is false, so the remaining one must be true; or *LIA derives y = k1*), then the assignment (*Propagate : x + 1 < y → true*). A theory conflict is: invoke the theory solver, context is unsatisfiable, add the lemma, conflicting clause.

**You make the choices.**
- **Preview.** Pointing at a choice (→ true / → false, a case of a split, a unit clause) runs it ahead of time: the literals it would set are shown dashed in the formula, with one line on how the run would end (e.g. "then LIA rejects the context: a conflict").
- **Several unit clauses at once.** When propagation makes two or more clauses unit and they force different literals, the solver stops: those clauses flash slowly in the formula, and you click one to make its literal true first. This includes the input's own facts (one-literal assertions such as the bounds in `lia_branch.smt2`), which are all unit from the start; when one assertion holds several of them (an `and` of facts), you click the flashing literal. With only one unit clause the solver propagates it without asking. Unit clauses over the theories' internal helper atoms are always propagated automatically.
- **Case splits.** A case that led to a conflict is not offered again under the same decisions. When both cases of a split have failed, the decision before them is undone too, and with no decision left the page says the input is unsat.

**Inside the theory solvers.** Below the graph, one tab per part of the theory reasoning, each with its own Back / Next. The tabs follow the main stepper: they show the theory's most recent check at the current step, and a theory step ("Invoke the theory solver for LIA") has a link that scrolls there.

| Tab | What it draws |
|---|---|
| LIA · Simplex | Two views. **Constraints**: with two variables, each arithmetic literal is a line in the plane; with three, a plane in a 3D view you can turn. The space starts green; each literal, one per step, lays a transparent red over the side it rules out, so points several literals rule out are darker, and green stays only where every literal allows the point. Each step also gives the literal's integer meaning (`x + 1 > 0` is `x ≥ 0`, `¬(x + y > 0)` is `x + y ≤ 0`). Further variables are eliminated (Fourier–Motzkin: `x − z ≥ 1` and `z − y ≥ 1` give `x − y ≥ 2`, purple). The last step is "LIA-unsatisfiable" (nothing green, the blamed literals in red, the lemma) or "Consistent" (the integer points in the green part). **Simplex**: the tableau after every pivot (each basic variable as a row over the others, every variable's value and bounds), the row that is out of bounds (red) and the variable that enters (blue), with the candidate point moving in the picture, until every bound holds or a row is stuck. |
| DT · congruence closure | The terms of the datatype literals as a graph (arrows to arguments), coloured by equivalence class. One merge per step, with its rule: asserted, congruence, injectivity (`cons(x, nil) = cons(y, nil)` gives `x = y`), selector, tester, only constructor left. Merges arc below the terms, disequalities above in red; then the conflict (constructor clash, violated disequality, cycle) or "consistent". Constants shared with LIA have a dashed purple outline. |
| Purification | Which symbols each theory understands; each mixed assertion before and after, with the alien subterm highlighted and the fresh constant that replaces it (`head(l) = x + 1` becomes `head(l) = k1` with `k1 = x + 1`); what each theory then sees; the shared constants Nelson–Oppen must agree on. Shown when the input has shared or fresh constants. |

The data comes from the solvers themselves: while tracing, LIA records each check (the asserted bounds after integer normalisation, and after every pivot the values and the whole tableau) and DT keeps its merge history with the rule of each merge; both are part of the theory snapshots in the trace (`check`, `nodes`, `history`, `diseqNodes`). The raw end-of-run tableau and classes are still there, folded away.

- **Theory propagation** is **off** by default. The theories then only *check* the context, as in the textbook loop; interface equalities are still propagated, so the Nelson–Oppen exchange stays visible. Turned on, theories also derive literals (bound propagation, congruence).
- **Backtrack** after a conflict keeps the First-UIP clause that CDCL would learn. That clause then propagates the opposite value: in the exercise, learn `¬(x > y)`, propagate `x > y → false`, choose between the unit clauses F1 and F3, then the final LIA conflict and "Input is LIA-unsat".
- **Let the solver finish** continues with full CDCL(T) search from your decisions; its steps are marked "solver".
- **Replay model.** Each action replays your decisions, unit-clause picks and kept lemmas on a fresh solver (`POST /api/playground`; a pick is written `u<lit>` in the `DECISIONS` line), so it is reproducible and backtracking is exact. A decision on an atom that a theory creates later (a split) waits until the atom exists.

**Educational mode.** The checkbox in the header replaces the examples with levels that each practise one idea, showing only what that exercise needs. The topics come in the order a course meets them, and a level's name stays hidden ("Level 2") until it is solved, so it gives nothing away (progress is kept in the browser):

| Topic | The task |
|---|---|
| Unit propagation | A formula and the decisions so far; in a copy of it, click every literal propagation sets (several rounds), and say which clause becomes false if there is a conflict. The check accepts any order propagation could take. |
| Implication graphs | The real solver's run (propositional, DPLL(LIA), and DPLL(DT) with theory propagation): click a propagated literal or κ, then the literals that caused it. Checked against the reason clauses. |
| Conflict analysis | The implication graph of a conflict: click the First UIP, then the literals on the cut (the learnt clause is their negations), then the backjump level. Checked against what the solver learns; a wrong UIP is told whether it is at the wrong level, not on every path, or a UIP but not the first. |
| LIA in the plane | For each constraint, click two grid points on its line, then a point on the side it allows; red covers what is ruled out, green what is left. At the end: is an integer point left? The last level is a small triangle with no grid point inside: Simplex finds a rational point, and you run branch and bound (pick a branch, split on a fractional value) until every branch is empty. |
| Simplex | A tableau of slack rows: click a basic variable that breaks its bound, then a nonbasic variable of its row that can repair it (the pivot is computed with exact fractions), until every bound holds (sat) or a row is stuck (unsat, with the row as the explanation). |
| Theory lemmas | A context LIA rejects: pick the literals that conflict. The solver checks that they really are unsatisfiable together, and that none of them is unnecessary; their negations are the lemma. |
| DT: congruence closure | Equalities and disequalities over lists and colours: click two terms to merge them, one justified step at a time (given, congruence or injectivity), then say what the conflict is (two constructors, a broken disequality, a cycle) or that there is none. |
| LIA + DT: purification | Mixed literals such as `head(l) + 1 ≤ x`: click every alien subterm (a DT term inside arithmetic, or an arithmetic term inside a DT term, also nested ones). The page then shows the purified LIA and DT parts with fresh constants `v1, v2, …` and their definitions, and you pick the constants both parts share. |
| LIA + DT: Nelson–Oppen | Which equalities between the shared constants LIA forces (checked by the solver), which DT then derives, and which theory finds the conflict, if any. |

**Building the page.** The sources are in `playground/` (`src/model.ts` turns the solver's events into steps, `src/components/` holds the views, `src/theory/` the theory tabs, `src/edu/` the educational levels; the 3D view uses three.js). The examples are bundled from `examples/smt/`, and their order and names are listed in `src/api.ts`. `npm run build` type-checks and writes `ui/playground/{index.html, playground.js, playground.css}`, which the Rust binary embeds with `include_str!`, so `cargo build` needs no Node. Rebuild after changing the sources or the examples:

```
cd playground
npm install
npm run build
```

For live reloading, run `cdcl serve` and `npm run dev` side by side; Vite proxies `/api` to port 8080.

### SMT examples

| File | Shows | Result |
|---|---|---|
| `dpllt_intro.smt2` | the DPLL(T) lecture example: theory conflict, lemma, backtrack | unsat |
| `learn_backtrack.smt2` | the lecture's exercise: theory conflict, learned clause, backtrack, a choice of unit clauses | unsat |
| `several_decisions.smt2` | 7 clauses of 3–4 literals: several decisions, two theory conflicts, two learned clauses | sat |
| `lia_simplex.smt2` | a Simplex conflict and its explanation | unsat |
| `lia_gcd.smt2` | `2x − 2y = 1`: GCD tightening | unsat |
| `lia_branch.smt2` | `2x + 3y = 1` in a box: branch and bound | unsat |
| `lia_sat.smt2` | scheduling with a disjunction | sat |
| `dt_intro.smt2` | DT introduction: `cons(x, nil) = cons(y, z)` gives `x = y` (injectivity), which contradicts `x = red ∨ x ≠ y` | unsat |
| `dt_colors.smt2` | finite datatype: tester splits | unsat |
| `dt_lists.smt2` | selectors, testers, model construction (lists of Int, so LIA + DT) | sat |
| `dt_cycle.smt2` | acyclicity, purification of a numeral (LIA + DT) | unsat |
| `no_lists.smt2` | Nelson–Oppen with decisions: DT derives `x = y`, two LIA conflicts, learned clauses | sat |
| `combo_injectivity.smt2` | Nelson–Oppen: DT derives `x = y` for LIA | unsat |
| `combo_purify.smt2` | purification of `head(l) = x + 1` | unsat |
| `nonconvex.smt2` | non-convex combination: the arrangement must be guessed | unsat |
| `combo_sat.smt2` | both theories, satisfiable | sat |

### Limits

- **Theory checks.** They run after every BCP round and DT rebuilds its closure each time. This is clear and robust but not tuned for large SMT problems.
- **No cuts.** LIA has no cutting planes and no bound tightening across rows, so branch and bound can need many splits on unbounded problems (it stops at 5 000).
- **Interface atoms.** Every pair of shared constants gets one, so problems with hundreds of shared constants get large.
- **Not tested on SMT-LIB benchmarks.** Correctness was tested on the examples, hand-made cases and 250 random LIA problems checked against brute force, with every model verified.

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
- **Trace consistency:** every trace from the tests above is replayed and checked:
  - every propagation's reason clause is really unit;
  - every conflict clause is really all-false;
  - every learned clause has exactly one conflict-level literal and the right backjump level;
  - every backjump undoes exactly the trail suffix.
- **Clause deletion:** 400 random instances plus pigeonhole files are solved with deletion forced after only 4–20 learned clauses, and the answers still match brute force. A traced run never deletes.
- **Limits:** the time limit, cancellation and the conflict limit each stop the solver with the right reason.

- **SMT** (`tests/smt_tests.rs`):
  - LIA: Simplex conflicts, GCD, branch and bound, Boolean structure, non-convex disequalities;
  - DT: clash, acyclicity, constructor exclusion, finite sorts, selectors and models;
  - the combination: Nelson–Oppen equality exchange, purification of mixed terms, non-convex arrangement guessing, shared variables through datatypes;
  - every example file, parse errors, the playground replay;
  - 250 random LIA problems with Boolean structure, checked against brute force.

  Every SMT trace is replayed by the same trace checker as SAT traces, including theory clauses and new variables. Every SAT model is verified against the original assertions.
- **Solver hook** (unit tests in `solver.rs`): a toy theory that propagates and conflicts through `TheoryHook`, and the playground `replay`.

Not yet tested on actual SAT Competition benchmark files. Timing used generated random 3-SAT with up to 250 variables and 1065 clauses.
