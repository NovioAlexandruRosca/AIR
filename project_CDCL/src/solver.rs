//! CDCL solver: DPLL search + two-watched-literal BCP + MOMS decisions +
//! First-UIP clause learning + non-chronological backjumping.
//!
//! The solver is also the SAT engine of CDCL(T): an optional [`TheoryHook`]
//! is consulted after every BCP fixpoint (partial check) and when all
//! problem clauses are satisfied (final check). The hook can propagate
//! literals, report conflicts, add clauses and ask for case splits; the
//! solver only ever sees clauses and literals, never theory terms.
//!
//! Data structures
//! - `clauses: Vec<Clause>`: originals first, then learned and theory
//!   clauses in creation order. A clause id is its index and never changes.
//! - `watches[lit]`: clauses watching `lit` (it is `lits[0]` or `lits[1]`),
//!   each with a blocker literal. The list is visited when `lit` becomes false.
//! - Per variable: `value`, `level`, `reason` (None = decision or unassigned).
//! - `trail`: assigned literals in assignment order; `trail_lim[d]` is the
//!   trail position where decision level `d + 1` starts.

use crate::dimacs::Cnf;
use crate::lit::Lit;
use crate::trace::{DecisionOrigin, Event, MomsCandidate, Tracer};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Instant;

/// The `k` in the MOMS score `(f(x) + f(¬x)) * 2^k + f(x) * f(¬x)`.
pub const MOMS_K: u32 = 1;
/// How many MOMS candidates a `Decide` event records.
const TRACED_CANDIDATES: usize = 8;
/// Consecutive hook rounds without any effect before giving up.
const MAX_IDLE_HOOK_ROUNDS: usize = 3;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Status {
    Sat,
    Unsat,
    /// Stopped before an answer; see `Solver::stop_reason`.
    Unknown,
}

impl Status {
    pub fn as_str(self) -> &'static str {
        match self {
            Status::Sat => "SAT",
            Status::Unsat => "UNSAT",
            Status::Unknown => "UNKNOWN",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StopReason {
    ConflictLimit,
    TimeLimit,
    Cancelled,
    /// A theory could not decide (e.g. branch-and-bound limit); see
    /// `Solver::incomplete_reason`.
    Incomplete,
}

impl StopReason {
    pub fn as_str(self) -> &'static str {
        match self {
            StopReason::ConflictLimit => "conflict limit",
            StopReason::TimeLimit => "time limit",
            StopReason::Cancelled => "cancelled",
            StopReason::Incomplete => "theory incomplete",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ClauseKind {
    /// Input clause (for SMT: Tseitin, purification and registration axioms).
    Original,
    /// Learned by conflict analysis.
    Learned,
    /// Permanent clause added during search (axioms for a new theory atom).
    Axiom,
    /// Theory lemma / explanation / conflict clause; deletable like learned.
    Theory,
}

#[derive(Debug, Clone)]
pub struct Clause {
    pub lits: Vec<Lit>,
    pub learnt: bool,
    pub kind: ClauseKind,
    /// Literal block distance: distinct decision levels among the literals
    /// when the clause was learned (0 for original clauses).
    pub lbd: u32,
    /// Removed by learned-clause database reduction; `lits` is then empty.
    pub deleted: bool,
}

#[derive(Debug, Clone, Default)]
pub struct Stats {
    pub decisions: u64,
    pub propagations: u64,
    pub conflicts: u64,
    pub learned: u64,
    pub deleted: u64,
    pub max_level: usize,
    pub theory_propagations: u64,
    pub theory_conflicts: u64,
    pub theory_splits: u64,
}

/// Learned clauses kept before the first database reduction.
pub const FIRST_REDUCE_AT: u64 = 8_000;

/// A clause produced by a theory, with a human-readable justification.
#[derive(Debug, Clone)]
pub struct TheoryClause {
    pub lits: Vec<Lit>,
    pub theory: String,
    pub why: String,
}

/// What a theory check asks the SAT solver to do.
#[derive(Debug, Clone, Default)]
pub struct TheoryResponse {
    /// Permanent clauses that are part of the problem (e.g. the definition
    /// of a freshly created atom). They count for MOMS and for "all
    /// problem clauses satisfied".
    pub axioms: Vec<TheoryClause>,
    /// Theory-valid clauses that may help pruning (deletable).
    pub lemmas: Vec<TheoryClause>,
    /// `lits[0]` is implied; the other literals are currently false and
    /// their negations are the explanation.
    pub propagations: Vec<TheoryClause>,
    /// Every literal is currently false: the negations are inconsistent.
    pub conflict: Option<TheoryClause>,
    /// Decide this literal next (splitting on demand). Only honoured on
    /// a final check.
    pub split: Option<(Lit, String, String)>,
    /// The theory cannot decide the current assignment.
    pub unknown: Option<String>,
}

/// The theory side of CDCL(T). The solver calls it; it never calls back
/// except through the `&mut Solver` it is handed.
pub trait TheoryHook {
    /// Called after BCP reaches a fixpoint (`final_check == false`) and when
    /// every problem clause is satisfied (`final_check == true`). On a final
    /// check an empty response means "the assignment is theory-consistent
    /// and complete": the formula is satisfiable.
    fn check(&mut self, sat: &mut Solver, final_check: bool) -> TheoryResponse;
    /// Everything above decision level `level` was unassigned; the trail
    /// now has `trail_len` literals.
    fn backjump(&mut self, level: usize, trail_len: usize);
}

/// Result of replaying user decisions in the playground.
#[derive(Debug, Clone)]
pub struct Replay {
    /// Number of decisions applied before stopping.
    pub applied: usize,
    /// Conflicting clause, if propagation ran into one.
    pub conflict: Option<usize>,
    /// Decisions that were skipped because their variable was already set
    /// (index into the decision list, and whether it agreed).
    pub skipped: Vec<(usize, bool)>,
    /// "open", "conflict", "sat", "split" or "unknown".
    pub outcome: &'static str,
    /// For "split": the literal and why the theory wants it decided.
    pub split: Option<(Lit, String, String)>,
    pub note: Option<String>,
    /// Index of the first trace event produced by "let the solver finish".
    pub finish_from: Option<usize>,
    /// For a conflict above level 0: the First-UIP clause CDCL would learn
    /// (not added; the playground keeps it when the user backtracks).
    pub learned: Option<Vec<Lit>>,
    /// For "units": several clauses are unit and force different literals;
    /// the user picks which to propagate first (clause id, forced literal).
    pub units: Vec<(usize, Lit)>,
}

/// One step of a playground replay: a decision, or the choice of which unit
/// clause to propagate when several are unit at once.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Action {
    Decide(Lit),
    /// Propagate this literal (it must be forced by one of the unit clauses).
    Pick(Lit),
}

/// Remove duplicate literals, keeping the first occurrence's position.
pub fn dedup_clause(lits: &[Lit]) -> Vec<Lit> {
    let mut out: Vec<Lit> = Vec::with_capacity(lits.len());
    for &l in lits {
        if !out.contains(&l) {
            out.push(l);
        }
    }
    out
}

/// True when every clause has at least one literal true under `model`
/// (`model[v]` is the value of variable `v`, 0-based).
pub fn verify_model(cnf: &Cnf, model: &[bool]) -> bool {
    cnf.clauses
        .iter()
        .all(|c| c.iter().any(|l| model[l.var()] == l.is_positive()))
}

fn lit_val(value: &[Option<bool>], l: Lit) -> Option<bool> {
    value[l.var()].map(|v| v == l.is_positive())
}

/// Number of unassigned literals if the clause is not satisfied, else None.
fn open_size(value: &[Option<bool>], lits: &[Lit]) -> Option<usize> {
    let mut n = 0;
    for &l in lits {
        match lit_val(value, l) {
            Some(true) => return None,
            None => n += 1,
            Some(false) => {}
        }
    }
    Some(n)
}

fn to_dimacs_sorted(lits: &[Lit]) -> Vec<i64> {
    let mut v: Vec<i64> = lits.iter().map(|l| l.to_dimacs()).collect();
    v.sort_by_key(|x| (x.unsigned_abs(), *x < 0));
    v
}

/// Binary resolution of `a` (contains ¬p) and `b` (contains p) on var(p).
fn resolve(a: &[Lit], b: &[Lit], p: Lit) -> Vec<Lit> {
    let mut out: Vec<Lit> = a.iter().copied().filter(|&l| l != !p).collect();
    for &l in b {
        if l != p && !out.contains(&l) {
            out.push(l);
        }
    }
    out
}

/// Watch-list entry. `blocker` is another literal of the clause: if it is
/// true the clause is satisfied and BCP skips it without reading the clause.
#[derive(Debug, Clone, Copy)]
struct Watch {
    cid: usize,
    blocker: Lit,
}

/// Outcome of BCP plus theory checks run to a fixpoint.
enum Fixpoint {
    Stable,
    Conflict(usize),
    Unknown(String),
}

/// Effect of applying one theory response.
enum Applied {
    Nothing,
    Progress,
    Conflict(usize),
    Split(Lit, String, String),
    Unknown(String),
}

/// Effect of adding one clause during search.
enum Added {
    Quiet,
    Unit,
    Conflict(usize),
}

pub struct Solver {
    num_vars: usize,
    num_original: usize,
    clauses: Vec<Clause>,
    /// Axiom clauses added during search; with the originals they form the
    /// problem MOMS looks at.
    extra_problem: Vec<usize>,
    watches: Vec<Vec<Watch>>,
    value: Vec<Option<bool>>,
    level: Vec<usize>,
    reason: Vec<Option<usize>>,
    trail: Vec<Lit>,
    trail_lim: Vec<usize>,
    qhead: usize,
    seen: Vec<bool>,
    moms_count: Vec<u32>,
    model: Vec<bool>,
    pub max_conflicts: Option<u64>,
    /// Give up (Unknown) once this instant has passed.
    pub deadline: Option<Instant>,
    /// Give up (Unknown) as soon as another thread sets this flag.
    pub cancel: Option<Arc<AtomicBool>>,
    /// Why the last `solve` returned Unknown.
    pub stop_reason: Option<StopReason>,
    /// Message from a theory that returned "unknown".
    pub incomplete_reason: Option<String>,
    /// Delete the worse half of the learned clauses whenever more than
    /// `max_learnts` are alive. The limit is raised in `solve` above anything
    /// a trace can record, so traces never contain a deletion.
    pub reduce_db: bool,
    pub max_learnts: u64,
    learnts_alive: u64,
    /// CDCL(T): the theory combination, if any.
    pub hook: Option<Box<dyn TheoryHook>>,
    /// Playground replay: unit clauses found by `propagate` are collected in
    /// `pending_units` instead of being propagated, so the user can choose.
    manual_units: bool,
    pending_units: Vec<(usize, Lit)>,
    pub stats: Stats,
    pub tracer: Tracer,
}

impl Solver {
    pub fn new(cnf: &Cnf) -> Solver {
        Solver::with_tracer(cnf, Tracer::disabled())
    }

    pub fn with_tracer(cnf: &Cnf, tracer: Tracer) -> Solver {
        let n = cnf.num_vars;
        let mut s = Solver {
            num_vars: n,
            num_original: cnf.clauses.len(),
            clauses: Vec::with_capacity(cnf.clauses.len()),
            extra_problem: Vec::new(),
            watches: vec![Vec::new(); 2 * n],
            value: vec![None; n],
            level: vec![0; n],
            reason: vec![None; n],
            trail: Vec::with_capacity(n),
            trail_lim: Vec::new(),
            qhead: 0,
            seen: vec![false; n],
            moms_count: vec![0; 2 * n],
            model: Vec::new(),
            max_conflicts: None,
            deadline: None,
            cancel: None,
            stop_reason: None,
            incomplete_reason: None,
            reduce_db: true,
            max_learnts: FIRST_REDUCE_AT,
            learnts_alive: 0,
            hook: None,
            manual_units: false,
            pending_units: Vec::new(),
            stats: Stats::default(),
            tracer,
        };
        for c in &cnf.clauses {
            let lits = dedup_clause(c);
            let id = s.clauses.len();
            if lits.len() >= 2 {
                s.watches[lits[0].index()].push(Watch {
                    cid: id,
                    blocker: lits[1],
                });
                s.watches[lits[1].index()].push(Watch {
                    cid: id,
                    blocker: lits[0],
                });
            }
            s.clauses.push(Clause {
                lits,
                learnt: false,
                kind: ClauseKind::Original,
                lbd: 0,
                deleted: false,
            });
        }
        s
    }

    pub fn num_vars(&self) -> usize {
        self.num_vars
    }

    pub fn num_original(&self) -> usize {
        self.num_original
    }

    pub fn clauses(&self) -> &[Clause] {
        &self.clauses
    }

    /// Assigned literals in assignment order.
    pub fn trail(&self) -> &[Lit] {
        &self.trail
    }

    /// Decision level at which `var` was assigned (meaningless if unassigned).
    pub fn var_level(&self, var: usize) -> usize {
        self.level[var]
    }

    /// Reason clause of an assigned variable (None for decisions).
    pub fn var_reason(&self, var: usize) -> Option<usize> {
        self.reason[var]
    }

    pub fn value(&self, l: Lit) -> Option<bool> {
        lit_val(&self.value, l)
    }

    /// Create a fresh Boolean variable (used for atoms made during search).
    pub fn new_var(&mut self) -> usize {
        let v = self.num_vars;
        self.num_vars += 1;
        self.value.push(None);
        self.level.push(0);
        self.reason.push(None);
        self.seen.push(false);
        self.moms_count.extend([0, 0]);
        self.watches.push(Vec::new());
        self.watches.push(Vec::new());
        v
    }

    /// Model as DIMACS literals (free variables are reported false).
    pub fn model_dimacs(&self) -> Vec<i64> {
        self.model
            .iter()
            .enumerate()
            .map(|(v, &b)| Lit::new(v, b).to_dimacs())
            .collect()
    }

    pub fn model(&self) -> &[bool] {
        &self.model
    }

    pub fn decision_level(&self) -> usize {
        self.trail_lim.len()
    }

    pub(crate) fn lit_value(&self, l: Lit) -> Option<bool> {
        lit_val(&self.value, l)
    }

    /// Unit and empty input clauses are handled at level 0 up front.
    /// Returns the conflicting clause, if any.
    fn load_units(&mut self) -> Option<usize> {
        for cid in 0..self.num_original {
            match self.clauses[cid].lits.len() {
                0 => return Some(cid),
                1 => {
                    let l = self.clauses[cid].lits[0];
                    match self.lit_value(l) {
                        Some(true) => {}
                        Some(false) => return Some(cid),
                        // manual units: the input's unit clauses wait too
                        None if self.manual_units => {
                            if !self.pending_units.iter().any(|&(c, _)| c == cid) {
                                self.pending_units.push((cid, l));
                            }
                        }
                        None => self.enqueue(l, Some(cid)),
                    }
                }
                _ => {}
            }
        }
        None
    }

    pub fn solve(&mut self) -> Status {
        // Every learned clause costs at least 3 events (Conflict, Learn,
        // Backjump), so no reduction can happen while a trace is recorded.
        if self.tracer.enabled {
            self.max_learnts = self.max_learnts.max(self.tracer.limit as u64 / 3 + 1);
        }
        if let Some(cid) = self.load_units() {
            if !self.clauses[cid].lits.is_empty() {
                self.stats.conflicts += 1;
            }
            self.tracer.push(|| Event::Conflict {
                clause: cid,
                level: 0,
            });
            return self.finish(Status::Unsat);
        }

        let mut idle_final_rounds = 0;
        loop {
            if let Some(reason) = self.external_stop() {
                self.stop_reason = Some(reason);
                return self.finish(Status::Unknown);
            }
            match self.fixpoint() {
                Fixpoint::Conflict(confl) => {
                    if let Some(status) = self.on_conflict(confl) {
                        return self.finish(status);
                    }
                    continue;
                }
                Fixpoint::Unknown(msg) => return self.give_up(msg),
                Fixpoint::Stable => {}
            }

            let decision = match self.pick_branch() {
                Some((lit, min_size, candidates)) => (lit, min_size, candidates, None),
                None => {
                    if self.hook.is_none() {
                        return self.finish(Status::Sat);
                    }
                    match self.call_hook(true) {
                        Applied::Nothing => return self.finish(Status::Sat),
                        Applied::Progress => {
                            idle_final_rounds = 0;
                            continue;
                        }
                        Applied::Conflict(confl) => {
                            if let Some(status) = self.on_conflict(confl) {
                                return self.finish(status);
                            }
                            continue;
                        }
                        Applied::Unknown(msg) => return self.give_up(msg),
                        Applied::Split(lit, by, why) => {
                            if self.lit_value(lit).is_some() {
                                // Already decided: the theory will see it next round.
                                idle_final_rounds += 1;
                                if idle_final_rounds > MAX_IDLE_HOOK_ROUNDS {
                                    return self.give_up(format!(
                                        "{by} asked to split on an assigned literal"
                                    ));
                                }
                                continue;
                            }
                            self.stats.theory_splits += 1;
                            (lit, 0, Vec::new(), Some(DecisionOrigin { by, why }))
                        }
                    }
                }
            };
            idle_final_rounds = 0;
            let (lit, min_size, candidates, origin) = decision;
            self.decide_traced(lit, min_size, candidates, origin);
        }
    }

    fn decide_traced(
        &mut self,
        lit: Lit,
        min_size: usize,
        candidates: Vec<MomsCandidate>,
        origin: Option<DecisionOrigin>,
    ) {
        self.stats.decisions += 1;
        self.trail_lim.push(self.trail.len());
        let level = self.decision_level();
        self.stats.max_level = self.stats.max_level.max(level);
        self.tracer.push(|| Event::Decide {
            lit: lit.to_dimacs(),
            level,
            min_size,
            candidates,
            origin,
        });
        self.enqueue(lit, None);
    }

    fn give_up(&mut self, msg: String) -> Status {
        self.stop_reason = Some(StopReason::Incomplete);
        self.incomplete_reason = Some(msg);
        self.finish(Status::Unknown)
    }

    /// Handle a falsified clause: record it, learn and backjump. Returns a
    /// final status when the conflict settles the problem.
    fn on_conflict(&mut self, confl: usize) -> Option<Status> {
        self.stats.conflicts += 1;
        // Theory clauses may be falsified entirely below the current level.
        let max_level = self.clauses[confl]
            .lits
            .iter()
            .map(|l| self.level[l.var()])
            .max()
            .unwrap_or(0);
        if max_level < self.decision_level() {
            self.backjump(max_level);
        }
        let level = self.decision_level();
        self.tracer.push(|| Event::Conflict {
            clause: confl,
            level,
        });
        if level == 0 {
            return Some(Status::Unsat);
        }
        if self.max_conflicts.is_some_and(|m| self.stats.conflicts > m) {
            self.stop_reason = Some(StopReason::ConflictLimit);
            return Some(Status::Unknown);
        }
        self.learn_and_backjump(confl);
        if self.reduce_db && self.learnts_alive > self.max_learnts {
            self.reduce_db();
            self.max_learnts += self.max_learnts / 10;
        }
        None
    }

    /// BCP, then partial theory checks, until nothing changes.
    fn fixpoint(&mut self) -> Fixpoint {
        let mut idle = 0;
        loop {
            if let Some(confl) = self.propagate() {
                return Fixpoint::Conflict(confl);
            }
            // Manual units: Boolean propagation is not finished while unit
            // clauses wait for the user, so the theories are not asked yet.
            if self.manual_units {
                self.refresh_pending_units();
                if !self.pending_units.is_empty() {
                    return Fixpoint::Stable;
                }
            }
            if self.hook.is_none() {
                return Fixpoint::Stable;
            }
            match self.call_hook(false) {
                Applied::Conflict(confl) => return Fixpoint::Conflict(confl),
                Applied::Unknown(msg) => return Fixpoint::Unknown(msg),
                Applied::Progress => idle = 0,
                Applied::Nothing | Applied::Split(..) => {
                    idle += 1;
                    if self.qhead == self.trail.len() || idle > MAX_IDLE_HOOK_ROUNDS {
                        return Fixpoint::Stable;
                    }
                }
            }
        }
    }

    /// Run the theory hook once and apply its response.
    fn call_hook(&mut self, final_check: bool) -> Applied {
        let mut hook = match self.hook.take() {
            Some(h) => h,
            None => return Applied::Nothing,
        };
        let resp = hook.check(self, final_check);
        self.hook = Some(hook);

        let before = self.trail.len();
        for tc in resp.axioms {
            if let Added::Conflict(c) =
                self.add_clause_during_search(tc, ClauseKind::Axiom, "axiom")
            {
                return Applied::Conflict(c);
            }
        }
        for tc in resp.lemmas {
            if let Added::Conflict(c) =
                self.add_clause_during_search(tc, ClauseKind::Theory, "lemma")
            {
                return Applied::Conflict(c);
            }
        }
        if let Some(tc) = resp.conflict {
            self.stats.theory_conflicts += 1;
            match self.add_clause_during_search(tc, ClauseKind::Theory, "conflict") {
                Added::Conflict(c) => return Applied::Conflict(c),
                // A "conflict" that is not falsified (stale): just keep the lemma.
                Added::Unit | Added::Quiet => {}
            }
        }
        for tc in resp.propagations {
            let implied = match tc.lits.first() {
                Some(&l) => l,
                None => continue,
            };
            if self.lit_value(implied) == Some(true) {
                continue;
            }
            match self.add_clause_during_search(tc, ClauseKind::Theory, "explanation") {
                Added::Conflict(c) => return Applied::Conflict(c),
                Added::Unit => self.stats.theory_propagations += 1,
                Added::Quiet => {}
            }
        }
        if let Some(msg) = resp.unknown {
            return Applied::Unknown(msg);
        }
        if self.trail.len() > before {
            return Applied::Progress;
        }
        if let Some((lit, by, why)) = resp.split {
            return Applied::Split(lit, by, why);
        }
        Applied::Nothing
    }

    /// Add a clause in the middle of search, choosing watches so that the
    /// 2WL invariant holds for the current assignment. Unit clauses are
    /// asserted at level 0 (after backjumping there) so they are never lost.
    fn add_clause_during_search(
        &mut self,
        tc: TheoryClause,
        kind: ClauseKind,
        kind_name: &'static str,
    ) -> Added {
        let mut lits = dedup_clause(&tc.lits);
        if lits.iter().any(|&l| lits.contains(&!l)) {
            return Added::Quiet; // tautology
        }
        // True literals first, then unassigned, then false by decreasing level.
        lits.sort_by_key(|&l| match self.lit_value(l) {
            Some(true) => (0, 0),
            None => (1, 0),
            Some(false) => (2, usize::MAX - self.level[l.var()]),
        });
        if lits.len() == 1 && self.lit_value(lits[0]) != Some(true) && self.decision_level() > 0 {
            self.backjump(0);
        }

        let id = self.clauses.len();
        let learnt = kind == ClauseKind::Theory;
        if lits.len() >= 2 {
            self.watches[lits[0].index()].push(Watch {
                cid: id,
                blocker: lits[1],
            });
            self.watches[lits[1].index()].push(Watch {
                cid: id,
                blocker: lits[0],
            });
        }
        let trace_lits = to_dimacs_sorted(&lits);
        self.tracer.push(|| Event::TheoryClause {
            clause: id,
            lits: trace_lits,
            kind: kind_name,
            theory: tc.theory.clone(),
            why: tc.why.clone(),
        });
        let first = lits.first().copied();
        let second = lits.get(1).copied();
        self.clauses.push(Clause {
            lits,
            learnt,
            kind,
            lbd: 0,
            deleted: false,
        });
        if kind == ClauseKind::Axiom {
            self.extra_problem.push(id);
        }
        if learnt {
            self.learnts_alive += 1;
        }

        let Some(first) = first else {
            return Added::Conflict(id); // empty clause
        };
        match self.lit_value(first) {
            Some(true) => Added::Quiet,
            Some(false) => Added::Conflict(id),
            None => {
                let unit = match second {
                    None => true,
                    Some(s) => self.lit_value(s) == Some(false),
                };
                if unit {
                    self.enqueue(first, Some(id));
                    Added::Unit
                } else {
                    Added::Quiet
                }
            }
        }
    }

    /// Time limit or cancellation. Checked once per search iteration (one
    /// BCP round plus one decision or conflict), which is cheap next to MOMS.
    fn external_stop(&self) -> Option<StopReason> {
        if self
            .cancel
            .as_ref()
            .is_some_and(|c| c.load(Ordering::Relaxed))
        {
            return Some(StopReason::Cancelled);
        }
        if self.deadline.is_some_and(|d| Instant::now() >= d) {
            return Some(StopReason::TimeLimit);
        }
        None
    }

    fn finish(&mut self, status: Status) -> Status {
        if status == Status::Sat {
            self.model = self.value.iter().map(|v| v.unwrap_or(false)).collect();
            // Problem clauses must hold; learned and theory clauses are only
            // implied (by the problem, or by the theories) and may not.
            debug_assert!(self
                .clauses
                .iter()
                .filter(|c| !c.learnt && !c.deleted)
                .all(|c| c
                    .lits
                    .iter()
                    .any(|l| self.model[l.var()] == l.is_positive())));
        }
        let model = if status == Status::Sat {
            self.model_dimacs()
        } else {
            Vec::new()
        };
        // The result is recorded even when the trace was truncated.
        self.tracer.enabled = self.tracer.enabled || self.tracer.truncated;
        self.tracer.limit = self.tracer.limit.max(self.tracer.events.len() + 1);
        self.tracer.push(|| Event::Result {
            status: status.as_str(),
            model,
        });
        status
    }

    pub(crate) fn enqueue(&mut self, lit: Lit, reason: Option<usize>) {
        let v = lit.var();
        let level = self.decision_level();
        self.value[v] = Some(lit.is_positive());
        self.level[v] = level;
        self.reason[v] = reason;
        self.trail.push(lit);
        if let Some(r) = reason {
            self.stats.propagations += 1;
            self.tracer.push(|| Event::Propagate {
                lit: lit.to_dimacs(),
                reason: r,
                level,
            });
        }
    }

    /// Open a new decision level and assign `lit` (used by tests).
    #[cfg(test)]
    pub(crate) fn decide(&mut self, lit: Lit) {
        self.trail_lim.push(self.trail.len());
        self.enqueue(lit, None);
    }

    /// Playground: apply `decisions` in order, propagating (BCP + theory)
    /// after each one, and stop at the first conflict. No learning, no
    /// backjumping: the user sees exactly what their choices imply. When
    /// every problem clause ends up satisfied, the theories' final check is
    /// run once and its verdict reported.
    /// Unit clauses still waiting (manual units): drop those that are no
    /// longer unit (satisfied, or undone by a backjump).
    fn refresh_pending_units(&mut self) {
        let mut pending = std::mem::take(&mut self.pending_units);
        pending.retain(|&(cid, l)| {
            let c = &self.clauses[cid];
            // a falsified one-literal clause stays: it is a conflict
            if c.lits.len() == 1 && self.lit_value(l) == Some(false) {
                return true;
            }
            !c.deleted
                && self.lit_value(l).is_none()
                && c.lits
                    .iter()
                    .all(|&m| m == l || self.lit_value(m) == Some(false))
        });
        self.pending_units = pending;
    }

    /// Propagate every waiting unit clause and go back to automatic
    /// propagation (before "let the solver finish").
    pub fn flush_pending_units(&mut self) {
        self.manual_units = false;
        self.refresh_pending_units();
        for (cid, l) in std::mem::take(&mut self.pending_units) {
            if self.lit_value(l).is_none() {
                self.enqueue(l, Some(cid));
            }
        }
    }

    /// Replay decisions with automatic unit propagation (see `replay_actions`).
    pub fn replay(&mut self, decisions: &[Lit]) -> Replay {
        let actions: Vec<Action> = decisions.iter().map(|&d| Action::Decide(d)).collect();
        self.replay_actions(&actions, false, &|_| true)
    }

    /// Replay the playground's actions. With `manual`, whenever several unit
    /// clauses force different literals that `choosable` accepts, the replay
    /// stops ("units") unless the next action picks one of them. Units on
    /// other literals (internal helper atoms) are propagated right away.
    pub fn replay_actions(
        &mut self,
        actions: &[Action],
        manual: bool,
        choosable: &dyn Fn(Lit) -> bool,
    ) -> Replay {
        let mut r = Replay {
            applied: 0,
            conflict: None,
            skipped: Vec::new(),
            outcome: "open",
            split: None,
            note: None,
            finish_from: None,
            learned: None,
            units: Vec::new(),
        };
        self.manual_units = manual;
        if let Some(cid) = self.load_units() {
            self.tracer.push(|| Event::Conflict {
                clause: cid,
                level: 0,
            });
            r.conflict = Some(cid);
            r.outcome = "conflict";
            return r;
        }
        let mut next = 0usize;
        let check = |s: &mut Solver, r: &mut Replay, next: &mut usize| -> bool {
            loop {
                match s.fixpoint() {
                    Fixpoint::Conflict(cid) => {
                        let level = s.decision_level();
                        s.tracer.push(|| Event::Conflict { clause: cid, level });
                        r.conflict = Some(cid);
                        r.outcome = "conflict";
                        // What CDCL would learn: analysis needs a literal of the
                        // conflict clause at the current level.
                        if level > 0
                            && s.clauses[cid]
                                .lits
                                .iter()
                                .any(|l| s.level[l.var()] == level)
                        {
                            let tracing = s.tracer.enabled;
                            s.tracer.enabled = false;
                            let (lits, _, _) = s.analyze(cid);
                            s.tracer.enabled = tracing;
                            r.learned = Some(lits);
                        }
                        return false;
                    }
                    Fixpoint::Unknown(msg) => {
                        r.outcome = "unknown";
                        r.note = Some(msg);
                        return false;
                    }
                    Fixpoint::Stable => {}
                }
                // A waiting one-literal clause whose literal became false
                // (another unit clause forced the opposite): a conflict.
                if let Some(&(cid, _)) = s
                    .pending_units
                    .iter()
                    .find(|&&(c, l)| s.clauses[c].lits.len() == 1 && s.lit_value(l) == Some(false))
                {
                    let level = s.decision_level();
                    s.tracer.push(|| Event::Conflict { clause: cid, level });
                    r.conflict = Some(cid);
                    r.outcome = "conflict";
                    return false;
                }
                s.refresh_pending_units();
                if s.pending_units.is_empty() {
                    return true;
                }
                // Internal helper atoms, or one literal forced by every unit
                // clause: nothing to choose.
                let mut lits: Vec<Lit> = Vec::new();
                for &(_, l) in &s.pending_units {
                    if !lits.contains(&l) {
                        lits.push(l);
                    }
                }
                let auto = s
                    .pending_units
                    .iter()
                    .copied()
                    .find(|&(_, l)| !choosable(l))
                    .or_else(|| (lits.len() == 1).then(|| s.pending_units[0]));
                if let Some((cid, l)) = auto {
                    s.enqueue(l, Some(cid));
                    continue;
                }
                match actions.get(*next) {
                    Some(&Action::Pick(p)) => {
                        *next += 1;
                        if let Some(&(cid, l)) = s.pending_units.iter().find(|&&(_, l)| l == p) {
                            s.enqueue(l, Some(cid));
                        }
                    }
                    _ => {
                        r.outcome = "units";
                        r.units = s.pending_units.clone();
                        return false;
                    }
                }
            }
        };
        if !check(self, &mut r, &mut next) {
            return r;
        }
        // Decisions on atoms that a theory only creates later (e.g. a split
        // atom made by the final check) wait until the atom exists.
        let mut deferred: Vec<(usize, Lit)> = Vec::new();
        let decide_user = |s: &mut Solver, d: Lit| {
            s.decide_traced(
                d,
                0,
                Vec::new(),
                Some(DecisionOrigin {
                    by: "user".into(),
                    why: "chosen in the playground".into(),
                }),
            );
        };
        while next < actions.len() {
            let i = next;
            next += 1;
            // a pick that no choice point asked for is out of date: ignore it
            let Action::Decide(d) = actions[i] else {
                continue;
            };
            if d.var() >= self.num_vars {
                deferred.push((i, d));
                continue;
            }
            if let Some(v) = self.lit_value(d) {
                r.skipped.push((i, v));
                continue;
            }
            decide_user(self, d);
            r.applied = i + 1;
            if !check(self, &mut r, &mut next) {
                return r;
            }
        }
        loop {
            // Apply deferred decisions whose atom exists by now.
            if let Some(pos) = deferred.iter().position(|(_, d)| d.var() < self.num_vars) {
                let (i, d) = deferred.remove(pos);
                if let Some(v) = self.lit_value(d) {
                    r.skipped.push((i, v));
                } else {
                    decide_user(self, d);
                    r.applied = r.applied.max(i + 1);
                    if !check(self, &mut r, &mut next) {
                        return r;
                    }
                }
                continue;
            }
            // All problem clauses satisfied? Then ask the theories for a verdict.
            let open = self
                .problem_clause_ids()
                .any(|id| open_size(&self.value, &self.clauses[id].lits).is_some());
            if open {
                r.outcome = "open";
                break;
            }
            if self.hook.is_none() {
                r.outcome = "sat";
                break;
            }
            match self.call_hook(true) {
                Applied::Nothing => {
                    r.outcome = "sat";
                    break;
                }
                Applied::Split(lit, by, why) => {
                    if deferred.iter().any(|(_, d)| d.var() == lit.var()) {
                        continue; // the user already chose this split
                    }
                    r.outcome = "split";
                    r.split = Some((lit, by, why));
                    break;
                }
                Applied::Conflict(cid) => {
                    let level = self.decision_level();
                    self.tracer.push(|| Event::Conflict { clause: cid, level });
                    r.conflict = Some(cid);
                    r.outcome = "conflict";
                    break;
                }
                Applied::Progress => {
                    if !check(self, &mut r, &mut next) {
                        return r;
                    }
                }
                Applied::Unknown(msg) => {
                    r.outcome = "unknown";
                    r.note = Some(msg);
                    break;
                }
            }
        }
        for (i, _) in deferred {
            r.skipped.push((i, false));
        }
        r
    }

    fn problem_clause_ids(&self) -> impl Iterator<Item = usize> + '_ {
        (0..self.num_original).chain(self.extra_problem.iter().copied())
    }

    /// Unit propagation with two watched literals. Returns a conflicting
    /// clause id, or None when the queue is exhausted without conflict.
    pub(crate) fn propagate(&mut self) -> Option<usize> {
        while self.qhead < self.trail.len() {
            let p = self.trail[self.qhead];
            self.qhead += 1;
            let false_lit = !p;
            let mut ws = std::mem::take(&mut self.watches[false_lit.index()]);
            let (mut i, mut j) = (0, 0);
            let mut conflict = None;

            while i < ws.len() {
                let w = ws[i];
                i += 1;
                // Clause already satisfied by its blocker: skip without reading it.
                if lit_val(&self.value, w.blocker) == Some(true) {
                    ws[j] = w;
                    j += 1;
                    continue;
                }
                let cid = w.cid;
                let lits = &mut self.clauses[cid].lits;
                // Keep the falsified watch at position 1.
                if lits[0] == false_lit {
                    lits.swap(0, 1);
                }
                let first = lits[0];
                let kept = Watch {
                    cid,
                    blocker: first,
                };
                if lit_val(&self.value, first) == Some(true) {
                    ws[j] = kept;
                    j += 1;
                    continue;
                }
                // Look for a non-false literal to watch instead.
                let mut moved = false;
                for k in 2..lits.len() {
                    if lit_val(&self.value, lits[k]) != Some(false) {
                        lits.swap(1, k);
                        self.watches[lits[1].index()].push(kept);
                        moved = true;
                        break;
                    }
                }
                if moved {
                    continue;
                }
                // No replacement: the clause is unit or conflicting.
                ws[j] = kept;
                j += 1;
                if lit_val(&self.value, first) == Some(false) {
                    conflict = Some(cid);
                    while i < ws.len() {
                        ws[j] = ws[i];
                        j += 1;
                        i += 1;
                    }
                } else if self.manual_units {
                    if !self.pending_units.iter().any(|&(c, _)| c == cid) {
                        self.pending_units.push((cid, first));
                    }
                } else {
                    self.enqueue(first, Some(cid));
                }
            }

            ws.truncate(j);
            debug_assert!(self.watches[false_lit.index()].is_empty());
            self.watches[false_lit.index()] = ws;
            if conflict.is_some() {
                return conflict;
            }
        }
        None
    }

    /// MOMS: among unsatisfied clauses of minimum open size, pick the
    /// variable maximising `(f(x)+f(¬x)) * 2^k + f(x)*f(¬x)`; ties go to the
    /// lowest variable index, polarity to the more frequent literal.
    /// Only problem clauses (originals and axioms) are scored: learned and
    /// theory clauses are implied by them, and rescanning tens of thousands
    /// of learned clauses at every decision made the solver quadratic.
    /// Returns None when every problem clause is satisfied.
    fn pick_branch(&mut self) -> Option<(Lit, usize, Vec<MomsCandidate>)> {
        let min_size = self
            .problem_clause_ids()
            .filter_map(|id| open_size(&self.value, &self.clauses[id].lits))
            .min()?;
        debug_assert!(min_size >= 2, "BCP left a unit or empty clause");

        self.moms_count.fill(0);
        let ids: Vec<usize> = self.problem_clause_ids().collect();
        for id in ids {
            let c = &self.clauses[id];
            if open_size(&self.value, &c.lits) == Some(min_size) {
                for &l in &c.lits {
                    if lit_val(&self.value, l).is_none() {
                        self.moms_count[l.index()] += 1;
                    }
                }
            }
        }

        let score_of = |v: usize, counts: &[u32]| {
            let p = counts[Lit::new(v, true).index()];
            let n = counts[Lit::new(v, false).index()];
            let s = ((p + n) as u64) << MOMS_K;
            (p, n, s + p as u64 * n as u64)
        };

        let mut best: Option<(usize, u64)> = None;
        for v in 0..self.num_vars {
            let (p, n, s) = score_of(v, &self.moms_count);
            if p + n > 0 && best.is_none_or(|(_, bs)| s > bs) {
                best = Some((v, s));
            }
        }
        let (v, _) = best.expect("an open clause has an unassigned literal");
        let (p, n, _) = score_of(v, &self.moms_count);
        let lit = Lit::new(v, p >= n);

        let mut candidates = Vec::new();
        if self.tracer.enabled {
            for u in 0..self.num_vars {
                let (p, n, s) = score_of(u, &self.moms_count);
                if p + n > 0 {
                    candidates.push(MomsCandidate {
                        var: u + 1,
                        pos: p,
                        neg: n,
                        score: s,
                    });
                }
            }
            candidates.sort_by(|a, b| b.score.cmp(&a.score).then(a.var.cmp(&b.var)));
            candidates.truncate(TRACED_CANDIDATES);
        }
        Some((lit, min_size, candidates))
    }

    /// First-UIP conflict analysis. Returns the learned clause with the
    /// asserting literal at index 0 and the highest-level remaining literal
    /// at index 1, the backjump level, and the resolved-away variables
    /// (1-based, the conflict side of the cut).
    pub(crate) fn analyze(&mut self, confl: usize) -> (Vec<Lit>, usize, Vec<usize>) {
        let cur = self.decision_level();
        let tracing = self.tracer.enabled;
        let mut lower: Vec<Lit> = Vec::new();
        let mut counter = 0usize;
        let mut conflict_side = Vec::new();
        let mut resolvent: Vec<Lit> = if tracing {
            self.clauses[confl].lits.clone()
        } else {
            Vec::new()
        };
        let mut first_step = true;

        let mut clause = confl;
        let mut skip: Option<Lit> = None;
        let mut idx = self.trail.len();
        let uip: Lit;
        loop {
            for k in 0..self.clauses[clause].lits.len() {
                let l = self.clauses[clause].lits[k];
                if Some(l) == skip {
                    continue;
                }
                let v = l.var();
                if !self.seen[v] {
                    self.seen[v] = true;
                    if self.level[v] == cur {
                        counter += 1;
                    } else {
                        lower.push(l);
                    }
                }
            }

            // Most recently assigned marked literal (always at level `cur`).
            loop {
                idx -= 1;
                if self.seen[self.trail[idx].var()] {
                    break;
                }
            }
            let p = self.trail[idx];
            self.seen[p.var()] = false;
            counter -= 1;
            if counter == 0 {
                uip = p;
                break;
            }

            let r = self.reason[p.var()].expect("non-UIP literal at the conflict level is implied");
            if tracing {
                let next = resolve(&resolvent, &self.clauses[r].lits, p);
                let (a, a_id) = (to_dimacs_sorted(&resolvent), first_step.then_some(confl));
                let res = to_dimacs_sorted(&next);
                self.tracer.push(|| Event::Resolve {
                    clause_a: a,
                    clause_a_id: a_id,
                    clause_b: r,
                    pivot: p.var() + 1,
                    resolvent: res,
                });
                resolvent = next;
            }
            first_step = false;
            conflict_side.push(p.var() + 1);
            clause = r;
            skip = Some(p);
        }

        let mut lits = Vec::with_capacity(lower.len() + 1);
        lits.push(!uip);
        lits.extend(lower);
        for l in &lits[1..] {
            self.seen[l.var()] = false;
        }
        if tracing {
            debug_assert_eq!(to_dimacs_sorted(&resolvent), to_dimacs_sorted(&lits));
        }

        let mut bt = 0;
        let mut max_i = 1;
        for (i, l) in lits.iter().enumerate().skip(1) {
            if self.level[l.var()] > bt {
                bt = self.level[l.var()];
                max_i = i;
            }
        }
        if lits.len() > 1 {
            lits.swap(1, max_i);
        }
        (lits, bt, conflict_side)
    }

    fn learn_and_backjump(&mut self, confl: usize) {
        let (lits, bt, conflict_side) = self.analyze(confl);
        let id = self.clauses.len();
        self.stats.learned += 1;
        self.tracer.push(|| Event::Learn {
            clause: id,
            lits: to_dimacs_sorted(&lits),
            uip: (!lits[0]).to_dimacs(),
            conflict_side,
            reason_side: lits.iter().map(|l| l.var() + 1).collect(),
            backjump_level: bt,
        });
        let mut levels: Vec<usize> = lits.iter().map(|l| self.level[l.var()]).collect();
        levels.sort_unstable();
        levels.dedup();
        self.backjump(bt);
        if lits.len() >= 2 {
            self.watches[lits[0].index()].push(Watch {
                cid: id,
                blocker: lits[1],
            });
            self.watches[lits[1].index()].push(Watch {
                cid: id,
                blocker: lits[0],
            });
        }
        let asserting = lits[0];
        self.clauses.push(Clause {
            lits,
            learnt: true,
            kind: ClauseKind::Learned,
            lbd: levels.len() as u32,
            deleted: false,
        });
        self.learnts_alive += 1;
        self.enqueue(asserting, Some(id));
    }

    /// A clause is locked while it is the reason of a current assignment
    /// (its implied literal is always `lits[0]`).
    fn is_locked(&self, id: usize) -> bool {
        let c = &self.clauses[id];
        !c.lits.is_empty() && self.reason[c.lits[0].var()] == Some(id)
    }

    /// Delete the worse half of the unlocked learned clauses: highest LBD
    /// first, then longest. "Glue" clauses (LBD ≤ 2) are always kept.
    /// Clause ids stay valid; deleted clauses just become empty.
    fn reduce_db(&mut self) {
        let mut candidates: Vec<usize> = (self.num_original..self.clauses.len())
            .filter(|&id| {
                let c = &self.clauses[id];
                c.learnt
                    && !c.deleted
                    && (c.lbd > 2 || c.kind == ClauseKind::Theory)
                    && !self.is_locked(id)
            })
            .collect();
        candidates.sort_by_key(|&id| {
            let c = &self.clauses[id];
            (std::cmp::Reverse(c.lbd), std::cmp::Reverse(c.lits.len()))
        });
        let remove = candidates.len() / 2;
        for &id in &candidates[..remove] {
            let c = &mut self.clauses[id];
            c.deleted = true;
            c.lits = Vec::new();
        }
        let clauses = &self.clauses;
        for ws in self.watches.iter_mut() {
            ws.retain(|w| !clauses[w.cid].deleted);
        }
        self.learnts_alive -= remove as u64;
        self.stats.deleted += remove as u64;
    }

    pub(crate) fn backjump(&mut self, to: usize) {
        let from = self.decision_level();
        if from <= to {
            return;
        }
        let start = self.trail_lim[to];
        for &l in &self.trail[start..] {
            self.value[l.var()] = None;
            self.reason[l.var()] = None;
        }
        let unassigned: Vec<Lit> = self.trail.drain(start..).collect();
        self.trail_lim.truncate(to);
        self.qhead = start;
        let trail_len = self.trail.len();
        if let Some(h) = self.hook.as_mut() {
            h.backjump(to, trail_len);
        }
        self.tracer.push(|| Event::Backjump {
            from,
            to,
            unassigned: unassigned.iter().map(|l| l.to_dimacs()).collect(),
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dimacs::parse;

    fn lit(x: i64) -> Lit {
        Lit::from_dimacs(x)
    }

    fn sorted(lits: &[Lit]) -> Vec<i64> {
        to_dimacs_sorted(lits)
    }

    #[test]
    fn bcp_records_reasons_and_levels() {
        // C1: ¬1 ∨ 2, C2: ¬2 ∨ 3, C3: ¬3 ∨ ¬1 ∨ 4
        let cnf = parse("p cnf 4 3\n-1 2 0\n-2 3 0\n-3 -1 4 0\n").unwrap();
        let mut s = Solver::new(&cnf);
        s.decide(lit(1));
        assert_eq!(s.propagate(), None);
        assert_eq!(s.trail, vec![lit(1), lit(2), lit(3), lit(4)]);
        assert_eq!(s.reason[0], None);
        assert_eq!(s.reason[1], Some(0));
        assert_eq!(s.reason[2], Some(1));
        assert_eq!(s.reason[3], Some(2));
        assert!(s.level.iter().all(|&l| l == 1));
    }

    #[test]
    fn bcp_detects_conflict() {
        let cnf = parse("p cnf 2 3\n-1 2 0\n-1 -2 0\n1 2 0\n").unwrap();
        let mut s = Solver::new(&cnf);
        s.decide(lit(1));
        assert_eq!(s.propagate(), Some(1));
    }

    /// Hand-checked First-UIP example:
    ///   C1: ¬1 ∨ 6        C2: ¬6 ∨ 2       C3: ¬6 ∨ 3 ∨ 5
    ///   C4: ¬2 ∨ 4        C5: ¬3 ∨ ¬4      C6: 7 ∨ 8
    /// Decisions: ¬5 @1, 7 @2, 1 @3.
    /// Level 3: 1 → 6 (C1) → 2 (C2), 3 (C3, needs ¬5) ; 2 → 4 (C4) ; C5 conflicts.
    /// Resolution: C5 ⊗ C4 on x4 = {¬2,¬3}; ⊗ C3 on x3 = {¬2,¬6,5};
    ///             ⊗ C2 on x2 = {¬6, 5}  -> only x6 left at level 3: First UIP = x6.
    /// Learned (¬6 ∨ 5); backjump skips level 2 and lands on level 1,
    /// where ¬6 is asserted.
    #[test]
    fn first_uip_hand_checked() {
        let cnf = parse("p cnf 8 6\n-1 6 0\n-6 2 0\n-6 3 5 0\n-2 4 0\n-3 -4 0\n7 8 0\n").unwrap();
        let mut s = Solver::with_tracer(&cnf, Tracer::with_limit(1000));
        s.decide(lit(-5));
        assert_eq!(s.propagate(), None);
        s.decide(lit(7));
        assert_eq!(s.propagate(), None);
        s.decide(lit(1));
        let confl = s.propagate().expect("conflict");
        assert_eq!(confl, 4); // C5

        let (learnt, bt, conflict_side) = s.analyze(confl);
        assert_eq!(learnt[0], lit(-6), "asserting literal is the negated UIP");
        assert_eq!(sorted(&learnt), vec![5, -6]);
        assert_eq!(bt, 1);
        assert_eq!(conflict_side, vec![4, 3, 2]);

        let resolves: Vec<(usize, usize, Vec<i64>)> = s
            .tracer
            .events
            .iter()
            .filter_map(|e| match e {
                Event::Resolve {
                    clause_b,
                    pivot,
                    resolvent,
                    ..
                } => Some((*clause_b, *pivot, resolvent.clone())),
                _ => None,
            })
            .collect();
        assert_eq!(
            resolves,
            vec![
                (3, 4, vec![-2, -3]),
                (2, 3, vec![-2, 5, -6]),
                (1, 2, vec![5, -6]),
            ]
        );

        s.backjump(bt);
        assert_eq!(s.decision_level(), 1);
        assert_eq!(s.lit_value(lit(-5)), Some(true));
        assert_eq!(s.lit_value(lit(7)), None);
    }

    #[test]
    fn full_solve_learns_and_asserts() {
        let cnf = parse("p cnf 8 6\n-1 6 0\n-6 2 0\n-6 3 5 0\n-2 4 0\n-3 -4 0\n7 8 0\n").unwrap();
        let mut s = Solver::new(&cnf);
        assert_eq!(s.solve(), Status::Sat);
        assert!(verify_model(&cnf, s.model()));
    }

    #[test]
    fn moms_picks_most_frequent_in_smallest_clauses() {
        // Binary clauses: (1∨2), (1∨3), (¬2∨3). Ternary (4∨5∨6) is ignored.
        // f: x1 = 2/0 -> 4; x2 = 1/1 -> 5; x3 = 2/0 -> 4. Pick x2 (true on tie).
        let cnf = parse("p cnf 6 4\n1 2 0\n1 3 0\n-2 3 0\n4 5 6 0\n").unwrap();
        let mut s = Solver::with_tracer(&cnf, Tracer::with_limit(10));
        let (l, min, cands) = s.pick_branch().unwrap();
        assert_eq!(min, 2);
        assert_eq!(l, lit(2));
        assert_eq!(cands[0].var, 2);
        assert_eq!(cands[0].score, 5);
    }

    #[test]
    fn unit_and_empty_input_clauses() {
        let unsat = parse("p cnf 1 2\n1 0\n-1 0\n").unwrap();
        assert_eq!(Solver::new(&unsat).solve(), Status::Unsat);
        let empty = parse("p cnf 1 1\n0\n").unwrap();
        assert_eq!(Solver::new(&empty).solve(), Status::Unsat);
        let sat = parse("p cnf 2 2\n1 0\n-1 2 0\n").unwrap();
        let mut s = Solver::new(&sat);
        assert_eq!(s.solve(), Status::Sat);
        assert_eq!(s.model_dimacs(), vec![1, 2]);
    }

    #[test]
    fn duplicate_literals_are_merged() {
        let cnf = parse("p cnf 2 2\n1 1 0\n-1 2 2 0\n").unwrap();
        let mut s = Solver::new(&cnf);
        assert_eq!(s.solve(), Status::Sat);
        assert_eq!(s.model_dimacs(), vec![1, 2]);
    }

    /// A toy theory: variables 0 and 1 may not both be true. It reports a
    /// conflict instead of using a clause, so the solver has to learn it.
    struct NotBoth;
    impl TheoryHook for NotBoth {
        fn check(&mut self, sat: &mut Solver, _final_check: bool) -> TheoryResponse {
            let mut r = TheoryResponse::default();
            if sat.value(lit(1)) == Some(true) && sat.value(lit(2)) == Some(true) {
                r.conflict = Some(TheoryClause {
                    lits: vec![lit(-1), lit(-2)],
                    theory: "toy".into(),
                    why: "x1 and x2 exclude each other".into(),
                });
            } else if sat.value(lit(1)) == Some(true) && sat.value(lit(2)).is_none() {
                r.propagations.push(TheoryClause {
                    lits: vec![lit(-2), lit(-1)],
                    theory: "toy".into(),
                    why: "x1 excludes x2".into(),
                });
            }
            r
        }
        fn backjump(&mut self, _level: usize, _trail_len: usize) {}
    }

    #[test]
    fn theory_hook_propagates_and_conflicts() {
        // (x1 ∨ x3) ∧ (x2 ∨ x3) ∧ (¬x3): forces x1 and x2, which the theory forbids.
        let cnf = parse("p cnf 3 3\n1 3 0\n2 3 0\n-3 0\n").unwrap();
        let mut s = Solver::with_tracer(&cnf, Tracer::with_limit(1000));
        s.hook = Some(Box::new(NotBoth));
        assert_eq!(s.solve(), Status::Unsat);
        assert!(s
            .tracer
            .events
            .iter()
            .any(|e| matches!(e, Event::TheoryClause { .. })));

        // Without ¬x3 the theory pushes x2 false and x3 must be true.
        let cnf = parse("p cnf 3 2\n1 3 0\n2 3 0\n").unwrap();
        let mut s = Solver::new(&cnf);
        s.hook = Some(Box::new(NotBoth));
        assert_eq!(s.solve(), Status::Sat);
        let m = s.model();
        assert!(!(m[0] && m[1]));
        assert!(m[2] || (m[0] && m[1]), "both input clauses must hold");
    }

    #[test]
    fn replay_stops_at_conflict() {
        // ¬1∨2, ¬2∨¬3, 3∨¬1∨4: deciding 3 forces ¬2 and then ¬1.
        let cnf = parse("p cnf 4 3\n-1 2 0\n-2 -3 0\n3 -1 4 0\n").unwrap();
        let mut s = Solver::new(&cnf);
        let r = s.replay(&[lit(3), lit(1)]);
        assert_eq!(r.outcome, "sat");
        assert_eq!(r.skipped, vec![(1, false)], "x1 was already forced false");
        assert_eq!(s.value(lit(-1)), Some(true));

        // Deciding 1 then 3: 1 forces 2, 2 forces ¬3 and then 4, so
        // deciding 3 is skipped and everything is satisfied.
        let mut s = Solver::new(&cnf);
        let r = s.replay(&[lit(1), lit(3)]);
        assert_eq!(r.outcome, "sat");
        assert_eq!(r.skipped, vec![(1, false)]);
        assert_eq!(s.value(lit(2)), Some(true));
        assert_eq!(s.value(lit(4)), Some(true));

        // Only the first decision: clauses still open.
        let cnf = parse("p cnf 3 2\n-1 2 0\n2 3 1 0\n").unwrap();
        let mut s = Solver::new(&cnf);
        let r = s.replay(&[lit(-1)]);
        assert_eq!(r.outcome, "open");

        // A decision whose propagation falsifies a clause.
        let cnf = parse("p cnf 2 2\n-1 2 0\n-1 -2 0\n").unwrap();
        let mut s = Solver::new(&cnf);
        let r = s.replay(&[lit(1)]);
        assert_eq!(r.outcome, "conflict");
        assert_eq!(r.applied, 1);
    }
}
