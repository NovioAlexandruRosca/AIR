//! CDCL solver: DPLL search + two-watched-literal BCP + MOMS decisions +
//! First-UIP clause learning + non-chronological backjumping.
//!
//! Data structures
//! - `clauses: Vec<Clause>`: originals first, learned clauses appended. A
//!   clause id is its index and never changes (no clause deletion).
//! - `watches[lit]`: clauses watching `lit` (it is `lits[0]` or `lits[1]`),
//!   each with a blocker literal. The list is visited when `lit` becomes false.
//! - Per variable: `value`, `level`, `reason` (None = decision or unassigned).
//! - `trail`: assigned literals in assignment order; `trail_lim[d]` is the
//!   trail position where decision level `d + 1` starts.

use crate::dimacs::Cnf;
use crate::lit::Lit;
use crate::trace::{Event, MomsCandidate, Tracer};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Instant;

/// The `k` in the MOMS score `(f(x) + f(¬x)) * 2^k + f(x) * f(¬x)`.
pub const MOMS_K: u32 = 1;
/// How many MOMS candidates a `Decide` event records.
const TRACED_CANDIDATES: usize = 8;

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
}

impl StopReason {
    pub fn as_str(self) -> &'static str {
        match self {
            StopReason::ConflictLimit => "conflict limit",
            StopReason::TimeLimit => "time limit",
            StopReason::Cancelled => "cancelled",
        }
    }
}

#[derive(Debug, Clone)]
pub struct Clause {
    pub lits: Vec<Lit>,
    pub learnt: bool,
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
}

/// Learned clauses kept before the first database reduction.
pub const FIRST_REDUCE_AT: u64 = 8_000;

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

pub struct Solver {
    num_vars: usize,
    num_original: usize,
    clauses: Vec<Clause>,
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
    /// Delete the worse half of the learned clauses whenever more than
    /// `max_learnts` are alive. The limit is raised in `solve` above anything
    /// a trace can record, so traces never contain a deletion.
    pub reduce_db: bool,
    pub max_learnts: u64,
    learnts_alive: u64,
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
            reduce_db: true,
            max_learnts: FIRST_REDUCE_AT,
            learnts_alive: 0,
            stats: Stats::default(),
            tracer,
        };
        for c in &cnf.clauses {
            let lits = dedup_clause(c);
            let id = s.clauses.len();
            if lits.len() >= 2 {
                s.watches[lits[0].index()].push(Watch { cid: id, blocker: lits[1] });
                s.watches[lits[1].index()].push(Watch { cid: id, blocker: lits[0] });
            }
            s.clauses.push(Clause {
                lits,
                learnt: false,
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

    pub(crate) fn decision_level(&self) -> usize {
        self.trail_lim.len()
    }

    pub(crate) fn lit_value(&self, l: Lit) -> Option<bool> {
        lit_val(&self.value, l)
    }

    pub fn solve(&mut self) -> Status {
        // Every learned clause costs at least 3 events (Conflict, Learn,
        // Backjump), so no reduction can happen while a trace is recorded.
        if self.tracer.enabled {
            self.max_learnts = self.max_learnts.max(self.tracer.limit as u64 / 3 + 1);
        }
        // Unit and empty input clauses are handled at level 0 up front.
        for cid in 0..self.num_original {
            match self.clauses[cid].lits.len() {
                0 => {
                    self.tracer.push(|| Event::Conflict { clause: cid, level: 0 });
                    return self.finish(Status::Unsat);
                }
                1 => {
                    let l = self.clauses[cid].lits[0];
                    match self.lit_value(l) {
                        Some(true) => {}
                        Some(false) => {
                            self.stats.conflicts += 1;
                            self.tracer.push(|| Event::Conflict { clause: cid, level: 0 });
                            return self.finish(Status::Unsat);
                        }
                        None => self.enqueue(l, Some(cid)),
                    }
                }
                _ => {}
            }
        }

        loop {
            if let Some(reason) = self.external_stop() {
                self.stop_reason = Some(reason);
                return self.finish(Status::Unknown);
            }
            if let Some(confl) = self.propagate() {
                self.stats.conflicts += 1;
                let level = self.decision_level();
                self.tracer.push(|| Event::Conflict { clause: confl, level });
                if level == 0 {
                    return self.finish(Status::Unsat);
                }
                if self.max_conflicts.is_some_and(|m| self.stats.conflicts > m) {
                    self.stop_reason = Some(StopReason::ConflictLimit);
                    return self.finish(Status::Unknown);
                }
                self.learn_and_backjump(confl);
                if self.reduce_db && self.learnts_alive > self.max_learnts {
                    self.reduce_db();
                    self.max_learnts += self.max_learnts / 10;
                }
            } else {
                match self.pick_branch() {
                    None => return self.finish(Status::Sat),
                    Some((lit, min_size, candidates)) => {
                        self.stats.decisions += 1;
                        self.trail_lim.push(self.trail.len());
                        let level = self.decision_level();
                        self.stats.max_level = self.stats.max_level.max(level);
                        self.tracer.push(|| Event::Decide {
                            lit: lit.to_dimacs(),
                            level,
                            min_size,
                            candidates,
                        });
                        self.enqueue(lit, None);
                    }
                }
            }
        }
    }

    /// Time limit or cancellation. Checked once per search iteration (one
    /// BCP round plus one decision or conflict), which is cheap next to MOMS.
    fn external_stop(&self) -> Option<StopReason> {
        if self.cancel.as_ref().is_some_and(|c| c.load(Ordering::Relaxed)) {
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
            debug_assert!(self
                .clauses
                .iter()
                .all(|c| c.deleted || c.lits.iter().any(|l| self.model[l.var()] == l.is_positive())));
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
                let kept = Watch { cid, blocker: first };
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
    /// Only original clauses are scored: learned clauses are implied by them,
    /// and rescanning tens of thousands of learned clauses at every decision
    /// made the solver quadratic. Returns None when every original clause is
    /// satisfied (then the formula is).
    fn pick_branch(&mut self) -> Option<(Lit, usize, Vec<MomsCandidate>)> {
        let min_size = self
            .clauses[..self.num_original]
            .iter()
            .filter_map(|c| open_size(&self.value, &c.lits))
            .min()?;
        debug_assert!(min_size >= 2, "BCP left a unit or empty clause");

        self.moms_count.fill(0);
        for c in &self.clauses[..self.num_original] {
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
            self.watches[lits[0].index()].push(Watch { cid: id, blocker: lits[1] });
            self.watches[lits[1].index()].push(Watch { cid: id, blocker: lits[0] });
        }
        let asserting = lits[0];
        self.clauses.push(Clause {
            lits,
            learnt: true,
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
                !c.deleted && c.lbd > 2 && !self.is_locked(id)
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

    /// Hand-checked First-UIP example (also `examples/uip.cnf`):
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
}
