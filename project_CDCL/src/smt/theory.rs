//! The theory interface. A theory plugs into the solver by implementing
//! [`Theory`] and being listed in `smt::default_theories()`; nothing else in
//! the solver, the parser or the combination needs to change.
//!
//! A theory
//! 1. contributes sorts and symbols to the signature (`init`, `command`,
//!    `type_app`), which also tells purification who owns which term;
//! 2. receives the atoms it owns (`register_atom`) and the truth values the
//!    SAT solver assigns to them (`assert_lit` / `backtrack`);
//! 3. answers `check`: conflict (with an explanation), propagations (with
//!    explanations), or, on a final check, a case split;
//! 4. produces model values and a JSON snapshot of its state for the UI.

use super::sexp::{Sexp, SmtError};
use super::term::{TermId, Terms, TheoryId, Value};
use crate::lit::Lit;
use crate::solver::TheoryClause;
use std::collections::HashMap;

/// What a theory sees while it runs: the term bank and a way to create new
/// atoms (Boolean variables) on demand.
pub struct Ctx<'a> {
    pub terms: &'a mut Terms,
    atom_of: &'a mut HashMap<TermId, usize>,
    alloc: &'a mut dyn FnMut() -> usize,
    /// Atoms created during this call; the combination registers them with
    /// their theories right after the call returns.
    pub new_atoms: Vec<(usize, TermId)>,
    /// Permanent clauses (e.g. definitions of new atoms).
    pub axioms: Vec<TheoryClause>,
}

impl<'a> Ctx<'a> {
    pub fn new(
        terms: &'a mut Terms,
        atom_of: &'a mut HashMap<TermId, usize>,
        alloc: &'a mut dyn FnMut() -> usize,
    ) -> Ctx<'a> {
        Ctx {
            terms,
            atom_of,
            alloc,
            new_atoms: Vec::new(),
            axioms: Vec::new(),
        }
    }

    /// Boolean variable of an atom term, created if it does not exist yet.
    pub fn atom(&mut self, term: TermId) -> usize {
        if let Some(&v) = self.atom_of.get(&term) {
            return v;
        }
        let v = (self.alloc)();
        self.atom_of.insert(term, v);
        self.new_atoms.push((v, term));
        v
    }

    /// Literal "atom term is `value`".
    pub fn lit(&mut self, term: TermId, value: bool) -> Lit {
        Lit::new(self.atom(term), value)
    }

    pub fn existing_atom(&self, term: TermId) -> Option<usize> {
        self.atom_of.get(&term).copied()
    }

    pub fn axiom(&mut self, lits: Vec<Lit>, theory: &str, why: String) {
        self.axioms.push(TheoryClause {
            lits,
            theory: theory.to_string(),
            why,
        });
    }
}

/// `implied` holds because all of `because` (currently true literals) do.
#[derive(Debug, Clone)]
pub struct Implied {
    pub implied: Lit,
    pub because: Vec<Lit>,
    pub why: String,
}

/// The currently true literals `lits` cannot hold together.
#[derive(Debug, Clone)]
pub struct Inconsistent {
    pub lits: Vec<Lit>,
    pub why: String,
}

#[derive(Debug, Clone, Default)]
pub struct Check {
    pub conflict: Option<Inconsistent>,
    pub propagations: Vec<Implied>,
    /// Final checks only: decide this literal next, and why.
    pub split: Option<(Lit, String)>,
    pub unknown: Option<String>,
    /// Explanatory notes for the playground: (kind, message, literals).
    pub notes: Vec<(&'static str, String, Vec<Lit>)>,
}

impl Check {
    pub fn is_empty(&self) -> bool {
        self.conflict.is_none()
            && self.propagations.is_empty()
            && self.split.is_none()
            && self.unknown.is_none()
    }
}

pub trait Theory {
    fn name(&self) -> &'static str;

    // ---------------------------------------------------------- signature

    /// Add built-in sorts and symbols. `me` is this theory's id.
    fn init(&mut self, terms: &mut Terms, me: TheoryId);

    /// Handle a theory-specific command such as `declare-datatypes`.
    /// Returns Ok(false) when the command is not this theory's.
    fn command(
        &mut self,
        _cmd: &Sexp,
        _terms: &mut Terms,
        _me: TheoryId,
    ) -> Result<bool, SmtError> {
        Ok(false)
    }

    /// Build (and type-check) an application of a symbol this theory owns.
    fn mk_app(&self, sym: &str, args: Vec<TermId>, terms: &mut Terms) -> Result<TermId, String>;

    // ---------------------------------------------------------- solving

    /// A Boolean variable now stands for `atom`, which this theory must
    /// interpret. New atoms and definitional axioms go through `ctx`.
    fn register_atom(&mut self, var: usize, atom: TermId, ctx: &mut Ctx) -> Result<(), String>;

    /// The SAT solver assigned `value` to the atom variable `var` at `level`.
    fn assert_lit(&mut self, var: usize, value: bool, level: usize);

    /// Undo everything asserted above decision level `level`.
    fn backtrack(&mut self, level: usize);

    /// Consistency check. On a final check every relevant atom is assigned
    /// and the theory must either accept, report a conflict, or ask for a
    /// split.
    fn check(&mut self, ctx: &mut Ctx, final_check: bool) -> Check;

    /// Nelson–Oppen guidance: are `a` and `b` equal in the theory's current
    /// candidate model? Used to pick the polarity of arrangement splits.
    fn eq_hint(&self, _a: TermId, _b: TermId) -> Option<bool> {
        None
    }

    /// Add model values for the terms this theory knows. `known` already
    /// holds the values decided by theories that ran before.
    fn model(&mut self, terms: &mut Terms, known: &mut HashMap<TermId, Value>);

    /// JSON snapshot of the theory state for the playground.
    fn snapshot(&self, terms: &Terms) -> String;

    /// Evaluate an application of one of this theory's symbols on model
    /// values (used to verify models). None when unspecified (e.g. a
    /// selector applied to the wrong constructor).
    fn eval_app(&self, _sym: &str, _args: &[Value], _terms: &Terms) -> Option<Value> {
        None
    }

    /// Some value of a sort this theory owns.
    fn default_value(&self, _sort: usize, _terms: &Terms) -> Option<Value> {
        None
    }

    /// Did the state change since the last call? (Avoids repeating
    /// identical snapshots in the trace.)
    fn take_changed(&mut self) -> bool {
        true
    }

    /// Keep a detailed record of each check for the snapshot (on while
    /// tracing; the playground draws it).
    fn set_recording(&mut self, _on: bool) {}
}
