//! Algebraic datatypes (SMT-LIB `declare-datatypes`, non-parametric).
//!
//! Decision procedure: congruence closure over the DT terms of the
//! asserted literals, rebuilt from scratch at every check (so backtracking
//! is free), saturated with the datatype rules:
//! - clash:        C(..) = D(..) with C ≠ D is a conflict;
//! - injectivity:  C(a₁..aₙ) = C(b₁..bₙ) implies aᵢ = bᵢ;
//! - selectors:    t = C(a₁..aₙ) implies selᵢ(t) = aᵢ;
//! - testers:      is-C(t) makes t = C(sel₁(t), …, selₙ(t)); ¬is-C(t)
//!   excludes C, and if one constructor is left it is used;
//! - acyclicity:   no term may (transitively) contain itself, e.g. l = cons(x, l);
//! - disequalities a ≠ b must keep a and b in different classes.
//!
//! Every merge records why (input literal, congruence, injectivity, …) so a
//! conflict or propagation can be explained by input literals only.
//!
//! Final check: a class without a constructor is split on its testers when
//! its sort is finite or a selector is applied to it (splitting on demand).

use super::sexp::{err, Sexp, SmtError};
use super::term::{Op, SortId, TermId, Terms, TheoryId, Value, BOOL};
use super::theory::{Check, Ctx, Implied, Inconsistent, Theory};
use crate::lit::Lit;
use crate::trace::json_string;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt::Write;

const SNAPSHOT_CLASSES: usize = 120;
const SNAPSHOT_NODES: usize = 80;

/// (constructor name, [(selector, sort name)])
type CtorDecl = (String, Vec<(String, String)>);
/// (datatype name, constructors)
type DtDecl = (String, Vec<CtorDecl>);

struct Ctor {
    name: String,
    fields: Vec<(String, SortId)>,
}

struct Datatype {
    name: String,
    sort: SortId,
    ctors: Vec<Ctor>,
    finite: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum DtFun {
    Ctor(usize, usize),
    Sel(usize, usize, usize),
    Tester(usize, usize),
}

#[derive(Clone, Copy)]
enum DtAtom {
    Eq {
        var: usize,
        a: TermId,
        b: TermId,
    },
    Tester {
        var: usize,
        dt: usize,
        ctor: usize,
        t: TermId,
    },
}

impl DtAtom {
    fn var(&self) -> usize {
        match self {
            DtAtom::Eq { var, .. } | DtAtom::Tester { var, .. } => *var,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum NKind {
    Leaf,
    Ctor(usize, usize),
    Sel(usize, usize, usize),
}

struct CNode {
    term: TermId,
    kind: NKind,
    children: Vec<usize>,
}

/// A merge and its justification: input literals plus earlier equalities.
struct Edge {
    a: usize,
    b: usize,
    lits: Vec<Lit>,
    eqs: Vec<(usize, usize)>,
    /// rule that made the merge (asserted, congruence, injectivity, ...)
    rule: &'static str,
}

/// Congruence closure with explanations.
#[derive(Default)]
struct Cc {
    nodes: Vec<CNode>,
    node_of: HashMap<TermId, usize>,
    root: Vec<usize>,
    members: Vec<Vec<usize>>,
    edges: Vec<Edge>,
    /// root -> constructor node of the class
    ctor_of: HashMap<usize, usize>,
    /// root -> excluded constructors (ctor index, literal, tester argument)
    excluded: HashMap<usize, Vec<(usize, Lit, usize)>>,
    diseqs: Vec<(usize, usize, Lit)>,
}

impl Cc {
    fn find(&self, n: usize) -> usize {
        self.root[n]
    }

    fn node(&mut self, dt: &Dt, terms: &Terms, t: TermId) -> usize {
        if let Some(&n) = self.node_of.get(&t) {
            return n;
        }
        let kind = match terms.sym(t).and_then(|s| dt.funs.get(s)) {
            Some(DtFun::Ctor(d, c)) => NKind::Ctor(*d, *c),
            Some(DtFun::Sel(d, c, f)) => NKind::Sel(*d, *c, *f),
            _ => NKind::Leaf,
        };
        let children: Vec<usize> = if kind == NKind::Leaf {
            Vec::new()
        } else {
            terms
                .args(t)
                .to_vec()
                .into_iter()
                .map(|a| self.node(dt, terms, a))
                .collect()
        };
        let n = self.nodes.len();
        self.nodes.push(CNode {
            term: t,
            kind,
            children,
        });
        self.node_of.insert(t, n);
        self.root.push(n);
        self.members.push(vec![n]);
        n
    }

    /// Merge the classes of a and b; false if already equal.
    fn union(
        &mut self,
        a: usize,
        b: usize,
        lits: Vec<Lit>,
        eqs: Vec<(usize, usize)>,
        rule: &'static str,
    ) -> bool {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra == rb {
            return false;
        }
        self.edges.push(Edge {
            a,
            b,
            lits,
            eqs,
            rule,
        });
        let (big, small) = if self.members[ra].len() >= self.members[rb].len() {
            (ra, rb)
        } else {
            (rb, ra)
        };
        let moved = std::mem::take(&mut self.members[small]);
        for &m in &moved {
            self.root[m] = big;
        }
        self.members[big].extend(moved);
        true
    }

    /// Input literals that justify a = b, using only edges before `limit`.
    fn explain_into(
        &self,
        a: usize,
        b: usize,
        limit: usize,
        out: &mut Vec<Lit>,
        done: &mut HashSet<(usize, usize, usize)>,
    ) {
        if a == b {
            return;
        }
        let key = (a.min(b), a.max(b), limit);
        if !done.insert(key) {
            return;
        }
        // BFS over the undirected edge graph restricted to edges[..limit].
        let mut adj: HashMap<usize, Vec<(usize, usize)>> = HashMap::new();
        for (i, e) in self.edges[..limit].iter().enumerate() {
            adj.entry(e.a).or_default().push((e.b, i));
            adj.entry(e.b).or_default().push((e.a, i));
        }
        let mut prev: HashMap<usize, (usize, usize)> = HashMap::new();
        let mut queue = VecDeque::from([a]);
        let mut seen = HashSet::from([a]);
        while let Some(x) = queue.pop_front() {
            if x == b {
                break;
            }
            for &(y, ei) in adj.get(&x).map(|v| v.as_slice()).unwrap_or(&[]) {
                if seen.insert(y) {
                    prev.insert(y, (x, ei));
                    queue.push_back(y);
                }
            }
        }
        let mut x = b;
        while x != a {
            let Some(&(p, ei)) = prev.get(&x) else {
                debug_assert!(false, "no explanation path");
                return;
            };
            let e = &self.edges[ei];
            for &l in &e.lits {
                if !out.contains(&l) {
                    out.push(l);
                }
            }
            for &(u, v) in &e.eqs {
                self.explain_into(u, v, ei, out, done);
            }
            x = p;
        }
    }

    fn explain(&self, pairs: &[(usize, usize)], extra: &[Lit]) -> Vec<Lit> {
        let mut out: Vec<Lit> = extra.to_vec();
        let mut done = HashSet::new();
        for &(a, b) in pairs {
            self.explain_into(a, b, self.edges.len(), &mut out, &mut done);
        }
        out
    }
}

pub struct Dt {
    me: TheoryId,
    dts: Vec<Datatype>,
    funs: HashMap<String, DtFun>,
    sort_dt: HashMap<SortId, usize>,
    atoms: Vec<DtAtom>,
    atom_of_var: HashMap<usize, usize>,
    term_of_var: HashMap<usize, TermId>,
    assigned: Vec<Option<bool>>,
    /// (atom, value, level) in assertion order
    trail: Vec<(usize, bool, usize)>,
    changed: bool,
    last: Option<Cc>,
    last_event: Option<String>,
}

impl Default for Dt {
    fn default() -> Self {
        Dt::new()
    }
}

impl Dt {
    pub fn new() -> Dt {
        Dt {
            me: 0,
            dts: Vec::new(),
            funs: HashMap::new(),
            sort_dt: HashMap::new(),
            atoms: Vec::new(),
            atom_of_var: HashMap::new(),
            term_of_var: HashMap::new(),
            assigned: Vec::new(),
            trail: Vec::new(),
            changed: true,
            last: None,
            last_event: None,
        }
    }

    fn lit_label(&self, terms: &Terms, l: Lit) -> String {
        match self.term_of_var.get(&l.var()) {
            Some(&t) if l.is_positive() => terms.display(t),
            Some(&t) => terms.display_neg(t),
            None => format!("literal {l}"),
        }
    }

    fn labels(&self, terms: &Terms, lits: &[Lit]) -> String {
        if lits.is_empty() {
            return "(no assumptions)".into();
        }
        lits.iter()
            .map(|&l| self.lit_label(terms, l))
            .collect::<Vec<_>>()
            .join(", ")
    }

    fn ctor_name(&self, d: usize, c: usize) -> &str {
        &self.dts[d].ctors[c].name
    }

    /// Declare datatypes: `decls` is [(name, constructors)] where a
    /// constructor is (name, [(selector, sort name)]).
    fn declare(
        &mut self,
        decls: Vec<DtDecl>,
        terms: &mut Terms,
        line: usize,
    ) -> Result<(), SmtError> {
        let first = self.dts.len();
        for (name, _) in &decls {
            if terms.sort_named(name).is_some() {
                return err(line, format!("sort '{name}' is already declared"));
            }
            let sort = terms.add_sort(name, Some(self.me));
            self.sort_dt.insert(sort, self.dts.len());
            self.dts.push(Datatype {
                name: name.clone(),
                sort,
                ctors: Vec::new(),
                finite: false,
            });
        }
        for (k, (name, ctors)) in decls.into_iter().enumerate() {
            let d = first + k;
            if ctors.is_empty() {
                return err(line, format!("datatype '{name}' has no constructors"));
            }
            for (cname, fields) in ctors {
                let mut fs = Vec::new();
                for (sel, sort_name) in fields {
                    let s = match terms.sort_named(&sort_name) {
                        Some(s) if s != BOOL => s,
                        Some(_) => {
                            return err(
                                line,
                                format!("field '{sel}': Bool fields are not supported"),
                            )
                        }
                        None => {
                            return err(line, format!("field '{sel}': unknown sort '{sort_name}'"))
                        }
                    };
                    fs.push((sel, s));
                }
                let c = self.dts[d].ctors.len();
                for n in std::iter::once(cname.clone())
                    .chain(fs.iter().map(|(s, _)| s.clone()))
                    .chain(std::iter::once(format!("is-{cname}")))
                {
                    if terms.is_declared(&n) || self.funs.contains_key(&n) {
                        return err(line, format!("'{n}' is already declared"));
                    }
                }
                self.funs.insert(cname.clone(), DtFun::Ctor(d, c));
                terms.add_fun(&cname, self.me);
                for (f, (sel, _)) in fs.iter().enumerate() {
                    self.funs.insert(sel.clone(), DtFun::Sel(d, c, f));
                    terms.add_fun(sel, self.me);
                }
                self.funs.insert(format!("is-{cname}"), DtFun::Tester(d, c));
                terms.add_fun(&format!("is-{cname}"), self.me);
                self.dts[d].ctors.push(Ctor {
                    name: cname,
                    fields: fs,
                });
            }
        }
        // A datatype is finite when it reaches neither Int nor itself.
        for d in 0..self.dts.len() {
            let mut finite = true;
            let mut stack = vec![d];
            let mut seen = HashSet::new();
            'outer: while let Some(x) = stack.pop() {
                for c in &self.dts[x].ctors {
                    for &(_, s) in &c.fields {
                        match self.sort_dt.get(&s) {
                            None => {
                                finite = false;
                                break 'outer;
                            }
                            Some(&y) if y == d => {
                                finite = false;
                                break 'outer;
                            }
                            Some(&y) => {
                                if seen.insert(y) {
                                    stack.push(y);
                                }
                            }
                        }
                    }
                }
            }
            self.dts[d].finite = finite;
        }
        Ok(())
    }

    /// Build and saturate the congruence closure for the asserted literals.
    fn build(&self, terms: &mut Terms, cc: &mut Cc) -> Result<(), Inconsistent> {
        *cc = Cc::default();
        for a in &self.atoms {
            match *a {
                DtAtom::Eq { a, b, .. } => {
                    cc.node(self, terms, a);
                    cc.node(self, terms, b);
                }
                DtAtom::Tester { t, .. } => {
                    cc.node(self, terms, t);
                }
            }
        }
        type Merge = (usize, usize, Vec<Lit>, Vec<(usize, usize)>, &'static str);
        let mut queue: Vec<Merge> = Vec::new();
        let mut testers: Vec<(usize, usize, usize, Lit, bool)> = Vec::new();
        for &(idx, val, _) in &self.trail {
            let lit = Lit::new(self.atoms[idx].var(), val);
            match self.atoms[idx] {
                DtAtom::Eq { a, b, .. } => {
                    let (na, nb) = (cc.node_of[&a], cc.node_of[&b]);
                    if val {
                        queue.push((na, nb, vec![lit], Vec::new(), "asserted"));
                    } else {
                        cc.diseqs.push((na, nb, lit));
                    }
                }
                DtAtom::Tester { dt, ctor, t, .. } => {
                    testers.push((cc.node_of[&t], dt, ctor, lit, val))
                }
            }
        }
        let mut instantiated: HashSet<usize> = HashSet::new();

        loop {
            let mut changed = false;
            for (a, b, lits, eqs, rule) in queue.drain(..) {
                changed |= cc.union(a, b, lits, eqs, rule);
            }
            // congruence
            let mut sig: HashMap<(NKind, Vec<usize>), usize> = HashMap::new();
            for n in 0..cc.nodes.len() {
                if cc.nodes[n].kind == NKind::Leaf {
                    continue;
                }
                let key = (
                    cc.nodes[n].kind,
                    cc.nodes[n].children.iter().map(|&c| cc.find(c)).collect(),
                );
                match sig.get(&key) {
                    Some(&m) if cc.find(m) != cc.find(n) => {
                        let eqs = cc.nodes[n]
                            .children
                            .iter()
                            .copied()
                            .zip(cc.nodes[m].children.iter().copied())
                            .collect();
                        queue.push((n, m, Vec::new(), eqs, "congruence"));
                    }
                    Some(_) => {}
                    None => {
                        sig.insert(key, n);
                    }
                }
            }
            // clash and injectivity
            cc.ctor_of.clear();
            for n in 0..cc.nodes.len() {
                let NKind::Ctor(d, c) = cc.nodes[n].kind else {
                    continue;
                };
                let r = cc.find(n);
                match cc.ctor_of.get(&r).copied() {
                    None => {
                        cc.ctor_of.insert(r, n);
                    }
                    Some(m) => {
                        let NKind::Ctor(_, c2) = cc.nodes[m].kind else {
                            unreachable!()
                        };
                        if c2 != c {
                            let lits = cc.explain(&[(m, n)], &[]);
                            return Err(Inconsistent {
                                why: format!(
                                    "constructor clash: {} = {} but {} and {} are different constructors (because {})",
                                    terms.display(cc.nodes[m].term),
                                    terms.display(cc.nodes[n].term),
                                    self.ctor_name(d, c2),
                                    self.ctor_name(d, c),
                                    self.labels(terms, &lits)
                                ),
                                lits,
                            });
                        }
                        for i in 0..cc.nodes[n].children.len() {
                            let (x, y) = (cc.nodes[m].children[i], cc.nodes[n].children[i]);
                            if cc.find(x) != cc.find(y) {
                                queue.push((x, y, Vec::new(), vec![(m, n)], "injectivity"));
                            }
                        }
                    }
                }
            }
            // selectors applied to a constructor term
            for n in 0..cc.nodes.len() {
                let NKind::Sel(d, c, f) = cc.nodes[n].kind else {
                    continue;
                };
                let arg = cc.nodes[n].children[0];
                if let Some(&k) = cc.ctor_of.get(&cc.find(arg)) {
                    if cc.nodes[k].kind == NKind::Ctor(d, c) {
                        let field = cc.nodes[k].children[f];
                        if cc.find(field) != cc.find(n) {
                            queue.push((n, field, Vec::new(), vec![(arg, k)], "selector"));
                        }
                    }
                }
            }
            // testers
            cc.excluded.clear();
            for &(t, d, c, lit, val) in &testers {
                let r = cc.find(t);
                let k = cc.ctor_of.get(&r).copied();
                if val {
                    match k {
                        Some(k) => {
                            if cc.nodes[k].kind != NKind::Ctor(d, c) {
                                let lits = cc.explain(&[(t, k)], &[lit]);
                                return Err(Inconsistent {
                                    why: format!(
                                        "tester clash: {} but {} = {} (because {})",
                                        self.lit_label(terms, lit),
                                        terms.display(cc.nodes[t].term),
                                        terms.display(cc.nodes[k].term),
                                        self.labels(terms, &lits)
                                    ),
                                    lits,
                                });
                            }
                        }
                        None => {
                            if instantiated.insert(r) {
                                let k = self.instantiate(cc, terms, t, d, c);
                                queue.push((t, k, vec![lit], Vec::new(), "tester"));
                            }
                        }
                    }
                } else {
                    if k.is_some_and(|k| cc.nodes[k].kind == NKind::Ctor(d, c)) {
                        let k = k.unwrap();
                        let lits = cc.explain(&[(t, k)], &[lit]);
                        return Err(Inconsistent {
                            why: format!(
                                "tester clash: {} but {} = {} (because {})",
                                self.lit_label(terms, lit),
                                terms.display(cc.nodes[t].term),
                                terms.display(cc.nodes[k].term),
                                self.labels(terms, &lits)
                            ),
                            lits,
                        });
                    }
                    cc.excluded.entry(r).or_default().push((c, lit, t));
                }
            }
            // a class with every constructor but one excluded must use that one
            let roots: Vec<usize> = cc.excluded.keys().copied().collect();
            for r in roots {
                if cc.ctor_of.contains_key(&r) || instantiated.contains(&r) {
                    continue;
                }
                let excl = cc.excluded[&r].clone();
                let t0 = excl[0].2;
                let d = self.sort_dt[&terms.sort(cc.nodes[t0].term)];
                let left: Vec<usize> = (0..self.dts[d].ctors.len())
                    .filter(|c| !excl.iter().any(|e| e.0 == *c))
                    .collect();
                let pairs: Vec<(usize, usize)> = excl.iter().map(|e| (e.2, t0)).collect();
                let lits_ex: Vec<Lit> = excl.iter().map(|e| e.1).collect();
                if left.is_empty() {
                    let lits = cc.explain(&pairs, &lits_ex);
                    return Err(Inconsistent {
                        why: format!(
                            "{} has no constructor left: {}",
                            terms.display(cc.nodes[t0].term),
                            self.labels(terms, &lits)
                        ),
                        lits,
                    });
                }
                if left.len() == 1 {
                    instantiated.insert(r);
                    let k = self.instantiate(cc, terms, t0, d, left[0]);
                    let lits = cc.explain(&pairs, &lits_ex);
                    queue.push((t0, k, lits, Vec::new(), "last constructor"));
                }
            }
            if !changed && queue.is_empty() {
                break;
            }
        }

        for &(a, b, lit) in &cc.diseqs {
            if cc.find(a) == cc.find(b) {
                let lits = cc.explain(&[(a, b)], &[lit]);
                return Err(Inconsistent {
                    why: format!(
                        "{} but congruence closure derives {} = {} (because {})",
                        self.lit_label(terms, lit),
                        terms.display(cc.nodes[a].term),
                        terms.display(cc.nodes[b].term),
                        self.labels(terms, &lits)
                    ),
                    lits,
                });
            }
        }
        if let Some(cycle) = self.find_cycle(cc, terms) {
            return Err(cycle);
        }
        Ok(())
    }

    /// Add the term C(sel₁(t), …, selₙ(t)) and return its node.
    fn instantiate(&self, cc: &mut Cc, terms: &mut Terms, t: usize, d: usize, c: usize) -> usize {
        let tt = cc.nodes[t].term;
        let ctor = &self.dts[d].ctors[c];
        let sels: Vec<TermId> = ctor
            .fields
            .iter()
            .map(|(sel, s)| terms.app(sel, vec![tt], *s))
            .collect();
        let term = terms.app(&ctor.name, sels, self.dts[d].sort);
        cc.node(self, terms, term)
    }

    /// Occurs check: a class reachable from itself through constructor
    /// arguments is a cycle such as l = cons(x, l).
    fn find_cycle(&self, cc: &Cc, terms: &Terms) -> Option<Inconsistent> {
        // root -> [(ctor node, child node)] for datatype-sorted children
        let mut out: HashMap<usize, Vec<(usize, usize)>> = HashMap::new();
        for (&r, &k) in &cc.ctor_of {
            for &ch in &cc.nodes[k].children {
                if self.sort_dt.contains_key(&terms.sort(cc.nodes[ch].term)) {
                    out.entry(r).or_default().push((k, ch));
                }
            }
        }
        // iterative DFS with colours; path keeps (root, ctor node, child node)
        let mut colour: HashMap<usize, u8> = HashMap::new();
        let mut roots: Vec<usize> = out.keys().copied().collect();
        roots.sort();
        for start in roots {
            if colour.get(&start).copied().unwrap_or(0) != 0 {
                continue;
            }
            let mut stack: Vec<(usize, usize)> = vec![(start, 0)];
            let mut path: Vec<(usize, usize, usize)> = Vec::new();
            colour.insert(start, 1);
            while let Some(&mut (r, ref mut i)) = stack.last_mut() {
                let edges = out.get(&r).map(|v| v.as_slice()).unwrap_or(&[]);
                if *i >= edges.len() {
                    colour.insert(r, 2);
                    stack.pop();
                    path.pop();
                    continue;
                }
                let (k, ch) = edges[*i];
                *i += 1;
                let next = cc.find(ch);
                match colour.get(&next).copied().unwrap_or(0) {
                    0 => {
                        colour.insert(next, 1);
                        path.push((r, k, ch));
                        stack.push((next, 0));
                    }
                    1 => {
                        // cycle: from `next` along the path back to r, then r -> next
                        let mut steps: Vec<(usize, usize)> = Vec::new();
                        let pos = path.iter().position(|p| p.0 == next).unwrap_or(path.len());
                        for p in &path[pos..] {
                            steps.push((p.1, p.2));
                        }
                        steps.push((k, ch));
                        // step j: ctor k_j and child ch_j; ch_j ~ k_{j+1}
                        let mut pairs = Vec::new();
                        for j in 0..steps.len() {
                            let ch_j = steps[j].1;
                            let k_next = steps[(j + 1) % steps.len()].0;
                            pairs.push((ch_j, k_next));
                        }
                        let lits = cc.explain(&pairs, &[]);
                        let chain: Vec<String> = steps
                            .iter()
                            .map(|&(k, _)| terms.display(cc.nodes[k].term))
                            .collect();
                        return Some(Inconsistent {
                            why: format!(
                                "acyclicity: {} would contain itself (a datatype value cannot be its own subterm; because {})",
                                chain.join(" ⊃ "),
                                self.labels(terms, &lits)
                            ),
                            lits,
                        });
                    }
                    _ => {}
                }
            }
        }
        None
    }

    fn propagations(&self, cc: &Cc, terms: &Terms) -> Vec<Implied> {
        let mut out = Vec::new();
        for (idx, atom) in self.atoms.iter().enumerate() {
            if self.assigned[idx].is_some() {
                continue;
            }
            match *atom {
                DtAtom::Eq { var, a, b } => {
                    let (na, nb) = (cc.node_of[&a], cc.node_of[&b]);
                    let (ra, rb) = (cc.find(na), cc.find(nb));
                    if ra == rb {
                        let because = cc.explain(&[(na, nb)], &[]);
                        out.push(Implied {
                            implied: Lit::new(var, true),
                            why: format!(
                                "congruence closure: {} (because {})",
                                terms.display(self.term_of_var[&var]),
                                self.labels(terms, &because)
                            ),
                            because,
                        });
                        continue;
                    }
                    if let (Some(&ka), Some(&kb)) = (cc.ctor_of.get(&ra), cc.ctor_of.get(&rb)) {
                        if cc.nodes[ka].kind != cc.nodes[kb].kind {
                            let because = cc.explain(&[(na, ka), (nb, kb)], &[]);
                            out.push(Implied {
                                implied: Lit::new(var, false),
                                why: format!(
                                    "different constructors: {} is {} and {} is {}, so {}",
                                    terms.display(a),
                                    terms.display(cc.nodes[ka].term),
                                    terms.display(b),
                                    terms.display(cc.nodes[kb].term),
                                    terms.display_neg(self.term_of_var[&var])
                                ),
                                because,
                            });
                            continue;
                        }
                    }
                    for &(u, v, lit) in &cc.diseqs {
                        let (ru, rv) = (cc.find(u), cc.find(v));
                        let pairs = if ru == ra && rv == rb {
                            Some([(na, u), (nb, v)])
                        } else if ru == rb && rv == ra {
                            Some([(na, v), (nb, u)])
                        } else {
                            None
                        };
                        if let Some(pairs) = pairs {
                            let because = cc.explain(&pairs, &[lit]);
                            out.push(Implied {
                                implied: Lit::new(var, false),
                                why: format!(
                                    "{} follows from {} (because {})",
                                    terms.display_neg(self.term_of_var[&var]),
                                    self.lit_label(terms, lit),
                                    self.labels(terms, &because)
                                ),
                                because,
                            });
                            break;
                        }
                    }
                }
                DtAtom::Tester { var, dt, ctor, t } => {
                    let nt = cc.node_of[&t];
                    let r = cc.find(nt);
                    if let Some(&k) = cc.ctor_of.get(&r) {
                        let yes = cc.nodes[k].kind == NKind::Ctor(dt, ctor);
                        let because = cc.explain(&[(nt, k)], &[]);
                        out.push(Implied {
                            implied: Lit::new(var, yes),
                            why: format!(
                                "{} = {}, so {}",
                                terms.display(t),
                                terms.display(cc.nodes[k].term),
                                self.lit_label(terms, Lit::new(var, yes))
                            ),
                            because,
                        });
                    } else if let Some(&(_, lit, t2)) = cc
                        .excluded
                        .get(&r)
                        .and_then(|ex| ex.iter().find(|e| e.0 == ctor))
                    {
                        let because = cc.explain(&[(nt, t2)], &[lit]);
                        out.push(Implied {
                            implied: Lit::new(var, false),
                            why: format!(
                                "{} because {}",
                                terms.display_neg(self.term_of_var[&var]),
                                self.labels(terms, &because)
                            ),
                            because,
                        });
                    }
                }
            }
        }
        out
    }

    /// Final check: a class that must be built by a constructor but has
    /// none yet gets a tester split.
    fn split(&self, cc: &Cc, ctx: &mut Ctx) -> Option<(Lit, String)> {
        let mut has_sel: HashSet<usize> = HashSet::new();
        for n in &cc.nodes {
            if let NKind::Sel(..) = n.kind {
                has_sel.insert(cc.find(n.children[0]));
            }
        }
        let mut roots: Vec<usize> = (0..cc.nodes.len()).filter(|&n| cc.find(n) == n).collect();
        roots.sort_by_key(|&r| cc.members[r].iter().map(|&m| cc.nodes[m].term).min());
        for r in roots {
            if cc.ctor_of.contains_key(&r) {
                continue;
            }
            let rep = *cc.members[r]
                .iter()
                .min_by_key(|&&m| cc.nodes[m].term)
                .unwrap();
            let t = cc.nodes[rep].term;
            let Some(&d) = self.sort_dt.get(&ctx.terms.sort(t)) else {
                continue;
            };
            let finite = self.dts[d].finite;
            if !finite && !has_sel.contains(&r) {
                continue;
            }
            let excluded: Vec<usize> = cc
                .excluded
                .get(&r)
                .map(|v| v.iter().map(|e| e.0).collect())
                .unwrap_or_default();
            // Prefer constructors that do not recurse into the same sort.
            let sort = self.dts[d].sort;
            let mut order: Vec<usize> = (0..self.dts[d].ctors.len())
                .filter(|c| !excluded.contains(c))
                .collect();
            order.sort_by_key(|&c| self.dts[d].ctors[c].fields.iter().any(|f| f.1 == sort));
            let Some(&c) = order.first() else { continue };
            let tester = ctx
                .terms
                .app(&format!("is-{}", self.ctor_name(d, c)), vec![t], BOOL);
            let lit = ctx.lit(tester, true);
            let reason = if finite {
                format!("{} is a finite datatype", self.dts[d].name)
            } else {
                format!("a selector is applied to {}", ctx.terms.display(t))
            };
            let why = format!(
                "datatype split: {} must be built by one of the constructors of {} ({reason}); try {} first",
                ctx.terms.display(t),
                self.dts[d].name,
                self.ctor_name(d, c)
            );
            return Some((lit, why));
        }
        None
    }

    /// A value of sort `d` that differs from every value in `used`.
    fn fresh_value(
        &self,
        d: usize,
        excluded: &[usize],
        fresh_int: &mut i128,
        used: &HashSet<Value>,
        depth: usize,
    ) -> Value {
        let sort = self.dts[d].sort;
        let mut order: Vec<usize> = (0..self.dts[d].ctors.len())
            .filter(|c| !excluded.contains(c))
            .collect();
        if order.is_empty() {
            order = (0..self.dts[d].ctors.len()).collect();
        }
        // Non-recursive constructors first, unless we need depth to be fresh.
        order.sort_by_key(|&c| self.dts[d].ctors[c].fields.iter().any(|f| f.1 == sort));
        for &c in &order {
            let v = self.build_value(d, c, fresh_int, depth);
            if !used.contains(&v) {
                return v;
            }
        }
        // Go deeper through a recursive constructor.
        if depth < 64 {
            return self.fresh_value(d, excluded, fresh_int, used, depth + 1);
        }
        self.build_value(d, order[0], fresh_int, 0)
    }

    fn build_value(&self, d: usize, c: usize, fresh_int: &mut i128, depth: usize) -> Value {
        let ctor = &self.dts[d].ctors[c];
        let mut args = Vec::new();
        for &(_, s) in &ctor.fields {
            match self.sort_dt.get(&s) {
                None => {
                    *fresh_int += 1;
                    args.push(Value::Int(*fresh_int));
                }
                Some(&d2) => {
                    let sort2 = self.dts[d2].sort;
                    let mut order: Vec<usize> = (0..self.dts[d2].ctors.len()).collect();
                    order.sort_by_key(|&k| {
                        self.dts[d2].ctors[k].fields.iter().any(|f| f.1 == sort2)
                    });
                    let k = if depth > 0 {
                        *order.last().unwrap()
                    } else {
                        order[0]
                    };
                    args.push(self.build_value(d2, k, fresh_int, depth.saturating_sub(1)));
                }
            }
        }
        Value::Dt(ctor.name.clone(), args)
    }
}

impl Theory for Dt {
    fn name(&self) -> &'static str {
        "DT"
    }

    fn init(&mut self, _terms: &mut Terms, me: TheoryId) {
        self.me = me;
    }

    fn command(&mut self, cmd: &Sexp, terms: &mut Terms, me: TheoryId) -> Result<bool, SmtError> {
        self.me = me;
        let line = cmd.line();
        let items = cmd.list().unwrap_or(&[]);
        let head = cmd.head().unwrap_or("");
        let parse_ctor = |c: &Sexp| -> Result<(String, Vec<(String, String)>), SmtError> {
            match c {
                Sexp::Atom(name, _) => Ok((name.clone(), Vec::new())),
                Sexp::List(parts, l) => {
                    let name = parts.first().and_then(|p| p.atom()).ok_or(SmtError {
                        line: *l,
                        message: "constructor name expected".into(),
                    })?;
                    let mut fields = Vec::new();
                    for f in &parts[1..] {
                        match f.list() {
                            Some([Sexp::Atom(sel, _), Sexp::Atom(sort, _)]) => {
                                fields.push((sel.clone(), sort.clone()))
                            }
                            _ => {
                                return err(
                                    f.line(),
                                    format!("field must be (selector Sort), got {f}"),
                                )
                            }
                        }
                    }
                    Ok((name.to_string(), fields))
                }
            }
        };
        match head {
            "declare-datatype" => {
                let (Some(name), Some(ctors)) = (
                    items.get(1).and_then(|s| s.atom()),
                    items.get(2).and_then(|s| s.list()),
                ) else {
                    return err(
                        line,
                        "usage: (declare-datatype Name ((ctor (sel Sort) ...) ...))",
                    );
                };
                let cs: Result<Vec<_>, _> = ctors.iter().map(parse_ctor).collect();
                self.declare(vec![(name.to_string(), cs?)], terms, line)?;
                Ok(true)
            }
            "declare-datatypes" => {
                let (Some(sorts), Some(bodies)) = (
                    items.get(1).and_then(|s| s.list()),
                    items.get(2).and_then(|s| s.list()),
                ) else {
                    return err(line, "usage: (declare-datatypes ((Name 0) ...) (((ctor (sel Sort) ...) ...) ...))");
                };
                let mut decls = Vec::new();
                if sorts.is_empty() {
                    // SMT-LIB 2.5 style: (declare-datatypes () ((Name ctor ...) ...))
                    for b in bodies {
                        let parts = b.list().unwrap_or(&[]);
                        let Some(name) = parts.first().and_then(|p| p.atom()) else {
                            return err(b.line(), "datatype name expected");
                        };
                        let cs: Result<Vec<_>, _> = parts[1..].iter().map(parse_ctor).collect();
                        decls.push((name.to_string(), cs?));
                    }
                } else {
                    if sorts.len() != bodies.len() {
                        return err(line, "declare-datatypes: number of sorts and bodies differ");
                    }
                    for (s, b) in sorts.iter().zip(bodies) {
                        let (name, arity) = match s.list() {
                            Some([Sexp::Atom(n, _), Sexp::Atom(a, _)]) => (n.clone(), a.clone()),
                            _ => return err(s.line(), format!("expected (Name 0), got {s}")),
                        };
                        if arity != "0" {
                            return err(
                                s.line(),
                                format!("parametric datatype '{name}' is not supported"),
                            );
                        }
                        if b.head() == Some("par") {
                            return err(
                                b.line(),
                                "parametric datatypes (par ...) are not supported",
                            );
                        }
                        let ctors = b.list().unwrap_or(&[]);
                        let cs: Result<Vec<_>, _> = ctors.iter().map(parse_ctor).collect();
                        decls.push((name, cs?));
                    }
                }
                self.declare(decls, terms, line)?;
                Ok(true)
            }
            _ => Ok(false),
        }
    }

    fn mk_app(&self, sym: &str, args: Vec<TermId>, terms: &mut Terms) -> Result<TermId, String> {
        let f = *self
            .funs
            .get(sym)
            .ok_or_else(|| format!("unknown datatype symbol '{sym}'"))?;
        let check_arg = |terms: &Terms, args: &[TermId], d: usize| -> Result<(), String> {
            if args.len() != 1 {
                return Err(format!("'{sym}' takes one argument"));
            }
            if terms.sort(args[0]) != self.dts[d].sort {
                return Err(format!(
                    "'{sym}' expects a {}, got {} : {}",
                    self.dts[d].name,
                    terms.display(args[0]),
                    terms.sort_name(terms.sort(args[0]))
                ));
            }
            Ok(())
        };
        match f {
            DtFun::Ctor(d, c) => {
                let ctor = &self.dts[d].ctors[c];
                if args.len() != ctor.fields.len() {
                    return Err(format!(
                        "constructor '{sym}' takes {} argument(s), got {}",
                        ctor.fields.len(),
                        args.len()
                    ));
                }
                for (a, (sel, s)) in args.iter().zip(&ctor.fields) {
                    if terms.sort(*a) != *s {
                        return Err(format!(
                            "'{sym}': field '{sel}' needs {}, got {} : {}",
                            terms.sort_name(*s),
                            terms.display(*a),
                            terms.sort_name(terms.sort(*a))
                        ));
                    }
                }
                Ok(terms.app(sym, args, self.dts[d].sort))
            }
            DtFun::Sel(d, c, fi) => {
                check_arg(terms, &args, d)?;
                Ok(terms.app(sym, args, self.dts[d].ctors[c].fields[fi].1))
            }
            DtFun::Tester(d, _) => {
                check_arg(terms, &args, d)?;
                Ok(terms.app(sym, args, BOOL))
            }
        }
    }

    fn register_atom(&mut self, var: usize, atom: TermId, ctx: &mut Ctx) -> Result<(), String> {
        let node = ctx.terms.node(atom).clone();
        let a = match (&node.op, node.args.as_slice()) {
            (Op::App(s), [a, b]) if s == "=" => DtAtom::Eq { var, a: *a, b: *b },
            (Op::App(s), [t]) => match self.funs.get(s) {
                Some(&DtFun::Tester(dt, ctor)) => DtAtom::Tester {
                    var,
                    dt,
                    ctor,
                    t: *t,
                },
                _ => return Err(format!("DT cannot interpret {}", ctx.terms.display(atom))),
            },
            _ => return Err(format!("DT cannot interpret {}", ctx.terms.display(atom))),
        };
        self.atom_of_var.insert(var, self.atoms.len());
        self.term_of_var.insert(var, atom);
        self.atoms.push(a);
        self.assigned.push(None);
        self.changed = true;
        Ok(())
    }

    fn assert_lit(&mut self, var: usize, value: bool, level: usize) {
        let Some(&idx) = self.atom_of_var.get(&var) else {
            return;
        };
        if self.assigned[idx].is_some() {
            return;
        }
        self.assigned[idx] = Some(value);
        self.trail.push((idx, value, level));
        self.changed = true;
    }

    fn backtrack(&mut self, level: usize) {
        while let Some(&(idx, _, l)) = self.trail.last() {
            if l <= level {
                break;
            }
            self.trail.pop();
            self.assigned[idx] = None;
            self.changed = true;
        }
    }

    fn check(&mut self, ctx: &mut Ctx, final_check: bool) -> Check {
        let mut out = Check::default();
        if self.atoms.is_empty() {
            return out;
        }
        let mut cc = Cc::default();
        match self.build(ctx.terms, &mut cc) {
            Err(conflict) => {
                self.last_event = Some(conflict.why.clone());
                // Keep the closure: the UI shows the classes behind the conflict.
                self.last = Some(cc);
                out.conflict = Some(conflict);
            }
            Ok(()) => {
                out.propagations = self.propagations(&cc, ctx.terms);
                if final_check && out.propagations.is_empty() {
                    if let Some((lit, why)) = self.split(&cc, ctx) {
                        self.last_event = Some(why.clone());
                        out.split = Some((lit, why));
                    }
                }
                self.last = Some(cc);
            }
        }
        out
    }

    fn model(&mut self, terms: &mut Terms, known: &mut HashMap<TermId, Value>) {
        let mut cc = Cc::default();
        if self.build(terms, &mut cc).is_err() {
            return;
        }
        let mut fresh_int = known
            .values()
            .filter_map(|v| {
                if let Value::Int(i) = v {
                    Some(*i)
                } else {
                    None
                }
            })
            .max()
            .unwrap_or(0)
            .max(0)
            + 100;
        let mut used: HashSet<Value> = HashSet::new();
        let mut val: HashMap<usize, Value> = HashMap::new();

        // Int classes: the value LIA chose for a member, else a fresh one.
        let roots: Vec<usize> = (0..cc.nodes.len()).filter(|&n| cc.find(n) == n).collect();
        for &r in &roots {
            let t = cc.nodes[r].term;
            if self.sort_dt.contains_key(&terms.sort(t)) {
                continue;
            }
            let v = cc.members[r]
                .iter()
                .find_map(|&m| known.get(&cc.nodes[m].term).cloned())
                .unwrap_or_else(|| {
                    fresh_int += 1;
                    Value::Int(fresh_int)
                });
            val.insert(r, v);
        }
        // Datatype classes: constructor classes bottom-up (acyclic), the
        // rest get fresh values distinct from everything else.
        fn eval(
            dt: &Dt,
            cc: &Cc,
            r: usize,
            val: &mut HashMap<usize, Value>,
            pending: &mut Vec<usize>,
        ) -> Option<Value> {
            if let Some(v) = val.get(&r) {
                return Some(v.clone());
            }
            let k = *cc.ctor_of.get(&r)?;
            let NKind::Ctor(d, c) = cc.nodes[k].kind else {
                return None;
            };
            let mut args = Vec::new();
            for &ch in &cc.nodes[k].children {
                match eval(dt, cc, cc.find(ch), val, pending) {
                    Some(v) => args.push(v),
                    None => {
                        pending.push(cc.find(ch));
                        return None;
                    }
                }
            }
            let v = Value::Dt(dt.ctor_name(d, c).to_string(), args);
            val.insert(r, v.clone());
            Some(v)
        }
        let mut pending = Vec::new();
        for &r in &roots {
            eval(self, &cc, r, &mut val, &mut pending);
        }
        for v in val.values() {
            used.insert(v.clone());
        }
        let mut free: Vec<usize> = roots
            .iter()
            .copied()
            .filter(|r| !val.contains_key(r) && !cc.ctor_of.contains_key(r))
            .collect();
        free.sort();
        for r in free {
            let d = self.sort_dt[&terms.sort(cc.nodes[r].term)];
            let excluded: Vec<usize> = cc
                .excluded
                .get(&r)
                .map(|v| v.iter().map(|e| e.0).collect())
                .unwrap_or_default();
            let v = self.fresh_value(d, &excluded, &mut fresh_int, &used, 0);
            used.insert(v.clone());
            val.insert(r, v);
        }
        for &r in &roots {
            let mut p = Vec::new();
            eval(self, &cc, r, &mut val, &mut p);
        }
        for (n, node) in cc.nodes.iter().enumerate() {
            if let Some(v) = val.get(&cc.find(n)) {
                known.entry(node.term).or_insert_with(|| v.clone());
            }
        }
    }

    fn snapshot(&self, terms: &Terms) -> String {
        let mut s = String::from("{\"classes\":[");
        if let Some(cc) = &self.last {
            let mut roots: Vec<usize> = (0..cc.nodes.len()).filter(|&n| cc.find(n) == n).collect();
            roots.sort_by_key(|&r| cc.members[r].iter().map(|&m| cc.nodes[m].term).min());
            for (i, r) in roots.into_iter().take(SNAPSHOT_CLASSES).enumerate() {
                if i > 0 {
                    s.push(',');
                }
                let mut members: Vec<usize> = cc.members[r].clone();
                members.sort_by_key(|&m| cc.nodes[m].term);
                s.push_str("{\"members\":[");
                for (j, m) in members.iter().enumerate() {
                    if j > 0 {
                        s.push(',');
                    }
                    json_string(&mut s, &terms.display(cc.nodes[*m].term));
                }
                s.push_str("],\"sort\":");
                json_string(&mut s, terms.sort_name(terms.sort(cc.nodes[r].term)));
                s.push_str(",\"ctor\":");
                match cc.ctor_of.get(&r) {
                    Some(&k) => json_string(&mut s, &terms.display(cc.nodes[k].term)),
                    None => s.push_str("null"),
                }
                s.push_str(",\"excluded\":[");
                if let Some(ex) = cc.excluded.get(&r) {
                    let t = cc.nodes[r].term;
                    let d = self.sort_dt.get(&terms.sort(t)).copied();
                    for (j, e) in ex.iter().enumerate() {
                        if j > 0 {
                            s.push(',');
                        }
                        let name = d
                            .map(|d| self.ctor_name(d, e.0).to_string())
                            .unwrap_or_default();
                        json_string(&mut s, &name);
                    }
                }
                s.push_str("]}");
            }
            s.push_str("],\"diseqs\":[");
            for (i, &(a, b, _)) in cc.diseqs.iter().enumerate() {
                if i > 0 {
                    s.push(',');
                }
                s.push('[');
                json_string(&mut s, &terms.display(cc.nodes[a].term));
                s.push(',');
                json_string(&mut s, &terms.display(cc.nodes[b].term));
                s.push(']');
            }
            let _ = write!(s, "],\"merges\":{}", cc.edges.len());
            // The whole closure, for the playground's step-by-step graph.
            s.push_str(",\"nodes\":[");
            for (i, n) in cc.nodes.iter().enumerate().take(SNAPSHOT_NODES) {
                if i > 0 {
                    s.push(',');
                }
                s.push_str("{\"term\":");
                json_string(&mut s, &terms.display(n.term));
                let kind = match n.kind {
                    NKind::Leaf => "leaf",
                    NKind::Ctor(..) => "ctor",
                    NKind::Sel(..) => "sel",
                };
                let _ = write!(s, ",\"kind\":\"{kind}\",\"children\":[");
                for (j, c) in n.children.iter().enumerate() {
                    if j > 0 {
                        s.push(',');
                    }
                    let _ = write!(s, "{c}");
                }
                s.push_str("]}");
            }
            s.push_str("],\"history\":[");
            let shown = |x: usize| x < SNAPSHOT_NODES;
            let mut first = true;
            for e in cc.edges.iter().filter(|e| shown(e.a) && shown(e.b)) {
                if !first {
                    s.push(',');
                }
                first = false;
                let _ = write!(
                    s,
                    "{{\"a\":{},\"b\":{},\"rule\":\"{}\",\"lits\":[",
                    e.a, e.b, e.rule
                );
                for (j, l) in e.lits.iter().enumerate() {
                    if j > 0 {
                        s.push(',');
                    }
                    let _ = write!(s, "{}", l.to_dimacs());
                }
                s.push_str("]}");
            }
            s.push_str("],\"diseqNodes\":[");
            let mut first = true;
            for &(a, b, l) in cc.diseqs.iter().filter(|d| shown(d.0) && shown(d.1)) {
                if !first {
                    s.push(',');
                }
                first = false;
                let _ = write!(s, "[{a},{b},{}]", l.to_dimacs());
            }
            s.push(']');
        } else {
            s.push_str("],\"diseqs\":[],\"merges\":0");
        }
        s.push_str(",\"datatypes\":[");
        for (i, d) in self.dts.iter().enumerate() {
            if i > 0 {
                s.push(',');
            }
            let ctors: Vec<String> = d
                .ctors
                .iter()
                .map(|c| {
                    if c.fields.is_empty() {
                        c.name.clone()
                    } else {
                        let fs: Vec<String> = c
                            .fields
                            .iter()
                            .map(|(n, srt)| format!("{n}: {}", terms.sort_name(*srt)))
                            .collect();
                        format!("{}({})", c.name, fs.join(", "))
                    }
                })
                .collect();
            s.push_str("{\"name\":");
            json_string(&mut s, &d.name);
            s.push_str(",\"ctors\":");
            json_string(&mut s, &ctors.join(" | "));
            let _ = write!(s, ",\"finite\":{}}}", d.finite);
        }
        s.push_str("],\"last\":");
        match &self.last_event {
            Some(e) => json_string(&mut s, e),
            None => s.push_str("null"),
        }
        s.push('}');
        s
    }

    fn eval_app(&self, sym: &str, args: &[Value], _terms: &Terms) -> Option<Value> {
        match *self.funs.get(sym)? {
            DtFun::Ctor(d, c) => Some(Value::Dt(self.ctor_name(d, c).to_string(), args.to_vec())),
            DtFun::Tester(d, c) => match args.first()? {
                Value::Dt(n, _) => Some(Value::Bool(n == self.ctor_name(d, c))),
                _ => None,
            },
            // A selector applied to another constructor is unspecified.
            DtFun::Sel(d, c, f) => match args.first()? {
                Value::Dt(n, fields) if n == self.ctor_name(d, c) => fields.get(f).cloned(),
                _ => None,
            },
        }
    }

    fn default_value(&self, sort: usize, _terms: &Terms) -> Option<Value> {
        let d = *self.sort_dt.get(&sort)?;
        let mut fresh = 0;
        Some(self.fresh_value(d, &[], &mut fresh, &HashSet::new(), 0))
    }

    fn take_changed(&mut self) -> bool {
        std::mem::replace(&mut self.changed, false)
    }
}
