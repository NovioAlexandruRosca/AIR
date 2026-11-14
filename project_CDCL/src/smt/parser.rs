//! SMT-LIB 2 subset: declarations, `assert`, `let`, Boolean connectives and
//! whatever symbols the registered theories own. Theory-specific commands
//! (e.g. `declare-datatypes`) are handed to the theories.

use super::sexp::{err, parse_all, Sexp, SmtError};
use super::term::{TermId, Terms, BOOL};
use super::theory::Theory;
use std::collections::HashMap;

#[derive(Debug, Clone, Default)]
pub struct Problem {
    pub logic: Option<String>,
    /// Declared constants, in declaration order.
    pub consts: Vec<TermId>,
    /// Asserted formulas (Bool-sorted terms).
    pub assertions: Vec<TermId>,
    pub check_sat: bool,
}

struct Parser<'a> {
    terms: &'a mut Terms,
    theories: &'a mut [Box<dyn Theory>],
    consts: HashMap<String, TermId>,
    /// `define-fun` macros without arguments.
    macros: HashMap<String, TermId>,
    scopes: Vec<HashMap<String, TermId>>,
}

pub fn parse_problem(
    text: &str,
    terms: &mut Terms,
    theories: &mut [Box<dyn Theory>],
) -> Result<Problem, SmtError> {
    let cmds = parse_all(text)?;
    let mut p = Parser {
        terms,
        theories,
        consts: HashMap::new(),
        macros: HashMap::new(),
        scopes: Vec::new(),
    };
    let mut problem = Problem::default();
    for cmd in &cmds {
        p.command(cmd, &mut problem)?;
    }
    if problem.assertions.is_empty() && !problem.check_sat {
        return err(
            0,
            "no (assert ...) or (check-sat) found: is this an SMT-LIB file?",
        );
    }
    Ok(problem)
}

impl<'a> Parser<'a> {
    fn command(&mut self, cmd: &Sexp, problem: &mut Problem) -> Result<(), SmtError> {
        let line = cmd.line();
        let items = match cmd.list() {
            Some(l) if !l.is_empty() => l,
            _ => {
                return err(
                    line,
                    format!("expected a command in parentheses, got {cmd}"),
                )
            }
        };
        let head = match items[0].atom() {
            Some(h) => h,
            None => return err(line, "command name expected"),
        };
        match head {
            "set-logic" => problem.logic = items.get(1).and_then(|s| s.atom()).map(String::from),
            "set-info" | "set-option" | "get-model" | "get-info" | "exit" | "echo"
            | "get-assertions" => {}
            "check-sat" => problem.check_sat = true,
            "declare-const" => {
                if items.len() != 3 {
                    return err(line, "usage: (declare-const name Sort)");
                }
                let name = self.symbol(&items[1])?;
                let sort = self.sort(&items[2])?;
                self.declare(name, sort, line, problem)?;
            }
            "declare-fun" => {
                if items.len() != 4 {
                    return err(line, "usage: (declare-fun name () Sort)");
                }
                let name = self.symbol(&items[1])?;
                if items[2].list().is_none_or(|l| !l.is_empty()) {
                    return err(
                        line,
                        format!("'{name}' takes arguments: uninterpreted functions are not supported (only constants)"),
                    );
                }
                let sort = self.sort(&items[3])?;
                self.declare(name, sort, line, problem)?;
            }
            "define-fun" => {
                if items.len() != 5 || items[2].list().is_none_or(|l| !l.is_empty()) {
                    return err(
                        line,
                        "only argument-free (define-fun name () Sort term) is supported",
                    );
                }
                let name = self.symbol(&items[1])?;
                let sort = self.sort(&items[3])?;
                let body = self.term(&items[4])?;
                if self.terms.sort(body) != sort {
                    return err(
                        line,
                        format!(
                            "define-fun '{name}': body has sort {}",
                            self.terms.sort_name(self.terms.sort(body))
                        ),
                    );
                }
                self.macros.insert(name, body);
            }
            "assert" => {
                if items.len() != 2 {
                    return err(line, "usage: (assert formula)");
                }
                let t = self.term(&items[1])?;
                if self.terms.sort(t) != BOOL {
                    return err(
                        line,
                        format!(
                            "assert needs a Bool formula, got sort {}",
                            self.terms.sort_name(self.terms.sort(t))
                        ),
                    );
                }
                problem.assertions.push(t);
            }
            "push" | "pop" | "reset" | "check-sat-assuming" => {
                return err(
                    line,
                    format!("'{head}' is not supported (single check-sat only)"),
                );
            }
            _ => {
                for me in 0..self.theories.len() {
                    if self.theories[me].command(cmd, self.terms, me)? {
                        return Ok(());
                    }
                }
                return err(line, format!("unknown or unsupported command '{head}'"));
            }
        }
        Ok(())
    }

    fn declare(
        &mut self,
        name: String,
        sort: usize,
        line: usize,
        problem: &mut Problem,
    ) -> Result<(), SmtError> {
        if self.consts.contains_key(&name) || self.terms.fun_owner(&name).is_some() {
            return err(line, format!("'{name}' is already declared"));
        }
        let v = self.terms.var(&name, sort);
        self.consts.insert(name, v);
        problem.consts.push(v);
        Ok(())
    }

    fn symbol(&self, s: &Sexp) -> Result<String, SmtError> {
        match s.atom() {
            Some(a) if !a.starts_with('"') => Ok(a.to_string()),
            _ => err(s.line(), format!("symbol expected, got {s}")),
        }
    }

    fn sort(&self, s: &Sexp) -> Result<usize, SmtError> {
        let name = match s.atom() {
            Some(a) => a,
            None => return err(s.line(), format!("parametric sort {s} is not supported")),
        };
        match self.terms.sort_named(name) {
            Some(id) => Ok(id),
            None => err(s.line(), format!("unknown sort '{name}'")),
        }
    }

    fn lookup(&self, name: &str) -> Option<TermId> {
        for scope in self.scopes.iter().rev() {
            if let Some(&t) = scope.get(name) {
                return Some(t);
            }
        }
        self.macros
            .get(name)
            .or_else(|| self.consts.get(name))
            .copied()
    }

    fn term(&mut self, s: &Sexp) -> Result<TermId, SmtError> {
        let line = s.line();
        match s {
            Sexp::Atom(a, _) => self.atom_term(a, line),
            Sexp::List(items, _) => {
                if items.is_empty() {
                    return err(line, "empty term ()");
                }
                let head = match &items[0] {
                    Sexp::Atom(h, _) => h.clone(),
                    // ((_ is C) t): indexed tester
                    Sexp::List(idx, _) => match idx.as_slice() {
                        [Sexp::Atom(u, _), Sexp::Atom(is, _), Sexp::Atom(c, _)]
                            if u == "_" && is == "is" =>
                        {
                            format!("is-{c}")
                        }
                        _ => return err(line, format!("unsupported function head {}", items[0])),
                    },
                };
                match head.as_str() {
                    "let" => return self.let_term(items, line),
                    "!" => {
                        return match items.get(1) {
                            Some(t) => self.term(t),
                            None => err(line, "empty annotation (!)"),
                        }
                    }
                    "_" => return err(line, format!("unsupported indexed term {s}")),
                    _ => {}
                }
                let mut args = Vec::with_capacity(items.len() - 1);
                for a in &items[1..] {
                    args.push(self.term(a)?);
                }
                self.app(&head, args, line)
            }
        }
    }

    fn atom_term(&mut self, a: &str, line: usize) -> Result<TermId, SmtError> {
        if a == "true" {
            return Ok(self.terms.bool_const(true));
        }
        if a == "false" {
            return Ok(self.terms.bool_const(false));
        }
        if a.chars().all(|c| c.is_ascii_digit()) && !a.is_empty() {
            let n: i128 = match a.parse() {
                Ok(n) => n,
                Err(_) => return err(line, format!("numeral {a} is too large")),
            };
            return match self.terms.sort_named("Int") {
                Some(int) => Ok(self.terms.num(n, int)),
                None => err(line, "numerals need a theory that provides Int"),
            };
        }
        if let Some(t) = self.lookup(a) {
            return Ok(t);
        }
        if let Some(owner) = self.terms.fun_owner(a) {
            return self.theories[owner]
                .mk_app(a, Vec::new(), self.terms)
                .or_else(|m| err(line, m));
        }
        err(
            line,
            format!("unknown symbol '{a}' (declare it with declare-const)"),
        )
    }

    fn let_term(&mut self, items: &[Sexp], line: usize) -> Result<TermId, SmtError> {
        if items.len() != 3 {
            return err(line, "usage: (let ((x t) ...) body)");
        }
        let bindings = match items[1].list() {
            Some(b) => b,
            None => return err(line, "let bindings must be a list"),
        };
        // Parallel let: all bound terms are read in the outer scope.
        let mut scope = HashMap::new();
        for b in bindings {
            match b.list() {
                Some([name, t]) => {
                    let n = self.symbol(name)?;
                    let v = self.term(t)?;
                    scope.insert(n, v);
                }
                _ => return err(b.line(), "let binding must be (name term)"),
            }
        }
        self.scopes.push(scope);
        let body = self.term(&items[2]);
        self.scopes.pop();
        body
    }

    fn expect_bool(&self, args: &[TermId], op: &str, line: usize) -> Result<(), SmtError> {
        for &a in args {
            if self.terms.sort(a) != BOOL {
                return err(
                    line,
                    format!(
                        "'{op}' expects Bool arguments, got {} : {}",
                        self.terms.display(a),
                        self.terms.sort_name(self.terms.sort(a))
                    ),
                );
            }
        }
        Ok(())
    }

    fn same_sort(&self, args: &[TermId], op: &str, line: usize) -> Result<(), SmtError> {
        if args.len() < 2 {
            return err(line, format!("'{op}' needs at least two arguments"));
        }
        let s = self.terms.sort(args[0]);
        for &a in &args[1..] {
            if self.terms.sort(a) != s {
                return err(
                    line,
                    format!(
                        "'{op}' mixes sorts {} and {}",
                        self.terms.sort_name(s),
                        self.terms.sort_name(self.terms.sort(a))
                    ),
                );
            }
        }
        Ok(())
    }

    /// `a = b`, with constant-constant equalities in a canonical order so
    /// `x = y` and `y = x` are the same atom.
    fn mk_eq(&mut self, a: TermId, b: TermId) -> TermId {
        let (a, b) = if self.terms.is_var(a) && self.terms.is_var(b) && b < a {
            (b, a)
        } else {
            (a, b)
        };
        self.terms.app("=", vec![a, b], BOOL)
    }

    fn app(&mut self, head: &str, args: Vec<TermId>, line: usize) -> Result<TermId, SmtError> {
        match head {
            "not" => {
                if args.len() != 1 {
                    return err(line, "'not' takes one argument");
                }
                self.expect_bool(&args, head, line)?;
                Ok(self.terms.app("not", args, BOOL))
            }
            "and" | "or" => {
                self.expect_bool(&args, head, line)?;
                Ok(match args.len() {
                    0 => self.terms.bool_const(head == "and"),
                    1 => args[0],
                    _ => self.terms.app(head, args, BOOL),
                })
            }
            "=>" => {
                if args.len() < 2 {
                    return err(line, "'=>' needs at least two arguments");
                }
                self.expect_bool(&args, head, line)?;
                // right associative
                let mut acc = *args.last().unwrap();
                for &a in args[..args.len() - 1].iter().rev() {
                    acc = self.terms.app("=>", vec![a, acc], BOOL);
                }
                Ok(acc)
            }
            "xor" => {
                if args.len() < 2 {
                    return err(line, "'xor' needs at least two arguments");
                }
                self.expect_bool(&args, head, line)?;
                let mut acc = args[0];
                for &a in &args[1..] {
                    acc = self.terms.app("xor", vec![acc, a], BOOL);
                }
                Ok(acc)
            }
            "=" => {
                self.same_sort(&args, head, line)?;
                let pairs: Vec<TermId> = args.windows(2).map(|w| self.mk_eq(w[0], w[1])).collect();
                Ok(if pairs.len() == 1 {
                    pairs[0]
                } else {
                    self.terms.app("and", pairs, BOOL)
                })
            }
            "distinct" => {
                self.same_sort(&args, head, line)?;
                let mut parts = Vec::new();
                for i in 0..args.len() {
                    for j in i + 1..args.len() {
                        let eq = self.mk_eq(args[i], args[j]);
                        parts.push(self.terms.app("not", vec![eq], BOOL));
                    }
                }
                Ok(if parts.len() == 1 {
                    parts[0]
                } else {
                    self.terms.app("and", parts, BOOL)
                })
            }
            "ite" => {
                if args.len() != 3 {
                    return err(line, "'ite' takes three arguments");
                }
                self.expect_bool(&args[..1], head, line)?;
                self.same_sort(&args[1..], head, line)?;
                if self.terms.sort(args[1]) != BOOL {
                    return err(line, "ite over non-Boolean terms is not supported; write the case split with Boolean connectives");
                }
                Ok(self.terms.app("ite", args, BOOL))
            }
            _ => {
                if self.lookup(head).is_some() {
                    return err(line, format!("'{head}' is a constant, not a function"));
                }
                match self.terms.fun_owner(head) {
                    Some(owner) => self.theories[owner]
                        .mk_app(head, args, self.terms)
                        .or_else(|m| err(line, m)),
                    None => err(line, format!("unknown function '{head}'")),
                }
            }
        }
    }
}

/// Is this text SMT-LIB (as opposed to DIMACS)? The first non-comment
/// character of SMT-LIB is '('.
pub fn looks_like_smtlib(text: &str) -> bool {
    for line in text.lines() {
        let l = line.trim();
        if l.is_empty() || l.starts_with(';') {
            continue;
        }
        return l.starts_with('(');
    }
    false
}
