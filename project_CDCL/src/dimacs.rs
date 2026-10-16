//! DIMACS CNF parser (the SAT Competition input format).
//!
//! Accepted:
//! - `c ...` comment lines (anywhere),
//! - one `p cnf <vars> <clauses>` header before the first clause,
//! - clauses as whitespace-separated non-zero integers terminated by `0`,
//!   possibly spanning several lines or sharing a line,
//! - a `%` line, which ends the formula (used by the SATLIB benchmark files).
//!
//! Recoverable irregularities (clause count differs from the header, a last
//! clause without its terminating `0`) are reported as warnings; everything
//! else is a `ParseError` with a line number.

use crate::lit::Lit;
use std::fmt;

#[derive(Debug, Clone)]
pub struct Cnf {
    pub num_vars: usize,
    pub clauses: Vec<Vec<Lit>>,
    pub warnings: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    pub line: usize,
    pub message: String,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.line == 0 {
            write!(f, "{}", self.message)
        } else {
            write!(f, "line {}: {}", self.line, self.message)
        }
    }
}

impl std::error::Error for ParseError {}

fn err(line: usize, message: impl Into<String>) -> ParseError {
    ParseError {
        line,
        message: message.into(),
    }
}

pub fn parse(input: &str) -> Result<Cnf, ParseError> {
    let mut header: Option<(usize, usize)> = None;
    let mut clauses: Vec<Vec<Lit>> = Vec::new();
    let mut current: Vec<Lit> = Vec::new();
    let mut warnings = Vec::new();

    for (i, raw) in input.lines().enumerate() {
        let line_no = i + 1;
        let line = raw.trim();
        if line.is_empty() || line.starts_with('c') {
            continue;
        }
        if line.starts_with('%') {
            break;
        }
        if line.starts_with('p') {
            if header.is_some() {
                return Err(err(line_no, "duplicate 'p cnf' header"));
            }
            let parts: Vec<&str> = line.split_whitespace().collect();
            if parts.len() != 4 || parts[0] != "p" || parts[1] != "cnf" {
                return Err(err(
                    line_no,
                    format!("malformed header '{line}', expected 'p cnf <vars> <clauses>'"),
                ));
            }
            let vars = parts[2]
                .parse::<usize>()
                .map_err(|_| err(line_no, format!("invalid variable count '{}'", parts[2])))?;
            let ncl = parts[3]
                .parse::<usize>()
                .map_err(|_| err(line_no, format!("invalid clause count '{}'", parts[3])))?;
            header = Some((vars, ncl));
            continue;
        }

        let (num_vars, _) = header.ok_or_else(|| {
            err(line_no, "clause found before the 'p cnf <vars> <clauses>' header")
        })?;

        for tok in line.split_whitespace() {
            let x: i64 = tok
                .parse()
                .map_err(|_| err(line_no, format!("'{tok}' is not an integer literal")))?;
            if x == 0 {
                clauses.push(std::mem::take(&mut current));
                continue;
            }
            if x.unsigned_abs() as usize > num_vars {
                return Err(err(
                    line_no,
                    format!("literal {x} uses a variable above the declared {num_vars}"),
                ));
            }
            current.push(Lit::from_dimacs(x));
        }
    }

    let (num_vars, declared) =
        header.ok_or_else(|| err(0, "missing 'p cnf <vars> <clauses>' header"))?;

    if !current.is_empty() {
        warnings.push("last clause was not terminated by 0; accepted anyway".to_string());
        clauses.push(current);
    }
    if clauses.len() != declared {
        warnings.push(format!(
            "header declares {declared} clauses but {} were read",
            clauses.len()
        ));
    }

    Ok(Cnf {
        num_vars,
        clauses,
        warnings,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn d(c: &[Lit]) -> Vec<i64> {
        c.iter().map(|l| l.to_dimacs()).collect()
    }

    #[test]
    fn parses_example_from_spec() {
        let cnf = parse(
            "c This is a comment line (starts with 'c')\nc Another comment\np cnf 5 3\n1 -5 4 0\n-1 5 3 4 0\n-3 -4 0\n",
        )
        .unwrap();
        assert_eq!(cnf.num_vars, 5);
        assert_eq!(cnf.clauses.len(), 3);
        assert_eq!(d(&cnf.clauses[0]), vec![1, -5, 4]);
        assert_eq!(d(&cnf.clauses[1]), vec![-1, 5, 3, 4]);
        assert_eq!(d(&cnf.clauses[2]), vec![-3, -4]);
        assert!(cnf.warnings.is_empty());
    }

    #[test]
    fn clauses_may_span_and_share_lines() {
        let cnf = parse("p cnf 3 3\n1 2\n3 0 -1 0\n-2\n-3 0\n").unwrap();
        assert_eq!(d(&cnf.clauses[0]), vec![1, 2, 3]);
        assert_eq!(d(&cnf.clauses[1]), vec![-1]);
        assert_eq!(d(&cnf.clauses[2]), vec![-2, -3]);
    }

    #[test]
    fn satlib_percent_terminator() {
        let cnf = parse("p cnf 2 1\n1 2 0\n%\n0\n\n").unwrap();
        assert_eq!(cnf.clauses.len(), 1);
        assert!(cnf.warnings.is_empty());
    }

    #[test]
    fn empty_clause_is_kept() {
        let cnf = parse("p cnf 1 2\n1 0\n0\n").unwrap();
        assert_eq!(cnf.clauses.len(), 2);
        assert!(cnf.clauses[1].is_empty());
    }

    #[test]
    fn warnings_for_count_mismatch_and_missing_terminator() {
        let cnf = parse("p cnf 2 5\n1 2 0\n-1").unwrap();
        assert_eq!(cnf.clauses.len(), 2);
        assert_eq!(cnf.warnings.len(), 2);
    }

    #[test]
    fn errors() {
        assert!(parse("1 2 0\n").unwrap_err().message.contains("before"));
        assert!(parse("c only comments\n").unwrap_err().message.contains("missing"));
        assert_eq!(parse("p cnf 2 1\n1 3 0\n").unwrap_err().line, 2);
        assert!(parse("p cnf 2 1\n1 x 0\n").unwrap_err().message.contains("'x'"));
        assert!(parse("p cnf 2\n").unwrap_err().message.contains("malformed"));
        assert!(parse("p cnf 2 1\np cnf 2 1\n").unwrap_err().message.contains("duplicate"));
    }
}
