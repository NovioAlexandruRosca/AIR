mod server;

use cdcl::solver::{verify_model, Solver, Status};
use cdcl::trace::Tracer;
use cdcl::{parse, run_json, Limits, Timing, DEFAULT_TRACE_LIMIT};
use std::process::ExitCode;
use std::time::{Duration, Instant};

/// Default per-request time limit in `serve` mode.
const SERVE_TIMEOUT: Duration = Duration::from_secs(60);

const USAGE: &str = "\
CDCL SAT solver (MOMS decisions, First-UIP learning, backjumping) and
CDCL(T) SMT solver for LIA + algebraic datatypes (Nelson–Oppen)

USAGE:
  cdcl <file.cnf|file.smt2> [--trace <out.json>] [--trace-limit <N>] [--max-conflicts <N>] [--timeout <T>]
  cdcl serve [--port <P>] [--trace-limit <N>] [--max-conflicts <N>] [--timeout <T>]

  <file>              DIMACS CNF, or SMT-LIB 2 (.smt2 or text starting with '(');
                      '-' reads stdin
  --trace <out.json>  write the solver's step-by-step trace as JSON
  --trace-limit <N>   stop recording after N events (default 20000)
  --max-conflicts <N> give up (s UNKNOWN) after N conflicts
  --timeout <T>       give up (s UNKNOWN) after T: 30, 30s, 500ms, 2m, or none
                      (serve default: 60s)
  --no-reduce         never delete learned clauses (by default the worse half is
                      deleted once 8000+ are kept; never happens inside a trace)
  serve               start the DPLL(T) playground on http://127.0.0.1:<P>/ (default 8080)

Exit code: 10 = SAT, 20 = UNSAT, 0 = UNKNOWN, 1 = error.";

struct Args {
    serve: bool,
    input: Option<String>,
    trace: Option<String>,
    trace_limit: usize,
    max_conflicts: Option<u64>,
    /// None = flag not given, Some(None) = explicitly unlimited.
    timeout: Option<Option<Duration>>,
    no_reduce: bool,
    port: u16,
}

fn parse_timeout(s: &str) -> Result<Option<Duration>, String> {
    let bad = || format!("--timeout expects e.g. 30, 30s, 500ms, 2m or none, got {s:?}");
    if s == "none" || s == "0" {
        return Ok(None);
    }
    let (num, scale) = if let Some(n) = s.strip_suffix("ms") {
        (n, 0.001)
    } else if let Some(n) = s.strip_suffix('s') {
        (n, 1.0)
    } else if let Some(n) = s.strip_suffix('m') {
        (n, 60.0)
    } else {
        (s, 1.0)
    };
    let secs = num.parse::<f64>().map_err(|_| bad())? * scale;
    if !(secs.is_finite() && secs > 0.0) {
        return Err(bad());
    }
    Ok(Some(Duration::from_secs_f64(secs)))
}

fn parse_args() -> Result<Args, String> {
    let mut args = Args {
        serve: false,
        input: None,
        trace: None,
        trace_limit: DEFAULT_TRACE_LIMIT,
        max_conflicts: None,
        timeout: None,
        no_reduce: false,
        port: 8080,
    };
    let mut it = std::env::args().skip(1);
    while let Some(a) = it.next() {
        let mut value = |name: &str| it.next().ok_or_else(|| format!("{name} needs a value"));
        match a.as_str() {
            "-h" | "--help" => return Err(String::new()),
            "serve" if args.input.is_none() && !args.serve => args.serve = true,
            "--trace" => args.trace = Some(value("--trace")?),
            "--trace-limit" => {
                args.trace_limit = value("--trace-limit")?
                    .parse()
                    .map_err(|_| "--trace-limit expects a number")?
            }
            "--max-conflicts" => {
                args.max_conflicts = Some(
                    value("--max-conflicts")?
                        .parse()
                        .map_err(|_| "--max-conflicts expects a number")?,
                )
            }
            "--timeout" => args.timeout = Some(parse_timeout(&value("--timeout")?)?),
            "--no-reduce" => args.no_reduce = true,
            "--port" => {
                args.port = value("--port")?
                    .parse()
                    .map_err(|_| "--port expects a port number")?
            }
            _ if a.starts_with("--") => return Err(format!("unknown option {a}")),
            _ if args.input.is_none() && !args.serve => args.input = Some(a),
            _ => return Err(format!("unexpected argument {a}")),
        }
    }
    if !args.serve && args.input.is_none() {
        return Err(String::new());
    }
    Ok(args)
}

fn main() -> ExitCode {
    let args = match parse_args() {
        Ok(a) => a,
        Err(msg) => {
            if !msg.is_empty() {
                eprintln!("error: {msg}\n");
            }
            eprintln!("{USAGE}");
            return ExitCode::from(1);
        }
    };

    if args.serve {
        // The web UI runs on small teaching instances; cap runaway solves.
        let limits = Limits {
            max_conflicts: args.max_conflicts,
            timeout: args.timeout.unwrap_or(Some(SERVE_TIMEOUT)),
            cancel: None,
            no_reduce: args.no_reduce,
        };
        return match server::serve(args.port, args.trace_limit, limits) {
            Ok(()) => ExitCode::SUCCESS,
            Err(e) => {
                eprintln!("error: {e}");
                ExitCode::from(1)
            }
        };
    }

    let path = args.input.clone().unwrap();
    let text = if path == "-" {
        let mut s = String::new();
        if let Err(e) = std::io::Read::read_to_string(&mut std::io::stdin(), &mut s) {
            eprintln!("error: reading stdin: {e}");
            return ExitCode::from(1);
        }
        s
    } else {
        match std::fs::read_to_string(&path) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("error: cannot read {path}: {e}");
                return ExitCode::from(1);
            }
        }
    };

    if path.ends_with(".smt2") || cdcl::smt::looks_like_smtlib(&text) {
        return run_smt(&text, &path, &args);
    }

    let parse_start = Instant::now();
    let parsed = parse(&text);
    let parse_ms = parse_start.elapsed().as_secs_f64() * 1000.0;
    let cnf = match parsed {
        Ok(c) => c,
        Err(e) => {
            eprintln!("error: {path}: {e}");
            return ExitCode::from(1);
        }
    };
    println!(
        "c parsed {} variables, {} clauses",
        cnf.num_vars,
        cnf.clauses.len()
    );
    for w in &cnf.warnings {
        println!("c warning: {w}");
    }

    let tracer = if args.trace.is_some() {
        Tracer::with_limit(args.trace_limit)
    } else {
        Tracer::disabled()
    };
    let start = Instant::now();
    let mut solver = Solver::with_tracer(&cnf, tracer);
    solver.max_conflicts = args.max_conflicts;
    solver.deadline = args.timeout.flatten().map(|t| start + t);
    solver.reduce_db = !args.no_reduce;
    let status = solver.solve();
    let elapsed = start.elapsed();

    let st = &solver.stats;
    println!(
        "c decisions {}  propagations {}  conflicts {}  learned {}  deleted {}  max level {}",
        st.decisions, st.propagations, st.conflicts, st.learned, st.deleted, st.max_level
    );
    println!(
        "c time {:.3} ms (parse {:.3} ms){}",
        elapsed.as_secs_f64() * 1000.0,
        parse_ms,
        if args.trace.is_some() {
            ", tracing on"
        } else {
            ""
        }
    );

    if let Some(out) = &args.trace {
        // This run recorded the trace, so its time includes tracing overhead.
        let timing = Timing {
            parse_ms,
            solve_ms: elapsed.as_secs_f64() * 1000.0,
            solve_untraced_ms: None,
        };
        let json = run_json(&cnf, &solver, status, &timing);
        if let Err(e) = std::fs::write(out, json) {
            eprintln!("error: cannot write {out}: {e}");
            return ExitCode::from(1);
        }
        let note = if solver.tracer.truncated {
            " (truncated)"
        } else {
            ""
        };
        println!(
            "c trace: {} events written to {out}{note}",
            solver.tracer.events.len()
        );
    }

    match status {
        Status::Sat => {
            if !verify_model(&cnf, solver.model()) {
                eprintln!("c ERROR: model does not satisfy the formula");
                return ExitCode::from(1);
            }
            println!("c model verified against all {} clauses", cnf.clauses.len());
            println!("s SATISFIABLE");
            let mut line = String::from("v");
            for x in solver.model_dimacs() {
                let tok = format!(" {x}");
                if line.len() + tok.len() > 78 {
                    println!("{line}");
                    line = String::from("v");
                }
                line.push_str(&tok);
            }
            println!("{line} 0");
            ExitCode::from(10)
        }
        Status::Unsat => {
            println!("s UNSATISFIABLE");
            ExitCode::from(20)
        }
        Status::Unknown => {
            if let Some(r) = solver.stop_reason {
                println!("c stopped: {}", r.as_str());
            }
            println!("s UNKNOWN");
            ExitCode::SUCCESS
        }
    }
}

/// SMT-LIB input: CDCL(T) with the LIA and DT theories.
fn run_smt(text: &str, path: &str, args: &Args) -> ExitCode {
    let limits = Limits {
        max_conflicts: args.max_conflicts,
        timeout: args.timeout.flatten(),
        cancel: None,
        no_reduce: args.no_reduce,
    };
    let trace_limit = args.trace.as_ref().map(|_| args.trace_limit);
    let r = match cdcl::smt::solve(text, trace_limit, &limits) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("error: {path}: {e}");
            return ExitCode::from(1);
        }
    };
    let p = &r.prepared;
    let comb = p.comb.borrow();
    let names: Vec<&str> = comb.theories.iter().map(|t| t.name()).collect();
    println!(
        "; {} assertions, theories {}, {} Boolean variables, {} clauses",
        p.problem.assertions.len(),
        names.join(" + "),
        p.prep.cnf.num_vars,
        p.prep.cnf.clauses.len()
    );
    for &d in &p.prep.definitions {
        println!("; purification: {}", comb.terms.display(d));
    }
    if !comb.shared.is_empty() {
        let shared: Vec<String> = comb.shared.iter().map(|&t| comb.terms.display(t)).collect();
        println!("; shared constants (Nelson–Oppen): {}", shared.join(", "));
    }
    let st = &r.solver.stats;
    println!(
        "; decisions {}  propagations {}  conflicts {}  theory propagations {}  theory conflicts {}  theory splits {}",
        st.decisions, st.propagations, st.conflicts, st.theory_propagations, st.theory_conflicts, st.theory_splits
    );
    println!(
        "; time {:.3} ms (parse {:.3} ms)",
        r.timing.solve_ms, r.timing.parse_ms
    );
    drop(comb);

    if let Some(out) = &args.trace {
        if let Err(e) = std::fs::write(out, cdcl::smt::result_json(&r)) {
            eprintln!("error: cannot write {out}: {e}");
            return ExitCode::from(1);
        }
        println!(
            "; trace: {} events written to {out}",
            r.solver.tracer.events.len()
        );
    }

    match r.status {
        Status::Sat => {
            if r.verified != Some(true) {
                eprintln!("; ERROR: the model does not satisfy every assertion");
                return ExitCode::from(1);
            }
            println!("sat");
            println!("{}", cdcl::smt::model_smtlib(&r.model));
            println!(
                "; model verified against all {} assertions",
                p.problem.assertions.len()
            );
            ExitCode::from(10)
        }
        Status::Unsat => {
            println!("unsat");
            ExitCode::from(20)
        }
        Status::Unknown => {
            if let Some(why) = r.solver.incomplete_reason.as_ref() {
                println!("; {why}");
            } else if let Some(s) = r.solver.stop_reason {
                println!("; stopped: {}", s.as_str());
            }
            println!("unknown");
            ExitCode::SUCCESS
        }
    }
}
