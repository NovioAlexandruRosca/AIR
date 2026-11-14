//! Minimal std-only HTTP server for the playground.
//!
//! - `GET /` (or `/playground`) -> the DPLL(T) playground, a React app built from
//!   `playground/` into `ui/playground/` (`/playground.js`, `/playground.css`)
//! - `POST /api/solve`       -> body: DIMACS or SMT-LIB text, response: trace JSON
//! - `POST /api/playground`  -> body: a `DECISIONS l1 l2 ...` line, then the formula;
//!   response: the state after replaying those decisions
//!
//! Binds to 127.0.0.1 only. Each connection gets its own thread: browsers
//! open idle "preconnect" sockets, and a single-threaded loop would sit on
//! one of those while the real request waits behind it.

use cdcl::trace::json_string;
use cdcl::{parse, solve_to_json, Limits};
use std::io::{self, Read, Write};
use std::net::{TcpListener, TcpStream};
use std::time::{Duration, Instant};

const PLAYGROUND_HTML: &str = include_str!("../ui/playground/index.html");
const PLAYGROUND_JS: &str = include_str!("../ui/playground/playground.js");
const PLAYGROUND_CSS: &str = include_str!("../ui/playground/playground.css");
const MAX_HEADER: usize = 64 * 1024;
const MAX_BODY: usize = 64 * 1024 * 1024;

pub fn serve(port: u16, trace_limit: usize, limits: Limits) -> io::Result<()> {
    let listener = TcpListener::bind(("127.0.0.1", port))?;
    println!("DPLL(T) playground: http://127.0.0.1:{port}/   (Ctrl+C to stop)");
    for stream in listener.incoming() {
        match stream {
            Ok(s) => {
                let limits = limits.clone();
                std::thread::spawn(move || {
                    if let Err(e) = handle(s, trace_limit, &limits) {
                        // Idle preconnects time out here; not worth reporting.
                        if e.kind() != io::ErrorKind::WouldBlock
                            && e.kind() != io::ErrorKind::TimedOut
                        {
                            eprintln!("request failed: {e}");
                        }
                    }
                });
            }
            Err(e) => eprintln!("connection failed: {e}"),
        }
    }
    Ok(())
}

fn handle(mut stream: TcpStream, trace_limit: usize, limits: &Limits) -> io::Result<()> {
    stream.set_read_timeout(Some(Duration::from_secs(30)))?;

    let mut buf = Vec::new();
    let mut chunk = [0u8; 8192];
    let header_end = loop {
        if let Some(pos) = buf.windows(4).position(|w| w == b"\r\n\r\n") {
            break pos + 4;
        }
        if buf.len() > MAX_HEADER {
            return respond(
                &mut stream,
                "431 Request Header Fields Too Large",
                "text/plain",
                b"headers too large",
            );
        }
        let n = stream.read(&mut chunk)?;
        if n == 0 {
            return Ok(());
        }
        buf.extend_from_slice(&chunk[..n]);
    };

    let head = String::from_utf8_lossy(&buf[..header_end]).to_string();
    let mut lines = head.lines();
    let request_line = lines.next().unwrap_or("");
    let mut parts = request_line.split_whitespace();
    let method = parts.next().unwrap_or("");
    let path = parts.next().unwrap_or("/").split('?').next().unwrap_or("/");
    let content_length = lines
        .filter_map(|l| l.split_once(':'))
        .find(|(k, _)| k.trim().eq_ignore_ascii_case("content-length"))
        .and_then(|(_, v)| v.trim().parse::<usize>().ok())
        .unwrap_or(0);

    match (method, path) {
        ("GET", "/" | "/index.html" | "/playground" | "/playground.html") => respond(
            &mut stream,
            "200 OK",
            "text/html; charset=utf-8",
            PLAYGROUND_HTML.as_bytes(),
        ),
        ("GET", "/playground.js") => respond(
            &mut stream,
            "200 OK",
            "text/javascript; charset=utf-8",
            PLAYGROUND_JS.as_bytes(),
        ),
        ("GET", "/playground.css") => respond(
            &mut stream,
            "200 OK",
            "text/css; charset=utf-8",
            PLAYGROUND_CSS.as_bytes(),
        ),
        ("POST", "/api/solve") | ("POST", "/api/playground") => {
            if content_length > MAX_BODY {
                return respond(
                    &mut stream,
                    "413 Payload Too Large",
                    "text/plain",
                    b"input too large",
                );
            }
            let mut body = buf[header_end..].to_vec();
            while body.len() < content_length {
                let n = stream.read(&mut chunk)?;
                if n == 0 {
                    break;
                }
                body.extend_from_slice(&chunk[..n]);
            }
            let text = String::from_utf8_lossy(&body).to_string();
            let result = if path == "/api/playground" {
                guarded(|| playground(&text))
            } else if cdcl::smt::looks_like_smtlib(&text) {
                guarded(|| {
                    cdcl::smt::solve_to_json(&text, trace_limit, limits).map_err(|e| e.to_string())
                })
            } else {
                guarded(|| dimacs(&text, trace_limit, limits))
            };
            match result {
                Ok(json) => respond(&mut stream, "200 OK", "application/json", json.as_bytes()),
                Err(e) => {
                    let mut json = String::from(r#"{"error":"#);
                    json_string(&mut json, &e);
                    json.push('}');
                    respond(
                        &mut stream,
                        "400 Bad Request",
                        "application/json",
                        json.as_bytes(),
                    )
                }
            }
        }
        _ => respond(&mut stream, "404 Not Found", "text/plain", b"not found"),
    }
}

/// Run a request handler; a panic (e.g. arithmetic overflow) becomes an
/// error message instead of a dropped connection.
fn guarded(f: impl FnOnce() -> Result<String, String>) -> Result<String, String> {
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)) {
        Ok(r) => r,
        Err(p) => Err(format!(
            "solver error: {}",
            p.downcast_ref::<&str>()
                .map(|s| s.to_string())
                .or_else(|| p.downcast_ref::<String>().cloned())
                .unwrap_or_else(|| "internal panic".into())
        )),
    }
}

fn dimacs(text: &str, trace_limit: usize, limits: &Limits) -> Result<String, String> {
    let start = Instant::now();
    let cnf = parse(text).map_err(|e| e.to_string())?;
    let parse_ms = start.elapsed().as_secs_f64() * 1000.0;
    Ok(solve_to_json(&cnf, trace_limit, limits, parse_ms))
}

/// Body: a `DECISIONS 3 -5 ...` line, optionally a `LEMMAS 1 -2 0 3 4 0` line
/// (clauses kept from earlier conflicts), optionally an `OPTIONS [no-theory-propagation] [finish]`
/// line, then the formula.
fn playground(body: &str) -> Result<String, String> {
    let (first, mut rest) = body.split_once('\n').unwrap_or((body, ""));
    // `3 -5 u7 2`: decisions, and `u<lit>` = propagate the unit clause forcing lit
    let actions: Vec<(bool, i64)> = match first.trim().strip_prefix("DECISIONS") {
        Some(list) => list
            .split_whitespace()
            .filter_map(|t| match t.strip_prefix('u') {
                Some(l) => l.parse().ok().map(|l| (true, l)),
                None => t.parse().ok().map(|l| (false, l)),
            })
            .collect(),
        None => return Err("playground request must start with a DECISIONS line".into()),
    };
    let mut lemmas: Vec<Vec<i64>> = Vec::new();
    if let Some((line, after)) = rest.split_once('\n') {
        if let Some(list) = line.trim().strip_prefix("LEMMAS") {
            let mut cur = Vec::new();
            for x in list
                .split_whitespace()
                .filter_map(|t| t.parse::<i64>().ok())
            {
                if x == 0 {
                    lemmas.push(std::mem::take(&mut cur));
                } else {
                    cur.push(x);
                }
            }
            rest = after;
        }
    }
    let mut theory_propagation = true;
    let mut finish = false;
    if let Some((line, after)) = rest.split_once('\n') {
        if let Some(opts) = line.trim().strip_prefix("OPTIONS") {
            theory_propagation = !opts
                .split_whitespace()
                .any(|o| o == "no-theory-propagation");
            finish = opts.split_whitespace().any(|o| o == "finish");
            rest = after;
        }
    }
    cdcl::smt::playground_actions_json(rest, &actions, &lemmas, theory_propagation, finish)
}

fn respond(stream: &mut TcpStream, status: &str, ctype: &str, body: &[u8]) -> io::Result<()> {
    let header = format!(
        "HTTP/1.1 {status}\r\nContent-Type: {ctype}\r\nContent-Length: {}\r\nCache-Control: no-store\r\nConnection: close\r\n\r\n",
        body.len()
    );
    stream.write_all(header.as_bytes())?;
    stream.write_all(body)?;
    stream.flush()
}
