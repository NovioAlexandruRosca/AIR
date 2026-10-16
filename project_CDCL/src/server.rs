//! Minimal std-only HTTP server for the visualizer.
//!
//! - `GET /`            -> the single-page UI (`ui/index.html`, embedded)
//! - `POST /api/solve`  -> body: DIMACS text, response: trace JSON
//!
//! Binds to 127.0.0.1 only. Each connection gets its own thread: browsers
//! open idle "preconnect" sockets, and a single-threaded loop would sit on
//! one of those while the real request waits behind it.

use cdcl::trace::json_string;
use cdcl::{parse, solve_to_json, Limits};
use std::io::{self, Read, Write};
use std::net::{TcpListener, TcpStream};
use std::time::{Duration, Instant};

const INDEX_HTML: &str = include_str!("../ui/index.html");
const MAX_HEADER: usize = 64 * 1024;
const MAX_BODY: usize = 64 * 1024 * 1024;

pub fn serve(port: u16, trace_limit: usize, limits: Limits) -> io::Result<()> {
    let listener = TcpListener::bind(("127.0.0.1", port))?;
    println!("CDCL visualizer: http://127.0.0.1:{port}/   (Ctrl+C to stop)");
    for stream in listener.incoming() {
        match stream {
            Ok(s) => {
                let limits = limits.clone();
                std::thread::spawn(move || {
                    if let Err(e) = handle(s, trace_limit, &limits) {
                        // Idle preconnects time out here; not worth reporting.
                        if e.kind() != io::ErrorKind::WouldBlock && e.kind() != io::ErrorKind::TimedOut {
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
            return respond(&mut stream, "431 Request Header Fields Too Large", "text/plain", b"headers too large");
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
        ("GET", "/") | ("GET", "/index.html") => {
            respond(&mut stream, "200 OK", "text/html; charset=utf-8", INDEX_HTML.as_bytes())
        }
        ("POST", "/api/solve") => {
            if content_length > MAX_BODY {
                return respond(&mut stream, "413 Payload Too Large", "text/plain", b"input too large");
            }
            let mut body = buf[header_end..].to_vec();
            while body.len() < content_length {
                let n = stream.read(&mut chunk)?;
                if n == 0 {
                    break;
                }
                body.extend_from_slice(&chunk[..n]);
            }
            let text = String::from_utf8_lossy(&body);
            let start = Instant::now();
            match parse(&text) {
                Ok(cnf) => {
                    let parse_ms = start.elapsed().as_secs_f64() * 1000.0;
                    let json = solve_to_json(&cnf, trace_limit, limits, parse_ms);
                    respond(&mut stream, "200 OK", "application/json", json.as_bytes())
                }
                Err(e) => {
                    let mut json = String::from(r#"{"error":"#);
                    json_string(&mut json, &e.to_string());
                    json.push('}');
                    respond(&mut stream, "400 Bad Request", "application/json", json.as_bytes())
                }
            }
        }
        _ => respond(&mut stream, "404 Not Found", "text/plain", b"not found"),
    }
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
