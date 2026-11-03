// Copyright Cedar Contributors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Parsing throughput of the generated Rust parsers against cedar-policy-core, on the same
//! files:
//!
//! ```text
//! cedar-parser-compare --policies a.cedar b.cedar --schemas x.cedarschema y.cedarschema
//! cedar-parser-compare --policies-from policy-list.txt --schemas-from schema-list.txt
//! ```
//!
//! Both sides go from text to a concrete syntax tree and drop it:
//! - policies: `lex + parse_values` of `cedar.lig` against
//!   `cedar_policy_core::parser::text_to_cst::parse_policies`;
//! - schemas: `lex + parse_values` of `CedarSchema.lig` against
//!   `cedar_policy_core::validator::cedar_schema::parser::parse_schema`.
//!
//! Neither does the later step (CST to AST for policies, CST to JSON schema for schemas).
//! A file is timed only if both parsers accept it; the others are listed. `BENCH_ITERS` sets
//! the number of passes over the corpus (default 500).

use std::hint::black_box;
use std::time::Instant;

use cedar_policy_core::parser::text_to_cst;
use cedar_policy_core::validator::cedar_schema::parser::parse_schema;

fn read(paths: &[String]) -> Vec<(String, String)> {
    paths
        .iter()
        .map(|p| (p.clone(), std::fs::read_to_string(p).unwrap_or_else(|e| panic!("{p}: {e}"))))
        .collect()
}

/// Time `f` over `iters` passes of the corpus; microseconds per file.
fn time<'a, F: FnMut(&'a str) -> usize>(srcs: &[&'a str], iters: usize, mut f: F) -> (f64, usize) {
    let t = Instant::now();
    let mut acc = 0usize;
    for _ in 0..iters {
        for s in srcs {
            acc += f(black_box(s));
        }
    }
    (t.elapsed().as_nanos() as f64 / 1000.0 / (iters * srcs.len()) as f64, acc)
}

struct Row {
    name: &'static str,
    us: f64,
}

fn report(title: &str, files: usize, bytes: usize, rows: &[Row]) {
    println!("\n{title}: {files} files, {bytes} bytes");
    let base = rows.first().map(|r| r.us).unwrap_or(1.0);
    for r in rows {
        let mbs = bytes as f64 / files as f64 / r.us; // bytes per µs = MB/s
        println!("  {:<44} {:>9.2} us/file {:>8.1} MB/s {:>6.2}x", r.name, r.us, mbs, base / r.us);
    }
}

fn policies(paths: &[String], iters: usize) {
    use cedar_rust_parser::generated;
    let files = read(paths);
    let mut both: Vec<&str> = Vec::new();
    for (p, s) in &files {
        let core = text_to_cst::parse_policies(s).is_ok();
        let mut toks = Vec::new();
        let lpg = generated::tokenize(s, &mut toks).is_ok()
            && generated::parse_values(s, &toks, &mut generated::Stacks::new()).is_ok();
        if core && lpg {
            both.push(s);
        } else {
            println!("policies: skipped {p} (cedar-policy-core {core}, generated {lpg})");
        }
    }
    let bytes: usize = both.iter().map(|s| s.len()).sum();
    let mut rows = Vec::new();
    rows.push(Row {
        name: "cedar-policy-core parse_policies",
        us: time(&both, iters, |s| text_to_cst::parse_policies(s).is_ok() as usize).0,
    });
    let mut toks = Vec::new();
    let mut stacks = generated::Stacks::new();
    rows.push(Row {
        name: "generated lex + parse_values",
        us: time(&both, iters, |s| {
            toks.clear();
            let _ = generated::tokenize(s, &mut toks);
            generated::parse_values(s, &toks, &mut stacks).map(|p| p.policies.len()).unwrap_or(0)
        })
        .0,
    });
    let mut toks2 = Vec::new();
    rows.push(Row {
        name: "  of which lex",
        us: time(&both, iters, |s| {
            toks2.clear();
            let _ = generated::tokenize(s, &mut toks2);
            toks2.len()
        })
        .0,
    });
    let mut p = cedar_rust_parser::Parser::new();
    let mut toks3 = Vec::new();
    rows.push(Row {
        name: "generated lex + parse (trace only, no CST)",
        us: time(&both, iters, |s| {
            let _ = p.parse(s, &mut toks3);
            p.nodes.len()
        })
        .0,
    });
    report("policies", both.len(), bytes, &rows);
}

fn schemas(paths: &[String], iters: usize) {
    use cedarschema_rust_parser::generated;
    let files = read(paths);
    let mut both: Vec<&str> = Vec::new();
    for (p, s) in &files {
        let core = parse_schema(s).is_ok();
        let lpg = cedarschema_rust_parser::parse_str(s).is_ok();
        if core && lpg {
            both.push(s);
        } else {
            println!("schemas: skipped {p} (cedar-policy-core {core}, generated {lpg})");
        }
    }
    let bytes: usize = both.iter().map(|s| s.len()).sum();
    let mut rows = Vec::new();
    rows.push(Row {
        name: "cedar-policy-core parse_schema",
        us: time(&both, iters, |s| parse_schema(s).is_ok() as usize).0,
    });
    let mut toks = Vec::new();
    let checks = cedarschema_rust_parser::cst::Checks::default();
    let mut stacks = generated::Stacks::new();
    rows.push(Row {
        name: "generated lex + parse_values + checks",
        us: time(&both, iters, |s| {
            cedarschema_rust_parser::parse(s, &mut toks, &mut stacks, &checks)
                .map(|p| p.namespaces.len())
                .unwrap_or(0)
        })
        .0,
    });
    let mut toks2 = Vec::new();
    rows.push(Row {
        name: "  of which lex",
        us: time(&both, iters, |s| {
            toks2.clear();
            let _ = generated::tokenize(s, &mut toks2);
            toks2.len()
        })
        .0,
    });
    report("schemas", both.len(), bytes, &rows);
}

fn main() {
    let iters: usize = std::env::var("BENCH_ITERS").ok().and_then(|v| v.parse().ok()).unwrap_or(500);
    let mut pol: Vec<String> = Vec::new();
    let mut sch: Vec<String> = Vec::new();
    let mut cur: Option<&mut Vec<String>> = None;
    let mut skip = false;
    for a in std::env::args().skip(1) {
        if std::mem::take(&mut skip) {
            continue;
        }
        match a.as_str() {
            "--policies" => cur = Some(&mut pol),
            "--schemas" => cur = Some(&mut sch),
            // `--policies-from FILE`, `--schemas-from FILE`: one path per line.
            "--policies-from" | "--schemas-from" => {
                let list = std::env::args().skip_while(|x| *x != a).nth(1).expect("a file name");
                let paths = std::fs::read_to_string(&list).unwrap_or_else(|e| panic!("{list}: {e}"));
                let dst = if a == "--policies-from" { &mut pol } else { &mut sch };
                dst.extend(paths.lines().filter(|l| !l.is_empty()).map(str::to_string));
                cur = None;
                skip = true;
            }
            _ => match cur.as_deref_mut() {
                Some(v) => v.push(a),
                None => panic!("expected --policies or --schemas before {a}"),
            },
        }
    }
    if !pol.is_empty() {
        policies(&pol, iters);
    }
    if !sch.is_empty() {
        schemas(&sch, iters);
    }
}
