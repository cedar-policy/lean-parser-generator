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

//! Throughput benchmark over a corpus of Cedar policy files, mirroring
//! `test/cedar/CedarBench.lean`: one "policy" is one file.
//! `BENCH_ITERS` sets the iteration count (default 2000).

use cedar_rust_parser::generated::{self, Spanned, Tok};
use cedar_rust_parser::Parser;
use std::hint::black_box;
use std::time::Instant;

fn main() {
    let sources: Vec<String> = std::env::args()
        .skip(1)
        .map(|p| std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("{p}: {e}")))
        .collect();
    let total_bytes: usize = sources.iter().map(|s| s.len()).sum();
    println!("corpus: {} policies, {} bytes", sources.len(), total_bytes);

    let mut p = Parser::new();
    let mut tk: Vec<Spanned<Tok>> = Vec::new();
    let ok = sources.iter().filter(|s| p.parse(s, &mut tk).is_ok()).count();
    println!("parsed OK: {}/{}", ok, sources.len());
    let iters: usize = std::env::var("BENCH_ITERS").ok().and_then(|v| v.parse().ok()).unwrap_or(2000);
    let total = (iters * sources.len()) as f64;
    let report = |name: &str, ns: f64, acc: usize| {
        let per = ns / 1000.0 / total;
        let mbs = (total_bytes * iters) as f64 / (ns / 1e9) / 1e6;
        println!("[{name}] per policy: {per:.3} us, {mbs:.1} MB/s (acc={acc})");
    };

    // `BENCH_LEX_ONLY=1`: only the lexer, for profiling.
    if std::env::var("BENCH_LEX_ONLY").is_ok() {
        let mut toks: Vec<Spanned<Tok>> = Vec::new();
        let t = Instant::now();
        let mut acc = 0usize;
        for _ in 0..iters {
            for s in &sources {
                toks.clear();
                let _ = black_box(generated::tokenize(black_box(s), &mut toks));
                acc += toks.len();
            }
        }
        report("lex only", t.elapsed().as_nanos() as f64, acc);
        return;
    }

    // lex + parse, reusing buffers
    let t = Instant::now();
    let mut acc = 0usize;
    for _ in 0..iters {
        for s in &sources {
            black_box(p.parse(black_box(s), &mut tk).is_ok());
            acc += p.nodes.len();
        }
    }
    report("lex+parse, reused buffers", t.elapsed().as_nanos() as f64, acc);

    // lex + parse, fresh allocations per policy
    let t = Instant::now();
    let mut acc = 0usize;
    for _ in 0..iters {
        for s in &sources {
            let mut q = Parser::new();
            let mut qt = Vec::new();
            black_box(q.parse(black_box(s), &mut qt).is_ok());
            acc += q.nodes.len();
        }
    }
    report("lex+parse, fresh buffers", t.elapsed().as_nanos() as f64, acc);

    // lex only
    let mut toks: Vec<Spanned<Tok>> = Vec::new();
    let t = Instant::now();
    let mut acc = 0usize;
    for _ in 0..iters {
        for s in &sources {
            toks.clear();
            let _ = black_box(generated::tokenize(black_box(s), &mut toks));
            acc += toks.len();
        }
    }
    report("lex only", t.elapsed().as_nanos() as f64, acc);

    // parse only, from pre-lexed tokens
    let lexed: Vec<Vec<Spanned<Tok>>> = sources
        .iter()
        .map(|s| {
            let mut v = Vec::new();
            let _ = generated::tokenize(s, &mut v);
            v
        })
        .collect();
    let t = Instant::now();
    let mut acc = 0usize;
    for _ in 0..iters {
        for ts in &lexed {
            let _ = black_box(generated::parse(black_box(ts), &mut p.stack, &mut p.nodes));
            acc += p.nodes.len();
        }
    }
    report("parse only", t.elapsed().as_nanos() as f64, acc);
}
