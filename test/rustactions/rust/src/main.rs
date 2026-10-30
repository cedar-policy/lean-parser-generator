//! Smoke test of the Rust actions in `rustactions.lig` and `rustarena.lig`: parses each file
//! argument with `parse_values` of both and exits with an error unless every file parses with
//! both, to the same number of statements.
mod arena;
mod ast;
mod ast_arena;
mod generated;
mod generated_arena;
use generated::*;

fn main() {
    let mut failed = false;
    for path in std::env::args().skip(1) {
        let src = std::fs::read_to_string(&path).unwrap();
        let mut toks = Vec::new();
        let mut stacks = Stacks::new();
        let ok = tokenize(&src, &mut toks).is_ok() && {
            // `parse` (the trace) and `parse_values` are separate copies of the LR loop: they
            // must agree.
            let (mut stack, mut nodes) = (Vec::new(), Vec::new());
            let trace = parse(&toks, &mut stack, &mut nodes);
            let values = parse_values(&toks, &mut stacks);
            match (trace, values) {
                (Ok(()), Ok(p)) => {
                    // The same grammar with the actions allocating from an arena.
                    let mut toks_a = Vec::new();
                    let mut stacks_a = generated_arena::Stacks::new();
                    let arena = arena::Arena::new();
                    generated_arena::tokenize(&src, &mut toks_a).unwrap();
                    let first = generated_arena::parse_values(&toks_a, &mut stacks_a, &arena)
                        .map(|q| q.stmts.iter().count());
                    // The buffers of `stacks_a` serve a second parse, in a second arena.
                    let mut stacks_b = stacks_a.recycle();
                    let arena_b = arena::Arena::new();
                    let second = generated_arena::parse_values(&toks_a, &mut stacks_b, &arena_b)
                        .map(|q| q.stmts.iter().count());
                    match (first, second) {
                        (Ok(n), Ok(n2)) if n == p.stmts.len() && n2 == n => {
                            println!("{path}: {} statements", p.stmts.len());
                            true
                        }
                        r => {
                            println!("{path}: arena parser differs: {r:?}");
                            false
                        }
                    }
                }
                (a, b) => {
                    println!("{path}: failed or mismatch: {a:?} {:?}", b.err());
                    false
                }
            }
        };
        failed |= !ok;
    }
    if failed {
        std::process::exit(1);
    }
}
