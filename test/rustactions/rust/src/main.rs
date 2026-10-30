//! Smoke test of the Rust actions in `rustactions.lig`: parses each file argument with
//! `parse_values` and exits with an error unless every file parses.
mod ast;
mod generated;
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
                    println!("{path}: {} statements", p.stmts.len());
                    true
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
