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

//! The kernels of the Rust backend: loops that are the same for every grammar and take the
//! grammar's tables as arguments. They are written in the subset of Rust that Aeneas
//! translates (no trait objects, no closures, no lifetimes in `&mut`, tables as plain
//! slices and arrays), so that `rust/verif/` can prove them equal to the Lean specification once.
//! See docs/RUST_PARSER.md.

#![no_std]
extern crate alloc;

use alloc::vec::Vec;

/// A token as the parser reads it: the lexer rule that matched, its terminal, and its byte
/// span in the source. It carries no value; the semantic value of a token is rebuilt from
/// the source text of its span when it is needed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Token {
    pub rule: u16,
    pub term: u16,
    pub start: u32,
    pub end: u32,
}

/// A node of the postorder trace: a shifted token or a reduction.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Node {
    /// A terminal index, or `PROD_FLAG | production`.
    pub kind: u16,
    pub start: u32,
    pub end: u32,
}

pub const PROD_FLAG: u16 = 0x8000;

/// An entry of the parse stack: an automaton state and the byte offset where its symbol starts.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Entry {
    pub state: u16,
    pub start: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ParseError {
    /// Index of the offending token.
    pub token: usize,
    pub state: usize,
    /// The offending terminal, or `u16::MAX` when the tables are inconsistent.
    pub term: u16,
}

/// The "no entry" value of `goto` and `default_reduce`.
pub const NONE: u16 = 65535;

/// The `term` of a `ParseError` that is not about a terminal: the tables are inconsistent
/// (a reduction that cannot be made).
pub const TERM_INCONSISTENT: u16 = u16::MAX;

/// The `term` of a `ParseError` that says the step budget ran out.
pub const TERM_OUT_OF_FUEL: u16 = u16::MAX - 1;

/// The step budget the generated parsers pass: far more steps than any input needs
/// (a step shifts a token or reduces by a production), and small enough that the buffers
/// cannot overflow `usize` before it runs out.
pub const FUEL: usize = 1 << 62;

/// Where the symbol a reduction makes starts: where the first symbol it pops starts, or, for a
/// production with an empty right-hand side, where the previous token ended.
///
/// A function of its own, so that the translation of `reduce` is straight-line code: a choice
/// bound with `let` makes Aeneas copy the rest of the function into both branches.
#[inline(always)]
fn first_start(stack: &Vec<Entry>, base: usize, n: usize, prev_end: u32) -> u32 {
    if n > 0 {
        stack[base].start
    } else {
        prev_end
    }
}

/// The lookahead: the token at `ti`, or, when the tokens have run out, the end-of-input terminal
/// `eof` at the end of the previous token. Its terminal, start and end.
#[inline(always)]
fn lookahead(tokens: &[Token], ti: usize, eof: u16, prev_end: u32) -> (u16, u32, u32) {
    if ti < tokens.len() {
        (tokens[ti].term, tokens[ti].start, tokens[ti].end)
    } else {
        (eof, prev_end, prev_end)
    }
}

/// The `term` of a lexer rule that emits no token (whitespace, comments).
pub const TERM_SKIP: u16 = 65535;

/// The `term` of a lexer rule whose terminal depends on its text: the grammar's own code
/// computes it after `lex` (see `lex`).
pub const TERM_HOOK: u16 = 65534;

/// The `rule` of the end-of-input token.
pub const RULE_EOF: u16 = u16::MAX;

/// Why `lex` stopped. (No derives: they would be translated to Lean too.)
pub enum LexFail {
    /// No rule matches a nonempty prefix of the input at this byte offset.
    NoMatch(usize),
    /// The input is longer than `u32::MAX` bytes, so token spans would not fit.
    TooLong,
}

/// The end of the run of bytes from `i` on that keep the scanner in state `row` (a run of
/// identifier characters, of spaces, …). A loop of its own: the loads of the bytes of the
/// run do not depend on each other.
#[inline(always)]
fn self_run<const NC: usize, const R: usize>(
    src: &[u8],
    class: &[u8; 256],
    trans: &[[u16; NC]; R],
    row: usize,
    i: usize,
) -> usize {
    let mut i = i;
    while i < src.len() && trans[row][class[src[i] as usize] as usize] as usize == row {
        i += 1;
    }
    i
}

/// The longest match so far: `(accept[row], i)` if `row` accepts, `(best, end)` otherwise. A
/// function of its own, so that the translation of `scan` does not copy the rest of the loop
/// body into both branches.
#[inline(always)]
fn record<const R: usize>(
    row: usize,
    i: usize,
    accept: &[u16; R],
    accept_from: usize,
    best: u16,
    end: usize,
) -> (u16, usize) {
    if row >= accept_from {
        (accept[row], i)
    } else {
        (best, end)
    }
}

/// The longest match from `pos` in the DFA (`class`, `trans`, `accept`, `start`,
/// `accept_from`): the accepting rule plus one (0 for none) and the end of the match.
///
/// The DFA's states are the rows of `trans`; row 0 is the dead state. `trans[s][class[b]]`
/// is the state after byte `b` in state `s`. The accepting states are the rows from
/// `accept_from` on, and `accept[s]` is the rule of an accepting state plus one (0 for the
/// others).
#[inline(always)]
fn scan<const NC: usize, const R: usize>(
    src: &[u8],
    pos: usize,
    class: &[u8; 256],
    trans: &[[u16; NC]; R],
    accept: &[u16; R],
    start: usize,
    accept_from: usize,
) -> (u16, usize) {
    let mut row = start;
    let mut i = pos;
    let mut best = 0u16;
    let mut end = pos;
    loop {
        (best, end) = record(row, i, accept, accept_from, best, end);
        if i >= src.len() {
            break;
        }
        let next = trans[row][class[src[i] as usize] as usize] as usize;
        if next == 0 {
            break;
        }
        i += 1;
        if next == row {
            i = self_run(src, class, trans, row, i);
        } else {
            row = next;
        }
    }
    (best, end)
}

/// Longest-match tokenization of `src` with one DFA, appending to `out` (not cleared).
///
/// From each position the longest prefix that a rule matches is a token of that rule, of
/// the earliest rule among those that match it (the DFA's `accept`). `rule_term[r]` is the
/// terminal of rule `r`, `TERM_SKIP` for a rule that emits nothing, or `TERM_HOOK` for a
/// rule whose terminal the grammar's code computes from the text after `lex` returns. The
/// last token is the end-of-input token: rule `RULE_EOF`, terminal `eof`, an empty span at
/// the end. On an error, `out` holds the tokens before it.
#[allow(clippy::too_many_arguments)]
pub fn lex<const NC: usize, const R: usize, const NR: usize>(
    src: &[u8],
    out: &mut Vec<Token>,
    class: &[u8; 256],
    trans: &[[u16; NC]; R],
    accept: &[u16; R],
    start: usize,
    accept_from: usize,
    rule_term: &[u16; NR],
    eof: u16,
) -> Result<(), LexFail> {
    let n = src.len();
    if n > u32::MAX as usize {
        return Err(LexFail::TooLong);
    }
    let mut pos = 0usize;
    loop {
        if pos >= n {
            out.push(Token { rule: RULE_EOF, term: eof, start: n as u32, end: n as u32 });
            return Ok(());
        }
        let (rule, end) = scan(src, pos, class, trans, accept, start, accept_from);
        if rule == 0 || end <= pos {
            return Err(LexFail::NoMatch(pos));
        }
        let r = rule - 1;
        let term = rule_term[r as usize];
        if term != TERM_SKIP {
            out.push(Token { rule: r, term, start: pos as u32, end: end as u32 });
        }
        pos = end;
    }
}

/// What a reduction did.
pub enum Reduced {
    /// The reduction was made, and the parser goes to this state.
    Next(usize),
    /// The reduction has no goto: the input is accepted. With the generator's tables this is
    /// the reduction of the augmented production. As in Lean's `Runtime.Exec.reduce`, the
    /// production is not checked, so that the kernel computes what `Exec` computes on any
    /// table.
    Accept,
    /// The stack is shorter than the production: the tables are inconsistent.
    Inconsistent,
}

/// Reduce by production `prod`: pop its right-hand side from `stack`, push the trace node of
/// the reduction on `nodes`, and push the entry of the state to go to.
///
/// A separate function, so that the proof about the loop treats a reduction once, although the
/// loop reduces in two places (by a default reduction and by an action).
#[inline(always)]
fn reduce<const NN: usize, const S: usize, const P: usize>(
    prod: usize,
    stack: &mut Vec<Entry>,
    nodes: &mut Vec<Node>,
    prev_end: u32,
    goto: &[[u16; NN]; S],
    lhs: &[u16; P],
    rhs_len: &[u16; P],
) -> Reduced {
    let n = rhs_len[prod] as usize;
    if n >= stack.len() {
        return Reduced::Inconsistent;
    }
    let base = stack.len() - n;
    let start = first_start(stack, base, n, prev_end);
    stack.truncate(base);
    let top = stack[base - 1].state as usize;
    let g = goto[top][lhs[prod] as usize] as usize;
    nodes.push(Node { kind: PROD_FLAG | prod as u16, start, end: prev_end });
    if g == NONE as usize {
        return Reduced::Accept;
    }
    stack.push(Entry { state: g as u16, start });
    Reduced::Next(g)
}

/// Parse `tokens`; when they run out the parser reads the terminal `eof`. `stack` and `nodes`
/// are scratch and output buffers and are cleared first. On success `nodes` is the postorder
/// trace; with the generator's tables its last node is the augmented start production.
///
/// Every iteration of the loop is one step (a shift, or a reduction) and uses one unit of
/// `fuel`. With no fuel left the result is an error whose `term` is `TERM_OUT_OF_FUEL`. A
/// well-formed table needs a number of steps proportional to the input, so `fuel` only
/// matters for a table that loops (a cycle of reductions); it is what makes the function
/// total. `fuel` must be at most `1 << 62` (the buffers then cannot overflow).
///
/// The tables, for `S` states, `NT` terminals, `NN` nonterminals and `P` productions:
/// * `action[s][t]`: 0 error, `(target << 1) | 1` shift, `(production + 1) << 1` reduce;
/// * `goto[s][n]`: the state after reducing to `n` in `s`, or `NONE`;
/// * `default_reduce[s]`: the production `s` reduces whatever the lookahead, or `NONE`;
/// * `lhs[p]` and `rhs_len[p]`: the nonterminal and the length of production `p`.
#[allow(clippy::too_many_arguments)]
pub fn parse<const NT: usize, const NN: usize, const S: usize, const P: usize>(
    tokens: &[Token],
    stack: &mut Vec<Entry>,
    nodes: &mut Vec<Node>,
    action: &[[u16; NT]; S],
    goto: &[[u16; NN]; S],
    default_reduce: &[u16; S],
    lhs: &[u16; P],
    rhs_len: &[u16; P],
    eof: u16,
    fuel: usize,
) -> Result<(), ParseError> {
    stack.clear();
    nodes.clear();
    stack.push(Entry { state: 0, start: 0 });
    let mut ti = 0usize;
    let mut prev_end = 0u32;
    // The state on top of `stack`, kept in a register instead of reloaded from it.
    let mut state = 0usize;
    let mut fuel = fuel;
    loop {
        if fuel == 0 {
            return Err(ParseError { token: ti, state, term: TERM_OUT_OF_FUEL });
        }
        fuel -= 1;
        let dr = default_reduce[state] as usize;
        let prod = if dr != NONE as usize {
            dr
        } else {
            let (term, tstart, tend) = lookahead(tokens, ti, eof, prev_end);
            if term as usize >= NT {
                return Err(ParseError { token: ti, state, term });
            }
            let a = action[state][term as usize] as usize;
            if a == 0 {
                return Err(ParseError { token: ti, state, term });
            }
            if a & 1 == 1 {
                stack.push(Entry { state: (a >> 1) as u16, start: tstart });
                state = a >> 1;
                nodes.push(Node { kind: term, start: tstart, end: tend });
                prev_end = tend;
                ti += 1;
                continue;
            }
            (a >> 1) - 1
        };
        match reduce(prod, stack, nodes, prev_end, goto, lhs, rhs_len) {
            Reduced::Next(g) => state = g,
            Reduced::Accept => return Ok(()),
            Reduced::Inconsistent => {
                return Err(ParseError { token: ti, state, term: TERM_INCONSISTENT });
            }
        }
    }
}
