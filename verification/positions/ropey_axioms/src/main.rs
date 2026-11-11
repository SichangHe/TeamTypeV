// Tests the trusted Ropey specs in ../refinement.rs (rope_wf + external_body ensures) against real
// Ropey 1.6.1 built with the SAME features as crates/teamtype/Cargo.toml (default-features = false:
// LF-only line breaks, see 23c37e2): exhaustively for <= 4 scalars, plus random large ropes.
use ropey::Rope;
fn check(text: &str) {
    let r = Rope::from_str(text);
    let nc = text.chars().count();
    assert_eq!(r.len_chars(), nc);
    assert!(r.chars().eq(text.chars()));
    let nl = r.len_lines();
    let start = |l: usize| r.line_to_char(l);
    let line_len = |l: usize| if l + 1 < nl { start(l + 1) - start(l) } else { nc - start(l) };
    assert!(1 <= nl && nl <= nc + 1 && start(0) == 0 && start(nl - 1) <= nc);
    for i in 0..nl.saturating_sub(1) { assert!(start(i) < start(i + 1)); }
    assert!(r.line(nl - 1).chars().last() != Some('\n'));
    for l in 0..nl {
        assert_eq!(r.line(l).len_chars(), line_len(l));
        assert_eq!(r.try_line_to_char(l).unwrap(), start(l));
        if l + 1 < nl {
            // ends_lf(l) holds exactly for LF / CRLF terminators
            let line: Vec<char> = r.line(l).chars().collect();
            let last = *line.last().unwrap();
            assert_eq!(last, '\n');
        }
    }
    assert_eq!(r.try_line_to_char(nl).unwrap(), nc);
    assert!(r.try_line_to_char(nl + 1).is_err());
    for o in 0..=nc {
        let l = r.try_char_to_line(o).unwrap();
        assert!(l < nl && start(l) <= o && (l == nl - 1 || o < start(l + 1)));
    }
    assert!(r.try_char_to_line(nc + 1).is_err());
}

fn main() {
    let alphabet = ['a', '😀', '\n', '\r', '\u{b}', '\u{c}', '\u{85}', '\u{2028}', '\u{2029}'];
    let k = alphabet.len();
    let (mut strings, mut code) = (0, 0usize);
    loop {
        let mut n = code;
        let mut len = 0;
        let mut text = String::new();
        while n > 0 { text.push(alphabet[(n - 1) % k]); n = (n - 1) / k; len += 1; }
        if len > 4 { break; }
        code += 1;
        check(&text);
        strings += 1;
    }
    println!("ropey axioms held on {strings} strings (finite tests, not proof)");
    // large multi-chunk ropes: pseudo-random text, 200 strings of 2-20k scalars
    let mut x: u64 = 0x9e3779b97f4a7c15;
    let mut next = || { x ^= x << 13; x ^= x >> 7; x ^= x << 17; x };
    for _ in 0..200 {
        let len = 2000 + (next() % 18000) as usize;
        let text: String = (0..len).map(|_| { let v = next() % 20; if (v as usize) < k { alphabet[v as usize] } else { 'b' } }).collect();
        check(&text);
    }
    println!("ropey axioms held on 200 random strings of 2000-19999 scalars (finite tests, not proof)");
}
