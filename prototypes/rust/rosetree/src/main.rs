//! The benchmark: `cargo run --release`. Prints a table of nanoseconds per
//! node for each operation and regime, which the manual's representation
//! chapter records.

use rosetree::*;
use std::time::Instant;

fn fresh(k: usize, d: usize, seed: u64) -> Node {
    let label = Bits::from_u64(seed % 200, 8);
    if d == 0 {
        Node::new(label, Vec::new())
    } else {
        Node::new(label, (0..k).map(|i| fresh(k, d - 1, seed * k as u64 + i as u64 + 1)).collect())
    }
}

fn blob(bits: u64) -> Node {
    let big = |x: u64| {
        let n = ((bits + 63) / 64) as usize;
        let mut v = vec![0u64; n];
        v[0] = x;
        v[n - 1] |= 1 << 63;
        Bits::from_limbs(v, bits)
    };
    Node::new(big(12345), vec![
        Node::new(big(67890), vec![Node::new(big(1), vec![])]),
        Node::new(Bits::from_u64(3, 2), vec![]),
    ])
}

fn timed<T>(f: impl FnOnce() -> T) -> (T, u128) {
    let t0 = Instant::now();
    let r = f();
    (r, t0.elapsed().as_nanos())
}

fn best<T>(reps: u32, mut f: impl FnMut() -> T) -> (T, u128) {
    let (mut r, mut b) = timed(&mut f);
    for _ in 1..reps {
        let (r2, t) = timed(&mut f);
        if t < b {
            b = t;
            r = r2;
        }
    }
    (r, b)
}

fn report(regime: &str, op: &str, nodes: usize, ns: u128) {
    println!("{regime}\t{op}\t{nodes}\t{:.3} ms\t{} ns/node", ns as f64 / 1e6, ns / nodes as u128);
}

fn bench(regime: &str, build: impl Fn() -> Node) {
    let (t, ns_build) = best(3, &build);
    let n = t.size();
    report(regime, "build", n, ns_build);
    let (_, ns) = best(5, || t.size());
    report(regime, "size (fold)", n, ns);
    let (w, ns) = best(3, || encode(&t));
    report(regime, "encode (wire)", n, ns);
    println!("{regime}\tbits\t{}\tbytes {}", w.nbits, (w.nbits + 7) / 8);
    let (ok, ns) = best(5, || recognize(&w));
    report(regime, &format!("recognize = {ok}"), n, ns);
    let (d, ns) = best(3, || decode(&w));
    report(regime, &format!("decode ok = {}", d.is_some()), n, ns);
    let u = build();
    let (e, ns) = best(5, || t == u);
    report(regime, &format!("equality = {e}"), n, ns);
    let (_, ns) = best(3, || t.hash_tree());
    report(regime, "hash (fold)", n, ns);
    let (tape, ns) = best(3, || Tape::build(&t));
    report(regime, "tape build", n, ns);
    let (_, ns) = best(5, || tape.sum_children_by_skip());
    report(regime, "tape walk by skip", n, ns);
    if n > 8 {
        let (bp, ns) = best(3, || bp_tree(&t));
        report(regime, "bp build (vers)", n, ns);
        let (_, ns) = best(3, || bp_walk(&bp));
        report(regime, "bp parent+first_child walk", n, ns);
        let (_, ns) = best(3, || {
            fn walk(t: &Node) -> usize { t.children.iter().map(walk).sum::<usize>() + t.children.len() }
            walk(&t)
        });
        report(regime, "pointer child walk", n, ns);
    }
}

fn main() {
    println!("size_of Bits {} Node {}", std::mem::size_of::<Bits>(), std::mem::size_of::<Node>());
    println!("regime\top\tnodes\ttotal\tper node");
    bench("syntax k=3 d=8", || fresh(3, 8, 1));
    bench("syntax k=2 d=16", || fresh(2, 16, 1));
    bench("syntax k=8 d=5", || fresh(8, 5, 1));
    bench("blob 2^12 bits", || blob(4096));
    bench("blob 2^16 bits", || blob(65536));
    bench("blob 2^20 bits", || blob(1 << 20));
    bench("blob 2^24 bits", || blob(1 << 24));
}
