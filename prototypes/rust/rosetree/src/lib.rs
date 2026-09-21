//! Prototype representations of rose trees of bitstrings.
//!
//! The semantics is a rose tree whose every node carries a bitstring. Three
//! representations are implemented and measured: a pointer tree of owned
//! nodes with a small-string label (`Node`, `Bits`), the serialized form of
//! the Lean prototype (`wire`), whose bits agree with `Geb.Packed.encode`, and
//! a preorder tape with skip pointers in the manner of the structural JSON
//! parsers (`Tape`). Nothing here is proved; the Lean side carries the
//! proofs, and this crate carries the measurements.

use std::hash::{Hash, Hasher};
use vers_vecs::trees::{Tree, TreeBuilder};

/// A bitstring: its exact bit length and its bits, least significant first
/// within little-endian 64-bit limbs, the dead bits of the last limb zero.
/// Up to two limbs are stored inline.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Bits {
    len: u64,
    data: Data,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Data {
    Inline([u64; 2]),
    Heap(Box<[u64]>),
}

impl Bits {
    /// The empty bitstring.
    pub fn empty() -> Self {
        Bits { len: 0, data: Data::Inline([0, 0]) }
    }

    /// The low `len` bits of a word, `len <= 64`.
    pub fn from_u64(w: u64, len: u32) -> Self {
        let w = if len >= 64 { w } else { w & ((1u64 << len) - 1) };
        Bits { len: len as u64, data: Data::Inline([w, 0]) }
    }

    /// A bitstring from limbs, the dead bits made zero.
    pub fn from_limbs(mut limbs: Vec<u64>, len: u64) -> Self {
        let n = ((len + 63) / 64) as usize;
        limbs.resize(n, 0);
        if len % 64 != 0 {
            let last = n - 1;
            limbs[last] &= (1u64 << (len % 64)) - 1;
        }
        if n <= 2 {
            let mut a = [0u64; 2];
            a[..n].copy_from_slice(&limbs);
            Bits { len, data: Data::Inline(a) }
        } else {
            Bits { len, data: Data::Heap(limbs.into_boxed_slice()) }
        }
    }

    /// The bit length.
    pub fn len(&self) -> u64 {
        self.len
    }

    /// Whether the string is empty.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// The limbs, least significant first.
    pub fn limbs(&self) -> &[u64] {
        let n = ((self.len + 63) / 64) as usize;
        match &self.data {
            Data::Inline(a) => &a[..n.min(2)],
            Data::Heap(b) => b,
        }
    }

    /// The bit at a position, false beyond the length.
    pub fn get(&self, i: u64) -> bool {
        i < self.len && (self.limbs()[(i / 64) as usize] >> (i % 64)) & 1 == 1
    }

    /// Concatenation.
    pub fn append(&self, other: &Bits) -> Bits {
        let mut w = Writer::with_capacity(self.len + other.len);
        w.push_bits_of(self);
        w.push_bits_of(other);
        Bits::from_limbs(w.words, w.nbits)
    }
}

/// A node: a label and its children, the children in one allocation.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Node {
    pub label: Bits,
    pub children: Box<[Node]>,
}

impl Node {
    /// A node.
    pub fn new(label: Bits, children: Vec<Node>) -> Self {
        Node { label, children: children.into_boxed_slice() }
    }

    /// The number of nodes.
    pub fn size(&self) -> usize {
        1 + self.children.iter().map(Node::size).sum::<usize>()
    }

    /// A shape-following hash, a fold with the standard hasher.
    pub fn hash_tree(&self) -> u64 {
        let mut h = std::collections::hash_map::DefaultHasher::new();
        self.label.hash(&mut h);
        for c in self.children.iter() {
            c.hash_tree().hash(&mut h);
        }
        h.finish()
    }
}

/// A bit writer over 64-bit words, least significant bit first.
pub struct Writer {
    pub words: Vec<u64>,
    pub nbits: u64,
}

impl Default for Writer {
    fn default() -> Self {
        Self::new()
    }
}

impl Writer {
    /// An empty writer.
    pub fn new() -> Self {
        Writer { words: Vec::new(), nbits: 0 }
    }

    /// An empty writer with room for a number of bits.
    pub fn with_capacity(bits: u64) -> Self {
        Writer { words: Vec::with_capacity(((bits + 63) / 64) as usize), nbits: 0 }
    }

    /// Append the low `k` bits of a word, least significant first, `k <= 64`.
    #[inline]
    pub fn push_bits(&mut self, w: u64, k: u32) {
        if k == 0 {
            return;
        }
        let w = if k >= 64 { w } else { w & ((1u64 << k) - 1) };
        let off = (self.nbits % 64) as u32;
        if off == 0 {
            self.words.push(w);
        } else {
            let last = self.words.len() - 1;
            self.words[last] |= w << off;
            if off + k > 64 {
                self.words.push(w >> (64 - off));
            }
        }
        self.nbits += k as u64;
    }

    /// Append the low `k` bits of a word, most significant first.
    #[inline]
    pub fn push_bits_rev(&mut self, w: u64, k: u32) {
        if k > 0 {
            self.push_bits(w.reverse_bits() >> (64 - k), k);
        }
    }

    /// Append `k` one bits.
    pub fn push_ones(&mut self, mut k: u64) {
        while k >= 64 {
            self.push_bits(u64::MAX, 64);
            k -= 64;
        }
        self.push_bits(u64::MAX, k as u32);
    }

    /// Append the bits of a bitstring.
    pub fn push_bits_of(&mut self, b: &Bits) {
        let mut rem = b.len;
        for &w in b.limbs() {
            let k = rem.min(64) as u32;
            self.push_bits(w, k);
            rem -= k as u64;
        }
    }

    /// Append the Elias delta code of a length, as `Geb.BitTree.Elias.encodeNat`
    /// lays it out: the size of the size in unary zeros and a one, the size's
    /// payload, then the length's payload, the fixed fields most significant
    /// bit first.
    pub fn push_delta(&mut self, n: u64) {
        let m = n + 1;
        let s = 64 - m.leading_zeros(); // size of m
        let z = 31 - s.leading_zeros(); // log2 of s
        self.push_bits(0, z);
        self.push_bits(1, 1);
        self.push_bits_rev(s as u64, z);
        self.push_bits_rev(m, s - 1);
    }

    /// The bits as bytes, least significant byte first.
    pub fn to_bytes(&self) -> Vec<u8> {
        let nbytes = ((self.nbits + 7) / 8) as usize;
        let mut out = Vec::with_capacity(nbytes);
        for w in &self.words {
            out.extend_from_slice(&w.to_le_bytes());
        }
        out.truncate(nbytes);
        out
    }
}

/// A bit reader over the writer's words.
pub struct Reader<'a> {
    words: &'a [u64],
    nbits: u64,
}

impl<'a> Reader<'a> {
    /// A reader of a writer's bits.
    pub fn new(w: &'a Writer) -> Self {
        Reader { words: &w.words, nbits: w.nbits }
    }

    /// The `k` bits from a position, least significant first, `k <= 64`,
    /// zero beyond the end.
    #[inline]
    pub fn get_bits(&self, i: u64, k: u32) -> u64 {
        if k == 0 {
            return 0;
        }
        let idx = (i / 64) as usize;
        let off = (i % 64) as u32;
        let lo = self.words.get(idx).copied().unwrap_or(0) >> off;
        let v = if off + k > 64 {
            lo | (self.words.get(idx + 1).copied().unwrap_or(0) << (64 - off))
        } else {
            lo
        };
        if k >= 64 { v } else { v & ((1u64 << k) - 1) }
    }

    /// The `k` bits from a position, most significant first.
    #[inline]
    pub fn get_bits_rev(&self, i: u64, k: u32) -> u64 {
        if k == 0 { 0 } else { self.get_bits(i, k).reverse_bits() >> (64 - k) }
    }

    /// The number of consecutive one bits from a position, by word.
    pub fn count_ones(&self, mut i: u64) -> u64 {
        let mut n = 0;
        while i < self.nbits {
            let w = !self.get_bits(i, 64);
            let t = w.trailing_zeros() as u64;
            n += t;
            i += t;
            if t < 64 {
                break;
            }
        }
        n.min(self.nbits.saturating_sub(i - n))
    }

    /// The number of consecutive zero bits from a position, by word.
    pub fn count_zeros(&self, mut i: u64) -> u64 {
        let mut n = 0;
        while i < self.nbits {
            let w = self.get_bits(i, 64);
            let t = w.trailing_zeros() as u64;
            n += t;
            i += t;
            if t < 64 {
                break;
            }
        }
        n.min(self.nbits.saturating_sub(i - n))
    }

    /// Read an Elias delta code at a position: the length and the position
    /// after it.
    pub fn read_delta(&self, i: u64) -> Option<(u64, u64)> {
        let z = self.count_zeros(i);
        if i + z >= self.nbits || z >= 64 {
            return None;
        }
        let s = self.get_bits_rev(i + z + 1, z as u32) + (1u64 << z);
        if s - 1 >= 64 {
            return None;
        }
        let j = i + z + 1 + z;
        let m = self.get_bits_rev(j, (s - 1) as u32) + (1u64 << (s - 1));
        let end = j + (s - 1);
        if end > self.nbits { None } else { Some((m - 1, end)) }
    }

    /// Read a bitstring of a length at a position.
    pub fn read_label(&self, i: u64, len: u64) -> Bits {
        let n = ((len + 63) / 64) as usize;
        let mut limbs = Vec::with_capacity(n);
        let mut rem = len;
        let mut p = i;
        while rem > 0 {
            let k = rem.min(64) as u32;
            limbs.push(self.get_bits(p, k));
            p += k as u64;
            rem -= k as u64;
        }
        Bits::from_limbs(limbs, len)
    }

    /// Read one node's header: its arity, its label, and the position after.
    pub fn read_node(&self, i: u64) -> Option<(u64, Bits, u64)> {
        let k = self.count_ones(i);
        if i + k >= self.nbits {
            return None;
        }
        let (len, j) = self.read_delta(i + k + 1)?;
        if j + len > self.nbits {
            return None;
        }
        Some((k, self.read_label(j, len), j + len))
    }
}

/// The serialization: each node as its arity in unary, a zero, the delta code
/// of its label's length, the label, and the children.
pub fn encode(t: &Node) -> Writer {
    let mut w = Writer::new();
    encode_into(t, &mut w);
    w
}

fn encode_into(t: &Node, w: &mut Writer) {
    w.push_ones(t.children.len() as u64);
    w.push_bits(0, 1);
    w.push_delta(t.label.len());
    w.push_bits_of(&t.label);
    for c in t.children.iter() {
        encode_into(c, w);
    }
}

/// The one-counter recognizer.
pub fn recognize(w: &Writer) -> bool {
    let r = Reader::new(w);
    let mut pending: u64 = 1;
    let mut i: u64 = 0;
    while pending > 0 {
        match r.read_node(i) {
            Some((k, _, j)) => {
                pending = pending - 1 + k;
                i = j;
            }
            None => return false,
        }
    }
    i == w.nbits
}

/// The stack-based decoder.
pub fn decode(w: &Writer) -> Option<Node> {
    let r = Reader::new(w);
    let mut stack: Vec<(Bits, u64, Vec<Node>)> = Vec::new();
    let mut i: u64 = 0;
    loop {
        let (k, label, j) = r.read_node(i)?;
        i = j;
        let mut done = if k == 0 {
            Node::new(label, Vec::new())
        } else {
            stack.push((label, k, Vec::with_capacity(k as usize)));
            continue;
        };
        loop {
            match stack.last_mut() {
                None => return if i == w.nbits { Some(done) } else { None },
                Some((_, remaining, children)) => {
                    children.push(done);
                    if children.len() as u64 == *remaining {
                        let (label, _, children) = stack.pop().unwrap();
                        done = Node::new(label, children);
                    } else {
                        break;
                    }
                }
            }
        }
    }
}

/// A preorder tape: one word per node holding the arity, the label's index
/// and the number of words in the subtree, so that a subtree is skipped in
/// constant time; the labels in a side table.
pub struct Tape {
    pub words: Vec<u64>,
    pub labels: Vec<Bits>,
}

impl Tape {
    /// The tape of a tree.
    pub fn build(t: &Node) -> Tape {
        let mut tape = Tape { words: Vec::new(), labels: Vec::new() };
        tape.push(t);
        tape
    }

    fn push(&mut self, t: &Node) -> u64 {
        let here = self.words.len();
        let li = self.labels.len() as u64;
        self.labels.push(t.label.clone());
        self.words.push(0);
        let mut size = 1;
        for c in t.children.iter() {
            size += self.push(c);
        }
        self.words[here] = (t.children.len() as u64) | (li << 20) | (size << 44);
        size
    }

    /// The arity of the node at a word.
    #[inline]
    pub fn arity(&self, i: usize) -> u64 {
        self.words[i] & 0xFFFFF
    }

    /// The label of the node at a word.
    #[inline]
    pub fn label(&self, i: usize) -> &Bits {
        &self.labels[((self.words[i] >> 20) & 0xFFFFFF) as usize]
    }

    /// The number of words of the subtree at a word.
    #[inline]
    pub fn subtree(&self, i: usize) -> usize {
        (self.words[i] >> 44) as usize
    }

    /// The sum over nodes of a function of arity, in tape order.
    pub fn fold_size(&self) -> usize {
        self.words.len()
    }

    /// Visit each node's children by skipping, summing the arities: a check
    /// that skip pointers navigate the whole tree.
    pub fn sum_children_by_skip(&self) -> u64 {
        let mut total = 0;
        let mut stack = vec![0usize];
        while let Some(i) = stack.pop() {
            let k = self.arity(i);
            total += k;
            let mut c = i + 1;
            for _ in 0..k {
                stack.push(c);
                c += self.subtree(c);
            }
        }
        total
    }
}

/// The balanced-parentheses word of a tree, for the succinct comparison.
pub fn bp_tree(t: &Node) -> vers_vecs::BpTree {
    let mut b = vers_vecs::trees::bp::BpBuilder::<512>::new();
    fn go(t: &Node, b: &mut vers_vecs::trees::bp::BpBuilder<512>) {
        b.enter_node();
        for c in t.children.iter() {
            go(c, b);
        }
        b.leave_node();
    }
    go(t, &mut b);
    b.build().unwrap()
}

/// Walk a parenthesis tree by first child and next sibling, counting the
/// nodes with a parent: the succinct navigation cost per node.
pub fn bp_walk(bp: &vers_vecs::BpTree) -> usize {
    let mut count = 0;
    let mut stack = vec![bp.root().unwrap()];
    while let Some(v) = stack.pop() {
        if bp.parent(v).is_some() {
            count += 1;
        }
        let mut c = bp.first_child(v);
        while let Some(x) = c {
            stack.push(x);
            c = bp.next_sibling(x);
        }
    }
    count
}

#[cfg(test)]
mod tests {
    use super::*;

    fn n(label: u64, len: u32, cs: Vec<Node>) -> Node {
        Node::new(Bits::from_u64(label, len), cs)
    }

    /// The tree `sample` of the Lean tests: label rank [1,0,1] = 12 has the
    /// bits 1,0,1; the others are indices whose bit strings are the bits of
    /// index + 1 below its top bit.
    fn sample() -> Node {
        let lab = |r: u64| {
            let m = r + 1;
            let len = 63 - m.leading_zeros();
            Bits::from_u64(m, len)
        };
        Node::new(lab(12), vec![
            Node::new(lab(5), vec![]),
            Node::new(lab(0), vec![Node::new(lab(12), vec![]), Node::new(lab(3), vec![])]),
        ])
    }

    #[test]
    fn lean_vectors() {
        let w = encode(&sample());
        assert_eq!(w.nbits, 38);
        assert_eq!(w.to_bytes(), vec![51, 165, 46, 83, 10]);
        let leaf = n(0, 0, vec![]);
        let w = encode(&leaf);
        assert_eq!((w.nbits, w.to_bytes()), (2, vec![2]));
    }

    #[test]
    fn lean_vector_long() {
        // long = node (2^100 + 12345) [node (2^70) [], node (2^64 - 1) [], sample]
        let lab = |m_minus_one_limbs: Vec<u64>, len: u64| Bits::from_limbs(m_minus_one_limbs, len);
        // rank a: string = bits of (a+1) below its top bit.
        // 2^100 + 12345 + 1 = 2^100 + 12346: bits below bit 100: 12346, len 100.
        let l1 = lab(vec![12346, 0], 100);
        // 2^70 + 1: bits below bit 70: 1, len 70.
        let l2 = lab(vec![1, 0], 70);
        // 2^64 - 1 + 1 = 2^64: len 64, bits 0.
        let l3 = lab(vec![0], 64);
        let t = Node::new(l1, vec![Node::new(l2, vec![]), Node::new(l3, vec![]), sample()]);
        let w = encode(&t);
        assert_eq!(w.nbits, 311);
        assert_eq!(w.to_bytes(), vec![199, 83, 29, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 192, 241, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 7, 1, 0, 0, 0, 0, 0, 0, 0, 102, 74, 93, 166, 20]);
        assert!(recognize(&w));
        assert_eq!(decode(&w).as_ref(), Some(&t));
    }

    #[test]
    fn roundtrip_and_reject() {
        let t = sample();
        let w = encode(&t);
        assert!(recognize(&w));
        assert_eq!(decode(&w).as_ref(), Some(&t));
        let mut w2 = encode(&t);
        w2.push_bits(1, 1);
        assert!(!recognize(&w2));
        assert!(decode(&w2).is_none());
        let tape = Tape::build(&t);
        assert_eq!(tape.fold_size(), 5);
        assert_eq!(tape.sum_children_by_skip(), 4);
        let bp = bp_tree(&t);
        assert_eq!(bp.subtree_iter(bp.root().unwrap()).count(), 5);
        assert_eq!(bp_walk(&bp), 4);
    }
}
