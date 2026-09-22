/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import VersoManual
public import GebManual.Bibliography
import Geb.Prototypes.Computability.BitTree
import Geb.Prototypes.Computability.BitTree.Elias.RepresentationSize
import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.Machine
import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.RecognizeExpr
import Geb.Prototypes.Computability.Oitavem
import Geb.Prototypes.Computability.Oitavem.Machine.SpaceTime
import Geb.Prototypes.Computability.Oitavem.Word
import Geb.Prototypes.Typechecker.Oitavem
import Geb.Mathlib.Data.PFunctor.Presheaf.Decidable
import Geb.Prototypes.CanonicalSExpr
import Geb.Prototypes.RoseTree
import Geb.Prototypes.SuccinctTree

/-! # Value representation chapter

The design record for the representation of the language's values:
the requirements, the state of the repository's encodings and
recognizers, the literature, the prototypes and their measurements,
and the recommendations.
-/

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

#doc (Manual) "Representing rose trees of bitstrings" =>

The language's values are rose trees of bitstrings: finite ordered
trees of unbounded branching, each node of which carries a bitstring
of arbitrary length. Every finitary W-type is presented by such
trees, the label selecting a shape together with its non-recursive
data and the children supplying the recursive data. This chapter
records the design of a representation of those trees: the
requirements, the encodings and recognizers the repository already
has, the literature on succinct, persistent and word-level tree and
string representations, the prototypes written against that
literature with their measurements, and, last, the recommendations
with their tradeoffs. It is a record of an investigation in progress;
each section states what has been established and what remains
conjectural. The literature searches are of September 2026. Every
measurement describes the stated program on the stated machine, and
none is a measurement of a complete presheaf type checker.

# Requirements

The representation is judged by the following properties, in the
order of their weight.

* Semantics. Whatever the internal form, the type represented is the
  rose tree of bitstrings, up to a computable isomorphism proved in
  Lean. Variants adapted to different host languages may differ
  internally; they agree on this semantics. Empty labels, leading
  zeros, the order of children and repeated equal subtrees are
  observable; pointer identity, block boundaries, the choice of hash
  and the machine word width are not.
* Recognition in logarithmic space. The recognizer of a serialized
  value, through each stage of the type checker, is a function in
  `FLOGSPACE`. The stages are: the word encodes a tree; each node's
  label decodes to a shape of the signature whose arity matches the
  node's number of children (a finitary W-type); each child's shape
  lies over the index its parent's shape prescribes at the child's
  position (a slice W-type); and the direction restrictions of a
  presheaf signature commute with the tree's structure, hereditarily
  (a presheaf W-type). Membership in `FLOGSPACE` is witnessed by an
  expression of a sound function algebra whose meaning is
  extensionally equal to the recognizer, not by the recognizer's own
  implementation, which is free to use any resources.
* Word-level operation. Bitstrings are handled in machine words of a
  compile-time width, so that a bit operation is a word operation
  where the hardware or abstract machine has one, and a bitstring
  longer than a word is a sequence of words or a further tree.
* Storage. The space taken by a stored tree is within a constant
  factor well under two of the information-theoretic minimum for its
  number of nodes and its total payload, and asymptotically optimal
  in both. § The space denominator states the minimum.
* Operation cost. Construction, destructuring, folding, equality and
  hashing run in time linear in the data touched with word-sized
  constants, and in parallel where a parallel evaluator hosts the
  representation.
* Persistence. A value, once published, is immutable and shared: an
  edit produces a new version that shares unchanged structure with
  the old, older versions remain readable while a later one is being
  built, and the space of a history is accounted as the live shared
  graph plus the incremental bytes of each edit.
* Portability. The same semantics and serialized form are
  implemented in Lean, in systems languages such as Rust, and on
  interaction-net runtimes such as HVM4, each with the internal form
  that suits it.

Construction dominates the workload: values are built and rebuilt by
an evaluator far more often than they are recognized from a
serialized form. Among workloads, self-hosting comes first: parsing,
type checking, interpretation and compilation of the language by
itself, and the developer tooling around them, syntax trees for
editors and the Language Server Protocol among them. Frequent
persistent updates and structural sharing are central to those
workloads: an editor edits one snapshot while a language-server
request reads an older one. The recommendations are ordered by what
serves those, since that work pays off first; the other workloads,
large data and streams among them, and the eventual operating-system
applications, are investigated to the same depth and ordered after.
The design therefore has two faces, a serialized form whose
recognizer is the object of the complexity requirement and an
in-memory form whose construction cost is the object of the
operation-cost requirement, related by a conversion in each
direction.

The storage model of the language's source shapes the syntax-tree
workload further. As in Unison, a definition is identified by the
cryptographic hash of its abstract syntax tree alone, and everything
else about it, comments, the Merkle hashes of its nodes, and
whatever further annotations are kept, is stored beside the tree
rather than in it, each annotation with a hash of its own. The
syntax tree itself then has small labels, constructor identifiers on
the order of the number of constructors of the types the program
mentions, while the structures beside it hold data that may dwarf
the tree, a comment being often larger than the code it comments
and a digest per node being larger than the node. Data accessed
together are stored together, so the tree is one structure and each
kind of annotation is another, keyed by the position of the node it
annotates. The representation therefore serves two shapes at once: a
tree of many nodes with labels of a few bits, and parallel sequences
of larger payloads indexed by node.

## The space denominator

For a fixed node count $`n \ge 1` and total label length $`M`, the
family of rose trees of bitstrings has
$`C_{n-1}\binom{M+n-1}{n-1}2^M` members: an ordered topology, a weak
composition of the payload length into node lengths, and the payload
bits. Its information bound, up to integer rounding, is therefore

$`H(n,M) = M + \log_2 C_{n-1} + \log_2\binom{M+n-1}{n-1}`.

This is a counting argument, not a formalized theorem. The familiar
$`2n` topology bits omit the cost of the label boundaries, the third
term, which a per-label length code pays and a representation that
knows the labels' lengths from a schema does not; an unrestricted
bitstring label cannot inherit that saving silently. A header that
states $`n` and $`M` also counts.

Succinctness means $`H + o(H)` bits over a stated asymptotic regime.
A practical claim, such as at most 1.3 times the bound, needs a
minimum object size, the header cost and an explicit treatment of
allocation, alignment, indexes and hashes, since for tiny objects the
fixed overhead cannot vanish. For a persistent history, the report
is the live shared graph and the incremental bytes per edit;
comparing a whole history to the latest tree's bound alone would
mislead.

Separating the topology, the lengths and the payloads into three
sequences makes each cost visible. Elias delta codes for every length
are the baseline. Monotone cumulative endpoints, shifted by their
ordinal to distinguish empty labels, admit Elias–Fano techniques.
Neither a per-label delta code nor an unspecified $`O(n)` endpoint
redundancy proves uniform succinctness across every ratio $`M/n`;
adaptive block encodings, compact codes for small lengths and
enumerative composition codes among them, merit a later comparison,
each with an exact decoder and a redundancy bound that includes its
block headers.

# The repository's present representations

The bitstring is `List Bool`, and every operation on it in the
formal development is a recursion over that list. The binary tree
with bitstrings at its leaves is {name}`Geb.BitTree.Tree`, the W-type
of the polynomial `X ↦ List Bool + X × X`. Two encodings of it into
`List Bool` are proved injective with linear-time, logarithmic-space
recognizers. {name}`Geb.BitTree.encode` escapes each payload bit, at
a cost of doubling the payload; {name}`Geb.BitTree.Elias.encode`
tags each node with one bit and prefixes each payload with its length
in the Elias delta code {citep Elias1975}[], whose representation
size the module proves optimal to within the length headers by a
counting argument over every lossless representation.
{name}`Geb.BitTree.Elias.length_encode` counts the encoding's bits
exactly, and {name}`Geb.BitTree.Elias.representation_redundancy_vanishes`
proves the relative redundancy vanishing as the average payload
length diverges; it asserts neither succinctness in every relation
between payload size and node count nor a bound for indexed
navigation.

A finitary slice W-type over a signature whose shapes are coded by
bitstrings is spelled as such a binary tree by
{name}`Geb.SizeBounded.Logspace.WTree.CodedSig.spell`: a node of
arity `k` is the left spine of `k` forks whose leftmost leaf carries
the shape's code and whose right children are the children's
spellings. Under the Elias-length encoding the node reads as `k`
ones, a zero, the coded length of the label, the label, and the
children in order. The recognizer
{name}`Geb.SizeBounded.Logspace.WTree.CodedSig.recognize` accepts
exactly the spellings of admissible W-trees
({name}`Geb.SizeBounded.Logspace.WTree.CodedSig.recognize_iff`), and
{name}`Geb.SizeBounded.Logspace.WTree.CodedSig.computableInTimeAndSpace_recognize`
places it in polynomial time and logarithmic space by reading the
bound off the soundness theorem of Kristiansen's logspace algebra
{citep Kristiansen2005}[], in which the recognizer is written as
{name}`Geb.SizeBounded.Logspace.WTree.recognizeExpr`. The recognizer
re-reads the word once per node, so its time is quadratic in the
word's length: the label and edge checks at a node need the node's
parent, and a logarithmic-space machine locates a parent in a
preorder word only by a scan. The theorem
{name}`Geb.SizeBounded.Logspace.WTree.CodedSig.recognizeExprSem_eq_singleton_iff_isW`
connects the recognizer to a successor-free expression, conditional
on expressions computing the signature's label and edge tests; a
representation change must preserve these conditions.

Oitavem's algebra for logspace {citep Oitavem2010}[] is the second
witness available. Its syntax and interpreter are formalized, with
the truncation and output-length results of the paper's soundness
argument; the compiler to a machine and its soundness theorem are in
progress, general reader substitution and the retained-prefix
recursion machine being the parts its umbrella module states as
open, and {name}`Geb.Oitavem.Machine.computes_polytime_logspace`
already converts any halting logarithmic-space transducer into a
polynomial time bound. Finitarity alone is not a witness:
{name}`Geb.Oitavem.no_universal_decider` rules out a universal
membership test, and
{name}`Geb.Oitavem.PresheafCounterexample.no_oitavem_nativeCheck` is
a presheaf signature whose native check no expression of the algebra
computes as stated.

The presheaf stage has a Lean-native decision procedure and no
algebraic witness. {name}`PresheafPFunctor.isHereditarilyNaturalBoolCore`
decides hereditary naturality by a fold over the slice W-tree whose
step at a node compares subtrees, so it runs in time quadratic in the
number of nodes and in space linear in the tree's height. The
condition that it decides compares, at each node and for each
morphism of the index category and each direction, the value at the
restricted direction with the restriction of the value at the
original direction; each such comparison is an equality of subtrees
up to a fixed relabelling. {name}`Geb.PresheafRecognition.native_eq_scan`
expresses the native check as a conjunction of local tests, and
{name}`Geb.PresheafRecognition.restrictedEq_eq_true_iff` reduces each
restriction comparison to a root-shape test and equalities of
original subtrees, so that an implementation compares input spans or
shared immutable values without constructing restricted copies;
{name}`Geb.Oitavem.Expr.presheafScan_pass_iff` supplies the outer
scan once its local position expression and node-enumeration
obligations are discharged.

The linear space is the implementation's, not the problem's. The fold
keeps a frame per level of recursion, so on a chain it keeps one per
node; the specification it decides is in logarithmic space, and in
`TC^0` on the serialized form, because every ingredient of a
comparison is a counting computation: the subtree at a direction is
located from a node's position by a matching-parenthesis scan with an
excess counter, the relabelling is a fixed local map given by the
functor's finite data, and two subtrees are compared in lockstep by
walking both with their current positions and the counters that step
to a child. The logarithmic-space form iterates over node positions
and, for each morphism and direction, locates the two subtrees by
scanning and compares them by scanning, in place of the stack; its
time is quadratic to cubic, one scan per location and one per
comparison. It is the form the algebras express, as the recognizer of
slice W-trees is already written, and it remains to be written for
this stage (§ Recommendations). The three forms decide one
specification: the fold at depth space, the check over hash-consed
trees at linear time, and the counter scan at logarithmic space.

The evaluators of the algebras themselves interpret bit by bit. The
recognizer of the algebra's own expressions, evaluated with sharing,
takes tens of seconds at a ten-bit word; § The interpreter and
parser measurements records the figures. The Lean-native decision
procedures run at the speed of Lean's compiled code over `List Bool`,
which is faster by orders of magnitude and still allocates one cell
per bit.

The concrete syntax of the repository fixes the semantics from the
other side: {name}`Geb.Ast.ofRose_toRose` relates the abstract syntax
to its rose presentation and {name}`Geb.Rose.parse_print` is the
round trip of the printed form. Both remain the semantic anchors; a
representation is a second presentation of these trees, not a second
language of trees.

# Literature

The surveys below were made against primary sources; every
identifier was checked against the arXiv, the IACR ePrint archive
or Crossref before entering the bibliography. Statements marked as
derived are the author's deductions from the cited results rather
than results stated in them. The building blocks surveyed rest on
different assumptions, and naming several together does not combine
their guarantees.

## Succinct and compact trees

An ordinal tree of `n` nodes has `2n + o(n)`-bit representations
with constant-time navigation: balanced parentheses with pioneer
structures {citep MunroRaman2001}[], the depth-first unary degree
sequence, DFUDS, in which each node is written as its degree in
unary followed by a closing bit, so that the `i`-th child and the
degree are found from one matching-parenthesis query
{citep BenoitDemaineMunroRamanRamanRao2005}[], and the range
min-max tree over the excess sequence, which supports every
operation of both families, level ancestors and lowest common
ancestors included, in constant time, and in its dynamic form
supports node insertion and deletion in `O(log n / log log n)` time,
with attach and detach of subtrees at a separate
`O(log^{1+ε} n)` {citep NavarroSadakane2014}[]. The DFUDS degree
sequence compresses to the degree entropy of the tree
{citep JanssonSadakaneSung2012}[]. Tree covering gives the same
bounds by a different route {citep FarzanMunro2014}[]; a
finger-based dynamic variant supports constant-time navigation at a
finger and constant amortized leaf insertion
{citep FarzanMunro2011}[]. Measured, the range min-max tree with a
block size of 512 takes 2.37 to 2.38 bits per node and answers most
operations in under half a microsecond, against 18 to 31 nanoseconds
for the child operation of a pointer tree
{citep ArroyueloCanovasNavarroSadakane2010}[]; a simplified
inter-block scheme reaches 2.34 bits per node at up to four times
the speed of the reference implementation
{citep CordovaNavarro2016}[]; a 2024 tree-covering variant over
balanced parentheses, each microtree at most two parenthesis
intervals, measures 1.822 bits per node for average-case range-minimum
queries {citep HamadaChakrabortyJoKoriyamaSadakaneSatti2024}[], a
candidate for sealed blocks whose sub-`2n` figures in that setting
neither contradict the worst-case topology bound nor supply an
incremental persistent implementation. The range min-max tree is
constructed from the parenthesis word in `O(n/p + log p)` time on
`p` processors, by a parallel prefix over the excess sequence
{citep FuentesSepulvedaFerresHeZeh2017}[]. The shared pioneer
structure of {citep GogFischer2010}[], which is what the `sdsl`
library ships, shares navigation auxiliaries between succinct
operations; it is not sharing between persistent versions of an
application's values.

Dynamic rank and select over a set of `n` elements from a universe
of size `U` polynomial in `n` reaches the optimal amortized expected
`O(1 + log n / log log U)` time with `o(n)` redundancy
{citep KuszmaulLiangZhou2026}[], the first dynamic structure to
bypass the tree-structure bottleneck, in which the bits encoding a
dynamic tree structure are themselves enough to force nearly linear
redundancy; its compressed-tabulation and shared-table techniques
are relevant to a persistent structure's space accounting, and it is
neither a measured library nor a worst-case, fully persistent
range-minimum result. For rank and select on static bit vectors,
[SPIDER](https://arxiv.org/abs/2405.05214) interleaves rank metadata
with the bits and predicts select positions, at 3.82 percent space
overhead in its tested configuration, and
[BiRank and QuadRank](https://curiouscoding.nl/posts/quadrank/)
attend to cache traffic, batching, prefetching and multicore
throughput, BiRank at 3.28 percent overhead; their comparisons are
workload-specific, and rank throughput and rank metadata are neither
the whole cost of parenthesis navigation nor of the labels.

None of these represents labels of arbitrary length natively. The
standard construction stores the labels as a parallel array of
variable-length cells: the payloads concatenated, with the
boundaries given by Elias-coded lengths or by an Elias-Fano
sequence of cumulative offsets, at `n ⌈log(L/n)⌉ + 2n` bits for `n`
labels of total length `L` {citep Navarro2016}[]. Top-tree
compression is the family in which labels are native; it represents
a labelled tree by a directed acyclic graph of
`O(n / log_σ n)` nodes in the worst case, navigable in logarithmic
time {citep BilleGortzLandauWeimann2015}[]
{citep DudekGawrychowski2024}[], and is static.

Of the Rust libraries, `vers-vecs` ships a static balanced-parentheses
tree over a pointerless min-max tree with the full navigation set in
logarithmic time and a configurable block size, rank in 6 to 26
nanoseconds and select in 30 to 159, and is maintained; `sucds`
ships bit vectors and Elias-Fano sequences without trees, and `sux`
adds word-level Jacobson parenthesis matching with Elias-Fano pioneer
information, a matching primitive rather than a labelled-tree
interface. Each constructor assumes valid parentheses, so untrusted
input is validated before it is indexed. No Rust crate ships DFUDS, a
dynamic parenthesis tree, or a labelled succinct tree. The C++
reference, `sdsl-lite`, is maintained in its version 3 fork. No
surveyed succinct dynamic tree is persistent: every one is
ephemeral, and pays `O(log n / log log n)` to `O(log n)` per
navigation and per update.

## Persistent sequences

Full persistence of a sequence under path copying is the property the
editor workload needs and the succinct trees lack. FeAVL
{citep KanedaArimuraInenaga2026}[] makes a string fully persistent
with path-copying AVL trees and obtains worst-case logarithmic
updates, splits and concatenations creating logarithmically many new
nodes, where the splay-based alternative loses its amortized analysis
once an unbalanced past version can be reused indefinitely; its
equality and longest-common-extension queries rest on fingerprints
and are probabilistic, and its grammar variant addresses repetitive
data. Its balance and persistence analysis transfers; exact equality
must be retained for recognition. Relaxed-radix-balanced vectors
{citep StuckiRompfUrecheBagwell2015}[] are the wider-fanout design
with logarithmic split and concatenation for parallel work. Two
editor implementations are source-reuse candidates rather than
published crates: Zed's
[sum tree](https://github.com/zed-industries/zed/tree/main/crates/sum_tree),
Apache-2.0, a persistent B-tree with shared nodes and generic
composable summaries, and
[crop](https://github.com/noib3/crop), a copy-on-write text B-tree;
both carry UTF-8 interfaces that arbitrary bitstrings would need
adapted, and both were source-reviewed, not benchmarked. The public
[editing traces](https://github.com/josephg/editing-traces) used by
rope benchmarks can supplement traces of the language's own parsing
and checking when the designs are compared.

Content-defined chunking deduplicates large changing blobs by cutting
at content-determined boundaries so that an insertion resynchronizes
after a bounded distance in expectation:
[FastCDC's Rust implementation](https://github.com/nlfiedler/fastcdc-rs)
and
[VectorCDC, FAST 2025](https://www.usenix.org/conference/fast25/presentation/udayashankar)
are the practical starting points. Resynchronization is a
workload-dependent benefit, not a worst-case bound on the chunks an
edit affects; it applies to cold payloads and distribution artifacts
first, since low-entropy topology and tiny syntax nodes need their
own evaluation.

## Word-level bitstrings

Every arbitrary-precision natural number library stores its limbs
least significant first and normalized, without high zero limbs:
GMP's `mpz`, whose
[limb representation](https://gmplib.org/manual/Integer-Internals)
is the model for word packing and arithmetic, `malachite`, `ibig`,
`dashu` and `num-bigint` in Rust, and Lean 4's own `Nat`, which is a
tagged scalar below `2^63` and a GMP object above it. A bitstring is
not a number: its leading zeros are significant, so each of these
needs a bit length beside it, and GMP's normalization of leading zero
limbs cannot serve as bitstring identity without that length. The
libraries that track a bit length, `bitvec`, `bit-vec`,
`smallbitvec`, `sucds` and `vers-vecs` in Rust and `sdsl`'s
bit vector in C++, agree on packing least significant bit first
within little-endian words with the dead bits of the last word zero,
which makes equality and hashing word-wise operations. The small
forms are the instructive part. `dashu` stores two words inline in
a 24-byte representation whose discriminant is the sign of its
capacity field; `smallbitvec` stores up to 62 bits in a single
machine word whose length is marked by a sentinel one bit above
the data, with the low bit distinguishing the inline form from a
heap pointer; `compact_str` stores 24 bytes inline by using an
invalid UTF-8 byte as its tag. The pattern is uniform: the inline
threshold is the size of the heap descriptor that must be paid
anyway, and the discriminant is hidden in a value the heap form
cannot produce.

The sentinel encoding is the bijection between bitstrings and
positive natural numbers in which the string `w` is the number whose
binary numeral is `1w`. The repository already uses it as
{name}`Geb.Oitavem.rank` and {name}`Geb.Oitavem.unrank`, shifted by
one. Under it, a bitstring of up to 62 bits is one unboxed scalar in
Lean's runtime, its length is the position of the highest set bit,
concatenation is a shift and an or, and a bitstring longer than
that is a GMP number with the same operations on limbs.

Two facts about Lean's runtime, checked in this session, bound this
choice. The built-in hash of a `Nat` is its value truncated to 64
bits, so `2^300 + 7` hashes to `7`; and there is no primitive that
exposes the limbs of a large `Nat`, so extracting them by shifts
costs time quadratic in the number of limbs. A long label in Lean is
therefore hashed in linear time only when it is stored as a
`ByteArray`, which has a linear-time hash and a 24-byte header, or
as a sequence of word-sized scalars. The append of a `BitVec` is a
shift followed by an or without a modulus, so its cost is that of
the underlying `Nat` operations.

The word width is a compile-time parameter of a backend with a
bit-level meaning, so that runtime words of 8, 16, 32 or 64 bits
represent the same values; Bend and HVM2 add 24-bit numerics to the
list. The implementation uses native unsigned arithmetic, shifts,
masks and popcount, with vector instructions where available and a
portable fallback, never shifts by a full width, and never relies on
overflowing length arithmetic. A bitstring remains a length together
with its bits even where the pair is implicit in block metadata.

For length codes, the Elias gamma and delta codes decode with one
count-leading-zeros instruction and a shift, and the byte-oriented
codes of the systems world, LEB128 and the prefix-varint family,
decode with one unaligned load and a count-trailing-zeros; the
vectorized codes, Stream VByte and group varint, pay off only for
arrays of integers, not for one length per node.

## Hashing

The hash functions of the fastest current hash tables, `foldhash`,
`rapidhash`, `ahash` and XXH3, consume words in sequence with a seed
and a length finalization; none is an associative fold, so the hash
of a concatenation is not computable from the hashes of the parts,
and each is documented as unstable across versions, which excludes
them from hashes that are persisted or compared across
implementations. A polynomial hash is composable,
`h(a ‖ b) = h(a) · x^|b| + h(b)`, and its Horner evaluation modulo
an `O(log n)`-bit prime keeps an `O(log n)`-bit accumulator, which
places it in `FLOGSPACE` {citep KarpRabin1987}[]. The iteration of a
fixed compression function over a stream, the Merkle-Damgård
construction of SHA-256 {citep NIST2015}[], is a finite-state
transducer with a length counter, hence also in `FLOGSPACE`. BLAKE3
hashes a stream as a Merkle tree over 1024-byte chunks whose left
subtrees are full, and its incremental implementation keeps a stack
of chaining values indexed by the one bits of the chunk count, at
most 54 of them {citep OConnorAumassonNevesWilcoxOHearn2020}[]; its
[specification and implementations](https://github.com/BLAKE3-team/BLAKE3)
are the concrete fixed-width, chunked, vectorized and parallel model
to study. In general the Merkle root of a leaf sequence in
binary-numeral shape is computed in one pass with `O(log n)` space
{citep Champine2021}[]: a frontier of `O(log n)` digests plus
logarithmic counters, which is `O(log n)` bits for a fixed digest
width and `O(log^2 n)` bits if the security parameter itself grows
as `Θ(log n)`. Emitting every internal node needs an output
convention and possibly recomputation, not their retention. A Merkle
root that follows the shape of a rose tree, each node hashing its
label with its children's digests, has a pending-digest stack of
depth equal to the tree's depth, `Θ(depth · digest)` bits, and no
logarithmic-space algorithm for it over unbounded depth is known;
the shape-independent root over the serialization is the one that is
provably in `FLOGSPACE`.

A Merkle root over physical pages changes when pages split or
rebalance, so a semantic content identifier requires a canonical
encoding or a canonical chunking rule; streaming a canonical flat
encoding gives a stable digest but may rehash linearly after an
insertion, so it promises no logarithmic persistent update. A
fingerprint rejects inequality quickly and certifies nothing: an
exact type checker settles the equal-fingerprint case by pointer
equality of shared objects, by exact comparison, or by interning
that checks collisions.

## Complexity of recognition

The model is the conventional one: a read-only two-way input, a
write-only output and `O(log N)` bits of work tape for input length
`N`. A constant number of word-RAM counters meets the bound when
their widths grow as `Θ(log N)`; fixed 64-bit counters have a finite
supported size, which the code checks. Input storage, result
storage, persistent caches and parallel workers are charged
separately, never to the work tape and never omitted from a
practical memory report.

Membership in a parenthesis language is in logarithmic space, with
a counter for the excess, and logarithmic-space translators exist
between representations {citep Lynch1977}[]; the excess counter
accepts a forest, the empty one included, and a single tree needs in
addition a nonempty input and strictly positive excess on every
proper nonempty prefix. The one-sided Dyck
languages `D_k` for every `k`, and the structured and bracketed
context-free languages, are in DLOGTIME-uniform `TC^0`
{citep BarringtonCorbett1989}[]; `D_1` is not in `AC^0`, since an
instance of exact-half counting embeds in it (derived). The position
of the parenthesis matching a given one is definable in first-order
logic with majority quantifiers from prefix counts, hence computable
in `TC^0` (derived from {citep BarringtonCorbett1989}[]); an
ALOGTIME algorithm computes the depth of a node, its `i`-th child
and the ancestor relation from the parenthesis word
{citep Buss1997}[]. The Boolean formula value problem is in
ALOGTIME and complete for it {citep Buss1987}[]. A fixed number of
nested scans over the input, each with its own counters, stays in
logarithmic space at polynomial time; this is how a fast cached
recognizer can agree exactly with a slower small-space witness
without inheriting its running time or workspace.

For the streaming setting the picture is different. `D_1` has a
deterministic one-pass algorithm with a counter. `D_2` requires
linear space for deterministic one-pass algorithms; one-pass
randomized algorithms use `O(√n log n)` space, which is optimal up
to polylogarithmic factors, and a bidirectional two-pass randomized
algorithm uses `O(log^2 n)` space {citep MagniezMathieuNayak2014}[].
Unidirectional multi-pass algorithms with `p` passes and `s` space
need `p · s = Ω(√n)` {citep ChakrabartiCormodeKondapallyMcGregor2013}[]
{citep JainNayak2014}[]. These bounds bind only checkers that read
the input in one direction a bounded number of times; a
logarithmic-space machine with random access to its input, the
definition of `L`, is unconstrained by them, and typed matching is
in `TC^0 ⊆ L`. Logarithmic space is therefore not one-pass
streaming: subtree equality and naturality checks may reread or use
external storage, and an infinite M-type stream never supplies the
end-of-input test a finite W-value needs, so a stream checker
recognizes completed framed values and maintains prefix invariants
rather than deciding the whole stream.

Compressed sharing changes the input-size question. A small directed
acyclic graph unfolds into an exponentially larger tree, so a
logarithmic-space claim in the length of the flat encoding is not one
in the size of the compressed graph, and polynomial work in the
unfolded size may be exponential in the stored bytes; external
references add validity and termination rules of their own. The flat
finite format is certified first, and a graph format is studied with
its own size measure rather than by transfer.

Tree canonization, and so unordered tree isomorphism, is in `L`
{citep Lindell1992}[]; with the string encoding it is in ALOGTIME,
and the encoding matters: from the pointer encoding the descendant
relation is `L`-hard, so ALOGTIME algorithms cannot parse
pointer-encoded trees unless ALOGTIME equals `L` {citep Buss1997}[].
Tree isomorphism is `NC^1`-complete for the string encoding and
`L`-complete for the pointer-list encoding
{citep JennerKoblerMcKenzieToran2003}[]. Ordered tree equality on the
string encoding is equality of serializations, in `AC^0`; equality
of two subtrees inside one serialization is in `TC^0`, their
endpoints coming from the matching function; and equality with a
fixed relabelling of another subtree stays in `TC^0`, the offsets
becoming prefix sums of label lengths (derived). Equality up to a
relabelling that is not fixed is as hard as graph isomorphism and
is to be avoided. Membership in a fixed recognizable tree language,
the term string given, is `NC^1`-complete {citep Lohrey2001}[]. No
published result places type checking of a first-order or dependent
calculus in `L` or `NC^1`; the tree-automaton and monadic
second-order results are the closest, and they require a finite
label alphabet.

The function algebras that capture logarithmic space are: for
predicates, Kristiansen's successor-free algebra
{citep Kristiansen2005}[], which the repository has transcribed and
proved sound; for functions, Oitavem's `Logs`
{citep Oitavem2010}[], transcribed with its soundness in progress,
and Neergaard's `BC^-_ε`, the first algebra characterizing the
logspace-computable functions rather than predicates
{citep Neergaard2004}[]; and, by types rather than recursion
schemes, LogFPL {citep Schopp2006}[] and IntML, in which a term of
the word-to-word type represents exactly a logspace-computable
function, and a term not mentioning the integer type evaluates in
constant space {citep DalLagoSchopp2016}[]. On ordered structures,
first-order logic with deterministic transitive closure captures
`L` and with transitive closure captures `NL`
{citep Immerman1987}[]; the Dyck languages are not regular, so tree
well-formedness is not definable in monadic second-order logic over
the string, and is definable in first-order logic with majority.
Following a forward pointer chain is complete for `L`
{citep CookMcKenzie1987}[], which is what the validation of a
length-prefixed format reduces to.

## Parallel evaluation

In the work-span model, an Euler tour and a parallel prefix give
preorder numbers, depths and subtree sizes in `O(n)` work and
`O(log n)` span; matching parentheses takes `O(log n)` time on
`n / log n` processors {citep BarOnVishkin1985}[]; tree contraction
folds any bottom-up computation whose partial results compose over
an arbitrary tree in `O(log n)` time {citep MillerReif1985}[]. The
total and minimum-prefix excess of a parenthesis block form an
associative summary, the total and minimum components of the range
min-max tree, so independent block scans followed by a balanced
reduction, or cached summaries in a persistent tree, compute the
whole word's summary; § What is proved has the algebra with its
proofs. A shape-following Merkle hash has span proportional to the
depth, since a cryptographic compression function does not compose;
the hash of the serialization has span `O(log n)`.

The Higher-Order Virtual Machine 2 is an interaction-combinator
evaluator {citep Taelin2024}[] {citep Lafont1997}[] whose port is a
32-bit word of a 3-bit tag and a 29-bit value, whose node is a
64-bit pair of ports, whose unboxed scalars are 24-bit, and which
has no native constructors, arrays or strings, one duplication
label, and strict order-invariant reduction whose cost is the
interaction count. Its front end Bend 1 encodes an `n`-ary
constructor as a chain of binary nodes, four nodes and 32 bytes per
binary constructor against one node and 8 bytes per native pair. As
of September 2026 both are frozen: HVM2's last commit is of August
2024, and the live Bend 2 compiles to C, Metal, CUDA and
JavaScript through a runtime that is not an interaction-net
runtime. The successor, HVM4, is a C runtime for the interaction
calculus, a term language whose four rules are the symmetric
combinator rules with a lambda-application orientation, extended
with explicit duplication and superposition that control lazy
sharing inside lambdas: a term is a 64-bit word of an 8-bit tag, a
24-bit extension and a 32-bit value; numbers are unboxed 32-bit
unsigned words; constructors are native and flat, of arity up to 16,
their fields consecutive heap words; structural equality and
matching are primitive interactions; duplication is lazy and
labelled, so nested cloning is sound and an unshared subtree is never
copied; and reduction is lazy. Dynamic terms live in a mutable
bump-allocated heap whose allocation counter grows during evaluation
and is released at teardown, so the inspected commit has no
long-lived reclamation strategy, and it has no CUDA backend,
worker-thread scheduler or external-call layer. Its documented
calculus is relevant to the language's foundational computation
model; it is not by itself a correctness or cost theorem identifying
every runtime operation with Lafont's combinators, which a
translation and a cost correspondence would have to supply. Nothing
compiles to it yet, and its GPU port is history rather than current
code. Every one of the three imposes that structure be balanced to a
known depth for a GPU to schedule it, and none gives duplication the
constant cost of a reference-counted read-only share: duplication may
propagate through a consumed value, and a packed immutable array or
block handle would need a runtime primitive with its own semantics,
or an encoding whose allocation cost is measured.

## Compilers and syntax tooling

The persistent collections of language runtimes are 32-way tries:
Clojure's vector and hash-array-mapped trie {citep Bagwell2001}[]
copy one node per level on update and batch construction through a
transient owned by one thread; CHAMP keeps two bitmaps per node,
payload from the front and sub-nodes from the back of one array,
with a canonical form that lets structural equality fail on a
bitmap mismatch, and measures 16 to 23 percent less memory than
Clojure's and 65 to 68 percent less than Scala's previous maps
{citep SteindorferVinju2015}[]; a trie's hash order is not the
semantic order of a node's children, so it serves environments,
symbol tables and memo tables, and a sequence structure serves
children. Syntax trees separate an immutable, parent-free,
width-carrying green tree from a red façade of cursors with offsets:
Roslyn caches only green nodes of at most three children, in a
direct-mapped table keyed by the children's identities; `rowan` in
rust-analyzer lays a green node out as one allocation of reference
count, kind, text length, child count and children with relative
offsets, interns nodes of at most three children, and measured 17
percent memory saved by it, and its child replacement rebuilds the
whole child collection, so its work is the node's arity, not
logarithmic in it; tree-sitter packs a leaf into the 8 bytes of a
pointer with the inline flag in the pointer's low bit, allocates a
node's children immediately before its header in one block, reuses
the edited old tree during a reparse, and copies a tree cheaply for
concurrent use, so that editing one snapshot never mutates the
older snapshot a language-server request is reading, source
coordinates being kept apart from immutable semantic identity;
`rustc` interns every type, with pointer equality and pointer
hashing, and caches a stable hash and flags beside it, its
[arena and interning design](https://rustc-dev-guide.rust-lang.org/memory.html)
and LLVM's
[FoldingSet](https://llvm.org/doxygen/FoldingSet_8h_source.html)
being the scoped-allocation and exact-uniquing models, in which
pointer equality is meaningful after interning and arena lifetime
and collision handling still matter to an editor retaining old
versions; Lean's own `Expr` caches a 32-bit hash, an approximate
depth, flags and the loose bound-variable range in one 64-bit field
computed by the constructor, and its `replace` consults its cache
only on subterms whose reference count shows them shared.
Hash-consing as a discipline is {citep FilliatreConchon2006}[];
Lean's runtime performs the update in place when the reference count
is one {citep UllrichDeMoura2019}[].

For an editor, the unit of caching is a checked value under a
particular signature, index, environment and restriction context; a
content digest alone omits these dependencies. The editor reuses
unchanged scopes and subtree checks, cancels obsolete requests, and
accounts for every retained root. Batch construction inside a
uniquely owned builder, the transient of Clojure's collections,
reduces allocation before any globally compressed representation is
attempted; published snapshots remain immutable.

The structural JSON parsers are the measured state of the art for
turning a serialized tree into an indexed one. `simdjson` finds the
structural characters of 64-byte blocks branchlessly with vector
instructions and a carry-less multiplication for the prefix parity
of quotes, then writes a tape of 64-bit words in which every
container's opening word holds the index of its closing word and a
child count, so that a subtree is skipped in constant time; it
exceeds two gigabytes per second where the previous parsers reached
half of one {citep LangdaleLemire2019}[]; its
[parse-many](https://github.com/simdjson/simdjson/blob/master/doc/parse_many.md)
interface processes a stream of documents in a bounded buffer,
which is not constant-space validation of one arbitrarily large
dependent object. `yyjson` stores each value in 16 bytes with the
size in the high 56 bits of a tag word and each container's byte
extent, again for constant-time skipping. The formats of the systems
world confirm the same division: length prefixes, as in Cap'n Proto,
FlatBuffers, DER, Protobuf and the WebAssembly binary format, buy
constant-time skipping and parallel decoding and cost, per node,
tens to hundreds of bits and a validation that follows a pointer
chain, with depth caps of 64 in the verifiers of FlatBuffers and
Cap'n Proto; counts and brackets, as in CBOR and MessagePack, cost a
few bits per node and are checked by counters. Content-addressed
stores, Git, IPLD and Unison, pay 20 to 64 bytes per child link for
Merkle identity.

# Design space

The requirements and the literature fix the shape of the design:
two faces joined by conversions, each face chosen from a short list,
with a persistent sequence beneath whichever face holds a large
value.

## The serialized face

Four forms were considered.

* Interleaved DFUDS with Elias-coded lengths, the repository's
  present spelling: each node in preorder is its arity in unary, a
  zero, the delta-coded length of its label, the label, and then its
  children. It is streamable, a producer emitting node by node
  without knowing the total; it is checked in one pass with two
  counters for the tree and the arity stages, and its label and
  index stages have the witnessed logarithmic-space recognizer at
  quadratic time. Its overhead is the arity, `2n` bits over the
  tree, plus the length code, `2 + log ℓ + 2 log log ℓ` bits per
  label.
* Sectioned DFUDS: the same three streams, arity bits, length codes
  and payloads, stored as three sections behind a header of section
  lengths. The topology is then checked in `TC^0`, by a prefix sum,
  and every stage parallelizes by prefix sums; a static index of a
  third of a bit per node makes navigation logarithmic; the label
  section is what a variable-length-cells array is, and its
  boundaries may be Elias–Fano cumulative endpoints instead of
  per-label codes. It is not streamable without knowing the section
  lengths.
* A word-aligned profile of either: arities and lengths as
  prefix-varints in bytes, labels of at least a word padded to a
  byte boundary. It trades at most seven bits per long label, a
  factor below 1.11 for labels of 64 bits or more, for aligned
  loads; short labels stay bit-packed, which keeps the overhead on
  trees of small labels within the succinct bound.
* Length-prefixed subtrees, the tape of the JSON parsers and the
  format of the zero-copy serializers. It buys constant-time skips
  and independent decoding of siblings, and its validation is a
  pointer chase, complete for `L`, with a stack of pending end
  positions in a linear-time checker. It is rejected as the
  recognized form and retained as an optional side index, which does
  not change what is recognized.

The two DFUDS forms are related by transcoders in logarithmic space,
each a matter of locating the `i`-th node's label by a counter, so a
witnessed recognizer for one gives one for the other by composition.
The interleaved form is the canonical one, since its witness exists;
the sectioned form is the storage form.

Whichever form is stored or transmitted carries a version, explicit
counts, a specified bit order, bounded length headers and zeroed
unused bits in its final word, and its reader rejects truncation,
trailing material, arithmetic overflow, inconsistent lengths and a
second root. An uncompressed boundary mode is verified first; a
compressed mode needs its own accounting and its own equivalence
theorem. These are requirements on a specification, not a frozen
wire format.

## Labels

Three representations, related by the word width `w`:

* The sentinel natural number, `1w` read as a numeral: in Lean a
  `Nat`, scalar to 62 bits and GMP above; in Rust a `u64` with the
  same sentinel below 63 bits; proofs by the existing `rank` and
  `unrank` lemmas and `Nat.testBit`.
* A limb vector with an inline small form: the `dashu` layout of a
  length word and two inline words, the length above 128 marking the
  heap form; in Lean a `ByteArray` with a bit length. Linear-time
  hashing and comparison, aligned loads.
* A balanced tree of word chunks, each chunk a label of at most `w`
  bits, the tree's shape canonical in the label's length. It is the
  form the interaction-net runtimes need, since their unboxed
  scalars are 24 or 32 bits and their constructors are small; it
  gives logarithmic-span folds, comparisons and hashes of a long
  label; and it costs one node per word, which a limb vector avoids.

The three agree on semantics through a computable isomorphism with
`List Bool`; a host uses the one its runtime favours, and the
chunk tree is the canonical one for hashing, so that a hash
computed on one host equals the hash computed on another. A label
under edit, or one larger than a page, takes the persistent page
sequence below as its limb vector.

## The in-memory face

The rose tree as a nested inductive type with a children array,
the label inline when short, is the form every host builds fastest:
a child access is a load, against half a microsecond in a succinct
tree, and construction is one allocation per node. Its refinements,
each measured in a shipped compiler:

* A cached word-sized hash in the node header, computed at
  construction, as Lean's `Expr` does; equality then fails on a hash
  mismatch, and a subtree digest of a rebuilt tree costs only the
  path rebuilt when the digests are kept beside the tree.
* Hash-consing of small nodes, at most three children, as Roslyn
  and `rowan` do; equality of hash-consed subtrees is pointer
  equality, and the hereditary naturality check, whose cost is its
  subtree comparisons, becomes linear.
* Children in one allocation with the header, as tree-sitter and
  `rowan` do, in the hosts that allocate by hand.
* On an interaction-net runtime, a node as a native constructor of
  at most sixteen fields where the runtime has them, and as a
  balanced tree of pairs where it has only pairs, the arity carried
  in the label.

Two costs of this face are its semantic shape's. Replacing one child
of a node copies the node's whole child array, so a node of large
arity, a block of many statements, holds its children as a balanced
persistent sequence above a threshold the editor traces set, and a
child replacement then copies logarithmically many entries. And an
edit deep in a semantic chain copies the chain's ancestors, one node
per level, which no physical balance removes: materializing a changed
recursive spine costs its semantic depth, a dependent fold has a
critical path of that depth, and an incremental type checker may
invalidate distant users of a changed binding however small the
changed span. The face is not succinct, and a cryptographic digest per
node is larger than the node, so digests are selective, kept beside
the tree for the definitions and nodes that need identity, not in
every header.

No succinct dynamic tree serves this face: none is persistent, and
all are slower per operation by more than an order of magnitude.

## The persistent page sequence

Beneath either face, a value too large for one allocation is a
persistent sequence of immutable pages. The topology is the
depth-first opening and closing bit pair of each node, the labels
follow in opening order as exact lengths and concatenated payload
bits, and a subtree is then an interval of topology bits, an interval
of lengths and an interval of payload bits. One immutable root record
ties the three sequences together, and a transaction publishes every
changed root at once. The physical tree over the pages balances
itself independently of the semantic tree, so a point edit copies a
path of the physical tree and not the ancestors of a semantically
deep node.

:::table +header
*
  * Component
  * Representation
  * Contract
*
  * Topology
  * Packed balanced parentheses in persistent pages
  * One root; cached counts and excess summaries agree with the bits
*
  * Labels
  * Exact lengths plus packed concatenated payloads
  * One length per opening; their sum is the payload bit count
*
  * Navigation
  * Relative counts in branch nodes; optional local static indexes
  * No stored global offset that a suffix-wide update would rewrite
*
  * Identity and caches
  * Shared handles, optional fingerprints, exact fallback comparison
  * Equality and type checking remain deterministic and exact
:::

A branch node carries subtree lengths, opening counts and the excess
total, minimum and maximum of its span, the summary algebra of
§ What is proved supplying the total and minimum part; a balanced
binary tree, the AVL of the prototype, is the small testable
reference, and a wider fanout reduces pointer chasing at the cost of
copying more entries on each changed path, a tradeoff to measure on
editor traces before fixing a fanout. Page sizes of 256 bytes,
1 KiB and 4 KiB are the first comparison points. Leaf coalescing,
occupancy and reclamation are part of the contract, not
implementation details left open.

Let $`P` be the number of occupied pages, $`b` their payload
capacity in bytes, $`w` the word size in bits and $`f` the fanout.
Under a maintained balance and occupancy invariant, a path-copying
point edit copies $`O(b + f w \log_f P / 8)` bytes; rebuilding a
page's summary is $`O(b)` work by a byte-table scan, with word and
vector implementations improving the constant; a splice adds the
newly written data and the rebuilding of its boundary pages. A
snapshot is constant handle work, and dropping the last reference to
a large unshared region takes linear reclamation work that must not
block an editor request. Physical balance does not make every
semantic operation logarithmic: a scan or serialization reads or
writes its output, and the semantic-depth costs of § The in-memory
face remain.

The space of this sequence is practically compact, not automatically
succinct. Fresh pages are full, but half-full pages after long edit
histories approach twice the payload space before metadata, which
fails the required factor; a smaller factor needs a stated occupancy
and repacking policy whose update work and retained versions are
charged. Fixed-size pages with fixed-size pointers cost, in a
word-RAM with $`w = \Theta(\log N)`, about $`O((N/B)\log N)` bits of
branch metadata for $`N` encoded bits in pages of $`B` bits; making
that $`o(N)` needs pages growing as $`\log^2 N` or compressed
addressing, together with vanishing slack, and that addresses the
metadata term alone. A 256-bit digest per 1-KiB page adds 3.125
percent before any internal digest, one more reason digests are
selective. § The persistent page-sequence measurements gives the
prototype's figures.

## Hashing

Two hashes, for two purposes. The hash over the serialization, a
polynomial hash for speed or BLAKE3's tree mode for collision
resistance, is in `FLOGSPACE` and has logarithmic span. The
shape-following Merkle hash, each node's digest over its label's
chunk hash and its children's digests, is the one that hash-consing
and a digest table beside the tree maintain incrementally, and it is
in `FLOGSPACE` only on trees of logarithmic depth. Both are defined
on the canonical chunking of labels and on canonical serialization
bytes, never on physical pages, so that every host computes the same
value and no page split changes it. Neither certifies equality: a
digest match is followed by pointer equality, exact comparison or
collision-checked interning wherever the type checker's verdict
depends on it.

## What the complexity results decide

The child-index stage is a typed-matching problem, so no one-pass
checker in small space exists for it, and the practical checker is
the linear-time one with a stack of pending arities and index
prescriptions, `O(depth)` words, logarithmic on balanced trees. The
logarithmic-space guarantee on every input is the witnessed
quadratic-time recognizer, a separate function extensionally equal
to the practical one; its nested scans keep the workspace
logarithmic at polynomial time, and its hypothesis is effective,
complexity-bounded enumeration and comparison of the signature's
shapes, morphisms and local naturality tests, not their mathematical
finiteness alone. The naturality stage compares subtrees under a
fixed relabelling and is in `TC^0` on the string encoding, so it adds
no complexity class; its practical cost is quadratic without sharing
and linear with hash-consing. A parallel checker follows the JSON
parsers: prefix sums over the sectioned form give every node its
parent and position, and each stage is then a map. The witnessed
form is stated over the flat finite format; a shared graph format,
with its own size measure, is a separate certification.

The certification of a new serialization then has four
obligations: a specification with its decode and encode laws,
invalid encodings included, and a statement of how the reference
witness reads each logical input bit; a size-controlled
logarithmic-space translation to the witnessed form, or a direct
algebraic recognizer, a translation coming with its polynomial length
bound and a random-access simulation that never materializes the
intermediate word on the work tape; the existing label, edge,
local-presheaf-test and enumeration witnesses, with a proof that the
optimized recognizer is extensionally equal to their composition;
and the general Oitavem machine soundness proof as a separate
dependency, the implementation itself neither interpreting the
expression nor running in logarithmic space.

# Prototypes and measurements

The prototypes are literate modules included below, test modules,
a benchmark executable, Rust programs and interaction-net programs.
They establish the semantic layer with proofs, the serialized form
with proofs where the repository already had them and tests where it
did not, the summary algebra of the page sequence with proofs, and
the costs by measurement. Every measurement in this section is from
a run on one machine, an AMD Ryzen AI 9 HX 370 laptop processor
under WSL2 with sixteen logical processors exposed and an NVIDIA RTX
4070 Laptop GPU with 8 GiB, without controlled clock frequency or
confidence intervals; each reports the best or the median of a few
repetitions as its subsection states; and each is a comparison
between representations on the same machine, not a characterization
of any of them, nor of a different processor, compiler, tree
distribution or end-to-end compiler throughput.

## What is proved

{name}`Geb.RoseTree` is the W-type of the signature whose shapes are
a label with an arity, with the list-of-children constructor
{name}`Geb.RoseTree.node` and its projections, the induction
principle {name}`Geb.RoseTree.ind` and the fold
{name}`Geb.RoseTree.elim`; it generalizes the concrete-syntax
prototype's rose tree over `Fin k` to any label type, and unifying the
two is a follow-up. A label is its enumeration index, a natural
number, and {name}`Geb.Bits.append_rank`, {name}`Geb.Bits.take_rank`,
{name}`Geb.Bits.drop_rank`, {name}`Geb.Bits.getBit_rank` and
{name}`Geb.Bits.length_rank` prove the word-level operations equal to
the list operations. {name}`Geb.RoseTree.equivBin` rotates a rose
tree to the binary tree whose left spines carry the children, so that
the repository's Elias-length encoding serializes rose trees,
{name}`Geb.RoseTree.wire`, injectively
({name}`Geb.RoseTree.wire_injective`), and its recognizer accepts
exactly the serialized rose trees
({name}`Geb.RoseTree.validBool_iff_wire`); the recognizer's
linear-time, logarithmic-space machine and its expression in
Kristiansen's algebra are the repository's, unchanged. The
serialization is therefore proved injective and its first
recognition stage proved in `FLOGSPACE` by composition, with no new
complexity proof.

The summary algebra of the page sequence is
{name}`Geb.SuccinctTree.Summary`, the total and minimum prefix excess
of a parenthesis block, with the combination
{name}`Geb.SuccinctTree.Summary.append` of adjacent blocks.
{name}`Geb.SuccinctTree.Summary.append_assoc` permits any
reassociation of a block reduction, which is what parallel block
scans and cached summaries in a persistent tree rest on;
{name}`Geb.SuccinctTree.summarize_flatten` proves that grouping the
steps into blocks preserves the summary;
{name}`Geb.SuccinctTree.scan_eq_summarize` proves the two-integer
accumulator scan equal to the specification; and
{name}`Geb.SuccinctTree.balanced_eq_true_iff` proves the acceptance
test exact, total zero and every prefix nonnegative, which accepts a
forest. {name}`Geb.SuccinctTree.wordSummary` interprets a word at an
explicit width. The proofs use no new axioms. They establish the
correctness of the summaries, not a machine-space bound, an Oitavem
witness, an isomorphism between a labelled wire format and the
W-type, or the correctness of the Rust or interaction-net programs.

## What is tested

{name}`Geb.Packed.encode` writes the same bits into a byte buffer at
word level, and {name}`Geb.Packed.run` reads a buffer by a fold over
its words with a mode, the repository's streaming scanner at word
level, passing over a payload's whole words in one step; it yields the
recognizer {name}`Geb.Packed.recognize` and the decoder
{name}`Geb.Packed.decode`. The tests check the encoder's bits against
{name}`Geb.RoseTree.wire` on trees of each shape the format
distinguishes, the recognizer against
{name}`Geb.BitTree.Elias.validBool` on every word of length at most
ten, and the decoder on round trips. The Rust crate under
`prototypes/rust/rosetree/` implements the same serialization and
checks its bytes against three vectors printed by the Lean encoder,
so the two implementations agree byte for byte on the wire.

The summary algebra's test module checks malformed topology, word
boundaries and the composition of word summaries, the composition law
being proved for all word pairs and the examples executed by Lean's
interpreter during the build; it also holds the timing functions of
§ The interpreter and parser measurements, which reject an unexpected
result and assert nothing about the timings. The Rust page-sequence
program under `Geb/Prototypes/SuccinctTree/` carries two tests: one
exhausts every 16-bit topology and every closing query on it, and one
applies 1,500 splices and updates branching from older versions
against a flat oracle, checking balance, lengths, summaries and every
retained version.

The first version of the word-level reader iterated by the natural
number recursor over the remaining bit count, once per node. A strict
recursor evaluates its whole tower before the first step, so each
call cost the buffer's length and the recognizer was quadratic; it
did not finish on a tree of a hundred thousand nodes. The rule that
every recursion goes through a recursor is compatible with
linear-time streaming, but only in the form the repository's scanner
already has: one fold over the input carrying a mode, never a
recursor call per element whose fuel is the input's length.

## The Rust measurements

The Rust crate's pointer tree stores a node as a 32-byte label, two
words inline and a length, and a boxed slice of children, 48 bytes
per node before the children's array; the numbers are nanoseconds
per node on a full binary tree of 131,071 nodes with 8-bit labels,
the syntax-like regime, a single thread, the best of a few
repetitions.

:::table +header
*
  * Operation
  * ns per node
*
  * build (allocation)
  * 26
*
  * fold (node count)
  * 1
*
  * serialize (wire)
  * 8
*
  * recognize (one counter, streaming)
  * 22
*
  * decode (stack)
  * 60
*
  * equality (structural)
  * 2
*
  * hash (shape-following fold)
  * 20
*
  * tape build (preorder words with skip pointers)
  * 20
*
  * tape walk by skip pointers
  * 1
*
  * balanced-parentheses build (`vers-vecs`)
  * 3
*
  * balanced-parentheses walk, parent and first child
  * 11
*
  * pointer walk, same traversal
  * 1
:::

The serialized form of that tree takes 18 bits per node: 8 for the
label, 8 for its delta-coded length, and 2 for the arity. On the
blob-like regime, four nodes with labels of `2^24` bits, the
serializer runs at 4.4 gigabytes per second, the recognizer at 6,
the shape-following hash at 6.8 and equality at 37, all a single
thread.

## The Lean measurements

The Lean benchmark, `lake exe rosebench`, times the same operations
on the same trees in Lean's compiled code, with the list forms beside
the word-level forms.

The first table is the syntax-like regime, a full binary tree of
131,071 nodes whose labels are indices below 200, so of about seven
bits, in nanoseconds per node; the list forms are on the smaller tree
of 9,841 nodes, since the list recognizer is quadratic and takes
seventeen seconds there.

:::table +header
*
  * Operation
  * ns per node
*
  * build (allocation)
  * 54
*
  * fold (node count)
  * 42
*
  * serialize, word level
  * 250
*
  * serialize, list form (9,841 nodes)
  * 687
*
  * recognize, word-level streaming fold
  * 622
*
  * recognize, list form (9,841 nodes)
  * 1,758,170
*
  * decode, word-level streaming fold with a stack
  * 465
*
  * equality (fold)
  * 149
*
  * hash (fold)
  * 49
:::

The second is the blob-like regime, four nodes whose labels are
natural numbers of `2^20` bits, in microseconds for the whole tree.

:::table +header
*
  * Operation
  * microseconds
*
  * build
  * 397
*
  * serialize, word level
  * 258,865
*
  * recognize, word level
  * 2,018
*
  * decode, word level
  * 1,846
*
  * equality
  * 27
*
  * hash (truncating)
  * 2
:::

The serialized tree of 131,071 nodes takes 13.8 bits per node, the
label and its length code each about seven and the arity two.

## The interpreter and parser measurements

The summary algebra's test module times, in Lean's interpreter
during elaboration, the existing native Elias scanner
{name}`Geb.BitTree.Elias.Scanner.validBool` against the shared
interpretation of the algebraic recognizer on the encoding of one
leaf; routine elaboration runs payload lengths zero and one, and
passing {lit}`[0, 1, 8, 32]` to {lit}`benchmarkRecognition` runs the
recorded comparison. A 32-bit payload gives a 43-bit input, on which
the shared algebra interpretation took about 11.2 seconds and the
native scanner about 28 microseconds, a factor of four hundred
thousand; at 17 input bits the two took 840 milliseconds and 23
microseconds, and the smaller inputs show the interpreter's warm-up
in the native figures. These are single diagnostic evaluations in the
interpreter, not compiled code; they justify replacing interpreted
primitives extensionally, and they estimate no speedup of the whole
type checker.

The same module times the repository's concrete-syntax parser on a
chain and on a wide tree of the rose syntax over three constructors,
measuring parsing plus exact equality with printing excluded, in the
interpreter: at 256 links or children, an input of 1,285 characters,
the chain took 138 milliseconds and the wide tree 74; at 64, an input
of 325 characters, 5.8 and 4.2 milliseconds. Compiled code and
incremental checking need their own benchmarks before a latency
target is set. The observations are retained in {lit}`lean.csv`
beside the Rust program; cached build output replays an older
observation, so a replay is not a fresh run.

## The persistent page-sequence measurements

The program {lit}`bench.rs` under `Geb/Prototypes/SuccinctTree/`
uses only the Rust standard library: leaves hold byte arrays, AVL
branches cache summaries and lengths, and immutable nodes are shared
by `Arc`. It implements point reads and updates, split and
concatenate, byte-aligned splices, matching-close queries by cached
summaries, and range summaries; it is a sequence prototype, not a
labelled-tree codec, and its splices do not coalesce fragments, so it
has no succinctness guarantee under long histories. The input is a
byte sequence in which every byte holds four empty roots, a balanced
forest. The 1,000-operation read and update mixes adapt the 50/50 and
95/5 proportions of
[YCSB workloads A and B](https://github.com/brianfrankcooper/YCSB/tree/master/workloads),
at uniform positions or at a hotspot that draws 80 percent of the
operations from the first 20 percent of positions and the rest from
the whole input; every updated version is retained. Separate traces
alternate insertion and deletion, and branch a thousand updates from
one original root. Each timing is the median of seven runs after one
warm-up and includes the destruction of the timed result;
construction is timed separately. Requested bytes count the
allocations reachable from the supplied roots once, node and `Arc`
headers and root entries included, and exclude the input buffer, the
lookup table, allocator rounding and metadata, spare capacity,
temporaries and stacks; the flat baseline's column counts its byte
buffers alone.

:::table +header
*
  * 1-MiB input, page size
  * Initial requested bytes / input bytes
  * 500 updates + 500 reads, ms
  * Requested bytes with 501 versions
*
  * 256 B
  * 1.5624
  * 0.509
  * 2,238,336
*
  * 1 KiB
  * 1.1406
  * 0.761
  * 2,107,968
*
  * 4 KiB
  * 1.0351
  * 1.821
  * 3,461,376
*
  * Flat full-copy buffers
  * 1.0000, buffers only
  * 215.770
  * 525,336,576, buffers only
:::

At 16 MiB the same mix took 0.705, 0.850 and 2.000 milliseconds at
the three page sizes, and construction 20.2, 16.0 and 13.4
milliseconds. A thousand point reads took 23, 10 and 6 microseconds
at 1 MiB, a thousand matching-close queries 140, 60 and 35, and a
thousand 4-KiB range summaries 0.35, 0.79 and 2.87 milliseconds, the
last growing with the page since a partial page is rescanned. A
thousand splices retained 3.7, 3.7 and 5.1 megabytes of versions and
took 2.2, 2.5 and 4.3 milliseconds; a thousand branches from the
original root took 0.86, 1.46 and 3.85 milliseconds. The ratios
concern topology bytes in a freshly packed sequence, not the full
labelled bound; the full-copy baseline is deliberately naive, and is
not evidence against a production persistent vector or succinct
library. The 1-KiB page is the next comparison point, not an optimum.

For a summary scan over 16 MiB, the bit-at-a-time loop took 59.7
milliseconds, the byte-table scan 11.6, and two, four and eight
threads 6.5, 4.1 and 2.5; at 1 MiB the table scan took 0.70
milliseconds and eight threads 0.86, the spawning erasing the
benefit, so a worker pool and batching are the follow-up. The scan
inputs labelled {lit}`star`, {lit}`nested` and {lit}`chain` are
forests of four leaves per byte, a depth-four chain per byte, and one
long chain; they exercise scan mechanics, not a parser. A parallel
reduction's worker state is not the workspace of the sequential
witness. The files {lit}`cpu-1m.csv` and {lit}`cpu-16m.csv` retain
every observation, including the hotspot and history traces.
Fragmentation, reclamation tail latency, cross-thread reference-count
contention, bit-aligned edits and label-boundary compression are
unmeasured.

## The static-library measurements

The program {lit}`libraries.rs`, a Cargo package pinning
[vers-vecs](https://github.com/Cydhra/vers) 1.10.2 and
[sux](https://github.com/vigna/sux-rs) 0.14.0 with its own lockfile
outside the production dependencies, builds a star, a chain and a
root of chains of at most 31 nodes, each of 4,194,304 nodes and 1 MiB
of parenthesis bits, checks every opening's matching close in both
libraries against a stack oracle, and then times 100,000
deterministic random matching-close queries, the median of seven
runs after a warm-up, constructors and oracle excluded.

:::table +header
*
  * Shape
  * vers-vecs BP, 512-bit blocks, ms
  * sux Jacobson, ms
*
  * Star
  * 0.477
  * 0.513
*
  * Chain
  * 25.969
  * 9.346
*
  * Root of short chains
  * 3.888
  * 5.443
:::

The `vers-vecs` heap-size method reported 1,884,168 bytes for each
shape, 1.797 times the parenthesis bytes with its chosen indexes,
which is not a minimum-space configuration; `sux` heap space was not
measured. The ordering depends on the shape, a reason to keep both
baselines. These static queries are not comparable to the page
sequence's queries or updates; construction cost, the other
navigation operations and tuning remain open. The observations are in
{lit}`libraries.csv`.

## The interaction-net measurements

The programs under `prototypes/hvm/` build a full binary tree of
`2^20` leaves with distinct labels and sum, hash and compare it, as an
encoded algebraic data type and as native pairs, on HVM2 through
Bend 1 and on HVM4 built from its source at commit `6defdfc`, one
process at a time on the same machine; a chunked label of `2^K`
24-bit chunks in a balanced pair tree is folded and concatenated on
HVM2. The unit is the interaction, which is the runtimes' cost model
and which the HVM2 interpreters and compiled code agree on exactly.

:::table +header
*
  * Program and operation, `2^20` leaves
  * HVM2 interactions
  * HVM2 ms, 16 threads
  * HVM4 interactions
  * HVM4 ms, 1 thread
*
  * encoded constructors, sum
  * 69.2 M
  * 1060
  * 19.9 M
  * 835
*
  * encoded constructors, hash
  * 70.3 M
  * 1150
  * 21.0 M
  * 861
*
  * encoded constructors, equality of two trees
  * 149.9 M
  * 2890
  * 39.8 M
  * 1420
*
  * encoded constructors, equality of a duplicated tree
  * 124.8 M
  * 1770
  * 30.4 M
  * 1033
*
  * native pairs, sum
  * 56.6 M
  * 890
  * 24.1 M
  * 979
*
  * native pairs, equality of two trees
  * 98.6 M
  * 1880
  * 41.9 M
  * 1474
:::

On HVM2 a constructor encoded as a lambda costs 22 percent more
interactions than a native pair for a fold and 52 percent more for
an equality, 66 against 54 interactions per leaf for generation and
fold together; on HVM4, whose constructors are native, the order
reverses, 19 against 23, the pair version paying a numeric switch on
the depth at every node. HVM4 performs 3.5 times fewer interactions
than HVM2 for the same work on the encoded form, and one HVM4 thread
finishes ahead of sixteen HVM2 threads; HVM2's compiled code gains
nothing beyond four threads at this size and is no faster per
interaction than its interpreter. Duplicating a tree for a comparison
costs the same order as generating it. A chunked label folds at 54
interactions per chunk at every size, and concatenating two labels
of equal length is one pair node. HVM4's native structural equality
performs 47 percent more interactions than the hand-written fold and
leaves priority wrappers in its result, so it is not a shortcut.

A second program, {lit}`summary.bend` under
`Geb/Prototypes/SuccinctTree/` with its HVM4 counterpart
{lit}`summary.hvm`, generates seed-dependent 24-bit words at the
leaves of a balanced recursion, scans each word and combines the
summaries, so that no input is transferred and nothing is updated;
the driver {lit}`runtimes.py` checks every result against a Python
oracle and records whole-process wall times, the median of three runs
after a warm-up. Bend 0.2.38 and HVM 2.0.22 generated C and CUDA,
the CUDA compiled with `-arch=sm_89` under a checksum-verified CUDA
13.3.1 redistribution, since the host's CUDA 12.8 headers did not
compile against its compiler and C library; the GPU works under WSL2
outside the restricted process sandbox. This establishes the
configuration's feasibility, not a supported matrix. At depth 16 both
backends returned `(105134, -66)`, the C program in 0.610 seconds and
the CUDA program in 0.572 seconds of wall time, a first GPU run
reporting 0.22 seconds internally while taking 0.80 seconds in all:
the runtime's own timing excludes the launch, transfer and teardown
that a short editor request pays, and the measured end-to-end
advantage is small. HVM4 at depth 12 returned `(2332, -529)` in
0.367 seconds, a diagnostic run reporting 10,331,617 allocated heap
slots and about 592 MiB peak resident memory including its other
structures; the input size and strategy differ from the HVM2 run, so
this is no ranking between runtimes. The upstream test script's
`fib_small` and `spin` cases exceeded its two-second timeout at that
commit and the others passed, which is not recorded as a clean test
pass. The observations are in {lit}`runtimes.csv`.

## Reproduction

The rose-tree programs run as `lake exe rosebench`, the Rust crate's
own tests and benchmark under `prototypes/rust/rosetree/`, and the
Bend and HVM4 programs under `prototypes/hvm/`. The page-sequence,
static-library and summary-reduction programs run from the repository
root as follows, with executables and Cargo products kept outside the
source tree; the Cargo packages are experiment dependencies only.

```
lake build Geb.Prototypes.SuccinctTree GebTests.Prototypes.SuccinctTree
rustc -O --edition=2021 --test Geb/Prototypes/SuccinctTree/bench.rs \
  -o /tmp/geb-tree-tests
/tmp/geb-tree-tests --test-threads=1
rustc -O --edition=2021 Geb/Prototypes/SuccinctTree/bench.rs -o /tmp/geb-tree-bench
/tmp/geb-tree-bench 1048576 2
/tmp/geb-tree-bench 16777216 2
CARGO_TARGET_DIR=/tmp/geb-libraries cargo run --release --locked \
  --manifest-path Geb/Prototypes/SuccinctTree/Cargo.toml -- 4194304
bend gen-c Geb/Prototypes/SuccinctTree/summary.bend > /tmp/geb-summary.c
gcc -O3 /tmp/geb-summary.c -lm -pthread -o /tmp/geb-summary-cpu
bend gen-cu Geb/Prototypes/SuccinctTree/summary.bend > /tmp/geb-summary.cu
nvcc -O3 -arch=sm_89 /tmp/geb-summary.cu -o /tmp/geb-summary-gpu
python3 Geb/Prototypes/SuccinctTree/runtimes.py \
  /tmp/geb-summary-cpu /tmp/geb-summary-gpu /path/to/pinned/hvm4/src/hvm
scripts/manual.sh build
```

The page-sequence program's second argument is the maximum number of
scan workers, 1, 2, 4 or 8, where 1 skips the threaded scans; the
recorded files hold all three threaded configurations. On a
constrained host, restrict builds to two processors with `taskset`
and run builds and benchmarks one at a time, and keep such reruns
apart from the recorded configuration. HVM4 is built at the recorded
revision with its documented `clang -O2 -o src/hvm src/hvm.c`; a
separately unpacked CUDA redistribution needs its `lib` directory
passed with `-L` to its `nvcc`. Lean timing output appears on
rebuilding the test module.

## Observations

* The list recognizer of the repository is quadratic: its fuel-bounded
  parser is a recursor tower whose fuel is the word's length, so it
  takes 1.8 milliseconds per node on ten thousand nodes and the
  word-level streaming fold, at 0.6 microseconds per node, is faster
  by a factor above three thousand. This is the cost the type checker
  pays today, and the streaming form removes it without leaving the
  recursor discipline. The interpreted algebra is slower again by
  five orders of magnitude, which is the cost of certifying by
  interpretation rather than by an extensional equality.
* Lean's compiled word-level forms are slower than Rust's by a factor
  of ten to forty per node, the fold most, since the W-type's children
  are a function tabulated into a list at every node; the same
  operations in the same order, so the factor is the runtime's, not
  the design's.
* A long label as a natural number serializes at twelve megabytes per
  second in Lean, since each sixty-four-bit chunk is a shift of the
  whole number, quadratic in its length; the same label as limbs
  serializes at 4.4 gigabytes per second in Rust. In Lean a long label
  belongs in a byte array, as the recommendations say. The list form
  of a long label is worse still, since mathlib's bit enumeration
  divides the number by two once per bit.
* On the syntax-like regime the delta-coded length costs as much as
  the label: 8 bits per node for an 8-bit label. A syntax tree over a
  fixed signature does not need a per-node length code, since its
  labels are constructor identifiers of a known width; the
  serialization of a typed tree is best specialized to its signature,
  the length code kept for the untyped carrier alone.
* The succinct tree costs an order of magnitude more per navigation
  than a pointer tree and a third of a bit per node more than the
  parenthesis word itself, and the two static libraries order
  differently by shape; it is a storage and query structure, not an
  evaluator's.
* The tape, one word per node with a skip pointer, is built at the
  cost of a hash and walked at the cost of a fold; it is the cheapest
  form for a checker that needs random access, and its pointer chase
  is the reason it is not the recognized form.
* The persistent page sequence applies five hundred updates to a 1-MiB
  value and retains every version in the time the full-copy baseline
  takes for one to four updates, the retained history costing two to
  three times the input's bytes; the page size trades update cost
  against initial space and retained history, and the cached summaries
  make matching-close queries skip whole pages.
* Threads pay for themselves on a 16-MiB scan and not on a 1-MiB one,
  and a GPU's end-to-end time on a balanced reduction is within seven
  percent of a CPU's; bulk parallelism belongs to large cold values,
  and small interactive operations stay on the CPU.
* On the interaction-net hosts the representation of a node is the
  cost: native constructors where the runtime has them, pairs where it
  has not, never encoded constructors; balanced chunk trees give
  labels the same cost per chunk as trees per node; and a runtime that
  releases its heap only at teardown cannot hold a persistent store.
* Equality and hashing are memory-bound: on long labels the structural
  equality runs at memory bandwidth and the hash at the hasher's
  throughput, so a cached hash per node is what makes an inequality
  constant, and an exact comparison or interning is what makes an
  equality certain.

{includeLiterate "." Geb.Prototypes.RoseTree.Basic "Geb.Prototypes.RoseTree.Basic" (level := 1)}

{includeLiterate "." Geb.Prototypes.RoseTree.Bits "Geb.Prototypes.RoseTree.Bits" (level := 1)}

{includeLiterate "." Geb.Prototypes.RoseTree.Spine "Geb.Prototypes.RoseTree.Spine" (level := 1)}

{includeLiterate "." Geb.Prototypes.RoseTree.Packed "Geb.Prototypes.RoseTree.Packed" (level := 1)}

{includeLiterate "." Geb.Prototypes.SuccinctTree "Geb.Prototypes.SuccinctTree" (level := 1)}

{includeLiterate "." GebTests.Prototypes.SuccinctTree "Executed storage experiments" (level := 1)}

# Recommendations

The recommendations are ordered by what serves self-hosting first:
the syntax trees of the parser, type checker, interpreter, compiler
and editor tooling, then the stored and transmitted form, then the
hashes that identify code, then long payloads, then the
interaction-net hosts. Each states its tradeoffs and what it
excludes. All of them share one semantics, {name}`Geb.RoseTree` over
bitstring labels, and one serialization, and differ in the internal
form each host builds.

## First: the in-memory syntax tree

A node is one allocation holding a label, a cached word-sized hash,
the subtree's serialized size, and its children in an array,
immutable once built and shared by reference count; the label is an
unboxed word when it fits one, which every constructor identifier
does. This is the green tree of Roslyn and rust-analyzer with Lean's
cached `Expr` header, and it is what every measured evaluator builds
fastest: one allocation per node, a load per child access, a fold at
a nanosecond per node, and structural equality that fails on a hash
mismatch before it descends. The serialized size in the header is
what the editor tooling needs: a cursor over such a tree, a red node,
carries the absolute position of a node in the serialized text, so
the Language Server Protocol's positions are computed by descent, as
they are in the editors surveyed, without storing them. A node whose
arity exceeds a threshold set by editor traces holds its children as
a balanced persistent sequence, so that replacing one child of a
long block copies logarithmically many entries rather than the array;
the cost of an edit deep in a semantic chain remains the chain's
depth. Nodes of at most three children are interned in a
direct-mapped table, as Roslyn and rust-analyzer do, which makes
equality of interned subtrees a pointer comparison and the
hereditary naturality check linear; interning is a phase's choice,
since a global table serializes parallel construction, and a
transient owner, as in Clojure's collections, batches a rebuild
before freezing it. Cache keys of the incremental checker name the
signature, index, environment and restriction context beside the
value, since a digest alone omits them; obsolete requests are
cancelled, and every retained root is accounted. In Lean the tree is
the W-type {name}`Geb.RoseTree` itself, the array of children being
the tabulation of its direction function, and the runtime updates a
uniquely referenced node in place.

The acceptance workload is an editor session: parse a source file,
change one token, produce diagnostics, and retain the older
language-server snapshots while doing so, measuring cold and warm
latency, allocations, the breadth of invalidation and reclamation
pauses. The measurements support replacing interpreted primitives by
extensionally equal native ones; they do not yet quantify an
incremental checker's speedup.

Tradeoffs: the in-memory form is not succinct, a node costing tens
of bytes against two bits of shape and a few bits of label in the
serialized form, which is the price of construction at allocation
speed; it is the form for values being computed on, and values at
rest take the second form.

Excluded: the succinct dynamic trees, which are ephemeral and an
order of magnitude slower per navigation; a self-referential
inductive type, which the repository's discipline forbids and the
W-type replaces at no cost; a cryptographic digest in every header,
which is larger than the node it identifies.

## Second: the serialized and stored form

The recognized carrier is the interleaved word the repository
already has: each node its arity in unary, a zero, the delta-coded
length of its label, the label, then its children, which
{name}`Geb.RoseTree.wire` produces from a rose tree and
{name}`Geb.BitTree.Elias.validBool` recognizes in linear time and
logarithmic space with a proof already in place, whose size is
optimal to within the length codes by the repository's counting
argument, and which {name}`Geb.Packed.encode` writes and
{name}`Geb.Packed.run` reads at word level, byte for byte as the Rust
crate does. Its bits are the same at every word width, so the word
width parameterizes the implementation and not the format. Its
stored and transmitted profile carries the version, counts, bit
order, bounded length headers and zeroed final bits of § The
serialized face, and its reader rejects every malformed input named
there.

Two profiles of it serve the two shapes the storage model has. A
typed tree over a known signature drops the length code and the
unary arity: its labels are constructor identifiers of the width the
signature fixes and its arities follow from them, so a node costs
that width alone, the recognizer is a finite tree automaton, and a
logarithmic-space transcoder recovers the carrier form, which is
what the algebraic witness is stated over. The stored form of a
value at rest is sectioned: the shape word, the length codes and the
payloads as three sections behind a header, with every annotation,
comments and digests among them, as a further section keyed by
preorder position, so that the tree of small labels and the
sequences of large payloads are each contiguous. The interleaved
form is the streaming form, emitted node by node without knowing
the total; the sectioned form is the storage form; logarithmic-space
transcoders relate them, and a sectioned tree is checked in
parallel by prefix sums.

A stored value under edit, a module's source or a large payload,
holds each section as the persistent page sequence of § The
persistent page sequence: immutable pages of about 1 KiB as the first
comparison point, cached summaries in the branches, one root record
per version, and exact bit spans, label lengths and coordinated
splices across the three sections, with a coalescing and occupancy
policy stated and charged before any succinctness factor is claimed
for a history. The prototype's AVL over pages is the tested
reference; a wider fanout is adopted only after editor traces
compare it. Accelerators are side structures and never part of what
is recognized: the range min-max index at a third of a bit per node
for logarithmic navigation over a stored tree, the preorder tape at a
word per node for constant-time skipping in a checker, and, on sealed
blocks and frozen snapshots, module caches, compiler artifacts and
query-heavy stores, the static succinct indexes of `vers-vecs`,
`sux` or a tree-covering layout, whose space and query costs differ
by shape and which are never rebuilt per keystroke.

Tradeoffs: the delta-coded length costs as much as an 8-bit label,
which is why the typed profile exists; the sectioned form is not
streamable without its header, which is why the interleaved form is
kept; the page sequence costs its metadata and its slack, a fresh
1-KiB packing measuring 1.14 times its bytes, and it is compact
rather than proved succinct.

Excluded as the recognized form: length-prefixed subtrees, whose
validation is a pointer chase complete for logarithmic space and
whose linear-time checkers cap the depth at sixty-four.

## Third: the digests that identify code

Two hashes, for two purposes, both computed over canonical
serialization bytes so that every host, whatever its word width or
page size, computes the same value. A subtree's digest, the identity
of a definition in the content-addressed store, is the digest of its
label's serialization together with its children's digests, computed
bottom-up and kept beside the tree in the storage form, one per node
where node identity is needed and one per definition otherwise, so
that a rebuilt tree costs only the path rebuilt; the in-memory header
carries the word-sized hash and not the digest. The integrity digest
of a stream or blob is the tree-mode digest of its serialization,
which is computed in one pass with a logarithmic stack of chaining
values and in logarithmic span in parallel, and which is the one
provably in `FLOGSPACE`. BLAKE3 serves both, its tree mode giving the
second and its compression the first; the repository has no
implementation of it in Lean, and a reference implementation or a
binding is a prerequisite. For in-memory equality that must compose
under concatenation, a polynomial hash modulo a word-sized prime is
the composable choice and is in `FLOGSPACE`. No digest certifies an
equality the type checker's verdict depends on: a match is followed
by pointer equality, exact comparison or collision-checked interning.

Tradeoffs: the subtree digest follows the tree's shape, so its
streaming computation needs space proportional to the depth, and it
is in `FLOGSPACE` only on trees of logarithmic depth; the integrity
digest is shape-independent and does not identify subtrees; a digest
per node is larger than the node, which is why it is stored beside
the tree and computed selectively. Both are needed.

## Fourth: long labels and blobs

In a systems language a label is a length and two inline words,
the heap form marked by a length above two words, as `dashu` and
`smallbitvec` do; bits are packed least significant first in
little-endian words with the dead bits zero, so equality and hashing
run at memory bandwidth, and concatenation and extraction are shifts.
In Lean a label of at most sixty-two bits is a natural number, which
the runtime keeps unboxed, and a longer one is a byte array with its
bit length, since a large natural number exposes no linear-time
access to its limbs and its built-in hash truncates. On an
interaction-net host a long label is a balanced tree of word chunks,
one chunk per unboxed scalar, folded in logarithmic span. The three
are isomorphic to the bitstring, and none is the canonical form for
hashing, which the serialization bytes are. A blob under edit is the
persistent page sequence of the second recommendation, its history
accounted as live pages plus incremental bytes; a cold blob or a
distribution artifact is chunked by content for deduplication, and a
repetitive corpus takes a grammar-compressed backend of its own, each
with its own size, collision and version-lifetime analysis.

Tradeoffs: the chunk tree costs a node per word and the byte array a
header per label; the inline form fits the syntax-tree labels and
costs nothing; content-defined chunking bounds the chunks an edit
touches in expectation, not in the worst case.

## Fifth: the interaction-net hosts

On HVM4, the live interaction-calculus runtime, a node is a native
constructor of at most sixteen fields, with wider nodes nested as
balanced blocks, labels as balanced trees of 32-bit chunks, equality
by the runtime's structural-equality interaction, and the same
serialization. On HVM2 through Bend 1, both frozen, a node is a
balanced tree of native pairs with the arity carried in the label,
and a label a balanced tree of 24-bit chunks; the encoded algebraic
data types cost four nodes per binary constructor and are avoided.
Every host of this kind needs structure balanced to a known depth
for a GPU to schedule it, which the balanced chunk trees and the
sectioned form both give. The summary algebra stays portable across
hosts, and bulk parallel work uses coarse independent blocks,
preserves the reduction order, and is measured with its transfer,
launch, allocation and reclamation, since a GPU's advantage on a
balanced reduction was within seven percent end to end.

Tradeoffs: nothing compiles to HVM4 yet, its GPU port is not current
code, its heap is released only at teardown, and Bend 2 runs on a
runtime that is not an interaction net; duplication on these hosts
is not a constant-cost share, and a packed block would need a runtime
primitive of its own. The recommendation is a layout for the
calculus, not for a shipped toolchain.

## Sixth: the type checker

Two implementations of each recognition stage, extensionally equal:
the practical one, a linear-time streaming reader with a stack of
pending arities and index prescriptions, whose space is the depth,
and the witnessed one, an expression of a sound logarithmic-space
algebra with quadratic time, which is the proof. The first stage has
both today. The child-index stage cannot have a one-pass
logarithmic-space checker, so its practical form keeps the stack and
its witness re-scans. The naturality stage compares subtrees under a
fixed relabelling, which adds no complexity class, and its practical
form compares interned subtrees by pointer and the rest exactly,
after a hash has rejected the unequal ones. A parallel checker uses
the sectioned form, prefix sums giving each node its parent and
position, and each stage is then a map. A stream checker recognizes
completed framed values by prefix invariants. The certification of a
new serialization discharges the four obligations of § What the
complexity results decide, over the flat finite format first, the
general Oitavem machine soundness proof remaining a separate
dependency; a shared graph format is certified against its own size
measure.

## Decision gates

Before the foundational format is fixed, the following are in hand:
a complete codec equivalence for the serialization; a recognition
witness and an optimized-equivalence theorem for the supported
signatures; an occupancy and history-space bound for the page
sequence; and traces of real parsing, type checking and editing,
including malformed and adversarially deep and wide inputs, many
tiny labels, large blobs, branching undo histories, and cancellation
while old readers remain active, with bytes compared against the
full label and topology bound and both throughput and tail latency
measured.

## Order of preference

The first four together are the design: a green tree of word labels
with a cached hash in memory, its wide nodes over balanced
sequences; the interleaved carrier with a typed profile and a
sectioned storage form on disk and on the wire, its sections
persistent page sequences under edit and static indexes once sealed;
BLAKE3 digests over serialization bytes for identity and integrity,
stored beside the tree; and labels inline, in byte arrays or in
chunk trees by host. The fifth adapts the same design to interaction
nets and waits on a runtime that ships; the sixth is the discipline
the repository has followed and continues. Where a choice within them
remains open, the measurements decide it: the typed profile over the
length code for syntax trees, the pointer tree over the succinct tree
for evaluation, the streaming fold over the recursor per node for
readers, the byte array over the natural number for long labels in
Lean, the 1-KiB page as the next comparison point for the sequence,
and the CPU over the GPU for interactive work.
