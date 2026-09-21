/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import VersoManual
public import GebManual.Bibliography
import Geb.Prototypes.Computability.BitTree
import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.Machine
import Geb.Prototypes.Computability.Oitavem.Machine.SpaceTime
import Geb.Mathlib.Data.PFunctor.Presheaf.Decidable
import Geb.Prototypes.Computability.Oitavem.Word

/-! # Value representation chapter

The design record for the representation of the language's values:
the requirements, the state of the repository's encodings and
recognizers, the literature, the prototypes and their measurements,
and the recommendations.
-/

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Representing rose trees of bitstrings" =>

The language's values are rose trees of bitstrings: finite ordered
trees of unbounded branching, each node of which carries a bitstring
of arbitrary length. Every finitary W-type is presented by such
trees, the label selecting a shape together with its non-recursive
data and the children supplying the recursive data. This chapter
records the design of a representation of those trees: the
requirements, the encodings and recognizers the repository already
has, the literature on succinct and word-level tree and string
representations, the prototypes written against that literature with
their measurements, and, last, the recommendations with their
tradeoffs. It is a record of an investigation in progress; each
section states what has been established and what remains
conjectural.

# Requirements

The representation is judged by the following properties, in the
order of their weight.

* Semantics. Whatever the internal form, the type represented is the
  rose tree of bitstrings, up to a computable isomorphism proved in
  Lean. Variants adapted to different host languages may differ
  internally; they agree on this semantics.
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
  in both.
* Operation cost. Construction, destructuring, folding, equality and
  hashing run in time linear in the data touched with word-sized
  constants, and in parallel where a parallel evaluator hosts the
  representation.
* Portability. The same semantics and serialized form are
  implemented in Lean, in systems languages such as Rust, and on the
  Higher-Order Virtual Machine 2, each with the internal form that
  suits it.

Construction dominates the workload: values are built and rebuilt by
an evaluator far more often than they are recognized from a
serialized form. Among workloads, self-hosting comes first: parsing,
type checking, interpretation and compilation of the language by
itself, and the developer tooling around them, syntax trees for
editors and the Language Server Protocol among them. The
recommendations are ordered by what serves those, since that work
pays off first; the other workloads, large data and streams among
them, are investigated to the same depth and ordered after. The
design therefore has two faces, a serialized form whose recognizer
is the object of the complexity requirement and an in-memory form
whose construction cost is the object of the operation-cost
requirement, related by a conversion in each direction.

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
preorder word only by a scan.

Oitavem's algebra for logspace {citep Oitavem2010}[] is the second
witness available. Its syntax and interpreter are formalized, with
the truncation and output-length results of the paper's soundness
argument; the compiler to a machine and its soundness theorem are in
progress, and {name}`Geb.Oitavem.Machine.computes_polytime_logspace`
already converts any halting logarithmic-space transducer into a
polynomial time bound.

The presheaf stage has a Lean-native decision procedure and no
algebraic witness. {name}`PresheafPFunctor.isHereditarilyNaturalBoolCore`
decides hereditary naturality by a fold over the slice W-tree whose
step at a node compares subtrees, so it runs in time quadratic in the
number of nodes and in space linear in the tree's height. The
condition that it decides compares, at each node and for each
morphism of the index category and each direction, the value at the
restricted direction with the restriction of the value at the
original direction; each such comparison is an equality of subtrees
up to a fixed relabelling.

The evaluators of the algebras themselves interpret bit by bit. The
recognizer of the algebra's own expressions, evaluated with sharing,
takes tens of seconds at a ten-bit word. The Lean-native decision
procedures run at the speed of Lean's compiled code over `List Bool`,
which is faster by orders of magnitude and still allocates one cell
per bit.

# Literature

The surveys below were made against primary sources; every
identifier was checked against the arXiv, the IACR ePrint archive
or Crossref before entering the bibliography. Statements marked as
derived are the author's deductions from the cited results rather
than results stated in them.

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
supports node insertion and deletion in `O(log n / log log n)` time
{citep NavarroSadakane2014}[]. The DFUDS degree sequence compresses
to the degree entropy of the tree {citep JanssonSadakaneSung2012}[].
Tree covering gives the same bounds by a different route
{citep FarzanMunro2014}[]; a finger-based dynamic variant supports
constant-time navigation at a finger and constant amortized leaf
insertion {citep FarzanMunro2011}[]. Measured, the range min-max
tree with a block size of 512 takes 2.37 to 2.38 bits per node and
answers most operations in under half a microsecond, against 18 to
31 nanoseconds for the child operation of a pointer tree
{citep ArroyueloCanovasNavarroSadakane2010}[]; a simplified
inter-block scheme reaches 2.34 bits per node at up to four times
the speed of the reference implementation
{citep CordovaNavarro2016}[]; a 2024 tree-covering variant over
balanced parentheses measures 1.822 bits per node for range-minimum
queries {citep HamadaChakrabortyJoKoriyamaSadakaneSatti2024}[]. The
range min-max tree is constructed from the parenthesis word in
`O(n/p + log p)` time on `p` processors, by a parallel prefix over
the excess sequence {citep FuentesSepulvedaFerresHeZeh2017}[]. The
shared pioneer structure of {citep GogFischer2010}[] is what the
`sdsl` library ships.

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
logarithmic time, rank in 6 to 26 nanoseconds and select in 30 to
159, and is maintained; `sucds` and `sux` ship bit vectors and
Elias-Fano sequences without trees. No Rust crate ships DFUDS, a
dynamic parenthesis tree, or a labelled succinct tree. The C++
reference, `sdsl-lite`, is maintained in its version 3 fork. No
surveyed succinct dynamic tree is persistent: every one is
ephemeral, and pays `O(log n / log log n)` to `O(log n)` per
navigation and per update.

## Word-level bitstrings

Every arbitrary-precision natural number library stores its limbs
least significant first and normalized, without high zero limbs:
GMP's `mpz`, `malachite`, `ibig`, `dashu` and `num-bigint` in Rust,
and Lean 4's own `Nat`, which is a tagged scalar below `2^63` and a
GMP object above it. A bitstring is not a number: its leading zeros
are significant, so each of these needs a bit length beside it.
The libraries that track a bit length, `bitvec`, `bit-vec`,
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
most 54 of them {citep OConnorAumassonNevesWilcoxOHearn2020}[]; in
general the Merkle root of a leaf sequence in binary-numeral shape is
computed in one pass with `O(log n)` space {citep Champine2021}[].
A Merkle root that follows the shape of a rose tree, each node
hashing its label with its children's digests, has a pending-digest
stack of depth equal to the tree's depth, `Θ(depth · digest)` bits,
and no logarithmic-space algorithm for it over unbounded depth is
known; the shape-independent root over the serialization is the one
that is provably in `FLOGSPACE`.

## Complexity of recognition

Membership in a parenthesis language is in logarithmic space, with
a counter for the excess, and logarithmic-space translators exist
between representations {citep Lynch1977}[]; the one-sided Dyck
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
ALOGTIME and complete for it {citep Buss1987}[].

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
in `TC^0 ⊆ L`.

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
an arbitrary tree in `O(log n)` time {citep MillerReif1985}[]. A
shape-following Merkle hash has span proportional to the depth,
since a cryptographic compression function does not compose; the
hash of the serialization has span `O(log n)`.

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
combinator rules with a lambda-application orientation: a term is
a 64-bit word of an 8-bit tag, a 24-bit extension and a 32-bit
value; numbers are unboxed 32-bit unsigned words; constructors are
native and flat, of arity up to 16, their fields consecutive heap
words; structural equality and matching are primitive
interactions; duplication is lazy and labelled, so nested cloning
is sound and an unshared subtree is never copied; and reduction is
lazy. Nothing compiles to it yet, and its GPU port is history
rather than current code. Every one of the three imposes that
structure be balanced to a known depth for a GPU to schedule it.

## Compilers and syntax tooling

The persistent collections of language runtimes are 32-way tries:
Clojure's vector and hash-array-mapped trie {citep Bagwell2001}[]
copy one node per level on update and batch construction through a
transient owned by one thread; CHAMP keeps two bitmaps per node,
payload from the front and sub-nodes from the back of one array,
with a canonical form that lets structural equality fail on a
bitmap mismatch, and measures 16 to 23 percent less memory than
Clojure's and 65 to 68 percent less than Scala's previous maps
{citep SteindorferVinju2015}[]; relaxed-radix-balanced vectors add
size tables to obtain logarithmic concatenation
{citep StuckiRompfUrecheBagwell2015}[]. Syntax trees separate an
immutable, parent-free, width-carrying green tree from a red façade
of cursors with offsets: Roslyn caches only green nodes of at most
three children, in a direct-mapped table keyed by the children's
identities; `rowan` in rust-analyzer lays a green node out as one
allocation of reference count, kind, text length, child count and
children with relative offsets, interns nodes of at most three
children, and measured 17 percent memory saved by it; tree-sitter
packs a leaf into the 8 bytes of a pointer with the inline flag in
the pointer's low bit, and allocates a node's children immediately
before its header in one block; `rustc` interns every type, with
pointer equality and pointer hashing, and caches a stable hash and
flags beside it; Lean's own `Expr` caches a 32-bit hash, an
approximate depth, flags and the loose bound-variable range in one
64-bit field computed by the constructor, and its `replace`
consults its cache only on subterms whose reference count shows
them shared. Hash-consing as a discipline is
{citep FilliatreConchon2006}[]; Lean's runtime performs the update
in place when the reference count is one
{citep UllrichDeMoura2019}[].

The structural JSON parsers are the measured state of the art for
turning a serialized tree into an indexed one. `simdjson` finds the
structural characters of 64-byte blocks branchlessly with vector
instructions and a carry-less multiplication for the prefix parity
of quotes, then writes a tape of 64-bit words in which every
container's opening word holds the index of its closing word and a
child count, so that a subtree is skipped in constant time; it
exceeds two gigabytes per second where the previous parsers reached
half of one {citep LangdaleLemire2019}[]. `yyjson` stores each value
in 16 bytes with the size in the high 56 bits of a tag word and each
container's byte extent, again for constant-time skipping. The
formats of the systems world confirm the same division: length
prefixes, as in Cap'n Proto, FlatBuffers, DER, Protobuf and the
WebAssembly binary format, buy constant-time skipping and parallel
decoding and cost, per node, tens to hundreds of bits and a
validation that follows a pointer chain, with depth caps of 64 in
the verifiers of FlatBuffers and Cap'n Proto; counts and brackets,
as in CBOR and MessagePack, cost a few bits per node and are checked
by counters. Content-addressed stores, Git, IPLD and Unison, pay 20
to 64 bytes per child link for Merkle identity.

# Design space

The requirements and the literature fix the shape of the design:
two faces joined by conversions, each face chosen from a short list.

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
  section is what a variable-length-cells array is. It is not
  streamable without knowing the section lengths.
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
computed on one host equals the hash computed on another.

## The in-memory face

The rose tree as a nested inductive type with a children array,
the label inline when short, is the form every host builds fastest:
a child access is a load, against half a microsecond in a succinct
tree, and construction is one allocation per node. Its refinements,
each measured in a shipped compiler:

* A cached hash in the node header, computed at construction, as
  Lean's `Expr` does; equality then fails on a hash mismatch and a
  Merkle hash of a rebuilt tree costs only the path rebuilt.
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

No succinct dynamic tree serves this face: none is persistent, and
all are slower per operation by more than an order of magnitude.

## Hashing

Two hashes, for two purposes. The hash over the serialization, a
polynomial hash for speed or BLAKE3's tree mode for collision
resistance, is in `FLOGSPACE` and has logarithmic span. The
shape-following Merkle hash, each node's digest over its label's
chunk hash and its children's digests, is the one that a cached
header hash and hash-consing maintain incrementally, and it is in
`FLOGSPACE` only on trees of logarithmic depth. Both are defined on
the canonical chunking of labels so that every host computes the
same value.

## What the complexity results decide

The child-index stage is a typed-matching problem, so no one-pass
checker in small space exists for it, and the practical checker is
the linear-time one with a stack of pending arities and index
prescriptions, `O(depth)` words, logarithmic on balanced trees. The
logarithmic-space guarantee on every input is the witnessed
quadratic-time recognizer, a separate function extensionally equal
to the practical one. The naturality stage compares subtrees under
a fixed relabelling and is in `TC^0` on the string encoding, so it
adds no complexity class; its practical cost is quadratic without
sharing and linear with hash-consing. A parallel checker follows
the JSON parsers: prefix sums over the sectioned form give every
node its parent and position, and each stage is then a map.

# Prototypes and measurements

This section is filled in as the prototypes are written.

# Recommendations

This section is written last.
