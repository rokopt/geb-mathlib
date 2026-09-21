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
import Geb.Prototypes.RoseTree

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
  implemented in Lean, in systems languages such as Rust, and on
  interaction-net runtimes such as HVM4, each with the internal form
  that suits it.

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

The prototypes are literate modules under `Geb/Prototypes/RoseTree/`,
included below, a test module, a benchmark executable, and a Rust
crate. They establish the semantic layer with proofs, the serialized
form with proofs where the repository already had them and tests
where it did not, and the costs by measurement. Every measurement in
this section is from a run on one machine, an AMD Ryzen AI 9 HX 370
laptop processor with fifteen logical cores available, of a single
thread, and reports the best of a few repetitions; it is a
comparison between representations on the same machine, not a
characterization of any of them.

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
the syntax-like regime.

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

## Observations

* The list recognizer of the repository is quadratic: its fuel-bounded
  parser is a recursor tower whose fuel is the word's length, so it
  takes 1.8 milliseconds per node on ten thousand nodes and the
  word-level streaming fold, at 0.6 microseconds per node, is faster
  by a factor above three thousand. This is the cost the type checker
  pays today, and the streaming form removes it without leaving the
  recursor discipline.
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
  parenthesis word itself; it is a storage and query structure, not
  an evaluator's.
* The tape, one word per node with a skip pointer, is built at the
  cost of a hash and walked at the cost of a fold; it is the cheapest
  form for a checker that needs random access, and its pointer chase
  is the reason it is not the recognized form.
* On the interaction-net hosts the representation of a node is the
  cost: native constructors where the runtime has them, pairs where it
  has not, never encoded constructors; and balanced chunk trees give
  labels the same cost per chunk as trees per node.
* Equality and hashing are memory-bound: on long labels the structural
  equality runs at memory bandwidth and the hash at the hasher's
  throughput, so a cached digest per node is what makes equality
  constant.

{includeLiterate "." Geb.Prototypes.RoseTree.Basic "Geb.Prototypes.RoseTree.Basic" (level := 1)}

{includeLiterate "." Geb.Prototypes.RoseTree.Bits "Geb.Prototypes.RoseTree.Bits" (level := 1)}

{includeLiterate "." Geb.Prototypes.RoseTree.Spine "Geb.Prototypes.RoseTree.Spine" (level := 1)}

{includeLiterate "." Geb.Prototypes.RoseTree.Packed "Geb.Prototypes.RoseTree.Packed" (level := 1)}

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

A node is one allocation holding a label, a cached digest, the
subtree's serialized size, and its children in an array, immutable
once built and shared by reference count; the label is an unboxed
word when it fits one, which every constructor identifier does. This
is the green tree of Roslyn and rust-analyzer with Lean's cached
`Expr` header, and it is what every measured evaluator builds
fastest: one allocation per node, a load per child access, a fold at
a nanosecond per node, and structural equality that fails on a
digest mismatch before it descends. The serialized size in the
header is what the editor tooling needs: a cursor over such a tree,
a red node, carries the absolute position of a node in the
serialized text, so the Language Server Protocol's positions are
computed by descent, as they are in the editors surveyed, without
storing them. Nodes of at most three children are interned in a
direct-mapped table, as Roslyn and rust-analyzer do, which makes
equality of interned subtrees a pointer comparison and the
hereditary naturality check linear; interning is a phase's choice,
since a global table serializes parallel construction, and a
transient owner, as in Clojure's collections, batches a rebuild
before freezing it. In Lean the tree is the W-type
{name}`Geb.RoseTree` itself, the array of children being the
tabulation of its direction function, and the runtime updates a
uniquely referenced node in place.

Tradeoffs: the in-memory form is not succinct, a node costing tens
of bytes against two bits of shape and a few bits of label in the
serialized form, which is the price of construction at allocation
speed; it is the form for values being computed on, and values at
rest take the second form.

Excluded: the succinct dynamic trees, which are ephemeral and an
order of magnitude slower per navigation; a self-referential
inductive type, which the repository's discipline forbids and the
W-type replaces at no cost.

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
width parameterizes the implementation and not the format.

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

Accelerators are side structures and never part of what is
recognized: the range min-max index at a third of a bit per node for
logarithmic navigation over a stored tree, or the preorder tape at a
word per node for constant-time skipping in a checker.

Tradeoffs: the delta-coded length costs as much as an 8-bit label,
which is why the typed profile exists; the sectioned form is not
streamable without its header, which is why the interleaved form is
kept.

Excluded as the recognized form: length-prefixed subtrees, whose
validation is a pointer chase complete for logarithmic space and
whose linear-time checkers cap the depth at sixty-four.

## Third: the digests that identify code

Two hashes, for two purposes, both computed over canonical
serialization bytes so that every host, whatever its word width,
computes the same value. A subtree's digest, the identity of a
definition in the content-addressed store, is the digest of its
label's serialization together with its children's digests, computed
bottom-up at construction and cached in the node's header, so that a
rebuilt tree costs only the path rebuilt; it is stored beside the
tree, one per node, in the storage form. The integrity digest of a
stream or blob is the tree-mode digest of its serialization, which is
computed in one pass with a logarithmic stack of chaining values and
in logarithmic span in parallel, and which is the one provably in
`FLOGSPACE`. BLAKE3 serves both, its tree mode giving the second and
its compression the first; the repository has no implementation of
it in Lean, and a reference implementation or a binding is a
prerequisite. For in-memory equality that must compose under
concatenation, a polynomial hash modulo a word-sized prime is the
composable choice and is in `FLOGSPACE`.

Tradeoffs: the subtree digest follows the tree's shape, so its
streaming computation needs space proportional to the depth, and it
is in `FLOGSPACE` only on trees of logarithmic depth; the integrity
digest is shape-independent and does not identify subtrees. Both are
needed.

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
hashing, which the serialization bytes are.

Tradeoffs: the chunk tree costs a node per word and the byte array a
header per label; the inline form fits the syntax-tree labels and
costs nothing.

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
sectioned form both give.

Tradeoffs: nothing compiles to HVM4 yet, its GPU port is not current
code, and Bend 2 runs on a runtime that is not an interaction net;
the recommendation is a layout for the calculus, not for a shipped
toolchain.

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
form compares digests. A parallel checker uses the sectioned form,
prefix sums giving each node its parent and position, and each
stage is then a map.

## Order of preference

The first four together are the design: a green tree of word labels
with a cached digest in memory, the interleaved carrier with a typed
profile and a sectioned storage form on disk and on the wire,
BLAKE3 digests over serialization bytes for identity and integrity,
and labels inline, in byte arrays or in chunk trees by host. The
fifth adapts the same design to interaction nets and waits on a
runtime that ships; the sixth is the discipline the repository has
followed and continues. Where a choice within them remains open, the
measurements decide it: the typed profile over the length code for
syntax trees, the pointer tree over the succinct tree for evaluation,
the streaming fold over the recursor per node for readers, and the
byte array over the natural number for long labels in Lean.
