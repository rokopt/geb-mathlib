/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import VersoManual
public import GebManual.Bibliography
import Geb.Prototypes.SuccinctTree
import Geb.Prototypes.Typechecker.Oitavem
import Geb.Prototypes.Computability.Oitavem
import Geb.Prototypes.Computability.BitTree.Elias.RepresentationSize
import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.RecognizeExpr
import Geb.Prototypes.CanonicalSExpr
import GebTests.Prototypes.SuccinctTree

/-! # Storage investigation chapter -/

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

#doc (Manual) "Persistent storage for labelled trees" =>

This investigation compares representations of finite ordered trees with arbitrary
bitstring labels. The first deployment priority is self-hosting: parsing, typechecking,
interpretation, compilation, and editor tooling. Frequent persistent updates and
structural sharing are central to these workloads. Large databases, streams, and
eventual operating-system applications remain within the design scope.
The literature search is dated 21 September 2026. Measurements describe the stated
programs and machine, and are not measurements of a complete presheaf typechecker.

The recommended direction is a common semantic interface with native packed words,
immutable blocks, and a balanced persistent sequence representation for large values.
Small syntax values should fit in a block without an allocated navigation tree.
Typed syntax views and bounded caches can serve the compiler without imposing their
metadata on every stored value. Static succinct indexes belong in sealed blocks or
frozen snapshots. The evidence supports investigating this combination; it does not
establish one implementation attaining every known optimum simultaneously.

# Semantics and the space denominator

A value is one finite rooted ordered tree, with an exact finite bitstring at each node.
Empty labels, leading zeroes, child order, and repeated equal subtrees are observable.
Pointer identity, block boundaries, hash choice, and machine word width are not.
The repository already supplies the binary/rose equivalence and concrete syntax;
{name}`Geb.Ast.ofRose_toRose` and {name}`Geb.Rose.parse_print` should remain semantic
anchors rather than be replaced by a second language of trees.

For fixed node count $`n \ge 1` and total label length $`M`, the family has
$`C_{n-1}\binom{M+n-1}{n-1}2^M` members: choose an ordered topology, a weak composition
of the payload length into node lengths, then the payload bits. Thus its information
bound, up to integer rounding, is
$`H(n,M)=M+\log_2 C_{n-1}+\log_2\binom{M+n-1}{n-1}`.
This is a counting argument for this investigation, not a new formalized theorem.
The familiar approximately $`2n` topology bits omit the cost of label boundaries.
Known schema lengths can reduce the family and its bound; an unrestricted bitstring
label cannot silently inherit that saving. Headers specifying $`n` and $`M` also count.

Succinctness should mean $`H+o(H)` over a stated asymptotic regime. A practical claim
such as “at most 1.3 times the information bound” needs a minimum object size, the
header cost, and an explicit treatment of allocation, alignment, indexes, and hashes.
For tiny objects the fixed overhead cannot vanish. For persistent histories, report
the live shared graph and the incremental bytes per edit; comparing the entire history
only to the latest tree's information bound would be misleading.

Separate topology, length, and payload sequences make these costs visible. Elias delta
codes for every label length are a useful baseline. Monotone cumulative endpoints,
shifted by their ordinal to distinguish empty labels, admit Elias–Fano techniques.
Neither a per-label delta code nor an unspecified $`O(n)` endpoint redundancy proves
uniform succinctness for all ratios $`M/n`. Adaptive block encodings, including compact
small lengths and enumerative composition codes, merit a later comparison. They must
come with an exact decoder and a redundancy bound, including per-block headers.

# Existing correctness boundaries

The Elias representation already separates raw payload bits from length headers.
{name}`Geb.BitTree.Elias.length_encode` counts its bits exactly.
{name}`Geb.BitTree.Elias.representation_redundancy_vanishes` proves vanishing relative
redundancy when average payload length diverges. It does not assert succinctness in
every relation between payload size and node count, or provide an indexed navigation bound.

The coded-signature recognizer
{name}`Geb.SizeBounded.Logspace.WTree.CodedSig.recognize` checks syntax, labels, arities,
and child indices. Its child scan revisits the input for each node. The theorem
{name}`Geb.SizeBounded.Logspace.WTree.CodedSig.recognizeExprSem_eq_singleton_iff_isW`
connects it to a successor-free expression, conditional on expressions computing
the signature's label and edge tests. These existing conditions must survive a
representation change.

For presheaves, {name}`Geb.PresheafRecognition.native_eq_scan` reduces hereditary
naturality to local tests. {name}`Geb.PresheafRecognition.restrictedEq_eq_true_iff`
reduces restriction comparisons to a root-shape test and equalities of original
subtrees. A new implementation should compare input spans or shared immutable values,
without constructing restricted copies. The theorem
{name}`Geb.Oitavem.Expr.presheafScan_pass_iff` supplies the outer scan once its local
position expression and node-enumeration obligations are discharged.

An Oitavem syntax witness and extensional equality are the intended certification
interface. The current umbrella module states that general reader substitution and
the retained-prefix recursion machine are still open. This investigation does not
claim the repository has already completed the algebra's machine soundness theorem.
Finitarity alone is insufficient: the repository also proves
{name}`Geb.Oitavem.no_universal_decider` and the presheaf counterexample
{name}`Geb.Oitavem.PresheafCounterexample.no_oitavem_nativeCheck`.

# Candidate representation

Use a depth-first opening/closing bit pair for each semantic node. Keep labels in
opening order. A subtree then occupies an interval of topology bits, an interval of
label lengths, and an interval of concatenated payload bits. One immutable root record
ties these sequences together; a transaction publishes all changed roots together.
The physical sequence tree can rebalance independently of the semantic tree, avoiding
path copying through every ancestor of a semantically deep chain.

:::table +header
*
  * Component
  * Proposed representation
  * Contract
*
  * Topology
  * Packed balanced parentheses, persistent sequence blocks
  * One root; counts and excess summaries agree with the bits
*
  * Labels
  * Exact lengths plus packed concatenated payloads
  * One length per opening; their sum is the payload bit count
*
  * Navigation
  * Relative counts in branch nodes; optional local static indexes
  * No stored global offsets requiring suffix-wide updates
*
  * Identity and caches
  * Shared handles, optional fingerprints, exact fallback comparison
  * Equality and typechecking remain deterministic and exact
:::

For the hot representation, start by comparing 256-byte, 1-KiB, and 4-KiB immutable
pages. Branches carry subtree lengths, opening counts, and excess minima/maxima;
the proof prototype below isolates the total/minimum part. An AVL sequence is a small
testable reference. A wider tree can reduce pointer chasing, but copies more child
entries on each changed path. This tradeoff should be measured on editor traces before
selecting a branching factor. Leaf coalescing, occupancy, and reclamation are part of
the representation contract, not optional implementation details.

The interchange format should be a separate, flat canonical serialization, with a
version, explicit counts, specified bit order, bounded length headers, and zeroed
unused final-word bits. Reject truncation, trailing material, arithmetic overflow,
inconsistent lengths, and extra roots. These are proposed requirements, not a frozen
wire specification. An initial uncompressed boundary mode is easier to verify; a
compressed mode needs its own accounting and equivalence theorem.

Machine widths should be compile-time backend parameters with a bit-level meaning.
Use native unsigned arithmetic, shifts, masks, popcount, and optional SIMD where
available, with a portable fallback. Never shift by a width or rely on overflowing
length arithmetic. Runtime words can be 8, 16, 32, or 64 bits without changing values;
Bend/HVM2 also requires consideration of 24-bit numerics. A bitstring remains a
length together with its bits even if that pair is entirely implicit in block metadata.
The [GMP limb representation](https://gmplib.org/manual/Integer-Internals) is useful
for word packing and arithmetic, but its normalization of leading zero limbs cannot
be used as bitstring identity without the separate exact length.

This is a candidate architecture, not a completed format or a proved optimal data
structure. Its static topology component is supported by
{citep NavarroSadakane2014}[]. Its fully persistent implementation and label-boundary
representation require separate analysis. Static succinct indexes are useful within
sealed blocks and frozen snapshots; they do not supply a dynamic persistence bound.

## Work, history space, and occupancy

Let $`P` be the number of occupied pages, $`b` their payload capacity in bytes, $`w`
the machine word size in bits, and $`f` a fixed internal fanout. Under a maintained
balance and occupancy invariant, a path-copying point edit copies
$`O(b+fw\log_f P/8)` bytes. Rebuilding an ordinary page summary takes $`O(b)` work
with the byte-table scan used here; word/SIMD implementations can improve the constant.
Splice costs add the newly written data and boundary-page rebuilding. Snapshot creation
is constant handle work; dropping the last reference to a large unshared region can
take linear reclamation work and should not block an editor request.

Physical balance does not make every semantic operation logarithmic. A full scan or
serialization must read/write its output-sized data. Materializing a changed recursive
syntax spine can take its semantic depth. A general dependent fold can have a critical
path proportional to that depth. Incremental typechecking may invalidate distant
users of a changed binding, even when the changed source span is small.

The prototype's fresh pages are full, but its splices do not coalesce fragments. It
therefore has no worst-case succinctness guarantee under long edit histories.
Conventional half-full B-tree pages can approach twice the payload space before
metadata, which fails the desired factor. To promise a smaller factor, specify a
stronger occupancy/repacking policy and charge its update work and retained versions.

Fixed-size pages with fixed-size pointers are practically compact, not automatically
asymptotically succinct. In a word-RAM with $`w=\Theta(\log N)`, branch metadata alone
costs roughly $`O((N/B)\log N)` bits for $`N` encoded bits and $`B` bits per page.
Making this $`o(N)` requires growing page sizes or compressed addressing, as well as
vanishing slack. Pages of order $`\log^2 N` address that metadata term, but are not a
proof for the whole structure. A 256-bit digest per 1-KiB page adds another 3.125 percent
before internal digests. Hashes should be selective, not attached to every tiny node.

# Logspace recognition and hashing

Use the conventional model: a read-only, two-way input, write-only output, and
$`O(\log N)` work bits for input length $`N`. A constant number of word-RAM counters
has this bound when their widths grow as $`\Theta(\log N)`; fixed 64-bit code instead
has a finite supported size and must check it. Input storage, result storage, persistent
caches, and parallel workers must not be silently charged to the work tape or omitted
from the practical memory report.

The topology recognizer needs a position and an excess counter, rejecting negative
prefixes and a nonzero final excess. That accepts a forest, including the empty one.
For a single tree, additionally require a nonempty input and strictly positive excess
at every proper nonempty prefix. Label lengths can be checked sequentially against
the payload budget and opening count. These steps have direct logarithmic-counter
implementations. The left-fold theorem below establishes summary correctness, not a
complete machine-space proof or an Oitavem syntax witness.

For W-type recognition, enumerate nodes and their children by input positions and
rescan when necessary; check constructor decoding and arity. For slice W-types also
check the required result index and each direction's source/target index. For presheaf
W-types, enumerate the prescribed morphisms and local naturality comparisons using
the existing restriction-equality reduction. The needed hypothesis is effective,
complexity-bounded enumeration and comparison, not merely mathematical finiteness.
A fixed number of nested scans preserves logarithmic workspace, although it can have
large polynomial time. This explains how a fast cached recognizer can agree exactly
with a slower small-space witness without inheriting its running time or workspace.

The next certification obligations are concrete:

1. Specify the new serialization and prove its decode/encode laws, including invalid
   encodings. Show how each logical input bit can be read by the reference witness.
2. Construct a size-controlled logspace translation or a direct algebraic recognizer.
   When using translations, establish their polynomial length bound and random-access
   simulation; do not materialize the intermediate word on the work tape.
3. Supply the existing label, edge, local-presheaf-test, and enumeration witnesses,
   then prove the optimized recognizer extensionally equal to their composition.
4. Keep the unfinished general Oitavem machine soundness proof as a separate dependency.
   The implementation need not itself interpret the expression or run in logspace.

Compressed sharing changes the input-size question. A small DAG can unfold into an
exponentially larger tree. A logspace claim in the flat encoding's length is not a
logspace claim in compressed DAG size, and polynomial work in the unfolded size may
be exponential in stored bytes. External references also need explicit validity and
termination rules. Initially certify the flat finite format; study a DAG format with
its own size measure rather than implicitly transferring the result.

Logspace is also not synonymous with one-pass streaming. A one-type parenthesis stream
can maintain prefix excess, but arbitrary subtree equality and naturality checks may
need rereads or external storage. An infinite M-type stream never supplies the final
end-of-input test for a finite W-value; recognize completed framed values and maintain
prefix invariants instead of deciding the whole infinite stream.

For a fixed digest width, a balanced binary Merkle reduction over a blob can keep a
frontier of $`O(\log N)` fixed-size digests plus logarithmic counters. Thus computing
its root has a logarithmic-workspace algorithm in this model. If the security parameter
itself is $`\Theta(\log N)`, that frontier can occupy $`O(\log^2 N)` bits. Outputting
all nodes requires an output convention and may require recomputation, but not retaining
all nodes in work memory. An arbitrary depth-$`N` semantic tree does not inherit the
balanced-blob frontier bound. This is an algorithmic argument, not a formalized theorem.
[BLAKE3's specification and implementations](https://github.com/BLAKE3-team/BLAKE3)
provide a concrete fixed-width, chunked, SIMD/parallel hashing model to study.

A physical-page Merkle root changes when pages split or rebalance. A semantic content
identifier requires a canonical encoding or canonical chunking rule. Streaming a
canonical flat encoding gives a stable digest but may require linear rehashing after
an insertion; it does not promise logarithmic persistent update cost. Fingerprints
can reject inequality quickly. They cannot certify equality in an exact typechecker;
use pointer equality for shared objects and exact comparison or collision-checked
interning for the remaining equal-fingerprint case.

# Literature and reusable implementations

The following are separate building blocks with different assumptions. Combining
their names does not combine their guarantees.

* {citep NavarroSadakane2014}[] gives static ordinal-tree topology in
  $`2n+O(n/\operatorname{polylog} n)` bits with constant-time navigation, and dynamic
  variants with logarithmic operations. An improved variant reaches
  $`O(\log n/\log\log n)` for most operations; attach/detach has a separate
  $`O(\log^{1+\epsilon}n)` bound. These word-RAM results guide summary design but do
  not automatically cover arbitrary labels or full persistence.
* {citep HamadaEtAl2024}[] reduces tree-cover bookkeeping by representing each microtree
  with at most two BP intervals. Its practical average-case RMQ results make it a
  candidate for sealed blocks. Sub-$`2n` measurements in those settings do not violate
  the worst-case topology bound or supply an incremental persistent implementation.
* {citep KuszmaulLiangZhou2026}[] obtains optimal amortized expected dynamic
  insert/delete/rank/select time $`O(1+\log n/\log\log U)` with nearly optimal space
  for ordered sets in the polynomial-universe regime. Its compressed tabulation
  techniques and shared-table assumptions deserve attention. This is not a measured
  BP-tree library or a worst-case, fully persistent range-minimum theorem.
* {citep KanedaArimuraInenaga2026}[] is particularly relevant to retained versions:
  FeAVL uses path-copying AVL trees for fully persistent strings and worst-case
  logarithmic updates, splits, and concatenation, with logarithmically many new nodes.
  Its fingerprint-based equality/LCE guarantees are probabilistic. Borrow its balance
  and persistence analysis while retaining exact equality for recognition. Its grammar
  variant motivates a separate repetitive-data backend.
* [SPIDER](https://arxiv.org/abs/2405.05214) combines interleaved rank metadata and
  predicted select search, reporting 3.82 percent overhead for its tested configuration.
  [BiRank/QuadRank](https://curiouscoding.nl/posts/quadrank/) further emphasize cache
  traffic, batching, prefetching, and multicore throughput; BiRank reports 3.28 percent
  overhead. Their published comparisons are workload-specific. Neither rank-only
  throughput nor rank/select metadata is the total cost of BP navigation and labels.
* The local Gog–Fischer paper on “shared data structures” concerns sharing navigation
  auxiliaries between succinct operations. It does not mean sharing persistent
  application versions. Its [author's publication page](https://ae.iti.kit.edu/english/1621.php)
  remains useful background for avoiding duplicated indexes.

The Rust experiment pins [vers-vecs](https://github.com/Cydhra/vers) 1.10.2 and
[sux](https://github.com/vigna/sux-rs) 0.14.0 with a separate Cargo lockfile, outside
Geb's production dependencies. The former offers a BP tree with broader navigation
and configurable block size; its implementation documents logarithmic navigation.
The latter supplies word-level Jacobson balanced-parenthesis matching, with Elias–Fano
pioneer information. A matching primitive is not the whole labelled-tree interface.
Both are useful baselines or frozen-block components, and neither is a replacement
for the persistent update layer. Validate untrusted parentheses before calling a
constructor that assumes valid input. The prototype tests valid queries exhaustively
on its generated shapes, not the libraries' complete API or every malformed input.

Content-defined chunking is relevant to deduplicating large changing blobs.
[FastCDC's Rust implementation](https://github.com/nlfiedler/fastcdc-rs) and
[VectorCDC, FAST 2025](https://www.usenix.org/conference/fast25/presentation/udayashankar)
offer practical starting points. Boundary resynchronization is a workload-dependent
benefit, not a worst-case guarantee that an edit affects a bounded number of chunks.
Apply this first to cold payloads or distribution artifacts; low-entropy topology and
tiny syntax nodes need different evaluation.

## Lessons from compilers and syntax tools

The self-hosting priority changes where implementation effort should go first.

* Clojure's [implementation](https://github.com/clojure/clojure/tree/master/src/jvm/clojure/lang)
  and the [CHAMP paper](https://michael.steindorfer.name/publications/oopsla15.pdf)
  motivate bitmap-packed nodes, path copying, and cache-conscious layouts for
  environments, symbol tables, and memo tables. A HAMT's key-hash order does not
  implement the semantic order of child sequences; use a sequence structure there.
* [Tree-sitter](https://tree-sitter.github.io/tree-sitter/using-parsers/3-advanced-parsing.html)
  reuses an edited old tree during reparsing and supports cheap copies for concurrent
  use. Separate source coordinates from immutable semantic identity. Editing one
  snapshot should not mutate an older snapshot being used by a language-server request.
* [Rowan](https://raw.githubusercontent.com/rust-analyzer/rowan/master/src/green/node.rs)
  demonstrates compact immutable nodes and cached child offsets. Its child replacement
  rebuilds a child collection; do not assume logarithmic work in arbitrary node arity.
  Typed parent-aware views can be short-lived wrappers, while large child collections
  and deep data use balanced sequences independently of the syntax hierarchy.
* [RRB vectors](https://doi.org/10.1145/2784731.2784739) provide a wider persistent
  sequence design with split/concatenate operations for parallel work. Zed's
  [sum tree](https://github.com/zed-industries/zed/tree/main/crates/sum_tree) is an
  Apache-2.0 editor implementation with shared nodes and generic composable summaries;
  it is a source-reuse candidate, not a standalone published crate at the inspected
  revision. [crop](https://github.com/noib3/crop) supplies a copy-on-write text B-tree.
  These should be baselines before replacing the reference AVL tree with custom
  production code. Text-specific UTF-8 APIs need adaptation for arbitrary bitstrings.
  They were source-reviewed here, not benchmarked. The public
  [editing traces](https://github.com/josephg/editing-traces) used by rope benchmarks
  can supplement Geb-specific parsing and checking traces in that comparison.
* [Rustc's arena and interning design](https://rustc-dev-guide.rust-lang.org/memory.html)
  and [LLVM's FoldingSet](https://llvm.org/doxygen/FoldingSet_8h_source.html) suggest
  scoped allocation and exact structural uniquing. Pointer equality becomes useful
  after successful interning. Arena lifetime and collision handling still matter for
  a long-running editor retaining old document versions.
* [SIMD JSON parsing](https://arxiv.org/abs/1902.08318) separates bulk structural
  classification from higher-level parsing. Apply this to word-level scanning,
  delimiter masks, and batched validation before constructing individual nodes.
  [parse-many](https://raw.githubusercontent.com/simdjson/simdjson/master/doc/parse_many.md)
  illustrates bounded-buffer processing of multiple documents; it does not establish
  constant-space validation of any arbitrarily large single dependent object.

For an editor, the useful unit of caching is a checked value under a particular
signature, index, environment, and restriction context. A content digest alone omits
these dependencies. Reuse unchanged scopes and subtree checks, cancel obsolete
requests, and account for all retained roots. Batch transient construction is useful
inside a uniquely owned builder; published snapshots remain immutable. This can reduce
allocation before implementing a more elaborate globally compressed representation.

# Executable summary algebra

The following source is compiled as part of the library and rendered directly here.
Its associativity theorem is the basis for parallel block reduction and cached
summaries in the persistent prototype.

The proofs establish associativity, exact prefix acceptance, block regrouping, and
equivalence of the accumulator scan. They use no new axioms or admitted obligations.
They do not yet establish an isomorphism between a complete labelled wire format and
the existing W-type, nor verify the Rust AVL implementation or a GPU runtime.

{includeLiterate "." Geb.Prototypes.SuccinctTree "Composable block summaries" (level := 2)}

# Measurements and their limits

The CPU was an AMD Ryzen AI 9 HX 370 under WSL2, with 16 logical processors exposed.
Rust was 1.99.0-nightly (3d6c19bb9, 2026-08-11); the standalone prototype used
{lit}`rustc -O --edition=2021`, without {lit}`target-cpu=native`.
The GPU was an NVIDIA RTX 4070 Laptop GPU with 8 GiB, Windows driver 616.92.
Measurements are local microbenchmarks without controlled CPU frequency or confidence
intervals. Do not extrapolate them to a different processor, compiler, tree distribution,
or end-to-end compiler throughput.

## Existing Lean implementation

The following checks cover malformed topology and word boundaries, composition of
byte summaries, the existing Elias scanner/algebra interpreter, and the repository's
concrete-syntax parser. The composition law is proved for all word pairs; the worked
examples execute through Lean's interpreter during the build.
The timing functions reject an unexpected result; timings themselves are not assertions.
Routine elaboration runs the leaf benchmark at payload lengths zero and one.
Passing {lit}`[0, 1, 8, 32]` to {lit}`benchmarkRecognition` runs the larger comparison.

In the recorded leaf experiment, a 32-bit payload produced a 43-bit Elias input. The
shared algebra interpretation took approximately 11.2 seconds; the native scanner
took about 28 microseconds. These are single diagnostic interpreter evaluations, with
warm-up effects visible at smaller sizes. They justify prioritizing extensional
replacement of interpreted primitives, but are not a reliable speedup estimate for
the complete typechecker. The syntax experiment adds deep and wide trees to the
repository's small examples; it measures parsing plus exact result equality, with
printing excluded. At 256 links/children (1,285 input characters), these evaluations
took 138 ms for the chain and 74 ms for the wide tree. Compiled native code and
incremental checking require their own
benchmarks before setting latency targets. The observations are retained in {lit}`lean.csv`.

{includeLiterate "." GebTests.Prototypes.SuccinctTree "Executed Lean experiments" (level := 2)}

## Persistent Rust sequence

The adjacent {lit}`Geb/Prototypes/SuccinctTree/bench.rs` uses only the Rust standard
library. Leaves hold byte arrays; AVL branches cache summaries and lengths; immutable
nodes use {lit}`Arc`. It implements point reads/updates, split/concatenate, byte-aligned
splices, matching-close queries, and range summaries. It is a sequence prototype,
not a complete labelled-tree codec. Two runnable tests exhaust every 16-bit topology
and its closing queries, and compare 1,500 edits branching from older versions against
a flat oracle while checking balance, lengths, summaries, and retained values.

The 1,000-operation read/update mixes adapt the 50/50 and 95/5 proportions of
[YCSB workloads A and B](https://github.com/brianfrankcooper/YCSB/tree/master/workloads).
They use uniform or hotspot positions. The hotspot chooses 80 percent of operations
from the first 20 percent of positions and the rest from the whole input; therefore
about 84 percent land in that first region. These are in-memory sequence analogues,
not YCSB database results. Every updated version is retained. Separate traces exercise
alternating insertion/deletion and branching updates from the original root.

Each timing is the median of seven runs after one warm-up. Timed result destruction
is included. Initial tree construction is excluded from query/update timings and
measured separately. Requested bytes count allocations reachable from the supplied
version roots once, including node/Arc headers and root entries. They exclude the
separate input buffer, lookup table, other roots, allocator rounding/metadata, spare
root-vector capacity, temporary allocations, stacks, and the accounting HashSet.
The flat baseline's storage column counts only its byte buffers.

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

At 16 MiB the same update mix took 0.705, 0.850, and 2.000 ms for the respective
page sizes. These results support page-level sharing and expose the copy/metadata
tradeoff; a deliberately full-copy baseline is not evidence of superiority over a
production persistent-vector or succinct-tree library. The 1-KiB setting is a useful
next experiment, not a universal optimum. The ratios concern topology bytes in a
freshly packed sequence, not the full labelled-value information bound.

For summary scans over 16 MiB, the scalar bit loop took 59.73 ms, byte-table scanning
11.60 ms, and the eight-thread version 2.53 ms. At 1 MiB, table scanning took 0.696 ms
and eight threads 0.858 ms: spawning threads erased the benefit at that size. A worker
pool and batching are relevant follow-ups. The scan datasets labelled {lit}`star`
and {lit}`nested` in the CSV are forests of four leaves or one depth-four chain per
byte; {lit}`chain` is one long chain. They test scan mechanics, not a parser for
application syntax. Parallel reduction uses extra worker state; its space is not the
workspace of the sequential logspace witness.

The raw files {lit}`cpu-1m.csv` and {lit}`cpu-16m.csv` also retain build, range-summary,
navigation, hotspot, splice-history, and branch-history measurements. Fragmentation,
garbage collection tail latency, cross-thread reference-count contention, arbitrary
bit-aligned edits, and label-boundary compression remain unmeasured.

## Static Rust libraries

The separate {lit}`libraries.rs` constructs single-root stars, chains, and a root with
short chains, each with 4,194,304 nodes and 1 MiB of BP bits. A stack oracle checks
every opening's matching close in both libraries before timing 100,000 deterministic
random opening queries. Constructors, the oracle, and its memory are outside timings.
The median again uses seven runs after a warm-up; default release CPU settings apply.

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

The vers-vecs heap-size method reported 1,884,168 bytes for each shape, about 1.797
times the BP bytes, including its chosen indexes. This configuration is not a
minimum-space measurement. sux heap space was not measured. The shape-dependent
ordering is a reason to keep both baselines. These static-query results are not
directly comparable to the rope's forest-query trace or its persistent-update results.
Construction cost, other navigation operations, and target-specific tuning remain
open comparisons. Raw observations are in {lit}`libraries.csv`.

## Bend, HVM2, CUDA, and HVM4

Bend 0.2.38 and HVM 2.0.22 were available on the host; temporary copies of the same
versions generated identical C for the experiment. The GPU works under WSL2 when
accessed outside the restricted process sandbox. CUDA 12.8's headers did not compile
against this host's GCC/libc combination. A temporary, checksum-verified CUDA 13.3.1
redistribution compiled the unchanged generated CUDA with {lit}`-arch=sm_89`.
This establishes this configuration's feasibility, not an upstream-supported matrix.

The checked program generates seed-dependent 24-bit words at the leaves of a balanced
recursion, scans each word, and combines summaries. Both backends returned
{lit}`(105134, -66)` at depth 16, agreeing with the independent Python oracle.
There is no stored input transfer and no persistent update in this experiment.
Whole-process median wall times over three runs after a warm-up were 0.610 seconds
for generated C and 0.572 seconds for generated CUDA. A first GPU run reported
0.22 seconds internally but took 0.80 seconds wall time. Runtime-internal timings
exclude costs important to a short editor request; the measured end-to-end advantage
here is small, not a compelling reason to put small interactive operations on a GPU.

[HVM4](https://github.com/HigherOrderCO/HVM4) was inspected and built at commit
{lit}`6defdfc7dae2a3cca5dd6e74ed0612385b5646a8`. Its documented interaction calculus
extends lambda terms with explicit duplication and superposition; these control lazy
sharing, including inside lambdas. This makes it relevant to Geb's foundational
computation model. It is not by itself a correctness or complexity theorem identifying
every runtime operation with Lafont's minimal interaction combinators
{citep Lafont1997}[]. A formal
translation and a cost correspondence would be separate obligations.

The inspected HVM4 C source has 64-bit tagged term words with 32-bit unsigned numeric
payloads and 24-bit extension fields. Constructors hold at most 16 fields. Dynamic
terms live in a mutable bump-allocated heap; static book terms are immutable. The
implementation has no CUDA backend, worker-thread scheduler, or external-call layer.
Its heap allocation counter grows during evaluation and storage is released at runtime
teardown; this is not a long-lived persistent-store reclamation strategy. These are
observations about this commit, not limits of interaction calculus.

The HVM4 summary port masks generated seeds to 24 bits and implements signed comparisons
over modulo-$`2^{32}` summaries. At depth 12 it returned {lit}`(2332, -529)`, matching
the oracle, with median whole-process time 0.367 seconds. A diagnostic run reported
10,331,617 allocated heap slots and about 592 MiB peak RSS, which also includes other
runtime structures. This differs in input size and execution strategy from the HVM2
experiment and is not a speed ranking between runtimes. The upstream test script's
{lit}`fib_small` and {lit}`spin` exceeded its default two-second timeout; the other
reported cases passed. That run is not recorded as a clean upstream test pass.

Interaction-net duplication must not be assumed to have {lit}`Arc`'s constant-time
read-only sharing cost: duplication may propagate through a consumed value. Packed
immutable arrays or block handles would need an explicit runtime primitive and
semantics, or an encoding whose allocation cost is measured. Keep the block-summary
algebra portable; prototype the model of computation separately from the packed store.
For parallel bulk work, use coarse independent blocks, preserve reduction order, and
measure transfer, launch, allocation, and reclamation along with reduction time.

## Reproduction

Run these from the repository root. Generated executables and Cargo build products
are kept outside the source tree. The Cargo packages are experiment dependencies only.

```
lake build Geb.Prototypes.SuccinctTree GebTests.Prototypes.SuccinctTree
rustc -O --edition=2021 --test Geb/Prototypes/SuccinctTree/bench.rs -o /tmp/geb-tree-tests
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

The Rust runner defaults to at most two scan workers. Its optional second argument
accepts 1, 2, 4, or 8; 1 skips threaded scans. The recorded CPU CSVs include all three
parallel configurations, up to eight workers. On constrained Linux/WSL hosts, restrict build
commands to two available CPUs with {lit}`taskset` and run builds and benchmarks
sequentially. Such restricted reruns are a different configuration from the recorded
measurements; keep their results separate.

Build HVM4 at the recorded revision using its documented
{lit}`clang -O2 -o src/hvm src/hvm.c`. For the temporary NVIDIA redistribution used
here, add its {lit}`lib` directory with {lit}`-L` when invoking its {lit}`nvcc`.
The program {lit}`runtimes.py` checks every result and writes the whole-process timing
CSV. Lean timing output appears on rebuilding its test module; cached build output
can replay older observations, so do not treat a replay as a fresh run.

# Recommendations, ordered for self-hosting

1. *Prioritize native execution and incremental compiler reuse.* Preserve the proved
   semantics and algebraic witnesses, but replace bit-by-bit interpreted operations
   with packed-word implementations proved extensionally equal to them. Keep small
   syntax values in compact immutable blocks, use typed views, and reuse unchanged
   subtrees/scopes with context-sensitive cache keys. Use HAMT-like maps for compiler
   environments, not ordered children. The first acceptance workload should be parsing
   a source file, changing a token, producing diagnostics, and retaining older LSP
   snapshots. Measure cold and warm latency, allocations, invalidation breadth, and
   reclamation pauses. The current measurements support the primitive-replacement
   priority; they do not yet quantify an incremental compiler's speedup.
2. *Develop the persistent packed-sequence backend for growing syntax and general
   values.* Start with the tested AVL/block mechanism and a 1-KiB comparison point,
   adding exact bit spans, label lengths, coordinated splices, and bounded fragmentation.
   Compare wider branches only after representative editor traces are available.
   This separates semantic depth from physical balance and offers version sharing
   without allocating a hash or pointer-rich object per tiny semantic node. The
   unresolved costs are occupancy maintenance, boundaries, and retained-history memory;
   no global succinctness theorem is claimed for the present prototype.
3. *Use static succinct indexes when values become stable.* Evaluate vers-vecs, sux,
   and tree-covering/local rank layouts on module caches, immutable compiler artifacts,
   sealed subtrees, and large query-heavy snapshots. Their space/query tradeoffs can
   differ by tree shape. Rebuilding a whole static index after each keystroke is outside
   their intended role here. This path gives a practical way to tighten storage while
   the hot representation remains easier to update and verify.
4. *Add specialized representations when workloads justify them.* Exact hash-consing,
   grammar compression, content-defined payload chunks, and persistent Merkle indexes
   can help repetitive build graphs and large databases. They need separate compressed
   size, collision, and version-lifetime analyses. GPU bulk scans and HVM2 reduction
   are feasible experiments; HVM4 is presently a computation-model experiment. None
   should delay a responsive native self-hosted toolchain.

Before selecting a foundational format, require a complete codec equivalence, a
recognition witness and optimized-equivalence theorem for the supported signatures,
an occupancy/history-space bound, and traces of real parsing/typechecking/editing.
Include malformed and adversarially deep/wide inputs, many tiny labels, large blobs,
branching undo histories, and cancellation while old readers remain active. Compare
bytes against the full label/topology bound and measure both throughput and tail
latency. These are the decision gates for a full implementation; the compiled proofs,
tested prototypes, raw results, and ranked options above are the investigation's
reusable starting point.
