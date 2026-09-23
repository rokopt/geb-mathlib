# Bootstrapping Geb

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Existing material and its bootstrap role](#existing-material-and-its-bootstrap-role)
- [Boundary of the seed](#boundary-of-the-seed)
- [Values, tags, and external identity](#values-tags-and-external-identity)
- [Computation and metalogic](#computation-and-metalogic)
- [Lessons from existing bootstraps](#lessons-from-existing-bootstraps)
- [Acceptance milestones](#acceptance-milestones)
- [What self-compilation must establish](#what-self-compilation-must-establish)
- [Computation-certificate prototype](#computation-certificate-prototype)

<!-- END doctoc -->

The proposed bootstrap is a Lean implementation of a finite executable
profile, a certificate checker, and codecs, followed by a compiler and
language tools written in that Geb profile. The semantic contracts remain
available as a reference implementation after their implementations move
into Geb. Self-compilation does not require first implementing the
optimized representation, a content-store database, or the categorical
library in Geb.

The initial proof requirement is a checked kernel that can support later
development in Geb. The computation-certificate prototype linked below
implements one fragment of that requirement. It does not implement the
free-topos logic or a self-hosting compiler. The stages below are proposed
acceptance milestones, not claims that those components exist.

## Existing material and its bootstrap role

| Material | Reuse | Boundary |
| --- | --- | --- |
| [Rose trees](../Geb/Prototypes/RoseTree/Basic.lean) and [bitstring ranks](../Geb/Prototypes/RoseTree/Bits.lean) | The value model and recursors | Storage optimization is independent of this model |
| [Rose-tree serialization](../Geb/Prototypes/RoseTree/Spine.lean) | An injective encoding with a characterized recognizer | A versioned file envelope and complete operational codec contract still need to be fixed |
| [Packed representation](../Geb/Prototypes/RoseTree/Packed.lean) | Word-level implementation candidate | Its agreement with the list implementation is tested, not proved |
| [Definitions](definitions.md) and [their implementation](../Geb/Prototypes/Definition/Basic.lean) | Terms, parameters, linking, unfolding, interpretation laws | Finitary mathematical data still need effective encoders and validated external references |
| [Vertices](../Geb/Prototypes/Definition/Vertex.lean) | Selection and composition of structural addresses | An export direction and an arbitrary syntax vertex have different meanings |
| [Triage implementation](../Geb/Prototypes/Computability/Triage/Bitstrings.lean) | A total one-step execution interface with soundness | A reduction strategy is not a complete equality decision procedure |
| [Concrete syntaxes](concrete-syntaxes.md) | Existing parser/printer laws and syntax conventions | The finite-label S-expression implementations do not directly supply the arbitrary-label definition codec |
| [Bitstring metalogic](bitstring-metalogic.md) | The distinction between proof checking and theorem search | This is a design account, not an implemented free-topos kernel |

The experimental repository was inspected in its `geb-idris/` and
`geb-lean/` subdirectories at revision
`9c24f4727d3c6c34abece2174b04fd74e1ab37aa`. Relevant findings are:

- [Idris GebTopos][old-idris] contains finite constructor encodings,
  indexed expression signatures, folds, and checking algebras, including
  `GWExpWT`, `gwexpCata`, and `finCatSigCheck`. These are specifications and
  examples to port by use case; transferring the whole module into the
  seed is not required.
- [Lean FreeToposBT][old-topos] presents base objects, arrows, and equality
  constructors, then a second layer with equalizers and coequalizers of
  base arrows. That restriction is not closure under the constructions
  needed at arbitrary later types. Reusing its name as a certification of
  a complete free topos would therefore be unjustified.
- [InteractionNets][old-nets] has executable graph operations and reduction
  rules. Its raw arrays and wire lists need a checked graph invariant
  before being a trusted execution interface.
- [InteractionExecution][old-execution] explicitly separates its
  polynomial-machine and polling constructions from an adequate
  compositional translation of interaction-net graphs. Its categorical
  packaging does not discharge that translation obligation.
- [TreeCalcPrograms][old-tree-programs] implements bracket abstraction
  using a value fold. [LawvereERKSim.Compiler][old-compiler] translates
  elementary-recursive terms to register-machine programs. These are
  narrower compilation components to examine when implementing the
  corresponding passes, rather than an existing whole-language bootstrap.

These are source inspections, not a fresh build or a correctness audit
of the experimental repository.

## Boundary of the seed

The first supported host supplies Lean compilation, allocation and
reclamation, native natural-number arithmetic, byte input/output, and
ordinary files. A host cryptographic-hash implementation can join that
list when immutable external references are introduced. A pinned host
toolchain and a small runtime are compatible with self-hosting: the Geb
compiler can compile its own source to Lean while Lean continues to
compile the resulting host code.

Keep the following distinctions explicit:

| Component | Initially supplied by the host | Intended Geb implementation |
| --- | --- | --- |
| Values | Natural numbers, child collections, allocation | Representation selection and optimizations; native operations remain possible |
| Execution | Reference evaluator for a fixed profile | Compiler and evaluator with the same observable behavior |
| Logic | Fixed inference checker and its Lean soundness argument | Proof construction, tactics, derived rules, then a checked implementation of the checker |
| Definitions | Validation of finite bodies and references | Richer interfaces, module tools, categorical definitions |
| Storage | Codec and files; optional hash binding | Reader, printer, dependency tools, content store |
| Target code | Lean compiler and runtime | Additional Geb backends as separate milestones |

The logical trust boundary includes the stated kernel rules. The initial
machine-code execution boundary additionally includes Lean's compiler,
runtime, and the relevant host services. Compiling a checker from a
sound Lean definition is not by itself an end-to-end machine-code
verification theorem.

## Values, tags, and external identity

Retain the semantic carrier `RoseTree ℕ`, interpreting each natural label
through the existing `rank`/`unrank` bijection. This preserves empty
bitstrings and leading zero bits. Interpreting a bitstring as an ordinary
binary numeral without its length or sentinel would lose information.

Fixed-width constructor tags are a reasonable implementation technique.
They need not be a limit on the semantic alphabet. For example, a byte
profile could represent ranks below 255 directly and reserve tag 255 for
an arbitrary natural-number rank. Require the escaped rank to be at least
255 if that profile is to be canonical. The escape must be available to
labels at internal nodes as well as leaves. Constructor meanings and
arities belong to a versioned signature, not to the untyped tree carrier.

If fixed-size constructors means fixed arities as well, arbitrary rose
branching needs a list, spine, or block representation with a proved
conversion. It should not silently become a restriction on values. In
Lean, start with the existing W-type and native `Nat`; a separate small
integer wrapper is optional. For wide nodes, tabulate directions in an
array: the existing list-based `RoseTree.node` indexes a list, so it does
not establish constant-time child access. Certificate nodes in the
prototype have at most two children.

The [representation chapter][representation] also identifies a ceiling
of the natural-number implementation: large-label scanning and hashing
need efficient access to payload words. That is a reason to replace the
physical representation when those workloads appear, not to delay the
bootstrap on a custom big-number representation.

Fix one canonical tree encoding and its versioned envelope before
assigning durable hashes. Specify framing, bit order, padding, natural
number encoding, full input consumption, and malformed-input behavior.
Reuse the existing wire language; obtain a complete decode/encode
round trip before declaring the external contract stable. A human
S-expression view can be layered over those trees. Names, comments, and
source locations remain separate annotations.

A minimal definition block follows the existing construction:

```text
block = (profile, imports, export layout, bodies)
reference = (immutable block identity, validated export direction)
body = term over a fixed signature with explicit import/parameter slots
```

Start with acyclic blocks and recursors. Reject unresolved references,
out-of-range paths, mismatched interfaces, and cycles in that profile.
Recursion through a declared recursor is distinct from an arbitrary
cyclic equation block. General guarded or partial recursive blocks need
their own semantic profile; a syntactic equation does not prove that it
has a unique solution.

There are two separate addressing problems. A local structural path
selects a position within a fixed tree. It does not identify that tree
across edits or distinguish two different dependency environments. A
first executable can use a closed bundle with a dependency-ordered
manifest and bundle-local ordinals. For separately stored definitions,
use immutable block identities plus paths. Do not expose mutable file
positions as permanent identities.

For the requested Unison-style workflow, introduce host hashing before
growing the bootstrap library, after the canonical bundle is settled.
Use the chapter's BLAKE3 choice through its
[official implementation and specification][blake3]. Hash a canonically
encoded tuple containing a domain identifier, schema version, semantic
profile identifier, imports, export layout, and bodies. Distinct tuple
fields need unambiguous framing. Primitive-profile identifiers must have
a fixed initial convention so their meaning does not depend circularly
on hashing their own definition.

Mutually recursive members, when supported, refer by local directions
inside one hashed block; the dependency graph between blocks is acyclic.
Keep the chosen layout order significant initially. Unison's cycle
references provide a precedent, but Geb does not need permutation
canonicalization to bootstrap. Hashes locate payloads; the checker uses
validated contents and exact equality. Hash equality must not create
logical equality. These choices follow [the existing definition
design](definitions.md#content-identity) and
[Unison's reference format][unison-hashes].

## Computation and metalogic

The first computational profile should serve the compiler's operations:
finite tree construction and inspection, natural-number operations,
products and sums, environments, application, and structural recursors.
The existing finite polynomial signatures and free-monad terms provide
its syntax framework. Select the actual primitive set by implementing
the reader, substitution, and checker workloads, rather than importing
the host's entire library as primitives.

Use the existing in-memory triage machine as the first executable
reference for applications. Keep values in memory between steps instead
of serializing and parsing on every step. Native tree and arithmetic
operations can be explicitly versioned primitives with reference
meanings; their optimized implementations require equivalence arguments.
A typed core with direct recursor operations is preferable to expanding
every compiler operation into tiny combinators if the first real compiler
workloads expose that cost. This is the first performance decision to
measure, before committing to a larger runtime.

Supply a total step function and a bounded runner returning a value,
an error, or a resumable state. Fuel exhaustion does not mean falsehood
or divergence. An unbounded driver can run outside the total logical
fragment. Self-compilation is a transformation of finite syntax and does
not require a total internal evaluator for every program of the same
language. The distinction is already developed in
[the recognizer-complexity account](presheaf-recognizer-complexity.md).

For logic, prefer an explicit presentation of intuitionistic higher-order
logic with a natural numbers or tree object, and certificate checking
over that presentation. [Lambek and Scott, Sections 1.2–1.4][free-topos]
describe the relation between such type theories and their syntactic
toposes. The seed must state its typing, substitution, comprehension,
extensionality, and induction rules. The prototype's computation
equalities supply none of these rules automatically.

This makes two kinds of extension different:

- A derived definition or proof-producing tactic can live in Geb and
  produce evidence checked by the existing kernel.
- A new foundational principle requires a conservative interpretation
  into that kernel or an explicit change of the foundational theory.
  Defining a data type of purported proofs does not make those proofs
  sound. An equality-only computation checker cannot gain the full
  free-topos metalogic by ordinary definitions alone.

Consequently, choose the foundational rule set before migrating general
mathematical proofs, even if its initial user interface is small. Keep
proof terms explicit and finite. Do not require the kernel to decide
arbitrary equality of morphisms, normalize arbitrary programs, or search
for functionality proofs of relations. Logical propositions are not
generally executable booleans.

The proposed equivalence between the tree-based and NNO-based free
toposes is a proof obligation about structure and its preservation. A
bijection of finite trees with natural numbers in `Set` alone does not
prove it. Likewise, migration of Lean code requires checking its logical
strength and universes: a fixed elementary-topos presentation should not
be assumed to internalize all of Lean's universe-polymorphic mathematics.
Reuse source definitions and proofs as specifications, and migrate the
constructive fragment the compiler and libraries actually consume.

Interaction nets remain a candidate backend. First specify graph
well-formedness, interfaces, reduction, readback, and preservation of the
source observations. A tree can serialize a graph by storing node and
port references; unfolding the graph into a tree is not required. Net
sharing, erasure, and duplication are operational structure, not the
same thing as immutable pointer sharing in a rose-tree runtime.

HVM2 documents an executable IR with Rust/C interpreters and C/CUDA
generation. HVM4 documents a different, extended interaction calculus,
including native constructors, affine variables, explicit duplication,
and structural equality; its README labels it pre-launch. These are
separate target contracts. Pin one revision and test its behavior before
making it a bootstrap dependency. Neither parallel speedup nor compiler
correctness follows just from choosing interaction combinators.
Sources: [HVM2][hvm2], [HVM4][hvm4], [HVM4 core syntax][hvm4-core].

## Lessons from existing bootstraps

The final column gives proposed applications to Geb, rather than claims
made by the source projects. Some entries supply relevant implementation
patterns without establishing a self-hosting result.

| System and primary source | Established mechanism | Application to Geb |
| --- | --- | --- |
| [Ribbit][ribbit] and [its REPL paper][ribbit-paper] | A Scheme compiler and compact portable VM; the same compiler serves multiple hosts | Keep a small host runtime and move the reader/compiler/library into Geb; code-size optimization is a separate objective |
| [GNU Mes][mes] | A C implementation of a Scheme interpreter and a Scheme implementation of a C compiler bootstrap one another | An interpreter is enough to start running a compiler written in the new language; replacing the entire host toolchain is a later goal |
| [Gforth cross compiler][gforth] | A cross compiler produces an initial Forth kernel image; much of the interpreter/compiler is Forth | Preserve a reproducible initial image and an explicit host interface; Forth's stack and dictionary need not become Geb's semantics |
| [Nock][nock] | Natural atoms, binary cells, structural axes, and a small evaluator over subjects and formulas | Separate tree addressing from naming, and distinguish the mathematical evaluator from its host representation |
| [Tree calculus/LambAda][tree-start] | The published workflow loads a compiler represented as a tree, reads lightweight notation, and uses textual/ternary/DAG representations | A tiny calculus can support a concrete bootstrap workflow; inspect those tools before inventing another combinator reader |
| [Hagino's categorical language][hagino] and [Charity's term logic][charity] | Categorical datatype declarations provide their associated recursion operations; Charity exposes folds and unfolds through a term language | Make recursors and their laws part of the executable profile, while deriving convenient syntax and richer categorical structure above it |
| [Unison][unison-idea] and [cycle hashes][unison-hashes] | Names are metadata; dependencies use immutable references; recursive cycles have member references | Set canonical syntax, dependency identity, and block conventions before storing a substantial bootstrap library |
| [Lean][lean-bootstrap] | Archived generated C starts a staged build; later stages check stabilization | Define the exact compared artifacts and preserve a seed that does not need the current compiler |
| [Idris 2][idris-bootstrap] | Scheme or Racket bootstraps a language implementation largely written in Idris | A host-language backend can remain while language implementation becomes self-hosted |
| [CakeML][cakeml] | A proved compiler is bootstrapped inside HOL using a proof-producing translation route | Keep implementation, semantic preservation, and the compiler's own bootstrap theorem as distinct obligations |
| [Candle][candle] | A verified HOL Light implementation with an end-to-end soundness result | Aim for an independently checked kernel boundary; do not import its classical logic as Geb's constructive foundation |
| [MetaRocq][metarocq] | Formalized syntax, metatheory, a verified checker, and erasure are separate developments | Treat reification, checking, and compilation as separate interfaces with separate correctness results |
| [HVM2][hvm2] and [HVM4][hvm4-core] | Interaction execution with distinct extensions and runtime interfaces | Add an interaction backend after the reference profile and its observable semantics are fixed |

The synthesis is an interpreter-first bootstrap with explicit staged
comparison, finite certificates, and immutable definition references.
It does not require a minimal binary seed, a universal content database,
or an optimized interaction runtime at the first milestone.

## Acceptance milestones

| Stage | Deliverable and dependencies | Executable acceptance condition |
| --- | --- | --- |
| 0. Profile boundary | Specify the value model, computation rules, foundational proof rules, and host services; reuse the existing semantic modules | Tiny constructor, evaluation, and proof examples run without the future Geb libraries |
| 1. Closed bundle | An arbitrary-label codec, versioned framing, export layouts, and validated structural references; depends on 0 | A bundle containing a definition and its client round-trips; invalid paths, trailing data, wrong profiles, and unsupported cycles are rejected |
| 2. Reference execution | In-memory evaluator, bounded driver, and explicit native primitives; depends on 0–1 | Tree map/fold, substitution, arithmetic beyond a machine word, and serialization run; bounded execution resumes to the same result |
| 3. Foundation checker | Raw certificate decoding, typed rule checking, substitution/side-condition checks, and a soundness theorem for the chosen logical presentation; depends on 0–1 | A theorem with hypotheses, a substitution, and an induction proof check; altered binders, invalid dependencies, and false conclusions fail |
| 4. Geb library and reader | Definitions of lists, trees, environments, folds, a readable syntax, and proof-building helpers in the executable subset; depends on 1–3 | The Geb reader regenerates the bootstrap bundle and the Geb serializer matches the seed codec byte for byte |
| 5. Immutable store | Canonical block digests, host BLAKE3, dependency manifests, and separate name/comment tables; depends on 1 and joins 4 before the library grows | A rename leaves identity unchanged; a changed dependency changes identity; retrieval validates contents and layout |
| 6. Geb checker | Reimplement the fixed checker in Geb; depends on 3–4 | Seed and Geb checkers agree on valid and malformed fixtures; prove implementation agreement, with the seed checking the relevant certificates |
| 7. Geb compiler | A Geb program compiling the supported subset to Lean plus the declared runtime; depends on 2–4 and 6 | Compiled and interpreted versions of reader, checker, and compiler transformations agree; generated host code compiles on the pinned toolchain |
| 8. Self-compilation | Run the stage-7 compiler on its own closed source bundle; depends on 5–7 | The staged artifacts reach the exact fixed point specified below; the host seed implementation is not invoked by the last build |
| 9. Migration and optimization | Move mathematical libraries, richer definitions, representations, and other backends into Geb; depends on 8 | Each migration preserves its stated semantics; each optimization has an equivalence argument and measurements on compiler workloads |

Stages 2 and 3 can develop independently after their common format and
profile dependencies. Hashing need not block closed-bundle execution.
The full presheaf/free-monad/cofree-comonad library need not precede the
definition loader: its existing finite presentations are enough. This
is an implementation dependency separation, not an abandonment of the
mathematical account of definitions.

The first nontrivial Geb programs should be the tree fold, the serializer,
the reference resolver, and a fragment of the certificate checker. These
exercise the data operations the compiler will repeatedly use. Measure
them on a growing compiler-source bundle before adding interning,
cached hashes, succinct pages, net parallelism, or additional backends.
If triage expansion dominates this workload, the direct recursor/native
primitive profile is justified before attempting self-compilation.

At each stage retain a runnable fixture, the source needed to regenerate
it, and the precise input/output contract. During the early stages the
fixtures are small bundles; at stage 8 the fixture is the compiler and
checker source closure itself. No acceptance condition relies on an
unimplemented optimizer or on importing the future categorical library.

## What self-compilation must establish

Fix compiler source closure `S`, target profile, compiler options,
dependency contents, and host build function `H`. Let `B` be either a
Lean-written seed compiler or the Geb compiler run by the seed
interpreter. Each compiler emits the same kind of target artifact.

```text
C1 = H(B(S))
C2 = H(C1(S))
C3 = H(C2(S))

compare target artifacts: C1(S) = C2(S)
compare executable artifacts: C2 = C3
```

The second comparison requires a reproducible host build as well as
deterministic Geb output. Pin target parameters, order maps explicitly,
and keep timestamps, random identifiers, and absolute build paths out of
identity-bearing output. Compare bytes, not just digests. If machine
code is not yet reproducible, report the fixed point of emitted Lean or
another canonical target artifact separately; do not report a binary
fixed point.

The first compiler can compile less efficiently than the resulting
compiler. Stabilization is an acceptance test, not a consequence of the
phrase self-hosting. Changes to `S`, compiler flags, or dependency
profiles start a new test. Lean's own staged build provides a concrete
precedent, including the distinction between a seed-produced library
format and one produced by the new compiler [in its bootstrap
documentation][lean-bootstrap].

A fixed point does not prove compilation correct, prove the logical
kernel sound, or remove the host runtime from the trusted execution
stack. Retain independent seed checks and semantic-preservation proofs.
The meaning of self-hosted here is that the Geb implementation is written
in and compiled by Geb; a native-code backend without Lean is a separate
deliverable.

## Computation-certificate prototype

[Bootstrap.lean](../Geb/Prototypes/Bootstrap.lean) folds rose-tree
certificates with labels `UInt8 × ℕ`. The natural-number payload holds
the rank of a serialized expression where a rule needs one.

| Tag | Payload | Children | Reconstructed conclusion |
| --- | --- | --- | --- |
| 0 | Ranked valid expression `a` | None | `a = a` |
| 1 | Ranked expression `a` with a successor | None | `a = step(a)` |
| 2 | Zero | Proof of `a = b` | `b = a` |
| 3 | Zero | Proofs of `a = b` and `b = c` | `a = c` |

All other forms are rejected. `check_sound` proves that acceptance
implies both endpoint bitstrings represent expressions related by the
equivalence closure of the existing contextual triage reduction. The
checker compares exact syntax when joining premises. It neither trusts
a supplied conclusion nor treats a digest as proof. The theorem depends
only on `propext` and `Quot.sound` among Lean axioms.

The [executable examples](../GebTests/Prototypes/Bootstrap.lean) compose
two reductions, reverse the result, and reject malformed or incompatible
certificates. They also exercise the existing rank bijection above the
machine-word range. Run them with:

```sh
lake build Geb.Prototypes.Bootstrap GebTests.Prototypes.Bootstrap
```

The prototype is deliberately a computation-equality fragment. It has no
logical binders, induction rule, general congruence constructor,
definition loader, or external certificate parser. Its chosen reduction
strategy gives no completeness theorem for contextual convertibility.
It uses bit lists and re-encodes expressions; no throughput or logspace
claim is made. A future codec must map external bytes into certificates
with the same checks. A future free-topos kernel must supply its own
foundational rule and soundness development before general proofs can
migrate.

[representation]: ../manual/GebManual/ValueRepresentation.lean
[old-idris]: https://github.com/rokopt/geb/blob/9c24f4727d3c6c34abece2174b04fd74e1ab37aa/geb-idris/src/LanguageDef/GebTopos.idr
[old-topos]: https://github.com/rokopt/geb/blob/9c24f4727d3c6c34abece2174b04fd74e1ab37aa/geb-lean/GebLean/FreeToposBT.lean
[old-nets]: https://github.com/rokopt/geb/blob/9c24f4727d3c6c34abece2174b04fd74e1ab37aa/geb-lean/GebLean/InteractionNets.lean
[old-execution]: https://github.com/rokopt/geb/blob/9c24f4727d3c6c34abece2174b04fd74e1ab37aa/geb-lean/GebLean/InteractionExecution.lean
[old-tree-programs]: https://github.com/rokopt/geb/blob/9c24f4727d3c6c34abece2174b04fd74e1ab37aa/geb-lean/GebLean/PLang/TreeCalcPrograms.lean
[old-compiler]: https://github.com/rokopt/geb/blob/9c24f4727d3c6c34abece2174b04fd74e1ab37aa/geb-lean/GebLean/LawvereERKSim/Compiler.lean
[blake3]: https://github.com/BLAKE3-team/BLAKE3
[unison-hashes]: https://www.unison-lang.org/docs/language-reference/hashes/
[unison-idea]: https://www.unison-lang.org/docs/the-big-idea/
[free-topos]: https://www.site.uottawa.ca/~phil/papers/LS11.final.pdf
[hvm2]: https://github.com/HigherOrderCO/HVM2
[hvm4]: https://github.com/HigherOrderCO/HVM4
[hvm4-core]: https://github.com/HigherOrderCO/HVM4/blob/main/docs/hvm/core.md
[ribbit]: https://github.com/udem-dlteam/ribbit
[ribbit-paper]: https://arxiv.org/abs/2310.13589
[mes]: https://www.gnu.org/software/mes/
[gforth]: https://www.complang.tuwien.ac.at/forth/gforth/Docs-html/Cross-Compiler.html
[nock]: https://docs.urbit.org/nock/specification
[tree-start]: https://treecalcul.us/quick-start/
[hagino]: https://www.lfcs.inf.ed.ac.uk/reports/87/ECS-LFCS-87-38/
[charity]: https://doi.org/10.1016/0304-3975(94)00099-5
[lean-bootstrap]: https://github.com/leanprover/lean4/blob/master/doc/dev/bootstrap.md
[idris-bootstrap]: https://idris2.readthedocs.io/en/stable/tutorial/starting.html
[cakeml]: https://cakeml.org/
[candle]: https://github.com/CakeML/candle
[metarocq]: https://github.com/MetaRocq/metarocq
