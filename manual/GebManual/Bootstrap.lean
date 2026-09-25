/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import VersoManual
public import GebManual.Bibliography
import Geb.Prototypes.Bootstrap
import Geb.Prototypes.Kernel
import Geb.Prototypes.Metalogic
import Geb.Prototypes.Definition
import Geb.Prototypes.FreeTopos
import Geb.Prototypes.Computability.Triage.Simulation

/-! # Bootstrap chapter

The design record for bootstrapping Geb: the decisions that fix the
seed, a survey of how other languages and proof checkers bootstrap,
the staged plan with an executable acceptance condition for each
step, and the statement of what self-compilation establishes.
-/

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Bootstrapping Geb" =>

The aim is an implementation of Geb written in Geb and compiled by
Geb, with a small, fixed seed in host languages: Lean first, and a
systems language after it. The seed consists of the representation of
values, a kernel language with its type checker and evaluator, a
loader for a canonical serialized form, and byte input and output.
Everything else, the reader, the elaborator, the compiler, the
libraries and eventually the proof checker, is Geb code, which the
seed runs until the compiler written in Geb reproduces itself.

This chapter records a road map of the bootstrap and of the work
written in Geb after it, the decisions that fix the seed, a survey of
how other languages and proof checkers bootstrap, and the plan, a
sequence of phases each ending with an executable acceptance condition.
The
optimized representation that the chapter on value representation
designs is not a prerequisite: the seed uses the plain representation,
and the optimized one is written later in Geb. Nothing in this chapter
asserts that a component exists unless it names the Lean declaration or
file that implements it.

# Road map

The bootstrap ends when a developer can write the rest of Geb in Geb:
when the logic, the computation and the first compilers and hosts
exist, and the language suffices to write the rest of Geb's programs
and proofs in it. Most of what the repository formalizes in Lean is then
written in Geb and is not part of the bootstrap. The road map therefore
has two parts: the bootstrap, whose end point is stated first, and the
work written in Geb after it.

Each item is marked constructed, begun, not begun or deferred, and
names the section or file that details it. The items of a list are in
the order of dependence.

## The bootstrap's end point

* Computation. Geb's implementation, the reader, the expansion, the
  type checker and the compilers, is written in Geb and compiled by Geb,
  with the host code reduced to the seed, and every compiler reproduces
  itself (the section on what self-compilation establishes). Reached on
  the Lean host.
* Hosts and targets. The kernel runs on three hosts or targets: Lean,
  where the seed and the backend emitting Lean are; a systems language,
  Rust, where a second seed reproduces the fixed points; and an
  interaction-net runtime, HVM, Bend or a similar one, which a compiler
  written in Geb targets for parallel workloads. Lean reached; the
  others not begun.
* Logic. Two checkers, each proved sound in Lean and written again in
  Geb, where a prover has tactics that construct its certificates: the
  computational core's, of equations between kernel terms, and the
  metalogic's, the free topos with the natural numbers, list and
  rose-tree objects, presented as the initial model of one partial Horn
  theory (Phase 7). Begun: the computational core's checker is
  constructed and its proof construction is begun; the metalogic's
  constructions are not begun.
* Extension. A program is extended by definitions whose identity
  survives edits, and Surface 1 is complete enough to write the rest of
  Geb in, with diagnostics that name what fails. Begun: closed bundles
  and Surface 1 are constructed.

## The bootstrap

Computation:

* The seed, Phase 1: the kernel's syntax, its type checker and
  evaluator, the primitives and the reader, with numeral abbreviations
  for labels. Constructed, except the reader's printer and the
  retraction law between them, not begun.
* Definitions and images, Phase 3: closed bundles, the image format and
  the host driver `geb-kernel`. Constructed; the names of bound
  variables and comments beside a bundle, not begun.
* Geb grows in itself, Phase 4: the stage-0 compiler in the kernel's
  syntax, the Surface 1 expansion, the stage-1 compiler written in
  Surface 1, and their fixed points. Constructed.
* The Lean backend, Phase 5 step 3: `bootstrap/stage1/lean.geb`, the
  committed `bootstrap/compiler.img` and `bootstrap/lean/GebBoot.lean`,
  and the executable `geb-compile`. Constructed.
* Surface 1's completion, the section on improvements: generated
  recognizers, type parameters, a static check of datatypes, patterns
  with `&`, unused pattern variables, primitives that no binding
  shadows, emitted names that no definition captures, and diagnostics
  naming the definition that fails. Not begun.
* The choice of machine, Phase 2: the benchmark programs, the
  environment machine, the compilation to the triage calculus, the
  compilation to interaction combinators, and the decision. Deferred
  until before the second host.
* The second host, Phase 5 step 1: the evaluator and loader in Rust,
  reproducing the stage-0 and stage-1 fixed points, which is diverse
  double-compiling across hosts. Not begun.
* Accelerations, Phase 5 step 2: native code bound by position or
  builtin identifier, proved in Lean against the denotation and run in
  shadow mode. Not begun.
* The interaction-net target, Phase 5 step 3: a compiler written in
  Geb to HVM, Bend or a similar runtime, each pinned to a revision and
  tested, within the limits on duplicating λ-values of the section on
  operational semantics. Not begun.
* The Geb reader and serializer in constant depth, and the stage tests
  run by the compiled executables, the section on improvements. Not
  begun.

Logic, Phase 7, the computational core and then the metalogic, as the
sections below detail:

* The computational core, a cartesian closed locos: the rules and their
  soundness in Lean, and the checker written in Geb, constructed; the
  proof construction, begun; proofs about the compiler's components,
  which exercise the prover, begun, and paused until the fifth choice;
  stronger checkers admitted by translations of certificates, not begun.
* The metalogic, the free topos in one presentation: the rule set with
  its checker in Lean, sound, and the proof that every model is an
  elementary topos with the data objects, constructed; the converse, not
  begun; the model in Lean with functional relations, the definitional
  extension with its unfolding theorem, not begun; a prover prototyped
  in Lean, constructed, and with it the measurement that decides when
  the Mitchell–Bénabou language is written, made, both criteria
  failing; the checker and prover written in Geb, not begun.

Extension:

* Closed bundles referring to definitions by position, Phase 3.
  Constructed.
* Content identity, Phase 6: the hash and its version tag, BLAKE3 and
  SHA3-256 reconciled; its input, recorded in `docs/definitions.md`
  § Content identity; the hash written in Geb and compared with a host
  binding; the migration from positions to digests, the namespace tree
  and the re-keying of annotations. Not begun.
* A printer for the kernel's readable syntax and the retraction law,
  and the unification of the readable S-expressions with the canonical
  ones, with a quoted spelling for atoms that are not tokens (`TODO.md`
  § Bootstrap). Not begun.

## After the bootstrap

Written in Geb, each proof in the computational core when it is an
equation between kernel terms, and in the metalogic otherwise:

* Surface 2: quotients whose respect is proved, subset types by
  propositions, definitions by equations whose unique solution is
  proved, and dependent products of families, each a construction of
  the metalogic's topos.
* The richer forms of definition of `docs/definitions.md`: well-founded
  and guarded blocks, presentations, presheaf signatures, a binding
  language with its substitution laws, and modules. Their Lean
  prototypes under `Geb/Prototypes/Definition/` are constructed.
* The mathematics the repository formalizes in Lean: polynomial
  functors and their W-types and M-types, the presheaf parametric right
  adjoints and their inductive-recursive codes, the quotient polynomial
  functors of the chapter on them, the decision problems, and the
  constructive fragment of the Lean and Idris developments that the
  libraries consume.
* The optimized representation of the chapter on value representation,
  after its decision gates, and the further concrete syntaxes of
  `docs/concrete-syntaxes.md` § Roadmap.
* Theorems about the metalogic proved in it: the soundness of the
  computational core's checker, and the equivalence of the free topos
  with the rose-tree object and the free topos with a natural numbers
  object; and the extraction of programs from proofs of totality,
  through a realizability topos.
* A backend without Lean, a milestone separate from the bootstrap (the
  section on what self-compilation establishes).

# Decisions

The following are fixed; the plan builds on them.

* Proofs. During the bootstrap, correctness proofs are Lean proofs:
  the kernel's evaluator is proved to agree with the kernel's
  denotation, and every codec with its decoder. The proof checker for
  the metalogic is a Geb program written after Geb compiles itself,
  and its soundness proof stays in Lean.
* Kernel. The kernel language is Gödel's System T
  {citep Goedel1958}[] over rose trees: simple types built from the
  single base type of rose trees by products, function types and lists,
  the constructors and destructors of rose trees, and a fold whose
  result may be of any type. Every program terminates, and its denotation is
  a Lean function. The functions it defines are those of System T over
  the natural numbers, the recursive functions provably total in Peano
  arithmetic (Section 7.4.2 of {citet GirardLafontTaylor1989}[]),
  since a rose tree is coded by a natural number. The resource target
  of the bitstring-metalogic design, polynomial time and linear space,
  and the logarithmic-space recognizers of the value-representation
  chapter are theorems about particular programs, witnessed by the
  function algebras the repository formalizes, not restrictions of
  the kernel.
* Stage 0. The first Geb code is written directly in the kernel,
  spelled as readable S-expressions. There is no compiler written in a
  host language: Geb grows by elaborators written in Geb.
* Semantics. The reference semantics of the kernel is its denotation.
  Which machine runs it, an environment machine, a compilation to tree
  calculus, or a compilation to interaction combinators, is decided by
  the comparison of Phase 2, run on the same kernel programs.
* Layers. Above the kernel, the language grows in three layers. Surface
  1 is computational: named datatypes whose constructors and structural
  recursion are derived from their declarations, case analysis,
  functions with result types, type parameters instantiated at
  elaboration, and quotients only by computable normal forms. Its types
  denote objects of the category of recognized types over the functions
  the kernel defines, which has finite limits and finite coproducts;
  that category has no subobject classifier for propositions about
  programs (the necessity theorem of `Geb/Prototypes/Typechecker/`'s
  classifier module), so logic is not a Surface 1 construct. The
  metalogic of Phase 7 holds propositions and their proofs about kernel
  programs, and the computational core the equations between them.
  Surface 2, built on both, adds subset types by arbitrary
  propositions, quotients whose respect for their relation is proved,
  and definitions by equations whose unique solution is proved; it is
  the setoid completion of Surface 1 with its obligations discharged in
  the metalogic. Type parameters are instantiated at elaboration
  because the polymorphic λ-calculus has no set-theoretic model, which
  the kernel's denotation in Lean types requires.
* Concrete syntax. Geb specifies its abstract syntax, rose trees, and
  not a concrete syntax. Until Geb can express arbitrary concrete
  syntaxes itself, the default is readable S-expressions, the readable
  form of the canonical S-expressions of {citet RFC9804}[], whose data
  model the reader's S-expressions share.
* Metalogic. The metalogic is the free topos with the inductive types
  the bootstrap uses, natural numbers and rose trees, and its
  equivalence with the free topos with a natural numbers object is
  proved in Geb. It is presented at once, as the initial model of one
  partial Horn theory of an elementary topos with the data objects
  (Phase 7, the section on the metalogic), and no classical logic is an
  intermediate step. Beneath it, the computational core is the
  equational logic of the kernel's terms of every type, a cartesian
  closed category with the data objects, since the kernel's programs
  have function types.
* Artifacts. The compiler's image and, once the compiler emits Lean,
  the emitted Lean are committed as build artifacts. Continuous
  integration regenerates them and compares their bytes with the
  committed ones, so a change that leaves the compiler's source
  unchanged, of the seed, the host or the toolchain, leaves them
  unchanged.

## The seed boundary

The first host supplies Lean's compiler and runtime, allocation and
reclamation, arithmetic on natural numbers, and byte input and output
on files. A pinned toolchain and a small runtime are compatible with
self-hosting: once the compiler emits Lean, it compiles its own source
to Lean, which Lean's compiler continues to compile.

:::table +header
*
  * Component
  * Supplied by the seed
  * Written later in Geb
*
  * Values
  * Rose trees with natural-number labels, allocation
  * Representation selection and its optimizations
*
  * Execution
  * Kernel type checker and evaluator
  * Compilers and evaluators with the same observable behaviour
*
  * Definitions
  * Closed bundles and the validation of their references
  * Signatures, equation blocks, presheaf definitions, modules
*
  * Storage
  * The canonical codec, files, and later a hash binding
  * Reader, printer, dependency tools, content store
*
  * Logic
  * Soundness of the proof checker, in Lean
  * The proof checker, derived rules, proof construction
:::

The logical trust boundary is the kernel's rules together with the
Lean proofs about them. The execution boundary also includes Lean's
compiler and runtime: compiling a checker from a sound Lean definition
does not verify the machine code that runs it.

## Values and labels

The carrier is {name}`Geb.RoseTree` at natural-number labels. A label
is read as a bitstring through the rank and unrank bijection of the
value-representation chapter, which preserves empty bitstrings and
leading zeros; reading a label as an ordinary binary numeral would
lose them. Every other inductive type is presented as a set of rose
trees recognized by a kernel program.

Machine words are a representation, not a restriction on labels. In
Lean a natural number is a machine word when it fits and a
multiple-precision number otherwise, so the seed needs nothing beyond
`Nat`. A format with fixed-width tags reserves one tag value as an
escape to an arbitrary natural number; it is canonical only if the
escape is used exactly when the value does not fit, which in a byte
profile means that the escaped value is at least the reserved tag.
The escape applies to the labels of internal nodes as well as leaves.
Constructor meanings and arities belong to a versioned signature, not
to the untyped carrier; a signature of fixed arities presents
arbitrary branching through a list, spine or block encoding with a
proved conversion, never by restricting values. The list-based
constructor of {name}`Geb.RoseTree` does not give constant-time access
to a child, so wide nodes tabulate their children in an array. Long
labels need linear-time access to their words for scanning and
hashing, which a natural number does not expose; that is a reason to
change the physical representation when such workloads appear, not a
prerequisite of the bootstrap.

## Definitions, references and identity

A definition block follows the construction of
`Geb/Prototypes/Definition/`: terms of the free monad of the kernel's
signature, linked by Kleisli composition, and interpreted by
{name}`Geb.Definition.eval`. A block consists of a profile, its
imports, the layout of its exports, and its bodies; a reference is the
identity of a block together with a validated direction to one of its
exports; a body is a term over the profile's signature with explicit
slots for imports and parameters. At the bootstrap every block is well
founded: a body refers to imports and to exports earlier in the
block's order. Recursion is the kernel's fold, not self-reference, so
no guarded or cyclic blocks are needed before Geb compiles itself; a
loader rejects unresolved references, directions out of range,
mismatched interfaces and cycles.

The first executable environment is a closed bundle: a manifest of
definitions in dependency order, each referring to earlier ones by
their position in the bundle, a vertex in the sense of
`Geb/Prototypes/Definition/Vertex.lean`. A position identifies a
definition only within one frozen bundle, since an edit that inserts a
definition shifts its successors. Identity across edits is the digest
of a definition's canonical serialization. Three conventions are fixed
before the first image, because every digest will depend on them.

* One node kind carries every reference that leaves a definition. Its
  payload is a position before digests are introduced, a digest after,
  or the identifier of a builtin. The migration from positions to
  digests then rewrites that node kind alone, and the vertices inside
  each definition do not move, so annotations keyed by them survive
  it. References within a definition remain relative.
* Builtin identifiers are only ever added. A digest that mentions a
  builtin includes its identifier, so renaming one would change every
  such digest; Unison's [documentation on adding
  builtins](https://github.com/unisonweb/unison/blob/trunk/docs/adding-builtins.markdown)
  records the same constraint.
* A block with several members is hashed in its written order, and a
  member is referred to by the block's digest and a direction. An
  identity invariant under reordering the members would require a
  canonical order on cyclic graphs; Unison's hashing of mutually
  recursive definitions has an open defect of exactly this kind
  ([issue 2787](https://github.com/unisonweb/unison/issues/2787)).

The migration from positions to digests is a fold over the dependency
order, the shape of Git's
[conversion of a repository from SHA-1 to SHA-256](https://git-scm.com/docs/hash-function-transition),
and it is safe because nothing without a digest has an identity to
preserve. It fails on a missing dependency rather than substituting a
placeholder, recomputes each digest before rewriting, and gives the
same result when run twice. Names, comments and per-node digests are
annotations kept in one table per bundle, keyed by vertex, never
inside a hashed object; at the migration a key splits into the digest
of the enclosing definition and a vertex inside it. The
value-representation chapter selects BLAKE3
{citep OConnorAumassonNevesWilcoxOHearn2020}[] and the repository's
survey of concrete syntaxes names SHA3-256; the two are reconciled
before the first digest. A digest locates a payload and never creates
an equality: the checker compares validated contents exactly.

## Input and output

Kernel programs are pure. The host driver alone reads and writes
files, presenting each input file as a tree of byte labels and writing
each output tree back as bytes. The compiler is then a function from
input trees to output trees, and the host services are a fixed, small
set, to which primitives are added and never renamed. Running a
program with a step bound returns a value, an error, or a resumable
state; exhausting the bound is neither falsity nor divergence.

# Survey

The survey covers four questions: how other systems keep a seed and
check a fixed point, how small kernels grow in themselves, which
operational semantics the kernel should run on, and how small a proof
checker for the metalogic can be. A fifth part maps the prior art in
this repository and the experimental one.

## Seed images and fixed points

The bootstraps that remain maintainable keep a small interpreter in
the host and the compiler as an image the interpreter runs. OCaml
checks in the bytecode of its compiler under `boot/`, and its
`make bootstrap` target recompiles the compiler until it reports
["Fixpoint reached, bootstrap succeeded."](https://github.com/ocaml/ocaml/blob/trunk/Makefile).
Zig replaced its compiler written in C++ by a WebAssembly build of the
compiler and a translator from WebAssembly to C
([announcement](https://ziglang.org/news/goodbye-cpp/)). GCC compares
the object files of its second and third stages
([build documentation](https://gcc.gnu.org/install/build.html)), and
Lean's staged build states that the third stage "should always be
identical to stage 2" ([bootstrap
documentation](https://github.com/leanprover/lean4/blob/master/doc/dev/bootstrap.md)).
Urbit boots from a serialized noun, a pill, which "is a recipe for a
complete bootstrap sequence, starting with a bootstrap Hoon compiler as
a Nock formula" ([Core Academy, lesson
4](https://docs.urbit.org/build-on-urbit/core-academy/ca04)).

Two failures recur. A self-hosted system comes to need itself to be
built, and "once a system has been bootstrapped, features are often
re-implemented in terms of themselves, and the original, non-circular
code is deleted" {citep KelseyRees1994}[]. And an image that evolves
by self-modification loses the source from which it could be rebuilt,
as the Smalltalk images descended from Squeak did. The first is
addressed here by keeping the hand-written kernel sources and the
Lean evaluator as a permanent, independent route to the compiler's
image; comparing the image produced by that route with the image the
compiler produces from itself is diverse double-compiling
{citep Wheeler2005}[], the answer to {citet Thompson1984}[]. The
second is addressed by treating every image as a build artifact whose
source is committed.

Format changes are what force a bootstrap to be rerun: OCaml rebuilds
its seed when the bytecode format or the set of primitives changes,
and Lean when its object-file format changes. The image is therefore
a kernel term, not the state of a particular machine, so that the
choice of Phase 2 cannot invalidate it; it carries a version header,
and it shares no subtrees, compression being a separate outer layer.
Ribbit's compiler likewise emits trees without sharing, which keeps
its decoder small {citep YvonFeeley2021}[].

## Kernels grown in themselves

Ribbit's virtual machine is "roughly 150 lines of portable code", its
every heap object a rib of three fields, and one Scheme compiler
serves many host languages {citep YvonFeeley2021}[]. Squeak's virtual
machine is written in a subset of Smalltalk that excludes blocks,
message sending and objects, translated to C, and it also runs inside
Smalltalk as a simulator "roughly 450 times slower than the C version"
{citep IngallsKaehlerMaloneyWallaceKay1997}[]. Scheme 48's virtual
machine is written in Pre-Scheme, a statically typed subset of Scheme
compiled to C {citep KelseyRees1994}[]. These are the pattern for the
later reduction of the seed: the evaluator is written in a subset of
Geb and translated to the host.

Native accelerations of interpreted code need a binding and a check.
Urbit's jets bind native code to Nock code through labels registered
at run time, and its runtime can run both and compare them, reporting
a mismatch ([`jets.c`](https://github.com/urbit/vere/blob/develop/pkg/noun/jets.c));
its documentation describes jet hashes as "not as of this writing
actively used" ([jetting
guide](https://docs.urbit.org/build-on-urbit/runtime/jetting)). A
digest key goes stale with every edit of the accelerated code, so
during the bootstrap an acceleration is bound by position or builtin
identifier, proved in Lean to agree with the denotation of the term it
replaces, and run in a shadow mode that compares both; a digest key is
adopted once the accelerated code is frozen.

Categorical programming languages attach the recursion operations to
datatype declarations: {citet Hagino1987}[] defines datatypes by their
universal properties, and Charity's term logic exposes the folds and
unfolds they provide {citep CockettSpencer1995}[]. Geb's signature
declarations do the same, deriving the constructors, the recognizer
and the fold of a declared signature over the carrier.

Other systems separate the concerns this plan separates.
[GNU Mes](https://www.gnu.org/software/mes/) pairs a Scheme interpreter
written in C with a C compiler written in Scheme, so an interpreter
suffices to start running a compiler written in the new language.
[Idris 2](https://idris2.readthedocs.io/en/stable/tutorial/starting.html)
is written largely in Idris and bootstraps through a Scheme backend
that remains, as Lean may remain Geb's first backend.
[MetaRocq](https://github.com/MetaRocq/metarocq) develops the syntax,
metatheory, verified checker and erasure of Rocq as separate
components with separate correctness results, and
[Candle](https://github.com/CakeML/candle) is an implementation of HOL
Light with an end-to-end soundness theorem, whose classical logic Geb
does not adopt. The [tree-calculus
workflow](https://treecalcul.us/quick-start/) loads a compiler
represented as a tree and reads a lightweight notation, the workflow
Phase 2's triage arm needs.

## Operational semantics

Three candidates run the kernel, and Phase 2 compares them on the same
programs.

Environment machines. The Categorical Abstract Machine executes
categorical combinators, morphisms of a free cartesian closed
category, and was the first implementation of CAML
{citep CousineauCurienMauny1987}[]. The smallest machine with a
mechanized correctness proof has five instructions, `Var`, `Const`,
`Clos`, `App` and `Ret`, with a compilation scheme proved correct in
Coq for terminating and diverging evaluations alike (Section 9.2 of
{citet LeroyGrall2009}[]). A machine is derived from an evaluator by
closure conversion, transformation to continuation-passing style and
defunctionalization {citep AgerBiernackiDanvyMidtgaard2003}[], and a
datatype-generic, tail-recursive machine "guaranteed to produce the
same result as the fold" is verified in Agda
{citep TomeCortinasSwierstra2018}[], its frames being McBride's
dissections of the polynomial {citep McBride2008}[]. The kernel's
fold is a fold over a polynomial, so that construction applies
directly.

Tree calculus. The triage calculus has five reduction rules
{citep Jay2024CalculusCalculi}[], and the repository implements it
with an in-memory machine proved to agree with its reduction step
({name}`Geb.Triage.Machine.execute_eq_step`). Its carrier is the
unlabelled binary tree and its numerals are unary, so the kernel's
natural-number labels need either an encoding into trees or a native
acceleration for every arithmetic operation, and hand-written programs
need bracket abstraction, which is a compiler, before stage 0 can be
written in it.

Interaction combinators. Three symbols and six rules suffice to encode
any interaction system {citep Lafont1997}[], and their parallelism is
the reason to consider them. Evaluating λ-terms by optimal reduction
needs Lamping's bookkeeping, the oracle {citep Lamping1990}[]
{citep AspertiGuerrini1998}[]; without it, the abstract algorithm is
sound and complete for terms typable in elementary or light affine
logic {citep BaillotCoppolaDalLago2011}[]. Elementary linear logic
captures the elementary functions {citep DanosJoinet2003}[], and System
T defines functions that are not elementary, so the kernel does not
lie inside the certified fragment: duplication of λ-values needs a
per-program certificate, a copying discipline without optimal sharing,
or the oracle's cost. Duplication of first-order data is not
restricted. The value-representation chapter records the state of the
interaction-net runtimes and their measurements. As a compilation
target, a net runtime needs its own contract: well-formedness of
graphs, interfaces, reduction, read-back, and preservation of the
source's observations. A tree can serialize a graph by storing node
and port references, and sharing, erasure and duplication in a net are
operational structure, distinct from the sharing of immutable pointers
in a rose-tree runtime. [HVM2](https://github.com/HigherOrderCO/HVM2)
and [HVM4](https://github.com/HigherOrderCO/HVM4) implement different
calculi with different interfaces, so each is a separate target, pinned
to a revision and tested before any step depends on it.

The evidence points to an environment machine as the reference and to
interaction combinators as a compilation target for measured parallel
workloads; Phase 2 decides.

## The metalogic and its checker

The free topos is the topos generated by pure intuitionistic type
theory, whose types include a natural numbers type and power types
and whose only primitive predicate is equality; its entailment
relation is indexed by a set of variables, which makes empty types
sound (Sections 1 and 4 of {citet LambekScott1980}[]). Every topos with
a natural numbers object has W-types {citep MoerdijkPalmgren2000}[], so
the free topos with the rose-tree object differs from the free topos
with a natural numbers object in what is primitive. That the two are
equivalent is to be proved in Geb; a bijection between trees and natural
numbers in sets does not prove it. The equivalence is a statement about
the syntax of two presentations: translations of their objects and
morphisms in each direction, and derivable isomorphisms between each
object and its translation back. Its proof is an induction on terms and
derivations.

The metalogic presents the free topos with the data objects directly, as
the initial model of a partial Horn theory (Phase 7, the section on the
metalogic). Beneath it, the computational core is the equational logic
of the kernel's terms: its judgments are equations between kernel terms
of a type under hypotheses, the logic of a locos as
{citet Maietti2010}[] defines it with exponentials added, since the
kernel's programs are terms of System T, whose types include function
types. The kernel's types, function types included, are objects of the
metalogic, and Surface 1's recognized types are subobjects of the type
of trees there, cut out by their recognizers.

The functor from the free cartesian closed category of the kernel's
terms to the free topos that preserves its structure sends each
equation the computational core proves to one the metalogic proves, so
a proof checked in the core remains valid in the metalogic. The functor
need not be full or faithful: the free topos has arrows between natural
numbers that no System T term defines (below), and it may prove
equations between programs that the core does not. A proof therefore
moves from the core to the metalogic by a translation of its
certificate, through the translation of λ-terms into the combinators,
and back only by being checked again. Within the core, a certificate
cites an axiom by its index in the table of axioms and a theorem by its
index among the theorems, by two rules, so that the axioms added later
leave every citation unchanged. A cited theorem need only be valid, so a
proof in the core may cite an equation between kernel terms that the
metalogic proves.

Relative soundness takes two forms. One checker is admitted beside
another of the same judgments when a Geb program translates each
certificate the first accepts into one the second accepts with the same
conclusion. That is an equation between kernel programs under the
hypothesis that the first checker accepts, and it is proved in the
computational core by induction on certificates; the checkers' results
are functions of the context and the hypotheses, so the equation is
stated at function types and its induction hypothesis covers the
contexts and hypotheses of the premises. That a checker is sound, every
certificate it accepts valid, is a statement about the denotation of
kernel terms, which no kernel term computes (below); it is stated in
the metalogic, whose topos has System T's evaluator. The computational
core cannot prove its own checker sound, since the core's consistency is
an equation between kernel terms that the core does not prove.

Each checker's rule set states typing, substitution, extensionality and
induction explicitly; the equalities of computation supply none of
them. Proof terms are explicit and finite, and a checker is not
required to decide equality of morphisms, to normalize programs, or to
search for proofs that a relation is functional. Propositions are not
executable Booleans in general. Three properties of the metalogic fix
its checker's rules:

* Sequents are indexed by their free variables, as Lambek and Scott's
  are, so that empty types are sound.
* There is no choice operator, since in a topos choice implies excluded
  middle {citep Diaconescu1975}[]. A topos has unique choice, so a
  functional relation is a morphism; descriptions are admitted only
  with a proof of unique existence.
* A subtype is a subobject: its inclusion is a monomorphism with no
  total map back from the base type. A retraction onto every inhabited
  subtype would decide every proposition $`p`: the subtype
  $`\{x : 2 \mid x = 1 \lor p\}` of $`2` is inhabited by $`1`, the
  retraction's value at $`0` is $`0` exactly when $`p` holds, and
  equality on $`2` is decidable.

Each checker is a fold over proof objects that computes each conclusion
from the premises' conclusions, trusting no stated conclusion;
{name}`Geb.Bootstrap.infer` is that pattern for a fragment of
computation equalities. Its soundness is proved in Lean by interpreting
types as Lean types, without `Classical.choice`, and the metalogic's,
where disjunction appears, is tested as well in a model that is not
Boolean, where a classical rule would fail.

Programs are weaker than the metalogic. The free topos has arrows
between natural numbers that no System T term defines, System T's own
normalizer among them, and not every recursive function is
representable in it (Proposition 3.7 of {citet LambekScott1980}[]). A
Geb program that evaluates kernel terms therefore takes a step bound,
and the host evaluator is the only total one; self-compilation is a
transformation of finite syntax and needs no total internal
evaluator. Extracting programs from proofs of totality is a later
concern, through a realizability topos over a combinatory algebra of
programs {citep Hyland1982}[].

Other checkers bound the size of this one. Milawa admits a sequence of
increasingly capable proof checkers, each after the previous one
verifies it, and is proved sound down to the machine code that runs it
{citep DavisMyreen2015}[]. Metamath Zero trusts a verifier and a
specification file, and takes proofs as untrusted input
{citep Carneiro2019}[]. CakeML bootstraps a verified compiler inside
the logic of HOL {citep KumarMyreenNorrishOwens2014}[]. After
self-hosting, Geb admits stronger checkers as Milawa does; no checker
proves itself sound, which would prove its own consistency, so the
metalogic's soundness proof stays in Lean.

Two kinds of extension differ. A derived definition, a derived rule or
a proof-producing tactic can be written in Geb and produce evidence
the existing checker accepts. A new foundational principle needs a
conservative interpretation into the checker's theory or an explicit
change of the theory: defining a data type of purported proofs does
not make them sound. The metalogic's rule set is therefore fixed before
mathematical proofs are migrated to it, and a migration from Lean checks
the logical strength and the universes it relies on, since a fixed
elementary-topos presentation does not internalize all of Lean's
universe-polymorphic mathematics.

## Prior art in the repositories

The value model, its serialization and the definitions exist.
{name}`Geb.RoseTree` is the W-type of rose trees with its fold
{name}`Geb.RoseTree.elim`; `Geb/Prototypes/RoseTree/Spine.lean` proves
the serialization injective with a characterized recognizer; the
word-level codec of `Geb/Prototypes/RoseTree/Packed.lean` is tested
against it, not proved. {name}`Geb.Definition.encode` writes a term of
the free monad of a signature as a rose tree, injectively. The concrete
syntaxes of `Geb/Prototypes/ReadableSExpr.lean` and
`Geb/Prototypes/CanonicalSExpr.lean` are proved to round-trip, over
labels bounded by a fixed number rather than arbitrary natural numbers.

The experimental repository, in its `geb-lean/` and `geb-idris/`
subdirectories at revision `9c24f4727d3c6c34abece2174b04fd74e1ab37aa`,
uses binary trees throughout and self-referential inductive types
rather than W-types, so its modules are design references or
candidates for porting, not seed components.

* `LawvereGodelT` and its companions state a System T over natural
  numbers and binary trees with typed combinators and one-step
  reduction; the kernel's types and rules port from them.
* `Ramified/Soundness/` contains a simply typed λ-calculus with
  constructors, destructors and case over word algebras, with an
  evaluator proved sound: the closest existing model of the kernel's
  type checker and evaluator.
* `Binding/` implements de Bruijn terms as a free monad with renaming
  and substitution laws.
* `LawvereBTEq.lean` represents equality proofs as trees whose
  endpoints are computed from the proof, the format of the checker's
  proof objects.
* `FreeToposBT.lean` presents a free topos with a binary-tree object
  by combinators. Its equations do not force its subobject classifier
  to classify, since interpreting that object as the terminal object
  satisfies them, and its equalizers are restricted to base arrows; it
  is superseded by the partial Horn presentation of Phase 7.
* `InteractionNets.lean` evaluates Lafont's combinators with maximal
  parallel steps and no proofs; it is the starting point of the
  interaction arm of Phase 2, after a well-formedness invariant for its
  graphs is stated. `InteractionExecution.lean` separates its
  polynomial machines and polling constructions from a translation of
  net graphs, and does not discharge that translation.
* `PLang/TreeCalcPrograms.lean` implements bracket abstraction by a
  fold over values, and `LawvereERKSim/Compiler.lean` translates
  elementary-recursive terms to register-machine programs; both are
  components to examine when writing the corresponding passes.
* In `geb-idris/`, `GebTopos.idr` contains finite constructor
  encodings, indexed expression signatures, their folds and checking
  algebras, specifications to port by use case.
* In `geb-idris/`, `Nock.idr` departs from the Nock specification in
  several rules and is not ported; `TreeCalculus.idr` relates
  natural binary trees to unlabelled rose trees.

The original Common Lisp implementation of Geb translated a simply
typed λ-calculus into categorical morphisms, the translation that a
later Geb compiler to categorical combinators repeats.

# The plan

Each step is marked by where it lives: the Lean seed, Geb code, or a
comparison whose output is a decision. Each phase ends with an
executable acceptance condition, and every step retains a runnable
fixture, the source that regenerates it, and its input and output
contract.

## Status

The fixed points hold on images and on Lean. The seed builds the
stage-0 compiler, written in the kernel's syntax, and the stage-0
compiler builds the stage-1 compiler, whose Surface 1 expansion is
written in Surface 1 and which also emits Lean; each, run by the Lean
evaluator from its image, compiles its own source to that image. Built
by Lake from the Lean it emits from its own source, the stage-1
compiler emits the same Lean and the same image. The stage-1 compiler's
image and its Lean are committed, and continuous integration checks
every fixed point on every build. The road map at the head of the
chapter marks the state of every item.

The implementation changed the plan in these respects. The kernel's
terms and types are rose trees read directly, and its checker and
evaluator are one fold whose results are Lean closures, so no machine
is needed before the first fixed point and Phase 2 left the critical
path. The kernel gained lists, case analysis of lists and the
logarithm of a label, each for a cost measured on the bootstrap's own
programs. And the representation of rose trees tabulates a node's
children in an array, without which a fold over a wide node, such as a
file, takes quadratic time.

## Phase 1: the kernel runs in Lean

1. Lean: the kernel's syntax. Terms and types are rose trees read
   directly, the label of a node naming its constructor, so a program
   is a value of the language and needs no separate syntax type: de
   Bruijn variables, abstraction over a domain type, application, the
   unit value, pairs and projections, quoted trees, a conditional on
   whether a label is non-zero, lists with their right fold
   ({name}`Geb.Kernel.foldrDen`) and their case analysis
   ({name}`Geb.Kernel.lcaseDen`), which the fold alone gives only in
   time linear in the list, the fold of trees and iteration at
   given result types, primitives and references by index; the types
   `T`, `1`, products, functions and lists. A tree is a label with a
   list of trees, and the fold's step receives the leaf of a node's
   label and the list of its children's results
   ({name}`Geb.Kernel.foldDen`), so the fold is the recursion of the
   carrier itself. Lists are in the kernel because a node is built from
   the list of its children: building a node one child at a time copies
   the children at each step, which on a node of many children, a file
   of bytes among them, takes quadratic time, while a list of children
   is built in linear time and tabulated once.
2. Lean: the type checker and the evaluator are one paramorphism,
   {name}`Geb.Kernel.infer`, returning a term's type together with its
   denotation, or nothing when the term is ill-typed: `T` denotes
   {name}`Geb.RoseTree`, the fold denotes {name}`Geb.RoseTree.elim`,
   and a well-typed term denotes a Lean function
   ({name}`Geb.Kernel.Ty.den`). The evaluator agrees with the
   denotation by construction. The term is traversed once and its
   meaning is a Lean closure, so running a program is compiled Lean
   code rather than an interpretive loop.
3. Lean: the primitives {name}`Geb.Kernel.prims`, on labels and
   children: a node's label, arity and child by index; a node from a
   label and a list of children, and the list of a node's children;
   arithmetic and comparison of labels; equality of trees; and the
   base-two logarithm of a label, without which a label's bit length
   would need as many steps of iteration as the label's value. The
   table is only extended, and its members are chosen by what the
   reader, substitution and the checker need.
4. Lean: the reader. A program is a sequence of named definitions in
   S-expressions over lists of characters; names resolve to de Bruijn
   indices, references and primitives ({name}`Geb.Kernel.readProgram`),
   and the reader expands type abbreviations, abstractions over lists
   of binders and local bindings, which the kernel does not have, and
   numeral abbreviations, which name labels as an assembler's symbolic
   constants do and leave no trace in the terms read; the
   definitions are checked and evaluated in order
   ({name}`Geb.Kernel.load`), and the last is applied to an input tree
   ({name}`Geb.Kernel.runMain`). A printer and the retraction law
   between it and the reader remain to be written.

Acceptance: a program written by hand in S-expressions is read, type
checked and run, with arithmetic beyond a machine word; ill-typed and
malformed programs are rejected. The examples of
`GebTests/Prototypes/Kernel.lean` meet it: factorial of thirty by
iteration, the size and mirror image of a tree by the fold, the reversal
of a list in linear time by the right fold, definitions
referring to earlier ones, and rejections of ill-typed, unbalanced,
unresolved and mistyped programs.

## Phase 2: the choice of machine

1. The benchmark programs, written once in kernel S-expressions: a fold
   over a balanced tree of $`2^{20}` leaves, as the value-representation
   chapter measures; a comb and a node of many children; labels beyond
   a machine word; a reader over a megabyte of bytes; the kernel
   evaluator written in the kernel, with a step bound; a normalizer and
   type checker for simply typed terms; and the higher-order terms that
   probe the oracle-free fragment.
2. The arms: an environment machine derived from the denotation, with
   fold frames given by dissections and a proof that it agrees with the
   denotation, and a bounded runner that resumes to the same result; a
   compilation of the kernel to the triage calculus by bracket
   abstraction, run by the repository's machine; and a compilation of
   the kernel's first-order folds to interaction combinators. Every
   result is compared with the denotation.
3. Measurements: agreement, host lines, proof lines, steps and time per
   leaf, memory and its reclamation, and speedup with threads, one heavy
   process at a time. The decision on the reference machine and the
   compilation targets is recorded in this chapter.

Acceptance: the measurements and the decision are recorded.

Deferred: images are kernel terms and the Lean evaluator runs compiled
closures, so the choice of machine matters for the second host and the
backends, not for the first fixed point; the comparison runs before
Phase 5's second host.

## Phase 3: definitions and images

1. Lean: the closed bundle, a well-founded block of kernel definitions
   stored as a rose tree and linked through the reference node,
   evaluated by one fold over its order. {name}`Geb.Kernel.bundle`
   stores a program's definitions beside the table of their names, and
   {name}`Geb.Kernel.runEntry` loads a bundle by
   {name}`Geb.Kernel.load` and applies its named definition; a
   reference to a definition that is not earlier fails to load, so a
   loaded bundle is well founded.
2. Lean: the annotation table of names and comments, keyed by vertex.
   Names of definitions are kept in the bundle; names of bound
   variables and comments are not yet kept.
3. Lean: the image, a header of a magic number, a version and a bit
   count, followed by the word-level form of the interleaved wire
   format without sharing ({name}`Geb.Kernel.writeImage`). Its reader
   {name}`Geb.Kernel.readImage` rejects a wrong magic number or
   version, truncation, trailing data and non-zero bits beyond the
   count. The host driver, the executable `geb-kernel` over
   {name}`Geb.Kernel.Command.run`, builds an image from a program's
   source and runs an image's named definition on a file, presented as
   the tree whose children are the leaves of its bytes. The word-level
   codec agrees with the list form by test, not by proof.
4. Lean: the host binding of the selected hash, if the
   content-addressed workflow is wanted before the library grows, with
   the node-digest rule restated for rose trees; digests are then a
   function of the image's canonical bytes.

Acceptance: an image holding a definition and a client of it
round-trips through the codec and runs a named entry point, and each
malformed variant is rejected. The image examples of
`GebTests/Prototypes/Kernel.lean` meet it. Through the host driver, on
one machine, reversing the bytes of a file of one mebibyte takes
0.58 seconds and summing them 0.19 seconds, at a peak of about 480
megabytes of memory: the plain representation costs hundreds of bytes
per node, which the optimized representation of the value-representation
chapter addresses later.

## Phase 4: Geb grows in itself

1. Geb: libraries of lists, bytes and text, label operations and tree
   utilities, written in kernel S-expressions; the serializer first,
   which must match the seed codec byte for byte, then the reference
   resolver. The sources are under `bootstrap/`: `prelude.geb` names
   the kernel's labels and primitives by numeral abbreviations and holds
   list and digit utilities, and `serialize.geb` writes a tree's image,
   which `GebTests/Prototypes/Stage0.lean` compares with
   {name}`Geb.Kernel.writeImage` byte for byte, on labels of zero and
   beyond a machine word, a node of many children, and the bundle of
   the serializer's own program. These are measured on the growing bundle of the compiler's
   own source before interning, cached hashes, succinct pages or
   parallel evaluation are added.
2. Geb: the reader, from bytes to trees with name resolution, accepting
   exactly the syntax the seed reader accepts, abbreviations included.
   The Lean reader remains as the independent route.
3. Geb: the kernel type checker, compared with the Lean one on valid
   and malformed fixtures.
4. Geb: a minimal elaborator in kernel S-expressions: named variables,
   definitions, and signature declarations whose constructors,
   recognizers and folds are derived generically. `bootstrap/surface.geb`
   expands the Surface 1 forms into kernel S-expressions before the
   reader resolves them: a datatype declaration, whose values are erased
   to trees, the node labelled by a constructor's position over its
   fields, a last field taking the remaining children; case analysis,
   exhaustive unless it has an else clause; structural recursion at a
   result type, the kernel's fold at pairs of a subtree and a suspended
   result, so that no clause is evaluated at the subtrees of fields
   that are not recursive; and functions with result types. A program of
   kernel forms alone expands to itself, so the fixed point holds with
   the expansion in the compiler. Recognizers, type parameters and a
   static check of datatypes are still to be added; the expansion
   refers to some primitives by name, so a program does not rebind them
   around case analysis and structural recursion.
5. Geb: the elaborator rewritten in the surface language it accepts,
   and its staged self-compilation.

Acceptance: the fixed point of the section on what self-compilation
establishes, on images, becomes a continuous-integration target, and
the committed image is a build artifact.

The fixed point holds for the stage-0 compiler written in the kernel's
syntax. `bootstrap/reader.geb` reads text into a program's bundle as the
seed's reader does; `bootstrap/check.geb` is the kernel's type checker,
deciding as the typing half of {name}`Geb.Kernel.infer` decides; and
`bootstrap/compile.geb` composes them with the serializer, from a
program's source to its image, or to the empty file when the program
does not read or is ill-typed. Built by the seed and run by the Lean
evaluator on its own source of about twenty-five kilobytes, it checks
its own definitions' types and produces the seed's image of itself byte
for byte in 0.22 seconds on one machine, and the image it produces
reproduces itself. The examples of `GebTests/Prototypes/Stage0.lean`
compare the checker with the seed's on the kernel's examples, the
compiler and malformed terms, and the compiler with the seed on the
kernel's examples, rejected and ill-typed ones included, and on its own
source, on every build.

The stage-1 compiler is the stage-0 compiler with the Surface 1
expansion rewritten in Surface 1, `bootstrap/stage1/surface.geb`:
datatypes for optional trees, S-expressions and declarations, case
analysis and structural recursion in place of tests of labels and folds,
and functions with result types, computing the same function of a
program's forms. The seed cannot read Surface 1, so the stage-0 compiler
builds its image; run from that image, the stage-1 compiler compiles its
own source to the same image, of about sixteen kilobytes, in 0.61
seconds on one machine, and the image it produces reproduces itself.
`GebTests/Prototypes/Stage1.lean` checks this fixed point and the
agreement of the two compilers on the Surface 1 programs and the
kernel's examples on every build. The rewrite needed neither generated
recognizers nor type parameters, which are therefore added when a
program needs them. The stage-0 sources remain the independent route
from the seed.

## Phase 5: speed and a second host

1. A systems-language host: the evaluator and loader ported from the
   Rust crate of the value-representation prototypes.
2. Lean and Geb: accelerations bound by position or builtin
   identifier, each proved in Lean against the denotation of the term
   it replaces, with the shadow mode that runs both.
3. Geb: compilers to the targets Phase 2 selects, emitting Lean first
   and then an interaction-net runtime, HVM, Bend or a similar one; the
   optimized compiler compiles itself. The emitted Lean is
   committed beside the image, each definition under a name derived
   from its Geb name and in the order of the source, so that a change
   of the compiler's source changes the emitted definitions it touches
   and no others.

Acceptance: both hosts reach the same image fixed point, and the
compiler emitting Lean reaches the fixed point on emitted Lean, which
regenerates the committed Lean byte for byte.

What the first four phases fix for this one: a second host implements
the kernel as {name}`Geb.Kernel.infer` defines it, the labels of its
types and terms and the table {name}`Geb.Kernel.prims`, whose indices
are only extended, together with the image format of
{name}`Geb.Kernel.readImage`; its acceptance is the stage-0 and stage-1
fixed points reproduced on it. A compiler emitting Lean follows the
denotation's structure: a kernel type becomes the Lean type
{name}`Geb.Kernel.Ty.den` gives it, the fold becomes
{name}`Geb.RoseTree.elim`, and each primitive its Lean definition, so
that the emitted program is the denotation written out, and the
executable fixed point of the section on what self-compilation
establishes takes Lake's build as the host build.

The Lean backend of step 3 is constructed. `bootstrap/stage1/lean.geb`
writes a checked program's bundle as a Lean module in which each
definition, in order and under its name, is its denotation written with
the functions of the namespace `Geb.Kernel.Const`, those the seed's
denotations apply at the denotations of their types; the constants are
referred to by qualified names, which no definition's name can capture.
A variable is named by its binding depth, a binder whose variable is
unused is written `_`, an abstraction applied to a value is written as
a `let`, and the text is laid out in groups, each printed on one line
when it and the text following it up to the next line break fit within
100 columns and within 70 columns beyond the indentation. The stage-1
compiler with this backend, built by the stage-0 compiler, is committed
as `bootstrap/compiler.img`, and the Lean it emits from its own source
as `bootstrap/lean/GebBoot.lean`, which Lake builds into the executable
`geb-compile`. That executable compiles the compiler's source to the
committed Lean and the committed image byte for byte, which is
`B(S) = C1(S)` of the section on what self-compilation establishes.
`scripts/bootstrap.sh regen` regenerates both artifacts, and
`scripts/bootstrap.sh check`, run by continuous integration and the
pre-push checklist, checks every fixed point with the compiled
executables. On one machine the compiled compiler emits its Lean in 0.5
seconds, where its image run by the Lean evaluator takes 1.2 seconds.

## Phase 6: content identity

1. The node-digest rule, the hash function and its version tag, if
   Phase 3 did not fix them.
2. Geb: the hash, compared with known answers from the host binding.
3. Geb: the migration from positions to digests, the namespace tree,
   and the re-keying of annotations.

Acceptance: a rename leaves every digest unchanged, a changed
dependency changes the digests of its dependents, and running the
migration twice changes nothing.

What the first four phases fix for this one: the reference node is
the kernel's constructor of label 23 over a definition's position in
its bundle, which the migration rewrites to a digest; the node-digest
rule is restated for rose trees with natural-number labels; and the
serializer written in Geb, `bootstrap/serialize.geb`, is the model for
the hash written in Geb.

## Phase 7: the metalogic

Phase 7 builds two checkers, the computational core's and the
metalogic's (the section on the metalogic and its checker), each by the
same steps.

1. Lean: the rule set and its soundness, without `Classical.choice`, in
   the model of Lean types, and for the metalogic also in a model that
   is not Boolean. For the computational core this step depends only on
   Phase 1 and may proceed in parallel with Phases 2 to 6.
2. Geb: the proof checker, a fold over proof objects, compared with the
   Lean checker on valid and malformed certificates.
3. Geb: proof construction, and proofs about Geb programs that exercise
   it, each in the computational core when it is an equation between
   kernel terms and in the metalogic otherwise, the compiler's
   components first; and stronger checkers admitted by relative
   soundness proofs, each a translation of certificates proved in the
   computational core. The rest of what the metalogic states, the
   richer definitions, Surface 2, the mathematics the libraries consume
   and the equivalence of the free topos with the rose-tree object and
   the free topos with a natural numbers object, is written in Geb
   after the bootstrap (the road map).

Acceptance, for each checker: a theorem with hypotheses, a substitution
and an induction checks, and certificates with altered binders, invalid
dependencies or false conclusions fail; for the metalogic, a
characteristic map checks as well.

For the computational core, step 1 is constructed.
`Geb/Prototypes/Kernel/Subst.lean` weakens kernel terms and
substitutes for their innermost variable through one traversal
({name}`Geb.Kernel.trav`), and proves that both agree with the
denotation ({name}`Geb.Kernel.infer_wk`, {name}`Geb.Kernel.infer_subst`).
`Geb/Prototypes/Metalogic/Equations.lean` defines a sequent as a
context, a list of hypotheses and a conclusion, each an equation
between two kernel terms of a type, valid when both sides of the
conclusion have its type and their denotations agree at every value of
the context at which the hypotheses hold ({name}`Geb.Metalogic.Valid`).
A certificate is a rose tree whose label names a rule, and the checker
{name}`Geb.Metalogic.check` is a paramorphism over it whose result, as
the denotation's, is a function of an environment of a program's
definitions and theorems about it, the global environment the
definitions load, the context and the hypotheses. Its rules are
equality's; congruence of every term former; the β and η rules of
functions, pairs and the unit type; the δ rules, each a primitive
applied to literals, which are quoted trees and lists of them, equal to
the literal of its value; weakening, cut and instantiation of the
innermost variable by a term; the computation rules of the conditional
at a quoted tree, of the right fold and case analysis of lists, of
iteration at the label zero and at a successor, and of the fold of
trees at a node; induction on a list, on a tree,
under the hypothesis that its children satisfy the equation, and on a
label; references to definitions, each the definition weakened into
the context; iteration's reading of its argument's label, and the
conditional as the iteration of a constant function; and instances of
the axioms and of proved theorems, each cited by its index in its own
table, each variable replaced by a term of its type. An induction's
hypotheses must not mention its variable: the checker lowers them and
checks that they are typed below it, which
replaces a converse of weakening by a decidable check. A reference's
rule rests on {name}`Geb.Metalogic.load_loaded`, by which each of a
loaded program's definitions denotes its global in the whole
environment, since extending an environment keeps every denotation
({name}`Geb.Kernel.infer_append`). {name}`Geb.Metalogic.check_sound`
proves every computed conclusion valid, without `Classical.choice`. The
examples of `GebTests/Prototypes/Metalogic.lean` meet the acceptance for
the computational core: a theorem from a hypothesis by congruence, an
instantiation, the proofs by induction that appending the empty list to
a list gives the list, that iterating the identity from a tree as many
times as a label gives the tree, and that a fold whose step ignores its
arguments is constant, a reference to a definition of a loaded program,
and the rejection of certificates with an annotation that is not a
type, a β step whose argument has another type, a missing hypothesis or
definition, a transitivity whose middle terms differ, an induction
whose step does not prove its case, and an induction on a label whose
variable is not a tree.

The axioms are the defining equations of the kernel's primitives, each
from the universal property of the object the primitive acts on
({name}`Geb.Metalogic.axioms`). The rose-tree object's structure map
is inverse to the label and the children, by Lambek's lemma, and the
labels are leaves. The labels are the natural numbers object, zero
and the successor, the sum with one, and its arithmetic is defined by
iteration, its universal property: addition iterates the successor,
the predecessor is the first component of an iteration on pairs,
truncated subtraction iterates the predecessor, multiplication
iterates addition, and the quotient and the remainder are the two
components of one iteration; equality and order of labels are tests
for zero of truncated differences, and the logarithm has its recursion
equation. The arity and the children by index are defined by the right
fold and case analysis of lists, and equality of trees is the
characteristic map of the diagonal: reflexive, licensing replacement,
and Boolean. Each is proved valid in every global environment
({name}`Geb.Metalogic.axioms_valid`), and one rule cites an axiom or a
theorem at terms for its variables ({name}`Geb.Metalogic.valid_thm_inst`).

The checker evaluates no term but a primitive at literals. A Geb
program that evaluates kernel terms takes a step bound (the section on
the metalogic and its checker), so a checker written in Geb could not
apply a rule evaluating every closed term, and a Lean checker with that
rule would not be the Geb checker's specification. The evaluation of a
closed term is derived instead, from the δ rules, the computation rules
and congruence, by a certificate whose size grows with the length of
the evaluation.

For the computational core, step 2 is constructed as well.
`bootstrap/metalogic/equations.geb` is the checker written in Surface 1,
deciding as {name}`Geb.Metalogic.check` decides: a fold over the
certificate whose result at each node is the node paired with its
conclusion as a function of the context and the hypotheses, over the
traversal, weakening and substitution of kernel terms and the values of
the primitives written in Geb, with `bootstrap/check.geb` typing terms
in a context. The examples of `GebTests/Prototypes/Metalogic.lean`
compile it with the stage-0 compiler and compare its conclusion with
the Lean checker's at the certificates of step 1, one certificate of
each rule besides, and malformed variants of each, the certificate's
root relabelled with every rule's label and one beyond or deprived of
its last child; the two agree on every one, the tables of axioms
included. The labels of the kernel's constructors, the primitives'
indices and the checker's rules are named by numeral abbreviations in
`bootstrap/prelude.geb` and `bootstrap/metalogic/equations.geb` and by
abbreviations in Lean, `Geb.Kernel.Label`,
`Geb.Kernel.Prim` and `Geb.Metalogic.Rule`, which the
tests hold equal name for name.

Step 3 is begun for the computational core. `bootstrap/metalogic/prove.geb`
constructs certificates by derived rules, so that nothing in it is
trusted. Normalization, innermost first, contracts the redexes of the
computation rules, with literals put in constructor form by δ rules
used backward, unfolds chosen definitions and rewrites with chosen
axioms and theorems, found by first-order matching, and with the
hypotheses; each node's children are normalized under one congruence,
so that a certificate restates a term once per contraction at its
node rather than once per step. Tactics simplify both sides of a goal,
rewrite a side at a chosen occurrence, and split a goal by induction on
a list, a tree or a label into the goals the checker's induction rules
expect. A file of a program's forms and theorems is read with each
theorem's statement read as a definition of the program, so that it is
expanded, resolved and typed as the program is, its Surface 1 forms
expanded by the stage-0 expansion that the prover carries, and each
theorem's certificate is checked against its statement, citing the
theorems before it. `bootstrap/proofs/prelude.geb` proves the empty
list a unit of appending and appending associative;
`bootstrap/proofs/nat.geb` derives addition's recursion equations from
its definition by iteration and proves zero a left unit of addition by
induction on labels; `bootstrap/proofs/check.geb` proves, about the
kernel's type checker written in Geb, that a quoted tree has the type of
trees in every context and environment; `bootstrap/proofs/equations.geb`
proves, about the metalogic's checker written in Surface 1, that the
accessors of an equation return the fields it is built from; and
`bootstrap/proofs/surface.geb` derives the recursion equations of a
function by structural recursion over a declared datatype from its
expansion. The examples of
`GebTests/Prototypes/Proofs.lean` check every certificate in Geb and
again with {name}`Geb.Metalogic.check`, and reject a false equation and
an unproved one.

### The computational core

The computational core is built by the three steps above. It states
and proves the following.

* Judgment: a context of kernel types, a list of equations as
  hypotheses, and an equation between kernel terms of a type; valid
  when both sides denote one value at every value of the context that
  satisfies the hypotheses ({name}`Geb.Metalogic.Valid`). Constructed.
* Types and terms: the kernel's, of every type. Constructed.
* Rules: equality, congruence of every term former, the β and η rules,
  the δ rules at literals, weakening, cut, instantiation, the
  computation rules of the kernel's eliminators, induction on lists,
  trees and labels, the unfolding of definitions, iteration's reading
  of the label, the conditional as an iteration, and citations of
  axioms and of theorems, each named in `Geb.Metalogic.Rule`.
  Constructed.
* Axioms: the defining equations of the primitives
  ({name}`Geb.Metalogic.axioms`). Constructed.
* In Lean: soundness in the model of Lean types
  ({name}`Geb.Metalogic.check_sound`). Constructed.
* In Geb: the checker `bootstrap/metalogic/equations.geb`, constructed;
  the prover `bootstrap/metalogic/prove.geb`, with normalization,
  rewriting, induction and the Surface 1 forms, begun.
* Proofs of the bootstrap, which exercise the prover on the compiler's
  components, in order:
  1. lists and labels: the prelude's appending, addition's recursion
     equations and zero as a unit of addition, constructed;
  2. the accessors of the checker's equations, and the recursion
     equations of a structural recursion, through the Surface 1
     expansion, constructed;
  3. the type checker's preservation of types by weakening and by
     substitution, not begun (the next phase);
  4. the Surface 1 expansion's identity on programs of kernel forms,
     not begun;
  5. the reader's inverse to the printer, after the printer, not begun;
  6. the admission of a stronger checker by the proof that a Geb
     program translates its certificates into the computational core's
     with the same conclusions, not begun.
* After the bootstrap: equational theorems about programs, and the
  lemmas that the metalogic's proofs cite.

### The metalogic

The metalogic is the free topos with the natural numbers, list and
rose-tree objects, presented at once and checked by one checker, which
is built by the method the computational core establishes: a checker
defined, proved sound in Lean and written again in Geb. This section
states the presentation, its relation to the computational core, and
the questions that remain, which are settled by constructing and
measuring.

A category is a presheaf on the walking parallel pair whose two objects
are the objects and the morphisms and whose two restrictions are the
domain and the codomain, a directed multigraph, with composition and
identities. A category with chosen finite limits and finite colimits,
exponentials, a subobject classifier and the data objects is then a
model of an essentially algebraic theory over that graph, one whose
operations are partial, the domain of each given by equations
{citep Freyd1972}[], and the free topos with the data objects is its
initial model. The theory has these operations:

* on objects: the terminal and initial objects, binary products and
  coproducts, the equalizer and the coequalizer of a parallel pair, the
  exponential, the subobject classifier, and the natural numbers, list
  and rose-tree objects, with any other data object that is built in for
  the cost of computing with it;
* on morphisms: identities, composition, and the universal morphisms of
  each object, its constructors and destructors: the projections and
  pairing, the injections and case analysis, the equalizer's inclusion
  and factorization, the coequalizer's projection and descent,
  evaluation and currying, truth and the characteristic map, and each
  data object's structure map and fold;
* axioms: the laws of a category and the equations of each universal
  property, those of the data objects stating that each is an initial
  algebra of its polynomial functor, through the notions of an algebra
  and of a morphism of algebras.

The axiomatization is the definition of an elementary topos, not a
Grothendieck topos, as a finitely complete and finitely cocomplete
category with exponentiation and a subobject classifier (Section 4.3 of
{citet Goldblatt1984}[]), the finite limits
given by the terminal object, binary products and equalizers, and the
finite colimits by the initial object, binary coproducts and
coequalizers. The finite colimits follow from the rest
{citep Pare1974}[] and are operations nonetheless, so that the bootstrap
does not construct them; their redundancy, an equivalence between the
two presentations, is proved in Geb after the bootstrap.
Each operation is then one universal property with its own name, and
the constructions composed from them, pullbacks and kernel pairs among
them, are definitions. The pullback of truth along a morphism into the
subobject classifier is the equalizer of that morphism and of truth
after the unique morphism to the terminal object, so the classifier's
axioms state that a monomorphism's factorization through that equalizer
is an isomorphism, and, as an equation with premises, that a morphism
along which a monomorphism is so a pullback is that monomorphism's
characteristic map.

That construction is established. Toposes with chosen structure, with
the functors that preserve it on the nose, are the models of an
essentially algebraic theory, whose monomorphisms are the morphisms
whose kernel pair's projections are isomorphisms; the theory's initial
model is the free strict topos, and it is bi-initial among toposes,
logical functors and natural isomorphisms, so it is the free topos
(Proposition 1.16, Definition 1.21 and Proposition 1.22 of
{citet ForssellLumsdaineSwan2026}[], whose toposes are regular
categories with power objects and a natural numbers object). The strict
initial model depends on the axiomatization: a topos defined as a
cartesian closed category with a subobject classifier gives another
strict initial model, equivalent to the first and not isomorphic to it
(their Caveat 1.5). Data objects added as operations change the strict
initial model in the same way, each new object isomorphic, not equal, to
the one the topos structure constructs.

Partial Horn logic presents such a theory syntactically. Its example
theories of directed graphs and of categories have exactly the sorts of
objects and arrows, with the domain, the codomain and the identity as
total operations and composition defined when the codomain of one arrow
equals the domain of the other (Examples 4, 5 and 13 of
{citet PalmgrenVickers2007}[]). A derivation proves that a term is
defined or that two terms are equal, and the closed terms that are
provably defined, taken modulo provable equality, are the initial model
(their Theorem 22), by a proof that uses no choice and is formalizable
in a constructive, predicative theory (their Section 1). That is the
computational core's architecture: every term is a rose tree, the checker is a
fold over certificates whose conclusions are definedness and equality,
and the quotient is the equality the checker proves. Composition is
defined when the codomain of one morphism equals the domain of the
other, the equalizer's factorization when a
morphism equalizes the pair, and the characteristic map at a
monomorphism, a morphism whose kernel pair's projections are equal; each
condition is a premise of a rule, as the computational core's induction rules
have premises, and not an argument of the term. The terms' identity
therefore does not depend on proofs, and no equation making proofs
irrelevant is needed. This presentation is fibered: the morphisms form
one sort, with their domains and codomains as operations. It is the form
chosen, since each of its definitions is one of that literature's.

Equality is a judgment at both sorts, so the quotient identifies objects
as well as morphisms. The equalizer of two morphisms equals the
equalizer of two morphisms provably equal to them, by congruence, and
must, since a term is replaced by an equal one inside every other; and
the premise of a composite's definedness is an equation between
objects. The objects of the strict initial model therefore have an
equality, which the notions of category theory invariant under
equivalence do not use: the strict categories are a technical device and
the 2-categories the objects of study (Caveat 1.5 of
{citet ForssellLumsdaineSwan2026}[]), and the bi-initiality of the free
strict topos is its invariant universal property.

The presentation may instead be indexed, the morphisms a family over
pairs of objects, as in quotient inductive-inductive types; Section 4.7
of {citet Kovacs2022}[] compares the two forms. The indexed form carries
a formation's conditions by transport, the conversion rule of
dependent type theory: a morphism with an equality between its domain
or its codomain and another object is a morphism with that object in
its place, the checker checking the equality first, and two terms that
differ only in their transports' certificates are equal. The conditions
that are not agreements of domains and codomains become such agreements
through diagonal instances. The equalizer of a morphism with itself is
that morphism's domain, so its inclusion has an inverse at every
morphism; the equalizer is functorial, a morphism `h` into the domain of
a pair `f`, `g` sending the equalizer of `f ∘ h` and `g ∘ h` into that of
`f` and `g`; and a morphism `h` with `f ∘ h = g ∘ h` factors through the
equalizer of `f` and `g` as the inverse at `f ∘ h`, transported along
the equality between the equalizer of `f ∘ h` with itself and that of
`f ∘ h` and `g ∘ h`, followed by the functorial map. The coequalizer is
dual, and the characteristic map is formed at every morphism as that of
its image. Transport is then the one former whose checking depends on an
equality. In the fibered form transport is the rule by which an equation
establishes a term's definedness, and no former. The quotient presheaf
polynomial functors of `Geb/Prototypes/QuotientPRA/` express neither
form: their free arities admit no condition between the arguments of a
term constructor, their initiality theorem requires term constructors
whose arguments are terms, and `no_uniform_transport` in
`Geb/Prototypes/QuotientPRA/Obstruction.lean` proves that transport is
not a constructor of fixed shape, since the restriction of a tree
rebuilds its root; composition is excluded by the same argument, the
domain of a composite being that of its first morphism. The checker
computes domains and codomains instead, as a fold cutting a subtype out
of rose trees, the form of the slice W-types' {name}`SlicePFunctor.W`.

The checker's language is the combinators, the terms of the fibered
presentation, a program being extended by definitions of objects, of
morphisms and of equalities in place of the definitions of kernel terms.
The internal language of the topos, the Mitchell–Bénabou language,
which is the intuitionistic higher-order type theory of the section on
the metalogic and its checker, may be a surface language over them,
elaborated into the combinators by its interpretation in a topos, as
Surface 1 is elaborated into the kernel; its proofs bind variables where
the combinators compose projections.

The kernel remains the language of computation, since the free topos
has arrows that no System T term defines. The computational core's
rules are the equations of the fragment that the kernel's terms denote,
the cartesian closed category with the data objects, related to the
presentation by the translation between λ-terms and the morphisms of a
free cartesian closed category that the Categorical Abstract Machine
compiles by {citep CousineauCurienMauny1987}[].

The theory, its axioms and the certificates of its derivations are
finite syntax, rose trees, and so data of the metalogic: the checker is
a kernel program on them, and that a certificate derives a judgment is
an equation about that program, as in the computational core. The categorical
form of that internalization is the initial internal model: every
finitely presented essentially algebraic theory has an initial internal
model in every arithmetic universe (Theorem 3.22 of
{citet ForssellLumsdaineSwan2026}[], who attribute its only full proof
to an unpublished manuscript of Maietti), and a topos with a natural
numbers object is an arithmetic universe, so the free topos contains an
internal free topos, the object of its own syntax. That the checker is
sound, every certificate it accepts valid, is not provable in the
metalogic of that internal syntax (the section on the metalogic and its
checker).

The soundness proof interprets objects as Lean types, and the subobject
classifier of Lean's types is `Prop`: `Utilities/TypesClassifier.lean` in
the `geb-lean/` subdirectory of the experimental repository constructs
`ULift Prop` as a classifier of `Type u`, the characteristic map of a
monomorphism holding at the points of its image, and compares it with
the classifier of presheaves on the terminal category, whose sieves on
the one object are propositions. Its pullback property is proved through
mathlib's `Limits.Types.isPullback_iff`, which depends on
`Classical.choice`: the pullback's factorization is a function from the
image of a monomorphism back to its domain, which is unique choice, and
Lean's propositions do not eliminate into its types. With morphisms
interpreted as Lean functions, the presentation's isomorphism between a
monomorphism and the pullback of truth along its characteristic map
needs that function. With morphisms interpreted as functional relations,
total and single-valued relations valued in `Prop`, it is a relation
and needs no choice; those are the arrows of the free topos that
{citet LambekScott1980}[] construct from a type theory without a
description operator (their Definition 4.3). The Mitchell–Bénabou
language needs neither when it has no description operator, since its
terms are λ-terms, interpreted as Lean functions.

Two presentations in the experimental repository bear on the rule set.
`FreeToposBT.lean` presents a free topos by combinators whose equations
the terminal object satisfies as a subobject classifier (the section on
prior art in the repositories). The axioms above exclude that model:
with the terminal object as the subobject classifier, the pullback of
truth along the characteristic map of the monomorphism from the initial
object to the terminal object is the terminal object, so the isomorphism
would identify the two. `src/LanguageDef/ProgFinSet.idr` in `geb-idris/`
defines the objects, morphisms and equalities of finite sets
inductive-inductively, with equalizers and coequalizers of arbitrary
morphisms, factorizations that take proofs of their conditions,
equations making those proofs irrelevant, and a classifier of equalizer
inclusions, which avoids the condition of monicity since every
monomorphism of a topos is an equalizer; it is the nearest prior
presentation, in the Boolean case.

Definitions would be one index of the checker's syntax: a Boolean
states whether a term may refer to definitions, the node of a
reference being admitted at one value only. A term with references is
checked and interpreted in an environment of definitions, each an
object, a morphism or an equality over the definitions before it; the
unfolding replaces each reference by its definition, from the syntax
with references to the syntax without; and a theorem proved in Lean
states that the interpretation of every term is that of its unfolding.
The unfolding is not run but on small tests; checking and evaluation
use the definitions. The definition of a definition is the structure
the unfolding theorem is stated over. For one sort it is constructed in
`Geb/Prototypes/Definition/`. A new operation's body is a term of the
free monad of the signature it extends, and the interpretation of a
term with new operations, each read as its body, is the interpretation
of its unfolding ({name}`Geb.Definition.eval_expandOps`), which is the
theorem above for one sort. Derived operations present, over the sum of
a signature with the new operations, the equations stating that each new
operation equals its body
({name}`Geb.Definition.Presentation.ofDerived`); the unfolding
({name}`Geb.Definition.Presentation.unfoldOps`), a morphism of free
monads, coequalizes the two endpoints of those equations' witnesses,
the inclusion of the terms without new operations being its section;
and the criteria of eliminability and non-creativity {citep Suppes1957}[]
are theorems ({name}`Geb.Definition.Presentation.cls_inlTerm_unfoldOps`,
{name}`Geb.Definition.Presentation.eq_of_cls_inlTerm_eq`), the models of
the extension being the algebras of the signature it extends
({name}`Geb.Definition.Presentation.modelEquiv`). The Boolean chooses
between the sum and the signature. The form chosen is this monadic one:
definitions, from new operations to terms of a signature, extend to a
morphism of free monads from the extended signature to the signature,
which is the unfolding, and the defining equations make it inverse to
the inclusion of the signature's terms. The proposal needs that structure
for a partial Horn theory of two sorts, a defined operation being defined
where its body is and equal to it there; iterated, so that a definition
refers to earlier ones; and with defined equalities, theorems whose
unfolding is their certificates. In the computational core a reference unfolds
one step at a time ({name}`Geb.Metalogic.valid_unfold`), resting on
{name}`Geb.Metalogic.load_loaded`; no theorem yet unfolds every
reference of a kernel term.

The questions are of two kinds. The first are constructions, each of
which is established by carrying it out:

1. the rule set, the axioms of each operation above as partial Horn
   sequents with the rules of partial Horn logic, checked against its
   specification: its models are the elementary toposes with chosen
   structure and the data objects, which the literature establishes for
   some such rule set and not for this one;
2. the model in Lean, with morphisms as functional relations: whether
   the universal property of every operation, the exponential's among
   them, holds there without `Classical.choice`, and so whether the rule
   set is sound in it;
3. the definitional extension of a partial Horn theory in the monadic
   form, iterated: whether unfolding preserves the judgments of
   definedness and equality, so that certificates unfold as well as
   terms, and its unfolding theorem.

The second are choices between options each of which is known to be
constructible:

4. whether the Mitchell–Bénabou language is written as a surface
   language during the bootstrap or after it;
5. whether the computational core keeps a checker and prover of its
   own, or its equations are proved in the metalogic through the
   translation of kernel terms, which depends on how the kernel's
   denotations, which are functions, relate to the model's morphisms,
   which are functional relations (the second construction).

The first construction precedes the other two, which are independent of
each other; the choices follow them.

The first construction is made in one direction. The rule set is
{name}`Geb.FreeTopos.theory`, a partial Horn theory whose sorts are the
objects and the arrows, and its certificates are rose trees that
{name}`Geb.PartialHorn.check` checks, sound in every model of the theory
({name}`Geb.PartialHorn.check_sound`). The category of a model
({name}`Geb.FreeTopos.ToposModel.Cat`) is an elementary topos as the
repository's class states it
({name}`Geb.FreeTopos.ToposModel.elementaryTopos`), and its data objects
have the universal properties of the natural numbers object, of list
objects and of the initial algebra of rose trees
({name}`Geb.FreeTopos.ToposModel.natRec_uniq`,
{name}`Geb.FreeTopos.ToposModel.listRec_uniq`,
{name}`Geb.FreeTopos.ToposModel.roseRec_uniq`). The construction of the
category and of its universal morphisms uses no axiom beyond
`propext` and `Quot.sound`; only the packaging as mathlib's structures,
whose limit cones and pullbacks do, uses `Classical.choice`. The
converse, a model of the theory from an elementary topos with chosen
structure and data objects, is not constructed. A model's operations
({name}`Geb.PartialHorn.Model`) are partial functions whose domains of
definition are propositions, as mathlib's `Part` states them, so that a
model need not decide where an operation is defined: neither the
converse nor the second construction is confined to a topos whose
objects have decidable equality.

The fourth choice is made by measurement. Soon after the first
construction, the theorems proved in the computational core in
`bootstrap/proofs/prelude.geb` and `bootstrap/proofs/nat.geb` are
proved again in the combinators, and the two are compared on the size
of their certificates and the time to check them, and on how they read.
Programs remain kernel terms, so the choice does not change the speed
of the compiler, only that of checking the development written in the
combinators, whose certificates bind no variables and are the larger
for it. The Mitchell–Bénabou language is deferred while checking stays
within a small multiple of the computational core's time and the proofs read as
their mathematics rather than as the arrangement of projections,
pairings and curryings. When either fails, it is written at the
earliest point at which it can be, after the first construction, since
its interpretation needs every operation of the topos and nothing of the
other two constructions. It is written as a logic of its own. Each of
its constructions has defining equations stating its meaning in the
combinators, and each of its rules is proved sound in Lean against the
language's interpretation in the free topos. A translation compiles
each of its derivations to a certificate of the combinators, which the
one checker checks, so that the checker stays small; the translation is
proved in Lean to send every derivation to a certificate of its
conclusion's interpretation, so that every theorem of the language has
one. A user of the language then proves theorems about its
constructions in the language they are written in, and the defining
equations state what each construction means in the object language.
Its terms refer to the definitions made in the combinators before it, so
that the development continues in it without rewriting them.

The measurement is made. A prover prototyped in Lean computes
certificates of the combinators: it types a term by the axioms that
compute domains and codomains, proving each fact about a subterm once as
a lemma of the development that later certificates cite; it rewrites by
the axioms and a library of derived equations, which it proves itself,
matching objects by canonical form; and it proves an equation between
arrows from a natural numbers or list object by the uniqueness of
recursion, and one from a list object with a parameter by that of the
curryings ({name}`Geb.FreeTopos.Prover.normalize`,
{name}`Geb.FreeTopos.Prover.byListParamInduction`). A development
checks when each certificate proves its sequent with those before it as
theorems, and its sequents then hold in every model
({name}`Geb.PartialHorn.checkDevelopment_sound`). The seven theorems,
appending and addition defined by recursion into exponentials, are
proved so in `GebTests/Prototypes/FreeTopos/Benchmark.lean`. Checked by
the Lean checkers, the computational core's certificates have from 22
to 1315 nodes and check in 29 milliseconds; the combinators' have from
4938 to 798736, from 70 to 1376 times as many, and check in 17 seconds.
Neither criterion holds. Checking takes several hundred times the
core's time, and the statements, the definitions and the steps an
induction names are arrangements of projections, pairings and
curryings. The associativity of appending, `(append (append xs ys) zs)`
equal to `(append xs (append ys zs))` in the core, equates the arrows

```
comp append (pair (comp append (pair (fst L P) (comp (fst L L) (snd L P))))
  (comp (snd L L) (snd L P)))
comp append (pair (fst L P) (comp append (snd L P)))
```

The two failures have different causes. Of the combinators'
certificates' nodes, 89 in 100 are the terms that instances of axioms
and theorems repeat in full, the expansions of appending and addition
among them. The Mitchell–Bénabou language compiles to the same
certificates, so it answers how the development reads and not how long
it takes to check. The third construction, by which a certificate names
a definition rather than repeating its expansion, bears on the size;
and a checker that infers definedness and canonical objects, as the
core's checker infers the types of kernel terms, proved sound in Lean,
bears on the facts the certificates prove besides.

The fifth choice is deferred until the three constructions are made.

## Improvements

The following are known limitations of what is constructed, each with
the change that removes it.

* Primitives named in expansions. The Surface 1 expansion refers to the
  primitives `label`, `child`, `children`, `node` and `eq` by name, so a
  program that binds one of these names around a case analysis or a
  structural recursion changes the expansion's meaning. A reference to
  a primitive that no binding shadows, a reader form naming a
  primitive by its index, added to the seed's reader and to the Geb
  reader alike, removes the dependence; the reservation of names
  beginning with `%` for the expansion is likewise documented and not
  enforced.
* Diagnostics of the Geb compiler. The stage-0 and stage-1 compilers
  report a program that does not read, expand or type-check by an empty
  image and name no definition, where {name}`Geb.Kernel.diagnose` in the
  seed names the first failing one. Until the Geb compiler reports a
  message, a failing program is diagnosed by expanding it with the
  stage-0 expansion, printing the kernel forms, and applying
  {name}`Geb.Kernel.diagnose` to them.
* The reader's printer and the retraction law of Phase 1, and the
  unification of the readable S-expressions with the canonical ones,
  with a quoted spelling for atoms that are not tokens.
* The equivalence of the word-level codec with
  {name}`Geb.RoseTree.wire`, tested and not proved, which is the first
  of the decision gates of the value-representation chapter.
* Memory. The plain representation takes about 480 bytes of memory per
  byte of input to the host driver; the optimized representation of the
  value-representation chapter removes most of it.
* Proof construction. The prover rewrites with a hypothesis only where
  its side occurs outside the goal's binders and unapplied: a side that
  reaches a binder by β-reduction is rewritten first, since
  normalization contracts arguments before the redex, but a hypothesis
  between functions is not used at their applications. And it
  normalizes innermost first, so that the branches a conditional
  discards are normalized as well. Rewriting at applications under
  binders (the next phase), and normalizing a conditional's test before
  its branches, remove each.
* Atoms as character codes. The Geb sources spell the atoms they
  compare with, the keywords of the reader, the expansion and the
  prover, as quoted lists of character codes, since a datum has no
  spelling for an atom; the quoted spelling of the syntax unification
  removes it.
* Depth of the Geb reader and serializer. The reader's tokenizer and
  the serializer's packing of bits are right folds whose continuations
  nest one call per character and per bit, so running either in Lean's
  interpreter needs stack in proportion to a program's length; the
  tests bundle and load the prover without writing its image for that
  reason. Folds that thread their state from the left in constant depth
  remove the limit.
* Test time. The stage tests compare the Geb compilers with the seed in
  Lean's interpreter, tens of seconds each; running those comparisons
  with the compiled executables, as `scripts/bootstrap.sh` runs the
  fixed points, shortens them. A change to a Geb source rebuilds every
  test module, since the test library as a whole depends on the
  sources that some of its modules read by `include_str`; a library of
  those modules alone would confine the rebuild to them and their
  importers.
* Emitted names. A program's definition named `T`, `leaf` or `mk` makes
  the emitted module ill-typed, since the module refers to the tree type,
  the leaf and the node by those names; qualifying them as the constants
  are qualified removes the restriction.
* Surface 1 lacks generated recognizers, type parameters and a static
  check of datatypes; a pattern omits the `&` that a declaration
  writes; and every pattern variable is bound whether or not the clause
  uses it.
* Only the names of definitions are kept beside a bundle; the names of
  bound variables and comments are not.
* Names. The computational core's checker and prover are in the
  namespace `Geb.Metalogic` and under `bootstrap/metalogic/`, although
  the metalogic is the free topos above the core; renaming them for the
  core, the Geb rule names with the Lean ones that a test holds equal,
  removes the ambiguity.

## The next phase

The metalogic is built next, in the order of the section on the
metalogic: after its first construction, made in one direction, the
measurement that makes the fourth choice; the second and third
constructions; and then the fifth choice. The computational
core's step 3, whose proofs are about kernel programs whichever the
fifth choice, resumes after it, at the proof that follows. The next
proof is the type checker's preservation of types by weakening, of `typeIn`
in `bootstrap/check.geb` and `wkAt` in `bootstrap/metalogic/equations.geb`:
for every environment `G`, contexts `c1` and `c2`, type `a` and term
`t`, `typeIn G (append c1 (cons a c2)) (wkAt (length c1) 1 t)` equals
`typeIn G (append c1 c2) t`. The checker checks an abstraction's body
one binder deeper, where the inserted type is one position further in,
so the statement is proved as an equation between functions of `c1`,
by induction on `t`; the induction's hypothesis is an equation between
the lists of the children's functions. The checker tests a node's label
by a chain of conditionals, which do not reduce at a variable label.
The proof needs, in order:

1. lemmas moving a fold, a projection and an application through a
   conditional, stated with variables of function type and proved by
   induction on the label of the test;
2. lemmas on lists: the fusion of two maps, the element of a mapped
   list at a position, and the positions of an appended list;
3. a tactic that proves an intermediate equation and adds it as a
   hypothesis by cut, so that the list equation of the induction yields
   an equation for each child;
4. rewriting with a hypothesis between functions at its applications,
   `f u` to `g u`, by congruence of application and β, under binders,
   the hypothesis's free variables weakened past them.

Substitution follows by the same method, then the expansion's identity
on programs of kernel forms. The rest of the road map's bootstrap, the
choice of machine and the second host, content identity and the syntax
unification, is independent of the metalogic and may proceed beside it.

## What self-compilation establishes

Fix the compiler's source closure `S`, its target, its options, its
dependencies, and the host build `H`, which is the identity while the
target is the image and Lean's build once the compiler emits Lean. Let
`B` be the elaborator written in kernel S-expressions and run by the
Lean evaluator.

```
C1 = H(B(S))
C2 = H(C1(S))
C3 = H(C2(S))
```

The target artifacts must agree, `B(S) = C1(S)`, and that one comparison
suffices while the target is the image or Lean source. The host build
is then applied to identical bytes, `C2 = H(C1(S)) = H(B(S)) = C1`, so a
comparison of executables tests only whether the host build is
reproducible, a property of Lean and Lake rather than of Geb, and is
checked separately if at all. GCC compares the object files of its
second and third stages because its target is machine code; a compiler
whose target is the source of another compiler compares that source.
Lean compiles a program to C, which the toolchain's C compiler
compiles and links; neither the C nor the executable is one of Geb's
artifacts. Maps are ordered explicitly, and timestamps, random
identifiers and absolute paths are excluded from every artifact that
carries identity. Bytes are compared, not digests. A change of `S`, of
the options or of a dependency starts a new test.

A fixed point does not prove the compiler correct, prove the checker
sound, or remove the host's runtime from the trusted base; the Lean
proofs and the independent route remain. Self-hosted here means that
Geb's implementation is written in Geb and compiled by Geb; a native
backend without Lean is a separate milestone.

## Comparing builds

Another builder compares its artifacts with the committed ones by
digest. The image and the emitted Lean are functions of the source and
the pinned toolchain, so every builder's must agree; executables are
not compared, by the previous section. Git names each committed file by
the digest of its contents, SHA-1 in the default object format, and a
signed commit or tag signs the tree of those digests; a builder who
regenerates the artifacts in a checkout compares them by the status of
the working copy, or compares a file's `git hash-object` with the blob
the tree names. An artifact published outside the repository is
accompanied by a manifest of SHA-256 digests signed with the key that
signs commits, by `ssh-keygen -Y sign` when that key is an SSH key.
GNU Guix compares builds the same way:
[`guix challenge`](https://guix.gnu.org/manual/en/html_node/Invoking-guix-challenge.html)
compares the digest of a locally built item with the digests that
substitute servers publish and reports each mismatch.

The digests of Phase 6 give definitions an identity across edits; they
are not needed for this comparison, since the image is a canonical
serialization without sharing and the digest of its bytes identifies
the bundle. A table of them, one per definition, would locate a
mismatch at a definition, where the digest of a file reports only that
the files differ.

{includeLiterate "." Geb.Prototypes.Kernel.Basic "The kernel" (level := 1)}

{includeLiterate "." Geb.Prototypes.Kernel.Reader "The kernel's readable syntax" (level := 1)}

{includeLiterate "." Geb.Prototypes.Kernel.Image "Bundles and images" (level := 1)}

{includeLiterate "." Geb.Prototypes.Kernel.Command "The kernel's host driver" (level := 1)}

{includeLiterate "." Geb.Prototypes.Kernel.Subst "Substitution in kernel terms" (level := 1)}

{includeLiterate "." Geb.Prototypes.Metalogic.Equations "The computational core" (level := 1)}

{includeLiterate "." Geb.Prototypes.Bootstrap "A computation-certificate prototype" (level := 1)}
