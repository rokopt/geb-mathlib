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
import Geb.Prototypes.Definition
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

This chapter records the decisions that fix the seed, a survey of how
other languages and proof checkers bootstrap, and the plan, a sequence
of phases each ending with an executable acceptance condition. The
optimized representation that the chapter on value representation
designs is not a prerequisite: the seed uses the plain representation,
and the optimized one is written later in Geb. Nothing in this chapter
asserts that a component exists unless it names the Lean declaration or
file that implements it.

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
adding the rose-tree type with its constructor, no-confusion and
induction axioms to that type theory generates the free topos on the
rose-tree object. A checker for the type theory with the rose-tree
type is therefore a complete kernel for the metalogic: the topos
structure is derived from provability rather than presented by
combinators, and no mutual definition of objects, morphisms and their
equalities is needed. That this topos is equivalent to the free topos
with a natural numbers object is a claim about structure and its
preservation, to be proved; a bijection between trees and natural
numbers in sets does not prove it.

The seed's rule set states typing, substitution, comprehension,
extensionality and induction explicitly; the equalities of the
computation fragment supply none of them. Proof terms are explicit and
finite, and the checker is not required to decide equality of
morphisms, to normalize programs, or to search for proofs that a
relation is functional. Propositions are not executable Booleans in
general.

The ten primitive rules of HOL Light are "rather similar to those for
the internal logic of a topos", and "it is only from" the choice axiom
that the HOL logic is classical {citep Harrison2009}[], excluded
middle following from choice {citep Diaconescu1975}[]. The metalogic's
checker is accordingly designed as intuitionistic higher-order logic
in the style of HOL Light, with proof objects, and with three
differences:

* Sequents are indexed by their free variables, as Lambek and Scott's
  are, since HOL's rules assume every type inhabited.
* There is no choice operator. A topos has unique choice, so a
  functional relation is a morphism; descriptions are admitted only
  with a proof of unique existence.
* A defined type is a subobject: its representation map is a
  monomorphism with no total map back from the base type. A total map
  back is suspected of deriving the weak excluded middle; that is to
  be checked in Lean before the rule set is fixed, and the design
  avoids it in any case.

The checker is a fold over proof objects that computes each
conclusion from the premises' conclusions, trusting no stated
conclusion; {name}`Geb.Bootstrap.infer` is that pattern for a fragment
of computation equalities. Its soundness is proved in Lean by
interpreting types as Lean types, without `Classical.choice`, and it
is tested in a model that is not Boolean, where a classical rule would
fail.

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
self-hosting, Geb admits stronger checkers as Milawa does; it cannot
prove its first checker sound, which would prove its own consistency,
so that proof stays in Lean.

Two kinds of extension differ. A derived definition, a derived rule or
a proof-producing tactic can be written in Geb and produce evidence
the existing checker accepts. A new foundational principle needs a
conservative interpretation into the checker's theory or an explicit
change of the theory: defining a data type of purported proofs does
not make them sound. The foundational rule set is therefore fixed
before mathematical proofs are migrated, and a migration from Lean
checks the logical strength and the universes it relies on, since a
fixed elementary-topos presentation does not internalize all of
Lean's universe-polymorphic mathematics.

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
  is superseded by the type-theoretic presentation above.
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

## Phase 1: the kernel runs in Lean

1. Lean: the kernel's syntax. Terms and types are rose trees read
   directly, the label of a node naming its constructor, so a program
   is a value of the language and needs no separate syntax type: de
   Bruijn variables, abstraction over a domain type, application, the
   unit value, pairs and projections, quoted trees, a conditional on
   whether a label is non-zero, lists with their right fold
   ({name}`Geb.Kernel.foldrDen`), the fold of trees and iteration at
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
   arithmetic and comparison of labels; and equality of trees. The
   table is only extended, and its members are chosen by what the
   reader, substitution and the checker need.
4. Lean: the reader. A program is a sequence of named definitions in
   S-expressions over lists of characters; names resolve to de Bruijn
   indices, references and primitives ({name}`Geb.Kernel.readProgram`),
   the definitions are checked and evaluated in order
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

## Phase 3: definitions and images

1. Lean: the closed bundle, a well-founded block of kernel definitions
   stored as a rose tree and linked through the reference node,
   evaluated by one fold over its order. The reader's sequence of
   definitions, loaded in order by {name}`Geb.Kernel.load`, is its first
   form; the bundle adds the stored tree and the validation of its
   references.
2. Lean: the annotation table of names and comments, keyed by vertex.
3. Lean: the image, a version header followed by the interleaved wire
   form without sharing; its loader, which rejects truncation, trailing
   data, a wrong version and unresolved or cyclic references; and the
   host driver of the section on input and output.
4. Lean: the host binding of the selected hash, if the
   content-addressed workflow is wanted before the library grows, with
   the node-digest rule restated for rose trees; digests are then a
   function of the image's canonical bytes.

Acceptance: an image holding a definition and a client of it
round-trips through the codec and runs a named entry point, and each
malformed variant is rejected.

## Phase 4: Geb grows in itself

1. Geb: libraries of lists, bytes and text, label operations and tree
   utilities, written in kernel S-expressions; the serializer first,
   which must match the seed codec byte for byte, then the reference
   resolver. These are measured on the growing bundle of the compiler's
   own source before interning, cached hashes, succinct pages or
   parallel evaluation are added.
2. Geb: the reader, from bytes to trees with name resolution. The Lean
   reader remains as the independent route.
3. Geb: the kernel type checker, compared with the Lean one on valid
   and malformed fixtures.
4. Geb: a minimal elaborator in kernel S-expressions: named variables,
   definitions, and signature declarations whose constructors,
   recognizers and folds are derived generically.
5. Geb: the elaborator rewritten in the surface language it accepts,
   and its staged self-compilation.

Acceptance: the fixed point of the section on what self-compilation
establishes, on images, becomes a continuous-integration target, and
the committed image is a build artifact.

## Phase 5: speed and a second host

1. A systems-language host: the evaluator and loader ported from the
   Rust crate of the value-representation prototypes.
2. Lean and Geb: accelerations bound by position or builtin
   identifier, each proved in Lean against the denotation of the term
   it replaces, with the shadow mode that runs both.
3. Geb: compilers to the targets Phase 2 selects, emitting Lean first;
   the optimized compiler compiles itself.

Acceptance: both hosts reach the same image fixed point, and the
compiler emitting Lean reaches the fixed point on emitted Lean.

## Phase 6: content identity

1. The node-digest rule, the hash function and its version tag, if
   Phase 3 did not fix them.
2. Geb: the hash, compared with known answers from the host binding.
3. Geb: the migration from positions to digests, the namespace tree,
   and the re-keying of annotations.

Acceptance: a rename leaves every digest unchanged, a changed
dependency changes the digests of its dependents, and running the
migration twice changes nothing.

## Phase 7: the metalogic

1. Lean: the rule set of the section on the metalogic and its
   soundness, without `Classical.choice`, checked in a Boolean and a
   non-Boolean model. This step depends only on Phase 1 and may proceed
   in parallel with Phases 2 to 6.
2. Geb: the proof checker, a fold over proof objects, compared with
   the Lean checker on valid and malformed certificates.
3. Geb: proofs about Geb programs, the elaborator's components first;
   stronger checkers admitted by relative soundness proofs; then the
   richer definitions, equation blocks, guarded blocks and presheaf
   signatures, and the constructive fragment of the Lean and Idris
   developments that the libraries consume.

Acceptance: a theorem with hypotheses, a substitution and an induction
checks, and certificates with altered binders, invalid dependencies or
false conclusions fail.

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

The target artifacts must agree, `C1(S) = C2(S)`, and so must the
executable ones, `C2 = C3`; the second comparison needs a reproducible
host build as well as deterministic output. Maps are ordered
explicitly, and timestamps, random identifiers and absolute paths are
excluded from every artifact that carries identity. Bytes are compared,
not digests. A change of `S`, of the options or of a dependency starts
a new test.

A fixed point does not prove the compiler correct, prove the checker
sound, or remove the host's runtime from the trusted base; the Lean
proofs and the independent route remain. Self-hosted here means that
Geb's implementation is written in Geb and compiled by Geb; a native
backend without Lean is a separate milestone.

{includeLiterate "." Geb.Prototypes.Kernel.Basic "The kernel" (level := 1)}

{includeLiterate "." Geb.Prototypes.Kernel.Reader "The kernel's readable syntax" (level := 1)}

{includeLiterate "." Geb.Prototypes.Bootstrap "A computation-certificate prototype" (level := 1)}
