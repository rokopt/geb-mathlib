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
import Geb.Prototypes.GoedelT
import Geb.Prototypes.Definition
import Geb.Prototypes.FreeTopos
import Geb.Prototypes.PartialHorn
import Geb.Prototypes.Computability.Triage.Simulation

/-! # Bootstrap chapter

The design record for bootstrapping Geb: the decisions that fix the
seed, a survey of how other languages and proof checkers bootstrap,
the plan, each of its parts with an executable acceptance condition,
and the statement of what self-compilation establishes.
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
how other languages and proof checkers bootstrap, and the plan, each
of whose sections ends with an executable acceptance condition.
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

Each item opens with its state, one of the five the section on status
defines: complete, in progress, ready, waiting or deferred. Each names
the section or file that details it, and the items of a list are in the
order of dependence.

## The bootstrap's end point

* Computation. Geb's implementation, the reader, the expansion, the
  type checker and the compilers, is written in Geb and compiled by Geb,
  with the host code reduced to the seed, and every compiler reproduces
  itself (the section on what self-compilation establishes); the
  bootstrap's programs carry elementary-affine decorations that a
  checker and a search written in Geb check and find
  ({ref "choice-of-machine"}[The choice of machine]). Complete on the
  Lean host but for the decorations, which are in progress.
* Hosts and targets. The kernel runs on three hosts or targets: Lean,
  where the seed and the backend emitting Lean are; a systems language,
  Rust, where a second seed reproduces the fixed points; and an
  interaction-net runtime running the staged interaction system of the
  choice of machine, which a compiler written in Geb targets for
  parallel workloads. Complete for Lean; the
  systems language and the interaction-net runtime wait on
  {ref "choice-of-machine"}[the choice of machine].
* Logic. One checker, proved sound in Lean and written again in Geb,
  the checker written in Geb proved in Lean to agree with it, and a
  prover in Geb whose tactics construct its derivations: the
  metalogic's, the free topos with the natural numbers, list and
  rose-tree objects, presented as the initial model of one partial Horn
  theory, whose developments mix the Mitchell–Bénabou language's
  derivations with the combinators' certificates ({ref "logic"}[The
  logic]). Kernel
  programs are reasoned about through their translation into the
  language, sound by a theorem in Lean. In progress: the checker and the
  translation are constructed in Lean and proved sound, the proofs
  about the compiler's components are made in the language, and the
  checker, the translation, the prover, its tactics and the combinator
  prover are written in Geb and proved in Lean to agree with their Lean
  prototypes.
  The checker of Gödel's T, the equational theory of the kernel's terms,
  constructed and written in Geb first, is retired: equations between
  kernel programs are proved in the metalogic
  ({ref "functional-relations"}[Functional relations and the checker of
  Gödel's T]).
* Extension. A program is extended by definitions whose identity
  survives edits, and the datatype language is complete enough to write
  the rest of Geb in, with diagnostics that name what fails. In
  progress: closed bundles and the datatype language are complete, and
  content identity is ready.

## The bootstrap

Computation:

* Complete. The seed ({ref "kernel-in-lean"}[The kernel runs in Lean]):
  the kernel's syntax, its type checker
  and evaluator, the primitives and the reader, with numeral
  abbreviations for labels. The reader's printer and the retraction law
  between them are ready.
* Complete. {ref "definitions-and-images"}[Definitions and images]:
  closed bundles, the image
  format and the host driver `geb-kernel`. The names of bound variables
  and comments beside a bundle are ready.
* Complete. {ref "geb-grows-in-itself"}[Geb grows in itself]: the
  stage-0 compiler in the kernel's syntax, the datatype language's
  expansion, the stage-1 compiler written in the datatype language, and
  their fixed points.
* Complete. The Lean backend ({ref "speed-and-second-host"}[Speed and a
  second host]):
  `bootstrap/stage1/lean.geb`, the committed `bootstrap/compiler.img`
  and `bootstrap/lean/GebBoot.lean`, and the executable `geb-compile`.
* Ready. The datatype language's completion
  ({ref "datatype-completion"}[The datatype language's completion]),
  before substantial authoring:
  datatype names as types distinct from the type of trees, checked at
  every use, a datatype reaching the trees only through its
  representation and its decoding by its generated recognizer, both
  written explicitly; type parameters checked opaquely; the soundness of
  the typing, proved with the prover in Geb; patterns with `&`, unused
  pattern variables, primitives that no binding shadows, emitted names
  that no definition captures, and diagnostics naming the definition that
  fails.
* Ready. The first stage of the interaction-net arm of
  {ref "choice-of-machine"}[the choice of machine]: a kernel program's
  interaction system, duplicating no λ-value, with a sequential reducer
  in Lean and the proof that its read-back is the denotation.
* Deferred until before the second host.
  {ref "choice-of-machine"}[The choice of machine]: the benchmark
  programs, the environment machine, the compilation to
  the triage calculus, native code with forks over a node's children,
  the staged interaction system, and the decision.
* Waiting on the choice of machine. The second host
  ({ref "speed-and-second-host"}[Speed and a second host]): the evaluator
  and loader in Rust, reproducing the stage-0 and stage-1 fixed points,
  which is diverse double-compiling across hosts.
* Ready. Accelerations ({ref "speed-and-second-host"}[Speed and a
  second host]): native code bound by position
  or builtin identifier, proved in Lean against the denotation and run
  in shadow mode.
* Waiting on the choice of machine. The interaction-net target
  ({ref "speed-and-second-host"}[Speed and a second host]): a
  compiler written in Geb to the staged interaction system of the
  choice of machine, run on a runtime pinned to a revision and tested,
  within the limits on duplicating λ-values of the section on
  operational semantics; HVM4 serves as an external back end for
  measurement and for searching certificates.
* In progress. Elementary-affine decorations of the bootstrap's
  programs ({ref "choice-of-machine"}[The choice of machine]): each
  program typable with first-order data copied natively, its decoration
  found by an untrusted search and checked in the build by a checker
  specified in Lean and written in Geb; then a search written in Geb,
  which full self-hosting requires; and later, elementary affine logic
  without the exemption. The search with z3, `scripts/eal/eal.py`, is
  constructed, and the rest is ready.
* Ready. The Geb reader and serializer in constant depth, and the stage
  tests run by the compiled executables, the section on improvements.

Logic ({ref "logic"}[The logic]), Gödel's T and then the metalogic, as
the sections below detail:

* Gödel's T over rose trees, the equational theory of the kernel's
  terms:
  * Complete. The rules and their soundness in Lean, and the checker
    written in Geb, with its prover begun; both are retired, equations
    between kernel programs being proved in the metalogic, and their
    proofs remain and are checked.
  * In progress. The proofs about the compiler's components: those of
    the prelude's lists and labels and of the checker's accessors, in
    Gödel's T, are complete; the rest are proved in the metalogic, about
    the components' translations, the type checker's preservation of
    types by weakening and by substitution and the datatype language's
    expansion's identity on programs of kernel forms complete, and the
    reader's inverse to the printer waiting on the printer.
* The metalogic, the free topos in one presentation:
  * Complete. The rule set with its checker in Lean, sound, and the
    proof that every model is an elementary topos with the data
    objects, with its converse ({ref "rule-set-models"}[The rule set and
    its models]).
  * Complete. The model in Lean with functional relations
    ({ref "functional-relations"}[Functional relations and the checker of
    Gödel's T]), with a model of the theory from a topos with chosen
    structure and the data objects, Lean's
    functions as graphs in it, and the bridge from mathlib's elementary
    toposes.
  * Complete. The definitional extension with its unfolding theorem,
    for the models ({ref "definitional-extensions"}[Definitional
    extensions and shared certificates]). The unfolding of certificates
    is ready.
  * Complete. A prover prototyped in Lean, and with it the measurement
    that decides when the Mitchell–Bénabou language is written, both
    criteria failing ({ref "when-mb-written"}[When the Mitchell–Bénabou
    language is written]).
  * Complete. Certificates over a store of shared terms, checked with
    the typing of their terms inferred.
  * Complete. The Mitchell–Bénabou language's terms, compilation and
    definitions, with the proof that compiling agrees with unfolding in
    every model, the laws of its renaming and substitution, and the
    benchmark's theorems stated in it.
  * Complete. Its derivations of equations, its logical rules, and its
    connectives, comprehension and description, each with its checker
    proved sound.
  * Complete. Its types built in, the mixing of the two presentations
    and its completeness ({ref "mb-types-mixing-completeness"}[Types
    built in, mixing and completeness]), in order:
    * Complete. The arrow a functional relation determines, a definition
      of the combinators; binary coproducts and the initial object; and
      rose trees over a type of labels, with induction on rose trees.
    * Complete. Citations between the two checkers: a derivation of the
      language citing a certificate of the combinators, and a
      certificate citing a theorem of the language, in a development
      of declarations of both kinds.
    * Complete. Definitions of the language and primitive arrows
      declared in a development, each confirmed by its compilation, by
      the checker's inference, or by a certificate that may cite the
      theorems before it.
    * Complete. Object definitions declared in a development: objects
      of the combinators in object parameters, which name types of the
      language.
    * Complete. Quotient types: the coequalizer of a relation's
      projections, with its rules.
    * Complete. The partial Horn logic's term model and completeness
      theorem, the completeness of the language citing certificates,
      and the round trips of the compilation.
  * Complete. The choice whether Gödel's T keeps its own checker: its
    measurement, the translation's soundness, and the decision, to
    retire the checker of Gödel's T.
  * Complete. The checker written in Geb, the language's completeness
    having settled its rules, compared with the Lean checker at the
    developments of the language's tests and at variants of each
    ({ref "logic"}[The logic]).
  * Complete. The translation of kernel programs written in Geb and
    proved in Lean to agree with the Lean translation: its translations
    of a program, of a translated program's constants and of a theorem
    of Gödel's T, at every input, are the Lean translation's.
  * Complete. The checker's prover, its tactics and the combinator
    prover written in Geb, each proved in Lean to agree with its Lean
    prototype, so that the provers written in Geb construct exactly the
    derivations and certificates the Lean provers construct.
  * Complete. The proof in Lean that the checker written in Geb agrees
    with the Lean checker: its denotation, at every development, is the
    Lean checker's result, by the method of the checker of Gödel's T
    ({ref "logic"}[The logic]).
  * Ready. Stronger checkers admitted beside it by relative
    soundness, each by a translation of its certificates into the
    metalogic's derivations ({ref "metalogic-and-checker"}[The
    metalogic and its checker]). Two are required by the bootstrap: the
    checker with a step of conversion to a normal form under named
    rules, the evaluation of primitives at literals among its rules, and
    the checker of holes, admitted beside it
    ({ref "the-next-phase"}[The next phase]). The checker of the shared
    certificates, by unsharing, is required if measurement shows the
    checking or storage of certificates to need it, and follows the
    bootstrap otherwise.

Extension:

* Complete. Closed bundles referring to definitions by position
  ({ref "definitions-and-images"}[Definitions and images]).
* In progress. {ref "content-identity"}[Content identity]: identifiers as
  CIDs whose multihashes are of BLAKE3, and their codec; its input,
  recorded in
  `docs/definitions.md` § Content identity; the hash written in Geb and
  compared with a host binding; the migration from positions to
  digests, the tree of modules and the re-keying of annotations.
* Ready. The syntaxes of {citet RFC9804}[] and the Geb authoring profile,
  reading into one document type with proved retractions, and the
  importer from the present syntax
  ({ref "rfc9804-syntaxes"}[The syntaxes of RFC 9804]); and a printer for
  the kernel's terms with the retraction law, the section on
  improvements.
* In progress. {ref "authoring-compatibility"}[Authoring across bootstrap
  revisions]: preservation of source documents, bindings and dependency
  references through format changes. Checked filling of one contextual
  term hole in Lean, source documents keeping comments as decorations with
  their retraction and formatter, adopted over `bootstrap/`, and the
  authoring profile read by the seed and by the Geb reader, rejecting
  duplicate and reserved names, with quoted atoms in the sources, are
  complete, as are the canonical and basic transport encodings of the
  strict encodings of RFC 9804 with their retraction. Ready, in the order
  of {ref "authoring-sequence"}[the sequence]: the printer of the advanced
  encoding, modules with parameters,
  imports and export lists, the datatype language's completion, manifests
  with editions and the record of
  elaborated definitions, a durable document with versioned profiles,
  hygienic elaboration with explicit assembly and diagnostics, the markup
  of comments with documentation as literate pages, and the `geb` editor
  language; then, early in writing, `let*` and `cond`, the
  syntax of holes, the checker of holes in programs in its suspending
  form and the display of their obligations, located diagnostics and the
  typed enumerator. The rest, the store, a language server, holes in
  proofs and the Geb-native refinement search among it, waits on its
  consumers.

## After the bootstrap

Every item waits on the bootstrap. Each is written in Geb, and each
proof in the metalogic, a proof about programs being about their
translations:

* The setoid language: quotients whose respect is proved, subset types by
  propositions, definitions by equations whose unique solution is
  proved, and dependent products of families, each a construction of
  the metalogic's topos.
* Internal universes and internal category theory: the universe of
  datatypes, whose codes are their recognizers as elements of `2^T`, and
  the universe of subobjects of the trees, with codes in the power object
  `Ω^T`, each interpreting a code by membership; internal categories
  carried by subobjects of the trees, a category and one of its objects
  forming a parameter of an ordinary type; and the conversion of code
  generic over opaque type parameters into code over a universe, by the
  logical functor the generic family determines. No universe interprets
  every object of the free topos, truth being undefinable
  ({citet Tarski1935}[]). {ref "datatype-completion"}[The datatype
  language's completion] details both.
* The richer forms of definition of `docs/definitions.md`: well-founded
  and guarded blocks, presentations, presheaf signatures, and a binding
  language with its substitution laws; modules precede them, before
  substantial authoring
  ({ref "modules"}[Modules]). Their Lean
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
* Theorems about the metalogic proved in it: the equivalence of the
  free topos with the rose-tree object and the free topos with a natural
  numbers object; and the extraction of programs from proofs of
  totality, through a realizability topos.
* A theorem about Gödel's T, conjectured: its category of contexts
  under equational hypotheses is a cartesian closed locos. A locos
  is a finitely complete category with stable disjoint finite coproducts
  and parameterized list objects ({citet Cockett1990}[]), in the terms
  of {citet Maietti2010}[], Definition 2.5, a lextensive category with
  parameterized list objects; Maietti states Cockett's formulation of
  the list objects, by recursive objects that the pullback functors to
  the slices preserve, equivalent to hers. In a cartesian closed
  category a list object is parameterized, by currying, as a natural
  numbers object is ({citet Maietti2010}[], Section 2), and as
  {name}`Geb.FreeTopos.listRec_param_exists` constructs the parameterized
  fold in a model of the metalogic's theory. The kernel's
  types include no coproducts, and the conjecture rests on their
  construction from the others (the section on Gödel's T).
* The Mitchell–Bénabou language's terms inside the combinators' terms,
  the direction of the two presentations' mixing that the bootstrap
  leaves; and the language's own term model, of its provably functional
  relations after {citet LambekScott1980}[], proving its rules complete
  without citations of certificates, with the isomorphism of its
  quotient types and the objects of equivalence classes that power
  objects construct.
* A backend without Lean, a milestone separate from the bootstrap (the
  section on what self-compilation establishes).

# Decisions

The following are fixed; the plan builds on them.

* Proofs. During the bootstrap, correctness proofs are Lean proofs:
  the kernel's evaluator is proved to agree with the kernel's
  denotation, and every codec with its decoder. The proof checker for
  the metalogic is a Geb program written after Geb compiles itself,
  and its soundness proof stays in Lean: the Lean checker is proved
  sound, and the denotation of the checker written in Geb is proved in
  Lean to agree with it, a proof without which the bootstrap is not
  complete.
* Kernel. The kernel language is Gödel's System T
  {citep Goedel1958}[] over rose trees: simple types built from the
  single base type of rose trees by products, function types and lists,
  the constructors and destructors of rose trees, and folds whose
  result may be of any type, one whose step sees the leaf of a node's
  label and one whose step sees the node itself. Every program terminates,
  and its denotation is
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
  the comparison of {ref "choice-of-machine"}[the choice of machine],
  run on the same kernel programs.
* Layers. Above the kernel, the language grows in three layers. The
  datatype language is computational: named datatypes whose
  constructors and structural
  recursion are derived from their declarations, case analysis,
  functions with result types, type parameters instantiated at
  elaboration, and quotients only by computable normal forms. A datatype
  is the initial algebra of its declaration, a type distinct from the
  type of trees, reaching them only through its representation, the
  unique algebra morphism into them, and its decoding by its recognizer;
  generic code is a module parameterized by an interface, a theory, and a
  model of it instantiates the code, so that abstraction needs no
  construct of its own. Its types
  denote objects of the category of recognized types over the functions
  the kernel defines, which has finite limits and finite coproducts;
  that category has no subobject classifier for propositions about
  programs (the necessity theorem of `Geb/Prototypes/Typechecker/`'s
  classifier module), so logic is not a construct of the datatype
  language. The metalogic ({ref "logic"}[The logic]) holds propositions
  and their proofs about kernel programs, equations between them among
  the propositions, stated of the programs' translations into its
  internal language. The setoid language, built on it, adds subset
  types by arbitrary
  propositions, quotients whose respect for their relation is proved,
  and definitions by equations whose unique solution is proved; it is
  the setoid completion of the datatype language with its obligations
  discharged in
  the metalogic. Type parameters are instantiated at elaboration
  because the polymorphic λ-calculus has no set-theoretic model, which
  the kernel's denotation in Lean types requires.
* Datatypes. The datatype language's completion precedes substantial
  authoring, entire: datatype names as exact types checked at every use,
  the representation and the decoding written explicitly where they are
  used, generated recognizers, type parameters checked opaquely, and the
  soundness of the typing, proved with the prover in Geb
  ({ref "datatype-completion"}[The datatype language's completion]).
  Type parameters are sorts through the bootstrap. After it, among the
  first work written in Geb, category theory is internalized and type
  parameters become parameters over internal universes defined from the
  topos's structure, the datatypes' codes in `2^T` and the subobjects' in
  `Ω^T`, each interpreted by membership; no universe interprets every
  object.
* Concrete syntax. Geb specifies its abstract syntax, rose trees, and
  not a concrete syntax. Source is written in the syntaxes of
  {citet RFC9804}[]: its canonical encoding and the transport encoding of
  it, for exchange, hashing and signing; its advanced encoding; and a Geb
  authoring profile, the advanced encoding with line comments, UTF-8 and
  line breaks in quoted strings, numerals as bare runs of digits, `&` as a
  token, and `?name` for the form `(hole name)`. All four read into one
  document type, which keeps comments and empty lines, and each printer is
  a section of its parser, so conversion among them preserves the
  document, and the four share code as far as their grammars allow
  ({ref "rfc9804-syntaxes"}[The syntaxes of RFC 9804]). Identifiers are
  its tokens, and a name beyond ASCII is a quoted atom in Unicode's
  normalization form C. The strict printers write numerals and `&`
  quoted, `"0"` and `"&"`. A hole is the form `(hole name)` in every
  syntax, `(hole name T)` giving an expected type. The present sources'
  syntax, the kernel reader's, is converted into the authoring profile.
  In a quoted datum, an atom that is not a numeral contributes the leaves
  of its bytes to the list it is in, so `(quote (0 let))` is
  `(quote (0 108 101 116))`.
* Annotations. Every annotation of source is a decoration of the rose
  trees read: each node carries, beside its atom or list, a value of a
  decoration type, and the decorated trees form the cofree recursive
  comonad on the rose functor ({citet UustaluVene2011}[]), whose
  redecoration computes one decoration from another. The reader
  decorates each node with its trivia, the comment lines and the empty
  line before it, and a list also with the comment lines before its
  closing parenthesis; which definition a comment documents is a
  redecoration of the trivia into the vocabulary of annotations, a
  function of the trees read, outside reading and printing. The
  vocabulary is versioned and extensible, a field it does not know being
  kept. What changes elaboration is not a decoration: erasing every
  decoration leaves the elaborated core unchanged
  ({ref "documents-annotations"}[Documents and annotations]).
* Identity. A reference to a definition is, once content identity
  exists, a CIDv1 ({citet RatajBerjon2026}[]) in the definition's
  payload, of the codec `raw` until a code for Geb's blocks is
  registered, whose multihash ({citet BenetSporny2023}[]) is of BLAKE3
  ({citet OConnorAumassonNevesWilcoxOHearn2020}[]), multicodec `0x1e`
  in the table of {citet Multiformats2026}[], where its status is draft;
  a linker gives the kernel positions in place of the CIDs, so the
  kernel is unchanged; the version of the CID and the codes of its codec
  and its hash make
  every identifier self-describing, so a later hash or codec is a new
  identifier and not a new format. Names are decorations: the name a
  definition is declared under, and the name written at a reference to
  it, decorate the declaration and the reference, whose identity is the
  CID alone ({ref "content-identity"}[Content identity]).
* Layout. The formatter writes a list that fits on one line on it;
  otherwise the list's elements fill the first line while they fit, the
  parentheses that close after them included, and each remaining element
  begins a line of its own, indented past the list's opening parenthesis
  by two columns after an atom at its head and by one otherwise, none
  hung on the current line ({ref "source-documents"}[Source documents and
  the formatter]).
* Conversion. Until the bootstrap completes, no source is kept unchanged
  for its own sake: whatever is preferable is adopted everywhere, every
  source converted to it, and the languages admit exactly what the
  mathematics states, without implicit coercions or silent
  conversions.
* Modules. Code is organized in modules, block forms `(module M …)`
  independent of files and not reopened. A module's header is a
  telescope of parameters and imports in the order of their dependence,
  followed by an export list, which may re-export imported definitions; a
  block without one exports nothing. An import supplies every parameter
  of the module it imports, a parameter of the importer passing through
  any left open; `(import M)` brings names in unqualified, a clash being
  rejected, and `(import M as N)` qualified alone. Every definition in a
  module takes all of its parameters, a module's body being one structure
  over the context they form; declarations keep parameters of their own,
  supplied where they are used. A parameter may take a named telescope,
  an abbreviation of its entries, declared as `(interface I entries…)` and
  taken as `(parameter (m I))`, its entries then named `m.x`. The rest of
  an enclosing body refers to the exports of a nested module without
  parameters of its own by qualified name, and uses a nested module with
  parameters through an import in a later module's header
  ({ref "modules"}[Modules]).
* Documentation. The markup of comments and documentation is Verso's,
  with the role `{name}` for Lean constants and a role `{geb}` for Geb
  definitions, and documentation renders as literate pages generated from
  Geb source, not as docstrings in the emitted Lean
  ({ref "documentation"}[Documentation]).
* Editor. The editor is a `geb` language with Mike's Paredit as the
  structural editor; parinfer is optional, through the `geb` extension
  ({ref "editing"}[Editing]).
* Metalogic. The metalogic is the free topos with the inductive types
  the bootstrap uses, natural numbers and rose trees, and its
  equivalence with the free topos with a natural numbers object is
  proved in Geb. It is presented at once, as the initial model of one
  partial Horn theory of an elementary topos with the data objects
  ({ref "metalogic"}[The metalogic]), and no classical logic is an
  intermediate step. Kernel programs enter it through their translation
  into its internal language, the Mitchell–Bénabou language. Gödel's
  T over rose trees, the equational theory of the kernel's terms of
  every type, whose rules are the laws of a cartesian closed category
  with the data objects, since the kernel's programs have function
  types, preceded it, and its checker is retired
  ({ref "functional-relations"}[Functional relations and the checker of
  Gödel's T]).
* Stronger checkers. The bootstrap requires two: first the checker with
  a step of conversion to a normal form under named rules, the evaluation
  of primitives at literals a family of its rules, and second the checker
  of holes, admitted beside the first. The checker of shared certificates
  becomes a requirement only if measurement of checking or storing cached
  certificates calls for it, and is otherwise an early item after the
  bootstrap ({ref "the-next-phase"}[The next phase]). The checker of holes
  in programs is written now, in Lean, in the suspending form with
  explicit work items and a budget, to be transcribed into Geb and proved
  to agree ({ref "typed-holes"}[Typed holes]).
* Libraries. The prover's public contract is any checked certificate of
  the statement, behind an abstraction clients may check or cite but not
  inspect; exact agreement with the Lean prover is a milestone of the
  bootstrap, not a promise to clients
  ({ref "compatibility-contract"}[The compatibility contract]).
* Canonical. Canonical is a dependency of the package for experiments,
  removed once everything done or planned with it is written, or
  writable, in Geb ({ref "search-synthesis"}[Search and synthesis];
  `TODO.md` § Triggers).
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
[conversion of a repository from SHA-1 to
SHA-256](https://git-scm.com/docs/hash-function-transition),
and it is safe because nothing without a digest has an identity to
preserve. It fails on a missing dependency rather than substituting a
placeholder, recomputes each digest before rewriting, and gives the
same result when run twice. Names, comments and per-node digests are
annotations kept in one table per bundle, keyed by vertex, never
inside a hashed object; at the migration a key splits into the digest
of the enclosing definition and a vertex inside it. The
value-representation chapter selects BLAKE3
{citep OConnorAumassonNevesWilcoxOHearn2020}[] and the repository's
survey of concrete syntaxes names SHA3-256; the decision on identity
reconciles them, BLAKE3 in the multihash of a CID, which names its
hash, so a later change of hash is a new identifier. A digest locates a payload and never creates
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
checker for the metalogic can be. Two more parts cover how source and
its annotations are kept and edited across changes of format, and how
holes in programs and proofs are reported and filled by search. A last
part maps the prior art in this repository and the experimental one.

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
choice of machine ({ref "choice-of-machine"}[The choice of machine])
cannot invalidate it; it carries a version header,
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
triage arm of {ref "choice-of-machine"}[the choice of machine] needs.

## Operational semantics

Four candidates run the kernel, and
{ref "choice-of-machine"}[the choice of machine] compares them on the
same programs.

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
any interaction system, and interaction nets reduce with the one-step
diamond property, so that every reduction to normal form has the same
length and the number of interactions is a cost independent of the
schedule {citep Lafont1997}[]. Their parallelism is the reason to
consider them. The symmetric variant, whose two annihilations both
connect auxiliary ports straight, is equally expressive and has a
relational semantics for which it is fully complete
{citep Mazza2007}[] {citep Mazza2009}[], a semantics against which a
read-back could be stated.

Evaluating λ-terms by optimal reduction needs Lamping's bookkeeping,
the oracle {citep Lamping1990}[] {citep AspertiGuerrini1998}[].
Without it, the abstract algorithm is sound and complete for the terms
typable in elementary or light affine logic, its duplicators indexed as
the typing assigns {citep BaillotCoppolaDalLago2011}[], and it is not
sound for System T: the simply typed term
`(λn.(n λy.(n λz.y)) λx.(x (x y)))` of base type reduces under it to a
cycle, which is no λ-term {citep CoppolaMartini2006}[]. That term uses
an iterator twice, once inside the argument of the other use, a
pattern that the kernel's folds at function type can form. Elementary
affine logic captures the elementary functions
{citep DanosJoinet2003}[], and System T defines functions that are not
elementary, so no elementary-affine typing certifies every kernel
program; typability is decidable {citep CoppolaMartini2006}[], so it
can certify programs one at a time. Duplication of first-order data is
not restricted. [HVM4](https://github.com/HigherOrderCO/HVM4) labels
its duplicators by their occurrences in a program's source, every
instance of a definition sharing its labels, not as a typing assigns,
so the theorem does not cover it, and it normalizes the twice
combinator applied to itself to three applications instead of four
([HVM4 issue 22](https://github.com/HigherOrderCO/HVM4/issues/22)).
Optimal sharing is also not efficiency: the cost of implementing the
parallel β-steps that optimal reduction counts is not bounded by any
elementary function of their number {citep AspertiMairson2001}[], and
closed reduction, which copies only closed terms and shares less, was
measured more efficient than optimal reduction in many cases
{citep FernandezMackieSinot2005}[].

Bend's first version, a high-level language, ran on HVM2, which adds
native agents for numbers to the combinators, emulating arithmetic by
Church or Scott numerals being too slow, and has a single duplicator,
sound only for programs in which no higher-order λ that copies its
variable is itself copied, an invariant it leaves to the source
language to check. Its paper
proposes an elementary-affine inference, with Lamping's bookkeeping as
a fallback about ten times slower, as future work
{citep Taelin2024}[].

The value-representation chapter records the state of the
interaction-net runtimes and their measurements: a fold over a tree of
$`2^{20}` leaves took about a second on HVM2 with sixteen threads and on
HVM4 with one, where Lean's compiled code folds at about 42 nanoseconds
per node. As a compilation
target, a net runtime needs its own contract: well-formedness of
graphs, interfaces, reduction, read-back, and preservation of the
source's observations. A tree can serialize a graph by storing node
and port references, and sharing, erasure and duplication in a net are
operational structure, distinct from the sharing of immutable pointers
in a rose-tree runtime. [HVM2](https://github.com/HigherOrderCO/HVM2)
and HVM4 implement different calculi with different interfaces, so each
is a separate target, pinned to a revision and tested before any step
depends on it. HVM4's repository carries no licence, nor does that of
the calculus it implements, so neither's code nor text can enter this
repository, only the published rules of the calculus, re-derived and
cited; HVM1 and HVM3 are licensed MIT, and HVM2 and both versions of
Bend Apache-2.0.

Ownership-based native code. Bend's second version, which succeeds the
first, runs on no interaction net, and gives up optimal reduction of
shared redexes for sequential code at native speed, flat memory and a
cost model a programmer can read {citep Taelin2026BendRT}[]. Its type
theory makes running code affine: a variable is used at most once
unless its type is of kind `Data`, whose values hold labels, pairs and
proofs of equality and no function, a list being of kind `Data` when
its elements are, and a definition calls itself only on smaller
arguments. Since the paradoxes of a type of all types and of datatypes
negative in themselves each copy a function, the theory admits both
and is consistent; termination and consistency are proved in one Lean
file, and the cost of evaluation has no bound, Ackermann's function
being typable {citep Taelin2026BendTT}[]. The runtime compiles a
program to one C file that runs sequentially, on threads and on a GPU.
Affinity makes the match that consumes a value the place that frees it,
so there is no collector; reference counts exist only for the types a
whole-program analysis finds shared, and an argument a callee only
reads is lent without a count. Parallelism is a fork of calls the
program marks, dealt to a fixed grid of task rings without work
stealing, on the program's promise, unverified, that its forks split
the work evenly. On one machine the sequential build runs within 0.8 to
1.5 times the time of the same programs written in C, sixteen threads
run 8.8 to 12.1 times faster than one, and a GPU runs up to 67 times
faster on uniform work and slower than sixteen threads on divergent
work {citep Taelin2026BendRT}[]. Its speed of compilation, as its
[README](https://github.com/bendlang/bend/blob/018751270e800bc222a93dad7f257083ee53a5f7/README.md)
states, is that of its checker, which checks in under a second files
that proof assistants take minutes over, while compiling to native code
through a C, Metal or CUDA compiler is slow and not incremental.

Its discipline, copying data and never a function, is the first stage
of the staged interaction system of
{ref "choice-of-machine"}[the choice of machine], stated as a type
system of the source language where that stage obtains it by
defunctionalization, and the folds the elementary-affine checker
rejects for reading their children's results twice are rejected by it
too. The Lean backend already has the memory half of the design, the
reference counting of Lean's runtime {citep UllrichDeMoura2019}[], and
the kernel's fold offers the fork: the results of a node's children are
independent of each other, so a fold may compute them in parallel. This
target needs no discipline on λ-values; the elementary-affine
decorations keep a target with optimal sharing available beside it.

The evidence points to an environment machine as the reference and to
two parallel targets for measured parallel workloads: ownership-based
native code with forks over a node's children, and an interaction
system staged by how it duplicates λ-values, its first stage
duplicating none; {ref "choice-of-machine"}[the choice of machine]
decides.

## The metalogic and its checker
%%%
tag := "metalogic-and-checker"
%%%

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
the initial model of a partial Horn theory ({ref "metalogic"}[The
metalogic]). The equational logic of the kernel's terms, whose judgments
are equations between kernel terms of a type under hypotheses, is a
variant of Gödel's T whose rules are the laws of a cartesian closed
category with list objects and a rose-tree object, since the kernel's
programs are terms of System T, whose types include function types (the
section on Gödel's T); its checker was implemented first, and is retired
({ref "functional-relations"}[Functional relations and the checker of
Gödel's T]). The kernel's types, function
types included, are objects of the metalogic, and the datatype
language's recognized types are subobjects of the type of trees there, cut out by
their recognizers.

A kernel program enters the metalogic by its translation into the
Mitchell–Bénabou language, compositional in the kernel's term formers,
whose soundness is a theorem in Lean: the translation of a kernel term
represents its denotation ({name}`Geb.FreeTopos.Translation.repC_term`),
so that an equation between kernel terms whose translation the checker
proves holds of their denotations at every represented value of its
context ({name}`Geb.FreeTopos.Translation.translation_sound`). The
translation need not be full or faithful: the free topos has arrows
between natural numbers that no System T term defines (below), and it
proves equations between programs that the kernel's equational logic
does not. A
proposition about kernel programs is therefore stated of their
translations and proved in the metalogic.

Relative soundness takes two forms. One checker is admitted beside
another of the same judgments when a Geb program translates each
certificate the first accepts into one the second accepts with the same
conclusion. The condition is a proposition about kernel programs under
the hypothesis that the first checker accepts, so both checkers are Geb
programs, the second the metalogic's checker written in Geb
({ref "logic"}[The logic]); it is proved in the metalogic,
about the programs' translations, by induction on certificates; the
checkers' results are functions of the context and the hypotheses, so
the proposition is stated of functions, and its induction hypothesis
covers the contexts and hypotheses of the premises, as the type
checker's preservation of types by substitution is proved (the section
on Gödel's T). That a checker is sound, every certificate
it accepts valid, is a statement about the denotation of kernel terms,
which no kernel term computes (below); it is stated in the metalogic,
whose topos has System T's evaluator, and no checker proves itself
sound, which would prove its own consistency.

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

A checker whose rules are explicit makes its certificates long, and two
systems answer that cost in opposite ways. Milawa's first checker,
Level 1, accepts only primitive steps; each later level accepts derived
rules of inference as single steps, up to Level 11, whose single step
replays a proof skeleton of its tactics. A command switches the kernel
to a new checker once the current one has accepted its fidelity claim,
that whenever the new checker accepts a proof, a Level 1 proof of the
same conclusion exists; the claim is proved through builders, functions
that construct the lower-level proof of a step, each with theorems that
the proof has the step's conclusion and that the lower level accepts it
(Sections 4.5 and 12.1 of {citet Davis2009}[]). The levels exist
because fully expansive proofs of the tactics' soundness were too large
to construct: one lemma's proof has 3681 megaconses and checks in 11440
seconds at Level 1, and 0.8 megaconses and 12.6 seconds at Level 11, and
the construction of a Level 1 proof of another exhausted 32 gigabytes
(Section 12.11 of {citet Davis2009}[]). Trusting Level 11 requires
trusting Level 1 alone, and the kernel, the switch included, is proved
sound down to the machine code that runs it {citep DavisMyreen2015}[].
Metamath Zero instead keeps its verifier fixed: the verifier and the
specification file are trusted, the proof file is untrusted input whose
format is designed to be checked fast, each term constructed once so
that equality is identity of references, an untrusted front end does
the search, and the proofs of other systems enter by translation
(Sections 1.4, 3 and 5 of {citet Carneiro2019}[]). CakeML applies its
verified compiler, a function in the logic of HOL4, to itself, and so
obtains a verified machine-code implementation of the compiler
{citep KumarMyreenNorrishOwens2014}[], a bootstrap inside a logic where
Geb's fixed points are a bootstrap outside one.

Geb takes both courses, in turn. During the bootstrap its checker is
extended in Lean, each extension proved sound there, and its
certificates are made compact as Metamath Zero's are, each term stated
once in a store and cited by its index: the certificates over a store of
shared terms and the checker that infers their typing
({ref "definitional-extensions"}[Definitional extensions and shared
certificates]) are checked by a Lean
checker proved sound there, not admitted. The developments that mix the
language's derivations with the combinators' certificates cite
certificates in their plain form
({name}`Geb.FreeTopos.Internal.checkDev`), and the proofs about programs
cite none, so the checker written in Geb decides the plain form, and
the shared form reaches Geb by admission rather than by a second proof
of agreement in Lean. Once the
metalogic's checker is written in Geb, Geb admits stronger checkers as
Milawa does, by relative soundness: the translation of a stronger
checker's certificates is the counterpart of Milawa's builders, and the
proposition proved about it in the metalogic is the counterpart of the
fidelity claim, which Milawa states as the existence of a Level 1 proof
and Geb as the translation's result. A stronger checker is stronger in
the steps it accepts, not in its theory: every conclusion it accepts is
one the metalogic derives, so its theorems are the metalogic's, and a
new principle is the other kind of extension (below). An admission adds
no proof in Lean
and nothing to what is trusted, which is why it is the course after the
bootstrap, when the rest of Geb is written in Geb. An admitted checker
is sound as far as the checker it is admitted beside: the proposition
holds of the programs' denotations by the translation's soundness at
the types of first order it is stated at, functions of data; and the
metalogic's checker written in Geb is sound through its agreement with
the Lean checker, which the checker in Geb ({ref "logic"}[The logic])
tests on valid and
malformed certificates and proves in Lean, of the Geb checker's
denotation, the counterpart of Davis and Myreen's proof that Milawa's
kernel is faithful to its logic. No checker proves
itself sound, which would prove its own consistency: Milawa's levels
prove their fidelity to Level 1, not its soundness, and the metalogic's
soundness proof stays in Lean.

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

## Source and its tools
%%%
tag := "source-tools"
%%%

A formatter that keeps comments reads them as data. The lossless syntax
trees of Roslyn and of rust-analyzer's rowan
([syntax trees](https://github.com/rust-lang/rust-analyzer/blob/master/docs/book/src/contributing/syntax.md))
keep comments and whitespace as items in document order rather than as
annotations of the nodes after them, as does
[rewrite-clj](https://github.com/clj-commons/rewrite-clj), on which the
Clojure formatters cljfmt and zprint are built; gofmt and ormolu keep at
most one empty line between items.

{citet RFC9804}[] specifies three encodings of S-expressions: a canonical
encoding, designed for hashing and signing; a basic encoding for
transport, which is the base-64 of the canonical one; and an advanced
encoding for people. It is an Informational RFC, not on the standards
track, and requires an implementation to support the first two, the
third being optional (§ 6). Its atoms are octet strings with optional
display hints, which an implementation may exclude (§ 8), and canonical
lengths count bytes. An advanced token is a letter or one of
`- . / _ : * + =` followed by letters, digits and those marks, so it
cannot begin with a digit, and a digit begins a length only when `:`,
`"`, `#` or `|` follows it. Quoted strings admit printable ASCII alone: a
line break or any other byte is escaped (`\n`, `\xhh`, `\ooo`) or
continued by a backslash before the break. The advanced grammar has no
comments (§§ 4, 7.1).

Two arrangements keep a program's annotations beside its code. In the
first, text is primary, comments are data in it, and the separation into
core and annotations is derived when reading, so that editors, diffs,
merges, reviews and searches need nothing new.
[Clojure's metadata](https://clojure.org/reference/metadata) does not
affect equality or hashes;
[Dhall](https://docs.dhall-lang.org/discussions/Safety-guarantees.html)
hashes a normal form without comments; and
[Yatima](https://github.com/argumentcomputer/yatima-lang-alpha)'s
`Term::embed` separates a nameless tree for the content identifier from a
tree of names of the same shape, and its `unembed` rejoins them and fails
when the shapes differ. Darklang returned from a structure editor to text
as the source of truth
([status update](https://blog.darklang.com/an-overdue-status-update/)).
In the second, core and annotations are two independently authoritative
artifacts, with text as a projection: Unison, Lamdu, MPS, and Unison's
design of 2019, not built, of comments keyed by a hash and a path
([unison#443](https://github.com/unisonweb/unison/issues/443)). They need
atomic updates, detection of stale annotations and coordinated merging.
Keys by path move under edits, as Go's comment map's do
([golang/go#20744](https://github.com/golang/go/issues/20744)); keys by
hash conflate structurally equal definitions
([unison#462](https://github.com/unisonweb/unison/issues/462)); Unison
drops comments inside terms when they are added to its codebase
([language reference](https://www.unison-lang.org/docs/language-reference/comments/),
[unison#6262](https://github.com/unisonweb/unison/issues/6262)) and
removed its metadata links
([unison#4574](https://github.com/unisonweb/unison/pull/4574)).

A content identifier names an algorithm and the bytes it hashes. A
multihash names an algorithm and a digest; it neither versions a schema
nor specifies the bytes hashed, and a CID also names the codec of the
block hashed ([IPLD primer](https://ipld.io/docs/intro/primer/)). Unison
separates names from identity, refers to a member of a recursive
component by the component's hash and an index
([hashes](https://www.unison-lang.org/docs/language-reference/hashes/)),
and pins a dependency in source by a digest literal, `#…`.

A language whose reader changes records the version a source is written
for, as Racket's `#lang`, Rust's editions and Go's `go` directive do.
Agda's parameterized modules abstract every definition of a module over
the module's parameters, and an import instantiates them
([Agda's module system](https://agda.readthedocs.io/en/latest/language/module-system.html)).
Isabelle's locales are parameterized by assumptions as well as by
constants, each interpretation discharging the assumptions
{citep Ballarin2014}[].

The following was determined for VS Code on 2026-09-29.

* Bracket pairs are coloured without an extension
  (`editor.bracketPairColorization.enabled`, the default since version
  1.67); brackets inside comments are skipped only when a TextMate grammar
  marks the comment as one
  ([bracket pair colorization](https://code.visualstudio.com/blogs/2021/09/29/bracket-pair-colorization)).
  A language configuration and a small TextMate grammar are declarative
  features and need no language server
  ([language extensions](https://code.visualstudio.com/api/language-extensions/overview)).
* [Mike's Paredit](https://marketplace.visualstudio.com/items?itemName=MikeDelmonaco.paredit)
  (`MikeDelmonaco.paredit`, MIT) extracts Calva's structural operations
  (navigation, selection, slurp, barf, raise, splice, transpose, wrap,
  kill), is independent of language, takes delimiters per language
  (`paredit.customDelimiters`) and reads the comment configuration of a
  language's extension. It had 29 installations.
  [strict-paredit](https://github.com/ailisp/strict-paredit-vscode)
  (`ailisp.strict-paredit` 0.3.1) fixes the languages it serves
  (`commonlisp`, `clojure`, `lisp`, `scheme`), and Calva's paredit serves
  Clojure only.
* The parinfer extensions (`shaunlebron.vscode-parinfer` 0.6.2 and its
  forks) fix their languages likewise. The library
  [parinfer.js](https://github.com/parinfer/parinfer.js), npm package
  `parinfer` 3.13.1, exposes `parenMode` and `indentMode` over whole texts
  and treats `[`, `]`, `{`, `}` as parentheses, `"` as a string delimiter
  and `\` as an escape, so atoms containing them break it.
* `sjhuangx.vscode-scheme` supplies a grammar and language configuration
  for `scheme`, and `pucelle.run-on-save` runs a command on saving a file.
  Whether `emeraldwalk.RunOnSave` can run commands of VS Code is not
  verified.

Paredit and parinfer are alternative models of editing the same balanced
text. Paredit's commands change the tree explicitly and keep parentheses
balanced by construction, whatever the layout. Parinfer infers while one
types, and depends on layout: Indent Mode infers parentheses from
indentation, so it changes the tree by design and is an operation of
editing, never a formatter; Paren Mode infers indentation from
parentheses and never changes the tree. Their invariant is that each
continuation line is indented beyond the innermost open parenthesis and
not beyond a parenthesis closed at the end of the line before
([parinfer](https://shaunlebron.github.io/parinfer/#mathematical-foundation)).
Paren Mode would serve as a formatter, but its equations are stated
properties, not proofs for a given grammar.

Tree-sitter is an incremental concrete-syntax parser that recovers from
errors ([introduction](https://tree-sitter.github.io/tree-sitter/)); it
helps selection and incomplete buffers independently of a language
server. VS Code offers no user-extensible tree-sitter highlighting,
having experimental grammars for a few built-in languages only
([vscode#50140](https://github.com/microsoft/vscode/issues/50140) is
open); [tree-sitter-vscode](https://github.com/AlecGhost/tree-sitter-vscode)
highlights with a supplied grammar through semantic tokens, and Neovim,
Helix, Zed and Emacs 29 use tree-sitter natively. tree-sitter-scheme is
licensed MIT. [efm-langserver](https://github.com/mattn/efm-langserver)
turns a checker on the command line into diagnostics, with a generic
client for VS Code. A language service needs source spans and structured
diagnostics, lookup of definitions, inferred and expected types, and the
obligations of holes
([language-server guide](https://code.visualstudio.com/api/language-extensions/language-server-extension-guide));
the protocol transports those services between a checker and an editor,
and does not store or rebuild annotations. Whether clojure-lsp reports
errors on `.geb` files is not verified.

## Holes and search
%%%
tag := "holes-and-search"
%%%

A hole of type `A` in a context `Γ` is a metavariable `u :: A[Γ]`
occurring as `clo(u, id_Γ)` {citep NanevskiPfenningPientka2008}[]. Their
Theorem 4.6 translates such a metavariable into an ordinary variable of
type `B₁ → … → Bₘ → A`, instantiation being substitution followed by β:
holes are lambda-lifted variables, and in a cartesian closed category a
term with a hole is a morphism out of the exponential `[Γ ⇒ A]`, by
functional completeness {citep LambekScott1986}[]. Hazelnut studies typed
editing states, incomplete terms included
{citep OmarVoyseyHiltonAldrichHammer2017}[]; Hazelnut Live assigns a hole
its type in checking mode (rule EAEHole), and filling commutes with
evaluation (Theorems 4.1 and 4.2) {citep OmarVoyseyChughHammer2019}[]. The
free Σ-monoid over presheaves on contexts characterizes metavariables,
metasubstitution being the monad's bind {citep FioreHur2010}[]
{citep FioreSzamozvancev2022}[]. An Isabelle proof state with subgoals
`ψ₁ … ψₙ` is the theorem `[ψ₁, …, ψₙ] ⇒ C`, the subgoals lifted over their
parameters, and admits nothing {citep Paulson1989}[], unlike an axiom
such as Lean's `sorryAx`. That a derivation with open subgoals is a
derivation under the hypotheses `∀Γ_h. φ_h` in a topos's internal
language follows from the rules introducing `⇒` and `∀`; a statement of
it in the literature was not located.

The universal property of the fold turns the synthesis of a recursive
function from examples into the synthesis of its non-recursive step
{citep Hutton1999}[] {citep FeserChaudhuriDillig2015}[]
{citep OseraZdancewic2015}[]. Equality saturation records explanations of
the equalities it derives {citep WillseyNandiWangFlattTatlockPanchekha2021}[].
cvc5's SyGuS interface restricts candidates by a grammar
([example](https://cvc5.github.io/docs/latest/examples/sygus-fun.html),
[SyGuS 2.1](https://arxiv.org/abs/2312.06001)). A topos interprets
existential quantification through images, without sections of every
epimorphism
([Borceux, *Some flavours of topos theory*, §§ 3.5, 4.4–4.5](https://www.uclouvain.be/system/files/uclouvain_assetmanager/groups/cms-editors-irmp/Lecture%20Notes.pdf)),
so a derivation of an internal existential statement is not an executable
witness.

SupGen searches by shared enumeration. Its mechanism, from its two gists
([60d3bc72](https://gist.github.com/VictorTaelin/60d3bc72fb4edefecd42095e44138b41),
[7fe49a99](https://gist.github.com/VictorTaelin/7fe49a99ebca42e5721aa1a3bb32e278))
and the public sources of [HVM4](https://github.com/HigherOrderCO/HVM4):
given a type, helper functions and equations between inputs and outputs,
the candidates form one term with a labelled superposition at each
choice; the interaction rules for applying and duplicating
superpositions share every computation independent of a choice; failed
tests erase branches; and a breadth-first collapse reads the survivors
back. This is pull-tabbing {citep Antoy2011}[] with the pruning of partial
candidates of Lazy SmallCheck {citep RuncimanNaylorLindblad2008}[], shared
under optimal reduction. SupGen's source is not published and HVM4 has no
licence; Bend 2, launched without it, states that it has no tactics or
proof search. Its reported speeds are not reproduced independently, and
its programs recurse through `Y`, so they need not be total. Material for
a bounded experiment exists:
[HVM3](https://github.com/HigherOrderCO/HVM3)'s
[enumerator of affine λ-terms](https://github.com/HigherOrderCO/HVM3/blob/fba2e9c82faf6e2f019c9ecea94c32f19a8b7820/examples/enum_lam_smart.hvm),
which bounds the depth of binding and the arity of application, and its
[type-directed enumerator](https://github.com/HigherOrderCO/HVM3/blob/fba2e9c82faf6e2f019c9ecea94c32f19a8b7820/examples/enum_coc_smart.hvm),
both needing adaptation of their discipline of contexts and grammar of
candidates to Geb; and the
[SupVM gist](https://gist.github.com/VictorTaelin/7ae3d262e4d0b80a4e8817a80f976a68),
a small evaluator in TypeScript for a stated subset of HVM, representing
correlated labelled choices by a map, which is neither a specification nor
a verification of HVM.

Canonical is a solver for type inhabitation in dependent type theory
{citep NormanAvigad2025}[]
([paper](https://drops.dagstuhl.de/storage/00lipics/lipics-vol352-itp2025/LIPIcs.ITP.2025.14/LIPIcs.ITP.2025.14.pdf);
talks by Chase Norman,
[1](https://www.youtube.com/watch?v=y6p0hHkabXs) and
[2](https://www.youtube.com/watch?v=Me7WFEvoksw)).

* Its format is that of the Logical Framework
  {citep HarperHonsellPlotkin1993}[] without universes, with let
  definitions carrying reduction rules.
* Every term is β-normal and η-long, with one constructor,
  `λ x̄. let ȳ := M̄. f Ā`, and the type of a symbol determines its arity.
* A search refines one metavariable at a time. It chooses a head from the
  metavariable's local context and creates fresh metavariables for the
  head's arguments, all at once, so that they may be refined in any order
  and a later argument, a proof for instance, can constrain an earlier
  one, the witness it is about.
* Terms carry explicit substitutions, so an equation between partial
  terms is found violated as soon as its head symbols differ, and the
  branch is abandoned.
* Metavariables with a rigid equation are refined first, as unit
  propagation in SAT.
* Iterative deepening bounds a measure it calls entropy, estimated from
  statistics of earlier refinements, and branches are searched in
  parallel.
* The algorithm is Dowek's complete method {citep Dowek1993}[] with this
  representation.
* On the Natural Number Game it proves 62 of 74 statements in 51 seconds
  in all, against 27 for Aesop and 45 for Duper, with shorter proofs.
* Its future work names forward reasoning and the invention of lemmas and
  tactics as absent. Canonical produces cut-free proofs.

Canonical-min {citep NormanAvigad2026}[] is a reference implementation in
185 lines of Lean
([repository](https://github.com/chasenorman/Canonical-min), cited here at
revision `72a24f13ec2e6ff3150e609cb5edbc70ef59a236`).

* Its type checker for dependent type theory runs in a continuation
  monad. Meeting an unassigned metavariable, the checker stores the rest
  of the check as a constraint on that metavariable, and continues the
  independent checks of other arguments (`judgment`); assigning the
  metavariable resumes it.
* The search is iterative deepening over assignments of heads, favoring
  rigid constraints and otherwise later arguments, and raising both a
  bound on the size of terms and a heuristic budget.
* On DTTBench, 31 problems from Lean's library needing β-reduction only,
  with a timeout of 60 seconds, it solves 31. Twelf solves 8, sauto 6 and
  Mimer 2.
* Its search is written with `partial` functions, so being Lean source
  proves neither soundness nor completeness of the search; and its tactic
  wrapper imports Canonical itself for preparing premises, translation and
  reconstruction of proofs.

Canonical is available under the MIT licence: the solver in Rust with the
Lean tactic ([Canonical](https://github.com/chasenorman/Canonical),
[CanonicalLean](https://github.com/chasenorman/CanonicalLean)), released
for each Lean version with precompiled libraries for three platforms, the
latest for Lean v4.34.0 on 2026-09-27. Outside Lean it reads a problem in
an undocumented JSON form. A mode for program synthesis, in which an
equation stuck on the major argument of a recursor counts as stuck rather
than violated (§ 3.3.1 of the paper), is absent from the released tactic.
A stuck check is not a failed one, `natRec z s ?n = z` becoming true when
`?n` is zero, so a search claiming completeness over its grammar keeps
stuck branches that remain viable. The paper's encoding of Lean (§ 4)
erases universes; it is not a foundation for Geb, whose final checker
stays the boundary of acceptance.

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
  is superseded by the partial Horn presentation
  ({ref "presentation"}[The presentation]).
* `InteractionNets.lean` evaluates Lafont's combinators with maximal
  parallel steps and no proofs; it is the starting point of the
  interaction arm of {ref "choice-of-machine"}[the choice of machine],
  after a well-formedness invariant for its
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

Each part of the plan is marked by where it lives: the Lean seed, Geb
code, or a comparison whose output is a decision. Each section below
ends with an executable acceptance condition, and every part retains a
runnable fixture, the source that regenerates it, and its input and
output contract.

## Status

The state of every part of the plan is one of five:

* complete: constructed, and its acceptance met;
* in progress: begun and not complete;
* ready: not begun, and depending on no part that is not complete;
* waiting: not begun, and depending on a named part that is not
  complete;
* deferred: not begun, by a decision that names when it is taken up.

A section of the plan is complete when its acceptance is met; the parts
it leaves are listed beside it, each with its own state. The road map at
the head of the chapter marks its items by these states, and each
section below opens with a table of the states of its parts.

:::table +header
*
  * Section
  * State
  * What remains, and its state
*
  * {ref "kernel-in-lean"}[The kernel runs in Lean]
  * Complete
  * The reader's printer and the retraction law: ready
*
  * {ref "choice-of-machine"}[The choice of machine]
  * Deferred until before the second host
  * The first stage of the interaction-net arm: ready; the
    elementary-affine decorations: in progress; the rest: deferred
*
  * {ref "definitions-and-images"}[Definitions and images]
  * Complete
  * The names of bound variables and comments: ready; the hash binding:
    deferred to content identity
*
  * {ref "geb-grows-in-itself"}[Geb grows in itself]
  * Complete
  * The datatype language's completion
    ({ref "datatype-completion"}[The datatype language's completion]):
    ready
*
  * {ref "speed-and-second-host"}[Speed and a second host]
  * In progress
  * The second host and the interaction-net target: waiting on the choice
    of machine; accelerations: ready
*
  * {ref "content-identity"}[Content identity]
  * Ready
  * Every part
*
  * {ref "authoring-compatibility"}[Authoring across bootstrap revisions]
  * In progress
  * Checked contextual-hole filling, source documents with their
    formatter, the formatter's adoption, the authoring profile read by the
    seed and the Geb reader, and the canonical and basic transport
    encodings: complete; the advanced encoding's printer and the rest of the
    sequence: ready, but the parts that follow their consumers, which wait
    on them
*
  * {ref "goedel-t"}[Gödel's T]
  * In progress
  * Weakening, substitution and the identity of the datatype language's
    expansion: complete; the reader's inverse to the printer: waiting on
    the printer
*
  * {ref "metalogic"}[The metalogic]
  * In progress
  * The Mitchell–Bénabou language's completeness, the model of functional
    relations and the retirement of the checker of Gödel's T: complete;
    the checker and the translation written in Geb and the proofs of
    their agreement: complete; the prover, its tactics and the
    combinator prover written in Geb and the proofs of their agreement:
    complete; stronger checkers: ready
:::

The fixed points hold on images and on Lean. The seed builds the
stage-0 compiler, written in the kernel's syntax, and the stage-0
compiler builds the stage-1 compiler, whose expansion of the datatype
language is written in the datatype language and which also emits Lean;
each, run by the Lean
evaluator from its image, compiles its own source to that image. Built
by Lake from the Lean it emits from its own source, the stage-1
compiler emits the same Lean and the same image. The stage-1 compiler's
image and its Lean are committed, and continuous integration checks
every fixed point on every build.

The implementation changed the plan in these respects. The kernel's
terms and types are rose trees read directly, and its checker and
evaluator are one fold whose results are Lean closures, so no machine
is needed before the first fixed point and the choice of machine left
the critical path. The kernel gained lists, case analysis of lists and the
logarithm of a label, each for a cost measured on the bootstrap's own
programs. And the representation of rose trees tabulates a node's
children in an array, without which a fold over a wide node, such as a
file, takes quadratic time.

## The kernel runs in Lean
%%%
tag := "kernel-in-lean"
%%%

:::table +header
*
  * Step
  * State
*
  * The syntax, the type checker and evaluator, the primitives
  * Complete
*
  * The reader
  * Complete; its printer and the retraction law are ready
*
  * Acceptance
  * Met
:::

* Lean: the kernel's syntax. Terms and types are rose trees read
  directly, the label of a node naming its constructor, so a program
  is a value of the language and needs no separate syntax type: de
  Bruijn variables, abstraction over a domain type, application, the
  unit value, pairs and projections, quoted trees, a conditional on
  whether a label is non-zero, lists with their right fold
  ({name}`Geb.Kernel.foldrDen`) and their case analysis
  ({name}`Geb.Kernel.lcaseDen`), which the fold alone gives only in
  time linear in the list, the fold of trees, the fold whose step sees
  the node, and iteration at given result types, primitives and
  references by index; the types `T`, `1`, products, functions and lists.
  A tree is a label with a list of trees, and the fold's step receives
  the leaf of a node's label and the list of its children's results
  ({name}`Geb.Kernel.foldDen`), so the fold is the recursion of the
  carrier itself; the second fold's step receives the node itself and the
  same list ({name}`Geb.Kernel.paraDen`), so that a recursion needing a
  node's subtrees need not rebuild them from its results. Lists are in
  the kernel because a node is built from
  the list of its children: building a node one child at a time copies
  the children at each step, which on a node of many children, a file
  of bytes among them, takes quadratic time, while a list of children
  is built in linear time and tabulated once.
* Lean: the type checker and the evaluator are one paramorphism,
  {name}`Geb.Kernel.infer`, returning a term's type together with its
  denotation, or nothing when the term is ill-typed: `T` denotes
  {name}`Geb.RoseTree`, the fold denotes {name}`Geb.RoseTree.elim`,
  and a well-typed term denotes a Lean function
  ({name}`Geb.Kernel.Ty.den`). The evaluator agrees with the
  denotation by construction. The term is traversed once and its
  meaning is a Lean closure, so running a program is compiled Lean
  code rather than an interpretive loop.
* Lean: the primitives {name}`Geb.Kernel.prims`, on labels and
  children: a node's label, arity and child by index; a node from a
  label and a list of children, and the list of a node's children;
  arithmetic and comparison of labels; equality of trees; and the
  base-two logarithm of a label, without which a label's bit length
  would need as many steps of iteration as the label's value. The
  table is only extended, and its members are chosen by what the
  reader, substitution and the checker need.
* Lean: the reader. A program is a sequence of named definitions in
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

## The choice of machine
%%%
tag := "choice-of-machine"
%%%

:::table +header
*
  * Step
  * State
*
  * The stages of the interaction-net arm
  * Complete
*
  * The first stage in Lean, its read-back proved to be the denotation
  * Ready
*
  * The benchmark programs, the arms, the measurements
  * Deferred until before the second host
*
  * Acceptance
  * Not met
:::

* The benchmark programs, written once in kernel S-expressions: a fold
  over a balanced tree of $`2^{20}` leaves, as the value-representation
  chapter measures; a comb and a node of many children; labels beyond
  a machine word; a reader over a megabyte of bytes; the kernel
  evaluator written in the kernel, with a step bound; a normalizer and
  type checker for simply typed terms; and the higher-order terms that
  probe the oracle-free fragment.
* The arms: an environment machine derived from the denotation, with
  fold frames given by dissections and a proof that it agrees with the
  denotation, and a bounded runner that resumes to the same result; a
  compilation of the kernel to the triage calculus by bracket
  abstraction, run by the repository's machine; native code with
  ownership-based memory and forks over the children of a node, the
  design of Bend's runtime {citep Taelin2026BendRT}[] grown from the
  Lean backend; and the interaction system below, at its first stage.
  Every result is compared with the denotation.
* Measurements: agreement, host lines, proof lines, steps and time per
  leaf, memory and its reclamation, and speedup with threads, one heavy
  process at a time. The decision on the reference machine and the
  compilation targets is recorded in this chapter.

Acceptance: the measurements and the decision are recorded.

The interaction-net arm is staged by how it duplicates λ-values, each
stage adding one family of agents whose correctness has a published
proof, and each program running at the highest stage it qualifies for
(the section on operational semantics gives the reasons):

1. The first-order kernel. A program becomes an interaction system of
   its own: its closures defunctionalized into first-order data with
   one agent that applies them, one agent for each occurrence of a
   fold, with a rule for each constructor
   {citep MackiePintoVilaca2009}[], and the nodes of rose trees as
   agents whose labels are attributes, which data and conditional rules
   admit with one-step confluence kept {citep Sato2024}[]. No λ-value is
   duplicated, only
   data, which a copying agent copies constructor by constructor, so
   every kernel program runs, and the work under a copied closure is
   repeated in each copy.
2. λ-values in the net, a function copied only once it is closed: a
   linear System T that iterates only closed functions is, under closed
   reduction, as powerful as System T
   {citep AlvesFernandezFloridoMackie2010}[]. This stage's proof of
   correctness is to be written; the other route to a machine for
   linear System T, a token machine of the geometry of interaction, can
   be exponentially slower than an environment machine on higher-order
   programs {citep AccattoliDalLagoVanoni2021}[].
3. Duplicators indexed by the depths of an elementary-affine typing,
   for the programs a typing certifies, which reduce with optimal
   sharing {citep BaillotCoppolaDalLago2011}[]; the other programs run
   at the second stage. The labels come from the typing: no result
   supports labels chosen otherwise, by the nesting of recursors for
   instance, and HVM2's single label fails on Church numeral two applied
   to itself {citep Taelin2024}[], a term the discipline types.
4. Superpositions of candidates, for searching certificates. The
   checker re-checks what a search returns, so a runtime without a
   proof of correctness costs a search completeness or time, never
   soundness. A search gains from sharing only with a checker that
   produces a rule's conclusion before checking its premises and reads
   each subtree of a certificate once, and with the labels forked at
   each child position of a node, siblings otherwise being entangled. A
   superposed term denotes a family of values indexed by assignments to
   its labels, as choice identifiers do in pull-tabbing
   {citep Antoy2011}[], and a correctness statement would say that
   collapsing its normal form returns that family, which no source
   states. Whether shared evaluation outperforms a lazy, pruning
   enumerator {citep RuncimanNaylorLindblad2008}[] is measured before
   this stage is built.
5. Realizers extracted from the metalogic's proofs, after the
   bootstrap. They are untyped, so they run at the second stage:
   closed reduction evaluates them correctly and without optimal
   sharing {citep FernandezMackieSinot2005}[], and optimal sharing for
   them needs the oracle. Realizability over the geometry of
   interaction is established {citep AbramskyHaghverdiScott2002}[];
   whether closed nets under application form a partial combinatory
   algebra is not settled.

The machine runs kernel programs. The metalogic's terms are data that
its checker, a kernel program, reads, and are not executed, so no stage
needs optimal reduction of the metalogic, whose functions are not all
System T's. Nor does the kernel's strength bear on the machine's
correctness, which the first stage has for all of System T; an
elementary-affine discipline decides where the third stage applies.

The first stage's prototype in Lean is the interaction system of a
kernel program, a sequential reducer on the configurations of the
calculus of interaction nets {citep FernandezMackie1999}[], its names
allocated explicitly so that each step is a function, read-back at the
type of trees, and the theorem that for
every closed program from trees to trees and every input the reducer
reaches a normal form whose read-back is the denotation
{name}`Geb.Kernel.infer` assigns, by a logical relation between
configurations and denotations observed at trees. A second milestone is
the one-step diamond property up to renaming of cells and wires, the
cells indexed by `Fin k` so that renamings are permutations and the
quotient is decidable: it extends the theorem to every schedule, by
mathlib's `Relation.church_rosser` or CSLib's
`Relation.Diamond.to_confluent`, so that a parallel runtime is covered.
De Falco's presentation of nets by partial permutations, with strong
confluence proved on paper, is the algebraic alternative to indexed
cells {citep DeFalco2010}[]. A later milestone proves a data structure
in close correspondence with the calculus, as in
{citet HassanMackieSato2015}[], to refine the reduction of nets.

Elementary-affine typability was measured on the programs by
`scripts/eal/eal.py`, over the definitions `lake exe geb-defs` writes
from an image, with an inference in the style of
{citet CoppolaMartini2006}[], linear constraints on the numbers of boxes
solved by an SMT solver, and with first-order data exempted from the
discipline, since duplicating data duplicates no λ-value. One at a
time, 197 of the stage-0 compiler's 200 definitions are typable, 313 of
the stage-1 compiler's 315, 359 of the prover of Gödel's T's 368 and
370 of the metalogic checker's 374; without the exemption, 187, 296,
342 and 363. Every definition that
fails, among them the type checker `typeIn` and the resolver `resolve`,
is a fold at pairs of a subtree and a function whose step reads the
list of its children's results more than once, contracting a list of
functions. A step that reads the list once contracts none, and on
folds into functions of an argument is typable in some forms only: a
step that applies the first child's function by case analysis, or that
composes the children's functions into one by a right fold and returns
that function, is typable, and a step returning a closure over the
argument that loops over the children's functions is not, the right
fold's list of functions needing a box that the closure's body cannot
give it. The serializer's `treeBits`, which pairs its children's count
with the composition of their results, takes the composing form, and
`scripts/eal/examples.defs` holds the four shapes. Typing a whole program with
one decoration per definition fails for three of the four programs, so
a program's typing needs a decoration per use of a definition. The exemption is not proved sound
for a net machine; the third stage needs it, and the first two need no
typing.

The bootstrap's programs, its compilers, checkers and prover, and its
reader and printer once they are written in Geb, are required to be
typable in this discipline, first-order data copied natively and the
fold whose step sees the node among the primitives that copy it, so
that the third stage can run them with optimal sharing. A program's
decoration is a certificate. A search finds it and is not trusted, and
a checker checks it and is, which is the rule for every solver the
bootstrap uses: `scripts/eal/eal.py` is the search, with z3 as its
solver, and checking a decoration is checking linear inequalities
between given numbers, which needs no solver. The steps, in order: a
decoration per use of a definition, each use taking a fresh copy of the
linear constraints that describe the definition's decorations, all of
which the constraints on its simple principal type schema yield
{citep CoppolaMartini2006}[]; the rewriting of the folds that read their
children's results twice; a checker of decorations specified in Lean
and written in Geb, the checker written in Geb proved in Lean to agree
with it by the method of the metalogic's checker, and the check in the
build of every program's committed decoration, the checker's own among
them; and a search written in Geb, which full self-hosting requires so
that no external solver regenerates a decoration. An inference in
polynomial time given a simple type derivation
{citep BaillotTerui2005}[], for a system without sharing or
polymorphism, is the search's starting point, extended to the kernel's
constants, and its verdicts are compared with those of the search that
uses z3.

A stricter requirement is a later step: elementary affine logic
without the exemption, to which the published soundness of the
oracle-free algorithm applies as proved. The fold whose step sees the
node cannot be defined in it, since its step receives the node whose
children its recursion also consumes, so that step replaces that fold
by a fold whose step receives the node under a box, or proves the
native copying of data sound.

Deferred: images are kernel terms and the Lean evaluator runs compiled
closures, so the choice of machine matters for the second host and the
backends, not for the first fixed point; the comparison runs before
the second host ({ref "speed-and-second-host"}[Speed and a second
host]).

## Definitions and images
%%%
tag := "definitions-and-images"
%%%

:::table +header
*
  * Step
  * State
*
  * The closed bundle
  * Complete
*
  * The annotation table
  * In progress: the names of definitions are kept; those of bound
    variables and comments are ready
*
  * The image and the host driver
  * Complete
*
  * The hash binding
  * Deferred to {ref "content-identity"}[Content identity]
*
  * Acceptance
  * Met
:::

* Lean: the closed bundle, a well-founded block of kernel definitions
  stored as a rose tree and linked through the reference node,
  evaluated by one fold over its order. {name}`Geb.Kernel.bundle`
  stores a program's definitions beside the table of their names, and
  {name}`Geb.Kernel.runEntry` loads a bundle by
  {name}`Geb.Kernel.load` and applies its named definition; a
  reference to a definition that is not earlier fails to load, so a
  loaded bundle is well founded.
* Lean: the annotation table of names and comments, keyed by vertex.
  Names of definitions are kept in the bundle; names of bound
  variables and comments are not yet kept.
* Lean: the image, a header of a magic number, a version and a bit
  count, followed by the word-level form of the interleaved wire
  format without sharing ({name}`Geb.Kernel.writeImage`). Its reader
  {name}`Geb.Kernel.readImage` rejects a wrong magic number or
  version, truncation, trailing data and non-zero bits beyond the
  count. The host driver, the executable `geb-kernel` over
  {name}`Geb.Kernel.Command.run`, builds an image from a program's
  source and runs an image's named definition on a file, presented as
  the tree whose children are the leaves of its bytes. The word-level
  codec agrees with the list form by test, not by proof.
* Lean: the host binding of the selected hash, if the
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

## Geb grows in itself
%%%
tag := "geb-grows-in-itself"
%%%

:::table +header
*
  * Step
  * State
*
  * The libraries and serializer, the reader, the type checker, the
    elaborator, and its self-compilation
  * Complete; the datatype language's completion is ready
*
  * Acceptance
  * Met
:::

* Geb: libraries of lists, bytes and text, label operations and tree
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
* Geb: the reader, from bytes to trees with name resolution, accepting
  exactly the syntax the seed reader accepts, abbreviations included.
  The Lean reader remains as the independent route.
* Geb: the kernel type checker, compared with the Lean one on valid
  and malformed fixtures.
* Geb: a minimal elaborator in kernel S-expressions: named variables,
  definitions, and signature declarations whose constructors,
  recognizers and folds are derived generically. `bootstrap/datatype.geb`
  expands the forms of the datatype language into kernel S-expressions
  before the
  reader resolves them: a datatype declaration, whose values are erased
  to trees, the node labelled by a constructor's position over its
  fields, a last field taking the remaining children; case analysis,
  exhaustive unless it has an else clause; structural recursion at a
  result type, the kernel's fold whose step sees the node, at a
  suspended result, the clause's fields taking the children's suspended
  results in order, so that no clause is evaluated at the subtrees of
  fields that are not recursive and no subtree is rebuilt; and functions
  with result types. A program of
  kernel forms alone expands to itself, so the fixed point holds with
  the expansion in the compiler. Recognizers, type parameters and a
  static check of datatypes are the datatype language's completion
  ({ref "datatype-completion"}[The datatype language's completion]); the
  expansion refers to some primitives by name, so a program does not
  rebind them around case analysis and structural recursion.
* Geb: the elaborator rewritten in the datatype language it accepts,
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

The stage-1 compiler is the stage-0 compiler with the expansion of the
datatype language rewritten in the datatype language,
`bootstrap/stage1/datatype.geb`:
datatypes for optional trees, S-expressions and declarations, case
analysis and structural recursion in place of tests of labels and folds,
and functions with result types, computing the same function of a
program's forms. The seed cannot read the datatype language, so the
stage-0 compiler
builds its image; run from that image, the stage-1 compiler compiles its
own source to the same image, of about sixteen kilobytes, in 0.61
seconds on one machine, and the image it produces reproduces itself.
`GebTests/Prototypes/Stage1.lean` checks this fixed point and the
agreement of the two compilers on the programs in the datatype language
and the
kernel's examples on every build. The rewrite needed neither generated
recognizers nor type parameters, which the datatype language's
completion adds before substantial authoring. The stage-0 sources remain
the independent route from the seed.

### The datatype language's completion
%%%
tag := "datatype-completion"
%%%

State: ready.

The sources annotate every value of a declared datatype as `T`:
`bootstrap/free-topos/partial-horn.geb` declares `(data Eqn (eqn T T))`,
and functions over optional trees take `(m T)`. The expansion of the
datatype language ignores the types of fields. Which datatype a value is
meant to belong to is therefore recorded nowhere, and it is information
no tool recovers later. The layers of the decisions make the datatype
language's types denote recognized types instead, a datatype being the
subset of trees its recognizer accepts, a subobject
`{t : T | rec_D t}` of the tree object in the metalogic, whose language
is typed throughout. The completion consists of six parts, all of which
precede substantial authoring:

:::table +header
*
  * Part
  * Content
*
  * Datatype names as types
  * `(m Opt)` rather than `(m T)`, in fields, parameters and results
*
  * Static check at every use
  * Constructors produce `D`, case analysis and structural recursion
    consume `D`, and fields and results are checked; `D` and `T` are
    distinct types, with no implicit conversion between them
*
  * Representation and decoding
  * `D`'s representation `D → T` and its decoding `T → 1 + D`, each
    written explicitly where it is used
*
  * Generated recognizers
  * The kernel program deciding membership in `D`, which decoding and the
    meaning of `D` need
*
  * Type parameters checked opaquely
  * A parameter `X` has no representation; it is instantiated at
    elaboration, as the decision on layers states, with the interface's
    operations passed as values
*
  * Soundness of the typing
  * A checked program maps members of `D` to members of `E`, so that
    typed programs translate into morphisms between subobjects; proved
    with the metalogic's prover in Geb
:::

The types are exactly those of the mathematics. A datatype `D` is the
initial algebra of the polynomial functor its declaration presents: its
constructors are the algebra's structure map, its case analysis the
inverse that Lambek's lemma gives, and its structural recursion the fold.
The encoding of a constructor as the node of its position over its
fields' encodings makes the trees an algebra of the same functor, so
initiality determines the representation `D → T` as the unique algebra
morphism, chosen by no convention; it is a monomorphism, and `D`'s
recognizer cuts out its image. The recognizer decides membership, so the
image is a complemented subobject and decoding `T → 1 + D` is a total
morphism. `D` and `T` are distinct types: a tree operation such as
`label` or `child` applies to a value of `D` only through its
representation, written where it is used, which marks exactly the code
that depends on the encoding. The kernel erases the distinction, the
representation compiling to the identity on trees, and the soundness of
the typing relates the two.

The first five parts are work of the elaborator, a Geb program; the
kernel is unchanged, and the check is outside the trusted base, since a
wrong check can accept an ill-typed program but cannot change a kernel
term's meaning. Every source of the datatype language is retyped
exactly, the metalogic's checker in Geb included; the stage-0 sources,
written in the kernel's syntax, keep the kernel's types, exact for a
kernel whose only type of data is the trees. The soundness theorem lets
a proof use a datatype's type as a hypothesis; it is proved by induction
on the check.

Abstraction is mathematical, not syntactic, and needs no mark of its
own. An interface is a theory, a presentation of operations and axioms
(`docs/definitions.md` § Definitions as presentations). Generic code is
a module over it ({ref "modules"}[Modules]), parameterized by an opaque
type and by the interface's operations, so it holds no reference to a
concrete type and has no representation to inspect. Instantiation is
interpretation by the universal property, evaluation into an
implementation, a model of the theory, as {name}`Geb.Definition.eval` and
{name}`Geb.Definition.derivedAlg` evaluate. In the metalogic this is the
topos generated by the language extended by the interface's constants
and axioms, from which an implementation determines a logical functor,
so a theorem proved of the generic code holds of every instance
{citep LambekScott1986}[]. A certificate is a hypothesis: code using a
proof of a proposition works under it, in the slice over the
proposition's subterminal, and instantiating supplies the proof. The
prover's contract, any checked certificate of the statement, is kept by
clients written so.

Type parameters are sorts through the bootstrap. After it, written in Geb
among the first items, they become parameters over internal universes
(the road map). A universe is a family `El → U`, `U` an object of codes
and `El X` the type the code `X` names. Two are defined from the
exponentials and power objects every topos has {citep MacLaneMoerdijk1992}[],
and interpret a code by membership. Every value is a tree and a datatype
is a complemented subobject of `T`, so the datatypes have codes in `2^T`,
the morphisms `T → 1 + 1`, a datatype's code being the transpose of its
recognizer, with `El X = {t : T | X t = 1}`; and the subobjects of `T`,
the setoid language's subset types of trees among them, have codes in
the power object `Ω^T`, with `El X = {t : T | t ∈ X}`. Internal
categories whose objects and arrows are carried by subobjects of `T`
form an object too, a subobject of a product of power objects, so a pair
of such a category and one of its objects is a parameter of an ordinary
type; using the elements of that object takes an interpretation of the
category in a universe. Code generic over an opaque sort converts to code
over a universe by the universal property above: sending the sort to the
generic family `El → U` is a model of the extended language in the slice
over `U`, which determines a logical functor, so every theorem about the
generic code holds of the converted code {citep LambekScott1986}[].

No universe interprets every object of the topos. The free topos with a
natural numbers object contains arithmetic, and its syntax, being
inductively generated, has codes in it. A family `El` over the codes of
its objects with `El ⌜A⌝ ≅ A` for every closed object `A` would, at the
codes of subterminals, make `Tr c := ∃ e : El c` satisfy `Tr ⌜φ⌝ ↔ φ` for
every closed proposition `φ`. The diagonal lemma gives a `ψ` with
`ψ ↔ ¬ Tr ⌜ψ⌝`, hence `ψ ↔ ¬ψ`, which is contradictory in intuitionistic
as in classical logic; the free topos being non-degenerate, no such
family exists, which is the undefinability of truth {citep Tarski1935}[].
The codes of the whole language are therefore data that a program
constructs and inspects but that no program interprets uniformly, and
each universe interprets a part of the topos. Within their parts `2^T`
and `Ω^T` meet no such limit, since their codes are not syntax: a code is
the subobject itself, an element of an exponential or a power object, and
no step interprets a program's text.

## Speed and a second host
%%%
tag := "speed-and-second-host"
%%%

:::table +header
*
  * Step
  * State
*
  * The second host
  * Waiting on the choice of machine
*
  * Accelerations
  * Ready
*
  * The compilers
  * In progress: the Lean backend is complete; the interaction-net
    target waits on the choice of machine
*
  * Acceptance
  * Met on emitted Lean; the second host's fixed point waits on the
    second host
:::

* A systems-language host: the evaluator and loader ported from the
  Rust crate of the value-representation prototypes.
* Lean and Geb: accelerations bound by position or builtin
  identifier, each proved in Lean against the denotation of the term
  it replaces, with the shadow mode that runs both.
* Geb: compilers to the targets the choice of machine selects, emitting
  Lean first
  and then the staged interaction system for an interaction-net
  runtime; the
  optimized compiler compiles itself. The emitted Lean is
  committed beside the image, each definition under a name derived
  from its Geb name and in the order of the source, so that a change
  of the compiler's source changes the emitted definitions it touches
  and no others.

Acceptance: both hosts reach the same image fixed point, and the
compiler emitting Lean reaches the fixed point on emitted Lean, which
regenerates the committed Lean byte for byte.

What the sections before the choice of machine fix for this one: a
second host implements
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

The Lean backend is constructed. `bootstrap/stage1/lean.geb`
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

`scripts/bench-bootstrap.sh` times both compilers on the compiler's own
source and the prover of Gödel's T on the files of theorems its tests
check, and compares two builds. Byte-identical copies of an executable
were measured to differ in speed by up to a quarter, reproducibly per
copy, a bias of the kind an executable's layout causes
{citep MytkowiczDiwanHauswirthSweeney2009}[]; a comparison timing one
copy per build can therefore report a difference that is only layout.
The script times each build over several copies of its executables,
written independently and rotated across rounds that alternate the
builds' order, and reports each copy's medians beside the whole ones.
Measured so, the fold whose step sees the node made the compiler run
by the Lean evaluator 5 percent faster, the compiled compiler 3 percent
faster and the prover 13 percent faster on the datatype language's
theorems, and made the prover 4.5 percent slower on the theorems about
the type checker, whose source it extends with the new fold's case; on
the same input files the two provers do not differ measurably, nor do
they on the other workloads. Moving the new fold's tests to the ends of
the type checker's and the prover's chains of tests made no measurable
difference.

## Content identity
%%%
tag := "content-identity"
%%%

:::table +header
*
  * Step
  * State
*
  * The identity-bearing payload and the format of identifiers
  * In progress: definitions in Lean
*
  * The node-digest rule, the hash, the migration
  * In progress: in Lean, the linker's relabelling proved; in Geb, ready
*
  * Acceptance
  * Met in Lean; not met in Geb
:::

* The identity-bearing payload and the format of identifiers, frozen
  before durable identifiers are published.
* The node-digest rule, the hash function and its version tag, if
  {ref "definitions-and-images"}[Definitions and images] did not fix
  them.
* Geb: the hash, compared with known answers from the host binding. The
  kernel has no operations on the bits of a word, so the hash written in
  Geb computes BLAKE3's exclusive or, rotations and addition modulo
  `2^32` by arithmetic on natural numbers; an acceleration bound to it
  ({ref "speed-and-second-host"}[Speed and a second host]) makes it fast
  later without changing what it computes.
* Geb: the migration from positions to digests, the tree of modules,
  and the re-keying of annotations.

Acceptance: a rename leaves every digest unchanged, a changed
dependency changes the digests of its dependents, and running the
migration twice changes nothing.

In Lean, `Geb/Prototypes/Kernel/Blake3.lean` is the host binding of the
hash, tested against the official vectors, and
`Geb/Prototypes/Kernel/Identity.lean` defines the varint, the
multihash, the CIDv1 of codec `raw`, the payload
`(geb-def/v1 geb-kernel/v1 (imports …) body)`, the migration and the
linker. A payload's imports are the CIDs of the definitions its body
refers to, each once, in the order of their first references, and its
body refers to them by their positions among the imports. The theorem
`migrate_link` states that the migration of a linked bundle of payloads,
each derived from the payloads before it, gives those payloads back,
and `migrate_idem` that running the migration twice changes nothing;
`GebTests/Prototypes/Kernel/Identity.lean` checks the three conditions
of acceptance on examples and on the stage-0 compiler.

What the sections before the choice of machine fix for this one: the
reference node is
the kernel's constructor of label 23 over a definition's position in
its bundle, which the migration rewrites to a digest; the node-digest
rule is restated for rose trees with natural-number labels; and the
serializer written in Geb, `bootstrap/serialize.geb`, is the model for
the hash written in Geb.

Content identity follows the preservation of authoring information
({ref "authoring-compatibility"}[Authoring across bootstrap revisions]),
and in particular the strict encodings of {citet RFC9804}[], whose
canonical encoding gives the bytes a CID hashes.
The block of `docs/definitions.md` § Content identity is the starting
point of the payload that bears identity:

```
(schema version, semantic profile reference,
 import interface, export layout, definition bodies)
```

The profile fixes primitive identities, binding rules and the
interpretation of the representation; display names and comments stay
outside the payload; types and certificates are inside it when they
affect meaning, and a separately checked certificate of an identified
term is an artifact of its own. The payload's schema and its
interpretation are versioned separately from the hash algorithm.

* An identifier is a CIDv1 ({citet RatajBerjon2026}[]) of an actual
  serialized block, the identity-bearing payload in the canonical
  encoding, with the codec of that block
  ({ref "source-tools"}[Source and its tools]); its multihash
  ({citet BenetSporny2023}[]) is of BLAKE3 (the decision on identity).
  A structural digest of the Merkle kind is not presented as the CID of
  unrelated exchange bytes. The table of multicodecs
  ({citet Multiformats2026}[]) names no code for canonical
  S-expressions. The codec is `raw`, `0x55`, over the canonical bytes,
  until a code registered for Geb's blocks replaces it; `raw` declares no
  links between blocks, and `dag-cbor`, whose links the tools of the
  table's ecosystem follow, would hash bytes other than the canonical
  S-expressions. A change of codec gives new identifiers and no new
  format, the CID naming its codec. The tags of
  `docs/concrete-syntaxes.md` § Structural content-addressing
  specification are not used: the payload is hashed whole, not node by
  node. A local store of canonical blocks suffices at first;
  networking, CAR archives, digests per node and deduplication across
  graphs are features of storage for later.
* This is structural identity, not semantic identity: renaming bound
  variables leaves the resolved representation unchanged, while
  inlining, changing a derived operation or choosing another proof
  usually does not, and semantic equivalence belongs to checked
  certificates. Equal finite digests prove nothing about unbounded
  trees: retrieved content is verified, payloads are compared before
  objects are identified, and an identifier associated with conflicting
  payloads is rejected.
* A member of a block of several members is referred to by the block's
  digest and its validated export direction, where Unison uses an index
  into a recursive component.

Identifiers live above the kernel. A definition's payload refers to the
definitions it depends on by their CIDs, and the kernel goes on reading
a reference as a position in a bundle: a linker, given the payloads a
program needs, orders them by dependence and replaces each CID by the
position of the definition it identifies, a relabelling proved in Lean
to preserve the payloads, so the kernel, its checkers, the translation
into the metalogic and their proofs are unchanged. A position is then a
property of one linked bundle, never a globally meaningful integer. The
migration to digests runs in the order of dependence, rewrites the
constructor of external references, produces a map from old references
to new, and re-keys annotations with it; a later change of algorithm or schema computes new
identifiers without promising equal ones. The traversal follows the
grammar: a data tree inside a quotation may contain the label of the
reference constructor without being a reference, as the substitution
traversal of `Geb/Prototypes/Kernel/Subst.lean` already treats
quotations apart from term children, and reflective code values need an
identified schema and a transport of their own. A digest literal in
source, pinning a dependency as Unison's `#…` does, is a hexadecimal or
base-64 atom of {citet RFC9804}[] that Geb's grammar reads as a
reference.

With content identity a file is a view: a qualified name names a
definition's digest, and a program's order is the order of its
references. The manifest of a program
({ref "files-editions"}[Files, editions and the host boundary]) migrates
mechanically into that; names being unique, a file resolves alike in
every program that includes it. Content identity also gives incremental
compilation, a cache per definition keyed by digest, which is a reason
to take it early, though not one of format.

## Authoring across bootstrap revisions
%%%
tag := "authoring-compatibility"
%%%

:::table +header
*
  * Step
  * State
*
  * Checked filling of one contextual term hole in Lean
  * Complete
*
  * Source documents keeping comments, their retraction and the formatter
  * Complete, and adopted over `bootstrap/`
*
  * The authoring profile and the importer, the kernel's readers reading
    it and rejecting duplicate and ambiguous names
  * Complete
*
  * The strict encodings of RFC 9804
  * In progress: the readers of every spelling of their atoms, the
    canonical and basic transport encodings and the strict form of
    documents, with the retraction, complete; the printer of the advanced
    encoding, ready
*
  * Modules with parameters, imports and export lists
  * Ready
*
  * The datatype language's completion
    ({ref "datatype-completion"}[The datatype language's completion])
  * Ready
*
  * Manifests with editions, and the record of elaborated definitions
  * Ready
*
  * A durable document with versioned profiles
  * Ready
*
  * Hygienic elaboration, explicit assembly and diagnostics
  * Ready
*
  * The markup and conventions of comments, and documentation
  * Ready
*
  * The `geb` editor language with Mike's Paredit
  * Ready
*
  * Early in writing: `let*` and `cond`, the syntax of holes, the
    suspending checker of holes in programs and the display of their
    obligations, located diagnostics, literate pages and the typed
    enumerator
  * Ready
*
  * When their consumers exist: digests and the store, the attachment of
    annotations and hover text, a language server, tree-sitter, holes in
    proofs, the cache of certificates, the export to canonical
    S-expressions, and the Geb-native refinement search
  * Waiting on their consumers
*
  * Acceptance
  * Not met
:::

Programs written during the bootstrap require preservation of their
authoring information as well as their denotation. This section states
what must be fixed about Geb's source and its authoring tools before most
of Geb's code is written in Geb, so that every later change of format or
implementation is a mechanical, provable translation: the compatibility
contracts, the concrete syntax, comments and documentation, names, files
and the host boundary, editor tooling, typed holes and synthesis; content
identity is the section before. The survey's sections on source and its
tools and on holes and search supply the prior art, the survey of
concrete syntaxes (`docs/concrete-syntaxes.md`) the constructions of
syntax and annotation, and `docs/definitions.md` those of blocks, linking
and addresses.

A later change of format is a mechanical, provable translation exactly
when the source written now records every piece of information a person
supplies, the reading of that source is fixed by a recorded version, and
every artifact that persists has a versioned contract. Whatever a program
can compute from the source, digests, addresses, the separation of
comments from code, highlighting, rendered documentation, reports of
holes and synthesized terms, can be added later without touching what was
written. The work to do first:

1. Read comments and empty lines as data, decorations of the trees read
   of the same kind as declaration and binder names, prose, examples and
   links
   ({ref "source-documents"}[Source documents and the formatter],
   {ref "documents-annotations"}[Documents and annotations]).
2. Write source in the syntaxes of {citet RFC9804}[]: its canonical and
   transport encodings for exchange, hashing and signing, its advanced
   encoding, and a Geb authoring profile extending the advanced encoding
   by line comments and UTF-8 in strings, all four reading into one
   document type ({ref "rfc9804-syntaxes"}[The syntaxes of RFC 9804]).
3. Make name resolution a function of recorded data: a manifest per
   program, rejection of duplicate and ambiguous names, a separator of
   qualified names, and hygienic generated names
   ({ref "files-editions"}[Files, editions and the host boundary],
   {ref "modules"}[Modules]).
4. Record what an author knows of types and organization: the datatype
   language's completion, with datatype names as exact types checked at
   every use, explicit representation and decoding, opaque type
   parameters and the soundness of the typing, and modules with
   parameters, imports and export lists. Which datatype a value belongs
   to, and which definitions a module exports, are information no tool
   recovers later ({ref "datatype-completion"}[The datatype language's
   completion], {ref "modules"}[Modules]).
5. Pin elaboration as well as syntax: an edition per program, and a
   committed record of each program's elaborated definitions compared in
   continuous integration ({ref "files-editions"}[Files, editions and the
   host boundary]).
6. Version every interface that persists: document and core schemas,
   semantic profiles, datatype encodings, certificates and host protocols
   ({ref "further-requirements"}[Further requirements]).
7. Write comments in Verso markup, with explicit links for references to
   code, since links cannot be added mechanically to prose written
   without them ({ref "documentation"}[Documentation]).
8. State which steps of the pipeline are proved and which are tested
   ({ref "compatibility-contract"}[The compatibility contract]).

Content storage, a network of identifiers, a language server,
tree-sitter, richer holes and synthesis derive from the source and
follow; each section below states its present obligation, usually none or
a reserved character. Two prototypes implement first steps: source
documents that keep comments, with a verified formatter, in
`Geb/Prototypes/Kernel/Document.lean`, its tests and the executable
`geb-fmt`, run by `lake exe geb-fmt` (`GebFmtMain.lean`); and the checked
filling of one contextual
hole, in `Geb/Prototypes/Kernel/Hole.lean`.

### The compatibility contract
%%%
tag := "compatibility-contract"
%%%

For a syntax with parser `p : C → Option D` and printer `q : D → C`, the
required equation is `p (q d) = some d`: the parser retracts the printer.
Parsing followed by printing is then a partial idempotent, and the
printer is injective; `Geb/Prototypes/ConcreteSyntax.lean` proves both
consequences once. For two syntaxes of one document type,

```
migrate₁₂ c = (p₁ c).map q₂
(migrate₁₂ c).bind p₂ = p₁ c
(migrate₁₂ c).bind migrate₂₃ = migrate₁₃ c
```

follow from the destination's retraction alone. A migration preserves the
parsed document, not its whitespace; a formatter chooses a normal layout
while preserving every name, comment and link the document type holds.

A change of the document or core schema needs a computable map and its
preservation theorem: for a document migration `M`, a core migration `m`
and erasures `erase₁`, `erase₂`,

```
erase₂ (M d) = m (erase₁ d).
```

Widening a grammar is the case in which `M` is an embedding and `m` the
identity. A lossless change needs an inverse or a retained representation
of the old information. Three conditions make migration available:

* completeness of the document type: whatever a person wrote that it
  omits is lost by every migration (`docs/concrete-syntaxes.md` § The
  laws must be lifted to the annotated level);
* determinism of the reader relative to recorded context: a migration
  replays the old reader, its rules of resolution included, and whatever
  the reader consults, such as the order in which files are joined, is
  recorded;
* an image in the new edition for every old document.

Two consequences follow. Restrictions cost little before code exists and
much after, and extensions the reverse, so the grammar is made as narrow
as present code requires. And a feature may be deferred when its data is
a function of the document.

Until the bootstrap completes, no source is kept unchanged for its own
sake (the decision on conversion): Geb is built from scratch and has no
users to keep compatible, so whatever is preferable is adopted
everywhere, every source converted to it, mechanically where the contract
above permits and by hand where it does not. And the languages admit
exactly what the mathematics states: no implicit coercion, no silent
conversion, no convenience that makes a term differ from the mathematical
object it denotes. Editions and importers exist
to make conversions mechanical and to state what a conversion preserves,
not to keep old code in use.

Universal properties fix the interpretation up to the relevant
isomorphism, or equivalence where categories are compared. They supply
no serialized schema, executable migration, source location or bound on
cost. A replacement implementation provides the comparison and shows that
interpretation commutes with it; where representations of input or
output change, the maps of observation commute as well.
`docs/definitions.md` § Content identity separates equality of
presentations from equality of their denotations in the same way.

Libraries need their own contract. Two sound provers may return
different certificates, or succeed on different inputs; soundness does
not make them equal as Geb functions returning certificates. A
replacement keeps the old dependency available or is proved equal for the
observations its interface permits. Hiding a certificate behind a proved
abstraction permits changes of its representation; promising only some
checked witness does not erase differences a client can observe. The
prover's public contract is therefore any checked certificate of the
statement, behind an abstraction clients may check or cite but not
inspect, and exact agreement with the Lean implementation is a milestone
of the bootstrap, not a choice of that public contract (the decision on
libraries).

The compatibility policy covers accepted programs of a named profile. A
program that depended on an implementation error may admit no migration
to the corrected meaning preserving its semantics: its source and
compiler profile are kept, the discrepancy is identified, and a repair is
decided explicitly. Neither a universal property nor a converter infers
which behavior the author intended.

The verification boundary is tracked through the whole pipeline.
Soundness of the metalogic's checkers and their agreement do not prove
the reader, the serializer, the code generator, the host compiler or the
file driver correct, and the bootstrap's fixed points, byte for byte, are
evidence against regression, not preservation theorems. Which steps are
proved and which tested is stated explicitly, the agreement of the word
codec with the wire form, tested and not proved, among them.

### The sources and what the guarantees leave out
%%%
tag := "authoring-state"
%%%

Geb specifies an abstract syntax with a retraction to each concrete one,
and its semantics by universal properties: the first protects the kernel
term and the second its denotation. Four things lie outside both.

1. Content that is not a kernel term: comments, names of bound variables,
   abbreviations and layout. A retraction at the level of kernel terms
   prints `app (lam A b) e` where a person wrote `let` or `defn`, and
   loses numeral abbreviations such as `Label.app`, which the reader
   expands before resolution. The formatter's retraction therefore
   belongs at the level of documents; the retraction at the level of
   kernel terms, the printer for the kernel's readable syntax, serves
   generated code and decompilation.
2. Elaboration. The datatype language is defined by a Geb program,
   `bootstrap/stage1/datatype.geb`, and its encoding, the constructor of
   position `i` as the node of label `i` over its fields, `&` taking the
   remaining children, is observable: sources use it directly, as
   `bootstrap/free-topos/base.geb` does for optional trees. A revision of
   the expansion changes the meaning of existing source while every
   universal property still holds. Elaboration need not be invertible,
   since a printed expansion cannot recover the author's abstractions:
   the authoring document is kept beside its elaborated result, and the
   elaborator is versioned ({ref "files-editions"}[Files, editions and the
   host boundary]).
3. Proof scripts. A proposition of the metalogic keeps its meaning, but a
   tactic script is a program for one prover
   ({ref "proof-scripts"}[Proof scripts and certificates]).
4. Organization: which definitions form a program, their order, files,
   sections and modules, recorded now in the source lists of
   `scripts/bootstrap.sh` and in the `include_str` definitions of the
   tests.

The components that bear on authoring, and their contracts or
limitations:

:::table +header
*
  * Component
  * Contract or limitation
*
  * The kernel reader, `Geb/Prototypes/Kernel/Reader.lean`, and its Geb
    counterpart, `bootstrap/reader.geb`
  * Resolve definition names to positions in the bundle and binders to
    de Bruijn indices; expand abbreviations; discard comments. An atom is
    any run of characters other than whitespace, parentheses and `;`,
    one character per byte; there are no strings and no program printer.
*
  * Source documents, `Geb/Prototypes/Kernel/Document.lean`
  * Read comments and empty lines into a document conservatively over the
    kernel reader, and print it at any layout with a proved retraction.
    Binder names at the level of kernel terms are not yet kept.
*
  * Canonical S-expressions, `Geb/Prototypes/CanonicalSExpr.lean`
  * Proved retractions for the presentations of trees over a finite
    alphabet; the generic renderer counts characters, so its conformance
    to {citet RFC9804}[] holds for ASCII atoms.
*
  * Readable S-expressions, `Geb/Prototypes/ReadableSExpr.lean`
  * A proved syntax of rose trees labelled by numerals, distinct from the
    kernel reader and from the advanced encoding of {citet RFC9804}[].
*
  * Definition vertices, `Geb/Prototypes/Definition/Vertex.lean`
  * Selection of subterms, composition of addresses and their laws: a
    basis for addressing occurrences.
*
  * Images, `Geb/Prototypes/Kernel/Image.lean`
  * A versioned bundle keeping definition names, without binder names or
    comments; the word codec's agreement with the wire form is tested,
    not proved.
*
  * The file driver, `Geb/Prototypes/Kernel/Command.lean`
  * Joins ordered source files with a newline; file operations stay in
    the host.
*
  * The Lean emitter, `bootstrap/stage1/lean.geb`
  * Emits definitions under their names with a generated module comment;
    variables are named by depth, and author documentation and source
    spans are not carried.
*
  * Contextual hole filling, `Geb/Prototypes/Kernel/Hole.lean`
  * Checks and fills one explicitly typed contextual hole, with theorems
    for the result's typing and denotation; a Lean interface, not a
    surface or editor feature.
:::

The syntax prototypes' retractions do not yet certify the migration of
bootstrap programs: the connection needs arbitrary atom bytes, the
program grammar, name resolution and the document. The following was
measured at revision `b3aa139a`.

* The 21 files under `bootstrap/`, of about 250 kilobytes:
  * use atoms from `[A-Za-z0-9.&-]` only, each a numeral, an identifier
    beginning with a letter, or `&`;
  * contain only whole-line comments: a header per file followed by an
    empty line, blocks immediately before a top-level form, and blocks
    immediately before a sub-form, the last all in the chains of
    conditionals of `bootstrap/goedel-t/equations.geb` but for one each
    in `bootstrap/stage1/lean.geb` and `bootstrap/goedel-t/prove.geb`;
  * have comments whose only character special in Verso or Markdown
    markup is a single `_`;
  * form programs, joined as `scripts/bootstrap.sh` joins them, without a
    duplicated name.
* The reader resolves a duplicated definition name to the first
  definition, and a duplicated `deftype` or `defnum` to the latest, and
  it substitutes numeral abbreviations into binder names, `expandNums`
  running before resolution. No source relies on these; a migration
  replays them.
* Dependencies between files are recorded in prose only ("Requires the
  prelude, the reader and the checker").
* Content identity is designed: the node-digest rule, the migration from
  positions to digests and the annotation tables keyed by vertex
  ({ref "content-identity"}[Content identity]), with identifiers as CIDs
  whose multihashes are of BLAKE3 (the decision on identity).

### Source documents and the formatter
%%%
tag := "source-documents"
%%%

A document, written in the authoring profile
({ref "rfc9804-syntaxes"}[The syntaxes of RFC 9804]), is read into
S-expressions with comments
({name}`Geb.Kernel.Document.SExpr`), rose trees whose nodes are atoms and
lists, each decorated ({name}`Geb.RoseTree.Decorated`, the decision on
annotations) with its trivia ({name}`Geb.Kernel.Document.Trivia`): the
comment lines before the node, each with whether an empty line precedes
it, whether an empty line precedes the node itself, and, for a list, the
comment lines before its closing parenthesis; the comment lines after the
last S-expression belong to the document
({name}`Geb.Kernel.Document.Doc`). An empty line is a flag, as gofmt and
ormolu keep at most one empty line between items. Placing each comment by
its position is a rule of the syntax, so reading and printing keep their
retraction, while which definition a comment documents is a redecoration
outside them ({ref "documents-annotations"}[Documents and annotations]).
The lexer reads one character per byte, as the kernel's readers do, so
atoms and comments keep their bytes. The kernel's reader of the seed,
{name}`Geb.Kernel.readSExps`, is this reader with the decorations erased.

Two theorems hold, neither depending on `Classical.choice`:

* {name}`Geb.Kernel.Document.readDoc_print`:
  `readDoc (print L d) = some d` at every well-formed document and
  every layout `L`, a function from the positions of tokens to a choice
  of line break and indentation. The separator before a token is a fixed
  function of the token before it, the token and the layout's choice
  ({name}`Geb.Kernel.Document.sepFor`), and the lexer is proved correct
  for every sequence of separators so formed, so the layout policy is
  outside what is proved.
* {name}`Geb.Kernel.Document.format_format`: the formatter
  {name}`Geb.Kernel.Document.format`, the executable `geb-fmt`, is
  idempotent.

Measured on a copy of the files under `bootstrap/`:

:::table +header
*
  * Check
  * Result
*
  * Formatting all files
  * 0.11 s
*
  * `geb-fmt --check` after formatting
  * No file changes
*
  * Stage-0 image from formatted sources, built by the seed
  * The original's, byte for byte
*
  * Stage-1 image from the formatted compiler, built by the stage-0
    compiler
  * The original's, and `bootstrap/compiler.img`, byte for byte
*
  * Lean emitted by `bootstrap/compiler.img` from the formatted compiler
  * `bootstrap/lean/GebBoot.lean`, byte for byte
*
  * parinfer 3.13.1, Paren Mode and Indent Mode, on formatted files
  * No file changes
*
  * parinfer on the files as written
  * 16 files changed by Paren Mode, 15 by Indent Mode, and an Indent Mode
    error in `goedel-t/prove.geb`
*
  * Lines beyond 100 columns after formatting
  * 17, all comments in the chain of conditionals of
    `goedel-t/equations.geb`
:::

The layout policy ({name}`Geb.Kernel.Document.planStep`,
{name}`Geb.Kernel.Document.planElem`) is the decision on layout: a list
that fits on one line is written on it; otherwise its elements fill the
first line while they fit, the parentheses that close after them
included, and the rest begin lines of their own indented past the list's
opening parenthesis, by two columns after an atom at its head and by one
otherwise. An element that does not fit is not hung on the current line:
a body's indentation then depends on its depth of nesting alone, so
renaming a definition changes one line of a diff rather than every line
of the body, and a chain of nested forms indents by two columns a level
rather than by the width of everything before it. Its output meets
parinfer's invariant ({ref "source-tools"}[Source and its tools]). The
written files place a nested `let` or conditional at its parent's
indentation, which parinfer's Indent Mode reads as closing the parent.
The same cause produces the long lines: the kernel's binary conditional
and single-binding `let` make chains nest, and nesting is indentation
under any layout parinfer admits; the forms `let*` and `cond` remove
both ({ref "improvements"}[Improvements]). Parinfer's Paren Mode, which
never changes the tree, would also serve as a formatter, but without
proofs for Geb's grammar; the formatter here has its proofs.

The sources' convention of comments is kept as it stands: whole-line
comments, a block of comments immediately before a form documenting it,
and a block followed by an empty line being prose. The graded semicolons
of Common Lisp's style (the HyperSpec, section 2.4.4.2) serve if headings
and documentation must be told apart without empty lines. The formatter
reads a comment after code on the same line and moves it before the next
item. A comment as the last element of a list is excluded, being the one
construct parinfer cannot lay out stably: the prototype prints the
closing parenthesis of such a list at the start of a line, which
parinfer rejects, and no file has one.

One thing is left open: the attachment of comments to the definitions
they document, which hover text and a store need, a redecoration not yet
written ({ref "documents-annotations"}[Documents and annotations]).

### The syntaxes of RFC 9804
%%%
tag := "rfc9804-syntaxes"
%%%

Geb's source is written in the syntaxes of {citet RFC9804}[] (the
decision on concrete syntax), whose encodings the survey describes
({ref "source-tools"}[Source and its tools]). Four syntaxes read into one
document type:

* the canonical encoding, for exchange, hashing and signing: a
  definition's digest is taken over the canonical bytes of its
  identity-bearing payload ({ref "content-identity"}[Content identity]),
  and the canonical bytes of a source document identify the document;
* the basic encoding for transport, completing conformance;
* the advanced encoding, strictly as specified, printed when a
  conforming readable file is wanted;
* a Geb authoring profile, in which source is written by hand: the
  advanced encoding with its extensions, `;` line comments, read as items
  of the document ({ref "source-documents"}[Source documents and the
  formatter]); UTF-8 and line breaks inside quoted strings; numerals as
  bare runs of digits; `&` as a token; and `?name` as shorthand for the
  form `(hole name)`. Each extension is unambiguous against the advanced
  grammar, so every strictly conforming advanced file is a file of the
  profile. The profile is not called RFC 9804.

The strict encodings have no comments, so they carry each node's
decoration, its comments and empty lines among it, as an annotation
form among the node's children, a list headed by a reserved token such
as `*ann`, as the annotated examples of
`docs/concrete-syntaxes.md` § One tree, every recommended encoding do; a
list of code headed by that token is excluded, so that annotation and
code are never confused. A strict quoted string escapes each non-ASCII
byte and line break, and a canonical verbatim atom holds the bytes as
they are, so prose passes through every syntax unchanged.

Each syntax's printer is a section of its parser into the document type,
so the migrations among the four are those of the compatibility contract:
each preserves the parsed document, and they compose. The four share
code as far as their grammars allow:

* the document type and its well-formedness, and the encoding of
  comments and empty lines as annotation forms;
* the choice of an atom's spelling from its bytes: a token where one is
  legal, else a quoted string, else a hexadecimal or verbatim atom;
* the decimal layer of length prefixes, which verbatim atoms and quoted
  and hexadecimal atoms with lengths share, and which `Csexp.decOf` and
  `Csexp.digitsVal` implement already;
* base-64, for the transport encoding and for base-64 atoms;
* escaping and its inverse, parameterized by the bytes a profile admits
  unescaped;
* the loop over a list's elements (`Rose.parseChildren`);
* for both advanced syntaxes, the lexer and printer of the source
  documents, with its separators chosen by the layout;
* the generic corollaries of the retraction law, proved once in
  `Geb/Prototypes/ConcreteSyntax.lean`.

The authoring profile's reader and printer are constructed in Lean
({name}`Geb.Kernel.Document.readDoc`,
{name}`Geb.Kernel.Document.print`), with the retraction at every layout
({name}`Geb.Kernel.Document.readDoc_print`), and the seed reads the
profile ({name}`Geb.Kernel.readSExps`). Its reader reads every spelling
of an atom of the advanced encoding, verbatim, quoted, hexadecimal and
base-64, each with or without a length, which its bytes must match, so
every file of the advanced encoding without display hints is a file of
the profile. The canonical encoding, written by
{name}`Geb.Kernel.Document.canonOf`, reads back to every well-formed
S-expression ({name}`Geb.Kernel.Document.readDoc_canonOf`); a document
is written in a strict encoding as one S-expression, its decorations as
annotation forms headed by `*ann` inside a list headed by `*doc`, and
read back from its canonical encoding
({name}`Geb.Kernel.Document.readStrictDoc_printCanonDoc`) when no list
of it is headed by the atom `*ann`; the basic transport encoding is read
from the canonical one or from its base-64 form between braces
({name}`Geb.Kernel.Document.readBasic`) and written as the canonical
one. The heads `*ann` and `*doc` are reserved names. The Geb reader
reads the same spellings. The advanced encoding's printer, writing every
atom that is not a token quoted with escapes of ASCII alone, remains.
The `.geb` sources were written in a legacy syntax, the kernel reader's,
whose atoms were any characters but whitespace, parentheses and the
semicolon. They were files of the profile already but for two names
beyond ASCII, which were renamed, so the importer is the profile's
reader itself; its acceptance, that the sources compile to the same
checked bundles with names and comments kept, is that of the fixed
points, and every source is a fixed point of the profile's formatter.
The Geb reader, `bootstrap/reader.geb`, reads the profile as the seed
does, rejecting the same texts and the same declarations; the stage
tests compare the two on programs with quoted atoms and their escapes,
comments, holes, the spellings the profile does not admit, and reserved
and repeated names.

Identifiers are tokens of {citet RFC9804}[]: ASCII letters, digits and
`- . / _ : * + =`, not beginning with a digit. Every identifier of the
present sources is one already. A name beyond ASCII is a quoted atom,
readable in the authoring profile, whose quoted strings admit UTF-8.
Names are compared byte for byte, and since no reader normalizes, a
quoted name not already in Unicode's normalization form C is rejected,
so that equal-looking names are equal.

Numerals, which no token spells, are bare runs of digits in the
authoring profile, unambiguous against the advanced grammar, in which a
digit begins a length only before `:`, `"`, `#` or `|`; the strict
printers write them quoted (`"0"`). The datatype language's `&`, not a
token character, is a token of the authoring profile, and the strict
printers write it `"&"`. A hole is the form `(hole name)`, of tokens
alone, in the document type and in every syntax, and the authoring
profile writes it `?name`, as a Lisp writes `'x` for `(quote x)`: the
profile's reader reads `?name` as the form, and its printer writes a hole
form of one argument as `?name`, deterministically, so the retraction
holds. The form extends where the prefix cannot: `(hole name T)` gives
an expected type, which a first implementation may require, and `(hole)`
an anonymous hole. No atom prefix is reserved, and the strict encodings
need nothing of their own; `hole` is a keyword that no definition may
shadow, as the names the expansions use must be
({ref "improvements"}[Improvements]).

Further:

* Atoms are byte strings preserved exactly; human names and prose are
  UTF-8, without implicit Unicode normalization. Whether an atom names a
  numeral, an identifier or a datum is decided by Geb's grammar, not by
  the S-expression layer, so a change of spelling changes no decoded
  bytes.
* A canonical file holding arbitrary bytes is not an editor buffer, since
  trimming whitespace or converting encodings corrupts a length-prefixed
  atom.
* Display hints are excluded, as {citet RFC9804}[] § 8 permits; format
  information is a field of the document, and hints accepted later keep
  their bytes.
* The existing canonical codec, `Geb/Prototypes/CanonicalSExpr.lean`, is
  proved over trees of numerals and counts characters, so its
  conformance holds for ASCII atoms; it is generalized to byte atoms and
  to lists of every shape, empty or headed by lists. The advanced
  encoding's parser and printer and the inverse of its escaping are new,
  the separators and lexer lemmas of the source documents carrying over.
* Kernel terms also have a canonical, versioned exchange format, the
  image ({name}`Geb.Kernel.writeImage`), compared by bytes in continuous
  integration.
* The syntax unification, one reader over the canonical data model with a
  quoted spelling for atoms that are not tokens, is this decision. In a
  quoted datum, an atom that is not a numeral contributes the leaves of its
  bytes to the list it is in, so the sources spell the atoms they compare
  with, the keywords of the reader, the expansion and the prover, as atoms,
  `(quote (1 let))` for `(quote (1 108 101 116))`, and the trees quoted are
  unchanged; a text of digits alone, which would read as a numeral, stays a
  list of its codes.

### Documents and annotations
%%%
tag := "documents-annotations"
%%%

Comments never reach the image, and the compiler reads the core tree
only, so their separation has no motive at compilation. Its motives are
identity, the digest excluding annotations; reuse of a checked core when
only documentation changes, whose benefit is to be measured; and a future
content store. Of the two arrangements of the survey
({ref "source-tools"}[Source and its tools]), the first is adopted: text
is primary, comments are data in it, and the separation into core and
annotations is derived when reading, in memory and in build artifacts.
The second, core and annotations as two authoritative artifacts, is
adopted when a store or editor provides the atomic updates, detection of
stale annotations and coordinated merging it needs, with a proved
conversion from the single document. The document keeps at least:

* declaration and binder names, ordered prose, links, examples, and the
  associations of source to core;
* unknown annotation fields of a known version, kept on read and write;
* everything that affects elaboration, type annotations and datatype
  encodings among it, in the checked input, since calling such
  information a decoration must not let its erasure change meaning.

Annotations are decorations of the trees read (the decision on
annotations), one mechanism for comments, names, prose, links and every
later kind. The attachment is a redecoration, from the trivia the reader
decorates each node with to decorations in the vocabulary of
annotations, and erasing the decorations gives the core. The side table
`Vertex ⇀ Notes` is the same decoration presented apart from the tree,
a presentation with a proved correspondence, which separate hashes of
core and annotations use. Its keys identify occurrences relative to one revision
of a document or definition: two equal subtrees can carry different
comments, which a key made from their hash cannot distinguish, while
metadata meant for every instance of an equal definition uses that
definition's content identity; the two are different attachments
(`docs/concrete-syntaxes.md` § Wrapper model, environment model, and the
occurrence pitfall). A path means something only at its identified root,
and a change of representation transports paths. An edit of a program
can delete, duplicate or merge occurrences, so a migration of meaning
cannot place every comment: an explicit map of the edit is kept, or
unmatched annotations are kept for reconciliation, never attached to the
nearest equal subtree. A map of sources through elaboration is a
relation, one source form generating several core nodes. A store, when
one exists, keys annotations by the named entry, a core digest with its
names, as Yatima does, and checks shapes as Yatima's `unembed` does.

Addresses reuse the constructions of
`Geb/Prototypes/Definition/Vertex.lean`. A direction of the free monad
selects a variable leaf, a vertex any node; an export layout marks
exports as variable leaves deliberately, and an annotation on an internal
expression uses a vertex. Treating the two kinds of address as one loses
occurrences. Now: the vocabulary of addresses is recorded as those
vertices, with the root of each, and paths are checked on input wherever
a path is read; the compact wire spelling and a surface syntax for
navigation wait. Addresses become persistent only when a table keyed by
vertex is stored, which the arrangement adopted above never does, or when
a reference is a digest of a block with a direction, which blocks of
several members, absent from the kernel, need. A change of
representation supplies a transport of addresses with a proof that
selection commutes with it; an isomorphism of values alone does not
preserve a chosen set of addressable intermediate nodes. The finite
decorated trees serve the annotations: those of
`Geb/Prototypes/ConcreteSyntax.lean`, with their comonad laws, decorate
its binary syntax, and the same construction over the rose functor
decorates the S-expressions read; `docs/concrete-syntaxes.md` § The
document type is a μ, not a ν distinguishes them from the possibly
infinite cofree comonad. The strict encodings of
{citet RFC9804}[], which have no comments, write a node's decoration as
an annotation form among its children
({ref "rfc9804-syntaxes"}[The syntaxes of RFC 9804]).

### Files, editions and the host boundary
%%%
tag := "files-editions"
%%%

Files stay outside Geb's semantics: they organize writing and delivery,
and semantic dependencies are references to definitions.

* A manifest per program, an S-expression naming the program, its
  edition, its sources in order and its entry points, is read by the host
  driver, the tests, the formatter and a language server. It replaces the
  lists in `scripts/bootstrap.sh` and the tests, and the dependencies
  stated in comments. No scan of directories or working directory decides
  the order of binding implicitly.
* The first linker keeps the present well-founded order, resolves each
  import to an explicit definition, rejects unresolved and ambiguous
  references, and checks the bundle; references by digest replace frozen
  positions later. General cyclic blocks and a canonical order of
  recursive components are unnecessary for the bootstrap's recursion by
  folds, and sorting the members of a cycle by their digests does not
  solve symmetric cycles.
* Generated names are made hygienic before a large library is written:
  identifiers the expansion generates are reserved or its expansion is
  hygienic, and emitted Lean names escape injectively with the runtime's
  names qualified. The section on improvements records the capture of
  primitives in the datatype language's expansion and the conflicts with
  emitted `T`, `leaf` and `mk`.
* Converting existing source replays the old resolver, so that the
  meaning to be re-expressed is known exactly, and the converted source
  then follows the new reader's rules, duplicates rejected; no present
  source has one.

Interaction with the operating system stays a pure interface of requests
and results with an interpreter in the host. Byte encoding, framing of
input and output, errors and exhaustion of resources have explicit
contracts, which a later interface of effects implements. Paths, clocks,
environment variables and the width of machine integers are never hidden
semantic inputs.

The manifest records an edition per program, as Racket's `#lang`, Rust's
editions and Go's `go` directive do. An edition fixes the reader, its
rules of resolution included, and the elaborator. An elaborator is a
committed image and the kernel is fixed, so an old edition's image runs
unchanged. Before the bootstrap completes, sources are converted to the
current edition rather than kept under old ones; editions preserve
meaning across revisions for code relied on beyond the bootstrap. Mixing
editions in one program needs an interface between the environments of
elaborators, such as declarations of constructors; that is its cost.

Elaboration is pinned as syntax is. The higher-level source is kept
beside its resolved core, the rules of expansion and name resolution are
versioned by edition, and generated names are hygienic. For each program,
the elaborated definitions that `lake exe geb-defs` writes are committed,
regenerated in continuous integration and compared: any change of
expansion or resolution that alters existing code is then detected,
before digests exist, as `bootstrap/compiler.img` detects it for the
compiler alone. The encoding of the datatype language is stated in this
manual as part of the first edition. A specification of the expansion in
Lean, as the checkers have, would free its meaning from one Geb program;
that is larger and can follow.

### Modules
%%%
tag := "modules"
%%%

A module is a block form, `(module M header… body…)` (the decision on
modules). It does not depend on files, so the same source can be kept in
files, in a database or in a content-addressed store, and membership in a
module is structural: a module is a subtree of the document, and a
definition's module travels with it. Blocks nest, each level indenting
its contents by two columns under the layout policy, so the depth of
nesting shows at a glance.

The header is a telescope followed by an export list. Its entries,
`(parameter …)` and `(import …)`, stand in the order of their dependence,
each in scope for the entries after it and for the body: a parameter's
type may use an imported name, and an import may take a parameter as an
argument. A parameter is a sort, an operation, a certificate of a
proposition, or a named telescope, which abbreviates its entries:
declared as `(interface I entries…)`, parameter and import entries under
a name, and taken as `(parameter (m I))`, its entries then named `m.x`.
An import names a module and supplies every one of its parameters; a
module leaving one of them open declares a parameter of its own and
passes it through. `(import M)` brings `M`'s exports into scope
unqualified, and a clash between two names in scope is rejected;
`(import M as N)` brings them in qualified alone, as `N.x`, which two
instances of one module in one block need. The export list, `(export …)`,
follows the telescope and may name imported definitions as well as the
body's, re-exporting them. A module refers to nothing outside it except
through its imports, its parameters and the blocks enclosing it, so its
meaning is its text and the identities of its imports. An import names a
module by its path from the root; `.` separates the components of a
qualified name, being a token character of {citet RFC9804}[] and already
used so (`Label.app`, `Prim.add`, `Rule.hyp`). `module`, `parameter`,
`import`, `export` and `interface` are keywords no definition may shadow.
In the present syntax of definitions:

```
(module Sorting
  (import Prelude)             ; List, Bool
  (parameter A)
  (parameter (le (A A) Bool))  ; typed by the import above
  (import (Orders A le))       ; both parameters passed through
  (export sort)
  (defn sort ((xs (List A))) (List A) …))
```

A block without an export list exports nothing: a test's ad hoc
definitions, for instance, stay unreachable from other code. The
resolver rejects an entry naming nothing. A module is not reopened: a
second block of one module would either see the first's unexported
definitions or divide its interface, and a module extending another
imports it.

Every definition in a module takes all of its parameters, as in Agda's
parameterized modules ({ref "source-tools"}[Source and its tools]): the
body is one structure over the context the parameters form, abstracted
over all of them as a whole, and an import instantiates the whole of it
at once. A definition that takes fewer belongs in an enclosing block. A
nested module's context extends the enclosing one by its own parameters:
the rest of the enclosing body refers to the exports of a nested module
without parameters of its own by qualified name, `N.x`, and a nested
module with parameters is used through an import in a later module's
header, supplying parameters being an import's work. Declarations keep
parameters of their own, supplied where they are used: a module uses a
declaration at several arguments, as `bootstrap/free-topos/partial-horn.geb`
writes `(List PT)` beside `(nil T)`, and a nested datatype such as
`(data Tree (node T (List Tree)))` applies `List` to the type being
defined, which no header can name.

For parameters that are terms or certificates, the body lies in the
slice over the context `Γ` the parameters form, a telescope denoting one
object: an iterated dependent pair, a certificate contributing a subset
rather than a component. A definition in the body is a morphism in the
context, corresponding to a morphism out of `Γ × X` by functional
completeness {citep LambekScott1986}[]; an import at arguments
`σ : Δ → Γ` is reindexing along `σ`, which on the syntax is
substitution; and imports passing parameters through compose as their
substitutions do. In a topos a slice is again a topos and reindexing is a
logical functor {citep MacLaneMoerdijk1992}[], so the language of a
module's body is the whole language, and a theorem proved in a module
holds at every instance. A sort parameter extends the language instead,
and its instantiation is the logical functor of the datatype language's
completion ({ref "datatype-completion"}[The datatype language's
completion]). A named telescope therefore adds nothing to the semantics.
An import supplying a certificate discharges an assumption as an
interpretation of an Isabelle locale does ({ref "source-tools"}[Source
and its tools]).

Parameters make modules a matter of elaboration: the elaborator
abstracts each module's definitions over its parameters and instantiates
an import by substitution, type parameters being instantiated at
elaboration, and the correctness of the step is the substitution lemma.
Imports and exports are otherwise a matter of the reader; names are
annotations and bear no identity, so modules migrate mechanically. Now:
duplicates are rejected and `.` is reserved for qualification. Then the
present sources are organized into modules with export lists, before the
sources grow. Prefixes that avoid collisions, such as `mTypeIn` beside
`typeIn`, otherwise accumulate, and removing them later is renaming by
hand. A whole module written as one block is one form, so an unbalanced
parenthesis inside it leaves the block unreadable; the kernel's reader
already rejects an unbalanced text as a whole, and a language server's
recovery from errors, not the reader, answers it. The block's closing
parenthesis ends the line of its last definition, so appending a
definition changes that line too.

### Documentation
%%%
tag := "documentation"
%%%

The markup of comments is Verso's (the decision on documentation). Its
storage is fixed before substantial prose is written, and rendering
follows once storage round-trips. The comments of the sources read as
Verso inline text but for one `_`, whereas a reference such as
``{name}`infer_subst` `` cannot be inferred mechanically from prose that
reads "the substitution theorem". A migration keeps unmarked prose byte
for byte but cannot tell which words were meant as references, so
references that should follow renaming are marked from the start. The
roles are the four the repository's Lean modules use, `{name}` resolving
Lean constants as it does there, and one more, `{geb}`, for Geb
definitions, resolved through the compiler's maps of names and sources
against the manifest, so that a comment citing both a Geb definition and
the Lean theorem about it is unambiguous; both are checked when
documentation is built. Verso's design suits this use: its markup fails
on mismatched or unmatched delimiters rather than guessing, parses with
little lookahead, and extends by roles and directives rather than
textual sub-formats (Verso's user guide, § Design Principles). Verso's
markup is defined by its implementation in Lean rather than by an
independent specification, so a field of format and version with the
prose's bytes records the subset in use, and permits starting from that
subset without a complete parser; `scripts/extract-pr.sh` converts the
four roles to Markdown where Markdown is wanted. The convention the
sources follow is kept: a block of comments immediately before a form
documents it, and a block followed by an empty line is prose.

Documentation renders as a literate page per Geb file, generated from its
document: top-level comments become prose and forms become code blocks
of a `geb` expander (Verso supports `@[code_block]` expanders, as its
`InlineLean` shows), which reads each block, fails the build of
documentation on one that does not read, and anchors each definition;
Lean may still check its examples. The page shows the Geb source,
rendered as the repository's literate Lean modules are, and the compiler
is unchanged. One implementation writes each Geb file as a generated
literate module holding only its prose and `geb` blocks, which a chapter
includes by `includeLiterate` as it includes any literate module.

The alternative, docstrings in the emitted Lean, would render Geb's
prose beside the Lean denotations, generated artifacts, rather than the
source, and would change the backend `bootstrap/stage1/lean.geb` and its
committed artifacts. What it alone offers, documentation on hover where
a Lean proof cites an emitted definition and the emitted definitions in
doc-gen4's reference, remains available as a further renderer of the
same document: docstrings pointing to the page, generated with Lean's
comment delimiters, quoted identifiers and markup escaped explicitly,
since a string interpolated into generated Lean is not a safe encoding of
a document.

The model of documentation stays independent of its renderer, which
permits either view and renderers without Lean. Files whose comments come
first and literate Markdown whose prose comes first are two printers of
one document type, so either can be adopted later mechanically. The
acceptance is a module with a description, a documented definition, a
checked example and a cross-reference; editing only its documentation
changes the rendered manual and the document's identity and leaves the
checked core's identity unchanged.

### Editing
%%%
tag := "editing"
%%%

Paredit and parinfer, the two models of editing balanced text that the
survey describes ({ref "source-tools"}[Source and its tools]), bear on
neither the document type, the reader nor the formatter. Paredit's
commands keep parentheses balanced by construction, whatever the layout,
`geb-fmt` restoring the layout after them. Either serves the same Geb
source: the authoring profile uses no brackets or braces, whose display
hints and transport encoding are never written by hand, and its strings
are those parinfer reads, delimited by double quotes with backslash
escapes; the formatter's output is a fixed point of both of parinfer's
modes.

The editor is a `geb` language, a declarative extension of a manifest, a
language configuration and a TextMate grammar of some fifteen lines, with
Mike's Paredit configured for it as the structural editor (the decision on
the editor); Mike's Paredit having few installations, its version is
pinned and tested. Parinfer is optional: its extensions fix their
languages and are unmaintained, so it enters, if wanted, through the
`geb` extension calling the `parinfer` library's `parenMode` or
`smartMode` on formatted files. `geb-fmt` is the formatter; a test in
continuous integration,
`parenMode(x).text === x && indentMode(x).text === x` at a pinned
parinfer, keeps its output usable under parinfer. For the legacy syntax
until the extension exists, associating `*.geb` with `scheme`
(`"files.associations": {"*.geb": "scheme"}`), with
`sjhuangx.vscode-scheme` for a grammar and language configuration, serves
Mike's Paredit or `ailisp.strict-paredit`, sound because atoms avoid the
characters Scheme treats specially.

Before an extension is the supported default, it passes a fixture of the
profile: nested bindings, parentheses in comments, parentheses and
semicolons in quoted atoms, escaped quotes, Unicode names, input with
CRLF, and incomplete syntax. Navigation, selection, wrap, slurp, barf and
undo are tested in VS Code; formatting is tested by comparing the parsed
documents, annotations included, before and after, and structural edits
by their intended change of the tree with the checker run again. An
editor's recognition of other brackets or reader macros never defines
Geb syntax. Formatting on save, through `pucelle.run-on-save` calling
`geb-fmt`, stays off until the fixture passes.

A tree-sitter grammar for Geb is derived from the same profile when the
editors that use tree-sitter need it, from tree-sitter-scheme as a base,
and its recovery from errors never supplies trusted input to the
compiler. Nothing is needed now.

Diagnostics come before a language server: efm-langserver runs the
checker {name}`Geb.Kernel.diagnose`, which names the first failing
definition, applied after the stage-0 expansion for the datatype
language. A language service then needs the services the survey lists,
of which the existing checker serves behind it; the server tracks
versions of buffers, cancels stale checks, and translates offsets of
bytes into the position encoding the editor negotiates, which reliable
diagnostics after Unicode edits require. Diagnostics with locations need
a map from vertices to spans, a derived annotation, and a checker that
reports the failing vertex; the trusted checker stays as it is, and the
locating checker is a separate, untrusted function.

### Typed holes
%%%
tag := "typed-holes"
%%%

The first step is implemented. `Geb/Prototypes/Kernel/Hole.lean` treats a
sketch with one hole of type `A` in context `Γ` as a kernel term in
`A :: Γ`, the innermost free variable standing for the hole, its
occurrences under binders included, and a filling as a term of type `A`
in `Γ`:

```
sketch : A :: Γ ⊢ B
filling : Γ ⊢ A
subst filling sketch : Γ ⊢ B
```

In the cartesian interpretation the sketch is a map `A × Γ → B`, the
filling a map `Γ → A`, and filling composes the sketch with
`⟨filling, id⟩ : Γ → A × Γ`: ordinary substitution, whose denotation is
the kernel's {name}`Geb.Kernel.infer_subst`. {name}`Geb.Kernel.fillHole`
checks the expected type, the filling and the sketch before
substituting; {name}`Geb.Kernel.infer_fillHole` gives the type and
denotation of every accepted result, and
{name}`Geb.Kernel.fillHole_of_infer` accepts every valid input. The
examples of `GebTests/Prototypes/Kernel.lean` cover capture avoidance,
repeated occurrences, and rejection of wrong types, variables escaping
their scope, invalid sketches and malformed expected types. No slice or
presheaf construction is needed for this operation. The hole is the case
of one hole of the lambda-lifting the survey describes
({ref "holes-and-search"}[Holes and search]); the literature there is a
reference for the interface, and its calculi need not enter Geb's
trusted logic.

Holes in programs, the next layer:

* Holes are forms `(hole name)`, written `?name` in the authoring profile
  ({ref "rfc9804-syntaxes"}[The syntaxes of RFC 9804]). The reader takes
  them as variables of the free monad of the definition, the directions
  of `docs/definitions.md`, so that filling is linking, the Kleisli
  composition the definitions prototype proves associative
  ({name}`Geb.Definition.link_assoc`).
* Each hole has an identity, a declaring context, an expected type and
  its occurrences in the source; repeated uses of a named hole share one
  obligation, and unrelated holes of one type do not. Uses in contexts
  other than the declaring one carry explicit substitutions from it, the
  closures of {citet NanevskiPfenningPientka2008}[].
* Expected types come from bidirectional checking, with first-order
  unification of simple types, which is decidable; people fill holes, so
  no higher-order unification arises. An initial implementation may
  require explicit types and decline to evaluate through holes; inference
  of missing types and live evaluation are extensions.
* Each hole is reported with its context, the names of its binders taken
  from the document, and its type. The trusted checker is unchanged: a
  program with holes checks exactly when its lambda-lifting does.
* A slice `Set/(Ctx × Ty)` is the bookkeeping; presheaves on contexts are
  needed only for metasubstitution capturing ambient variables or for
  first-class contextual types, neither of which is wanted.

Holes in proofs: a leaf `hole` carries an open sequent
`Γ_h | Φ_h ⊢ ψ_h`; the checker returns the conclusion with the list of
open obligations and certifies `(⋀_h ∀Γ_h. (⋀Φ_h ⇒ ψ_h)) ⊢ goal`, sound
in every topos since it uses intuitionistic `∀` and `⇒` alone. Filling is
grafting, the bind of the free monad of derivation trees. Only a closed
derivation is accepted as the original theorem; a sketch is state of the
editor, not an axiom or a completed program.

Only a term with all its holes filled, or a derivation with all its
obligations discharged, is accepted as the completed program or theorem.
Search may propose fillings ({ref "search-synthesis"}[Search and
synthesis]); the checker checks their types and the certificates of any
claimed properties. The checker of holes is the second stronger checker
the bootstrap requires (the decision on stronger checkers), admitted
beside the first, the checker with a step of conversion, rather than
beside the base checker: its certificates are the conversion checker's
with leaves for holes, its translation targets the conversion checker,
and soundness chains from holes to conversion to the base, as Milawa's
levels layer ({ref "the-next-phase"}[The next phase]). Its conclusions
are conditional, the obligations of the holes implying the goal, which
the base checker can state, so admission applies to it as to any
checker. Admitting a checker of open sketches is not admitting their
unresolved conclusions, and an unresolved hole never becomes an axiom.
It rests on the metalogic's prover in Geb, which is complete.

The checker of holes in programs is written now, in Lean, in the
suspending form. A checker written as Canonical-min's is, suspending at
unassigned metavariables, reports each hole's goal as the constraints
suspended on it, so the report of holes and the search that fills them
share one implementation ({ref "search-synthesis"}[Search and
synthesis]). Canonical-min keeps suspended work as closures of Lean in a
continuation monad, through `partial` functions; the repository's rules
admit no function calling itself, so the checker keeps it as explicit
finite work items, each carrying its context, its substitution and the
check that remains, resumes those an assignment affects, and runs within
a natural-number budget, driven by recursors. That is the form a checker
written in Geb needs, so it is transcribed into Geb later and proved in
Lean to agree, by the method of the metalogic's checker. It extends
{name}`Geb.Kernel.fillHole` from one hole to many, and leaves
{name}`Geb.Kernel.infer`, the trusted checker, unchanged: a program with
holes checks exactly when its lambda-lifting does.

### Search and synthesis
%%%
tag := "search-synthesis"
%%%

The obligation of a hole is the interface to synthesis. A request
carries the frozen dependencies, the profile, the context, the target
type or proposition, the permitted grammar, examples and a budget of
resources; a result carries a candidate and, when a semantic property is
claimed, its certificate, with the revision of its input, so that it is
not applied silently to another hole. Failure or exhaustion of the budget
refutes nothing.

The target is explicit. Inhabiting a computational type such as
`Tree → Tree` specifies no behavior, so a program and a derivation of its
specification are searched together, sharing unknowns. A derivation of an
internal existential statement is not an executable witness
({ref "holes-and-search"}[Holes and search]), and a broader claim of
extraction needs its own theorem. For unique existence the repository
proves the property of descriptions
({name}`Geb.FreeTopos.Internal.description`). When a program is
requested, a term of the executable fragment is required.

In order of availability:

1. Lookup of matching local terms, introduction of constructors,
   application, rewriting by named theorems and bounded enumeration, with
   the prover as the producer of certificates: these make explicit typed
   holes useful without a new dependency.
2. A typed enumerator beside the combinator prover of
   `Geb/Prototypes/FreeTopos/Prover.lean`, recursing only through `iter`,
   `fold`, `para` and `foldr`, so that totality is given. The universal
   property of the fold reduces the synthesis of a recursive function
   from examples to that of its non-recursive step; candidates are pruned
   by observational equivalence and by evaluating partial candidates, the
   suspension of the refinement search below supplying the latter. A
   certificate is the kernel term with its examples, checked by typing and
   evaluation, or, against a specification, a derivation from the
   prover's normalization and induction.
3. Search over the prover's choices, with equality saturation whose
   explanations become the prover's certificates of rewriting, and
   refinement in the manner of Canonical for choices of induction, motive
   and lemma.
4. SMT and syntax-guided synthesis for fragments with suitable encodings.
   Z3 already proposes decorations in the elementary-affine prototype,
   `scripts/eal/eal.py`, validated in Geb; cvc5's SyGuS interface also
   restricts candidates by a grammar. An SMT proof is not a Geb proof: its
   theory, Boolean reasoning and encoding must be related to the
   constructive metalogic, and a proof of unsatisfiability of the negated
   goal in a classical encoding yields constructively only a doubly
   negated conclusion. A first integration takes candidates checked by
   Geb's rules, or a fragment with a proved translation of certificates,
   and a report of no solution is never trusted.
5. Shared enumeration in the manner of SupGen. Superposition is a
   representation of search, not a new constructor of the accepted
   language; the decoded result passes Geb's checker whatever found it.
   The fourth stage of the interaction-net arm of
   {ref "choice-of-machine"}[the choice of machine], superpositions for
   searching certificates, is where it would enter, after typed and
   shared enumeration are compared on one finite grammar and set of
   obligations, measuring generation, checking, size of certificates,
   time and peak memory together.

Constraint pruning and sharing address different costs and may later be
combined. None of these is a prerequisite for preserving source across
revisions of the bootstrap; synthesis produces source and constrains the
format through holes only.

Three properties of Geb fit Canonical ({ref "holes-and-search"}[Holes and
search]).

* A checker of Geb is a fold over a tree of rule applications, that is,
  over the terms of a signature of the Logical Framework: judgements are
  families of types indexed by the terms they relate, and rules are
  constants. An inhabitant of a judgement is, after decoding, a
  certificate for Geb's trusted checker to check again, and a wrong
  encoding costs completeness, never soundness.
* Canonical's metavariables with local contexts are the metavariables of
  contextual modal type theory, and a checker written as Canonical-min's
  is reports each hole's goal as the constraints suspended on it: the
  report of holes and the search that fills them are one program
  ({ref "typed-holes"}[Typed holes]).
* Canonical accepts reduction rules. Given the kernel's computation rules
  (β, projections, the folds at constructors) as rules, an equation that
  holds by computation holds definitionally, and the search is left the
  structural choices of induction, motive and lemma, which complements
  the normalizing prover.

Experiments were made on one machine with Canonical and Canonical-min at
Lean v4.34.0, the goals stated in Lean as Canonical-min's DTTBench states
them, the signature as hypotheses:

:::table +header
*
  * Goal
  * Encoding
  * Canonical
  * Canonical-min
*
  * `foldr cons nil xs = xs`
  * Rules of Gödel's T as axioms
  * Found, about 1 s
  * Not found in 60 s
*
  * Uniqueness of the right fold
  * The same, with symmetry and congruence of an argument
  * Found, about 100 s
  * Not run
*
  * Uniqueness of the right fold
  * Equality by reflexivity and a Leibniz eliminator
  * Not found in 180 s
  * Not run
*
  * Associativity of appending
  * Rules of Gödel's T as axioms
  * Not found in 60 s
  * Not run
*
  * The three theorems above
  * Lean's `List`, the fold's equations as reduction rules
  * All found, 11 s in all
  * Not run
*
  * Length and sum of `List Nat` from three examples each
  * Lean's `List` and `Nat`
  * Not found in 30 s and 60 s
  * Not run
:::

The machine has 16 threads (AMD Ryzen AI 9 HX 370); Canonical used all
of them. Canonical-min was measured at the revision the survey names,
Canonical at tag `v4.34.0` of CanonicalLean. To reproduce: the manifest
of Canonical-min pins an untagged revision of CanonicalLean, for which no
release archive exists, so the revision is replaced by the tag's; and the
tactic's native library is loaded when a goal is built as a module of the
package by `lake build`, not by `lake env lean`.

The signature of the rules of Gödel's T over lists, in higher-order
abstract syntax, with nothing computing definitionally, is:

```
(Ty : Type) → (Tm : (A : Ty) → Type) →
(Eq : (A : Ty) → (a : Tm A) → (b : Tm A) → Type) →
(trans : (A : Ty) → (a b c : Tm A) → Eq A a b → Eq A b c → Eq A a c) →
(List : (A : Ty) → Ty) → (nil : (A : Ty) → Tm (List A)) →
(cons : (A : Ty) → Tm A → Tm (List A) → Tm (List A)) →
(congCons : (A : Ty) → (x : Tm A) → (xs ys : Tm (List A)) →
  Eq (List A) xs ys → Eq (List A) (cons A x xs) (cons A x ys)) →
(foldr : (A B : Ty) → Tm B → (Tm A → Tm B → Tm B) → Tm (List A) → Tm B) →
(foldrNil : (A B : Ty) → (z : Tm B) → (s : Tm A → Tm B → Tm B) →
  Eq B (foldr A B z s (nil A)) z) →
(foldrCons : (A B : Ty) → (z : Tm B) → (s : Tm A → Tm B → Tm B) →
  (x : Tm A) → (xs : Tm (List A)) →
  Eq B (foldr A B z s (cons A x xs)) (s x (foldr A B z s xs))) →
(indList : (A : Ty) → (P : Tm (List A) → Type) → P (nil A) →
  ((x : Tm A) → (xs : Tm (List A)) → P xs → P (cons A x xs)) →
  (xs : Tm (List A)) → P xs) → …
```

For the goal
`Eq (List A) (foldr A (List A) (nil A) (λ x r. cons A x r) xs) xs`,
Canonical returns the following term, a derivation in these rules
(induction on the list, the fold's rules and congruence of `cons`), its
motive synthesized:

```
indList A (fun xs ↦ Eq (List A) (foldr A (List A) (nil A) (fun x r ↦ cons A x r) xs) xs)
  (foldrNil A (List A) (nil A) fun x r ↦ cons A x r)
  (fun x xs ih ↦
    trans (List A) (foldr A (List A) (nil A) (fun x r ↦ cons A x r) (cons A x xs))
      (cons A x (foldr A (List A) (nil A) (fun x r ↦ cons A x r) xs)) (cons A x xs)
      (foldrCons A (List A) (nil A) (fun x r ↦ cons A x r) x xs)
      (congCons A x (foldr A (List A) (nil A) (fun x r ↦ cons A x r) xs) xs ih))
  xs
```

The encoding is in higher-order abstract syntax, and Geb's checker of
Gödel's T works with de Bruijn contexts and hypotheses; the terms found
were not decoded into Geb certificates and checked, so they establish
which encodings search well, not a working route. Four conclusions
follow from the measurements, within their small number.

* With the rules as axioms, Canonical finds derivations of a few steps
  with a synthesized motive, and those that chain several equational
  steps take minutes or are not found, as its paper reports of
  equational problems. Explicit rules of congruence, which Geb's checkers
  have, served better than a Leibniz eliminator here.
* With the computation rules as reduction rules, the same theorems are
  found in seconds, the search being left the induction and its motive.
  This is the configuration of the first stronger checker, a checker with
  a step of conversion to a normal form under named rules: a term found
  against reduction rules is a certificate of that checker, which reaches
  the metalogic's derivations through the translation that admits it.
  Canonical returns such proofs as `simp only` steps with the equations
  it rewrote by, which is the information that translation needs.
* Programs from examples are not found, the released tactic lacking the
  mode for synthesis; they remain the enumerator's.
* Canonical-min, without the heuristics and parallelism of the solver in
  Rust, did not find the shortest derivation in 60 s; it specifies the
  algorithm rather than serving as a solver.

The operations that transfer to Geb are three: each unknown has its
declaring context and an explicit substitution at each use, and a
candidate application is its head with all its argument holes; a check
needing an unassigned hole is suspended on it while independent checks
continue; and a step chooses a hole and a head, allocates the argument
holes together, resumes the checks waiting on that assignment, rejects
the branch when a constraint fails, and undoes its assignments and
constraints on backtracking. Two routes implement them:

:::table +header
*
  * Route
  * Benefit
  * Work required
*
  * Encode Geb's derivations as a signature for Canonical
  * Exercises an existing, parallel search at once
  * Specify the signature, scoping, substitution and decoding exactly;
    decode each found term into a Geb derivation and check it; a Lean
    proof of an analogous statement alone is insufficient
*
  * Implement refinement over Geb's terms and derivations
  * Uses the actual language and checker; a bounded search written in
    Geb survives the bootstrap
  * Contextual metavariables and suspended constraints; checking,
    branching and reduction adapted to partial syntax
:::

The second is the implementation meant to last, and the first serves
experiment. The Geb-native search starts from the finite grammar of
selected heads and proof rules for actual obligations; for logical goals
it searches for a Geb derivation of the sequent, and for computational
goals it shares the holes of a candidate term with the derivation of its
required property, which needs no dependent types in Geb's object
language. It reuses the internal-language prover of
`Geb/Prototypes/FreeTopos/Internal/Prove.lean`, scoped matching of
theorems, normalization producing certificates, function extensionality,
case analysis and combinators of induction, whose matcher handles
supplied terms, suspension and shared unknowns being additional work
rather than an existing general unifier; normalization in search uses
justified computational equations and does not treat equality in the
metalogic as decidable by normalization. Where Canonical-min keeps
suspended work as closures of Lean, a first implementation in Geb keeps
it as explicit finite work items carrying contexts and substitutions,
resumes only those an assignment affects, and bounds search and reduction
by a natural number, returning unfinished state when the bound is spent,
so that each run is a total operation of System T that the host may
repeat; a heuristic entropy in floating point is not needed at first.

Its obligations are separate: checking every completed candidate gives
correctness of accepted results through the existing checker; correct
pruning also needs that a rejected partial state has no valid completion;
and completeness also needs coverage of the chosen grammar, correct
scoping and backtracking, and fair exploration as bounds grow. An
exhausted finite run establishes none of the global claims. The first
experiment compares refinement with typed enumeration on one finite
grammar, with composition, repeated holes under binders, a proof
constraining an earlier witness, and a fold stuck on an unknown argument;
it replays every certificate and records nodes searched, reduction, time
of checking and size of certificates; the search for induction motives
follows once the basic constraints work, the existing combinators of
induction serving meanwhile. It needs contextual holes richer than
{name}`Geb.Kernel.fillHole`.

Nothing in the source format is needed beyond the syntax of holes; the
checker of holes is written to suspend, so that it serves as the
search's checker; and the Geb-native refinement is the lasting
implementation. Canonical is a dependency of the package for experiments
throughout the bootstrap (the decision on Canonical). It enters
`lakefile.toml` at tag `v4.34.0`, which was measured to build and run
under the repository's toolchain, and has no dependencies of its own. The
experiments form a library of their own that no module of `Geb`,
`GebLang` or `GebTests` imports, so a default build never fetches its
solver library, and committed experiments call the solver as a program,
the tactic leaving `sorry`, which committed code excludes, and check what
they decode with Geb's checkers, the first route above. `TODO.md`
§ Triggers records the condition for removing it: everything done or
planned with it written in Geb, or writable in Geb by the Geb-native
search.

### Proof scripts and certificates
%%%
tag := "proof-scripts"
%%%

Before many proofs are written in Geb, the durable artifact is fixed.
Scripts are the source. A certificate is kept with its statement, theory
and profile, dependencies and format, and replayed, or translated by a
certified translator, when rules or encodings change. Certificates,
derivations under the fixed rule set, are cached artifacts of the build,
keyed by the statement and the elaborated definitions it cites, and a
script that fails after a change of the prover falls back to its cached
certificate while it is repaired. The complete proofs about the
compiler's components have from 600000 to 1240000 nodes, so the cache
holds the form of shared certificates. The metalogic has no surface
syntax for statements in Geb text yet, and it will need its own
retraction at the level of documents.

### Further requirements
%%%
tag := "further-requirements"
%%%

Before substantial authoring, each of the following has at least the
contract stated.

:::table +header
*
  * Requirement
  * Minimum contract
*
  * Schema and feature versions
  * Syntax, core, annotations, certificates and semantic profile are
    identified separately; an unsupported mandatory feature is rejected
    and an optional field kept opaque.
*
  * Persistent data
  * Serialized values, tags of datatype constructors, examples and saved
    inputs of programs are versioned interfaces; migrating code does not
    migrate values stored outside it.
*
  * Library behavior
  * Dependencies are frozen; an implementation is replaced only with
    proved equality for the observations its interface permits, or kept
    under its old identity (the compatibility contract).
*
  * Verification boundary
  * Which steps of parsing, elaboration, serialization, code generation
    and host execution are proved and which tested is stated, and
    correctness is carried through the whole path that runs a program.
*
  * Reproducible builds
  * Source, the closure of dependencies and the compiler profile are
    kept; the identities of document, checked core and generated
    artifacts are distinct; a corpus of previously accepted programs is
    kept.
*
  * Diagnostics
  * A structured result of success or error with its source occurrence;
    an empty output of the compiler is not an interface for developers.
*
  * Editing and recovery
  * Incomplete documents, obligations of holes and unattached annotations
    are saved; drafts are distinguished from accepted programs; updates
    of several artifacts are atomic.
*
  * Performance and limits
  * Exhaustion of resources is distinct from falsity and from
    ill-typing; representative operations of editing, checking and
    compiling are measured; implementations may improve without promising
    equal cost.
*
  * Reflection
  * Representations of code are distinguished from ordinary data; which
    structural observations are stable, and how quoted schemas migrate,
    is stated.
*
  * Host protocols
  * Contracts of bytes, framing, errors and types of entry points are
    fixed independently of files, the width of machine words and the
    names of backends (files, editions and the host boundary).
:::

### The sequence and its acceptance
%%%
tag := "authoring-sequence"
%%%

Before most Geb code is written, in this order; the steps that change
`bootstrap/reader.geb` and the committed images follow other work on the
reader:

:::table +header
*
  * Step
  * Acceptance
*
  * Adopt the document reader and the formatter
  * `bootstrap/` formatted in one mechanical change with images and
    emitted Lean unchanged, as measured above; `geb-fmt --check` and the
    test of parinfer's fixed points in continuous integration
*
  * The authoring profile and the importer; the kernel's readers reading
    the profile and rejecting duplicate and ambiguous names
  * The retraction proved for the profile over S-expressions with
    comments at every layout; the bootstrap sources converted, with names
    and comments kept, compile to the same checked bundles; both readers
    read the profile, reject duplicates and accept every converted source
*
  * The strict encodings of RFC 9804: canonical, basic and advanced
  * The retraction proved for each over the same S-expressions with
    comments, their decorations as annotation forms; the bootstrap
    sources convert among the four syntaxes and compile to the same
    checked bundles
*
  * Modules with parameters, imports and export lists
  * The bootstrap sources, organized into modules with export lists and
    without the prefixes that avoided collisions, compile and pass their
    tests; a clash, an unresolved name and an import leaving a parameter
    unsupplied are rejected
*
  * The datatype language's completion
  * Every source of the datatype language retyped with datatype names as
    exact types, checked at every use, with representation and decoding
    written explicitly, generated recognizers and opaque type parameters,
    compiles and passes its tests; the soundness of the typing is proved
    with the prover in Geb
*
  * Manifests with editions; the record of elaborated definitions
  * The build and tests read manifests; the regenerated record equals the
    committed one
*
  * A durable document with versioned profiles
  * Declaration and binder names, prose, examples, links and unknown
    optional fields survive reading, printing and conversion
*
  * Hygienic elaboration, explicit assembly, diagnostics
  * Shadowing a primitive cannot alter generated operations; imports
    resolve deterministically; failures name a source occurrence and
    preserve existing outputs
*
  * Markup and conventions of comments; documentation
  * One Geb module renders prose, a checked example and a link through
    Verso; editing only its documentation leaves the core identity
    unchanged
*
  * The `geb` language with Mike's Paredit
  * The pinned extensions pass the profile's fixture
:::

Early in writing, alongside the first substantial module where it helps:
`let*` and `cond`; the syntax of holes, the suspending
checker of holes in programs and the display of their obligations;
diagnostics with locations through efm-langserver; literate pages
generated from documents; and the typed enumerator. When their consumers
exist: digests and the store, `attach` and hover text, a language
server, tree-sitter, holes in proofs, the cache of certificates, the
export to canonical S-expressions, and the Geb-native refinement search.
The library then written in Geb drives content storage, richer language
services, adapters to solvers and optimization of the runtime; none of
them may discard the document, binding or dependency information already
kept. The limits that more Geb code meets are among the improvements
({ref "improvements"}[Improvements]): the Geb reader's stack in
proportion to a program's length, about 480 bytes of memory per byte of
input, the rebuilding of every test module on a change of a Geb source,
and a Geb compiler that names no failing definition.

Acceptance: a documented module survives conversion among the syntaxes
of RFC 9804 and the authoring profile, retaining names, comments,
examples, links and dependency resolution, and compiles to the same
checked core. A documentation-only edit leaves core identity unchanged.
Its documentation renders through Verso. The `geb` editor language with
Mike's Paredit preserves the parsed document. A typed hole displays its
context and target, accepts a well-typed filling without capture, and
prevents a remaining obligation from being reported as a completed
theorem. These conditions concern authoring; network storage and a second
runtime are independent of them.

## The logic
%%%
tag := "logic"
%%%

:::table +header
*
  * Part
  * State
*
  * Gödel's T: the rule set and its soundness
  * Complete
*
  * Gödel's T: the checker in Geb
  * Complete
*
  * Gödel's T: proof construction and proofs
  * In progress: the proofs of the prelude's lists and labels and of the
    checker's accessors are complete in Gödel's T, whose checker and
    prover are retired; the rest are proved in the metalogic, the
    preservation of types by weakening and by substitution and the
    identity of the datatype language's expansion complete, and the
    admission of stronger checkers waiting on the metalogic's checker in
    Geb
*
  * Metalogic: the rule set and its soundness
  * Complete: the rule set, its checker and their soundness in every
    model, and the model of Lean's types and functional relations, with
    a model from every topos with chosen structure and the data objects
*
  * Metalogic: the checker and prover in Geb
  * In progress: the checker is written in Geb and compared with the Lean
    checker; the prover and the proof in Lean of the checker's agreement
    are ready
*
  * Acceptance
  * Met for Gödel's T; waiting, for the metalogic, on the proof of its
    checker's agreement
:::

The metalogic's checker ({ref "metalogic-and-checker"}[The metalogic and
its checker]) is built by the parts below, as that of Gödel's T was
built first; the checker of Gödel's T is retired.

* The rule set and its soundness, in Lean, without `Classical.choice`,
  in the model of Lean types, and for the metalogic also in a model that
  is not Boolean. For Gödel's T this part depends only on
  {ref "kernel-in-lean"}[The kernel runs in Lean].
* The checker in Geb, a fold over proof objects, compared with the
  Lean checker on valid and malformed certificates; for the metalogic,
  also proved in Lean to agree with the Lean checker, its denotation at
  every development being the Lean checker's result.
* Proof construction in Geb, and proofs about Geb programs that
  exercise it, the compiler's components first, each in the metalogic
  about the programs' translations, the checker of Gödel's T being
  retired ({ref "functional-relations"}[Functional relations and the
  checker of Gödel's T]); and stronger checkers admitted by relative
  soundness proofs, each a translation of their certificates into the
  metalogic's derivations, proved in the metalogic. The rest of what the
  metalogic states, the richer definitions, the setoid language, the
  mathematics the libraries consume
   and the equivalence of the free topos with the rose-tree object and
   the free topos with a natural numbers object, is written in Geb
   after the bootstrap (the road map).

Acceptance, for each checker: a theorem with hypotheses, a substitution
and an induction checks, and certificates with altered binders, invalid
dependencies or false conclusions fail; for the metalogic, a
characteristic map checks as well, and the checker written in Geb is
proved in Lean to agree with the Lean checker.

For Gödel's T, the rule set and its soundness are constructed.
`Geb/Prototypes/Kernel/Subst.lean` weakens kernel terms and
substitutes for their innermost variable through one traversal
({name}`Geb.Kernel.trav`), and proves that both agree with the
denotation ({name}`Geb.Kernel.infer_wk`, {name}`Geb.Kernel.infer_subst`).
`Geb/Prototypes/GoedelT/Equations.lean` defines a sequent as a
context, a list of hypotheses and a conclusion, each an equation
between two kernel terms of a type, valid when both sides of the
conclusion have its type and their denotations agree at every value of
the context at which the hypotheses hold ({name}`Geb.GoedelT.Valid`).
A certificate is a rose tree whose label names a rule, and the checker
{name}`Geb.GoedelT.check` is a paramorphism over it whose result, as
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
rule rests on {name}`Geb.GoedelT.load_loaded`, by which each of a
loaded program's definitions denotes its global in the whole
environment, since extending an environment keeps every denotation
({name}`Geb.Kernel.infer_append`). {name}`Geb.GoedelT.check_sound`
proves every computed conclusion valid, without `Classical.choice`. The
examples of `GebTests/Prototypes/GoedelT.lean` meet the acceptance for
Gödel's T: a theorem from a hypothesis by congruence, an
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
({name}`Geb.GoedelT.axioms`). The rose-tree object's structure map
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
({name}`Geb.GoedelT.axioms_valid`), and one rule cites an axiom or a
theorem at terms for its variables ({name}`Geb.GoedelT.valid_thm_inst`).

The checker evaluates no term but a primitive at literals. A Geb
program that evaluates kernel terms takes a step bound (the section on
the metalogic and its checker), so a checker written in Geb could not
apply a rule evaluating every closed term, and a Lean checker with that
rule would not be the Geb checker's specification. The evaluation of a
closed term is derived instead, from the δ rules, the computation rules
and congruence, by a certificate whose size grows with the length of
the evaluation.

For Gödel's T, the checker in Geb is constructed as well.
`bootstrap/goedel-t/equations.geb` is the checker written in the
datatype language,
deciding as {name}`Geb.GoedelT.check` decides: a fold over the
certificate whose result at each node is the node paired with its
conclusion as a function of the context and the hypotheses, over the
traversal, weakening and substitution of kernel terms and the values of
the primitives written in Geb, with `bootstrap/check.geb` typing terms
in a context. The examples of `GebTests/Prototypes/GoedelT.lean`
compile it with the stage-0 compiler and compare its conclusion with
the Lean checker's at the certificates above, one certificate of
each rule besides, and malformed variants of each, the certificate's
root relabelled with every rule's label and one beyond or deprived of
its last child; the two agree on every one, the tables of axioms
included. The labels of the kernel's constructors, the primitives'
indices and the checker's rules are named by numeral abbreviations in
`bootstrap/prelude.geb` and `bootstrap/goedel-t/equations.geb` and by
abbreviations in Lean, `Geb.Kernel.Label`,
`Geb.Kernel.Prim` and `Geb.GoedelT.Rule`, which the
tests hold equal name for name.

The checker of Gödel's T written in Geb is also proved in Lean to agree
with the Lean checker, by a method the metalogic's checker reuses. The
stage-1 compiler's Lean backend emits the checker's program as Lean
definitions, one for each of its definitions, committed as
`bootstrap/lean/GebMirror/GoedelT.lean` and compared with a fresh
emission by `scripts/bootstrap.sh check`.
`GebTests/Prototypes/GoedelT/MirrorLoad.lean` states that loading the
program with {name}`Geb.Kernel.load` gives globals whose denotations are
those definitions, one definition at a time, each step closed by
reflexivity, which the kernel checks by evaluating the checker-evaluator
in the loading mode `rfl`, and stated as an axiom in the mode `native`
(`docs/rules/ci-and-workflow.md` § Loading modes). The other modules of
`GebTests/Prototypes/GoedelT/` prove, side by side, that the emitted
definitions compute what the Lean checker computes: the type checker,
the traversal of terms with weakening and substitution, the operations
on equations and theorems, the values of primitives at literals, and
each rule, assembled by induction on the certificate.
`GebTests/Prototypes/GoedelT/Agreement.lean` states the result: at every
certificate, program, theorems, global environment, context and
hypotheses, encoded, the loaded checker gives the encoding of what
{name}`Geb.GoedelT.check` gives, so the two accept the same certificates
with the same conclusions. In the loading mode `rfl` the proof depends
on no axiom beyond `propext` and `Quot.sound`; in the mode `native` it
depends also on the axioms stating the loading.

The metalogic's checker is written in Geb in `bootstrap/free-topos/`, in
the datatype language, deciding as the Lean definitions it transcribes
decide: `base.geb` holds optional trees, truth values and lists;
`partial-horn.geb` the sorts, scope and substitution of partial Horn
terms, sequents, the checker of certificates
({name}`Geb.PartialHorn.check`) and the extension of a theory by
definitions; `theory.geb` the theory of an elementary topos with the
data objects; `infer.geb` the checker's inference of typings;
`language.geb` the Mitchell–Bénabou language's terms, their renaming
and substitution and their compilation to the combinators; and
`derivation.geb` the checker of the language's derivations and of
developments ({name}`Geb.FreeTopos.Internal.checkDev`). A value of a
Lean structure or inductive type is the node of its constructor's
position over its fields, and a term or a derivation is the node of its
label's or its rule's position over the node of the label's or the
rule's data, followed by its children.
`GebTests/Prototypes/FreeTopos/GebCheck.lean` and
`GebTests/Prototypes/FreeTopos/GebCheckInternal.lean` load the program
with the stage-0 compiler's front end and compare its definitions with
the Lean definitions they transcribe: the checker of certificates at
valid certificates and malformed variants of each, the theory, the
inference at the sides of every axiom, and the checker of developments
at the developments of the language's tests, at each small development
with a declaration removed, and at declarations altered in their
equations, types, arities, objects, indices, certificates and
derivations, each checked in the state before the declaration it
alters.

`GebTests/Prototypes/FreeTopos/Agreement.lean` proves the checker
written in Geb equal to {name}`Geb.FreeTopos.Internal.checkDev`, by the
method of the checker of Gödel's T. The Lean the bootstrap compiler
emits from the program, `GebMirror.Metalogic`, is the denotation of each
of the program's definitions as {name}`Geb.Kernel.load` loads them,
checked by the kernel's evaluation in the loading mode `rfl`, and agrees
definition by definition with the Lean definitions it transcribes: each
fold of the program pairing a node's tree with its result is related to
a paramorphism of the tree it encodes, and the partial Horn logic, the
theory, the inference, the language and the checker of derivations and
developments each agree at every encoded input. At every development,
its constants, entries and declarations encoded, the loaded check gives
the encoding of the state the Lean checker gives, so the two accept the
same developments with the same results. In the loading mode `rfl` the
proof depends on no axiom beyond `propext` and `Quot.sound`; in the mode
`native` it depends also on the axioms stating the loading.

The translation of kernel programs into the Mitchell–Bénabou language is
written in Geb in `bootstrap/free-topos/translation.geb`, translating as
{name}`Geb.FreeTopos.Translation.term` translates, in one program with
the checker, the reader and the kernel's type checker, whose types of
the kernel's constants and primitives it shares.
`GebTests/Prototypes/FreeTopos/Agreement/Translation.lean` proves its
mirror equal to the Lean translation by the same method: the types, the
library, the numerals, whose base-two digits are the bijective
numeration's, the quoted trees, the kernel's constants and primitives,
and the translation of a term, each node's step related to the step of
the paramorphism {name}`Geb.RoseTree.para` of the term. At every
program, every translated program's definitions and every theorem of
Gödel's T, the loaded translation gives the encoding of the Lean
translation's result. In the loading mode `rfl` the proof depends on no
axiom beyond `propext` and `Quot.sound`; in the mode `native` it depends
also on the axioms stating the loading.

The language's prover is written in Geb in
`bootstrap/free-topos/prove.geb`, in the same program, proving as
{name}`Geb.FreeTopos.Internal.byNorm` and the provers beside it prove:
the matching of patterns, the rewriting at a term's root by the
normalizer's rules, normalization innermost first, the reduction to a
depth through weak head normal forms, and the proofs of an equation by
normalization, by induction, by extensionality and by case analysis. A
rule of the normalizer is its encoding paired with a matching, which the
preparation of a theorem computes once from the theorem's left side.
`GebTests/Prototypes/FreeTopos/GebProve.lean` compares it with the Lean
prover at the proofs of the test modules, and
`GebTests/Prototypes/FreeTopos/Agreement/Prove.lean` proves it equal to
the Lean prover by the same method: at encoded arguments, rules related
to the normalizer's and provers related to Lean's, each of its entry
points gives the encoding of the Lean prover's derivation, so that the
prover written in Geb constructs exactly the derivations the Lean prover
constructs. In the loading mode `rfl` the proof depends on no axiom
beyond `propext` and `Quot.sound`; in the mode `native` it depends also
on the axioms stating the loading.

The tactics the proofs about the compiler's components compose from the
prover are written in Geb in `bootstrap/free-topos/tactics.geb`, in the
same program, as {name}`Geb.FreeTopos.Tactics.byAuto` and the tactics
beside it compose them: proofs by reduction to a depth, by induction and
case analysis of lists, bitstrings, rose trees, coproducts and trees,
with hypotheses and their instances cut in as rewriting rules, by the
search of the hypotheses' instances and of the variables the sides are
stuck on, and by rewriting under a conditional's mask.
`GebTests/Prototypes/FreeTopos/GebTactics.lean` compares them with the
Lean tactics at the theorems of the test modules and at their subterms,
and `GebTests/Prototypes/FreeTopos/Agreement/Tactics.lean` proves each
of their definitions equal to the Lean definition it transcribes by the
same method, at encoded arguments, rules related to the normalizer's,
provers related to Lean's and provers from rules related to Lean's. In
the loading mode `rfl` the proof depends on no axiom beyond `propext`
and `Quot.sound`; in the mode `native` it depends also on the axioms
stating the loading.

The combinator prover, which proves equations of the theory of an
elementary topos and certifies them for the checker of partial Horn
theories ({name}`Geb.FreeTopos.Prover.normalize` and the tactics beside
it), is written in Geb in `bootstrap/free-topos/combinator.geb`, in the
same program: the typing of terms by their canonical objects, the match
of a rule's side against a term up to canonical objects, rewriting at a
term's root and through associativity, normalization innermost first,
the proofs by normalization and by induction on the natural numbers
object and on list objects, and the library of derived equations. Its
state records typings and normal forms in association lists where the
Lean prover's records them in hash tables.
`GebTests/Prototypes/FreeTopos/GebCombinator.lean` compares it with the
Lean prover at the library and at the benchmark's development, and
`GebTests/Prototypes/FreeTopos/Agreement/Combinator.lean` proves each of
its definitions equal to the Lean definition it transcribes by the same
method, at encoded arguments and related states, a list related to a
table when their lookups agree. In the loading mode `rfl` the proof
depends on no axiom beyond `propext` and `Quot.sound`; in the mode
`native` it depends also on the axioms stating the loading.

Proof construction was begun for Gödel's T. `bootstrap/goedel-t/prove.geb`
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
expanded, resolved and typed as the program is, its forms of the
datatype language
expanded by the stage-0 expansion that the prover carries, and each
theorem's certificate is checked against its statement, citing the
theorems before it. `bootstrap/proofs/prelude.geb` proves the empty
list a unit of appending and appending associative;
`bootstrap/proofs/nat.geb` derives addition's recursion equations from
its definition by iteration and proves zero a left unit of addition by
induction on labels; `bootstrap/proofs/check.geb` proves, about the
kernel's type checker written in Geb, that a quoted tree has the type of
trees in every context and environment; `bootstrap/proofs/equations.geb`
proves, about the checker of Gödel's T written in the datatype
language, that the
accessors of an equation return the fields it is built from; and
`bootstrap/proofs/datatype.geb` derives the recursion equations of a
function by structural recursion over a declared datatype from its
expansion. The examples of
`GebTests/Prototypes/Proofs.lean` check every certificate in Geb and
again with {name}`Geb.GoedelT.check`, and reject a false equation and
an unproved one. This checker and its prover are retired
({ref "functional-relations"}[Functional relations and the checker of
Gödel's T]): their proofs remain and are checked, and the proofs that
follow them are made in the metalogic, about the programs' translations.

### Gödel's T
%%%
tag := "goedel-t"
%%%

Gödel's T {citep Goedel1958}[] is the quantifier-free theory of the
primitive recursive functionals of finite type: its atomic formulas are
equations between terms of one type, and it has a rule of induction
({citet AvigadFeferman1998}[], Section 2.2). The equational theory of
the kernel's terms is a variant of it, called Gödel's T in this
chapter: the functionals are the kernel's terms, of the unit, product,
function, list and tree types, the rose trees with natural-number labels
standing in place of the natural numbers; a formula is a sequent, an
equation under equational hypotheses; and the rules are the laws of a
cartesian closed category with list objects and a rose-tree object, the
η rules among them. Its checker, the bootstrap's first, is built by the
parts above, and is retired: a kernel program is interpreted soundly in
the free topos by its translation into the Mitchell–Bénabou language
({ref "functional-relations"}[Functional relations and the checker of Gödel's T]).

Its category of contexts under equational hypotheses is conjectured to
be a cartesian closed locos (the road map, after the bootstrap). Since
the kernel's types include no coproducts and no empty type, the
conjecture rests on constructing them from the others: the object of
two elements cut out of the trees by an equation; a coproduct cut out
of the product of that object, the tag, with the two summands, each
summand's hypotheses guarded by the conditional on the tag and the
component the tag does not select fixed at an element of its type,
which every kernel type has; and the empty object as the terminal object under the hypothesis
that two distinct leaves are equal. That these coproducts are disjoint
and stable under pullback is not proved.

Gödel's T states and proves the following.

* Judgment: a context of kernel types, a list of equations as
  hypotheses, and an equation between kernel terms of a type; valid
  when both sides denote one value at every value of the context that
  satisfies the hypotheses ({name}`Geb.GoedelT.Valid`). Complete.
* Types and terms: the kernel's, of every type. Complete.
* Rules: equality, congruence of every term former, the β and η rules,
  the δ rules at literals, weakening, cut, instantiation, the
  computation rules of the kernel's eliminators, induction on lists,
  trees and labels, the unfolding of definitions, iteration's reading
  of the label, the conditional as an iteration, and citations of
  axioms and of theorems, each named in `Geb.GoedelT.Rule`.
  Complete.
* Axioms: the defining equations of the primitives
  ({name}`Geb.GoedelT.axioms`). Complete.
* In Lean: soundness in the model of Lean types
  ({name}`Geb.GoedelT.check_sound`). Complete.
* In Geb: the checker `bootstrap/goedel-t/equations.geb`, complete;
  the prover `bootstrap/goedel-t/prove.geb`, with normalization,
  rewriting, induction and the forms of the datatype language, begun;
  both retired, equations between kernel programs being proved in the
  metalogic.
* Proofs of the bootstrap, which exercise a prover on the compiler's
  components, in order, those of lists and labels and of the checker's
  accessors in Gödel's T and the rest in the metalogic, about the
  components' translations:
  * lists and labels: the prelude's appending, addition's recursion
    equations and zero as a unit of addition, complete;
  * the accessors of the checker's equations, and the recursion
    equations of a structural recursion, through the expansion of the
    datatype language, complete;
  * the type checker's preservation of types by weakening and by
    substitution, complete;
  * the identity of the datatype language's expansion on programs of
    kernel forms, complete;
  * the reader's inverse to the printer, waiting on the printer;
  * the admission of a stronger checker by the proof that a Geb
    program translates its certificates into the metalogic's
    derivations with the same conclusions, ready: it is admitted beside
    the metalogic's checker written in Geb, whose agreement with the
    Lean checker is proved.
* After the bootstrap: equational theorems about programs, in the
  metalogic.

The preservation of types by weakening is proved in the metalogic
(`GebTests/Prototypes/FreeTopos/Weakening.lean`): for every environment
`G`, contexts `c1`, `c0` and `c2` and term `t`,
`typeIn G (append c1 (append c0 c2)) (wkAt (length c1) (length c0) t)`
equals `typeIn G (append c1 c2) t`, weakening past a list of types, of
which weakening past one is the instance at a list of one, about the
translations of the prelude, the reader, the type checker and the
checker of Gödel's T, read and expanded by the stage-0 compiler's front
end. The two sides, as functions of `G`, `c1`, `c0` and `c2`, are equal
by induction on rose trees with an
induction hypothesis ({name}`Geb.FreeTopos.Internal.roseIndHyp_sound`).
At a construction the label's bits are split, which decides every test
the traversal and the checker make on it. Where the label's case depends
on its children's types, the list of the children is split to their
number, with the induction hypothesis, which mentions the list,
reverted into an implication and introduced again in each case, and
instantiated at each child, at `c1` or, under an abstraction, at `c1`
extended by the abstraction's type. At a variable, a lookup lemma
relates the index moved past the inserted types to the index, by
induction on `c1` and, below it, on `c0`.

The sides are compared in weak normal form, which leaves the steps of
folds and the bodies of abstractions unreduced, so that the fold at a
child that is a variable does not unfold the checker; they are
rewritten by a development of lemmas. The conditionals are moved through
projections, applications and folds; the folds' first components rebuild
their trees and lists, whose lengths are the lengths of the lists they
come from, the traversal's at every function it applies at a variable,
which weakening and substitution instantiate; and the labels' arithmetic
gives the addition of one as the successor, the addition of a successor
on either side as the successor of the sum, the comparison of two
successors, iteration at a successor and the successor of a
predecessor, each by induction on bitstrings with case analysis of
their bits. The prover finds those proofs by
instantiating the induction hypothesis where its body occurs in a normal
form and splitting a variable the normal form is stuck on. At a label
it tries the language's rules and the definitions alone first, and the
lemmas after them, each matched by a matching of its left side prepared
once ({name}`Geb.FreeTopos.Internal.prepareRules`). The lemmas'
derivations have 60492 nodes and the theorem's 540159, which the prover
finds in 60 seconds and the checker checks in 31.

The preservation of types by substitution is proved in the metalogic
(`GebTests/Prototypes/FreeTopos/Substitution.lean`): for every
environment `G`, contexts `c1` and `c`, type `a` and terms `u` and `t`,
if `typeIn G c u` is `some a`, then
`typeIn G (append c1 c) (trav (substVar u) t (length c1))` equals
`typeIn G (append c1 (cons a c)) t`, of which the metalogic's `subst`
is the instance at the empty `c1`. The statement is an equation between
two functions of `G`, `c1`, `c`, `a` and `u` into the subobject
classifier, the implication of the equation by the typing and truth,
proved by induction on rose trees with an induction hypothesis as
weakening is. At each label the implication is introduced, and its
antecedent, in normal form, rewrites the substituted term's type; the
induction hypothesis's instances at the children are implications with
that antecedent, whose conclusions modus ponens cuts in. At the
substituted variable, the substituted term weakened past `c1` has in
the context of `c1` and `c` its type in `c`, by weakening past a list
below no part; the lookups before, at and past the substituted
variable's index are the lookup in the context with it, by induction on
`c1`, with lemmas on successors: a successor is not empty, the
predecessor, the double and the difference with one of a successor are
computed, and two successors are equal as their predecessors are. The
development, which contains the weakening proof, has 626085 nodes, of
which the lemmas substitution adds have 25434, and the theorem's
derivation 604928, which the prover finds in 66 seconds and the checker
checks in 35.

The identity of the datatype language's expansion on programs of kernel
forms is
proved in the metalogic (`GebTests/Prototypes/FreeTopos/Expansion.lean`):
for every list `es` of trees of which each is a kernel form,
`expandProgram es` is `some (node 0 es)`. A kernel expression is a tree
no list of which has a head that the reader names by the atom `case` or
`cata`, and a kernel form is a list of three trees whose head names
`def`, with a kernel expression as the third, `deftype` or `defnum`.
The predicates are folds written in Geb beside the statement, which is
an equation between masks: the conditionals on the predicate between
each side and `none`. The proof proceeds by equations of functions
under a mask: the expression's identity in every scope, by
induction on rose trees with an induction hypothesis, whose instances
at the children give, by induction on the children, an equation of the
lists of the two sides' functions; the identity of the expansion's step
at a form, which adds the form to the output and a type's alias to the
environment; the run over the forms, by induction on them; and the
program's, by the reversal of a reversal. The provers of
`GebTests/Prototypes/FreeTopos/TreeCases.lean` carry the proofs: a
compound test, such as whether a head names a keyword, is generalized
to a new tree variable and split by case analysis of trees, and a term
under a mask is rewritten by a hypothesis that holds under the mask's
test, the absorption lemma moving the rewriting into the branch the
test selects. The development has 668870 nodes, which the prover finds
in 72 seconds and the checker checks in 34.

### The metalogic
%%%
tag := "metalogic"
%%%

The metalogic is the free topos with the natural numbers, list and
rose-tree objects, presented at once and checked by one checker, which
is built by the method Gödel's T establishes: a checker defined,
proved sound in Lean and written again in Geb. This section states the
presentation, its relation to Gödel's T, and
the questions its form depended on, which were settled by constructing
and measuring.

#### The presentation
%%%
tag := "presentation"
%%%

State: complete, as the rule set of
{ref "rule-set-models"}[The rule set and its models].

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
architecture of the checker of Gödel's T: every term is a rose tree, the checker is a
fold over certificates whose conclusions are definedness and equality,
and the quotient is the equality the checker proves. Composition is
defined when the codomain of one morphism equals the domain of the
other, the equalizer's factorization when a
morphism equalizes the pair, and the characteristic map at a
monomorphism, a morphism whose kernel pair's projections are equal; each
condition is a premise of a rule, as the induction rules of Gödel's T
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

The certificates' language is the combinators, the terms of the
fibered presentation, a program being extended by definitions of
objects, of morphisms and of equalities in place of the definitions of
kernel terms. The internal language of the topos, the Mitchell–Bénabou
language, the intuitionistic higher-order type theory of the section on
the metalogic and its checker, is written over them: its terms compile
into the combinators by their interpretation in a topos, as the
datatype language is expanded into the kernel, and its derivations bind variables where
the combinators compose projections (the section on the
Mitchell–Bénabou language). A development mixes the two, its theorems
of the language and its sequents of the combinators each citing the
others.

The kernel remains the language of computation, since the free topos
has arrows that no System T term defines. The kernel's terms denote
arrows of the cartesian closed category with the data objects, and they
enter the presentation by their translation into the Mitchell–Bénabou
language, whose compilation into the combinators follows the
translation between λ-terms and the morphisms of a free cartesian
closed category that the Categorical Abstract Machine compiles by
{citep CousineauCurienMauny1987}[]
({ref "functional-relations"}[Functional relations and the checker of
Gödel's
T]).

The theory, its axioms and the certificates of its derivations are
finite syntax, rose trees, and so data of the metalogic: the checker is
a kernel program on them, and that a certificate derives a judgment is
an equation about that program, as in Gödel's T. The categorical
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

#### Definitions

State: complete for one sort in `Geb/Prototypes/Definition/`, and for
the partial Horn theory, in its models
({ref "definitional-extensions"}[Definitional extensions and shared
certificates]).

A term with references to definitions is checked and interpreted in an
environment of definitions, each an object or a morphism over the
definitions before it; the unfolding replaces each reference by its
definition, from the syntax with references to the syntax without; and
a theorem proved in Lean states that the interpretation of every term is
that of its unfolding.
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
({name}`Geb.Definition.Presentation.modelEquiv`). The form chosen is
this monadic one: definitions, from new operations to terms of a
signature, extend to a morphism of free monads from the extended
signature to the signature, which is the unfolding, and the defining
equations make it inverse to the inclusion of the signature's terms. The
definitional extension ({ref "definitional-extensions"}[Definitional
extensions and shared certificates]) carries that
structure to the partial Horn theory of
two sorts, a defined operation being defined where its body is and equal
to it there, iterated, so that a definition refers to earlier ones; a
theorem of a development is cited by its sequent, not unfolded into its
certificate. In Gödel's T a reference unfolds
one step at a time ({name}`Geb.GoedelT.valid_unfold`), resting on
{name}`Geb.GoedelT.load_loaded`; no theorem yet unfolds every
reference of a kernel term. The families of definitions of
`Geb/Prototypes/Definition/` and their linking form the Kleisli category
of the free monad of the signature, linking associative and the
variables its units ({name}`Geb.Definition.link_assoc`,
{name}`Geb.Definition.link_pure`, {name}`Geb.Definition.pure_link`),
the free monad's own laws being Cslib's.

#### The constructions and the choices

The questions are of two kinds. The first are constructions, each of
which is established by carrying it out:

* the rule set, the axioms of each operation above as partial Horn
  sequents with the rules of partial Horn logic, checked against its
  specification: its models are the elementary toposes with chosen
  structure and the data objects, which the literature establishes for
  some such rule set and not for this one ({ref "rule-set-models"}[The rule set and its models]);
* the model in Lean, with morphisms as functional relations: whether
  the universal property of every operation, the exponential's among
  them, holds there without `Classical.choice`, and so whether the rule
  set is sound in it ({ref "functional-relations"}[Functional relations
  and the checker of Gödel's T]);
* the definitional extension of a partial Horn theory in the monadic
  form, iterated: whether unfolding preserves the judgments of
  definedness and equality, so that certificates unfold as well as
  terms, and its unfolding theorem
  ({ref "definitional-extensions"}[Definitional extensions and shared
  certificates]).

The second are choices between options each of which is known to be
constructible:

* whether the Mitchell–Bénabou language is written during the bootstrap
  or after it ({ref "when-mb-written"}[When the Mitchell–Bénabou language is written]);
* whether Gödel's T keeps a checker and prover of its
  own, or its equations are proved in the metalogic through the
  translation of kernel terms, which depends on how the kernel's
  denotations, which are functions, relate to the model's morphisms,
  which are functional relations
  ({ref "functional-relations"}[Functional relations and the checker of
  Gödel's T]).

The rule set and its models precede the other two constructions, which
are independent of each other; the choices follow them. Each is
complete.

#### The rule set and its models
%%%
tag := "rule-set-models"
%%%

State: complete, with its converse.

The rule set's models are established in both directions. The rule set is
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
converse, a model of the theory from a topos with chosen structure and
the data objects ({name}`Geb.FreeTopos.ChosenTopos.isModel`), is made
with the model of functional relations
({ref "functional-relations"}[Functional relations and the checker of
Gödel's
T]). A model's
operations
({name}`Geb.PartialHorn.Model`) are partial functions whose domains of
definition are propositions, as mathlib's `Part` states them, so that a
model need not decide where an operation is defined: neither the
converse nor the model of functional relations is confined to a topos
whose
objects have decidable equality.

#### When the Mitchell–Bénabou language is written
%%%
tag := "when-mb-written"
%%%

State: complete; the Mitchell–Bénabou language is written during the
bootstrap.

The choice is made by measurement. Once the rule set's models are
established, the theorems proved in Gödel's T in
`bootstrap/proofs/prelude.geb` and `bootstrap/proofs/nat.geb` are
proved again in the combinators, and the two are compared on the size
of their certificates and the time to check them, and on how they read.
Programs remain kernel terms, so the choice does not change the speed
of the compiler, only that of checking the development written in the
combinators, whose certificates bind no variables and are the larger
for it. The Mitchell–Bénabou language is deferred while checking stays
within a small multiple of the time of Gödel's T and the proofs read as
their mathematics rather than as the arrangement of projections,
pairings and curryings. When either fails, it is written at the
earliest point at which it can be, once the rule set's models are
established, since its interpretation needs every operation of the
topos and neither the model of functional relations nor the definitional
extension. It is written as a logic of its own, with a
checker of its own. Its judgments state that hypotheses entail a
formula, a term of the subobject classifier's type, an equation being
the formula of equality; its certificates name its rules, as the
certificates of Gödel's T do, and the checker computes each
substitution, so that a certificate has the size of one of Gödel's T
rather than of the
combinators'. The checker is proved sound in Lean against the language's
interpretation in the free topos, and the language, with its citations
of the combinators' certificates, is proved complete for it. A user of
the language then proves theorems about its constructions in the
language they are written in, and the compilation states what each
construction means in the object language. Its terms
refer to the definitions made in the combinators before it, so that the
development continues in it without rewriting them.

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
the Lean checkers, the certificates of Gödel's T have from 22
to 1315 nodes and check in 29 milliseconds; the combinators' have from
4938 to 798736, from 70 to 1376 times as many, and check in 17 seconds.
Neither criterion holds. Checking takes several hundred times the
time of Gödel's T, and the statements, the definitions and the steps an
induction names are arrangements of projections, pairings and
curryings. The associativity of appending, `(append (append xs ys) zs)`
equal to `(append xs (append ys zs))` in Gödel's T, equates the arrows

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
it takes to check. The definitional extension, by which a certificate
names
a definition rather than repeating its expansion, bears on the size;
and a checker that infers definedness and canonical objects, as the
checker of Gödel's T infers the types of kernel terms, proved sound in Lean,
bears on the facts the certificates prove besides.

#### Definitional extensions and shared certificates
%%%
tag := "definitional-extensions"
%%%

State: complete for the models; the unfolding of certificates is ready.

The definitional extension is made for the models, where the checker
needs
it. A definition names a term of the signature in the variables of a
context, each of which occurs in it; the extension by it adds an
operation, defined where the body is and equal to it there, and defined
only there. A model of the theory expands to a model of the extension,
the operation read as the body's value, and the value of a well-sorted
term in the expansion is the value of its unfolding
({name}`Geb.PartialHorn.eval_expand_unfold`), which is eliminability; a
sequent of the signature valid in every model of the extension is valid
in every model of the theory ({name}`Geb.PartialHorn.valid_of_valid_extendAll`),
which is non-creativity. Definitions iterate, each over the signature
the earlier ones extend ({name}`Geb.PartialHorn.valid_unfoldAll`). A
certificate is checked in the extension, citing a definition by its
axioms, and the unfolding of every sequent a checked development proves
holds in every model of the theory
({name}`Geb.PartialHorn.checkDevelopment_extendAll_sound`), so no
certificate is unfolded. The unfolding of certificates into the theory
without definitions, which a checker of that theory alone would need, is
not constructed. The requirement that every argument occur in the body
keeps the strictness of an application: its unfolding, the body with
the arguments substituted, is defined only where each argument is.

The measurement is repeated with definitions. Appending, addition and
the curried cases of their recursions are definitions; the recursions'
computation equations are proved by unfolding them, and the theorems
with the recursions folded (`GebTests/Prototypes/FreeTopos/Benchmark.lean`).
The certificates have from 4245 to 395728 nodes, from 47 to 799 times
those of Gödel's T, and 536226 in all against 1007453 without
definitions. The
checker's environment of theorems is indexed by arrays, since the
certificates cite earlier theorems 35786 times; the development checks
in 16 seconds, 19 by lists. Of the certificates' nodes, 78 in 100 are
still terms that instances repeat, now the normal forms of the arrows
the rewriting steps pass through, arrangements of projections and
pairings rather than expansions of definitions. Neither the definitions
nor the Mitchell–Bénabou language reduce these: a certificate that
cites each term once from a table of shared terms, and a checker that
infers definedness and canonical objects, do.

Both are made. A store holds the terms of a development, each node a
label and its children's indices, and a shared certificate cites a term
by its index, so that two terms are equal when their indices are and an
instance of an axiom is verified by matching the axiom's sides against
the store ({name}`Geb.PartialHorn.checkShared_sound`). The checker of
the topos theory infers the typing of the store's terms in each scope,
whether a term is defined and the canonical forms of an object or of an
arrow's domain and codomain, by the rules the prover's typing follows,
read off the axioms and checked where used; a certificate cites the
definedness of a term so typed, and the equation of two objects of one
canonical form, by two rules of the checker's oracle
({name}`Geb.FreeTopos.infers_sound`,
{name}`Geb.FreeTopos.checkTopos_sound`). The prover emits those rules in
place of its typing lemmas. The benchmark's development, the library
included, then has 739 sequents whose certificates have 20160 nodes over
a store of 1551, against 1007453 nodes at the first measurement; the
theorems' certificates, with the recursions' computation lemmas, have
from 7 to 30 times as many nodes as those of Gödel's T, 18754 against
2071, and the development checks in 0.9 seconds against 29 milliseconds
for Gödel's T.

The shared certificates are checked by a Lean checker of their own,
proved sound there, and the developments of the language cite
certificates in the plain form. In Geb the shared checker is not written
again with a proof of its agreement: it is a candidate for admission
beside the checker written in Geb, by unsharing, a translation that
spells out each index as the term it denotes and replaces each rule of
the oracle by the typing lemmas the prover emits without it (the
section on the metalogic and its checker).

#### The Mitchell–Bénabou language
%%%
tag := "mb-language"
%%%

State: complete, and its own term model follows the bootstrap.

##### Terms, compilation and definitions

State: complete.

The Mitchell–Bénabou language is written after the definitional
extension,
with definitions of its own. Its terms are those of the typed λ-calculus
with products whose types are object terms of the combinators, built
from object variables by the terminal object, products, the initial
object, coproducts, exponentials, the subobject classifier and the data
objects; its other constants are
the folds of the data objects, primitive arrows of the combinators,
each named by an index with the domain and codomain the checker's
inference confirms, and the definitions
({name}`Geb.FreeTopos.Internal.Term`). A term is typed and compiled to
an arrow of the combinators in one pass, a variable to a projection, an
abstraction to a currying and an application to evaluation after a
pairing, as the categorical abstract machine compiles them
({name}`Geb.FreeTopos.Internal.compile`). A definition names a term in
term and object parameters and compiles to a definition of the
combinators, the arrow of its body from the product of its parameters'
types; its application compiles to that definition's operation after
the tuple of its arguments.

A theorem in Lean states that compiling a term and then unfolding the
combinators' definitions agrees with unfolding the language's
definitions and then compiling: in every model of the theory extended
by the combinators' definitions, the unfolded term has the term's type
and an arrow of the same value
({name}`Geb.FreeTopos.Internal.compile_unfold_of_ok`). They are not the
same term. Unfolding in the language substitutes the arguments for the
parameters, where the compiled application composes the definition's
arrow with the tuple of the arguments; the proof meets the two by the
lemma that substitution is composition
({name}`Geb.FreeTopos.Internal.compile_subst`), which rests on the
naturality of the compilation
({name}`Geb.FreeTopos.Internal.compile_comp`), whose case of abstraction
is the naturality of currying, derived from the axioms of exponentials
({name}`Geb.FreeTopos.curry_comp`). The compiled arrows are well sorted
({name}`Geb.FreeTopos.Internal.compile_sortOf`), so that by eliminability
the theorem carries to the definition-free arrows: in every model of the
theory, the unfoldings of the combinators' definitions in the two arrows
have one value ({name}`Geb.FreeTopos.Internal.valid_unfoldAll_compile`).
That the unfolded term compiles is itself the theorem in the one-point
model, the terminal model, in which every operation is defined and every
axiom holds ({name}`Geb.PartialHorn.isModel_point`).

The benchmark's theorems are stated in the language, appending and
addition defined in it by folds into exponentials, and each equation
compiled over the product of its variables' types, a single variable's
type standing for itself. The prover proves the compiled sequents
unchanged: by unfolding the definitions and normalizing, by induction
through the uniqueness of recursion, and by rewriting with an earlier
theorem, the start of the induction for associativity itself compiled
from the language (`GebTests/Prototypes/FreeTopos/InternalBenchmark.lean`).
The development, the library included, has 767 sequents whose
certificates have 20785 nodes over a store of 1578; the theorems and the
lemmas proved for them have 19379 nodes, against 18754 in the
combinators and 2071 in Gödel's T, and the development
takes 1.65 times as long to check as the combinators'. The difference is
in the definitions' granularity: appending and addition are each one
definition, whose unfolding exposes the whole of its recursion's start
and step, where the combinators' benchmark defines the start, the step,
the recursion and the operation separately. Defined in the language as
the combinators' benchmark defines them, they compile to definitions of
the combinators with which that benchmark's proofs apply unchanged, and
the development takes 1.07 times as long to check as the combinators',
with 20290 nodes against 18754. Each statement equates
applications of the language's definitions to its variables, as those
of Gödel's T do, where the combinators equate arrangements of projections and
pairings; the variables are de Bruijn indices, and the proofs are the
combinators' tactics.

Renaming and substitution of the language's terms obey the laws of a
monad of terms over variables, as well-scoped λ-terms form a relative
monad on the finite sets ({citet AltenkirchChapmanUustalu2015}[],
Example 2.1): renaming preserves composites and identities, and
substitution has the variable as its unit on either side and is
associative ({name}`Geb.FreeTopos.Internal.Term.rename_rename`,
{name}`Geb.FreeTopos.Internal.Term.subst_id`,
{name}`Geb.FreeTopos.Internal.Term.subst_subst`). The laws of identity
hold of every term that compiles
({name}`Geb.FreeTopos.Internal.Term.rename_id_of_compile`,
{name}`Geb.FreeTopos.Internal.Term.subst_id_of_compile`): renaming and
substitution rebuild a variable as a leaf, and the variables of a term
that compiles are leaves
({name}`Geb.FreeTopos.Internal.Term.varLeaves_of_compile`). The
language's definitions unfold by this substitution. The combinators'
substitution for their object variables obeys the same unit laws and
associativity ({name}`Geb.FreeTopos.subst_x`,
{name}`Geb.FreeTopos.subst_vars`, {name}`Geb.FreeTopos.subst_subst`),
its law of identity stated of terms in scope. A variable is the node of
label zero over the leaf of its index, and a node of label zero over a
child that is not a leaf is no term: it has no sort, no value and no
variable in scope, and it is no type, so that no children of an index
are admitted only to be ignored.

##### Soundness and completeness

The language's derivations are checked by a checker of their own rather
than translated to certificates of the combinators, whose sizes a
translation would inherit. The language is then established twice
over: sound, every theorem it proves holding in every model of the
theory, and complete, whatever holds in every model being provable in it
and every object and arrow of the free topos named by it. Two
formulations as different as the language's typing and logical rules
over λ-terms and the axioms of an elementary topos, agreeing on what is
definable and provable, are evidence for each other, and the partial
Horn presentation is itself related to mathlib's elementary toposes by
{ref "rule-set-models"}[The rule set and its models].

The two presentations mix. In the Mitchell–Bénabou language of a topos
every object is a type and every arrow applies to terms
({citet MacLaneMoerdijk1992}[], Section VI.5); the language here is the
fragment its type formers generate, and its compilation interprets that
fragment. {ref "mb-types-mixing-completeness"}[Types built in, mixing
and completeness] widens it in one direction. A derivation
cites a certificate of the combinators for an equation whose compiled
sequent the certificate proves, and a certificate cites a theorem of the
language by the sequent it compiles to; and a development declares
constants of the combinators, objects that become types and arrows that
the language applies, each confirmed by the checker's inference or by a
certificate of its definedness, so that every object and arrow of the
free topos is named in the language. The other direction, the
language's terms inside the combinators' terms, follows the bootstrap
(the road map), since the language is the one in which programs and
proofs are written.

Completeness then follows from the partial Horn logic's. The values of
the theory's term model in a context under hypotheses
({name}`Geb.PartialHorn.TermModel.termModel`) are the terms of a sort
provably defined there, modulo provable equality; it is a model of
every theory whose axioms are in scope and equate terms of one sort,
and in it, at the context's variables, an equation holds exactly when
it is proved ({citet Kawase2024}[], Section 6.3, whose finitary case is
{citet PalmgrenVickers2007}[]'s). A sequent of the language that holds
in every model compiles to a sequent of the combinators that holds in
every model, which a certificate therefore proves, and the language
cites the certificate. A combinator translates into the
language as its declared constant, and the round trips of the
compilation are provably the identity by certificates. The language's
own term model, the topos of its types with predicates and its provably
functional relations as {citet LambekScott1980}[] construct the free
topos from a type theory, proves its rules complete without citations;
it follows the bootstrap (the road map), and the model of functional
relations is the same construction over Lean's propositions in place of
the language's provability. Its parts are the checker with equations as
its formulas and induction as the uniqueness of recursion, measured
against the certificates of Gödel's T; the logical rules, whose soundness
needs the internal Heyting algebra of the subobject classifier;
comprehension and description; and the types built in, the mixing of the
two presentations and the completeness theorems. Each is complete.

##### Equations
%%%
tag := "mb-equations"
%%%

State: complete.

A derivation is a rose tree of rules ({name}`Geb.FreeTopos.Internal.Rule`).
A rewriting derivation transforms a given term: congruence into each
child of a node, each in its own context, β, the components of a pair,
the η of pairs and of the terminal type, the unfolding of a definition,
the computation of the folds at zero, a successor, the empty list and a
construction, and an instance of an earlier theorem in either direction.
An equation is proved by rewriting both sides to one term, or by
induction on the innermost variable of the natural numbers or of a list
type: both sides agree at the start, and each is, at a successor or a
construction, a given step of their type applied to its own value. The
rewriting takes its terms from the term it rewrites, so that a
derivation names no term but the steps of its inductions and the
instances of the theorems it cites, and the checker computes every
substitution ({name}`Geb.FreeTopos.Internal.check`). The checker is
proved sound: every theorem of a development that checks is valid in
every model of the theory extended by the combinators' definitions, and,
with every definition unfolded, in every model of the theory
({name}`Geb.FreeTopos.Internal.valid_unfoldAll_of_checkDev`). The
induction rules are sound by the uniqueness of the folds with a
parameter, which every natural numbers object of a cartesian closed
category has ({citet EscardoSimpson2025}[], Proposition 2.3), derived in
Lean from the theory's uniqueness of the folds without one by currying
the parameter ({name}`Geb.FreeTopos.natRec_param_unique`,
{name}`Geb.FreeTopos.listRec_param_unique`). A prover prototyped in Lean
derives the benchmark's seven theorems, which the checker checks
(`GebTests/Prototypes/FreeTopos/InternalDerivation.lean`). The
derivations have 169 nodes, the terms they name counted, against 2071
in the certificates of Gödel's T and 18754 in the combinators',
and check in 2.4 milliseconds, where the combinators' development of the
same theorems, the lemmas it proves for them included, checks in about
0.9 seconds.

##### Logical rules
%%%
tag := "mb-logical-rules"
%%%

State: complete.

The logical rules make a judgment a formula in a context under
hypotheses, formulas in the same context, and its meaning external: it
holds when, in every environment of arrows of the context's types in
which the hypotheses are true, the formula is true
({name}`Geb.FreeTopos.Internal.FmSound`). Rewriting gains the equations
among the hypotheses, and proof gains a hypothesis, the cut, the proof
of a formula before or after a rewriting, the equality of two formulas
that entail each other, the equality of two functions whose
applications to a new variable are equal, the application of an earlier
theorem with its hypotheses' instances proved, and induction on the
innermost variable under the induction hypothesis. These are the basic
axioms and rules of a local set theory ({citet RuizHernandezSolorzano2021}[],
Section 3.2), with the extensionality of every exponential in place of
that of power types, and with induction; the connectives are defined
from equality as that theory defines them, truth as an equation of the
terminal type's element with itself, a conjunction as the equality of
the pair of its formulas with the pair of truths, an implication as the
equality of the conjunction with the antecedent, a universal
quantification as the equality of the abstraction of its formula with
the abstraction of truth, and falsity as the universal quantification of
every formula. The soundness of propositional extensionality is the
uniqueness of the characteristic map of a subobject
({name}`Geb.FreeTopos.omega_ext`), and that of induction under the
hypothesis is induction on subobjects: a formula over the product of the
other variables' object with the natural numbers or a list object that
is true at the start and, on its pullback of truth, at a successor or a
construction is true ({name}`Geb.FreeTopos.truth_of_natInd`,
{name}`Geb.FreeTopos.truth_of_listInd`), by the existence and uniqueness
of the folds with a parameter
({name}`Geb.FreeTopos.natRec_param_exists`). The checker with these rules
is proved sound as before ({name}`Geb.FreeTopos.Internal.check_sound`),
with no axiom but propositional extensionality and the soundness of
quotients. The introduction and elimination rules of the connectives
are derived as theorems with hypotheses, and the left unit of addition
and the right unit of appending are proved again by induction under the
hypothesis, which the prover normalizes, cuts in and rewrites by
(`GebTests/Prototypes/FreeTopos/InternalLogic.lean`). The derivations
have 568 nodes, the terms they name counted, and check in 5.6
milliseconds; the two inductions under the hypothesis have 48 and 52
nodes, where the same equations by the uniqueness of recursion have 25
and 29.

##### Connectives, comprehension and description
%%%
tag := "mb-connectives"
%%%

State: complete.

The connectives are definitions of the language in a library, placed at
an index among a development's definitions and their rules at an index
among its theorems, with unique existence among them
(`Geb/Prototypes/FreeTopos/Internal/Logic.lean`). Their meaning in every
model is derived from the equalities that define them: the conditions
of the Kripke–Joyal semantics ({citet MacLaneMoerdijk1992}[], Section
VI.6), stated of the arrows the formulas compile to, a conjunction
holding when both its formulas do, an implication when its consequent
is true after every arrow after which its antecedent is, a universal
quantification when its predicate is true at the generic element, and an
existential quantification that holds making true every formula true
after each arrow at whose pairing with an element the predicate is true
({name}`Geb.FreeTopos.Internal.holds_ex_elim`). Comprehension needs no
syntax of its own: the comprehension of a formula over a type is its
abstraction, membership is application, the comprehension axiom is β,
and the subobject a formula names is its pullback of truth. Description
is not an operator of the language either, which keeps its terms the
λ-terms that the model of functional relations interprets as Lean
functions
without unique choice: an arrow a functional relation determines is
named by the relation, and description is the theorem that a formula of
which a unique existential quantification holds holds, in every model,
at exactly one element of its variable's type
({name}`Geb.FreeTopos.Internal.description`). It follows from unique
choice, which holds in every model of the theory
({name}`Geb.FreeTopos.unique_choice`): the first projection of the
formula's pullback of truth is a monomorphism, whose characteristic map
is truth, and the inverse of the monomorphism's factorization, an
operation of the theory, gives the section after which the second
projection is the arrow, as {citet DubucSzyld2015}[], Proposition 1.21,
characterize the relations that are the graphs of arrows.

##### Types built in, mixing and completeness
%%%
tag := "mb-types-mixing-completeness"
%%%

State: complete. Its parts, in order:

* Complete. The arrow a functional relation determines, a definition of
  the combinators; binary coproducts and the initial object; and rose
  trees over a type of labels, with induction on rose trees.
* Complete. Citations between the two checkers.
* Complete. Declared definitions of the language and primitive arrows.
* Complete. Object definitions.
* Complete. Quotient types.
* Complete. The completeness theorems.
* Complete. The round trips of the compilation.

The arrow a relation determines is the second projection after the
inverse of the first projection of the relation's pullback of truth
({name}`Geb.FreeTopos.desc`), the construction of unique choice, which
is stated of it ({name}`Geb.FreeTopos.unique_choice`). It is defined
exactly where the relation is functional: a relation whose arrow is
defined is total and univalent ({name}`Geb.FreeTopos.functional_of_desc`),
since the inverse's definedness makes the first projection a
monomorphism and the lift of the identity's makes its characteristic map
truth. As a definition of the combinators in two objects and an arrow
({name}`Geb.FreeTopos.descDefn`, well formed by
{name}`Geb.FreeTopos.descDefn_wf`), it is a partial operation of the
theory's extension, whose axioms make it defined where its body is, and
at a functional relation its value is the arrow's
({name}`Geb.FreeTopos.eval_op_desc`). The partial Horn logic's
definedness carries the condition that a description operator of the
language would need proved; the compilation of a term model's arrow into
the combinators is this operation, and the language keeps no description
operator.

Binary coproducts and the initial object are types of the language. The
injections are primitive arrows
({name}`Geb.FreeTopos.Internal.inlPrim`,
{name}`Geb.FreeTopos.Internal.inrPrim`), and so is case analysis
({name}`Geb.FreeTopos.Internal.casePrim`): the arrow from the product of
the exponentials of two summands into a type to the exponential of
their coproduct into it ({name}`Geb.FreeTopos.caseArr`), so that the
analysis of a term by two functions is the application of the case
analysis of their pair to it, and the language gains no binder. The
arrow is the transpose of the copairing, in the context of the pair, of
the two evaluations ({name}`Geb.FreeTopos.copairIn`). In a cartesian
closed category the product with an object preserves coproducts, being
a left adjoint, so that an arrow from the product of an object and a
coproduct is determined by its composites with the products of the
object and the injections ({name}`Geb.FreeTopos.prod_coprod_ext`): the
category is distributive, and its initial object is strict
({citet CarboniLackWalters1993}[], Proposition 3.4), an object with an
arrow to it being initial ({name}`Geb.FreeTopos.eq_of_hom_zero`). The
rules are the computation of case analysis at each injection, a
rewriting; case analysis on the innermost variable of a coproduct type,
a formula proved at the left injection of a variable of the first
summand and at the right injection of a variable of the second, under
hypotheses that do not mention the variable; and every formula in a
context with a variable of the initial type. The checker with these
rules is proved sound as before
({name}`Geb.FreeTopos.Internal.coprodInd_sound`,
{name}`Geb.FreeTopos.Internal.zeroInd_sound`). The η of case analysis is
a theorem, proved by case analysis on its variable, and the arrow from
the initial object is a primitive arrow that a development may add,
about which the last rule proves every formula
(`GebTests/Prototypes/FreeTopos/InternalCoproducts.lean`).

The Boolean type is the coproduct of the terminal object with itself,
optional values of a type its coproduct with the terminal object, and
the finite types the iterated coproducts of the terminal object from the
initial object; the case analysis of the Boolean type is a conditional
that computes, which a formula does not. Products of more than two
factors and the finite types are not built in: the compilers choose
their representations, arrays and fixed-width numbers among them.

Rose trees over a type of labels are a data object of the theory, as
lists over a type of elements are: the initial algebra of the functor
taking an object to the product of the type of labels and the object's
list object ({name}`Geb.FreeTopos.lrose`,
{name}`Geb.FreeTopos.lroseRec`). Their operations and axioms follow the
others, so that no certificate's citation of an axiom by its index
moves. The language's fold of a rose tree folds either rose-tree object,
the one with natural numbers for labels that models the kernel's values
or one over a type of labels, and its computation at a construction is a
rule: the step at the pair of the label and the list of the folds of the
children, that list itself a fold of the children
({name}`Geb.FreeTopos.Internal.roseNode_sound`,
`GebTests/Prototypes/FreeTopos/InternalRoseTrees.lean`). Each type built
in is determined up to isomorphism by the universal property its axioms
state, and is constructed by the rest of the topos {citep Pare1974}[]
{citep MoerdijkPalmgren2000}[], so each extension is equivalent to the
free topos with a natural numbers object alone. The kernel gains the
same types when the Geb programs move to them, since a change of the
kernel moves every fixed point.

Induction on rose trees is a rule in the form of the uniqueness of the
fold: two terms in a context of a rose tree, each of which at a
construction is a step at the label and the list of its values at the
children, are equal ({name}`Geb.FreeTopos.Internal.roseInd_sound`). The
rule takes a context of the tree alone and no hypotheses, since the list
of a term's values at the children is a fold of the children, and a
fold's step is a term of a context of its own; its soundness is then the
uniqueness of the fold itself, with no parameter. A term with other
variables is brought under the rule by abstracting them, the fold's type
an exponential, as the definitions of appending and addition fold into
exponentials. The fold that rebuilds a tree is the identity by the rule,
with the fold that rebuilds a list, the identity by induction on lists,
cited at the children (`GebTests/Prototypes/FreeTopos/InternalRoseTrees.lean`).

Induction on rose trees with an induction hypothesis is a second rule,
beside those of the natural numbers and lists: a formula in a context of
a rose tree alone holds when it holds at a construction under the
hypothesis that it holds at each child, the list of its values at the
children being the list of truths of the same length
({name}`Geb.FreeTopos.Internal.roseIndHyp_sound`). Its soundness is the
fold of the formula's pullback of truth by the structure map there,
which the premise gives: that fold followed by the pullback's inclusion
is the identity, by the uniqueness of the fold, so the formula is true
({name}`Geb.FreeTopos.truth_of_roseInd`), with the action of the list
object on arrows functorial ({name}`Geb.FreeTopos.listMap_comp`). The
rule takes a context of the tree alone for the reason the first does;
quantifiers, or abstraction, bring other variables under it.

Citations between the two checkers, complete. A development is one list
of declarations, each checked with the entries before it: a theorem of
the language with its derivation, or a sequent of the combinators with
its certificate ({name}`Geb.FreeTopos.Internal.Decl`). A derivation
proves an equation between two terms of a context, under any
hypotheses, by a certificate that proves the sequent the equation
compiles to ({name}`Geb.FreeTopos.Internal.compileEq`), and a
certificate cites a theorem of the language by the sequent it compiles
to ({name}`Geb.FreeTopos.Internal.Thm.seq`): the equation of its
conclusion's sides' arrows, or of its conclusion's arrow with truth,
after the inclusion of the subobject on which its hypotheses are true
where it has any. The sequent of a valid theorem is valid
({name}`Geb.FreeTopos.Internal.Thm.seq_valid`), and a cited equation is
sound by the certificates' checker's soundness
({name}`Geb.FreeTopos.Internal.cert_sound`). A certificate is checked in
the theory extended by the compilations of the language's definitions,
so a development citing certificates has no definitions of the
combinators before the language's; its own objects and arrows of the
combinators are object definitions and primitive arrows declared in it.
The prover's library of
the combinators opens a development that the language continues: the
language proves that appending the empty list gives the list by
induction, the prover proves that appending it twice does by rewriting
with that theorem, and the language cites the prover's certificate for
the same equation (`GebTests/Prototypes/FreeTopos/InternalCitations.lean`).

Declared definitions of the language and primitive arrows, complete. A
development's declarations are theorems of the language, sequents of
the combinators, definitions of the language, and primitive arrows
({name}`Geb.FreeTopos.Internal.Decl`), each checked with the constants
and the entries before it, so that the constants grow along the
development ({name}`Geb.FreeTopos.Internal.checkDev`). A definition is
checked by its compilation. A primitive arrow is a term of the
combinators in object parameters, with a domain and a codomain that are
types in them, which the language applies as before. It is confirmed by
the checker's inference of its domain and codomain, or by a certificate
of the sequent that its composite with the identities of its domain and
of its codomain is itself ({name}`Geb.FreeTopos.Internal.Prim.seq`),
since that composite is defined only where they are its domain and
codomain ({name}`Geb.FreeTopos.Internal.Prim.val_of_seq`); the
certificate may cite the theorems before it, whose validity uses only
the constants before them. A theorem valid with fewer constants is valid
with more, its formulas compiling to the same arrows
({name}`Geb.FreeTopos.Internal.Thm.Valid.mono`). A certificate checked,
or a primitive arrow inferred, in the theory extended by the
definitions so far is sound in every model of an extension of that
theory, since the certificates' checker and the inference are sound in
every model of a signature extending a theory's in which the theory's
axioms hold ({name}`Geb.PartialHorn.check_sound`,
{name}`Geb.FreeTopos.ExtEnv.Sound`). Every entry of a development that
checks is valid in every model of the theory extended by the
compilations of its definitions
({name}`Geb.FreeTopos.Internal.valid_of_checkDev`). A development
declares the constant one, confirmed by the inference, adding two,
confirmed by the prover's certificate, a definition applying adding
two, and a theorem applying the three
(`GebTests/Prototypes/FreeTopos/InternalConstants.lean`).

Object definitions, complete. An object definition is an object of
the combinators in object parameters, declared in a development
({name}`Geb.FreeTopos.Internal.Definition`) and confirmed by the
checker's inference of its definedness or by a certificate of it
({name}`Geb.FreeTopos.Internal.objConfirms`). It compiles to a
definition of the combinators, and its operation at types is a type, so
that typing remains a syntactic test, the object definitions of the
constants among the operations that build types
({name}`Geb.FreeTopos.Internal.IsTy`). The language's definitions and
the object definitions are one list, each the operation of its
position. A primitive arrow's types may name object definitions: the
inference confirms it where the canonical forms of its inferred domain
and codomain are those of its types. As the object definitions grow the
types, a development's invariant is stated at every assignment of
objects to the constants' object parameters rather than at types
({name}`Geb.FreeTopos.Internal.DefsVal`), and at types follows by
substitution. A development declares the pairs of an object parameter,
confirmed by the inference, the product of the natural numbers with
themselves, confirmed by the prover's certificate, arrows into and out
of the pairs, and theorems in a context of the pairs
(`GebTests/Prototypes/FreeTopos/InternalConstants.lean`). The partial
constructions whose definedness a certificate establishes, the
factorization through an equalizer and the descent through a
coequalizer, have as domains or codomains objects that object
definitions name, and enter a development as primitive arrows confirmed
by certificates; an arrow of a definition of the combinators, the arrow
a functional relation determines among them, enters as a primitive
arrow of its body.

Quotient types, complete. The quotient of a type by a relation, a
formula in two variables of the type, is declared in a development
({name}`Geb.FreeTopos.Internal.Decl`): the coequalizer of the two
projections of the relation's pullback of truth
({name}`Geb.FreeTopos.Internal.relPair`), an object definition, the
projection to it, a primitive arrow, and the theorem that related
elements have equal images, sound because a pair of related elements
factors through the pullback of truth, whose projections the projection
coequalizes ({name}`Geb.FreeTopos.Internal.relPair_coeq`). A formula
holds of every element of the codomain of a coequalizer's projection
when it holds at the projection's image of every element of its domain
(`quotInd`, {name}`Geb.FreeTopos.Internal.quotInd_sound`): the
projection is an epimorphism, by the uniqueness of the coequalizer's
factorization, and so is its product with an object, the product being
a left adjoint ({name}`Geb.FreeTopos.coeqProj_epi`,
{name}`Geb.FreeTopos.prod_coeq_ext`). The descent of a function is a
declaration citing the theorem that the function respects the relation:
a primitive arrow from the quotient, the coequalizer's factorization,
and the theorem of its computation at an image. Its definedness follows
in Lean from the cited theorem, applied in the environment of the
relation's pullback of truth, where the relation holds, rather than from
a certificate of the combinators, so that the program states no
certificate. A development takes the quotient of the pairs of natural
numbers by equal sums, applies the theorem of related elements to a
pair and the pair with zero added to its second component, descends the
sum and the sum with zero added, and proves the descents equal by
induction on the quotient
(`GebTests/Prototypes/FreeTopos/InternalQuotients.lean`). For an
equivalence relation, the quotient is isomorphic to the object of
equivalence classes that power objects construct, the image of the
arrow taking an element to its class, since in a topos an equivalence
relation is the kernel pair of its coequalizer; that isomorphism
follows the bootstrap (the road map). An equivalence relation and its
coequalizer state a quotient as programs state it, where the object of
equivalence classes states it as a set of subsets.

Completeness, complete. The partial Horn logic's term model and its
completeness theorem ({name}`Geb.PartialHorn.derivable_iff_valid`), of
the section on soundness and completeness, give the completeness of the
language citing certificates
({name}`Geb.FreeTopos.Internal.exists_certSeq_of_valid`), by a rule
that cites a certificate of the sequent a theorem compiles to under its
hypotheses ({name}`Geb.FreeTopos.Internal.Thm.seq`, sound by
{name}`Geb.FreeTopos.Internal.certSeq_sound`). The rule is the converse
of the citation of a theorem by a certificate: the arrow of an
environment in which the hypotheses hold factors through the subobject
on which their arrows are truth
({name}`Geb.FreeTopos.Internal.truthSub_lift`).

Round trips, complete. A combinator to its declared constant and a
term of the language to the constant of its compiled arrow are provably
the identity, each an equation valid in every model and therefore
proved. A primitive arrow applied in its object variables to the
variable of its domain compiles to its arrow after the identity, whose
equation with the arrow the partial Horn logic derives
({name}`Geb.FreeTopos.Internal.roundTrip_prim`). A term's compiled
arrow, declared as a primitive arrow and applied to the tuple of the
context's variables ({name}`Geb.FreeTopos.Internal.varsTerm`), equals
the term by the citation of a certificate
({name}`Geb.FreeTopos.Internal.roundTrip_term`).

#### Functional relations and the checker of Gödel's T
%%%
tag := "functional-relations"
%%%

State: complete. The model of functional relations is complete, with
the converse of the rule set's models, and the choice whether Gödel's T
keeps its own checker is made, by a measurement with labels that are
bitstrings and the translation's correctness: the checker of Gödel's T
is retired.

The choice follows the constructions.

The model of functional relations is a model of the theory in Lean
without
`Classical.choice`: its objects are the types of `Type`, and its arrows
functional relations between them, relations under which each element
of the domain is related to exactly one element of the codomain. Lean's
types with functions are not such a model. The inverse of the
factorization of a monomorphism through the pullback of truth along its
characteristic map takes an element of that pullback, which records
that some element of the domain has the given image, to that element,
and a proof that one exists yields no term of a type without
`Classical.choice`, though the element is unique. The arrow a
functional relation determines is the relation itself, so that unique
choice holds in the model by construction, as it holds in the free
topos by the arrow a functional relation determines there. The model
is the construction of a topos from a type theory by its types and
provably functional relations, after {citet LambekScott1980}[], over
Lean's propositions; the language's own term model is the same
construction over the language's provability.

It is made in five parts, in order:

* Complete. A topos with chosen structure and the data objects in
  dependent form ({name}`Geb.FreeTopos.ChosenTopos`): a record of the
  theory's operations, their arguments typed by their domains and
  codomains, and of its equational axioms. It presents the models the
  partial Horn theory presents, as a generalized algebraic theory
  presents what an essentially algebraic one does, and the typing
  axioms hold in it by the operations' types.
* Complete. The record of Lean's types and functional relations
  ({name}`Geb.FreeTopos.relTopos`), its laws, the exponential's and the
  classifier's among them, proved without `Classical.choice`
  ({name}`Geb.FreeTopos.relData_laws`), which the axiom linter checks.
  The exponential is the type of functional relations, the classifier
  `Prop`, and the inverse comparison of a monomorphism relates an
  element of the pullback of truth to the element whose image it is
  ({name}`Geb.FreeTopos.FunRel.chiInv`) rather than choosing it.
* Complete. The converse of the rule set's models, for the record:
  every record gives a model of the theory
  ({name}`Geb.FreeTopos.ChosenTopos.isModel`), its sorts the record's
  objects and its arrows with their domains and codomains, each
  operation defined where the typing axioms make it defined. The
  validity of every axiom is proved by one procedure, which evaluates
  the hypotheses into equations of objects and arrows, substitutes
  those of variables, and closes the evaluated conclusion by the laws.
  At the record of types and functional relations it gives the model of
  functional relations.
* Complete. Lean's functions as functional relations: the graph of a
  function determines it ({name}`Geb.FreeTopos.FunRel.ofFun_injective`),
  and the graphs are closed under composition, pairing, copairing, the
  folds of the data objects, and currying with evaluation, so that a
  sequent a certificate proves, or a development that checks, equates
  the functions whose graphs its sides evaluate to
  ({name}`Geb.FreeTopos.eq_of_check`,
  {name}`Geb.FreeTopos.eq_of_checkDevelopment`): the link between the
  kernel's denotations and the model's arrows on which the choice
  whether Gödel's T keeps its own checker turns. A test derives, from
  the prover's development, that the right
  fold of lists with the empty list and construction is the identity.
* Complete. The bridge from mathlib: an elementary topos of the
  repository's class, with chosen data objects, initial algebras of
  mathlib's endofunctor algebras, and chosen limit cones for its
  subobject classifier's squares, gives a record
  ({name}`Geb.FreeTopos.Elementary.chosenTopos`). The class states the
  classifier's squares to be pullbacks by a proposition, from which the
  inverse comparison is computed only by `Classical.choice`, so their
  limit cones are chosen as the class chooses its other limits. Its
  subject is the correspondence with mathlib's structures, which use
  `Classical.choice`, and it is admitted to it as the constructive-only
  rules provide.

The choice whether Gödel's T keeps its own checker follows the model of
functional relations. Its options are two.
In the first, Gödel's T keeps its checker and prover, and an equation
between kernel programs is proved in it. In the second, its checker is
retired, and such an equation is proved in the Mitchell–Bénabou
language, about the translation of the kernel's terms into the
language's. The two mix already, since a proof in Gödel's T may cite an
equation between kernel terms that the metalogic proves. The factors
are these.

* What each states. Gödel's T states equations between kernel terms of
  a type, under equations as hypotheses, and proves them with induction
  on lists, trees and labels. The language has the connectives and the
  quantifiers, subobjects, description and quotients, and is complete,
  citing the combinators' certificates. The next proof in Gödel's T,
  the type checker's preservation of types by weakening, is an
  implication between typings, which Gödel's T states as an equation
  between functions of a context, proved by an induction whose
  hypothesis is an equation between lists of functions, and which needs
  its prover to rewrite at applications under binders; the admission of a
  stronger checker has the same form.
* Size and time. On the benchmark's seven theorems the certificates of
  Gödel's T have 2071 nodes and check in 29 milliseconds, the
  language's derivations 169 nodes and 2.4 milliseconds, and the
  combinators' shared certificates 18754 nodes and 0.9 seconds. The
  language's derivations are of statements written in it, not of
  translated kernel programs. The δ rules of Gödel's T evaluate a primitive at
  literals in one step, by the host's arithmetic; the natural numbers
  object is unary, so a label's literal translated to it has the size
  of its value, and label arithmetic at literals is a fold. The
  kernel's programs are rich in literals: an atom is a list of
  character codes.
* Trust. The validity of Gödel's T is defined by the Lean denotations of
  kernel terms. The metalogic's is validity in every model, and it
  bears on kernel programs through one theorem in Lean, now proved
  (below): the translation of a kernel term represents, in the topos of
  types and functional relations, the term's denotation, by a logical
  relation that relates a tree to the tree of its labels' bitstrings
  and is built by products, functional relations and lists at the other
  types. Its induction's cases are the representations' closure under
  composition, pairing, copairing, the folds and currying with
  evaluation, together with the primitives. Either option needs the
  theorem as soon as a proof in Gödel's T cites the metalogic. The
  metalogic states the soundness of the checker of Gödel's T, which
  Gödel's T cannot prove of itself; the soundness
  of each stays in Lean.
* Implementation. Retiring the checker of Gödel's T leaves the
  metalogic's checker, the
  larger, as the one checker written in Geb that is trusted; keeping it
  keeps two rule sets, each specified in Lean and implemented in Geb,
  and two provers.
* Work. Keeping Gödel's T continues its prover, with rewriting under
  binders, and its proofs; the metalogic's checker and prover are
  written in Geb in either case. Retiring it adds the translation of
  kernel terms in Geb, and the prover's front end reading programs and
  statements from files in the datatype language, as the prover of
  Gödel's T does; the translation in Lean and its correctness in Lean are
  complete, and the proofs in Gödel's T, prelude, nat, check, equations
  and datatype, remain
  citable.
* One language. Writing the Mitchell–Bénabou language during the
  bootstrap ({ref "when-mb-written"}[When the Mitchell–Bénabou language
  is written]) made the language the one
  mathematics is written in. Keeping Gödel's T writes proofs about programs in a
  second logic; the translation of a kernel term is itself a λ-term.

The factors favour retiring the checker of Gödel's T, which removes a rule
set, its specification and its implementation from what is trusted, and
the redundancy of two provers, unless the measurement below shows the
cost prohibitive. The cost of literals has a remedy of its own, which
the measurement takes: labels that are bitstrings, the initial algebra
of the functor taking an object to its sum with the terminal object and
two copies of itself, whose universal property gives its computation
and uniqueness rules as the natural numbers object's gives theirs, so
that a literal has the size of its binary representation and arithmetic
at literals is a fold over its bits. The bitstrings are the list object
of the coproduct of the terminal object with itself, since the sum of
one with two copies of an object is the sum of one with the product of
two and the object: their fold and its uniqueness are the list object's
composed with the coproduct's, and the theory, the checker and their
proofs are unchanged. A label is the bitstring of its index in the
bijective numeration of {citet Oitavem2010}[]
({name}`Geb.Oitavem.unrank`), least significant bit first, in which
every bitstring is the numeral of exactly one number; Lean's lists of
Booleans and rose trees of them are the same carriers. The repository's
value representation is rose trees of bitstrings
(`Geb/Prototypes/RoseTree.lean`), and its type-checking prototypes
build decision problems from expressions of the algebra of
{citet Oitavem2010}[], whose expressions define exactly the logspace
functions on bitstrings, by their syntax alone
(`Geb/Prototypes/Typechecker/Oitavem.lean`); labels that are bitstrings
bring the kernel's values, the value representation and that algebra to
one carrier.

The choice is made by measurement, in these parts, in order:

* Complete. The translation of kernel types and terms into the
  language, in Lean ({name}`Geb.FreeTopos.Translation.term`): the base
  type of trees to the rose-tree object over the bitstrings, a label to
  its numeral ({name}`Geb.FreeTopos.Translation.numeral`), the unit,
  product, function and list types to their objects, and each term
  former, the kernel's constants and its primitives to terms and
  definitions of the language ({name}`Geb.FreeTopos.Translation.lib`), a
  fold whose step uses the context folding into functions of it. The
  primitives' arithmetic is structural recursion on the bits, since the
  numeral of a bit before a bitstring denotes twice the bitstring's
  number, plus one, plus the bit: addition and comparison from the least
  significant bits, a successor as the carry; equality likewise, decided
  by the first unequal bits rather than by the comparison, which reaches
  the most significant; subtraction likewise, of a
  number at most the first; multiplication by doubling; division by
  long division; and iteration of a step twice the rest's number of
  times and then once or twice. A test checks each against the natural
  numbers' operations.
* Complete. The literals' cost. The prelude, the reader and the type
  checker, 97 definitions of 6218 nodes with 306 quoted trees of 461
  nodes, translate to definitions of 9501 nodes, of which 1685 are the
  numerals' bits and ends, where unary numerals took 25420 nodes, 16411
  of them successors; the translation's library has 681
  (`GebTests/Prototypes/FreeTopos/Translation.lean`, which prints them).
* Complete. The proofs. Each theorem of the proofs in Gödel's T is
  proved in the language by its prover, from the translation of its
  statement, the facts the axioms of Gödel's T state of the primitives
  proved as lemmas:
  Lambek's lemma, that a tree is rebuilt from its unfolding, by the
  uniqueness of the rose tree's fold, from the fold of a list by
  construction and the fusion of two folds of lists, each by list
  induction; and the addition of one, addition to zero and the addition
  of a successor on bitstrings, which Gödel's T takes from its axiom that
  addition iterates the successor, by induction on the bitstrings, case
  analysis of their bits and, for the functions of the first summand,
  extensionality. The nodes of the certificates of Gödel's T and of the
  language's derivations, the terms they name counted, the case analyses
  of bits among the latter, and the least of three times each checker
  takes, the lemmas each development proves before the theorems of
  Gödel's T in
  rows of their own (`GebTests/Prototypes/FreeTopos/TranslationProofs.lean`,
  which prints them):

:::table +header
*
  * File
  * Nodes of Gödel's T
  * Language's nodes
  * Bit steps
  * Time of Gödel's T
  * Language's time
*
  * prelude
  * 1748
  * 475
  * 0
  * 11 ms
  * 9.1 ms
*
  * nat, lemmas
  * none
  * 12214
  * 58
  * none
  * 582 ms
*
  * nat
  * 323
  * 184
  * 0
  * 2.6 ms
  * 3.6 ms
*
  * check
  * 82602
  * 2022
  * 32
  * 539 ms
  * 81 ms
*
  * equations, lemmas
  * none
  * 79
  * 0
  * none
  * 4.6 ms
*
  * equations
  * 3449
  * 541
  * 2
  * 59 ms
  * 8.3 ms
*
  * datatype, lemmas
  * none
  * 79
  * 0
  * none
  * 4.3 ms
*
  * datatype
  * 6384
  * 1037
  * 0
  * 52 ms
  * 22 ms
:::

Three properties of the prover and the checker the measurement rests
on. Innermost normalization, the strategy of the prover of Gödel's T,
does not
reach the normal form of the type checker's statement within fifteen
minutes, since it normalizes the cases the checker's conditionals
discard; the language's prover reduces to weak head normal forms first
({name}`Geb.FreeTopos.Internal.eval`), so that a fold whose datum
computes selects its case before the cases are normalized. It reduces
an argument that an abstraction uses more than once before substituting
it, so that its value is computed once rather than at each use, which,
with unary labels, took the type checker's time from 287 milliseconds
to 163 and datatype's from 106 to 35. And the
checker computes the contexts of a congruence's children, which type a
fold's start and datum, only where a rewritten child is in a context of
its own ({name}`Geb.FreeTopos.Internal.congCtxs`), which divides the type
checker's time by four. The prover proves the
bitstrings' lemmas by case analysis of a bit anywhere in the context
({name}`Geb.FreeTopos.Internal.bySplit`), from extensionality and the
case analysis of an innermost variable, so that the checker's rules
are unchanged.

The cost does not forbid retiring the checker of Gödel's T. The
language's derivations are smaller than the certificates of Gödel's T,
the type
checker's by a factor of 40, and check faster in every file but nat,
whose theorems check in about the time of Gödel's T. The lemmas on the
bitstrings' addition, which Gödel's T takes as an axiom, are proved once
and cost 12214 nodes and 582 milliseconds, 10908 of the nodes the
induction on functions that proves the addition of a successor.

The translation is correct
({name}`Geb.FreeTopos.Translation.translation_sound`). Each definition
of the library, compiled and unfolded, represents in the topos of types
and functional relations the Lean function it computes, the arithmetic
through the indices of the bitstrings in the bijective numeration. A
logical relation relates each kernel type's denotation to its
translation's value ({name}`Geb.FreeTopos.Translation.KRel`), a label to
the bitstring of its index, and its fundamental lemma states that a
kernel term's translation, in a represented context, has the type the
kernel's checker infers and represents the term's denotation
({name}`Geb.FreeTopos.Translation.repC_term`). A program's translation
represents, definition by definition, the globals the kernel loads, and
an equation whose translation a development proves holds in the
kernel's semantics at each value of its context that has a
representation. The values of the types of first order, whose function
types have domains of data, all have one, so that such a theorem is
valid ({name}`Geb.FreeTopos.Translation.thm_valid`); a value of a
function type whose domain contains a function type has one by unique
choice, which the internal language validates and Lean's logic without
`Classical.choice` does not.

The restriction to types of first order is Lean's rather than the
translation's, and it has a factoring that separates the two. Unique
choice, the principle that a relation relating each element to exactly
one element is the graph of a function, the axiom of unique choice of
{citet ContenteMaietti2024}[], section 3.2, stated in Lean as a
proposition ({name}`Geb.FreeTopos.UniqueChoice`), makes the
representation of every function type total on functional relations,
so that every type's representation relates its values bijectively.
Taken as a hypothesis, it gives the theorem for every type without
`Classical.choice`
({name}`Geb.FreeTopos.Translation.thm_valid_of_uniqueChoice`). Lean
proves it from `Classical.choice` ({name}`Geb.FreeTopos.uniqueChoice`),
and the two give the theorem for every type
({name}`Geb.FreeTopos.Translation.thm_valid_classical`), in two modules
of their own, admitted to the axiom linter's allowlist; every model of
the theory validates unique choice without `Classical.choice`
({name}`Geb.FreeTopos.unique_choice`). The hypothesis thus marks the
one step that a proof of the theorem inside the free topos takes from
the topos's own logic.

The decision follows: the cost is not prohibitive and the translation
is sound, so the checker of Gödel's T is retired, and an
equation between kernel programs is proved in the Mitchell–Bénabou
language, about the programs' translations. Its consequences are these.

* The metalogic's checker is the one checker written in Geb that is
  trusted. A proof about kernel programs bears on them through the
  translation's soundness in Lean, for the types of first order without
  `Classical.choice` and for every type under unique choice.
* The translation joins it in what is trusted, written in Geb, since a
  Geb program states what the checker checks; its agreement with the
  translation in Lean is proved, as the checker's is.
* The checker of Gödel's T, its prover and their proofs remain, checked by
  their tests, and nothing is added to them. The weakening and the
  substitution of kernel terms that `bootstrap/goedel-t/equations.geb`
  defines are programs, which the proofs about the type checker are
  about.
* A stronger checker is admitted by the proof, in the metalogic, that a
  Geb program translates its certificates into the metalogic's
  derivations with the same conclusions.
* The bootstrap's fixed points are unchanged: the checker and prover of
  Gödel's T are outside the compiler's source closure, which
  `scripts/bootstrap.sh` compiles.

## Improvements
%%%
tag := "improvements"
%%%

The following are known limitations of what is constructed, each with
the change that removes it.

* Primitives named in expansions. The expansion of the datatype language
  refers to the
  primitives `label`, `child`, `children`, `node` and `eq` by name, so a
  program that binds one of these names around a case analysis or a
  structural recursion changes the expansion's meaning. A reference to
  a primitive that no binding shadows, a reader form naming a
  primitive by its index, added to the seed's reader and to the Geb
  reader alike, removes the dependence; the reservation of names
  beginning with `%` for the expansion is likewise documented and not
  enforced. Hygienic elaboration, a step of the authoring sequence,
  removes both ({ref "files-editions"}[Files, editions and the host
  boundary]).
* Diagnostics of the Geb compiler. The stage-0 and stage-1 compilers
  report a program that does not read, expand or type-check by an empty
  image and name no definition, where {name}`Geb.Kernel.diagnose` in the
  seed names the first failing one. Until the Geb compiler reports a
  message, a failing program is diagnosed by expanding it with the
  stage-0 expansion, printing the kernel forms, and applying
  {name}`Geb.Kernel.diagnose` to them. Diagnostics that name a source
  occurrence are a step of the authoring sequence
  ({ref "editing"}[Editing]).
* The reader's printer and the retraction law
  ({ref "kernel-in-lean"}[The kernel runs in Lean]), and the syntaxes of
  {citet RFC9804}[] with the Geb authoring profile, one document type read
  by all of them, replacing the kernel reader's syntax through an
  importer ({ref "rfc9804-syntaxes"}[The syntaxes of RFC 9804]);
  `Geb/Prototypes/CanonicalSExpr.lean` supplies the canonical codec over
  trees of numerals, generalized to atoms of bytes, and
  `Geb/Prototypes/Kernel/Document.lean` the document and its layouts.
* Chains of tests and bindings. The kernel's conditional and `let` are
  binary, so chains of tests and of bindings nest, and under a layout
  parinfer admits, nesting is indentation. The chain of tests of rules in
  `bootstrap/goedel-t/equations.geb` gives the only lines the formatter
  cannot keep within 100 columns, and the written files' flat chains are
  what parinfer's Indent Mode restructures
  ({ref "source-documents"}[Source documents and the formatter]). Forms
  `let*`, of several bindings, and `cond`, of several guarded branches,
  expanded by the reader as the lists of binders of `lam` are, remove
  both; they are widenings, and precede long chains.
* The equivalence of the word-level codec with
  {name}`Geb.RoseTree.wire`, tested and not proved, which is the first
  of the decision gates of the value-representation chapter.
* Memory. The plain representation takes about 480 bytes of memory per
  byte of input to the host driver; the optimized representation of the
  value-representation chapter removes most of it.
* Folds that read their children's results twice. The type checker
  `typeIn`, the resolver `resolve` and the other folds at pairs of a
  subtree and a function whose step reads the list of its children's
  results more than once are the only definitions of the bootstrap's
  programs that an elementary-affine typing with first-order data
  exempted rejects ({ref "choice-of-machine"}[The choice of machine]).
  A step that splits the list once, as the datatype language's
  structural recursion does, contracts no list of functions; where the
  step loops over the children's functions, the loop composes them
  into one function and the step returns it, a loop inside a closure
  over the argument not being typable. The requirement that the
  bootstrap's programs be decorated waits on that rewriting.
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
* Load time. The kernel checks the loading of the metalogic's program
  by evaluating the checker-evaluator {name}`Geb.Kernel.infer`, by
  reduction, on each definition in the globals before it, and comparing
  the denotation it computes with the definition's mirror. The check
  takes hours and grows faster than the program. The program is loaded a
  layer to a module, generated with the mirror by `scripts/bootstrap.sh`,
  so a change to a layer's sources checks again that layer, the layers
  after it, and the equality of the program's exported definitions with
  their mirrors, and no other layer. The kernel makes the check in the
  loading mode `rfl`, daily in CI and on demand; in the default mode
  `native` the facts it checks are axioms, declared after the compiled
  checker-evaluator has loaded the program
  (`docs/rules/ci-and-workflow.md` § Loading modes). Each global's type
  is computed from its definition ({name}`Geb.Kernel.defType`) rather
  than stored: the checker-evaluator builds a type from its constructors
  and from type annotations its fold rebuilds, and the kernel cannot
  equate the children of a rebuilt node with those of a constructed one,
  so a stored type equals a computed one only by decision, while the
  casts inside a denotation compare them by reduction. A shorter check in
  the mode `rfl` is made before or shortly after the end of the
  bootstrap, as its duration requires.
* Emitted names. A program's definition named `T`, `leaf` or `mk` makes
  the emitted module ill-typed, since the module refers to the tree type,
  the leaf and the node by those names; qualifying them as the constants
  are qualified, as the hygiene of generated names requires, removes the
  restriction.
* The datatype language annotates every value of a datatype as the type
  of trees and lacks generated recognizers, type parameters and a static
  check of datatypes, so the datatype a value belongs to is recorded
  nowhere, which its completion removes
  ({ref "datatype-completion"}[The datatype language's completion]); a
  pattern omits the `&` that a declaration writes; and every pattern
  variable is bound whether or not the clause uses it.
* Only the names of definitions are kept beside a bundle; the names of
  bound variables and comments are not. The source documents keep the
  comments, and the durable document of the authoring sequence keeps
  both ({ref "documents-annotations"}[Documents and annotations]).
* Proof time. The prover finds the weakening proof in about a minute
  and the checker checks it in half of one, most of both normalizing the
  checker afresh at each of the label's cases, whose cost is the
  substitutions of β-reduction and of the folds' steps. Recursion
  equations of the checker and of the traversal at a construction,
  proved once and rewritten by with their folds left unexpanded, shorten
  both; a substitution that shifts a substituted term once rather than
  at each binder, and leaves a closed one in place, is a tenth to a fifth
  faster, and would replace the language's by a `csimp` lemma proving the
  two equal; and a stored derivation would leave the check alone, and
  spare the substitution test, which proves weakening again as a lemma
  before its own theorem.

## The next phase
%%%
tag := "the-next-phase"
%%%

The proofs about the compiler's components that need neither the
printer nor a checker written in Geb are complete: the type checker's
preservation of types by weakening and by substitution and the identity
of the datatype language's expansion on programs of kernel forms
({ref "goedel-t"}[Gödel's T]). The reader's
inverse to the printer waits on the printer; the admission of a stronger
checker beside the metalogic's checker written in Geb, whose agreement
with the Lean checker is proved, is ready (the section on the metalogic
and its checker). The first of the two items below is complete, the
checker, the translation, the prover, its tactics and the combinator
prover written in Geb and their agreement proved. The second proves a
property of the kernel's reader, so it followed the change of that
reader's syntax to the authoring profile, which is complete
({ref "authoring-sequence"}[The sequence and its acceptance]); the next
phase is the second, which is ready:

* The metalogic's checker, its prover and the translation of kernel
  programs written in Geb, the checker in Geb and proof construction for
  the metalogic ({ref "logic"}[The logic]): the checker compared with the Lean checker on valid and
  malformed derivations and proved in Lean to agree with it, which the
  bootstrap requires; the prover, its tactics and the combinator
  prover, each proved in Lean to agree with its Lean prototype, so that
  the prover written in Geb constructs exactly the derivations the Lean
  prover constructs; and the translation proved in Lean to agree with
  the Lean translation. During the bootstrap it meets the logic's end point and
  the metalogic's acceptance, lets the proofs about programs be made
  without the Lean prototype, and is the checker every stronger checker
  is admitted beside. After the bootstrap it checks the proofs the road
  map lists, written in Geb, and is the checker of a host or a backend
  without Lean, which cannot run the Lean checker.
* The printer for the kernel's readable syntax and the retraction law
  (the section on improvements), and then the reader's inverse to the
  printer, proved in the metalogic by the method of the three complete
  proofs, of the reader of the authoring profile.

The admission of stronger checkers rests on the checker written in Geb
and its agreement, and two are required by the bootstrap. The provers
compare the sides of an equation in their normal forms under rewriting
rules, a conversion that the metalogic's checker does not compute but
checks step by step in the derivation, so the first is a checker with a
step of conversion to a normal form under named rules, which the checker
computes, admitted by the translation of that step into the derivation
the provers construct. The evaluation of primitives at literals, which the
language derives by folds over their bits, is a family of its rules, each
step translated into that derivation. Which rules it carries is decided,
as the choices of when the Mitchell–Bénabou language is written and
whether Gödel's T keeps its own checker were, by measurement: the nodes
of the complete proofs' derivations, counted by rule, locate the steps it
would take at once. The second is the checker of holes, admitted beside
the first rather than beside the metalogic's checker: its certificates
are the first's with leaves for open obligations, its translation targets
the first, and its soundness rests on the first's, as each of Milawa's
levels rests on the one below. Its conclusions are conditional, the
obligations of the holes implying the goal, which the metalogic's checker
can state ({ref "authoring-compatibility"}[Authoring across bootstrap
revisions]). One checker admitted beside another admitted checker shows
the admission repeatable. The checker of the shared certificates, admitted
by unsharing, a translation that spells out each index as its term and
each rule of the oracle as the typing lemmas the prover emits without it,
speeds the developments of the combinators' certificates, which the
proofs about programs do not cite; it is required by the bootstrap if
measurement shows the checking or storage of cached certificates to need
it, and follows the bootstrap otherwise (`TODO.md` § Triggers).
During the bootstrap a stronger checker shortens the
proofs about the compiler's components, whose derivations have from
600000 to 1240000 nodes and take from 30 to 40 seconds to check. After
the bootstrap it bears on the size of the proofs of the mathematics the
road map lists, and adds decision procedures and tactics as single
steps without adding to what is trusted.

The rest of the road map's bootstrap is independent of these proofs and
may proceed beside them: the choice of machine and the second host;
content identity; and the authoring sequence, the syntax unification
among it ({ref "authoring-sequence"}[The sequence and its acceptance]).

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

The digests of {ref "content-identity"}[Content identity] give
definitions an identity across edits; they
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

{includeLiterate "." Geb.Prototypes.GoedelT.Equations "Gödel's T over rose trees" (level := 1)}

{includeLiterate "." Geb.Prototypes.Bootstrap "A computation-certificate prototype" (level := 1)}
