# Authoring Geb across bootstrap revisions

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [The compatibility contract](#the-compatibility-contract)
- [What the bootstrap already retains](#what-the-bootstrap-already-retains)
- [Readable and canonical S-expressions](#readable-and-canonical-s-expressions)
- [Documents and separate annotations](#documents-and-separate-annotations)
- [Content identity and dependency references](#content-identity-and-dependency-references)
- [Files, names and the host boundary](#files-names-and-the-host-boundary)
- [Free-monad and comonadic addresses](#free-monad-and-comonadic-addresses)
- [Documentation and Verso](#documentation-and-verso)
- [Structural editing, highlighting and language services](#structural-editing-highlighting-and-language-services)
- [Typed holes](#typed-holes)
- [Synthesis and certificates](#synthesis-and-certificates)
  - [Canonical and suspended checking](#canonical-and-suspended-checking)
  - [SMT and grammar-directed synthesis](#smt-and-grammar-directed-synthesis)
  - [SupGen and shared enumeration](#supgen-and-shared-enumeration)
- [Further requirements before substantial authoring](#further-requirements-before-substantial-authoring)
- [Recommended order and acceptance](#recommended-order-and-acceptance)

<!-- END doctoc -->

The proposed prerequisite for substantial Geb development is a
versioned, information-preserving authoring representation, with a
checked route to the bootstrap that exists. A content store, a second
runtime and a new proof-search engine can follow it. Source migration
can preserve only information that the authoring representation retains.

This document distinguishes recommendations from implemented contracts.
The [bootstrap chapter](../manual/GebManual/Bootstrap.lean) records the
implementation milestones. The
[syntax survey](concrete-syntaxes.md) supplies the syntax and annotation
constructions, and [definitions](definitions.md) supplies the block,
linking and address constructions.

## The compatibility contract

For a syntax with parser `p : C → Option D` and printer `q : D → C`,
the required equation is

```text
p (q d) = some d.
```

Thus the parser retracts the printer; the printer is a section of the
parser. Parsing followed by printing is a partial idempotent. The
repository proves that consequence, and printer injectivity, in
[ConcreteSyntax.lean](../Geb/Prototypes/ConcreteSyntax.lean).

For two syntaxes of the same document type, define

```text
migrate₁₂ c = (p₁ c).map q₂.
(migrate₁₂ c).bind p₂ = p₁ c.
(migrate₁₂ c).bind migrate₂₃ = migrate₁₃ c.
```

These equations follow from the destination retraction. The migration
preserves the parsed document, not necessarily its original whitespace.
A source formatter may choose a normal layout while preserving every
name, comment and document link represented in `D`.

Changing the document or core schema requires a further computable map
and its preservation theorem. For a document migration `M`, core
migration `m` and erasures `erase₁`, `erase₂`, the obligation is

```text
erase₂ (M d) = m (erase₁ d).
```

Lossless changes additionally need an inverse or a retained representation
of the old information. Elaboration of datatypes, abbreviations and
syntactic conveniences need not be invertible: retain the authoring
document beside its elaborated result. A printed expanded kernel term
cannot recover the author's original abstractions.

Universal properties fix the interpretation up to the relevant
structure-preserving isomorphism, or equivalence when categories are
being compared. They do not themselves supply a serialized schema,
an executable migration, source locations or a performance bound. A
replacement implementation must provide the comparison and show that
interpretation commutes with it. Where input or output representations
change, the observation maps must commute as well. The
[definition design](definitions.md#content-identity) already separates
equality of presentations from equality of their denotations.

Library behavior needs its own compatibility contract. Two sound provers
may return different certificates or find proofs on different inputs;
soundness alone does not make them equal as Geb functions returning
certificate data. Keep the old dependency available, or prove replacement
equivalent for the observations the API permits. Hiding a certificate
behind a proved abstraction can permit changes to its representation;
merely promising any checked witness does not erase differences that a
client can still observe. Exact output agreement with the Lean
implementation is a useful bootstrap milestone, not a substitute for
choosing that public contract.

The resulting compatibility policy should cover accepted programs of a
named profile. A program that depended on an implementation error may
not admit a semantics-preserving migration to the corrected meaning.
Preserve its original source and compiler profile, identify the
discrepancy, and require an explicit repair decision. Neither a universal
property nor a converter can infer which behavior the author intended.

Track the verification boundary through the whole pipeline. Soundness
and agreement of the metalogic checkers do not by themselves prove the
reader, serializer, code generator, host compiler or file driver correct.
The bootstrap's byte-for-byte fixed points are regression evidence,
not a replacement for those preservation theorems. Keep the proved and
tested obligations explicit, including the word-codec gap below.

## What the bootstrap already retains

| Component | Implemented contract or limitation |
| --- | --- |
| [Kernel reader](../Geb/Prototypes/Kernel/Reader.lean) | Resolves definition names to bundle positions and binders to de Bruijn indices; expands abbreviations; discards lexical comments. It has no matching program printer. |
| [Canonical S-expressions](../Geb/Prototypes/CanonicalSExpr.lean) | Proved retractions for the finite-alphabet tree presentations. The generic renderer counts characters; its documented RFC conformance applies to ASCII atoms. |
| [Readable S-expressions](../Geb/Prototypes/ReadableSExpr.lean) | A proved numeral-labelled rose-tree syntax, distinct from the bootstrap reader and from RFC 9804's advanced syntax. |
| [Definition vertices](../Geb/Prototypes/Definition/Vertex.lean) | Subterm selection, address composition and their laws. These already provide a basis for occurrence addressing. |
| [Images](../Geb/Prototypes/Kernel/Image.lean) | A versioned bundle representation retaining definition names. Binder names and comments are absent. The executable word codec's agreement with the wire representation is tested rather than proved. |
| [File driver](../Geb/Prototypes/Kernel/Command.lean) | Ordered source files joined with a newline; file operations remain in the host. |
| [Lean emitter](../bootstrap/stage1/lean.geb) | Emits definitions with their names and a generated module comment, without transporting author documentation or source spans. |
| [Contextual hole filling](../Geb/Prototypes/Kernel/Hole.lean) | Checks and fills one explicitly typed contextual hole, with a theorem for the result's typing and denotation. It is a Lean API, not a surface-language or editor feature. |

The syntax prototypes' retractions therefore do not yet certify migration
of bootstrap programs. The missing connection includes arbitrary atom
bytes, the program grammar, name resolution and the authoring document.

## Readable and canonical S-expressions

Use RFC 9804 advanced S-expressions for the first durable human-readable
profile, and its canonical form for exchange, with a specified Geb
mapping into their shared data model. RFC 9804 is an Informational RFC,
not an Internet Standards Track specification. It describes both forms
in one document. Its atoms carry octet strings and optional display
hints; canonical lengths count bytes. Advanced tokens cannot start with
digits, and semicolon comments are not part of its grammar. These details
prevent treating the existing `.geb` reader as an implementation of that
profile.
[RFC 9804, §§3–8](https://www.rfc-editor.org/rfc/rfc9804.html).

The first printer can emit a restricted, deterministic readable subset:
lists, legal tokens and quoted atoms with one escape convention. The
parser's supported subset must be named accurately; support for the full
advanced grammar is a separate conformance claim. Numeral atoms such
as the current `0` acquire quotes or a length prefix. Existing atoms
containing punctuation outside the token alphabet acquire quotes. This
changes spelling, not their decoded bytes. Resolve whether an atom names
a numeral, identifier or datum at the Geb grammar layer.

Before adopting the profile, implement byte-based atoms and decide text
interpretation: UTF-8 for human names and prose, with exact byte
preservation; no implicit Unicode normalization. Keep binary atoms
available for exchange. A canonical file containing arbitrary bytes is
not an editor buffer: generic whitespace trimming or encoding conversion
can corrupt a length-prefixed atom.

There is a readability tradeoff for Unicode: strict RFC quoted strings
escape non-ASCII UTF-8 bytes; verbatim atoms instead need byte lengths.
If direct Unicode prose is essential, use a separately named convenience
profile with the same document retraction. The preserved UTF-8 bytes
make that spelling change mechanical. Exclude display hints from the
first Geb profile, as RFC §8 permits, using document fields for format
information. If later accepted, retain their exact bytes. General RFC
conformance also requires the basic transport form; a restricted Geb
codec must not claim that conformance prematurely.

Durable documentation should be an explicit field or annotation form in
the document grammar. A readable projection can display it beside the
code. If semicolon comments remain in a convenience syntax, give that
syntax its own profile and parse those comments into annotation values;
do not silently call it RFC 9804. The
[existing annotation design](concrete-syntaxes.md#lexical-comments-are-not-durable)
already requires this distinction.

The alternative is to retain today's syntax while first proving its
program retraction. That avoids changing both readers immediately, but
delays useful atom quoting and durable prose. Prefer the RFC-based route
for new substantial source, while keeping a legacy importer. Its first
acceptance condition should convert actual bootstrap sources, preserve
names and comments, and reproduce their checked core bundles. A proof
over a numeral-only tree does not meet that condition.

## Documents and separate annotations

Separate the compiler's core from annotations in memory and in build
artifacts. Initially keep an ordinary editable source document as the
authoritative input. Parsing can produce the core and its annotation
table together; compilation then traverses only the core. A documentation
change can reuse a checked core artifact once their identities are
separated. Measure the speed benefit on real documents.

This offers ordinary text editing, diffs and reviews without requiring a
projection editor before any documentation can be written. The alternative,
two independently authoritative files, requires atomic updates,
stale-annotation detection and coordinated merging. Adopt it when a store
or editor provides those operations, with a proved conversion from the
single-document representation.

Retain at least declaration and binder display names, ordered prose,
document links, examples, and source-to-core associations. Preserve
unknown versioned annotation fields on read and write. Type annotations,
datatype encodings and other information affecting elaboration must stay
in the checked input; calling them decorations must not cause their
erasure to change meaning.

Use occurrence keys relative to a particular document or definition
revision. Two identical subtrees can have different comments. A key made
only from their subtree hash cannot express that distinction. Metadata
intended for all instances of an identical definition can use its content
identity instead. These are different attachments, as the
[syntax survey](concrete-syntaxes.md#wrapper-model-environment-model-and-the-occurrence-pitfall)
explains.

A path remains meaningful only in its identified root. A representation
migration must transport paths. An arbitrary program edit can delete,
duplicate or combine occurrences, so a migration of meaning alone cannot
determine where every comment belongs. Retain an explicit edit map or
retain unmatched annotations for reconciliation; do not silently attach
them to the nearest equal subtree. Source maps through elaboration may
be relations because one source form can generate several core nodes.

## Content identity and dependency references

Freeze the identity-bearing payload schema before publishing durable
identifiers. The existing
[block proposal](definitions.md#content-identity) is the appropriate
starting point:

```text
(schema version, semantic profile reference,
 import interface, export layout, definition bodies)
```

The profile determines primitive identities, binding rules and the
interpretation of the representation. Display names and comments stay
outside this payload. Include types or certificates when they affect
meaning; a separately checked certificate of an already identified term
can be a separate artifact.

Use a versioned identifier containing a multihash, or CIDv1 for an actual
serialized block with a specified codec. Multihash identifies a hash
algorithm and digest; it does not version the Geb schema or specify the
bytes hashed. IPLD CIDs additionally identify the codec. A structural
Merkle digest should not be presented as the CID of unrelated exchange
bytes. [IPLD primer](https://ipld.io/docs/intro/primer/).

Choose one initial algorithm before assigning those identifiers. The
bootstrap chapter already records the unresolved BLAKE3 versus SHA3-256
choice. Preserve the multihash envelope and version the payload; the
algorithm choice need not delay source authoring. A local store of
canonical definition blocks is sufficient initially. IPFS networking,
CAR archives, per-node hashing and graph-wide deduplication are later
storage features.

Call this structural content identity, not general semantic identity.
Alpha-renaming can leave a resolved representation unchanged; inlining,
changing a derived operation or choosing a different proof usually does
not. Semantic equivalence belongs to checked certificates. Equal finite
hashes are not proofs of equal unbounded trees. Verify retrieved content,
compare canonical payloads before identifying objects, and reject an
identifier associated with conflicting payloads.

Unison is a precedent for separating names from identity and for referring
to a member of a recursive component by a component hash and index.
Geb can use its validated export direction in place of the index.
[Unison hashes](https://www.unison-lang.org/docs/language-reference/hashes/).

Full hashing is unnecessary to prepare migration. Preserve complete
frozen bundles, their semantic profile and their dependency order.
Before hashes exist, an address is a position relative to that frozen
bundle, never a globally meaningful integer. Migrate in dependency order,
rewriting explicit external-reference constructors and producing an
old-to-new reference map. Keep the original artifacts and re-key
annotations using that map. A later algorithm or schema transition
similarly computes new identifiers; it does not promise identical hashes.

The traversal must understand the grammar. A data tree inside a quotation
may happen to contain the external-reference label; that does not make
it a code reference. Reflective code values require explicit schema
identification and their own transport. The kernel's
[substitution traversal](../Geb/Prototypes/Kernel/Subst.lean) already
treats quotations separately from term children.

## Files, names and the host boundary

Continue using ordered source assembly, which the host driver already
supports. Record the source list, entry points and compilation profile
in a toolchain manifest. Files organize authoring and delivery; semantic
dependencies are references to definitions. Do not use directory scans
or the current working directory to decide binding order implicitly.

The first linker can retain the existing well-founded order. It should
resolve each import to an explicit definition, reject unresolved and
ambiguous references, and check the resulting bundle. Hash references
can replace frozen positional references later. General cyclic blocks
and canonical ordering of recursive components are unnecessary for the
bootstrap's fold-based recursion. Merely sorting recursive members by
their hashes is not a solution to symmetric cycles.

Names require attention before a large source library: reserve generated
identifiers or make expansion hygienic, and give generated Lean names
an injective escaping scheme with qualified runtime names. The bootstrap
chapter records primitive capture in datatype expansion and conflicts
with emitted `T`, `leaf` and `mk`. Fix those shared boundaries before
encouraging unrestricted new names. Preserve the old resolver's meaning
when importing existing source; retroactively changing duplicate-name
or shadowing rules can change a previously accepted program.

Keep OS interaction as a pure request/result interface with a host
interpreter. Byte encoding, input framing, output framing, errors and
resource exhaustion need explicit contracts. A later effect interface
can implement that contract. Paths, clocks, environment variables and
platform integer sizes must not become hidden semantic inputs.

## Free-monad and comonadic addresses

Reuse the constructions in
[Definition/Vertex.lean](../Geb/Prototypes/Definition/Vertex.lean).
Free-monad directions select variable leaves; vertices select arbitrary
nodes. An export layout deliberately marks exports as variable leaves.
An annotation on an internal expression uses a vertex. Treating the two
address types as interchangeable loses occurrences.

Record the address vocabulary and its root now, and check paths on input.
The compact wire spelling and surface navigation syntax can wait. If
the representation changes, supply address transport and prove that
selection commutes with it. An isomorphism between values alone does not
automatically preserve a chosen set of addressable intermediate nodes.

The finite decorated-tree construction and its comonad laws already
exist in [ConcreteSyntax.lean](../Geb/Prototypes/ConcreteSyntax.lean).
The [survey](concrete-syntaxes.md#the-document-type-is-a-μ-not-a-ν)
distinguishes the cofree recursive construction from the possibly
infinite ordinary cofree comonad. Use that finite construction, or its
side-table presentation with a proved correspondence. A new general
comonad implementation is not a prerequisite for authoring.

## Documentation and Verso

Specify documentation storage before writing substantial prose; generate
Verso after that storage round-trips. Preserve document order, declaration
attachment, code examples and links to identified definitions or
occurrences. A format/version field with preserved prose bytes permits
starting with a selected Verso-compatible subset without implementing a
complete documentation parser.

Mark prose references that should track renaming as explicit links.
A migration can preserve unmarked prose bytes, but cannot infer which
words the author intended as references to code.

Generate declaration docstrings and module prose from those annotations,
and render them through the existing
[literate pipeline](rules/lean-coding.md#literate-modules). Resolve Geb
links through the compiler's name and source maps. Explicitly escape
Lean comment delimiters, quoted identifiers and markup. A free-form
string interpolated into generated Lean is not a safe encoding of a
document.

The emitted code can also accompany a generated manual page displaying
Geb source, with Lean used for checking examples. This may be more useful
than presenting only expanded Lean. Keeping the documentation model
independent of the renderer permits either view and later non-Lean
renderers. The current emitter's generated module comment supplies none
of these author-documentation guarantees.

Acceptance should include a module description, a documented definition,
a checked example and a cross-reference. Editing only documentation
should change the rendered manual and document identity while leaving
checked core identity unchanged.

## Structural editing, highlighting and language services

Start with VS Code's native bracket-pair colors and a small language
configuration/TextMate grammar for the selected readable profile.
Neither requires LSP. VS Code describes these as declarative language
features; diagnostics, hovers and navigation are programmatic features.
[VS Code language extensions](https://code.visualstudio.com/api/language-extensions/overview),
[bracket colors](https://code.visualstudio.com/docs/editing/editingevolved#_bracket-pair-colorization).

For explicit structural editing, the first extension to evaluate is
`MikeDelmonaco.paredit`. It extracts Calva's structural operations, accepts
language-specific delimiters and reads comment configuration. Calva
itself is an alternative if its Clojure-specific behavior is wanted.
Neither should be presumed to parse arbitrary RFC advanced or canonical
S-expressions correctly.
[Mike's Paredit](https://marketplace.visualstudio.com/items?itemName=MikeDelmonaco.paredit),
[Calva Paredit](https://calva.io/paredit/).

Prefer explicit Paredit edits initially. Parinfer Paren Mode is a
candidate formatter, subject to `parseDoc (format c) = parseDoc c` and
idempotence. Its Indent Mode intentionally changes parenthesis structure;
that is an edit operation rather than a semantics-preserving formatter.
The equations on Parinfer's page are stated desired properties, not a
machine-checked proof for Geb's grammar.
[Parinfer's mathematical foundation](https://shaunlebron.github.io/parinfer/#mathematical-foundation).

A corpus regression can format the bootstrap sources with a pinned
Paren Mode, check token preservation and idempotence, and require the
formatted stage-1 source to reproduce `bootstrap/compiler.img` and
`bootstrap/lean/GebBoot.lean` byte for byte. This tests the legacy grammar,
not all accepted inputs or the editor integration. Pin and test the
extension's actual engine before making it the supported default.

The editor acceptance fixture should contain nested bindings, comment
parentheses, quoted parentheses and semicolons, escaped quotes, Unicode
names, CRLF input, and incomplete syntax. Test navigation, selection,
wrap, slurp, barf and undo in VS Code. For formatting, compare parsed
documents, including annotations, before and after; for structural edits,
check the intended tree change and re-run the checker. A Lisp editor's
recognition of additional bracket kinds or reader macros must not
silently define Geb syntax. Keep format-on-save disabled until that
fixture passes.

Tree-sitter is an incremental, error-tolerant concrete-syntax parser; it
can help with selection and incomplete buffers independently of LSP.
Add it when those services need it, with a grammar derived from the same
profile. Its error recovery must not supply trusted compiler input.
[Tree-sitter introduction](https://tree-sitter.github.io/tree-sitter/).

An initial language service needs source spans and structured diagnostics,
then definition lookup, inferred/expected types and hole obligations.
LSP transports those services between the checker process and the
editor; it is not the mechanism that stores or reconstructs annotations.
Use the existing checker behind that interface. Track buffer versions,
cancel stale checks and translate byte offsets to the negotiated editor
position encoding. These are prerequisites for reliable diagnostics
after Unicode edits.
[VS Code language-server guide](https://code.visualstudio.com/api/language-extensions/language-server-extension-guide).

## Typed holes

Begin with term holes whose types and local contexts are explicit.
For one hole, the existing kernel suffices:

```text
sketch : A :: Γ ⊢ B
filling : Γ ⊢ A
subst filling sketch : Γ ⊢ B
```

In the Cartesian interpretation, the sketch is a map `A × Γ → B`
and the filling a map `Γ → A`. Filling composes the sketch with
`⟨filling, id⟩ : Γ → A × Γ`. This is ordinary substitution; a new
slice or presheaf development is not needed for this first operation.
The denotation equation is already the kernel's `infer_subst` theorem.

[Hole.lean](../Geb/Prototypes/Kernel/Hole.lean) implements `fillHole`,
which checks the expected type, the filling and the sketch before
substituting. `infer_fillHole` proves the typing and denotation of every
accepted result; `fillHole_of_infer` proves acceptance of valid inputs.
The [kernel examples](../GebTests/Prototypes/Kernel.lean) cover capture
avoidance, repeated occurrences, and rejection of wrong types, escaping
variables, invalid sketches and malformed expected types. Run them with
`lake build GebTests.Prototypes.Kernel`.

The next authoring layer assigns hole identities and records each one's
context, expected type, source occurrence and constraints. Repeated uses
of a named hole share one obligation; unrelated holes of the same type
do not. Occurrences in different scopes require explicit substitutions
from the hole's declaring context. One contextual variable as above is
not a complete implementation of that machinery.

For proof holes, expose an open sequent and its undischarged obligations.
Only a closed derivation is accepted as the original theorem. A sketch
is useful editor state, not an axiom or a completed program. An initial
implementation can decline to execute through holes and can require
explicit types; live evaluation through holes and inference of missing
types are separate extensions.

Contextual modal type theory studies metavariables with explicit
contexts and substitutions. Hazelnut studies typed editing states,
including incomplete terms, with mechanized metatheory. These are
appropriate references for the richer interface; their entire calculi
need not enter Geb's trusted logic.
[Nanevski–Pfenning–Pientka](https://www.cs.cmu.edu/~fp/papers/tocl07.pdf),
[Hazelnut](https://arxiv.org/abs/1607.04180),
[Hazelnut Live](https://arxiv.org/abs/1805.00155).

A hole-aware elaborator is a possible relative-soundness exercise: filling
all obligations produces an ordinary checked term or derivation. It need
not be the first stronger checker. The bootstrap chapter's candidates
for compressed conversion and shared certificates address existing proof
costs more directly. Admitting a checker of open sketches must not be
confused with admitting their unresolved conclusions.

## Synthesis and certificates

Use the hole obligation as the interface to synthesis. A request includes
the frozen dependencies, profile, context, target type or proposition,
permitted grammar, examples and resource budget. A result contains a
candidate and, when a semantic property is claimed, its certificate.
Record the input revision so a result cannot be applied silently to a
different hole. Failure or budget exhaustion supplies no refutation.

Begin with lookup of matching local terms, constructor introduction,
application, rewriting by named theorems and bounded enumeration. Reuse
the prover being written in Geb as the certificate producer. These
operations can already make explicit typed holes useful without a new
solver dependency.

Keep the synthesis target explicit. Inhabiting a computational type such
as `Tree → Tree` does not specify the behavior of a translator. Search
jointly for a program and a derivation of its specification, with shared
unknowns between them. A derivation of an internal existential statement
is not automatically an executable witness: general topos semantics
interprets existential quantification through images, without supplying
sections of every epimorphism. Any broader extraction claim needs its
own theorem. For unique existence, the repository already proves the
relevant description property in
[Internal.Connectives](../Geb/Prototypes/FreeTopos/Internal/Connectives.lean).
Require a term in the selected executable fragment when the requested
result is a program.
[Borceux, *Some flavours of topos theory*, §§3.5, 4.4–4.5](https://www.uclouvain.be/system/files/uclouvain_assetmanager/groups/cms-editors-irmp/Lecture%20Notes.pdf).

### Canonical and suspended checking

Canonical is the proposed first general synthesis experiment. Its
refinement of holes and its suspension of checks fit the contextual-hole
interface, and both a paper and a small implementation are available.
This is a recommendation about an approach to test, not a performance
prediction from Geb's smaller syntax.
[Norman and Avigad, ITP 2025, DOI 10.4230/LIPIcs.ITP.2025.14](https://drops.dagstuhl.de/storage/00lipics/lipics-vol352-itp2025/LIPIcs.ITP.2025.14/LIPIcs.ITP.2025.14.pdf),
[Canonical-min](https://github.com/chasenorman/Canonical-min).

The source references below pin revision
`72a24f13ec2e6ff3150e609cb5edbc70ef59a236`. The advertised small core is
not the entire Lean integration: its
[tactic wrapper](https://github.com/chasenorman/Canonical-min/blob/72a24f13ec2e6ff3150e609cb5edbc70ef59a236/CanonicalMin.lean)
imports `Canonical` for premise preparation, translation and proof
reconstruction. The core implements search using `partial` functions;
being Lean source does not itself constitute a machine-checked proof
of search soundness or completeness.

The transferable operations are:

1. Give each unknown its declaring context and an explicit substitution
   at each use. Represent a candidate application by its head and all
   its argument holes. The
   [data representation](https://github.com/chasenorman/Canonical-min/blob/72a24f13ec2e6ff3150e609cb5edbc70ef59a236/CanonicalMin/Data.lean)
   separates unknowns, assignments and substitution blocks.
2. When checking needs an unassigned hole, suspend the remaining check
   on that hole. Continue independent checks of the other arguments.
   Thus a later argument can constrain an earlier one. In particular,
   a proof argument can constrain the witness it is about.
   The implementation makes this independence explicit through
   `judgment` in its
   [continuation monad](https://github.com/chasenorman/Canonical-min/blob/72a24f13ec2e6ff3150e609cb5edbc70ef59a236/CanonicalMin/Monad.lean).
3. Choose a hole and a head, allocate its argument holes together,
   then resume checks waiting on that assignment. Reject a branch when
   a constraint fails; undo its assignments and constraints on
   backtracking. The minimal
   [search](https://github.com/chasenorman/Canonical-min/blob/72a24f13ec2e6ff3150e609cb5edbc70ef59a236/CanonicalMin/Search.lean)
   favors rigid constraints and otherwise later arguments. It increases
   both a term-capacity bound and a heuristic search budget.

There are two implementation routes:

| Route | Benefit | Work required |
| --- | --- | --- |
| Encode Geb derivations as an external Canonical signature | Exercise an existing search implementation | Specify the exact signature, scoping, substitution and decoding; reconstruct a Geb derivation and check it. A Lean proof of an analogous statement alone is insufficient. |
| Implement refinement over Geb terms and derivations | Reuse the actual language and its checker; implement bounded search in Geb | Add contextual metavariables and suspended constraints; adapt checking, branching and reduction to partial syntax. |

Prefer the second route for the implementation intended to survive the
bootstrap. Start with the finite grammar of selected heads and proof
rules for actual hole obligations. For logical goals, search for a Geb
derivation of the sequent, not arbitrary inhabitants of Lean's `Prop`.
For computational goals, share candidate-term holes with the derivation
of the required property. Defining dependent types in Geb's object
language is not a prerequisite for representing these search states.

Reuse the existing
[internal-language prover](../Geb/Prototypes/FreeTopos/Internal/Prove.lean):
it already provides scoped theorem matching, certificate-producing
normalization, function extensionality, case analysis and induction
combinators. Preserve its checked theorem and induction interfaces as
ways of discharging obligations. Its matcher handles supplied terms;
suspension and shared unknowns are additional work, not an existing
general unifier. Search normalization must use justified computational
equations, without assuming that arbitrary metalogic equality is
decidable by normalization.

The minimal implementation stores suspended work as Lean function
closures. For a first Geb implementation, represent the checks as
explicit finite work items, carrying contexts and substitutions. Resume
only those affected by an assignment. Use a natural-number budget for
both search and reduction, returning unfinished state when it runs out;
the host may request another bounded run. This replaces unrestricted
search with total operations expressible in System T. Heuristic
floating-point entropy is not required for the first implementation.

Do not equate a blocked check with a failed check. For example, an
equation `natRec z s ?n = z` may become true when `?n` is zero. The
paper's §3.3.1 distinguishes a pruning default from its more permissive
`synth` mode on such constraints. A Geb implementation claiming complete
search over its chosen grammar must retain viable blocked branches.
Likewise, the paper's §4 describes universe erasure in its Lean encoding;
that encoding is not a foundation for Geb. Keep the final Geb checker
as the acceptance boundary.
[Canonical paper](https://drops.dagstuhl.de/storage/00lipics/lipics-vol352-itp2025/LIPIcs.ITP.2025.14/LIPIcs.ITP.2025.14.pdf).

Separate the verification obligations. Checking every completed
candidate establishes accepted-result correctness through the existing
checker. Correct pruning additionally requires that a rejected partial
state has no valid completion. Completeness additionally requires
coverage of the selected grammar, correct scoping and backtracking,
and fair exploration as bounds increase. An exhausted finite run
establishes none of these global claims.

The first experiment should compare this refinement against simple
typed enumeration on the same finite grammar. Include composition,
repeated holes under binders, a proof constraining an earlier witness,
and a fold blocked on an unknown argument. Replay every resulting
certificate. Record search nodes, reduction work, checking time and
certificate size. Add induction-motive search after the basic constraints
work; use the existing induction combinators in the meantime. This
experiment depends on richer contextual holes than `fillHole` alone
provides, and remains to be implemented.

### SMT and grammar-directed synthesis

Z3 can propose witnesses for bounded data and decoration constraints,
as in the [elementary-affine prototype](../scripts/eal/eal.py). Validate
the witness in Geb. cvc5's SyGuS interface additionally accepts a grammar
restricting candidate implementations, which suits small arithmetic or
datatype fragments. It is a more direct synthesis interface to evaluate
than building an unrestricted solver bridge first.
[cvc5 synthesis example](https://cvc5.github.io/docs/latest/examples/sygus-fun.html),
[SyGuS 2.1](https://arxiv.org/abs/2312.06001).

An SMT proof is not automatically a Geb proof. Its theory, Boolean
reasoning and encoding must be related to the constructive metalogic.
An unsatisfiability proof for a classical encoding of a negated goal may
only provide a double-negated conclusion constructively. For a first
integration, use candidates checked by existing Geb rules, or restrict
to a fragment with a proved certificate translation. Examples and type
checking alone do not certify an arbitrary claimed program property.

### SupGen and shared enumeration

SupGen merits a bounded experiment after this interface exists. The
[sup-node search gist](https://gist.github.com/VictorTaelin/7fe49a99ebca42e5721aa1a3bb32e278)
contains a restricted program enumerator and reported timings; the
[collapse gist](https://gist.github.com/VictorTaelin/60d3bc72fb4edefecd42095e44138b41)
contains labelled-choice code and author-supplied corrections. They
establish material to experiment with, not a validated speedup for Geb.
The [HVM3 repository](https://github.com/HigherOrderCO/HVM3) supplies a
runtime and concrete search examples:
[an affine lambda-term enumerator](https://github.com/HigherOrderCO/HVM3/blob/fba2e9c82faf6e2f019c9ecea94c32f19a8b7820/examples/enum_lam_smart.hvm)
and [a type-directed enumerator](https://github.com/HigherOrderCO/HVM3/blob/fba2e9c82faf6e2f019c9ecea94c32f19a8b7820/examples/enum_coc_smart.hvm).
The former bounds binding depth and application arity; the latter uses
types to guide introduction and elimination. Their context discipline
and candidate grammar require adaptation to Geb. These are useful source
examples, not a verified Geb synthesizer or a completeness result for
its search space. An integration needs a pinned, runnable experiment
and an explicit account of that space and its search semantics.

The author's [SupVM gist](https://gist.github.com/VictorTaelin/7ae3d262e4d0b80a4e8817a80f976a68)
also provides a small TypeScript evaluator for a stated HVM subset,
representing correlated labelled choices with a map. It is further
experimental material, not a specification or verification of HVM.

Compare typed enumeration with shared enumeration on the same finite
Geb grammar and obligations. Measure candidate generation, checking,
certificate size, elapsed time and peak memory together. Labelled choice
correlations, scope and resource bounds need explicit semantics.
Superposition is a search representation; it does not add a new term
constructor to the accepted object language. Require the decoded result
to pass Geb's checker regardless of how it was found.

Canonical's constraint pruning and SupGen's sharing address different
costs and may eventually be combined. Establish the search space and a
checked baseline first. Use SMT/SyGuS for fragments with suitable
encodings, Canonical-style refinement for general contextual goals,
and shared enumeration when measurements show repeated search work
that sharing can eliminate. None is a prerequisite for preserving
source across bootstrap revisions.

## Further requirements before substantial authoring

| Requirement | Minimum contract |
| --- | --- |
| Elaboration stability | Preserve the higher-level source and its resolved core; version expansion and name-resolution rules; make generated names hygienic. |
| Library behavior | Freeze dependencies; replace an implementation only with proved equivalence for the API's permitted observations, or retain it under its old identity. Distinguish valid certificates from promises about which certificate a prover returns. |
| Schema and feature versions | Identify syntax, core, annotations, certificates and semantic profile separately; reject unsupported mandatory features and preserve optional opaque fields. |
| Persistent data | Treat serialized values, datatype constructor tags, examples and saved program inputs as versioned interfaces; code migration alone cannot migrate externally stored values. |
| Certificates | Keep the statement, theory/profile, dependencies and certificate format with the proof; provide replay or a certified translator when rules or encodings change. |
| Verification boundary | State which parsing, elaboration, serialization, code-generation and host-execution steps are proved and which are tested; transport correctness through the complete path used to run the program. |
| Reproducible builds | Keep source, dependency closure and compiler profile; distinguish document, checked core and generated-artifact identities; preserve a corpus of prior accepted programs. |
| Diagnostics | Return a structured success/error result and source occurrence; an empty compiler output is not a sufficient developer interface. |
| Editing and recovery | Save incomplete documents, hole obligations and unattached annotations; distinguish draft state from an accepted program; make multi-artifact updates atomic. |
| Performance and limits | Specify resource exhaustion separately from falsehood or ill-typing; benchmark representative edit/check/compile operations; allow implementations to improve without promising identical cost. |
| Reflection | Distinguish code representations from ordinary data; specify which structural observations are stable and how their quoted schemas migrate. |
| Host protocols | Fix byte/framing/error contracts and entry-point types independently of files, native word size and backend names. |

## Recommended order and acceptance

| Before substantial source | Acceptance condition |
| --- | --- |
| A durable authoring document and versioned profiles | Declaration/binder names, prose, examples, links and unknown optional fields survive read/print and conversion. |
| The chosen readable and canonical program codecs | Proved document retractions, byte-correct atoms and grammar conformance; legacy bootstrap programs convert to the same checked core. |
| Hygienic elaboration, explicit assembly and diagnostics | Primitive shadowing cannot alter generated operations; imports resolve deterministically; failures name a source occurrence and preserve existing outputs. |
| Occurrence addresses and dependency snapshots | Paths validate against a named root; repeated identical subtrees retain distinct annotations; frozen positional references convert in dependency order. |
| Editor and documentation examples | The actual VS Code extension passes the profile fixture; one Geb module renders prose, checked examples and links through Verso. |

Implement typed-hole syntax and obligation display immediately alongside
that work if they improve the first substantial module. The checked
filling operation above makes that an incremental tooling task, while
the contextual metavariable and proof-obligation extensions retain their
own proof obligations.

After these conditions hold, write the library in Geb and use that
development to drive content storage, richer LSP services, Tree-sitter,
solver adapters and runtime optimization. None of those later choices
should be allowed to discard the document, binding or dependency
information already preserved.
