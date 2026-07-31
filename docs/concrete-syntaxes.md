# Concrete syntaxes for the Geb abstract syntax tree

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Status](#status)
- [The AST and its isomorphisms](#the-ast-and-its-isomorphisms)
  - [The rose-tree presentation, derived and verified](#the-rose-tree-presentation-derived-and-verified)
  - [Which occurrences the rose presentation can name](#which-occurrences-the-rose-presentation-can-name)
  - [Applicative-calculus reading](#applicative-calculus-reading)
  - [Complexity note](#complexity-note)
- [Round-trip laws](#round-trip-laws)
  - [The setting is partial functions](#the-setting-is-partial-functions)
  - [Idempotence is a corollary, and so is injectivity](#idempotence-is-a-corollary-and-so-is-injectivity)
  - [The laws must be lifted to the annotated level](#the-laws-must-be-lifted-to-the-annotated-level)
- [Annotations](#annotations)
  - [The document type is a μ, not a ν](#the-document-type-is-a-%CE%BC-not-a-%CE%BD)
  - [The side-table presentation](#the-side-table-presentation)
  - [Wrapper model, environment model, and the occurrence pitfall](#wrapper-model-environment-model-and-the-occurrence-pitfall)
  - [Lexical comments are not durable](#lexical-comments-are-not-durable)
- [Canonicalization: two nested quotients, not one](#canonicalization-two-nested-quotients-not-one)
- [Merkle hashing as a catamorphism](#merkle-hashing-as-a-catamorphism)
- [Structural content-addressing specification](#structural-content-addressing-specification)
- [Format-by-format evaluation](#format-by-format-evaluation)
  - [Canonical S-expressions (RFC 9804)](#canonical-s-expressions-rfc-9804)
  - [CBOR (RFC 8949 §4.2) and DAG-CBOR](#cbor-rfc-8949-42-and-dag-cbor)
  - [JSON, JCS (RFC 8785), DAG-JSON](#json-jcs-rfc-8785-dag-json)
  - [Protocol Buffers — rejected for any hash-bearing role](#protocol-buffers--rejected-for-any-hash-bearing-role)
  - [Cap'n Proto — best typed-binary candidate, not chosen](#capn-proto--best-typed-binary-candidate-not-chosen)
  - [XML with C14N — the strongest "genuinely different" alternative](#xml-with-c14n--the-strongest-genuinely-different-alternative)
  - [WebAssembly text format (WAT)](#webassembly-text-format-wat)
  - [EDN](#edn)
  - [The remainder](#the-remainder)
- [Evaluating the candidates](#evaluating-the-candidates)
  - [The bootstrap set](#the-bootstrap-set)
- [Prior art on content-addressed code](#prior-art-on-content-addressed-code)
- [One tree, every recommended encoding](#one-tree-every-recommended-encoding)
- [Local verification](#local-verification)
- [Ecosystem notes](#ecosystem-notes)
- [Roadmap](#roadmap)
  - [Relation to existing repository content](#relation-to-existing-repository-content)
- [Caveats](#caveats)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Geb specifies its abstract syntax and leaves the concrete syntax open:
anything admitting a reliable extraction to the abstract syntax tree
is a valid concrete syntax. This document fixes the laws such an
extraction must satisfy, specifies the structural content addressing
built on the abstract syntax, surveys existing standards suitable for
the concrete role, and states the implementation roadmap.

## Status

The format-independent core and the first concrete syntax are
implemented in
[Geb/Internal/ConcreteSyntax.lean](../Geb/Internal/ConcreteSyntax.lean),
with tests in
[GebTests/Internal/ConcreteSyntax.lean](../GebTests/Internal/ConcreteSyntax.lean).
[Local verification](#local-verification) records the facts the
implementation fixes; [Roadmap](#roadmap) states the staging and
supersedes the format-by-format sections where the two differ.

Everything between § The AST and its isomorphisms and § References,
other than § Local verification and § Roadmap, is inherited text and
does not yet conform to
[CONTRIBUTING.md](../CONTRIBUTING.md) § Style and references; `TODO.md`
§ Prose-conformance pass over the concrete-syntax survey records the
outstanding pass and its scope.

## The AST and its isomorphisms

Geb's only specified syntax is the AST: the initial algebra
`μX. (k + X²)` of the polynomial endofunctor `F(X) = k + X²` — a finite
constant `k` of leaf labels plus a binary product for internal nodes;
`k = 1` gives unlabeled leaves, and `k = 0` gives the empty type. These
are full binary trees: every node is either a leaf carrying a label in
`{0, …, k − 1}` or an internal node with exactly two children.

### The rose-tree presentation, derived and verified

Writing `R = μX. (k × List X)` for `k`-labeled rose trees, the recursive
equation for `R` transforms as follows:

```text
R ≅ k × List R
  ≅ k × (1 + R × List R)        -- List R ≅ 1 + R × List R
  ≅ (k × 1) + (k × R × List R)  -- distributivity
  ≅ k + R × (k × List R)        -- unit, commutativity, associativity
  ≅ k + R × R                   -- k × List R ≅ R
```

So `R` satisfies the same fixed-point equation `X ≅ k + X²` as `A`.
Three precision caveats:

1. Satisfying the fixed-point equation does not by itself identify the
   initial algebra: the terminal coalgebra `νX. (k + X²)` of possibly
   infinite trees satisfies it too. The derivation supplies candidate
   maps; something further must prove them mutually inverse.
2. The bijection depends on a **convention**. Reading the last step
   forwards, a rose node `(l, t :: ts)` maps to the fork whose *left*
   child is the head child `t` and whose *right* child is the rose node
   `(l, ts)` carrying the label and the remaining siblings. Choosing the
   last child instead gives a different, equally valid bijection. The
   convention must be fixed and versioned, because annotation *paths*
   travel through it.
3. Reading the derivation off as a bijection of *initial algebras* is
   available but not free: `R` carries an `F`-algebra structure and `A`
   carries a `k × List(−)`-algebra structure, so initiality gives maps
   both ways, but concluding that the composites are identities needs
   the two algebra structures to be compatible. In a mechanized
   development it is shorter to define both maps directly and prove the
   round trips on each side — which is what `Ast.toRose`, `Ast.ofRose`,
   `Ast.ofRose_toRose` and `Ast.toRose_ofRose` do.

The classical left-child/right-sibling correspondence is the unlabeled
shadow of this: a bijection between binary trees and *forests* of rose
trees. The `k`-labeled statement is stronger and is the one Geb should
normatively adopt: binary tree as the core, rose tree as a surface
presentation.

### Which occurrences the rose presentation can name

Occurrences in `A` are words over `{L, R}`. Under the convention above,
child `i` of the rose node at binary position `q` sits at binary
position `q · Rⁱ · L`. Hence:

> The binary occurrences that are rose-tree nodes are the empty path
> together with the paths ending in `L`. Binary positions ending in `R`
> are sibling-list cells and have no rose-tree name.

`rosePathToBin_last` proves one inclusion of this: every path in the
image of `rosePathToBin` is empty or ends in `L`. The converse is not
proved, and no lemma connects `rosePathToBin` to the tree it indexes, so
the two design consequences below rest on statements the development
does not establish.

- A document written in a rose-shaped syntax can annotate strictly fewer
  positions than one written in a binary-shaped syntax. If both syntaxes
  are offered, the normative path vocabulary must be the binary one, and
  the rose syntax must be documented as annotating a sub-poset of the
  occurrences.
- Because sibling-list cells are unnameable in the rose view, an
  annotation attached to one and then round-tripped through a rose
  syntax would be silently lost. Either forbid such annotations in the
  rose profile or make `parseDoc`/`printDoc` for that profile total on a
  restricted `D`.

### Applicative-calculus reading

`μX. (k + X²)` is precisely the raw term syntax of an untyped
applicative combinator calculus with `k` constants: leaves are the
constants and each internal node is an application. In particular:

- `k = 1` gives the term syntax of Barry Jay's tree calculus (single
  operator `△`, binary application) — the free magma on one generator.
- `k = 2` gives SK-combinator terms, the base of the `RT(SK)`
  realizability construction.
- Nock nouns (an atom — a natural number — or a cell of exactly two
  nouns) are the `ℕ`-labeled analogue `μX. (ℕ + X²)`; Geb's AST is its
  restriction to a finite leaf alphabet.

Any syntax adequate for Geb's AST is therefore automatically adequate
for storing combinator-calculus terms, and vice versa.

### Complexity note

As algorithms, parsing, printing and the Merkle fold are linear in the
size of the tree with a constant number of passes. Neither implemented
map achieves that. `Csexp.printAst` re-appends at every level, so each
node's output is copied once per ancestor. `Csexp.parse` evaluates
`r.length` over the whole remaining input at every atom, and
`Csexp.readDigits` is a strict `List.rec` that traverses the rest of the
input even when the first character is not a digit; the cost is the
node count times the input length. An accumulator-passing printer and a
parser carrying the remaining length would restore linearity, at the
cost of restating and reproving `parseAst_printAst` and `parse_print`,
which are stated about the present maps.

All three are elementary — indeed they sit in the lower-elementary
fragment once the hash primitive is taken as a unit-cost oracle. Nothing
in this design requires more than bounded primitive recursion over the
tree, which matters for a project that tracks where its constructions
sit in the Grzegorczyk hierarchy.

## Round-trip laws

The specified laws are `parse : C → Option A`, `print : A → C`, with
`parse (print a) = some a` for all `a`.

### The setting is partial functions

`print` is total and `parse` is partial, so the split-idempotent
statement lives in the category **Par** of sets and partial functions
(equivalently the Kleisli category of `Option`), not in **Set**. There,
`parse ∘ print = id_A` makes `print` a split monomorphism and `parse` a
split epimorphism, and `e = print ∘ parse` is an idempotent partial
endomorphism of `C` whose splitting object is `A`. Its domain of
definition is the parseable subset, and its image is the set of
canonical concrete forms. Stating it in **Set**, with a parenthetical
"(where defined)", is imprecise enough to cause trouble in
mechanization, where `Option` is not silent.

### Idempotence is a corollary, and so is injectivity

Formatter idempotence need not be a separate axiom. Writing
`format : C → Option C` for `format c = (parse c).map print`, the
statement is `(format c).bind format = format c`, since `format` cannot
be composed with itself directly. If `parse c = none` both sides are
`none`; if `parse c = some a` then:

```text
(format c).bind format = format (print a)
                       = (parse (print a)).map print
                       = (some a).map print    by the retraction law
                       = some (print a)
                       = format c
```

Less obviously, the retraction law also **forces `print` to be
injective**: if `print d₁ = print d₂` then
`some d₁ = parse (print d₁) = parse (print d₂) = some d₂`. Both facts
are proved once and generically, as `format_idem` and `print_injective`.

Injectivity is a design constraint on the document type. It
means the document type `D` must contain **no redundant
representations**: if `D` can express the same document two ways — an
unsorted annotation list, duplicate keys, two spellings of a link — then
either the printer distinguishes them in the output (making the concrete
syntax carry noise) or the retraction law is false. Practically:

- annotation collections in `D` must be canonically ordered and
  duplicate-free by construction (a sorted, key-distinct map type rather
  than a `List`), or
- the law must be restated modulo a setoid on `D`, in which case every
  downstream theorem inherits the setoid.

Choose the first. It is cheaper in Lean and it is the choice that makes
`docMH` well defined.

### The laws must be lifted to the annotated level

If `parse` lands in the bare `A`, then every name, comment, link, and
layout choice is necessarily discarded, and a formatter built from that
`parse` cannot preserve them — `format` would *erase* annotations, the
opposite of what a code formatter should do. The architecture therefore
needs a decorated document type `D` and:

```text
parseDoc : C → Option D
printDoc : D → C
erase    : D → A
parse    = Option.map erase ∘ parseDoc
print    = printDoc ∘ trivialDoc
```

with the retraction law stated at the document level,
`parseDoc (printDoc d) = some d`. The bare-level law is then a
corollary — but only given the auxiliary lemma
`Tree.erase (Ast.trivialDoc a) = a`, proved as `Ast.erase_trivialDoc`.

One caution: any data the printer *invents* must either be omitted from
`parseDoc`'s result or be a deterministic function of the tree, or
document-level idempotence fails. The simplest policy is that the
printer never invents annotation content.

## Annotations

### The document type is a μ, not a ν

The document type is the initial algebra of the annotation functor
`X ↦ Ann × F X` over the base functor `F = k + (−)²`:

```text
D = μX. Ann × F X,   D ≅ Ann × (k + D²)
```

This is deliberately *not* the cofree comonad on `F`, which is the
terminal coalgebra `νX. Ann × F X` and whose inhabitants include
infinitely deep annotated trees. That is the right home for execution
traces; individual syntax trees are finite, so annotated syntax lives at
`μ`. Haskell folklore writes an inductive-looking `Cofree` and is
entitled to, because CPO-enriched semantics makes locally continuous
functors algebraically compact, so initial algebras and terminal
coalgebras coincide there (Freyd; Smyth–Plotkin). In `Set` or in Lean
they differ, and the difference is exactly finite versus
possibly-infinite trees.

Uustalu and Vene call this μ-carrier the **cofree recursive comonad** on
`F` and build a recursion scheme from it, contrasting it explicitly with
the scheme obtained from the ordinary cofree comonad. Their carrier is
`D A = A × μ(F(A ⋉ Id))`, with counit `fst` and a comultiplication
defined by the initial-algebra recursor; this is the redecoration map
that relabels each node with the annotated subtree rooted there.

A caution about how much to claim. The word "cofree" here is
load-bearing terminology from that paper, and the relevant universal
apparatus is the theory of **recursive coalgebras** — those `γ : C → F C`
admitting a *unique* coalgebra-to-algebra morphism into every algebra
(Osius; developed by Capretta, Uustalu and Vene) — not cofreeness over
all `F`-coalgebras, which fails, since unfolding an arbitrary coalgebra
can diverge and so cannot land in `μ`. For a mechanized development the
right move is to **state and prove the comonad laws concretely** rather
than lean on the slogan; `Tree.extract_duplicate`,
`Tree.map_extract_duplicate` and `Tree.duplicate_duplicate` are those
laws.

The comultiplication is the structure behind histomorphisms
(course-of-values recursion), which Geb will plausibly want over
annotated syntax. Two facts keep the subrecursive bookkeeping intact: a
histomorphism is implementable as an ordinary catamorphism whose carrier
is the annotated-tree type, and over `ℕ` course-of-values recursion
defines nothing beyond the primitive recursive functions.

Erasure is *not* the comonad counit, which returns the root's `Ann`. It
is the fold induced by the second projection `π₂ : Ann × F X → F X`,
i.e. the fold of the algebra `Ann × F (μF) → μF` sending `(a, x)` to
`in x`, forgetting the annotation at every node.

The free monad enters on the orthogonal axis. The bare AST is `Free F 0`
(the free monad at the initial object: closed terms), while
`Free F V = μX. V + F X` adds variables at the leaves and its bind is
substitution. The
decoration comonad's extend is *redecoration* — attribute-grammar
evaluation — and the two are dual in the sense of Uustalu and Vene's
"The dual of substitution is redecoration". The axes combine
componentwise: `μX. Ann × (V + k + X²)` is annotated open syntax.

### The side-table presentation

```text
D' = Σ (a : A), (Occ a ⇀ Ann)
```

where `Occ a` is the set of occurrence paths valid for `a`, and `⇀`
denotes a partial map with decidable, finite domain. Then
`μX. (Option Ann) × F X ≅ D'` up to the representation of partial maps.
The side-table form has the practical virtue that the core tree is
*literally unchanged* inside the document, which makes separate core and
annotation hashes straightforward; the recursive form is friendlier to
structural recursion in Lean. Implement one, prove the equivalence, and
use whichever is convenient per task. Note that the `printDoc`
injectivity constraint bites hardest here: the partial map must be
represented canonically.

### Wrapper model, environment model, and the occurrence pitfall

A *wrapper* is a document that embeds the core tree, its core hash, and
metadata fields. An *environment* stores the core tree in a
content-addressed store keyed by hash, with a separate namespace mapping
names and comments to hashes. The environment model is Unison's
codebase/namespace split and is the right shape for *definition-level*
names.

It has a pitfall: **content addressing conflates occurrences.** Under a
Merkle hash, every occurrence of a structurally equal subtree *is* the
same value — with a small alphabet this is pervasive (every `leaf 0` in
the entire codebase is one object). A comment keyed by `subtreeMH`
therefore attaches to *every* occurrence of that subtree, everywhere.
That is sometimes wanted (documentation of an idiom) and sometimes
absurd (a remark about *this* operand). The design should support both
key forms:

- `(rootCoreId, path)` — an annotation attached to one occurrence in one
  tree; `path` is meaningful only relative to a root.
- `subtreeMH` — metadata intended for every occurrence of an equal
  subtree.

Paths must be expressed in a fixed, versioned vocabulary, and per the
occurrence characterization above, the normative vocabulary should be
the binary one.

### Lexical comments are not durable

Even when a surface syntax has lexical comments (XML, YAML, EDN; JSON
does not), generic parsers routinely discard them, and canonical forms
differ about them — Canonical XML 1.1 exists in with-comments and
without-comments variants. Anything that must survive formatting,
conversion between syntaxes, or content addressing must be an explicit
annotation *value* in the document model, not a lexical comment.

## Canonicalization: two nested quotients, not one

Calling a canonical form a section of the quotient of byte strings by
"encode the same value" elides the distinction the architecture turns
on. There are **two** relevant
equivalences on the set `C` of byte strings:

```text
c ∼_fmt c'   iff  c and c' denote the same value of the format's
                  own data model  (same JSON value, same CBOR
                  data item, same s-expression)

c ∼_geb c'   iff  parse c = parse c' and both are `some`
```

`∼_geb` is a partial equivalence relation: it relates nothing to an
unparseable string, so it is an equivalence on the parseable subset
`C_ok ⊆ C` only. For any sane implementation `parse` factors as
`decode ∘ formatParse`, so on `C_ok` we have `∼_fmt ⊆ ∼_geb`: the Geb
equivalence is strictly **coarser**.

- Format canonicalizers — JCS, RFC 8949 §4.2, canonical csexp, Canonical
  XML 1.1 — choose a section of `q_fmt : C ↠ C/∼_fmt`.
- `printDoc ∘ parseDoc` chooses a section of `q_geb : C_ok ↠ C_ok/∼_geb`.

These are different jobs. A format canonicalizer will *not* merge two
different-but-legitimate Geb encodings within one format (say a compact
and a tagged JSON encoding); only the Geb-level section does that. And
across formats there is no shared byte-level equivalence at all.

Two consequences, and the second is the architectural pivot:

1. The cross-syntax, permanent identity of a Geb tree must be defined on
   `A` itself.
2. **A concrete syntax does not need a normative canonical form.** What
   it needs is a *deterministic printer*, so that `printDoc` picks one
   representative per document. Format-level canonicalization is needed
   only when one wants a stable address for the *stored bytes*, which is
   a storage concern, discharged by the binary syntax. "The standard
   defines a canonical form" is therefore a real but secondary
   criterion when scoring textual candidates.

Amazon's Ion Hash is the clearest existing endorsement of this split: it
hashes at the data-model level and guarantees the same hash for a value
independent of whether it was written in Ion text or Ion binary.

## Merkle hashing as a catamorphism

This section and the next are specification, not implementation. No hash
function usable from Lean exists yet, so the fold would have no consumer
and is not written; [Roadmap](#roadmap) stage 3 carries it.

A Merkle hash is a catamorphism over the initial algebra with a hash
algebra `h : F(Digest) → Digest`; the unique fold `⦇h⦈ : μF → Digest` is
the content hash.

Structural equality implies hash equality, but not by the fold's
universal property: every function respects equality, so that argument
is vacuous. What the universal property actually gives
is **uniqueness**, hence *compositionality*: the digest of a node is a
function of the digests of its children and nothing else. That is what
licenses incremental recomputation under local edits, subtree-level
deduplication, and structural sharing. The interesting direction — hash
equality implying structural equality — is not a theorem at all; it
holds only under a collision-resistance assumption that lives outside
the kernel.

Injectivity-up-to-collision of the algebra requires:

- distinct domain-separation tags for the leaf and fork cases, and those
  tags must be **equal-length or prefix-free**, or the concatenations
  can themselves collide;
- unambiguous child digests, obtained either by fixing the digest length
  or, as recommended below, by encoding each child digest as a
  self-delimiting multihash; and
- a self-delimiting, injective label encoding (shortest-form unsigned
  LEB128).

The citable precedent is not only git. RFC 6962 §2.1 defines the
Certificate Transparency Merkle tree hash with a `0x00` prefix for
leaves and `0x01` for internal nodes, and states outright that the
domain separation is required for second-preimage resistance; RFC 9162
is its standards-track successor and keeps the prefixes. Git's
`blob`/`tree` prefixes are the same idea with a different alphabet.

Flat versus Merkle: Dhall hashes the *whole* canonical CBOR encoding of
the normal form (one digest per definition); a Merkle fold hashes every
subtree. The Merkle form costs one digest per node but yields
per-subtree addresses, incremental recomputation, and the easiest Lean
proofs, because it is literally a fold. Recommendation: Merkle as the
primary definition, with the whole-block digest arising anyway as the
block CID of the canonical encoding.

## Structural content-addressing specification

Let `H` be a cryptographic hash carrying its multicodec identifier
(SHA3-256, multicodec `0x16`, to start; SHA3-512 is `0x14`). Let
`uvarint` be shortest-form unsigned LEB128, `‖` byte concatenation, and
let the tags be distinct ASCII strings **of equal length**:

```text
tagLeaf = "geb/v1/core/leaf"   (16 bytes)
tagFork = "geb/v1/core/fork"   (16 bytes)
tagRoot = "geb/v1/core/root"   (16 bytes)
tagDoc  = "geb/v1/docs/root"   (16 bytes)
```

Write `MH(H, bs)` for the pair `⟨code(H), H(bs)⟩` and `enc(m)` for its
multihash serialization `uvarint(code) ‖ uvarint(len) ‖ digest`. Then:

```text
subtreeMH (leaf i)   = MH(H, tagLeaf ‖ uvarint i)
subtreeMH (fork l r) = MH(H, tagFork ‖ enc(subtreeMH l)
                                     ‖ enc(subtreeMH r))

coreMH (k, a)        = MH(H, tagRoot ‖ uvarint k ‖ enc(subtreeMH a))

docMH (k, d)         = MH(H, tagDoc ‖ enc(coreMH (k, erase d))
                                    ‖ annCanon d)
```

Notes:

1. **Multihash all the way down, unlike Unison.** So far as the public
   documentation shows, Unison stores a bare digest: a hash is "a
   512-bit SHA3 digest of a term or a type's internal structure,
   excluding all names", rendered in base32Hex, with no algorithm
   identifier alongside it and no documented hash-version concept. That
   is a hash-agility liability. Encoding each child
   digest as a multihash costs two varints per node and buys: a
   self-describing algorithm, a migration path, and — because multihash
   is length-prefixed and therefore self-delimiting — the concatenation
   injectivity the fold needs, *without* a fixed-length side condition.
   With SHA3-256 both varints are single bytes, so the cost is two bytes
   per child digest. Every argument to `H` above is uniquely parseable:
   a 16-byte tag, then self-delimiting fields, so the leaf and fork
   preimage sets are disjoint and each is injective in its arguments.
2. **`k` is part of the root identity.** The same numeric tree read over
   different leaf alphabets is a different object. Subtree hashes
   deliberately omit `k` so that equal subtrees share addresses across
   alphabets containing them; if that sharing is unwanted, move `k` into
   the leaf tag instead — decide once, version it.
3. **Two-level identity.** `coreMH` is the semantic identity: renaming,
   commenting, or re-linking never changes it. `docMH` identifies the
   exact decorated artifact. `annCanon` is a canonical serialization of
   the annotation table, sorted by occurrence key and encoded in
   deterministic CBOR. It occupies the final position, so no length
   prefix is needed: `tagDoc` is a fixed 16 bytes and `enc(coreMH …)` is
   self-delimiting, so the remainder is unambiguously `annCanon`. It
   must itself be injective on annotation
   tables — which is exactly the `printDoc` injectivity constraint
   again, applied to the annotation component.
4. **Version everything that feeds a hash** — tag strings, `uvarint`,
   `annCanon`, the binary/rose bijection for paths. Dhall's experience
   is the cautionary tale: dhall-lang issue #242 records that a
   β-normalization change (`[] : Optional Natural` normalizing to itself
   under standard 1.0 but to `None Natural` under 2.0) silently
   perturbed semantic hashes, prompting the proposal to version
   normalization itself.
5. **Collision policy.** Where adversarial correctness matters, hash
   equality is evidence, not proof: before permanently merging two store
   entries, fetch both and compare canonical ASTs. In Lean, theorems are
   stated for structural equality; `coreMH` is injective only modulo a
   collision-resistance assumption that stays outside the kernel.
6. **Addressing wrapper.** In **binary**, a CIDv1 is
   `uvarint(version) ‖ uvarint(multicodec) ‖ multihash`. Multibase is
   prepended only when the binary CID is rendered as a **string**.
   Blocks of canonical CBOR bytes get ordinary CIDs; `coreMH` itself,
   not being the hash of a standard block, travels either as a small
   IPLD block naming the scheme and digest or as a Geb-versioned
   identifier. Bundles ship as CARv1 archives. Note also that DAG-CBOR
   embeds a CID under tag 42 as a byte string prefixed with the identity
   multibase byte `0x00`.

## Format-by-format evaluation

### Canonical S-expressions (RFC 9804)

Published June 2025 as RFC 9804, *Simple Public Key Infrastructure
(SPKI) S-Expressions*, by Rivest and Eastlake. Status is
**Informational** on the IETF stream — not Standards Track, which is
worth knowing before describing csexp as "standardized" without
qualification. It specifies a **canonical** encoding (length-prefixed
atoms, parenthesized lists, no whitespace, one encoding per value,
designed for hashing and signing), an **advanced** human-readable
encoding, a basic/**transport** encoding, and an in-memory
representation; the base-64 form (`{…}`) wraps the canonical bytes.

The canonical grammar is two productions, pulling in two more by
reference:

```abnf
c-sexp   = c-string / ("(" *c-sexp ")")
c-string = [ "[" verbatim "]" ] verbatim
verbatim = decimal ":" *OCTET
decimal  = %x30 / (%x31-39 *DIGIT)
```

The advanced grammar is not tiny. It adds
quoted strings with C-style escapes and an optional length prefix,
hexadecimal `#…#` atoms, base-64 `|…|` atoms, display hints, whitespace
rules, and:

```abnf
token       = (ALPHA / simple-punc) *(ALPHA / DIGIT / simple-punc)
simple-punc = "-" / "." / "/" / "_" / ":" / "*" / "+" / "="
```

Two consequences constrain how the examples may be written:

- **`@` is not a token character** — it is not even in RFC 9804 §3's
  permitted character set except inside verbatim and quoted-string
  encodings. So `(@ (name operator))` is ill-formed. Use a token that
  starts with a legal punctuation character; this report adopts `*ann`.
- **A token may not begin with a digit**, because a leading digit starts
  a length prefix. So `(leaf 0)` is ill-formed. Labels must be written
  as quoted strings `(leaf "0")` or verbatim atoms `(leaf 1:0)`.

Geb profile decisions, which must be fixed for `printDoc` to be
injective:

- A leaf label is the **shortest decimal ASCII** representation, no
  leading zeros, `"0"` for zero. That binds the printer. The decoder is
  deliberately laxer — `Csexp.digitsVal` accepts leading zeros and the
  empty atom, and `Csexp.readNat` accepts a leading zero in a length
  prefix — since the retraction law constrains only the composite. A
  profile that rejects non-canonical spellings on input is a separate
  obligation, and is not discharged here.
- `printDoc` emits a fixed sublanguage of the advanced form (quoted
  strings only, one fixed indentation discipline, no display hints);
  `parseDoc` accepts the full advanced form. The retraction law
  constrains only the composite, so this asymmetry is legitimate and is
  what makes the formatter useful.
- Any list element whose head atom is `*ann` is an annotation and is
  skipped by the core decoder.

Tooling, stated honestly: implementations exist and are real. RFC 9804
§1.1 names two — GNU Libgcrypt (used by GnuPG) and Ribose's RNP, whose
`sexpp` is C++ — and refers to Appendix A for the rest. Appendix A lists
seven in all: those two, plus implementations in C, Ruby and OCaml, one
for Inferno, and the Small Fast X-Expression Library. It lists no Python
code. There is no maintained, first-class canonical-S-expression library
across
Python/JavaScript/Rust/Go/Java. The ecosystem is roughly one to two
orders of magnitude smaller than JSON's, CBOR's, or bencode's, and it is
concentrated in the SPKI/PGP niche. "Multiple open-source
implementations exist" is literally true of csexp and misleading as a
tooling claim.

### CBOR (RFC 8949 §4.2) and DAG-CBOR

RFC 8949 §4.2.1 defines the core deterministic encoding: shortest-form
integer and length arguments, definite lengths, and map keys **sorted in
the bytewise lexicographic order of their deterministic encodings**.
§4.2.3 explicitly records that this differs from the ordering suggested
by RFC 7049 §3.9, which is retained only as an optional "length-first"
variant.

**The correction, and it is not the one it first appears to be.**
DAG-CBOR's specification says to use the §4.2 rules *except* for map key
ordering, which follows RFC 7049 §3.9, "so the keys are sorted by length
first". Asserting §4.2 ordering for DAG-CBOR while warning against the
length-first order reads as though the two were in conflict. They are
not, for DAG-CBOR:

> For text-string keys, RFC 8949 §4.2's bytewise order on the
> *encoded* key coincides with RFC 7049 §3.9's length-first order.

The reason is that a text-string head is monotone in the string's
length: lengths 0–23 encode as the single bytes `0x60`–`0x77`, lengths
24–255 as `0x78 nn`, and so on, so comparing encoded keys bytewise
compares length first and content second. DAG-CBOR's own wording says
as much — keys sort "in (byte-wise) lexical order, including their
major type 3 and length", *therefore* by length first. The two rules can
only diverge on maps that mix major types (integer key `1000` encodes as
`19 03e8`, string key `"z"` as `61 7a`; bytewise puts the integer first,
length-first puts the string first), and DAG-CBOR forbids non-string
keys, so for DAG-CBOR the two rules cannot diverge at all.

So that warning is misleading rather than false, and the practical
divergence is elsewhere: **CBOR sorts the encoded key, JSON
sorts the raw key.** The keys `k, ann, root, format` sort as
`k, ann, root, format` under both CBOR rules and as
`ann, format, k, root` under JCS and DAG-JSON: the two orders differ
whenever two keys differ in length.

DAG-CBOR's other constraints, all confirmed: map keys must be strings;
only tag 42 (CID) is permitted and it must be encoded as `0xd82a`, so
the bignum tags 2 and 3 are excluded along with everything else; floats
are always 64-bit, with NaN, ±Infinity, and −0.0 forbidden; and the
codec assumes integers fit the 64-bit signed range. That last bound is
documented as a **codec and library limitation**, not as a Data Model
type definition.

**Design resolution.** Take RFC 8949 §4.2 deterministic CBOR as the
normative Geb binary syntax, matching the IETF standard, the CDE draft,
and the verified implementation. Then choose **map-free encodings** —
positional arrays instead of string-keyed maps. A CBOR item containing
no maps is simultaneously valid §4.2 deterministic CBOR and valid
DAG-CBOR, **with identical bytes**, because the only divergence is key
ordering. This removes the hazard rather than documenting it, and it
costs only the self-description that map keys would have provided, which
the format tag in position 0 restores.

Verified prior art, and it exists for CBOR and for no other candidate
format: EverCBOR, part of EverParse, implements RFC 8949 §4.2
deterministic CBOR in F* with proofs of memory safety, arithmetic
safety, functional correctness, non-ambiguity, and non-malleability of
the deterministic fragment, extracting to C and safe Rust; EverCDDL adds
a CDDL frontend. What it offers a Lean development is bounded, and
[Evaluating the candidates](#evaluating-the-candidates) states the
bound: the proof does not cross into Lean, the extracted C does.

### JSON, JCS (RFC 8785), DAG-JSON

Plain JSON bytes are non-canonical (whitespace, key order, number
spelling, escaping). RFC 8785 (JCS; Independent Submission,
Informational, June 2020) canonicalizes an I-JSON value; DAG-JSON is
IPLD's canonicalized JSON codec. Both make a JSON *document* hashable;
neither merges distinct JSON encodings of the same tree.

A hazard that is easily missed. **The relevant orderings are mutually
different, and not only outside ASCII:**

- RFC 8785 §3.2.3 sorts property names as arrays of **UTF-16 code
  units** compared as unsigned integers — the *raw* name, with no
  length prefix.
- DAG-JSON sorts object keys by their **raw UTF-8 bytes**, i.e.
  code-point order.
- CBOR (both §4.2 and DAG-CBOR) sorts the **encoded** key, hence by
  length first.

The JSON pair agree on ASCII and disagree exactly on the surrogate
range: `"\uFFFF"` precedes `"\U00010000"` in code-point order but
follows it in UTF-16 order, since the latter begins with code unit
`0xD800`. Both disagree with CBOR whenever two keys differ in length,
ASCII or not. Two mitigations, and Geb should adopt both:

- **Restrict all object keys to 7-bit ASCII**, which makes JCS and
  DAG-JSON agree. RFC 8785 itself notes that names are rarely outside
  7-bit ASCII and that ASCII-only names may be sorted in UTF-8 without
  conversion and remain JCS-conformant.
- **Avoid maps in the CBOR encoding altogether** (see above), so that no
  CBOR key order is ever computed and the JSON/CBOR mismatch cannot
  arise.

Other practical notes: JSON has no comments, so annotations must be
explicit fields; I-JSON caps exactly-interchangeable integers at
`2⁵³ − 1`, so labels beyond that must be decimal strings; DAG-JSON
reserves the object key `"/"` for links and byte strings, so Geb must
never use `"/"` as a key. Lean fit is excellent (`Lean.Json` in core).
The most useful role is DAG-JSON as a *debugging projection* of the
CBOR storage —

```text
DAG-JSON bytes ─parse─┐
                      ├─→ IPLD value ─decode─→ D ─erase─→ A
DAG-CBOR bytes ─parse─┘
```

— the same data-model value rendered readably for inspection and
compactly for storage. Note that this is a shared *value*, not a shared
byte layout: the two codecs order keys differently, so one cannot be
transliterated into the other.

A point in JSON's favour: the **core**
encoding `[0, [2, 1]]` uses only arrays and small non-negative integers.
A verified parser for that profile needs no string escapes, no floats,
and no Unicode handling, and is about as small as a canonical csexp
parser. JSON's verification cost is concentrated entirely in the
*annotated* document, where strings appear — and csexp's quoted-string
form carries a comparable cost there.

Against full JSON: **no fully verified RFC 8259 parser or RFC 8785
canonicalizer is known to exist in any proof assistant.** The nearest
artifacts are Isabelle's Nano JSON entry (explicitly not fully
compliant, with no round-trip proofs), Coq's Vermillion (an LL(1) parser
generator using JSON only as a benchmark), and a Lean project proving
serialization-to-schema validity in one direction. So JSON's enormous
*implementation* ecosystem does not translate into any *verification*
leverage.

This does not separate JSON from canonical S-expressions, for which no
verified parser exists either; both are written here from nothing. It
bears on the *full* JSON document — escaping, Unicode, floats — which is
why the roadmap takes the core profile, whose parser needs none of the
three, and leaves the rest to the annotated stage.

### Protocol Buffers — rejected for any hash-bearing role

Google's own documentation page "Proto Serialization Is Not Canonical"
states that protobuf serialization is not and cannot be canonical, that
deterministic serialization is not canonical and can change when the
schema changes, the application changes, build flags change, or the
library is updated, and that hashes of serialized protos are therefore
fragile and not stable across time or space. Deterministic ≠ canonical:
the mode stabilizes output within one binary, which is exactly not the
property content addressing needs. ProtoJSON is not canonical either —
field-name casing, default-field emission, and whitespace are all
configurable. Protobuf remains fine as a *transport or cache* format
whose decoded trees are re-hashed structurally; it must not define
identity.

### Cap'n Proto — best typed-binary candidate, not chosen

Unlike protobuf, Cap'n Proto's encoding specification *does* define a
canonical form intended for hashing and signing: single segment, with
the segment table excluded from the hashed bytes, and trailing
zero-valued words truncated from struct data and pointer sections.
Canonicalization operations exist in the C++, Go, and Haskell
implementations. The spec's own motivation for zero-truncation is that
adding a new field must not change the canonical encoding of messages
that do not set it, so that sensitivity is partially designed away.
The residual caveat is narrower and still real: the schema
documentation lists backwards-compatible schema changes that
*may* alter a canonical encoding, so schema-evolution discipline becomes
part of the identity specification. Together with a much larger encoding
surface to verify (segments, pointers, far pointers, packing) and no
CID/IPLD ecosystem, that keeps it out of the bootstrap set. If Geb later
wants generated typed APIs and high-throughput transport, Cap'n Proto is
the right typed-binary choice — with identity still on the structural
hash.

### XML with C14N — the strongest "genuinely different" alternative

XML is not another spelling of the JSON-ish data model: it exercises
ordered child elements *and* attributes, namespaces, IDs, a different
parser family, mature schema languages (RELAX NG, XSD), XLink for typed
links, and Canonical XML 1.1 for document hashing.

```xml
<geb:tree xmlns:geb="https://example.org/geb/tree/v1" k="3">
  <geb:fork>
    <geb:leaf label="0"/>
    <geb:fork>
      <geb:leaf label="2"/>
      <geb:leaf label="1"/>
    </geb:fork>
  </geb:fork>
</geb:tree>
```

with annotations as explicit elements, never XML comments:

```xml
<geb:annotation path="RL">
  <geb:name>operator</geb:name>
  <geb:link href="https://example.org/reference"/>
</geb:annotation>
```

Why it still loses a place in the bootstrap set: this project must
produce
verified parse/print for each syntax, and XML-with-namespaces plus C14N
1.1 is a large and subtle target — RFC 8785's own introduction cites the
difficulty of getting XML signatures to validate, attributing it to
divergent readings of the canonicalization rules, and lists JSON's lack
of a namespace concept as the reason JCS should not repeat it.
Canonical XML 1.1 additionally comes in with-comments and
without-comments variants, which is one more axis to pin down. XML is
the right third-or-later syntax if maximal annotation-surface diversity
becomes a goal in itself.

### WebAssembly text format (WAT)

WAT is s-expression-shaped, with mature parsers (wabt, wasm-tools), and
its custom-annotation syntax `(@id …)` is no longer merely a proposal —
it is in the core specification appendix, with the lexical rule that no
space may appear between the opening parenthesis and the annotation id.
But WAT is the concrete syntax of one specific language, not a general
data-format standard: adopting it means borrowing lexical conventions
while inheriting none of the spec, and its folded/unfolded instruction
forms and rich abbreviations make it deliberately non-canonical. If Wasm
interop ever matters, revisit.

### EDN

EDN fits the rose view directly — lists, vectors, maps, symbols,
keywords, tagged elements, and `;` comments:

```clojure
#geb/node [0
  #geb/node [2]
  #geb/node [1]]
```

Against it: no broadly adopted canonical byte serialization, a smaller
cross-language ecosystem than JSON/XML/CBOR, no Lean tooling, and
semicolon comments are lexical and hence non-durable. A pleasant later
frontend; not a bootstrap identity format.

### The remainder

- **Bencode**: canonical by construction — length-prefixed strings,
  integers with no leading zeros and no `-0`, dictionary keys sorted as
  raw strings — and as small as canonical csexp, with a *broader*
  library ecosystem. BitTorrent v1 infohashes are SHA-1 over the
  bencoded info dictionary; BEP 52 (v2) moved to SHA2-256. It is the
  strongest runner-up on the "smallest verified parser" axis and is
  arguably ahead of csexp on tooling; it loses only on human
  readability, since it has no readable form at all.
- **ASN.1 DER**: the classic canonical-encoding-for-signing precedent,
  genuinely canonical, but a large and edge-case-rich TLV system.
  Verified prior art exists — ASN1★ (Ni, Delignat-Lavaud, Fournet,
  Ramananandro, Swamy, CPP 2023) gives the first mechanized
  non-malleability proof for DER parsing, built on EverParse — so it is
  feasible, just unjustified for a two-shape AST.
- **YAML**: enormous surface, no standard canonicalization; reject.
- **TOML**: config tables, not recursive trees; reject.
- **MessagePack**: CBOR's cousin without an equally crisp normative
  deterministic profile; prefer CBOR.
- **Amazon Ion**: large grammar and no Lean tooling, but its companion
  **Ion Hash** specification is directly relevant prior art, since it
  hashes at the data-model level and is invariant across Ion's text and
  binary encodings.

## Evaluating the candidates

Scoring the serious candidates, where "parser cost" is the cost of a
*verified* parser — the binding constraint here — and "tooling" is
breadth of maintained third-party libraries:

| Format | Parser cost | Tooling | Readable | Canonical form |
| --- | --- | --- | --- | --- |
| csexp canonical | very low | thin | no | normative |
| csexp advanced | medium | thin | yes | n/a |
| CBOR §4.2 | low | broad | no | normative |
| JSON core profile | very low | very broad | yes | via JCS |
| JSON annotated | medium | very broad | yes | via JCS |
| bencode | very low | broad | no | by construction |
| XML + C14N 1.1 | high | very broad | yes | normative |

Three findings bear on the choice, and they do not point the same way:

1. Because identity lives on `A`, a textual syntax needs a
   deterministic printer, not a normative canonical form. This
   removes csexp's headline advantage.
2. csexp's tooling is thin, and its advanced form is not small.
3. No verified JSON parser or canonicalizer is known to exist in any
   proof assistant, whereas a verified deterministic-CBOR
   implementation with non-malleability proofs does.

The third finding is narrower than it looks. EverCBOR's *proof* is an
F* artifact and does not cross into a Lean development. Its extracted C
does, through `@[extern]`, as an unverified differential-testing oracle,
and its methodology transfers. That is worth having — it is the route
[Ecosystem notes](#ecosystem-notes) proposes for the hash as well — and
it is not enough to order the syntaxes by.

### The bootstrap set

Data-model diversity is the purpose of writing more than one syntax:
the exercise validates that the architecture is syntax-independent.
csexp's data model is nested lists of byte strings — no maps, no
numbers, no scalar types — which stresses the abstraction further than
a second array-and-map format would. A DAG-JSON and DAG-CBOR pair
would share the identical IPLD data model and test it least.

Two considerations constrain the order.

- Canonical csexp has no readable form. Readability lives in the
  advanced form, which is a second and larger parser. A bootstrap
  built on the canonical form alone gains nothing from the
  readability argument until that second parser exists, so
  readability cannot rank canonical csexp above formats that lack it.
- The JSON *core* profile — `[0, [2, 1]]`, arrays and small
  non-negative integers — needs no string escapes, no floats and no
  Unicode handling. It is a different data model from csexp's at the
  lowest available verified-parser cost, and `Lean.Json` supplies an
  unverified oracle for differential testing immediately.

The order adopted is canonical S-expressions, then the JSON core
profile, then deterministic CBOR.

Canonical csexp earns a place in the set: among the bootstrap-eligible
candidates its data model is the one that shares least with the others,
so the pair {csexp, JSON core} stresses syntax independence more than
any pair drawn from the array-and-map formats would. That is an argument
for inclusion and not for sequence — syntax independence is validated by
the pair, and swapping the two yields the same pair. On sequence the two
are close: both are "very low" parser cost, and JSON core has the
tie-breaker, `Lean.Json` as an immediate differential-testing oracle.
The order was settled by writing csexp first; stage 1a is done, so the
question is no longer open. Had it been reopened before implementation,
JSON core first would have been the better call.

CBOR is not dropped: it shares JSON's data model, so once the JSON core
is proved its incremental cost is the byte-level integer encoding alone,
and it carries the storage and interchange role. Ordering it third costs
nothing that validating syntax independence needs.

What this ordering costs, stated plainly: outside the Geb
implementation, nobody's toolchain reads Geb csexp without new code.
That is acceptable for a bootstrap format and unacceptable for an
interchange format, which is why JSON and then CBOR carry the
interchange role.

**Switch thresholds**, which bear on the syntaxes not yet written;
canonical S-expressions are implemented, so none of them displaces it.
Promote CBOR ahead of the JSON core profile if a storage format is
needed before a second validation of syntax independence. Add the csexp
advanced form ahead of both if the textual form is read and written by
hand often enough for the canonical form's unreadability to cost more
than the second parser. Add bencode if a second
canonical-by-construction format is wanted: it is smaller to verify and
better tooled than canonical csexp, and it loses only on human
readability, which the canonical form does not supply either.

## Prior art on content-addressed code

**Unison** (v1.0, 25 November 2025). Definitions are identified by a
hash of their syntax tree; names are metadata excluded from the hash, so
renaming is a non-breaking metadata edit. The documentation describes a
hash as a 512-bit SHA3 digest of a term's or type's internal structure,
excluding all names, rendered in base32Hex, and permits abbreviating a
hash literal to an unambiguous prefix. Mechanics worth copying:

- references to dependencies are replaced by the dependencies' hashes
  before hashing, so identity is closed under the dependency graph;
- bound variables are replaced by positional references — Unison hashes
  abstract binding trees, making the hash alpha-invariant;
- mutually recursive groups are hashed as a *cycle*: each member gets
  `#x.n` where `x` is the cycle's hash and `n` an index, with the cycle
  put in canonical order by sorting members by their individual hashes
  computed with the cycle edges removed;
- data constructors hash as `#x#c` (type hash, constructor index);
  built-ins as `##Name`.

One thing **not** to copy: the published scheme stores a bare digest
with no algorithm identifier and no documented hash-version concept.
Geb should use multihash and explicit versioning throughout, as
specified above.

Geb's current name-free, binder-free AST needs none of the ABT
machinery yet; the cycle-order trick and ABTs are what to adopt when
references and binders arrive. Whether identity then remains purely
syntactic or quotients by α (or more) is a language-semantics decision
and must be made in the Geb specification, not delegated to a
serialization format.

**Dhall.** Semantic integrity checks resolve imports, β-normalize,
α-normalize, encode in the standard binary CBOR form, SHA-256 the bytes,
and prefix the digest with its algorithm for agility. Dhall is the
flat-hash design point against which the Merkle choice above is argued;
issue #242 supplies the "version everything feeding the hash" lesson.

**git, Nix, IPLD.** git: a Merkle store hashing
`SHA1(type ‖ " " ‖ size ‖ "\0" ‖ content)` with tree entries sorted by
name — the domain-separation precedent. Nix distinguishes
input-addressed from content-addressed store paths; Geb wants the
content-addressed model. IPLD supplies CID/multihash/multibase and the
DAG-CBOR/DAG-JSON codecs, plus CARv1 archives.

**Certificate Transparency.** RFC 6962 §2.1 is the cleanest normative
statement of domain-separated Merkle hashing: `0x00` before a leaf,
`0x01` before an internal node, with the stated rationale of
second-preimage resistance. RFC 9162 is its standards-track successor.

**Hash-consing.** Conchon and Filliâtre, "Type-Safe Modular
Hash-Consing" (ML '06), plus Braibant, Jourdan and Monniaux,
"Implementing hash-consed structures in Coq" (ITP 2013): the in-memory
dual of content addressing, where the content hash is a persistent
hash-cons key. LeanSerde's structural deduplication is an instance.

**Scrapscript**: a small, pure, content-addressable language whose own
summary is that all expressions are content-addressible "scraps", all
programs are data, and all programs are platformed — a lighter-weight
design reference alongside Unison.

## One tree, every recommended encoding

Running example, with `k = 3`:

```text
fork (leaf 0) (fork (leaf 2) (leaf 1))
```

csexp advanced (human) form. Note the quoted labels: bare `0` is not a
legal token.

```text
(geb-doc/v1 "3"
  (fork (leaf "0")
        (fork (leaf "2") (leaf "1"))))
```

csexp canonical form — the hashing target for the csexp *document*,
67 bytes. Note that `geb-doc/v1` is a legal token: it starts with a
letter, and `-` and `/` are `simple-punc`.

```text
(10:geb-doc/v11:3(4:fork(4:leaf1:0)(4:fork(4:leaf1:2)(4:leaf1:1))))
```

csexp annotated, advanced form; `(*ann …)` elements are annotations and
erasure drops them:

```text
(geb-doc/v1 "3"
  (fork
    (leaf "0")
    (fork (leaf "2" (*ann (name "operator"))) (leaf "1"))
    (*ann (name "example")
          (doc "the root expression")
          (link "https://example.org/spec"))))
```

JSON, compact core encoding (leaf = integer, fork = 2-element array):

```json
[0, [2, 1]]
```

JSON, annotated document. Keys are ASCII only, so the JCS and DAG-JSON
orders coincide; the CBOR encoding below is map-free, so no CBOR key
order is ever computed:

```json
{
  "format": "geb-doc/v1",
  "k": 3,
  "root": [0, [2, 1]],
  "annotations": [
    { "path": "",
      "name": "example",
      "doc": "the root expression",
      "links": ["https://example.org/spec"] },
    { "path": "RL",
      "name": "operator" }
  ]
}
```

This is a *different document* from the compact core with a different
JCS hash, and the same `coreMH`. That is the whole architecture in one
example.

CBOR core, diagnostic notation `[0, [2, 1]]`, canonical bytes:

```text
82 00 82 02 01
```

Five bytes: `82` array(2), `00` = 0, `82` array(2), `02` = 2, `01` = 1 —
definite lengths and shortest-form integers, as RFC 8949 §4.2 requires.

CBOR annotated document, **map-free** so that the §4.2 and DAG-CBOR
encodings are byte-identical. The shape is
`[format, k, root, annotations]` with each annotation
`[path, name, doc, links]`, writing `null` for an absent scalar field
and `[]` for absent `links`, as `Ann.links` defaults:

```text
84 6a 67 65 62 2d 64 6f 63 2f 76 31 03 82 00 82 02 01 82 84
60 67 65 78 61 6d 70 6c 65 73 74 68 65 20 72 6f 6f 74 20 65
78 70 72 65 73 73 69 6f 6e 81 78 18 68 74 74 70 73 3a 2f 2f
65 78 61 6d 70 6c 65 2e 6f 72 67 2f 73 70 65 63 84 62 52 4c
68 6f 70 65 72 61 74 6f 72 f6 80
```

Ninety-one bytes. The block CID of these bytes is the storage address;
`coreMH` of the tree is the semantic identity.

## Local verification

The development is
[Geb/Internal/ConcreteSyntax.lean](../Geb/Internal/ConcreteSyntax.lean),
806 lines and 54 theorems, with 123 lines of tests in
[GebTests/Internal/ConcreteSyntax.lean](../GebTests/Internal/ConcreteSyntax.lean).
It builds under the toolchain pinned in `lean-toolchain` with
`autoImplicit` and `relaxedAutoImplicit` false and contains no `sorry`.
Its one import is
[Geb/Mathlib/Data/W/Basic.lean](../Geb/Mathlib/Data/W/Basic.lean), and
through it `Mathlib.Data.W.Basic` and
[Geb/Mathlib/Data/FinEnum.lean](../Geb/Mathlib/Data/FinEnum.lean), which
supplies the choice-free decidability instances fact 3 below relies on.

Four facts constrain how it is written.

1. `Ast`, `Tree` and `Rose` are W-types, and every recursion runs
   through `WType.elim`, `WType.para` or a recursor application.
   [docs/rules/lean-coding.md](rules/lean-coding.md) § Recursion and
   induction through recursors requires it: no self-referential
   `inductive`, no self-calling `def`, no `induction` tactic. The
   parser's fuel and the decimal digits are therefore written as
   `Nat.rec` and `List.rec` applications rather than through the
   equation compiler.
2. mathlib's `Nat.digits` depends on `Classical.choice`, which
   [CONTRIBUTING.md](../CONTRIBUTING.md) § Constructive-only forbids. It
   does have a native implementation and does run in the interpreter;
   the choice dependency alone is what rules it out. The decimal
   encoding is written out instead — `digitsLE`, `ofLE`, and the round
   trip `ofLE_digitsLE`.
3. mathlib's `FinEnum` instances for `Fin n` and `Empty` are built
   through `FinEnum.ofList`, whose proof obligations depend on
   `Classical.choice`. `finEnumFin` and `finEnumEmpty` name choice-free
   constructions in their place, and the arity instances are defined
   from those, so decidable equality on each tree type stays
   choice-free.
4. Core's `String.toList` and `String.data` depend on
   `Classical.choice`, so the tests build their inputs as `List Char`.
   `String.ofList` does not, so the printer's output is still compared
   against a string literal.

The fuel measure is `Ast.size`, the node count, named for its return
value as [docs/rules/lean-coding.md](rules/lean-coding.md) § Naming
conventions requires. Every bound on it is discharged by `omega`, per
that file's § Constructive-only rule on `Fin` and `Nat` arithmetic.

The implemented wire form is header-free and carries the bare tree
alone: `Csexp.print` emits neither the `geb-doc/v1` header nor the
alphabet size that
[One tree, every recommended encoding](#one-tree-every-recommended-encoding)
shows, both of which belong to the document level that stage 2 reaches.
The tests pin the spelling, and for the three-node tree over `Fin 3` it
is `(4:fork(4:leaf1:0)(4:fork(4:leaf1:1)(4:leaf1:2)))`.

Axiom dependencies, from `#print axioms` over all 54 theorems:

| Theorems | Axioms |
| --- | --- |
| 13, among them `Tree.map_mk`, `print_injective`, `Csexp.charDigit_digitChar` | none |
| 13, among them `Ast.toRose_fork`, `format_idem`, `rosePathToBin_last` | `propext` |
| 6, among them `Tree.map_extract_duplicate`, `Ast.erase_trivialDoc` | `Quot.sound` |
| the remaining 22, among them `Csexp.parse_print` | `propext`, `Quot.sound` |

No declaration depends on `Classical.choice`, and `lake lint` enforces
that through `GebMeta.detectNonstandardAxiom`.

The theorems that carry the architecture:

- `Tree.extract_duplicate`, `Tree.map_extract_duplicate` and
  `Tree.duplicate_duplicate` are the three comonad laws, and
  `Tree.map_id` and `Tree.map_map` the two functor laws they presuppose.
  They justify calling `μX. Ann × F X` a comonad without appealing to
  the cofree-recursive-comonad terminology.
- `Ast.ofRose_toRose` and `Ast.toRose_ofRose` are the rose/binary
  bijection.
- `rosePathToBin_last` bounds the image of the rose-to-binary path map.
  See
  [Which occurrences the rose presentation can name](#which-occurrences-the-rose-presentation-can-name)
  for what it does and does not establish.
- `Ast.erase_trivialDoc` says that decorating every node with the empty
  annotation and then erasing is the identity. It is what will make a
  bare-level round-trip law a corollary of the document-level one, once
  stage 2 states that law.
- `format_idem` and `print_injective` are the two corollaries of the
  retraction law, proved once and generically, so that each concrete
  syntax has exactly one obligation left to discharge: its own
  retraction.
- `Csexp.parse_print` discharges that obligation for the canonical
  S-expression syntax on the bare tree; `Csexp.format_idem` and
  `Csexp.print_injective` instantiate the two corollaries at it.

Two facts about the encoding, for anyone extending the development:

1. `simp` and `rw` match at reducible transparency, so an arity family
   used as a W-type index is an `abbrev`. Left as a plain `def`, a child
   function whose type reads `Rose.Arity (i, n) → _` in a goal will not
   unify with a lemma stating `Fin n → _`, definitional equality
   notwithstanding.
2. `WType.para` supplies `Tree.duplicate` with no new recursion:
   redecorating each node with its own subtree is a paramorphism.
   `Tree.map` and `Tree.erase` need less than that — each changes a
   node's shape and not its children, so each is a morphism of
   polynomial functors.

Remaining proof obligations, in dependency order: the retraction law for
a second syntax; the cross-syntax agreement theorem; the lift of every
syntax from `Ast` to `Doc`; injectivity of the annotation
canonicalization `annCanon`, which
[Structural content-addressing specification](#structural-content-addressing-specification)
specifies and no module defines; and the equivalence of the recursive
and side-table document presentations.

## Ecosystem notes

- `Lean.Json` is in core; its object case is
  `Std.TreeMap.Raw String Json`, so keys sit sorted by construction.
  That is incidental, not RFC 8785 conformance: the sort is by Lean's
  `String` comparison, i.e. code-point order, which agrees with JCS's
  UTF-16 order only on ASCII keys. Number and escape canonicalization
  still need an explicit verified pass. The core parser
  (`Lean.Data.Json.Parser`, built on `Std.Internal.Parsec`) contains
  `partial def`s, so the verified pipeline needs its own total parser.
- No Lean 4 package exists for CBOR, canonical S-expressions, bencode,
  or multihash/CID. `LeanSerde` (v0.2.0, MIT, updated 4 May 2026) emits
  CBOR and performs structural deduplication via a graph format with
  `{"ref": n}` back-references; it is a useful unverified reference
  implementation, not a conformance target.
- Cryptographic hashing is the weakest link. `@gdncc/cryptography`
  implements SHA3-224/256/384/512 and SHAKE128/256 in pure Lean 4 and
  passes the NIST test vectors, but its own documentation says it must
  not be used for cryptographic applications; the accompanying write-up
  is Doussot, ePrint 2024/1880. There is no pure-Lean SHA-2 at all. The
  realistic production route is FFI: `joehendrix/lean-crypto` already
  links OpenSSL and libkeccak, and Lean's `@[extern]` makes binding
  OpenSSL, libsodium, or BLAKE3 straightforward. This is why the hash
  is a parameter in
  [Structural content-addressing specification](#structural-content-addressing-specification)
  rather than a fixed function: the fold's theorems will hold for any
  `H`, and the choice of `H` is a deployment decision.
- Verified-parsing leverage: EverCBOR and EverCDDL (F*, RFC 8949 §4.2,
  with non-malleability proofs) as a differential-testing oracle and as
  methodology; ASN1★ for how a non-malleability argument is structured;
  Narcissus (Coq) for derivation methodology. Lean parser-combinator
  options: `Std.Internal.Parsec` in core Std — not Batteries; it moved
  from `Lean.Data.Parsec` in v4.12.0 and now parses `ByteArray` as well
  as `String` — plus `fgdorais/lean4-parser`,
  `argumentcomputer/Megaparsec.lean`, and `tydeu/lean4-partax`.
- `cslib` is `leanprover/cslib`, lead maintainer Fabrizio Montesi. Its
  mature content is labelled transition systems and
  bisimulation/simulation/trace equivalence, plus CCS and typed lambda
  calculi; automata theory is a stated pillar still being ported in. It
  is relevant to Geb's *semantics*, not to its wire formats — do not
  expect serialization support from it.

## Roadmap

The order is: get the bare tree round-tripping in three syntaxes, then
lift to the annotated document, then hash. Fixing `annCanon`, the
multihash codes, the CID layout and the version numbers first would
specify a component whose hash function does not yet exist in Lean — see
[Ecosystem notes](#ecosystem-notes) — against no running code. What
must be fixed before those identifiers are *used*, rather than before
implementation begins, is the annotation vocabulary, the two key forms
`(rootCoreId, path)` and `subtreeMH`, and version numbers for
everything feeding a hash.

| Stage | Content | Status |
| --- | --- | --- |
| 1a | canonical S-expressions, bare tree, retraction proved | done |
| 1b | JSON core profile, bare tree, retraction proved | next |
| 1c | deterministic CBOR, bare tree, retraction proved | after 1b |
| 1d | cross-syntax agreement theorem | after 1c |
| 2 | lift every syntax from `Ast` to `Doc` | not started |
| 3 | a hash that runs | not started |
| 4 | CID, multibase, CAR | deferred |

[Local verification](#local-verification) gives stage 1a's size. That is
the only measured quantity, and one implementation is too small a base
to extrapolate a schedule from, so the stages below are ordered by
dependency and carry no estimate.

Stage 1b introduces no new proof technique and reuses the decimal layer
unchanged: the JSON core profile's integers are decimal ASCII, which is
what `decOf` and `digitsVal` already encode and decode. Its new work is
the bracket-and-comma grammar and the whitespace the profile permits.
Stage 1c is where a byte-level integer encoding first appears, and that
round-trip lemma is what CBOR adds over JSON. Stage 1d is a corollary of
the retractions preceding it, every syntax parsing to the same `Ast`.

Stage 2 is the largest. Moving from `Ast k` to `Doc k = Tree k Ann` puts
`Option String` and `List String` into the syntax, so the printer and
parser acquire string escaping and the round-trip proofs acquire its
inverse.

The injectivity constraint on `printDoc` is discharged for free on
`Doc k` as `Ann` is presently declared: it is a plain product, so
distinct `Doc k` values are distinguished by any printer that emits
every field, and no setoid is needed. What
[Idempotence is a corollary, and so is injectivity](#idempotence-is-a-corollary-and-so-is-injectivity)
warns against is the prior question, whether `Doc k` is the right model.
`Ann.links : List String` gives one document several `Doc k` values
whenever link order is not meant to be semantic. Injectivity survives
that; what fails is that `format` then has no fixed point to converge
to, and the choice — order is semantic, or `links` becomes a sorted
duplicate-free type — has to be made before stage 2 states a
document-level law. The same choice, one level up, is what
[The side-table presentation](#the-side-table-presentation) requires of
an annotation table.

Stage 3 is a build problem before it is a proof problem. What is missing
is any usable hash function; the realistic route is `@[extern]` against
OpenSSL, libsodium or BLAKE3, and a verified pure-Lean hash is not
available and is not on this path. The fold itself is specified in
[Structural content-addressing specification](#structural-content-addressing-specification)
and not written, since with no hash to run it would have no consumer.
Its compositionality will be a consequence of the fold's uniqueness,
which
[Geb/Mathlib/Data/W/Basic.lean](../Geb/Mathlib/Data/W/Basic.lean)
already states as `WType.elim_unique`; stage 3 inherits it rather than
proving it again.

Stage 4 is deferred in full. Validating syntax independence needs no
content identifiers, multibase, CAR archives or IPLD interoperation;
those are storage-interoperation features, taken up when a store
exists.

Stage 5, when references and binders arrive: abstract binding trees
for alpha-invariant hashing, and Unison-style cycle hashing by sorted
sub-hashes. Whether identity then remains purely syntactic or
quotients by α is a language-semantics decision for the Geb
specification, not one to delegate to a serialization format.

Thresholds that would change the plan: the switch thresholds in
[Evaluating the candidates](#evaluating-the-candidates); publication
of CBOR CDE as an RFC, which would become the citable
deterministic-CBOR profile in place of a bare §4.2 reference; a
verified pure-Lean SHA-2, which would reopen SHA-256 for git, Dhall
and IPFS interoperation; a need for generated typed APIs or
high-throughput transport, which would add Cap'n Proto as transport
with identity unchanged; a need for maximal annotation-surface
diversity, which would add XML with explicit annotation elements.

### Relation to existing repository content

`Ast k` is the W-type of the polynomial functor with shapes in bijection
with `Fin k ⊕ Unit` and arities `0` and `2`, and it is declared as one:
`Ast.Shape k` carries the two shapes, `Ast.Arity` sends them to `Empty`
and `Fin 2`, and `Ast k` is `WType Ast.Arity`.
[docs/rules/lean-coding.md](rules/lean-coding.md) § Recursion and
induction through recursors requires this. An ordinary inductive would
supply `DecidableEq` and `Repr` through `deriving` and structural
recursion through the equation compiler, and is not available.

Nothing the syntax layer needs is forfeited.
[Geb/Mathlib/Data/W/Basic.lean](../Geb/Mathlib/Data/W/Basic.lean)
supplies the fold's computation rule and its uniqueness, the
paramorphism `WType.para`, and a `DecidableEq` instance needing only a
finitely enumerable arity; `Ast.ind` recovers the two-constructor
induction principle, so no proof in the module mentions the shape and
arity encoding. No `Repr` instance is derived for the three tree types,
and nothing asks for one; `Ann` and `Dir`, which are ordinary
non-recursive declarations, derive theirs.

This repository separately carries the polynomial-functor presentation
of the same construction, in
[Geb/Mathlib/Data/PFunctor/Univariate/W.lean](../Geb/Mathlib/Data/PFunctor/Univariate/W.lean)
and
[Geb/Mathlib/Data/PFunctor/Univariate/Initial.lean](../Geb/Mathlib/Data/PFunctor/Univariate/Initial.lean).
Reconciling the two is a single equivalence, proved when the categorical
machinery needs it, which the parse and print layer does not.

## Caveats

- **"Deterministic" ≠ "canonical."** Protobuf's deterministic mode and
  any library's "stable output" flag stabilize bytes within one
  implementation; canonical means one encoding per value across all
  implementations. Only the latter supports content addressing.
- **CBOR sorts encoded keys; JSON sorts raw keys.** For string keys
  RFC 8949 §4.2 and RFC 7049 §3.9 agree (both are length-first), so
  DAG-CBOR's stated exception is a no-op; but both disagree with JCS and
  DAG-JSON for keys of unequal length. Audit any CBOR library for
  whether it sorts the encoded item or the bare string, and prefer
  map-free encodings, which make the question moot.
- **JCS and DAG-JSON disagree outside ASCII.** JCS sorts UTF-16 code
  units, DAG-JSON sorts UTF-8 bytes. Restrict keys to 7-bit ASCII.
- **Per-format canonical hashes identify documents, not values.** JCS,
  C14N, canonical csexp, and CBOR block hashes all differ across
  encodings of the same tree; semantic identity is `coreMH` on `A`.
- **A concrete syntax needs a deterministic printer, not a normative
  canonical form.** Do not over-weight the latter when choosing one.
- **`printDoc` must be injective**, so `D` must contain no redundant
  representations; annotation tables must be canonically ordered and
  duplicate-free by construction.
- **Content addressing conflates occurrences.** Hash-keyed annotation
  tables attach metadata to every equal subtree; per-occurrence
  annotation needs `(rootCoreId, path)` keys, and paths depend on the
  versioned binary/rose bijection.
- **The rose presentation cannot name every occurrence** — only the root
  and positions ending in `L`. Annotations on sibling-list cells do not
  survive a round trip through a rose-shaped syntax. The development
  proves one inclusion of this; see
  [Which occurrences the rose presentation can name](#which-occurrences-the-rose-presentation-can-name).
- **Lexical comments do not survive**; durable metadata must be explicit
  annotation values.
- **Fixed-point equations do not pin down `μ`.** The rose/binary
  correspondence needs explicit mutually-inverse maps proved by
  induction, and a fixed orientation convention.
- **The Merkle fold gives compositionality, not injectivity.** Hash
  equality implies structural equality only under a collision-resistance
  assumption held outside the kernel. Domain-separation tags must be
  equal-length or prefix-free.
- **Printers must not invent annotation content** (synthetic names), or
  document-level idempotence is at risk.
- **RFC 9804 is Informational**, `@` is not a legal token character, and
  a leading digit is not a legal token start.
- **CBOR and DAG-CBOR limits**: integers effectively i64 by codec and
  library convention, no bignum tags, only tag 42, 64-bit floats only.
- **DAG-JSON reserves the key `"/"`.** Never use it as a Geb key.
- **Lean crypto is research-grade.** `@gdncc/cryptography` disclaims
  cryptographic use and there is no pure-Lean SHA-2; plan for FFI.
  Round-trip laws are provable in Lean; collision resistance is an
  assumption.
- **Freshness.** RFC 9804 is June 2025; CBOR CDE was still
  `draft-ietf-cbor-cde-13` (October 2025, intended BCP) and not an RFC;
  Unison 1.0 is 25 November 2025; LeanSerde v0.2.0 is May 2026; the Lean
  development here is against v4.33.0-rc1. Re-check CDE, the Lean crypto
  situation, and the csexp tooling landscape before committing.

## References

[docs/references.bib](references.bib) is authoritative for the
bibliographic detail of three works this list also carries: RFC 9804 and
Uustalu and Vene 2011, both cited from Lean source, and RFC 6962, cited
from [Merkle hashing as a catamorphism](#merkle-hashing-as-a-catamorphism)
here and from Lean source once roadmap stage 3 writes the fold.
Migrating the rest of this list into the `.bib` is part of the
outstanding pass `TODO.md` records.

Standards and specifications:

- Rivest, R., and D. Eastlake 3rd, "Simple Public Key Infrastructure
  (SPKI) S-Expressions", RFC 9804, Informational, June 2025.
  <https://www.rfc-editor.org/rfc/rfc9804.html>
- Bormann, C., and P. Hoffman, "Concise Binary Object Representation
  (CBOR)", STD 94, RFC 8949, December 2020; §4.2 deterministic
  encoding. <https://www.rfc-editor.org/rfc/rfc8949.html>
- Bormann, C., "CBOR Common Deterministic Encoding (CDE)",
  draft-ietf-cbor-cde-13, October 2025.
  <https://datatracker.ietf.org/doc/draft-ietf-cbor-cde/>
- Rundgren, A., B. Jordan, and S. Erdtman, "JSON Canonicalization
  Scheme (JCS)", RFC 8785, Informational, June 2020.
  <https://www.rfc-editor.org/rfc/rfc8785.html>
- Bray, T., Ed., "The I-JSON Message Format", RFC 7493, March 2015.
  <https://www.rfc-editor.org/rfc/rfc7493.html>
- Laurie, B., A. Langley, and E. Kasper, "Certificate Transparency",
  RFC 6962, June 2013; §2.1 Merkle Hash Trees.
  <https://www.rfc-editor.org/rfc/rfc6962.html>
- Laurie, B., et al., "Certificate Transparency Version 2.0", RFC 9162,
  December 2021. <https://www.rfc-editor.org/rfc/rfc9162.html>
- IPLD, "DAG-CBOR Specification".
  <https://ipld.io/specs/codecs/dag-cbor/spec/>
- IPLD, "DAG-JSON Specification".
  <https://ipld.io/specs/codecs/dag-json/spec/>
- IPLD, "Content Addressable aRchives (CARv1)".
  <https://ipld.io/specs/transport/car/carv1/>
- Multiformats, "CID (Content IDentifier) Specification".
  <https://github.com/multiformats/cid>
- W3C, "Canonical XML Version 1.1", Recommendation, 2 May 2008.
  <https://www.w3.org/TR/xml-c14n11/>
- Cohen, B., "The BitTorrent Protocol Specification", BEP 3.
  <https://www.bittorrent.org/beps/bep_0003.html>
- Cap'n Proto, "Encoding Specification", canonicalization section.
  <https://capnproto.org/encoding.html>
- Google, "Proto Serialization Is Not Canonical".
  <https://protobuf.dev/programming-guides/serialization-not-canonical/>
- Amazon, "Ion Hash Specification".
  <https://amazon-ion.github.io/ion-hash/>
- WebAssembly, "Custom Annotation Syntax in the Text Format".
  <https://github.com/WebAssembly/annotations>

Category theory and recursion schemes:

- Uustalu, T., and V. Vene, "The recursion scheme from the cofree
  recursive comonad", Electronic Notes in Theoretical Computer Science
  229(5):135–157, 2011 (MSFP 2008). DOI 10.1016/j.entcs.2011.02.020
- Uustalu, T., and V. Vene, "Primitive (co)recursion and
  course-of-value (co)iteration, categorically", Informatica
  10(1):5–26, 1999.
- Uustalu, T., and V. Vene, "The dual of substitution is redecoration",
  in Trends in Functional Programming 3, Intellect, 2002, pp. 99–110.
- Capretta, V., T. Uustalu, and V. Vene, "Recursive coalgebras from
  comonads", Information and Computation 204(4):437–468, 2006.
  DOI 10.1016/j.ic.2005.08.005
- Osius, G., "Categorical set theory: a characterization of the
  category of sets", Journal of Pure and Applied Algebra 4:79–119,
  1974.
- Taylor, P., "Practical Foundations of Mathematics", CUP, 1999.
- Freyd, P., "Algebraically complete categories", LNM 1488, 1991; and
  "Remarks on algebraically compact categories", LMS Lecture Note
  Series 177, 1992.
- Smyth, M., and G. Plotkin, "The category-theoretic solution of
  recursive domain equations", SIAM Journal on Computing 11(4), 1982.
- Kleene, S. C., "Introduction to Metamathematics", 1952; §43,
  course-of-values recursion.

Verification and content addressing:

- Ramananandro, T., G. Ebner, G. Martínez, and N. Swamy, "Secure
  Parsing and Serializing with Separation Logic Applied to CBOR, CDDL,
  and COSE", ACM CCS 2025. DOI 10.1145/3719027.3765120;
  arXiv:2505.17335. <https://github.com/project-everest/everparse>
- Ni, H., A. Delignat-Lavaud, C. Fournet, T. Ramananandro, and N.
  Swamy, "ASN1*: Provably Correct, Non-malleable Parsing for ASN.1
  DER", CPP 2023. DOI 10.1145/3573105.3575684
- Delaware, B., S. Suriyakarn, C. Pit-Claudel, Q. Ye, and A. Chlipala,
  "Narcissus: Correct-by-Construction Derivation of Decoders and
  Encoders from Binary Formats", ICFP 2019.
- Conchon, S., and J.-C. Filliâtre, "Type-Safe Modular Hash-Consing",
  ACM SIGPLAN Workshop on ML, 2006, pp. 12–19.
  DOI 10.1145/1159876.1159880
- Braibant, T., J.-H. Jourdan, and D. Monniaux, "Implementing
  hash-consed structures in Coq", ITP 2013; arXiv:1304.6038.
  DOI 10.1007/978-3-642-39634-2_36
- Doussot, G., "Cryptography Experiments in Lean 4: SHA-3
  Implementation", IACR ePrint 2024/1880.
  <https://eprint.iacr.org/2024/1880>
- Unison Computing, "Hashes", Unison language reference.
  <https://www.unison-lang.org/docs/language-reference/hashes/>
- Unison Computing, "Announcing Unison 1.0", 25 November 2025.
  <https://www.unison-lang.org/unison-1-0/>
- dhall-lang issue #242, "Discuss: Version α-normalization and
  β-normalization?", October 2018.
  <https://github.com/dhall-lang/dhall-lang/issues/242>
- Jay, B., "Reflective Programs in Tree Calculus", 2021.
- Troesh, T., "Scrapscript". <https://scrapscript.org/>
