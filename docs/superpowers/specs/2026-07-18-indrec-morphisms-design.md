# Morphisms of IR codes — design

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Purpose](#purpose)
- [Source and proof-route deviation](#source-and-proof-route-deviation)
- [Design](#design)
  - [FreeCoprodCompDisc additions](#freecoprodcompdisc-additions)
  - [Precomposition on codes](#precomposition-on-codes)
  - [Universe scheme](#universe-scheme)
  - [Homset (Definition 8)](#homset-definition-8)
  - [Identity, composition, laws](#identity-composition-laws)
  - [Semantic statements](#semantic-statements)
  - [Placement and documentation](#placement-and-documentation)
- [Branch decomposition](#branch-decomposition)
- [Constraints](#constraints)

<!-- END doctoc generated TOC -->

## Purpose

Extend `Geb/Mathlib/Data/PFunctor/IndRec/Basic.lean` with the
morphisms of IR codes, following
[HancockMcBrideGhaniMalatestaAltenkirch2013] from "The category of
small IR codes" through Corollary 2: the auxiliary semantic
operations (copower, `(+i)`), the code operation `γ^i` (Lemma 4),
the homset (Definition 8), and identity, composition, and the
category laws (Corollary 2). The `Category` instance, Theorem 2
(the left-Kan-extension characterization), Theorem 3 (the
interpretation extended to morphisms, full and faithful), and the
equivalence with dependent polynomial functors are deferred to
future workstreams.

## Source and proof-route deviation

The paper's Corollary 2 is proved by transfer along the full and
faithful interpretation functor of Theorem 3; the paper exhibits
neither explicit identity and composition on the homsets of
Definition 8 nor a concrete construction of `γ^i` (Lemma 4 asserts
its existence; the appendix proves Theorems 2 and 3 and restates
Corollary 2's transfer argument). This workstream keeps the paper's
definitions and theorem statements and supplies its own
constructions and proofs:

- Transcription: the homset clauses of Definition 8; the statements
  of Lemma 3 and Lemma 4; the copower and `(+i)` operations; the
  binary coproduct `[i, k]` of objects (the paper's cotuple, used
  by `(+i)`).
- Novel (specified by the paper, constructed here): the concrete
  `γ^i`; explicit identity and composition; the category-law
  proofs; the auxiliary morphism operations they require; the
  universe scheme below; the object-isomorphism notion and the
  name-lifting operation on `FreeCoprodCompDisc` objects.

Recorded deviations from the paper's statements: Lemma 4's
equality of interpretations is stated as a pointwise isomorphism
(the intensional setting does not validate the paper's equality of
functors); Lemma 3's natural isomorphism is likewise stated as a
pointwise isomorphism (natural transformations between
interpretations are not yet defined; naturality is deferred with
Theorem 3); the clauses of `γ^i` and of the homset carry
`ULift` insertions forced by the universe scheme below; clause 1A
renders the paper's proposition `o ≡ o'` as the type
`PLift (o = o')`; and the homset is heterogeneous in the arity
universes where Definition 8 states one instantiation.

## Design

### FreeCoprodCompDisc additions

In `Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean`:

- Binary coproduct of objects (`Sum` of name types, `Sum.elim` of
  decodings), with injections and cotuple universal property.
- Copower `X ⊗ i`: `coprod X (fun _ ↦ i)` for a type `X` and an
  object `i`, with its universal property.
- `(+i)`: the object map sending `k` to the binary coproduct of a
  fixed object `i` with `k`.
- A name-lifting operation (`ULift` on the name type, decoding
  through `ULift.down`), so objects at a lower index universe can
  enter `Hom` and the coproduct constructions.
- An object-isomorphism notion: a name-type equivalence commuting
  with decodings. Chosen over a mutually inverse `Hom` pair
  because `Equiv` relates name types at different universes, which
  the lemma statements below require (`Hom` is fixed at one index
  universe).

### Precomposition on codes

`γ^i` internalizes precomposition with `(+i)` for `i : Q → I`: its
specification (Lemma 4) is `⟦γ^i⟧ k ≅ ⟦γ⟧ ((+i) k)` where the
object of `(+i)` is `⟨Q, i⟩`. Defined by `IR.elim` on `γ`:

- `(ι o)^i = ι o`; `(σ A K)^i = σ A (fun a ↦ (K a)^i)`.
- `(δ Q' K')^i`: a `σ` over `c : Q' → Q ⊕ PUnit` (classifying
  each element of the arity `Q'` as resolved immediately into `i`
  or not), then a `δ` over the subtype of unresolved arity
  elements, recursing on `K'` at the assignment merging `i ∘ c`
  with the `δ` directions.

The clauses are stated up to the `ULift` insertions the target
universe instantiation requires (for example `σ` receives the
lifted `A` and the lifted `c`-type).

### Universe scheme

The `σ` arity in the `δ` clause of `γ^i` lives at
`max uB' uB` (`Q' : Type uB'`, `Q : Type uB`), so for `i : Q → I`
with `Q : Type uB`, `γ^i` maps `IR.{uA', uB', uI, uO}` to
`IR.{max uA' uB' uB, uB', uI, uO}`, and that target instantiation
is a fixed point of the operation. Consequently:

- `IR.Hom` is heterogeneous: left code at `{uA, uB}`, right code at
  the stabilized instantiation `{max uA' uB uB', uB'}` (clause 3
  sends the right code through `γ^i`, and a single Lean definition
  cannot recurse at a changed universe instantiation).
- Identity, composition, and the laws are stated at the uniform
  stabilized instantiation `IR.{max uA uB, uB, uI, uO}`: a
  `Hom γ γ` requires the right side's `σ`-arity universe to carry
  the `max … uB` shape. The raw homset keeps the extra
  heterogeneous generality.
- The semantic lemmas are also stated at the uniform
  instantiation. `IR.interpObj` lands in `Map.{max uA uB, uI, uO}`
  and `Map` fixes one index universe for domain and codomain, so
  `⟦γ⟧ ((+i) k)` elaborates only where the coproduct's index
  universe is absorbed by the interpretation's — which the
  uniform instantiation provides (`Q : Type uB`,
  `γ : IR.{max uA uB, uB, uI, uO}`). The heterogeneous generality
  applies to the code operation and the homset, not to the
  interpretation, whose signature this workstream does not
  change.

### Homset (Definition 8)

`IR.Hom`, by `IR.elim` on the left code with an inner `IR.elim` on
the right code in the `ι` case:

- Clause 1A: `Hom (ι o) (ι o') = PLift (o = o')` (a `Type`, since
  other clauses wrap homsets in `Σ`/`Π`).
- Clause 1B: `Hom (ι o) (σ A K) = Σ a, Hom (ι o) (K a)`.
- Clause 1C: `Hom (ι o) (δ Q' K') =
  Σ e : Q' → PEmpty, Hom (ι o) (K' (PEmpty.elim ∘ e))`.
- Clause 2: `Hom (σ A K) γ' = Π a, Hom (K a) γ'`.
- Clause 3: `Hom (δ Q K) γ' = Π i : Q → I, Hom (K i) (γ'^i)`.

### Identity, composition, laws

By induction on codes at the uniform instantiation, broken into
named one-step auxiliary operations. Case analysis of
Definition 8 requires at least the following family (superscripts
by an index object `a = ⟨Q, i⟩` of `FreeCoprodCompDisc I`):

- Transport of homsets along code equalities (the `homOfEq`
  analogue for `IR.Hom`).
- σ-injection postcomposition `Hom γ (K a) → Hom γ (σ A K)`
  (identity at a `σ` code is not componentwise reflexivity:
  clause 2 makes `id` there a product of morphisms into the whole
  `σ` code).
- δ-injection postcomposition at an empty witness:
  `(e : E → PEmpty) → Hom γ (K (PEmpty.elim ∘ e)) →
  Hom γ (δ E K)`, and the dual elimination
  `Hom (ι o) (γ^(PEmpty.elim ∘ e)) → Hom (ι o) γ` (clause 1C in
  each direction of use).
- The generalized action of superscripting on morphisms:
  `Hom γ γ' → Hom_{Set/I}(a, b) → Hom (γ^a) (γ'^b)`, covariant in
  the index object through a `FreeCoprodCompDisc.Hom`. The plain
  action (`b = a`, identity) and the reindexing that the action's
  own `δ` case requires (the classification of a merged
  assignment induces a morphism of index objects) are its
  instances.
- Iterated-superscript conversion
  `Hom ((γ^a)^b) (γ^(a ⊕ b))` and its converse (the `δ` case of
  a unit or pre-unit produces `((δ Q K)^a)^b` obligations; the
  two codes differ by a currying of the classification `σ` and
  are related by morphisms, not equalities).
- The pre-unit `Hom γ (γ^a)` and the unit
  `Hom (K i) ((δ Q K)^i)` (what identity requires at a `δ`
  code).

These statements are expected to form one simultaneous induction
whose recursive calls land at superscripted images of subcodes
rather than at subcodes themselves (subcodes of `γ^a` are
superscripts of subcodes of `γ`), so the motives are expected to
be superscript-generalized, with the iterated-superscript
conversions bounding the depth. The plan for the second branch fixes the exact closed
statement set and derives every case of the induction before
implementation begins; if the set fails to close, the workstream
returns to design before any implementation. Auxiliary
operations beyond these identified during planning each get
their own named definition and lemmas.

Statements: `id : Hom γ γ`; `comp : Hom γ γ' → Hom γ' γ'' →
Hom γ γ''`; left identity, right identity, associativity as
equalities in the homsets.

### Semantic statements

Both at the uniform instantiation (`γ : IR.{max uA uB, uB}`,
`i : Q → I`, `Q : Type uB`), with the object-isomorphism notion
absorbing residual index-universe differences between the two
sides:

- Lemma 4: `⟦γ^i⟧ k ≅ ⟦γ⟧ ((+i) k)` pointwise, by induction on
  `γ` — the correctness proof for the constructed `γ^i`.
- Lemma 3:
  `⟦δ Q K⟧ k ≅ ∐ (i : Q → I), Hom(lift ⟨Q, i⟩, k) ⊗ ⟦K i⟧ k`
  pointwise, from the coproduct and copower machinery; `⟨Q, i⟩`
  enters `Hom` through the name-lifting operation, since its
  names live at `uB` and `k`'s at `max uA uB`.

### Placement and documentation

A requirement of this workstream is that the morphism development
precede the `Universes` and `Container` sections, so later
workstreams can extend those sections with morphism uses; the
code section therefore sits in `IndRec/Basic.lean` between the
interpretation block and `section Universes`. If the resulting
module size conflicts with the narrow-and-deep directory
structure, a follow-on refactor can move the morphism development
to a sibling `IndRec` module and relocate the `Universes` and
`Container` sections after it — a decision deferred until the
development's size is known. Module docstrings (`## Main definitions`,
`## Main statements`, implementation notes) are updated in every
touched file (including `Geb/Mathlib/Logic/Equiv/Basic.lean`,
which receives generic `Equiv` combinators the constructions
factor through); every declaration transcribed from or specified
by the paper cites [HancockMcBrideGhaniMalatestaAltenkirch2013]
per the citation rules, with docstrings distinguishing
transcription from construction. Generic auxiliary machinery
(hom composition, the isomorphism notion, lifting, the `Equiv`
combinators) is not taken from the paper and carries no
citation, per the citation rules' scope. Mirrored test files
under `GebTests/` and the `docs/index.md` entry are updated in
the same branches.

## Branch decomposition

Two stacked topic branches, each with its own plan:

1. FreeCoprodCompDisc additions, `γ^i`, Lemmas 3 and 4.
2. Homset, identity, composition, category laws.

## Constraints

- Constructive discipline: no `noncomputable`, no `Classical`;
  axiom linter passes (`propext`, `Quot.sound` only).
- Recursor-only recursion: all definitions by `IR.elim`/`IR.rec`;
  no `induction` tactic, no self-referential `def`.
- Explicit proof terms: committed definitions and proofs are
  term-mode, with no tactic blocks. Tactics may be used during
  intermediate development to discover a proof; the committed
  form spells out the resulting term, factored into small named
  declarations (motives, step functions, auxiliary lemmas) in the
  manner of `IR.ExtMotive` and `IR.ext`, whose motive is factored
  out precisely so that the proof is an `Eq.rec` application.
  Rationale: the development is eventually to become
  self-referential — fixed points of inductive-recursive types
  that themselves describe the syntax of inductive-recursive
  definitions, including the syntax of these proofs — and tactic
  scripts obscure the proof terms that syntax must describe.
- `lake build`, `lake test`, `lake lint`,
  `scripts/lint-imports.sh` pass on each branch.
- Interface fixed by the source: the homset clauses and lemma
  statements follow the paper up to the recorded deviations
  (isomorphism for equality of interpretations; `ULift`
  insertions); implementation strategies are free.
