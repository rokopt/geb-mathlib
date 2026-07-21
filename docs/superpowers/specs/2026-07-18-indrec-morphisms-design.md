# Morphisms of IR codes — design

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Purpose](#purpose)
- [Closure gate result](#closure-gate-result)
- [Source and proof-route deviation](#source-and-proof-route-deviation)
- [Design](#design)
  - [FreeCoprodCompDisc additions](#freecoprodcompdisc-additions)
  - [Precomposition on codes](#precomposition-on-codes)
  - [Universe scheme](#universe-scheme)
  - [Homset (Definition 8)](#homset-definition-8)
  - [Identity (branch 2a)](#identity-branch-2a)
  - [Theorem 2.4 functoriality (branch 2b)](#theorem-24-functoriality-branch-2b)
  - [Naturality and Theorem 3 (branch 2c)](#naturality-and-theorem-3-branch-2c)
    - [The natural-transformation notion](#the-natural-transformation-notion)
    - [New `FreeCoprodCompDisc` infrastructure](#new-freecoprodcompdisc-infrastructure)
    - [Naturality upgrades of Lemmas 3 and 4](#naturality-upgrades-of-lemmas-3-and-4)
    - [The Theorem 3 induction](#the-theorem-3-induction)
  - [Composition and the category laws (branch 2d)](#composition-and-the-category-laws-branch-2d)
    - [The identity-image equation (branch 2d closure gate)](#the-identity-image-equation-branch-2d-closure-gate)
    - [The iterated-precomposition tower, semantically](#the-iterated-precomposition-tower-semantically)
    - [Characterizing equations of `IR.interpHom`](#characterizing-equations-of-irinterphom)
    - [Characterization of the injection helpers](#characterization-of-the-injection-helpers)
    - [The identity-image induction](#the-identity-image-induction)
    - [Composition and the laws by transfer](#composition-and-the-laws-by-transfer)
    - [Placement (branch 2d)](#placement-branch-2d)
  - [Semantic statements (branch 1, complete)](#semantic-statements-branch-1-complete)
  - [Placement and documentation](#placement-and-documentation)
- [Branch decomposition](#branch-decomposition)
- [Constraints](#constraints)

<!-- END doctoc generated TOC -->

## Purpose

Extend `Geb/Mathlib/Data/PFunctor/IndRec/Basic.lean` with the
category of IR codes, following
[HancockMcBrideGhaniMalatestaAltenkirch2013] from "The category of
small IR codes" through Corollary 2. Branch 1 (complete) supplied the
auxiliary semantic operations (copower, `(+i)`, the cotuple `[i, k]`),
the code operation `γ^i` (Lemma 4), and Lemmas 3 and 4. The remaining
work — the homset (Definition 8), the identity, composition, and the
category laws (Corollary 2) — is delivered in four dependency-ordered
branches (see Branch decomposition):

- 2a: the homset and the identity morphism, constructed syntactically.
- 2b: the functoriality content of Theorem 2.4 of
  [GhaniNordvallForsbergMalatesta2015] for the interpretation
  (`FreeCoprodCompDisc.Hom` identity and category laws; the `IR.rec`
  computation rule; the characterizing equations of `IR.interpMor`;
  preservation of identity and composition).
- 2c: natural transformations between interpretations and Theorem 3
  (the interpretation extended to morphisms, full and faithful).
- 2d: composition and the category laws (Corollary 2), by transfer
  through the full-and-faithful interpretation of Theorem 3.

The scope grew from the original branch-2 plan (homset plus a purely
syntactic identity, composition, and laws) after the closure gate below
established that composition does not close by syntactic induction on
codes and requires the semantic transfer of Theorem 3.

The mathlib `Category` instance, Theorem 2 (the left-Kan-extension
characterization), and Theorem 4 (the equivalence with dependent
polynomial functors) remain deferred to future workstreams.

## Closure gate result

The identity, composition, and category laws were first specified as a
single simultaneous syntactic induction on codes (no interpretation
route). A prototype of the homset and the candidate auxiliary
operations, checked against the built `Basic.lean`, established:

- The homset (Definition 8) computes definitionally at every clause,
  and the identity morphism closes syntactically — through a
  list-generalized pre-unit `Hom γ (γ^a)` whose recursion appends the
  mapped `δ`-direction to a superscript stack (so the subcode
  induction hypothesis lands at the required precomposition depth) and
  a navigation operation carrying a factorization parameter. The
  identity depends only on `propext` and `Quot.sound`.
- Composition does not close. It requires `supMor` (the action of
  precomposition on morphisms) and `sup2` (associativity of iterated
  precomposition) at the codomain code, which is a parameter rather
  than a structural subcode of the recursion; no generalization of the
  recursion variable reaches it, and the homset is domain-recursive, so
  inducting on the codomain does not decompose it either. This matches
  the source, which obtains Corollary 2 by transfer along the
  full-and-faithful interpretation (Theorem 3), not syntactically.

## Source and proof-route deviation

The paper proves Corollary 2 by transfer along the full and faithful
interpretation functor of Theorem 3; the paper exhibits no explicit
identity or composition on the homsets of Definition 8, and asserts
`γ^i` only to exist (Lemma 4). This workstream follows the paper's
transfer route for composition and the category laws (branch 2d),
constructs the identity syntactically (branch 2a), and supplies its own
constructive proofs, in the `FreeCoprodCompDisc` encoding, of the
Theorem 2.4 functoriality (branch 2b) and of Theorem 3 (branch 2c) that
the transfer consumes:

- Transcription: the homset clauses of Definition 8; the statements
  of Lemma 3, Lemma 4, the functoriality content of Theorem 2.4 of
  [GhaniNordvallForsbergMalatesta2015], Theorem 3, and Corollary 2;
  the copower and `(+i)` operations; the binary coproduct `[i, k]`
  of objects (the paper's cotuple, used by `(+i)`).
- Novel (constructed here): the concrete `γ^i` (branch 1); the
  syntactic identity, through a list-generalized pre-unit and a
  navigation operation (branch 2a); the constructive proofs of the
  Theorem 2.4 functoriality, Theorem 3, and Corollary 2 in the
  `FreeCoprodCompDisc` encoding, together with the natural-transformation
  notion between interpretations they require; the universe scheme
  below; the object-isomorphism notion and the name-lifting operation
  on `FreeCoprodCompDisc` objects.

Recorded deviations from the paper's statements: composition and the
category laws are obtained by the paper's transfer through Theorem 3
rather than by syntactic induction on codes, the closure gate having
established that the syntactic route does not reach composition;
Theorem 3's natural isomorphism is realized in the constructive,
`Classical`-free `FreeCoprodCompDisc` encoding (no mathlib `Category`);
Lemma 4's
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
  the lemma statements below require (`Hom` itself is
  universe-heterogeneous, but stating a mutually inverse pair
  requires `Hom.comp`, which fixes one index universe — as do
  `Map` and `MapMor`).

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

### Identity (branch 2a)

The homset and the identity are constructed syntactically at the
uniform instantiation, by `IR.rec` on the domain code, in named
one-step operations (each an explicit term). The construction, verified
against `Basic.lean`:

- Homset transport `homOfEq` along code equalities (the `IR.Hom`
  analogue of `FreeCoprodCompDisc.homOfEq`).
- `sigmaPush : Hom γ (K a) → Hom γ (σ A K)` — σ-injection
  postcomposition, `IR.rec` on the domain with the target `(A, K, a)`
  generalized. (Identity at a `σ` code is not componentwise
  reflexivity; clause 2 makes it a product of injections into the
  whole `σ` code.)
- `deltaEmptyPush : Hom γ (M (PEmpty.elim ∘ e)) → Hom γ (δ E M)` for an
  empty witness `e : E → PEmpty`, `IR.rec` on the domain with
  `(E, e, M)` generalized.
- A list-generalized pre-unit `preUnitStack γ L : Hom γ (γ ^^ L)`,
  where `γ ^^ L` folds precomposition over a list `L` of index
  objects. `IR.rec` on `γ` with `L` generalized: the `δ` case appends
  the mapped direction `⟨B, i⟩` to `L`, so the subcode induction
  hypothesis lands at the precomposition depth the clause-3 superscript
  demands. The navigation from that hypothesis into the superscripted
  `δ`-tower is a `deltaNav` operation carrying a factorization
  parameter `g : Bin → Bout` that tracks how a peeled classifier layer
  resolves against the outer superscript.
- `id γ := preUnitStack γ []`.

The stack generalization replaces the simultaneous superscript-generalized
induction the original branch-2 plan anticipated. For the identity every
superscript layer is generated by the domain's own directions, which the
stack captures, so the recursion is well-founded on the domain code with
the stack a parameter. The identity depends only on `propext` and
`Quot.sound`. The `List`-recursive helpers (`γ ^^ L`, the stack folds)
are committed through `List.rec`, per the recursor-only rule.

Statement: `id : Hom γ γ`.

### Theorem 2.4 functoriality (branch 2b)

The functoriality content of Theorem 2.4 of
[GhaniNordvallForsbergMalatesta2015], constructively, so that `⟦γ⟧` is a
functor and natural transformations between interpretations can be
stated:

- `FreeCoprodCompDisc.Hom` identity and the category laws (left
  identity, right identity, associativity); composition
  (`FreeCoprodCompDisc.Hom.comp`) exists from branch 1. The
  functoriality of `coprodMor` (preservation of identity and
  composition), which the functor-law proofs and branch 2c's
  naturality consume.
- The propositional computation rule of `IR.rec`, and from it the
  characterizing equations of `IR.interpMor` at `IR.iota`,
  `IR.sigma`, and `IR.delta`.
- Preservation of identity and composition by `IR.interpMor`.

Independent of branch 2a. Corresponds to the existing TODO item
"Complete Theorem 2.4 for `IndRec`" (constructive part).

### Naturality and Theorem 3 (branch 2c)

- A notion of natural transformation between interpretations
  `⟦γ⟧ ⇒ ⟦γ'⟧` (families of `FreeCoprodCompDisc.Hom` commuting with the
  morphism maps), with identity and vertical composition.
- Theorem 3: the interpretation extended to morphisms,
  `Hom γ γ' → Nat(⟦γ⟧, ⟦γ'⟧)`, full and faithful — the correspondence
  `Hom γ γ' ≅ Nat(⟦γ⟧, ⟦γ'⟧)`, by induction on the homset structure,
  using Lemmas 3 and 4 (branch 1). Fullness (the `Nat → Hom` direction)
  is what the transfer of branch 2d consumes.

Depends on branch 2b. The constructive proof of Theorem 3 in the
`FreeCoprodCompDisc` encoding — in particular staying `Classical`-free —
is this branch's closure gate: its plan derives the induction before
implementation, returning to design if it fails to close. The
derivation below discharges the gate; the subsections record, in
dependency order, the notions and infrastructure it consumes.

#### The natural-transformation notion

Generic to `FreeCoprodCompDisc`, not specific to interpretations of
codes: for object maps `F G : Map I O` with morphism maps
`mF : MapMor I O F` and `mG : MapMor I O G`, a natural transformation
is a family `η : (X : FreeCoprodCompDisc I) → Hom O (F X) (G X)`
satisfying `(mF X Y h).comp (η Y) = (η X).comp (mG X Y h)` for every
`h : Hom I X Y` — a subtype with a `Prop`-valued naturality
condition, so equality of transformations is `Subtype.ext` plus
`funext`. Identity, vertical composition, and the laws branch 2d
consumes (left and right identity, associativity) are componentwise,
from the `FreeCoprodCompDisc.Hom` category laws (branch 2b).
`Nat(⟦γ⟧, ⟦γ'⟧)` is the instantiation at
`(interpObj γ, interpMor γ)` and `(interpObj γ', interpMor γ')`; it
lives at `Type (max (max uA uB + 1) uI)` (a function over the
object type at `Type (max (max uA uB + 1) uI)` with `Hom`-values at
`Type (max uA uB)`; neither level mentions `uO`), at least as
large as `IR.Hom`'s `Type (max uA uB uI)` and not level-equal to
it in general — `Equiv` is universe-heterogeneous, so the
Theorem 3 statement elaborates.

A natural family of isomorphisms (the form of the Lemma 4 upgrade)
is a family of `FreeCoprodCompDisc.Iso` whose forward homs satisfy
the same naturality condition; naturality of the inverse family
follows by a lemma (conjugating the square by the inverses), so
such a family converts to a mutually inverse pair of natural
transformations — the form the transport lemma of the `δ`-case
consumes.

The branch also exposes the composition API of the notion (none of
it is consumed by Theorem 3 or the branch 2d transfer; it is the
client-facing surface of the functor-category structure): the
composite of two `Map`s and of their `MapMor`s (function
composition, at one index universe); right whiskering
(precomposition of a transformation with a functor — no functor-law
hypotheses); left whiskering and horizontal composition, whose
naturality consumes the outer functor's composition-preservation
law as a hypothesis, in the manner of the copower–Yoneda adjunction
below; the agreement of the two orientations of the horizontal
composite (the outer morphism map of a component followed by the
second transformation, against the second transformation followed
by the other outer morphism map of the component), by the second
transformation's naturality; the identity coherences (the
horizontal composite of identity transformations is the identity —
consuming the outer functor's identity-preservation law — and
whiskering by an identity functor is the identity operation); and
the interchange law with vertical composition, from naturality and
the composition-law hypotheses.

#### New `FreeCoprodCompDisc` infrastructure

- The initial object `⟨PEmpty, PEmpty.elim⟩`, the morphism
  `bang X` out of it, and its uniqueness (every commutation
  condition out of an empty name type holds by `funext`).
- The universal property of the indexed coproduct, at one index
  universe (the large-index coproduct of the `δ`-clause is handled
  by the per-summand Lemma 3 upgrade instead): injections
  `coprodInj`, the cotuple `coprodDesc`, the equivalence
  `Hom (coprod ι fi) Z ≃ ((i : ι) → Hom (fi i) Z)` (generalizing
  `copowerEquiv`, which is its constant-family case), and the
  composition compatibilities
  (`(coprodMor r hom).comp (coprodDesc m)` as a cotuple;
  `(coprodDesc m).comp g` as a cotuple of composites;
  `(hom i).comp (coprodInj (r i)) = (coprodInj i).comp
  (coprodMor r hom)` on the injection side).
- `coprodPairMor` — the functorial action of `coprodPair` (hence of
  `plus c`) on morphisms, with preservation of identity and
  composition; it makes `X ↦ ⟦γ'⟧ (plus c X)` a morphism-mapped
  family, the codomain of the copower–Yoneda adjunction below.
  Universe-heterogeneous in the two objects, mirroring
  `coprodPair.{uX, uY}` (the Lemma 4 upgrade composes
  `Hom.id ⟨Q, i⟩` at index universe `uB` with a morphism at
  `max uA uB`; a single-universe form would not elaborate there).
- The singleton-domain fiber description
  `Hom (⟨ULift Unit, fun _ ↦ d⟩) Z ≃ {z : Z.1 // Z.2 z = d}`
  (consumed throughout the `ι`-case), together with the
  sigma–subtype commutation
  `{z : Σ a, N a // P z} ≃ Σ a, {n : N a // P ⟨a, n⟩}` that
  decomposes it over a coproduct in clause 1B (a generic `Equiv`
  combinator, placed per § Placement and documentation).

#### Naturality upgrades of Lemmas 3 and 4

- Lemma 4 (`IR.interpPrecompIso`, fixed `Q`, `i`, `γ`): the
  right-hand side `k ↦ ⟦γ⟧ (plus ⟨Q, i⟩ k)` stays at the uniform
  index universe (`plus` of `⟨Q, i⟩` at `uB` with `k` at
  `max uA uB` lands at `max uA uB`) and carries the composite
  morphism map
  `h ↦ interpMor γ _ _ (coprodPairMor (Hom.id ⟨Q, i⟩) h)` (the
  heterogeneous `coprodPairMor` instantiation). The upgrade states
  that the existing pointwise isomorphism family is natural with
  respect to it, by `IR.induction` on `γ` (the square is
  `Prop`-valued), using branch 2b's characterizing equations, with
  the transport eliminations in the manner of
  `InterpMorCompHgMotive`.
- Lemma 3 (`IR.interpDeltaIso`, fixed `B`, `c`): the lemma's
  right-hand side is a coproduct over `i : B → I`, whose index type
  lives at `Type (max uB uI)`, exceeding the uniform index universe
  whenever `uI` does — so the total coproduct is not a
  `Map.{max uA uB, uI, uO}` and cannot carry a `MapMor`. The
  upgrade therefore takes per-summand form and never treats the
  total coproduct as a functor. Each summand
  `W i := fun X ↦ Hom(lift ⟨B, i⟩, X) ⊗ ⟦c i⟧ X` is a `Map` at the
  uniform index universe, with morphism map `mW i` reindexing the
  copower weight by postcomposition (`e ↦ e.comp h`) over
  `interpMor (c i)`. The upgrade delivers:
  - the inclusion family
    `deltaInto i X : Hom (W i X) (⟦δ B c⟧ X)` (the `i`-summand of
    the pointwise Lemma 3 isomorphism, inverted), natural in `X`
    with respect to `mW i` and `interpMor (delta B c)`;
  - the cotuple `deltaDesc : ((i : B → I) → Hom (W i X) Z) →
    Hom (⟦δ B c⟧ X) Z`, defined directly through the grouping
    equivalences of `interpDeltaIso` (both endpoints in-category;
    the large-index coproduct never appears as a `Hom` endpoint
    and never carries a morphism map), with the computation
    law `(deltaInto i X).comp (deltaDesc m) = m i` and the
    uniqueness law
    `deltaDesc (fun i ↦ (deltaInto i X).comp h) = h` (together
    these make the inclusions jointly epic).

  `IR.interpDeltaIso` is a single non-recursive composite of
  equivalences, so these are direct calculations (after rewriting
  the `⟦δ B c⟧`-side morphism map by branch 2b's `interpMor_delta`,
  and with the established transport eliminations for the weight
  equalities), not inductions.

#### The Theorem 3 induction

By `IR.rec` on the domain code with motive
`γ ↦ ∀ γ', Hom γ γ' ≃ Nat(⟦γ⟧, ⟦γ'⟧)`, mirroring the domain
recursion of `IR.Hom` itself; the characterizing equations of the
resulting equivalence at each constructor hold propositionally via
`IR.rec_mk` (branch 2b), and the homset clauses compute
definitionally. The characterizing equations `interpMor_sigma` /
`interpMor_delta` enter as propositional rewrites of the morphism
map before the generic lemmas below apply.

- `σ`-case: `Hom (σ A K) γ' = Π a, Hom (K a) γ'` maps through the
  inductive hypotheses to `Π a, Nat(⟦K a⟧, ⟦γ'⟧)`, and
  `⟦σ A K⟧ X = coprod A (fun a ↦ ⟦K a⟧ X)` with `coprodMor`-shaped
  morphism map (identity reindexing), so a generic lemma — a
  natural transformation out of an indexed coproduct of
  morphism-mapped families is exactly a family of natural
  transformations out of the summands — closes the case. Both
  directions are `coprodDesc` / `coprodInj`; naturality decomposes
  componentwise by the composition compatibilities.
- `δ`-case (through Lemmas 3 and 4):

  1. `Nat(⟦δ Q K⟧, ⟦γ'⟧) ≃ Π i : Q → I, Nat(W i, ⟦γ'⟧)` by the
     per-summand Lemma 3 upgrade: forward restricts along the
     inclusions (`θ i` at `X` is `(deltaInto i X).comp (η X)`,
     natural by the inclusion naturality, the naturality of `η`,
     and associativity); backward cotuples (`η` at `X` is
     `deltaDesc (fun i ↦ θ i X)`), natural by joint epicness of
     the inclusions, the computation law, the naturality of each
     `θ i`, the inclusion naturality, and associativity; the round
     trips are the computation and uniqueness laws.
  2. `≃ Π i, Nat(⟦K i⟧, ⟦γ'⟧ ∘ (plus (lift ⟨Q, i⟩) ·))` by the
     copower–Yoneda adjunction below, at `c := lift ⟨Q, i⟩` (which
     places `c` at the uniform index universe `max uA uB`, so all
     injections, cotuples, and composites are same-universe).
  3. `≃ Π i, Nat(⟦K i⟧, ⟦γ'⟧ ∘ (plus ⟨Q, i⟩ ·))` by transport along
     the bridge isomorphism `plus (lift ⟨Q, i⟩) X ≅ plus ⟨Q, i⟩ X`
     (`ULift` on the left summand's names), imaged under `⟦γ'⟧` via
     `interpMor` and the functor laws as a mutually inverse pair of
     natural transformations — matching Lemma 4's stated right-hand
     side. Naturality of the imaged family rests on the
     object-level commutation of the bridge with `coprodPairMor`
     (a `Subtype.ext` calculation) before `interpMor_comp`
     applies.
  4. `≃ Π i, Nat(⟦K i⟧, ⟦precomp Q i γ'⟧)` by transport along the
     Lemma 4 upgrade, converted to a mutually inverse natural pair
     (the generic transport lemma, stated for such pairs on either
     side: mutually inverse `Nat`s between `G` and `G'` induce
     `Nat(F, G') ≃ Nat(F, G)`, and dually on the domain side).
  5. `≃ Π i, Hom (K i) (precomp Q i γ')` by the inductive
     hypothesis at `K i` (a structural subcode; the motive
     quantifies over all codomains, so instantiating at
     `precomp Q i γ'` is available, and the uniform instantiation
     is preserved since `Q : Type uB`) — which is definitionally
     `Hom (δ Q K) γ'`'s clause 3.

  The copower–Yoneda adjunction (generic; the functor laws of both
  `F` and `G` are hypotheses — supplied by `interpMor_id` /
  `interpMor_comp` — together with the binary-coproduct computation
  laws `coprodPair_inl_desc` / `coprodPair_inr_desc` and the
  cotuple uniqueness `coprodPairDesc_eta`):
  `Nat(Hom(c, ·) ⊗ F, G) ≃ Nat(F, G ∘ (plus c ·))`. Forward: at
  `X`, inject `F X` into `F (plus c X)` along `mF` of the right
  injection, pair with the left injection as the weight, and apply
  the transformation at `plus c X`. Backward: at `X` and weight
  `h : Hom(c, X)`, apply the transformation at `X` and follow with
  `G` of the cotuple `coprodPairDesc h (Hom.id)`. Round trips are
  the coproduct laws, both functor-law hypotheses, and naturality
  of the given transformation.
- `ι`-case: `⟦ι o⟧` is the constant map at the singleton object
  `single o := ⟨ULift Unit, fun _ ↦ o⟩`, and evaluation at the
  initial object gives
  `Nat(⟦ι o⟧, ⟦γ'⟧) ≃ Hom(single o, ⟦γ'⟧ ∅)`: forward is
  `η ↦ η ∅`; backward sends `f` to the family
  `X ↦ f.comp (interpMor γ' ∅ X (bang X))`, natural by
  `interpMor_iota` (reducing the `⟦ι o⟧`-side morphism map to the
  identity — `interpMor` computes only propositionally),
  `interpMor_comp`, initial-object uniqueness, and the `Hom`
  category laws, with the round trips by `interpMor_id` (at
  `bang ∅ = Hom.id`), `interpMor_iota`, and naturality.
  A second equivalence `InnerHom o γ' ≃ Hom(single o, ⟦γ'⟧ ∅)`
  follows by `IR.rec` on the codomain, mirroring `InnerHom`'s own
  recursion, through the fiber description
  `Hom(single o, Z) ≃ {z : Z.1 // Z.2 z = o}`:
  - Clause 1A (`ι o'`): both interpretations are singletons; the
    commutation condition is exactly `o = o'`, matching
    `ULift (PLift (o = o'))`.
  - Clause 1B (`σ A' K'`): `⟦σ A' K'⟧ ∅` is a coproduct, a
    morphism out of a singleton into a coproduct is a summand
    choice with a morphism into that summand, and the inner
    inductive hypotheses close each summand:
    `Σ a', InnerHom o (K' a')`.
  - Clause 1C (`δ Q' K'`): `⟦δ Q' K'⟧ ∅` is the coproduct over
    directions `g : Q' → PEmpty` landing in the initial object's
    empty name type, so the summand choice is an empty witness
    and the subcode argument is the vacuous assignment:
    `Σ e : Q' → PEmpty, InnerHom o (K' (PEmpty.elim ∘ e))`, up to
    the universe bridge between `InnerHom`'s `PEmpty.{1}` witness
    and the initial object's names at `Type (max uA uB)` (empty
    types are equivalent across universes) and up to an `Eq.rec`
    transport of the subcode assignment: the interpretation side
    feeds `∅.2 ∘ g` where clause 1C feeds the neutral elimination
    `fun b ↦ (e b).elim`, equal only propositionally (by `funext`
    of the pointwise eliminations).

Statement: `interpHomEquiv : Hom γ γ' ≃ Nat(⟦γ⟧, ⟦γ'⟧)`, whose
forward map `interpHom` is the interpretation extended to
morphisms. Theorem 3 transcribes as this equivalence (fullness is
the inverse map, faithfulness is injectivity of the forward map);
the induction realizing it is this project's construction, per
§ Source and proof-route deviation.

Closure-gate assessment: every map above is explicit data;
transports are `Eq.rec` along given equalities; the round trips use
only the functor laws, the coproduct and copower laws, naturality,
`funext`, and `Subtype.ext`. No step consumes `Classical`; the gate
closes.

Not in branch 2c: the equation sending `interpHom (IR.id γ)` to the
identity natural transformation. It consumes branch 2a's syntactic identity, on
which 2c does not depend; branch 2d (which depends on both) proves
it for the identity laws. The `IR.elim` / `IR.rec` uniqueness
properties remain outside the workstream (this route does not need
them).

Tests: fold in the morphism-action sample of `TODO.md` § Complete
Theorem 2.4 for `IndRec` (a propositionally nontrivial commutation
proof exercising the `homOfEq` transport in `IR.interpMorDelta`
observably) — naturality statements produce exactly such
transports.

### Composition and the category laws (branch 2d)

By transfer through the full-and-faithful interpretation of Theorem 3
(the paper's Corollary 2):

- `comp : Hom γ γ' → Hom γ' γ'' → Hom γ γ''`, the image under fullness
  of the vertical composite of the transported natural transformations.
- Left identity, right identity, and associativity, as equalities in
  the homsets, from the corresponding laws for natural transformations
  together with faithfulness.

The auxiliary code operations the syntactic route required (`supMor`,
the action of precomposition on morphisms; `sup2`, associativity of
iterated precomposition) are subsumed: they are precomposition's
functoriality and associativity, which hold semantically through
Lemma 4 and need no separate syntactic construction. Depends on
branches 2a and 2c.

Associativity and the composition operation consume only the
equivalence's round-trip laws and `NatTrans.vcomp_assoc`; the identity
laws additionally require the identity-image equation below, which is
branch 2d's closure gate: its induction is derived here before
planning, returning to design if it fails to close.

#### The identity-image equation (branch 2d closure gate)

Statement: `interpHom γ γ (IR.id γ) = NatTrans.id ⟦γ⟧`. Deliberately
not part of branch 2c (it consumes branch 2a's `preUnitStack`
construction, on which 2c does not depend).

`NatTrans` is a subtype (a component family with a `Prop`-valued
naturality condition), so the equation reduces by `Subtype.ext` and
`funext` to component equations in `FreeCoprodCompDisc.Hom`, and the
whole derivation is phrased at the component level: no intermediate
transformation is constructed as a `NatTrans`, so no intermediate
naturality proof arises — each equation relates plain
`FreeCoprodCompDisc.Hom` composites, and component equations between
plain homs carry no naturality obligation (the left sides happen to
be components of `IR.interpHom` images; the right sides are explicit
composites). For the
same reason `NatTrans.congrSource` drops out of every component
calculation: it transports the naturality proof and fixes the
component family.

The induction generalizes the identity to the pre-unit: with
`γ ^^ L` for `IR.mprecomp L γ`, the generalized statement is a
component equation for `interpHom γ (γ ^^ L) (preUnitStack γ L)`
against an explicit semantic pre-unit component, by `IR.induction`
on `γ` with `L` generalized — mirroring `preUnitStack`'s own
recursion, as the Theorem 3 induction mirrors `IR.Hom`'s.

#### The iterated-precomposition tower, semantically

Three `List.rec` constructions over the stack (no code recursion),
with snoc lemmas in the manner of `mprecomp_snoc`:

- `mplus L X`: the iterated coproduct object,
  `mplus [] X = X` and `mplus (b :: L) X = plus b (mplus L X)`;
  `mplus (L ++ [b]) X = mplus L (plus b X)`.
- `mplusInj L X : Hom X (mplus L X)`: the iterated right injection,
  `Hom.id` at `[]`, and at `b :: L` the right coproduct-pair
  injection after `mplusInj L X`. `coprodPairInl`/`coprodPairInr`
  are pinned to one index universe while the summands here sit at
  `uB` and `max uA uB`; a universe generalization
  `coprodPairInl.{uX, uY}`/`coprodPairInr.{uX, uY}` (in the manner
  of `coprodPairMor.{uX, uY, uX', uY'}`; the underlying
  `⟨Sum.inl, rfl⟩`/`⟨Sum.inr, rfl⟩` terms elaborate
  heterogeneously) is a required `FreeCoprodCompDisc` addition.
- `mprecompIso γ L X : Iso (⟦γ ^^ L⟧ X) (⟦γ⟧ (mplus L X))`: the
  iterated Lemma 4 isomorphism, `Iso.refl` at `[]` and
  `Iso.trans` of `mprecompIso (precomp b γ) L X` with
  `interpPrecompIso γ b.1 b.2 (mplus L X)` at `b :: L` (the motive
  quantifies over `γ`).

The semantic pre-unit component is
`preUnitComponent γ L X := (interpMor γ X (mplus L X)
(mplusInj L X)).comp ((mprecompIso γ L X).invHom)`. At `L = []` it
is `Hom.id` by `interpMor_id` and the identity laws, which reduces
the closure-gate statement to the generalized one.

#### Characterizing equations of `IR.interpHom`

The domain-constructor unfoldings of `IR.interpHomEquiv`, from
`IR.rec_mk` as for the `interpMor` family — client-facing API as
well as the induction's rewriting lemmas, each stated as the
component formula the step realizes:

- `interpHom_iota`: at an `ι`-domain, the component at `X` is the
  `∅`-evaluation composed with the codomain's image of
  `emptyDesc X` (the `natIotaInvFun` formula).
- `interpHom_sigma`: at a `σ`-domain, the component at `X` is the
  cotuple `coprodDesc` of the subcode components.
- `interpHom_delta`: at a `δ`-domain, the component at `X` is the
  cotuple `deltaDesc` of the transported subcode components, the
  transport being the composite the Theorem 3 `δ`-case fixes
  (`natCopowerPlusEquiv` backward, the bridge pair, the Lemma 4
  pair — each `equivOfInverseTarget` acts on components as
  composition with a fixed component family, and the
  `natCopowerPlusEquiv` directions carry explicit component
  formulas).

#### Characterization of the injection helpers

For each branch 2a helper, a component equation of the form
"`interpHom` of the helper's output is `interpHom` of its input
composed with an explicit inclusion", proved by the recursion the
helper itself uses:

- `sigmaPush` (by `IR.induction` on the domain, target
  generalized): the inclusion is `coprodInj a'` into
  `⟦σ A' K'⟧ X` (definitionally a coproduct). The `ι`-domain case
  computes `innerHomEquiv` at clause 1B (`rec_mk`) against the
  summand-choice decomposition; the `σ`-domain case is
  `coprodDesc_comp`; the `δ`-domain case pushes the inclusion
  through the Theorem 3 target transports via the Lemma 4
  `σ`-square below.
- The Lemma 4 `σ`-square: `interpPrecompIso` at a `σ`-code
  (`interpPrecompIso_mk`, `precompIsoSigma`) is a `coprodIso`, so
  its forward hom commutes `coprodInj` at a lifted summand with
  `coprodInj` at the summand — a componentwise calculation, not an
  induction.
- `deltaEmptyPush` (same pattern): the inclusion is the copower
  injection at the unique weight out of an empty-name object,
  composed with `deltaInto` at the vacuous assignment. The
  `ι`-domain case computes `innerHomEquiv` at clause 1C; the
  `δ`-domain case uses the Lemma 4 `δ`-square below. A small
  `FreeCoprodCompDisc` addition is expected: hom-extensionality at
  an empty-name domain (the `emptyDesc_unique` argument at an
  arbitrary empty name type), for the weight uniqueness.
- The Lemma 4 `δ`-square: the all-resolved-classifier summand
  inclusion composed with `interpPrecompIso (delta B c)` equals
  `deltaInto` at the merged assignment composed with the
  interpretation image of the coproduct-pair inclusion.
  `precompIsoDelta` is `precompIsoDeltaStrip` (a `coprodIso` over
  classifiers of `coprodIso`s over unresolved assignments) followed
  by `precompIsoDeltaReshuffle` (name-level regrouping whose
  decoding proof is `rfl`), so the square is a name-level
  calculation through `precompMerge_elim`, with the transport
  eliminations in the established `Eq.rec` style.
- `msigmaPush` (by `List.rec`, base `sigmaPush`): the inclusion is
  `coprodInj` at the `mplus`-position, conjugated by `mprecompIso`;
  the cons step is the Lemma 4 `σ`-square.
- `deltaNavBase`: a composite of the `sigmaPush` and
  `deltaEmptyPush` characterizations at the classifier
  `Sum.inl ∘ g`; no new recursion.
- `deltaNav` (by `List.rec` at the general factorization parameter
  `g`, matching its own recursion): the inclusion is the copower
  injection at the weight "`g` followed by the left coproduct-pair
  injection, followed by `mplusInj L` at the coproduct object"
  (the semantic content of the classifier `Sum.inl ∘ g`: every
  direction resolves into the outer superscript through `g`),
  composed with `deltaInto` at `iout ∘ g`, at the
  `mplus`-position, conjugated by `mprecompIso`; the cons step is
  the `msigmaPush` characterization at the all-unresolved
  classifier.

Transports along code equalities (`mprecomp_snoc`,
`mprecomp_iota_mk`) are handled by `interpHom_cast` lemmas in the
manner of branch 2c's `interpMor_cast` (generic `Eq.rec`
eliminations). Three further transports the characterizations must
eliminate, in the same style: the internal
`cast (congrArg … (funext …))` along a direction-assignment
equality inside `deltaEmptyPush` and `deltaNavBase`; and, in the
`ι`-domain cases, `interpHomEquivStep`'s own `Eq.rec` along
`mk_congr` (a general `mk (Sum.inl o) c` is not definitionally
`iota o`). The homset codomain transport `IR.Hom.homOfEq`
deferred by branch 2a's plan is not needed on this route and
remains unbuilt.

#### The identity-image induction

By `IR.induction` on `γ` (the statement is `Prop`-valued), motive
`∀ L X, ((interpHom γ (γ ^^ L) (preUnitStack γ L)).1 X =
preUnitComponent γ L X)`, with `preUnitStack` unfolded one step by
`rec_mk` and `interpHom` by its characterizing equations. Each case
rewrites every cotuple component into the form "inclusion composed
with a common factor" via the helper characterizations, and
collapses by the corresponding cotuple eta law:

- `ι`-case: both interpretations are constant (`interpMor_iota`);
  after transport along `mprecomp_iota_mk`, `interpHom_iota` sends
  the reflexivity witness to `Hom.id`-composites, and
  `preUnitComponent` reduces to `Hom.id` since `interpPrecompIso`
  at an `ι`-code is `Iso.refl` (`precompIsoIota`); transport
  bookkeeping only.
- `σ`-case: `interpHom_sigma` exposes `coprodDesc` of the
  `msigmaPush` characterizations; the `mprecompIso` halves cancel
  by `Iso.invHom_hom`; the `coprodInj_mor` square and
  `interpMor_sigma` commute the injection with the morphism map;
  `coprodDesc_eta` collapses the cotuple to
  `preUnitComponent (σ A K) L X`.
- `δ`-case: `interpHom_delta` exposes `deltaDesc`; per summand
  `i`, `interpHom_cast` eliminates the `mprecomp_snoc` cast, and
  the `deltaNav` characterization (at `g = id`) with the inductive
  hypothesis at `L ++ [⟨B, i⟩]` rewrites the component. The
  per-summand identity — "transported component equals
  `deltaInto i X` composed with `preUnitComponent (delta B c) L X`"
  — reduces by `coprodDesc_eta` to a per-weight identity, which is
  proved by post-composing with `mprecompIso`'s forward hom
  (`eq_comp_invHom`). That post-composition collapses
  `preUnitComponent`'s right-hand side to a bare `interpMor` of
  `mplusInj`, so the `mprecomp_snoc` transport and the Lemma 4
  layer merge into the single tower isomorphism at
  `L ++ [⟨B, i⟩]`, which cancels against the inverse halves inside
  `preUnitComponent` and the navigation inclusion. The residue is
  `deltaInto`/`coprodInj` naturality together with two morphism
  identities on the tower (the iterated injection and the
  navigation weight, both against the bridge morphism carrying
  `plusLiftBridgeInvHom` and the coproduct-pair cotuple).
  `deltaDesc_eta` then collapses the outer cotuple. Merging the
  transports is what makes the case finite: unfolding the tower
  layer by layer and cancelling the Lemma 4 layer separately does
  not terminate against the `mprecomp_snoc` cast.

Closure-gate assessment: every statement is a component equation
between explicit `FreeCoprodCompDisc.Hom` composites; every
recursion mirrors an existing recursion (`preUnitStack`'s and the
helpers' own); the commutation squares are calculations at
`mk`-codes through the `_mk` equations and name-level `Equiv`
composites; transports are `Eq.rec` along given equalities. The
laws consumed — cotuple computation and eta (`coprodInj_desc`,
`coprodDesc_eta`, `coprodDesc_comp`, `coprodInj_mor`,
`deltaInto_desc`, `deltaDesc_eta`, the `coprodPair` lemmas), the
functor laws (`interpMor_id`, `interpMor_comp`), the `_mk`
characterizing equations, and the `Iso` inverse laws — all exist
from branches 1–2c. No step consumes `Classical`; the gate closes.

The gate is discharged by construction, not by assessment alone: a
session prototype realizes every declaration of this subsection at
the universe scheme of § Universe scheme, with `IR.interpHom_id`,
`IR.id_comp`, `IR.comp_id`, and `IR.comp_assoc` each depending on
`propext` and `Quot.sound` only. Two consequences for the plan:
the recursor-computation lemmas require the branch-2a helpers'
step functions to be named declarations (`IR.rec_mk` does not
unify against an inline step lambda), so `Hom.lean` names them in
the manner of `IR.interpMorStep`; and
`FreeCoprodCompDisc.coprodPairInl`/`coprodPairInr` are
universe-generalized as recorded above.

#### Composition and the laws by transfer

- `comp f g := natToHom (NatTrans.vcomp (interpHom f)
  (interpHom g))`.
- `interpHom_comp`: `interpHom (comp f g) = NatTrans.vcomp
  (interpHom f) (interpHom g)` — `interpHom_natToHom` applied to
  the vertical composite; with `interpHom_id` this is the
  functoriality of the interpretation on morphisms.
- `id_comp`, `comp_id`: rewrite by `interpHom_id`, collapse by
  `NatTrans.id_vcomp` / `NatTrans.vcomp_id`, and close by
  `natToHom_interpHom`.
- `comp_assoc`: conjugation by the equivalence —
  `interpHom_natToHom` on both sides and `NatTrans.vcomp_assoc`.

No new induction; the `FreeCoprodCompDisc` additions are limited to
the universe-generalized coproduct-pair injections and the possible
hom-extensionality lemma noted above.

#### Placement (branch 2d)

A `Geb/Mathlib/Data/PFunctor/IndRec/Category.lean` module per the
one-module-per-branch split: the tower constructions, the
characterizing equations of `interpHom`, the helper
characterizations, the identity-image equation, `comp`, and the
laws; the mirrored `GebTests/` module (checking sample names
against the umbrella-wide test namespace before planning) and both
umbrella registrations; `docs/index.md` entries in the same branch.
Its final commits remove the workstream's transient documents per
§ Branch decomposition.

### Semantic statements (branch 1, complete)

Both at the uniform instantiation (`γ : IR.{max uA uB, uB}`,
`i : Q → I`, `Q : Type uB`), with the object-isomorphism notion
absorbing residual index-universe differences between the two
sides. Branch 2c reuses these as the semantic content of Theorem 3:

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
workstreams can extend those sections with morphism uses. The
expanded scope (homset and identity, Theorem 2.4 functoriality,
naturality and Theorem 3, composition and the laws) is large enough
that the narrow-and-deep directory structure favours sibling `IndRec`
modules over a single `IndRec/Basic.lean`; each branch's plan fixes
its file placement (a natural split is one module per branch —
`Hom`, `Functor`, `Naturality`, `Category` — with the `Universes` and
`Container` sections relocated after the morphism development). Module
docstrings (`## Main definitions`,
`## Main statements`, implementation notes) are updated in every
touched file (including `Geb/Mathlib/Logic/Equiv/Basic.lean`,
which receives generic `Equiv` combinators the constructions
factor through); every declaration transcribed from or specified
by the paper cites [HancockMcBrideGhaniMalatestaAltenkirch2013]
per the citation rules, with docstrings distinguishing
transcription from construction. Generic auxiliary machinery
(hom composition, the isomorphism notion, lifting, the `Equiv`
combinators) is the project's own construction, outside the
citation rules' scope. Mirrored test files
under `GebTests/` and the `docs/index.md` entry are updated in
the same branches.

## Branch decomposition

Branch 1 is complete (merged). The remaining work is four
dependency-ordered topic branches, each with its own plan:

- Branch 1 (complete): `FreeCoprodCompDisc` additions, `γ^i`,
  Lemmas 3 and 4.
- Branch 2a: the homset (Definition 8) and the identity. Depends on
  branch 1.
- Branch 2b: Theorem 2.4 functoriality. Depends on branch 1;
  independent of branch 2a.
- Branch 2c: naturality and Theorem 3 (full and faithful). Depends
  on branch 2b.
- A dedicated relocation branch (after 2b): moves the `Universes`
  and `Container` sections of `Basic.lean` into sibling modules
  following the morphism development, discharging the ordering
  requirement of Placement and documentation. Depends on branch 2b
  (which creates the module the sections must follow).
- Branch 2d: composition and the category laws (Corollary 2), by
  transfer. Depends on branches 2a and 2c.

Branches 2a and 2b are independent and may proceed in parallel. The
spec and all branch plans are removed in the final commits of the
last branch (2d), per CONTRIBUTING § Concern shape.

## Constraints

- Constructive discipline: no `noncomputable`, no `Classical`;
  axiom linter passes (`propext`, `Quot.sound` only).
- Recursor-only recursion: all definitions by recursors
  (`IR.elim`/`IR.rec`, and `List.rec` for the branch-2a stack
  helpers); no `induction` tactic, no self-referential `def`,
  no `termination_by`.
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
