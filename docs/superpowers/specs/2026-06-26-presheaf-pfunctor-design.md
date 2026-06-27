# Presheaf polynomial functors (parametric right adjoints): design

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Status](#status)
- [Scope](#scope)
- [Transcription vs novel](#transcription-vs-novel)
- [Background](#background)
  - [The parametric-right-adjoint evaluation formula](#the-parametric-right-adjoint-evaluation-formula)
  - [Reduction to a restriction of `SlicePFunctor`](#reduction-to-a-restriction-of-slicepfunctor)
- [Constructiveness boundary and the allowlist](#constructiveness-boundary-and-the-allowlist)
- [Layer split: `PresheafDomPFunctor` then `PresheafPFunctor`](#layer-split-presheafdompfunctor-then-presheafpfunctor)
- [What data each layer adds](#what-data-each-layer-adds)
- [Constructive core (`Basic.lean`)](#constructive-core-basiclean)
  - [`PresheafDomPFunctor`: operations, lawfulness, bundle](#presheafdompfunctor-operations-lawfulness-bundle)
  - [The arity presheaf as fibres of `s`](#the-arity-presheaf-as-fibres-of-s)
  - [Naturality predicate and `obj`](#naturality-predicate-and-obj)
  - [`PresheafDomPFunctor` morphism map](#presheafdompfunctor-morphism-map)
  - [`PresheafPFunctor`: operations, lawfulness, bundle](#presheafpfunctor-operations-lawfulness-bundle)
  - [Output presheaf structure](#output-presheaf-structure)
- [Categorical wrapper (`Functor.lean`)](#categorical-wrapper-functorlean)
- [Universe posture](#universe-posture)
- [Placement and naming](#placement-and-naming)
- [Reuse inventory](#reuse-inventory)
- [Out of scope (deferred)](#out-of-scope-deferred)
- [Higher-order-constructions tension](#higher-order-constructions-tension)
- [Verification plan](#verification-plan)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Status

Design for review. Spec and plan are transient artifacts removed in
the topic branch's final commits, per `CONTRIBUTING.md` § Concern
shape.

## Scope

Extend the slice polynomial functors
(`Geb/Mathlib/Data/PFunctor/Slice/`) to functors between presheaf
categories. The functors realized are the **parametric right
adjoints** (p.r.a., also "local right adjoints" or "familial"
functors) `Iᵒᵖ ⥤ Type → Jᵒᵖ ⥤ Type`, the presheaf-category
generalization of polynomial functors.

The construction is, throughout, a restriction of mathlib's `PFunctor`
interpretation: each layer is a `PFunctor` value together with added
data and `Prop`s, and each `obj` is a subtype of `PFunctor.Obj`. This
delivers, in two layers parallel to `SliceDomPFunctor`/`SlicePFunctor`:

- `PresheafDomPFunctor` — the restriction layer. A `SliceDomPFunctor`
  over the object type of a source category `I`, plus the restriction
  maps that make each shape's arity a presheaf on `I`, plus the
  naturality predicate. Its action is a functor `(Iᵒᵖ ⥤ Type) ⥤ Type`.
- `PresheafPFunctor` — adds the presheaf-form of codomain tagging. The
  bare tag `t : A → J` of `SlicePFunctor` is upgraded to a presheaf
  `T1` on the target category `J` whose elements are the shapes,
  together with the reindexing of arities along `J`-morphisms. Its
  action is a functor `(Iᵒᵖ ⥤ Type) ⥤ (Jᵒᵖ ⥤ Type)`.

As with the slice work, the choice-free content (structures,
predicates, object/morphism maps, functoriality as plain equalities)
lives in `Basic.lean`; the packaging as `CategoryTheory.Functor`s
between presheaf categories lives in `Functor.lean`, the only module
permitted `Classical.choice`.

The natural-isomorphism validation (that the wrapper functor is the
p.r.a. determined by its generic data, in the sense of the nlab
generic-morphisms characterization) is out of scope and recorded as a
deferred follow-on, mirroring the slice increment C.

## Transcription vs novel

Per `CONTRIBUTING.md` § Submission policy, each definition is marked
transcription or novel.

- **Transcription** (the mathematical interface, from Weber 2007 and
  the nlab parametric-right-adjoint page): the parametric-right-adjoint
  functor, its evaluation formula
  `T(Z)(j) = ∐_{x ∈ T1(j)} [Iᵒᵖ, Set](E_T(x), Z)`, and its determining
  data `(T1, E_T : el(T1)ᵒᵖ → [Iᵒᵖ, Set])`. The realized object,
  theorem set (it is a functor between presheaf categories), and the
  arity/shape/reindexing interface are fixed by these sources.
- **Novel** (the Lean encoding, this project): representing the functor
  as a restriction of mathlib's `PFunctor` interpretation — the
  operations/laws/bundle triad at each layer (`PresheafDomPFunctorData`
  / `.IsFunctorial` / `PresheafDomPFunctor`, and `PresheafPFunctorData`
  / `.IsFunctorial` / `PresheafPFunctor`), `IsNatural`, `obj`,
  `objPresheaf`, the named fibre predicates and types
  `SliceDomPFunctor.PositionOver` / `Position` and
  `SlicePFunctor.ShapeOver` / `Shape`, the named law conditions
  (`RestrId` / `RestrComp` / `TagRestrId` / `TagRestrComp` /
  `ReindexNaturality` / `ReindexId` / `ReindexComp`), and the option-(A)
  representation of each arity `E_T(a)` as fibres of the constraint leg
  `s` (rather than a stored presheaf), with `restr` / `tagRestr` /
  `reindex` as raw position/shape reindexing. This encoding is an
  implementation choice; the same mathematical object admits other
  encodings.

## Background

The project's polynomial-functors survey records that mathlib has no
polynomial functors between presheaf categories and no parametric
right adjoints. The slice work (`Geb/Mathlib/Data/PFunctor/Slice/`)
provides polynomial functors `Type/I → Type/J` as restrictions of
`PFunctor`. This branch lifts that one categorical level: from slices
of `Type` to presheaf categories.

### The parametric-right-adjoint evaluation formula

A functor `T : C → D` is a parametric right adjoint when its
factorization `C → D/T1 → D` through the slice over `T1 := T(1)` (`1`
terminal in `C`) has a right-adjoint first leg. For presheaf
categories `T : [Iᵒᵖ, Set] → [Jᵒᵖ, Set]`, the nlab
"parametric right adjoint" page (generic-morphisms section) gives the
evaluation formula verbatim:

```text
T(Z)(j) = ∐_{x ∈ T1(j)} [Iᵒᵖ, Set](E_T(x), Z)
```

and states that such a `T` "is completely determined by providing
`T1 ∈ [Jᵒᵖ, Set]` together with the functor
`E_T : el(T1)ᵒᵖ → [Iᵒᵖ, Set]`." Here `T1` is the presheaf of shapes on
`J`, `el(T1)` its category of elements, and `E_T(x)` the arity
presheaf on `I` of the shape `x`. The hom-set
`[Iᵒᵖ, Set](E_T(x), Z)` is a set of natural transformations: the
formula is a coproduct of natural transformations, indexed by the
shapes lying over `j`.

p.r.a. functors preserve connected limits (the slice projection
creates them); this is the structural reason the construction is
polynomial-like.

### Reduction to a restriction of `SlicePFunctor`

The object-map of a presheaf `Z` on `I` is exactly an object of the
slice `Type/I₀` (its total space `Σ i, Z(i)` over the object set
`I₀`), and a natural transformation `E_T(x) → Z` is exactly a slice
morphism on object-maps together with a naturality `Prop`. Therefore:

- `SlicePFunctor I J` already computes
  `∐_{x : t x = j} SliceHom(E_T(x)_obj, Z_obj)` — the coproduct of
  slice morphisms, tagged into `J` by `t`. Its `obj` is the
  `Compatible` subtype of `PFunctor.Obj`, tagged by `t`.
- `PresheafPFunctor.obj` is the further subtype cut out by naturality,
  turning each slice morphism into an actual natural transformation.
  This is precisely the p.r.a. evaluation formula.

So `PresheafPFunctor` is a restriction of `SlicePFunctor`, exactly as
`SlicePFunctor` is a restriction (plus tag) of `PFunctor`. Two kinds
of morphism data are added, on the two sides:

- **`I`-side (input).** The morphisms of `I` restrict each hom-set
  `SliceHom(E_T(x), Z)` to its natural members. The added datum `restr`
  is the presheaf structure on the arities (functorial data, not a mere
  restriction),
  but it enters the codomain only as a restriction, and the layer's
  functoriality in `Z` uses only the input morphism's naturality. This
  is the `PresheafDomPFunctor` layer.
- **`J`-side (output).** The morphisms of `J`, via `T1`'s restriction
  maps and `E_T`'s functoriality over `el(T1)`, supply the restriction
  maps of the output presheaf `T(Z)`. Genuine functorial data; this is
  the presheaf-form tagging of the `PresheafPFunctor` layer.

## Constructiveness boundary and the allowlist

The relevant axiom facts were verified this session with
`#print axioms` against the repository pin (toolchain `v4.32.0-rc1`):

- The category-theory data is axiom-free: `CategoryTheory.Functor`
  and `CategoryTheory.Category` "do not depend on any axioms".
- Reading a presheaf object through its projections is choice-free: a
  function reading `Z.obj` reports `[propext]`; reading `Z.map`, and a
  naturality `Prop` stated through `Z.map`, report
  `[propext, Quot.sound]` — within the strict permitted set.
- Naming a presheaf-category morphism taints: a declaration whose
  signature names `Z ⟶ Z'` (the functor-category hom), or that uses
  `𝟙`/`≫` on presheaves, or `CategoryTheory.NatTrans.id` /
  `CategoryTheory.NatTrans.vcomp`, reports
  `[propext, Classical.choice, Quot.sound]` — verified this session.
  The hom and identity/composite resolve through the
  `CategoryTheory.Functor.category` instance, whose law fields are
  discharged with choice-using automation.
- The bare `NatTrans` structure is choice-free: a declaration taking
  `α : CategoryTheory.NatTrans Z Z'` (the structure, which needs only
  `[Category I]`, not the functor-category instance) and projecting
  `α.app`/`α.naturality` reports `[propext, Quot.sound]`; a hand-built
  identity natural transformation (`app := 𝟙 (Z.obj _)` in `Type`)
  reports `[propext]`. `CategoryTheory.Functor` and
  `CategoryTheory.Category` themselves depend on no axioms.
- Building a presheaf value is choice-free: a `Iᵒᵖ ⥤ Type` (or
  `Jᵒᵖ ⥤ Type`) constructed with explicit `map_id`/`map_comp` reports
  `{propext, Quot.sound}` (within the strict permitted set); the
  opposite-category instance `Category Iᵒᵖ` reports `[propext]`, and the
  operations-only `CategoryTheory.Prefunctor` is likewise within the
  strict set.
- Building a functor between presheaf categories taints even with all
  laws explicit: `(Iᵒᵖ ⥤ Type) ⥤ (Jᵒᵖ ⥤ Type)` reports
  `[propext, Classical.choice, Quot.sound]`, because the
  functor-category instance is required on its source and target; so
  does `CategoryTheory.Functor.comp`. The three-layer bundle
  constructor `PresheafPFunctor.mk` is, by contrast, axiom-free.

So the taint is not in building presheaves but in being a functor whose
source or target is a functor category. Consequently the core can: take
input presheaves `Iᵒᵖ ⥤ Type` as objects and project `.obj`/`.map`;
take input morphisms as the bare `NatTrans Z Z'` (not `Z ⟶ Z'`) and
hand-build the identity/composite its laws need (never `NatTrans.id` /
`NatTrans.vcomp` / `𝟙` / `≫` on the functor category); and build the
output presheaf `objPresheaf Z : Jᵒᵖ ⥤ Type` as a real value,
its `map_id`/`map_comp` discharged from the `isFunctorial` laws. All of
that is certified `Classical.choice`-free by the strict linter.
`Classical.choice` enters only in `Functor.lean`, and only at the final
upgrade of the maps to the categorical functor
`(Iᵒᵖ ⥤ Type) ⥤ (Jᵒᵖ ⥤ Type)` (whose source/target are functor
categories), together with converting the input hom `Z ⟶ Z'` to
`NatTrans Z Z'` (definitional). That module is added to
`GebMeta.classicalAllowedModules`, exactly as `Slice/Functor` is.

This is a sharper boundary than the slice work drew: there, `Basic`
avoided `CategoryTheory` entirely and took a raw `p : X → dom`. Here the
core reuses mathlib's `Category`/`Functor`/`NatTrans` as data — objects,
the bare transformation structure, and assembled presheaf values — and
only the functor-into-or-out-of-a-functor-category step is quarantined.
The boundary falls at "be a functor whose source or target is a functor
category", not at "name category theory".

## Layer split: `PresheafDomPFunctor` then `PresheafPFunctor`

Parallel to `SliceDomPFunctor → SlicePFunctor`:

| Slice layer | functor | Presheaf parallel | functor |
| --- | --- | --- | --- |
| `SliceDomPFunctor I` (leg `s`) | `Over I ⥤ Type` | `PresheafDomPFunctor I` (`I`-naturality) | `(Iᵒᵖ ⥤ Type) ⥤ Type` |
| `SlicePFunctor I J` (add tag `t`) | `Over I ⥤ Over J` | `PresheafPFunctor I J` (add `T1`/`E_T` over `J`) | `(Iᵒᵖ ⥤ Type) ⥤ (Jᵒᵖ ⥤ Type)` |

`PresheafDomPFunctor` is the untagged restriction layer;
`PresheafPFunctor` adds codomain presheaf-tagging.

## What data each layer adds

Each row adds data and `Prop`s to the row above; `obj` is a subtype of
`PFunctor.Obj` throughout. For each presheaf layer the "Added data"
column is an operations `…Data` structure and the "Added `Prop`s"
column a `Prop`-valued `IsFunctorial` structure over it, joined by a
bundle (see Constructive core).

| Layer | Added data | Added `Prop`s |
| --- | --- | --- |
| `PFunctor` (mathlib) | `A`, `B` | — |
| `SliceDomPFunctor I` | `s : Idx → I` | `Compatible` (in `obj`) |
| `PresheafDomPFunctor I` | `restr` (arity restriction over `I`) | `restr` presheaf laws; `IsNatural` (in `obj`) |
| `PresheafPFunctor I J` | `t : A → J`; `tagRestr` (`T1` restriction over `J`); `reindex` (`E_T` functoriality) | `tagRestr` presheaf laws; `reindex` naturality + functor laws |

## Constructive core (`Basic.lean`)

Snippets elide the `module`/`public import`/`public section`
boilerplate and the universe declarations. The fibre-and-cast
mechanics noted below are the main proof-engineering cost of option
(A) (arities as fibres of `s`) and are pinned exactly in the
implementation plan, not here; the slice spec deferred its tactic
forms identically.

### `PresheafDomPFunctor`: operations, lawfulness, bundle

Each presheaf layer is built in three steps, mirroring mathlib's
`Functor`/`LawfulFunctor` separation and the project's structure /
typeclass pattern: an operations `…Data` structure carrying the raw
data, a `Prop`-valued `IsFunctorial` structure depending on it carrying
the laws, and a bundle joining the two. This unbundles computations
(`obj`/`map`, definable from the operations alone) from theorems
(functoriality; "the output is a presheaf") that need the laws. The
skeleton and the bundle's choice-freedom (`PresheafDomPFunctor.mk`
axiom-free) were verified this session. (`Position`/`Shape` are defined
in the next subsection.)

```lean
-- operations
structure PresheafDomPFunctorData (I : Type uI) [Category I]
    extends SliceDomPFunctor I where
  restr : ∀ (a : toPFunctor.A) ⦃i i' : I⦄ (f : i' ⟶ i),
      toSliceDomPFunctor.Position a i → toSliceDomPFunctor.Position a i'

-- each law is a named Prop, so a caller can state `: F.RestrComp`
-- rather than restate the condition
def PresheafDomPFunctorData.RestrId {I : Type uI} [Category I]
    (F : PresheafDomPFunctorData I) : Prop :=
  ∀ (a : F.A) (i : I), F.restr a (𝟙 i) = id
def PresheafDomPFunctorData.RestrComp {I : Type uI} [Category I]
    (F : PresheafDomPFunctorData I) : Prop :=
  ∀ (a : F.A) ⦃i i' i'' : I⦄ (f : i' ⟶ i) (g : i'' ⟶ i'),
      F.restr a (g ≫ f) = F.restr a g ∘ F.restr a f

-- laws: a Prop-valued structure bundling the named conditions
structure PresheafDomPFunctorData.IsFunctorial {I : Type uI} [Category I]
    (F : PresheafDomPFunctorData I) : Prop where
  restr_id : F.RestrId
  restr_comp : F.RestrComp

-- bundle: operations together with a proof they are functorial
structure PresheafDomPFunctor (I : Type uI) [Category I]
    extends PresheafDomPFunctorData I where
  isFunctorial : toPresheafDomPFunctorData.IsFunctorial
```

The operations reuse `SliceDomPFunctor I` (so `A`, `B`, `s`) verbatim,
with `dom := I` the object type of the source category; `restr` is the
only added datum, the contravariant action of `I` on positions, fibre
by fibre. `restr_id`/`restr_comp` are exactly the functoriality of each
arity presheaf `E_T(a)`.

### The arity presheaf as fibres of `s`

The repeated fibre `{ b : B a // s ⟨a, b⟩ = i }` — the positions of
shape `a` whose constraint-leg image is `i` — is factored exactly as
`SlicePFunctor` factors its `obj` condition through the named
`Compatible`: the fibre condition is a named, point-free `Prop`
predicate, and the fibre type is its `Subtype`. Both live in
`Slice/Basic.lean` (mathlib has no fitting named type: `Function.Fiber`
is the fibre-partition index, and `s ⁻¹' {i}` is a `Set`, not the
subtype):

```lean
-- the constraint-leg condition, point-free, as a predicate on positions
@[expose] def SliceDomPFunctor.PositionOver {dom : Type uD}
    (F : SliceDomPFunctor.{uA, uB} dom) (a : F.A) (i : dom) : F.B a → Prop :=
  (· = i) ∘ F.sCurried a
@[expose] def SliceDomPFunctor.Position {dom : Type uD}
    (F : SliceDomPFunctor.{uA, uB} dom) (a : F.A) (i : dom) : Type uB :=
  Subtype (F.PositionOver a i)
```

Verified this session: `Position a i` is definitionally
`{ b : F.B a // F.s ⟨a, b⟩ = i }` (`rfl`) and
`PositionOver a i b ↔ F.s ⟨a, b⟩ = i` is `Iff.rfl`, so the fields using
`Position` are unaffected and a caller can name the condition
(`F.PositionOver a i`) to state things of the same fibre type.
`@[expose]` (matching `obj`/`map`/`sCurried`) lets both unfold across
the module boundary. For a shape `a`, the arity presheaf
`E_T(a) : Iᵒᵖ ⥤ Type` has object-map `i ↦ F.Position a i` and
restriction map `restr a`. This is option (A): the arity is not stored
as a separate `Iᵒᵖ ⥤ Type` field but recovered from the existing
`B`/`s`, keeping each layer a `PFunctor` value plus data and `Prop`s.
The cost is fibre membership proofs and casts (over the `PositionOver`
equality) in the naturality and reindexing statements.

The codomain fibre `{ a : A // t a = j }` — the shapes lying over `j`,
i.e. the object-map of the shape presheaf `T1` — is factored
symmetrically on `SlicePFunctor`, also in `Slice/Basic.lean`:

```lean
@[expose] def SlicePFunctor.ShapeOver {dom : Type uD} {cod : Type uC}
    (F : SlicePFunctor.{uA, uB, uD, uC} dom cod) (j : cod) : F.A → Prop :=
  (· = j) ∘ F.t
@[expose] def SlicePFunctor.Shape {dom : Type uD} {cod : Type uC}
    (F : SlicePFunctor.{uA, uB, uD, uC} dom cod) (j : cod) : Type uA :=
  Subtype (F.ShapeOver j)
```

So `tagRestr : ∀ ⦃j j'⦄ (g : j' ⟶ j), F.Shape j → F.Shape j'`, and
neither raw fibre subtype appears in the structure fields.

### Naturality predicate and `obj`

For an input presheaf `Z : Iᵒᵖ ⥤ Type` write `p_Z : (Σ i, Z.obj ⟨i⟩) → I`
for the total-space projection (`⟨i⟩` is `Opposite.op i`). An element
`x : F.toSliceDomPFunctor.obj p_Z` is `⟨⟨a, v⟩, hx⟩` with
`v : F.B a → Σ i, Z.obj ⟨i⟩` and `hx : Compatible` placing `v b` in the
fibre over `s ⟨a, b⟩`. `v` is the object-map component of a candidate
natural transformation `E_T(a) → Z`; the naturality predicate asserts
it commutes with `restr a` and `Z.map`:

`IsNatural` and `obj` are computations: they need only the operations
`PresheafDomPFunctorData`, not the laws.

```lean
def PresheafDomPFunctorData.IsNatural (F : PresheafDomPFunctorData I)
    {Z : Iᵒᵖ ⥤ Type} (x : F.toSliceDomPFunctor.obj p_Z) : Prop
-- pointwise: for f : i' ⟶ i and b : F.Position a i,
--   v (restr a f b) = Z.map f.op (v b)   (modulo the Position-index casts)

@[expose] def PresheafDomPFunctorData.obj (F : PresheafDomPFunctorData I)
    (Z : Iᵒᵖ ⥤ Type) : Type _ :=
  { x : F.toSliceDomPFunctor.obj p_Z // F.IsNatural x }
```

`obj Z` is a subtype of `SliceDomPFunctor.obj`, itself a subtype of
`PFunctor.Obj`; the chain `PFunctor.Obj ⊇ Compatible ⊇ IsNatural` is
the slice-then-presheaf restriction made literal. `IsNatural` is stated
through `Z.map` and `restr`, so it stays in `{propext, Quot.sound}`.

### `PresheafDomPFunctor` morphism map

Also a computation on the operations layer. A morphism of input
presheaves is taken as the bare structure `α : NatTrans Z Z'` (not
`Z ⟶ Z'`, which would taint — see Constructiveness boundary). It
induces `f_α : (Σ i, Z.obj ⟨i⟩) → (Σ i, Z'.obj ⟨i⟩)`,
`⟨i, z⟩ ↦ ⟨i, α.app ⟨i⟩ z⟩`, with `p_{Z'} ∘ f_α = p_Z`.
`PresheafDomPFunctorData.map α` is `SliceDomPFunctor.map f_α` restricted
to the `IsNatural` subtype; `IsNatural` is preserved because
`α.naturality` (a projection, choice-free to use) intertwines `Z.map`
and `Z'.map` — no `restr` law is needed. `map_id`/`map_comp` (the
functoriality of the dom functor in `Z`) are likewise on the operations
layer: stated against a hand-built identity transformation
(`app := 𝟙 (Z.obj _)` in `Type`) and a hand-built vertical composite
(never `NatTrans.id` / `NatTrans.vcomp`, which taint), delegating to the
slice-side lemmas plus subtype extensionality, mirroring `SlicePFunctor`.
These naturality proofs must use the raw `α.naturality` projection
(via `congrArg (ConcreteCategory.hom ·)`), not the `Classical.choice`-
tainted `_apply` convenience lemmas (`NatTrans.naturality_apply`,
`ConcreteCategory` `_apply`); choice-free forms exist (verified this
session) and the strict `Basic.lean` lint gate catches any slip. The
wrapper converts `Z ⟶ Z'` to `NatTrans Z Z'` (definitional) when
packaging the functor.

### `PresheafPFunctor`: operations, lawfulness, bundle

Same three-step shape. The operations `…Data` carries the diamond —
both `PresheafDomPFunctorData` and `SlicePFunctor` extend
`SliceDomPFunctor I`, verified this session to merge (the shared parent
is one value; `t`, `restr`, `s`, `toPFunctor` all project from it). The
`IsFunctorial` structure extends the dom-level one across the diamond
(also verified) with the `J`-side laws.

```lean
-- operations (the diamond)
structure PresheafPFunctorData (I : Type uI) [Category I]
    (J : Type uJ) [Category J]
    extends PresheafDomPFunctorData I, SlicePFunctor I J where
  tagRestr : ∀ ⦃j j' : J⦄ (g : j' ⟶ j),
      toSlicePFunctor.Shape j → toSlicePFunctor.Shape j'
  reindex : ∀ ⦃j j' : J⦄ (g : j' ⟶ j) (a : toSlicePFunctor.Shape j) ⦃i : I⦄,
      toSliceDomPFunctor.Position (tagRestr g a).1 i →
        toSliceDomPFunctor.Position a.1 i

-- the J-side laws, each a named Prop (so a caller can state, e.g.,
-- `: F.ReindexComp` rather than restate the transport-laden condition)
def PresheafPFunctorData.TagRestrId {I : Type uI} [Category I]
    {J : Type uJ} [Category J] (F : PresheafPFunctorData I J) : Prop :=
  ∀ (j : J), F.tagRestr (𝟙 j) = id
def PresheafPFunctorData.TagRestrComp {I : Type uI} [Category I]
    {J : Type uJ} [Category J] (F : PresheafPFunctorData I J) : Prop :=
  ∀ ⦃j j' j'' : J⦄ (g : j' ⟶ j) (h : j'' ⟶ j'),
      F.tagRestr (h ≫ g) = F.tagRestr h ∘ F.tagRestr g
-- `ReindexNaturality` (commutes with `restr`), `ReindexId`, and
-- `ReindexComp` (the last carrying the `Eq.mpr` transport over
-- `TagRestrComp`) are named the same way; their statements are pinned
-- in the plan.

-- laws: extends the dom-level IsFunctorial with the named J-side laws
structure PresheafPFunctorData.IsFunctorial {I : Type uI} [Category I]
    {J : Type uJ} [Category J] (F : PresheafPFunctorData I J) : Prop
    extends F.toPresheafDomPFunctorData.IsFunctorial where
  tagRestr_id : F.TagRestrId
  tagRestr_comp : F.TagRestrComp
  reindex_naturality : F.ReindexNaturality
  reindex_id : F.ReindexId
  reindex_comp : F.ReindexComp

-- bundle
structure PresheafPFunctor (I : Type uI) [Category I]
    (J : Type uJ) [Category J]
    extends PresheafPFunctorData I J where
  isFunctorial : toPresheafPFunctorData.IsFunctorial
```

`t : A → J` (inherited from `SlicePFunctor`) is the object-map of the
shape presheaf `T1`, whose object-map is `j ↦ F.Shape j` and
restriction `tagRestr`. `reindex` is the action of `E_T` on the
morphisms of `el(T1)`: for `g : j' ⟶ j` and a shape `a` over `j`, a
presheaf morphism from the arity of the reindexed shape to the arity
of `a`. Its naturality and functor laws are added `Prop` fields. This
is the presheaf-form of the bare tag `t`: upgrading `A`-over-`J` to a
`J`-presheaf together with the arity reindexing.

The direction `E_T(tagRestr g a) ⟶ E_T(a)` is confirmed two ways, which
agree: (i) the output presheaf law — `T(Z)(g)` sends
`(a, φ : E_T(a) ⟹ Z) ↦ (tagRestr g a, φ ∘ reindex g a)`, forcing
`reindex g a : E_T(tagRestr g a) ⟶ E_T(a)`; and (ii) variance
bookkeeping — in `el(T1)` (the comma category `y/T1`, on which
`E_T : el(T1)ᵒᵖ → [Iᵒᵖ, Set]` is covariant) the morphism induced by
`g : j' ⟶ j` runs `(j', tagRestr g a) → (j, a)`, so covariant `E_T`
yields the same arrow. The law serves as an independent check on the
implementation. `reindex_comp` is the one law dependently ill-typed
without a transport: for `g : j' ⟶ j` and `h : j'' ⟶ j'` it equates
`reindex (h ≫ g) a` with `reindex g a ∘ reindex h (tagRestr g a)`,
whose source `E_T(tagRestr (h ≫ g) a)` equals
`E_T(tagRestr h (tagRestr g a))` only propositionally (via
`tagRestr_comp`), so it carries an `Eq.mpr`/`▸` over `tagRestr_comp`
(outer factor the `g` leg). `reindex_naturality` and the option-(A)
fibre casts (over `PositionOver`) are ordinary and carry no such
transport. The `reindex_comp` transport is the highest-effort proof
item, pinned in the implementation plan.

### Output presheaf structure

A presheaf value is choice-free to build (a `Jᵒᵖ ⥤ Type` with explicit
laws reports `{propext, Quot.sound}`, within the strict set; verified
this session), so the core builds the output presheaf rather than
exposing loose data:

```lean
@[expose] def PresheafPFunctor.objPresheaf (F : PresheafPFunctor I J)
    (Z : Iᵒᵖ ⥤ Type) : Jᵒᵖ ⥤ Type
-- obj ⟨j⟩ := { z : F.toPresheafPFunctorData.obj Z // F.t z.shape = j }
-- map g   := reindex-precomposition, lying over `tagRestr g`
-- map_id, map_comp : discharged from F.isFunctorial (tagRestr/reindex laws)
```

`objPresheaf Z` reuses mathlib's `Functor` as its output type; its
`map_id`/`map_comp` are the output presheaf's lawfulness, discharged
from `F.isFunctorial`. It therefore lives on the bundle (it needs the
laws), whereas the untagged `obj`/`map` stay on the operations layer
(`…Data`). The shape `z.shape` is the underlying `PFunctor` shape, so
the `t`-fibre `{ z // t z.shape = j }` reuses the `Shape`/tag data.
Building one presheaf value is choice-free (only `Category Jᵒᵖ` and
`Category Type`, both clean); only upgrading the family
`Z ↦ objPresheaf Z` to a categorical functor needs the allowlist (its
source/target are functor categories — `F0` above reports
`Classical.choice`). The morphism action `objPresheaf` is natural in
`Z` via the operations-layer `map`, an added lemma.

## Categorical wrapper (`Functor.lean`)

The wrapper is now thin: the output presheaf is already built in the
core (`objPresheaf`), so all that remains is to upgrade the
object/morphism maps to functors whose source/target are functor
categories. That upgrade is the only `Classical.choice`-tainted step
(verified: `F0`, a functor between presheaf categories with explicit
laws, reports `Classical.choice`), so this module is allowlisted.

- `PresheafDomPFunctorData.domFunctor : (Iᵒᵖ ⥤ Type) ⥤ Type`, obj/map
  the operations `obj`/`map`, laws from `map_id`/`map_comp` (no `restr`
  law needed — it takes the operations, not the bundle).
- `PresheafPFunctor.functor : (Iᵒᵖ ⥤ Type) ⥤ (Jᵒᵖ ⥤ Type)`,
  `obj Z := F.objPresheaf Z` (the core presheaf), and on `α : Z ⟶ Z'`
  the operations `map` applied to the converted `NatTrans Z Z'`.
- Bridge lemmas `functor_obj`/`functor_map` stating the categorical
  maps are definitionally the core maps (`functor.obj Z = objPresheaf Z`
  as `rfl`, via `@[expose]`).

Unlike the slice wrapper, there is no `Functor.toOver` shortcut: the
target is a presheaf category, not an `Over` category. mathlib has no
helper that builds a p.r.a. presheaf functor from `(T1, E_T)`
(leansearch / loogle surface only adjoint and `Functor.pi` /
`mapPresheaf` machinery, none applicable), so the functor is assembled
directly. Two assembly routes are weighed in the plan: (i) direct, from
`objPresheaf` plus the morphism map; (ii) `CategoryTheory.curry` on a
bifunctor `((Iᵒᵖ ⥤ Type) × Jᵒᵖ) ⥤ Type`, discharging fewer hand-rolled
laws (favoured by `docs/rules/lean-coding.md` § Higher-order
constructions). A Kan-extension packaging exists abstractly but pulls
heavier machinery for no lasting return here. Whichever route, only this
categorical-upgrade step is in the allowlisted layer.

## Universe posture

Attempt maximal polymorphism: `[Category.{vI, uI} I]`,
`[Category.{vJ, uJ} J]`, input presheaves into `Type uZ`, and
`PFunctor.{uA, uB}`. As in the slice work, the presheaf-category and
subtype constraints couple these levels; the exact maximal-polymorphic
signature is an attempt, with a uniform-universe fallback
(`I J : Type u`, `Category.{u} I`, presheaves into `Type u`,
`PFunctor.{u, u}`) as the verified baseline. The feasibility sketch
compiled this session used `I J : Type` with `Category.{u_1, 0}` and
deferred universes; the plan settles the signature one definition at a
time, removing unused `universe`/`variable` declarations and applying
the `checkUnivs`/`nolint` treatment already used in `Slice/Basic.lean`.

The inheritance diamond (on the operations structures) merges its
shared `SliceDomPFunctor` parent only if both parents pin that parent's
universes identically in their `extends` clauses
(`PresheafDomPFunctorData` via `extends SliceDomPFunctor.{uA, uB} I`,
and `PresheafPFunctorData` via
`extends PresheafDomPFunctorData.{uA, uB} I, SlicePFunctor.{uA, uB} I J`);
unpinned parents auto-bind fresh `u_N` levels and the merge fails. This
is `docs/rules/lean-coding.md` § "Pin parent universes in `extends`",
verified this session to be load-bearing for the merge.

## Placement and naming

Mirror the slice lineage exactly:

- `Geb/Mathlib/Data/PFunctor/Presheaf/Basic.lean` (constructive core:
  the operations/laws/bundle structures for both layers, the maps, and
  `objPresheaf`), extracting to
  `Mathlib/Data/PFunctor/Presheaf/Basic.lean`.
- `Geb/Mathlib/Data/PFunctor/Presheaf/Functor.lean` (categorical
  wrapper); its module
  `Geb.Mathlib.Data.PFunctor.Presheaf.Functor` is added to
  `GebMeta.classicalAllowedModules`.
- Directory-index file `Geb/Mathlib/Data/PFunctor/Presheaf.lean`
  (`public import`-ing `Basic` and `Functor`), and the
  `…/Data/PFunctor.lean` index updated to import it.
- Additions to the slice substrate, in service of the presheaf work:
  the named fibre predicates `SliceDomPFunctor.PositionOver` /
  `SlicePFunctor.ShapeOver` and their `Subtype`s `Position` / `Shape`,
  added to the existing `Slice/Basic.lean` as companions to `sCurried`
  and `Compatible`; the slice tests gain small `example`s exercising
  them. They are slice-level concepts (the fibres of the `s` and `t`
  legs), so `Slice/Basic.lean` is their proper home and the additions
  land as the topic branch's first commits, ahead of the presheaf
  content that consumes them; the new tests give them local use, so an
  independently-extracted slice PR carries no dead API.
- Mirrored test modules under
  `GebTests/Mathlib/Data/PFunctor/Presheaf/`.
- `docs/index.md` entry for the new concept, same branch; `TODO.md`
  "Next up" entry removed and any follow-ons recorded.

The Lean declarations introduced (no `Geb` prefix) are, per layer, the
operations `…Data`, the named law `Prop`s it carries, the `Prop`-valued
`…Data.IsFunctorial` bundling them, and the bundle:
`PresheafDomPFunctorData` (with `RestrId` / `RestrComp`),
`PresheafDomPFunctorData.IsFunctorial`, `PresheafDomPFunctor`;
`PresheafPFunctorData` (with `TagRestrId` / `TagRestrComp` /
`ReindexNaturality` / `ReindexId` / `ReindexComp`),
`PresheafPFunctorData.IsFunctorial`, `PresheafPFunctor`; plus the
substrate fibre predicates/types `SliceDomPFunctor.PositionOver` /
`Position` and `SlicePFunctor.ShapeOver` / `Shape`. The self-prefix
`Geb.Mathlib.` appears only in `import` lines. Module docstrings carry
the mathlib sections in order, the wrapper's notes recording the
allowlist entry and the absence of a `toOver` shortcut, `Basic`'s
recording the choice-free core, the operations/laws/bundle split, and
the fibre-encoding of arities.

## Reuse inventory

Axiom facts verified this session via `#print axioms` (see
Constructiveness boundary). mathlib API names to re-verify against the
pin during planning:

- `PFunctor.Obj`, `PFunctor.Idx`, `PFunctor.map`, and the
  `LawfulFunctor (PFunctor.Obj P)` instance — reused through the
  inherited `SliceDomPFunctor`.
- `Geb.Mathlib.Data.PFunctor.Slice.Basic` — `SliceDomPFunctor`,
  `SlicePFunctor`, `Compatible`, `obj`, `map`, `map_fst`, `map_id`,
  `map_comp` (the substrate this branch restricts), plus the new
  `SliceDomPFunctor.Position` / `SlicePFunctor.Shape`.
- `Function.Fiber` (`Mathlib.Logic.Function.FiberPartition`) — checked
  and rejected: it is the fibre-partition index type (elements coerce
  to `Set`), not the subtype over a chosen point, so `Position` is
  defined here rather than reused.
- `CategoryTheory.Category`, `CategoryTheory.Functor`,
  `CategoryTheory.NatTrans` (`.app`, `.naturality` projections),
  `Opposite`/`Opposite.op`, `Functor.op`, the presheaf-category
  notation `Iᵒᵖ ⥤ Type`, and `Functor.comp`/evaluation for the
  wrapper. The output presheaf reuses `Functor` as a value (its
  `map_id`/`map_comp` are the output's lawfulness).
- Operations/laws abstractions assessed: `CategoryTheory.Prefunctor`
  (ops-only functor) is choice-free and available, but option (A) keeps
  arities as fibres of `s`, so `restr` stays a raw field. `LawfulFunctor`
  is for `Type → Type` functors and `CategoryStruct`/`Category` for
  hom-composition; neither fits a presheaf's `map` action, so the
  `IsFunctorial` laws are stated directly (shaped like
  `Functor.map_id`/`map_comp`).
- `GebMeta.classicalAllowedModules` (`GebMeta.lean`) — the wrapper
  module is appended here.

## Out of scope (deferred)

- **Natural-isomorphism validation.** That `functor` is the p.r.a.
  determined by `(T1, E_T)` per the nlab generic-morphisms
  characterization — the presheaf analogue of the slice increment C
  (`Σ_t ∘ Π_f ∘ Δ_s`). Lives in the allowlisted layer; recorded as a
  `TODO.md` follow-on.
- **Slice and presheaf W-types** as subtypes of mathlib's `PFunctor.W`,
  cut by the `Compatible`/`IsNatural` predicates. The subtype
  discipline is what makes these reductions clean; separate branch.
- **Free monads** over the presheaf polynomial functors, as
  restrictions/tags of cslib's free-monad construction. Separate
  branch; requires re-verifying cslib's API against the pin.

## Higher-order-constructions tension

`docs/rules/lean-coding.md` § Higher-order constructions prefers
functors built by composition over hand-rolled maps and law proofs.
The split makes the trade explicit, as in the slice work:

- The core maps and their functoriality are hand-rolled plain
  functions and lemmas — necessarily, since the compositional route
  (assembling `Iᵒᵖ ⥤ Type` functors) pulls `Classical.choice`. The
  hand-rolling is minimized by reusing the inherited `SliceDomPFunctor`
  maps and `PFunctor`'s `LawfulFunctor` lemmas; the bespoke content is
  `restr`/`reindex` and the naturality/reindexing reasoning.
- The wrapper assembles the presheaf functor directly. Lacking a
  `Functor.toOver` analogue, it carries more plumbing than the slice
  wrapper (the `curry` route above can reduce it), but stays in the
  allowlisted layer.

The `J`-side coherence (`tagRestr`/`reindex` and their laws) is the
highest-effort part: it earns "the output is a presheaf and
`T` a functor". The implementation builds it one definition
at a time, and the wrapper compiling against the core is positive
evidence the law set is complete.

## Verification plan

- `Basic.lean` (core) passes `lake lint` under the strict
  `{propext, Quot.sound}` set: its module is NOT on
  `classicalAllowedModules`, so a green run positively certifies the
  core is `Classical.choice`-free. A regression pulling a constructed
  functor into `Basic` would fail CI.
- `Functor.lean` (wrapper): module added to
  `classicalAllowedModules`; `lake lint` then passes with only
  `Classical.choice` additionally permitted.
- Mirrored test modules: a concrete small `PresheafPFunctor` (a source
  and target category with a couple of objects and a non-identity
  morphism, so naturality and reindexing are exercised, not
  collapsed), checking the core `obj`/`map`, the naturality
  restriction, the output restriction maps, and the wrapper
  `functor`/bridge lemmas. Computes; no `Classical`, no
  `noncomputable`.
- `lake build`, `lake test`, `lake lint`, `lake lint -- GebTests`,
  `lake shake`, `scripts/lint-imports.sh`, `markdownlint-cli2` +
  `doctoc` on touched Markdown. Pre-push checklist with line-by-line
  review before any push.

## References

- nlab, *parametric right adjoint*, generic-morphisms section
  (`https://ncatlab.org/nlab/show/parametric+right+adjoint`): the
  evaluation formula and the `(T1, E_T)` determination.
- nlab, *polynomial functor*, the 2-category of polynomial functors
  (`https://ncatlab.org/nlab/show/polynomial+functor`): the slice-level
  `Δ`/`Π`/`Σ` description this branch generalizes (this page does not
  treat presheaf categories; the presheaf-level claims rest on the
  parametric-right-adjoint page and Weber 2007).
- M. Weber, *Familial 2-functors and parametric right adjoints*,
  Theory and Applications of Categories 18 (2007).
- N. Gambino and M. Hyland, *Wellfounded trees and dependent
  polynomial functors* (TYPES 2003); J. Kock, *Polynomial functors and
  polynomial monads*.
- `Geb/Mathlib/Data/PFunctor/Slice/` (`Basic.lean`, `Functor.lean`) —
  the substrate restricted here.
- mathlib `Mathlib/Data/PFunctor/Univariate/Basic.lean`;
  `Mathlib/CategoryTheory/` (functors, presheaves, opposites).
- `GebMeta.lean` — the module-scoped `Classical.choice` allowlist.
