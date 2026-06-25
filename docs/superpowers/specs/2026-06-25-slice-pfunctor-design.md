# Slice polynomial functors on `Type`: design

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Status](#status)
- [Scope](#scope)
- [Background](#background)
- [Constructiveness boundary and the allowlist](#constructiveness-boundary-and-the-allowlist)
- [Increment split: A now, C next](#increment-split-a-now-c-next)
- [Constructive core (`Basic.lean`)](#constructive-core-basiclean)
  - [`SliceDomPFunctor`](#slicedompfunctor)
  - [`SlicePFunctor`](#slicepfunctor)
  - [Curried constructor for the constraint leg](#curried-constructor-for-the-constraint-leg)
  - [Compatibility predicate](#compatibility-predicate)
  - [Object and morphism maps (plain, choice-free)](#object-and-morphism-maps-plain-choice-free)
- [Categorical wrapper (`Functor.lean`)](#categorical-wrapper-functorlean)
  - [`SliceDomPFunctor.domFunctor`](#slicedompfunctordomfunctor)
  - [`SlicePFunctor.functor`](#slicepfunctorfunctor)
  - [Bridge to the core](#bridge-to-the-core)
- [Universe posture](#universe-posture)
- [Placement and naming](#placement-and-naming)
- [Reuse inventory (verified against the pin)](#reuse-inventory-verified-against-the-pin)
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

First mathematical content for `Geb/Mathlib/`. Construct polynomial
functors between slice categories of `Type`, as a restriction of the
interpretation of mathlib's `PFunctor`. Increment A delivers:

- a **constructive core** (one file): the structures, the
  compatibility predicate, the curried constructor, and the object and
  morphism maps together with their functoriality stated as plain
  equalities — no `CategoryTheory.Functor`, no `Over`, certified
  `Classical.choice`-free by the strict axiom linter;
- a **thin categorical wrapper** (a second file): the action as a
  `CategoryTheory.Functor` between `Over` categories, via
  `Functor.toOver`, reusing the core. Because mathlib's `Over` is
  `Classical.choice`-dependent at the type level, this module is added
  to `GebMeta.classicalAllowedModules`.

The natural-isomorphism validation is increment C, specified here only
as a deferred follow-on.

## Background

The project's polynomial-functors survey (pins: mathlib `360da6f`,
toolchain `v4.32.0-rc1`; cslib `e0573fb`) records that mathlib has no
polynomial functors between slice categories `Type/I → Type/O`, no
indexed containers, and no dependent W-types. The only slice-level
treatment in the Lean ecosystem is the external `sinhp/Poly`
(`MvPoly`), which is not a mathlib dependency.

A `PFunctor` (`A : Type uA`, `B : A → Type uB`) is the middle leg of a
Gambino–Hyland polynomial diagram

```text
dom  ◀──s──  Idx  ──fst──▶  A  ──t──▶  cod
```

where `Idx = Σ a, B a` (mathlib's `PFunctor.Idx`) and `fst : Idx → A`
is the bundle of positions over shapes. Supplying the two outer legs
`s` and `t` turns a `PFunctor` into a polynomial functor
`Type/dom → Type/cod`, defined as the restriction of
`P.Obj X = Σ a, (B a → X)` to `s`-compatible position assignments,
tagged by `t`.

References for the mathematical object: Gambino and Hyland,
*Wellfounded trees and dependent polynomial functors* (TYPES 2003);
Kock, *Polynomial functors and polynomial monads*; the names
"dependent polynomial functor" and "slice polynomial functor" denote
the same construction.

## Constructiveness boundary and the allowlist

mathlib's `CategoryTheory.Over` is `Classical.choice`-dependent at the
type level: any declaration whose signature merely names `Over X`
depends on `Classical.choice` — verified, `fun X : Over Bool => X`
reports `[propext, Classical.choice, Quot.sound]` — because `Over X`
unfolds through `CostructuredArrow`/`Comma` constructs whose category
and functor coherence obligations mathlib discharges with classical
automation (`cat_disch`/`aesop_cat`). The categorical *data* is
constructive (the bare `Category (Type u)` instance, `PFunctor.Obj`,
and `PFunctor.map` are axiom-free); the taint is in the proofs, not
the definitions.

The repository's `GebMeta.detectNonstandardAxiom` linter fails
`lake lint` for any `Geb`/`GebTests` declaration depending on an axiom
outside `{propext, Quot.sound}`, except in the exact modules listed in
`GebMeta.classicalAllowedModules`, which additionally permit
`Classical.choice` (and only that). That module-scoped allowlist
landed on `main` in a prior branch.

Increment A is therefore split across two files:

- `…/Slice/Basic.lean` — the constructive core. It names no `Over` and
  no `CategoryTheory.Functor`; it is held to the strict
  `{propext, Quot.sound}` set, so the linter *certifies* it is
  `Classical.choice`-free.
- `…/Slice/Functor.lean` — the categorical wrapper. It names `Over`,
  so its module `Geb.Mathlib.Data.PFunctor.Slice.Functor` is added to
  `GebMeta.classicalAllowedModules` and permitted `Classical.choice`.

The split quarantines the irreducible mathlib taint in one thin,
auditable module while the mathematical content is proven choice-free.

## Increment split: A now, C next

- **A (this branch).** The constructive core (`Basic.lean`) and the
  categorical wrapper (`Functor.lean`): the structures, the maps and
  their functoriality, and their packaging as a
  `CategoryTheory.Functor (Over dom) (Over cod)`. No natural
  isomorphism.
- **C (later, separate branch(es)).** Prove the wrapper's functor
  naturally isomorphic to the categorical composite
  `Σ_t ∘ Π_f ∘ Δ_s` of base change, dependent product, and dependent
  sum. This certifies the construction is the Gambino–Hyland
  polynomial. C lives in the categorical (allowlisted) layer and has a
  named prerequisite (see "Out of scope").

The natural isomorphism is reserved for C rather than approximated by
an elementary check in A: an elementary object-level equivalence would
be superseded by C, so it is cost without lasting return.

## Constructive core (`Basic.lean`)

Code snippets elide the `universe u` declaration and the
module-system boilerplate (`module`, `public import`, public section)
present in the file.

### `SliceDomPFunctor`

```lean
structure SliceDomPFunctor (dom : Type u) extends PFunctor.{u, u} where
  s : toPFunctor.Idx → dom
```

Carries the input-restriction (constraint) leg only.

### `SlicePFunctor`

```lean
structure SlicePFunctor (dom cod : Type u) extends SliceDomPFunctor dom where
  t : toPFunctor.A → cod
```

Adds the output-tagging leg. The two-layer factoring separates
input-restriction from output-tagging and aligns the definitions with
the view that a functor into `Type/cod` is a `cod`-indexed family of
functors into `Type`; `SliceDomPFunctor` is the `cod = Unit`
component. The formal universal-property statement of that view is
deferred (see "Out of scope").

`@[ext]` is applied to each structure where it compiles. `Inhabited`
is not unconditionally derivable (`SliceDomPFunctor dom` adds
`s : Idx → dom`, so an instance needs `[Inhabited dom]` plus a default
shape). Add `DecidableEq` / `Repr` only where they compile and help.

### Curried constructor for the constraint leg

The field `s : Idx → dom` is the canonical polynomial-diagram
morphism. A smart constructor supplies the dependently-curried form:

```lean
def SliceDomPFunctor.ofCurried (P : PFunctor.{u, u}) (dom : Type u)
    (sc : (a : P.A) → P.B a → dom) : SliceDomPFunctor dom
```

by `Sigma` uncurrying (`s := fun ⟨a, b⟩ => sc a b`); a matching curried
accessor `fun a b => s ⟨a, b⟩` is provided, the round-trip `rfl`. The
stored field stays uncurried so increment C feeds `Over.pullback s`
directly.

### Compatibility predicate

The constraint leg selects a sub-family of position assignments. Name
that condition as a dependent predicate, an equality of composed
functions (no `∀`):

```lean
def SliceDomPFunctor.Compatible (F : SliceDomPFunctor dom) {X : Type u}
    (p : X → dom) (a : F.A) (v : F.B a → X) : Prop :=
  p ∘ v = F.s ∘ Sigma.mk a
```

`Sigma.mk a : F.B a → F.Idx` is the fibre inclusion, so
`F.s ∘ Sigma.mk a : F.B a → dom` is the constraint leg restricted to
shape `a`; the predicate equates it with `p ∘ v`. Pointwise this is
`p (v b) = s ⟨a, b⟩`.

### Object and morphism maps (plain, choice-free)

The core presents the domain-restricted functor as plain data — an
object assignment, a morphism action, a shape-preservation lemma, and
functoriality lemmas — with no `CategoryTheory.Functor` and no `Over`
(both of which would pull `Classical.choice`). A slice object over
`dom` is represented by its structure map `p : X → dom`; a slice
morphism `(X, p) → (X', p')` by a function `f : X → X'` with
`p' ∘ f = p`.

`obj`, `map`, and `map_fst` carry `@[expose]` (load-bearing, not
boilerplate: the wrapper needs their definitions unfolded to discharge
`Over` laws and the tag triangle; `#print axioms` confirms exposure
introduces no `Classical.choice`).

```lean
@[expose] def SliceDomPFunctor.obj (F : SliceDomPFunctor dom) {X : Type u}
    (p : X → dom) : Type u :=
  { x : F.toPFunctor.Obj X // F.Compatible p x.1 x.2 }

@[expose] def SliceDomPFunctor.map (F : SliceDomPFunctor dom) {X X' : Type u}
    {p : X → dom} {p' : X' → dom} (f : X → X') (hf : p' ∘ f = p) :
    F.obj p → F.obj p' :=
  fun x => ⟨F.toPFunctor.map f x.1, ?compat⟩
```

Witness strategy (`?compat`): destructure `x` as `⟨⟨a, v⟩, hx⟩`; the
goal reduces to `p' ∘ (f ∘ v) = F.s ∘ Sigma.mk a`, closed from `hf`
(`p' ∘ f = p`) and `hx` (`Compatible`, i.e. `p ∘ v = F.s ∘ Sigma.mk a`)
by `Function.comp_assoc`. (A bare `rw [PFunctor.map_eq]` does not fire:
`x.1` is not a literal `⟨a, g⟩`; destructure first.)

```lean
@[expose] theorem SliceDomPFunctor.map_fst (F : SliceDomPFunctor dom)
    {X X' : Type u} {p : X → dom} {p' : X' → dom} (f : X → X')
    (hf : p' ∘ f = p) (x : F.obj p) : (F.map f hf x).1.1 = x.1.1

theorem SliceDomPFunctor.map_id (F : SliceDomPFunctor dom) {X : Type u}
    (p : X → dom) : F.map id (by simp) = (id : F.obj p → F.obj p)

theorem SliceDomPFunctor.map_comp (F : SliceDomPFunctor dom)
    {X Y Z : Type u} {p : X → dom} {q : Y → dom} {r : Z → dom}
    (f : X → Y) (g : Y → Z) (hf : q ∘ f = p) (hg : r ∘ g = q) :
    F.map (g ∘ f) (by rw [← hf, ← hg, Function.comp_assoc])
      = F.map g hg ∘ F.map f hf
```

`map_fst` records that the action fixes the shape `x.1.1` (the wrapper
tag triangle needs it; it is provable only after destructuring, not by
`rfl`). `map_id`/`map_comp` reduce to `F.toPFunctor.id_map` /
`F.toPFunctor.map_map` (the `LawfulFunctor (PFunctor.Obj _)` instance,
reached through `toPFunctor`) plus subtype extensionality, again after
destructuring. Only `propext`/`Quot.sound`-class reasoning is used
(`funext` reduces to `Quot.sound`); the strict linter certifies no
`Classical.choice` (verified: `obj`/`map`/`map_fst` axiom-free,
`map_id` = `{propext, Quot.sound}`, `map_comp` = `{Quot.sound}`). Exact
tactic forms are pinned in the implementation plan.

## Categorical wrapper (`Functor.lean`)

This file names `Over` and is allowlisted for `Classical.choice`. It
packages the core maps as honest `CategoryTheory.Functor`s.

`Over dom` is `CostructuredArrow (𝟭 (Type u)) dom`, and `Type u` has
bundled morphisms (`TypeCat.Hom`): a hom applies to an element through
its `FunLike` coercion, a function is promoted to a hom with `↾`
(`TypeCat.ofHom`), and hom-equalities are proved with `ext` (not
`funext`). Project-strict lints bind these proofs: use `;` not `<;>`
where one goal results (`linter.style`); use `change`, never goal-
changing `show` (`linter.style.show`); and a `simp only` that closes
by `TypeCat.hom_ofHom` plus definitional reduction may report the core
lemmas as unused (`linter.unusedSimpArgs`), needing a local
`set_option` or restructuring. These are pinned in the plan.

### `SliceDomPFunctor.domFunctor`

```lean
def SliceDomPFunctor.domFunctor (F : SliceDomPFunctor dom) :
    CategoryTheory.Functor (Over dom) (Type u) where
  obj Y := F.obj (ConcreteCategory.hom Y.hom)
  map h := ↾(F.map (ConcreteCategory.hom h.left) ?w)   -- `?w` from `Over.w h`
  map_id Y := ?law_id
  map_comp f g := ?law_comp
```

The object and morphism maps are the core's `F.obj` / `F.map`; the
wrapper-specific content is:

- the slice-morphism hypothesis `?w` (`p'_Y ∘ h' = p'_X`) derived from
  `Over.w h` *pointwise* — `funext` first, then
  `rw [← ConcreteCategory.comp_apply, Over.w h]` (the naive
  `congrFun (congrArg hom (Over.w h))` does not reduce);
- the `TypeCat.Hom` law goals (`?law_id`/`?law_comp`) discharged via
  `ext` and the core's `map_id`/`map_comp`, bridged through
  `Over.id_left`/`Over.comp_left`, `CategoryTheory.hom_id` /
  `CategoryTheory.hom_comp` (named under `CategoryTheory.*`, with the
  `⇑` coercion — not `ConcreteCategory.hom_id`),
  `ConcreteCategory.comp_apply`, `CategoryTheory.id_apply`, and
  `TypeCat.hom_ofHom`. The core lemmas must be supplied with their
  implicit structure maps pinned (`F.map_comp (p := …) (q := …)
  (r := …)`; the auto-bound objects named via `rename_i`).

Exact tactic forms are pinned in the implementation plan; both files
verified to compile during spec review.

### `SlicePFunctor.functor`

```lean
def SlicePFunctor.functor (F : SlicePFunctor dom cod) :
    CategoryTheory.Functor (Over dom) (Over cod) :=
  Functor.toOver F.toSliceDomPFunctor.domFunctor cod
    (fun _ => ↾(fun z => F.t z.1.1))    -- tag by `t` of the shape
    ?triangle
```

`Functor.toOver F X f h` upgrades `F : S ⥤ T` to `S ⥤ Over X` from
maps `f : (Y : S) → F.obj Y ⟶ X` whose triangles commute, supplying
the object map, morphism map, and both functor laws at once — the
§ Higher-order constructions route, no hand-rolled law proofs for the
`Type → Over cod` lift. An element `z : domFunctor.obj Y` has
`z.1 : Obj X` and `z.1.1 : A`, so the tag is `F.t z.1.1`. The triangle
`?triangle` does NOT hold by `rfl`: shape-preservation under
`domFunctor.map` is propositional (through the `Subtype`), so it goes
through the core lemma `map_fst` and `congrArg F.t` (after
`simp only [ConcreteCategory.comp_apply, …domFunctor, TypeCat.hom_ofHom]`).
The same triangle obligation recurs in `functor_comp_forget` below;
factor it as a named lemma.

### Bridge to the core

```lean
theorem SlicePFunctor.functor_comp_forget (F : SlicePFunctor dom cod) :
    F.functor ⋙ Over.forget cod = F.toSliceDomPFunctor.domFunctor
```

records that the wrapper forgets back to `domFunctor`, hence
(transitively) to the core maps. Proved in tactic mode
(`by rw [functor]; apply Functor.toOver_comp_forget`, then re-discharge
the same tag triangle as in `functor`) — not term-mode
`:= Functor.toOver_comp_forget`, whose `f`/`h` arguments are
underdetermined and whose `rfl` is blocked by `domFunctor`'s law-proof
fields.

## Universe posture

Attempt maximal universe polymorphism: `PFunctor.{uA, uB}` with
`dom cod : Type u`. The `Over` slice categories require their objects
in a single universe, constraining the core carrier
`{ x : F.toPFunctor.Obj X // … } : Type (max u uA uB)` (via
`PFunctor.Obj X : Type (max v uA uB)`) to lie in `Type u`, forcing
`uA ≤ u` and `uB ≤ u`. If polymorphism does not compile, fall back to
the single universe `PFunctor.{u, u}`, `dom cod : Type u` shown above
(mirroring `MvPFunctor`). Remove unused `universe`/`variable`
declarations after settling this. (The constraint binds even the core
carrier, whose `Type u` codomain the wrapper's `Over` requires.) Spec
review verified only the single-universe fallback; the plan records
the polymorphic form as an unverified attempt.

## Placement and naming

Mirror mathlib's `Mathlib/Data/PFunctor/Univariate/Basic.lean`
lineage. Two new content modules plus the directory-index chain:

- `Geb/Mathlib/Data/PFunctor/Slice/Basic.lean` (constructive core),
  extracting to `Mathlib/Data/PFunctor/Slice/Basic.lean`.
- `Geb/Mathlib/Data/PFunctor/Slice/Functor.lean` (categorical
  wrapper), `public import`-ing `Basic` and mathlib's `Over`. Its
  module `Geb.Mathlib.Data.PFunctor.Slice.Functor` is added to
  `GebMeta.classicalAllowedModules`.
- Directory-index files (`Geb/Mathlib/Data.lean`,
  `…/Data/PFunctor.lean`, `…/Data/PFunctor/Slice.lean`) per the
  narrow-and-deep "one indexing file per directory" convention, and a
  `Geb/Mathlib.lean` umbrella import.
- `docs/index.md` entry for the new concept, same branch.

Each module docstring carries the mathlib sections in order:
`# Title`, summary, `## Main definitions`, `## Implementation notes`,
`## References`, `## Tags` (the wrapper's notes record the `Over`
dependence and the allowlist entry; `Basic`'s record the choice-free
core). `## Main statements` is omitted (definitions, with the
functoriality lemmas covered by the summary); `## Notation` omitted.

The self-prefix `Geb.Mathlib.` appears only in `import` lines, never
in namespaces/bodies/docstrings. Lean namespaces are `SliceDomPFunctor`
/ `SlicePFunctor` (no `Geb` prefix).

## Reuse inventory (verified against the pin)

Citations re-verified against the repo's current pin under
`.lake/packages/mathlib/`.

- `PFunctor.Obj` (interpretation, axiom-free) and
  `PFunctor.Idx := Σ x : P.A, P.B x` —
  `Mathlib/Data/PFunctor/Univariate/Basic.lean` (lines 45, 119).
- `PFunctor.map` (53), `PFunctor.map_eq` (67), `PFunctor.id_map` (72),
  `PFunctor.map_map` (75), `LawfulFunctor (PFunctor.Obj P)` (78) —
  the core morphism action and functoriality.
- `CategoryTheory.Functor.toOver` —
  `Mathlib/CategoryTheory/Comma/Over/Basic.lean:1147` (distinct from
  `Over.toOver` at 584); `Functor.toOver_comp_forget` nearby.
- `CategoryTheory.Over` (39), `Over.forget`, `Over.w`,
  `Over.id_left`/`Over.comp_left`, `ConcreteCategory.hom` /
  `ConcreteCategory.comp_apply`, and `CategoryTheory.hom_id` /
  `CategoryTheory.hom_comp` / `CategoryTheory.id_apply` (under
  `CategoryTheory.*`, stated with the `⇑` coercion — not
  `ConcreteCategory.hom_id`); `↾` and `TypeCat.hom_ofHom`
  (`Types/Basic.lean:142`); `Over.pullback`/`Over.map` (`Δ`, `Σ` legs)
  for C.
- `GebMeta.classicalAllowedModules` (`GebMeta.lean`) — the wrapper
  module is appended here.

## Out of scope (deferred)

- **Increment C: the natural isomorphism** to `Σ_t ∘ Π_f ∘ Δ_s`, in
  the categorical (allowlisted) layer.
- **Prerequisite for C: `Type` is locally cartesian closed.** The pin
  provides the dependent-product machinery (`pushforward`,
  `ExponentiableMorphism`, `ChosenPullbacksAlong`) abstractly but
  instantiates none on `Type`; only `Π_f` is missing
  (`Δ_s = Over.pullback`, `Σ_t = Over.map` exist). Supplying these for
  `Type` is upstreamable infrastructure and a separate concern. They
  must be computable: the mathlib route
  `ChosenPullbacksAlong.ofHasPullbacksAlong` is `noncomputable` (and,
  being in a `Classical`-permitted layer, only the `noncomputable`
  obligation — not the axiom — would bind there).
- **Universal property of the codomain split**: `Type/cod`-valued
  functors as a `cod`-indexed product of `Type`-valued functors.
  Requires `Over cod ≌ (cod → Type)`, absent from the pin.

## Higher-order-constructions tension

`docs/rules/lean-coding.md` § Higher-order constructions prefers
functors built from compositions over hand-rolled object/morphism maps
and law proofs. The split makes the trade explicit:

- The **core** `obj`/`map`/`map_id`/`map_comp` are hand-rolled plain
  functions and lemmas — necessarily, because the compositional route
  (`CategoryTheory.Functor`, `Π_f ∘ Δ_s`) names `Over` and would pull
  `Classical.choice`, defeating the choice-free goal. The hand-rolling
  is minimized by reusing `PFunctor.Obj`/`PFunctor.map` and their
  `LawfulFunctor` lemmas; the only bespoke content is the `Compatible`
  predicate and the witness/functoriality reasoning.
- The **wrapper** is compositional: `domFunctor` is a thin packaging of
  the core maps, and `functor` is `Functor.toOver` of it — no
  hand-rolled functor-law proofs beyond `Over` plumbing.

C later discharges the remaining obligation by proving the wrapper's
functor isomorphic to `Σ_t ∘ Π_f ∘ Δ_s`.

## Verification plan

- `Basic.lean` (core) passes `lake lint` under the **strict** set: its
  module is NOT on `classicalAllowedModules`, so a green lint run is
  positive proof the core is `Classical.choice`-free. (A regression
  that pulled `Over`/`Classical` into `Basic.lean` would fail CI.)
- `Functor.lean` (wrapper): its module is added to
  `classicalAllowedModules`; `lake lint` then passes (only
  `Classical.choice` permitted there, nothing else).
- Mirrored test modules under `GebTests/Mathlib/Data/PFunctor/Slice/`:
  a compositional `example` exercising the core object map on a
  concrete small `SlicePFunctor` (computes; no `Classical`, no
  `noncomputable`), and the wrapper's `functor`/forget bridge.
- `lake build`, `lake test`, `lake lint`, `lake lint -- GebTests`,
  `lake shake`, `scripts/lint-imports.sh`, `markdownlint-cli2` +
  `doctoc` on touched Markdown. Pre-push checklist with line-by-line
  review before any push.

## References

- The project's polynomial-functors survey (external working
  document; not committed to this repo).
- Gambino and Hyland, *Wellfounded trees and dependent polynomial
  functors* (TYPES 2003).
- Kock, *Polynomial functors and polynomial monads*.
- mathlib `Mathlib/Data/PFunctor/Univariate/Basic.lean`;
  `Mathlib/CategoryTheory/Comma/Over/`;
  `Mathlib/CategoryTheory/LocallyCartesianClosed/`.
- `GebMeta.lean` — the module-scoped `Classical.choice` allowlist.
