# Finite presheaf parametric right adjoints: decidability of W-type validity

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Scope](#scope)
- [Concern shape and the PR split](#concern-shape-and-the-pr-split)
- [Prior state](#prior-state)
  - [This repository](#this-repository)
  - [mathlib](#mathlib)
- [The finiteness condition](#the-finiteness-condition)
- [Module layout](#module-layout)
- [Module contents](#module-contents)
  - [`Finite/Basic.lean`](#finitebasiclean)
  - [`Finite/W.lean`](#finitewlean)
- [Tests](#tests)
- [Transcription or novel](#transcription-or-novel)
- [Universe constraints](#universe-constraints)
- [Choice boundary](#choice-boundary)
- [Verification performed](#verification-performed)
- [Documentation and roadmap](#documentation-and-roadmap)
- [Out of scope](#out-of-scope)
- [References](#references)

<!-- END doctoc -->

## Scope

The presheaf decidability layer
(`Geb/Mathlib/Data/PFunctor/Presheaf/Decidable.lean`) decides naturality
of a direction assignment and hereditary naturality of a slice W-tree.
Its instances consume four hypotheses supplied by the caller:
`F.Finitary` (each direction type carries a `FinEnum`), `FinEnum I`
(finitely many objects), `∀ i i', FinEnum (i' ⟶ i)` (finite hom-sets),
and `DecidableEq F.A` (decidable shape equality). The slice layer
(`Slice/Decidable.lean`) additionally decides W-type admissibility from
`F.Finitary` and `DecidableEq I`. Nothing in either layer bundles the
hypotheses or supplies them from a single source.

This work bundles the finiteness evidence for a presheaf polynomial
functor whose shapes, directions, and index categories are all finite.
A single structure records a `PresheafPFunctor I J` together with
`FinEnum` evidence for the shape type `A`, the direction types `B a`,
the object types `I` and `J`, and the hom-sets of both categories. The
existing decidability instances are reused unchanged; the structure's
forwarding instances supply the scattered hypotheses from the bundled
fields.

Two tiers, matching where the predicates live:

- **General (`I`, `J` separate).** Finiteness of `T1` (the shape
  presheaf on `J`) and `E_T` (the arity presheaves on `I`): finite
  shapes, finite directions, finite index categories. Decidability of
  `IsNatural` (naturality of a direction assignment) and of the slice
  fiber/compatibility predicates.

- **Endofunctor (`I = J`).** W-type validity: admissibility
  (`SlicePFunctor.WValid`) and hereditary naturality
  (`PresheafPFunctor.IsHereditarilyNatural`) are decidable. A combined
  `Bool`-valued validator decides membership in the W-type presheaf
  fiber. `DecidableEq` on the W-type is derived.

The endofunctor restriction is imposed only where the W-type requires
it (the admissibility step compares a child's codomain-index against its
parent's domain-index); the general tier carries no diagonal assumption.

## Concern shape and the PR split

One concern — bundling the finiteness evidence for a fully-finite
presheaf PRA and deriving the decision procedures — on one branch,
delivered as one dependency-ordered PR.

| PR | Modules | Depends on |
| --- | --- | --- |
| 1 | `Presheaf/Finite/Basic.lean`, `Presheaf/Finite/W.lean`, and their tests | `Presheaf/Basic.lean`, `Presheaf/W.lean`, `Presheaf/Decidable.lean`, `Slice/Decidable.lean`, `Univariate/Finitary.lean`, `Data/FinEnum.lean`, `Data/W/Basic.lean` |

PR 1 depends on content not yet upstreamed: the presheaf PRA modules
and the slice decidability layer. The dependency is recorded so the
delivery order is derivable; it is not a deliverable of this branch.

## Prior state

### This repository

| Module | Content consumed by this work |
| --- | --- |
| `Presheaf/Basic.lean` | `PresheafDomPFunctorData`, `PresheafPFunctorData`, `PresheafPFunctor`, `Shape`, `Direction`, `shapeRestr`, `directionRestr`, `reindex`, `objPresheaf` |
| `Presheaf/W.lean` | `IsHereditarilyNatural`, `wRestrTree`, `W` (the carrier presheaf), `W.mk`/`W.dest` |
| `Presheaf/Decidable.lean` | `decidableIsNatural`, `isHereditarilyNaturalBoolCore`, `isHereditarilyNaturalBoolCore_eq_true_iff`, `decidableIsHereditarilyNatural` |
| `Slice/Basic.lean` | `SliceDomPFunctor`, `SlicePFunctor`, `DirectionOver`, `Direction`, `ShapeOver`, `Shape`, `Compatible` |
| `Slice/W.lean` | `WValid`, `wIndex`, `W` (the admissible-tree subtype) |
| `Slice/Decidable.lean` | `decidableDirectionOver`, `decidableForallDirection`, `decidableCompatible`, `decidableShapeOver`, `wValidBool`, `wValidBool_eq_true_iff`, `decidableWValid` |
| `Univariate/Finitary.lean` | `PFunctor.Finitary`, the abbreviation `∀ a, FinEnum (P.B a)` |
| `Data/FinEnum.lean` | `decidableForallFinEnum`, `decidableForallSubtype`, `decidablePiFinEnum` |
| `Data/W/Basic.lean` | `WType.beq`, `WType.instDecidableEq` |

The existing instances and the hypotheses they consume:

| Instance | Hypotheses |
| --- | --- |
| `PresheafDomPFunctorData.decidableIsNatural` | `F.Finitary`, `FinEnum I`, `∀ i i', FinEnum (i' ⟶ i)`, `∀ i, DecidableEq (Z.obj ⟨i⟩)` |
| `PresheafPFunctor.decidableIsHereditarilyNatural` | `F.Finitary`, `FinEnum I`, `∀ i i', FinEnum (i' ⟶ i)`, `DecidableEq F.A` |
| `SlicePFunctor.decidableWValid` | `F.Finitary`, `DecidableEq I` |
| `WType.instDecidableEq` | `DecidableEq F.A`, `∀ a, FinEnum (F.B a)` |

`F.Finitary` enters all four. `FinEnum I` and finite hom-sets enter the
two presheaf predicates. `DecidableEq F.A` enters hereditary naturality
and W-type equality. None of the four receives an instance that supplies
the hypotheses from a bundled finite structure; that is the omission
this work addresses.

### mathlib

- `Mathlib.Data.FinEnum` provides the `FinEnum` class (a type with an
  explicit `List` enumeration and `DecidableEq`), `FinEnum.toList`, and
  `FinEnum.mem_toList`. The class extends `DecidableEq`, so `FinEnum α`
  supplies `DecidableEq α`.
- No bundled finite presheaf polynomial functor exists; the reuse
  target is this repository's `PresheafPFunctor`.

## The finiteness condition

A presheaf polynomial functor `F : PresheafPFunctor I J` is fully
finite when:

1. **Shapes are finite:** `FinEnum F.A`. This gives `DecidableEq F.A`
   (since `FinEnum` extends `DecidableEq`) and, with `DecidableEq J`,
   yields `FinEnum (F.Shape j)` for each `j : J` (the fiber of `q` over
   `j` is a decidable subtype of the finite type `A`).

2. **Directions are finite:** `F.Finitary` (`∀ a, FinEnum (F.B a)`).
   This gives, with `DecidableEq I`, `FinEnum (F.Direction a i)` for
   each `a : A`, `i : I` (the fiber of `rCurried a` over `i` is a
   decidable subtype of the finite type `B a`).

3. **The domain category `I` is finite:** `FinEnum I` (finitely many
   objects) and `∀ i i' : I, FinEnum (i' ⟶ i)` (finite hom-sets).

4. **The codomain category `J` is finite:** `FinEnum J` and
   `∀ j j' : J, FinEnum (j' ⟶ j)`.

Conditions 1–2 are the finiteness of `T1` (shapes and directions of the
shape presheaf) and `E_T` (the arity presheaves). Conditions 3–4 are the
finiteness of the index categories.

| Predicate | Required of the structure | Supplied by the caller |
| --- | --- | --- |
| `decidableIsNatural` | `Finitary`, `FinEnum I`, finite `I`-hom-sets | `∀ i, DecidableEq (Z.obj ⟨i⟩)` |
| `decidableIsHereditarilyNatural` | `Finitary`, `FinEnum I`, finite `I`-hom-sets, `DecidableEq F.A` | — |
| `decidableWValid` | `Finitary`, `DecidableEq I` | — |
| `WType.instDecidableEq` | `Finitary`, `DecidableEq F.A` | — |

The `∀ i, DecidableEq (Z.obj ⟨i⟩)` hypothesis of `decidableIsNatural`
is not bundled: it depends on the input presheaf `Z`, which is an
argument to the functor, not part of the functor's own data. The caller
supplies it.

The `FinEnum J` and finite `J`-hom-sets are not consumed by the existing
decidability instances (which quantify only over `I`). They are included
because the structure represents a fully-finite presheaf PRA: `T1` is a
presheaf on `J`, and its finiteness includes the finiteness of `J`
itself. They also support future work (decidability of shape-restriction
equations, exhaustive verification of the `shapeRestr`/`reindex` laws).

## Module layout

Two new source modules and two new test modules, in a `Finite/`
subdirectory of `Presheaf/`.

| Path | Role |
| --- | --- |
| `Geb/Mathlib/Data/PFunctor/Presheaf/Finite/Basic.lean` | the bundled structure, derived finiteness (shapes, directions), forwarding instances for the general tier (`IsNatural`, slice predicates) |
| `Geb/Mathlib/Data/PFunctor/Presheaf/Finite/W.lean` | the endofunctor tier: combined `Bool`-valued W-type validator, forwarding instances for `WValid`, `IsHereditarilyNatural`, W-type membership, and `DecidableEq` on the W-type |
| `GebTests/Mathlib/Data/PFunctor/Presheaf/Finite/Basic.lean` | reduction tests for the general tier |
| `GebTests/Mathlib/Data/PFunctor/Presheaf/Finite/W.lean` | reduction tests for the endofunctor tier |

Both source modules are registered in their respective import-index
files, and `docs/index.md` is updated.

## Module contents

### `Finite/Basic.lean`

```lean
universe uI uJ uA uB vI vJ uZ uX

set_option linter.checkUnivs false in
/-- A presheaf polynomial functor whose shapes, directions, and index
categories are all finite. Bundles the `FinEnum` evidence the
decidability layers consume. -/
structure FinitePresheafPFunctor (I : Type uI) [Category.{vI} I]
    (J : Type uJ) [Category.{vJ} J] :
    Type (max (uA + 1) (uB + 1) uI uJ vI vJ) where
  /-- The underlying presheaf polynomial functor. -/
  toPresheafPFunctor : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J
  /-- Finitely many objects in the domain category. -/
  finEnumI : FinEnum I
  /-- Finite hom-sets in the domain category. -/
  finEnumHomI : ∀ i i' : I, FinEnum (i' ⟶ i)
  /-- Finitely many objects in the codomain category. -/
  finEnumJ : FinEnum J
  /-- Finite hom-sets in the codomain category. -/
  finEnumHomJ : ∀ j j' : J, FinEnum (j' ⟶ j)
  /-- Finitely many shapes. -/
  finEnumA : FinEnum toPresheafPFunctor.A
  /-- Finitely many directions per shape. -/
  finitary : toPresheafPFunctor.toPFunctor.Finitary
```

The structure is a plain `structure`, not a `class`: the finiteness
evidence is passed explicitly (as a `FinitePresheafPFunctor` argument)
or through forwarding instances that extract the fields. This follows
the design of `FinitarySlicePFunctor` and avoids typeclass resolution
traversing the `PresheafPFunctor` diamond inheritance.

`@[ext]` is added. `Inhabited` is not derived (the function-typed
fields `directionRestr`, `shapeRestr`, `reindex` of the underlying
`PresheafPFunctor` carry no `Inhabited` instances in general).

Derived finiteness (theorems, not fields):

```lean
namespace FinitePresheafPFunctor

variable {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]

/-- `DecidableEq` on shapes, from `FinEnum A`. -/
@[expose] def decidableEqA (F : FinitePresheafPFunctor I J) :
    DecidableEq F.toPresheafPFunctor.A :=
  F.finEnumA.decEq

/-- `DecidableEq` on domain objects, from `FinEnum I`. -/
@[expose] def decidableEqI (F : FinitePresheafPFunctor I J) : DecidableEq I :=
  F.finEnumI.decEq

/-- `DecidableEq` on codomain objects, from `FinEnum J`. -/
@[expose] def decidableEqJ (F : FinitePresheafPFunctor I J) : DecidableEq J :=
  F.finEnumJ.decEq

/-- The shape fiber `Shape j` is finite: a decidable subtype of the
finite shape type `A`. -/
@[expose] def finEnumShape (F : FinitePresheafPFunctor I J) (j : J) :
    FinEnum (F.toPresheafPFunctor.Shape j) :=
  sorry -- construct directly: filter finEnumA.toList by (decidableEqJ (q ·) j),
        -- prove nodup (from the parent's nodup), then build FinEnum fields:
        --   card := filtered.length
        --   equiv := via List.idxOf on the nodup filtered list
        --   decEq := Subtype.decidableEq (from decidableEqA restricted)

/-- The direction fiber `Direction a i` is finite: a decidable subtype
of the finite direction type `B a`. -/
@[expose] def finEnumDirection (F : FinitePresheafPFunctor I J)
    (a : F.toPresheafPFunctor.A) (i : I) :
    FinEnum (F.toPresheafPFunctor.toSliceDomPFunctor.Direction a i) :=
  sorry -- construct directly: filter (finitary a).toList by
        -- (decidableEqI (rCurried a ·) i), prove nodup, build FinEnum
        -- fields as above with decEq from (finitary a).decEq restricted
```

The `sorry` placeholders mark implementation details to be resolved
during implementation. The mathematical content is straightforward:
`Shape j = {a : A // q a = j}` is a decidable subtype of the finite
type `A` (decidable by `decidableEqJ`), and `Direction a i = {b : B a //
rCurried a b = i}` is a decidable subtype of the finite type `B a`
(decidable by `decidableEqI`). The construction must avoid
`FinEnum.Subtype.finEnum` (which routes through `FinEnum.ofList` and is
`Classical.choice`-dependent); instead, construct the `FinEnum` fields
directly from the filtered `toList` of the parent `FinEnum`. The
filtered list inherits `Nodup` from the parent. The equivalence is
built via `List.idxOf` on the nodup filtered list (giving the forward
map `Subtype → Fin card`) and `List.get` (giving the inverse). The
`decEq` field is the parent's `decEq` restricted to the subtype (via
`Subtype.decidableEq`). If `FinEnum.ofNodupList` is available and
verified axiom-free, it may be used as a shorthand for the direct
field construction; otherwise the fields are supplied individually.

Forwarding instances (general tier):

```lean
/-- Naturality of a direction assignment is decidable. Forwards through
`toPresheafPFunctor` with the bundled `Finitary`, `FinEnum I`, and
finite `I`-hom-sets. The caller supplies `DecidableEq` on the input
presheaf's values. -/
instance decidableIsNatural (F : FinitePresheafPFunctor I J)
    {Z : Iᵒᵖ ⥤ Type uZ} [∀ i : I, DecidableEq (Z.obj ⟨i⟩)]
    (x : F.toPresheafPFunctor.toSliceDomPFunctor.Obj
      (PresheafDomPFunctorData.elemProj Z)) :
    Decidable (F.toPresheafPFunctor.toPresheafDomPFunctorData.IsNatural x) :=
  @PresheafDomPFunctorData.decidableIsNatural I _
    F.toPresheafPFunctor.toPresheafDomPFunctorData Z
    F.finitary F.finEnumI F.finEnumHomI inferInstance x

/-- Slice compatibility is decidable. -/
instance decidableCompatible (F : FinitePresheafPFunctor I J)
    {X : Type uX} (p : X → I) (a : F.toPresheafPFunctor.A)
    (v : F.toPresheafPFunctor.B a → X) :
    Decidable (F.toPresheafPFunctor.toSliceDomPFunctor.Compatible p a v) :=
  @SliceDomPFunctor.decidableCompatible I
    F.toPresheafPFunctor.toSliceDomPFunctor
    F.finitary F.decidableEqI _ p a v

/-- Shape-fiber membership is decidable. -/
instance decidableShapeOver (F : FinitePresheafPFunctor I J) (j : J) :
    DecidablePred (F.toPresheafPFunctor.toSlicePFunctor.ShapeOver j) :=
  @SlicePFunctor.decidableShapeOver I J F.toPresheafPFunctor.toSlicePFunctor
    F.decidableEqJ j

/-- Direction-fiber membership is decidable. -/
instance decidableDirectionOver (F : FinitePresheafPFunctor I J)
    (a : F.toPresheafPFunctor.A) (i : I) :
    DecidablePred (F.toPresheafPFunctor.toSliceDomPFunctor.DirectionOver a i) :=
  @SliceDomPFunctor.decidableDirectionOver I
    F.toPresheafPFunctor.toSliceDomPFunctor F.decidableEqI a i

end FinitePresheafPFunctor
```

**Implementation notes.**

The `finitary` field has type
`F.toPresheafPFunctor.toPFunctor.Finitary`, which is definitionally
`∀ a, FinEnum (F.toPresheafPFunctor.toPFunctor.B a)`. The forwarding
instances pass it where the source instances expect `[F.Finitary]` (the
`abbrev` on `PFunctor`). Through the diamond inheritance
(`PresheafPFunctor extends PresheafPFunctorData, SlicePFunctor`, both
extending `SliceDomPFunctor` which extends `PFunctor`), the
`toPFunctor` projection from any path through the diamond is
definitionally the same `PFunctor` value. The `Finitary` abbreviation,
being reducible, unfolds transparently, so `F.finitary` type-checks at
the expected position without a transport. This matches the
`FinitarySlicePFunctor` spec's verification of the analogous case.

The `@[expose]` attribute on `decidableEqA`, `decidableEqI`,
`decidableEqJ`, `finEnumShape`, `finEnumDirection`, and `decidableEqW`
serves cross-module `decide`-reduction in the test modules: `decide`
unfolds `def`s at kernel WHNF transparency, but only if the definition
is visible across the module boundary. `@[expose]` marks the definition
for cross-module unfolding, matching the existing slice and presheaf
modules' use of the attribute.

### `Finite/W.lean`

This module imports `Finite/Basic.lean` and `Presheaf/Decidable.lean`,
and restricts to the endofunctor case `I = J`.

```lean
universe uI uA uB vI

namespace FinitePresheafPFunctor

variable {I : Type uI} [Category.{vI} I]

/-- The combined `Bool`-valued W-type validator: a raw tree is valid
(admissible and hereditarily natural) exactly when both the slice
admissibility checker and the hereditary-naturality checker return
`true`. All instance arguments are supplied explicitly. -/
@[expose] def wValidBool (F : FinitePresheafPFunctor I I) :
    F.toPresheafPFunctor.toPFunctor.W → Bool :=
  fun w ↦ @SlicePFunctor.wValidBool I F.toPresheafPFunctor.toSlicePFunctor
      F.finitary F.decidableEqI w
    && F.toPresheafPFunctor.isHereditarilyNaturalBoolCore
      F.decidableEqI F.finEnumI F.finEnumHomI F.finitary
      (WType.instDecidableEq F.decidableEqA F.finitary) w

/-- `wValidBool` decides W-type membership: given admissibility, it
returns `true` exactly on hereditarily natural trees. The explicit
`(hw : WValid w)` hypothesis avoids forming the `SlicePFunctor.W`
subtype in the proposition (which would be circular, since `WValid w`
is itself a conjunct of the predicate being decided). -/
theorem wValidBool_eq_true_iff (F : FinitePresheafPFunctor I I)
    (w : F.toPresheafPFunctor.toPFunctor.W)
    (hw : F.toPresheafPFunctor.toSlicePFunctor.WValid w) :
    F.wValidBool w = true ↔
      F.toPresheafPFunctor.IsHereditarilyNatural ⟨w, hw⟩ := by
  sorry -- from isHereditarilyNaturalBoolCore_eq_true_iff, since the
        -- admissibility conjunct of wValidBool is already `true` by hw
        -- (wValidBool_eq_true_iff)

/-- The admissibility conjunct: `wValidBool w = true` implies
admissibility. -/
theorem wValidBool_imp_wValid (F : FinitePresheafPFunctor I I)
    (w : F.toPresheafPFunctor.toPFunctor.W) :
    F.wValidBool w = true →
      F.toPresheafPFunctor.toSlicePFunctor.WValid w := by
  sorry -- from Bool.and_eq_true.mp and SlicePFunctor.wValidBool_eq_true_iff

/-- W-type admissibility is decidable. -/
instance decidableWValid (F : FinitePresheafPFunctor I I)
    (w : F.toPresheafPFunctor.toPFunctor.W) :
    Decidable (F.toPresheafPFunctor.toSlicePFunctor.WValid w) :=
  @SlicePFunctor.decidableWValid I F.toPresheafPFunctor.toSlicePFunctor
    F.finitary F.decidableEqI w

/-- Hereditary naturality is decidable. -/
instance decidableIsHereditarilyNatural (F : FinitePresheafPFunctor I I)
    (z : F.toPresheafPFunctor.toSlicePFunctor.W) :
    Decidable (F.toPresheafPFunctor.IsHereditarilyNatural z) :=
  @PresheafPFunctor.decidableIsHereditarilyNatural I _
    F.toPresheafPFunctor F.finitary F.finEnumI F.finEnumHomI
    F.decidableEqA z

/-- `DecidableEq` on raw W-trees. -/
@[expose] def decidableEqW (F : FinitePresheafPFunctor I I) :
    DecidableEq (WType F.toPresheafPFunctor.toPFunctor.B) :=
  WType.instDecidableEq F.decidableEqA F.finitary

/-- Membership in the W-type presheaf fiber is decidable, stated on the
raw tree with `wIndexRoot` (which does not require the admissibility
subtype). The two-stage decision: first decide `WValid w`; if
admissible, decide the index equality and hereditary naturality on the
subtype element `⟨w, hw⟩`. -/
instance decidableMemW (F : FinitePresheafPFunctor I I) (j : I)
    (w : F.toPresheafPFunctor.toPFunctor.W) :
    Decidable (∃ (hw : F.toPresheafPFunctor.toSlicePFunctor.WValid w),
      F.toPresheafPFunctor.toSlicePFunctor.wIndex ⟨w, hw⟩ = j ∧
        F.toPresheafPFunctor.IsHereditarilyNatural ⟨w, hw⟩) :=
  sorry -- two-stage: match decidableWValid w with
        -- | isFalse hnw => isFalse (fun ⟨hw, _⟩ => hnw hw)
        -- | isTrue hw => match decidableEqI (wIndex ⟨w, hw⟩) j with
        --   | isFalse hnq => isFalse
        --       (fun ⟨hw', hq', _⟩ => hnq (by change wIndexRoot w = j; exact hq'))
        --   | isTrue hq => match decidableIsHereditarilyNatural ⟨w, hw⟩ with
        --     | isFalse hnh => isFalse
        --         (fun ⟨hw', _, hn'⟩ => hnh (by convert hn'; exact Subtype.ext (proof_irrel hw hw')))
        --     | isTrue hhn => isTrue ⟨hw, hq, hhn⟩

end FinitePresheafPFunctor
```

The `wValidBool_eq_true_iff` theorem takes an explicit admissibility
hypothesis `(hw : WValid w)` to avoid a type-level circularity:
`IsHereditarilyNatural` is defined on `SlicePFunctor.W` (the admissible
subtype `{w // WValid w}`), so forming the subtype element in the
proposition requires the very proof that is a conjunct of the predicate
being decided. The explicit hypothesis breaks the circularity; the
companion theorem `wValidBool_imp_wValid` extracts admissibility from
the `Bool` verdict, so the caller can obtain `hw` from the first
conjunct.

The `decidableMemW` instance states the membership predicate as an
existential over the admissibility proof, using `wIndex` on the subtype
element. The decision proceeds in two stages: first decide `WValid w`
(via `decidableWValid`); if admissible, decide the index equality (via
`decidableEqI` on `wIndex ⟨w, hw⟩`, which is definitionally
`wIndexRoot w`) and hereditary naturality (via
`decidableIsHereditarilyNatural ⟨w, hw⟩`). The existential formulation
is proof-irrelevant (any two admissibility proofs give the same
`wIndex` and the same `IsHereditarilyNatural` verdict, since both are
`Prop`-valued and the subtype is proof-irrelevant).

## Tests

Reduction tests on a small presheaf endofunctor over a finite category
exercise both tiers by `decide`:

**General tier (`Finite/Basic.lean` test):**

- A natural and a non-natural direction assignment for
  `decidableIsNatural`.
- A compatible and an incompatible direction assignment for
  `decidableCompatible`.
- Shape-fiber and direction-fiber membership verdicts.

**Endofunctor tier (`Finite/W.lean` test):**

- An admissible and hereditarily natural tree (positive `wValidBool`).
- An admissible but non-hereditarily-natural tree (negative
  `wValidBool`).
- An inadmissible tree (negative `wValidBool`).
- `DecidableEq` on two equal and two unequal W-trees.
- A `decidableMemW` verdict for a tree at the correct and an incorrect
  index.

The test fixture is a presheaf polynomial endofunctor over a small
finite category (e.g. the walking arrow `Fin 2` with one non-identity
morphism, or a discrete category on `Fin 2` or `Fin 3`). The category
instance must be constructive (no `Classical.choice`). The fixture is
declared with `abbrev`/`@[reducible]` carriers so instance resolution
matches the projected types (§ Verification performed in the
`FinitarySlicePFunctor` spec documents this pattern).

Each verdict is a named `def`, not a bare `example`: the axiom linter
traverses only named declarations.

## Transcription or novel

[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Cite the literature when
transcribing requires each definition to be marked.

| Declaration | Status | Source |
| --- | --- | --- |
| `FinitePresheafPFunctor`, `toPresheafPFunctor`, `finEnumI`, `finEnumHomI`, `finEnumJ`, `finEnumHomJ`, `finEnumA`, `finitary` | neither | bundling of the finiteness conditions already consumed by the decidability layers |
| `finEnumShape`, `finEnumDirection` | neither | standard: a decidable subtype of a `FinEnum` type is `FinEnum` |
| `wValidBool`, `wValidBool_eq_true_iff` | neither | conjunction of the existing `wValidBool` and `isHereditarilyNaturalBoolCore` |
| forwarding instances | neither | instance plumbing over the existing decidability layers |

No new mathematical content is introduced: the structure bundles
hypotheses and forwards them. The underlying notions — presheaf
polynomial functor, parametric right adjoint, W-type, hereditary
naturality — are covered by the citations the presheaf modules already
carry (`[Weber2007]`, `[GambinoHyland2004]`, `[GambinoKock2013]`). No
new bib entry is added.

## Universe constraints

The structure is universe-polymorphic in all six parameters of
`PresheafPFunctor`: `uI`, `uJ` (object universes), `vI`, `vJ` (morphism
universes), `uA`, `uB` (shape and direction universes). The result sort
is `Type (max (uA + 1) (uB + 1) uI uJ vI vJ)`, matching
`PresheafPFunctor I J` itself: the `FinEnum` fields live at the same
universes as their subjects (`FinEnum I : Type uI`,
`∀ i i', FinEnum (i' ⟶ i) : Type (max uI vI)`, etc.) and do not
increase the overall universe.

The endofunctor tier instantiates `J := I` and `vJ := vI`, matching
`PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I`, the form the W-type
and hereditary-naturality declarations are stated at. No equality proof
between distinct types is involved; the endofunctor is the caller
passing one type for both arguments.

The `WType.instDecidableEq` argument to `isHereditarilyNaturalBoolCore`
requires `DecidableEq (WType F.toPFunctor.B)`, which lives at
`Type (max uA uB)`. This is consistent with the existing
`decidableIsHereditarilyNatural` instance, which infers the same
`DecidableEq` from `DecidableEq F.A` and `F.Finitary`.

## Choice boundary

Every declaration in this branch is within the axiom linter's default
permitted set `{propext, Quot.sound}`; none reaches `Classical.choice`.

**Routing.** The existing instances this work specializes already route
bounded quantifiers through `FinEnum.toList` and `List.decidableBAll`,
never through `Fintype`. The forwarding instances add no quantifier;
they supply the bundled evidence, inheriting that routing and its axiom
profile.

**The `FinEnum` sources.** The bundled fields are caller-supplied
`FinEnum` values. The structure does not construct `FinEnum` instances
from `Classical.choice`-dependent combinators. The derived
`finEnumShape` and `finEnumDirection` must be constructed by filtering
the parent's `toList` (choice-free), not through `FinEnum.Subtype.finEnum`
(which routes through `FinEnum.ofList` and is `Classical.choice`-dependent,
as verified in the `FinitarySlicePFunctor` spec).

**`WType.instDecidableEq`.** The W-type equality decision procedure
(this repository's `Data/W/Basic.lean`) is axiom-free: it recurses
structurally via `WType.beq`, using `FinEnum.toList` for the bounded
quantifier over directions.

No module in this branch is added to `GebMeta.classicalAllowedModules`.

## Verification performed

To be compiled against the pinned toolchain during implementation, with
axioms as reported by `#print axioms`.

| Fragment | Expected result |
| --- | --- |
| `@SlicePFunctor.wValidBool I F.toSlicePFunctor F.finitary F.decidableEqI w` with explicit instance supply | elaborates; the `Finitary` abbreviation unfolds transparently through the diamond |
| `WType.instDecidableEq F.decidableEqA F.finitary` at type `DecidableEq (WType F.toPFunctor.B)` | elaborates; `#print axioms` reports no axioms beyond `{propext, Quot.sound}` |
| `isHereditarilyNaturalBoolCore F.decidableEqI F.finEnumI F.finEnumHomI F.finitary (WType.instDecidableEq ...) w` with all arguments explicit | elaborates; matches the existing classless pattern in `Presheaf/Decidable.lean` |
| `finEnumShape` construction via filtered `toList` + direct `FinEnum` fields | compiles; `#print axioms` reports no `Classical.choice` |
| `FinEnum.ofNodupList` (if used) | `#print axioms` must be checked; if it carries `Classical.choice`, fall back to direct field construction |
| `F.finitary` passed at the `F.Finitary` position through the diamond | elaborates without transport (definitional equality of `toPFunctor` through the diamond) |
| forwarding instances (`decidableIsNatural`, `decidableCompatible`, `decidableShapeOver`, `decidableDirectionOver`, `decidableWValid`, `decidableIsHereditarilyNatural`) | elaborate within `namespace FinitePresheafPFunctor`; `#print axioms` reports `{propext, Quot.sound}` |
| `decidableMemW` two-stage decision | elaborates; the existential formulation is proof-irrelevant |
| `@[expose]` on `wValidBool`, `decidableEqW`, `finEnumShape`, `finEnumDirection` | cross-module `decide`-reduction in the test module proceeds through these definitions |

## Documentation and roadmap

- `docs/index.md` gains entries for the finite presheaf PRA modules,
  placed after the presheaf W-type and decidability entries.
- Each new module carries the mandatory `/-! … -/` module docstring
  (with `## Main definitions`, `## Main statements`, `## Tags`, and the
  other non-vacuous sections of `docs/rules/lean-coding.md` §
  Documentation) and a `/-- … -/` docstring on every `def`, `structure`,
  `instance`, and field.
- `TODO.md` gains a note on follow-on workstreams: a bundled
  finite-category construction (object counts plus a composition
  function whose associativity is checked exhaustively), and the
  specialization where the shape and direction types are `Fin` (the
  presheaf analogue of `FinitarySlicePFunctor`).

## Out of scope

- **A bundled finite-category construction.** The structure takes
  `[Category.{vI} I]` as a typeclass argument; constructing a finite
  category from object counts and a composition table is a separate
  workstream.

- **The `Fin`-specialization.** Restricting shapes and directions to
  `Fin` types (the presheaf analogue of `FinitarySlicePFunctor`) is a
  stronger specialization that supplies `FinEnum` automatically. It is
  deferred; the present work takes `FinEnum` evidence as fields.

- **Finiteness of the W-type presheaf fibers.** The W-type of a finite
  polynomial functor is generally infinite (e.g. `ℕ`). This work decides
  membership; it does not claim the fibers are finite.

- **Uniqueness of the eliminator.** The presheaf W-type's `elim`
  establishes existence of the initial-algebra morphism; uniqueness is
  not formalized and is independent of finiteness.

- **Decidability of the `shapeRestr`/`reindex` laws.** With finite `J`
  and finite hom-sets, the functor laws are exhaustively verifiable.
  This is a testing/verification concern, not a decidability-instance
  concern, and is deferred.

- **The `∀ i, DecidableEq (Z.obj ⟨i⟩)` hypothesis.** This depends on
  the input presheaf `Z`, not on the functor's own finite data. It
  remains caller-supplied.

## References

The notions this work packages are cited in the presheaf modules it
builds on; no new bib entry is added.

- `[Weber2007]` — familial 2-functors and parametric right adjoints.
- `[GambinoHyland2004]` — well-founded trees and dependent polynomial
  functors.
- `[GambinoKock2013]` — polynomial functors and polynomial monads.
- `[AltenkirchGhaniHancockMcBrideMorris2015]` — indexed containers.
