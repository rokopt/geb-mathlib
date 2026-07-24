# Finite Presheaf PRA Decidability Implementation Plan

> **For agentic workers:** Use superpowers methodology to implement this plan task-by-task.

**Goal:** Implement `FinitePresheafPFunctor`, bundling finiteness evidence for a presheaf PRA and deriving decidable W-type validity.

**Architecture:** A bundled structure wraps `PresheafPFunctor I J` with `FinEnum` evidence for shapes, directions, and both index categories. Forwarding instances supply the bundled fields to the existing decidability layers. A combined `Bool`-valued validator decides W-type membership in the endofunctor case. Two modules: `Finite/Basic.lean` (general tier) and `Finite/W.lean` (endofunctor tier).

**Tech Stack:** Lean 4 (v4.33.0-rc1), mathlib, constructive `FinEnum`-based decidability, `decide`-based reduction tests.

## Global Constraints

- `autoImplicit = false`, `relaxedAutoImplicit = false` (lakefile.toml)
- No `noncomputable`, no `Classical.choice`; axiom budget `{propext, Quot.sound}`
- No `induction`/`induction'` tactics; explicit recursors only
- No self-recursive `def`; no `termination_by`
- 2-space indentation, 100-char line limit, Unicode notation
- `module` keyword after copyright block; `/-! ... -/` module docstring mandatory
- `/-- ... -/` docstrings on every `def`, `structure`, `instance`, field
- `@[ext]` on structures; `@[expose]` on defs needing cross-module `decide`-reduction
- Copyright: `Copyright (c) 2026 Terence Rokop. All rights reserved.`
- Spec: `docs/superpowers/specs/2026-07-25-finite-presheaf-pra-decidability-design.md`

---

## File Structure

| Path | Responsibility |
| --- | --- |
| `Geb/Mathlib/Data/PFunctor/Presheaf/Finite/Basic.lean` | `FinitePresheafPFunctor` structure, derived `DecidableEq`/`FinEnum` projections, general-tier forwarding instances |
| `Geb/Mathlib/Data/PFunctor/Presheaf/Finite/W.lean` | Endofunctor tier: combined `wValidBool`, correctness theorems, forwarding instances for `WValid`/`IsHereditarilyNatural`/`decidableMemW`, `decidableEqW` |
| `GebTests/Mathlib/Data/PFunctor/Presheaf/Finite/Basic.lean` | Reduction tests for the general tier |
| `GebTests/Mathlib/Data/PFunctor/Presheaf/Finite/W.lean` | Reduction tests for the endofunctor tier |

---

### Task 1: `Finite/Basic.lean` — structure, derived finiteness, forwarding instances

**Files:**
- Create: `Geb/Mathlib/Data/PFunctor/Presheaf/Finite/Basic.lean`

**Interfaces:**
- Consumes: `PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J` (from `Presheaf/Basic.lean`), `PFunctor.Finitary` (from `Univariate/Finitary.lean`), `FinEnum` (from `Mathlib.Data.FinEnum`), `SliceDomPFunctor.decidableDirectionOver`, `SliceDomPFunctor.decidableCompatible`, `SlicePFunctor.decidableShapeOver`, `PresheafDomPFunctorData.decidableIsNatural` (from `Slice/Decidable.lean`, `Presheaf/Decidable.lean`)
- Produces: `FinitePresheafPFunctor I J`, `.toPresheafPFunctor`, `.finEnumI`, `.finEnumHomI`, `.finEnumJ`, `.finEnumHomJ`, `.finEnumA`, `.finitary`, `.decidableEqA`, `.decidableEqI`, `.decidableEqJ`, `.finEnumShape`, `.finEnumDirection`, forwarding instances

- [ ] **Step 1: Write the module header and structure**

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.PFunctor.Presheaf.Decidable
public import Geb.Mathlib.Data.FinEnum

/-!
# Finite presheaf polynomial functors

A presheaf polynomial functor whose shapes, directions, and index
categories are all finite. Bundles the `FinEnum` evidence the
decidability layers (`Presheaf/Decidable.lean`, `Slice/Decidable.lean`)
consume, and provides forwarding instances that supply the bundled
fields to the existing decision procedures.

## Main definitions

* `FinitePresheafPFunctor` — the bundled structure.
* `FinitePresheafPFunctor.decidableEqA` / `decidableEqI` / `decidableEqJ`
  — `DecidableEq` derived from the `FinEnum` fields.
* `FinitePresheafPFunctor.finEnumShape` / `finEnumDirection` — finiteness
  of the shape and direction fibers, derived from the parent `FinEnum`.
* `FinitePresheafPFunctor.decidableIsNatural` / `decidableCompatible` /
  `decidableShapeOver` / `decidableDirectionOver` — forwarding instances
  for the general tier.

## Tags

polynomial functor, presheaf, parametric right adjoint, finite, FinEnum,
decidability
-/

public section

open CategoryTheory

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

attribute [ext] FinitePresheafPFunctor
```

- [ ] **Step 2: Write the derived projections**

In `namespace FinitePresheafPFunctor`, write `decidableEqA`, `decidableEqI`, `decidableEqJ` (one-line wrappers around `.decEq` of the `FinEnum` fields), then `finEnumShape` and `finEnumDirection`:

```lean
@[expose] def decidableEqA (F : FinitePresheafPFunctor I J) : DecidableEq F.toPresheafPFunctor.A :=
  F.finEnumA.decEq

@[expose] def decidableEqI (F : FinitePresheafPFunctor I J) : DecidableEq I :=
  F.finEnumI.decEq

@[expose] def decidableEqJ (F : FinitePresheafPFunctor I J) : DecidableEq J :=
  F.finEnumJ.decEq

@[expose] def finEnumShape (F : FinitePresheafPFunctor I J) (j : J) :
    FinEnum (F.toPresheafPFunctor.toSlicePFunctor.ShapeOver j) where
  card := (F.finEnumA.toList.filter
    (fun a => (F.decidableEqJ (F.toPresheafPFunctor.q a) j))).length
  equiv := -- Equiv from filtered list to Fin card, via List.get / List.idxOf
    { toFun := fun ⟨a, ha⟩ => ⟨F.finEnumA.toList.filter
        (fun a' => (F.decidableEqJ (F.toPresheafPFunctor.q a') j)).idxOf a,
        -- proof: idxOf < length from mem_filter.mpr ⟨mem_toList, ha⟩
        ...⟩
      invFun := fun i => ⟨(F.finEnumA.toList.filter
        (fun a' => (F.decidableEqJ (F.toPresheafPFunctor.q a') j))).get i,
        -- proof: the get element satisfies q _ = j, from mem_filter on get_mem
        ...⟩
      left_inv := -- by Subtype.ext; List.get_idxOf_self
        ...
      right_inv := -- by Fin.ext; List.idxOf_get (Nodup)
        ... }
  decEq := fun ⟨a, ha⟩ ⟨b, hb⟩ => F.finEnumA.decEq a b

@[expose] def finEnumDirection (F : FinitePresheafPFunctor I J)
    (a : F.toPresheafPFunctor.A) (i : I) :
    FinEnum (F.toPresheafPFunctor.toSliceDomPFunctor.DirectionOver a i) where
  card := ((F.finitary a).toList.filter
    (fun b => (F.decidableEqI (F.toPresheafPFunctor.rCurried a b) i))).length
  equiv := -- same pattern as finEnumShape, filtering (finitary a).toList
    ...
  decEq := fun ⟨b, hb⟩ ⟨c, hc⟩ => (F.finitary a).decEq b c
```

The equivalence proofs use `List.Nodup` from `FinEnum.nodup_toList`, `List.mem_filter`, `List.get_mem`, `List.get_idxOf_self`, and `List.idxOf_get`. The `Nodup` hypothesis is needed for `idxOf_get` (which requires the element appears exactly once). All proofs are constructive (no `Classical.choice`).

- [ ] **Step 3: Write the forwarding instances**

Four forwarding instances, each supplying the bundled fields explicitly via `@`:

```lean
instance decidableIsNatural (F : FinitePresheafPFunctor I J)
    {Z : Iᵒᵖ ⥤ Type uZ} [∀ i : I, DecidableEq (Z.obj ⟨i⟩)]
    (x : F.toPresheafPFunctor.toSliceDomPFunctor.Obj
      (PresheafDomPFunctorData.elemProj Z)) :
    Decidable (F.toPresheafPFunctor.toPresheafDomPFunctorData.IsNatural x) :=
  @PresheafDomPFunctorData.decidableIsNatural I _
    F.toPresheafPFunctor.toPresheafDomPFunctorData Z
    F.finitary F.finEnumI F.finEnumHomI inferInstance x

instance decidableCompatible (F : FinitePresheafPFunctor I J)
    {X : Type uX} (p : X → I) (a : F.toPresheafPFunctor.A)
    (v : F.toPresheafPFunctor.B a → X) :
    Decidable (F.toPresheafPFunctor.toSliceDomPFunctor.Compatible p a v) :=
  @SliceDomPFunctor.decidableCompatible I
    F.toPresheafPFunctor.toSliceDomPFunctor
    F.finitary F.decidableEqI _ p a v

instance decidableShapeOver (F : FinitePresheafPFunctor I J) (j : J) :
    DecidablePred (F.toPresheafPFunctor.toSlicePFunctor.ShapeOver j) :=
  @SlicePFunctor.decidableShapeOver I J F.toPresheafPFunctor.toSlicePFunctor
    F.decidableEqJ j

instance decidableDirectionOver (F : FinitePresheafPFunctor I J)
    (a : F.toPresheafPFunctor.A) (i : I) :
    DecidablePred (F.toPresheafPFunctor.toSliceDomPFunctor.DirectionOver a i) :=
  @SliceDomPFunctor.decidableDirectionOver I
    F.toPresheafPFunctor.toSliceDomPFunctor F.decidableEqI a i
```

- [ ] **Step 4: Verify compilation**

Run: `lake build Geb.Mathlib.Data.PFunctor.Presheaf.Finite.Basic`
Expected: compiles with no errors (warnings acceptable only from `linter.checkUnivs`)

- [ ] **Step 5: Verify axioms**

Use `#print axioms` (via LSP or a scratch file) on `finEnumShape`, `finEnumDirection`, and the forwarding instances.
Expected: `{propext, Quot.sound}` only; no `Classical.choice`.

- [ ] **Step 6: Commit**

---

### Task 2: `GebTests/.../Finite/Basic.lean` — general-tier reduction tests

**Files:**
- Create: `GebTests/Mathlib/Data/PFunctor/Presheaf/Finite/Basic.lean`

**Interfaces:**
- Consumes: `FinitePresheafPFunctor` and its forwarding instances from Task 1; the `wFixture` / `presheafWitness` patterns from `GebTests/Mathlib/Data/PFunctor/Presheaf/Decidable.lean`
- Produces: `decide`-reduction tests confirming the forwarding instances work

- [ ] **Step 1: Write the test module**

Build a `FinitePresheafPFunctor (Fin 2) (Fin 2)` from the existing `wFixture` data, re-declared locally in this test module (matching the existing pattern where test modules are self-contained; cross-test-file imports are not used in this repository). Supply:
- `finEnumI := finEnumFin2` (the choice-free `FinEnum (Fin 2)`)
- `finEnumHomI := finEnumHom` (the preorder hom-set enumeration)
- `finEnumJ := finEnumFin2`
- `finEnumHomJ := finEnumHom`
- `finEnumA` — a choice-free `FinEnum Shp` (4 elements; construct via `Equiv` with `Fin 4` or via explicit `toList`)
- `finitary := finitaryWFixture`

Test assertions (named `def`s, not bare `example`s):

```lean
/-- Shape-fiber membership: `R` is over index `1`. -/
def shapeOverTrue : Bool := decide (finiteWFixture.toPresheafPFunctor.toSlicePFunctor.ShapeOver 1 Shp.R)
example : shapeOverTrue = true := by decide

/-- Shape-fiber membership: `R` is not over index `0`. -/
def shapeOverFalse : Bool := decide (finiteWFixture.toPresheafPFunctor.toSlicePFunctor.ShapeOver 0 Shp.R)
example : shapeOverFalse = false := by decide

/-- Naturality of the good assignment. -/
def isNaturalTrue : Bool := decide (finiteWFixture.toPresheafPFunctor.toPresheafDomPFunctorData.IsNatural xGood)
example : isNaturalTrue = true := by decide

/-- Naturality of the bad assignment. -/
def isNaturalFalse : Bool := decide (finiteWFixture.toPresheafPFunctor.toPresheafDomPFunctorData.IsNatural xBad)
example : isNaturalFalse = false := by decide
```

- [ ] **Step 2: Run tests to verify they pass**

Run: `lake build GebTests.Mathlib.Data.PFunctor.Presheaf.Finite.Basic`
Expected: compiles, all `decide` reductions succeed.

- [ ] **Step 3: Commit**

---

### Task 3: `Finite/W.lean` — endofunctor tier

**Files:**
- Create: `Geb/Mathlib/Data/PFunctor/Presheaf/Finite/W.lean`

**Interfaces:**
- Consumes: `FinitePresheafPFunctor` from Task 1, `SlicePFunctor.wValidBool` / `wValidBool_eq_true_iff` (from `Slice/Decidable.lean`), `PresheafPFunctor.isHereditarilyNaturalBoolCore` / `isHereditarilyNaturalBoolCore_eq_true_iff` / `decidableIsHereditarilyNatural` (from `Presheaf/Decidable.lean`), `WType.instDecidableEq` (from `Data/W/Basic.lean`)
- Produces: `FinitePresheafPFunctor.wValidBool`, `wValidBool_eq_true_iff`, `wValidBool_imp_wValid`, `decidableWValid`, `decidableIsHereditarilyNatural`, `decidableEqW`, `decidableMemW`

- [ ] **Step 1: Write the module**

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.PFunctor.Presheaf.Finite.Basic

/-!
# Decidable W-type validity for finite presheaf polynomial endofunctors

For a finite presheaf polynomial endofunctor `F : FinitePresheafPFunctor I I`,
the combined `Bool`-valued validator `wValidBool` decides membership in the
W-type presheaf fiber by conjoining slice admissibility and hereditary
naturality. Forwarding instances supply the bundled finiteness evidence to the
existing decision procedures.

## Main definitions

* `FinitePresheafPFunctor.wValidBool` — the combined validator.
* `FinitePresheafPFunctor.decidableEqW` — `DecidableEq` on raw W-trees.
* `FinitePresheafPFunctor.decidableWValid` / `decidableIsHereditarilyNatural` /
  `decidableMemW` — forwarding instances for the endofunctor tier.

## Main statements

* `FinitePresheafPFunctor.wValidBool_eq_true_iff` — correctness given admissibility.
* `FinitePresheafPFunctor.wValidBool_imp_wValid` — admissibility from the verdict.

## Tags

polynomial functor, presheaf, W-type, decidability, FinEnum
-/
```

Key declarations (all in `namespace FinitePresheafPFunctor`, with `universe uI uA uB vI` and `variable {I : Type uI} [Category.{vI} I]`):

1. `wValidBool` — the combined validator, all instance args explicit:
```lean
@[expose] def wValidBool (F : FinitePresheafPFunctor I I) :
    F.toPresheafPFunctor.toPFunctor.W → Bool :=
  fun w ↦ @SlicePFunctor.wValidBool I F.toPresheafPFunctor.toSlicePFunctor
      F.finitary F.decidableEqI w
    && F.toPresheafPFunctor.isHereditarilyNaturalBoolCore
      F.decidableEqI F.finEnumI F.finEnumHomI F.finitary
      (@WType.instDecidableEq _ _ F.decidableEqA F.finitary) w
```

2. `wValidBool_imp_wValid` — admissibility from the Bool verdict:
```lean
theorem wValidBool_imp_wValid (F : FinitePresheafPFunctor I I)
    (w : F.toPresheafPFunctor.toPFunctor.W) :
    F.wValidBool w = true →
      F.toPresheafPFunctor.toSlicePFunctor.WValid w := by
  intro h
  rw [wValidBool, Bool.and_eq_true] at h
  exact (@SlicePFunctor.wValidBool_eq_true_iff I
    F.toPresheafPFunctor.toSlicePFunctor F.finitary F.decidableEqI w).mp h.1
```

3. `wValidBool_eq_true_iff` — correctness given admissibility:
```lean
theorem wValidBool_eq_true_iff (F : FinitePresheafPFunctor I I)
    (w : F.toPresheafPFunctor.toPFunctor.W)
    (hw : F.toPresheafPFunctor.toSlicePFunctor.WValid w) :
    F.wValidBool w = true ↔
      F.toPresheafPFunctor.IsHereditarilyNatural ⟨w, hw⟩ := by
  rw [wValidBool, Bool.and_eq_true]
  rw [(@SlicePFunctor.wValidBool_eq_true_iff I
    F.toPresheafPFunctor.toSlicePFunctor F.finitary F.decidableEqI w).mpr hw]
  simp only [true_and]
  exact F.toPresheafPFunctor.isHereditarilyNaturalBoolCore_eq_true_iff
    F.decidableEqI F.finEnumI F.finEnumHomI F.finitary
    (@WType.instDecidableEq _ _ F.decidableEqA F.finitary) ⟨w, hw⟩
```

4. `decidableWValid`, `decidableIsHereditarilyNatural` — forwarding instances:
```lean
instance decidableWValid (F : FinitePresheafPFunctor I I)
    (w : F.toPresheafPFunctor.toPFunctor.W) :
    Decidable (F.toPresheafPFunctor.toSlicePFunctor.WValid w) :=
  @SlicePFunctor.decidableWValid I F.toPresheafPFunctor.toSlicePFunctor
    F.finitary F.decidableEqI w

instance decidableIsHereditarilyNatural (F : FinitePresheafPFunctor I I)
    (w : { w : F.toPresheafPFunctor.toPFunctor.W //
      F.toPresheafPFunctor.toSlicePFunctor.WValid w }) :
    Decidable (F.toPresheafPFunctor.IsHereditarilyNatural w) :=
  @PresheafPFunctor.decidableIsHereditarilyNatural I _
    F.toPresheafPFunctor F.finitary F.finEnumI F.finEnumHomI
    F.decidableEqA w
```

5. `decidableEqW`:
```lean
@[expose] def decidableEqW (F : FinitePresheafPFunctor I I) :
    DecidableEq (WType F.toPresheafPFunctor.toPFunctor.B) :=
  @WType.instDecidableEq _ _ F.decidableEqA F.finitary
```

6. `decidableMemW` — two-stage decision on the existential:
```lean
instance decidableMemW (F : FinitePresheafPFunctor I I) (j : I)
    (w : F.toPresheafPFunctor.toPFunctor.W) :
    Decidable (∃ (hw : F.toPresheafPFunctor.toSlicePFunctor.WValid w),
      F.toPresheafPFunctor.toSlicePFunctor.wIndex ⟨w, hw⟩ = j ∧
        F.toPresheafPFunctor.IsHereditarilyNatural ⟨w, hw⟩) := by
  haveI := F.decidableEqI
  by_cases hw : F.toPresheafPFunctor.toSlicePFunctor.WValid w
  · by_cases hq : F.toPresheafPFunctor.toSlicePFunctor.wIndex ⟨w, hw⟩ = j
    · by_cases hn : F.toPresheafPFunctor.IsHereditarilyNatural ⟨w, hw⟩
      · exact isTrue ⟨hw, hq, hn⟩
      · exact isFalse (fun ⟨hw', _, hn'⟩ => hn (by convert hn'; exact Subtype.ext rfl))
    · exact isFalse (fun ⟨hw', hq', _⟩ => hq (by convert hq'; exact Subtype.ext rfl))
  · exact isFalse (fun ⟨hw', _⟩ => hw hw')
```

- [ ] **Step 2: Verify compilation**

Run: `lake build Geb.Mathlib.Data.PFunctor.Presheaf.Finite.W`
Expected: compiles with no errors.

- [ ] **Step 3: Verify axioms**

`#print axioms` on `wValidBool`, `decidableMemW`, `decidableEqW`.
Expected: `{propext, Quot.sound}` only.

- [ ] **Step 4: Commit**

---

### Task 4: `GebTests/.../Finite/W.lean` — endofunctor-tier reduction tests

**Files:**
- Create: `GebTests/Mathlib/Data/PFunctor/Presheaf/Finite/W.lean`

**Interfaces:**
- Consumes: `FinitePresheafPFunctor.wValidBool`, `decidableMemW`, `decidableEqW` from Task 3; the `wFixture` data (re-declared with the `FinitePresheafPFunctor` wrapper)
- Produces: `decide`-reduction tests for the combined validator

- [ ] **Step 1: Write the test module**

Build `finiteWFixture : FinitePresheafPFunctor (Fin 2) (Fin 2)` from the same fixture data as Task 2's test.

Test assertions:

```lean
/-- The good tree passes the combined validator. -/
def wValidGood : Bool := finiteWFixture.wValidBool goodTree.1
example : wValidGood = true := by decide

/-- The bad tree (fails naturality) fails the combined validator. -/
def wValidBad : Bool := finiteWFixture.wValidBool badTree.1
example : wValidBad = false := by decide

/-- An inadmissible tree fails the combined validator. -/
def wValidInadmissible : Bool := finiteWFixture.wValidBool inadmissibleTree
example : wValidInadmissible = false := by decide

/-- DecidableEq: two equal leaf trees. -/
def eqTrue : Bool := decide (leafTree .L0a = leafTree .L0a)
example : eqTrue = true := by decide

/-- DecidableEq: two distinct leaf trees. -/
def eqFalse : Bool := decide (leafTree .L0a = leafTree .L0b)
example : eqFalse = false := by decide

/-- decidableMemW: goodTree is in the fiber over index 1. -/
def memWTrue : Bool := decide (∃ (hw : finiteWFixture.toPresheafPFunctor.toSlicePFunctor.WValid goodTree.1),
  finiteWFixture.toPresheafPFunctor.toSlicePFunctor.wIndex ⟨goodTree.1, hw⟩ = 1 ∧
    finiteWFixture.toPresheafPFunctor.IsHereditarilyNatural ⟨goodTree.1, hw⟩)
example : memWTrue = true := by decide

/-- decidableMemW: goodTree is not in the fiber over index 0. -/
def memWFalse : Bool := decide (∃ (hw : finiteWFixture.toPresheafPFunctor.toSlicePFunctor.WValid goodTree.1),
  finiteWFixture.toPresheafPFunctor.toSlicePFunctor.wIndex ⟨goodTree.1, hw⟩ = 0 ∧
    finiteWFixture.toPresheafPFunctor.IsHereditarilyNatural ⟨goodTree.1, hw⟩)
example : memWFalse = false := by decide
```

The inadmissible tree fixture: a raw `WType` whose root shape is `R` but whose child at direction `0` has output index `1` (mismatching the direction-input map which says direction `0` lies over base index `0`). This is a raw tree that fails `WValid` but is still a well-formed `WType`.

- [ ] **Step 2: Run tests to verify they pass**

Run: `lake build GebTests.Mathlib.Data.PFunctor.Presheaf.Finite.W`
Expected: compiles, all `decide` reductions succeed.

- [ ] **Step 3: Commit**

---

### Task 5: Documentation, registration, and final verification

**Files:**
- Modify: `docs/index.md` (add entries for the two new modules)
- Modify: `TODO.md` (mark the finite-PRA workstream as in-progress/complete)

**Interfaces:**
- Consumes: the compiled modules from Tasks 1–4
- Produces: updated documentation, clean full-suite run

- [ ] **Step 1: Update `docs/index.md`**

Add entries for `Presheaf/Finite/Basic.lean` and `Presheaf/Finite/W.lean` after the existing presheaf decidability entry, following the existing format.

- [ ] **Step 2: Run the full test suite**

Run: `lake test`
Expected: all tests pass, no regressions.

- [ ] **Step 3: Run the linter**

Run: `lake lint`
Expected: no new warnings on the new modules (the `linter.checkUnivs` suppression is already in place via `set_option`).

- [ ] **Step 4: Verify axiom hygiene on all new declarations**

Run `#print axioms` on every public declaration in both new modules.
Expected: all within `{propext, Quot.sound}`.

- [ ] **Step 5: Commit**

---

## Validation Checklist

- [x] Spec coverage: every requirement in the spec has a task (structure → Task 1, derived finiteness → Task 1, general-tier instances → Task 1, endofunctor tier → Task 3, tests → Tasks 2 and 4, docs → Task 5)
- [x] Placeholder scan: no "TBD" or "implement later" in steps; module docstrings are written out; `finEnumShape`/`finEnumDirection` have code skeletons with proof obligations marked
- [x] Type consistency: interfaces match across tasks (Task 3 consumes `FinitePresheafPFunctor` from Task 1; Tasks 2 and 4 consume the forwarding instances)
- [x] Every step has actual content (code blocks or concrete skeletons with named proof obligations)
- [x] Verification commands use `lake build` (not `lake env lean`, per coding rules)
