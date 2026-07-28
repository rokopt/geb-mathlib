# FinSetSkel W1 Implementation Plan

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Global Constraints](#global-constraints)
- [Task 1: Choice-free `ofFn` for root `Vector`](#task-1-choice-free-offn-for-root-vector)
- [Task 2: Choice-free inversion of an injective list](#task-2-choice-free-inversion-of-an-injective-list)
- [Task 3: Choice-free inversion of an injective vector](#task-3-choice-free-inversion-of-an-injective-vector)
- [Task 4: `FinSetSkel` and its morphism API](#task-4-finsetskel-and-its-morphism-api)
- [Task 5: The skeleton comparison (wrapper)](#task-5-the-skeleton-comparison-wrapper)
- [Task 6: Documentation entries](#task-6-documentation-entries)
- [Task 7: Roadmap and subtree-rule amendments](#task-7-roadmap-and-subtree-rule-amendments)
- [Task 8: Remove the spec and the plan](#task-8-remove-the-spec-and-the-plan)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build `FinSetSkel`, a skeletal category of finite sets whose
morphisms are length-indexed vectors of codomain indices, choice-free,
together with its comparison to mathlib's `FintypeCat.Skeleton`.

**Architecture:** Four choice-free modules and one allowlisted
wrapper. `Data/Vector/OfFn.lean` supplies a choice-free `ofFn` for root
`Vector`, core's being `Classical.choice`-dependent.
`Data/List/NodupEquivFin.lean` and `Data/Vector/NodupEquivFin.lean`
supply the choice-free inversion of an injective list and vector.
`CategoryTheory/FinSetSkel/Basic.lean` carries the objects, the sealed
morphism API and the `SmallCategory` instance.
`CategoryTheory/FinSetSkel/Skeleton.lean` carries the mathlib-facing
packaging, which `Cat.category`'s dependence on `Classical.choice`
forces into the allowlist.

**Tech Stack:** Lean 4 (`leanprover/lean4:v4.33.0-rc1`), mathlib and
Batteries at the `.lake/packages/` pins, `lake` for build/test/lint,
`jj` for version control.

## Global Constraints

- **No `noncomputable`, anywhere.** `CONTRIBUTING.md`
  § Constructive-only.
- **Choice-free means `propext` and `Quot.sound` only.** Every
  declaration in Tasks 1-4 must satisfy this; only
  `Geb.Mathlib.CategoryTheory.FinSetSkel.Skeleton` and its `GebTests`
  parallel may depend on `Classical.choice`, and only after being
  added to `GebMeta.classicalAllowedModules`.
- **Never use core's `Vector.ofFn`, `Vector.range` or
  `Vector.finRange`, nor `Array.toList_ofFn` / `List.toArray_ofFn`.**
  Their lemmas are `@[simp, grind =]` and choice-tainted, so a bare
  `simp` or `grind` meeting such a term silently introduces
  `Classical.choice`. Use `Vector.ofFnC` from Task 1.
- **Never import `Batteries.Data.Vector.Lemmas`.** It is permitted by
  the allow-list but brings choice-tainted `@[simp]` `Vector.get_ofFn`
  and `Vector.get_range` into the `get` normal form.
- **Application-normal form is `f.toVec.get i`**, `i : Fin X.len`.
  `Vector.get_eq_getElem` (Task 1) bridges to the `getElem` API and is
  deliberately not `@[simp]`.
- **`Geb/Mathlib/` imports only `Mathlib.*`, `Batteries.*` and
  `Geb.Mathlib.*`**; no bare umbrella `import Mathlib`.
  `scripts/lint-imports.sh` enforces this.
- **Every module carries the repository header**: the four-line
  copyright block (`Copyright (c) 2026 Terence Rokop. All rights
  reserved.` / `Released under Apache 2.0 license as described in the
  file LICENSE.` / `Authors: Terence Rokop`), then `module`, then
  `public import` lines, then the `/-! ... -/` module docstring, then
  `@[expose] public section`.
- **Commits use `jj`, never `git`.** A PreToolUse hook blocks mutating
  `git`. Use `jj commit -m "<message>"` with no path arguments.
- **Commit messages follow mathlib's Conventional-Commits form**:
  `feat`, `fix`, `doc`, `style`, `refactor`, `test`, `chore`, `perf`,
  `ci`.
- **Axiom and computability checks run through the `lean-lsp` MCP**,
  never `lake env lean` (`docs/rules/lean-coding.md`).
- **Test modules name a `def` or `theorem` built from the module under
  test.** `lake shake` cannot see imports used only inside `example`,
  and reports a false "remove import".
- **If a mathlib or toolchain bump lands mid-branch, re-verify the
  axiom findings before continuing.** The spec's findings are pinned
  to `leanprover/lean4:v4.33.0-rc1`. A core repair of
  `Array.getElem_ofFn_go` would leave `Vector.ofFnC` and its round
  trips duplicating core; a rename in the `ofFn` family would break
  Task 1. Re-run the `#print axioms` checks of Tasks 1-5.

---

## Task 1: Choice-free `ofFn` for root `Vector`

**Files:**

- Create: `Geb/Mathlib/Data/Vector/OfFn.lean`
- Create: `Geb/Mathlib/Data/Vector.lean` (directory index)
- Modify: `Geb/Mathlib/Data.lean` (add `public import Geb.Mathlib.Data.Vector`)
- Test: `GebTests/Mathlib/Data/Vector/OfFn.lean`
- Test: `GebTests/Mathlib/Data/Vector.lean` (directory index)
- Test: `GebTests/Mathlib/Data.lean` (add `import GebTests.Mathlib.Data.Vector`)

**Interfaces:**

- Consumes: nothing from other tasks.
- Produces:

```lean
Vector.ofFnC {α : Type u} {n : Nat} (f : Fin n → α) : Vector α n

Vector.getElem_ofFnC (f : Fin n → α) (i : Nat) (h : i < n) :
    (ofFnC f)[i] = f ⟨i, h⟩

Vector.get_eq_getElem (v : Vector α n) (i : Fin n) :
    v.get i = v[(i : Nat)]

@[simp] Vector.get_ofFnC (f : Fin n → α) (i : Fin n) :
    (ofFnC f).get i = f i

@[simp] Vector.ofFnC_get (v : Vector α n) : ofFnC v.get = v
```

- [ ] **Step 1: Create the directory index files**

`Geb/Mathlib/Data/Vector.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.Vector.OfFn

/-!
# Vector — index
-/
```

`GebTests/Mathlib/Data/Vector.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import GebTests.Mathlib.Data.Vector.OfFn

/-!
# Vector tests — index
-/
```

Add `public import Geb.Mathlib.Data.Vector` to `Geb/Mathlib/Data.lean`
and `import GebTests.Mathlib.Data.Vector` to `GebTests/Mathlib/Data.lean`,
both in alphabetical position (before `Geb.Mathlib.Data.W` /
`GebTests.Mathlib.Data.W`).

- [ ] **Step 2: Write `Geb/Mathlib/Data/Vector/OfFn.lean`**

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Mathlib.Data.Vector.Basic

/-!
# A choice-free `ofFn` for root `Vector`

Core builds `Vector.ofFn` on `Array.ofFn`, whose indexing lemmas
depend on `Classical.choice` through the private
`Array.getElem_ofFn_go`; the dependence reaches `Vector.getElem_ofFn`,
`Vector.ofFn_getElem`, `Vector.getElem_range` and
`Vector.getElem_finRange`. Routing the construction through
`List.ofFn` instead avoids it: every ingredient below is choice-free,
and the result is still array-backed, so indexing stays
constant-time.

`ofFnC` is not related to `Vector.ofFn` by any choice-free equation —
the bridge would be `List.toArray_ofFn`, itself choice-dependent — so
the two coexist unrelated, and choice-free modules use this one.

`get_eq_getElem` restates Batteries'
`Batteries.Data.Vector.Lemmas.get_eq_getElem`, which is unreachable:
no `Mathlib.*` module imports that file, and the bare umbrella
`import Mathlib` that would reach it is forbidden in
upstream-eligible files. Importing Batteries directly is permitted but
declined, because it would bring the choice-tainted `@[simp]`
`Vector.get_ofFn` and `Vector.get_range` into scope.

## Main definitions

* `Vector.ofFnC` — the choice-free `ofFn`.

## Main statements

* `Vector.getElem_ofFnC`, `Vector.get_ofFnC`, `Vector.ofFnC_get` — the
  indexing lemma and the two round trips.
* `Vector.get_eq_getElem` — the bridge to the `getElem` API,
  deliberately not `simp`.

## Tags

vector, ofFn, choice-free
-/

@[expose] public section

universe u

namespace Vector

/-- A vector from an index function, built through `List.ofFn` so that
no `Classical.choice`-dependent lemma is needed to reason about it. -/
def ofFnC {α : Type u} {n : Nat} (f : Fin n → α) : Vector α n :=
  ⟨(List.ofFn f).toArray, by rw [List.size_toArray, List.length_ofFn]⟩

/-- Indexing `ofFnC` at a `Nat` recovers the function. -/
theorem getElem_ofFnC {α : Type u} {n : Nat} (f : Fin n → α)
    (i : Nat) (h : i < n) : (ofFnC f)[i] = f ⟨i, h⟩ := by
  rw [ofFnC, getElem_mk, List.getElem_toArray, List.getElem_ofFn]

/-- The `Fin`-indexed accessor is the `Nat`-indexed one. Not `simp`:
the `get` form is the normal form, and marking this in either
orientation would rewrite it away. -/
theorem get_eq_getElem {α : Type u} {n : Nat} (v : Vector α n)
    (i : Fin n) : v.get i = v[(i : Nat)] := rfl

/-- Indexing `ofFnC` at a `Fin` recovers the function. -/
@[simp] theorem get_ofFnC {α : Type u} {n : Nat} (f : Fin n → α)
    (i : Fin n) : (ofFnC f).get i = f i := getElem_ofFnC f i.1 i.2

/-- `ofFnC` inverts indexing. -/
@[simp] theorem ofFnC_get {α : Type u} {n : Nat} (v : Vector α n) :
    ofFnC v.get = v :=
  Vector.ext fun i hi => getElem_ofFnC _ i hi

end Vector
```

- [ ] **Step 3: Build**

Run: `lake build Geb.Mathlib.Data.Vector.OfFn`
Expected: no errors.

- [ ] **Step 4: Verify the axioms**

Through the `lean-lsp` MCP (`mcp__lean-lsp__lean_run_code`), on a
snippet importing `Geb.Mathlib.Data.Vector.OfFn`:

```lean
#print axioms Vector.ofFnC
#print axioms Vector.getElem_ofFnC
#print axioms Vector.get_eq_getElem
#print axioms Vector.get_ofFnC
#print axioms Vector.ofFnC_get
```

Expected: `Vector.ofFnC` depends on `[propext]`; the other four on
`[propext, Quot.sound]`. Any `Classical.choice` is a failure — check
that no `Vector.ofFn`/`range`/`finRange` lemma crept in.

- [ ] **Step 5: Confirm the `@[simp]` lemmas fire**

`ofFnC_get` is a higher-order pattern (`ofFnC (fun i => v.get i) = v`),
so whether `simp` matches it is confirmed rather than assumed. Through
`lean-lsp`, on a snippet importing the module:

```lean
example (v : Vector Nat 3) : Vector.ofFnC v.get = v := by simp
example (f : Fin 3 → Nat) (i : Fin 3) : (Vector.ofFnC f).get i = f i := by simp
```

Expected: both close. If `ofFnC_get` does not fire, remove its
`@[simp]` and apply it by name at its use sites; `get_ofFnC` is
first-order and must fire either way.

- [ ] **Step 6: Write `GebTests/Mathlib/Data/Vector/OfFn.lean`**

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.Data.Vector.OfFn

/-!
# Tests for the choice-free `ofFn`

A sample index function round-trips through `ofFnC` in both
directions, and the `get`/`getElem` bridge holds at a sample index.

## Tags

vector, ofFn
-/

@[expose] public section

/-- A sample index function. -/
def sampleIdx : Fin 3 → Nat := fun i => 2 * i.1

/-- The sample vector built from it. -/
def sampleVec : Vector Nat 3 := Vector.ofFnC sampleIdx

/-- `ofFnC` recovers the sample function pointwise. -/
theorem sampleVec_get (i : Fin 3) : sampleVec.get i = sampleIdx i :=
  Vector.get_ofFnC sampleIdx i

/-- `ofFnC` inverts indexing on the sample vector. -/
theorem sampleVec_roundtrip : Vector.ofFnC sampleVec.get = sampleVec :=
  Vector.ofFnC_get sampleVec

/-- The bridge holds at a sample index. -/
theorem sampleVec_bridge : sampleVec.get ⟨1, by omega⟩ = sampleVec[1] :=
  Vector.get_eq_getElem sampleVec ⟨1, by omega⟩
```

- [ ] **Step 7: Build and lint**

Run: `lake build GebTests.Mathlib.Data.Vector.OfFn && lake lint && lake lint GebTests`
Expected: no errors, no linter output.

- [ ] **Step 8: Check imports**

Run: `scripts/lint-imports.sh`
Expected: exit 0.

- [ ] **Step 9: Commit**

```bash
jj commit -m "feat(vector): choice-free ofFn for root Vector

Core's Vector.ofFn indexing lemmas depend on Classical.choice through
the private Array.getElem_ofFn_go. Routing construction through
List.ofFn avoids it while leaving the result array-backed. Adds the
get/getElem bridge, Batteries' being unreachable from Mathlib.*
modules."
```

---

## Task 2: Choice-free inversion of an injective list

**Files:**

- Create: `Geb/Mathlib/Data/List/NodupEquivFin.lean`
- Create: `Geb/Mathlib/Data/List.lean` (directory index)
- Modify: `Geb/Mathlib/Data.lean` (add `public import Geb.Mathlib.Data.List`)
- Test: `GebTests/Mathlib/Data/List/NodupEquivFin.lean`
- Test: `GebTests/Mathlib/Data/List.lean` (directory index)
- Test: `GebTests/Mathlib/Data.lean` (add `import GebTests.Mathlib.Data.List`)

**Interfaces:**

- Consumes: nothing from other tasks.
- Produces:

```lean
List.Nodup.getEquivC {α : Type u} [DecidableEq α] (l : List α)
    (H : l.Nodup) : Fin l.length ≃ {x // x ∈ l}

Fin.compressC {n : ℕ} (p : Fin n → Bool) :
    Fin ((List.finRange n).filter p).length ≃ {i : Fin n // p i}
```

- [ ] **Step 1: Create the directory index files**

`Geb/Mathlib/Data/List.lean` and `GebTests/Mathlib/Data/List.lean`,
each in the shape of Task 1 Step 1 with `List` in place of `Vector`
and `Geb.Mathlib.Data.List.NodupEquivFin` /
`GebTests.Mathlib.Data.List.NodupEquivFin` as the single import. Add
the corresponding lines to `Geb/Mathlib/Data.lean` and
`GebTests/Mathlib/Data.lean` in alphabetical position (after
`FinEnum`, before `PFunctor`).

- [ ] **Step 2: Write `Geb/Mathlib/Data/List/NodupEquivFin.lean`**

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.Logic.Equiv.Basic

/-!
# Choice-free inversion of a duplicate-free list

`List.Nodup.getEquiv` depends on `Classical.choice` through a single
ingredient, `List.idxOf_lt_length_iff`. Substituting
`List.idxOf_lt_length_of_mem`, which depends on `propext` alone,
rebuilds it choice-free. `Fin.compressC` renumbers the indices
satisfying a decidable predicate, which is what an equalizer or a
coequalizer carrier needs.

## Main definitions

* `List.Nodup.getEquivC` — the choice-free rebuild of
  `List.Nodup.getEquiv`.
* `Fin.compressC` — the indices satisfying a predicate, renumbered.

## Tags

list, nodup, equiv, choice-free
-/

@[expose] public section

universe u

namespace List.Nodup

/-- Indices of a duplicate-free list correspond to its members.
Choice-free rebuild of `List.Nodup.getEquiv`. -/
def getEquivC {α : Type u} [DecidableEq α] (l : List α) (H : l.Nodup) :
    Fin l.length ≃ {x // x ∈ l} where
  toFun i := ⟨l.get i, List.get_mem _ _⟩
  invFun x := ⟨l.idxOf ↑x, List.idxOf_lt_length_of_mem x.2⟩
  left_inv i := by simp only [List.get_idxOf, Fin.eta, H]
  right_inv x := by simp

end List.Nodup

namespace Fin

/-- The indices of `Fin n` satisfying `p`, renumbered onto an initial
segment. -/
def compressC {n : ℕ} (p : Fin n → Bool) :
    Fin ((List.finRange n).filter p).length ≃ {i : Fin n // p i} :=
  (List.Nodup.getEquivC _ ((List.nodup_finRange n).filter p)).trans
    (Equiv.subtypeEquivRight (fun x => by simp [List.mem_filter]))

end Fin
```

- [ ] **Step 3: Build**

Run: `lake build Geb.Mathlib.Data.List.NodupEquivFin`
Expected: no errors.

- [ ] **Step 4: Verify the axioms**

Through `lean-lsp`, on a snippet importing the module:

```lean
#print axioms List.Nodup.getEquivC
#print axioms Fin.compressC
```

Expected: both `[propext, Quot.sound]`.

- [ ] **Step 5: Write `GebTests/Mathlib/Data/List/NodupEquivFin.lean`**

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.Data.List.NodupEquivFin

/-!
# Tests for the choice-free list inversion

A sample duplicate-free list round-trips through `getEquivC`, and
`compressC` renumbers a sample predicate's indices.

## Tags

list, nodup, equiv
-/

@[expose] public section

/-- A sample duplicate-free list. -/
def sampleList : List Nat := [7, 3, 5]

/-- It is duplicate-free. -/
theorem sampleList_nodup : sampleList.Nodup := by decide

/-- `getEquivC` round-trips a sample index. -/
theorem sampleList_roundtrip :
    (List.Nodup.getEquivC sampleList sampleList_nodup).symm
      (List.Nodup.getEquivC sampleList sampleList_nodup ⟨1, by decide⟩) =
      ⟨1, by decide⟩ :=
  (List.Nodup.getEquivC sampleList sampleList_nodup).left_inv _

/-- A sample decidable predicate on `Fin 4`. -/
def samplePred : Fin 4 → Bool := fun i => decide (i.1 % 2 = 0)

/-- `compressC` round-trips a sample compressed index. -/
theorem sampleCompress_roundtrip
    (i : Fin ((List.finRange 4).filter samplePred).length) :
    (Fin.compressC samplePred).symm (Fin.compressC samplePred i) = i :=
  (Fin.compressC samplePred).left_inv i
```

- [ ] **Step 6: Build and lint**

Run:

```bash
lake build GebTests.Mathlib.Data.List.NodupEquivFin
lake lint && lake lint GebTests
```

Expected: no errors.

- [ ] **Step 7: Commit**

```bash
jj commit -m "feat(list): choice-free inversion of a duplicate-free list

List.Nodup.getEquiv depends on Classical.choice through
List.idxOf_lt_length_iff alone; substituting
List.idxOf_lt_length_of_mem rebuilds it choice-free. Adds the
predicate compression that W3's equalizer and W4's coequalizer
carriers consume."
```

---

## Task 3: Choice-free inversion of an injective vector

**Files:**

- Create: `Geb/Mathlib/Data/Vector/NodupEquivFin.lean`
- Modify: `Geb/Mathlib/Data/Vector.lean` (add the import)
- Test: `GebTests/Mathlib/Data/Vector/NodupEquivFin.lean`
- Test: `GebTests/Mathlib/Data/Vector.lean` (add the import)

**Interfaces:**

- Consumes: `Vector.get_eq_getElem` (Task 1);
  `List.Nodup.getEquivC` (Task 2).
- Produces:

```lean
Vector.invOfInjectiveC {n k : ℕ} (ι : Vector (Fin n) k)
    (h : Function.Injective ι.get) :
    Fin k ≃ {j : Fin n // j ∈ ι.toList}
```

- [ ] **Step 1: Write `Geb/Mathlib/Data/Vector/NodupEquivFin.lean`**

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.List.NodupEquivFin
public import Geb.Mathlib.Data.Vector.OfFn

/-!
# Choice-free inversion of an injective vector

The operation inverts an injective `ι : Vector (Fin n) k` — the
vector, not a function `Fin k → Fin n`, since morphisms of
`FinSetSkel` are vectors. The hypothesis is stated over `ι.get`, the
application-normal form, rather than over `ι.toList.Nodup`;
`List.nodup_iff_injective_get` relates the two.

This module targets mathlib rather than Lean core or Batteries: its
statement is an `Equiv`, which exists in neither.

## Main definitions

* `Vector.invOfInjectiveC` — the inverse of an injective vector.

## Tags

vector, injective, equiv, choice-free
-/

@[expose] public section

namespace Vector

/-- An injective vector corresponds to the set of its entries. -/
def invOfInjectiveC {n k : ℕ} (ι : Vector (Fin n) k)
    (h : Function.Injective ι.get) :
    Fin k ≃ {j : Fin n // j ∈ ι.toList} :=
  have hlen : ι.toList.length = k := by simp
  have hnd : ι.toList.Nodup := by
    rw [List.nodup_iff_injective_get]
    intro a b hab
    have ha : (a : ℕ) < k := lt_of_lt_of_eq a.isLt hlen
    have hb : (b : ℕ) < k := lt_of_lt_of_eq b.isLt hlen
    have key : ι.get ⟨a, ha⟩ = ι.get ⟨b, hb⟩ := by
      simpa [Vector.get_eq_getElem, Vector.getElem_toList,
        List.get_eq_getElem] using hab
    exact Fin.ext (congrArg (Fin.val (n := k)) (h key))
  (finCongr hlen.symm).trans (List.Nodup.getEquivC _ hnd)

end Vector
```

Add `public import Geb.Mathlib.Data.Vector.NodupEquivFin` to
`Geb/Mathlib/Data/Vector.lean` (alphabetically before `OfFn`) and
`import GebTests.Mathlib.Data.Vector.NodupEquivFin` to
`GebTests/Mathlib/Data/Vector.lean`.

- [ ] **Step 2: Build**

Run: `lake build Geb.Mathlib.Data.Vector.NodupEquivFin`
Expected: no errors.

- [ ] **Step 3: Verify the axioms**

Through `lean-lsp`: `#print axioms Vector.invOfInjectiveC`
Expected: `[propext, Quot.sound]`.

- [ ] **Step 4: Write `GebTests/Mathlib/Data/Vector/NodupEquivFin.lean`**

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.Data.Vector.NodupEquivFin

/-!
# Tests for the injective-vector inversion

A sample injective vector round-trips through `invOfInjectiveC`.

## Tags

vector, injective, equiv
-/

@[expose] public section

/-- A sample injective vector. -/
def sampleInj : Vector (Fin 5) 3 :=
  Vector.ofFnC (fun i => ⟨i.1 + 1, by omega⟩)

/-- It is injective on indices. -/
theorem sampleInj_injective : Function.Injective sampleInj.get := by
  intro a b hab
  simp only [sampleInj, Vector.get_ofFnC] at hab
  have : a.1 + 1 = b.1 + 1 := congrArg Fin.val hab
  exact Fin.ext (by omega)

/-- The inversion round-trips a sample index. -/
theorem sampleInj_roundtrip (i : Fin 3) :
    (Vector.invOfInjectiveC sampleInj sampleInj_injective).symm
      (Vector.invOfInjectiveC sampleInj sampleInj_injective i) = i :=
  (Vector.invOfInjectiveC sampleInj sampleInj_injective).left_inv i
```

- [ ] **Step 5: Build and lint**

Run:

```bash
lake build GebTests.Mathlib.Data.Vector.NodupEquivFin
lake lint && lake lint GebTests
```

Expected: no errors.

- [ ] **Step 6: Commit**

```bash
jj commit -m "feat(vector): choice-free inversion of an injective vector

Stated over the get view fixed as the application-normal form rather
than over toList.Nodup, which List.nodup_iff_injective_get relates to
it. Consumed by W3's equalizer, W3's row m and W4's coequalizer."
```

---

## Task 4: `FinSetSkel` and its morphism API

**Files:**

- Create: `Geb/Mathlib/CategoryTheory/FinSetSkel/Basic.lean`
- Create: `Geb/Mathlib/CategoryTheory/FinSetSkel.lean` (directory index)
- Modify: `Geb/Mathlib/CategoryTheory.lean` (add the import)
- Test: `GebTests/Mathlib/CategoryTheory/FinSetSkel/Basic.lean`
- Test: `GebTests/Mathlib/CategoryTheory/FinSetSkel.lean` (directory index)
- Test: `GebTests/Mathlib/CategoryTheory.lean` (add the import)

**Interfaces:**

- Consumes: `Vector.ofFnC`, `Vector.get_ofFnC` (Task 1).
- Produces:
  - `FinSetSkel : Type u`, a one-field structure with `len : ℕ`,
    `@[ext]`, `DecidableEq`, `Repr`, `Inhabited`
  - `FinSetSkel.Hom (X Y : FinSetSkel.{u}) : Type u`
  - `FinSetSkel.Hom.ofVec`, `FinSetSkel.Hom.toVec` and both round
    trips `toVec_ofVec`, `ofVec_toVec`
  - `FinSetSkel.smallCategory : SmallCategory FinSetSkel.{u}`
  - `@[ext] FinSetSkel.hom_ext`, and `hom_ext_iff` generated by it
  - `@[simp] FinSetSkel.id_get`, `@[simp] FinSetSkel.comp_get`
  - `FinSetSkel.decidableEqHom`, `FinSetSkel.reprHom`
  - `FinSetSkel.ofIdxFun`, `FinSetSkel.toIdxFun` and the round trips
    `ofIdxFun_toIdxFun`, `toIdxFun_ofIdxFun`

**Declaration order is load-bearing.** After
`attribute [irreducible] FinSetSkel.Hom`, a body writing `.down`
against the sealed type fails with "invalid projection", and so does
any `rfl` reducing through it. Every pointwise lemma is therefore
stated before the seal over `Hom.id`, `Hom.comp` and `Hom.ofIdxFun'`;
the seal follows; the categorical forms and the pinned instances come
after.

- [ ] **Step 1: Create the directory index files**

`Geb/Mathlib/CategoryTheory/FinSetSkel.lean` and
`GebTests/Mathlib/CategoryTheory/FinSetSkel.lean`, in the shape of
Task 1 Step 1, each importing `Basic` only — `Skeleton` does not exist
until Task 5, and importing it now would leave this task's build red.
Task 5 Step 3 adds it. Add the corresponding lines to
`Geb/Mathlib/CategoryTheory.lean` and
`GebTests/Mathlib/CategoryTheory.lean`.

- [ ] **Step 2: Write `Geb/Mathlib/CategoryTheory/FinSetSkel/Basic.lean`**

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.Vector.OfFn
public import Mathlib.CategoryTheory.Category.Basic

/-!
# `FinSetSkel`: a skeletal category of finite sets with vector morphisms

Objects are natural numbers; a morphism `X ⟶ Y` is a vector of `X.len`
indices into `Fin Y.len`. mathlib's `FintypeCat.Skeleton` has the same
objects up to the evident bijection with ℕ but takes morphisms to be
functions, whose equality is decidable only through
`Classical.choice`. Morphisms here are data: they can be
pattern-matched through `toVec`, serialised through `Repr`, and
compared through `DecidableEq`, all choice-free.

The objects are a one-field structure rather than `ULift ℕ` with `mk`
and `len` as definitions. A definition is opaque at reducible
transparency, so `Fin (mk n).len` would not match a lemma stated at
`Fin X.len` and no `simp` lemma would fire; the repair, marking `mk`
and `len` `@[reducible]`, cannot be confined to this module, and every
downstream construction is stated over `Fin X.len`. A structure
projection reduces by iota, which is available at reducible
transparency, so no reducibility attribute is needed anywhere.

The morphism representation is root-namespace `Vector`, not
`List.Vector`. The evidence runs both ways and is recorded so the
decision is not revisited on one side of it.
`Mathlib/Data/Vector/Defs.lean` says both "Any combination of reducing
the use of `List.Vector` in Mathlib, or modernising its API, would be
welcome" and "Typically, if you are doing programming or verification,
you will primarily use `Vector α n`, and if you are doing mathematics,
you may want to use `List.Vector α n` instead." On axioms
`List.Vector` is the cleaner: its `DecidableEq` is axiom-free where
root `Vector`'s costs `propext` and `Quot.sound`, and its `get_ofFn`
and `ofFn_get` are choice-free where root `Vector`'s are not, which
costs the five declarations of `Geb/Mathlib/Data/Vector/OfFn.lean`.
Root `Vector` is chosen because composition is the operation this
category exists to run: composing `f : X ⟶ Y` with `g : Y ⟶ Z` is
`O(X.len)` here and `O(X.len² + X.len · Y.len)` on the list-backed
representation, whose indexing is linear.

The API shape — a named `Hom`, an `ofVec`/`toVec` pair, `@[ext]`, the
`@[simp]` application lemmas, then `attribute [irreducible]` — is
mathlib's own, from `SimplexCategory`. Only the shape is borrowed:
`SimplexCategory.Hom` is a bundled monotone function and its
hom-`DecidableEq` depends on `Classical.choice`.

## Main definitions

* `FinSetSkel` — the objects.
* `FinSetSkel.Hom`, `FinSetSkel.Hom.ofVec`, `FinSetSkel.Hom.toVec` —
  the morphisms and their representation.
* `FinSetSkel.smallCategory` — the category instance.
* `FinSetSkel.ofIdxFun`, `FinSetSkel.toIdxFun` — the correspondence
  with lifted index functions, which the skeleton comparison uses.

## Main statements

* `FinSetSkel.hom_ext` — morphisms agreeing indexwise are equal.
* `FinSetSkel.id_get`, `FinSetSkel.comp_get` — the
  application-normal form for identity and composition.

## References

* [nLabSkeletalCategory] — skeletal categories and the skeleton of a
  category. In the absence of the axiom of choice the entry notes that
  a weak skeleton is the more appropriate notion; the skeletality of
  this category is established in the wrapper module, which is where
  `Classical.choice` is permitted.

## Tags

category, finite set, skeleton, vector, choice-free
-/

@[expose] public section

universe u

open CategoryTheory

/-- An object of the skeletal category of finite sets: a length. -/
@[ext] structure FinSetSkel : Type u where
  /-- The number of elements. -/
  len : ℕ
  deriving DecidableEq, Repr

namespace FinSetSkel

instance : Inhabited FinSetSkel.{u} := ⟨⟨0⟩⟩

/-- A morphism is a vector of codomain indices, one per domain index.
The `ULift` is outside the vector, so index types stay at `Type 0`. -/
protected def Hom (X Y : FinSetSkel.{u}) : Type u :=
  ULift.{u} (Vector (Fin Y.len) X.len)

namespace Hom

variable {X Y Z : FinSetSkel.{u}}

/-- A morphism from its vector. -/
def ofVec (v : Vector (Fin Y.len) X.len) : FinSetSkel.Hom X Y :=
  ULift.up v

/-- The vector of a morphism. -/
def toVec (f : FinSetSkel.Hom X Y) : Vector (Fin Y.len) X.len := f.down

@[simp] theorem toVec_ofVec (v : Vector (Fin Y.len) X.len) :
    (ofVec v).toVec = v := rfl

@[simp] theorem ofVec_toVec (f : FinSetSkel.Hom X Y) :
    ofVec f.toVec = f := rfl

/-- The identity morphism. -/
protected def id (X : FinSetSkel.{u}) : FinSetSkel.Hom X X :=
  ofVec (Vector.ofFnC _root_.id)

/-- Composition of morphisms. -/
protected def comp (f : FinSetSkel.Hom X Y) (g : FinSetSkel.Hom Y Z) :
    FinSetSkel.Hom X Z :=
  ofVec (Vector.ofFnC fun i => g.toVec.get (f.toVec.get i))

/-- A morphism from a lifted index function. -/
def ofIdxFun' (g : ULift.{u} (Fin X.len) → ULift.{u} (Fin Y.len)) :
    FinSetSkel.Hom X Y :=
  ofVec (Vector.ofFnC fun i => (g (ULift.up i)).down)

theorem ext' {f g : FinSetSkel.Hom X Y}
    (h : ∀ i, f.toVec.get i = g.toVec.get i) : f = g :=
  congrArg ULift.up (Vector.ext fun i hi => h ⟨i, hi⟩)

theorem id_get' (X : FinSetSkel.{u}) (i : Fin X.len) :
    (Hom.id X).toVec.get i = i := Vector.get_ofFnC _ _

theorem comp_get' (f : FinSetSkel.Hom X Y) (g : FinSetSkel.Hom Y Z)
    (i : Fin X.len) :
    (Hom.comp f g).toVec.get i = g.toVec.get (f.toVec.get i) :=
  Vector.get_ofFnC _ _

theorem ofIdxFun'_get
    (g : ULift.{u} (Fin X.len) → ULift.{u} (Fin Y.len)) (i : Fin X.len) :
    (ofIdxFun' g).toVec.get i = (g (ULift.up i)).down :=
  Vector.get_ofFnC _ _

end Hom

attribute [irreducible] FinSetSkel.Hom

instance smallCategory : SmallCategory FinSetSkel.{u} where
  Hom X Y := FinSetSkel.Hom X Y
  id X := Hom.id X
  comp f g := Hom.comp f g
  id_comp f := Hom.ext' fun i => by rw [Hom.comp_get', Hom.id_get']
  comp_id f := Hom.ext' fun i => by rw [Hom.comp_get', Hom.id_get']
  assoc f g h := Hom.ext' fun i => by
    rw [Hom.comp_get', Hom.comp_get', Hom.comp_get', Hom.comp_get']

/-- Morphisms agreeing at every index are equal. -/
@[ext] theorem hom_ext {X Y : FinSetSkel.{u}} {f g : X ⟶ Y}
    (h : ∀ i, f.toVec.get i = g.toVec.get i) : f = g := Hom.ext' h

@[simp] theorem id_get (X : FinSetSkel.{u}) (i : Fin X.len) :
    (𝟙 X : X ⟶ X).toVec.get i = i := Hom.id_get' X i

@[simp] theorem comp_get {X Y Z : FinSetSkel.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (i : Fin X.len) :
    (f ≫ g).toVec.get i = g.toVec.get (f.toVec.get i) :=
  Hom.comp_get' f g i

/-- Decidable equality of morphisms, pinned to the choice-free route.
Instance search does not unfold the `Hom` definition, so this does not
follow from the category instance; and `instDecidableEqOfLawfulBEq`
inhabits the same class through the choice-dependent
`Vector.instLawfulBEq`, so leaving the instance to search would let a
bump silently change its axioms. -/
instance decidableEqHom (X Y : FinSetSkel.{u}) : DecidableEq (X ⟶ Y) :=
  fun f g => decidable_of_iff (f.toVec = g.toVec)
    ⟨fun h => hom_ext fun i => congrArg (·.get i) h,
     fun h => congrArg Hom.toVec h⟩

/-- Morphisms are serialisable, through their vector. -/
instance reprHom (X Y : FinSetSkel.{u}) : Repr (X ⟶ Y) :=
  ⟨fun f n => reprPrec f.toVec n⟩

/-- A morphism from a lifted index function. -/
def ofIdxFun {X Y : FinSetSkel.{u}}
    (g : ULift.{u} (Fin X.len) → ULift.{u} (Fin Y.len)) : X ⟶ Y :=
  Hom.ofIdxFun' g

@[simp] theorem ofIdxFun_get {X Y : FinSetSkel.{u}}
    (g : ULift.{u} (Fin X.len) → ULift.{u} (Fin Y.len)) (i : Fin X.len) :
    (ofIdxFun g).toVec.get i = (g (ULift.up i)).down :=
  Hom.ofIdxFun'_get g i

/-- The lifted index function of a morphism. -/
def toIdxFun {X Y : FinSetSkel.{u}} (f : X ⟶ Y) :
    ULift.{u} (Fin X.len) → ULift.{u} (Fin Y.len) :=
  fun i => ULift.up (f.toVec.get i.down)

@[simp] theorem ofIdxFun_toIdxFun {X Y : FinSetSkel.{u}} (f : X ⟶ Y) :
    ofIdxFun (toIdxFun f) = f :=
  hom_ext fun i => by simp only [ofIdxFun_get, toIdxFun]

@[simp] theorem toIdxFun_ofIdxFun {X Y : FinSetSkel.{u}}
    (g : ULift.{u} (Fin X.len) → ULift.{u} (Fin Y.len)) :
    toIdxFun (ofIdxFun g) = g :=
  funext fun i => by simp only [toIdxFun, ofIdxFun_get]

end FinSetSkel
```

- [ ] **Step 3: Build**

Run: `lake build Geb.Mathlib.CategoryTheory.FinSetSkel.Basic`
Expected: no errors.

- [ ] **Step 4: Verify the axioms**

Through `lean-lsp`, on a snippet importing the module:

```lean
#print axioms FinSetSkel.smallCategory
#print axioms FinSetSkel.hom_ext
#print axioms FinSetSkel.id_get
#print axioms FinSetSkel.comp_get
#print axioms FinSetSkel.decidableEqHom
#print axioms FinSetSkel.reprHom
#print axioms FinSetSkel.ofIdxFun_toIdxFun
#print axioms FinSetSkel.toIdxFun_ofIdxFun
```

Expected: every one `[propext, Quot.sound]`. A `Classical.choice`
here means the module needs the allowlist, which it must not.

- [ ] **Step 5: Confirm `hom_ext_iff` was generated**

Through `lean-lsp`: `#check @FinSetSkel.hom_ext_iff`
Expected: it exists. `@[ext]` on a hand-written theorem generates the
bidirectional companion; do not write one by hand, and do not use
`@[ext (iff := false)]`.

- [ ] **Step 6: Write `GebTests/Mathlib/CategoryTheory/FinSetSkel/Basic.lean`**

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.CategoryTheory.FinSetSkel.Basic

/-!
# Tests for `FinSetSkel`

Sample morphisms compose, the identity acts as such at sample
indices, decidable equality and `Repr` compute, and the index-function
correspondence round-trips.

## Tags

category, finite set, skeleton
-/

@[expose] public section

open CategoryTheory

/-- A sample object. -/
def objThree : FinSetSkel.{0} := ⟨3⟩

/-- A second sample object. -/
def objTwo : FinSetSkel.{0} := ⟨2⟩

/-- A sample morphism collapsing three indices onto two. -/
def sampleHom : objThree ⟶ objTwo :=
  FinSetSkel.Hom.ofVec (Vector.ofFnC (fun i => ⟨i.1 % 2, by omega⟩))

/-- Composition with the identity is the morphism, indexwise. -/
theorem sampleHom_id_comp (i : Fin objThree.len) :
    (𝟙 objThree ≫ sampleHom).toVec.get i = sampleHom.toVec.get i := by
  simp

/-- Decidable equality of morphisms computes. -/
theorem sampleHom_decEq : (sampleHom = sampleHom) := by decide

/-- The index-function correspondence round-trips the sample. -/
theorem sampleHom_idxFun_roundtrip :
    FinSetSkel.ofIdxFun (FinSetSkel.toIdxFun sampleHom) = sampleHom :=
  FinSetSkel.ofIdxFun_toIdxFun sampleHom
```

- [ ] **Step 7: Build and lint**

Run:

```bash
lake build GebTests.Mathlib.CategoryTheory.FinSetSkel.Basic
lake lint && lake lint GebTests
```

Expected: no errors.

- [ ] **Step 8: Commit**

```bash
jj commit -m "feat(finsetskel): the category and its vector morphism API

Objects are a one-field structure, whose projection reduces at
reducible transparency where a definition would not and would force a
global @[reducible] on three downstream workstreams. Morphisms are
ULift-wrapped vectors of codomain indices, with the SimplexCategory
API shape and the representation sealed once the API is in place.
Decidable equality is pinned to the choice-free route."
```

---

## Task 5: The skeleton comparison (wrapper)

**Files:**

- Create: `Geb/Mathlib/CategoryTheory/FinSetSkel/Skeleton.lean`
- Modify: `Geb/Mathlib/CategoryTheory/FinSetSkel.lean` (add the import)
- Modify: `GebMeta.lean` (two allowlist entries)
- Test: `GebTests/Mathlib/CategoryTheory/FinSetSkel/Skeleton.lean`
- Test: `GebTests/Mathlib/CategoryTheory/FinSetSkel.lean` (add the import)

**Interfaces:**

- Consumes: everything Task 4 produces.
- Produces: `FinSetSkel.toSkeleton`, `ofSkeleton`,
  `toSkeleton_comp_ofSkeleton`, `ofSkeleton_comp_toSkeleton`,
  `catIso`, `skeletonEquivalence`, `incl`, `skeletal`, `isSkeleton`.

- [ ] **Step 1: Add the allowlist entries to `GebMeta.lean`**

In `classicalAllowedModules`, add to the bracketed literal:

```lean
   `Geb.Mathlib.CategoryTheory.FinSetSkel.Skeleton,
   `GebTests.Mathlib.CategoryTheory.FinSetSkel.Skeleton,
```

Keep the `].foldl (·.insert ·)` terminator on the final element.

- [ ] **Step 2: Write `Geb/Mathlib/CategoryTheory/FinSetSkel/Skeleton.lean`**

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinSetSkel.Basic
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.CategoryTheory.Skeletal

/-!
# `FinSetSkel` compared with mathlib's skeleton

`FinSetSkel` and `FintypeCat.Skeleton` are the same category
presented differently: the comparison functors are mutually inverse on
the nose, giving an isomorphism in `Cat` rather than merely an
equivalence.

This module is allowlisted for `Classical.choice`, which
`CategoryTheory.Cat.category` depends on: an isomorphism in `Cat` is
an `Iso` with respect to that instance, so its type carries the
dependence however it is constructed. The comparison functors
themselves are choice-free; the taint enters the composite identities
through `CategoryTheory.Functor.comp` in their statements. Everything
pointwise is in `FinSetSkel.Basic`, so this module packages rather
than argues.

The isomorphism is closed by `CategoryTheory.Functor.hext`, which
takes object equality together with `HEq` of the morphism components.
`Functor.ext` does not close it: its `h_map` obligation retains
`eqToHom` applied to `(F ⋙ G).obj X = (𝟭 _).obj X`, on which
`eqToHom_refl` cannot fire. Write both names qualified — under
`open CategoryTheory` a bare `Functor.ext` resolves to the
`LawfulFunctor` lemma and errors with a message mentioning `f <$> x`.

## Main definitions

* `FinSetSkel.toSkeleton`, `FinSetSkel.ofSkeleton` — the comparison
  functors.
* `FinSetSkel.catIso` — the isomorphism in `Cat`.
* `FinSetSkel.skeletonEquivalence` — the equivalence, defined as
  `Cat.equivOfIso` of the isomorphism so that a reader arriving at the
  weaker statement is led to the stronger one.
* `FinSetSkel.incl` — the inclusion into `FintypeCat`.

## Main statements

* `FinSetSkel.skeletal` — isomorphic objects are equal.
* `FinSetSkel.isSkeleton` — `FinSetSkel` is a skeleton of
  `FintypeCat`.

## Tags

category, skeleton, equivalence
-/

@[expose] public section

universe u

open CategoryTheory

namespace FinSetSkel

/-- The comparison functor to mathlib's skeleton. -/
def toSkeleton : FinSetSkel.{u} ⥤ FintypeCat.Skeleton.{u} where
  obj X := FintypeCat.Skeleton.mk X.len
  map f := toIdxFun f
  map_id X := funext fun i => congrArg ULift.up (id_get X i.down)
  map_comp f g := funext fun i => congrArg ULift.up (comp_get f g i.down)

/-- The comparison functor from mathlib's skeleton. -/
def ofSkeleton : FintypeCat.Skeleton.{u} ⥤ FinSetSkel.{u} where
  obj X := ⟨X.len⟩
  map {X Y} g := ofIdxFun (X := ⟨X.len⟩) (Y := ⟨Y.len⟩) g
  map_id X := hom_ext fun i => by rw [ofIdxFun_get, id_get]; rfl
  map_comp f g := hom_ext fun i => by
    rw [ofIdxFun_get, comp_get, ofIdxFun_get, ofIdxFun_get]; rfl

theorem toSkeleton_comp_ofSkeleton :
    toSkeleton.{u} ⋙ ofSkeleton.{u} = Functor.id _ :=
  CategoryTheory.Functor.hext (fun _ => rfl) fun X Y f =>
    heq_of_eq (ofIdxFun_toIdxFun f)

theorem ofSkeleton_comp_toSkeleton :
    ofSkeleton.{u} ⋙ toSkeleton.{u} = Functor.id _ :=
  CategoryTheory.Functor.hext (fun _ => rfl) fun X Y f =>
    heq_of_eq (toIdxFun_ofIdxFun (X := ⟨X.len⟩) (Y := ⟨Y.len⟩) f)

/-- `FinSetSkel` and mathlib's skeleton are isomorphic in `Cat`. -/
def catIso : Cat.of FinSetSkel.{u} ≅ Cat.of FintypeCat.Skeleton.{u} where
  hom := toSkeleton.toCatHom
  inv := ofSkeleton.toCatHom
  hom_inv_id := Cat.ext (by
    simp only [Cat.Hom.comp_toFunctor, Cat.Hom.id_toFunctor,
      Functor.toCatHom_toFunctor]
    exact toSkeleton_comp_ofSkeleton)
  inv_hom_id := Cat.ext (by
    simp only [Cat.Hom.comp_toFunctor, Cat.Hom.id_toFunctor,
      Functor.toCatHom_toFunctor]
    exact ofSkeleton_comp_toSkeleton)

/-- The equivalence, derived from the isomorphism. -/
def skeletonEquivalence : FinSetSkel.{u} ≌ FintypeCat.Skeleton.{u} :=
  Cat.equivOfIso catIso

instance toSkeleton_isEquivalence : toSkeleton.{u}.IsEquivalence :=
  skeletonEquivalence.isEquivalence_functor

/-- The inclusion of `FinSetSkel` into `FintypeCat`. -/
def incl : FinSetSkel.{u} ⥤ FintypeCat.{u} :=
  toSkeleton ⋙ FintypeCat.Skeleton.incl

instance incl_isEquivalence : incl.{u}.IsEquivalence := by
  unfold incl; infer_instance

/-- Isomorphic objects of `FinSetSkel` are equal. -/
theorem skeletal : Skeletal FinSetSkel.{u} := fun X Y ⟨e⟩ =>
  FinSetSkel.ext (congrArg FintypeCat.Skeleton.len
    (FintypeCat.Skeleton.is_skeletal ⟨toSkeleton.mapIso e⟩))

/-- `FinSetSkel` is a skeleton of `FintypeCat`. -/
theorem isSkeleton : IsSkeletonOf FintypeCat.{u} FinSetSkel.{u} incl where
  skel := skeletal

end FinSetSkel
```

- [ ] **Step 3: Add the import to the directory index files**

`public import Geb.Mathlib.CategoryTheory.FinSetSkel.Skeleton` in
`Geb/Mathlib/CategoryTheory/FinSetSkel.lean`, and the `GebTests`
counterpart.

- [ ] **Step 4: Build**

Run: `lake build Geb.Mathlib.CategoryTheory.FinSetSkel.Skeleton`
Expected: no errors.

- [ ] **Step 5: Verify the axioms**

Through `lean-lsp`:

```lean
#print axioms FinSetSkel.toSkeleton
#print axioms FinSetSkel.ofSkeleton
#print axioms FinSetSkel.catIso
#print axioms FinSetSkel.skeletonEquivalence
#print axioms FinSetSkel.incl
#print axioms FinSetSkel.skeletal
#print axioms FinSetSkel.isSkeleton
```

Expected: the two functors `[propext, Quot.sound]`; the rest
`[propext, Classical.choice, Quot.sound]`.

- [ ] **Step 6: Confirm nothing is `noncomputable`**

`FintypeCat.Skeleton.equivalence` is `noncomputable` and must not be
reached. `Skeleton.incl` and `Cat.equivOfIso`, which are used, are
computable. Confirm the module compiles with no `noncomputable`
modifier anywhere; `CONTRIBUTING.md` § Constructive-only forbids it.

- [ ] **Step 7: Write `GebTests/Mathlib/CategoryTheory/FinSetSkel/Skeleton.lean`**

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.CategoryTheory.FinSetSkel.Skeleton

/-!
# Tests for the skeleton comparison

The comparison functors agree on a sample object, and the isomorphism
in `Cat` has the comparison functors as its components.

## Tags

category, skeleton
-/

@[expose] public section

open CategoryTheory

/-- The comparison functors are mutually inverse on a sample object. -/
theorem sampleObj_roundtrip :
    FinSetSkel.ofSkeleton.obj (FinSetSkel.toSkeleton.obj ⟨4⟩) =
      (⟨4⟩ : FinSetSkel.{0}) :=
  rfl

/-- The isomorphism's forward component is the comparison functor. -/
theorem sampleCatIso_hom :
    FinSetSkel.catIso.{0}.hom = FinSetSkel.toSkeleton.toCatHom :=
  rfl
```

- [ ] **Step 8: Build, lint and check the allowlist takes effect**

Run:

```bash
lake build GebTests.Mathlib.CategoryTheory.FinSetSkel.Skeleton
lake lint && lake lint GebTests
```

Expected: no errors. If the axiom linter reports
`Classical.choice` for a declaration in `FinSetSkel.Skeleton`, the
allowlist entry in Step 1 is missing or misspelled — `NameSet` accepts
a name for a nonexistent module silently.

- [ ] **Step 9: Commit**

```bash
jj commit -m "feat(finsetskel): the comparison with mathlib's skeleton

The comparison functors are mutually inverse on the nose, so the
categories are isomorphic in Cat and not merely equivalent. Cat's own
category instance depends on Classical.choice, so the isomorphism
cannot be choice-free however it is built, and this module is
allowlisted; the functors themselves are choice-free and everything
pointwise stays in Basic."
```

---

## Task 6: Documentation entries

**Files:**

- Modify: `docs/index.md` (§ Implemented content)
- Modify: `docs/references.bib` (add `nLabSkeletalCategory`)

**Interfaces:**

- Consumes: the module paths from Tasks 1-5.
- Produces: nothing consumed by later tasks.

- [ ] **Step 1: Add the bibliography entry**

In `docs/references.bib`, in the shape of the existing
`nLabParametricRightAdjoint`:

```bibtex
@misc{nLabSkeletalCategory,
  author        = {{nLab authors}},
  title         = {Skeletal category},
  howpublished  = {\url{https://ncatlab.org/nlab/show/skeletal+category}},
  note          = {nLab wiki entry},
}
```

The canonical URL is `skeletal+category`;
`skeleton+of+a+category` redirects to it with a 301, and
`.../show/skeleton` is a separate disambiguation page.

- [ ] **Step 2: Add the `docs/index.md` entries**

Append to § Implemented content, in the file's existing style:

```markdown
- `Geb/Mathlib/Data/Vector/OfFn.lean` — a choice-free `ofFn` for
  root `Vector`. Core's `Vector.ofFn` indexing lemmas depend on
  `Classical.choice` through the private `Array.getElem_ofFn_go`;
  `Vector.ofFnC` routes construction through `List.ofFn` instead,
  leaving the result array-backed and indexing constant-time.
  `Vector.get_eq_getElem` bridges to the `getElem` API.
  `Classical.choice`-free.
- `Geb/Mathlib/Data/List/NodupEquivFin.lean` — extensions of
  mathlib's `Mathlib/Data/List/NodupEquivFin.lean`.
  `List.Nodup.getEquivC` rebuilds `List.Nodup.getEquiv` choice-free,
  substituting `List.idxOf_lt_length_of_mem` for the
  `Classical.choice`-dependent `List.idxOf_lt_length_iff`.
  `Fin.compressC` renumbers the indices satisfying a decidable
  predicate onto an initial segment. `Classical.choice`-free.
- `Geb/Mathlib/Data/Vector/NodupEquivFin.lean` —
  `Vector.invOfInjectiveC` inverts an injective vector, stated over
  the `get` view rather than over `toList.Nodup`.
  `Classical.choice`-free.
- `Geb/Mathlib/CategoryTheory/FinSetSkel/Basic.lean` — `FinSetSkel`,
  a skeletal category of finite sets whose morphisms are
  length-indexed vectors of codomain indices. Objects are a one-field
  structure, so the length projection reduces at reducible
  transparency; morphisms carry `DecidableEq` and `Repr`, both pinned
  to choice-free terms, and the representation is sealed once the
  `ofVec`/`toVec` API is in place. `Classical.choice`-free.
- `Geb/Mathlib/CategoryTheory/FinSetSkel/Skeleton.lean` — the
  comparison with `FintypeCat.Skeleton`. The comparison functors are
  mutually inverse on the nose, giving an isomorphism in `Cat` and
  not merely an equivalence, together with the transported `Skeletal`
  and `IsSkeletonOf`. Allowlisted for `Classical.choice`:
  `CategoryTheory.Cat.category` depends on it, so an `Iso` in `Cat`
  carries the dependence however it is built.
```

- [ ] **Step 3: Regenerate the table of contents and lint**

Run: `doctoc --update-only . && markdownlint-cli2 '**/*.md'`
Expected: "Everything is OK" and 0 issues.

- [ ] **Step 4: Commit**

```bash
jj commit -m "doc(finsetskel): index and bibliography entries

Records the five modules under docs/index.md and adds the nLab
skeletal-category entry the FinSetSkel docstring cites."
```

---

## Task 7: Roadmap and subtree-rule amendments

The spec's § Amendments to `TODO.md` and the documents stating subtree
rules is the authority for this task; apply every item in it. The list
below is the checklist, not a substitute for that section — read it
before starting.

**Files:**

- Modify: `TODO.md`
- Modify: `docs/index.md` (§ Directory structure)
- Modify: `Geb.lean` (root docstring)
- Modify: `Geb/Mathlib.lean` (docstring heading, body sentence, and
  the stale import clause)
- Modify: `README.md` (§ Upstream targets)
- Modify: `docs/rules/upstream-eligible.md` (§ Two-track development
  step 1; § Subtree import rules)
- Modify: `docs/process.md` (§ Two-track development)
- Modify: `scripts/lint-imports.sh` (comment header)
- Modify: `scripts/extract-pr.sh` (comments at both mapping arms)

- [ ] **Step 1: Apply the `TODO.md` amendments**

Working through the spec's § Amendments in order: W0's precedence; the
objects; constraint 9 appended; the remaining decisions of § Decisions
fixed here added to the W1 bullet; the index equivalences (W1 bullet,
constraint 4, constraint 7's first sentence only — its second sentence
is retained verbatim); the isomorphism's placement; the representation
paragraph; the evidence pointer; the two § Triggers entries; the
§ Next up item; the § Standing obligations entry; and the status
table's W1 row.

- [ ] **Step 2: Apply the subtree-rule amendments**

Every place stating `Geb/Mathlib/`'s upstream target, per the spec:
`docs/index.md` § Directory structure; `Geb.lean`'s root docstring;
`Geb/Mathlib.lean`'s docstring heading and body sentence; `README.md`
§ Upstream targets; `docs/rules/upstream-eligible.md` § Two-track
development step 1 and § Subtree import rules; `docs/process.md`
§ Two-track development; `scripts/lint-imports.sh`'s comment header;
and comments at both `scripts/extract-pr.sh` mapping arms. Also
correct `Geb/Mathlib.lean`'s stale "import only from `Mathlib.*` or
`Geb.Mathlib.*`", which W0 left behind when it admitted `Batteries.*`.

- [ ] **Step 3: Verify the scripts still pass their own tests**

Run: `scripts/tests/test-lint-imports.sh && scripts/tests/test-extract-pr.sh`
Expected: both pass. The changes are to comments only; a failure means
a code line was touched.

- [ ] **Step 4: Regenerate the table of contents and lint**

Run: `doctoc --update-only . && markdownlint-cli2 '**/*.md'`
Expected: "Everything is OK" and 0 issues.

- [ ] **Step 5: Commit**

```bash
jj commit -m "doc(finsetskel): amend the roadmap and the subtree rules

Records what W1's re-verification changed for the workstreams that
read TODO.md from main: W0 no longer precedes W1, the objects are a
structure, the index-equivalence transports are dropped and their
choice-taint assigned to W3, the isomorphism moves to the wrapper, and
constraint 9 states the ofFn ban and the pinned-instance rule.

Corrects every place stating Geb/Mathlib/'s upstream target, since a
module may now target Lean core where the subtree import rules leave
no alternative, and the stale import clause W0 left in
Geb/Mathlib.lean."
```

---

## Task 8: Remove the spec and the plan

`CONTRIBUTING.md` § Concern shape orders the branch: commits adding
the spec and plan, then the implementation, then commits removing
them. They are transient — they record how the current state was
reached, not what it is — and must not reach `main`'s working tree.

**Files:**

- Delete: `docs/superpowers/specs/2026-07-28-finsetskel-w1-design.md`
- Delete: `docs/superpowers/plans/2026-07-28-finsetskel-w1.md`

- [ ] **Step 1: Confirm nothing durable still depends on them**

Run:

```bash
grep -rn "2026-07-28-finsetskel-w1" \
  --include=*.md --include=*.lean --include=*.sh . \
  | grep -v docs/superpowers
```

Expected: no matches. The `TODO.md` evidence pointer records the
spec's `jj` change-id, not its path, so it survives the deletion.

- [ ] **Step 2: Delete both files**

```bash
rm docs/superpowers/specs/2026-07-28-finsetskel-w1-design.md
rm docs/superpowers/plans/2026-07-28-finsetskel-w1.md
```

- [ ] **Step 3: Run the full pre-push checklist**

Run: `scripts/pre-push.sh`
Expected: every step passes — `lake build`, `lake test`, `lake lint`,
`lake lint GebTests`, `lake shake`, `scripts/lint-imports.sh`, the
script tests, `scripts/check-commit-msg.sh` and the `doctoc` check.

If `lake shake` reports an import to remove from a `GebTests` module,
confirm the module names a `def` or `theorem` built from the module
under test rather than only an `example`; that is the usual cause of a
false report.

- [ ] **Step 4: Commit**

```bash
jj commit -m "doc(finsetskel): remove the W1 spec and plan

Transient per CONTRIBUTING.md section Concern shape: they record how
the current state was reached, not what it is. Reachable in history;
the TODO.md evidence pointer carries the change-id."
```

- [ ] **Step 5: Hand back for review**

Do not push. `AGENTS.md` § No `jj git push` without user line-by-line
review binds this branch, as does `CONTRIBUTING.md` § Working. Report
the branch state and wait.
