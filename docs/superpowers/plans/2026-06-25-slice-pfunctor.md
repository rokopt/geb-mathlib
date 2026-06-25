# Slice polynomial functors (increment A) Implementation Plan

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Global Constraints](#global-constraints)
  - [Task 1: Scaffolding and the two structures (core file)](#task-1-scaffolding-and-the-two-structures-core-file)
  - [Task 2: The compatibility predicate](#task-2-the-compatibility-predicate)
  - [Task 3: Curried constructor and accessor](#task-3-curried-constructor-and-accessor)
  - [Task 4: Core object/morphism maps and functoriality (choice-free)](#task-4-core-objectmorphism-maps-and-functoriality-choice-free)
  - [Task 5: Categorical wrapper and allowlist entry](#task-5-categorical-wrapper-and-allowlist-entry)
  - [Task 6: Concept documentation and full verification](#task-6-concept-documentation-and-full-verification)
- [Post-implementation (handled outside this plan)](#post-implementation-handled-outside-this-plan)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Define slice polynomial functors on `Type` as a restriction
of mathlib's `PFunctor` interpretation: a `Classical.choice`-free
constructive core, plus a thin categorical wrapper realizing the
action as a `CategoryTheory.Functor` between `Over` categories.

**Architecture:** Two content files. `Basic.lean` (constructive core,
no `Over`/`CategoryTheory.Functor`) holds the structures, the
`Compatible` predicate, the curried constructor, and the object map
`obj`, morphism action `map`, shape lemma `map_fst`, and functoriality
lemmas `map_id`/`map_comp` as plain functions and equalities — held to
the strict `{propext, Quot.sound}` axiom set, so a green `lake lint`
certifies choice-freeness. `Functor.lean` (wrapper) packages the core
maps as `domFunctor : Over dom ⥤ Type` and `functor : Over dom ⥤
Over cod` (via `Functor.toOver`); because `Over` is `Classical.choice`-
dependent at the type level, its module is added to
`GebMeta.classicalAllowedModules`.

**Tech Stack:** Lean 4 (toolchain `v4.32.0-rc1`), mathlib4
(`PFunctor`, `CategoryTheory.Over`, `Functor.toOver`, `TypeCat`),
`GebMeta` axiom linter, `lake`, `jj` (VCS).

## Global Constraints

From `docs/superpowers/specs/2026-06-25-slice-pfunctor-design.md` and
repo rules. Every task's requirements implicitly include these.

- **Subtree:** `Geb/Mathlib/` (upstream-eligible). Imports only from
  `Mathlib.*` or `Geb.Mathlib.*`. The prefix `Geb.Mathlib.` appears
  only in `import` lines, never in namespaces/bodies/docstrings.
- **The core/wrapper boundary is load-bearing.** `Basic.lean` must
  name no `Over` and no `CategoryTheory.Functor` (either pulls
  `Classical.choice`); its module is NOT on the allowlist, so a green
  `lake lint` is positive proof it is choice-free. Only `Functor.lean`
  names `Over`, and its module `Geb.Mathlib.Data.PFunctor.Slice.Functor`
  is added to `GebMeta.classicalAllowedModules`.
- **Constructive-only:** no `noncomputable`, no `sorry`/`admit` in
  committed code. `Classical.choice` is permitted ONLY in
  `Functor.lean` (via the allowlist); forbidden everywhere else.
- **`@[expose]` is load-bearing**, not boilerplate: `obj`, `map`,
  `map_fst` carry it so the wrapper can unfold them to discharge `Over`
  laws and the tag triangle (`#print axioms` confirms exposure adds no
  `Classical.choice`).
- **Module system:** copyright block, then `module`; imports after
  `module`, before the docstring. `public import` for re-exported
  modules. A file with public declarations needs the public surface
  (`module` makes declarations private by default).
- **Style:** 2-space indent, 100-char lines, Unicode, `autoImplicit
  = false`. `snake_case` Prop lemmas; `lowerCamelCase` defs;
  `UpperCamelCase` structures and `Prop`-valued predicate defs;
  `@[ext]` on structures. Docstrings on every `def`/`structure`/field/
  predicate; module docstrings carry `# Title`, summary,
  `## Main definitions`, `## Implementation notes`, `## References`,
  `## Tags` (omit `## Main statements`/`## Notation`).
- **`Type u` morphisms are bundled** (`TypeCat.Hom`): promote a
  function to a hom with `↾`; apply a hom via its `FunLike` coercion or
  `ConcreteCategory.hom`; prove hom-equalities with `ext`. Project
  lints: `;` not `<;>` for a single goal; `change`, never goal-changing
  `show` (`linter.style.show`); a `simp only` closing by
  `TypeCat.hom_ofHom` + reduction may flag core lemmas as unused
  (`linter.unusedSimpArgs`) — use a local `set_option` if so.
- **VCS:** `jj` only (a hook blocks raw mutating `git`). Commits land
  on bookmark `feat/slice-pfunctor`. No push without line-by-line user
  review.
- **Verification gates:** `lake build`, `lake build GebTests`,
  `lake test`, `lake lint`, `lake lint -- GebTests`, `lake shake
  --add-public --keep-implied --keep-prefix Geb GebTests`,
  `scripts/lint-imports.sh`, `markdownlint-cli2` on touched Markdown.

The core (`obj`/`map`/`map_fst`/`map_id`/`map_comp`) and the wrapper
were compiled against the pin during spec review; the core was
confirmed choice-free by `#print axioms`. Proof bodies below are the
verified strategy; where a tactic still fails, use the `lean4` skills
(`lean4:prove`, LSP `lean_goal`/`lean_diagnostic_messages`) to repair
it without changing the stated interface.

---

### Task 1: Scaffolding and the two structures (core file)

**Files:**

- Create: `Geb/Mathlib/Data.lean`, `Geb/Mathlib/Data/PFunctor.lean`,
  `Geb/Mathlib/Data/PFunctor/Slice.lean` (directory indexes)
- Create: `Geb/Mathlib/Data/PFunctor/Slice/Basic.lean` (core content)
- Modify: `Geb/Mathlib.lean` (umbrella import)
- Create: `GebTests/Mathlib/Data.lean`,
  `GebTests/Mathlib/Data/PFunctor.lean`,
  `GebTests/Mathlib/Data/PFunctor/Slice.lean` (test indexes)
- Create: `GebTests/Mathlib/Data/PFunctor/Slice/Basic.lean` (tests)
- Modify: `GebTests/Mathlib.lean` (test umbrella import)

**Interfaces:**

- Produces: `SliceDomPFunctor (dom : Type u)` with `s : toPFunctor.Idx
  → dom`; `SlicePFunctor (dom cod : Type u) extends SliceDomPFunctor
  dom` with `t : toPFunctor.A → cod`. Both `@[ext]`.

Note: `Basic.lean` imports ONLY `Mathlib.Data.PFunctor.Univariate.Basic`
— NOT `Over` (the core must stay choice-free). The `Slice.lean` index
imports `Slice.Basic` now and gains `Slice.Functor` in Task 5.

- [ ] **Step 1: Write the failing test**

Create `GebTests/Mathlib/Data/PFunctor/Slice/Basic.lean`:

```lean
/-
Copyright (c) 2026 The geb-mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The geb-mathlib contributors
-/
module

import Geb.Mathlib.Data.PFunctor.Slice.Basic

-- Test files keep their declarations private; silence the
-- only-private-declarations lint.
set_option linter.privateModule false

/-!
# Tests for the slice polynomial functor core
-/

open SliceDomPFunctor SlicePFunctor

/-- A concrete slice polynomial functor: one shape, two `Bool`-indexed
positions, constraint `s ⟨(), b⟩ = b`, tag into `Unit`. -/
def testSlice : SlicePFunctor Bool Unit where
  A := Unit
  B := fun _ => Bool
  s := fun x => x.2
  t := fun _ => ()

example : testSlice.s ⟨(), true⟩ = true := rfl
example : testSlice.t () = () := rfl
```

- [ ] **Step 2: Run to verify it fails**

Run: `lake build GebTests.Mathlib.Data.PFunctor.Slice.Basic`
Expected: FAIL — module `Geb.Mathlib.Data.PFunctor.Slice.Basic` not
found / `unknown identifier 'SliceDomPFunctor'`.

- [ ] **Step 3: Create the core module with the structures**

Create `Geb/Mathlib/Data/PFunctor/Slice/Basic.lean`:

```lean
/-
Copyright (c) 2026 The geb-mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The geb-mathlib contributors
-/
module

public import Mathlib.Data.PFunctor.Univariate.Basic

/-!
# Slice polynomial functors on `Type` (constructive core)

A `PFunctor` is the middle leg of a Gambino–Hyland polynomial diagram
`dom ◀ s ─ Idx ─ fst ▶ A ─ t ▶ cod`. Adding `s : Idx → dom` and
`t : A → cod` yields a polynomial functor `Type/dom → Type/cod`,
defined as a restriction of the interpretation `P.Obj X = Σ a, B a → X`
to `s`-compatible position assignments, tagged by `t`.

This file is the constructive core: the structures, the compatibility
predicate, the curried constructor, and the object/morphism maps with
their functoriality stated as plain equalities. It names no `Over` and
no `CategoryTheory.Functor`, so it is `Classical.choice`-free (the
strict axiom linter certifies this). The categorical packaging is in
the sibling `Slice.Functor` module.

## Main definitions

* `SliceDomPFunctor`, `SlicePFunctor` — the structures.
* `SliceDomPFunctor.Compatible` — the position-compatibility predicate.
* `SliceDomPFunctor.obj` / `map` — the domain-restricted functor's
  object and morphism maps; `map_id` / `map_comp` its functoriality.

## Implementation notes

`obj` is a subtype of `PFunctor.Obj`; `map` is `PFunctor.map`
restricted; functoriality reuses `LawfulFunctor (PFunctor.Obj _)`.
`obj`, `map`, `ofCurried`, and `sCurried` are `@[expose]` so the
wrapper and tests can unfold them across the module boundary; exposure
introduces no `Classical.choice`. (`map_fst` is a theorem — `@[expose]`
is `def`-only — and needs no exposure.)

## References

* N. Gambino and M. Hyland, *Wellfounded trees and dependent
  polynomial functors*, TYPES 2003.
* J. Kock, *Polynomial functors and polynomial monads*.

## Tags

polynomial functor, dependent polynomial functor, slice category,
container, PFunctor
-/

public section

universe u

/-- A polynomial functor with a constraint leg `s` assigning each
position (an element of `PFunctor.Idx`) a `dom`-index. -/
structure SliceDomPFunctor (dom : Type u) extends PFunctor.{u, u} where
  /-- The constraint leg: each position is assigned a `dom`-index. -/
  s : toPFunctor.Idx → dom

/-- A `SliceDomPFunctor` with a tag leg `t` assigning each shape a
`cod`-index. -/
structure SlicePFunctor (dom cod : Type u) extends SliceDomPFunctor dom where
  /-- The tag leg: each shape is assigned a `cod`-index. -/
  t : toPFunctor.A → cod

attribute [ext] SliceDomPFunctor SlicePFunctor
```

Create the directory index files. `Geb/Mathlib/Data/PFunctor/Slice.lean`:

```lean
/-
Copyright (c) 2026 The geb-mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The geb-mathlib contributors
-/
module

public import Geb.Mathlib.Data.PFunctor.Slice.Basic

/-!
# Slice — index
-/
```

`Geb/Mathlib/Data/PFunctor.lean`:

```lean
/-
Copyright (c) 2026 The geb-mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The geb-mathlib contributors
-/
module

public import Geb.Mathlib.Data.PFunctor.Slice

/-!
# PFunctor — index
-/
```

`Geb/Mathlib/Data.lean`:

```lean
/-
Copyright (c) 2026 The geb-mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The geb-mathlib contributors
-/
module

public import Geb.Mathlib.Data.PFunctor

/-!
# Data — index
-/
```

Modify `Geb/Mathlib.lean`: insert between `module` and the `/-! … -/`
docstring:

```lean
module

public import Geb.Mathlib.Data

/-!
# Geb.Mathlib — upstream-eligible content for mathlib4
...
-/
```

Create the test index files. `GebTests/Mathlib/Data/PFunctor/Slice.lean`:

```lean
/-
Copyright (c) 2026 The geb-mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The geb-mathlib contributors
-/
module

import GebTests.Mathlib.Data.PFunctor.Slice.Basic

/-!
# Slice tests — index
-/
```

`GebTests/Mathlib/Data/PFunctor.lean`:

```lean
/-
Copyright (c) 2026 The geb-mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The geb-mathlib contributors
-/
module

import GebTests.Mathlib.Data.PFunctor.Slice

/-!
# PFunctor tests — index
-/
```

`GebTests/Mathlib/Data.lean`:

```lean
/-
Copyright (c) 2026 The geb-mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The geb-mathlib contributors
-/
module

import GebTests.Mathlib.Data.PFunctor

/-!
# Data tests — index
-/
```

Modify `GebTests/Mathlib.lean`: insert between `module` and the
docstring:

```lean
module

import GebTests.Mathlib.Data

/-!
# GebTests.Mathlib — tests for upstream-eligible content
-/
```

- [ ] **Step 4: Run the test to verify it passes**

Run: `lake build GebTests.Mathlib.Data.PFunctor.Slice.Basic`
Expected: PASS (the `example`s elaborate).

- [ ] **Step 5: Verify umbrella wiring and import rules**

Run: `lake build Geb.Mathlib && bash scripts/lint-imports.sh`
Expected: build succeeds; lint-imports reports no violations.

- [ ] **Step 6: Commit**

```bash
jj commit -m "feat(slice-pfunctor): add SliceDomPFunctor and SlicePFunctor structures"
```

---

### Task 2: The compatibility predicate

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/Slice/Basic.lean`
- Modify: `GebTests/Mathlib/Data/PFunctor/Slice/Basic.lean`

**Interfaces:**

- Produces: `SliceDomPFunctor.Compatible (F) {X} (p : X → dom)
  (a : F.A) (v : F.B a → X) : Prop := p ∘ v = F.s ∘ Sigma.mk a`; and
  `SliceDomPFunctor.compatible_iff : F.Compatible p a v ↔
  ∀ b, p (v b) = F.s ⟨a, b⟩`.

- [ ] **Step 1: Write the failing test**

Append to the test file:

```lean
example (X : Type) (p : X → Bool) (v : Bool → X) :
    testSlice.Compatible p () v ↔ ∀ b, p (v b) = b :=
  testSlice.compatible_iff p () v
```

- [ ] **Step 2: Run to verify it fails**

Run: `lake build GebTests.Mathlib.Data.PFunctor.Slice.Basic`
Expected: FAIL — `unknown identifier 'testSlice.Compatible'`.

- [ ] **Step 3: Add the predicate and the equivalence lemma**

In `Basic.lean`, after the structures:

```lean
namespace SliceDomPFunctor

/-- A position assignment `v : F.B a → X` is compatible with a base map
`p : X → dom` when, as functions `F.B a → dom`, `p ∘ v` equals the
constraint leg restricted to shape `a`. Pointwise: `p (v b) = s ⟨a, b⟩`. -/
def Compatible {dom : Type u} (F : SliceDomPFunctor dom) {X : Type u}
    (p : X → dom) (a : F.A) (v : F.B a → X) : Prop :=
  p ∘ v = F.s ∘ Sigma.mk a

/-- `Compatible` stated pointwise. -/
theorem compatible_iff {dom : Type u} (F : SliceDomPFunctor dom)
    {X : Type u} (p : X → dom) (a : F.A) (v : F.B a → X) :
    F.Compatible p a v ↔ ∀ b, p (v b) = F.s ⟨a, b⟩ :=
  funext_iff

end SliceDomPFunctor
```

Note: if `funext_iff` does not unify, use `Function.funext_iff` or
`constructor <;> intro h <;> [exact fun b => congrFun h b; exact funext h]`
— confirm with `lean_goal`.

- [ ] **Step 4: Run the test to verify it passes**

Run: `lake build GebTests.Mathlib.Data.PFunctor.Slice.Basic`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
jj commit -m "feat(slice-pfunctor): add Compatible predicate and pointwise lemma"
```

---

### Task 3: Curried constructor and accessor

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/Slice/Basic.lean`
- Modify: `GebTests/Mathlib/Data/PFunctor/Slice/Basic.lean`

**Interfaces:**

- Produces: `SliceDomPFunctor.ofCurried (P : PFunctor.{u, u})
  (dom : Type u) (sc : (a : P.A) → P.B a → dom) : SliceDomPFunctor dom`
  with `s := fun x => sc x.1 x.2`; accessor `sCurried (F) (a) (b) :=
  F.s ⟨a, b⟩`; round-trip `rfl`.

- [ ] **Step 1: Write the failing test**

Append to the test file:

```lean
example (P : PFunctor.{0, 0}) (sc : (a : P.A) → P.B a → Bool) (a : P.A)
    (b : P.B a) : (SliceDomPFunctor.ofCurried P Bool sc).sCurried a b = sc a b :=
  rfl
```

- [ ] **Step 2: Run to verify it fails**

Run: `lake build GebTests.Mathlib.Data.PFunctor.Slice.Basic`
Expected: FAIL — `unknown identifier 'SliceDomPFunctor.ofCurried'`.

- [ ] **Step 3: Add the constructor and accessor**

Inside `namespace SliceDomPFunctor`:

```lean
/-- Build a `SliceDomPFunctor` from the dependently-curried constraint
leg. -/
@[expose] def ofCurried (P : PFunctor.{u, u}) (dom : Type u)
    (sc : (a : P.A) → P.B a → dom) : SliceDomPFunctor dom where
  toPFunctor := P
  s := fun x => sc x.1 x.2

/-- The constraint leg in dependently-curried form. -/
@[expose] def sCurried {dom : Type u} (F : SliceDomPFunctor dom) (a : F.A)
    (b : F.B a) : dom :=
  F.s ⟨a, b⟩
```

- [ ] **Step 4: Run the test to verify it passes**

Run: `lake build GebTests.Mathlib.Data.PFunctor.Slice.Basic`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
jj commit -m "feat(slice-pfunctor): add curried constructor and accessor for s"
```

---

### Task 4: Core object/morphism maps and functoriality (choice-free)

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/Slice/Basic.lean`
- Modify: `GebTests/Mathlib/Data/PFunctor/Slice/Basic.lean`

**Interfaces:**

- Consumes: `Compatible`; `PFunctor.Obj`/`map`/`map_eq`/`id_map`/
  `map_map`.
- Produces (all in `namespace SliceDomPFunctor`):
  - `@[expose] obj (F) {X} (p : X → dom) : Type u`
  - `@[expose] map (F) {X X'} {p p'} (f : X → X') (hf : p' ∘ f = p) :
    F.obj p → F.obj p'`
  - `@[expose] map_fst (…) : (F.map f hf x).1.1 = x.1.1`
  - `map_id (…) : F.map id _ = id`
  - `map_comp (…) : F.map (g ∘ f) _ = F.map g hg ∘ F.map f hf`

- [ ] **Step 1: Write the failing test**

Append to the test file:

```lean
-- The object map is the compatibility subtype of the interpretation.
example : testSlice.toSliceDomPFunctor.obj (id : Bool → Bool) =
    { x : (testSlice.toPFunctor).Obj Bool //
      testSlice.toSliceDomPFunctor.Compatible (id : Bool → Bool) x.1 x.2 } := rfl

-- The action fixes the shape.
example (X : Type) (p p' : X → Bool) (f : X → X) (hf : p' ∘ f = p)
    (z : testSlice.toSliceDomPFunctor.obj p) :
    (testSlice.toSliceDomPFunctor.map f hf z).1.1 = z.1.1 :=
  testSlice.toSliceDomPFunctor.map_fst f hf z
```

- [ ] **Step 2: Run to verify it fails**

Run: `lake build GebTests.Mathlib.Data.PFunctor.Slice.Basic`
Expected: FAIL — `unknown identifier '… .obj'`.

- [ ] **Step 3: Define `obj`, `map`, `map_fst`, `map_id`, `map_comp`**

Inside `namespace SliceDomPFunctor`:

```lean
/-- Value of the domain-restricted functor on `(X, p)`: the
compatibility subtype of the `PFunctor` interpretation. -/
@[expose] def obj {dom : Type u} (F : SliceDomPFunctor dom) {X : Type u}
    (p : X → dom) : Type u :=
  { x : F.toPFunctor.Obj X // F.Compatible p x.1 x.2 }

/-- Action on a slice morphism `f` (with `p' ∘ f = p`): `PFunctor.map f`
restricted to the compatibility subtype. -/
@[expose] def map {dom : Type u} (F : SliceDomPFunctor dom) {X X' : Type u}
    {p : X → dom} {p' : X' → dom} (f : X → X') (hf : p' ∘ f = p) :
    F.obj p → F.obj p' :=
  fun x => ⟨F.toPFunctor.map f x.1, by
    obtain ⟨⟨a, v⟩, hx⟩ := x
    change p' ∘ (f ∘ v) = F.s ∘ Sigma.mk a
    rw [← Function.comp_assoc, hf]
    exact hx⟩

/-- `map` fixes the shape component. -/
theorem map_fst {dom : Type u} (F : SliceDomPFunctor dom) {X X' : Type u}
    {p : X → dom} {p' : X' → dom} (f : X → X') (hf : p' ∘ f = p)
    (x : F.obj p) : (F.map f hf x).1.1 = x.1.1 := by
  obtain ⟨⟨a, v⟩, hx⟩ := x
  rfl

/-- Functoriality: identity. -/
theorem map_id {dom : Type u} (F : SliceDomPFunctor dom) {X : Type u}
    (p : X → dom) : F.map id (by simp) = (id : F.obj p → F.obj p) := by
  funext x
  exact Subtype.ext (F.toPFunctor.id_map x.1)

/-- Functoriality: composition. -/
theorem map_comp {dom : Type u} (F : SliceDomPFunctor dom) {X Y Z : Type u}
    {p : X → dom} {q : Y → dom} {r : Z → dom} (f : X → Y) (g : Y → Z)
    (hf : q ∘ f = p) (hg : r ∘ g = q) :
    F.map (g ∘ f) (by rw [← hf, ← hg, Function.comp_assoc]) =
      F.map g hg ∘ F.map f hf := by
  funext x
  exact Subtype.ext (F.toPFunctor.map_map f g x.1).symm
```

Note (verified strategy): the `map` witness destructures `x` to
`⟨⟨a, v⟩, hx⟩` first (a bare `rw [PFunctor.map_eq]` on `x.1` does not
fire). `map_id`/`map_comp` reduce to `F.toPFunctor.id_map` /
`F.toPFunctor.map_map` (qualified through `toPFunctor`) plus
`Subtype.ext`. If `map_map`'s direction or `id_map`'s implicit args do
not line up, repair with `lean_goal` keeping the signatures fixed.

- [ ] **Step 4: Run the test to verify it passes**

Run: `lake build GebTests.Mathlib.Data.PFunctor.Slice.Basic`
Expected: PASS.

- [ ] **Step 5: Certify the core is choice-free**

Run: `lake build Geb.Mathlib && lake lint`
Expected: build succeeds; `lake lint` passes for `Geb.Mathlib`
(including `…Slice.Basic`). Because `…Slice.Basic` is NOT in
`GebMeta.classicalAllowedModules`, a green lint is positive proof the
core depends only on `{propext, Quot.sound}` — no `Classical.choice`.

- [ ] **Step 6: Commit**

```bash
jj commit -m "feat(slice-pfunctor): add choice-free core object/morphism maps"
```

---

### Task 5: Categorical wrapper and allowlist entry

**Files:**

- Create: `Geb/Mathlib/Data/PFunctor/Slice/Functor.lean` (wrapper)
- Modify: `Geb/Mathlib/Data/PFunctor/Slice.lean` (index: import Functor)
- Modify: `GebMeta.lean` (add the wrapper module to the allowlist)
- Create: `GebTests/Mathlib/Data/PFunctor/Slice/Functor.lean` (tests)
- Modify: `GebTests/Mathlib/Data/PFunctor/Slice.lean` (index: import
  the wrapper test)

**Interfaces:**

- Consumes: the core `obj`/`map`/`map_fst`/`map_id`/`map_comp`;
  `CategoryTheory.Over`, `Over.w`, `Over.forget`, `Over.id_left`/
  `Over.comp_left`, `ConcreteCategory.hom`/`comp_apply`,
  `CategoryTheory.hom_id`/`hom_comp`/`id_apply`, `↾`/`TypeCat.hom_ofHom`,
  `Functor.toOver`/`Functor.toOver_comp_forget`.
- Produces: `SliceDomPFunctor.domFunctor : Over dom ⥤ Type u`;
  `SlicePFunctor.functor : Over dom ⥤ Over cod`;
  `SlicePFunctor.functor_comp_forget`.

- [ ] **Step 1: Write the failing test**

Create `GebTests/Mathlib/Data/PFunctor/Slice/Functor.lean`:

```lean
/-
Copyright (c) 2026 The geb-mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The geb-mathlib contributors
-/
module -- shake: keep-all

import Geb.Mathlib.Data.PFunctor.Slice.Functor

set_option linter.privateModule false

/-!
# Tests for the slice polynomial functor wrapper
-/

open CategoryTheory SliceDomPFunctor SlicePFunctor

/-- A concrete slice polynomial functor for the wrapper tests (local,
to avoid a cross-test-file dependency). -/
def wrapperTestSlice : SlicePFunctor Bool Unit where
  A := Unit
  B := fun _ => Bool
  s := fun x => x.2
  t := fun _ => ()

-- The slice-valued functor forgets back to `domFunctor`.
example : wrapperTestSlice.functor ⋙ Over.forget Unit =
    wrapperTestSlice.toSliceDomPFunctor.domFunctor :=
  wrapperTestSlice.functor_comp_forget
```

Add `import GebTests.Mathlib.Data.PFunctor.Slice.Functor` to
`GebTests/Mathlib/Data/PFunctor/Slice.lean` (after the `Slice.Basic`
import). The `module -- shake: keep-all` header suppresses a
`lake shake` false positive on the reused-across-files import chain.

- [ ] **Step 2: Run to verify it fails**

Run: `lake build GebTests.Mathlib.Data.PFunctor.Slice.Functor`
Expected: FAIL — module `…Slice.Functor` not found.

- [ ] **Step 3: Create the wrapper module**

Create `Geb/Mathlib/Data/PFunctor/Slice/Functor.lean`:

```lean
/-
Copyright (c) 2026 The geb-mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The geb-mathlib contributors
-/
module

public import Geb.Mathlib.Data.PFunctor.Slice.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Slice polynomial functors: categorical wrapper

Packages the constructive core (`…Slice.Basic`) as a
`CategoryTheory.Functor` between `Over` categories. Because mathlib's
`Over` is `Classical.choice`-dependent at the type level, this module
is listed in `GebMeta.classicalAllowedModules`; the core stays
choice-free.

## Main definitions

* `SliceDomPFunctor.domFunctor` — the functor `Over dom ⥤ Type`.
* `SlicePFunctor.functor` — the functor `Over dom ⥤ Over cod`.

## Implementation notes

`domFunctor` reuses the core `obj`/`map`; `Over` structure maps are
read through `ConcreteCategory.hom`, the slice-morphism hypothesis is
derived from `Over.w`, results promoted with `↾`, and the `TypeCat.Hom`
laws discharged by `ext` plus the core `map_id`/`map_comp`. `functor`
is the `Functor.toOver` lift along the tag `t`.

## References

* N. Gambino and M. Hyland, *Wellfounded trees and dependent
  polynomial functors*, TYPES 2003.

## Tags

polynomial functor, slice category, Over, container, PFunctor
-/

public section

universe u

open CategoryTheory

namespace SliceDomPFunctor

/-- The functor `Over dom ⥤ Type` restricting the `PFunctor`
interpretation to `s`-compatible assignments; the core maps packaged
over `Over dom`. -/
@[expose] def domFunctor {dom : Type u} (F : SliceDomPFunctor dom) :
    CategoryTheory.Functor (Over dom) (Type u) where
  obj Y := F.obj (ConcreteCategory.hom Y.hom)
  map {Y Z} h := ↾(F.map (ConcreteCategory.hom h.left) (by
    funext z
    rw [Function.comp_apply, ← ConcreteCategory.comp_apply, Over.w h]))
  map_id Y := by
    ext z
    exact congrFun (F.map_id _) z
  map_comp f g := by
    ext z
    rfl

end SliceDomPFunctor

namespace SlicePFunctor

/-- The slice polynomial functor `Over dom ⥤ Over cod`: the
`Functor.toOver` lift of `domFunctor` along the tag leg `t`. -/
def functor {dom cod : Type u} (F : SlicePFunctor dom cod) :
    CategoryTheory.Functor (Over dom) (Over cod) :=
  Functor.toOver F.toSliceDomPFunctor.domFunctor cod
    (fun _ => ↾(fun z => F.t z.1.1))
    (by
      intro Y Z g
      ext z
      exact congrArg F.t (F.toSliceDomPFunctor.map_fst
        (ConcreteCategory.hom g.left)
        (by funext w; rw [Function.comp_apply, ← ConcreteCategory.comp_apply,
          Over.w g]) z))

/-- The wrapper forgets back to `domFunctor`. -/
theorem functor_comp_forget {dom cod : Type u} (F : SlicePFunctor dom cod) :
    F.functor ⋙ Over.forget cod = F.toSliceDomPFunctor.domFunctor := by
  rw [functor]
  apply Functor.toOver_comp_forget
  intro Y Z g
  ext z
  exact congrArg F.t (F.toSliceDomPFunctor.map_fst
    (ConcreteCategory.hom g.left)
    (by funext w; rw [Function.comp_apply, ← ConcreteCategory.comp_apply,
      Over.w g]) z)

end SlicePFunctor
```

Modify `Geb/Mathlib/Data/PFunctor/Slice.lean` to also export the
wrapper:

```lean
public import Geb.Mathlib.Data.PFunctor.Slice.Basic
public import Geb.Mathlib.Data.PFunctor.Slice.Functor
```

- [ ] **Step 4: Verify the wrapper is rejected before allowlisting**

Run: `lake build Geb.Mathlib && lake lint`
Expected: FAIL — `lake lint` reports the wrapper's `domFunctor`/
`functor`/`functor_comp_forget` depend on `[Classical.choice]` (the
module is not yet allowlisted). This confirms the core/wrapper boundary
is real: the `Over`-dependence forces `Classical.choice`.

- [ ] **Step 5: Add the wrapper module to the allowlist**

In `GebMeta.lean`, extend `classicalAllowedModules`:

```lean
def classicalAllowedModules : NameSet :=
  (({} : NameSet).insert `GebTests.Internal.AxiomLinterClassicalFixture).insert
    `Geb.Mathlib.Data.PFunctor.Slice.Functor
```

- [ ] **Step 6: Verify the wrapper is now accepted**

Run: `lake build && lake lint`
Expected: PASS — `lake lint` accepts the wrapper's `Classical.choice`
(allowlisted) and `…Slice.Basic` still passes under the strict set.

- [ ] **Step 7: Run the wrapper test**

Run: `lake build GebTests.Mathlib.Data.PFunctor.Slice.Functor`
Expected: PASS.

- [ ] **Step 8: Commit**

```bash
jj commit -m "feat(slice-pfunctor): add Over-categorical wrapper and allowlist it"
```

Note (verified by the execution review): once `domFunctor` is
`@[expose]`d, `map_id` closes by `ext z; exact congrFun (F.map_id _) z`
and `map_comp` by `ext z; rfl` (the simpler forms above supersede a
`simp only`-with-bridge-lemmas approach). The `functor` triangle is NOT
`rfl` — it goes through the core `map_fst` lemma and `congrArg F.t`,
supplying the slice-morphism hypothesis for `g` as
`by funext w; rw [Function.comp_apply, ← ConcreteCategory.comp_apply,
Over.w g]`; the same proof recurs in `functor_comp_forget`. If a tactic
fails on the executor's machine, repair with `lean_goal`/`lean4:prove`,
keeping the signatures fixed; use `change` not `show`.

---

### Task 6: Concept documentation and full verification

**Files:**

- Modify: `docs/index.md`

**Interfaces:**

- Consumes: all prior tasks. Produces a documented concept entry and a
  fully green verification run.

- [ ] **Step 1: Add the concept to `docs/index.md`**

Append after "Directory structure":

```markdown
## Implemented content

- `Geb/Mathlib/Data/PFunctor/Slice/` — slice polynomial functors on
  `Type`. Given a `PFunctor` with a constraint leg `s : Idx → dom` and
  a tag leg `t : A → cod`, a restriction of the `PFunctor`
  interpretation defines a functor `Type/dom → Type/cod`.
  `Slice/Basic.lean` is the constructive core (`SliceDomPFunctor`,
  `SlicePFunctor`, `Compatible`, `obj`/`map` with functoriality),
  `Classical.choice`-free. `Slice/Functor.lean` packages it as
  `CategoryTheory.Functor (Over dom) (Over cod)` (`domFunctor`,
  `functor`) via `Functor.toOver`; that module is on
  `GebMeta.classicalAllowedModules` because mathlib's `Over` is
  `Classical.choice`-dependent. A natural isomorphism to
  `Σ_t ∘ Π_f ∘ Δ_s` is a planned follow-on increment.
```

- [ ] **Step 2: Refresh the docs TOC and lint Markdown**

`docs/index.md` gains a second `##` heading, so it needs a
marker-delimited TOC after the H1. Plain `doctoc` would insert a
`**Table of Contents**` title block *before* the H1 and fail
markdownlint MD041; instead insert the empty markers right after the
title line:

```text
# geb-mathlib documentation

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
<!-- END doctoc generated TOC please keep comment here to allow auto update -->
```

then run `doctoc --notitle --update-only docs/index.md && markdownlint-cli2 docs/index.md`.
Expected: TOC filled between the markers (H1 first); no markdownlint
errors on `docs/index.md`.

- [ ] **Step 3: Attempt universe polymorphism (refinement)**

In `Basic.lean` (and the dependent `Functor.lean`), attempt widening
`PFunctor.{u, u}` to `PFunctor.{uA, uB}` with `dom cod : Type u`,
adjusting `Type u` annotations. Run `lake build Geb.Mathlib`. If it
compiles, keep it and remove now-unused `universe`/`variable`
declarations; record the outcome in the module `## Implementation
notes`. If the `Over` single-universe constraint forces a failure,
revert to `{u, u}` (the verified baseline) and note it.

- [ ] **Step 4: Full verification gate**

Run each and confirm before proceeding:

- `lake build` — succeeds.
- `lake build GebTests` — succeeds.
- `lake test` — `GebTests` builds; all `example` checks pass.
- `lake lint` — passes; `…Slice.Basic` under the strict set (proving
  the core is choice-free), `…Slice.Functor` under the allowlist.
- `lake lint -- GebTests` — passes.
- `lake shake --add-public --keep-implied --keep-prefix Geb GebTests`
  — exit 0.
- `bash scripts/lint-imports.sh` — no violations.
- `markdownlint-cli2 '**/*.md'` — no new errors (pre-existing
  `.remember/`/`.superpowers/` noise excepted).

- [ ] **Step 5: Pre-commit Lean review**

Invoke `lean4:review` on `Basic.lean` and `Functor.lean`; address
findings, keeping interfaces fixed.

- [ ] **Step 6: Commit**

```bash
jj commit -m "doc(slice-pfunctor): record slice polynomial functors in docs/index.md"
```

- [ ] **Step 7: Advance the bookmark**

```bash
jj bookmark set feat/slice-pfunctor -r @-
```

---

## Post-implementation (handled outside this plan)

- Final-review skills before any push: `lean4:review`,
  `pr-review-toolkit:review-pr`, then line-by-line user review. No push
  without that review.
- Per `CONTRIBUTING.md` § Concern shape, the spec and plan are removed
  in the branch's final commits (create → implement → remove) before
  merge to `main`. The `GebMeta.classicalAllowedModules` entry and the
  two content files are permanent.
