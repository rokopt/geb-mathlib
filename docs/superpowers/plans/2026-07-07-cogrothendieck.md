# Contravariant Grothendieck Construction Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan
> task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Implement `GrothendieckOp` and `CoGrothendieck` (the
contravariant Grothendieck construction for 1-functors
`Cᵒᵖ ⥤ Cat`) as transparent wrappers over mathlib's covariant
`CategoryTheory.Grothendieck`, per the approved spec at
[docs/superpowers/specs/2026-07-07-cogrothendieck-design.md](../specs/2026-07-07-cogrothendieck-design.md).

**Architecture:** Transparent `def` type synonyms over
`Grothendieck (F ⋙ Cat.opFunctor)` and its opposite category;
every functor is a composition of existing mathlib functors (no
hand-written object maps, morphism maps, or law proofs); a
wrapper API (`mk`/`base`/`fiber`, `homMk`/`homBase`/`homFiber`)
presents `C`-morphisms with `rfl` round-trips.

**Tech Stack:** Lean 4 (toolchain from `lean-toolchain`), mathlib
(pinned via lakefile), `lake` build, `jj` for all VCS mutations.

## Global Constraints

Every task implicitly includes these; they come from the spec and
the repository rules.

- Every `def` carries an explicit return type; universe levels
  are written explicitly. Universe header: `universe u v u₂ v₂`
  with `{C : Type u} [Category.{v} C]`, functors into
  `Cat.{v₂, u₂}`.
- The source module opens with the `module` keyword and
  `@[expose] public section` after imports and docstring. The
  test module uses the house test-file shape instead (`module`,
  plain `import`, `set_option linter.privateModule false`, no
  `@[expose] public section`); this supersedes the spec's
  § Module layout sentence for the test module — the spec's
  exposure-correctness argument needs only the *source* module
  exposed, which is preserved.
- No `noncomputable`. The whole module is `Classical.choice`-
  dependent through mathlib (verified fact, recorded in the
  spec); the allowlist entries in Task 1 make `lake lint` accept
  exactly `{propext, Classical.choice, Quot.sound}` and nothing
  more.
- mathlib style: 2-space indent, 100-column lines, declaration
  docstrings on every public `def`/`theorem`, `snake_case`
  theorem names, `lowerCamelCase` defs.
- Commit messages: mathlib convention, `type(scope): subject`
  with lowercase imperative subject, no trailing period. Use
  scope `cat`. All commits via `jj commit` (never raw mutating
  `git`).
- Tests are named `def`s/`theorem`s (never `example` — `lake
  shake` cannot see example-only imports).
- Statement types in this plan are the contract (they passed
  adversarial review against mathlib sources). Proof *scripts*
  are candidates: if a candidate tactic proof fails, iterate with
  compiler feedback (lean-lsp `lean_goal`,
  `lean_diagnostic_messages`) without changing the statement; a
  statement change requires returning to the plan for
  justification.
- `eqToHom` side-condition proofs written inside statements (the
  `(by simp)` arguments) share the candidate latitude: by proof
  irrelevance, any proof of the same equation yields the same
  statement.
- `Type`-category morphisms are bundled (`TypeCat.Hom`): in test
  code, promote functions with `↾f` and extract with
  `ConcreteCategory.hom`, following the idiom in
  `GebTests/Mathlib/Data/PFunctor/Slice/Functor.lean`. Bare
  functions are not morphisms of `Type`.
- Checkbox (`- [x]`) updates to this plan file ride along in each
  task's argument-less `jj commit`; this is the expected
  spec/plan-on-branch workflow.
- Where a step says "Run: `lake build`", the expected output ends
  with `Build completed successfully.` Where it says
  `lake test`, expect exit code 0. First errors first when a
  build fails.

---

### Task 1: Module skeletons, index wiring, axiom allowlist

**Files:**

- Create: `Geb/Mathlib/CategoryTheory/Grothendieck.lean`
- Create: `Geb/Mathlib/CategoryTheory.lean`
- Modify: `Geb/Mathlib.lean`
- Create: `GebTests/Mathlib/CategoryTheory/Grothendieck.lean`
- Create: `GebTests/Mathlib/CategoryTheory.lean`
- Modify: `GebTests/Mathlib.lean`
- Modify: `GebMeta.lean` (`classicalAllowedModules`)

**Interfaces:**

- Consumes: nothing (first task).
- Produces: the module `Geb.Mathlib.CategoryTheory.Grothendieck`
  (namespace `CategoryTheory`, `open Functor`, universes
  `u v u₂ v₂`, variable `{C : Type u} [Category.{v} C]`) and its
  test mirror, both importable and lint-clean; all later tasks
  add declarations inside these two files.

- [x] **Step 1: Create the source module skeleton**

Create `Geb/Mathlib/CategoryTheory/Grothendieck.lean`:

```lean
/-
Copyright (c) 2026 The geb-mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The geb-mathlib contributors
-/
module

public import Mathlib.CategoryTheory.Grothendieck
public import Mathlib.CategoryTheory.Category.Cat.Op
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Whiskering

/-!
# Covariant and contravariant Grothendieck constructions

For a functor `F : C ⥤ Cat`, mathlib's `CategoryTheory.Grothendieck F`
is the covariant Grothendieck construction. This module adds:

* a `Cat`-valued packaging of the covariant construction
  (`Grothendieck.functorToCat`);
* `GrothendieckOp F`, the covariant construction applied to the
  oppositization `F ⋙ Cat.opFunctor`;
* `CoGrothendieck G`, the contravariant Grothendieck construction of
  `G : Cᵒᵖ ⥤ Cat`, defined as `(GrothendieckOp G)ᵒᵖ`, together with an
  interface whose constructors and destructors use morphisms of `C`.

## Main definitions

* `CategoryTheory.Grothendieck.functorToCat`
* `CategoryTheory.GrothendieckOp`
* `CategoryTheory.CoGrothendieck`

## Main statements

* `GrothendieckOp.hom_ext` and `CoGrothendieck.hom_ext`
* `GrothendieckOp.map_id_eq`/`map_comp_eq` and the `CoGrothendieck`
  counterparts

## Implementation notes

`GrothendieckOp` and `CoGrothendieck` are semireducible `def` type
synonyms, not `abbrev`s and not new structures: instance synthesis and
object-level dot notation stop at the new names, while all round-trip
lemmas hold by `rfl`. Morphism-level dot notation resolves through
`Quiver.Hom` to `Grothendieck.Hom`'s own projections (whose op-side
types make direction misuse a type error); the wrapper accessors
`homBase`/`homFiber` are therefore free functions, used qualified or
via `open`.

Universe levels match the covariant construction exactly: for
`F : C ⥤ Cat.{v₂, u₂}` with `C : Type u` and `Category.{v} C`, both
`GrothendieckOp F` and `CoGrothendieck G` live in `Type (max u u₂)`
with `Category.{max v v₂}` instances, since `ᵒᵖ` and `Cat.opFunctor`
preserve universes. The packaged functors (`functor`, `functorToCat`)
restrict to `E : Cat.{v, u}` with fibers in the same `Cat.{v, u}`,
inherited from mathlib's `Grothendieck.functor`.

## References

The contravariant Grothendieck construction is standard; see
[Vistoli2008] and [JohnsonYau2021].

## Tags

Grothendieck construction, contravariant, opposite category, fibered
category
-/

@[expose] public section

universe u v u₂ v₂

namespace CategoryTheory

open Functor

variable {C : Type u} [Category.{v} C]

end CategoryTheory
```

- [x] **Step 2: Create the Geb-side index and wire it**

Create `Geb/Mathlib/CategoryTheory.lean`:

```lean
/-
Copyright (c) 2026 The geb-mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The geb-mathlib contributors
-/
module

public import Geb.Mathlib.CategoryTheory.Grothendieck

/-!
# CategoryTheory — index
-/
```

(The docstring title deliberately avoids the module's own
`Geb.Mathlib.` prefix: `scripts/lint-imports.sh` Rule 2 rejects
the subtree prefix anywhere outside import lines. The existing
index files use the same prefix-free style, e.g.
`# Data — index`.)

In `Geb/Mathlib.lean`, add after the existing
`public import Geb.Mathlib.Data`:

```lean
public import Geb.Mathlib.CategoryTheory
```

- [x] **Step 3: Create the test module skeleton and its index**

Create `GebTests/Mathlib/CategoryTheory/Grothendieck.lean`:

```lean
/-
Copyright (c) 2026 The geb-mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The geb-mathlib contributors
-/
module

import Geb.Mathlib.CategoryTheory.Grothendieck

set_option linter.privateModule false

/-!
# Tests for the covariant and contravariant Grothendieck constructions
-/

open CategoryTheory
```

This matches the house test-file shape
(`GebTests/Mathlib/Data/PFunctor/Slice/Functor.lean`): plain
`import`, the `privateModule` linter option, no namespace (test
declarations are top-level with distinctive names), no
`@[expose] public section`. The `↾` notation for promoting
functions to `Type`-category morphisms is available with this
`open`, as in that file.

Create `GebTests/Mathlib/CategoryTheory.lean`:

```lean
/-
Copyright (c) 2026 The geb-mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The geb-mathlib contributors
-/
module

import GebTests.Mathlib.CategoryTheory.Grothendieck

/-!
# CategoryTheory tests — index
-/
```

(Plain `import` and prefix-free title, matching
`GebTests/Mathlib/Data.lean`; the `GebTests.Mathlib.` prefix
outside import lines is rejected by `scripts/lint-imports.sh`.)

In `GebTests/Mathlib.lean`, add after the existing line
`import GebTests.Mathlib.Data` (note: plain `import`, unlike the
`Geb/` side):

```lean
import GebTests.Mathlib.CategoryTheory
```

- [x] **Step 4: Append both modules to the axiom allowlist**

In `GebMeta.lean`, the current list ends with

```lean
   `GebTests.Mathlib.Data.PFunctor.Presheaf.Functor].foldl (·.insert ·)
```

(no trailing comma; the closing bracket sits mid-line). Replace
that line so the list reads:

```lean
   `GebTests.Mathlib.Data.PFunctor.Presheaf.Functor,
   `Geb.Mathlib.CategoryTheory.Grothendieck,
   `GebTests.Mathlib.CategoryTheory.Grothendieck].foldl (·.insert ·)
```

- [x] **Step 5: Build and lint**

Run: `lake build && lake lint`
Expected: `Build completed successfully.` and lint exit 0 (the
new modules are empty of declarations, so this validates wiring
and docstring shape only).

- [x] **Step 6: Commit**

```bash
jj commit -m "feat(cat): add Grothendieck construction module skeletons"
```

---

### Task 2: Covariant `Grothendieck.functorToCat`

**Files:**

- Modify: `Geb/Mathlib/CategoryTheory/Grothendieck.lean`
- Modify: `GebTests/Mathlib/CategoryTheory/Grothendieck.lean`

**Interfaces:**

- Consumes: Task 1 skeletons.
- Produces: `CategoryTheory.Grothendieck.functorToCat {E : Cat.{v, u}} :
  (↑E ⥤ Cat.{v, u}) ⥤ Cat.{v, u}` and simp lemmas
  `functorToCat_obj`, `functorToCat_map`. Task 9 mirrors its
  shape.

- [x] **Step 1: Add the covariant section to the source module**

Inside `namespace CategoryTheory` (before `end CategoryTheory`),
add:

```lean
/-! ## Covariant construction: `Cat`-valued packaging -/

namespace Grothendieck

/-- The covariant Grothendieck construction as a functor to `Cat`:
`Grothendieck.functor` followed by forgetting the projection to the
base. -/
def functorToCat {E : Cat.{v, u}} : (↑E ⥤ Cat.{v, u}) ⥤ Cat.{v, u} :=
  Grothendieck.functor ⋙ Over.forget E

@[simp]
theorem functorToCat_obj {E : Cat.{v, u}} (F : ↑E ⥤ Cat.{v, u}) :
    functorToCat.obj F = Cat.of (Grothendieck F) :=
  rfl

@[simp]
theorem functorToCat_map {E : Cat.{v, u}} {F F' : ↑E ⥤ Cat.{v, u}}
    (α : F ⟶ F') : functorToCat.map α = (Grothendieck.map α).toCatHom :=
  rfl

end Grothendieck
```

Note the universe binders: mathlib's `Grothendieck.functor` uses
`{E : Cat.{v, u}}` with matching fiber universes; `v u` here are
this module's `u v` declared in Task 1 (order as in mathlib's
`Cat.{v, u}` notation: hom level first).

- [x] **Step 2: Build**

Run: `lake build`
Expected: `Build completed successfully.` If `functorToCat_map`'s
`rfl` fails, inspect with `lean_goal`; the fallback statement is
unchanged with proof `rfl` after `dsimp only [functorToCat]` —
do not weaken the statement.

- [x] **Step 3: Add the test**

In the test module, add:

```lean
/-! ## Covariant `functorToCat` -/

/-- A concrete covariant `Cat`-valued functor: constant at `Type`. -/
def constTypeCovariant : Type ⥤ Cat.{0, 1} :=
  (Functor.const (Type : Type 1)).obj (Cat.of Type)

/-- `functorToCat` applied to a constant functor yields the
Grothendieck construction on the nose. -/
theorem functorToCat_obj_constTypeCovariant :
    (Grothendieck.functorToCat (E := Cat.of (Type : Type 1))).obj
        constTypeCovariant =
      Cat.of (Grothendieck constTypeCovariant) :=
  rfl
```

(Note the parenthesization: the universe pin `(E := …)` must
attach to `functorToCat` itself, not to `.obj` — named arguments
do not travel through dot-notation projections.)

- [x] **Step 4: Build and test**

Run: `lake build && lake test`
Expected: build success, tests exit 0.

- [x] **Step 5: Verify axioms**

Use lean-lsp `lean_verify` on
`CategoryTheory.Grothendieck.functorToCat`.
Expected axiom set: subset of
`{propext, Classical.choice, Quot.sound}`.

- [x] **Step 6: Commit**

```bash
jj commit -m "feat(cat): add covariant Grothendieck functorToCat"
```

---

### Task 3: `GrothendieckOp` — type, instance, object interface

**Files:**

- Modify: `Geb/Mathlib/CategoryTheory/Grothendieck.lean`
- Modify: `GebTests/Mathlib/CategoryTheory/Grothendieck.lean`

**Interfaces:**

- Consumes: Task 1 skeletons.
- Produces: `GrothendieckOp (F : C ⥤ Cat.{v₂, u₂}) :
  Type (max u u₂)`, its `Category.{max v v₂}` instance, and
  `GrothendieckOp.mk (base : C) (fiber : F.obj base)`,
  `GrothendieckOp.base : GrothendieckOp F → C`,
  `GrothendieckOp.fiber (X : GrothendieckOp F) : F.obj X.base`.
  Tasks 4–9 build on these exact names.

- [x] **Step 1: Add the type synonym, instance, and object API**

After the covariant section, add:

```lean
/-! ## The Grothendieck construction of an oppositized functor -/

/-- The covariant Grothendieck construction applied to the
oppositization of `F`: objects are pairs of a base object `c : C` and a
fiber object of `F.obj c`, and morphisms reverse the fiber direction
relative to `Grothendieck F`. -/
def GrothendieckOp (F : C ⥤ Cat.{v₂, u₂}) : Type (max u u₂) :=
  Grothendieck (F ⋙ Cat.opFunctor)

namespace GrothendieckOp

/-- The category structure on `GrothendieckOp F`, inherited from the
underlying covariant Grothendieck construction. -/
instance category (F : C ⥤ Cat.{v₂, u₂}) :
    Category.{max v v₂} (GrothendieckOp F) :=
  inferInstanceAs (Category (Grothendieck (F ⋙ Cat.opFunctor)))

variable {F : C ⥤ Cat.{v₂, u₂}}

/-- Construct an object of `GrothendieckOp F` from a base object and a
fiber object. -/
def mk (base : C) (fiber : F.obj base) : GrothendieckOp F :=
  ⟨base, Opposite.op fiber⟩

/-- The base object of an object of `GrothendieckOp F`. -/
def base (X : GrothendieckOp F) : C :=
  Grothendieck.base X

/-- The fiber object of an object of `GrothendieckOp F`. -/
def fiber (X : GrothendieckOp F) : F.obj X.base :=
  Opposite.unop (Grothendieck.fiber X)

@[simp]
theorem base_mk (b : C) (f : F.obj b) : (mk b f).base = b :=
  rfl

@[simp]
theorem fiber_mk (b : C) (f : F.obj b) : (mk b f).fiber = f :=
  rfl

@[simp]
theorem mk_base_fiber (X : GrothendieckOp F) : mk X.base X.fiber = X :=
  rfl

end GrothendieckOp
```

- [x] **Step 2: Build**

Run: `lake build`
Expected: `Build completed successfully.` The `rfl`s rely on
structure eta for `Grothendieck` and `Opposite`; they are
expected to close as stated.

- [x] **Step 3: Add tests**

In the test module, add:

```lean
/-! ## `GrothendieckOp` objects -/

/-- A constant `Cat`-valued functor on `Type` for exercising
`GrothendieckOp`. -/
def constTypeOp : Type ⥤ Cat.{0, 1} :=
  (Functor.const (Type : Type 1)).obj (Cat.of Type)

/-- A sample object: base `Bool`, fiber `Nat`. -/
def gOpObj : GrothendieckOp constTypeOp :=
  GrothendieckOp.mk Bool Nat

theorem gOpObj_base : gOpObj.base = Bool := rfl

theorem gOpObj_fiber : gOpObj.fiber = Nat := rfl

theorem gOpObj_eta :
    GrothendieckOp.mk gOpObj.base gOpObj.fiber = gOpObj := rfl
```

(`constTypeCovariant` is deliberately not reused: the covariant
and contravariant test sections stay independently readable;
`constTypeOp` is the running example for the rest of the file.)

- [x] **Step 4: Build, test, verify**

Run: `lake build && lake test`
Expected: success. Then `lean_verify` on
`CategoryTheory.GrothendieckOp` and
`CategoryTheory.GrothendieckOp.mk`; expected axioms: subset of
`{propext, Classical.choice, Quot.sound}`.

- [x] **Step 5: Commit**

```bash
jj commit -m "feat(cat): add GrothendieckOp with object interface"
```

---

### Task 4: `GrothendieckOp` — hom interface, ext, id/comp lemmas

**Files:**

- Modify: `Geb/Mathlib/CategoryTheory/Grothendieck.lean`
- Modify: `GebTests/Mathlib/CategoryTheory/Grothendieck.lean`

**Interfaces:**

- Consumes: Task 3's `GrothendieckOp`, `mk`, `base`, `fiber`.
- Produces: `GrothendieckOp.homMk`, `homBase`, `homFiber` with
  the exact signatures below; `hom_ext`; simp lemmas
  `homBase_homMk`, `homFiber_homMk`, `homMk_base_fiber`,
  `homBase_id`, `homFiber_id`, `homBase_comp`, `homFiber_comp`.
  Task 6 wraps these; Task 7's `forget_map` mentions `homBase`.

- [ ] **Step 1: Add the hom API inside `namespace GrothendieckOp`**

Insert before `end GrothendieckOp`:

```lean
/-- Construct a morphism of `GrothendieckOp F` from a base morphism and
a fiber morphism. The fiber morphism runs from the target fiber to the
pushforward of the source fiber — the reversal relative to
`Grothendieck.Hom`. -/
def homMk {X Y : GrothendieckOp F} (base : X.base ⟶ Y.base)
    (fiber : Y.fiber ⟶ (F.map base).toFunctor.obj X.fiber) : X ⟶ Y :=
  ⟨base, fiber.op⟩

/-- The base morphism of a morphism of `GrothendieckOp F`. -/
def homBase {X Y : GrothendieckOp F} (f : X ⟶ Y) : X.base ⟶ Y.base :=
  Grothendieck.Hom.base f

/-- The fiber morphism of a morphism of `GrothendieckOp F`. -/
def homFiber {X Y : GrothendieckOp F} (f : X ⟶ Y) :
    Y.fiber ⟶ (F.map (homBase f)).toFunctor.obj X.fiber :=
  Quiver.Hom.unop (Grothendieck.Hom.fiber f)

@[simp]
theorem homBase_homMk {X Y : GrothendieckOp F} (b : X.base ⟶ Y.base)
    (φ : Y.fiber ⟶ (F.map b).toFunctor.obj X.fiber) :
    homBase (homMk b φ) = b :=
  rfl

@[simp]
theorem homFiber_homMk {X Y : GrothendieckOp F} (b : X.base ⟶ Y.base)
    (φ : Y.fiber ⟶ (F.map b).toFunctor.obj X.fiber) :
    homFiber (homMk b φ) = φ :=
  rfl

@[simp]
theorem homMk_base_fiber {X Y : GrothendieckOp F} (f : X ⟶ Y) :
    homMk (homBase f) (homFiber f) = f :=
  rfl

@[ext (iff := false)]
theorem hom_ext {X Y : GrothendieckOp F} (f g : X ⟶ Y)
    (hbase : homBase f = homBase g)
    (hfiber : homFiber f ≫ eqToHom (by rw [hbase]) = homFiber g) :
    f = g := by
  refine Grothendieck.ext f g hbase ?_
  apply Quiver.Hom.unop_inj
  simpa [homFiber, homBase, eqToHom_unop] using hfiber.symm

@[simp]
theorem homBase_id (X : GrothendieckOp F) : homBase (𝟙 X) = 𝟙 X.base :=
  rfl

@[simp]
theorem homFiber_id (X : GrothendieckOp F) :
    homFiber (𝟙 X) = eqToHom (by simp) := by
  simp [homFiber, homBase, Grothendieck.id_fiber, eqToHom_unop]

@[simp]
theorem homBase_comp {X Y Z : GrothendieckOp F} (f : X ⟶ Y) (g : Y ⟶ Z) :
    homBase (f ≫ g) = homBase f ≫ homBase g :=
  rfl

@[simp]
theorem homFiber_comp {X Y Z : GrothendieckOp F} (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    homFiber (f ≫ g) =
      homFiber g ≫ (F.map (homBase g)).toFunctor.map (homFiber f) ≫
        eqToHom (by simp) := by
  simp [homFiber, homBase, Grothendieck.comp_fiber, eqToHom_unop]
```

The three tactic proofs are candidates (see Global Constraints):
the statements are contractual; the `eqToHom` bookkeeping lemmas
to reach for are `eqToHom_unop`, `eqToHom_op`, `unop_comp`, and
`Quiver.Hom.unop_inj`.

- [ ] **Step 2: Build**

Run: `lake build`
Expected: success. Iterate on the three tactic proofs with
`lean_goal` / `lean_multi_attempt` if needed.

- [ ] **Step 3: Add tests**

```lean
/-! ## `GrothendieckOp` morphisms -/

/-- A second object: base `Nat`, fiber `String`. -/
def gOpObj' : GrothendieckOp constTypeOp :=
  GrothendieckOp.mk Nat String

/-- A sample morphism `gOpObj ⟶ gOpObj'`. Its fiber component runs
`String ⟶ Nat` (target fiber to source fiber) because the fiber
direction is reversed. -/
def gOpHom : gOpObj ⟶ gOpObj' :=
  GrothendieckOp.homMk (↾fun b => (cond b 1 0 : Nat)) (↾String.length)

theorem gOpHom_base :
    GrothendieckOp.homBase gOpHom = ↾fun b => (cond b 1 0 : Nat) :=
  rfl

theorem gOpHom_fiber :
    GrothendieckOp.homFiber gOpHom = ↾String.length :=
  rfl

theorem gOpHom_eta :
    GrothendieckOp.homMk (GrothendieckOp.homBase gOpHom)
      (GrothendieckOp.homFiber gOpHom) = gOpHom :=
  rfl

theorem gOpComp_base :
    GrothendieckOp.homBase (𝟙 gOpObj ≫ gOpHom) =
      GrothendieckOp.homBase gOpHom := by
  simp
```

- [ ] **Step 4: Build, test, verify**

Run: `lake build && lake test`
Expected: success. `lean_verify` on
`CategoryTheory.GrothendieckOp.homMk` and
`CategoryTheory.GrothendieckOp.hom_ext`; expected axioms within
the permitted set.

- [ ] **Step 5: Commit**

```bash
jj commit -m "feat(cat): add GrothendieckOp hom interface"
```

---

### Task 5: `CoGrothendieck` — type, instance, object interface

**Files:**

- Modify: `Geb/Mathlib/CategoryTheory/Grothendieck.lean`
- Modify: `GebTests/Mathlib/CategoryTheory/Grothendieck.lean`

**Interfaces:**

- Consumes: Task 3's `GrothendieckOp` object API.
- Produces: `CoGrothendieck (G : Cᵒᵖ ⥤ Cat.{v₂, u₂}) :
  Type (max u u₂)` with `Category.{max v v₂}` instance;
  `CoGrothendieck.mk (base : C) (fiber : G.obj (Opposite.op base))`,
  `CoGrothendieck.base`, `CoGrothendieck.fiber` as below.

- [ ] **Step 1: Add the type synonym, instance, and object API**

After `end GrothendieckOp`, add:

```lean
/-! ## The contravariant Grothendieck construction -/

/-- The contravariant Grothendieck construction of `G : Cᵒᵖ ⥤ Cat`:
the opposite category of `GrothendieckOp G`. Objects are pairs of
`c : C` and an object of `G.obj (op c)`; a morphism `X ⟶ Y` consists of
`β : X.base ⟶ Y.base` in `C` and a fiber morphism
`X.fiber ⟶ (G.map β.op).toFunctor.obj Y.fiber`. -/
def CoGrothendieck (G : Cᵒᵖ ⥤ Cat.{v₂, u₂}) : Type (max u u₂) :=
  (GrothendieckOp G)ᵒᵖ

namespace CoGrothendieck

/-- The category structure on `CoGrothendieck G`, inherited from the
opposite of `GrothendieckOp G`. -/
instance category (G : Cᵒᵖ ⥤ Cat.{v₂, u₂}) :
    Category.{max v v₂} (CoGrothendieck G) :=
  inferInstanceAs (Category (GrothendieckOp G)ᵒᵖ)

variable {G : Cᵒᵖ ⥤ Cat.{v₂, u₂}}

/-- Construct an object of `CoGrothendieck G` from a base object and a
fiber object. -/
def mk (base : C) (fiber : G.obj (Opposite.op base)) :
    CoGrothendieck G :=
  Opposite.op (GrothendieckOp.mk (Opposite.op base) fiber)

/-- The base object of an object of `CoGrothendieck G`, as an object
of `C`. -/
def base (X : CoGrothendieck G) : C :=
  Opposite.unop (GrothendieckOp.base (Opposite.unop X))

/-- The fiber object of an object of `CoGrothendieck G`. -/
def fiber (X : CoGrothendieck G) : G.obj (Opposite.op X.base) :=
  GrothendieckOp.fiber (Opposite.unop X)

@[simp]
theorem base_mk (b : C) (f : G.obj (Opposite.op b)) : (mk b f).base = b :=
  rfl

@[simp]
theorem fiber_mk (b : C) (f : G.obj (Opposite.op b)) :
    (mk b f).fiber = f :=
  rfl

@[simp]
theorem mk_base_fiber (X : CoGrothendieck G) : mk X.base X.fiber = X :=
  rfl

end CoGrothendieck
```

- [ ] **Step 2: Build**

Run: `lake build`
Expected: success. `fiber`'s return type uses
`Opposite.op X.base = X.unop.base` holding by `Opposite`
structure eta; if the ascription fails to elaborate, check with
`lean_term_goal` — the statement stands.

- [ ] **Step 3: Add tests**

```lean
/-! ## `CoGrothendieck` objects -/

/-- The running contravariant example: constant at `Type` on
`(Type)ᵒᵖ`. -/
def constTypeContra : (Type : Type 1)ᵒᵖ ⥤ Cat.{0, 1} :=
  (Functor.const (Type : Type 1)ᵒᵖ).obj (Cat.of Type)

/-- A sample object: base `Bool`, fiber `Nat`. -/
def coObj : CoGrothendieck constTypeContra :=
  CoGrothendieck.mk Bool Nat

/-- A second object: base `Nat`, fiber `String`. -/
def coObj' : CoGrothendieck constTypeContra :=
  CoGrothendieck.mk Nat String

theorem coObj_base : coObj.base = Bool := rfl

theorem coObj_fiber : coObj.fiber = Nat := rfl

theorem coObj_eta :
    CoGrothendieck.mk coObj.base coObj.fiber = coObj := rfl
```

- [ ] **Step 4: Build, test, verify**

Run: `lake build && lake test`
Expected: success. `lean_verify` on
`CategoryTheory.CoGrothendieck` and
`CategoryTheory.CoGrothendieck.mk`; axioms within the permitted
set.

- [ ] **Step 5: Commit**

```bash
jj commit -m "feat(cat): add CoGrothendieck with object interface"
```

---

### Task 6: `CoGrothendieck` — hom interface, ext, id/comp lemmas

**Files:**

- Modify: `Geb/Mathlib/CategoryTheory/Grothendieck.lean`
- Modify: `GebTests/Mathlib/CategoryTheory/Grothendieck.lean`

**Interfaces:**

- Consumes: Task 4's `GrothendieckOp` hom API; Task 5's
  `CoGrothendieck` object API.
- Produces: `CoGrothendieck.homMk`, `homBase`, `homFiber`,
  `hom_ext`, and the id/comp simp lemmas named exactly as in
  Task 4 but in the `CoGrothendieck` namespace.

- [ ] **Step 1: Add the hom API inside `namespace CoGrothendieck`**

Insert before `end CoGrothendieck`:

```lean
/-- Construct a morphism of `CoGrothendieck G` from a base morphism in
`C` and a fiber morphism. -/
def homMk {X Y : CoGrothendieck G} (base : X.base ⟶ Y.base)
    (fiber : X.fiber ⟶ (G.map base.op).toFunctor.obj Y.fiber) :
    X ⟶ Y :=
  Quiver.Hom.op (GrothendieckOp.homMk base.op fiber)

/-- The base morphism of a morphism of `CoGrothendieck G`, as a
morphism of `C`. -/
def homBase {X Y : CoGrothendieck G} (f : X ⟶ Y) : X.base ⟶ Y.base :=
  Quiver.Hom.unop (GrothendieckOp.homBase (Quiver.Hom.unop f))

/-- The fiber morphism of a morphism of `CoGrothendieck G`. -/
def homFiber {X Y : CoGrothendieck G} (f : X ⟶ Y) :
    X.fiber ⟶ (G.map (homBase f).op).toFunctor.obj Y.fiber :=
  GrothendieckOp.homFiber (Quiver.Hom.unop f)

@[simp]
theorem homBase_homMk {X Y : CoGrothendieck G} (b : X.base ⟶ Y.base)
    (φ : X.fiber ⟶ (G.map b.op).toFunctor.obj Y.fiber) :
    homBase (homMk b φ) = b :=
  rfl

@[simp]
theorem homFiber_homMk {X Y : CoGrothendieck G} (b : X.base ⟶ Y.base)
    (φ : X.fiber ⟶ (G.map b.op).toFunctor.obj Y.fiber) :
    homFiber (homMk b φ) = φ :=
  rfl

@[simp]
theorem homMk_base_fiber {X Y : CoGrothendieck G} (f : X ⟶ Y) :
    homMk (homBase f) (homFiber f) = f :=
  rfl

@[ext (iff := false)]
theorem hom_ext {X Y : CoGrothendieck G} (f g : X ⟶ Y)
    (hbase : homBase f = homBase g)
    (hfiber : homFiber f ≫ eqToHom (by rw [hbase]) = homFiber g) :
    f = g := by
  apply Quiver.Hom.unop_inj
  refine GrothendieckOp.hom_ext _ _ (Quiver.Hom.unop_inj hbase) ?_
  simpa [homFiber] using hfiber

@[simp]
theorem homBase_id (X : CoGrothendieck G) : homBase (𝟙 X) = 𝟙 X.base :=
  rfl

@[simp]
theorem homFiber_id (X : CoGrothendieck G) :
    homFiber (𝟙 X) = eqToHom (by simp) := by
  simpa [homFiber] using GrothendieckOp.homFiber_id (Opposite.unop X)

@[simp]
theorem homBase_comp {X Y Z : CoGrothendieck G} (f : X ⟶ Y)
    (g : Y ⟶ Z) : homBase (f ≫ g) = homBase f ≫ homBase g :=
  rfl

@[simp]
theorem homFiber_comp {X Y Z : CoGrothendieck G} (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    homFiber (f ≫ g) =
      homFiber f ≫ (G.map (homBase f).op).toFunctor.map (homFiber g) ≫
        eqToHom (by simp) := by
  simpa [homFiber, homBase] using
    GrothendieckOp.homFiber_comp (Quiver.Hom.unop g) (Quiver.Hom.unop f)
```

Note in `homFiber_comp` the argument order swap
(`g.unop`, `f.unop`): composition in the opposite category
reverses, which is what makes the `CoGrothendieck` statement come
out with `f` first. The tactic proofs are candidates; statements
are contractual.

- [ ] **Step 2: Build**

Run: `lake build`
Expected: success, iterating on tactic proofs only.

- [ ] **Step 3: Add tests**

```lean
/-! ## `CoGrothendieck` morphisms -/

/-- A sample morphism `coObj ⟶ coObj'`: base `Bool → Nat`, fiber
`Nat → String` (source fiber to target fiber — contravariant hom
direction with a constant functor). -/
def coHom : coObj ⟶ coObj' :=
  CoGrothendieck.homMk (↾fun b => (cond b 1 0 : Nat))
    (↾fun n : Nat => toString n)

/-- A third object, for composition tests. -/
def coObj'' : CoGrothendieck constTypeContra :=
  CoGrothendieck.mk Unit Bool

/-- A second morphism, composable after `coHom`. -/
def coHom' : coObj' ⟶ coObj'' :=
  CoGrothendieck.homMk (↾fun _ => ()) (↾String.isEmpty)

theorem coHom_base :
    CoGrothendieck.homBase coHom = ↾fun b => (cond b 1 0 : Nat) :=
  rfl

theorem coHom_fiber :
    CoGrothendieck.homFiber coHom = ↾fun n : Nat => toString n :=
  rfl

theorem coHom_eta :
    CoGrothendieck.homMk (CoGrothendieck.homBase coHom)
      (CoGrothendieck.homFiber coHom) = coHom :=
  rfl

theorem coComp_base :
    CoGrothendieck.homBase (coHom ≫ coHom') =
      CoGrothendieck.homBase coHom ≫ CoGrothendieck.homBase coHom' :=
  rfl

theorem coComp_fiber :
    CoGrothendieck.homFiber (coHom ≫ coHom') =
      ↾fun n : Nat => (toString n).isEmpty :=
  rfl
```

- [ ] **Step 4: Build, test, verify**

Run: `lake build && lake test`
Expected: success. `lean_verify` on
`CategoryTheory.CoGrothendieck.homMk` and
`CategoryTheory.CoGrothendieck.hom_ext`.

- [ ] **Step 5: Commit**

```bash
jj commit -m "feat(cat): add CoGrothendieck hom interface"
```

---

### Task 7: `forget` projections

**Files:**

- Modify: `Geb/Mathlib/CategoryTheory/Grothendieck.lean`
- Modify: `GebTests/Mathlib/CategoryTheory/Grothendieck.lean`

**Interfaces:**

- Consumes: Tasks 3–6 APIs.
- Produces: `GrothendieckOp.forget (F) : GrothendieckOp F ⥤ C`
  and `CoGrothendieck.forget (G) : CoGrothendieck G ⥤ C`, with
  simp lemmas `forget_obj`, `forget_map` in each namespace.
  Task 9's consistency lemmas mention both `forget`s.

- [ ] **Step 1: Add `GrothendieckOp.forget` (insert before the existing `end GrothendieckOp`)**

```lean
/-- The projection `GrothendieckOp F ⥤ C` onto the base category. -/
def forget (F : C ⥤ Cat.{v₂, u₂}) : GrothendieckOp F ⥤ C :=
  Grothendieck.forget (F ⋙ Cat.opFunctor)

@[simp]
theorem forget_obj (X : GrothendieckOp F) : (forget F).obj X = X.base :=
  rfl

@[simp]
theorem forget_map {X Y : GrothendieckOp F} (f : X ⟶ Y) :
    (forget F).map f = homBase f :=
  rfl
```

(`variable {F}` is already in scope; the two lemmas take `F`
implicit through it — match the file's existing variable block.)

- [ ] **Step 2: Add `CoGrothendieck.forget` (insert before the existing `end CoGrothendieck`)**

```lean
/-- The projection `CoGrothendieck G ⥤ C` onto the base category. -/
def forget (G : Cᵒᵖ ⥤ Cat.{v₂, u₂}) : CoGrothendieck G ⥤ C :=
  (GrothendieckOp.forget G).leftOp

@[simp]
theorem forget_obj (X : CoGrothendieck G) : (forget G).obj X = X.base :=
  rfl

@[simp]
theorem forget_map {X Y : CoGrothendieck G} (f : X ⟶ Y) :
    (forget G).map f = homBase f :=
  rfl
```

- [ ] **Step 3: Build**

Run: `lake build`
Expected: success.

- [ ] **Step 4: Add tests**

```lean
/-! ## Projections -/

theorem coForget_obj :
    (CoGrothendieck.forget constTypeContra).obj coObj = Bool := rfl

theorem coForget_map :
    (CoGrothendieck.forget constTypeContra).map coHom =
      CoGrothendieck.homBase coHom :=
  rfl
```

- [ ] **Step 5: Build, test, verify, commit**

Run: `lake build && lake test`; `lean_verify` both `forget`s.

```bash
jj commit -m "feat(cat): add GrothendieckOp and CoGrothendieck projections"
```

---

### Task 8: `map` functoriality

**Files:**

- Modify: `Geb/Mathlib/CategoryTheory/Grothendieck.lean`
- Modify: `GebTests/Mathlib/CategoryTheory/Grothendieck.lean`

**Interfaces:**

- Consumes: Tasks 3–6 APIs.
- Produces: `GrothendieckOp.map` / `CoGrothendieck.map` with
  `map_id_eq`, `map_comp_eq`, `mapIdIso`, `mapCompIso`,
  `map_obj_mk`, `homBase_map_map`, and `homFiber_map_map` in each
  namespace, exact signatures below.

- [ ] **Step 1: Add `GrothendieckOp.map` and laws**

Insert before the existing `end GrothendieckOp`:

```lean
/-- A natural transformation `α : F ⟶ F'` induces a functor
`GrothendieckOp F ⥤ GrothendieckOp F'`. -/
def map {F F' : C ⥤ Cat.{v₂, u₂}} (α : F ⟶ F') :
    GrothendieckOp F ⥤ GrothendieckOp F' :=
  Grothendieck.map (whiskerRight α Cat.opFunctor)

@[simp]
theorem map_obj_mk {F F' : C ⥤ Cat.{v₂, u₂}} (α : F ⟶ F') (b : C)
    (f : F.obj b) :
    (map α).obj (mk b f) = mk b ((α.app b).toFunctor.obj f) :=
  rfl

@[simp]
theorem homBase_map_map {F F' : C ⥤ Cat.{v₂, u₂}} (α : F ⟶ F')
    {X Y : GrothendieckOp F} (f : X ⟶ Y) :
    homBase ((map α).map f) = homBase f :=
  rfl

@[simp]
theorem homFiber_map_map {F F' : C ⥤ Cat.{v₂, u₂}} (α : F ⟶ F')
    {X Y : GrothendieckOp F} (f : X ⟶ Y) :
    homFiber ((map α).map f) =
      (α.app Y.base).toFunctor.map (homFiber f) ≫
        eqToHom (congrArg
          (fun p : F.obj X.base ⟶ F'.obj Y.base =>
            p.toFunctor.obj X.fiber)
          (α.naturality (homBase f))) := by
  simp [homFiber, homBase, map, eqToHom_unop]

theorem map_id_eq (F : C ⥤ Cat.{v₂, u₂}) :
    map (𝟙 F) = 𝟭 (GrothendieckOp F) := by
  rw [map, whiskerRight_id']
  exact Grothendieck.map_id_eq

theorem map_comp_eq {F F' F'' : C ⥤ Cat.{v₂, u₂}} (α : F ⟶ F')
    (β : F' ⟶ F'') : map (α ≫ β) = map α ⋙ map β := by
  rw [map, whiskerRight_comp]
  exact Grothendieck.map_comp_eq _ _

/-- `map (𝟙 F)` is the identity functor, as an isomorphism. -/
def mapIdIso (F : C ⥤ Cat.{v₂, u₂}) : map (𝟙 F) ≅ 𝟭 (GrothendieckOp F) :=
  eqToIso (map_id_eq F)

/-- `map` sends composition of natural transformations to composition
of functors, as an isomorphism. -/
def mapCompIso {F F' F'' : C ⥤ Cat.{v₂, u₂}} (α : F ⟶ F')
    (β : F' ⟶ F'') : map (α ≫ β) ≅ map α ⋙ map β :=
  eqToIso (map_comp_eq α β)
```

(`whiskerRight_id'` is the mathlib name for
`whiskerRight (𝟙 F) H = 𝟙 (F ⋙ H)`; if the name has drifted,
find the current one with `lean_local_search "whiskerRight_id"`.)

Proof notes for `homFiber_map_map` (both namespaces): the
`congrArg`-over-naturality side conditions are
statement-verified for the `GrothendieckOp` form; the
`CoGrothendieck` form is its direct mirror. The main tactic
scripts are candidates known to leave a residual goal of the
shape

```text
(eqToHom _ ≫ ((whiskerRight α Cat.opFunctor).app Y.base).toFunctor.map
    f.fiber).unop =
  (α.app Y.base).toFunctor.map f.fiber.unop ≫ eqToHom _
```

— push `unop` through the composition (`unop_comp`,
`eqToHom_unop`) and finish with `eqToHom` normalization
(`eqToHom_trans`, `Category.comp_id`/`id_comp`), iterating with
`lean_goal`.

- [ ] **Step 2: Add `CoGrothendieck.map` and laws**

Insert before the existing `end CoGrothendieck`:

```lean
/-- A natural transformation `α : G ⟶ G'` induces a functor
`CoGrothendieck G ⥤ CoGrothendieck G'` (covariantly in `α`). -/
def map {G G' : Cᵒᵖ ⥤ Cat.{v₂, u₂}} (α : G ⟶ G') :
    CoGrothendieck G ⥤ CoGrothendieck G' :=
  (GrothendieckOp.map α).op

@[simp]
theorem map_obj_mk {G G' : Cᵒᵖ ⥤ Cat.{v₂, u₂}} (α : G ⟶ G') (b : C)
    (f : G.obj (Opposite.op b)) :
    (map α).obj (mk b f) =
      mk b ((α.app (Opposite.op b)).toFunctor.obj f) :=
  rfl

@[simp]
theorem homBase_map_map {G G' : Cᵒᵖ ⥤ Cat.{v₂, u₂}} (α : G ⟶ G')
    {X Y : CoGrothendieck G} (f : X ⟶ Y) :
    homBase ((map α).map f) = homBase f :=
  rfl

@[simp]
theorem homFiber_map_map {G G' : Cᵒᵖ ⥤ Cat.{v₂, u₂}} (α : G ⟶ G')
    {X Y : CoGrothendieck G} (f : X ⟶ Y) :
    homFiber ((map α).map f) =
      (α.app (Opposite.op X.base)).toFunctor.map (homFiber f) ≫
        eqToHom (congrArg
          (fun p : G.obj (Opposite.op Y.base) ⟶
              G'.obj (Opposite.op X.base) =>
            p.toFunctor.obj Y.fiber)
          (α.naturality ((homBase f).op))) := by
  simpa [homFiber, map] using
    GrothendieckOp.homFiber_map_map α (Quiver.Hom.unop f)

theorem map_id_eq (G : Cᵒᵖ ⥤ Cat.{v₂, u₂}) :
    map (𝟙 G) = 𝟭 (CoGrothendieck G) := by
  rw [map, GrothendieckOp.map_id_eq]
  rfl

theorem map_comp_eq {G G' G'' : Cᵒᵖ ⥤ Cat.{v₂, u₂}} (α : G ⟶ G')
    (β : G' ⟶ G'') : map (α ≫ β) = map α ⋙ map β := by
  rw [map, GrothendieckOp.map_comp_eq]
  rfl

/-- `map (𝟙 G)` is the identity functor, as an isomorphism. -/
def mapIdIso (G : Cᵒᵖ ⥤ Cat.{v₂, u₂}) : map (𝟙 G) ≅ 𝟭 (CoGrothendieck G) :=
  eqToIso (map_id_eq G)

/-- `map` sends composition of natural transformations to composition
of functors, as an isomorphism. -/
def mapCompIso {G G' G'' : Cᵒᵖ ⥤ Cat.{v₂, u₂}} (α : G ⟶ G')
    (β : G' ⟶ G'') : map (α ≫ β) ≅ map α ⋙ map β :=
  eqToIso (map_comp_eq α β)
```

- [ ] **Step 3: Build**

Run: `lake build`
Expected: success; iterate on the four `rw` proofs only.

- [ ] **Step 4: Add tests**

```lean
/-! ## Functoriality in the functor -/

/-- The `List` endofunctor on the category of types, with bundled
morphisms. -/
def listFunctor : Type ⥤ Type where
  obj X := List X
  map f := ↾(List.map (ConcreteCategory.hom f))
  map_id X := by ext l; simp
  map_comp f g := by ext l; simp

/-- A natural transformation between constant functors, induced by
`listFunctor` via `Functor.const`. -/
def constListNatTrans : constTypeContra ⟶ constTypeContra :=
  (Functor.const (Type : Type 1)ᵒᵖ).map listFunctor.toCatHom

theorem coMap_obj :
    (CoGrothendieck.map constListNatTrans).obj coObj =
      CoGrothendieck.mk Bool (List Nat) := by
  simp [coObj, constListNatTrans, listFunctor]

theorem coMap_map_base :
    CoGrothendieck.homBase
        ((CoGrothendieck.map constListNatTrans).map coHom) =
      CoGrothendieck.homBase coHom :=
  rfl
```

(`listFunctor`'s `map_id`/`map_comp` are `aesop_cat` autoparams;
the explicit `by ext l; simp` scripts are candidates — omit the
two fields entirely if the autoparam discharges them.)

- [ ] **Step 5: Build, test, verify, commit**

Run: `lake build && lake test`; `lean_verify` both `map`s.

```bash
jj commit -m "feat(cat): add GrothendieckOp and CoGrothendieck map"
```

---

### Task 9: Packaged functors

**Files:**

- Modify: `Geb/Mathlib/CategoryTheory/Grothendieck.lean`
- Modify: `GebTests/Mathlib/CategoryTheory/Grothendieck.lean`

**Interfaces:**

- Consumes: Task 2's `Grothendieck.functorToCat` shape; Tasks
  7–8's `forget` and `map`.
- Produces: `GrothendieckOp.functor`,
  `GrothendieckOp.functorToCat`, `CoGrothendieck.functor`,
  `CoGrothendieck.functorToCat` with the exact signatures below,
  plus consistency lemmas `functor_obj_hom` and
  `functorToCat_obj` in each namespace.

- [ ] **Step 1: Add the `GrothendieckOp` packaged forms**

Insert before the existing `end GrothendieckOp`:

```lean
/-- The `GrothendieckOp` construction as a functor from `↑E ⥤ Cat` to
the over category of `E` in `Cat`: post-compose with `Cat.opFunctor`,
then apply mathlib's `Grothendieck.functor`. -/
def functor {E : Cat.{v, u}} :
    (↑E ⥤ Cat.{v, u}) ⥤ Over (T := Cat.{v, u}) E :=
  (whiskeringRight ↑E Cat.{v, u} Cat.{v, u}).obj Cat.opFunctor ⋙
    Grothendieck.functor

@[simp]
theorem functor_obj_hom {E : Cat.{v, u}} (F : ↑E ⥤ Cat.{v, u}) :
    (functor.obj F).hom = (forget F).toCatHom :=
  rfl

/-- The `GrothendieckOp` construction as a functor to `Cat`. -/
def functorToCat {E : Cat.{v, u}} : (↑E ⥤ Cat.{v, u}) ⥤ Cat.{v, u} :=
  functor ⋙ Over.forget E

@[simp]
theorem functorToCat_obj {E : Cat.{v, u}} (F : ↑E ⥤ Cat.{v, u}) :
    functorToCat.obj F = Cat.of (GrothendieckOp F) :=
  rfl
```

- [ ] **Step 2: Add the `CoGrothendieck` packaged forms**

Insert before the existing `end CoGrothendieck`:

```lean
/-- The `CoGrothendieck` construction as a functor from `(↑E)ᵒᵖ ⥤ Cat`
to the over category of `E` in `Cat`: apply `GrothendieckOp.functor`
over the base `(↑E)ᵒᵖ`, oppositize the total category with
`Over.post Cat.opFunctor`, and retarget along `unopUnop`. -/
def functor {E : Cat.{v, u}} :
    ((↑E)ᵒᵖ ⥤ Cat.{v, u}) ⥤ Over (T := Cat.{v, u}) E :=
  GrothendieckOp.functor (E := Cat.of (↑E)ᵒᵖ) ⋙
    Over.post Cat.opFunctor ⋙ Over.map (unopUnop ↑E).toCatHom

@[simp]
theorem functor_obj_hom {E : Cat.{v, u}} (G : (↑E)ᵒᵖ ⥤ Cat.{v, u}) :
    (functor.obj G).hom = (forget G).toCatHom := by
  rfl

/-- The `CoGrothendieck` construction as a functor to `Cat`. -/
def functorToCat {E : Cat.{v, u}} :
    ((↑E)ᵒᵖ ⥤ Cat.{v, u}) ⥤ Cat.{v, u} :=
  functor ⋙ Over.forget E

@[simp]
theorem functorToCat_obj {E : Cat.{v, u}} (G : (↑E)ᵒᵖ ⥤ Cat.{v, u}) :
    functorToCat.obj G = Cat.of (CoGrothendieck G) :=
  rfl
```

`CoGrothendieck.functor_obj_hom` compares
`(GrothendieckOp.forget G).op ⋙ unopUnop ↑E` (the pipeline's
projection, with an `Over.map` composite `p ≫ f`) against
`(GrothendieckOp.forget G).leftOp`; these agree definitionally
but the `rfl` crosses `Over.map`'s `Comma` plumbing. If plain
`rfl` fails, the fallback proof shape is:

```lean
  apply Cat.Hom.ext
  exact Functor.ext (fun X => rfl) (fun X Y f => rfl)
```

adjusting the `eqToHom` arguments `Functor.ext` demands with
compiler feedback. The statement is contractual. Likewise
`functorToCat_obj`: the object passes through
`Over.map`/`Over.post`, so its underlying `Cat.of` argument is
`(Grothendieck (G ⋙ Cat.opFunctor))ᵒᵖ` — definitionally
`CoGrothendieck G`.

- [ ] **Step 3: Build**

Run: `lake build`
Expected: success.

- [ ] **Step 4: Add tests**

```lean
/-! ## Packaged functors -/

theorem coFunctorToCat_obj :
    (CoGrothendieck.functorToCat (E := Cat.of (Type : Type 1))).obj
        constTypeContra =
      Cat.of (CoGrothendieck constTypeContra) :=
  rfl

theorem coFunctor_obj_hom :
    ((CoGrothendieck.functor (E := Cat.of (Type : Type 1))).obj
        constTypeContra).hom =
      (CoGrothendieck.forget constTypeContra).toCatHom := by
  simp
```

(Same parenthesization rule as Task 2: `(E := …)` attaches to the
packaged functor, never to `.obj`.)

- [ ] **Step 5: Build, test, verify, commit**

Run: `lake build && lake test`; `lean_verify` all four packaged
defs.

```bash
jj commit -m "feat(cat): add packaged Grothendieck op-construction functors"
```

---

### Task 10: Documentation and final gates

**Files:**

- Modify: `docs/references.bib`
- Modify: `docs/index.md`
- Modify: `Geb/Mathlib/CategoryTheory/Grothendieck.lean`
  (References section only, if adjustments surfaced)

**Interfaces:**

- Consumes: everything above.
- Produces: citations resolvable from the module docstring; the
  docs index entry; a fully gated branch.

- [ ] **Step 1: Add bib entries**

Append at the end of `docs/references.bib`:

```bibtex
@misc{Vistoli2008,
  author        = {Vistoli, Angelo},
  title         = {Notes on Grothendieck topologies, fibered categories
                   and descent theory},
  year          = {2008},
  eprint        = {math/0412512},
  archivePrefix = {arXiv},
  primaryClass  = {math.AG},
}

@book{JohnsonYau2021,
  author        = {Johnson, Niles and Yau, Donald},
  title         = {2-Dimensional Categories},
  publisher     = {Oxford University Press},
  year          = {2021},
  eprint        = {2002.06055},
  archivePrefix = {arXiv},
  primaryClass  = {math.CT},
}
```

- [ ] **Step 2: Add the docs index entry**

In `docs/index.md` § Implemented content, add this entry before
the `Geb/Mathlib/Data/PFunctor/Slice/` entry (the module depends
only on mathlib, so it precedes the `PFunctor` entries in
topological order):

```markdown
- `Geb/Mathlib/CategoryTheory/Grothendieck.lean` — covariant and
  contravariant Grothendieck constructions for 1-functors.
  `Grothendieck.functorToCat` packages mathlib's covariant
  construction as a functor to `Cat`. `GrothendieckOp F` is the
  covariant construction applied to the oppositization
  `F ⋙ Cat.opFunctor`; `CoGrothendieck G`, for `G : Cᵒᵖ ⥤ Cat`,
  is its opposite category — the contravariant Grothendieck
  construction, which mathlib states in a comment but implements
  only for pseudofunctors. Both carry constructor/destructor
  interfaces (`mk`/`base`/`fiber`, `homMk`/`homBase`/`homFiber`)
  using morphisms of `C`, with `rfl` round-trips, projections
  (`forget`), functoriality (`map`), and packaged forms
  (`functor` into `Over`, `functorToCat` into `Cat`). The source
  and test modules are listed in `GebMeta.classicalAllowedModules`
  because mathlib's `Grothendieck` and `Cat.opFunctor` are
  `Classical.choice`-dependent.
```

- [ ] **Step 3: Markdown gates**

Run: `doctoc --update-only docs/index.md && markdownlint-cli2 "**/*.md"`
Expected: 0 errors.

- [ ] **Step 4: Commit the documentation changes**

```bash
jj commit -m "doc(cat): cite and index the Grothendieck constructions"
```

(Committing before the review step keeps the `doc` commit free of
code changes; `jj commit` sweeps the whole working copy.)

- [ ] **Step 5: Full verification gates and review**

Run: `lake build && lake test && lake lint && scripts/lint-imports.sh`
Expected: all succeed. Then run the `lean4:review` skill over the
two new `.lean` files and resolve findings. Commit any resulting
`.lean` edits as their own appropriately-typed commits
(`style(cat): …` / `fix(cat): …` / `refactor(cat): …` per the
nature of each fix) before proceeding to Task 11.

---

### Task 11: Remove transient spec and plan (final review sign-off only)

Execute this task only after the user's line-by-line diff review
of the branch and any pre-push review rounds are complete; it is
the branch's final commit per the transient-artifact rule.

**Files:**

- Delete: `docs/superpowers/specs/2026-07-07-cogrothendieck-design.md`
- Delete: `docs/superpowers/plans/2026-07-07-cogrothendieck.md`

- [ ] **Step 1: Remove the files**

```bash
rm docs/superpowers/specs/2026-07-07-cogrothendieck-design.md \
   docs/superpowers/plans/2026-07-07-cogrothendieck.md
```

- [ ] **Step 2: Verify nothing references them**

Run:

```bash
grep -rn "2026-07-07-cogrothendieck" . \
  --exclude-dir={.lake,.jj,.git,node_modules,.remember} \
  | grep -v docs/superpowers
```

Expected: no output.

- [ ] **Step 3: Run `scripts/pre-push.sh`**

Expected: checklist passes.

- [ ] **Step 4: Commit**

```bash
jj commit -m "chore(cat): remove transient contravariant Grothendieck spec and plan"
```

No push occurs in this plan; pushing awaits the user's
line-by-line review per AGENTS.md.
