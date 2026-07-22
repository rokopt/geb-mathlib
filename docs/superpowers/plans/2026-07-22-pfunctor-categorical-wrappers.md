# Categorical wrappers for `PFunctor` and `WType` — implementation plan

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Global Constraints](#global-constraints)
- [Per-task gate](#per-task-gate)
- [File structure](#file-structure)
  - [Task 1: W-type fold laws](#task-1-w-type-fold-laws)
  - [Task 2: the `PFunctor` functor](#task-2-the-pfunctor-functor)
  - [Task 3: the W-type as an algebra, with initiality as `Unique`](#task-3-the-w-type-as-an-algebra-with-initiality-as-unique)
  - [Task 4: the `IsInitial` packaging](#task-4-the-isinitial-packaging)
  - [Task 5: rebuild `domFunctor` on `Subfunctor`](#task-5-rebuild-domfunctor-on-subfunctor)
  - [Task 6: documentation and roadmap](#task-6-documentation-and-roadmap)
  - [Task 7: remove the transient spec and plan](#task-7-remove-the-transient-spec-and-plan)

<!-- END doctoc -->

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` (recommended) or
> `superpowers:executing-plans` to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Characterise mathlib's `WType` as the initial algebra of the
endofunctor of mathlib's univariate `PFunctor`, and rebuild the existing
slice wrapper on the result.

**Architecture:** mathlib already supplies the existence half of
initiality (`WType.elim`); the only missing mathematics is its
uniqueness. Four new modules layer on that: the fold laws, the functor
(as `ofTypeFunctor`), the algebra with initiality stated choice-free as
`Unique`, and a one-declaration module packaging it as mathlib's
`Limits.IsInitial`. `Slice/Functor.lean`'s `domFunctor` is then rebuilt
as a `CategoryTheory.Subfunctor` of the composite, which is
definitionally equal to the current definition.

**Tech Stack:** Lean 4 (`v4.33.0-rc1`), mathlib, `lake`, `jj` (not
`git`), `doctoc`, `markdownlint-cli2`.

**Spec:** `docs/superpowers/specs/2026-07-21-pfunctor-categorical-wrappers-design.md`

## Global Constraints

Every task's requirements implicitly include this section.

- **No `noncomputable`, anywhere.** No `sorry` in any commit; no `admit`
  ever. Use `_` for an unfilled hole while working.
- **Axioms.** Every declaration in `Geb/` and `GebTests/` must depend
  only on `{propext, Quot.sound}`, enforced by `lake lint`. The sole
  exception is `Geb.Mathlib.Data.PFunctor.Univariate.Initial` and its
  test mirror, which are added to `GebMeta.classicalAllowedModules` in
  Task 4 and may additionally use `Classical.choice`.
- **Module system.** Every file opens with the copyright block, then
  `module`, then imports. Use `public import` for anything re-exported
  to downstream users, plain `import` in `GebTests/` files. Source files
  carrying definitions open `public section` after the module docstring.
  A `GebTests/` module whose declarations another test module imports
  (here, only `Univariate/Fixtures.lean`) also needs `public section`,
  since a `def` in a test module is otherwise private; the rest keep
  `set_option linter.privateModule false` and plain `import`.
- **`@[expose]`.** For a `def`, `@[expose]` is the only thing that
  exports the body across a module boundary; reducibility attributes do
  not. A class-typed `def` additionally needs `@[instance_reducible]` or
  the `warn.classDefReducibility` warning becomes an error under
  `weak.warningAsError = true` (`lakefile.toml:15`).
- **Style.** 2-space indent, 100-character lines, Unicode notation
  (`↦`, `⟶`, `≅`, `⥤`, `∀`, `Σ`), one declaration per line.
- **Docstrings.** Module docstring (`/-! ... -/`) mandatory after
  imports, with `# Title`, summary, and every applicable section of
  `## Main definitions`, `## Main statements`,
  `## Implementation notes`, `## References`, `## Tags` — each present
  when it has content, omitted (never a placeholder) when vacuous.
  `/-- ... -/` mandatory on every `def`, `structure`, `instance`, and
  theorem of public interest. No development-history references.
- **Recursors only.** No `induction` tactic, no self-recursive `def`, no
  self-referential `inductive`. Drive recursion with an explicit
  recursor application (`WType.rec`).
- **Universe polymorphism.** Maximal polymorphism that compiles; write
  full explicit `.{...}` universe lists where a level must be pinned.
- **Imports.** `Geb/Mathlib/` may import only `Mathlib.*` and
  `Geb.Mathlib.*`; `GebTests/Mathlib/` adds `GebTests.Mathlib.*`. The
  strings `Geb.Mathlib.` and `GebTests.Mathlib.` must not appear outside
  `^import` lines — not in namespaces, bodies, docstrings, or comments.
- **VCS is `jj`, never `git`.** A PreToolUse hook blocks mutating `git`
  subcommands. Commit with `jj describe -m "..."` then `jj new`.
- **Commit messages.** mathlib's convention: `type(scope): subject`,
  imperative present tense, lowercase first letter, no trailing period.
  Types: `feat | fix | doc | style | refactor | test | chore | perf | ci`.
- **Citations.** Cite only `[GambinoHyland2004]` and
  `[AltenkirchGhaniHancockMcBrideMorris2015]`; both already exist in
  `docs/references.bib`. Add no new key. `functor_obj`, `functor_map`,
  and `wStrIso_hom` carry no citation — they state definitional
  equalities, not published mathematics.

## Per-task gate

Every task ends with these commands green before its commit step:

```bash
lake build
lake test
lake lint
lake lint -- GebTests
bash scripts/lint-imports.sh
```

`lakefile.toml` sets `testDriver = "GebTests"`, so `lake test` already
builds `GebTests`; no separate build step is needed here.
`scripts/lint-imports.sh` needs no build and is cheap, so it runs per
task rather than only at Task 7 — an import violation is then fixed in
the commit that introduced it. If Task 7's `lake shake` nonetheless
demands a source change, fix it and `jj squash` the fix into the commit
that introduced the import rather than adding a follow-up commit.

The full pre-push checklist (`bash scripts/pre-push.sh`) runs once, in
Task 7.

## File structure

| File | Responsibility | Task |
| --- | --- | --- |
| `Geb/Mathlib/Data/W/Basic.lean` | fold computation rule and uniqueness | 1 |
| `Geb/Mathlib/Data/W.lean` | directory index | 1 |
| `Geb/Mathlib/Data.lean` | extended with the `W` index | 1 |
| `GebTests/Mathlib/Data/W/Basic.lean` | tests for the fold laws | 1 |
| `GebTests/Mathlib/Data/W.lean` | test directory index | 1 |
| `GebTests/Mathlib/Data.lean` | extended | 1 |
| `Geb/Mathlib/Data/PFunctor/Univariate/Functor.lean` | the functor and its map identities | 2 |
| `Geb/Mathlib/Data/PFunctor/Univariate.lean` | directory index | 2 |
| `Geb/Mathlib/Data/PFunctor.lean` | extended | 2 |
| `GebTests/…/Univariate/Fixtures.lean` | shared test fixture `testPFunctor` | 2 |
| `GebTests/…/Univariate/Functor.lean`, `Univariate.lean`, `PFunctor.lean` | mirrors | 2 |
| `Geb/Mathlib/Data/PFunctor/Univariate/W.lean` | algebra, `Unique`, structure-map iso | 3 |
| `Geb/…/Univariate.lean`, `GebTests/…/Univariate.lean` | extended | 3, 4 |
| `GebTests/…/Univariate/W.lean` | mirror | 3 |
| `Geb/Mathlib/Data/PFunctor/Univariate/Initial.lean` | `Limits.IsInitial` packaging | 4 |
| `GebMeta.lean` | allowlist entries | 4 |
| `GebTests/…/Univariate/Initial.lean` | mirror | 4 |
| `Geb/Mathlib/Data/PFunctor/Slice/Functor.lean` | `domFunctor` rebuilt on `Subfunctor` | 5 |
| `GebTests/…/Slice/Functor.lean` | mirror, appended | 5 |
| `docs/index.md`, `TODO.md` | documentation | 6 |

---

### Task 1: W-type fold laws

**Files:**

- Create: `Geb/Mathlib/Data/W/Basic.lean`
- Create: `Geb/Mathlib/Data/W.lean`
- Modify: `Geb/Mathlib/Data.lean`
- Create: `GebTests/Mathlib/Data/W/Basic.lean`
- Create: `GebTests/Mathlib/Data/W.lean`
- Modify: `GebTests/Mathlib/Data.lean`

**Interfaces:**

- Consumes: nothing from this branch.
- Produces:
  - `WType.elim_mk {α : Type uA} {β : α → Type uB} {γ : Type uC}
    (fγ : (Σ a : α, β a → γ) → γ) (a : α) (f : β a → WType β) :
    WType.elim γ fγ (WType.mk a f) = fγ ⟨a, fun b ↦ WType.elim γ fγ (f b)⟩`
  - `WType.elim_unique {α : Type uA} {β : α → Type uB} {γ : Type uC}
    (fγ : (Σ a : α, β a → γ) → γ) (g : WType β → γ)
    (hg : ∀ (a : α) (f : β a → WType β),
      g (WType.mk a f) = fγ ⟨a, fun b ↦ g (f b)⟩) : g = WType.elim γ fγ`

- [ ] **Step 1: Write the failing test**

Create `GebTests/Mathlib/Data/W/Basic.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.Data.W.Basic

/-!
# Tests for the W-type fold laws

A concrete fold over binary trees exercises the computation rule and the
uniqueness of `WType.elim`.

## Tags

W-type, fold, initial algebra
-/

set_option linter.privateModule false

/-- The branching family of the test W-type: one node label, two
children. -/
abbrev TestBranch : Unit → Type := fun _ ↦ Bool

/-- The algebra computing a node count. Factored out as a named
definition so that `WType.elim_mk` and `WType.elim_unique` unify with it
without unfolding the fold. -/
def nodeCountStep (x : Σ _ : Unit, Bool → Nat) : Nat :=
  1 + x.2 true + x.2 false

/-- The node count of a test tree, as a fold. -/
def nodeCount : WType TestBranch → Nat :=
  WType.elim Nat nodeCountStep

-- The computation rule fires on a constructor application.
example (f : Bool → WType TestBranch) :
    nodeCount (WType.mk () f) = 1 + nodeCount (f true) + nodeCount (f false) :=
  WType.elim_mk nodeCountStep () f

/-- Uniqueness: any function satisfying the same recursion is the fold.
This is the declaration that anchors the import: its proof term names
`WType.elim_unique`, so `lake shake` observes the module under test. -/
theorem nodeCount_unique (g : WType TestBranch → Nat)
    (hg : ∀ (a : Unit) (f : Bool → WType TestBranch),
      g (WType.mk a f) = 1 + g (f true) + g (f false)) :
    g = nodeCount :=
  WType.elim_unique nodeCountStep g hg
```

Create `GebTests/Mathlib/Data/W.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import GebTests.Mathlib.Data.W.Basic

/-!
# W tests — index
-/
```

Add to `GebTests/Mathlib/Data.lean`, in alphabetical order among its
existing plain `import` lines (that file has no `public import` lines):

```lean
import GebTests.Mathlib.Data.W
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `lake build GebTests`

Expected: FAIL. `lake` reports the missing source file, not a module
error:

```text
error: no such file or directory ...
  file: <repo>/Geb/Mathlib/Data/W/Basic.lean
```

Only the failure and the named file matter; the numeric code is not
load-bearing.

- [ ] **Step 3: Write the implementation**

Create `Geb/Mathlib/Data/W/Basic.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Mathlib.Data.W.Basic

/-!
# The W-type fold: computation rule and uniqueness

`WType.elim` is the non-dependent fold of a W-type: the morphism into a
given algebra of the polynomial endofunctor `X ↦ Σ a, β a → X`. mathlib
states the fold but neither its computation rule as a named `@[simp]`
lemma nor its uniqueness. Together the two make `WType β` the initial
algebra of that endofunctor, stated concretely.

## Main statements

* `WType.elim_mk` — the computation rule: the fold of a constructor
  application is the algebra applied to the folded children.
* `WType.elim_unique` — uniqueness: a function satisfying the
  computation rule is the fold.

## Implementation notes

`elim_mk` holds by `rfl`; mathlib's equation compiler generates the
equation, and the named `@[simp]` form is what makes the hypothesis
shape of `elim_unique` usable by `simp` at call sites. `elim_unique`
drives its recursion through an explicit `WType.rec` application into a
`Prop`-valued motive.

## References

* [GambinoHyland2004]

## Tags

W-type, fold, initial algebra, polynomial functor
-/

public section

universe uA uB uC

namespace WType

/-- The fold's computation rule: folding a constructor application
applies the algebra to the children's folds. -/
@[simp] theorem elim_mk {α : Type uA} {β : α → Type uB} {γ : Type uC}
    (fγ : (Σ a : α, β a → γ) → γ) (a : α) (f : β a → WType β) :
    elim γ fγ (mk a f) = fγ ⟨a, fun b ↦ elim γ fγ (f b)⟩ :=
  rfl

/-- The fold is the unique function satisfying its computation rule.
With `elim` itself, this is the initiality of `WType β` among algebras
of the polynomial endofunctor `X ↦ Σ a, β a → X`. -/
theorem elim_unique {α : Type uA} {β : α → Type uB} {γ : Type uC}
    (fγ : (Σ a : α, β a → γ) → γ) (g : WType β → γ)
    (hg : ∀ (a : α) (f : β a → WType β),
      g (mk a f) = fγ ⟨a, fun b ↦ g (f b)⟩) :
    g = elim γ fγ := by
  funext x
  refine rec (motive := fun x ↦ g x = elim γ fγ x) (fun a f ih ↦ ?_) x
  rw [hg a f]
  exact congrArg (fun h ↦ fγ ⟨a, h⟩) (funext ih)

end WType
```

Create `Geb/Mathlib/Data/W.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.W.Basic

/-!
# W — index
-/
```

Add to `Geb/Mathlib/Data.lean`, in alphabetical order:

```lean
public import Geb.Mathlib.Data.W
```

- [ ] **Step 4: Run the gate**

```bash
lake build
lake test
lake lint
lake lint -- GebTests
bash scripts/lint-imports.sh
```

Expected: all PASS. `lake lint` in particular confirms the axiom
linter accepts both declarations (`elim_mk` depends on no axioms,
`elim_unique` on `{Quot.sound}`).

- [ ] **Step 5: Commit**

```bash
jj describe -m "feat(w): add the W-type fold computation rule and uniqueness"
jj new
```

---

### Task 2: the `PFunctor` functor

**Files:**

- Create: `Geb/Mathlib/Data/PFunctor/Univariate/Functor.lean`
- Create: `Geb/Mathlib/Data/PFunctor/Univariate.lean`
- Modify: `Geb/Mathlib/Data/PFunctor.lean`
- Create: `GebTests/Mathlib/Data/PFunctor/Univariate/Fixtures.lean`
- Create: `GebTests/Mathlib/Data/PFunctor/Univariate/Functor.lean`
- Create: `GebTests/Mathlib/Data/PFunctor/Univariate.lean`
- Modify: `GebTests/Mathlib/Data/PFunctor.lean`

**Interfaces:**

- Consumes: nothing from Task 1.
- Produces:
  - `PFunctor.functor (P : PFunctor.{uA, uB}) :
    CategoryTheory.Functor (Type v) (Type (max v uA uB))`, `@[expose]`
  - `PFunctor.functor_obj (P) (α : Type v) : (P.functor).obj α = P.Obj α`
  - `PFunctor.functor_map (P) {α β : Type v} (f : α → β) :
    (P.functor).map (↾f) = ↾(P.map f)`

- [ ] **Step 1: Write the failing test**

First create the shared test fixture,
`GebTests/Mathlib/Data/PFunctor/Univariate/Fixtures.lean`. Tasks 3 and
4 import it too, so it is `public section` — a `def` in a `GebTests`
module is otherwise private and not importable. That combination
(`public import` + `public section` in a test module) is already used
by `GebTests/Mathlib/Data/PFunctor/IndRec/*.lean`.

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Mathlib.Data.PFunctor.Univariate.Basic

/-!
# Shared fixture for the univariate `PFunctor` tests

The concrete polynomial functor the `Univariate` test modules share.
It is defined once here rather than repeated per module so the three
test modules exercise the same object.

## Main definitions

* `testPFunctor` — two shapes, two directions each.

## Tags

polynomial functor, PFunctor, container
-/

public section

/-- A concrete polynomial functor: two shapes, two directions each. -/
def testPFunctor : PFunctor.{0, 0} := ⟨Bool, fun _ ↦ Bool⟩
```

Then create `GebTests/Mathlib/Data/PFunctor/Univariate/Functor.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.Data.PFunctor.Univariate.Functor
import GebTests.Mathlib.Data.PFunctor.Univariate.Fixtures

/-!
# Tests for the univariate `PFunctor` functor wrapper

A concrete polynomial functor exercises the categorical wrapper and its
agreement with the upstream `Obj` / `map`.

## Tags

polynomial functor, PFunctor, container
-/

set_option linter.privateModule false

open CategoryTheory

/-- The categorical wrapper of `testPFunctor`: a named value from the
module under test, so `lake shake` observes the import. -/
def testFunctor : CategoryTheory.Functor (Type 0) (Type 0) :=
  testPFunctor.functor.{0, 0, 0}

-- The object map is the upstream interpretation.
example (α : Type 0) : testFunctor.obj α = testPFunctor.Obj α :=
  testPFunctor.functor_obj α

-- The morphism map is the upstream action.
example {α β : Type 0} (f : α → β) :
    testFunctor.map (↾f) = ↾(testPFunctor.map f) :=
  testPFunctor.functor_map f
```

Create `GebTests/Mathlib/Data/PFunctor/Univariate.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import GebTests.Mathlib.Data.PFunctor.Univariate.Functor

/-!
# Univariate tests — index
-/
```

Add to `GebTests/Mathlib/Data/PFunctor.lean`, in alphabetical order:

```lean
import GebTests.Mathlib.Data.PFunctor.Univariate
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `lake build GebTests`

Expected: FAIL:

```text
error: no such file or directory ...
  file: <repo>/Geb/Mathlib/Data/PFunctor/Univariate/Functor.lean
```

- [ ] **Step 3: Write the implementation**

Create `Geb/Mathlib/Data/PFunctor/Univariate/Functor.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Data.PFunctor.Univariate.Basic

/-!
# The functor of a univariate polynomial functor

Packages mathlib's `PFunctor` interpretation as a
`CategoryTheory.Functor`. The interpretation `P.Obj` already carries
`Functor` and `LawfulFunctor` instances upstream, so the categorical
functor is their transport along `CategoryTheory.ofTypeFunctor` rather
than a hand-written object map, morphism map, and pair of functor laws.

`P.Obj : Type v → Type (max v uA uB)` maps `Type v` to itself whenever
`uA ≤ v` and `uB ≤ v`, so the functor is stated at an unconstrained `v`
and instantiated at the universe an endofunctor is wanted in.

## Main definitions

* `PFunctor.functor` — the functor `Type v ⥤ Type (max v uA uB)`.

## Main statements

* `PFunctor.functor_obj` / `PFunctor.functor_map` — the categorical
  object and morphism maps are the upstream `PFunctor.Obj` and
  `PFunctor.map`.

## Implementation notes

Morphisms of `Type v` are bundled, so a function is promoted to a
morphism with `↾` and the underlying function of a morphism is read
through `ConcreteCategory.hom`; `functor_map` is therefore stated in
promoted form on both sides. `functor` is `@[expose]` so both statements
are exported `rfl` theorems. Inside `namespace PFunctor` under
`open CategoryTheory` the bare identifier `Functor` is ambiguous between
core `Functor` and `CategoryTheory.Functor`, so the latter is written in
full.

## References

* [AltenkirchGhaniHancockMcBrideMorris2015]

## Tags

polynomial functor, container, PFunctor, functor
-/

public section

universe uA uB v

open CategoryTheory

namespace PFunctor

/-- The functor `Type v ⥤ Type (max v uA uB)` interpreting a polynomial
functor, transported from the upstream `Functor` and `LawfulFunctor`
instances on `PFunctor.Obj`. -/
@[expose] def functor (P : PFunctor.{uA, uB}) :
    CategoryTheory.Functor (Type v) (Type (max v uA uB)) :=
  ofTypeFunctor P.Obj

/-- The categorical object map is the upstream interpretation. -/
theorem functor_obj (P : PFunctor.{uA, uB}) (α : Type v) :
    (P.functor).obj α = P.Obj α :=
  rfl

/-- The categorical morphism map is the upstream action, on both sides
in the promoted form `Type v` morphisms take. -/
theorem functor_map (P : PFunctor.{uA, uB}) {α β : Type v} (f : α → β) :
    (P.functor).map (↾f) = ↾(P.map f) :=
  rfl

end PFunctor
```

Create `Geb/Mathlib/Data/PFunctor/Univariate.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.PFunctor.Univariate.Functor

/-!
# Univariate — index
-/
```

Add to `Geb/Mathlib/Data/PFunctor.lean`, in alphabetical order (it goes
after `Slice`):

```lean
public import Geb.Mathlib.Data.PFunctor.Univariate
```

- [ ] **Step 4: Run the gate**

```bash
lake build
lake test
lake lint
lake lint -- GebTests
bash scripts/lint-imports.sh
```

Expected: all PASS.

- [ ] **Step 5: Commit**

```bash
jj describe -m "feat(pfunctor): wrap the univariate interpretation as a functor"
jj new
```

---

### Task 3: the W-type as an algebra, with initiality as `Unique`

**Files:**

- Create: `Geb/Mathlib/Data/PFunctor/Univariate/W.lean`
- Modify: `Geb/Mathlib/Data/PFunctor/Univariate.lean`
- Create: `GebTests/Mathlib/Data/PFunctor/Univariate/W.lean`
- Modify: `GebTests/Mathlib/Data/PFunctor/Univariate.lean`

**Interfaces:**

- Consumes: `WType.elim_unique` (Task 1); `PFunctor.functor` (Task 2).
- Produces:
  - `PFunctor.wAlgebra (P : PFunctor.{uA, uB}) :
    Endofunctor.Algebra (P.functor.{uA, uB, max uA uB})`, `@[expose]`
  - `PFunctor.wElim (P)
    (B : Endofunctor.Algebra (P.functor.{uA, uB, max uA uB})) :
    P.wAlgebra ⟶ B`, `@[expose]`
  - `PFunctor.wUniqueHom (P) (B) : Unique (P.wAlgebra ⟶ B)`,
    `@[expose, instance_reducible]`
  - `PFunctor.wStrIso (P) : (P.functor.{uA, uB, max uA uB}).obj P.W ≅ P.W`,
    `@[expose]`
  - `PFunctor.wStrIso_hom (P) : (P.wStrIso).hom = (P.wAlgebra).str`

- [ ] **Step 1: Write the failing test**

Create `GebTests/Mathlib/Data/PFunctor/Univariate/W.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.Data.PFunctor.Univariate.W
import GebTests.Mathlib.Data.PFunctor.Univariate.Fixtures

/-!
# Tests for the W-type as the initial algebra

A concrete polynomial functor exercises the algebra, the uniqueness of
morphisms out of it, and the structure-map isomorphism.

## Tags

polynomial functor, W-type, initial algebra
-/

set_option linter.privateModule false

open CategoryTheory

/-- The W-type algebra of `testPFunctor`: a named value from the module
under test, so `lake shake` observes the import. It is an `abbrev`, not
a `def`: a semireducible `def` is not unfolded by instance synthesis, so
`Subsingleton (wTestAlgebra ⟶ B)` would fail to resolve against the
`Unique` introduced below. -/
abbrev wTestAlgebra : Endofunctor.Algebra (testPFunctor.functor.{0, 0, 0}) :=
  testPFunctor.wAlgebra

-- The structure-map isomorphism's forward map is the algebra's structure map.
example : (testPFunctor.wStrIso).hom = wTestAlgebra.str :=
  testPFunctor.wStrIso_hom

-- Any two algebra morphisms out of the W-type algebra agree.
example (B : Endofunctor.Algebra (testPFunctor.functor.{0, 0, 0}))
    (g h : wTestAlgebra ⟶ B) : g = h := by
  haveI := testPFunctor.wUniqueHom B
  exact Subsingleton.elim g h
```

Add to `GebTests/Mathlib/Data/PFunctor/Univariate.lean`, in
alphabetical order (the eventual test-side order is `Fixtures`,
`Functor`, `Initial`, `W`; the source-side index has no `Fixtures`, so
there it is `Functor`, `Initial`, `W`):

```lean
import GebTests.Mathlib.Data.PFunctor.Univariate.W
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `lake build GebTests`

Expected: FAIL:

```text
error: no such file or directory ...
  file: <repo>/Geb/Mathlib/Data/PFunctor/Univariate/W.lean
```

- [ ] **Step 3: Write the implementation**

Create `Geb/Mathlib/Data/PFunctor/Univariate/W.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.PFunctor.Univariate.Functor
public import Geb.Mathlib.Data.W.Basic
public import Mathlib.CategoryTheory.Endofunctor.Algebra

/-!
# The W-type as the initial algebra of a polynomial functor

The W-type `P.W` of a polynomial functor carries an algebra structure
for the endofunctor `P.functor`, and is initial among such algebras.
Initiality is stated as `Unique` on the hom-set rather than through
mathlib's colimit API, which keeps the whole module free of
`Classical.choice`; the `Limits.IsInitial` packaging is the sibling
`Univariate.Initial` module.

The universe is forced here and only here: `P.W : Type (max uA uB)` is
the algebra's carrier, so `P.functor` is instantiated at
`v := max uA uB`.

## Main definitions

* `PFunctor.wAlgebra` — the algebra `⟨P.W, W.mk⟩`.
* `PFunctor.wElim` — the algebra morphism into any algebra.
* `PFunctor.wUniqueHom` — uniqueness of that morphism; initiality.
* `PFunctor.wStrIso` — the structure map as an isomorphism.

## Main statements

* `PFunctor.wStrIso_hom` — the isomorphism's forward map is the
  algebra's structure map.

## Implementation notes

`wUniqueHom` is a `def`, not an `instance`. As an instance it makes
`default` depend on how the hom type is spelled: the upstream
`Inhabited (Endofunctor.Algebra.Hom A A)` gives `𝟙` at the `Hom`
spelling, while at the definitionally equal `⟶` spelling `default`
becomes `wElim`. It carries both `@[expose]`, without which its body
does not cross the module boundary, and `@[instance_reducible]`, without
which a class-typed definition warns.

`wStrIso` is mathlib's fixed-point equivalence `WType.equivSigma`
transported along `Equiv.toIso`. The `Iso` form is preferred to
`IsIso` because an `Iso` carries its inverse as data, so consumers never
reach for `CategoryTheory.inv`, which depends on `Classical.choice`;
constructing `IsIso` is itself choice-free, so that is not the
distinguishing reason. There is no companion statement for `wStrIso.inv`:
it is `equivSigma`'s forward map, which is not definitionally
`PFunctor.W.dest`.

## References

* [GambinoHyland2004]

## Tags

polynomial functor, W-type, initial algebra, PFunctor
-/

public section

universe uA uB

open CategoryTheory

namespace PFunctor

/-- The W-type of `P` as an algebra of `P.functor`, with the constructor
`W.mk` as structure map. -/
@[expose] def wAlgebra (P : PFunctor.{uA, uB}) :
    Endofunctor.Algebra (P.functor.{uA, uB, max uA uB}) where
  a := P.W
  str := ↾W.mk

/-- The algebra morphism from the W-type algebra into any algebra: the
fold of that algebra's structure map. -/
@[expose] def wElim (P : PFunctor.{uA, uB})
    (B : Endofunctor.Algebra (P.functor.{uA, uB, max uA uB})) :
    P.wAlgebra ⟶ B where
  f := ↾(WType.elim B.a (ConcreteCategory.hom B.str))
  h := by ext x; cases x; rfl

/-- The W-type algebra is initial: the morphism into any algebra is
unique. -/
@[expose, instance_reducible] def wUniqueHom (P : PFunctor.{uA, uB})
    (B : Endofunctor.Algebra (P.functor.{uA, uB, max uA uB})) :
    Unique (P.wAlgebra ⟶ B) where
  default := P.wElim B
  uniq g := by
    refine Endofunctor.Algebra.Hom.ext ?_
    ext x
    refine congrFun (WType.elim_unique (ConcreteCategory.hom B.str)
      (ConcreteCategory.hom g.f) (fun a f ↦ ?_)) x
    exact (ConcreteCategory.congr_hom g.h (⟨a, f⟩ : P.Obj P.W)).symm

/-- The structure map of the W-type algebra is an isomorphism: mathlib's
fixed-point equivalence, read as an isomorphism of types. -/
@[expose] def wStrIso (P : PFunctor.{uA, uB}) :
    (P.functor.{uA, uB, max uA uB}).obj P.W ≅ P.W :=
  (WType.equivSigma P.B).symm.toIso

/-- The isomorphism's forward map is the algebra's structure map. -/
theorem wStrIso_hom (P : PFunctor.{uA, uB}) :
    (P.wStrIso).hom = (P.wAlgebra).str :=
  rfl

end PFunctor
```

Add to `Geb/Mathlib/Data/PFunctor/Univariate.lean`, in alphabetical
order (the eventual test-side order is `Fixtures`, `Functor`,
`Initial`, `W`; the source-side index has no `Fixtures`, so there it is
`Functor`, `Initial`, `W`):

```lean
public import Geb.Mathlib.Data.PFunctor.Univariate.W
```

- [ ] **Step 4: Run the gate**

```bash
lake build
lake test
lake lint
lake lint -- GebTests
bash scripts/lint-imports.sh
```

Expected: all PASS. `lake lint` confirms every declaration stays within
`{propext, Quot.sound}`.

- [ ] **Step 5: Commit**

```bash
jj describe -m "feat(pfunctor): characterise the W-type as the initial algebra"
jj new
```

---

### Task 4: the `IsInitial` packaging

**Files:**

- Create: `Geb/Mathlib/Data/PFunctor/Univariate/Initial.lean`
- Modify: `Geb/Mathlib/Data/PFunctor/Univariate.lean`
- Modify: `GebMeta.lean:58-66` (the `classicalAllowedModules` list)
- Create: `GebTests/Mathlib/Data/PFunctor/Univariate/Initial.lean`
- Modify: `GebTests/Mathlib/Data/PFunctor/Univariate.lean`

**Interfaces:**

- Consumes: `PFunctor.wAlgebra`, `PFunctor.wUniqueHom` (Task 3).
- Produces: `PFunctor.wIsInitial (P : PFunctor.{uA, uB}) :
  Limits.IsInitial P.wAlgebra`

- [ ] **Step 1: Write the failing test**

Create `GebTests/Mathlib/Data/PFunctor/Univariate/Initial.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.Data.PFunctor.Univariate.Initial
import GebTests.Mathlib.Data.PFunctor.Univariate.Fixtures

/-!
# Tests for the W-type algebra's initiality

Exercises the `Limits.IsInitial` packaging of the W-type algebra.

## Tags

polynomial functor, W-type, initial algebra
-/

set_option linter.privateModule false

open CategoryTheory

/-- The initiality witness: a named value from the module under test, so
`lake shake` observes the import. -/
def initialTestWitness :
    Limits.IsInitial (testPFunctor.wAlgebra) :=
  testPFunctor.wIsInitial

-- The witness yields a morphism into any algebra.
example (B : Endofunctor.Algebra (testPFunctor.functor.{0, 0, 0})) :
    testPFunctor.wAlgebra ⟶ B :=
  initialTestWitness.to B
```

Add to `GebTests/Mathlib/Data/PFunctor/Univariate.lean`, in
alphabetical order (the eventual test-side order is `Fixtures`,
`Functor`, `Initial`, `W`; the source-side index has no `Fixtures`, so
there it is `Functor`, `Initial`, `W`):

```lean
import GebTests.Mathlib.Data.PFunctor.Univariate.Initial
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `lake build GebTests`

Expected: FAIL:

```text
error: no such file or directory ...
  file: <repo>/Geb/Mathlib/Data/PFunctor/Univariate/Initial.lean
```

- [ ] **Step 3: Write the implementation**

Create `Geb/Mathlib/Data/PFunctor/Univariate/Initial.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.PFunctor.Univariate.W
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-!
# The W-type algebra as an initial object

Packages the choice-free initiality of `PFunctor.wAlgebra` — the `Unique`
instance on its hom-sets — as mathlib's `Limits.IsInitial`, making it
available to the colimit API.

## Main definitions

* `PFunctor.wIsInitial` — the W-type algebra is an initial object of the
  category of algebras.

## Implementation notes

This module is the whole of the workstream's `Classical.choice`
dependency, which enters through `Limits.IsInitial.ofUnique`. It is
listed in `GebMeta.classicalAllowedModules`. Consumers wanting a
choice-free development use `PFunctor.wUniqueHom` directly, which is a
`def` rather than an `instance`, so it is introduced here with `haveI`.

## References

* [GambinoHyland2004]

## Tags

polynomial functor, W-type, initial algebra, initial object
-/

public section

universe uA uB

open CategoryTheory

namespace PFunctor

/-- The W-type algebra is an initial object of the category of algebras
of `P.functor`. -/
def wIsInitial (P : PFunctor.{uA, uB}) :
    Limits.IsInitial (P.wAlgebra) :=
  haveI (B : Endofunctor.Algebra (P.functor.{uA, uB, max uA uB})) :
      Unique (P.wAlgebra ⟶ B) := P.wUniqueHom B
  Limits.IsInitial.ofUnique _

end PFunctor
```

Add to `Geb/Mathlib/Data/PFunctor/Univariate.lean`, in alphabetical
order (the eventual test-side order is `Fixtures`, `Functor`,
`Initial`, `W`; the source-side index has no `Fixtures`, so there it is
`Functor`, `Initial`, `W`):

```lean
public import Geb.Mathlib.Data.PFunctor.Univariate.Initial
```

Modify `GebMeta.lean`. The list is grouped by wrapper family, not
alphabetical, and its last element carries the closing bracket on the
same line, so insert the two new entries immediately after
`` `GebTests.Mathlib.Data.PFunctor.Presheaf.Functor, `` (currently
line 63), leaving the bracket line untouched:

```lean
   `Geb.Mathlib.Data.PFunctor.Univariate.Initial,
   `GebTests.Mathlib.Data.PFunctor.Univariate.Initial,
```

The resulting list reads:

```lean
def classicalAllowedModules : NameSet :=
  [`GebTests.Internal.AxiomLinterClassicalFixture,
   `Geb.Mathlib.Data.PFunctor.Slice.Functor,
   `Geb.Mathlib.Data.PFunctor.Presheaf.Functor,
   `GebTests.Mathlib.Data.PFunctor.Slice.Functor,
   `GebTests.Mathlib.Data.PFunctor.Presheaf.Functor,
   `Geb.Mathlib.Data.PFunctor.Univariate.Initial,
   `GebTests.Mathlib.Data.PFunctor.Univariate.Initial,
   `Geb.Mathlib.CategoryTheory.Grothendieck,
   `GebTests.Mathlib.CategoryTheory.Grothendieck].foldl (·.insert ·)
    ({} : NameSet)
```

- [ ] **Step 4: Run the gate**

```bash
lake build
lake test
lake lint
lake lint -- GebTests
bash scripts/lint-imports.sh
```

Expected: all PASS. If `lake lint` reports a nonstandard-axiom failure
for `PFunctor.wIsInitial`, the `GebMeta.lean` edit is missing or the
module name is misspelled — the allowlist matches exact module names.

- [ ] **Step 5: Commit**

```bash
jj describe -m "feat(pfunctor): package W-type initiality as an initial object"
jj new
```

---

### Task 5: rebuild `domFunctor` on `Subfunctor`

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/Slice/Functor.lean` (imports at
  lines 8-9; module docstring lines 11-56; `domFunctor` at lines 75-85)
- Modify: `GebTests/Mathlib/Data/PFunctor/Slice/Functor.lean` (append)

**Interfaces:**

- Consumes: `PFunctor.functor` (Task 2).
- Produces: `SliceDomPFunctor.domSubfunctor {dom : Type uD}
  (F : SliceDomPFunctor.{uA, uB} dom) :
  Subfunctor (Over.forget dom ⋙ F.toPFunctor.functor.{uA, uB, uD})`,
  `@[expose]`. `SliceDomPFunctor.domFunctor` keeps its existing
  signature and is definitionally unchanged.

- [ ] **Step 1: Write the failing test**

Append to `GebTests/Mathlib/Data/PFunctor/Slice/Functor.lean`:

```lean
-- The subfunctor's object map is the choice-free core `Obj`.
example (Y : Over Bool) :
    wrapperTestSlice.toSliceDomPFunctor.domSubfunctor.toFunctor.obj Y =
      wrapperTestSlice.toSliceDomPFunctor.Obj (ConcreteCategory.hom Y.hom) :=
  rfl

-- The subfunctor's morphism map is the choice-free core `map`.
example {Y Z : Over Bool} (g : Y ⟶ Z) :
    wrapperTestSlice.toSliceDomPFunctor.domSubfunctor.toFunctor.map g =
      ↾(wrapperTestSlice.toSliceDomPFunctor.map (ConcreteCategory.hom g.left)
        (over_hom_comp g)) :=
  rfl
```

These assert agreement with the choice-free core, which is what the
refactor must preserve and what `output_triangle`, `functor_obj`, and
`functor_map` depend on. Do **not** assert
`domSubfunctor.toFunctor = domFunctor`: after Step 3 defines `domFunctor`
as `domSubfunctor.toFunctor` that equation holds by delta-reduction for
any body of `domSubfunctor`, so it cannot fail and guards nothing.

- [ ] **Step 2: Run the test to verify it fails**

Run: `lake build GebTests`

Expected: FAIL:

```text
error: Invalid field `domSubfunctor`: The environment does not contain
`SliceDomPFunctor.domSubfunctor`, so it is not possible to project the
field `domSubfunctor` from an expression
  wrapperTestSlice.toSliceDomPFunctor
of type `SliceDomPFunctor Bool`
```

- [ ] **Step 3: Write the implementation**

In `Geb/Mathlib/Data/PFunctor/Slice/Functor.lean`, replace the existing
two-line import block with these four lines — the two new imports
interleave, they do not append:

```lean
public import Geb.Mathlib.Data.PFunctor.Slice.Basic
public import Geb.Mathlib.Data.PFunctor.Univariate.Functor
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Subfunctor.Basic
```

Replace the `domFunctor` declaration (currently lines 75-85) with:

```lean
/-- The `r`-compatible assignments, as a subfunctor of the underlying
polynomial functor pulled back along the forgetful functor. The `obj`
field is the compatibility predicate; the `map` field is its closure
under the polynomial functor's action, supplied by the core `map`. -/
@[expose] def domSubfunctor {dom : Type uD} (F : SliceDomPFunctor.{uA, uB} dom) :
    Subfunctor (Over.forget dom ⋙ F.toPFunctor.functor.{uA, uB, uD}) where
  obj Y := {x | F.Compatible (ConcreteCategory.hom Y.hom) x.1 x.2}
  map i x hx := (F.map (ConcreteCategory.hom i.left) (over_hom_comp i) ⟨x, hx⟩).2

/-- The functor `Over dom ⥤ Type` restricting the `PFunctor`
interpretation to `r`-compatible assignments: the subfunctor
`domSubfunctor` read as a functor. `Subfunctor.ι` is the inclusion into
the underlying polynomial functor. -/
@[expose] def domFunctor {dom : Type uD} (F : SliceDomPFunctor.{uA, uB} dom) :
    CategoryTheory.Functor (Over dom) (Type (max uA uB uD)) :=
  F.domSubfunctor.toFunctor
```

In the module docstring, make three edits.

**Edit A** — in `## Main definitions`, add above the `domFunctor` entry:

```text
* `SliceDomPFunctor.domSubfunctor` — the compatible assignments as a
  subfunctor of the underlying polynomial functor.
```

**Edit B** — in `## Implementation notes`, replace the sentence
beginning "`domFunctor` reuses the core `obj`/`map`; …" and ending
"… and the composition law by `ext` and `rfl`." with:

```text
`domSubfunctor` is the subfunctor of `Over.forget dom ⋙ PFunctor.functor`
cut out by the compatibility predicate, and `domFunctor` reads it as a
functor, so the functor laws come from `Subfunctor.toFunctor` and
`Subfunctor.ι`
is the inclusion into the underlying polynomial functor. `Over`
structure maps are read through `ConcreteCategory.hom`, the
slice-morphism hypothesis is `SliceDomPFunctor.over_hom_comp` (the
function-level form of `Over.w`), and the subfunctor's closure condition
is the core `map`'s output compatibility. The composite instantiates
`PFunctor.functor` at `v := uD`, written explicitly as
`PFunctor.functor.{uA, uB, uD}`.
```

**Edit C** — in `## References`, add as the first entry (the list is
alphabetical, as in `Slice/Basic.lean`):

```text
* [AltenkirchGhaniHancockMcBrideMorris2015]
```

- [ ] **Step 4: Run the gate**

```bash
lake build
lake test
lake lint
lake lint -- GebTests
bash scripts/lint-imports.sh
```

Expected: all PASS, with `Slice/Functor.lean`'s existing
`output_triangle`, `functor`, `functor_comp_forget`, `functor_obj`, and
`functor_map` unchanged and still compiling — the redefinition is
definitionally equal to the previous one.

- [ ] **Step 5: Commit**

```bash
jj describe -m "refactor(pfunctor): rebuild the slice functor on the univariate wrapper"
jj new
```

---

### Task 6: documentation and roadmap

**Files:**

- Modify: `docs/index.md` (new entry; amend the existing Slice entry at
  lines 68-70)
- Modify: `TODO.md`

**Interfaces:**

- Consumes: everything from Tasks 1-5.
- Produces: no Lean declarations.

- [ ] **Step 1: Add the `docs/index.md` entry**

Insert this entry immediately before the existing
`Geb/Mathlib/Data/PFunctor/Slice/` entry, since the slice development
now depends on it:

```markdown
- `Geb/Mathlib/Data/W/Basic.lean` — the two laws of the W-type fold
  mathlib does not state: the computation rule `WType.elim_mk` and
  uniqueness `WType.elim_unique`. Together with mathlib's `WType.elim`
  they are the initiality of `WType β` among algebras of the polynomial
  endofunctor `X ↦ Σ a, β a → X`, stated concretely. Depends on
  mathlib's `Data/W/Basic.lean` only; no category theory.
- `Geb/Mathlib/Data/PFunctor/Univariate/` — the categorical reading of
  mathlib's univariate `PFunctor`. `Functor.lean` packages the
  interpretation as `PFunctor.functor : Type v ⥤ Type (max v uA uB)`,
  transported from the upstream `Functor` / `LawfulFunctor` instances
  along `ofTypeFunctor`. `W.lean` gives the W-type its algebra
  structure (`wAlgebra`), the algebra morphism into any algebra
  (`wElim`), initiality as `Unique` on the hom-sets (`wUniqueHom`), and
  the structure map as an isomorphism (`wStrIso`); all of it is
  `Classical.choice`-free. `Initial.lean` packages that initiality as
  mathlib's `Limits.IsInitial` (`wIsInitial`) and is listed in
  `GebMeta.classicalAllowedModules`, since
  `Limits.IsInitial.ofUnique` is `Classical.choice`-dependent.
  Consumers wanting a choice-free development use `wUniqueHom`
  directly. Depends on mathlib's `Data/PFunctor/Univariate/Basic.lean`,
  `CategoryTheory/Endofunctor/Algebra.lean`, and
  `Geb/Mathlib/Data/W/Basic.lean`, and mathlib's
  `CategoryTheory/Types/Basic.lean` and
  `CategoryTheory/Limits/Shapes/IsTerminal.lean`.
```

- [ ] **Step 2: Amend the existing Slice entry in `docs/index.md`**

Replace this clause of the `Geb/Mathlib/Data/PFunctor/Slice/` entry.
The block spans `docs/index.md:68-70` in full; its opening fragment
(`` `Classical.choice`-free. ``) closes the preceding `Slice/Basic.lean`
sentence and is reproduced unchanged in the replacement.

```markdown
  `Classical.choice`-free. `Slice/Functor.lean` packages it
  categorically as `domFunctor : Over dom ⥤ Type` (reusing the core
  `obj`/`map`) and, via `Functor.toOver`, `functor : Over dom ⥤ Over cod`;
```

with:

```markdown
  `Classical.choice`-free. `Slice/Functor.lean` packages it
  categorically: `domSubfunctor` cuts the `r`-compatible assignments out
  of the underlying polynomial functor `Over.forget dom ⋙ PFunctor.functor`,
  `domFunctor : Over dom ⥤ Type` reads that subfunctor as a functor, and
  `functor : Over dom ⥤ Over cod` is its `Functor.toOver` lift;
```

- [ ] **Step 3: Amend `TODO.md`'s roadmap-linearity claim**

Replace the first two sentences of the paragraph introducing the
polynomial-functor roadmap:

```markdown
The polynomial-functor roadmap below is a linear sequence of
separate planning–implementation cycles. Each item's full spec
and plan are written only after the prior item's implementation
is complete: the project is too large to fix every earlier
```

with:

```markdown
The polynomial-functor roadmap below is a partial order of
separate planning–implementation cycles. Items with disjoint file
sets that do not depend on one another may be taken in either
order. Each item's full spec and plan are written only after the
items it depends on are implemented: the project is too large to
fix every earlier
```

The remainder of the paragraph ("interface on the first attempt, so
interface corrections …") is unchanged.

- [ ] **Step 4: Remove item 2 and renumber**

Remove roadmap item 2 ("Categorical wrappers for mathlib's `PFunctor`
and `WType`") from `TODO.md`. Renumber the items below it: 3→2, 4→3,
5→4, 6→5. Then correct the six numeric cross-references:

| Line | In item | Current text | Action |
| --- | --- | --- | --- |
| 63-64 | 1 | wraps: "…the universal" / "morphisms (item 5)." | → item 4 |
| 82 | 3 | "wrappers of item 2" | referent removed — see below |
| 84 | 3 | "`WType` initiality of item 2" | referent removed — see below |
| 92 | 4 | "pattern of items 2 and 3" | referent removed — see below |
| 126 | 5 | "specializations (item 1)" | **no change** — item 1 keeps its number |
| 156 | 6 | "W-type (item 3) or M-type (item 4)" | → items 2 and 3 |

Line numbers are pre-edit; re-locate each by its quoted text rather than
by line number after the first edit shifts them.

The three references to the removed item (lines 82, 84, 92) are not a
renumbering: their referent leaves `TODO.md` entirely. Replace them
verbatim. In item 3 (renumbered 2), replace:

```markdown
Characterise the slice and presheaf W-types as the initial objects
of the categories of algebras of their functors, reusing the
`PFunctor` and `WType` wrappers of item 2. Build the presheaf
initiality proof on the slice initiality proof, and the slice
proof on the `WType` initiality of item 2.
```

with:

```markdown
Characterise the slice and presheaf W-types as the initial objects
of the categories of algebras of their functors, reusing the
`PFunctor` and `WType` wrappers described under
`Geb/Mathlib/Data/PFunctor/Univariate/` in `docs/index.md`. Build the
presheaf initiality proof on the slice initiality proof, and the slice
proof on the `WType` initiality established there.
```

In item 4 (renumbered 3), replace:

```markdown
as the terminal coalgebras of their functors. Following the
base-layer-first pattern of items 2 and 3, build a categorical
```

with:

```markdown
as the terminal coalgebras of their functors. Following the
base-layer-first pattern of the `PFunctor` wrappers and item 2,
build a categorical
```

- [ ] **Step 5: Add the two new `TODO.md` items**

The two items go in different places, because only one of them is a
polynomial-functor roadmap item.

**Composition** belongs inside `### Polynomial functors`, as a new
fourth-level (`####`) item appended after the last renumbered item
(which is item 5 after Step 4's renumbering). Insert verbatim:

```markdown
#### 6. Composition and identity of polynomial functors

Establish that the interpretation of mathlib's `PFunctor` carries
`PFunctor.comp` to composition of the corresponding functors, and
supply the identity polynomial functor together with the isomorphism
identifying its interpretation with the identity functor. mathlib
defines `comp`, `comp.mk`, and `comp.get` and states no lemma about
them, so the mutual-inverse laws `comp.get_mk` and `comp.mk_get` are
part of the item.

This is the 1-cell composition of `Cat`, a 2-categorical operation,
not a universal morphism. It is independent of the items above and may
be taken in any order relative to them. Two design points are settled:
the identity polynomial functor is `protected def PFunctor.id`, since
an unprotected `id` shadows `_root_.id` throughout the `PFunctor`
namespace and breaks uses such as `P.map id`; and both isomorphisms
admit an ambient universe beyond the parameters of the functors
involved.
```

**Upstream placement** is not a polynomial-functor roadmap item — it is
a repository-wide question about where categorical wrappers live — so it
goes outside the polynomial-functor section, as a new third-level
(`###`) heading under `## Next up`, placed after the
`Polynomial functors` section and before the
`Complete Theorem 2.4 for IndRec` section. Insert verbatim:

```markdown
### Upstream placement of categorical wrappers

Settle where the categorical wrappers under `Geb/Mathlib/Data/` belong
upstream. No file under mathlib's `Mathlib/Data/` imports
`Mathlib.CategoryTheory.*`; mathlib packages category-theoretic
material under `Mathlib/Algebra/Category/` and
`Mathlib/CategoryTheory/`. In scope is every file under
`Geb/Mathlib/Data/` that directly imports `Mathlib.CategoryTheory.*`
or `Geb.Mathlib.CategoryTheory.*`, the latter because it extracts to
the former: currently `PFunctor/Slice/Functor.lean`,
`PFunctor/Presheaf/Basic.lean`, `PFunctor/Presheaf/Functor.lean`,
`PFunctor/Univariate/Functor.lean`, `PFunctor/Univariate/W.lean`,
`PFunctor/Univariate/Initial.lean`, `PFunctor/IndRec/Basic.lean`, and
`PFunctor/IndRec/Naturality.lean`. Files importing those transitively —
`PFunctor/Presheaf/W.lean`, the rest of the `IndRec` family — follow
whatever placement is settled for them. Scoping the item by that
criterion
rather than by a module list keeps it from being settled
incompletely.
```

- [ ] **Step 6: Regenerate the TOCs and lint**

```bash
doctoc --update-only TODO.md docs/index.md
markdownlint-cli2 'TODO.md' 'docs/index.md'
```

Expected: `doctoc` reports "Everything is OK"; `markdownlint-cli2`
reports 0 issues.

- [ ] **Step 7: Commit**

```bash
jj describe -m "doc(pfunctor): document the univariate wrappers and update the roadmap"
jj new
```

---

### Task 7: remove the transient spec and plan

**Files:**

- Delete: `docs/superpowers/specs/2026-07-21-pfunctor-categorical-wrappers-design.md`
- Delete: `docs/superpowers/plans/2026-07-22-pfunctor-categorical-wrappers.md`

**Interfaces:**

- Consumes: nothing.
- Produces: nothing.

Specs and plans are transient (CONTRIBUTING § Concern shape): they are
removed in the branch's final commits, so they remain reachable in
history but absent from `main`'s working tree.

- [ ] **Step 1: Run the full pre-push checklist**

Run it here to catch anything the per-task gate omits before the final
commit is drafted. It is not the authoritative run: `pre-push.sh`
validates commit subjects over `fork_point(main | @)..@` and lints the
current tree, so it cannot see this task's own commit or the tree with
the spec and plan removed. The user's own run before pushing is
authoritative.

```bash
bash scripts/pre-push.sh
```

Expected: every step green. This is the only run of the full checklist;
it additionally covers `lake exe cache get`, `lake shake`,
`markdownlint-cli2` over the whole tree, `scripts/check-commit-msg.sh`,
the TOC check, and the `scripts/tests/*.sh` suite.

- [ ] **Step 2: Remove both files**

```bash
rm docs/superpowers/specs/2026-07-21-pfunctor-categorical-wrappers-design.md
rm docs/superpowers/plans/2026-07-22-pfunctor-categorical-wrappers.md
```

`jj` snapshots working-copy deletions automatically, so `rm` alone is
the complete idiom. Do not reach for `jj file untrack`: it requires its
paths to be ignored already (via `.gitignore` or `.git/info/exclude`),
and `docs/superpowers/` is tracked, so it would abort.

- [ ] **Step 3: Verify the working tree still builds**

```bash
lake build
lake build GebTests
```

Expected: PASS — no Lean file references either document.

- [ ] **Step 4: Commit**

```bash
jj describe -m "doc(pfunctor): remove the transient spec and plan"
jj new
```

- [ ] **Step 5: Hand off for review**

Do not push. Report the branch state and wait for the user's
line-by-line review; `jj git push` requires their explicit
authorisation (AGENTS.md § No `jj git push` without user line-by-line
review).
