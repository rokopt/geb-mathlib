# Presheaf polynomial functors Implementation Plan

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [Presheaf polynomial functors Implementation Plan](#presheaf-polynomial-functors-implementation-plan)
  - [Global Constraints](#global-constraints)
  - [Verification idioms (used throughout)](#verification-idioms-used-throughout)
  - [File structure](#file-structure)
    - [Task 1: Slice substrate — `PositionOver` / `Position`](#task-1-slice-substrate--positionover--position)
    - [Task 2: Slice substrate — `ShapeOver` / `Shape`](#task-2-slice-substrate--shapeover--shape)
    - [Task 3: Presheaf `Basic.lean` skeleton + dom operations/laws/bundle](#task-3-presheaf-basiclean-skeleton--dom-operationslawsbundle)
    - [Task 4: dom `IsNatural` predicate and `obj`](#task-4-dom-isnatural-predicate-and-obj)
    - [Task 5: dom morphism map and functoriality](#task-5-dom-morphism-map-and-functoriality)
    - [Task 6: full-layer operations/laws/bundle (`PresheafPFunctor`)](#task-6-full-layer-operationslawsbundle-presheafpfunctor)
    - [Task 7: `objPresheaf` — the output presheaf value](#task-7-objpresheaf--the-output-presheaf-value)
    - [Task 8: concrete witness instance + computation](#task-8-concrete-witness-instance--computation)
    - [Task 9: output naturality lemma (`objPresheaf` natural in `Z`)](#task-9-output-naturality-lemma-objpresheaf-natural-in-z)
    - [Task 10: wrapper `domFunctor` + allowlist entry](#task-10-wrapper-domfunctor--allowlist-entry)
    - [Task 11: wrapper `functor` + bridge lemmas](#task-11-wrapper-functor--bridge-lemmas)
    - [Task 12: index files and import wiring](#task-12-index-files-and-import-wiring)
    - [Task 13: docs and TODO](#task-13-docs-and-todo)
    - [Task 14: final gate + remove spec and plan](#task-14-final-gate--remove-spec-and-plan)
  - [Self-Review](#self-review)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task. Steps
> use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build parametric-right-adjoint (presheaf polynomial) functors
`(Iᵒᵖ ⥤ Type) ⥤ (Jᵒᵖ ⥤ Type)` as a restriction of the existing
`SlicePFunctor`, in `Geb/Mathlib/Data/PFunctor/Presheaf/`.

**Architecture:** Each layer is an operations `…Data` structure
(extending the slice substrate), a `Prop`-valued `…Data.IsFunctorial`
structure carrying named law conditions, and a bundle joining them.
Computations (`obj`/`map`/`objPresheaf`) live on the operations layer or
build genuine presheaf values; the constructive core (`Basic.lean`) is
held `Classical.choice`-free by the strict axiom linter, and only the
categorical-functor packaging (`Functor.lean`) is allowlisted.

**Tech Stack:** Lean 4 (toolchain `v4.32.0-rc1`), mathlib (repo pin),
`lake` (build/test/lint), `jj` (VCS, colocated), the `GebMeta`
axiom linter.

## Global Constraints

These apply to every task; copied from the spec
(`docs/superpowers/specs/2026-06-26-presheaf-pfunctor-design.md`) and the
repo rules.

- Toolchain `v4.32.0-rc1`; do not bump it in this branch.
- No `noncomputable`. No `Classical` in `Geb/Mathlib/.../Presheaf/Basic.lean`,
  the slice substrate, or the `GebTests` presheaf modules; the strict
  linter permits only `{propext, Quot.sound}` there. Only
  `Geb.Mathlib.Data.PFunctor.Presheaf.Functor` is added to
  `GebMeta.classicalAllowedModules` and may use `Classical.choice`.
- `sorry` is permitted only between commits as a development placeholder
  (never in a committed declaration); `admit` is never permitted. Prefer
  `_` to expose a hole while developing.
- One declaration at a time: get each compiling (no holes, no `sorry`)
  and axiom-clean before the next.
- Build/test/lint with `lake build`, `lake test`, `lake lint`. Never
  `lake clean`, never `lake env lean`.
- Every `.lean` file: `module` after the copyright block; mandatory
  module docstring (`# Title`, summary, `## Main definitions`,
  `## Implementation notes`, `## References`, `## Tags`); a `/-- … -/`
  docstring on every `def`/`structure`/`instance` and every structure
  field; `@[ext]` on structures where it compiles; no
  development-history in docstrings; lines ≤ 100 cols; 2-space indent;
  Unicode where mathlib uses it; `{u, v}` universe lists carry a space
  after each comma (the style linter is fatal under `warningAsError`).
- Self-prefix `Geb.Mathlib.` appears only in `^import` lines (never in
  namespaces, bodies, or docstrings). `Geb/Mathlib/` files import only
  `Mathlib.*` and `Geb.Mathlib.*`; test files additionally import
  `GebTests.Mathlib.*`. No bare `import Mathlib`.
- Commits via `jj commit -m "<msg>"` (raw mutating `git` is blocked).
  Conventional-commit subject: `<type>(<scope>): <subject>`, imperative
  present, lowercase first letter, no trailing period, ≤ ~72 chars,
  types `feat|fix|doc|style|refactor|test|chore|perf|ci`. End every
  commit message body with:
  `Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>`.
- No push: this plan never pushes; the contributor reviews line-by-line
  and pushes separately.
- Markdown touched (docs/index.md, TODO.md): pass `markdownlint-cli2`
  and run `doctoc --update-only` if a TOC is present.

## Verification idioms (used throughout)

- "Test" in a Lean formalization is a compiling `example`/`#check`
  in the mirrored `GebTests/` module, plus the axiom gate. The
  "write failing test → see it fail → implement → see it pass" cycle
  maps to: add the `example` referencing the not-yet-defined name (build
  fails: unknown identifier) → implement → build passes.
- A `Prop`-valued `def` body (e.g. `IsNatural`, `ReindexId`,
  `ReindexComp`) is a TERM to construct, not a tactic goal to close: the
  risk is that the cast/transport typechecks at all (correct direction
  over `PositionOver`/`tagRestr_comp`). Develop it by writing the term
  with `_` placeholders, building to read the expected types, and
  filling them; the step is done when the `def` ELABORATES.
- Per-declaration axiom check during development: temporarily add
  `#print axioms <Name>` and read it via `lake build` output or the
  Lean LSP; remove before committing (`#`-commands are lint-flagged in
  committed files). The committed gate is `lake lint`, which fails if
  any `Geb`/`GebTests` declaration depends on an axiom outside its
  permitted set.
- Build a single module fast with
  `lake build Geb.Mathlib.Data.PFunctor.Presheaf.Basic` (and the
  `GebTests.…` module for tests). Run the whole test library with
  `lake test`; the linter with `lake lint` and `lake lint -- GebTests`.

## File structure

Create:

- `Geb/Mathlib/Data/PFunctor/Presheaf/Basic.lean` — constructive core:
  the operations/laws/bundle structures for both layers, the named
  fibre predicates' consumers, `IsNatural`/`obj`/`map`, `objPresheaf`.
- `Geb/Mathlib/Data/PFunctor/Presheaf/Functor.lean` — categorical
  wrapper: `domFunctor`, `functor`, bridge lemmas.
- `Geb/Mathlib/Data/PFunctor/Presheaf.lean` — directory index.
- `GebTests/Mathlib/Data/PFunctor/Presheaf/Basic.lean`,
  `GebTests/Mathlib/Data/PFunctor/Presheaf/Functor.lean`,
  `GebTests/Mathlib/Data/PFunctor/Presheaf.lean` — mirrored tests +
  index.

Modify:

- `Geb/Mathlib/Data/PFunctor/Slice/Basic.lean` — add the fibre
  predicates/types `PositionOver`/`Position`, `ShapeOver`/`Shape`.
- `GebTests/Mathlib/Data/PFunctor/Slice/Basic.lean` — add `example`s.
- `Geb/Mathlib/Data/PFunctor.lean` — `public import` the Presheaf index.
- `GebTests/Mathlib/Data/PFunctor.lean` — `import` the Presheaf test
  index.
- `GebMeta.lean` — append
  `Geb.Mathlib.Data.PFunctor.Presheaf.Functor` to
  `classicalAllowedModules` (line 47-49 region).
- `docs/index.md` — add an entry under "Implemented content".
- `TODO.md` — remove the "Extend slice polynomial functors to presheaf
  categories" "Next up" entry; record the deferred follow-ons.

The branch already carries the spec-and-plan commit first (per
`CONTRIBUTING.md` § Concern shape, phase 1: the commits adding the spec
and plan). Implementation commits land on top; the final task removes
the spec and plan.

---

### Task 1: Slice substrate — `PositionOver` / `Position`

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/Slice/Basic.lean` (add after
  `sCurried`, before `Compatible`).
- Test: `GebTests/Mathlib/Data/PFunctor/Slice/Basic.lean`.

**Interfaces:**

- Consumes: `SliceDomPFunctor`, `SliceDomPFunctor.sCurried` (existing).
- Produces:
  - `SliceDomPFunctor.PositionOver {dom} (F : SliceDomPFunctor.{uA, uB} dom)
    (a : F.A) (i : dom) : F.B a → Prop`
  - `SliceDomPFunctor.Position {dom} (F : SliceDomPFunctor.{uA, uB} dom)
    (a : F.A) (i : dom) : Type uB`

- [ ] **Step 1: Add the failing test** in the `GebTests` slice module
  (inside its `open SliceDomPFunctor` scope):

```lean
-- Position is the constraint-leg fibre; the predicate is its membership.
example (F : SliceDomPFunctor.{0, 0} Bool) (a : F.A) (i : Bool) :
    F.Position a i = { b : F.B a // F.s ⟨a, b⟩ = i } := rfl
example (F : SliceDomPFunctor.{0, 0} Bool) (a : F.A) (i : Bool) (b : F.B a) :
    F.PositionOver a i b ↔ F.s ⟨a, b⟩ = i := Iff.rfl
```

- [ ] **Step 2: Build to verify it fails.**
  Run: `lake build GebTests.Mathlib.Data.PFunctor.Slice.Basic`
  Expected: FAIL — `unknown identifier 'SliceDomPFunctor.Position'`.

- [ ] **Step 3: Implement** in `Slice/Basic.lean` (inside
  `namespace SliceDomPFunctor`, `public section`):

```lean
/-- The constraint-leg condition on a position of shape `a`: that its
image under `sCurried a` is `i`. Point-free as `(· = i) ∘ sCurried a`. -/
@[expose] def PositionOver {dom : Type uD} (F : SliceDomPFunctor.{uA, uB} dom)
    (a : F.A) (i : dom) : F.B a → Prop :=
  (· = i) ∘ F.sCurried a

/-- The positions of shape `a` lying over the base point `i`: the fibre
of `sCurried a` over `i`, the object-map of shape `a`'s arity presheaf. -/
@[expose] def Position {dom : Type uD} (F : SliceDomPFunctor.{uA, uB} dom)
    (a : F.A) (i : dom) : Type uB :=
  Subtype (F.PositionOver a i)
```

- [ ] **Step 4: Build to verify the test passes.**
  Run: `lake build GebTests.Mathlib.Data.PFunctor.Slice.Basic`
  Expected: PASS.

- [ ] **Step 5: Axiom + lint gate.**
  Run: `lake lint` (Slice.Basic is not allowlisted, so a green run
  certifies `{propext, Quot.sound}` only). Optionally
  `#print axioms SliceDomPFunctor.Position`; remove the `#print` before
  committing.

- [ ] **Step 6: Commit.**

```bash
jj commit -m "feat(slice): add the constraint-leg fibre Position and PositionOver

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

### Task 2: Slice substrate — `ShapeOver` / `Shape`

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/Slice/Basic.lean` (in
  `namespace SlicePFunctor`).
- Test: `GebTests/Mathlib/Data/PFunctor/Slice/Basic.lean`.

**Interfaces:**

- Consumes: `SlicePFunctor`, its `t` field.
- Produces:
  - `SlicePFunctor.ShapeOver {dom cod} (F : SlicePFunctor.{uA, uB, uD, uC} dom cod)
    (j : cod) : F.A → Prop`
  - `SlicePFunctor.Shape {dom cod} (F) (j : cod) : Type uA`

- [ ] **Step 1: Add the failing test** in the `GebTests` slice module
  (it already `open`s `SlicePFunctor`):

```lean
example (F : SlicePFunctor.{0, 0} Bool Unit) (j : Unit) :
    F.Shape j = { a : F.A // F.t a = j } := rfl
example (F : SlicePFunctor.{0, 0} Bool Unit) (j : Unit) (a : F.A) :
    F.ShapeOver j a ↔ F.t a = j := Iff.rfl
```

- [ ] **Step 2: Build to verify it fails.**
  Run: `lake build GebTests.Mathlib.Data.PFunctor.Slice.Basic`
  Expected: FAIL — `unknown identifier 'SlicePFunctor.Shape'`.

- [ ] **Step 3: Implement** in `Slice/Basic.lean`
  (`namespace SlicePFunctor`):

```lean
/-- The tag-leg condition on a shape: that its image under `t` is `j`.
Point-free as `(· = j) ∘ t`. -/
@[expose] def ShapeOver {dom : Type uD} {cod : Type uC}
    (F : SlicePFunctor.{uA, uB, uD, uC} dom cod) (j : cod) : F.A → Prop :=
  (· = j) ∘ F.t

/-- The shapes lying over `j`: the fibre of `t` over `j`, the object-map
of the shape presheaf `T1`. -/
@[expose] def Shape {dom : Type uD} {cod : Type uC}
    (F : SlicePFunctor.{uA, uB, uD, uC} dom cod) (j : cod) : Type uA :=
  Subtype (F.ShapeOver j)
```

- [ ] **Step 4: Build to verify the test passes.**
  Run: `lake build GebTests.Mathlib.Data.PFunctor.Slice.Basic`
  Expected: PASS.

- [ ] **Step 5: Lint gate.** `lake lint` green.

- [ ] **Step 6: Commit.**

```bash
jj commit -m "feat(slice): add the tag-leg fibre Shape and ShapeOver

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

### Task 3: Presheaf `Basic.lean` skeleton + dom operations/laws/bundle

**Files:**

- Create: `Geb/Mathlib/Data/PFunctor/Presheaf/Basic.lean`.
- Test: `GebTests/Mathlib/Data/PFunctor/Presheaf/Basic.lean` (create).

**Interfaces:**

- Consumes: `SliceDomPFunctor`, `SliceDomPFunctor.Position`,
  `CategoryTheory.Category`, `𝟙`/`≫` on `I`.
- Produces:
  - `PresheafDomPFunctorData (I) [Category I]` with field `restr`.
  - `PresheafDomPFunctorData.RestrId (F) : Prop`,
    `PresheafDomPFunctorData.RestrComp (F) : Prop`.
  - `PresheafDomPFunctorData.IsFunctorial (F) : Prop` with fields
    `restr_id : F.RestrId`, `restr_comp : F.RestrComp`.
  - `PresheafDomPFunctor (I) [Category I]` with `isFunctorial`.

- [ ] **Step 1: Create the file** with copyright, `module`, imports, and
  the module docstring. `Basic.lean` needs the category-theory notation
  (`⥤`, `ᵒᵖ`, `NatTrans`, and the bundled `Type`-hom machinery
  `↾`/`ConcreteCategory.hom` that `objPresheaf.map` uses in Task 7), so
  more than `Category.Basic`. Start with:

```lean
module

public import Geb.Mathlib.Data.PFunctor.Slice.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
```

  (The bare names `Mathlib.CategoryTheory.Opposite` and
  `Mathlib.CategoryTheory.Types` do NOT resolve — the correct names are
  `Opposites` and `Types.Basic`.) After the later tasks add notation, run
  `lake build` then
  `lake shake --add-public --keep-implied --keep-prefix Geb GebTests` to
  settle the minimal import set; if any notation is missing,
  `Mathlib.CategoryTheory.Comma.Over.Basic` is a proven superset (the
  import `Slice/Functor.lean` uses). Module docstring records: the p.r.a.
  construction as a restriction of `SlicePFunctor`; the
  operations/laws/bundle split; the option-(A) fibre encoding;
  `## References` (Weber 2007; nlab parametric right adjoint;
  Gambino–Hyland; Kock); `## Tags`. Add
  `set_option linter.checkUnivs false in` + `@[nolint checkUnivs]` on the
  structures, mirroring `Slice/Basic.lean`.

- [ ] **Step 2: Add the failing test** in the new `GebTests` Presheaf
  module (create it: copyright/`module`/`import
  Geb.Mathlib.Data.PFunctor.Presheaf.Basic` /
  `set_option linter.privateModule false`, and `open CategoryTheory
  PresheafDomPFunctorData`):

```lean
-- A caller can name the law condition to state things of that type.
example {I : Type} [Category I] (F : PresheafDomPFunctor I) : F.RestrComp :=
  F.isFunctorial.restr_comp
```

  Build the test module; Expected: FAIL (unknown identifiers).

- [ ] **Step 3: Implement** the operations, named laws, `IsFunctorial`,
  and bundle. (Elaboration and `mk`-axiom-freeness are intended;
  confirmed by this task's build + the Step-5 axiom gate.)

```lean
/-- Operations of a presheaf-domain polynomial functor over `I`: a
`SliceDomPFunctor` on `I`'s objects, with the contravariant `I`-action
`restr` making each arity a presheaf on `I`. -/
@[nolint checkUnivs]
structure PresheafDomPFunctorData (I : Type uI) [Category I] : Type _
    extends SliceDomPFunctor.{uA, uB} I where
  /-- The arity-presheaf restriction: for `f : i' ⟶ i`, reindex
  positions of shape `a` over `i` to positions over `i'`. -/
  restr : ∀ (a : toPFunctor.A) ⦃i i' : I⦄ (f : i' ⟶ i),
      toSliceDomPFunctor.Position a i → toSliceDomPFunctor.Position a i'

namespace PresheafDomPFunctorData

/-- `restr` preserves identities. -/
def RestrId {I : Type uI} [Category I] (F : PresheafDomPFunctorData I) : Prop :=
  ∀ (a : F.A) (i : I), F.restr a (𝟙 i) = id

/-- `restr` is contravariant in `I`. -/
def RestrComp {I : Type uI} [Category I] (F : PresheafDomPFunctorData I) : Prop :=
  ∀ (a : F.A) ⦃i i' i'' : I⦄ (f : i' ⟶ i) (g : i'' ⟶ i'),
      F.restr a (g ≫ f) = F.restr a g ∘ F.restr a f

/-- The arities form presheaves on `I`: `restr` satisfies the functor
laws. -/
structure IsFunctorial {I : Type uI} [Category I]
    (F : PresheafDomPFunctorData I) : Prop where
  /-- Identity law for `restr`. -/
  restr_id : F.RestrId
  /-- Composition law for `restr`. -/
  restr_comp : F.RestrComp

end PresheafDomPFunctorData

/-- A presheaf-domain polynomial functor: operations together with a
proof they are functorial. Its action is a functor `(Iᵒᵖ ⥤ Type) ⥤ Type`
(packaged in `Presheaf.Functor`). -/
@[nolint checkUnivs]
structure PresheafDomPFunctor (I : Type uI) [Category I] : Type _
    extends PresheafDomPFunctorData I where
  /-- Proof the operations are functorial. -/
  isFunctorial : toPresheafDomPFunctorData.IsFunctorial
```

  Notes: `extends SliceDomPFunctor.{uA, uB} I` pins the parent universes
  (load-bearing for the Task-6 diamond; § "Pin parent universes").
  Add `attribute [ext] PresheafDomPFunctorData PresheafDomPFunctor`
  where `ext` compiles. Replace `Type _` with the flat `Type (max …)`
  the elaborator reports if `_` does not elaborate cleanly.

- [ ] **Step 4: Build both modules to verify the test passes.**
  Run: `lake build Geb.Mathlib.Data.PFunctor.Presheaf.Basic
  GebTests.Mathlib.Data.PFunctor.Presheaf.Basic`
  Expected: PASS.

- [ ] **Step 5: Axiom + lint gate.** `lake lint` green;
  `#print axioms PresheafDomPFunctor.mk` ⇒ no axioms (spot check, then
  remove the `#print`).

- [ ] **Step 6: Commit.**

```bash
jj commit -m "feat(presheaf): add PresheafDomPFunctor operations, laws, bundle

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

### Task 4: dom `IsNatural` predicate and `obj`

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/Presheaf/Basic.lean`.
- Test: `GebTests/Mathlib/Data/PFunctor/Presheaf/Basic.lean`.

**Interfaces:**

- Consumes: `PresheafDomPFunctorData`, `SliceDomPFunctor.obj`,
  `SliceDomPFunctor.Compatible`, a presheaf `Z : Iᵒᵖ ⥤ Type` (via
  `Z.obj`/`Z.map`), `Opposite.op`.
- Produces:
  - `PresheafDomPFunctorData.pZ {I} [Category I] (Z : Iᵒᵖ ⥤ Type) :
    (Σ i, Z.obj ⟨i⟩) → I` (`Sigma.fst`).
  - `PresheafDomPFunctorData.IsNatural (F) {Z} (x) : Prop`.
  - `PresheafDomPFunctorData.obj (F) (Z : Iᵒᵖ ⥤ Type) : Type _`.

- [ ] **Step 1: Add the failing test:**

```lean
example {I : Type} [Category I] (F : PresheafDomPFunctor I) (Z : Iᵒᵖ ⥤ Type) :
    F.obj Z = { x : F.toSliceDomPFunctor.obj (PresheafDomPFunctorData.pZ Z)
      // F.IsNatural x } := rfl
```

  Build ⇒ FAIL on `F.obj`.

- [ ] **Step 2: Construct `IsNatural` as a term** (definition-construction
  step: the risk is that the fibre cast over `PositionOver` typechecks).
  `x = ⟨⟨a, v⟩, hx⟩` with `v : F.B a → Σ i, Z.obj ⟨i⟩`; `hx : Compatible`
  forces `(v b).1 = s ⟨a, b⟩`, so the component `(v b).2 : Z.obj ⟨(v b).1⟩`
  casts to `Z.obj ⟨i⟩`. The condition: for `⦃i i'⦄ (f : i' ⟶ i)`
  `(b : F.Position a i)`, `comp (F.restr a f b) = Z.map f.op (comp b)`,
  where `comp` is the cast component. Use only `Z.map` and `restr`.

```lean
/-- Total-space projection of a presheaf `Z` on `I` to objects of `I`. -/
@[expose] def pZ {I : Type uI} [Category I] (Z : Iᵒᵖ ⥤ Type uZ) :
    (Σ i : I, Z.obj ⟨i⟩) → I := Sigma.fst

/-- The position-assignment of `x` is a natural transformation
`E_T(a) ⟶ Z`: it commutes with `restr` and `Z.map`. -/
@[expose] def IsNatural {I : Type uI} [Category I] (F : PresheafDomPFunctorData I)
    {Z : Iᵒᵖ ⥤ Type uZ} (x : F.toSliceDomPFunctor.obj (pZ Z)) : Prop :=
  _   -- the commuting condition above; a TERM to construct, not a goal

/-- The value of the presheaf-domain functor on `Z`: the `IsNatural`
subtype of the slice object. -/
@[expose] def obj {I : Type uI} [Category I] (F : PresheafDomPFunctorData I)
    (Z : Iᵒᵖ ⥤ Type uZ) : Type _ :=
  { x : F.toSliceDomPFunctor.obj (pZ Z) // F.IsNatural x }
```

- [ ] **Step 3: Build to verify the test passes** and `IsNatural` has no
  remaining `_`. Run `lake build` of both modules. Expected: PASS.

- [ ] **Step 4: Lint gate.** `lake lint` green; spot-check
  `#print axioms PresheafDomPFunctorData.obj` ⇒ `{propext, Quot.sound}`.

- [ ] **Step 5: Commit.**

```bash
jj commit -m "feat(presheaf): add the dom naturality predicate and obj

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

### Task 5: dom morphism map and functoriality

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/Presheaf/Basic.lean`.
- Test: `GebTests/Mathlib/Data/PFunctor/Presheaf/Basic.lean`.

**Interfaces:**

- Consumes: `PresheafDomPFunctorData.obj`, `SliceDomPFunctor.map`,
  `SliceDomPFunctor.map_id`/`map_comp`/`map_fst`,
  `CategoryTheory.NatTrans` (bare structure), `α.app`, `α.naturality`.
- Produces:
  - `PresheafDomPFunctorData.map (F) {Z Z'} (α : NatTrans Z Z') :
    F.obj Z → F.obj Z'`.
  - `PresheafDomPFunctorData.map_id`, `PresheafDomPFunctorData.map_comp`.

- [ ] **Step 1: Add the failing test.** Do NOT use `NatTrans.id` (it
  carries `Classical.choice`); reference `map` against a hand-built
  identity transformation:

```lean
example {I : Type} [Category I] (F : PresheafDomPFunctor I) (Z : Iᵒᵖ ⥤ Type) :
    F.map { app := fun _ => id, naturality := fun _ _ _ => rfl } =
      (id : F.obj Z → F.obj Z) := F.map_id Z
```

  Build ⇒ FAIL on `F.map`.

- [ ] **Step 2: Implement `map`.** From `α : NatTrans Z Z'` build
  `f_α := fun p => ⟨p.1, α.app ⟨p.1⟩ p.2⟩` with `pZ Z' ∘ f_α = pZ Z`
  (`rfl`), apply `SliceDomPFunctor.map f_α rfl`, restrict to the
  `IsNatural` subtype. Preservation of `IsNatural` uses `α.naturality`
  via the RAW projection — `congrArg (ConcreteCategory.hom ·) (α.naturality f)`
  — NOT `NatTrans.naturality_apply` (it carries `Classical.choice`).

```lean
/-- Action on a morphism of input presheaves (the bare `NatTrans`, not
the functor-category hom, to stay choice-free). -/
@[expose] def map {I : Type uI} [Category I] (F : PresheafDomPFunctorData I)
    {Z Z' : Iᵒᵖ ⥤ Type uZ} (α : CategoryTheory.NatTrans Z Z') :
    F.obj Z → F.obj Z' :=
  fun x => ⟨F.toSliceDomPFunctor.map (fun p => ⟨p.1, α.app ⟨p.1⟩ p.2⟩) rfl x.1, _⟩
```

- [ ] **Step 3: Implement `map_id`/`map_comp`.** State against a
  hand-built identity (`app i := 𝟙 (Z.obj i)`) and a hand-built vertical
  composite (`app i := α.app i ≫ β.app i`, naturality from
  `Category.assoc` + raw `.naturality`) — never `NatTrans.id` /
  `NatTrans.vcomp`. Reduce to `SliceDomPFunctor.map_id` /
  `SliceDomPFunctor.map_comp` plus `Subtype.ext`. No `restr` law needed.

- [ ] **Step 4: Build to verify the test passes.** Build both modules;
  Expected: PASS.

- [ ] **Step 5: Lint gate.** `lake lint` green; spot-check
  `#print axioms PresheafDomPFunctorData.map` ⇒ `{propext, Quot.sound}`.

- [ ] **Step 6: Commit.**

```bash
jj commit -m "feat(presheaf): add the dom morphism map and functoriality

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

### Task 6: full-layer operations/laws/bundle (`PresheafPFunctor`)

> **Verification unit (read before T6/T7/T8):** the `J`-side law set is
> validated only when `objPresheaf.map_comp` (Task 7) discharges and the
> concrete witness (Task 8) inhabits it over a non-identity `J`-morphism.
> If a law cannot be discharged, REVISE the `IsFunctorial` field set here
> (same branch) — add/alter a coherence field — and re-run T6→T8. Treat
> T6+T7+T8 as one verification unit even though each commits separately.

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/Presheaf/Basic.lean`.
- Test: `GebTests/Mathlib/Data/PFunctor/Presheaf/Basic.lean`.

**Interfaces:**

- Consumes: `PresheafDomPFunctorData`, `SlicePFunctor`,
  `SlicePFunctor.Shape`, `SliceDomPFunctor.Position`, `Category J`.
- Produces:
  - `PresheafPFunctorData (I) [Category I] (J) [Category J]`, the diamond
    `extends PresheafDomPFunctorData.{uA, uB} I, SlicePFunctor.{uA, uB} I J`,
    fields `tagRestr`, `reindex`.
  - Named laws `TagRestrId`, `TagRestrComp`, `ReindexNaturality`,
    `ReindexId`, `ReindexComp` (all `(F) : Prop`).
  - `PresheafPFunctorData.IsFunctorial (F) : Prop
    extends F.toPresheafDomPFunctorData.IsFunctorial`.
  - `PresheafPFunctor (I) [Category I] (J) [Category J]` with
    `isFunctorial`.

- [ ] **Step 1: Add the failing test** (inherited dom law projects from
  the full bundle, and a J-law is named):

```lean
example {I J : Type} [Category I] [Category J] (F : PresheafPFunctor I J) :
    F.RestrComp := F.isFunctorial.restr_comp
example {I J : Type} [Category I] [Category J] (F : PresheafPFunctor I J) :
    F.TagRestrComp := F.isFunctorial.tagRestr_comp
```

  Build ⇒ FAIL.

- [ ] **Step 2: Implement the operations diamond:**

```lean
/-- Operations of a presheaf polynomial functor `(Iᵒᵖ ⥤ Type) → (Jᵒᵖ ⥤ Type)`:
the dom operations plus the tag leg `t` (via `SlicePFunctor`), the
`J`-action `tagRestr` on shapes, and the arity reindexing `reindex`. -/
@[nolint checkUnivs]
structure PresheafPFunctorData (I : Type uI) [Category I]
    (J : Type uJ) [Category J] : Type _
    extends PresheafDomPFunctorData.{uA, uB} I, SlicePFunctor.{uA, uB} I J where
  /-- The shape-presheaf restriction: for `g : j' ⟶ j`, reindex shapes
  over `j` to shapes over `j'`. -/
  tagRestr : ∀ ⦃j j' : J⦄ (g : j' ⟶ j),
      toSlicePFunctor.Shape j → toSlicePFunctor.Shape j'
  /-- The arity reindexing along a `J`-morphism: a presheaf morphism
  `E_T(tagRestr g a) ⟶ E_T(a)`. -/
  reindex : ∀ ⦃j j' : J⦄ (g : j' ⟶ j) (a : toSlicePFunctor.Shape j) ⦃i : I⦄,
      toSliceDomPFunctor.Position (tagRestr g a).1 i →
        toSliceDomPFunctor.Position a.1 i
```

- [ ] **Step 3: Construct the named J-laws as terms.** `TagRestrId` /
  `TagRestrComp` / `ReindexNaturality` are plain `∀`-equations;
  `ReindexId` / `ReindexComp` are definition-construction steps carrying
  transports (build to read the expected type, fill the `Eq.mpr`/`▸`).
  Exact statements:

```lean
namespace PresheafPFunctorData

/-- `tagRestr` preserves identities. -/
def TagRestrId … : Prop := ∀ (j : J), F.tagRestr (𝟙 j) = id
/-- `tagRestr` is contravariant in `J`. -/
def TagRestrComp … : Prop :=
  ∀ ⦃j j' j'' : J⦄ (g : j' ⟶ j) (h : j'' ⟶ j'),
      F.tagRestr (h ≫ g) = F.tagRestr h ∘ F.tagRestr g
/-- Each `reindex g a` commutes with `restr` (a presheaf morphism
`E_T(tagRestr g a) ⟶ E_T(a)`): for `f : i' ⟶ i`,
  restr a.1 f ∘ reindex g a = reindex g a ∘ restr (tagRestr g a).1 f.
Ordinary fibre casts only; NO tagRestr transport. -/
def ReindexNaturality … : Prop :=
  ∀ ⦃j j' : J⦄ (g : j' ⟶ j) (a : F.Shape j) ⦃i i' : I⦄ (f : i' ⟶ i),
    F.restr a.1 f ∘ F.reindex g a = F.reindex g a ∘ F.restr (F.tagRestr g a).1 f
/-- `reindex (𝟙 j) a` is the identity, modulo the `Eq.mpr`/`▸` transport
on its source over `TagRestrId` at `j` (`tagRestr (𝟙 j) a = a`). -/
def ReindexId … : Prop := _
/-- For `g : j' ⟶ j`, `h : j'' ⟶ j'`:
  reindex (h ≫ g) a = reindex g a ∘ reindex h (tagRestr g a)
(outer factor the `g` leg), source transported by `Eq.mpr`/`▸` over
`TagRestrComp` (`tagRestr (h ≫ g) a = tagRestr h (tagRestr g a)`). -/
def ReindexComp … : Prop := _

end PresheafPFunctorData
```

  Then `IsFunctorial` (extends dom's) and the bundle:

```lean
/-- All functor laws: the dom laws plus the `J`-side laws making `T1` a
presheaf and `E_T` a functor on `el(T1)`. -/
structure PresheafPFunctorData.IsFunctorial {I : Type uI} [Category I]
    {J : Type uJ} [Category J] (F : PresheafPFunctorData I J) : Prop
    extends F.toPresheafDomPFunctorData.IsFunctorial where
  /-- Identity law for `tagRestr`. -/
  tagRestr_id : F.TagRestrId
  /-- Composition law for `tagRestr`. -/
  tagRestr_comp : F.TagRestrComp
  /-- `reindex` is a presheaf morphism (commutes with `restr`). -/
  reindex_naturality : F.ReindexNaturality
  /-- Identity law for `reindex`. -/
  reindex_id : F.ReindexId
  /-- Composition law for `reindex`. -/
  reindex_comp : F.ReindexComp

/-- A presheaf polynomial functor: operations together with a proof they
are functorial. Its action is a functor `(Iᵒᵖ ⥤ Type) ⥤ (Jᵒᵖ ⥤ Type)`. -/
@[nolint checkUnivs]
structure PresheafPFunctor (I : Type uI) [Category I]
    (J : Type uJ) [Category J] : Type _
    extends PresheafPFunctorData I J where
  /-- Proof the operations are functorial. -/
  isFunctorial : toPresheafPFunctorData.IsFunctorial
```

  Add `attribute [ext] PresheafPFunctorData PresheafPFunctorData.IsFunctorial
  PresheafPFunctor` where `ext` compiles.

- [ ] **Step 4: Build both modules to verify the tests pass.** Expected:
  PASS (inherited `restr_comp` and new `tagRestr_comp` both project).

- [ ] **Step 5: Lint gate.** `lake lint` green; spot-check
  `#print axioms PresheafPFunctor.mk` ⇒ no axioms.

- [ ] **Step 6: Commit.**

```bash
jj commit -m "feat(presheaf): add PresheafPFunctor operations, named laws, bundle

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

### Task 7: `objPresheaf` — the output presheaf value

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/Presheaf/Basic.lean`.
- Test: `GebTests/Mathlib/Data/PFunctor/Presheaf/Basic.lean`.

**Interfaces:**

- Consumes: `PresheafPFunctor` (bundle — needs the laws),
  `PresheafDomPFunctorData.obj`, `reindex`, `tagRestr`, the
  `isFunctorial` laws; `Jᵒᵖ ⥤ Type` as the output type.
- Produces:
  - `PresheafPFunctor.objPresheaf (F) (Z : Iᵒᵖ ⥤ Type) : Jᵒᵖ ⥤ Type`.

- [ ] **Step 1: Add the failing test** — the fibre over `j` is the
  `t`-tagged subtype of the dom `obj`:

```lean
example {I J : Type} [Category I] [Category J] (F : PresheafPFunctor I J)
    (Z : Iᵒᵖ ⥤ Type) (j : J) :
    (F.objPresheaf Z).obj ⟨j⟩ =
      { z : F.toPresheafDomPFunctorData.obj Z // F.t z.1.1.1 = j } := rfl
```

  (`z.1 : SliceDomPFunctor.obj`, `z.1.1 : PFunctor.Obj`, `z.1.1.1 : A`;
  confirm the depth against the concrete `obj`.) Build ⇒ FAIL.

- [ ] **Step 2: Implement `objPresheaf`** as a genuine `Jᵒᵖ ⥤ Type`
  VALUE with EXPLICIT `map_id`/`map_comp` (building a presheaf value is
  choice-free; constructing a categorical FUNCTOR between presheaf
  categories is NOT — that is Task 11). The `map` field is a hom in the
  `Type` category, BUNDLED in this pin: produce it with `↾`
  (`ConcreteCategory.ofHom`), not a raw function, and prove the laws with
  `ext`, not `funext` (mirror `Slice/Functor.lean`'s idioms).

```lean
/-- The output presheaf `T(Z) : Jᵒᵖ ⥤ Type`, built directly (a presheaf
value is `Classical.choice`-free). Its lawfulness is mathlib `Functor`'s
`map_id`/`map_comp`, discharged from `F.isFunctorial`. -/
@[expose] def objPresheaf {I : Type uI} [Category I] {J : Type uJ} [Category J]
    (F : PresheafPFunctor I J) (Z : Iᵒᵖ ⥤ Type uZ) : Jᵒᵖ ⥤ Type _ where
  obj j := { z : F.toPresheafDomPFunctorData.obj Z // F.t z.1.1.1 = j.unop }
  map g := _   -- ↾ of reindex-precomposition, retag via tagRestr g
  map_id j := _   -- from tagRestr_id, reindex_id (consumes the transport)
  map_comp g h := _   -- from tagRestr_comp, reindex_comp (consumes the transport)
```

  This is the single hardest task; budget for iterative development. If
  `map_comp` cannot be discharged from `reindex_comp`/`tagRestr_comp` as
  stated, the Task-6 `IsFunctorial` field set is wrong — revise it there
  (same branch) and re-run, per the T6/T7/T8 verification-unit note.
  `#print axioms` MUST stay within `{propext, Quot.sound}`; if a `simp`
  pulls a tainted `_apply` lemma, replace it with the raw projection form.

- [ ] **Step 3: Build to verify the test passes** and the file is hole-
  free.

- [ ] **Step 4: Axiom gate (critical).** `lake lint` green;
  `#print axioms PresheafPFunctor.objPresheaf` ⇒ `{propext, Quot.sound}`
  exactly. If `Classical.choice` appears, the build of `Basic.lean`
  itself fails `lake lint` (module not allowlisted) — fix before
  committing.

- [ ] **Step 5: Commit.**

```bash
jj commit -m "feat(presheaf): build the output presheaf objPresheaf in the core

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

### Task 8: concrete witness instance + computation

**Files:**

- Modify: `GebTests/Mathlib/Data/PFunctor/Presheaf/Basic.lean`.

**Interfaces:**

- Consumes: `PresheafPFunctor`, `objPresheaf`, dom `obj`/`map`, all five
  `J`-laws (via `isFunctorial`).
- Produces: `presheafWitness : PresheafPFunctor C C` (or `C D`) over a
  small category with a non-identity morphism; computational `example`s.

Rationale (do not skip): the abstract tests in Tasks 1-7 typecheck even
if a law's `_`-hole statement is malformed — `F.isFunctorial.reindex_comp`
is a field projection regardless of whether `ReindexComp`'s STATEMENT is
the intended one. Only a concrete instance discharging the laws over a
NON-identity `J`-morphism validates the law set is inhabitable and
correctly stated (and discharges the spec's "Computes; no `Classical`"
requirement). Mirrors the slice precedent (`testSlice`/`taggedSlice`).

- [ ] **Step 1: Pick a minimal category with a non-identity morphism.**
  Recommended: a `Preorder`-derived category — `Fin 2` (or `Bool`) with
  its order, where mathlib's preorder→category instance gives a
  non-identity `(0 : Fin 2) ⟶ 1` from `homOfLE (by decide)`. Use it for
  both `I` and `J` so `restr` AND `tagRestr`/`reindex` are exercised. The
  `Fin 2` preorder category needs two imports in the `GebTests` presheaf
  test module: `import Mathlib.CategoryTheory.Category.Preorder` (the
  `Preorder → Category` instance) and `import Mathlib.Order.Fin.Basic`
  (`Preorder (Fin 2)`). Confirm:
  `example : ((0 : Fin 2) ⟶ 1) := homOfLE (by decide)` builds.

- [ ] **Step 2: Build the witness.** A minimal `PFunctor` (e.g. one or
  two shapes; `Bool`/`Unit` positions), constraint `s`, tag `t`,
  `restr`/`tagRestr`/`reindex`, and `isFunctorial` discharging all of
  `RestrId`/`RestrComp`/`TagRestrId`/`TagRestrComp`/`ReindexNaturality`/
  `ReindexId`/`ReindexComp`. Choose the data so `reindex` is NOT the
  identity (positions genuinely reindex along the `J`-morphism) — else
  `reindex_comp`'s transport is exercised vacuously (cf. `taggedSlice`'s
  `t := id` choice to avoid collapse). No `Classical`, no `noncomputable`.

```lean
def presheafWitness : PresheafPFunctor (Fin 2) (Fin 2) where
  A := …
  B := …
  s := …
  t := …
  restr := …
  tagRestr := …
  reindex := …
  isFunctorial := { restr_id := …, restr_comp := …, tagRestr_id := …,
    tagRestr_comp := …, reindex_naturality := …, reindex_id := …,
    reindex_comp := … }
```

- [ ] **Step 3: Computational `example`s.** Apply `obj`/`map` and
  `objPresheaf` to a concrete input presheaf on `Fin 2`, asserting
  computed values with `rfl`/`decide` (mirroring
  `example : testSlice.s ⟨(), true⟩ = true := rfl`). Build ⇒ PASS.

- [ ] **Step 4: Axiom gate.** `lake lint -- GebTests` green;
  `#print axioms presheafWitness` ⇒ within `{propext, Quot.sound}` (the
  `GebTests` presheaf module is NOT allowlisted, so a green run certifies
  the witness is `Classical.choice`-free).

- [ ] **Step 5: Commit.**

```bash
jj commit -m "test(presheaf): add a computable witness over a two-object category

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

### Task 9: output naturality lemma (`objPresheaf` natural in `Z`)

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/Presheaf/Basic.lean`.
- Test: `GebTests/Mathlib/Data/PFunctor/Presheaf/Basic.lean`.

**Interfaces:**

- Consumes: `objPresheaf`, dom `map`, `NatTrans`, `SliceDomPFunctor.map_fst`.
- Produces:
  - `PresheafPFunctor.objPresheaf_naturality` (or the `map`-on-`objPresheaf`
    action plus the square): for `α : NatTrans Z Z'`, dom `map α` carries
    `objPresheaf Z`'s fibres to `objPresheaf Z'`'s and commutes with the
    `J`-restriction maps.

- [ ] **Step 1: Add the failing test** asserting the fibrewise action of
  `map α` lands in the right tagged subtype and commutes with the
  `objPresheaf` restriction (equality of functions, by `Subtype.ext`/`ext`).
  Build ⇒ FAIL.

- [ ] **Step 2: Implement** the lemma. `map α` preserves the `t`-tag (the
  shape is fixed, by `SliceDomPFunctor.map_fst`), so it restricts to each
  fibre; commutation with `objPresheaf`'s restriction is associativity of
  precomposition (postcompose-`α` vs precompose-`reindex`), needing no new
  law. Choice-free (raw projections only).

- [ ] **Step 3: Build to verify.** PASS.

- [ ] **Step 4: Lint gate.** `lake lint` green; axiom spot-check
  `{propext, Quot.sound}`.

- [ ] **Step 5: Commit.**

```bash
jj commit -m "feat(presheaf): add objPresheaf naturality in the input presheaf

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

### Task 10: wrapper `domFunctor` + allowlist entry

**Files:**

- Create: `Geb/Mathlib/Data/PFunctor/Presheaf/Functor.lean`.
- Modify: `GebMeta.lean` (append to `classicalAllowedModules`).
- Test: `GebTests/Mathlib/Data/PFunctor/Presheaf/Functor.lean` (create).

**Interfaces:**

- Consumes: `PresheafDomPFunctorData.obj`/`map`/`map_id`/`map_comp`,
  `CategoryTheory.Functor`, the functor-category instance, `↾`/
  `ConcreteCategory.hom` (mirror `Slice/Functor.lean`).
- Produces:
  - `PresheafDomPFunctorData.domFunctor (F) :
    CategoryTheory.Functor (Iᵒᵖ ⥤ Type) (Type _)`.

- [ ] **Step 1: Append the module to the allowlist** in `GebMeta.lean`
  (line 47-49 region), so the wrapper may use `Classical.choice`:

```lean
def classicalAllowedModules : NameSet :=
  ((({} : NameSet).insert `GebTests.Internal.AxiomLinterClassicalFixture).insert
    `Geb.Mathlib.Data.PFunctor.Slice.Functor).insert
    `Geb.Mathlib.Data.PFunctor.Presheaf.Functor
```

  Build the `GebMeta` module to confirm it compiles.

- [ ] **Step 2: Create `Functor.lean`** (copyright, `module`, imports
  `Geb.Mathlib.Data.PFunctor.Presheaf.Basic` and the needed
  `Mathlib.CategoryTheory.*`, module docstring noting the allowlist entry
  and the absence of a `toOver` shortcut). Add the failing test in the
  test module (`example` referencing `domFunctor`); build ⇒ FAIL.

- [ ] **Step 3: Implement `domFunctor`** — obj `F.obj`, map from the core
  `map` (converting the functor-category hom `α : Z ⟶ Z'` to the bare
  `NatTrans`, definitional), laws from `map_id`/`map_comp`, using the
  `↾`/`ConcreteCategory.hom`/`ext` idioms from `Slice/Functor.lean`.

- [ ] **Step 4: Build + lint.** `lake build` both modules; `lake lint`
  green (the wrapper is now allowlisted, so `Classical.choice` is
  permitted there and nothing else is).

- [ ] **Step 5: Commit.**

```bash
jj commit -m "feat(presheaf): package domFunctor and allowlist the wrapper module

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

### Task 11: wrapper `functor` + bridge lemmas

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/Presheaf/Functor.lean`.
- Test: `GebTests/Mathlib/Data/PFunctor/Presheaf/Functor.lean`.

**Interfaces:**

- Consumes: `PresheafPFunctor.objPresheaf`, `domFunctor`, dom `map`,
  `objPresheaf_naturality`.
- Produces:
  - `PresheafPFunctor.functor (F) :
    CategoryTheory.Functor (Iᵒᵖ ⥤ Type) (Jᵒᵖ ⥤ Type)`.
  - `PresheafPFunctor.functor_obj` (`functor.obj Z = objPresheaf Z`,
    `rfl`), `PresheafPFunctor.functor_map`.

- [ ] **Step 1: Add the failing test:**

```lean
example {I J : Type} [Category I] [Category J] (F : PresheafPFunctor I J)
    (Z : Iᵒᵖ ⥤ Type) : F.functor.obj Z = F.objPresheaf Z := F.functor_obj Z
```

  Build ⇒ FAIL.

- [ ] **Step 2: Implement `functor`** as the `CategoryTheory.Functor`
  whose `obj := objPresheaf` and whose `map α` is the dom `map` on the
  converted `NatTrans`, `map_id`/`map_comp` from Task 9's naturality plus
  the dom functoriality. This is the single `Classical.choice`-tainted
  construction (source/target are functor categories); it lives here by
  design. Weigh the two assembly routes from the spec (direct vs
  `CategoryTheory.curry` on a bifunctor `((Iᵒᵖ ⥤ Type) × Jᵒᵖ) ⥤ Type`);
  pick whichever discharges fewer hand-rolled laws.

- [ ] **Step 3: Implement the bridge lemmas** `functor_obj` (`:= rfl`,
  enabled by `@[expose]` on `objPresheaf`) and `functor_map`.

- [ ] **Step 4: Build to verify the test passes.** PASS.

- [ ] **Step 5: Lint gate.** `lake lint` green (allowlisted module).

- [ ] **Step 6: Commit.**

```bash
jj commit -m "feat(presheaf): package the presheaf functor and its core bridges

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

### Task 12: index files and import wiring

**Files:**

- Create: `Geb/Mathlib/Data/PFunctor/Presheaf.lean`,
  `GebTests/Mathlib/Data/PFunctor/Presheaf.lean`.
- Modify: `Geb/Mathlib/Data/PFunctor.lean`,
  `GebTests/Mathlib/Data/PFunctor.lean`.

**Interfaces:**

- Produces: the `Presheaf` directory index and the upward import chain.

- [ ] **Step 1: Create `Geb/Mathlib/Data/PFunctor/Presheaf.lean`**
  (copyright, `module`, module docstring `# Presheaf — index`):

```lean
public import Geb.Mathlib.Data.PFunctor.Presheaf.Basic
public import Geb.Mathlib.Data.PFunctor.Presheaf.Functor
```

- [ ] **Step 2: Create the test index**
  `GebTests/Mathlib/Data/PFunctor/Presheaf.lean`:

```lean
import GebTests.Mathlib.Data.PFunctor.Presheaf.Basic
import GebTests.Mathlib.Data.PFunctor.Presheaf.Functor
```

- [ ] **Step 3: Wire upward.** Add `public import
  Geb.Mathlib.Data.PFunctor.Presheaf` to `Geb/Mathlib/Data/PFunctor.lean`
  and `import GebTests.Mathlib.Data.PFunctor.Presheaf` to the test index.

- [ ] **Step 4: Build the whole library + tests.** Run: `lake build`
  then `lake test`. Expected: PASS.

- [ ] **Step 5: Import-rule + lint gate.** Run
  `scripts/lint-imports.sh`, `lake lint`, `lake lint -- GebTests`,
  `lake shake --add-public --keep-implied --keep-prefix Geb GebTests`.
  Expected: all green (no self-prefix leakage, no unused imports).

- [ ] **Step 6: Commit.**

```bash
jj commit -m "feat(presheaf): wire the Presheaf index into the PFunctor tree

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

### Task 13: docs and TODO

**Files:**

- Modify: `docs/index.md`, `TODO.md`.

- [ ] **Step 1: Add a `docs/index.md` entry** under "Implemented content"
  (mirroring the slice entry's shape), describing
  `Geb/Mathlib/Data/PFunctor/Presheaf/` — the operations/laws/bundle
  layers, `objPresheaf` built choice-free in the core, and the
  allowlisted wrapper.

- [ ] **Step 2: Update `TODO.md`** — remove the "Extend slice polynomial
  functors to presheaf categories" entry under "Next up"; record the
  deferred follow-ons: the natural-isomorphism validation (p.r.a.
  determined by `(T1, E_T)`), slice/presheaf W-types as subtypes of
  `PFunctor.W`, and free monads over cslib's construction.

- [ ] **Step 3: Markdown gate.** Run `markdownlint-cli2 '**/*.md'` and
  `doctoc --update-only docs/index.md TODO.md` (both carry TOCs);
  re-stage. (If `.remember/` flags, re-run
  `scripts/hooks/clean-remember.sh` per CLAUDE.md — do not hand-edit
  logs.) Expected: clean.

- [ ] **Step 4: Commit.**

```bash
jj commit -m "doc(presheaf): record presheaf polynomial functors in the index

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

### Task 14: final gate + remove spec and plan

**Files:**

- Delete: `docs/superpowers/specs/2026-06-26-presheaf-pfunctor-design.md`,
  `docs/superpowers/plans/2026-06-27-presheaf-pfunctor.md`.

- [ ] **Step 1: Run the canonical pre-push checklist.** Run
  `scripts/pre-push.sh` and confirm it is green end-to-end (it runs
  `lake build`, `lake test`, `lake lint`, `lake lint -- GebTests`,
  `lake shake --add-public --keep-implied --keep-prefix Geb GebTests`,
  `scripts/lint-imports.sh`, the `scripts/tests/*` smoke tests,
  `markdownlint-cli2`, and the doctoc dry-run). Fix any failure before
  proceeding; do not hand-curate a subset.

- [ ] **Step 2: Confirm the constructive boundary held.** `lake lint`
  passing with `Presheaf.Basic` and the `GebTests` presheaf modules NOT
  on `classicalAllowedModules` is positive proof the core and witness are
  `Classical.choice`-free; only `Presheaf.Functor` is allowlisted.

- [ ] **Step 3: Run the final-review skills** on the changed files:
  `lean4:review`, `lean4:golf` (golf the new proofs), and
  `pr-review-toolkit:review-pr`. Apply their findings (golfing is
  semantics-preserving; re-run the axiom gate after).

- [ ] **Step 4: Remove the transient spec and plan** (their decisions now
  live in code, docs, and history), per `CONTRIBUTING.md` § Concern
  shape. Delete the two files in the working copy first, then:

```bash
jj commit -m "chore: remove transient presheaf-pfunctor spec and plan

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

- [ ] **Step 5: Hand off for review.** The branch is ready for the
  contributor's line-by-line review before any push. Do not push.

---

## Self-Review

**Spec coverage** (each spec section → task):

- Transcription/novel, Background, Reduction → docstrings +
  `docs/index.md` (Task 13); the math is realized by Tasks 3-11.
- Constructiveness boundary / allowlist → Tasks 3-9 (strict core),
  Task 10 (allowlist entry), Task 14 Steps 1-2 (gate).
- Layer split + "what data each layer adds" → Tasks 3 (dom), 6 (full).
- Fibre predicates `PositionOver`/`Position`, `ShapeOver`/`Shape` →
  Tasks 1, 2.
- Operations/laws/bundle triad + named laws → Tasks 3, 6.
- `IsNatural`/`obj`, dom `map`/functoriality → Tasks 4, 5.
- `objPresheaf` (output presheaf value) + naturality → Tasks 7, 9.
- Concrete witness (spec Verification plan: "a concrete small
  `PresheafPFunctor` … Computes") → Task 8.
- Categorical wrapper (`domFunctor`, `functor`, bridges) → Tasks 10, 11.
- Universe posture (pin parent universes; uniform fallback) → Task 3/6
  notes (`extends …{uA, uB}…`).
- Placement/naming, indices → Task 12; docs/TODO → Task 13.
- Verification plan → Tasks' lint/axiom steps + Task 8 (witness) +
  Task 14 (`scripts/pre-push.sh`).
- Out-of-scope (nat-iso, W-types, free monads) → recorded in Task 13,
  not implemented.

**Placeholder scan:** The `_` holes in Tasks 4, 6, 7 are deliberate.
Tasks 4/6's `IsNatural`/`ReindexId`/`ReindexComp` are `Prop`-valued
DEFINITION bodies — terms to construct whose risk is that the
cast/transport typechecks at all (the step is done when the `def`
elaborates). Task 7's `map`/`map_id`/`map_comp` are true proof holes,
discharged from the matching `isFunctorial` fields (validated by Task 8's
witness; revised in Task 6 if they cannot close). Every such step names
the precise statement, the lemmas (`Subtype.ext`,
`SliceDomPFunctor.map_id/map_comp/map_fst`, raw `α.naturality` via
`congrArg (ConcreteCategory.hom ·)`, the `tagRestr_*` transports), and
the axiom gate. No `TODO`/`TBD`/"handle edge cases".

**Type consistency:** `PresheafDomPFunctorData`/`PresheafDomPFunctor`,
`PresheafPFunctorData`/`PresheafPFunctor`, `RestrId`/`RestrComp`,
`TagRestrId`/`TagRestrComp`/`ReindexNaturality`/`ReindexId`/`ReindexComp`,
`PositionOver`/`Position`, `ShapeOver`/`Shape`, `pZ`, `IsNatural`, `obj`,
`map`, `objPresheaf`, `presheafWitness`, `domFunctor`, `functor`,
`functor_obj`/`functor_map` are used consistently across tasks.
`objPresheaf` returns `Jᵒᵖ ⥤ Type` (value); `functor` returns the
categorical `(Iᵒᵖ ⥤ Type) ⥤ (Jᵒᵖ ⥤ Type)`.

**Highest-risk items** (flagged for the executor): Task 7 `objPresheaf`
`map_comp` and the Task 6 `ReindexId`/`ReindexComp` transports over
`tagRestr_id`/`tagRestr_comp` (exact equation:
`reindex (h ≫ g) a = reindex g a ∘ reindex h (tagRestr g a)`), validated
by Task 8's concrete witness; and the choice-free proof discipline (avoid
`_apply` convenience lemmas). The axiom linter on the un-allowlisted
`Basic.lean` and `GebTests` modules is the backstop.
