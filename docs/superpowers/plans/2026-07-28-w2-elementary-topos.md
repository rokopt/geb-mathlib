# W2 `ElementaryTopos` Implementation Plan

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Global Constraints](#global-constraints)
- [File Structure](#file-structure)
  - [Task 1: The class, its module, and the allow-lists](#task-1-the-class-its-module-and-the-allow-lists)
  - [Task 2: Derived accessors and instances](#task-2-derived-accessors-and-instances)
  - [Task 3: The degenerate-topos witness](#task-3-the-degenerate-topos-witness)
  - [Task 4: Citations and documentation](#task-4-citations-and-documentation)
  - [Task 5: Roadmap amendments](#task-5-roadmap-amendments)
  - [Task 6: Full verification and removal of the transient artifacts](#task-6-full-verification-and-removal-of-the-transient-artifacts)
- [Self-Review](#self-review)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add the `ElementaryTopos` class, its derived accessors and
derived `Prop` instances, a degenerate-topos witness, and the
citations and roadmap amendments, per
`docs/superpowers/specs/2026-07-28-w2-elementary-topos-design.md`.

**Architecture:** One wrapper module under `Geb/Mathlib/` holding a
seven-field class over mathlib types, four `def` accessors and ten
`instance`s derived from the fields; one test parallel under
`GebTests/Mathlib/` holding resolution assertions under a hypothetical
`[ElementaryTopos C]` and an instance at `Discrete PUnit` with the
same assertions through it. The wrapper adds no choice-free layer,
being packaging throughout, and the test module is allowlisted
alongside it as every `GebTests` parallel is.

**Tech Stack:** Lean 4 (`v4.33.0-rc1`), mathlib
(`79d0395a1825a6264ad5d269e35e60537518955e`), `lake`, `jj`.

## Global Constraints

- **VCS is `jj`, never raw mutating `git`.** `CLAUDE.md` § Rules; a
  PreToolUse hook blocks mutating `git` subcommands. Commit with
  `jj describe -m '…'` then `jj new`.
- **No `noncomputable`, anywhere.** `CONTRIBUTING.md`
  § Constructive-only.
- **No `sorry`, no `admit`, no proof-placeholder underscores.**
  `docs/rules/lean-coding.md`.
- **`Classical.choice` only in allowlisted modules.** Both of W2's
  modules are appended to `GebMeta.classicalAllowedModules` in Task 1.
- **Lean line length 100; Markdown line length 80** (tables and code
  blocks exempt). Deprecation warnings are errors:
  `lakefile.toml` sets `weak.warningAsError = true`.
- **Module system.** Every file under `Geb/Mathlib/` and
  `GebTests/Mathlib/` carries the copyright block, then `module`, then
  imports. `Geb/Mathlib/` uses `public import`; `GebTests/Mathlib/`
  uses plain `import`. Declarations live under `public section` in the
  wrapper; `@[expose]` is not taken, per Task 2 Step 4.
- **Naming.** `lowerCamelCase` for `def`s returning terms;
  `snake_case` for explicitly named instances of `Prop`-valued classes
  (`docs/rules/lean-coding.md` § Naming conventions).
- **Docstrings are mandatory** for the class, every field, and every
  named declaration.
- **Generic user references** in committed text; no first names.
  `CONTRIBUTING.md` § Style and references.

---

## File Structure

| File | Responsibility |
| --- | --- |
| `Geb/Mathlib/CategoryTheory/ElementaryTopos.lean` | Create. The class, four accessors, ten instances. |
| `GebTests/Mathlib/CategoryTheory/ElementaryTopos.lean` | Create. `Discrete PUnit` witness, resolution assertions. |
| `Geb/Mathlib/CategoryTheory.lean` | Modify. Add one `public import`. |
| `GebTests/Mathlib/CategoryTheory.lean` | Modify. Add one `import`. |
| `GebMeta.lean` | Modify. Append both module names to `classicalAllowedModules`. |
| `docs/references.bib` | Modify. Add `Freyd1972` and `Mikkelsen1976`. |
| `docs/index.md` | Modify. Add the module entry. |
| `TODO.md` | Modify. Amend § Class fields, constraints 2 and 6, § Standing obligations, § Status. |

---

### Task 1: The class, its module, and the allow-lists

**Files:**

- Create: `Geb/Mathlib/CategoryTheory/ElementaryTopos.lean`
- Create: `GebTests/Mathlib/CategoryTheory/ElementaryTopos.lean`
- Modify: `Geb/Mathlib/CategoryTheory.lean`
- Modify: `GebTests/Mathlib/CategoryTheory.lean`
- Modify: `GebMeta.lean:58-68` (the `classicalAllowedModules` list)

**Interfaces:**

- Consumes: nothing from earlier tasks.
- Produces: `CategoryTheory.ElementaryTopos (C : Type u)
  [Category.{v} C]`, a class with fields `cartesian`, `closed`,
  `initialCocone`, `binaryCoproductCocone`, `equalizerCone`,
  `coequalizerCocone`, `classifier`. Tasks 2 and 3 use these names.

- [ ] **Step 1: Write the failing test module**

Create `GebTests/Mathlib/CategoryTheory/ElementaryTopos.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.CategoryTheory.ElementaryTopos

/-!
# Tests for the elementary-topos class

An instance at the degenerate topos `Discrete PUnit` witnesses that
the class is inhabitable, and resolution assertions confirm that each
derived `Prop` instance is reachable through it.

## Tags

elementary topos, subobject classifier, degenerate topos
-/

set_option linter.privateModule false

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u

/-- The class elaborates and its fields are reachable. -/
example (C : Type u) [Category.{v} C] [ElementaryTopos C] :
    Subobject.Classifier C :=
  ElementaryTopos.classifier
```

- [ ] **Step 2: Run the build to verify it fails**

Run: `lake build GebTests.Mathlib.CategoryTheory.ElementaryTopos`

Expected: FAIL with `unknown module prefix
'Geb.Mathlib.CategoryTheory.ElementaryTopos'` or
`bad import`.

- [ ] **Step 3: Create the wrapper module with the class**

Create `Geb/Mathlib/CategoryTheory/ElementaryTopos.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Subobject.Classifier.Defs

/-!
# Elementary toposes

An elementary topos is a category with finite limits and finite
colimits that is cartesian closed and has a subobject classifier.
`ElementaryTopos C` carries chosen data for the generators of that
structure — the cartesian and closed structures, the initial object,
binary coproducts, equalizers, coequalizers, and the classifier — and
derives the finite-limit and finite-colimit properties from them.

## Main definitions

* `CategoryTheory.ElementaryTopos`
* `CategoryTheory.ElementaryTopos.cartesianMonoidalCategory`
* `CategoryTheory.ElementaryTopos.monoidalClosed`
* `CategoryTheory.ElementaryTopos.tensorUnitIsoΩ₀`
* `CategoryTheory.ElementaryTopos.isInitial`

## Implementation notes

The class is stated over `(C : Type u) [Category.{v} C]`, matching
mathlib convention. `SmallCategory C` is `Category.{u} C`, so a
formulation over it would admit small instances but foreclose every
non-small one.

Data is carried rather than asserted because a `Prop` form is
indifferent to a distinction that matters computationally: recovering
a cone from `Nonempty` is `getLimitCone`, which is `Classical.choice`
and `noncomputable`, so a class built on the `Prop` form computes
nothing. The finite-limit and finite-colimit properties are `Prop`
and are derived below rather than carried, chosen cones for an
arbitrary finite diagram not being computably derivable:
`FinCategory` carries a `Fintype`, whose underlying `Finset` yields a
list only through the `noncomputable` `Finset.toList`, and every
other route is `noncomputable` or `Trunc`-valued.

Accessors for the data-carrying classes are definitions, not
instances, two routes to data not needing to agree definitionally;
accessors for the `Prop` classes are instances, two resolution routes
being harmless there by proof irrelevance. A class-typed definition
carries `@[instance_reducible]`, without which it draws the
semireducibility warning such a definition otherwise attracts.

`cartesianMonoidalCategory` is marked `attribute [local instance]`,
in force for the rest of the module. Three declarations need it:
`monoidalClosed`, whose type mentions `MonoidalCategory C`;
`tensorUnitIsoΩ₀`, whose type mentions `𝟙_ C`; and `HasFiniteLimits`,
which needs `HasFiniteProducts C`. A consumer holding only
`[ElementaryTopos C]` must apply the same attribute before the
cartesian structure is in scope.

`Functor.empty.{0}` pins the universe deliberately. `HasInitial C`
unfolds to `HasColimitsOfShape (Discrete PEmpty.{1}) C` and `IsInitial`
is `IsColimit (asEmptyCocone _)` at the same level, so any other level
breaks the passage from the initial field to `HasInitial`.

The classifier's `Ω₀` is not required to be the cartesian terminal.
Both objects are terminal, hence canonically and uniquely isomorphic,
so no coherence condition arises; `tensorUnitIsoΩ₀` exports the
comparison. An equality of objects would not be invariant under
equivalence, and would oblige an instance whose natural classifier
yields an isomorphic but unequal `Ω₀` to rebuild it.

## References

* [Freyd1972], for the axiomatisation transcribed here, which
  includes the finite colimits.
* [Mikkelsen1976], whose Theorem 2.3 is that an elementary topos has
  finite colimits, so that the property is redundant as an axiom.
* [Pare1974], for a published proof of that theorem by the
  tripleability of the power-object functor.

## Tags

elementary topos, subobject classifier, cartesian closed, topos
-/

public section

universe v u

namespace CategoryTheory

open CategoryTheory.Limits MonoidalCategory

/-- An elementary topos: a cartesian closed category with a subobject
classifier, with chosen data for the generators of its finite limits
and finite colimits. -/
class ElementaryTopos (C : Type u) [Category.{v} C] where
  /-- The cartesian structure, supplying the terminal object and
  binary products. -/
  cartesian : CartesianMonoidalCategory C
  /-- Closure over the cartesian structure, supplying exponentials. -/
  closed : @MonoidalClosed C _ cartesian.toMonoidalCategory
  /-- A chosen initial object, as a cocone over the empty diagram. -/
  initialCocone : ColimitCocone (Functor.empty.{0} C)
  /-- Chosen binary coproducts. -/
  binaryCoproductCocone : ∀ X Y : C, ColimitCocone (pair X Y)
  /-- Chosen equalizers. -/
  equalizerCone : ∀ {X Y : C} (f g : X ⟶ Y), LimitCone (parallelPair f g)
  /-- Chosen coequalizers. -/
  coequalizerCocone : ∀ {X Y : C} (f g : X ⟶ Y), ColimitCocone (parallelPair f g)
  /-- A subobject classifier. -/
  classifier : Subobject.Classifier C

end CategoryTheory
```

- [ ] **Step 4: Add both modules to their directory indexes**

In `Geb/Mathlib/CategoryTheory.lean`, insert in alphabetical order:

```lean
public import Geb.Mathlib.CategoryTheory.ElementaryTopos
```

In `GebTests/Mathlib/CategoryTheory.lean`, insert in alphabetical
order:

```lean
import GebTests.Mathlib.CategoryTheory.ElementaryTopos
```

- [ ] **Step 5: Append both modules to the `Classical` allow-list**

In `GebMeta.lean`, inside `classicalAllowedModules`, append two
entries and move the closing `].foldl` onto the new last entry, which
carries no trailing comma, so that the list keeps its existing shape:

```lean
   `Geb.Mathlib.CategoryTheory.ElementaryTopos,
   `GebTests.Mathlib.CategoryTheory.ElementaryTopos].foldl (·.insert ·)
```

replacing the previous last entry's `].foldl (·.insert ·)` tail.

- [ ] **Step 6: Run the build to verify it passes**

Run: `lake build GebTests.Mathlib.CategoryTheory.ElementaryTopos`

Expected: PASS, no errors and no warnings.

- [ ] **Step 7: Commit**

```bash
jj describe -m "feat(elementary-topos): add the ElementaryTopos class

Carry seven fields of mathlib types: the cartesian and closed
structures, the initial object, binary coproducts, equalizers,
coequalizers, and the subobject classifier. State the class over
(C : Type u) [Category.{v} C].

Append the wrapper to GebMeta.classicalAllowedModules, its whole
deliverable being packaging over Classical-dependent mathlib category
theory, and the test module alongside it, TODO.md section Standing
obligations requiring each wrapper's GebTests parallel to be
allowlisted with it."
jj new
```

---

### Task 2: Derived accessors and instances

**Files:**

- Modify: `Geb/Mathlib/CategoryTheory/ElementaryTopos.lean` (append
  inside `namespace CategoryTheory`, before `end CategoryTheory`)
- Test: `GebTests/Mathlib/CategoryTheory/ElementaryTopos.lean`

**Interfaces:**

- Consumes: the seven field names from Task 1.
- Produces: `ElementaryTopos.cartesianMonoidalCategory`,
  `.monoidalClosed`, `.isInitial`, `.tensorUnitIsoΩ₀`, and the
  instances `hasColimit_pair`, `hasLimit_parallelPair`,
  `hasColimit_parallelPair`, plus unnamed instances for `HasInitial`,
  `HasBinaryCoproducts`, `HasEqualizers`, `HasCoequalizers`,
  `HasFiniteCoproducts`, `HasFiniteLimits`, `HasFiniteColimits`.
  Task 3 asserts that the seven whole-category classes resolve; the
  three per-diagram instances take implicit arguments and are
  exercised only through them.

- [ ] **Step 1: Write the failing test**

In the test module, replace the single `example` from Task 1, together
with its docstring, by:

```lean
section Resolution

variable (C : Type u) [Category.{v} C] [ElementaryTopos C]

example : HasInitial C := inferInstance
example : HasBinaryCoproducts C := inferInstance
example : HasEqualizers C := inferInstance
example : HasCoequalizers C := inferInstance
example : HasFiniteCoproducts C := inferInstance
example : HasFiniteLimits C := inferInstance
example : HasFiniteColimits C := inferInstance

end Resolution
```

- [ ] **Step 2: Run the build to verify it fails**

Run: `lake build GebTests.Mathlib.CategoryTheory.ElementaryTopos`

Expected: FAIL with `failed to synthesize instance of type class
HasInitial C` and six further synthesis failures.

- [ ] **Step 3: Add the accessors and instances**

Append to `Geb/Mathlib/CategoryTheory/ElementaryTopos.lean`, inside
`namespace CategoryTheory`, after the class:

```lean
namespace ElementaryTopos

variable (C : Type u) [Category.{v} C] [ElementaryTopos C]

/-- The cartesian structure, as a definition rather than an instance:
two routes to data need not agree definitionally. -/
@[instance_reducible] def cartesianMonoidalCategory :
    CartesianMonoidalCategory C :=
  cartesian

attribute [local instance] cartesianMonoidalCategory

/-- Closure over the cartesian structure. -/
@[instance_reducible] def monoidalClosed : MonoidalClosed C := closed

/-- The comparison of the cartesian terminal with the classifier's
`Ω₀`. Both are terminal, so this isomorphism is unique. -/
def tensorUnitIsoΩ₀ : 𝟙_ C ≅ (classifier (C := C)).Ω₀ :=
  IsTerminal.uniqueUpToIso CartesianMonoidalCategory.isTerminalTensorUnit
    Subobject.Classifier.isTerminalΩ₀

/-- The chosen initial object is initial. -/
def isInitial : IsInitial (initialCocone (C := C)).cocone.pt :=
  IsColimit.ofIsoColimit initialCocone.isColimit
    (Cocone.ext (Iso.refl _) (by simp))

/-- The initial-object field, as the corresponding `Prop` class. -/
instance : HasInitial C := IsInitial.hasInitial (isInitial C)

/-- The binary-coproduct field, per diagram. -/
instance hasColimit_pair {X Y : C} : HasColimit (pair X Y) :=
  ⟨⟨binaryCoproductCocone X Y⟩⟩

/-- Binary coproducts, from the per-diagram form. -/
instance : HasBinaryCoproducts C := hasBinaryCoproducts_of_hasColimit_pair C

/-- The equalizer field, per diagram. -/
instance hasLimit_parallelPair {X Y : C} {f g : X ⟶ Y} :
    HasLimit (parallelPair f g) :=
  ⟨⟨equalizerCone f g⟩⟩

/-- Equalizers, from the per-diagram form. -/
instance : HasEqualizers C := hasEqualizers_of_hasLimit_parallelPair C

/-- The coequalizer field, per diagram. -/
instance hasColimit_parallelPair {X Y : C} {f g : X ⟶ Y} :
    HasColimit (parallelPair f g) :=
  ⟨⟨coequalizerCocone f g⟩⟩

/-- Coequalizers, from the per-diagram form. -/
instance : HasCoequalizers C := hasCoequalizers_of_hasColimit_parallelPair C

/-- Finite coproducts, from the initial object and binary coproducts. -/
instance : HasFiniteCoproducts C :=
  hasFiniteCoproducts_of_has_binary_and_initial (C := C)

/-- Finite limits, from the cartesian structure and equalizers. -/
instance : HasFiniteLimits C :=
  hasFiniteLimits_of_hasEqualizers_and_finite_products

/-- Finite colimits, from finite coproducts and coequalizers. -/
instance : HasFiniteColimits C :=
  hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts

end ElementaryTopos
```

- [ ] **Step 4: Run the build to verify it passes**

Run: `lake build GebTests.Mathlib.CategoryTheory.ElementaryTopos`

Expected: PASS, with the wrapper under a plain `public section`.

What this does and does not show. A `public section` carries
signatures and instance resolution across a module boundary; it does
not carry definitional transparency, and `@[instance_reducible]` does
not supply it either — a downstream `rfl` through an accessor's body
reports `The following definitions were not unfolded because their
definition is not exposed`. These assertions are signature-level, so
they would pass for an unattributed `def` too.

W2 nonetheless does not need `@[expose]`, on three grounds that do not
depend on this build. W3 and W4 never import W2, per constraint 2, so
nothing can be denied them. W5 only constructs the instance, which
needs field signatures. And the equations a consumer wants about
`isInitial` and `tensorUnitIsoΩ₀` are settled by `IsInitial.hom_ext`
and `IsTerminal.hom_ext` rather than by unfolding — that is what
§ The two terminals need no coherence field already relies on.

The cost is recorded rather than hidden: no downstream `simp` or
`unfold` on a W2 accessor is available, so a consumer wanting one must
state its own lemma, and `@[expose]` is then a one-line change to the
wrapper. Do not test the question at `Discrete PUnit`: its objects are
a structure over `PUnit` and its morphisms are proofs, so a `rfl`
between accessors succeeds there by structure eta and proof
irrelevance whether or not the body is exposed.

- [ ] **Step 5: Verify the accessors are reachable across the module boundary**

Append to the test module, inside `section Resolution`:

```lean
attribute [local instance] ElementaryTopos.cartesianMonoidalCategory

/-- The data accessors cross the module boundary. -/
example : CartesianMonoidalCategory C :=
  ElementaryTopos.cartesianMonoidalCategory C

example : MonoidalClosed C := ElementaryTopos.monoidalClosed C
```

The `attribute` line is required and must precede the second example.
A `letI` inside the example does not serve: the example's *type* is
elaborated before its body, so `MonoidalClosed C` would report
`failed to synthesize instance of type class MonoidalCategory C`.
This is the same constraint the wrapper meets internally, now met by
a consumer.

Run: `lake build GebTests.Mathlib.CategoryTheory.ElementaryTopos`

Expected: PASS.

- [ ] **Step 6: Commit**

```bash
jj describe -m "feat(elementary-topos): derive the accessors and Prop instances

Add four definitions — two for the data-carrying classes, and the
comparison isomorphism and the initiality term — and ten instances for
the Prop classes, per the accessor rule: definitions for data, two
routes to which need not agree definitionally, and instances for Prop,
two routes to which are harmless by proof irrelevance.

Derive HasFiniteCoproducts, HasFiniteLimits and HasFiniteColimits from
the fields rather than carrying them, so that an instance discharges
seven obligations rather than ten."
jj new
```

---

### Task 3: The degenerate-topos witness

**Files:**

- Modify: `GebTests/Mathlib/CategoryTheory/ElementaryTopos.lean`

**Interfaces:**

- Consumes: the class and every accessor from Tasks 1 and 2.
- Produces: `instance : ElementaryTopos (Discrete PUnit.{1})`, used by
  nothing outside this module.

- [ ] **Step 1: Write the failing test**

Append to the test module, after `section Resolution`:

```lean
section Witness

/-- The degenerate topos: one object, one morphism. -/
abbrev Pt := Discrete PUnit.{1}

example : HasFiniteLimits Pt := inferInstance
example : HasFiniteColimits Pt := inferInstance
example : HasFiniteCoproducts Pt := inferInstance
example : HasEqualizers Pt := inferInstance
example : HasCoequalizers Pt := inferInstance
example : HasInitial Pt := inferInstance
example : HasBinaryCoproducts Pt := inferInstance

end Witness
```

- [ ] **Step 2: Run the build to verify it fails**

Run: `lake build GebTests.Mathlib.CategoryTheory.ElementaryTopos`

Expected: FAIL with `failed to synthesize instance of type class
HasFiniteLimits Pt` and five further failures — six in all, there
being no `ElementaryTopos Pt` yet. `HasInitial Pt` is the exception:
mathlib already supplies it for `Discrete PUnit`, so that assertion
passes either way and does not exercise the witness.

- [ ] **Step 3: Add the witness**

Insert into `section Witness`, immediately after the `abbrev Pt` line
and before the `example`s:

```lean
/-- Every hom-set of `Pt` is a singleton. mathlib supplies
`Subsingleton`; the `Unique` instance is what the constructions below
need. -/
instance uniqueHom (X Y : Pt) : Unique (X ⟶ Y) where
  default := eqToHom (by obtain ⟨⟨⟩⟩ := X; obtain ⟨⟨⟩⟩ := Y; rfl)
  uniq _ := Subsingleton.elim _ _

variable {J : Type u} [Category.{v} J] {F : J ⥤ Pt}

/-- Every cone over a functor into `Pt` is a limit cone. -/
def ptIsLimit (c : Cone F) : IsLimit c where
  lift _ := default
  fac := by intros; apply Subsingleton.elim
  uniq := by intros; apply Subsingleton.elim

/-- Every cocone over a functor into `Pt` is a colimit cocone. -/
def ptIsColimit (c : Cocone F) : IsColimit c where
  desc _ := default
  fac := by intros; apply Subsingleton.elim
  uniq := by intros; apply Subsingleton.elim

/-- A chosen limit cone over any functor into `Pt`. -/
def ptLimitCone (F : J ⥤ Pt) : LimitCone F where
  cone :=
    { pt := ⟨⟨⟩⟩
      π :=
        { app := fun _ => default
          naturality := by intros; apply Subsingleton.elim } }
  isLimit := ptIsLimit _

/-- A chosen colimit cocone over any functor into `Pt`. -/
def ptColimitCocone (F : J ⥤ Pt) : ColimitCocone F where
  cocone :=
    { pt := ⟨⟨⟩⟩
      ι :=
        { app := fun _ => default
          naturality := by intros; apply Subsingleton.elim } }
  isColimit := ptIsColimit _

/-- The cartesian structure on `Pt`. -/
instance ptCart : CartesianMonoidalCategory Pt :=
  .ofChosenFiniteProducts (ptLimitCone _) (fun X Y => ptLimitCone (pair X Y))

/-- Any two endofunctors of `Pt` are adjoint, hom-sets being
singletons. -/
def ptAdj (F G : Pt ⥤ Pt) : F ⊣ G :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ => Equiv.ofUnique _ _
      homEquiv_naturality_left_symm := by intros; apply Subsingleton.elim
      homEquiv_naturality_right := by intros; apply Subsingleton.elim }

/-- `Pt` is monoidal closed: every endofunctor is a right adjoint. -/
instance : MonoidalClosed Pt where
  closed _ := { rightAdj := 𝟭 Pt, adj := ptAdj _ _ }

/-- The degenerate topos is an elementary topos. -/
instance : ElementaryTopos Pt where
  cartesian := ptCart
  closed := (inferInstance : @MonoidalClosed Pt _ ptCart.toMonoidalCategory)
  initialCocone := ptColimitCocone _
  binaryCoproductCocone X Y := ptColimitCocone (pair X Y)
  equalizerCone f g := ptLimitCone (parallelPair f g)
  coequalizerCocone f g := ptColimitCocone (parallelPair f g)
  classifier :=
    Subobject.Classifier.mkOfTerminalΩ₀ (𝟙_ Pt)
      CartesianMonoidalCategory.isTerminalTensorUnit ⟨⟨⟩⟩ default
      (fun _ => default)
      (fun _ => { toCommSq := ⟨Subsingleton.elim _ _⟩
                  isLimit' := ⟨ptIsLimit _⟩ })
      (by intros; apply Subsingleton.elim)
```

- [ ] **Step 4: Run the build to verify it passes**

Run: `lake build GebTests.Mathlib.CategoryTheory.ElementaryTopos`

Expected: PASS.

- [ ] **Step 5: Verify no `sorry` and no `noncomputable`**

Run:

```bash
grep -nE '^noncomputable' \
  Geb/Mathlib/CategoryTheory/ElementaryTopos.lean \
  GebTests/Mathlib/CategoryTheory/ElementaryTopos.lean
```

Expected: no output. `noncomputable` is a declaration modifier, so it
opens a line where it is used as one; the module docstring mentions
the word in prose, never at the start of a line, and a pattern without
the anchor reports three docstring hits. The anchor does not catch every form:
`@[instance_reducible] noncomputable def` would evade it, and this
module has two `@[instance_reducible]` definitions already. No linter
catches `noncomputable`, which is legal Lean, so if the anchored scan
is ever in doubt, run it unanchored and
check the hit count is the three docstring lines.

`sorry` and `admit` need no textual scan: each makes the build itself
fail, ``declaration uses `sorry` `` being a warning that
`weak.warningAsError = true` promotes to an error. The axiom linter is
not the mechanism — it reports named declarations, and this module's
assertions are `example`s, which it does not name.

- [ ] **Step 6: Commit**

```bash
jj describe -m "test(elementary-topos): witness the class at the degenerate topos

Instantiate the class at Discrete PUnit, the one-object one-morphism
category, establishing what nothing else in W2 can: that the seven
fields are satisfiable together, before W3 through W5 build against
the class. Run every construction off Unique (X ⟶ Y), which mathlib
does not supply for Discrete: its Subsingleton instance gives the uniq
field, and eqToHom gives the default."
jj new
```

---

### Task 4: Citations and documentation

**Files:**

- Modify: `docs/references.bib`
- Modify: `docs/index.md`

**Interfaces:**

- Consumes: the module docstring's `## References` section from
  Task 1, which cites `[Freyd1972]`, `[Mikkelsen1976]` and
  `[Pare1974]`.
- Produces: nothing later tasks consume.

- [ ] **Step 1: Add the two bibliography entries**

Append to `docs/references.bib`:

```bibtex
@article{Freyd1972,
  author        = {Freyd, Peter},
  title         = {Aspects of topoi},
  journal       = {Bulletin of the Australian Mathematical Society},
  volume        = {7},
  number        = {1},
  pages         = {1--76},
  year          = {1972},
  doi           = {10.1017/S0004972700044828},
}
```

and:

```bibtex
@phdthesis{Mikkelsen1976,
  author        = {Mikkelsen, Christian Juul},
  title         = {Lattice Theoretic and Logical Aspects of
                   Elementary Topoi},
  school        = {Matematisk Institut, Aarhus Universitet},
  type          = {Licentiate thesis},
  series        = {Various Publication Series},
  number        = {25},
  year          = {1976},
  month         = mar,
  url           = {http://www.tac.mta.ca/tac/reprints/articles/29/tr29.pdf},
  note          = {Reprinted as Reprints in Theory and Applications of
                   Categories, No. 29 (2022), pp. 1--89. Theorem 2.3
                   states that elementary topoi have finite colimits;
                   the author's note to the reprint dates its
                   presentation to Oberwolfach, 23--29 July 1972.},
}
```

- [ ] **Step 2: Verify the module docstring's citation keys resolve**

Run:

```bash
for k in Freyd1972 Mikkelsen1976 Pare1974; do
  printf '%s: ' "$k"
  grep -c "^@[a-z]*{$k," docs/references.bib
done
```

Expected: each key reports `1`.

- [ ] **Step 3: Add the `docs/index.md` entry**

`docs/index.md` § Implemented content is one flat list in topological
order, and its `Geb/Mathlib/CategoryTheory/` entries are not
contiguous. Append this entry at the end of that list: nothing else in
the repository depends on the module, so nothing need follow it.

```markdown
- `Geb/Mathlib/CategoryTheory/ElementaryTopos.lean` — the
  `ElementaryTopos` class: a cartesian closed category with a
  subobject classifier, carrying chosen data for the generators of
  its finite limits and finite colimits — the cartesian and closed
  structures, the initial object, binary coproducts, equalizers,
  coequalizers, and the classifier — and deriving
  `HasFiniteCoproducts`, `HasFiniteLimits` and `HasFiniteColimits`
  from them. Accessors are definitions for the data-carrying classes
  and instances for the `Prop` classes. `tensorUnitIsoΩ₀` compares
  the cartesian terminal with the classifier's `Ω₀`, both being
  terminal. The source and test modules are listed in
  `GebMeta.classicalAllowedModules`, the module being a wrapper over
  mathlib's `Classical`-dependent category theory.
```

- [ ] **Step 4: Run the Markdown checks**

Run:

```bash
markdownlint-cli2 'docs/index.md' && doctoc --update-only docs/index.md
```

Expected: `Summary: 0 issues`, and `doctoc` reports the TOC unchanged
or updates it.

- [ ] **Step 5: Commit**

```bash
jj describe -m "doc(elementary-topos): cite the topos literature and index the module

Cite [Freyd1972] as the source of the axiomatisation the class
transcribes, the one that includes the finite colimits; [Pare1974]
page 556 names it, and Freyd states it directly, a cartesian closed
category being finitely bicomplete there.

Cite [Mikkelsen1976] and [Pare1974] as context for the redundancy of
the finite colimits rather than as sources of a transcription. Key the
Mikkelsen entry to the 1976 licentiate thesis rather than to the 1972
talk, which carries no searchable identifier, and record the 2022
Theory and Applications of Categories reprint as the retrievable
form."
jj new
```

---

### Task 5: Roadmap amendments

**Files:**

- Modify: `TODO.md` § FinSetSkel as an elementary topos

**Interfaces:**

- Consumes: nothing.
- Produces: nothing.

- [ ] **Step 1: Amend the attribution sentence in § Class fields**

In `TODO.md` § Class fields (lines 290-293), replace:

```text
finite colimits are redundant as an axiom, [Pare1974]
having first published that an elementary topos has them, but a
derived construction is whichever one the general proof yields, and
that is not union-find.
```

with:

```text
finite colimits are redundant as an axiom — that an elementary
topos has them is Mikkelsen's theorem [Mikkelsen1976], presented
at Oberwolfach in July 1972, of which [Pare1974] gives a published
proof by the tripleability of the power-object functor — but a
derived construction is whichever one the general proof yields, and
that is not union-find.
```

The sources establish Mikkelsen's discovery and that [Pare1974]
precedes [Mikkelsen1976]; they do not establish that no earlier
publication exists, which is what "first published" asserts.

- [ ] **Step 2: Amend the § Class fields table**

In the same section's table, strike the qualifier from the classifier
row so it reads:

```text
| classifier | `Subobject.Classifier C` | l |
```

Then append to the paragraph beginning "W2 may instead expose the
two `Prop` fields as derived instances" — the second of the two that
follow the table, not the first:

```text
W2 took the derived-instance route, so the finite-limits and
finite-colimits rows of the table above are not fields of the class:
rows e, j and k are W2's one-time derivations, and W3's and W5's
assignments become redundant.
```

- [ ] **Step 3: Amend constraints 2 and 6**

In § Cross-workstream interface constraints, strike the closing
sentence of constraint 2, "A `Prop` coherence field of W2's own
(constraint 6) is admitted, no workstream but W5 producing it."

Replace constraint 6 entirely with:

```text
6. The classifier field's `Ω₀` and the cartesian field's terminal
   object are both terminal, hence canonically and uniquely
   isomorphic; W2 exports the comparison as
   `ElementaryTopos.tensorUnitIsoΩ₀`. The class enforces no
   identification between them, an equality of objects not being
   invariant under equivalence. W3 builds row l over its own row b
   through `mkOfTerminalΩ₀`, as the operation table assigns, so the
   two coincide there as a matter of construction rather than of
   obligation.
```

- [ ] **Step 4: Strike the discharged standing obligation**

In § Standing obligations, delete the bullet beginning "W2 verifies,
against the primary source and before citing the work in Lean, the
[Pare1974] attribution". It is discharged: the record, the
tripleability proof route and Mikkelsen's priority were each checked
against the primary sources.

The § Status row is not changed here. The replacement row would
assert completion, and nothing has been verified yet; Task 6 Step 5
writes it after the checks pass.

- [ ] **Step 5: Run the Markdown checks**

Run:

```bash
markdownlint-cli2 'TODO.md' && doctoc --dryrun --update-only TODO.md
```

Expected: `Summary: 0 issues`, and `doctoc` reports "Everything is
OK".

- [ ] **Step 6: Commit**

```bash
jj describe -m "doc(elementary-topos): amend the roadmap for the W2 design

Relieve constraint 6 of requiring an identification of the
classifier's Ω₀ with the cartesian terminal: both are terminal and so
canonically and uniquely isomorphic, leaving no coherence condition to
impose, and an equality of objects is not invariant under equivalence.
Strike constraint 2's admission of a coherence field with it.

Note in the class-field section that W2 took the derived-instance
route, so that rows e, j and k are W2's one-time derivations while W3
and W5 proceed on the field form regardless.

Record the finite-colimits theorem as Mikkelsen's, the sources not
establishing the stronger claim that Pare's was the first publication
anywhere, and strike the standing obligation to verify it as
discharged."
jj new
```

---

### Task 6: Full verification and removal of the transient artifacts

**Files:**

- Modify: `TODO.md` (§ Status, in Step 5)
- Delete: `docs/superpowers/specs/2026-07-28-w2-elementary-topos-design.md`
- Delete: `docs/superpowers/plans/2026-07-28-w2-elementary-topos.md`

**Interfaces:**

- Consumes: everything.
- Produces: nothing.

- [ ] **Step 1: Run the full build**

Run: `lake build && lake build GebTests`

Expected: PASS, no errors and no warnings. The second invocation is
needed: `lakefile.toml` sets `defaultTargets = ["Geb"]`, so a bare
`lake build` does not reach the test module, and `lake shake` in
Step 4 requires its oleans.

- [ ] **Step 2: Run both lint invocations**

Run:

```bash
lake lint && lake lint -- GebTests
```

Expected: `-- Linting passed for Geb.` from the first, and both that
line and `-- Linting passed for GebTests.` from the second, which runs
over both libraries. The two are separate invocations because
`lakefile.toml` sets `lintDriverArgs = ["Geb"]`, so plain `lake lint`
does not reach the
test module.

- [ ] **Step 3: Run the import lint**

Run: `scripts/lint-imports.sh`

Expected: exit 0. W2 imports nothing outside `Mathlib.*`,
`Geb.Mathlib.*` and `GebTests.Mathlib.*`, all admitted.

- [ ] **Step 4: Run the minimised-imports check**

Run: `lake shake --add-public --keep-implied --keep-prefix Geb GebTests`

Expected: no suggested import removals for the two new modules. If it
suggests removing one, remove it and re-run Step 1.

- [ ] **Step 5: Update the § Status table**

Every check above has passed, so the row may now assert completion.
In `TODO.md` § Status, change the W2 row to:

```text
| W2 `ElementaryTopos` | — | Complete | `Geb/Mathlib/CategoryTheory/ElementaryTopos.lean` |
```

Then run `markdownlint-cli2 'TODO.md'`; expect `Summary: 0 issues`.

- [ ] **Step 6: Remove the spec and the plan**

Steps 7 and 8 follow this deletion and are not recoverable from disk
afterwards. They are: run `scripts/pre-push.sh`, then commit. Note
them before proceeding.

Run:

```bash
rm docs/superpowers/specs/2026-07-28-w2-elementary-topos-design.md
rm docs/superpowers/plans/2026-07-28-w2-elementary-topos.md
```

These are transient process artifacts per `CONTRIBUTING.md` § Concern
shape: they record how the current state was reached, not what it is,
so they belong in history rather than on an active branch.

- [ ] **Step 7: Run the pre-push checklist**

Run: `scripts/pre-push.sh`

Expected: exit 0.

- [ ] **Step 8: Commit**

```bash
jj describe -m "doc(elementary-topos): complete W2 and remove its spec and plan

Mark W2 complete in the roadmap's status table, every check having
passed: both builds, both lint invocations, the import lint, the
minimised-imports check and the pre-push script.

The spec and the plan are transient process artifacts, per
CONTRIBUTING.md section Concern shape: they record how the current
state was reached, not what it is.
They remain reachable in history and are absent from the working tree,
so no active branch presents superseded decisions as current."
jj new
```

---

## Self-Review

**Spec coverage.** Every deliverable of the spec's § Deliverables maps
to a task: deliverable 1 to Task 1 Step 3 and Task 2 Step 3;
deliverable 2 to Task 1 Step 1, Task 2 Steps 1 and 5, and Task 3;
deliverable 3 to Task 1 Step 4; deliverable 4 to Task 1 Step 5;
deliverable 5 to Tasks 4, 5 and 6 Step 5. Task 6 carries the two
separate `lake lint` invocations and
`lake shake`; the placeholder scan is Task 3 Step 5 and the Markdown
checks are in Tasks 4, 5 and 6. (The scan for `sorry` and
`noncomputable` is Task 3 Step 5; the check for TBDs and vague steps
is the next paragraph.)
The question the spec's § Verification records — whether the wrapper
needs `@[expose]` — is answered there and in Task 2 Step 4, on three
grounds independent of any build: W3 and W4 never import W2, W5 only
constructs the instance, and the equations a consumer wants go
through `IsInitial.hom_ext` and `IsTerminal.hom_ext`. The Task 2
build shows only that signatures and instance resolution cross a
plain `public section`; it does not bear on transparency, which
`@[expose]` alone supplies.

**Placeholder scan.** No step says TBD, "handle edge cases", or
"similar to Task N". Every code step carries the code.

**Type consistency.** `cartesianMonoidalCategory`, `monoidalClosed`,
`isInitial`, `tensorUnitIsoΩ₀`, `hasColimit_pair`,
`hasLimit_parallelPair` and `hasColimit_parallelPair` are spelled
identically in Task 2's interface block and its Step 3 code. The class
field names in Task 1 Step 3 match the field assignments in Task 3
Step 3 one for one.
