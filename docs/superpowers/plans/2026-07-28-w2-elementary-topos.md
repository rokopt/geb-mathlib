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
`GebTests/Mathlib/` holding an instance at `Discrete PUnit` and
resolution assertions through it. W2 adds no choice-free layer: its
whole deliverable is packaging, so both modules are allowlisted for
`Classical.choice`.

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
  uses plain `import`. Declarations live under `@[expose] public
  section` in the wrapper.
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
| `docs/references.bib` | Modify. Add `Mikkelsen1976`. |
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
* `CategoryTheory.ElementaryTopos.isInitial`
* `CategoryTheory.ElementaryTopos.tensorUnitIsoΩ₀`

## Implementation notes

The class is stated over `(C : Type u) [Category.{v} C]`, matching
mathlib convention. `SmallCategory C` is `Category.{u} C`, so a
formulation over it would admit small instances but foreclose every
non-small one.

Data is carried rather than asserted because a `Prop` form is
indifferent to a distinction that matters computationally: recovering
a cone from `Nonempty` is `getLimitCone`, which is `Classical.choice`
and `noncomputable`, and `noncomputable` is forbidden here. The
finite-limit and finite-colimit properties are `Prop` and are derived
below rather than carried, chosen cones for an arbitrary finite
diagram not being computably derivable — `FinCategory` carries no
enumeration, and every route to one is `noncomputable` or
`Trunc`-valued.

Accessors for the data-carrying classes are definitions, not
instances, two routes to data not needing to agree definitionally;
accessors for the `Prop` classes are instances, two resolution routes
being harmless there by proof irrelevance. A class-typed definition
is `@[instance_reducible]`, without which it draws a semireducibility
warning that this repository promotes to an error.

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

Finite colimits are redundant as an axiom: that an elementary topos
has them is Mikkelsen's theorem [Mikkelsen1976], presented at
Oberwolfach in July 1972, of which [Pare1974] gives a published proof
by the tripleability of the power-object functor. The definition
transcribed here is [MacLaneMoerdijk1992]'s.

## Tags

elementary topos, subobject classifier, cartesian closed, topos
-/

@[expose] public section

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
entries before the closing `].foldl`:

```lean
   `Geb.Mathlib.CategoryTheory.ElementaryTopos,
   `GebTests.Mathlib.CategoryTheory.ElementaryTopos,
```

- [ ] **Step 6: Run the build to verify it passes**

Run: `lake build GebTests.Mathlib.CategoryTheory.ElementaryTopos`

Expected: PASS, no errors and no warnings.

- [ ] **Step 7: Commit**

```bash
jj describe -m "feat(elementary-topos): add the ElementaryTopos class

Seven fields of mathlib types: the cartesian and closed structures,
the initial object, binary coproducts, equalizers, coequalizers, and
the subobject classifier. Stated over (C : Type u) [Category.{v} C].
Both modules are appended to GebMeta.classicalAllowedModules, W2's
whole deliverable being packaging over Classical-dependent mathlib
category theory."
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
  Task 3 asserts all ten resolve.

- [ ] **Step 1: Write the failing test**

In the test module, replace the single `example` from Task 1 with:

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

instance : HasInitial C := IsInitial.hasInitial (isInitial C)

instance hasColimit_pair {X Y : C} : HasColimit (pair X Y) :=
  ⟨⟨binaryCoproductCocone X Y⟩⟩

instance : HasBinaryCoproducts C := hasBinaryCoproducts_of_hasColimit_pair C

instance hasLimit_parallelPair {X Y : C} {f g : X ⟶ Y} :
    HasLimit (parallelPair f g) :=
  ⟨⟨equalizerCone f g⟩⟩

instance : HasEqualizers C := hasEqualizers_of_hasLimit_parallelPair C

instance hasColimit_parallelPair {X Y : C} {f g : X ⟶ Y} :
    HasColimit (parallelPair f g) :=
  ⟨⟨coequalizerCocone f g⟩⟩

instance : HasCoequalizers C := hasCoequalizers_of_hasColimit_parallelPair C

instance : HasFiniteCoproducts C :=
  hasFiniteCoproducts_of_has_binary_and_initial (C := C)

instance : HasFiniteLimits C :=
  hasFiniteLimits_of_hasEqualizers_and_finite_products

instance : HasFiniteColimits C :=
  hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts

end ElementaryTopos
```

- [ ] **Step 4: Run the build to verify it passes**

Run: `lake build GebTests.Mathlib.CategoryTheory.ElementaryTopos`

Expected: PASS. This build is also the settlement of the spec's one
open question: the test module is a second module, so if
`@[instance_reducible]` needed `@[expose]` to survive the module
boundary, the `HasFiniteLimits` assertion would fail here. The
wrapper already opens `@[expose] public section`, matching
`Geb/Mathlib/CategoryTheory/Grothendieck.lean`.

- [ ] **Step 5: Verify the accessors are reachable across the module boundary**

Append to the test module, inside `section Resolution`:

```lean
/-- The data accessors cross the module boundary. -/
example : CartesianMonoidalCategory C :=
  ElementaryTopos.cartesianMonoidalCategory C

example : MonoidalClosed C :=
  letI := ElementaryTopos.cartesianMonoidalCategory C
  ElementaryTopos.monoidalClosed C
```

Run: `lake build GebTests.Mathlib.CategoryTheory.ElementaryTopos`

Expected: PASS.

- [ ] **Step 6: Commit**

```bash
jj describe -m "feat(elementary-topos): derive the accessors and Prop instances

Four definitions for the data-carrying classes and ten instances for
the Prop classes, per the accessor rule: definitions for data, two
routes to which need not agree definitionally, and instances for Prop,
two routes to which are harmless by proof irrelevance.

HasFiniteCoproducts, HasFiniteLimits and HasFiniteColimits are derived
from the fields rather than carried, so an instance discharges seven
obligations rather than ten."
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
HasFiniteLimits Pt` and six further failures — there is no
`ElementaryTopos Pt` yet.

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

instance : MonoidalClosed Pt where
  closed _ := { rightAdj := 𝟭 Pt, adj := ptAdj _ _ }

/-- The degenerate topos is an elementary topos. -/
instance : ElementaryTopos Pt where
  cartesian := ptCart
  closed := inferInstance
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
grep -nE 'sorry|admit|noncomputable' \
  Geb/Mathlib/CategoryTheory/ElementaryTopos.lean \
  GebTests/Mathlib/CategoryTheory/ElementaryTopos.lean
```

Expected: no output.

- [ ] **Step 6: Commit**

```bash
jj describe -m "test(elementary-topos): witness the class at the degenerate topos

An instance at Discrete PUnit, the one-object one-morphism category.
It establishes what nothing else in W2 can, that the seven fields are
satisfiable together, before W3 through W5 build against the class.
Every construction runs off Unique (X - Y), which mathlib does not
supply for Discrete and which the module adds in one line over the
Subsingleton that it does."
jj new
```

---

### Task 4: Citations and documentation

**Files:**

- Modify: `docs/references.bib`
- Modify: `docs/index.md`

**Interfaces:**

- Consumes: the module docstring's `## References` section from
  Task 1, which cites `[Mikkelsen1976]`.
- Produces: nothing later tasks consume.

- [ ] **Step 1: Add the Mikkelsen entry to the bibliography**

Append to `docs/references.bib`:

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
for k in Mikkelsen1976 Pare1974 MacLaneMoerdijk1992; do
  printf '%s: ' "$k"
  grep -c "^@[a-z]*{$k," docs/references.bib
done
```

Expected: each key reports `1`.

- [ ] **Step 3: Add the `docs/index.md` entry**

Insert in `docs/index.md`, in the same list as the other
`Geb/Mathlib/CategoryTheory/` entries and in path order:

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
  terminal. A wrapper over mathlib's category theory, so
  `Classical.choice`-dependent.
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
jj describe -m "doc(elementary-topos): cite Mikkelsen 1976 and index the module

The finite-colimits theorem is Mikkelsen's, presented at Oberwolfach
in July 1972 and published in his 1976 licentiate thesis; the entry is
keyed to the thesis rather than to the talk, which carries no
searchable identifier, and records the 2022 Theory and Applications of
Categories reprint as the retrievable form."
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

In `TODO.md` § Class fields (lines 289-293), replace the two lines:

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

Then append to the paragraph following the table:

```text
W2 took the derived-instance route, so the finite-limits and
finite-colimits rows of the table above are not fields of the class:
rows e, j and k are W2's one-time derivations. W3 and W5 proceed on
the field form regardless, their assignments becoming redundant `Prop`
instances, harmless by proof irrelevance.
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

- [ ] **Step 5: Update the § Status table**

Change the W2 row to:

```text
| W2 `ElementaryTopos` | — | Complete | `Geb/Mathlib/CategoryTheory/ElementaryTopos.lean` |
```

- [ ] **Step 6: Run the Markdown checks**

Run:

```bash
markdownlint-cli2 'TODO.md' && doctoc --dryrun --update-only TODO.md
```

Expected: `Summary: 0 issues`, and `doctoc` reports "Everything is
OK".

- [ ] **Step 7: Commit**

```bash
jj describe -m "doc(finsetskel): amend the roadmap for W2's completion

Constraint 6 ceases to require an identification of the classifier's
Omega-0 with the cartesian terminal: both are terminal and so
canonically and uniquely isomorphic, leaving no coherence condition to
impose, and an equality of objects is not invariant under equivalence.
Constraint 2's admission of a coherence field goes with it.

The attribution sentence records the finite-colimits theorem as
Mikkelsen's, the sources not establishing the stronger claim that
Pare's was the first publication anywhere, and the standing obligation
to verify it is struck as discharged."
jj new
```

---

### Task 6: Full verification and removal of the transient artifacts

**Files:**

- Delete: `docs/superpowers/specs/2026-07-28-w2-elementary-topos-design.md`
- Delete: `docs/superpowers/plans/2026-07-28-w2-elementary-topos.md`

**Interfaces:**

- Consumes: everything.
- Produces: nothing.

- [ ] **Step 1: Run the full build**

Run: `lake build`

Expected: PASS, no errors and no warnings.

- [ ] **Step 2: Run both lint invocations**

Run:

```bash
lake lint && lake lint -- GebTests
```

Expected: both report `All declarations depend only on permitted
axioms.` The two are separate invocations because `lakefile.toml` sets
`lintDriverArgs = ["Geb"]`, so plain `lake lint` does not reach the
test module.

- [ ] **Step 3: Run the import lint**

Run: `scripts/lint-imports.sh`

Expected: exit 0. W2 imports nothing outside `Mathlib.*`,
`Geb.Mathlib.*` and `GebTests.Mathlib.*`, all admitted.

- [ ] **Step 4: Run the minimised-imports check**

Run: `lake shake --add-public --keep-implied --keep-prefix Geb GebTests`

Expected: no suggested import removals for the two new modules. If it
suggests removing one, remove it and re-run Step 1.

- [ ] **Step 5: Remove the spec and the plan**

Run:

```bash
rm docs/superpowers/specs/2026-07-28-w2-elementary-topos-design.md
rm docs/superpowers/plans/2026-07-28-w2-elementary-topos.md
```

These are transient process artifacts per `CONTRIBUTING.md` § Concern
shape: they record how the current state was reached, not what it is,
so they belong in history rather than on an active branch.

- [ ] **Step 6: Run the pre-push checklist**

Run: `scripts/pre-push.sh`

Expected: exit 0.

- [ ] **Step 7: Commit**

```bash
jj describe -m "doc(elementary-topos): remove the W2 spec and plan

Transient process artifacts, per CONTRIBUTING.md section Concern
shape: they record how the current state was reached, not what it is.
They remain reachable in history and are absent from the working tree,
so no active branch presents superseded decisions as current."
jj new
```

---

## Self-Review

**Spec coverage.** Every deliverable of the spec's § Deliverables maps
to a task: deliverable 1 to Task 1 Step 3 and Task 2 Step 3;
deliverable 2 to Task 1 Step 1 and Task 3; deliverable 3 to Task 1
Step 4; deliverable 4 to Task 1 Step 5; deliverable 5 to Tasks 4
and 5. Every check in the spec's § Verification appears in Task 6,
including the two separate `lake lint` invocations and `lake shake`.
The spec's one open question — whether cross-module `@[expose]` is
needed for the `@[instance_reducible]` accessors — is settled by
Task 2 Steps 4 and 5, which exercise the accessors from the test
module, a second module.

**Placeholder scan.** No step says TBD, "handle edge cases", or
"similar to Task N". Every code step carries the code.

**Type consistency.** `cartesianMonoidalCategory`, `monoidalClosed`,
`isInitial`, `tensorUnitIsoΩ₀`, `hasColimit_pair`,
`hasLimit_parallelPair` and `hasColimit_parallelPair` are spelled
identically in Task 2's interface block, its Step 3 code, and Task 3's
witness. The class field names in Task 1 Step 3 match the field
assignments in Task 3 Step 3 one for one.
