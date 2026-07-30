# FinSetSkel W5 Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task. Steps use
> checkbox (`- [ ]`) syntax for tracking.

**Goal:** Register `ElementaryTopos FinSetSkel` from the seven fields W3 and
W4 export, and remove the FinSetSkel roadmap entry from `TODO.md`, migrating
its durable content into the persistent documentation.

**Architecture:** One instance module assembling seven existing terms, one
test parallel asserting what the instance makes resolvable and that its
fields are the terms assigned, then a documentation migration and the
roadmap removal. No mathematical construction is written: the finite-colimit
property is derived generically by W2.

**Tech Stack:** Lean 4 v4.33.0-rc1, mathlib, `lake`, `jj` for version
control, `doctoc` and `markdownlint-cli2` for Markdown.

## Global Constraints

- Toolchain is v4.33.0-rc1. Every axiom measurement stated in prose is
  qualified as taken at that pin.
- No `noncomputable` declaration anywhere. `Classical.choice` only in the
  two modules this plan adds to `GebMeta.classicalAllowedModules`.
- Every `.lean` file: copyright header, `module` keyword, module docstring
  with the mandated sections, `/-- … -/` on every declaration.
- Theorem names `snake_case`; `def` and data-valued `instance` names
  `lowerCamelCase`. No workstream identifier (`W0`–`W5`), no operation-table
  row letter, and no `Geb.Mathlib.` prefix outside an `^import` line, in any
  file under `Geb/` or `GebTests/`.
- Every authored `.md` file passes `markdownlint-cli2`; any Markdown file
  whose sections change has its `doctoc` TOC regenerated in the same commit.
- VCS is `jj`. Raw mutating `git` is blocked by a PreToolUse hook.
  `jj commit` is `describe` + `new`, and bookmarks do not auto-advance, so
  every commit is followed by `jj bookmark set feat/finsetskel-w5 -r @-`.
  Run `jj st` before each commit and confirm the modified files are exactly
  that task's scope.
- Do not tick this plan's `- [ ]` boxes. `jj commit` takes the whole working
  copy, so a plan-file edit lands in the next task's commit.
- Commit subjects: imperative present, lower-case, no trailing period, under
  72 characters, one of `feat fix doc style refactor test chore perf ci`.
- Task order is fixed. Task 1 precedes Task 2 (whose module imports Task 1's);
  Tasks 1–2 precede Task 6 (whose `docs/index.md` entry names the module);
  Tasks 3–6 precede Tasks 7–8 (so no commit states the migrated rules
  nowhere); Task 7 precedes Task 8 (the deletion shifts Task 7's line
  anchors).

---

### Task 1: The instance module

**Files:**

- Create: `Geb/Mathlib/CategoryTheory/FinSetSkel/ElementaryTopos.lean`
- Modify: `GebMeta.lean` (append two allowlist names)
- Modify: `Geb/Mathlib/CategoryTheory/FinSetSkel.lean` (one import)
- Modify: `docs/references.bib` (one entry)

**Interfaces:**

- Consumes: `CategoryTheory.ElementaryTopos`;
  `FinSetSkel.cartesianMonoidalCategory`, `.monoidalClosed`,
  `.initialCocone`, `.binaryCoproductCocone`, `.equalizerCone`,
  `.coequalizerCocone`, `.classifier`.
- Produces: `FinSetSkel.elementaryTopos : ElementaryTopos FinSetSkel.{u}`,
  and with it resolution of `HasEqualizers`, `HasFiniteLimits`,
  `HasFiniteColimits` and `HasPushouts` at `FinSetSkel`. Task 2 asserts all
  of these.

- [ ] **Step 1: Confirm the four classes do not resolve yet**

Create a scratch file `Geb/Internal/W5Probe.lean`:

```lean
module

public import Geb.Mathlib.CategoryTheory.FinSetSkel.Shapes.Instances
public import Geb.Mathlib.CategoryTheory.FinSetSkel.Coequalizer

/-! # Scratch probe -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

/-- Should fail to synthesize. -/
example : HasFiniteColimits FinSetSkel.{0} := inferInstance
```

Run: `lake build Geb.Internal.W5Probe`
Expected: FAIL, `failed to synthesize instance of type class
HasFiniteColimits FinSetSkel`. Then delete the file:
`jj file untrack Geb/Internal/W5Probe.lean` is not needed — just remove it
with the Write/Edit tooling before proceeding, and confirm `jj st` shows no
trace of it.

- [ ] **Step 2: Write the module**

Create `Geb/Mathlib/CategoryTheory/FinSetSkel/ElementaryTopos.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.ElementaryTopos
public import Geb.Mathlib.CategoryTheory.FinSetSkel.Classifier.Instance
public import Geb.Mathlib.CategoryTheory.FinSetSkel.Coequalizer
public import Geb.Mathlib.CategoryTheory.FinSetSkel.Equalizer.Limits
public import Geb.Mathlib.CategoryTheory.FinSetSkel.Exponential.Closed
public import Geb.Mathlib.CategoryTheory.FinSetSkel.Shapes.Instances

/-!
# `FinSetSkel` is an elementary topos

The seven fields of `ElementaryTopos` are the terms the shapes, exponential,
equalizer, coequalizer and classifier modules export, assembled unchanged.
Registering the instance makes `HasEqualizers`, `HasFiniteLimits`,
`HasFiniteColimits` and `HasPushouts` resolve at `FinSetSkel`; the remaining
`Prop` classes the class derives resolve independently of it.

This module introduces no dependence on `Classical.choice` of its own,
inheriting the whole of it from the seven field terms, whose own modules
each name the mathlib construct responsible. It and its test parallel are
listed in `GebMeta.classicalAllowedModules` on that ground.

## Main definitions

* `FinSetSkel.elementaryTopos` — the elementary-topos structure.

## Implementation notes

Nothing beyond the instance is registered. A direct
`HasFiniteColimits FinSetSkel` would be a second resolution route to a
`Prop` that nothing consumes.

The class carries the coequalizer as data rather than asserting finite
colimits because the choice decides which algorithm runs. That an
elementary topos has finite colimits is a theorem, but the construction a
general proof yields is not the union-find of `FinSetSkel/Quotient.lean`.

## References

* [nLabFinSet]

## Tags

elementary topos, finite set, skeleton, subobject classifier
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace FinSetSkel

/-- `FinSetSkel` is an elementary topos. -/
instance elementaryTopos : ElementaryTopos FinSetSkel.{u} where
  cartesian := cartesianMonoidalCategory
  closed := monoidalClosed
  initialCocone := initialCocone
  binaryCoproductCocone := binaryCoproductCocone
  equalizerCone := equalizerCone
  coequalizerCocone := coequalizerCocone
  classifier := classifier

end FinSetSkel
```

- [ ] **Step 3: Add both allowlist names**

In `GebMeta.lean`, in the `classicalAllowedModules` list, after
`` `GebTests.Mathlib.CategoryTheory.FinSetSkel.Classifier.Instance ``, add:

```lean
   `Geb.Mathlib.CategoryTheory.FinSetSkel.ElementaryTopos,
   `GebTests.Mathlib.CategoryTheory.FinSetSkel.ElementaryTopos
```

Keep the existing `].foldl (·.insert ·)` tail on the final element.

- [ ] **Step 4: Add the index import**

In `Geb/Mathlib/CategoryTheory/FinSetSkel.lean`, between the `Coequalizer`
and `Equalizer` lines:

```lean
public import Geb.Mathlib.CategoryTheory.FinSetSkel.ElementaryTopos
```

- [ ] **Step 5: Add the bibliography entry**

In `docs/references.bib`, immediately after the `nLabSkeletalCategory` entry:

```bibtex
@misc{nLabFinSet,
  author        = {{nLab authors}},
  title         = {FinSet},
  howpublished  = {\url{https://ncatlab.org/nlab/show/FinSet}},
  note          = {nLab wiki entry},
}
```

- [ ] **Step 6: Build and lint**

Run, one at a time with a generous timeout:

```text
lake build
lake lint
```

Expected: both succeed. If `lake lint` reports `elementaryTopos depends on
non-standard axiom(s): [Classical.choice]`, Step 3 was not applied or the
index import of Step 4 is missing.

- [ ] **Step 7: Commit**

```bash
jj st
jj commit -m "feat(finsetskel): register the elementary-topos instance

Assembles the seven fields the shapes, exponential, equalizer,
coequalizer and classifier modules export."
jj bookmark set feat/finsetskel-w5 -r @-
```

---

### Task 2: The test parallel

**Files:**

- Create: `GebTests/Mathlib/CategoryTheory/FinSetSkel/ElementaryTopos.lean`
- Modify: `GebTests/Mathlib/CategoryTheory/FinSetSkel.lean` (one import)

**Interfaces:**

- Consumes: `FinSetSkel.elementaryTopos` from Task 1; `FinSetSkel.skeletal`
  from `FinSetSkel/Skeleton.lean`; `IsPushout.of_hasBinaryCoproduct'` from
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic`.
- Produces: nothing later tasks consume.

- [ ] **Step 1: Confirm the names are free across `GebTests/`**

Run:

```bash
grep -rnE '^(def|theorem|abbrev|lemma) (sampleSkelTopos|has(Equalizers|FiniteLimits|FiniteColimits|Pushouts)_finSetSkel)' GebTests/
```

Expected: no output. If any name is taken, rename with the same
`sampleSkelTopos` prefix and record the change in Step 2's code.

- [ ] **Step 2: Write the module**

Create `GebTests/Mathlib/CategoryTheory/FinSetSkel/ElementaryTopos.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinSetSkel.ElementaryTopos
import Geb.Mathlib.CategoryTheory.FinSetSkel.Skeleton
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Tests for `ElementaryTopos FinSetSkel`

Four assertions that the instance makes the classes it alone supplies
resolve, seven that each of its fields is the term assigned to it, and one
worked finite colimit at a shape neither the binary coproducts nor the
coequalizers cover.

## Main statements

* `hasPushouts_finSetSkel` — pushouts resolve, which they do not without
  the instance.
* `sampleSkelToposPushoutInitialSpan_eq` — the pushout of a span with
  initial apex is the two-element object.

## Tags

elementary topos, finite set, skeleton, test
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits FinSetSkel

/-- Equalizers resolve through the instance. -/
theorem hasEqualizers_finSetSkel : HasEqualizers FinSetSkel.{0} := inferInstance

/-- Finite limits resolve through the instance. -/
theorem hasFiniteLimits_finSetSkel : HasFiniteLimits FinSetSkel.{0} :=
  inferInstance

/-- Finite colimits resolve through the instance. -/
theorem hasFiniteColimits_finSetSkel : HasFiniteColimits FinSetSkel.{0} :=
  inferInstance

/-- Pushouts resolve, through the derived finite colimits. -/
theorem hasPushouts_finSetSkel : HasPushouts FinSetSkel.{0} := inferInstance

/-- The cartesian field is the shapes module's structure. -/
theorem sampleSkelTopos_cartesian :
    (FinSetSkel.elementaryTopos : ElementaryTopos FinSetSkel.{0}).cartesian
      = FinSetSkel.cartesianMonoidalCategory := rfl

/-- The closed field is the exponential module's structure. -/
theorem sampleSkelTopos_closed :
    (FinSetSkel.elementaryTopos : ElementaryTopos FinSetSkel.{0}).closed
      = FinSetSkel.monoidalClosed := rfl

/-- The initial-cocone field is the shapes module's cocone. -/
theorem sampleSkelTopos_initialCocone :
    (FinSetSkel.elementaryTopos : ElementaryTopos FinSetSkel.{0}).initialCocone
      = FinSetSkel.initialCocone := rfl

/-- The binary-coproduct field is the shapes module's family. -/
theorem sampleSkelTopos_binaryCoproductCocone (X Y : FinSetSkel.{0}) :
    (FinSetSkel.elementaryTopos :
        ElementaryTopos FinSetSkel.{0}).binaryCoproductCocone X Y
      = FinSetSkel.binaryCoproductCocone X Y := rfl

/-- The equalizer field is the equalizer module's family. -/
theorem sampleSkelTopos_equalizerCone {X Y : FinSetSkel.{0}} (f g : X ⟶ Y) :
    (FinSetSkel.elementaryTopos :
        ElementaryTopos FinSetSkel.{0}).equalizerCone f g
      = FinSetSkel.equalizerCone f g := rfl

/-- The coequalizer field is the coequalizer module's family. -/
theorem sampleSkelTopos_coequalizerCocone {X Y : FinSetSkel.{0}}
    (f g : X ⟶ Y) :
    (FinSetSkel.elementaryTopos :
        ElementaryTopos FinSetSkel.{0}).coequalizerCocone f g
      = FinSetSkel.coequalizerCocone f g := rfl

/-- The classifier field is the classifier module's structure. -/
theorem sampleSkelTopos_classifier :
    (FinSetSkel.elementaryTopos : ElementaryTopos FinSetSkel.{0}).classifier
      = FinSetSkel.classifier := rfl

/-- The pushout of a span whose apex is initial is the binary coproduct,
and `FinSetSkel` being skeletal makes that isomorphism an equality. -/
theorem sampleSkelToposPushoutInitialSpan_eq :
    pushout (initial.to (mk 1 : FinSetSkel.{0})) (initial.to (mk 1))
      = mk 2 :=
  skeletal
    ⟨(IsPushout.of_hasBinaryCoproduct' (mk 1 : FinSetSkel.{0})
        (mk 1)).isoPushout.symm ≪≫
      colimit.isoColimitCocone (binaryCoproductCocone (mk 1) (mk 1))⟩
```

- [ ] **Step 3: Add the test-index import**

In `GebTests/Mathlib/CategoryTheory/FinSetSkel.lean`, between the
`Coequalizer` and `Equalizer` lines:

```lean
import GebTests.Mathlib.CategoryTheory.FinSetSkel.ElementaryTopos
```

- [ ] **Step 4: Build, test and lint**

Run, one at a time:

```text
lake build GebTests
lake test
lake lint -- GebTests
```

Expected: all succeed. If `lake lint -- GebTests` flags the twelve
declarations for `Classical.choice`, Task 1 Step 3 omitted the `GebTests`
allowlist name.

- [ ] **Step 5: Check the import closure**

Run: `lake shake --add-public --keep-implied --keep-prefix Geb GebTests`
Expected: exit 0. If it reports either plain import of the test module as
removable, that import is referenced only from a proof term the elaborator
inlined; do not add `-- shake: keep` — instead report the finding, since
the spec's § Verified findings record that both are referenced.

- [ ] **Step 6: Commit**

```bash
jj st
jj commit -m "test(finsetskel): assert the topos instance and its fields"
jj bookmark set feat/finsetskel-w5 -r @-
```

---

### Task 3: The seven rules

**Files:**

- Modify: `docs/rules/lean-coding.md` § Constructive-only Lean code (`:399`)
  and § Structure and typeclass patterns (`:337`)

**Interfaces:**

- Consumes: nothing.
- Produces: the rule text Task 4 supplies rationale for.

- [ ] **Step 1: Append six bullets to § Constructive-only Lean code**

After the existing paragraph ending `scripts/tests/test-axiom-linter.sh
smoke-tests it.`, add:

```markdown
Six rules govern keeping a module choice-free. Each rests on axiom
measurements taken at v4.33.0-rc1.

- **Measure monomorphically, in the consuming closure.** Take an axiom
  measurement from a monomorphic declaration at the instances used, and in
  the import closure of the module that will use them. `#print axioms` on a
  polymorphic constant reports that constant and no instantiation of it,
  and instance search selects different instances in different closures, so
  a measurement taken narrowly can be the opposite of the one that binds.
- **Name the term where two routes inhabit one class.** Where only one of
  them is choice-free, name it rather than leaving instance search to
  select; where the only instance in scope is choice-dependent, supply one.
- **Split modules by what can be stated choice-free.** Constructions and
  the content of their universal properties go in modules choice-free over
  the underlying data; mathlib structures and `Prop` instances go in a
  wrapper whose fields are those terms. Only wrapper modules are admitted
  to `GebMeta.classicalAllowedModules`. A wrapper may carry content where
  that content cannot be stated choice-free.
- **Bound `Fin` and `Nat` arithmetic by `omega` or by cases.** Establish a
  bound over individually named hypotheses, or by case analysis, rather
  than by the single lemma that states it: the choice-dependent and
  choice-free lemmas of that API interleave under no separating convention.
- **Transport along the codomain freely; state domain transport yourself.**
  `Equiv`'s combinators divide by which side of the arrow they move.
  Mathlib's domain-transport combinators depend on `Classical.choice` where
  its codomain-transport ones do not, so a choice-free module supplies its
  own domain transport.
- **Pin `LawfulBEq (Fin n)` where the closure reaches mathlib's `Fin`
  order API.** Instance search there selects `Std.LawfulBEqOrd.lawfulBEq`,
  which is choice-dependent at `Fin n`, and every operation stated over the
  class inherits that, `decide (j ∈ l)` at `List (Fin n)` among them. Pin
  the instance to the construction over the `DecidableEq`-derived `BEq`.
  This is the second rule one level down, stated separately because the
  closure-dependence makes a narrow measurement read clean.

Re-measure each of these at every toolchain bump, a lemma's axioms
following its proof.

A violation of the `Vector.ofFn` ban stated in
`Geb/Mathlib/Data/Vector/OfFn.lean` is not an elaboration error. The banned
lemmas carry `@[simp]`, so a bare `simp` or `grind` introduces
`Classical.choice` silently, and the violation surfaces at `lake lint`.
```

- [ ] **Step 2: Append one bullet to § Structure and typeclass patterns**

After the `Compositional tests` bullet, add:

```markdown
- **Register a `Prop` class where something consumes it.** Redundant
  registrations are harmless by proof irrelevance, but that is not a reason
  to make them; a second resolution route to an unconsumed `Prop` is code
  without a return.
```

- [ ] **Step 3: Lint the Markdown**

Run:

```bash
npx markdownlint-cli2 'docs/rules/lean-coding.md'
doctoc --dryrun --update-only docs/rules/lean-coding.md
```

Expected: 0 issues; doctoc reports no change (no heading was added).

- [ ] **Step 4: Commit**

```bash
jj st
jj commit -m "doc(rules): state the choice-free discipline as rules"
jj bookmark set feat/finsetskel-w5 -r @-
```

---

### Task 4: The rationale section

**Files:**

- Modify: `docs/process.md` (new `##` section, TOC regenerated)

**Interfaces:**

- Consumes: Task 3's rule text.
- Produces: nothing.

- [ ] **Step 1: Insert the section**

Immediately before `## Avoid colloquialisms and metaphors`, add:

```markdown
## Constructive-only discipline

The rules in `docs/rules/lean-coding.md` § Constructive-only Lean code
exist because axiom cleanliness is not a property of a name. `#print
axioms` on a polymorphic constant reports that constant, not any
instantiation of it, so a constant whose hypothesis is a class can measure
clean while every use of it at a concrete type collects `Classical.choice`.
Instance search compounds this: which instance wins depends on the import
closure, so the same measurement taken in a narrow closure and in the
consuming one can disagree.

That is why the rules are stated as obligations on the author rather than
as facts about named declarations. Naming the term, pinning the instance
and splitting modules by what can be stated choice-free all remove the
dependence on what search happens to select. The module split additionally
keeps the allowlist honest: only a wrapper, whose content is packaging,
reaches `GebMeta.classicalAllowedModules`, so the constructive core stays
strict.

Each rule rests on a measurement, and a lemma's axioms follow its proof, so
they are re-measured on a toolchain bump rather than assumed to persist.
```

- [ ] **Step 2: Regenerate the TOC and lint**

```bash
doctoc --update-only docs/process.md
npx markdownlint-cli2 'docs/process.md'
```

Expected: doctoc updates the TOC; markdownlint reports 0 issues.

- [ ] **Step 3: Commit**

```bash
jj st
jj commit -m "doc(process): record why the choice-free rules exist"
jj bookmark set feat/finsetskel-w5 -r @-
```

---

### Task 5: The four docstring additions

**Files:**

- Modify: `Geb/Mathlib/Data/Vector/OfFn.lean` (module docstring)
- Modify: `Geb/Mathlib/CategoryTheory/ElementaryTopos.lean`
  (§ Implementation notes)
- Modify: `Geb/Mathlib/CategoryTheory/FinSetSkel/Basic.lean`
  (new § Implementation notes)
- Modify: `Geb/Mathlib/CategoryTheory/FinSetSkel/Skeleton.lean`
  (new § Implementation notes)

**Interfaces:**

- Consumes: nothing.
- Produces: nothing.

- [ ] **Step 1: `OfFn.lean`**

In the module docstring, after the sentence ending `into scope.`, add:

```markdown
The banned lemmas carry `@[simp]`, and all but `Vector.ofFn_getElem` also
`@[grind =]`, so a bare `simp` or `grind` meeting such a term introduces
`Classical.choice` without an error. The constructions `Vector.range` and
`Vector.finRange` are equally banned in choice-free modules, not only their
lemmas. Measured at v4.33.0-rc1.
```

- [ ] **Step 2: `ElementaryTopos.lean`**

In § Implementation notes, after the paragraph ending `rebuild it.`, add:

```markdown
The class is `ElementaryTopos` and not `Topos`: the qualifier distinguishes
it from a Grothendieck topos, and mathlib reserves `Topos` for
sheaf-theoretic material, `Mathlib/CategoryTheory/Topos/` holding
`Sheaf.lean` and a deprecated classifier shim while declaring no `Topos`
class.
```

- [ ] **Step 3: `Basic.lean`**

Between `## Main statements` and `## References`, insert:

```markdown
## Implementation notes

The name records the model: `Skel` marks this as the skeletal category of
finite sets, parallel to `FintypeCat.Skeleton`.
```

- [ ] **Step 4: `Skeleton.lean`**

Between `## Main statements` and `## Tags`, insert:

```markdown
## Implementation notes

`FinSetSkel` is not an instantiation of `FintypeCat.Skeleton` because it
cannot be. mathlib's `SmallCategory Skeleton` instance fixes
`Hom X Y := ULift (Fin X.len) → ULift (Fin Y.len)`, and a type carries one
`Category` instance, so a category with the same objects and vector
morphisms is a distinct type rather than a re-instantiation. The
representation is what makes the constructions decidable: mathlib's finite
limits and colimits on `FintypeCat` are layered over `noncomputable`
constructions, so nothing transported along the equivalence computes.
Measured at v4.33.0-rc1.
```

- [ ] **Step 5: Build and check the floodgate rules**

```bash
lake build
scripts/lint-imports.sh
```

Expected: both succeed. Confirm no addition names a workstream or a row
letter:

```bash
grep -rnE '\bW[0-5]\b|[Ww]orkstream' Geb/ GebTests/
```

Expected: no output.

- [ ] **Step 6: Commit**

```bash
jj st
jj commit -m "doc(finsetskel): record the naming and representation choices"
jj bookmark set feat/finsetskel-w5 -r @-
```

---

### Task 6: The `docs/index.md` entry

**Files:**

- Modify: `docs/index.md` (append one entry)

**Interfaces:**

- Consumes: Task 1's module path.
- Produces: nothing.

- [ ] **Step 1: Append the entry**

At the end of § Implemented content, after the
`Classifier/Instance.lean` entry, add:

```markdown
- `Geb/Mathlib/CategoryTheory/FinSetSkel/ElementaryTopos.lean` —
  `FinSetSkel.elementaryTopos`, the `ElementaryTopos FinSetSkel` instance,
  assembling unchanged the cartesian and monoidal-closed structures, the
  initial cocone, the binary-coproduct cocones, the equalizer cones, the
  coequalizer cocones and the classifier. It depends on the five
  field-supplying entries above and on the `ElementaryTopos` class entry.
  Registering it makes `HasEqualizers`, `HasFiniteLimits`,
  `HasFiniteColimits` and `HasPushouts` resolve at `FinSetSkel`; the other
  `Prop` classes the class derives already resolve without it. The source
  and test modules are listed in `GebMeta.classicalAllowedModules`, the
  module inheriting its `Classical.choice` dependence entirely from the
  field terms.
```

- [ ] **Step 2: Lint**

```bash
npx markdownlint-cli2 'docs/index.md'
doctoc --dryrun --update-only docs/index.md
```

Expected: 0 issues; no TOC change.

- [ ] **Step 3: Commit**

```bash
jj st
jj commit -m "doc(index): record the elementary-topos instance"
jj bookmark set feat/finsetskel-w5 -r @-
```

---

### Task 7: The `§ Triggers` edits

**Files:**

- Modify: `TODO.md` § Triggers only (lines 692 onward). Do not touch lines
  181–549 in this task.

**Interfaces:**

- Consumes: nothing.
- Produces: a `§ Triggers` of 22 top-level entries for Task 8 to leave alone.

- [ ] **Step 1: Remove the `Fin.compressEquiv` entry**

Delete `TODO.md:885-892`, the entry whose first line names
`Fin.compressEquiv` as having no consumer. Its condition is false —
`Geb/Mathlib/CategoryTheory/FinSetSkel/Quotient.lean` consumes it at lines
124, 130, 150, 158 and 183, and `docs/index.md:461` documents that.

Verify the bounds before deleting: line 885 must be the bullet naming
`Fin.compressEquiv`, and line 892 must be the last line of that entry.

- [ ] **Step 2: Append two entries**

At the end of § Triggers, add:

```markdown
- **Verify the attested textbook locators**: three locators are recorded
  from secondary attestation and none is verified against its primary
  source. [nLabSkeletalCategory] attests Mac Lane, _Categories for the
  Working Mathematician_ (1971), p. 91 and Riehl, _Category Theory in
  Context_ (2017), p. 34 for the skeleton of a category;
  [nLabFinSet] attests Johnstone, _Sketches of an Elephant_, example 2.1.2
  for the category of finite sets being an elementary topos. Attestation by
  a secondary source is not verification, on the [Pare1974] precedent.
  Trigger: the acquisition of any of the three primary sources, which
  discharges that locator and leaves the entry standing for the others.
- **Reconcile `## Main statements` across the test modules**:
  `GebTests/Mathlib/CategoryTheory/FinSetSkel/ElementaryTopos.lean` carries
  the section, and its siblings do not although each declares named
  theorems. `docs/rules/lean-coding.md` § Documentation requires a section
  when it has content. Trigger: the next occasion to revise those modules.
```

- [ ] **Step 3: Amend four entries**

In the `lake shake --keep-implied` entry, replace the file enumeration
sentence with output measured now:

```bash
lake shake --add-public --keep-prefix Geb GebTests
```

Record the counts that command reports, naming the invocation. Do not carry
the entry's present figures forward; they predate the FinSetSkel modules.

In the `mathlib-to-Batteries` entry, replace `which outlives this
workstream group` with `which outlives the FinSetSkel development`.

In the choice-free `Skeletal FinSetSkel` entry, replace its closing
sentence (that no such use exists while `Skeletal` is consumed only by the
wrapper) with: its consumers are the wrapper and its test parallels, all
allowlisted, so no such use has arisen.

In the `Reconcile test-module import visibility` entry, replace the claim
that every sibling test module uses plain `import` with: most test modules
use `public import` for the module under test, a minority plain `import`.
Do not state a count; it goes stale on the next test module.

- [ ] **Step 4: Verify the entry count and leave three entries alone**

```bash
awk 'NR>=692 && /^- \*\*/ {c++} END{print c}' TODO.md
```

Expected: `22`.

Do not touch the `Extract a shared presheaf test-fixtures module` entry
(its extraction is not discharged: `Fixtures.lean` declares an unrelated
family and `presheafWitnessData` is still duplicated at
`GebTests/Mathlib/Data/PFunctor/Presheaf/Basic.lean:85` and `W.lean:37`),
the `Decide a test-declaration privacy discipline` entry, or the
`Repo-relative paths` entry.

- [ ] **Step 5: Lint and commit**

```bash
npx markdownlint-cli2 'TODO.md'
jj st
jj commit -m "doc(todo): correct four trigger premises and add two"
jj bookmark set feat/finsetskel-w5 -r @-
```

---

### Task 8: The roadmap removal

**Files:**

- Modify: `TODO.md` (delete the section, amend the preamble, regenerate TOC)

**Interfaces:**

- Consumes: Tasks 3–6 having landed the durable content.
- Produces: nothing.

- [ ] **Step 1: Assert both bounds before deleting**

```bash
sed -n '180p;181p;549p;550p' TODO.md
```

Expected exactly: a blank line; `### FinSetSkel as an elementary topos`; a
blank line; `### Complexity of the decidable validity checkers`. If any
line differs, stop — Task 7 shifted the file and the anchors must be
recomputed.

- [ ] **Step 2: Delete lines 181–549**

Use a line-numbered edit, not a title match. Titles repeat in this file's
sections and a title-bounded edit has no checkable bound.

- [ ] **Step 3: Amend the preamble**

Replace `TODO.md:33-34`'s `Workstreams complete → removed; content merged
into \`docs/index.md\`.` with:

```markdown
Workstreams complete → removed; content merged into the persistent
documentation.
```

Leave the word "workstream" in place elsewhere: `CONTRIBUTING.md` § Working
step 2 directs a reader here to pick one.

- [ ] **Step 4: Regenerate the TOC and verify**

```bash
doctoc --update-only TODO.md
grep -nE '\bW[0-5]\b' TODO.md
grep -n '### FinSetSkel as an elementary topos' TODO.md
awk 'NR>=1 && /^- \*\*/ {c++} END{print c}' TODO.md
```

Expected: doctoc updates; both greps produce no output; the entry count is
22 (all `- **` bullets now live in § Triggers).

- [ ] **Step 5: Lint and commit**

```bash
npx markdownlint-cli2 'TODO.md'
jj st
jj commit -m "doc(todo): remove the finsetskel roadmap entry"
jj bookmark set feat/finsetskel-w5 -r @-
```

---

### Task 9: Pre-push verification and removal of the spec and plan

**Files:**

- Delete: `docs/superpowers/specs/2026-07-30-finsetskel-w5-design.md`
- Delete: `docs/superpowers/plans/2026-07-30-finsetskel-w5.md`

**Interfaces:**

- Consumes: everything above.
- Produces: the branch tip the user reviews.

- [ ] **Step 1: Run the full pre-push check**

```bash
scripts/pre-push.sh
```

Expected: passes. It runs the build, the tests, both `lake lint` roots,
`scripts/lint-imports.sh`, the shake check, `markdownlint-cli2` and the
doctoc check.

- [ ] **Step 2: Verify the acceptance criteria the check does not cover**

```bash
grep -rnE '^[[:space:]]*noncomputable[[:space:]]' Geb/ GebTests/
grep -rnE '\bW[0-5]\b|[Ww]orkstream' Geb/ GebTests/
grep -c 'monomorphic\|two routes\|underlying data\|omega\|codomain\|LawfulBEq\|toolchain bump\|elaboration error' docs/rules/lean-coding.md
grep -c 'Constructive-only discipline' docs/process.md
grep -c 'grind' Geb/Mathlib/Data/Vector/OfFn.lean
grep -c 'sheaf' Geb/Mathlib/CategoryTheory/ElementaryTopos.lean
grep -c 'skeletal model\|Skel. marks' Geb/Mathlib/CategoryTheory/FinSetSkel/Basic.lean
grep -c 'SmallCategory' Geb/Mathlib/CategoryTheory/FinSetSkel/Skeleton.lean
grep -c 'FinSetSkel/ElementaryTopos.lean' docs/index.md
grep -c 'nLabFinSet' docs/references.bib
grep -c 'Johnstone\|Mac Lane\|Riehl\|Main statements' TODO.md
```

Expected: the first two produce no output; every count is non-zero.

- [ ] **Step 3: Run the Lean review passes**

Invoke `lean4:review` on the two new modules and
`pr-review-toolkit:review-pr` on the branch, as `scripts/pre-push.sh`
prints. Address findings before proceeding.

- [ ] **Step 4: Remove the spec and the plan**

Delete both files.

- [ ] **Step 5: Final check and commit**

```bash
scripts/pre-push.sh
jj st
jj commit -m "chore(finsetskel): remove the W5 spec and plan"
jj bookmark set feat/finsetskel-w5 -r @-
```

Then stop. The branch is ready for the user's line-by-line review. Do not
push: `AGENTS.md` § No `jj git push` without user line-by-line review binds,
and the PR description is user-authored.
