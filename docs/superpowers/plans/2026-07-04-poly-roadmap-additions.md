# Polynomial-functor roadmap additions Implementation Plan

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [Polynomial-functor roadmap additions Implementation Plan](#polynomial-functor-roadmap-additions-implementation-plan)
  - [Global Constraints](#global-constraints)
  - [File Structure](#file-structure)
    - [Task 1: Add the three literature references](#task-1-add-the-three-literature-references)
    - [Task 2: Update the `TODO.md` roadmap](#task-2-update-the-todomd-roadmap)
    - [Task 3: Full verification gate](#task-3-full-verification-gate)
  - [Branch closeout](#branch-closeout)
  - [Self-review](#self-review)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:executing-plans to implement this plan. Steps use
> checkbox (`- [ ]`) syntax for tracking. This is a documentation-only
> change — no TDD, no build/test cycle; verification is markdownlint +
> doctoc + grep.

**Goal:** Update the `TODO.md` polynomial-functor roadmap (retire the
completed terminology item, add a decidable-specialization item,
restructure the universal-morphisms item, unify the free/cofree items
into one relative-(co)free-(co)monad item) and add three
`docs/references.bib` entries.

**Architecture:** Two edited files. The exact roadmap wording is in the
spec's fenced blocks (`docs/superpowers/specs/2026-07-04-poly-roadmap-additions-design.md`,
§ "Concrete `TODO.md` changes"); this plan sequences the edits and
their verification.

**Tech Stack:** Markdown; `doctoc` (TOC), `markdownlint-cli2` (lint),
`jj` (VCS).

## Global Constraints

- Documentation only: no `.lean` file, no build/test surface.
- Every Markdown edit keeps `markdownlint-cli2` green and the `TODO.md`
  doctoc TOC current (`doctoc --update-only TODO.md`).
- Prose follows the roadmap's existing register (formal, dry) and the
  settled terminology — no retired terms (`tag`/`tagging`/`leg`/
  `constraint leg`/`base map`); use direction-input map, shape-output
  map, compatibility property.
- Citation accuracy: verify each new `.bib` entry's details against
  arXiv / the DOI before committing (per CONTRIBUTING § Cite the
  literature; and the Branch-1 fabricated-citation lesson).
- Commit-message convention (mathlib): `type(scope): subject`,
  imperative present, no capital, no trailing period. Scope `poly`,
  type `doc`.
- VCS is `jj` (raw mutating `git` is hook-blocked); commit with
  `jj commit -m "<msg>"`; nothing is pushed.

## File Structure

- `docs/references.bib` — gains three `@article`/`@misc` entries.
- `TODO.md` — the roadmap edits; doctoc TOC regenerated.

---

### Task 1: Add the three literature references

**Files:**

- Modify: `docs/references.bib`

- [ ] **Step 1: Verify and append the entries**

Confirm each identifier resolves (arXiv IDs 1412.7148, 2302.14014,
2509.25879; DOIs as below), then append to `docs/references.bib`,
matching the file's existing aligned-field `@article` style:

```bibtex
@article{AltenkirchChapmanUustalu2015,
  author        = {Altenkirch, Thorsten and Chapman, James and Uustalu, Tarmo},
  title         = {Monads need not be endofunctors},
  journal       = {Logical Methods in Computer Science},
  volume        = {11},
  number        = {1},
  year          = {2015},
  doi           = {10.2168/LMCS-11(1:3)2015},
  eprint        = {1412.7148},
  note          = {Conference version: FoSSaCS 2010, LNCS 6014, pp. 297--311},
}

@article{ArkorMcDermott2024,
  author        = {Arkor, Nathanael and McDermott, Dylan},
  title         = {The formal theory of relative monads},
  journal       = {Journal of Pure and Applied Algebra},
  year          = {2024},
  doi           = {10.1016/j.jpaa.2024.107676},
  eprint        = {2302.14014},
}

@misc{DePascalisUustaluVeltri2025,
  author        = {De Pascalis, Michele and Uustalu, Tarmo and Veltri, Niccol\`{o}},
  title         = {Monoid Structures on Indexed Containers},
  year          = {2025},
  eprint        = {2509.25879},
}
```

- [ ] **Step 2: Commit**

```bash
jj commit -m "doc(poly): add relative-monad and indexed-container references"
```

---

### Task 2: Update the `TODO.md` roadmap

**Files:**

- Modify: `TODO.md`

- [ ] **Step 1: Apply the roadmap edits**

Per the spec's § "Concrete `TODO.md` changes", edit `TODO.md § Next
up`:

- Delete old `### 1. Standardise slice and polynomial-diagram
  terminology` and its body.
- Insert the new `### 1. Decidable-property specializations of the
  functor definitions` (spec's "New item 1" block, verbatim) in its
  place.
- Replace `### 6. Universal morphisms: limits, colimits, exponentials`
  and its body with the spec's "Restructured universal-morphisms item"
  block (`### 6. Universal morphisms` + the 12-step list) verbatim.
- Replace `### 7. Free monads` and `### 8. Cofree comonads` (both
  entries and bodies) with the single spec "Unified
  relative-(co)free-(co)monad item" block (`### 7. Relative (co)free
  (co)monads`) verbatim.
- Leave items 2–5 and the `Validate PresheafPFunctor.functor …`
  trigger unchanged.

- [ ] **Step 2: Regenerate the TOC and lint**

Run:

```bash
doctoc --update-only TODO.md && markdownlint-cli2 TODO.md
```

Expected: doctoc updates the TOC to items 1–7 (removing old item 8);
markdownlint reports 0 errors.

- [ ] **Step 3: Verify content**

Run:

```bash
grep -nE '^### ' TODO.md
grep -niE '\btag|\bleg\b|constraint leg|base map|Standardise' TODO.md
```

Expected: the first shows `### 1.`…`### 7.` (decidable, presheaf
W-types, PFunctor/WType wrappers, W-type initiality, M-types,
universal morphisms, relative (co)free (co)monads) plus the trigger
headings; the second is empty (no retired terms, no leftover
terminology item).

- [ ] **Step 4: Commit**

```bash
jj commit -m "doc(poly): expand the polynomial-functor roadmap"
```

---

### Task 3: Full verification gate

- [ ] **Step 1: Confirm clean**

Run:

```bash
markdownlint-cli2 TODO.md docs/references.bib 2>/dev/null; markdownlint-cli2 TODO.md
doctoc --dryrun --update-only TODO.md
grep -c '^### ' TODO.md
```

Expected: markdownlint 0 errors on `TODO.md`; doctoc dry-run reports
no change; seven `### N.` items plus the trigger/index headings.

- [ ] **Step 2: Advance the topic bookmark**

```bash
jj bookmark set doc/poly-roadmap-additions -r @-
```

---

## Branch closeout

After Task 3, remove the transient spec and plan, per CONTRIBUTING.md §
Concern shape:

```bash
rm docs/superpowers/specs/2026-07-04-poly-roadmap-additions-design.md
rm docs/superpowers/plans/2026-07-04-poly-roadmap-additions.md
jj commit -m "chore(poly): remove transient roadmap-additions spec and plan"
jj bookmark set doc/poly-roadmap-additions -r @-
```

Then line-by-line user review before any push.

## Self-review

**Spec coverage:** the retire+new-item-1 and item-6/item-7 edits (Task
2) and the three `.bib` entries (Task 1) cover the spec's Scope; the
verification list maps to Task 2 Step 3 and Task 3. Non-goals (no code)
hold — no `.lean` file is touched.

**Placeholder scan:** no TBD/TODO in the plan's own steps; the roadmap
items' deferred details ("settled when this item is taken up") are the
spec's intended content, not plan placeholders.

**Consistency:** the new `.bib` keys (`AltenkirchChapmanUustalu2015`,
`ArkorMcDermott2024`, `DePascalisUustaluVeltri2025`) match the keys the
spec's item-7 text references.
