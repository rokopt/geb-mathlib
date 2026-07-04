# Polynomial-functor terminology standardisation Implementation Plan

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [Global Constraints](#global-constraints)
- [File Structure](#file-structure)
  - [Task 1a: Free the `q`/`r` local variables to primed projections](#task-1a-free-the-qr-local-variables-to-primed-projections)
  - [Task 1b: Rename the indexing fields `s`/`t` to `r`/`q`](#task-1b-rename-the-indexing-fields-st-to-rq)
  - [Task 2a: Rename `tagRestr` to `shapeRestr`](#task-2a-rename-tagrestr-to-shaperestr)
  - [Task 2b: Rename `restr` to `directionRestr`](#task-2b-rename-restr-to-directionrestr)
  - [Task 3: Rename `OverLeg` and `tag_triangle`](#task-3-rename-overleg-and-tag_triangle)
  - [Task 4: Reword the retired prose in the `.lean` files](#task-4-reword-the-retired-prose-in-the-lean-files)
  - [Task 5: Add the reference and update `docs/index.md`](#task-5-add-the-reference-and-update-docsindexmd)
  - [Task 6: Full-suite verification gate](#task-6-full-suite-verification-gate)
- [Branch closeout](#branch-closeout)
- [Self-review](#self-review)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Rename the non-standard identifiers and reword the
docstrings and comments in the slice and presheaf polynomial-functor
sources to the terms fixed in the design spec, with no semantic
change.

**Architecture:** This is a rename refactor, not a feature. There is
no new test to write first; the existing test suite
(`GebTests/Mathlib/Data/PFunctor/`) is the regression oracle. Each
task's cycle is: apply an order-safe token rename or prose edit
across every file it touches, then `lake build` + `lake test` (green
proves no semantic change), then a grep sweep (proves the retired
token is gone), then commit. Tasks are ordered so each one leaves
the build green on its own.

**Tech Stack:** Lean 4 + mathlib (`lake build` / `lake test` /
`lake lint`); `markdownlint-cli2` + `doctoc` for Markdown; `jj` for
version control.

## Global Constraints

- No semantic change: no definition, statement, proof, universe
  signature, `@[expose]` / `@[nolint]` / `@[simp]` attribution, or
  import is altered. Only identifiers and docstring/comment prose
  change.
- Constructive discipline is unaffected: `lake lint`
  (`GebMeta.detectNonstandardAxiom`) must report the same
  permitted-axiom result before and after (a rename cannot change
  axiom dependencies).
- Single-letter field renames are targeted, never blanket. Rename
  the structure *field* `s`/`t` only through: the two field
  *declarations* (`Slice/Basic.lean:88` `s : …` and `:97` `t : …`,
  and their field docstrings), structure-literal fields `s :=` / `t
  :=`, projection accesses `.s` / `F.s` / `.t` / `F.t`, and
  `sCurried`. Do NOT rewrite any bound local named `s` or `t` — the
  `s :`/`t :` declaration pattern occurs *only* at those two lines;
  everywhere else `s :`/`t :` is a binder that must be left alone:
  - `funext s` (presheaf-witness law proofs);
  - `fun s : F.Shape j => …` (`Presheaf/Basic.lean:346,361`),
    `fun t : F.Shape j => …` (`:442`), `{s s' : F.Shape j}`
    (`:440`);
  - `fun t : presheafWitness2Data.Shape j => …`
    (`GebTests/.../Presheaf/Basic.lean:293`), `{s s' : … Shape j}`
    (`:291`).
  The `lake build` after each task is the safety net — an
  over-eager rename breaks it immediately.
- Commit-message convention (mathlib): `type(scope): subject`,
  imperative present, no capital, no trailing period. Scope `poly`.
  Renames use `refactor`; prose-only edits use `doc`.
- VCS is `jj` (raw mutating `git` is hook-blocked). Each task's
  commit step is `jj commit -m "<msg>"`. The topic bookmark
  `refactor/poly-functor-terminology` is advanced to the tip at the
  end; nothing is pushed (push requires separate line-by-line
  review).
- Every Markdown edit keeps `markdownlint-cli2` green and its
  doctoc TOC current.

## File Structure

All edits are to existing files. Twelve files total: ten `.lean`
(five source, five test), plus two documentation files.

Source (`Geb/Mathlib/Data/PFunctor/`):

- `Slice/Basic.lean` — slice core; defines the fields `s`/`t`,
  `sCurried`, `Compatible`, `map_comp` (holds a `q`/`r` local
  collision), the References section.
- `Slice/Functor.lean` — slice categorical wrapper; holds
  `tag_triangle`, `F.t` uses, `s :=`/`t :=` none (field access
  only).
- `Slice/W.lean` — slice W-types; holds `OverLeg`, the algebra
  structure-map local `q`, `F.t` uses.
- `Presheaf/Basic.lean` — presheaf core; holds
  `restr`/`tagRestr`/`reindex`, their law `Prop`s, the `map_comp`
  named-argument call `(q := …) (r := …)`, `F.t`/`F.s` uses, and
  `fun s :`/`fun t :`/`{s s' :}` binders that must be left alone.
- `Presheaf/Functor.lean` — presheaf categorical wrapper; prose
  only (retired "tag"/"retag"/"`t`-tagged" wording and docstring
  `` `t` `` field references; no code field access).

Test (`GebTests/Mathlib/Data/PFunctor/`, mirrors):

- `Slice/Basic.lean` — field literals `s :=`/`t :=`, `.s`/`.t`,
  `sCurried`, a `p`/`q`/`r` projection example (`:69`), "tag"/
  "constraint-leg" prose.
- `Slice/Functor.lean` — field literals `s :=`/`t :=`, "tag" prose.
- `Slice/W.lean` — field literals, `OverLeg`, local `q`, "tag"
  prose.
- `Presheaf/Basic.lean` — field literals, `restr`/`tagRestr`/
  `reindex` witnesses, `fun t :`/`{s s' :}` binders, heavy "tag"
  prose.
- `Presheaf/Functor.lean` — prose only (`` `t` ``-tagged fibre).

Documentation:

- `docs/references.bib` — gains the indexed-containers entry.
- `docs/index.md` — one paragraph of `constraint leg`/`tag leg`
  prose. (No other file under `docs/` is touched: "tag"/"leg"/
  "constraint" elsewhere refers to git tags, commit types, and
  unrelated prose.)

The module-index roots `Slice.lean` and `Presheaf.lean` are empty
umbrella files carrying none of the renamed tokens; unaffected.

---

### Task 1a: Free the `q`/`r` local variables to primed projections

Rename only the incidental *local* variables that currently occupy
`q` and `r`, so the field renames in Task 1b have those letters
free. Renaming bound locals is semantics-preserving; the build stays
green.

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/Slice/Basic.lean` (`map_comp`
  in both namespaces: locals `{q : Y → dom} {r : Z → dom}`)
- Modify: `Geb/Mathlib/Data/PFunctor/Slice/W.lean` (the slice-algebra
  structure map, currently `q : Y → I`, throughout `ElimData`,
  `elimStep`, `elimData`, `elimData_index`, `elimData_valid_mk`,
  `elimData_valid`, `elim`, `comp_elim`, `elim_mk`)
- Modify: `Geb/Mathlib/Data/PFunctor/Presheaf/Basic.lean` (the
  `map_comp` named-argument call at lines ~270–271: `(q := elemProj
  Z') (r := elemProj Z'')`)
- Modify: `GebTests/Mathlib/Data/PFunctor/Slice/W.lean` (the two
  `elim` examples: local `q : Y → Bool`)
- Modify: `GebTests/Mathlib/Data/PFunctor/Slice/Basic.lean` (the
  projection example at `:69`: `(p : X → Bool) (q : Y → Bool) (r : Z
  → Bool)`)

**Interfaces:**

- Produces: `SliceDomPFunctor.map_comp` / `SlicePFunctor.map_comp`
  and the `GebTests/.../Slice/Basic.lean:69` example with
  base-projection locals named `p'`, `p''` (was `q`, `r`).
  `SlicePFunctor.W.*` elim-family declarations with structure-map
  parameter named `p` (was `q`). These parameters are implicit or
  positional; positional call sites are unaffected, but the one
  named-argument call site in `Presheaf/Basic.lean` must use the new
  names.

- [ ] **Step 1: Rename `map_comp` chain locals in `Slice/Basic.lean`**

In both `SliceDomPFunctor.map_comp` and `SlicePFunctor.map_comp`,
rename the two base-projection locals: `q` → `p'` and `r` → `p''`.
They appear in the binder `{p : X → dom} {q : Y → dom} {r : Z →
dom}` and in `hf : q ∘ f = p` / `hg : r ∘ g = q`. After: `{p} {p'}
{p''}`, `hf : p' ∘ f = p`, `hg : p'' ∘ g = p'`.

- [ ] **Step 2: Rename the algebra structure-map local in `Slice/W.lean`**

Rename the slice-algebra structure map `q : Y → I` to `p` in every
elim-family declaration. It occurs in binders `(q : Y → I)`,
hypotheses `(hg : q ∘ g = F.obj q)`, statements `q ∘ elim … =
F.windex`, and bodies `F.obj q`. Replace each `q` denoting this map
with `p`. (There is no `p` already in these declarations, so `p` is
the natural single-projection name; this refines the spec's `p'`,
which reads oddly with no `p` alongside.)

- [ ] **Step 3: Update the `q`/`r` examples in the test files**

In `GebTests/.../Slice/W.lean`, the two `elim` examples (~lines
50–58) bind `(q : Y → Bool)`; rename that `q` to `p` (in `q ∘ …`,
`W.elim F Y q g hg`, `hg : q ∘ g = F.obj q`), and the comment `q =
id` (~line 97) to `p = id`. In `GebTests/.../Slice/Basic.lean:69`,
the example binds `(p : X → Bool) (q : Y → Bool) (r : Z → Bool)`;
rename `q` → `p'`, `r` → `p''` (and their uses in that example's
body).

- [ ] **Step 4: Update the named-argument call in `Presheaf/Basic.lean`**

At the `map_comp` application (~lines 270–271), change `(q :=
elemProj Z')` → `(p' := elemProj Z')` and `(r := elemProj Z'')` →
`(p'' := elemProj Z'')`. The `(p := elemProj Z)` argument is
unchanged.

- [ ] **Step 5: Build and test**

Run: `lake build && lake test`

Expected: both succeed. A failure means a local `q`/`r` was missed
or a named argument no longer resolves.

- [ ] **Step 6: Commit**

```bash
jj commit -m "refactor(poly): free q/r locals to primed projections"
```

---

### Task 1b: Rename the indexing fields `s`/`t` to `r`/`q`

With the locals freed, rename the structure fields. `s`/`sCurried`
become `r`/`rCurried` (the `direction-input` map); `t` becomes `q`
(the `shape-output` map).

**Files (all eight files that reference the fields):**

- Modify: `Geb/Mathlib/Data/PFunctor/Slice/Basic.lean`
- Modify: `Geb/Mathlib/Data/PFunctor/Slice/Functor.lean`
- Modify: `Geb/Mathlib/Data/PFunctor/Slice/W.lean`
- Modify: `Geb/Mathlib/Data/PFunctor/Presheaf/Basic.lean`
- Modify: `GebTests/Mathlib/Data/PFunctor/Slice/Basic.lean`
- Modify: `GebTests/Mathlib/Data/PFunctor/Slice/Functor.lean`
- Modify: `GebTests/Mathlib/Data/PFunctor/Slice/W.lean`
- Modify: `GebTests/Mathlib/Data/PFunctor/Presheaf/Basic.lean`

(`Presheaf/Functor.lean` and its test hold no code field access —
their docstring `` `t` `` references are handled in Task 4.)

**Interfaces:**

- Produces: `SliceDomPFunctor.r` (was `.s`),
  `SliceDomPFunctor.rCurried` (was `.sCurried`), `SlicePFunctor.q`
  (was `.t`). All later tasks and downstream references use these
  names.

- [ ] **Step 1: Rename `sCurried` → `rCurried`**

Replace every occurrence of the token `sCurried` with `rCurried`
across the eight files (definition, docstrings, uses). Unambiguous.

- [ ] **Step 2: Rename the field `s` → `r`**

Rename only field occurrences:

- the field declaration `s : toPFunctor.Idx → dom` and its
  docstring at `Slice/Basic.lean:88` → `r : toPFunctor.Idx → dom`;
- structure-literal fields `s := …` (in `ofCurried`, and test
  witnesses `testSlice`, `taggedSlice`, `wSlice`, `presheafWitness`,
  `presheafWitness2Data`) → `r := …`;
- projection accesses `F.s` / `.s` → `F.r` / `.r`.

Leave every bound local named `s` untouched (see Global
Constraints: `funext s`, `fun s : F.Shape j`, `{s s' : F.Shape j}`).
Do not touch `s.1` / `s = s'` bodies of those binders.

- [ ] **Step 3: Rename the field `t` → `q`**

Rename field occurrences:

- the field declaration `t : toPFunctor.A → cod` and its docstring
  at `Slice/Basic.lean:97` → `q : toPFunctor.A → cod`;
- structure-literal fields `t := …` (`t := id`, `t := tval2`, `t :=
  fun _ => ()`) → `q := …`;
- projection accesses `F.t` / `.t` → `F.q` / `.q`.

The token `.t` does not match `.tagRestr`, `.trans`, `.toPFunctor`,
or `t.1` (no word boundary). Leave bound locals `fun t : …`
untouched.

- [ ] **Step 4: Build and test**

Run: `lake build && lake test`

Expected: both succeed.

- [ ] **Step 5: Grep sweep**

Run:

```bash
grep -rnE '\bsCurried\b|\.s\b|\bs :=|\.t\b|\bt :=' \
  Geb/Mathlib/Data/PFunctor GebTests/Mathlib/Data/PFunctor
```

Expected: no field occurrences. Any remaining `s`/`t` match must be
a bound local (inspect to confirm none is a missed field access).

- [ ] **Step 6: Commit**

```bash
jj commit -m "refactor(poly): rename indexing fields s/t to r/q"
```

---

### Task 2a: Rename `tagRestr` to `shapeRestr`

The shape-presheaf restriction. Do this compound token before
`restr` (no ordering hazard exists — `tagRestr` has a capital-`R`
`Restr` a lowercase-`restr` pass cannot match — but it keeps the
greps clean).

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/Presheaf/Basic.lean`
- Modify: `GebTests/Mathlib/Data/PFunctor/Presheaf/Basic.lean`

**Interfaces:**

- Produces: field `shapeRestr` (was `tagRestr`); `ShapeRestrId` /
  `ShapeRestrComp` (was `TagRestrId` / `TagRestrComp`);
  `IsFunctorial` fields `shapeRestr_id` / `shapeRestr_comp`.

- [ ] **Step 1: Rename the compound tokens**

Across both files, replace: `TagRestrId` → `ShapeRestrId`;
`TagRestrComp` → `ShapeRestrComp`; `tagRestr` → `shapeRestr` (also
fixes `tagRestr_id`/`tagRestr_comp`).

- [ ] **Step 2: Build and test**

Run: `lake build && lake test`

Expected: both succeed.

- [ ] **Step 3: Grep sweep**

Run: `grep -rnE '\btagRestr|\bTagRestr' Geb GebTests`

Expected: no output.

- [ ] **Step 4: Commit**

```bash
jj commit -m "refactor(poly): rename tagRestr to shapeRestr"
```

---

### Task 2b: Rename `restr` to `directionRestr`

The direction-presheaf restriction.

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/Presheaf/Basic.lean`
- Modify: `GebTests/Mathlib/Data/PFunctor/Presheaf/Basic.lean`

**Interfaces:**

- Produces: field `directionRestr` (was `restr`); `DirectionRestrId`
  / `DirectionRestrComp` (was `RestrId` / `RestrComp`);
  `IsFunctorial` fields `directionRestr_id` / `directionRestr_comp`.

- [ ] **Step 1: Rename the tokens**

Across both files, replace (case-sensitively): `RestrId` →
`DirectionRestrId`; `RestrComp` → `DirectionRestrComp`; `restr`
(lowercase) → `directionRestr` (fixes the field, its accesses, and
`restr_id`/`restr_comp`; cannot match inside `shapeRestr`,
`objRestr`, or `objRestrElt`, which have a capital `R`). Take care
NOT to rewrite the ordinary English word "restricts"/"restriction"
in prose — it is not `\brestr\b` followed by a Lean identifier
character, but confirm by eye in any prose line.

- [ ] **Step 2: Build and test**

Run: `lake build && lake test`

Expected: both succeed.

- [ ] **Step 3: Grep sweep**

Run: `grep -rnE '\brestr\b|\brestr_|\bRestrId\b|\bRestrComp\b' Geb GebTests`

Expected: no output.

- [ ] **Step 4: Commit**

```bash
jj commit -m "refactor(poly): rename restr to directionRestr"
```

---

### Task 3: Rename `OverLeg` and `tag_triangle`

The two remaining identifiers carrying the retired "leg"/"tag"
coinages.

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/Slice/W.lean` (`OverLeg`,
  including the `simp only [OverLeg, elimData_index]` at ~line 320)
- Modify: `GebTests/Mathlib/Data/PFunctor/Slice/W.lean` (`OverLeg`)
- Modify: `Geb/Mathlib/Data/PFunctor/Slice/Functor.lean`
  (`tag_triangle` and its two call sites in `functor` and
  `functor_comp_forget`, ~lines 110, 117)

**Interfaces:**

- Produces: `SlicePFunctor.OverInput` (was `OverLeg`);
  `SlicePFunctor.output_triangle` (private, was `tag_triangle`).

- [ ] **Step 1: Rename the tokens**

Replace `OverLeg` → `OverInput` in the two `Slice/W.lean` files
(the `simp only` set is covered by the same replace). Replace
`tag_triangle` → `output_triangle` in `Slice/Functor.lean`.

- [ ] **Step 2: Build and test**

Run: `lake build && lake test`

Expected: both succeed.

- [ ] **Step 3: Grep sweep**

Run: `grep -rnE '\bOverLeg\b|\btag_triangle\b' Geb GebTests`

Expected: no output.

- [ ] **Step 4: Commit**

```bash
jj commit -m "refactor(poly): rename OverLeg and tag_triangle"
```

---

### Task 4: Reword the retired prose in the `.lean` files

All identifiers are now renamed; this task rewords the conceptual
prose in docstrings and comments across all ten `.lean` files,
including the docstring-only `Presheaf/Functor.lean` pair. Prose
changes do not affect `lake build` semantics, but the build is
re-run to confirm docstrings still parse. No new citation is
introduced here (that is Task 5).

**Files (all ten):** the five source and five test files listed in
File Structure.

**Interfaces:** none (prose only).

- [ ] **Step 1: Apply the phrase mapping**

Reword every occurrence, across all ten files, per this table.
Match inflections, not just the base phrase:

| Retired wording | Replacement |
| --- | --- |
| "constraint leg", "constraint-leg" (naming `s`/`r`) | "direction-input map" |
| "tag leg" (naming `t`/`q`) | "shape-output map" |
| "the tag", "root tag", "`t`-tag", "`t`-tagged", "tagged", "tagging", "retag(s)", "retagged" | "output index", "shape-output", or "reindex(es) the shape (via `shapeRestr`)" as the sentence requires |
| "tag category" | "output category" |
| "tag `j`", "over tag `0`" (an object of `J`) | "output index `j`", "over output index `0`" |
| "middle leg of a … diagram" | "middle map of a … diagram" |
| "base map" (naming `p`) | "projection" |
| the diagram `dom ◀ s ─ Idx ─ fst ▶ A ─ t ▶ cod` | `dom ◀ r ─ Idx ─ fst ▶ A ─ q ▶ cod` |
| docstring field references `` `t` `` / `` `s` `` (e.g. `` `t` ``-tagged in `Presheaf/Functor.lean`) | `` `q` `` / `` `r` `` |

Apply "total space"/"base space"/"base point"/"projection"
consistently. Do NOT alter the ordinary English "restricts"/
"restriction" or the `## Tags` docstring heading.

- [ ] **Step 2: Build and test**

Run: `lake build && lake test`

Expected: both succeed (docstrings parse; no semantic change).

- [ ] **Step 3: Grep sweep (inflection-aware)**

Run:

```bash
grep -rniE '\btag|\bleg\b|retag|base map' \
  Geb/Mathlib/Data/PFunctor GebTests/Mathlib/Data/PFunctor \
  | grep -vE '## Tags'
```

Expected: no output. `## Tags` headings are excluded as legitimate;
any other surviving "tag"/"leg"/"constraint"/"retag" is a missed
reword — inspect and fix.

- [ ] **Step 4: Commit**

```bash
jj commit -m "doc(poly): reword retired leg/tag/constraint prose"
```

---

### Task 5: Add the reference and update `docs/index.md`

The `[AltenkirchGhaniHancockMcBrideMorris2015]` `.bib` entry, the
`Slice/Basic.lean` docstring citation, and the `docs/index.md`
reword land in one commit, so no intermediate state references a
citation key whose `.bib` entry does not yet exist.

**Files:**

- Modify: `docs/references.bib`
- Modify: `Geb/Mathlib/Data/PFunctor/Slice/Basic.lean`
- Modify: `docs/index.md`

**Interfaces:** none.

- [ ] **Step 1: Add the bib entry**

Append to `docs/references.bib`, matching the existing aligned-field
style. The bibliographic detail is verified: Journal of Functional
Programming, vol. 25 (2015), article e5, doi
10.1017/S095679681500009X.

```bibtex
@article{AltenkirchGhaniHancockMcBrideMorris2015,
  author        = {Altenkirch, Thorsten and Ghani, Neil and Hancock, Peter
                   and McBride, Conor and Morris, Peter},
  title         = {Indexed containers},
  journal       = {Journal of Functional Programming},
  volume        = {25},
  pages         = {e5},
  year          = {2015},
  doi           = {10.1017/S095679681500009X},
}
```

- [ ] **Step 2: Cite it in the slice core**

In `Slice/Basic.lean`'s module docstring, add one sentence naming
the structure as the indexed container `(A, B, q, r)` of
[AltenkirchGhaniHancockMcBrideMorris2015] (`A` shapes, `B`
directions, `q` the `shape-output` map, `r` the `direction-input`
map). Add the key to that file's `## References` section.

- [ ] **Step 3: Reword `docs/index.md`**

At the paragraph reading "Given a `PFunctor` with a constraint leg
`s : Idx → dom` and a tag leg `t : A → cod` …", reword to "Given a
`PFunctor` with a direction-input map `r : Idx → dom` and a
shape-output map `q : A → cod` …". Also reword line ~51 "a tree's
root tag" → "a tree's root output index". Fix any other
retired-term occurrence the Step 5 grep finds.

- [ ] **Step 4: Build, refresh TOC, lint**

Run:

```bash
lake build && doctoc --update-only docs/index.md && markdownlint-cli2 docs/index.md
```

Expected: build succeeds (the new docstring citation parses); doctoc
reports no change or updates cleanly; markdownlint reports 0 errors.

- [ ] **Step 5: Grep sweep**

Run: `grep -nE '\btag|\bleg\b|base map' docs/index.md`

Expected: no output (all three retired occurrences — lines ~39, ~40,
~51 — reworded).

- [ ] **Step 6: Commit**

```bash
jj commit -m "doc(poly): cite indexed containers; update index prose"
```

---

### Task 6: Full-suite verification gate

No edits — a final confirmation that the rename is complete and
green.

- [ ] **Step 1: Comprehensive grep sweep (scoped, inflection-aware)**

Run:

```bash
grep -rniE 'constraint leg|tag leg|\btag|\bleg\b|retag|\btagRestr\b|\bsCurried\b|\bOverLeg\b|\btag_triangle\b|base map' \
  Geb/Mathlib/Data/PFunctor GebTests/Mathlib/Data/PFunctor docs/index.md \
  | grep -vE '## Tags'
```

Expected: no output. (Scoped to the poly-functor subtree and
`docs/index.md`; the wider `docs/` tree uses "tag"/"leg"/
"constraint" in unrelated senses.)

- [ ] **Step 2: Full build, test, and lint**

Run: `lake build && lake test && lake lint`

Expected: all succeed; `lake lint` reports the same permitted-axiom
result as before the branch (no new nonstandard-axiom findings).

- [ ] **Step 3: Advance the topic bookmark**

Run:

```bash
jj bookmark set refactor/poly-functor-terminology -r @-
jj log -r 'ancestors(@, 12)' --no-graph \
  -T 'change_id.shortest() ++ " " ++ description.first_line() ++ "\n"'
```

Expected: the bookmark points at the last real commit; the log shows
the spec commit and the six task commits in order.

---

## Branch closeout

After Task 6 is green, remove the transient spec and plan in the
branch's final commits, per CONTRIBUTING.md § Concern shape (the
spec/plan never reach `main`'s working tree):

```bash
rm docs/superpowers/specs/2026-07-04-poly-functor-terminology-design.md
rm docs/superpowers/plans/2026-07-04-poly-functor-terminology.md
jj commit -m "chore(poly): remove transient terminology spec and plan"
jj bookmark set refactor/poly-functor-terminology -r @-
```

The branch is then ready for the final-review skills (`lean4:review`,
`pr-review-toolkit:review-pr`) and line-by-line user review before
any push.

## Self-review

**Spec coverage:** the two indexing maps (Task 1b) and the `q`/`r`
collision (Task 1a); the presheaf actions (Tasks 2a, 2b); the
retired leg/tag identifiers (Task 3) and prose (Task 4);
base/total/projection (Task 4); the reference and `docs/index.md`
(Task 5); the verification list (per-task gates + Task 6). Non-goals
(no semantic change) are enforced by the build/test/lint gates.

**Adversarial-review amendments folded in:** the file scope is the
full ten `.lean` files (both `GebTests/.../Slice/{Basic,Functor}.lean`
and the `Presheaf/Functor.lean` pair were added); the `s :`/`t :`
declaration pattern is scoped to `Slice/Basic.lean:88,97` with the
`fun s :`/`fun t :`/`{s s' :}` binders listed as no-touch; the
completeness greps are inflection-aware (`tag`/`retag`/`leg`) and
scoped away from the unrelated `docs/` occurrences; the `.bib` entry
and its citation land in one commit (Task 5).

**Placeholder scan:** no TBD/TODO; every step gives exact tokens,
commands, and expected output.

**Type consistency:** the produced names (`r`, `rCurried`, `q`,
`directionRestr`, `shapeRestr`, `OverInput`, `output_triangle`) are
used identically in the Interfaces blocks and grep gates.

**Deviation from spec (flagged for reviewer):** Task 1a Step 2 names
the slice-algebra structure map `p` rather than the spec's `p'`,
since that context has no `p` alongside it; `p'`/`p''` are reserved
for the three-object projection chains.
