# Presheaf p.r.a. prototype trim implementation plan

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [Global Constraints](#global-constraints)
- [File structure](#file-structure)
  - [Task 1: Retire the shape-type equality from `Functor.lean`](#task-1-retire-the-shape-type-equality-from-functorlean)
  - [Task 2: Retire the bound and its apparatus from `Codes.lean`](#task-2-retire-the-bound-and-its-apparatus-from-codeslean)
  - [Task 3: Merge the two witness sections into `WorkedExample`](#task-3-merge-the-two-witness-sections-into-workedexample)
  - [Task 4: Retire the generators and the fixture from `Basic.lean`](#task-4-retire-the-generators-and-the-fixture-from-basiclean)
  - [Task 5: Name the leaf as a section of the interpretation](#task-5-name-the-leaf-as-a-section-of-the-interpretation)
  - [Task 6: The pre-push gate, and remove the two spent handoffs](#task-6-the-pre-push-gate-and-remove-the-two-spent-handoffs)
- [Self-review](#self-review)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task. Steps use
> checkbox (`- [ ]`) syntax for tracking.

**Goal:** Retire from `Geb/Internal/PresheafIRProto/` the fifty-two
declarations that measured what a restricted leaf reaches, add the three that
name the leaf as a section of the interpretation, and repair the documentation
and imports the retirement breaks.

**Architecture:** Deletion proceeds against the dependency order — `Functor`,
then `Codes`, then `Basic` — so that every intermediate commit builds. The
three additions and the section merge follow, then the pre-push gate. There is
no new mathematics: the additions are two `rfl`-level theorems and the `def`
they are about.

**Tech Stack:** Lean 4 (toolchain from `lean-toolchain`), Lake, mathlib,
`jj` for version control, `doctoc` and `markdownlint-cli2` for Markdown.

## Global Constraints

- The design record is
  [docs/superpowers/specs/2026-07-31-presheaf-pra-ir-codes-design.md](docs/superpowers/specs/2026-07-31-presheaf-pra-ir-codes-design.md).
  Where this plan and that document disagree, that document governs; where it
  and the prototype's elaborated content disagree, the prototype governs.
- Never `lake env lean`; use `lake build` and `lake test`
  (`docs/rules/lean-coding.md` § Lake / build workflow).
- Never `lake clean`; it forces a full mathlib rebuild.
- No `noncomputable`. No `sorry` in any committed state. No `admit` ever.
- Commit subjects are imperative present tense, lower case, no trailing period,
  from the type list in `docs/rules/ci-and-workflow.md`.
- No raw mutating `git` subcommands; use `jj`. Each task's final step ends
  with `jj new`, which is what keeps the next task's work out of the previous
  commit; do not issue a second one at the start of a task, or the log the
  user reviews gains an empty commit between every pair.
- Every commit in this plan leaves `lake build Geb.Internal.PresheafIRProto`
  passing. Only Task 6 runs the full `scripts/pre-push.sh`.
- Line ranges below are as of the branch head at the time of writing. Verify
  each against the file before deleting: check that the first and last line of
  the stated range match the quoted text.

---

## File structure

| File | Change |
| --- | --- |
| `Geb/Internal/PresheafIRProto/Functor.lean` | 1 declaration and 1 import removed; module docstring repaired |
| `Geb/Internal/PresheafIRProto/Codes.lean` | 41 declarations removed across 11 blocks; 3 sections emptied and deleted; 2 sections merged; 2 imports gained; 9 docstrings and the module docstring repaired |
| `Geb/Internal/PresheafIRProto/Basic.lean` | 10 declarations removed across 3 blocks; 2 sections emptied and deleted; 3 imports removed; 3 docstrings, 1 section docstring and the module docstring repaired |
| `docs/superpowers/specs/2026-07-30-presheaf-pra-handoff.md` | deleted |
| `docs/superpowers/specs/2026-08-02-presheaf-pra-codes-handoff.md` | deleted |

`TODO.md` and the design record are already current; Task 6 verifies rather
than edits them.

---

### Task 1: Retire the shape-type equality from `Functor.lean`

**Files:**

- Modify: `Geb/Internal/PresheafIRProto/Functor.lean:10` (import),
  `:45-49` (`## Main statements`), `:22` (summary count), `:105-112`
  (the declaration)

**Interfaces:**

- Consumes: nothing.
- Produces: nothing. This task only removes; no later task depends on its
  output beyond the file continuing to build.

- [ ] **Step 1: Confirm the declaration is the module's only `yoneda` user**

Run:

```bash
grep -n 'yoneda' Geb/Internal/PresheafIRProto/Functor.lean
```

Expected: exactly five hits — lines 47 and 49 (the `## Main statements`
bullet), 108 (the docstring), and 110 and 112 (the declaration). The grep is
case-sensitive, so line 10's `Mathlib.CategoryTheory.Yoneda` does not match.
If `yoneda` appears in any other declaration, stop and report: the import
removal in Step 5 is then wrong.

- [ ] **Step 2: Delete the declaration with its docstring**

Delete lines 105-112, which begin

```lean
/-- The two shape types coincide on the nose. Only the shape types: the
```

and end

```lean
      (iotaConstData.{uI, uJ, vJ, vI, vJ} (I := I) (yoneda.obj j₀)).A := rfl
```

- [ ] **Step 3: Delete the now-vacuous `## Main statements` section**

Delete the whole section — the heading, its blank line and its single bullet:

```markdown
## Main statements

* `GebProto.iotaPresheafData_A_eq_iotaConstData_yoneda` — the shape type of the
  constant functor at a representable is that of the constant functor at
  `yoneda.obj j₀`. An equality of total spaces, not of presheaves.
```

`docs/rules/lean-coding.md` § Documentation requires a vacuous section be
omitted, never left as a placeholder.

- [ ] **Step 4: Correct the summary count**

At line 22, replace

```text
Six things sit here.
```

with

```text
Five things sit here.
```

- [ ] **Step 5: Delete the `Yoneda` import**

Delete line 10:

```lean
public import Mathlib.CategoryTheory.Yoneda
```

- [ ] **Step 6: Build**

Run: `lake build Geb.Internal.PresheafIRProto`
Expected: exit 0, no errors. `arityPresheafHomULifted` still elaborates —
`uliftFunctor` comes from `Mathlib.CategoryTheory.Types.Basic`, which survives
through `Geb.Mathlib.Data.PFunctor.Presheaf.Basic`.

- [ ] **Step 7: Commit**

```bash
jj describe -m "refactor(proto): retire the shape-type equality and its import

Its statement names iotaConstData, which the bound's retirement removes;
Mathlib.CategoryTheory.Yoneda has no other consumer in the module."
jj new
```

---

### Task 2: Retire the bound and its apparatus from `Codes.lean`

**Files:**

- Modify: `Geb/Internal/PresheafIRProto/Codes.lean` — eleven deletion blocks,
  three section wrappers, two imports, nine declaration docstrings and the
  module docstring

**Interfaces:**

- Consumes: Task 1's file state.
- Produces: a `Codes.lean` with no `HasBijectiveReindex`, `coprod`,
  `deltaRec`, `unitPsh*`, `praWitnessLift*`, `elSliceEquiv*`,
  `ShapeArity.const` or `DomArity.ofPresheaf`. Task 4 relies on those absences
  when it removes the same names' providers from `Basic.lean`.

- [ ] **Step 1: Delete the eleven blocks, highest line first**

Delete in this order so earlier deletions do not shift later line numbers.
Each range is quoted by its first line for verification.

| Range | First line |
| --- | --- |
| 1854-1857 | `/-- So a code's interpretation lies outside the bound. -/` |
| 1677-1692 | `/-- δ at an output-varying arity has non-bijective reindexing, s…` |
| 1491-1528 | `/-- The recursive δ: adjoin the decoding's fibre arity and let t…` |
| 1408-1419 | `/-- The unit has bijective reindexing: it has no directions at all…` |
| 1283-1400 | `/-- The arity of arityVaries as a ShapeArity over unitPsh: t…` |
| 1202-1247 | `/-- Operations of the unit for δ: one shape over each output obj…` |
| 1060-1185 | `/-- Every reindexing map of F is a bijection. Read informally, a…` |
| 1021-1052 | `/-- The slice of ElObj S over an element collapses to the slice …` |
| 423-445 | `/-- The arity that adjoins the same presheaf G over every shape,…` |
| 312-361 | `/-- Every presheaf on the input base arises as an arity: its total…` |
| 210-260 | `/-- Operations of the coproduct of an S-indexed family of preshe…` |

That is 516 lines and forty-one declarations: `HasBijectiveReindex` with its
fourteen theorems, `coprodData`/`coprod`, `deltaRec`, `ShapeArity.const` with
`isFunctorial_const`, the four `unitPsh*`, the four `arityVariesShapeArity`
and `adjoinArityVarying` declarations, the six `praWitnessLift*`,
`elSliceEquiv` with `elSliceEquiv_fst`, and `DomArity.ofPresheaf` with its
four satellites.

Each block is bounded by a blank line on both sides, so deleting exactly the
stated range leaves two consecutive blank lines. Close each up to one; neither
module currently contains a double blank and `mathlibStandardSet` has no
linter for it, so nothing downstream will catch a miss.

- [ ] **Step 2: Delete the three emptied section wrappers**

`Coprod`, `Incompleteness` and `Closure` now contain nothing. Delete each
`section X` / `end X` pair together with the `variable` line it scopes;
`docs/rules/lean-coding.md` § Structure and typeclass patterns requires the
unused `variable` go with it.

- [ ] **Step 3: Check the universe line by hand**

Lean emits no diagnostic for an unused `universe` or section `variable`, so
this cannot be checked by building. Confirm by grep that each name on the
`universe` line still occurs in a surviving declaration:

```bash
for u in uI uJ uA uB uS uD vI vJ u v; do
  printf '%s %s\n' "$u" \
    "$(grep -c "\.{[^}]*\b$u\b\|([^)]*\b$u\b *:" Geb/Internal/PresheafIRProto/Codes.lean)"
done
```

Expected: every count non-zero. `uK` and `vK` are held by the `σ` transport
lemmas, `uS` by `sigmaPsh`, `uD` by the `Decoding` section, so none should
fall to zero; delete from the `universe` line any that does.

- [ ] **Step 4: Add the two imports Task 4 will strip from `Basic.lean`**

After the last Mathlib import, so the Geb and Mathlib import groups stay
separate as in the other two modules, add:

```lean
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Order.Fin.Basic
```

`public` because `arityVariesBase`'s type names the `Category (Fin 2)`
instance, and `scripts/pre-push.sh` runs `lake shake --add-public`, which
distinguishes the two forms.

- [ ] **Step 5: Repair `sigmaPsh`'s docstring**

Replace its last sentence — from "Its shape presheaf is the total space" to
"separating the two." — with the following. Keep the closing `-/`, which
shares `Codes.lean:1007` with the replaced text:

```lean
Its shape presheaf is the total space of `S` paired with the subfunctor's
shapes, which is what lets a later `δ` adjoin an arity varying over the
elements of `S`.
```

- [ ] **Step 6: Repair `PshMor`'s docstring**

Replace

```lean
depends on. `δ` takes one continuation over `ElObj (decPresheaf …)` rather than
a family indexed by these; `deltaRec` is the construction that does index a
family of functors by them.
```

with

```lean
depends on. `δ` takes one continuation over `ElObj (decPresheaf …)` rather than
a family indexed by these.
```

- [ ] **Step 7: Repair `decArity`'s docstring**

Replace

```lean
decoding's fibre arity — and the arity therefore varies over the output, which is the capability
`not_hasBijectiveReindex_arityVaries` and
`hasBijectiveReindex_adjoinArityConst` separate.
```

with

```lean
decoding's fibre arity, so the arity varies over the output object. That this
is a proper generalization of Section 6's constant arity is not established
here.
```

- [ ] **Step 8: Repair `delta`'s docstring**

Two edits. First, replace

```lean
`Σ_{g : P → X} ⟦F (f ∘ g)⟧ = Σ_{d : P → D} (sections of f over d) × ⟦F d⟧`,
which `deltaRec` uses as well. That regrouping is stated here and in
`deltaRec`, and no declaration establishes it as an equation.
```

with

```lean
`Σ_{g : P → X} ⟦F (f ∘ g)⟧ = Σ_{d : P → D} (sections of f over d) × ⟦F d⟧`.
That regrouping is stated here and nowhere established as an equation.
```

Second, replace

```lean
an enlargement of it: `sigmaPsh` leaves `A` untouched, and `Σ_{s ∈ S j} F.Shape
⟨j, s⟩` and `F.A` over `ElObj S` are the same total space, which is
`elSliceEquiv` again. `coprod` does enlarge `A`, its index being a bare type
rather than the fibres of a fibration.
```

with

```lean
an enlargement of it: `sigmaPsh` leaves `A` untouched, and `Σ_{s ∈ S j} F.Shape
⟨j, s⟩` and `F.A` over `ElObj S` are the same total space — stated here and
established by no declaration. A coproduct indexed by a bare type rather than
by the fibres of a fibration would enlarge `A`; no operation here takes one.
```

- [ ] **Step 9: Repair `arityVariesBase`'s docstring**

Replace it entirely with:

```lean
/-- An output-varying arity over the walking arrow: empty over `0`, inhabited
over `1`, reindexed along `0 ⟶ 1` by the map out of the empty type. The base of
the worked example below. -/
```

- [ ] **Step 10: Repair `decVariesElt`'s docstring**

Replace it entirely with:

```lean
/-- The element of the decoding presheaf that the continuation is taken at:
the arity is inhabited over `1`, where reindexing is the map out of the empty
type. -/
```

- [ ] **Step 11: Repair `deltaCodeVaries`'s docstring**

Replace it entirely with:

```lean
/-- A `δ` code at an output-varying arity, with `interp_deltaCodeVaries` below
the check that `interp_deltaCode`'s transports reduce at a closed instance. It
says nothing about what a constant-arity rule admits: no such rule is built
here, and this code type's leaf admits every presheaf p.r.a. functor. -/
```

- [ ] **Step 12: Repair `CodeShape`'s docstring**

Replace

```lean
functors at all, which is the content of `delta`'s type. What a code records is
a derivation, and the same two rules over a restricted leaf make closure under
`δ` a question again.
```

with

```lean
functors at all, which is the content of `delta`'s type. That what a code
records beyond its interpretation is a derivation is a reading, established by
no declaration here.
```

- [ ] **Step 13: Repair `interp_praCode_interp`'s docstring**

Replace

```lean
/-- Every code has the interpretation of a one-node code. So `δ` adds no
functor that `pra` does not already supply, and what a code carries beyond its
interpretation is the derivation. Equivalently,
```

with

```lean
/-- Every code has the interpretation of a one-node code, so `δ` adds no
functor that `pra` does not already supply. That what a code carries beyond
its interpretation is a derivation is a reading and is established nowhere.
Equivalently,
```

- [ ] **Step 14: Repair the module docstring**

Four edits.

1. In the summary, replace "`Basic` supplies the `ι` case (`iotaPresheaf`,
   `iotaConst`); this module supplies `σ` and `δ`." with "`Basic` supplies
   `iotaPresheaf`; this module supplies the semantic operations and the code
   type."
2. In `## Main definitions`, delete every bullet naming a retired
   declaration: `coprodData`/`coprod`, `HasBijectiveReindex`, `unitPsh*`,
   `elSliceEquiv`, `praWitnessLift`, `deltaRec`, and
   `arityVariesShapeArity`/`adjoinArityVarying`. Change the `ShapeArity`
   bullet to name `ShapeArity` alone. Rewrite the `DomArity` conversion
   bullet, three of whose four names go — only `presheaf` survives, so "the
   two conversions between the total-space and the fibrewise presentation of
   an arity, and the round trips" becomes:

   ```markdown
   * `GebProto.DomArity.presheaf` — an arity's fibrewise presentation, as a
     presheaf on the input base.
   ```

3. In `## Main statements`, delete every bullet naming a retired declaration —
   the `hasBijectiveReindex_*` family, the `not_hasBijectiveReindex_*` family,
   `elSliceEquiv_fst`, and the `praWitnessLift*` naturality bullets — with one
   exception. The bullet naming both `interp_deltaCodeVaries` and
   `not_hasBijectiveReindex_interp_deltaCodeVaries` is *rewritten*, not
   deleted, the first of the two surviving:

   ```markdown
   * `GebProto.interp_deltaCodeVaries` — the check that `interp_deltaCode`'s
     transports reduce at a closed instance.
   ```

4. Delete the `## Implementation notes` paragraph beginning "`iotaPresheaf`,
   `unitPshLift`, `sigmaPsh` and `adjoinArity` are semantic operations" —
   its subject is the measurement of restricted leaves.
5. Two `## Main definitions` bullets name no retired declaration but describe
   the retirement's subject, so neither the criterion above nor Step 16's grep
   reaches them. Replace both:

   ```markdown
   * `GebProto.termPsh` / `GebProto.arityVariesBase` / `GebProto.deltaVaries` —
     the worked example's decoding target, its output-varying arity, and the
     `δ` at it.
   * `GebProto.deltaCodeVaries` — a `δ` code at that arity.
   ```

   The first currently reads "the fixtures witnessing that `δ` keeps the
   output-varying arity", whose witness is retired and whose claim the design
   record marks *Unelaborated*; the second reads "a `δ` code whose
   interpretation lies outside the bound", and there is no bound.

- [ ] **Step 15: Build**

Run: `lake build Geb.Internal.PresheafIRProto`
Expected: exit 0.

- [ ] **Step 16: Verify no retired name survives outside the two witness
  section docstrings**

Run:

```bash
grep -n 'HasBijectiveReindex\|hasBijectiveReindex\|deltaRec\|unitPsh\|praWitnessLift\|elSliceEquiv\|ShapeArity.const\|isFunctorial_const\|ofPresheaf\|dirEquivOfPresheaf\|sigmaDirEquivCarrier\|\bcoprod\b\|adjoinArityVarying\|arityVariesShapeArity' Geb/Internal/PresheafIRProto/Codes.lean
```

Expected: hits only inside two `/-! … -/` section docstrings —
`VaryingWitness`'s, which names `not_hasBijectiveReindex_arityVaries`,
`adjoinArityVarying` and `unitPsh`, and `FusedWitness`'s, which names
`hasBijectiveReindex_adjoinArityConst`. Task 3 deletes the first and replaces
the second; leave both alone here. Any hit outside those two docstrings is a
miss in Steps 1-14 and must be fixed before committing.

- [ ] **Step 17: Commit**

```bash
jj describe -m "refactor(proto): retire the bound from the code combinators

The leaf admits every presheaf p.r.a. functor, so no generated fragment
remains for a bound to be complete over. Remove HasBijectiveReindex and its
fourteen theorems, coprod and deltaRec, the unit and the p.r.a. chain, the
slice collapse, ShapeArity.const and the arity round trips, and repair the
docstrings that named them."
jj new
```

---

### Task 3: Merge the two witness sections into `WorkedExample`

**Files:**

- Modify: `Geb/Internal/PresheafIRProto/Codes.lean` — the `VaryingWitness`
  and `FusedWitness` wrappers and their contents

**Interfaces:**

- Consumes: Task 2's file state.
- Produces: one `section WorkedExample` holding `termPsh`, `arityVariesBase`,
  `arityVariesBase_dir_ext`, `isFunctorial_arityVariesBase`, `decUnit`,
  `decVariesElt` and `deltaVaries`, in that order. Task 5 appends nothing to
  it; `deltaCodeVaries` stays in `CodeType`.

- [ ] **Step 1: Locate the two wrappers**

Run:

```bash
grep -n '^section VaryingWitness\|^end VaryingWitness\|^section FusedWitness\|^end FusedWitness\|^section Decoding\|^end Decoding' Geb/Internal/PresheafIRProto/Codes.lean
```

Note the six line numbers. `Decoding` lies between the two witness sections,
and `decUnit` depends on `PshMor`, which `Decoding` defines — so the merge
runs downward: `VaryingWitness`'s survivors move to `FusedWitness`'s position,
never the reverse.

- [ ] **Step 2: Cut `VaryingWitness`'s four survivors**

Cut `termPsh`, `arityVariesBase`, `arityVariesBase_dir_ext` and
`isFunctorial_arityVariesBase` with their docstrings, then delete the emptied
`section VaryingWitness` / `end VaryingWitness` pair and its `/-! … -/`
section docstring.

- [ ] **Step 3: Rename `FusedWitness` and paste the four in**

Rename `section FusedWitness` / `end FusedWitness` to
`section WorkedExample` / `end WorkedExample`, and paste the four cut
declarations at its head, before `decUnit`.

- [ ] **Step 4: Replace the section docstring**

Replace `FusedWitness`'s `/-! … -/` — which reads "That the fused `δ` keeps
the output-varying arity, checked rather than argued …" — with:

```lean
/-!
A worked instance of `δ` at an arity that varies over the output object: over
the walking arrow, empty over `0` and inhabited over `1`. `interp_deltaCodeVaries`
in § CodeType is the check that the rule and its code compute at it.
-/
```

- [ ] **Step 5: Build**

Run: `lake build Geb.Internal.PresheafIRProto`
Expected: exit 0. A failure here means a declaration was moved above something
it depends on; check `decUnit`'s use of `PshMor`.

- [ ] **Step 6: Commit**

```bash
jj describe -m "refactor(proto): merge the two witness sections into one

Their split was the bound's two witnesses; what remains is a single worked
example, which moves below Decoding because decUnit needs PshMor."
jj new
```

---

### Task 4: Retire the generators and the fixture from `Basic.lean`

**Files:**

- Modify: `Geb/Internal/PresheafIRProto/Basic.lean` — three deletion blocks,
  two section wrappers, three imports, three docstrings, one section
  docstring, the module docstring

**Interfaces:**

- Consumes: Tasks 2 and 3 (which removed every consumer of these names).
- Produces: a `Basic.lean` with no `iotaConst*`, `iotaDiscreteShapeEquiv` or
  `arityVaries*`, retaining `ArityB`, `subsingleton_arityB`, `iotaPresheaf`
  and `isFunctorial_of_subsingletonDirection`.

- [ ] **Step 1: Delete the three blocks, highest line first**

| Range | First line |
| --- | --- |
| 342-389 | `/-- Operations of a small functor whose reindex is not invertibl…` |
| 206-249 | `/-- Claim 3: the constant functor at an arbitrary presheaf P on …` |
| 187-198 | `/-- Claim 2: for a discrete J the generalized iota's shape type …` |

That is 104 lines and ten declarations. `ArityB` (line 331) and
`subsingleton_arityB` (line 335) lie between the 206-249 block and the 342-389
block, and stay.

Close up the double blank line each deletion leaves, as in Task 2.

- [ ] **Step 2: Delete the two emptied section wrappers**

`Degeneracy` and `IotaConst` now contain nothing. Delete each
`section` / `end` pair with the `variable` line it scopes.

- [ ] **Step 3: Delete the `Discrete` import**

Delete line 10:

```lean
public import Mathlib.CategoryTheory.Discrete.Basic
```

- [ ] **Step 4: Delete the two imports that moved to `Codes.lean`**

Delete:

```lean
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Order.Fin.Basic
```

Task 2 already added both to `Codes.lean`. `subsingleton_arityB` needs
neither: it uses only `Fin.isLt`, `Fin.ext`, `ULift.ext` and `omega`.

- [ ] **Step 5: Replace the `Reindex` section docstring**

Replace the whole `/-! … -/` at lines 305-327 with:

```lean
/-!
`reindex` is the obligation neither prior paper has an analogue for: Positive
IR's `F→` witnesses functoriality of subcodes in the input labelling
(`A → C`), which is the `directionRestr` side, whereas `reindex` witnesses
functoriality of the arity assignment over `el(T₁)` — the output side.

`ArityB` below is the fibre family the worked example in `Codes` is built on:
one direction at `1`, none at `0`, so that reindexing along `0 ⟶ 1` is the map
out of the empty type.
-/
```

- [ ] **Step 6: Repair `ArityB`'s docstring**

Replace it entirely with:

```lean
/-- The arity of the output object `a`: one direction at `1`, none at `0`.
`Codes`' `arityVariesBase` takes its fibres from this. -/
```

- [ ] **Step 7: Repair `iotaPresheaf`'s docstring**

Replace

```lean
presheaf is `y j₀` is not established here; see
`iotaPresheafData_A_eq_iotaConstData_yoneda`, which equates shape types only.
```

with

```lean
presheaf is `y j₀` is not established here.
```

- [ ] **Step 8: Repair `isFunctorial_of_subsingletonDirection`'s docstring**

Replace

```lean
content. Every constant functor here is of that kind. -/
```

with

```lean
content. `iotaPresheaf` is of that kind. -/
```

- [ ] **Step 9: Repair the module docstring**

Five edits.

1. Title: replace "and the `ι` generators" with "and the `ι` generator".
2. Summary: replace "the constant-functor generators and the fixtures that
   bound what they generate" with "the constant functor at a representable".
   That phrase spans a line break in the file (`Basic.lean:31-32`, "…and the
   fixtures" / "that bound what they generate"), so a literal single-line
   search fails; match across the newline.
3. Numbered claims list: delete claims 2, 3 and 5 (`iotaDiscreteShapeEquiv`,
   `iotaConst`, `arityVaries`), renumber the survivors from one, and rewrite
   the framing sentence "The generator development tests the following
   claims:" as "Two claims are tested here:" — `Functoriality`, the second
   survivor, is no part of the generator development.
4. `## Main definitions`: delete the bullets for `iotaDiscreteShapeEquiv`,
   `iotaConst`/`iotaConstData` and the `ArityB` / `arityVaries` /
   `arityVariesShapeEquiv` group; add a bullet for `ArityB` alone.
5. `## Main statements`: leave unchanged. Its one bullet,
   `pshHomFib_objFibRestr`, survives.

- [ ] **Step 10: Build**

Run: `lake build Geb.Internal.PresheafIRProto`
Expected: exit 0.

- [ ] **Step 11: Verify no retired name survives anywhere in the prototype**

Run:

```bash
grep -rn 'iotaConst\|iotaDiscreteShapeEquiv\|arityVariesData\|arityVariesShapeEquiv\|\barityVaries\b' Geb/Internal/PresheafIRProto/
```

Expected: no output.

- [ ] **Step 12: Commit**

```bash
jj describe -m "refactor(proto): retire the iota generators and the fixture

iotaConst and iotaDiscreteShapeEquiv measured iota as a generator and
arityVaries was the functor the bound was stated about; ArityB and
subsingleton_arityB stay for the worked example's fibres, and three imports
go with them, two to Codes."
jj new
```

---

### Task 5: Name the leaf as a section of the interpretation

**Files:**

- Modify: `Geb/Internal/PresheafIRProto/Codes.lean` — append to
  `section CodeType` after `interp_deltaCodeVaries`; add three bullets to the
  module docstring

**Interfaces:**

- Consumes: `Interp`, `Code`, `praCode`, `interp` and `interp_praCode`, all
  in `section CodeType`, under its `variable (I : Type u) [Category.{u} I]
  (D : Iᵒᵖ ⥤ Type u)`.
- Produces: `praCodeOf : Interp.{u, v} I D → Code.{u, v} I D`,
  `leftInverse_interp_praCodeOf : Function.LeftInverse (interp I D)
  (praCodeOf I D)`, and `surjective_interp : Function.Surjective (interp I D)`.

- [ ] **Step 1: Add the three declarations**

At the end of `section CodeType`, after `interp_deltaCodeVaries` and before
`end CodeType`:

```lean
/-- The leaf as a function of what it denotes: `praCode` uncurried over
`Interp`. It is a section of `interp`, which is what
`leftInverse_interp_praCodeOf` states. -/
def praCodeOf (p : Interp.{u, v} I D) : Code.{u, v} I D :=
  praCode I D p.1 p.2

/-- The interpretation retracts onto the leaf: interpreting the leaf code of a
presheaf p.r.a. functor returns that functor, paired with the base it lands in.
Definitional, `interp`'s leaf clause being the identity and `Interp` a `Sigma`,
so structure eta supplies `⟨p.1, p.2⟩ = p`. -/
theorem leftInverse_interp_praCodeOf :
    Function.LeftInverse (interp.{u, v} I D) (praCodeOf.{u, v} I D) :=
  fun _ ↦ rfl

/-- So the codes denote exactly the presheaf p.r.a. functors over `ElObj D` at
the universes `CodeShape` pins: every one of them has a code, and by
`interp_praCode_interp` `δ` supplies none that the leaf does not. -/
theorem surjective_interp : Function.Surjective (interp.{u, v} I D) :=
  (leftInverse_interp_praCodeOf.{u, v} I D).surjective
```

- [ ] **Step 2: Build**

Run: `lake build Geb.Internal.PresheafIRProto`
Expected: exit 0. A "type mismatch" on `leftInverse_interp_praCodeOf` means
the argument order is reversed: `Function.LeftInverse g f` unfolds to
`∀ a, g (f a) = a`, so `interp` is the first argument and `praCodeOf` the
second.

- [ ] **Step 3: Verify the axioms**

Run: `lake lint`
Expected: exit 0. `lake lint` drives `GebMeta.detectNonstandardAxiom` over
every named `Geb` declaration. `Codes.lean` is not on
`GebMeta.classicalAllowedModules`, so the permitted set there is
`{propext, Quot.sound}` and the linter fails if any of the three depends on
`Classical.choice`. Do not reach for `lake env lean` to `#print axioms`
directly; `docs/rules/lean-coding.md` § Lake / build workflow forbids it,
because it does not pick up `lakefile.toml`'s options and reports spurious
errors.

- [ ] **Step 4: Add the module-docstring entries**

In `## Main definitions`, add:

```markdown
* `GebProto.praCodeOf` — the leaf as a section of the interpretation.
```

In `## Main statements`, add:

```markdown
* `GebProto.leftInverse_interp_praCodeOf`, `GebProto.surjective_interp` — the
  interpretation retracts onto the leaf, so the codes denote exactly the
  presheaf p.r.a. functors over `ElObj D` at the universes `CodeShape` pins.
```

- [ ] **Step 5: Build and lint**

Run: `lake build Geb.Internal.PresheafIRProto && lake lint`
Expected: both exit 0.

- [ ] **Step 6: Commit**

```bash
jj describe -m "feat(proto): name the leaf as a section of the interpretation

praCodeOf is praCode uncurried over Interp; interp retracts onto it, so the
codes denote exactly the presheaf p.r.a. functors at the pinned universes."
jj new
```

---

### Task 6: The pre-push gate, and remove the two spent handoffs

**Files:**

- Delete: `docs/superpowers/specs/2026-07-30-presheaf-pra-handoff.md`,
  `docs/superpowers/specs/2026-08-02-presheaf-pra-codes-handoff.md`
- Verify: `TODO.md`, the design record

**Interfaces:**

- Consumes: Tasks 1-5.
- Produces: a branch state that passes `scripts/pre-push.sh`.

- [ ] **Step 1: Delete the two handoffs**

Both describe a five-rule system, `praWitnessCode`, and obligations 6 and 7 as
live work; none survives. The design record governs, as its § Scope says.

```bash
rm docs/superpowers/specs/2026-07-30-presheaf-pra-handoff.md
rm docs/superpowers/specs/2026-08-02-presheaf-pra-codes-handoff.md
```

- [ ] **Step 2: Verify nothing references them**

Run:

```bash
grep -rn '2026-07-30-presheaf-pra-handoff\|2026-08-02-presheaf-pra-codes-handoff' \
  --include='*.md' . | grep -v '^\./docs/superpowers/plans/'
```

Expected: hits only inside
`docs/superpowers/specs/2026-07-31-presheaf-pra-ir-codes-design.md`, which
names both and assigns their removal to this branch. The `grep -v` excludes
this plan, which names both paths and is itself removed in Step 6. If
`TODO.md` names either, fix `TODO.md`.

- [ ] **Step 3: Verify the design record's counts against the tree**

Run:

```bash
grep -cE '^(@\[[^]]*\] )?(def|theorem|abbrev|instance) ' \
  Geb/Internal/PresheafIRProto/Functor.lean
```

Expected: 5. The anchor matters: an unanchored `grep -c 'instance '` also
matches prose inside docstrings and reports 6. If the anchored count is not 5,
a declaration was lost or kept in error in Task 1 — fix the file, not the
design record, whose § Scope claim of six declarations with five remaining is
correct.

- [ ] **Step 4: Run the full gate**

Run: `scripts/pre-push.sh`
Expected: exit 0. It runs `lake exe cache get` first, then `lake build`,
`lake test`, `lake lint`, `lake build GebTests`, `lake lint -- GebTests`,
`lake shake --add-public --keep-implied --keep-prefix Geb GebTests`,
`scripts/tests/test-lake-shake.sh`, `scripts/lint-imports.sh` and
`scripts/tests/test-lint-imports.sh`, then its script and workflow tests
including `check-commit-msg.sh`, then the Markdown checks, then the axiom and
lint-driver tests. Budget for a long run; only the first `lake build` is
incremental.

If `lake shake` reports a removable import in `Basic.lean` or `Codes.lean`,
the Task 2 / Task 4 import moves were wrong: report which import and stop
rather than adding `-- shake: keep`.

- [ ] **Step 5: Remove this plan**

[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape orders the branch
so that its final commits remove its spec and plan. The design record has a
documented exception — it is the record for four further branches and goes
with the last of them — and this plan has none.

```bash
rm docs/superpowers/plans/2026-08-07-presheaf-pra-prototype-trim.md
```

Re-run `markdownlint-cli2 '**/*.md'` and `doctoc --dryrun --update-only .`
afterwards; both should still pass, the plan having no inbound links.

- [ ] **Step 6: Commit**

```bash
jj describe -m "doc(proto): remove the spent handoffs and this branch's plan

Both handoffs describe rules, obligations and branches the design no longer
has; the design record governs and is removed with the last branch."
jj new
```

- [ ] **Step 7: Report the final state**

Report to the user: the commit list from `main` to `@`, the `pre-push.sh`
result, and the line counts of the three prototype modules before and after.
Do not push; `AGENTS.md` requires the user's line-by-line review first.

---

## Self-review

**Spec coverage.** The design record's § Scope prescribes: the fifty-two
retirements (Tasks 1, 2, 4), the four imports (Tasks 1, 2, 4), the five
emptied sections and their `variable` lines (Tasks 2, 4), the
`VaryingWitness`/`FusedWitness` merge (Task 3), the twelve declaration
docstrings and three section docstrings and three module docstrings (Tasks 1,
2, 3, 4, 5), the three added declarations with their docstrings and module
entries (Task 5), and the prototype branch's acceptance — builds, lints,
passes `scripts/pre-push.sh`, no dangling cross-reference (Task 6). Every item
has a task. The obligations, which are the four upstream branches' work, are
out of this plan's scope by § Branches.

**Placeholder scan.** Every docstring rewrite gives the replacement text.
Every deletion gives a line range and its first line. The one instruction
without literal text is Task 2 Step 14 and Task 4 Step 9, which say which
module-docstring bullets to delete rather than reproducing all of them; the
deletion criterion there is mechanical — a bullet naming a retired
declaration — and Task 2 Step 16 and Task 4 Step 11 check it by grep.

**Type consistency.** `praCodeOf`, `leftInverse_interp_praCodeOf` and
`surjective_interp` are spelled identically in Task 5, in the design record's
§ Scope and obligation 4, and in `TODO.md`. `Function.LeftInverse`'s argument
order is stated once in Task 5 Step 2 with the failure mode named.
