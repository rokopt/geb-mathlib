# Cobham linear-space recognizer implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` (recommended) or
> `superpowers:executing-plans` to implement this plan task-by-task. Steps
> use checkbox (`- [ ]`) syntax for tracking.

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Global Constraints](#global-constraints)
- [Declaration inventory](#declaration-inventory)
- [Bookmark order](#bookmark-order)
  - [Task 1: Record the four deferrals in `TODO.md`](#task-1-record-the-four-deferrals-in-todomd)
  - [Task 2: Correct `BellantoniCook/Tree.lean`'s polytime citation](#task-2-correct-bellantonicooktreeleans-polytime-citation)
  - [Task 3: `BinTree.depth_le_length`](#task-3-bintreedepth_le_length)
  - [Task 4: Choice-free `FinEnum` instances](#task-4-choice-free-finenum-instances)
  - [Task 5: Retire `BellantoniCook`'s local instances](#task-5-retire-bellantonicooks-local-instances)
  - [Task 6: The Cobham signature](#task-6-the-cobham-signature)
  - [Task 7: The evaluator](#task-7-the-evaluator)
  - [Task 8: `RecBounded`](#task-8-recbounded)
  - [Task 9: `SmashFree`](#task-9-smashfree)
  - [Task 10: `pred` and `cond`](#task-10-pred-and-cond)
  - [Task 11: Documentation and indices for the class](#task-11-documentation-and-indices-for-the-class)
  - [Task 12: `comb`](#task-12-comb)
  - [Task 13: `eqOne` and `isTree`](#task-13-eqone-and-istree)
  - [Task 14: Correctness](#task-14-correctness)
  - [Task 15: Conclude, document, and remove the transient artifacts](#task-15-conclude-document-and-remove-the-transient-artifacts)

<!-- END doctoc -->

**Goal:** Place the decision of `BinTree.Valid` in the functions
computable simultaneously in polynomial time and linear space, by
expressing the tree recognizer in a Cobham-style function algebra and
exhibiting it as smash-free.

**Architecture:** A second term algebra beside `BellantoniCook`, over
`SlicePFunctor ℕ ℕ` rather than `SlicePFunctor (ℕ × ℕ) (ℕ × ℕ)`: Cobham's
bitstring syntax of [HeraudNowak2011] § 3.1 extended by a concatenation
generator, with the `Rec` bound carried as a `RecProp` fold rather than
decided, and a `Bool`-fold `SmashFree` predicate selecting the smash-free
subalgebra. The recognizer transcribes onto it and re-proves its own
correctness; only `BinTree.depth_le_length` is shared with the existing
module.

**Tech Stack:** Lean 4 (v4.33.0-rc2), mathlib, `lake build`, `lake test`,
`lake lint`, `lake shake`.

## Global Constraints

- No `noncomputable`; minimise `Classical`. Both new modules are held to
  the axiom set `{propext, Quot.sound}` and are **not** added to
  `GebMeta.classicalAllowedModules`.
- All recursion and induction through recursors. No `induction` tactic, no
  self-calling `def`, no `termination_by`, no self-referential `inductive`.
- `Geb/Mathlib/` may import only `Mathlib.*`, `Batteries.*`,
  `Geb.Mathlib.*`. The prefix `Geb.Mathlib.` appears only on `^import`
  lines — never in `namespace`, declaration bodies, docstrings or comments.
- Every `.lean` file: `module` keyword after the copyright block, mathlib
  copyright header, module docstring with `# Title`, summary, and every
  mandatory section that has content, tags included; a `/-- … -/` docstring
  on every `def`, `structure`, `instance` and public-interest theorem.
- 100-column lines, two-space indent, `UpperCamelCase` for `Prop`/`Type`,
  `lowerCamelCase` for values, `snake_case` for theorems.
- No `sorry` in any commit. Underscores, not `sorry`, for holes in progress.
- Commit messages: `type(scope): imperative subject`, lowercase, no
  trailing period, type from
  `feat | fix | doc | style | refactor | test | chore | perf | ci`.
- `scripts/pre-push.sh` before any push; no push without line-by-line
  review by the user.
- VCS is `jj`. Never a mutating `git` subcommand.

## Declaration inventory

Every `Cobham` declaration the tasks produce, so that no task names one a
neighbour does not create. Arities are Cobham arities; "bound" is the
fourth child of a `boundedRec` node. The recognizer's shape mirrors
`BellantoniCook/Tree.lean` declaration for declaration, so each row's
model is the same name there.

| Declaration | Task | Arity | Shape | Bound |
| --- | --- | --- | --- | --- |
| `zeroAt n` | 12 | `n` | `Comp^n O ⟨⟩` | — |
| `oneAt n` | 12 | `n` | `Comp^n S₁ ⟨zeroAt n⟩` | — |
| `falseAt n` | 12 | `n` | `Comp^n S₀ ⟨zeroAt n⟩` | — |
| `inc` | 12 | 1 | `Comp¹ S₁ ⟨Π^0_1⟩` | — |
| `predPred` | 12 | 1 | `Comp¹ pred ⟨Comp¹ pred ⟨Π^0_1⟩⟩` | — |
| `combFalseStep` | 12 | 2 | `Comp² cond ⟨Π^1_2, falseAt 2, Comp² inc ⟨Π^1_2⟩, falseAt 2⟩` | — |
| `combTrueStep` | 12 | 2 | `Comp² cond ⟨Comp² predPred ⟨Π^1_2⟩, falseAt 2, Comp² pred ⟨Π^1_2⟩, Comp² pred ⟨Π^1_2⟩⟩` | — |
| `comb` | 12 | 1 | `boundedRec 0` over `oneAt 0`, `combFalseStep`, `combTrueStep` | `S₁` |
| `eqOneInner` | 13 | 1 | `Comp¹ cond ⟨Comp¹ pred ⟨Π^0_1⟩, oneAt 1, zeroAt 1, zeroAt 1⟩` | — |
| `eqOne` | 13 | 1 | `Comp¹ cond ⟨Π^0_1, zeroAt 1, eqOneInner, eqOneInner⟩` | — |
| `isTree` | 13 | 1 | `Comp¹ eqOne ⟨Comp¹ pred ⟨comb⟩⟩` | — |

Superseded by the three-tier note above. Each row also gets — `combOf : COf 1`,
`eqOneOf : COf 1`, `isTreeOf : COf 1` — and a meaning ascribed at its
reduced arity: `combSem`, `eqOneSem`, `isTreeSem`, each
`(C.eval _).2` at the arity written out, as
`BellantoniCook/Tree.lean` does and for the same reason (a meaning taken
through the `Sigma` projection has a type headed by that projection rather
than by an arrow, and `rw` under it fails). `predSem` and `condSem` are
the same for Task 10's two derived expressions.

`RecBounded` obligations: only `comb`, `pred` and `cond` carry a new
inequality. Every other row contains no `boundedRec` node, or contains one
only inside an already-discharged `pred`, `cond` or `comb`, so its
obligation is discharged by `recBounded_mk` over its children.

Three tiers per row, as `BellantoniCook/Tree.lean` has them: `…Raw` is the
tree, the plain name is the `C` — `⟨…Raw, by decide, by …⟩`, two proof
components, `sig.W` being itself a subtype, and the raw tree must be named
first or `by decide` fails with "declaration has metavariables" — and
`…Of : COf n` ascribes the reduced arity. `concatOf` and `smashOf` of Task
8 are that tier over one-node `concatRaw` and `smashRaw`. The meanings
`predSem`, `condSem`, `combSem`, `eqOneSem`, `isTreeSem` are `C.eval` at
the written arity; Task 12 also produces `combSem`'s three unfolding
lemmas and Task 13 `isTreeSem_apply`.

Paper notation to constructor: `O` is `zero`, `Π^i_n` is `proj n i`, `S_b`
is `succ b`, `Comp^n` is `comp n m`, `∗` is `concat`, `#` is `smash`,
`Rec` is `boundedRec n`.

## Bookmark order

`doc/todo-cobham-deferrals`, `feat/tree-depth-le-length` and
`refactor/finenum-sum-instance` branch from `main` directly;
`fix/bc-tree-polytime-citation` stacks on the first of those, for the
`DecidablePred Valid` instance its theorem needs, and `feat/cobham-class`
on the last; `feat/cobham-tree-recognizer` is a two-parent merge of that
chain and `feat/tree-depth-le-length`, whose `depth_le_length` Task 12
consumes.

| Bookmark | Tasks | Depends on |
| --- | --- | --- |
| `doc/todo-cobham-deferrals` | 1 | — |
| `feat/tree-depth-le-length` | 3 | — |
| `fix/bc-tree-polytime-citation` | 2 | `feat/tree-depth-le-length` |
| `refactor/finenum-sum-instance` | 4–5 | — |
| `feat/cobham-class` | 6–11 | `refactor/finenum-sum-instance` |
| `feat/cobham-tree-recognizer` | 12–15 | `feat/cobham-class`, `feat/tree-depth-le-length` |

The spec and this plan are already committed on `feat/cobham-class` and
are removed in the final commit of `feat/cobham-tree-recognizer`
(Task 15).

Create each bookmark at its parent, then start each task with a fresh
commit. `jj describe` rewrites the **current** commit's description rather
than creating one, so a task that ends with `jj describe` collapses into
its predecessor; every task below therefore *opens* with `jj new`.

```bash
# a bookmark rooted on main
jj new main -m "<first task's subject>"
jj bookmark create <name> -r @

# the chained bookmarks
jj new refactor/finenum-sum-instance -m "<Task 6's subject>"
jj bookmark create feat/cobham-class -r @
jj new feat/cobham-class feat/tree-depth-le-length -m "<Task 12's subject>"
jj bookmark create feat/cobham-tree-recognizer -r @
```

`feat/cobham-class` currently exists rooted on `main`, carrying the spec
and this plan; rebase it onto `refactor/finenum-sum-instance` once that
bookmark exists:

```bash
jj rebase -b feat/cobham-class -d refactor/finenum-sum-instance
```

Within a bookmark, each task is `jj new -m "<subject>"` before its edits.
The subjects given at each task's end are those `jj new` messages.

A bookmark is a static pointer: it does not follow the working copy as
later commits land, and `revsets.bookmark-advance-from` governs only
`jj commit`. On a bookmark holding several tasks, the second and later
commits are otherwise left unreferenced. After every task:

```bash
jj bookmark set <name> -r @
```

---

### Task 1: Record the four deferrals in `TODO.md`

**Bookmark:** `doc/todo-cobham-deferrals`

**Files:**

- Modify: `TODO.md` — § Next up, § Triggers, and
  § The Bellantoni-Cook tree recognizer's opening line
- Modify: `docs/references.bib` — add
  `BeckmannBussFriedmanMuellerThapen2017`

**Interfaces:**

- Consumes: nothing.
- Produces: nothing consumed by later tasks. Independent.

- [ ] **Step 1: Add the Route A item under § Next up**

Insert as a new item in `TODO.md` § The Bellantoni-Cook tree recognizer,
after its existing item 5, the § Deferred "Route A" bullet from the spec
verbatim, with its three constraints. It names
`Cslib.Computability.Machines.Turing.MultiTape.Deterministic`,
`ComputableInTimeAndSpace`, and `Turing.MultiTapeTM.indicator` in full, so
that it stands without the spec.

- [ ] **Step 2: Replace that section's opening line**

`TODO.md:527` currently reads "Five items over
`Geb/Mathlib/Computability/BellantoniCook/Tree.lean`." Route A is a sixth
and is not over that file. Replace with a sentence naming the property the
items share rather than counting them — a count over a population the
project keeps adding to is forbidden by
`docs/rules/markdown-writing.md` § Prose style.

- [ ] **Step 3: Add the two trigger entries under § Triggers**

The `Geb/Cslib/`-importing-`Geb.Mathlib.*` entry with its full seven-item
change set, and the recursion-combinator entry with its construction, law,
arities and the naming question. Each takes the form the section's
existing entries take — `- **<condition or subject>**: <action>` — with
the firing condition in the bold clause or in a trailing `Trigger: …`
sentence. No entry there opens with a bold `Trigger:` label.

- [ ] **Step 4: Add the spec-lifecycle item under § Next up**

The question CONTRIBUTING § Concern shape leaves open for a multi-branch
series and for a topic branch with two topic-branch parents.

- [ ] **Step 5: Add the bibliography entry**

`BeckmannBussFriedmanMuellerThapen2017` (already drafted in
`docs/references.bib` on `feat/cobham-class`; move it to this bookmark, as
this is the only text that cites it).

- [ ] **Step 6: Verify**

```bash
npx markdownlint-cli2 'TODO.md' && doctoc --update-only TODO.md && scripts/check-md-links.sh TODO.md
```

Expected: clean; `doctoc` reports no change or regenerates the TOC.

- [ ] **Step 7: Commit**

The task opened with `jj new -m` carrying this subject; nothing further is
needed unless the message changed:

```bash
jj describe -m "doc(todo): record the Cobham workstream's four deferrals"
```

---

### Task 2: Correct `BellantoniCook/Tree.lean`'s polytime citation

**Bookmark:** `fix/bc-tree-polytime-citation`

**Files:**

- Modify: `Geb/Mathlib/Computability/BellantoniCook/Tree.lean` — module
  docstring (lines 19–22 and its `## References`), plus a new theorem
- Modify: `GebTests/Mathlib/Computability/BellantoniCook/Tree.lean`
- Modify: `docs/index.md` — the `BellantoniCook/Tree.lean` entry

**Interfaces:**

- Consumes: nothing.
- Produces: `BellantoniCook.isTreeSem_eq_ite`. Not consumed by later tasks
  (the Cobham module proves its own analogue in Task 14).

**Why:** the docstring reads "`B` is a characterization of the
polynomial-time functions [BellantoniCook1992]". `Basic.lean`'s own
docstring records that the class formalized is [HeraudNowak2011] § 3.2's
reformulation and **not** [BellantoniCook1992]'s — the conditional takes
four safe arguments and branches three ways, and the recursion's base case
is the empty bitstring. The licence is [HeraudNowak2011] Theorems 1 and 2
composed with Cobham's theorem.

- [ ] **Step 1: Correct the docstring**

Replace the sentence with one attributing the characterization to
[HeraudNowak2011] Theorems 1 and 2 composed with Cobham's theorem, and add
`[HeraudNowak2011]` to the module docstring's `## References` list.

- [ ] **Step 2: Write the failing test**

Append to `GebTests/Mathlib/Computability/BellantoniCook/Tree.lean`:

```lean
/-- The recognizer's value on a spelling and on a non-spelling. -/
def isTreeIteCheck : Bool :=
  decide (BellantoniCook.isTreeSem ![[true, false, false]] ![] = [true]) &&
    decide (BellantoniCook.isTreeSem ![[true, false]] ![] = [])

example : isTreeIteCheck = true := by decide
```

Not `#guard`: `docs/rules/lean-coding.md` § Lean 4 module system records
that a `#guard` calling a non-`meta` declaration from another module of
this package fails at evaluation with "Could not find native
implementation", and needs a `public meta import` beside the ordinary one.
This value reduces in the kernel, so the module's own idiom — a named
`def` plus `by decide` — applies and no meta import is needed. Every
assertion already in this file takes that form.

- [ ] **Step 3: Run to verify it builds and the guard holds**

```bash
lake build GebTests.Mathlib.Computability.BellantoniCook.Tree
```

Expected: PASS. (This pins the two branches before the theorem generalises
them; if it fails, the branch values are not what the theorem will claim.)

- [ ] **Step 4: State and prove the theorem**

In `Geb/Mathlib/Computability/BellantoniCook/Tree.lean`, after
`isTreeSem_eq_singleton_iff_valid`:

```lean
/-- The recognizer is the indicator of `BinTree.Valid`: `[true]` on a
spelling and `[]` on anything else. `isTreeSem_eq_singleton_iff_valid`
pins the value only where it accepts. -/
theorem isTreeSem_eq_ite (w : List Bool) :
    isTreeSem ![w] ![] = if BinTree.Valid w then [true] else [] := by
  rw [isTreeSem_apply, eqOneSem_env, eqOneSem_eq, combSem_eq]
  by_cases h : BinTree.ok w = true
  · rw [if_pos h]
    simp only [List.tail_replicate, List.length_replicate, Nat.add_sub_cancel]
    by_cases hd : BinTree.depth w = 1
    · rw [if_pos hd, if_pos ⟨h, hd⟩]
    · rw [if_neg hd, if_neg (fun hv ↦ hd hv.2)]
  · rw [if_neg h, if_neg (by decide : ¬ ([false] : List Bool).tail.length = 1),
      if_neg (fun hv ↦ h hv.1)]
```

- [ ] **Step 5: Consume the decidability instance**

The theorem does **not** elaborate without it:
`failed to synthesize instance of type class Decidable (BinTree.Valid w)`.
`BinTree.Valid` is a `def` returning a conjunction, so instance search does
not unfold it. `DecidablePred Valid` therefore sits in
`Geb/Mathlib/Data/Tree/Preorder.lean` after `Valid`, added by Task 3 on
`feat/tree-depth-le-length`; this task consumes it and adds nothing to
`Preorder.lean`. Keeping the instance beside `depth_le_length` leaves
`Preorder.lean` edited by one bookmark and holds the facts about `Valid`
and `depth` that other modules consume together.

The instance body binds with `fun _ ↦`. A binder that is named but never
syntactically referenced trips `linter.unusedVariables`, which
`weak.warningAsError` makes a hard error; the anonymous binder and a named
binder that the body does reference both elaborate.

This bookmark therefore depends on `feat/tree-depth-le-length`: land that
one first, or rebase this one onto the resulting `main`.

- [ ] **Step 6: Build**

```bash
lake build Geb.Mathlib.Computability.BellantoniCook.Tree
```

Expected: PASS, and the theorem's proof body compiles verbatim as given.

- [ ] **Step 7: Add the main-statement and docs entries**

Add `isTreeSem_eq_ite` to the module docstring's `## Main statements`, and
extend `docs/index.md`'s `BellantoniCook/Tree.lean` bullet with one clause
naming it.

- [ ] **Step 8: Verify axioms**

```bash
lake lint
```

Expected: clean — `GebMeta.detectNonstandardAxiom` permits only
`{propext, Quot.sound}` here.

- [ ] **Step 9: Commit**

```bash
jj describe -m "fix(bellantoni-cook): attribute the polytime characterization correctly"
```

---

### Task 3: `BinTree.depth_le_length`

**Bookmark:** `feat/tree-depth-le-length`

**Files:**

- Modify: `Geb/Mathlib/Data/Tree/Preorder.lean` — after `depth_cons_true`
  (line 134), and the module docstring's `## Main statements`
- Modify: `GebTests/Mathlib/Data/Tree/Preorder.lean`
- Modify: `docs/index.md` — the `Data/Tree/Preorder.lean` entry (line 103)

**Interfaces:**

- Consumes: `BinTree.depth`, `depth_cons_false`, `depth_cons_true`.
- Produces: `BinTree.depth_le_length : ∀ w : List Bool, depth w ≤ w.length`.
  Task 14 consumes it.

- [ ] **Step 1: Write the failing test**

Append to `GebTests/Mathlib/Data/Tree/Preorder.lean`:

```lean
/-- The stack depth never exceeds the word length, at the extremes and at
a mixed word. -/
def depthLeLengthCheck : Bool :=
  decide (BinTree.depth [] ≤ ([] : List Bool).length) &&
    decide (BinTree.depth [false, false, false] ≤ 3) &&
    decide (BinTree.depth [true, false, false] ≤ 3)

example : depthLeLengthCheck = true := by decide
```

Not `#guard`, for the reason Task 2 gives. This check is a sanity anchor
on `depth`, not a red test: it holds whether or not `depth_le_length` is
provable, and Step 2 expects it to pass. The lemma's own failure mode is a
build error at Step 4, which is where the red-green cycle actually sits
for a proof obligation.

- [ ] **Step 2: Run to verify it builds**

```bash
lake build GebTests.Mathlib.Data.Tree.Preorder
```

Expected: PASS.

- [ ] **Step 3: Write the lemma**

In `Geb/Mathlib/Data/Tree/Preorder.lean`, after `depth_cons_true`:

```lean
/-- The stack depth never exceeds the word length. A leaf bit raises the
depth by one and consumes one bit; a node bit lowers it, the subtraction
being truncated at zero. -/
theorem depth_le_length (w : List Bool) : depth w ≤ w.length :=
  List.rec (motive := fun u ↦ depth u ≤ u.length) (Nat.le_refl 0)
    (fun b v ih ↦ by
      cases b
      · rw [depth_cons_false, List.length_cons]
        omega
      · rw [depth_cons_true, List.length_cons]
        omega)
    w
```

- [ ] **Step 4: Build**

```bash
lake build Geb.Mathlib.Data.Tree.Preorder
```

Expected: PASS. `omega` closes both branches: `depth v ≤ v.length` gives
`depth v + 1 ≤ v.length + 1`, and `depth v - 1 ≤ depth v ≤ v.length ≤
v.length + 1` with truncated subtraction.

- [ ] **Step 5: Add the main-statement and docs entries**

Add `BinTree.depth_le_length` to that module's `## Main statements`, and
one clause to its `docs/index.md` bullet.

- [ ] **Step 6: Verify**

```bash
lake build && lake build GebTests && lake test && lake lint && lake lint -- GebTests
lake shake --add-public --keep-implied --keep-prefix Geb GebTests
scripts/lint-imports.sh && markdownlint-cli2 '**/*.md' && doctoc --dryrun --update-only . && scripts/check-md-links.sh
```

Expected: all clean.

- [ ] **Step 7: Commit**

The task opened with `jj new -m` carrying this subject; nothing further is
needed unless the message changed:

```bash
jj describe -m "feat(tree): bound the preorder stack depth by the word length"
```

---

### Task 4: Choice-free `FinEnum` instances

**Bookmark:** `refactor/finenum-sum-instance`

**Files:**

- Modify: `Geb/Mathlib/Data/FinEnum.lean` — three `scoped instance`s,
  `public import Mathlib.Logic.Equiv.Fin.Basic` for `finSumFinEquiv`,
  which `Mathlib.Data.FinEnum`'s import closure does not supply, and
  the module docstring's title, `## Main definitions` and `## Tags`
- Modify: `GebTests/Mathlib/Data/FinEnum.lean`

**Interfaces:**

- Consumes: mathlib's `FinEnum`, `finOneEquiv`, `finSumFinEquiv`,
  `Equiv.sumCongr`.
- Produces, all `scoped` in `namespace FinEnum`:
  - `FinEnum.unit : FinEnum Unit`
  - `FinEnum.finFin (n : ℕ) : FinEnum (Fin n)`
  - `FinEnum.finSum {α β} [FinEnum α] [FinEnum β] : FinEnum (α ⊕ β)`

  Task 5 and Task 6 consume all three.

**Why mathlib's will not do:** `FinEnum.punit` and `FinEnum.sum` both route
through `FinEnum.ofList`, whose `Equiv` field carries proofs that depend on
`Classical.choice`. Measured at v4.33.0-rc2 in the consuming closure:
`FinEnum Unit` and `FinEnum (Unit ⊕ Fin 3)` are
`{propext, Classical.choice, Quot.sound}`; the hand-built versions are
`{propext}` and `{propext, Quot.sound}`.

- [ ] **Step 1: Write the failing test**

Append to `GebTests/Mathlib/Data/FinEnum.lean`:

```lean
open scoped FinEnum in
/-- The enumerations have the cardinalities the instances declare. -/
def finEnumCardCheck : Bool :=
  decide (FinEnum.card Unit = 1) &&
    decide (FinEnum.card (Fin 4) = 4) &&
    decide (FinEnum.card (Unit ⊕ Fin 3) = 4)

example : finEnumCardCheck = true := by decide
```

- [ ] **Step 2: Run to see that it does not discriminate**

```bash
lake build GebTests.Mathlib.Data.FinEnum
```

Expected: PASS, on mathlib's instances alone. The cardinalities are right
either way, and `open scoped` on a namespace with no scoped members is
silent. The property this branch exists to establish is not the
cardinality but the axiom set, and the check that discriminates is
`lake lint -- GebTests` at Step 5 — `lake lint` alone lints `Geb` only
(`lintDriverArgs = ["Geb"]`), so the bare form would never see the test
module's `def`s.

- [ ] **Step 3: Write the instances**

In `Geb/Mathlib/Data/FinEnum.lean`, inside `namespace FinEnum`:

```lean
/-- A choice-free `FinEnum Unit`. `scoped`, so that it does not compete
with mathlib's `FinEnum.punit`, which is derived through `FinEnum.ofList`
and depends on `Classical.choice`. -/
scoped instance unit : FinEnum Unit where
  card := 1
  equiv := finOneEquiv.symm
  decEq := inferInstance

/-- A choice-free `FinEnum (Fin n)`: the cardinality is `n` and the
enumeration is the identity. `scoped`, for the same reason as `unit`. -/
scoped instance finFin (n : ℕ) : FinEnum (Fin n) where
  card := n
  equiv := Equiv.refl _
  decEq := inferInstance

/-- A choice-free `FinEnum` on a sum. `scoped`, for the same reason as
`unit`; mathlib's `FinEnum.sum` takes the `ofList` route. -/
scoped instance finSum {α β : Type*} [FinEnum α] [FinEnum β] :
    FinEnum (α ⊕ β) where
  card := FinEnum.card α + FinEnum.card β
  equiv := (Equiv.sumCongr (FinEnum.equiv) (FinEnum.equiv)).trans finSumFinEquiv
  decEq := inferInstance
```

- [ ] **Step 4: Run to verify it passes**

```bash
lake build GebTests.Mathlib.Data.FinEnum
```

Expected: PASS.

- [ ] **Step 5: Measure the axioms**

Add temporarily to the test module and then delete:

`#print axioms` takes an identifier, so name the instance first:

```lean
open scoped FinEnum in
/-- The composite instance the Cobham signature will resolve. -/
@[instance_reducible] def finEnumSumProbe : FinEnum (Unit ⊕ Fin 3) :=
  inferInstance

#print axioms finEnumSumProbe
```

Expected: `[propext, Quot.sound]`. Without `open scoped FinEnum` it is
`[propext, Classical.choice, Quot.sound]`; confirm both.

Keep `finEnumSumProbe` rather than deleting it. It is the branch's
permanent guard: `lake lint -- GebTests` fails on it if a later change
lets mathlib's instances win resolution, which is the regression this
branch exists to prevent and which nothing else would catch.

```bash
lake lint -- GebTests
```

- [ ] **Step 6: Update `docs/index.md`**

Its `Geb/Mathlib/Data/FinEnum.lean` entry reads "three choice-free
`Decidable` instances" and enumerates them. The branch adds three
`FinEnum` instances to the same file, so the entry misdescribes it, and
the count is over a population the project keeps adding to, which
`docs/rules/markdown-writing.md` § Prose style forbids. Restate as the
property the instances share.

- [ ] **Step 7: Update the module docstring**

Its title is "# Choice-free decidability over a `FinEnum`", its
`## Main definitions` lists three `Decidable` instances and its `## Tags`
is "FinEnum, decidability, constructive". All three are now incomplete.
Retitle to cover choice-free `FinEnum` instances as well as choice-free
decidability, add the three instances to `## Main definitions`, and extend
`## Tags`.

- [ ] **Step 8: Commit**

The task opened with `jj new -m` carrying this subject; nothing further is
needed unless the message changed:

```bash
jj describe -m "feat(finenum): add choice-free FinEnum instances for Unit, Fin and sums"
```

---

### Task 5: Retire `BellantoniCook`'s local instances

**Bookmark:** `refactor/finenum-sum-instance`

**Files:**

- Modify: `Geb/Mathlib/Computability/BellantoniCook/Basic.lean` — delete
  `finEnumFin` (line 167) and `finEnumCompDirection` (line 175), add the
  import and `open scoped`, update `sigFinitary` and the module docstring
- Modify: `docs/index.md` — the axiom sentence naming
  `finEnumCompDirection` (line ~229)
- Modify: `TODO.md` — delete the discharged trigger (lines ~867–871)

**Interfaces:**

- Consumes: Task 4's `FinEnum.unit`, `FinEnum.finFin`, `FinEnum.finSum`.
- Produces: `BellantoniCook.sigFinitary` unchanged in type, now resolved
  through the shared instances.

**Trigger discharged:** `TODO.md` records "A second consumer of
`BellantoniCook.finEnumFin` **or** `finEnumCompDirection` appears: move
them to `Geb/Mathlib/Data/FinEnum.lean`." Task 6 is a second consumer of
`finEnumFin`, so it fires as written.

- [ ] **Step 1: Add the import and the open**

In `Geb/Mathlib/Computability/BellantoniCook/Basic.lean`, after the
existing `public import` lines:

```lean
public import Geb.Mathlib.Data.FinEnum
```

and after the `namespace BellantoniCook` line:

```lean
open scoped FinEnum
```

Without the `open scoped`, mathlib's instances win resolution and every
`by decide` in `Tree.lean` acquires `Classical.choice`, which surfaces only
at `lake lint`.

- [ ] **Step 2: Delete the two local instances**

Remove `scoped instance finEnumFin` and `scoped instance
finEnumCompDirection` in their entirety, docstrings included.

- [ ] **Step 3: Rewrite `sigFinitary`'s `comp` branch**

The three-way sum now resolves by two applications of `finSum`:

```lean
  | .comp _ _ m k => inferInstanceAs (FinEnum (Unit ⊕ Fin m ⊕ Fin k))
```

is unchanged in text; only the instances it finds change. Keep the
explicit `inferInstanceAs` ascriptions — the existing docstring records
that instance search stops at reducible transparency on `sig.B a`, so a
bare `inferInstance` does not find them.

- [ ] **Step 4: Build and measure**

```bash
lake build Geb.Mathlib.Computability.BellantoniCook.Tree && lake lint
```

Expected: PASS and clean. If `lake lint` reports `Classical.choice`, the
`open scoped FinEnum` is missing or is inside the wrong scope.

- [ ] **Step 5: Update the docstrings and indices**

`Basic.lean`'s module docstring describes the two deleted instances and why
they were `scoped`; rewrite that paragraph to point at
`Geb/Mathlib/Data/FinEnum.lean` and to record the `open scoped`
requirement. Update `docs/index.md`'s axiom sentence, which names
`finEnumCompDirection`. Delete the `TODO.md` trigger.

`TODO.md` § Concrete-syntax prototype separately schedules
`Geb.finEnumFin` and `Geb.finEnumEmpty` into the same file. Task 4's
instances subsume `Geb.finEnumFin` only — `FinEnum Empty` follows from
neither `unit` nor `finSum`. Note that in the § Concrete-syntax prototype
item rather than deleting it.

- [ ] **Step 6: Verify**

```bash
lake build && lake build GebTests && lake test && lake lint && lake lint -- GebTests
lake shake --add-public --keep-implied --keep-prefix Geb GebTests
scripts/lint-imports.sh && markdownlint-cli2 '**/*.md' && doctoc --dryrun --update-only . && scripts/check-md-links.sh
```

- [ ] **Step 7: Commit**

The task opened with `jj new -m` carrying this subject; nothing further is
needed unless the message changed:

```bash
jj describe -m "refactor(bellantoni-cook): use the shared choice-free FinEnum instances"
```

---

### Task 6: The Cobham signature

**Bookmark:** `feat/cobham-class`

**Files:**

- Create: `Geb/Mathlib/Computability/Cobham/Basic.lean`
- Create: `Geb/Mathlib/Computability/Cobham.lean`
- Modify: `Geb/Mathlib/Computability.lean`

**Interfaces:**

- Consumes: `SlicePFunctor` (`Geb.Mathlib.Data.PFunctor.Slice.W`),
  `Finitary` (`…Univariate.Finitary`), Task 4's `FinEnum` instances,
  `Mathlib.Logic.Equiv.Fin.Basic` for `Fin.cons`, and
  `Geb.Mathlib.Data.PFunctor.Slice.Decidable` for `decidableWValid`. The
  last is needed from Task 10, which commits the first `⟨_, by decide⟩`
  terms; `BellantoniCook/Basic.lean` commits none and so does not import
  it. Import it here rather than adding an import mid-module.
- Produces:
  - `Cobham.Shape` with constructors `zero`, `proj (n : ℕ) (i : Fin n)`,
    `succ (b : Bool)`, `smash`, `concat`, `comp (n m : ℕ)`,
    `boundedRec (n : ℕ)`. **Not** `rec`: the auto-generated recursor owns
    that name and the kernel rejects the `inductive` with "constant has
    already been declared". `recOn`, `casesOn`, `brecOn`, `below`,
    `noConfusion` and `toCtorIdx` are reserved for the same reason.
  - `Cobham.Direction : Shape → Type`
  - `Cobham.rc : (a : Shape) → Direction a → ℕ`
  - `Cobham.q : Shape → ℕ`
  - `Cobham.sig : SlicePFunctor ℕ ℕ`
  - `Cobham.sigFinitary : sig.toPFunctor.Finitary`

**Template:** `Geb/Mathlib/Computability/BellantoniCook/Basic.lean`
lines 100–190 are the worked model. The deltas, and only these:

| | `BellantoniCook` | `Cobham` |
| --- | --- | --- |
| index | `ℕ × ℕ` | `ℕ` |
| `comp` directions | `Unit ⊕ Fin m ⊕ Fin k` | `Unit ⊕ Fin m` |
| recursion node | `safeRec`, `Fin 3` | `boundedRec`, `Fin 4` |
| arity relation | normal/safe pair | `a_h = a_g + 2 = a_j + 1` |
| generators | `succ b`, `pred`, `cond` | `succ b`, `smash`, `concat` |

- [ ] **Step 1: Write the signature**

`Direction`: `Fin 0` for `zero`, `proj`, `succ`, `smash` and `concat`;
`Unit ⊕ Fin m` for `comp`; `Fin 4` for `boundedRec`. `smash` and `concat`
are generators: their arity `2` comes from `q`, and they have no subterms,
exactly as `pred` and `cond` have `Fin 0` directions in
`BellantoniCook/Basic.lean`. Their `rc` clauses are `i.elim0`, without
which the match is non-exhaustive.

`q`: `0` for `zero`; `n` for `proj n _`; `1` for `succ`; `2` for `smash`
and `concat`; `n` for `comp n _`; `n + 1` for `boundedRec n`.

`rc` for `boundedRec n`, which is the whole arity relation — with
`a_j = n + 1`, `a_g = n`, `a_h = n + 2`, in the child order base, `h₀`,
`h₁`, bound:

```lean
  | .boundedRec n, ⟨0, _⟩ => n
  | .boundedRec n, ⟨1, _⟩ => n + 2
  | .boundedRec n, ⟨2, _⟩ => n + 2
  | .boundedRec n, _ => n + 1
```

`rc` for `comp n m`: `m` at `.inl ()`, `n` at `.inr _`.

Write `sig` exactly as `BellantoniCook/Basic.lean:159` does, and
`sigFinitary` with one branch per constructor, each an explicit
`inferInstanceAs` — a bare `inferInstance` does not find them, instance
search stopping at reducible transparency on `sig.B a`.

`@[expose, reducible]` on `Direction`, `rc` and `q`; `@[expose]` on `sig`,
as the template has them. Removing an `@[expose]` fails
at `lake build`, not at the language server.

- [ ] **Step 2: Write the module docstring**

`lakefile.toml` sets `weak.linter.style.header = true` under
`weak.warningAsError`, so the module docstring must be present at the
first build, not deferred to Task 11. Write it now with every mandatory
section that has content; Task 11 revises it once the module's contents
are complete.

- [ ] **Step 3: Write the index files**

`Geb/Mathlib/Computability/Cobham.lean` with a module docstring and
`public import Geb.Mathlib.Computability.Cobham.Basic`; add
`public import Geb.Mathlib.Computability.Cobham` to
`Geb/Mathlib/Computability.lean`.

- [ ] **Step 4: Build**

```bash
lake build Geb.Mathlib.Computability.Cobham.Basic
```

Expected: PASS.

- [ ] **Step 5: Commit**

```bash
jj describe -m "feat(cobham): add the signature of Cobham's bitstring class"
```

---

### Task 7: The evaluator

**Bookmark:** `feat/cobham-class`

**Files:**

- Modify: `Geb/Mathlib/Computability/Cobham/Basic.lean`

**Interfaces:**

- Consumes: Task 6's `sig`.
- Produces:
  - `Cobham.Sem : ℕ → Type := fun n ↦ (Fin n → List Bool) → List Bool`
  - `Cobham.transport {i j : ℕ} (h : i = j) (v : Sem i) : Sem j`
  - `Cobham.evalRec {n : ℕ} (g : Sem n) (h₀ h₁ : Sem (n + 2)) :
    List Bool → Sem n`
  - `Cobham.evalValue`, `Cobham.evalStep`
  - `Cobham.eval : sig.W → Σ n, Sem n` and
    `Cobham.arity : sig.W → ℕ := sig.wIndex`

  `C` and `COf` are not defined here: they carry `RecBounded`, which
  Task 8 introduces. This task's evaluator is over the raw `sig.W`.

  `@[expose]` on `Sem`, `transport`, `evalRec`, `evalValue`, `evalStep`,
  `eval` and `arity`, as the template carries it on their counterparts.
  Task 8's `C`, `C.arity`, `COf` and `C.eval` take it too: without it on
  `C`, Task 9's `e.1.1` projection fails with "`C` … is not a
  one-constructor inductive type".

**Template:** `BellantoniCook/Basic.lean` lines 213–290. One environment
rather than two throughout. `evalValue` stays separate from `evalStep`
because the match on `Shape` must generalize the compatibility hypothesis,
which arrives bundled.

- [ ] **Step 1: Write `Sem`, `transport`, `evalRec`**

`evalRec` recurses on the **first** argument by `List.rec`, matching
[HeraudNowak2011]'s `Rec` (`f(y·i, x) = h_i(y, f(y,x), x)`), not
[Strahm2003]'s last-argument form:

```lean
@[expose] def evalRec {n : ℕ} (g : Sem n) (h₀ h₁ : Sem (n + 2)) :
    List Bool → Sem n :=
  List.rec g (fun b v ih x ↦
    (if b then h₁ else h₀) (Fin.cons v (Fin.cons (ih x) x)))
```

- [ ] **Step 2: Write the generator semantics inside `evalValue`**

`zero ↦ fun _ ↦ []`; `proj n i ↦ fun x ↦ x i`; `succ b ↦ fun x ↦ b :: x 0`
— the Lean head is the word's **last** bit, so `S_b(x) = xb` prepends here;
`concat ↦ fun x ↦ x 1 ++ x 0`, which is the one clause where the bit-order
convention can silently invert; `smash ↦ fun x ↦ true ::
List.replicate ((x 0).length * (x 1).length) false`, so
`|#(a,b)| = |a|·|b| + 1`.

- [ ] **Step 3: Build**

```bash
lake build Geb.Mathlib.Computability.Cobham.Basic
```

- [ ] **Step 4: Write the smoke test**

Create `GebTests/Mathlib/Computability/Cobham/Basic.lean` and
`GebTests/Mathlib/Computability/Cobham.lean`, add the plain `import` to
`GebTests/Mathlib/Computability.lean`, and check `concat` and `smash` on
literals — `concat` under the head-is-last-bit convention and `smash`'s
length. Follow `GebTests/Mathlib/Computability/BellantoniCook/Basic.lean`
for the shape, including a named `def` with a value so `lake shake` has an
anchor.

- [ ] **Step 5: Build and commit**

```bash
lake build && jj describe -m "feat(cobham): interpret the signature"
```

---

### Task 8: `RecBounded`

**Bookmark:** `feat/cobham-class`

**Files:**

- Modify: `Geb/Mathlib/Computability/Cobham/Basic.lean`
- Modify: `GebTests/Mathlib/Computability/Cobham/Basic.lean`

**Interfaces:**

- Consumes: Task 7's `eval`, and `SlicePFunctor.W.RecProp`,
  `recProp_mk`, `comp_elim` from `Geb/Mathlib/Data/PFunctor/Slice/W.lean`.
- Produces:
  - `Cobham.RecBoundedValue` — the one-node condition
  - `Cobham.RecBounded : sig.W → Prop`
  - `Cobham.fst_eval (z : sig.W) : (eval z).1 = arity z` — the pointwise
    form of `SlicePFunctor.W.comp_elim`, composed with `arity := wIndex`.
  - `Cobham.recBounded_mk` — the raw-form introduction lemma, taking the
    child index equation `∀ b, (eval (c b)).1 = rc a b` as an explicit
    hypothesis; the proof still closes by `rfl`, `Prop` hypotheses being
    definitionally irrelevant to the iota-reduction.
  - `Cobham.C : Type := { e : sig.W // RecBounded e }`, first defined here
  - `Cobham.C.arity : C → ℕ := fun e ↦ Cobham.arity e.1` — the qualified
    name is not stylistic: inside the `Cobham.C` namespace an unqualified
    `arity` resolves to the declaration being defined, giving a
    termination failure and a `sig.W`-vs-`C` mismatch; record this as a
    compiler-forced exception to `docs/rules/lean-coding.md` § Naming.
  - `Cobham.COf (n : ℕ) : Type := { e : C // e.arity = n }`
  - `Cobham.C.eval : (e : C) → Sem (C.arity e)`, whose body reads
    `Cobham.eval e.1` for the same reason. **Not** definable as
    `(Cobham.eval e.1).2`: that has type `Sem (Cobham.eval e.1).1`, and
    `Sigma.fst ∘ eval = wIndex` is `SlicePFunctor.W.comp_elim`, a `funext`
    theorem rather than a definitional equality. It is
    `transport (fst_eval e.1) (Cobham.eval e.1).2`, and the step that
    writes it must show that transport.
  - `Cobham.concatOf`, `Cobham.smashOf : COf 2`, the one-node terms over
    named raw trees `concatRaw` and `smashRaw`, each admissible and
    `RecBounded` vacuously via `recBounded_mk`, since neither shape is
    `boundedRec`. Task 9's test consumes both.

  The raw tree of a `COf n` therefore sits at `e.1.1.1`; `SmashFree` in
  Task 9 projects to `e.1.1` from a `C`.

**Model:** `Geb/Mathlib/Data/PFunctor/Presheaf/W.lean`'s
`IsHereditarilyNatural` instantiates `RecProp` in exactly this pattern,
including the `compatible_iff … .mp x.2` idiom and the `∀ b, ih b`
conjunct.

- [ ] **Step 1: Write `RecBoundedValue` and `fst_eval`**

Takes the shape, the children as `sig.W`, and the index equation
`∀ b, (eval (c b)).1 = rc a b` — a statement about `eval`'s index, not
about arity. It is `True` for every shape but `boundedRec`; at
`boundedRec n` it is
`∀ (x : Fin (n+1) → List Bool), (evalRec … x).length ≤ (bound … x).length`,
with each child's meaning obtained by `transport` along that index
equation. `Prop`-valued, so `UpperCamelCase`. The `Step` suffix is wrong
here: `evalStep`, `wValidStep` and `wIndexStep` all name the **bundled**
half, which is what `RecProp` receives; this is the unbundled half
`evalValue` names.

Also prove `fst_eval (z : sig.W) : (eval z).1 = arity z`, the pointwise
form of `SlicePFunctor.W.comp_elim` (`Sigma.fst ∘ eval = wIndex`)
composed with `arity := wIndex`. Step 2 and `C.eval` both consume it.

- [ ] **Step 2: Write `RecBounded` through `RecProp`**

The step receives `x : sig.toSliceDomPFunctor.Obj sig.wIndex`, whose
`x.1.2 : sig.B x.1.1 → sig.W` are trees, so `eval` applies to them.
Relate a child's evaluated index to its `wIndex` by `fst_eval` before
transporting — the index equation does **not** arrive free from
`compatible_iff` here, unlike in `evalValue`. Conjoin `∀ b, ih b` for
hereditariness.

- [ ] **Step 3: Write `recBounded_mk`**

State it in raw form at `⟨WType.mk a f, h⟩` rather than at `W.mk x`: every
committed term is already destructured, so `WType.rec` iota-reduces and
the lemma closes by bare `rfl`. (`recProp_mk` needs its `obtain` only
because its subject is `W.mk x` at a bundled `x`.) Its signature takes the
child index equation `∀ b, (eval (f b)).1 = rc a b` as an explicit
hypothesis; binding it explicitly does not block the `rfl`, `Prop`
hypotheses being definitionally irrelevant to the reduction. `concatOf`
and `smashOf` are its first uses: each closes by `recBounded_mk`
trivially, no `boundedRec` node being present.

- [ ] **Step 4: Write the smoke test**

In `GebTests/Mathlib/Computability/Cobham/Basic.lean`, assert `concatOf`'s
and `smashOf`'s arities by `decide`. This exercises the six declarations
this task adds — nothing else in the module does.

- [ ] **Step 5: Build**

```bash
lake build Geb.Mathlib.Computability.Cobham.Basic
lake build GebTests.Mathlib.Computability.Cobham.Basic
```

Expected: PASS. `RecBounded` is a `Prop` in a subtype, so it is erased and
does not obstruct reduction; it is never decided.

- [ ] **Step 6: Commit**

```bash
jj describe -m "feat(cobham): carry the recursion bound as a hereditary fold"
```

---

### Task 9: `SmashFree`

**Bookmark:** `feat/cobham-class`

**Files:**

- Modify: `Geb/Mathlib/Computability/Cobham/Basic.lean`
- Modify: `GebTests/Mathlib/Computability/Cobham/Basic.lean`

**Interfaces:**

- Consumes: Task 6's `sig`; Task 8's `concatOf`, `smashOf`.
- Produces: `Cobham.smashFreeBool : sig.toPFunctor.W → Bool` and
  `Cobham.SmashFree (e : C) : Prop := smashFreeBool e.1.1 = true`.
  Task 15 consumes it.

**One artifact, not two.** `SmashFree` is the `Bool` equation itself, so
there is no `_eq_true_iff` bridge to state. `SlicePFunctor.wValidBool` is
the shape it follows, not a lemma it reuses — that one is about
admissibility alone.

- [ ] **Step 1: Write the test**

`concatOf` and `smashOf` are the two one-node committed terms Task 8 adds
for this purpose — over named raw trees `concatRaw` and `smashRaw`, both
`RecBounded` vacuously. Each is a `COf 2`, not a `C`, so `SmashFree` needs
the `.1` projection.

```lean
open scoped FinEnum in
/-- A smash node is rejected wherever it sits. -/
def smashFreeCheck : Bool :=
  decide (Cobham.SmashFree Cobham.concatOf.1) &&
    decide (¬ Cobham.SmashFree Cobham.smashOf.1)

example : smashFreeCheck = true := by decide
```

Any further `sig.WValid` witness this step introduces as a standalone
declaration must be a `theorem`, not a `def`: `linter.defProp` rejects a
`Prop`-valued `def`.

- [ ] **Step 2: Write the fold**

```lean
/-- Whether no `smash` node occurs anywhere in a raw tree. -/
@[expose] def smashFreeBool : sig.toPFunctor.W → Bool :=
  WType.elim Bool fun x ↦
    match x with
    | ⟨.smash, _⟩ => false
    | ⟨_, c⟩ => decide (∀ b, c b = true)
```

```lean
/-- An expression of the subalgebra `[ε, I, s₀, s₁, ∗; COMP, BRN]`, which
[Strahm2003] Theorem 1(2) contains in the functions computable
simultaneously in polynomial time and linear space. Hereditary: a
top-node test would not exclude `#` from subterms. -/
@[expose] def SmashFree (e : C) : Prop := smashFreeBool e.1.1 = true
```

- [ ] **Step 3: Supply decidability**

```lean
instance (e : C) : Decidable (SmashFree e) :=
  inferInstanceAs (Decidable (smashFreeBool e.1.1 = true))
```

A bare `inferInstance` does **not** see through the definition — measured.

- [ ] **Step 4: Run to verify it passes**

```bash
lake build GebTests.Mathlib.Computability.Cobham.Basic
```

- [ ] **Step 5: Commit**

```bash
jj describe -m "feat(cobham): decide freedom from the smash generator"
```

---

### Task 10: `pred` and `cond`

**Bookmark:** `feat/cobham-class`

**Files:**

- Modify: `Geb/Mathlib/Computability/Cobham/Basic.lean`
- Modify: `GebTests/Mathlib/Computability/Cobham/Basic.lean`

**Interfaces:**

- Consumes: Tasks 6–8.
- Produces: `Cobham.pred : COf 1`, `Cobham.cond : COf 4`,
  `Cobham.predSem_eq`, `Cobham.condSem_eq`. Tasks 12–14 consume all four.

**Transcribe, do not re-derive.** [HeraudNowak2011] § 4 gives
`pred = Rec O Π^0_2 Π^0_2 Π^0_1` and
`cond = Rec Π^0_3 Π^4_5 Π^3_5 j`. `Rec` peels the last bit, so `Π^4_5`
fires on `s₀` and `Π^3_5` on `s₁`; under the head-is-last-bit convention
that is the Lean `false :: _ ↦ y 3`, `true :: _ ↦ y 2`, matching
`BellantoniCook`'s `evalValue` exactly. It is transposed against
[HeraudNowak2011] § 3.2's **prose** for `B`, which is why the paper's own
`B` clause cannot be used to check it; `BellantoniCook/Basic.lean`'s
docstring records that this repository follows the authors' Coq ordering,
and § 4 is on that side. Re-deriving `h₀`/`h₁` from the semantics is the
likeliest way to land them swapped, and `cond` is the scrutinee dispatch
inside both `comb` steps.

- [ ] **Step 1: Write `pred` with its bound `Π^0_1`**

Mark it a transcription in its docstring, citing [HeraudNowak2011] § 4.
`RecBounded` obligation: `|f(y·i)| = |y| ≤ |y·i|` and `|f(ε)| = 0`. Also
define `predSem := transport pred.2 pred.1.eval`, the term's own arity
proof `pred.2` being `rfl`, so the transport is trivial; `predSem_eq`
below is stated over it.

- [ ] **Step 2: Write `predSem_eq`**

```lean
/-- The predecessor drops the word's last bit, which is the Lean list's
head. -/
theorem predSem_eq (u : List Bool) : predSem ![u] = u.tail := by
  match u with
  | [] => rfl
  | b :: v => cases b <;> rfl
```

- [ ] **Step 3: Write `cond` with its smash-free bound**

The bound is the concatenation of the three **branch** arguments, the
scrutinee projected away: `Comp⁴ ∗ ⟨Comp⁴ ∗ ⟨Π¹₄, Π²₄⟩, Π³₄⟩`, seven nodes,
making `cond` eleven with its `boundedRec` node and three children; it
evaluates to `x 3 ++ (x 2 ++ x 1)`, `++` left-associative. It dominates
because the value is one of `x`, `y`, `z` and
`|x ∗ y ∗ z| = |x| + |y| + |z|`. [HeraudNowak2011] uses
`#(S₁x, #(S₁y, S₁z))`, the `S₁` wrappers keeping that bound non-degenerate
at `ε`; only the smash-free replacement is novel, and its docstring says
so.

Also define `condSem := transport cond.2 cond.1.eval`, the term's own
arity proof `cond.2` being `rfl`, matching `predSem`.

A `boundedRec` node's direction is `Fin 4` regardless of `n`, but at the
goal it presents with type `sig.B (dest …).fst` rather than a bare
`Fin 4` — there is no `OfNat` instance at that type — so a literal-pattern
match on the four children does not elaborate directly; `refine
fun b : Fin 4 ↦ ?_` first, then match on `b`.

- [ ] **Step 4: Write `condSem_eq`**

Three cases on the scrutinee, matching `BellantoniCook`'s `evalValue`
`.cond` but over this algebra's single environment `x`: `[] ↦ x 1`,
`true :: _ ↦ x 2`, `false :: _ ↦ x 3`. Where the goal needs restating, use
`change`, not `show`: `linter.style.show` rejects a `show` that changes
the goal.

- [ ] **Step 5: Build and test**

```bash
lake build && lake lint
```

Expected: PASS, `{propext, Quot.sound}`. Both `RecBounded` obligations are
discharged from the `Sem` equations above plus `List.length_tail` and
`List.length_append` — `omega` or explicit cases where `ℕ` arithmetic
appears, per `docs/rules/lean-coding.md` § Constructive-only Lean code.

- [ ] **Step 6: Commit**

```bash
jj describe -m "feat(cobham): derive the predecessor and the conditional"
```

---

### Task 11: Documentation and indices for the class

**Bookmark:** `feat/cobham-class`

**Files:**

- Modify: `Geb/Mathlib/Computability/Cobham/Basic.lean` — module docstring
- Modify: `docs/index.md`
- Modify: `TODO.md` — § Bellantoni-Cook item 3 and its opening line

- [ ] **Step 1: Write the module docstring**

Every mandatory section that has content, tags included. It records: the
bit-order convention (`S_b` appends, `Rec` peels the last bit, the Lean
head is the word's last bit, and `∗` is `fun x ↦ x 1 ++ x 0`); the
`@[expose]` dependency; the `open scoped FinEnum` requirement; and cites
`[Strahm2003]`, `[Strahm2010]`, `[Clote1999]`, `[HeraudNowak2011]`,
`[Thompson1972]`, `[Ritchie1963]`, `[Cobham1965]`, `[Bellantoni1992]`. It
names declarations, never repository paths.

- [ ] **Step 2: Add the `docs/index.md` entry**

- [ ] **Step 3: Rewrite `TODO.md` item 3**

Its class half is discharged here. Rewrite to the translations of Theorems
1 and 2 alone, recording that they additionally need a `∗` case in the
`C → B` direction, and whether the stated dependence on items 1 and 2 still
holds. Restate the section's opening line — which scopes its items to
`BellantoniCook/Basic.lean`, and which its own item 1 already falsifies —
as covering each item's own destination. Extend `TODO.md`'s
attested-locators trigger to name `[Thompson1972]`, `[Ritchie1963]`,
`[Cobham1965]` and `[Bellantoni1992]`.

- [ ] **Step 4: Verify and commit**

```bash
lake build && lake build GebTests && lake test && lake lint && lake lint -- GebTests
lake shake --add-public --keep-implied --keep-prefix Geb GebTests
scripts/lint-imports.sh && markdownlint-cli2 '**/*.md' && doctoc --dryrun --update-only . && scripts/check-md-links.sh
scripts/pre-push.sh
```

```bash
jj describe -m "doc(cobham): document the class and rewrite the roadmap item"
```

---

### Task 12: `comb`

**Bookmark:** `feat/cobham-tree-recognizer`

**Files:**

- Create: `Geb/Mathlib/Computability/Cobham/Tree.lean`
- Create: `GebTests/Mathlib/Computability/Cobham/Tree.lean`
- Modify: `Geb/Mathlib/Computability/Cobham.lean` and its `GebTests`
  counterpart

**Interfaces:**

- Consumes: Task 10's `pred`, `cond`, `predSem_eq`, `condSem_eq`; Task 3's
  `BinTree.depth_le_length`; `BinTree.depth`, `ok` from
  `Geb.Mathlib.Data.Tree.Preorder`.
- Produces: `Cobham.comb : COf 1` and `Cobham.combSem_eq`.

Imports: `Cobham.Basic` and `Geb.Mathlib.Data.Tree.Preorder`. This module
does **not** need `open scoped FinEnum` — instance selection for `sig.B` is
fixed where `sigFinitary` elaborates in `Basic.lean`.

- [ ] **Step 1: Write the failing test**

Mirror `GebTests/Mathlib/Computability/BellantoniCook/Tree.lean`'s scan
checks: `comb` on `[]`, on `[false]`, on `[true, false, false]`, and on a
word failing `ok`.

- [ ] **Step 2: Write `combRaw` and `combSem`**

`combRaw` is the raw tree with bound `S₁` **itself** — arity one, so no
projection and no `Comp` wrapper; `|S₁ y| = |y| + 1`, exactly the value
bound. The arity relation closes: `a_j = 1`, `a_g = 0`, `a_h = 2`.
Seventy-seven nodes in total.

Define `combSem` directly from `combRaw`'s evaluation —
`combSem := transport (fst_eval ⟨combRaw, by decide⟩) (eval ⟨combRaw, by
decide⟩).2` — before `comb`'s `RecBounded` obligation is discharged.
`Cobham.eval` takes a raw `sig.W` and needs no `RecBounded` proof, so this
characterization is available before `comb : COf 1` exists. Step 5 needs
it there: the `RecBounded` proof is a field of `comb`, so nothing whose
type mentions `comb` — `combSem` included, were it defined from `comb` —
is in scope while that field is being supplied.

- [ ] **Step 3: Write the unfolding lemmas**

One per constructor, with the recursive value exposed on the right, as
`BellantoniCook/Tree.lean`'s `combSem_nil` / `combSem_cons_false` /
`combSem_cons_true` do. These close by `change` to the step's own
application — which is `rfl` — followed by `generalize`, not by `rw`:
`condSem` occurs nowhere in the unfolding goal for `rw` to target, `cond`
and `pred` being `Rec` nodes in this algebra and generators in `B`.

- [ ] **Step 4: Write `combSem_eq`**

```lean
theorem combSem_eq (w : List Bool) :
    combSem ![w] =
      if BinTree.ok w then List.replicate (BinTree.depth w + 1) true
      else [false]
```

Driven by `List.rec`, as the existing proof is. Its `0 / 1 / m+2` split for
the two-predecessor guard is unchanged; `combSem_cons_true` is stated over
`.tail.tail`, mirroring `BellantoniCook/Tree.lean`, so no
`simp only [predSem_eq]` is needed, and each branch closes by `rfl`.

- [ ] **Step 5: Discharge `comb`'s `RecBounded` and define `comb`**

From `combSem_eq` and `BinTree.depth_le_length`: `depth w + 1 ≤ w.length +
1` where `ok` holds, and `|[false]| = 1 ≤ w.length + 1` otherwise. Package
`combRaw` with this obligation as `comb : COf 1`.

- [ ] **Step 6: Build, test, commit**

```bash
lake build && lake test
```

```bash
jj describe -m "feat(cobham): scan the preorder stack depth"
```

---

### Task 13: `eqOne` and `isTree`

**Bookmark:** `feat/cobham-tree-recognizer`

**Interfaces:**

- Consumes: Task 12.
- Produces: `Cobham.eqOne : COf 1`, `Cobham.isTree : COf 1`,
  `Cobham.eqOneSem_eq`, `Cobham.eqOneSem_env`.

- [ ] **Step 1: Write `eqOne` and its two lemmas**

`eqOneSem_env` is needed for the same reason `BellantoniCook`'s is: the
argument arrives as `fun _ ↦ …` rather than `![…]`, and `eqOneSem_eq` does
not apply until it is normalised.

- [ ] **Step 2: Write `isTree` and `isTreeSem_apply`**

Unlike `BellantoniCook`'s counterpart, `isTreeSem_apply` does not close by
`rfl`: this algebra's `pred` is a derived `boundedRec` node, where
`BellantoniCook`'s is a primitive generator. Use `change`, `generalize`
and `match`, as Task 12's unfolding lemmas do.

- [ ] **Step 3: Build and commit**

```bash
lake build && jj describe -m "feat(cobham): recognize the preorder spellings"
```

---

### Task 14: Correctness

**Bookmark:** `feat/cobham-tree-recognizer`

**Interfaces:**

- Consumes: Tasks 12–13.
- Produces: `Cobham.isTreeSem_eq_singleton_iff_valid`,
  `Cobham.isTreeSem_eq_singleton_iff_exists_print`,
  `Cobham.isTreeSem_eq_ite`.

- [ ] **Step 1: Prove `isTreeSem_eq_singleton_iff_valid`**

Follow `BellantoniCook/Tree.lean`'s proof. `predSem_eq` as `.tail` leaves
`List.tail_replicate` applicable, so no further bridge lemma is needed.

- [ ] **Step 2: Prove the `exists_print` corollary**

By `BinTree.valid_iff_exists_print`, as the existing module does.

- [ ] **Step 3: Prove `isTreeSem_eq_ite`**

Same statement shape as Task 2's, over this module's `isTreeSem`. This is
what makes the containment a property of the function rather than of the
accepted set.

- [ ] **Step 4: Build, test, lint, commit**

```bash
lake build && lake test && lake lint
```

```bash
jj describe -m "feat(cobham): prove the recognizer accepts exactly the spellings"
```

---

### Task 15: Conclude, document, and remove the transient artifacts

**Bookmark:** `feat/cobham-tree-recognizer`

**Files:**

- Modify: `Geb/Mathlib/Computability/Cobham/Tree.lean` — module docstring
- Modify: `docs/index.md`
- Delete: `docs/superpowers/specs/2026-08-08-tree-recognizer-linear-space-design.md`
- Delete: `docs/superpowers/plans/2026-08-08-cobham-linear-space.md`

- [ ] **Step 1: State the conclusion**

```lean
/-- The recognizer lies in the smash-free subalgebra. With
[Strahm2003] Theorem 1(2)'s left-to-right inclusion, the decision of
`BinTree.Valid` is computable simultaneously in polynomial time and linear
space. -/
theorem isTree_smashFree : SmashFree isTree := by decide
```

If elaboration-time `decide` does not carry the ~151-node term, the
fallback is `maxRecDepth` or `maxHeartbeats` on the declaration with an
explanatory comment (`linter.style.maxHeartbeats` errors under
`weak.warningAsError` without one). `decide +kernel` does **not** help: the
proof term is `of_decide_eq_true rfl` either way and the kernel re-checks
it. Measurement at v4.33.0-rc2 decides synthetic 262-node `sig`-trees in
under a second at default heartbeats, so this is not expected to fire.

- [ ] **Step 2: Write the module docstring**

It records the distinction between a bound on a value and a bound on
evaluating an expression, over **this** module's `combSem`. It does not
restate the `BellantoniCook` inequality: this module's imports do not
reach it and no committed declaration would prove it.

- [ ] **Step 3: Add the `docs/index.md` entry**

- [ ] **Step 4: Remove the spec and this plan**

```bash
jj new -m "doc(cobham): remove the transient spec and plan"
rm docs/superpowers/specs/2026-08-08-tree-recognizer-linear-space-design.md
rm docs/superpowers/plans/2026-08-08-cobham-linear-space.md
```

Per CONTRIBUTING § Concern shape: the spec and plan record how the current
state was reached, not what it is, so they belong in history rather than
on an active branch. This bookmark is the tip of the chain that added
them.

- [ ] **Step 5: Final verification**

```bash
lake build && lake build GebTests && lake test && lake lint && lake lint -- GebTests
lake shake --add-public --keep-implied --keep-prefix Geb GebTests
scripts/lint-imports.sh && markdownlint-cli2 '**/*.md' && doctoc --dryrun --update-only . && scripts/check-md-links.sh
scripts/pre-push.sh
```

Expected: all clean, axiom set `{propext, Quot.sound}` throughout.

- [ ] **Step 6: Hand off for review**

Do not push. `AGENTS.md` § No `jj git push` without user line-by-line
review binds every bookmark in this series.
