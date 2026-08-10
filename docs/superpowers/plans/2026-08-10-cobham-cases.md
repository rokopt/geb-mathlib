# Cobham definition-by-cases implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` (recommended) or
> `superpowers:executing-plans` to implement this plan task-by-task. Steps use
> checkbox (`- [ ]`) syntax for tracking.

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Global constraints](#global-constraints)
- [File structure](#file-structure)
  - [Task 1: Remove the prototype](#task-1-remove-the-prototype)
  - [Task 2: Move the `zeroAt` family into `Basic.lean`](#task-2-move-the-zeroat-family-into-basiclean)
  - [Task 3: Add `semAt` and restate the six sites through it](#task-3-add-semat-and-restate-the-six-sites-through-it)
  - [Task 4: The iterated predecessor](#task-4-the-iterated-predecessor)
  - [Task 5: Prepending a word, and the constant word](#task-5-prepending-a-word-and-the-constant-word)
  - [Task 6: The diagonal](#task-6-the-diagonal)
  - [Task 7: `Cases.lean` — the scrutinee's bits and the shift](#task-7-caseslean--the-scrutinees-bits-and-the-shift)
  - [Task 8: `Cases.lean` — the case tree and its meaning](#task-8-caseslean--the-case-tree-and-its-meaning)
  - [Task 9: `Cases.lean` — the expression and the word characterisations](#task-9-caseslean--the-expression-and-the-word-characterisations)
  - [Task 10: The test mirror](#task-10-the-test-mirror)
  - [Task 11: Index modules and documentation](#task-11-index-modules-and-documentation)
  - [Task 12: Verify the segment](#task-12-verify-the-segment)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

**Goal:** Land segment 1 of
[the design](../specs/2026-08-10-cobham-cases-fold-ranked-design.md):
`Geb/Mathlib/Computability/Cobham/Cases.lean`, the combinator selecting among
`2 ^ p` expressions of arity one by the low `p` bits of a scrutinee, together
with the constant-word, iterated-predecessor and diagonal combinators its
consumers build branches from.

**Architecture:** The combinators that depend only on `Cobham/Basic.lean`'s
vocabulary go into `Basic.lean`; the case tree, which needs `liftRaw` from
`Cobham/Scan.lean`, and every characterisation naming `baseWord` or `stepWord`,
which are declared in `Scan.lean`, go into the new `Cases.lean`. The case tree
consumes its scrutinee by shifting it into the recursive subtree rather than by
scrutinising an iterated predecessor, which is what makes its semantic theorem
reduce under case analysis.

**Tech stack:** Lean 4 (toolchain pinned by `lean-toolchain`), mathlib, `lake`.

Every code block in Tasks 4 to 9 is transcribed from
`Geb/Internal/CasesSpike.lean`, which compiled before Task 1 removes it, every
declaration in it measuring `[propext, Quot.sound]` by direct measurement.
`lake lint` does not reach it: it lints the `Geb` umbrella's import closure,
and `Geb/Internal.lean` does not import the prototype. Copy those blocks; do
not retype them from memory. Task 10's mirror was compiled against the
prototype too, under the prototype's own names,
so its assertions are known to close. Tasks 2 and 3 are the exception: Task 2's
text is cut from `Cobham/Tree.lean` and Task 3's restatements were established
against a throwaway module since deleted, so they are the two whose builds are
worth watching.

## Global constraints

- No `noncomputable`, and no dependence on `Classical.choice`. `lake lint`
  enforces the permitted axiom set `{propext, Quot.sound}` over all of `Geb`.
- No `induction` tactic, no self-recursive `def`, no `termination_by`. Every
  recursion is an explicit `Nat.rec` or `List.rec` application.
- No `sorry` and no `admit` in a commit.
- Two-space indentation; 100-character lines; Unicode notation where mathlib
  uses it (`∀`, `→`, `↦`, `⟨ ⟩`, `≤`, `ℕ`).
- Every `def` and every theorem of public interest carries a `/-- … -/`
  docstring. Every module carries a `/-! … -/` module docstring with
  `# Title`, a summary, `## Main definitions`, `## Main statements`,
  `## Notation`, `## Implementation notes`, `## References` and `## Tags`, in
  that order, each present when it has content and omitted when vacuous. It
  stands immediately after the imports and before any `set_option` or `open`.
- No empty lines inside a declaration.
- `linter.unusedVariables`, `linter.flexible`, `linter.unnecessarySeqFocus`,
  `linter.style.show`, `linter.style.header`, `linter.unusedSimpArgs` and
  `linter.unnecessarySimpa` are errors under `weak.warningAsError`. A binder
  the statement does not mention is an error; a bare `simp` that changes the
  goal must be terminal; a `simp only` set must be exactly what is used; a
  `show` that changes the goal must be `change`.
- `Geb/Mathlib/` may import only `Mathlib.*`, `Batteries.*` and
  `Geb.Mathlib.*`; `GebTests/Mathlib/` may additionally import
  `GebTests.Mathlib.*`. Neither prefix appears outside `import` lines.
- `lake lint` covers `Geb` only, `lakefile.toml` setting its driver argument
  to that library. A change under `GebTests/` is put under the axiom linter by
  `lake lint -- GebTests`.
- Commit subjects are imperative present, no leading capital, no trailing
  period, with a type from
  `feat | fix | doc | style | refactor | test | chore | perf | ci`.
- Use `jj` for every state-mutating version-control operation. Never a
  mutating `git` subcommand.

## File structure

| File | Change | Responsibility |
| --- | --- | --- |
| `Geb/Mathlib/Computability/Cobham/Basic.lean` | modify | Gains `semAt`, the `zeroAt` family, and the `predIter`, `prepend`, `constAt` and `diag` families |
| `Geb/Mathlib/Computability/Cobham/Scan.lean` | modify | `boundSem`, `scanSem`, `baseWord`, `stepWord` restated through `semAt` |
| `Geb/Mathlib/Computability/Cobham/Tree.lean` | modify | Loses the `zeroAt` family; `eqOneSem` and `isTreeSem` restated through `semAt` |
| `Geb/Mathlib/Computability/Cobham/Cases.lean` | create | `bits`, the shift, the case tree, and the word characterisations |
| `Geb/Mathlib/Computability/Cobham.lean` | modify | Index: imports `Cases.lean` |
| `GebTests/Mathlib/Computability/Cobham/Cases.lean` | create | Mirror |
| `GebTests/Mathlib/Computability/Cobham.lean` | modify | Test index |
| `docs/index.md`, `TODO.md` | modify | Catalogue and roadmap |
| `Geb/Internal/CasesSpike.lean` | delete | The prototype, removed once the module exists |

---

### Task 1: Remove the prototype

`Geb/Internal/CasesSpike.lean` declares `Cobham.semAt`, `Cobham.predIterRaw`
and the rest of the names the tasks below add, in the same namespace, and it
imports `Cobham/Basic.lean`, `Cobham/Scan.lean` and `Cobham/Tree.lean`. Every
build from Task 3 onward fails with `Cobham.semAt has already been declared`
while it is present, so it goes first. It also fails a gate on its own account:
`scripts/tests/test-lint-driver.sh`, which `scripts/pre-push.sh` runs, reports
`Geb.Internal.CasesSpike` as unreachable from the `Geb` umbrella and so
escaping the linter.

The code blocks below were transcribed from it while it compiled and passed
`lake lint`; from Task 1 onward they, and not it, are the source.

**Files:**

- Delete: `Geb/Internal/CasesSpike.lean`

**Interfaces:**

- Consumes: nothing.
- Produces: nothing.

- [ ] **Step 1: Delete it**

```bash
rm Geb/Internal/CasesSpike.lean
```

- [ ] **Step 2: Build**

Run: `lake build`
Expected: success.

- [ ] **Step 3: Record that there is nothing to commit**

The prototype is an uncommitted working-tree artifact, as the scan
combinator's was: `jj status` shows it as added rather than modified, so
removing it leaves nothing to record. Confirm with `jj status` that the working
copy is otherwise clean, and move on without committing.

---

### Task 2: Move the `zeroAt` family into `Basic.lean`

`constAt` needs a nullary constant at an arbitrary arity, and `Tree.lean`
imports `Basic.lean` rather than the reverse.

**Files:**

- Modify: `Geb/Mathlib/Computability/Cobham/Tree.lean` (remove the family and
  its docstring entries)
- Modify: `Geb/Mathlib/Computability/Cobham/Basic.lean` (receive them)

**Interfaces:**

- Consumes: nothing.
- Produces: `Cobham.zeroAtRaw (n : ℕ) : sig.toPFunctor.W`,
  `Cobham.zeroAt (n : ℕ) : C`, `Cobham.zeroAtOf (n : ℕ) : COf n`, now visible
  from `Basic.lean` downward.

- [ ] **Step 1: Cut the three declarations from `Tree.lean`**

Remove `Geb/Mathlib/Computability/Cobham/Tree.lean` lines 165–186 — the
docstring and body of `zeroAtRaw`, of `zeroAt`, and of `zeroAtOf` — verbatim,
including their `/-- … -/` docstrings. Do not alter a character of them. Line
163 is `public section` and line 164 is blank: cutting from 163 makes every
remaining declaration in the module private and orphans its closing `end`.
After the cut, remove the doubled blank line the removal leaves behind.

- [ ] **Step 2: Paste them into `Basic.lean`**

Insert the cut text into `Geb/Mathlib/Computability/Cobham/Basic.lean`
immediately before the docstring of `concatRaw`, which opens
"The `concat` generator as a single node".

- [ ] **Step 3: Move the module-docstring entries**

In `Tree.lean`'s `## Main definitions`, line 46 reads:

```text
* `Cobham.zeroAt`, `Cobham.oneAt`, `Cobham.falseAt` — the empty bitstring and
```

Rewrite that bullet so it names only `Cobham.oneAt` and `Cobham.falseAt`, and
add to `Basic.lean`'s `## Main definitions`, after the `Cobham.smashOf` bullet:

```text
* `Cobham.zeroAt`, `Cobham.zeroAtOf` — the empty bitstring at an arbitrary
  arity.
```

In `Tree.lean`'s `## Implementation notes`, line 101 names `zeroAtRaw` among
the trees carrying a free arity; leave that sentence in place but drop
`zeroAtRaw` from its list, and add the same observation to `Basic.lean`'s
`## Implementation notes`, naming `zeroAtRaw`.

- [ ] **Step 4: Build**

Run: `lake build`
Expected: success. `Tree.lean`'s `oneAtRaw` and `falseAtRaw` are defined over
`zeroAtRaw n` and now resolve it from `Basic.lean`.

- [ ] **Step 5: Check the axiom gate and the moved tree's `decide`**

Run: `lake lint`
Expected: `-- Linting passed for Geb.` Step 4 is what confirms that
`isTree_smashFree`, which is `by decide` and folds over the relocated
`zeroAtRaw`, still closes; this step confirms the permitted axiom set is
unchanged.

- [ ] **Step 6: Commit**

```bash
jj commit Geb/Mathlib/Computability/Cobham/Basic.lean \
  Geb/Mathlib/Computability/Cobham/Tree.lean \
  -m "refactor(cobham): move the empty-bitstring family to the base module"
```

---

### Task 3: Add `semAt` and restate the six sites through it

**Files:**

- Modify: `Geb/Mathlib/Computability/Cobham/Basic.lean`
- Modify: `Geb/Mathlib/Computability/Cobham/Scan.lean`
- Modify: `Geb/Mathlib/Computability/Cobham/Tree.lean`

**Interfaces:**

- Consumes: `Cobham.transport`, `Cobham.fst_eval`, `Cobham.eval`,
  `Cobham.arity`, `Cobham.Sem`, all in `Basic.lean`.
- Produces: `Cobham.semAt (n : ℕ) (e : sig.W) (he : arity e = n) : Sem n`.

- [ ] **Step 1: Add `semAt` to `Basic.lean`**

Insert immediately after the `fst_eval` theorem. It names `eval`, `arity`
and `fst_eval`, which stand well below `transport_transport`, so an earlier
anchor fails with an unknown-identifier error naming `arity`:

```lean
/-- The meaning of a tree at a given arity. -/
@[expose] def semAt (n : ℕ) (e : sig.W) (he : arity e = n) : Sem n :=
  transport ((fst_eval e).trans he) (eval e).2
```

Add to `Basic.lean`'s `## Main definitions`:

```text
* `Cobham.semAt` — the meaning of a tree at a given arity.
```

- [ ] **Step 2: Restate the four sites in `Scan.lean`**

Replace each body, leaving every docstring unchanged:

```lean
@[expose] def boundSem (growth : ℕ) : Sem 1 :=
  semAt 1 ⟨boundRaw growth, wValid_boundRaw growth⟩ (arity_boundRaw growth)

@[expose] def scanSem (base : COf 0) (step₀ step₁ : COf 1) (growth : ℕ) :
    Sem 1 :=
  semAt 1 (scanW base step₀ step₁ growth) (arity_scanW base step₀ step₁ growth)

@[expose] def baseWord (base : COf 0) : List Bool :=
  semAt 0 base.1.1 base.2 Fin.elim0

@[expose] def stepWord (step : COf 1) (r : List Bool) : List Bool :=
  semAt 1 step.1.1 step.2 ![r]
```

- [ ] **Step 3: Restate the two sites in `Tree.lean`**

These two spell the `he := rfl` case, `Eq.trans h rfl` being definitionally
`h`:

```lean
@[expose] def eqOneSem : Sem 1 :=
  semAt 1 ⟨eqOneRaw, by decide⟩ rfl

@[expose] def isTreeSem : Sem 1 :=
  semAt 1 ⟨isTreeRaw, by decide⟩ rfl
```

- [ ] **Step 3a: Record the restatement in both module docstrings**

At the end of `Cobham/Scan.lean`'s `## Implementation notes`, and again at the
end of `Cobham/Tree.lean`'s, add:

```text
The meanings this module reads at a raw tree are taken through `Cobham.semAt`,
which names the composite of `fst_eval` with the tree's arity equation once
rather than spelling it at each site.
```

- [ ] **Step 4: Build**

Run: `lake build`
Expected: success. The proofs that read through the six definitions must still
close unchanged — `scanSem_nil`, `scanSem_eq_eval`, `scanSem_cons`,
`baseWord_eq_eval`, `stepWord_eq_eval`, `boundSem_eq`, `combSem_def`,
`combSem_nil`, `combSem_cons_false`, `combSem_cons_true`, `combSem_eq`,
`length_combSem_le`, `eqOneSem_env`, `eqOneSem_eq`, `isTreeSem_apply`,
`isTreeSem_eq_ite`, `isTreeSem_eq_eval` and `isTree_smashFree`. If any fails,
stop and report; do not weaken a `rfl` to a tactic proof.

- [ ] **Step 5: Test and lint**

Run: `lake test && lake lint`
Expected: both pass.

- [ ] **Step 6: Commit**

```bash
jj commit Geb/Mathlib/Computability/Cobham/Basic.lean \
  Geb/Mathlib/Computability/Cobham/Scan.lean \
  Geb/Mathlib/Computability/Cobham/Tree.lean \
  -m "refactor(cobham): name the meaning of a tree at an arity"
```

---

### Task 4: The iterated predecessor

**Files:**

- Modify: `Geb/Mathlib/Computability/Cobham/Basic.lean`

**Interfaces:**

- Consumes: `Cobham.predRaw`, `Cobham.pred`, `Cobham.RecBounded`,
  `SlicePFunctor.wIndexValid_index_eq_wIndexRoot`.
- Produces: `Cobham.predIterRaw (k : ℕ) : sig.toPFunctor.W`,
  `Cobham.wIndexRoot_predIterRaw`, `Cobham.wValid_predIterRaw`,
  `Cobham.recBounded_predIterRaw`, `Cobham.predIter (k : ℕ) : C`,
  `Cobham.predIterOf (k : ℕ) : COf 1`.

- [ ] **Step 1: Write the declarations**

Insert into `Basic.lean` after `predSem_eq`:

```lean
/-- The `k`-fold predecessor of the sole argument. -/
@[expose] def predIterRaw : ℕ → sig.toPFunctor.W :=
  Nat.rec (WType.mk (.proj 1 0) Fin.elim0)
    fun _ ih ↦
      WType.mk (.comp 1 1) fun d ↦
        match d with
        | .inl () => predRaw
        | .inr _ => ih

/-- The iterated predecessor has arity one, at every iterate. -/
theorem wIndexRoot_predIterRaw (k : ℕ) : sig.wIndexRoot (predIterRaw k) = 1 := by
  cases k with
  | zero => rfl
  | succ _ => rfl

/-- The iterated predecessor is admissible, at every iterate. -/
theorem wValid_predIterRaw (k : ℕ) : sig.WValid (predIterRaw k) :=
  Nat.rec ⟨fun c ↦ c.elim0, funext fun c ↦ c.elim0⟩
    (fun j ih ↦
      ⟨fun d ↦ match d with
        | .inl () => pred.1.1.2
        | .inr _ => ih,
      funext fun d ↦ match d with
        | .inl () =>
          (sig.wIndexValid_index_eq_wIndexRoot predRaw).trans pred.2
        | .inr _ =>
          (sig.wIndexValid_index_eq_wIndexRoot (predIterRaw j)).trans
            (wIndexRoot_predIterRaw j)⟩)
    k

/-- The iterated predecessor carries the predecessor's recursions and no
other. -/
theorem recBounded_predIterRaw (k : ℕ) :
    RecBounded ⟨predIterRaw k, wValid_predIterRaw k⟩ :=
  Nat.rec ⟨trivial, fun c ↦ c.elim0⟩
    (fun _ ih ↦ ⟨trivial, fun d ↦ match d with
      | .inl () => pred.1.2
      | .inr _ => ih⟩)
    k

/-- The iterated predecessor as an expression. -/
@[expose] def predIter (k : ℕ) : C :=
  ⟨⟨predIterRaw k, wValid_predIterRaw k⟩, recBounded_predIterRaw k⟩

/-- `predIter` at its declared arity. -/
@[expose] def predIterOf (k : ℕ) : COf 1 :=
  ⟨predIter k, wIndexRoot_predIterRaw k⟩
```

- [ ] **Step 2: Add the module-docstring entries**

At the end of `## Main definitions`:

```text
* `Cobham.predIter`, `Cobham.predIterOf` — the iterated predecessor.
```

At the end of `## Main statements`:

```text
* `Cobham.wIndexRoot_predIterRaw`, `Cobham.wValid_predIterRaw`,
  `Cobham.recBounded_predIterRaw` — the iterated predecessor's arity,
  admissibility and recursion bound.
```

- [ ] **Step 3: Build and lint**

Run: `lake build && lake lint`
Expected: both pass.

- [ ] **Step 4: Commit**

```bash
jj commit Geb/Mathlib/Computability/Cobham/Basic.lean \
  -m "feat(cobham): add the iterated predecessor"
```

---

### Task 5: Prepending a word, and the constant word

**Files:**

- Modify: `Geb/Mathlib/Computability/Cobham/Basic.lean`

**Interfaces:**

- Consumes: `Cobham.zeroAtOf` (Task 2), `Cobham.COf`, `Cobham.RecBounded`.
- Produces:
  `Cobham.prependRaw (n : ℕ) (u : List Bool) (e : sig.toPFunctor.W) : sig.toPFunctor.W`,
  `Cobham.wIndexRoot_prependRaw`, `Cobham.wValid_prependRaw`,
  `Cobham.recBounded_prependRaw`,
  `Cobham.prepend {n : ℕ} (u : List Bool) (e : COf n) : C`,
  `Cobham.prependOf {n : ℕ} (u : List Bool) (e : COf n) : COf n`,
  `Cobham.constAt (n : ℕ) (u : List Bool) : C`,
  `Cobham.constAtOf (n : ℕ) (u : List Bool) : COf n`.

`constAt`'s arity is explicit: it occurs in neither an argument type nor the
result type `C`, so an implicit binder could not be synthesized at any call
site. `prependRaw`'s is explicit for a different reason — it appears in the
`.comp n 1` node it builds, and its argument is a raw tree carrying no arity —
where `prepend` and `prependOf` take it implicitly, reading it off `e : COf n`.
Both depart from the spec, which gives `prependRaw` without the arity.

- [ ] **Step 1: Write the declarations**

Insert into `Basic.lean` after the `predIter` family:

```lean
/-- A fixed word prepended to what an expression of arity `n` computes. -/
@[expose] def prependRaw (n : ℕ) (u : List Bool) (e : sig.toPFunctor.W) :
    sig.toPFunctor.W :=
  List.rec e (fun b _ ih ↦
    WType.mk (.comp n 1) fun d ↦
      match d with
      | .inl () => WType.mk (.succ b) Fin.elim0
      | .inr _ => ih) u

/-- Prepending preserves the arity. -/
theorem wIndexRoot_prependRaw (n : ℕ) (u : List Bool) (e : sig.toPFunctor.W)
    (he : sig.wIndexRoot e = n) : sig.wIndexRoot (prependRaw n u e) = n := by
  cases u with
  | nil => exact he
  | cons _ _ => rfl

/-- Prepending preserves admissibility. -/
theorem wValid_prependRaw (n : ℕ) (e : sig.toPFunctor.W) (hv : sig.WValid e)
    (he : sig.wIndexRoot e = n) :
    ∀ u : List Bool, sig.WValid (prependRaw n u e) :=
  List.rec hv (fun _ v ih ↦
    ⟨fun d ↦ match d with
      | .inl () => ⟨fun c ↦ c.elim0, funext fun c ↦ c.elim0⟩
      | .inr _ => ih,
    funext fun d ↦ match d with
      | .inl () => rfl
      | .inr _ =>
        (sig.wIndexValid_index_eq_wIndexRoot (prependRaw n v e)).trans
          (wIndexRoot_prependRaw n v e he)⟩)

/-- Prepending introduces no recursion of its own. -/
theorem recBounded_prependRaw (n : ℕ) (e : sig.toPFunctor.W)
    (hv : sig.WValid e) (he : sig.wIndexRoot e = n) (hr : RecBounded ⟨e, hv⟩) :
    ∀ u : List Bool,
      RecBounded ⟨prependRaw n u e, wValid_prependRaw n e hv he u⟩ :=
  List.rec hr (fun _ _ ih ↦
    ⟨trivial, fun d ↦ match d with
      | .inl () => ⟨trivial, fun c ↦ c.elim0⟩
      | .inr _ => ih⟩)

/-- A fixed word prepended to an expression. -/
@[expose] def prepend {n : ℕ} (u : List Bool) (e : COf n) : C :=
  ⟨⟨prependRaw n u e.1.1.1, wValid_prependRaw n _ e.1.1.2 e.2 u⟩,
    recBounded_prependRaw n _ e.1.1.2 e.2 e.1.2 u⟩

/-- `prepend` at its declared arity. -/
@[expose] def prependOf {n : ℕ} (u : List Bool) (e : COf n) : COf n :=
  ⟨prepend u e, wIndexRoot_prependRaw n u e.1.1.1 e.2⟩

/-- The constant word at a given arity. -/
@[expose] def constAt (n : ℕ) (u : List Bool) : C := prepend u (zeroAtOf n)

/-- `constAt` at its declared arity. -/
@[expose] def constAtOf (n : ℕ) (u : List Bool) : COf n :=
  ⟨constAt n u, wIndexRoot_prependRaw n u _ (zeroAtOf n).2⟩
```

- [ ] **Step 2: Add the module-docstring entries**

At the end of `## Main definitions`:

```text
* `Cobham.prepend`, `Cobham.prependOf` — a fixed word prepended to an
  expression.
* `Cobham.constAt`, `Cobham.constAtOf` — the constant word at a given arity.
```

At the end of `## Main statements`:

```text
* `Cobham.wIndexRoot_prependRaw`, `Cobham.wValid_prependRaw`,
  `Cobham.recBounded_prependRaw` — prepending preserves the arity,
  admissibility and the recursion bound.
```

- [ ] **Step 3: Build and lint**

Run: `lake build && lake lint`
Expected: both pass.

- [ ] **Step 4: Commit**

```bash
jj commit Geb/Mathlib/Computability/Cobham/Basic.lean \
  -m "feat(cobham): add the prepended and constant words"
```

---

### Task 6: The diagonal

**Files:**

- Modify: `Geb/Mathlib/Computability/Cobham/Basic.lean`

**Interfaces:**

- Consumes: `Cobham.COf`, `Cobham.arity`, `Cobham.RecBounded`.
- Produces: `Cobham.diagRaw (e : sig.toPFunctor.W) : sig.toPFunctor.W`,
  `Cobham.wIndexRoot_diagRaw`, `Cobham.wValid_diagRaw`,
  `Cobham.recBounded_diagRaw`, `Cobham.diag (e : COf 2) : C`,
  `Cobham.diagOf (e : COf 2) : COf 1`.

- [ ] **Step 1: Write the declarations**

Insert into `Basic.lean` after the `prepend` family:

```lean
/-- A binary expression applied to its sole argument in both positions. -/
@[expose] def diagRaw (e : sig.toPFunctor.W) : sig.toPFunctor.W :=
  WType.mk (.comp 1 2) fun d ↦
    match d with
    | .inl () => e
    | .inr _ => WType.mk (.proj 1 0) Fin.elim0

/-- The diagonal has arity one, whatever it diagonalises. -/
theorem wIndexRoot_diagRaw (e : sig.toPFunctor.W) :
    sig.wIndexRoot (diagRaw e) = 1 := rfl

/-- The diagonal is admissible when what it diagonalises is, at arity two. -/
theorem wValid_diagRaw (e : sig.toPFunctor.W) (hv : sig.WValid e)
    (he : sig.wIndexRoot e = 2) : sig.WValid (diagRaw e) :=
  ⟨fun d ↦ match d with
    | .inl () => hv
    | .inr _ => ⟨fun c ↦ c.elim0, funext fun c ↦ c.elim0⟩,
  funext fun d ↦ match d with
    | .inl () => (sig.wIndexValid_index_eq_wIndexRoot e).trans he
    | .inr _ => rfl⟩

/-- The diagonal introduces no recursion of its own. -/
theorem recBounded_diagRaw (e : sig.W) (he : arity e = 2)
    (hr : RecBounded e) :
    RecBounded ⟨diagRaw e.1, wValid_diagRaw e.1 e.2 he⟩ :=
  ⟨trivial, fun d ↦ match d with
    | .inl () => hr
    | .inr _ => ⟨trivial, fun c ↦ c.elim0⟩⟩

/-- The diagonal as an expression. -/
@[expose] def diag (e : COf 2) : C :=
  ⟨⟨diagRaw e.1.1.1, wValid_diagRaw e.1.1.1 e.1.1.2 e.2⟩,
    recBounded_diagRaw e.1.1 e.2 e.1.2⟩

/-- `diag` at its declared arity. -/
@[expose] def diagOf (e : COf 2) : COf 1 := ⟨diag e, wIndexRoot_diagRaw _⟩
```

- [ ] **Step 2: Add the module-docstring entries**

At the end of `## Main definitions`:

```text
* `Cobham.diag`, `Cobham.diagOf` — a binary expression at its sole argument in
  both positions.
```

At the end of `## Main statements`:

```text
* `Cobham.wIndexRoot_diagRaw`, `Cobham.wValid_diagRaw`,
  `Cobham.recBounded_diagRaw` — the diagonal's arity, admissibility and
  recursion bound.
```

- [ ] **Step 3: Build and lint**

Run: `lake build && lake lint`
Expected: both pass.

- [ ] **Step 4: Commit**

```bash
jj commit Geb/Mathlib/Computability/Cobham/Basic.lean \
  -m "feat(cobham): add the diagonal of a binary expression"
```

---

### Task 7: `Cases.lean` — the scrutinee's bits and the shift

**Files:**

- Create: `Geb/Mathlib/Computability/Cobham/Cases.lean`

**Interfaces:**

- Consumes: `Cobham.semAt`, `Cobham.predRaw`, `Cobham.pred` (Basic);
  `Cobham.liftRaw` (Scan).
- Produces: `Cobham.bits (p : ℕ) (w : List Bool) : Fin p → Bool`,
  `Cobham.bits_succ`, `Cobham.bits_succ_tail`, `Cobham.bits_ofFn`,
  `Cobham.ofFn_bits`, `Cobham.shiftRaw`, `Cobham.wIndexRoot_shiftRaw`,
  `Cobham.wValid_shiftRaw`, `Cobham.shiftW`, `Cobham.arity_shiftW`,
  `Cobham.semAt_shiftW`, `Cobham.recBounded_shiftW`.

- [ ] **Step 1: Create the module with its header and imports**

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Computability.Cobham.Basic
public import Geb.Mathlib.Computability.Cobham.Scan
```

Then the module docstring, verbatim:

```lean
/-!
# Definition by cases over Cobham's class

A combinator selecting among `2 ^ p` expressions of arity one by the low `p`
bits of a scrutinee, and applying the selected one to a second argument. It
imposes no condition on the expressions it selects among: every node the
recursion introduces is a `comp`, whose `RecBoundedValue` is `True`, over
`proj` together with the trees underlying `cond` and `pred`, which carry their
own recursion bounds already.

## Main definitions

* `Cobham.bits` — the bits of a scrutinee word, `false` past its end.
* `Cobham.shiftRaw`, `Cobham.shiftW` — a tree of arity two at the predecessor
  of argument zero.
* `Cobham.casesRaw`, `Cobham.casesW`, `Cobham.casesSem` — the case tree, its
  admissible form, and its meaning.
* `Cobham.cases`, `Cobham.casesOf` — the case tree as an expression of `C`, and
  at its declared arity.

## Main statements

* `Cobham.bits_succ`, `Cobham.bits_succ_tail`, `Cobham.bits_ofFn`,
  `Cobham.ofFn_bits` — peeling, dropping, and the round trip against
  `List.ofFn`. The round trip is consumed by the branch families of the
  generic ranked recognizer and of the fold, which read a bit family as a
  `List Bool`.
* `Cobham.wValid_casesRaw`, `Cobham.recBounded_casesW` — admissibility and the
  recursion bound, from the branches' own.
* `Cobham.semAt_shiftW`, `Cobham.casesSem_eq`, `Cobham.casesSem_eq_eval` — the
  shift's meaning, the branch the scrutinee selects, and the identification
  with the meaning the expression carries.
* `Cobham.stepWord_predIterOf`, `Cobham.stepWord_prependOf`,
  `Cobham.baseWord_prependOf`, `Cobham.baseWord_constAtOf`,
  `Cobham.stepWord_constAtOf`, `Cobham.stepWord_diagOf` — the words the
  combinators of `Cobham/Basic.lean` contribute.

## Implementation notes

The scrutinee is consumed by shifting it into the recursive subtree rather than
by scrutinising an iterated predecessor of a fixed argument. At an iterated
predecessor the scrutinee is not a variable, so no case analysis reduces the
`boundedRec` node of `cond` and the semantic theorem is unreachable; shifting
leaves the scrutinee as argument zero itself. It is also linear rather than
quadratic in the number of bits dispatched on.

`cond`'s empty branch is directed at the same subtree as its head-`false`
branch, which reads a scrutinee shorter than `p` as zero-padded and keeps
`casesSem_eq` free of a hypothesis.

`ofFn_bits` is proved by structural induction on the width. The route through
`List.ext_getElem` and `omega` depends on `Classical.choice`.

The six word characterisations are stated here rather than beside the
definitions they characterise, `baseWord` and `stepWord` being declared in
`Cobham/Scan.lean`, which imports `Cobham/Basic.lean`.

## References

* [Cobham1965]

## Tags

Cobham, bounded recursion on notation, definition by cases
-/
```

Then `namespace Cobham`, `public section`, the declarations below, `end`,
`end Cobham`.

- [ ] **Step 2: Write `bits` and its four lemmas**

```lean
/-- Bit `j` of a scrutinee word, `false` past its end. -/
@[expose] def bits (p : ℕ) (w : List Bool) : Fin p → Bool :=
  fun j ↦ w.getD j false

/-- Peeling the low bit of a scrutinee's bit family. -/
theorem bits_succ (p : ℕ) (w : List Bool) :
    bits (p + 1) w = Fin.cons (w.getD 0 false) (bits p w.tail) := by
  refine funext fun i ↦ Fin.cases ?_ (fun _ ↦ ?_) i
  · rfl
  · match w with
    | [] => rfl
    | _ :: _ => rfl

/-- Dropping the low bit of a scrutinee's family. -/
theorem bits_succ_tail (p : ℕ) (w : List Bool) :
    (fun i : Fin p ↦ bits (p + 1) w i.succ) = bits p w.tail := by
  funext i
  match w with
  | [] => rfl
  | _ :: _ => rfl

/-- The bits of a spelled-out family are the family. -/
theorem bits_ofFn {p : ℕ} (f : Fin p → Bool) : bits p (List.ofFn f) = f :=
  funext fun j ↦ by simp [bits]

/-- A spelled-out bit family is the scrutinee truncated and zero-padded. -/
theorem ofFn_bits : ∀ (p : ℕ) (w : List Bool),
    List.ofFn (bits p w) = w.take p ++ List.replicate (p - w.length) false :=
  Nat.rec (fun w ↦ by
      rw [List.ofFn_zero, List.take_zero, Nat.zero_sub, List.replicate_zero,
        List.append_nil])
    (fun p ih w ↦ by
      rw [List.ofFn_succ, bits_succ_tail, ih]
      match w with
      | [] =>
        simp only [List.tail_nil, List.take_nil, List.nil_append,
          List.length_nil, Nat.sub_zero, List.replicate_succ]
        rfl
      | _ :: _ =>
        simp only [List.take_succ_cons, List.length_cons, Nat.succ_sub_succ,
          List.cons_append]
        rfl)
```

- [ ] **Step 3: Write the shift**

```lean
/-- A tree of arity two, carried to the predecessor of argument zero: its own
argument zero becomes `pred` of the outer one, its argument one the outer
argument one. -/
@[expose] def shiftRaw (e : sig.toPFunctor.W) : sig.toPFunctor.W :=
  WType.mk (.comp 2 2) fun d ↦
    match d with
    | .inl () => e
    | .inr i =>
      ![WType.mk (.comp 2 1) (fun c ↦
          match c with
          | .inl () => predRaw
          | .inr _ => WType.mk (.proj 2 0) Fin.elim0),
        WType.mk (.proj 2 1) Fin.elim0] i

/-- A shifted tree has arity two, whatever it shifts. -/
theorem wIndexRoot_shiftRaw (e : sig.toPFunctor.W) :
    sig.wIndexRoot (shiftRaw e) = 2 := rfl

/-- A shifted tree is admissible when what it shifts is, at arity two. -/
theorem wValid_shiftRaw (e : sig.toPFunctor.W) (he : sig.WValid e)
    (ha : sig.wIndexRoot e = 2) : sig.WValid (shiftRaw e) :=
  ⟨fun d ↦ match d with
    | .inl () => he
    | .inr i =>
      match i with
      | 0 =>
        ⟨fun c ↦ match c with
          | .inl () => pred.1.1.2
          | .inr _ => ⟨fun c ↦ c.elim0, funext fun c ↦ c.elim0⟩,
        funext fun c ↦ match c with
          | .inl () =>
            (sig.wIndexValid_index_eq_wIndexRoot predRaw).trans pred.2
          | .inr _ => rfl⟩
      | 1 => ⟨fun c ↦ c.elim0, funext fun c ↦ c.elim0⟩,
  funext fun d ↦ match d with
    | .inl () => (sig.wIndexValid_index_eq_wIndexRoot e).trans ha
    | .inr i => match i with | 0 => rfl | 1 => rfl⟩

/-- A shifted tree, carrying its admissibility. -/
@[expose] def shiftW (e : sig.W) (he : arity e = 2) : sig.W :=
  ⟨shiftRaw e.1, wValid_shiftRaw e.1 e.2 he⟩

/-- A shifted tree's arity, in the form `fst_eval` composes with. -/
theorem arity_shiftW (e : sig.W) (he : arity e = 2) :
    arity (shiftW e he) = 2 := rfl

/-- A shifted tree reads the tail of argument zero. -/
theorem semAt_shiftW (e : sig.W) (he : arity e = 2) (sel x : List Bool) :
    semAt 2 (shiftW e he) (arity_shiftW e he) ![sel, x] =
      semAt 2 e he ![sel.tail, x] := by
  refine congrArg (semAt 2 e he) (funext fun i : Fin 2 ↦ ?_)
  match i with
  | 0 =>
    match sel with
    | [] => rfl
    | b :: _ => cases b <;> rfl
  | 1 => rfl

/-- A shifted tree introduces no recursion of its own. -/
theorem recBounded_shiftW (e : sig.W) (he : arity e = 2) (hr : RecBounded e) :
    RecBounded (shiftW e he) :=
  ⟨trivial, fun d ↦ match d with
    | .inl () => hr
    | .inr i =>
      match i with
      | 0 => ⟨trivial, fun c ↦ match c with
          | .inl () => pred.1.2
          | .inr _ => ⟨trivial, fun c ↦ c.elim0⟩⟩
      | 1 => ⟨trivial, fun c ↦ c.elim0⟩⟩
```

- [ ] **Step 4: Build and lint**

Run: `lake build && lake lint`
Expected: both pass.

- [ ] **Step 5: Commit**

```bash
jj commit Geb/Mathlib/Computability/Cobham/Cases.lean \
  -m "feat(cobham): give the scrutinee's bits and the scrutinee shift"
```

---

### Task 8: `Cases.lean` — the case tree and its meaning

**Files:**

- Modify: `Geb/Mathlib/Computability/Cobham/Cases.lean`

**Interfaces:**

- Consumes: `Cobham.shiftRaw`, `Cobham.wValid_shiftRaw`,
  `Cobham.wIndexRoot_shiftRaw`, `Cobham.semAt_shiftW`, `Cobham.bits`,
  `Cobham.bits_succ` (Task 7); `Cobham.liftRaw`, `Cobham.wValid_liftRaw`,
  `Cobham.wIndexRoot_liftRaw`, `Cobham.stepWord` (Scan); `Cobham.condRaw`,
  `Cobham.cond` (Basic).
- Produces: `Cobham.casesRaw`, `Cobham.wIndexRoot_casesRaw`,
  `Cobham.wValid_casesRaw`, `Cobham.casesW`, `Cobham.arity_casesW`,
  `Cobham.casesSem`, `Cobham.casesSem_eq`.

- [ ] **Step 1: Write the case tree and its two structural lemmas**

Append to `Cases.lean`:

```lean
/-- The case tree over `p` bits of argument zero, applying the selected branch
to argument one. `cond`'s empty branch points at its head-`false` branch, which
reads a short scrutinee as zero-padded; each level shifts the scrutinee, so the
branch index is read off the low bits in order. -/
@[expose] def casesRaw :
    (p : ℕ) → ((Fin p → Bool) → sig.toPFunctor.W) → sig.toPFunctor.W :=
  Nat.rec (motive := fun p ↦
      ((Fin p → Bool) → sig.toPFunctor.W) → sig.toPFunctor.W)
    (fun br ↦ liftRaw (br Fin.elim0))
    (fun _ ih br ↦
      WType.mk (.comp 2 4) fun d ↦
        match d with
        | .inl () => condRaw
        | .inr i =>
          ![WType.mk (.proj 2 0) Fin.elim0,
            shiftRaw (ih (fun t ↦ br (Fin.cons false t))),
            shiftRaw (ih (fun t ↦ br (Fin.cons true t))),
            shiftRaw (ih (fun t ↦ br (Fin.cons false t)))] i)

/-- The case tree has arity two, whatever it branches over. -/
theorem wIndexRoot_casesRaw (p : ℕ) (br : (Fin p → Bool) → sig.toPFunctor.W) :
    sig.wIndexRoot (casesRaw p br) = 2 := by
  cases p with
  | zero => exact wIndexRoot_liftRaw _
  | succ _ => rfl

/-- The case tree is admissible when every branch is, at arity one. The motive
generalizes over the branch family, the recursive calls reindexing it. -/
theorem wValid_casesRaw : ∀ (p : ℕ) (br : (Fin p → Bool) → sig.toPFunctor.W),
    (∀ v, sig.WValid (br v)) → (∀ v, sig.wIndexRoot (br v) = 1) →
    sig.WValid (casesRaw p br) :=
  Nat.rec (fun _ hv ha ↦ wValid_liftRaw _ (hv _) (ha _))
    (fun p ih _ hv ha ↦
      ⟨fun d ↦ match d with
        | .inl () => cond.1.1.2
        | .inr i =>
          match i with
          | 0 => ⟨fun c ↦ c.elim0, funext fun c ↦ c.elim0⟩
          | 1 => wValid_shiftRaw _ (ih _ (fun _ ↦ hv _) (fun _ ↦ ha _))
              (wIndexRoot_casesRaw p _)
          | 2 => wValid_shiftRaw _ (ih _ (fun _ ↦ hv _) (fun _ ↦ ha _))
              (wIndexRoot_casesRaw p _)
          | 3 => wValid_shiftRaw _ (ih _ (fun _ ↦ hv _) (fun _ ↦ ha _))
              (wIndexRoot_casesRaw p _),
      funext fun d ↦ match d with
        | .inl () => (sig.wIndexValid_index_eq_wIndexRoot condRaw).trans cond.2
        | .inr i =>
          match i with
          | 0 => rfl
          | 1 => (sig.wIndexValid_index_eq_wIndexRoot _).trans
              (wIndexRoot_shiftRaw _)
          | 2 => (sig.wIndexValid_index_eq_wIndexRoot _).trans
              (wIndexRoot_shiftRaw _)
          | 3 => (sig.wIndexValid_index_eq_wIndexRoot _).trans
              (wIndexRoot_shiftRaw _)⟩)
```

- [ ] **Step 2: Write the meaning and the semantic theorem**

```lean
/-- The case tree over expressions, carrying its admissibility. -/
@[expose] def casesW (p : ℕ) (br : (Fin p → Bool) → COf 1) : sig.W :=
  ⟨casesRaw p (fun v ↦ (br v).1.1.1),
    wValid_casesRaw p _ (fun v ↦ (br v).1.1.2) (fun v ↦ (br v).2)⟩

/-- The case tree's arity, in the form `fst_eval` composes with. -/
theorem arity_casesW (p : ℕ) (br : (Fin p → Bool) → COf 1) :
    arity (casesW p br) = 2 :=
  wIndexRoot_casesRaw p _

/-- The meaning of a case tree at its arity, read at the raw tree. -/
@[expose] def casesSem (p : ℕ) (br : (Fin p → Bool) → COf 1) : Sem 2 :=
  semAt 2 (casesW p br) (arity_casesW p br)

/-- A case tree applies the branch its scrutinee selects to argument one, the
scrutinee zero-padded past its end. -/
theorem casesSem_eq : ∀ (p : ℕ) (br : (Fin p → Bool) → COf 1)
    (sel x : List Bool),
    casesSem p br ![sel, x] = stepWord (br (bits p sel)) x :=
  Nat.rec
    (fun br sel x ↦ by
      have hb : bits 0 sel = Fin.elim0 := funext fun i ↦ i.elim0
      rw [hb]
      change semAt 1 (br Fin.elim0).1.1 (br Fin.elim0).2 (fun _ ↦ x) = _
      exact congrArg _ (funext fun i ↦ match i with | ⟨0, _⟩ => rfl))
    (fun p ih br sel x ↦ by
      rw [bits_succ]
      match sel with
      | [] =>
        have h : casesSem (p + 1) br ![[], x] =
            casesSem p (fun s ↦ br (Fin.cons false s)) ![[], x] :=
          semAt_shiftW (casesW p fun s ↦ br (Fin.cons false s))
            (arity_casesW p _) [] x
        rw [h, ih]
        rfl
      | true :: t =>
        have h : casesSem (p + 1) br ![true :: t, x] =
            casesSem p (fun s ↦ br (Fin.cons true s)) ![t, x] :=
          semAt_shiftW (casesW p fun s ↦ br (Fin.cons true s))
            (arity_casesW p _) (true :: t) x
        rw [h, ih]
        rfl
      | false :: t =>
        have h : casesSem (p + 1) br ![false :: t, x] =
            casesSem p (fun s ↦ br (Fin.cons false s)) ![t, x] :=
          semAt_shiftW (casesW p fun s ↦ br (Fin.cons false s))
            (arity_casesW p _) (false :: t) x
        rw [h, ih]
        rfl)
```

- [ ] **Step 3: Build and lint**

Run: `lake build && lake lint`
Expected: both pass.

- [ ] **Step 4: Commit**

```bash
jj commit Geb/Mathlib/Computability/Cobham/Cases.lean \
  -m "feat(cobham): characterise the case tree's meaning"
```

---

### Task 9: `Cases.lean` — the expression and the word characterisations

**Files:**

- Modify: `Geb/Mathlib/Computability/Cobham/Cases.lean`

**Interfaces:**

- Consumes: everything from Tasks 4 to 8; `Cobham.transport_transport`,
  `Cobham.zeroAtOf`, `Cobham.baseWord`, `Cobham.stepWord`,
  `Cobham.recBounded_liftRaw`.
- Produces: `Cobham.recBounded_casesW`, `Cobham.cases`, `Cobham.casesOf`,
  `Cobham.casesSem_eq_eval`, `Cobham.stepWord_predIterOf`,
  `Cobham.stepWord_prependOf`, `Cobham.baseWord_prependOf`,
  `Cobham.baseWord_constAtOf`, `Cobham.stepWord_constAtOf`,
  `Cobham.stepWord_diagOf`.

These characterisations name `baseWord` and `stepWord`, which are declared in
`Cobham/Scan.lean`; `Basic.lean` is upstream of `Scan.lean`, so they cannot be
stated beside the definitions they characterise.

- [ ] **Step 1: Write the recursion bound and the expression**

```lean
/-- The case tree carries the branches' recursions and no other. -/
theorem recBounded_casesW : ∀ (p : ℕ) (br : (Fin p → Bool) → COf 1),
    RecBounded (casesW p br) :=
  Nat.rec (fun br ↦ recBounded_liftRaw (br Fin.elim0))
    (fun p ih br ↦
      ⟨trivial, fun d ↦ match d with
        | .inl () => cond.1.2
        | .inr i =>
          match i with
          | 0 => ⟨trivial, fun c ↦ c.elim0⟩
          | 1 => recBounded_shiftW _ (arity_casesW p _)
              (ih (fun t ↦ br (Fin.cons false t)))
          | 2 => recBounded_shiftW _ (arity_casesW p _)
              (ih (fun t ↦ br (Fin.cons true t)))
          | 3 => recBounded_shiftW _ (arity_casesW p _)
              (ih (fun t ↦ br (Fin.cons false t)))⟩)

/-- The case tree as an expression. Definition by cases imposes no condition on
the expressions it selects among: every node the recursion introduces is a
`comp`, whose `RecBoundedValue` is `True`, over `proj` together with the trees
underlying `cond` and `pred`, which carry their own recursion bounds already. -/
@[expose] def cases (p : ℕ) (br : (Fin p → Bool) → COf 1) : C :=
  ⟨casesW p br, recBounded_casesW p br⟩

/-- `cases` at its declared arity. -/
@[expose] def casesOf (p : ℕ) (br : (Fin p → Bool) → COf 1) : COf 2 :=
  ⟨cases p br, arity_casesW p br⟩

/-- The meaning read at the raw tree is the meaning the expression carries.
Unlike the scan combinator's counterpart this is not a `rfl`: `arity_casesW` is
a theorem rather than a definitional equality, so the transport it carries is
opaque. -/
theorem casesSem_eq_eval (p : ℕ) (br : (Fin p → Bool) → COf 1) :
    transport (casesOf p br).2 (casesOf p br).1.eval = casesSem p br :=
  transport_transport (fst_eval (casesW p br)) (arity_casesW p br)
    (eval (casesW p br)).2
```

- [ ] **Step 2: Write the word characterisations of the `Basic.lean` combinators**

```lean
/-- The iterated predecessor drops `k` bits. -/
theorem stepWord_predIterOf : ∀ (k : ℕ) (u : List Bool),
    stepWord (predIterOf k) u = u.drop k :=
  Nat.rec (fun _ ↦ rfl)
    (fun j ih u ↦ by
      have hfun : (fun _ : Fin 1 ↦ stepWord (predIterOf j) u) =
          ![stepWord (predIterOf j) u] :=
        funext fun i ↦ match i with | ⟨0, _⟩ => rfl
      have h : stepWord (predIterOf (j + 1)) u =
          predSem ![stepWord (predIterOf j) u] := congrArg predSem hfun
      rw [h, predSem_eq, ih u, List.tail_drop])

/-- Prepending a word prepends it to the value a step contributes. -/
theorem stepWord_prependOf (e : COf 1) (r : List Bool) :
    ∀ u : List Bool, stepWord (prependOf u e) r = u ++ stepWord e r :=
  List.rec rfl (fun b v ih ↦ by
    change b :: stepWord (prependOf v e) r = _
    rw [ih]
    rfl)

/-- Prepending a word to a nullary expression prepends it to the value. -/
theorem baseWord_prependOf (e : COf 0) :
    ∀ u : List Bool, baseWord (prependOf u e) = u ++ baseWord e :=
  List.rec rfl (fun b v ih ↦ by
    change b :: baseWord (prependOf v e) = _
    rw [ih]
    rfl)

/-- The constant word is the base it contributes. -/
theorem baseWord_constAtOf (u : List Bool) : baseWord (constAtOf 0 u) = u :=
  (baseWord_prependOf (zeroAtOf 0) u).trans (List.append_nil u)

/-- The constant word is the value a step contributes, whatever it reads. -/
theorem stepWord_constAtOf (u r : List Bool) :
    stepWord (constAtOf 1 u) r = u :=
  (stepWord_prependOf (zeroAtOf 1) r u).trans (List.append_nil u)

/-- The diagonal reads its argument in both positions. -/
theorem stepWord_diagOf (e : COf 2) (u : List Bool) :
    stepWord (diagOf e) u = semAt 2 e.1.1 e.2 ![u, u] := by
  have hfun : (fun _ : Fin 2 ↦ u) = ![u, u] :=
    funext fun i ↦ match i with | 0 => rfl | 1 => rfl
  exact congrArg (semAt 2 e.1.1 e.2) hfun
```

- [ ] **Step 3: Build, test and lint**

Run: `lake build && lake test && lake lint`
Expected: all three pass. The module docstring written in Task 7 already names
every declaration this task adds.

- [ ] **Step 4: Commit**

```bash
jj commit Geb/Mathlib/Computability/Cobham/Cases.lean \
  -m "feat(cobham): give definition by cases as an expression of the class"
```

---

### Task 10: The test mirror

**Files:**

- Create: `GebTests/Mathlib/Computability/Cobham/Cases.lean`

**Interfaces:**

- Consumes: everything `Cases.lean` produces.
- Produces: nothing consumed elsewhere.

The mirror names a `def` value built from the module under test rather than
asserting inside an anonymous `example`: `lake shake` infers a module's imports
from the constants its olean references, and an import used only by an
`example` leaves no such reference and is reported as removable.

- [ ] **Step 1: Create the module**

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Computability.Cobham.Cases

/-!
# Definition by cases over Cobham's class, exercised

Fixtures for `Geb/Mathlib/Computability/Cobham/Cases.lean`: a branch family
distinct at every index, and the combinators the branches are built from.
`combinators_apply` names `casesOf`, which is the constant `lake shake` infers
the import from.

## Main definitions

* `sampleBranches`, `sampleBranchesOneBit` — branch families over two bits and
  over one.

## Main statements

* `sampleCases_dispatch` — each branch is selected by its own scrutinee.
* `sampleCases_padding` — a short scrutinee reads as zero-padded and a long one
  ignores its high bits.
* `combinators_apply` — the iterated predecessor, the prepended and constant
  words, and the diagonal, at literal arguments.

## Tags

Cobham, bounded recursion on notation, definition by cases
-/

set_option linter.privateModule false

open Cobham
```

The module docstring stands immediately after the imports and before
`set_option`, which is where the sibling mirrors put theirs and where
`linter.style.header` requires it.

- [ ] **Step 2: Write the fixtures and the assertions**

```lean
/-- A branch family over two bits, distinct at every index. -/
def sampleBranches : (Fin 2 → Bool) → COf 1 := fun v ↦
  constAtOf 1 (if v 0 then if v 1 then [true, true] else [true] else
    if v 1 then [false] else [])

/-- A one-bit branch family, for the diagonal. -/
def sampleBranchesOneBit : (Fin 1 → Bool) → COf 1 := fun v ↦
  constAtOf 1 (if v 0 then [true] else [])

/-- Each of the four branches is selected by its own scrutinee. -/
theorem sampleCases_dispatch :
    casesSem 2 sampleBranches ![[false, false], []] = [] ∧
      casesSem 2 sampleBranches ![[true, false], []] = [true] ∧
      casesSem 2 sampleBranches ![[false, true], []] = [false] ∧
      casesSem 2 sampleBranches ![[true, true], []] = [true, true] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    rw [casesSem_eq] <;> rfl

/-- A scrutinee shorter than the dispatch width reads as zero-padded, and one
longer than it ignores the high bits. -/
theorem sampleCases_padding :
    casesSem 2 sampleBranches ![[], []] = [] ∧
      casesSem 2 sampleBranches ![[true], []] = [true] ∧
      casesSem 2 sampleBranches ![[true, true, true], []] = [true, true] := by
  refine ⟨?_, ?_, ?_⟩ <;>
    rw [casesSem_eq] <;> rfl

/-- The combinators the branches are built from. The first two need an explicit
`rfl` after the rewrite: `rw` closes only by its own `rfl` at reducible
transparency, which leaves the list computation standing. -/
theorem combinators_apply :
    stepWord (predIterOf 2) [true, false, true] = [true] ∧
      stepWord (prependOf [false, true] (predIterOf 1)) [true, false] =
        [false, true, false] ∧
      stepWord (constAtOf 1 [true]) [false, false] = [true] ∧
      baseWord (constAtOf 0 [true, false]) = [true, false] ∧
      stepWord (diagOf (casesOf 1 sampleBranchesOneBit)) [true] = [true] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [stepWord_predIterOf]
    rfl
  · rw [stepWord_prependOf, stepWord_predIterOf]
    rfl
  · rw [stepWord_constAtOf]
  · rw [baseWord_constAtOf]
  · rw [stepWord_diagOf]
    rfl
```

- [ ] **Step 3: Build the mirror**

Run: `lake build GebTests.Mathlib.Computability.Cobham.Cases`
Expected: success. If a `rfl` fails to close a dispatch case, report the goal
rather than replacing the assertion with a weaker one.

- [ ] **Step 4: Run the test suite and both linters**

Run: `lake test && lake lint && lake lint -- GebTests`
Expected: all three pass. The bare `lake lint` covers `Geb` only, so the second
invocation is what puts this mirror under the axiom linter.

- [ ] **Step 5: Commit**

```bash
jj commit GebTests/Mathlib/Computability/Cobham/Cases.lean \
  -m "test(cobham): mirror definition by cases"
```

---

### Task 11: Index modules and documentation

**Files:**

- Modify: `Geb/Mathlib/Computability/Cobham.lean`
- Modify: `GebTests/Mathlib/Computability/Cobham.lean`
- Modify: `docs/index.md`
- Modify: `TODO.md`

`lakefile.toml` declares `globs = ["Geb.*"]` and `globs = ["GebTests.*"]`, so
lake builds both new modules whether or not the indexes name them. The imports
are added for the re-export the narrow-and-deep structure depends on —
`CONTRIBUTING.md` § Repo structure, one indexing file per directory — not for
reachability.

- [ ] **Step 1: Add the imports**

To `Geb/Mathlib/Computability/Cobham.lean`, in the existing alphabetical run:

```lean
public import Geb.Mathlib.Computability.Cobham.Cases
```

To `GebTests/Mathlib/Computability/Cobham.lean`, matching the plain `import`
its three existing entries use:

```lean
import GebTests.Mathlib.Computability.Cobham.Cases
```

- [ ] **Step 2: Add the `docs/index.md` entries**

Insert immediately after the `Geb/Mathlib/Computability/Cobham/Tree.lean`
entry, which it is a sibling of, both depending on `Cobham/Basic.lean` and
`Cobham/Scan.lean`:

```text
- `Geb/Mathlib/Computability/Cobham/Cases.lean` — definition by cases: a
  combinator selecting among `2 ^ p` expressions of arity one by the low `p`
  bits of a scrutinee, and applying the selected one to a second argument.
  `casesRaw` is built by recursion on the number of bits dispatched on, each
  level a `cond` node whose scrutinee is argument zero and whose branches
  shift that argument into the recursive subtree; `wValid_casesRaw` gives
  admissibility from the branches' own, and `recBounded_casesW` the recursion
  bound, so the combinator imposes no condition on what it selects among.
  `casesSem_eq` identifies the meaning with the branch the scrutinee selects.
  Also the words the combinators of `Cobham/Basic.lean` contribute:
  `stepWord_predIterOf`, `stepWord_prependOf`, `baseWord_constAtOf`,
  `stepWord_constAtOf` and `stepWord_diagOf`. Depends on
  `Geb.Mathlib.Computability.Cobham.Basic` and
  `Geb.Mathlib.Computability.Cobham.Scan`.
```

Then revise the existing `Cobham/Basic.lean` entry to record `semAt`, the
`zeroAt` family arriving from `Cobham/Tree.lean`, and the `predIter`,
`prepend`, `constAt` and `diag` families; and the `Cobham/Tree.lean` entry to
record the `zeroAt` family leaving.

- [ ] **Step 3: Revise `TODO.md`**

In § Extensions of the tree recognizers, insert immediately before the `B6`
bullet. The case combinator carries no letter of its own, being the shared
machinery B6 and B3 are built from rather than a roadmap item:

```text
- **The case combinator is done.**
  `Geb/Mathlib/Computability/Cobham/Cases.lean` gives definition by cases over
  a fixed number of scrutinee bits, and `Cobham/Basic.lean` the constant-word,
  iterated-predecessor and diagonal combinators its branches are built from.
  B6 and B3 both consume them. See docs/index.md.
```

Make that last reference a link, `docs/index.md` in both halves, as the B1 and
B2 bullets beside it do; it is written bare here only so that
`scripts/check-md-links.sh`, which does not skip fenced blocks, resolves it
against `TODO.md`'s location rather than this file's.

Then append to the paragraph beginning `Deferred:`:

```text
Also deferred: `Cobham/Tree.lean`'s `oneAtOf` and `falseAtOf` duplicate
`constAtOf`, and its `predPred` duplicates `predIter 2`. Each is left in place
because substituting the general form changes the definitional unfolding that
`combSem_nil` and `isTreeSem_eq_eval` read through, and whether those proofs
survive the substitution is unmeasured.
```

- [ ] **Step 4: Check the Markdown gates**

Run:

```bash
doctoc --dryrun --update-only . && \
  npx markdownlint-cli2 '**/*.md' && \
  scripts/check-md-links.sh
```

Expected: no markdownlint issues, all link targets resolve. `--dryrun` is the
form `scripts/pre-push.sh` runs. If it reports a table of contents out of date,
regenerate with `doctoc --notitle --update-only .`, which is the style the
committed documents carry.

- [ ] **Step 5: Build and commit**

Run: `lake build`

```bash
jj commit Geb/Mathlib/Computability/Cobham.lean \
  GebTests/Mathlib/Computability/Cobham.lean docs/index.md TODO.md \
  -m "doc(cobham): catalogue definition by cases"
```

---

### Task 12: Verify the segment

**Files:** none changed.

- [ ] **Step 1: Build, test and lint both libraries**

Run: `lake build && lake test && lake lint && lake lint -- GebTests`
Expected: all four pass. `lakefile.toml` sets `lintDriverArgs = ["Geb"]`, so
the bare `lake lint` does not reach the new mirror; the second invocation is
what puts `GebTests` under the axiom linter.

- [ ] **Step 2: Run the pre-push checklist in full**

Run: `scripts/pre-push.sh`
Expected: passes. This adds the import linter, `lake shake`, and the Markdown,
table-of-contents and link checks to the gates already run.

If `lake shake` reports an import of `Cases.lean` as removable in the mirror,
the cause is an assertion made inside an anonymous `example` rather than a
named `def`; fix the mirror rather than suppressing the report.

- [ ] **Step 3: Remove this plan**

[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape orders a branch as
spec and plan, then implementation, then the commits removing them. This plan
covers segment 1 only and is spent once segment 1 lands:

```bash
rm docs/superpowers/plans/2026-08-10-cobham-cases.md
jj commit docs/superpowers/plans/2026-08-10-cobham-cases.md \
  -m "doc(cobham): remove the transient plan"
```

The design document
`docs/superpowers/specs/2026-08-10-cobham-cases-fold-ranked-design.md` is
**not** removed here: it covers segments 2 and 3 as well, and is removed in the
final commits of the last of them.

- [ ] **Step 4: Re-run the Markdown gates**

Run:

```bash
doctoc --dryrun --update-only . && \
  npx markdownlint-cli2 '**/*.md' && \
  scripts/check-md-links.sh
```

Expected: all three pass. Removing the plan removes a link target; confirm
nothing else pointed at it.

- [ ] **Step 5: Set the segment bookmark**

```bash
jj bookmark create feat/cobham-cases -r @-
```

Do not push. [AGENTS.md](../../../AGENTS.md) § No `jj git push` without user
line-by-line review binds: the user reviews the segment's diff before it goes
anywhere, first creation included.
