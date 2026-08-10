# Generic ranked recognizer implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` (recommended) or
> `superpowers:executing-plans` to implement this plan task-by-task. Steps use
> checkbox (`- [ ]`) syntax for tracking.

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Provenance of the code in this plan](#provenance-of-the-code-in-this-plan)
- [The citation gate, discharged](#the-citation-gate-discharged)
- [Global Constraints](#global-constraints)
- [Facts this plan rests on](#facts-this-plan-rests-on)
- [Deviations from the design](#deviations-from-the-design)
- [File structure](#file-structure)
- [Testing convention](#testing-convention)
  - [Task 1: The largest arity](#task-1-the-largest-arity)
  - [Task 2: The arity a block yields](#task-2-the-arity-a-block-yields)
  - [Task 3: The scan's invariants](#task-3-the-scans-invariants)
  - [Task 4: The state as a bitstring](#task-4-the-state-as-a-bitstring)
  - [Task 5: Inverting the state word](#task-5-inverting-the-state-word)
  - [Task 6: The step's decomposition](#task-6-the-steps-decomposition)
  - [Task 7: The scan as an expression](#task-7-the-scan-as-an-expression)
  - [Task 8: The verdict test](#task-8-the-verdict-test)
  - [Task 9: The recognizer and the bridge](#task-9-the-recognizer-and-the-bridge)
  - [Task 10: The test mirror](#task-10-the-test-mirror)
  - [Task 11: The catalogue and the roadmap](#task-11-the-catalogue-and-the-roadmap)
  - [Task 12: Verification, and the plan's removal](#task-12-verification-and-the-plans-removal)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

**Goal:** Express `RankedAlphabet.validBool`, the validity scan of the preorder
encoding, as a member of Cobham's class at an arbitrary ranked alphabet, and
identify it at the two-symbol alphabet with the recognizer
`Cobham/Tree.lean` carries. This closes B6 of
[TODO.md](../../../TODO.md) § Extensions of the tree recognizers.

**Architecture:** The scan's state — a liveness flag, an incomplete block, and
a count of pending subterms — is laid out as a bitstring whose bounded part
leads and whose unbounded count trails, so that a member of the class, which
reaches only a bounded prefix, can rewrite it. Each step decodes the leading
bits with the case combinator of `Cobham/Cases.lean`, then prepends a
statically known word and drops a statically known number of bits. The scan
combinator of `Cobham/Scan.lean` carries the recursion, and a verdict test
composed onto it decides acceptance.

**Tech Stack:** Lean 4 (`lean-toolchain`), mathlib, `lake`.

## Provenance of the code in this plan

Every declaration of Tasks 4 to 9 was compiled at a symbolic `RankedAlphabet`
in `Geb/Internal/RankedTreeSpike.lean`, as was every assertion of Task 10.
Transcribe that code as given rather than composing it afresh; where a proof
looks longer than it needs to be, the shorter form was tried and did not
compile.

**The prototype is deleted in Task 1, before anything else.** It declares
`maxArity`, `arity_le_maxArity`, `le_maxArity_of_arOf_eq_some`,
`length_buf_scanFinal_lt`, `depth_scanFinal_le_length` and
`valid_iff_scanFinal` inside `namespace RankedAlphabet`, and reaches the
modules Tasks 1 to 3 add those same names to, `Ranked/Preorder.lean` and
`Ranked/Binary.lean` directly and `Ranked/{Basic,Code}.lean` through them.
`lakefile.toml`'s `Geb.*` glob builds it whether or not `Geb/Internal.lean`
imports it, so from Task 1's first addition onward it fails to elaborate with
a duplicate declaration, and
a bare `lake build` — hence `scripts/pre-push.sh` and CI — fails at every
commit until it is gone. The targeted builds each task runs would not catch
this, the prototype being in none of their closures. Nothing is lost by
removing it first: every declaration it carries is transcribed below, and it
remains in the branch's history.

The mirror assertions of Tasks 1 to 3 were compiled there too, against the
prototype's own copies of `narrowAlphabet` and `sampleAlphabet` rather than
the `GebTests/` fixtures, which `Geb/Internal/` may not import. The copies are
the same alphabets written out again, so the assertions carry over; that they
elaborate in the mirror's own import closure is what Tasks 1 to 3 Step 5
checks.

Each declaration's axioms were measured by `#print axioms` on the prototype,
not by `lake lint`: the prototype is outside `Geb/Internal.lean`'s import
closure and so escapes the umbrella the linter walks. Every measurement fell
within `{propext, Quot.sound}`. Every module the tasks below touch is inside
that closure — `Geb/Mathlib/Data/Tree/Ranked/` always was, and
`Cobham/RankedTree.lean` is from Task 4 Step 3, when the index imports it — so
each source task runs `lake lint` as well as `lake build`, rather than
deferring the axiom gate to Task 12.

## The citation gate, discharged

[The design](../specs/2026-08-10-cobham-cases-fold-ranked-design.md)
§ Risks and open questions requires a literature search for the statement this
segment realizes, before the module docstring is written, and the recording of
any key found in `docs/references.bib`. That search was run: `theoremsearch`
for the containment of ranked-term preorder spellings in Cobham's class, for
the same over tree languages and the function algebra, and for the
characterisation of the polynomial-time functions by bounded recursion on
notation; and `arxiv-mcp-server` for bounded recursion on notation over terms.
No statement of the containment was located. It is an instance of Cobham's
characterisation of the polynomial-time functions, so the module delivers an
explicit expression rather than new mathematics, and its docstring claims
neither novelty nor a source beyond the class itself. No key is added to
`docs/references.bib` for this segment. The search is not repeated during
execution; segment 3's statement is a separate gate and is not settled here.

## Global Constraints

- **No `noncomputable`; `Classical.choice` excluded.** Every declaration
  measures within `{propext, Quot.sound}`, which `lake lint` enforces.
- **Recursion through recursors.** No `def` calls itself; no `induction`
  tactic. Every recursion is an explicit `Nat.rec`, `List.rec` or `WType.elim`.
- **No self-prefix outside import lines.** `Geb.Mathlib.` appears only in
  `^import` lines.
- **Every `def`, and every theorem of public interest, carries a docstring.**
  Each module carries the sections
  [docs/rules/lean-coding.md](../../rules/lean-coding.md) § Documentation
  mandates there, in order and non-vacuously.
- **Line length 100 in `.lean`, 80 in `.md`** prose; Markdown code blocks and
  tables are exempt.
- **Commit subjects** follow
  [docs/rules/ci-and-workflow.md](../../rules/ci-and-workflow.md)
  § Commit-message convention: imperative present, no capital, no trailing
  period, type from the list.
- **`jj` for every state-mutating VCS operation.** Local commits are fine; no
  push.
- **A bare `simp` that changes the goal must be terminal**, `tac1 <;> tac2`
  where `tac1` leaves one goal is an error, and a `show` that changes the goal
  must be `change`. Over- and under-specifying a `simp only` argument list are
  both errors.

## Facts this plan rests on

Each cost a failed build in the prototype. They are not optional style notes.

1. **A projection of a `Scan` constructor does not reduce syntactically.**
   After `obtain ⟨buf, depth, live⟩ := s`, or under `{ s with depth := … }`,
   the goal carries `{ buf := buf, … }.live` rather than `live`. A `cases` on a
   scrutinee written in the fields then matches nothing and silently splits
   nothing, and the following `rw` fails with a pattern that is visibly present
   in the printed goal. `dsimp only` reduces them, and is needed once after the
   definitions are unfolded and again after each `cases`.
2. **`rw` closes a goal by `rfl` at reducible transparency only.** A branch
   ending in an equation true by unfolding an `@[expose] def` needs an explicit
   `rfl` after the rewrite.
3. **`rw [List.length_cons]` inside a chain rewrites the first matching
   instantiation**, which under `scanStep`'s unfolding is the block's length
   rather than the word's. Supply the word's length as a `have` for `omega`.
4. **`List.takeWhile_replicate` was measured to depend on
   `Classical.choice`**, through `List.filter_replicate`, whose proof is a
   `simp_all` and so does not show it in the source. This is a fourth route
   beyond the three the design names; the two-case reduction that replaces it
   measures clean. `DecidableEq (Fin n → Bool)` was measured the same way and
   does depend on `Classical.choice`, while `DecidableEq (List Bool)` depends
   on nothing, which is what the decisions below are taken over.
5. **Two concurrent `lake build` invocations corrupt package `.trace` files**
   and fail unrelated mathlib targets. The `lean-lsp` tools that run Lean count
   as a second process. Build alone.

## Deviations from the design

[The design](../specs/2026-08-10-cobham-cases-fold-ranked-design.md) § Segment 2
is the specification. The prototype established the following departures from
its stated code; each is carried into this plan.

| Design | This plan | Why |
| --- | --- | --- |
| `constAtOf (stateWord R ⟨[], 0, true⟩)` | `constAtOf 0 (stateWord R ⟨[], 0, true⟩)` | `constAtOf` takes the arity first |
| `length_rankedSem_le … ≤ w.length + R.width + 1` | `≤ w.length + (R.width + 1)` | `Cobham.scan` asks for `≤ w.length + growth` at `growth = R.width + 1`; the other association needs an extra rewrite |
| `acceptTestRaw : sig.toPFunctor.W` | dropped | `casesOf` and `diagOf` deliver `COf` directly, so the verdict needs no raw tree and no admissibility of its own |
| `rankedSem_def` | dropped | `rw [← rankedSem]` rewrites by the generated equation lemma; a restatement would be a second name for it |
| a definition and four statements in `Data/Tree/Ranked/` | a definition and five statements | `valid_iff_scanFinal` is needed to relate `Valid` to the three field conditions the state word exposes |
| — | `ofFn_bits_stateWord`, `dropWhile_bufBits`, `stepWord_rankedStep_of_lt`, `ofFn_bits_stateWord_eq_iff`, `stepWord_acceptTest` | intermediate statements the design folds into prose |
| `isRankedSem_apply` by `change` / `generalize` / match | by `congrArg … (funext …)` | the design describes `isTreeSem_apply`'s shape, which reconciles a `pred` node; here the head is `diagOf (casesOf …)` and only the environment differs |

`ofFn_bits_stateWord` is stated at an arbitrary window `p = 1 + R.width + m`
rather than at `dispatchWidth R`, so that the dispatch (`m = R.maxArity + 1`)
and the verdict (`m = 2`) share one proof.

Dropping `rankedSem_def` leaves the tree carrying two accounts of the same
mechanism: `Cobham/Tree.lean`'s `combSem_def` docstring says a `def` carries
no equation lemma, while `length_rankedSem_le` here rewrites by
`rw [← rankedSem]`, which is that equation lemma. Lean generates one for both.
Lean generates an equation lemma for a non-recursive `def`, so the sibling
module's docstring is the inaccurate half; what is untried is only whether
`rw [combSem]` closes where `combSem_def` is used, `combSem` taking no
argument. Task 11 records that check as a deferral in
[TODO.md](../../../TODO.md) rather than editing `Tree.lean` here.

## File structure

| File | Responsibility |
| --- | --- |
| `Geb/Mathlib/Data/Tree/Ranked/Basic.lean` | gains the largest arity and its bound |
| `Geb/Mathlib/Data/Tree/Ranked/Code.lean` | gains the bound on an arity a block yields |
| `Geb/Mathlib/Data/Tree/Ranked/Preorder.lean` | gains the scan's two invariants and validity as field conditions |
| `Geb/Mathlib/Computability/Cobham/RankedTree.lean` | new: the state layout, the decoder, the step, the scan, the verdict, the bridge |
| `Geb/Mathlib/Computability/Cobham.lean` | imports the new module |
| `GebTests/Mathlib/Data/Tree/Ranked/{Basic,Code,Preorder}.lean` | mirror the additions |
| `GebTests/Mathlib/Computability/Cobham/RankedTree.lean` | new: mirrors the new module |
| `GebTests/Mathlib/Computability/Cobham.lean` | imports the new mirror |
| `docs/index.md`, `TODO.md` | catalogue the module and record B6 as done |

## Testing convention

A Lean theorem is its own specification, so the source tasks below do not open
with a failing test: the statement is written and the build is the check that
it holds. The mirrors under `GebTests/` carry what a statement cannot — that
the declarations reduce in the kernel at a concrete alphabet, and that they
agree with `validBool` over an enumeration. Each mirror names a `def` value
built from the module under test rather than asserting inside an anonymous
`example`, `lake shake` inferring imports from the constants an olean
references and reporting an import used only by an `example` as removable.
Named theorems whose statements mention those constants satisfy this as a
named `def` does, which is how the existing mirrors under
`GebTests/Mathlib/Data/Tree/Ranked/` are written; the mirrors under
`GebTests/Mathlib/Computability/Cobham/` name a `def` besides, and the new
mirror follows its own directory.

---

### Task 1: The largest arity

**Files:**

- Delete: `Geb/Internal/RankedTreeSpike.lean`
- Modify: `Geb/Mathlib/Data/Tree/Ranked/Basic.lean`
- Test: `GebTests/Mathlib/Data/Tree/Ranked/Basic.lean`

**Interfaces:**

- Consumes: `RankedAlphabet.arity`, `RankedAlphabet.card`.
- Produces: `RankedAlphabet.maxArity (R : RankedAlphabet) : ℕ` and
  `RankedAlphabet.arity_le_maxArity (R : RankedAlphabet) (i : Fin R.card) :
  R.arity i ≤ R.maxArity`.

- [ ] **Step 1: Remove the prototype, and commit that alone**

```bash
rm Geb/Internal/RankedTreeSpike.lean
lake build
jj describe -m "chore(cobham): remove the ranked recognizer prototype"
jj new
```

It must go before the first name below is added: it declares the same six
names in the same namespace and imports the modules they are added to, so the
tree stops building otherwise. See § Provenance.

- [ ] **Step 2: Add the definition and its bound**

Inside the existing `namespace RankedAlphabet` / `public section` block of
`Geb/Mathlib/Data/Tree/Ranked/Basic.lean`, after `size_le_sum_ofFn`, written
unprefixed:

```lean
/-- The largest arity of a symbol of the alphabet, and zero at an alphabet
with no symbols. -/
@[expose] def maxArity (R : RankedAlphabet) : ℕ :=
  (List.ofFn R.arity).foldr max 0

/-- Every symbol's arity is at most the largest. Proved from `List.rec` and the
two `Nat.le_max` lemmas rather than through the ordered-algebra API, which is
the discipline `size_le_sum_ofFn` records for the sum. -/
theorem arity_le_maxArity (R : RankedAlphabet) (i : Fin R.card) :
    R.arity i ≤ R.maxArity := by
  have hmem : ∀ (l : List ℕ) (x : ℕ), x ∈ l → x ≤ l.foldr max 0 := fun l ↦
    List.rec (fun x hx ↦ absurd hx (by simp))
      (fun a t iht x hx ↦ by
        rcases List.mem_cons.mp hx with h | h
        · subst h
          exact Nat.le_max_left _ _
        · exact Nat.le_trans (iht x h) (Nat.le_max_right _ _)) l
  exact hmem _ _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
```

- [ ] **Step 3: Record it in the module docstring**

In the `## Main definitions` list add, after the `Term.size` entry:

```text
* `RankedAlphabet.maxArity` — the largest arity of a symbol.
```

In the `## Main statements` list add, after the `size_le_sum_ofFn` entry:

```text
* `RankedAlphabet.arity_le_maxArity` — every symbol's arity is at most the
  largest.
```

- [ ] **Step 4: Build**

Run: `lake build Geb.Mathlib.Data.Tree.Ranked.Basic` and then `lake lint`, one
after the other rather than concurrently.
Expected: both succeed with no error and no warning.

- [ ] **Step 5: Mirror the definition**

In `GebTests/Mathlib/Data/Tree/Ranked/Basic.lean`, before the `end` closing the
`@[expose] public section`, not after it: a theorem outside that section trips
`linter.privateModule`, which is an error here.

```lean
/-- The largest arity at an alphabet whose arities run up to three. -/
theorem maxArity_sampleAlphabet : sampleAlphabet.maxArity = 3 := by decide

/-- And at the narrow alphabet, whose arities stop at two. -/
theorem maxArity_narrowAlphabet : narrowAlphabet.maxArity = 2 := by decide
```

Widen that module's summary, which does not yet cover the largest arity, and
add to its `## Main statements` prose that the assertions give the largest
arity of each alphabet.

- [ ] **Step 6: Build the mirror**

Run: `lake build GebTests.Mathlib.Data.Tree.Ranked.Basic` and then
`lake lint -- GebTests`.
Expected: both succeed with no error and no warning.

- [ ] **Step 7: Commit**

```bash
jj describe -m "feat(tree): give a ranked alphabet's largest arity"
jj new
```

---

### Task 2: The arity a block yields

**Files:**

- Modify: `Geb/Mathlib/Data/Tree/Ranked/Code.lean`
- Test: `GebTests/Mathlib/Data/Tree/Ranked/Code.lean`

**Interfaces:**

- Consumes: `RankedAlphabet.arOf`, `RankedAlphabet.arity_le_maxArity` (Task 1).
- Produces: `RankedAlphabet.le_maxArity_of_arOf_eq_some (R : RankedAlphabet)
  {v r : ℕ} (h : R.arOf v = some r) : r ≤ R.maxArity`.

- [ ] **Step 1: Add the statement**

Inside the existing `namespace RankedAlphabet` / `public section` block of
`Geb/Mathlib/Data/Tree/Ranked/Code.lean`, after `testBit_decodeBits`:

```lean
/-- Every arity a block yields is at most the largest, `arOf` returning an
arity only in the image of `arity`. -/
theorem le_maxArity_of_arOf_eq_some (R : RankedAlphabet) {v r : ℕ}
    (h : R.arOf v = some r) : r ≤ R.maxArity := by
  rw [arOf] at h
  split at h
  · rename_i hlt
    rw [← Option.some.inj h]
    exact arity_le_maxArity R ⟨v, hlt⟩
  · exact absurd h (by nofun)
```

- [ ] **Step 2: Record it in the module docstring**

In `## Main statements` add, after the `getElem_code_eq` entry, which is the
last in that list:

```text
* `RankedAlphabet.le_maxArity_of_arOf_eq_some` — an arity a block yields is at
  most the largest.
```

- [ ] **Step 3: Build**

Run: `lake build Geb.Mathlib.Data.Tree.Ranked.Code` and then `lake lint`.
Expected: both succeed with no error and no warning.

- [ ] **Step 4: Mirror it**

At the end of `GebTests/Mathlib/Data/Tree/Ranked/Code.lean`:

```lean
/-- The narrow alphabet's binary symbol's block yields its arity, and that
arity is the alphabet's largest, so the bound is attained rather than
slack. -/
theorem arOf_narrow_two_eq_maxArity :
    narrowAlphabet.arOf 2 = some narrowAlphabet.maxArity := by decide

/-- A block spelling no symbol yields no arity, so the bound is vacuous
there. -/
theorem arOf_narrow_three : narrowAlphabet.arOf 3 = none := by decide
```

That mirror already carries `public import
GebTests.Mathlib.Data.Tree.Ranked.Basic`, so `narrowAlphabet` is in scope and
no import is added. Its title says "Symbol codes on a worked alphabet" and
its summary names `sampleAlphabet` alone, so widen both to the two alphabets
and extend its `## Main statements` prose.

- [ ] **Step 5: Build the mirror**

Run: `lake build GebTests.Mathlib.Data.Tree.Ranked.Code` and then
`lake lint -- GebTests`.
Expected: both succeed with no error and no warning.

- [ ] **Step 6: Commit**

```bash
jj describe -m "feat(tree): bound the arity a block yields"
jj new
```

---

### Task 3: The scan's invariants

**Files:**

- Modify: `Geb/Mathlib/Data/Tree/Ranked/Preorder.lean`
- Test: `GebTests/Mathlib/Data/Tree/Ranked/Preorder.lean`

**Interfaces:**

- Consumes: `RankedAlphabet.scanFinal`, `RankedAlphabet.scanStep`,
  `RankedAlphabet.Valid`, `RankedAlphabet.validBool`.
- Produces: `length_buf_scanFinal_lt`, `depth_scanFinal_le_length`,
  `valid_iff_scanFinal`, each in the `RankedAlphabet` namespace.

- [ ] **Step 1: Add the three statements**

Inside the existing `namespace RankedAlphabet` / `public section` block of
`Geb/Mathlib/Data/Tree/Ranked/Preorder.lean`, after
`length_buf_scanFinal_of_live`:

```lean
/-- The incomplete block never fills, whether or not the scan has failed.
Stated unconditionally, which is the form a bitstring layout of the state
consumes; the `List.rec` below establishes the live and failed cases at once
rather than through `length_buf_scanFinal_of_live`. -/
theorem length_buf_scanFinal_lt (R : RankedAlphabet) (w : List Bool) :
    (R.scanFinal w).buf.length < R.width :=
  List.rec R.width_pos
    (fun b v ih ↦ by
      rw [scanFinal_cons, scanStep]
      cases (R.scanFinal v).live
      · exact ih
      · simp only []
        cases hc : decide ((b :: (R.scanFinal v).buf).length = R.width)
        · simp only [List.length_cons] at hc ⊢
          have := of_decide_eq_false hc
          omega
        · simp only []
          cases R.arOf (decodeBits (b :: (R.scanFinal v).buf))
          · exact R.width_pos
          · simp only []
            cases decide (_ ≤ (R.scanFinal v).depth) <;> exact R.width_pos) w

/-- The pending count is at most the word's length: every clause but the pop
leaves it alone, and the pop raises it by at most one. -/
theorem depth_scanFinal_le_length (R : RankedAlphabet) (w : List Bool) :
    (R.scanFinal w).depth ≤ w.length :=
  List.rec (Nat.le_refl 0)
    (fun b v ih ↦ by
      have hlen : (b :: v).length = v.length + 1 := rfl
      rw [scanFinal_cons, scanStep]
      cases (R.scanFinal v).live
      · simp only []
        omega
      · simp only []
        cases decide ((b :: (R.scanFinal v).buf).length = R.width)
        · simp only []
          omega
        · simp only []
          cases R.arOf (decodeBits (b :: (R.scanFinal v).buf))
          · simp only []
            omega
          · simp only []
            cases decide (_ ≤ (R.scanFinal v).depth)
            · simp only []
              omega
            · simp only []
              omega) w

/-- Validity as the three conditions on the final state, which is the form a
statement about the state word consumes. The two directions take different
routes: the forward one splits `validBool`'s conjunction and reads each
component, and the backward one closes by reduction once the fields are
substituted. -/
theorem valid_iff_scanFinal (R : RankedAlphabet) (w : List Bool) :
    R.Valid w ↔ ((R.scanFinal w).live = true ∧ (R.scanFinal w).buf = [] ∧
      (R.scanFinal w).depth = 1) := by
  constructor
  · intro hv
    have hb : ((R.scanFinal w).live && (R.scanFinal w).buf.isEmpty &&
        ((R.scanFinal w).depth == 1)) = true := hv
    rw [Bool.and_eq_true, Bool.and_eq_true] at hb
    exact ⟨hb.1.1, List.isEmpty_iff.mp hb.1.2, of_decide_eq_true hb.2⟩
  · intro hf
    change ((R.scanFinal w).live && (R.scanFinal w).buf.isEmpty &&
      ((R.scanFinal w).depth == 1)) = true
    rw [hf.1, hf.2.1, hf.2.2]
    rfl
```

Note on `valid_iff_scanFinal`: `validBool`'s `==` elaborates through
`DecidableEq ℕ`, not `Nat.beq`, so the third component is
`of_decide_eq_true hb.2` and `Nat.eq_of_beq_eq_true` does not typecheck there.

- [ ] **Step 2: Record them in the module docstring**

In `## Main statements` add, after the `length_buf_scanFinal_of_live` entry,
which is the last in that list:

```text
* `RankedAlphabet.length_buf_scanFinal_lt` — the incomplete block never fills.
* `RankedAlphabet.depth_scanFinal_le_length` — the pending count is at most
  the word's length.
* `RankedAlphabet.valid_iff_scanFinal` — validity as three conditions on the
  final state.
```

- [ ] **Step 3: Build**

Run: `lake build Geb.Mathlib.Data.Tree.Ranked.Preorder` and then `lake lint`.
Expected: both succeed with no error and no warning.

- [ ] **Step 4: Mirror the scan's final states**

The mirror asserts values, as Tasks 1 and 2 do, rather than re-asserting the
three theorems at a concrete alphabet. Append to
`GebTests/Mathlib/Data/Tree/Ranked/Preorder.lean`, which is not wrapped in a
`public section`:

```lean
/-- A word ending mid-block leaves that block incomplete. -/
theorem scanFinal_narrow_partial_buf :
    (narrowAlphabet.scanFinal [false]).buf = [false] := by decide

/-- And leaves nothing pending, no block having completed. -/
theorem scanFinal_narrow_partial_depth :
    (narrowAlphabet.scanFinal [false]).depth = 0 := by decide

/-- And leaves the scan live. -/
theorem scanFinal_narrow_partial_live :
    (narrowAlphabet.scanFinal [false]).live = true := by decide

/-- A block spelling no symbol fails the scan and clears the block, which is
what makes `RankedAlphabet.length_buf_scanFinal_lt` hold unconditionally
rather than only on a live scan. -/
theorem scanFinal_narrow_dead_buf :
    (narrowAlphabet.scanFinal [true, true]).buf = [] := by decide

/-- And leaves it failed. -/
theorem scanFinal_narrow_dead_live :
    (narrowAlphabet.scanFinal [true, true]).live = false := by decide
```

Widen that module's summary, which covers the spellings, the descent and the
scan's rejections but not the scan's final state, and extend its
`## Main statements` prose accordingly.

- [ ] **Step 5: Build the mirror**

Run: `lake build GebTests.Mathlib.Data.Tree.Ranked.Preorder` and then
`lake lint -- GebTests`.
Expected: both succeed with no error and no warning.

- [ ] **Step 6: Commit**

```bash
jj describe -m "feat(tree): give the validity scan's invariants"
jj new
```

---

### Task 4: The state as a bitstring

**Files:**

- Create: `Geb/Mathlib/Computability/Cobham/RankedTree.lean`
- Modify: `Geb/Mathlib/Computability/Cobham.lean`

**Interfaces:**

- Consumes: `RankedAlphabet.Scan`, `RankedAlphabet.maxArity` (Task 1),
  `RankedAlphabet.width_pos`, `Cobham.bits` and `Cobham.ofFn_bits` from
  `Cobham/Cases.lean`.
- Produces: `Cobham.bufBits (R : RankedAlphabet) (buf : List Bool) : List Bool`,
  `Cobham.stateWord (R : RankedAlphabet) (s : Scan) : List Bool`,
  `Cobham.dispatchWidth (R : RankedAlphabet) : ℕ`,
  `Cobham.length_bufBits_of_lt`, `Cobham.length_stateWord_of_lt`,
  `Cobham.dropWhile_bufBits`, `Cobham.ofFn_bits_stateWord`.

- [ ] **Step 1: Create the module with its header and docstring**

Create `Geb/Mathlib/Computability/Cobham/RankedTree.lean`. The module docstring
is written in full in Task 9, when every declaration it names exists; write it
now with the sections it can fill non-vacuously and extend it as each task
lands. It describes what the module contains at each commit and names no task:
a plan is a transient process artifact, and
[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Document only the persistent
keeps such references out of committed text.

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Computability.Cobham.Cases
public import Geb.Mathlib.Data.Tree.Ranked.Preorder

/-!
# The generic ranked recognizer

The state of the validity scan of
`Geb/Mathlib/Data/Tree/Ranked/Preorder.lean`, at an arbitrary ranked alphabet,
laid out as a bitstring.

## Main definitions

* `Cobham.bufBits` — the incomplete block in a slot of the alphabet's width.
* `Cobham.stateWord` — the scan state as a bitstring.
* `Cobham.dispatchWidth` — the number of state bits a step dispatches on.

## Main statements

* `Cobham.length_bufBits_of_lt`, `Cobham.length_stateWord_of_lt` — the slot's
  and the state word's lengths.
* `Cobham.dropWhile_bufBits` — the slot past its padding.
* `Cobham.ofFn_bits_stateWord` — the state word truncated to a window and
  zero-padded.

## Implementation notes

`RankedAlphabet.Scan` carries an incomplete block, a count of pending
subterms, and a liveness flag. The count is unbounded and the other two are
not, and an expression of the class reaches only a bounded prefix of a word,
so the count is the tail and the layout admits no alternative.

The block cannot be delimited by its own length, since the fields after it
would then stand at a position not statically known. It occupies a slot of
exactly `R.width` bits, delimited by a `true` sentinel preceded by `false`
padding: reading from offset one, past the flag, the first `true` is the
sentinel and the block is what follows it, the padding being all `false`. The
slot's length is invariant under accumulation — the padding shrinks as the
block grows — which is why the fields after it never move. This costs
`R.width` bits rather than the `2 * R.width` a separate fill counter would.

`length_bufBits_of_lt`'s hypothesis is consumed rather than decorative. `Nat`
subtraction being truncated, a block of length `R.width` or more yields a slot
of length one past the block, and `stateWord` is then not injective: at
`R.width = 2` the states `⟨[false, true], 0, true⟩` and `⟨[false], 1, true⟩`
share the word `[true, true, false, true]`. The invariant excluding this is
`RankedAlphabet.length_buf_scanFinal_lt`.

The pending count is unary. Binary would need a truncated subtraction
definable in the class, and `Cobham/Tree.lean`'s recognizer represents its own
depth in unary already.

`ofFn_bits_stateWord` is stated at an arbitrary window rather than at
`dispatchWidth`.

## Tags

Cobham, bounded recursion on notation, ranked alphabet, preorder, scan
-/

namespace Cobham

open RankedAlphabet

public section

end

end Cobham
```

- [ ] **Step 2: Add the layout and its lemmas**

Inside the `public section`:

```lean
/-- The incomplete block in a slot of the alphabet's width: `false` padding,
a `true` sentinel, then the block. -/
@[expose] def bufBits (R : RankedAlphabet) (buf : List Bool) : List Bool :=
  List.replicate (R.width - 1 - buf.length) false ++ true :: buf

/-- The scan state as a bitstring: the liveness flag, the block slot, then the
pending count in unary. -/
@[expose] def stateWord (R : RankedAlphabet) (s : Scan) : List Bool :=
  s.live :: bufBits R s.buf ++ List.replicate s.depth true

/-- The number of state bits a step dispatches on: the flag, the slot, and
enough of the pending count to decide `r ≤ depth` for every arity `r`. -/
@[expose] def dispatchWidth (R : RankedAlphabet) : ℕ := R.width + R.maxArity + 2

/-- The slot holds the alphabet's width, the padding shrinking as the block
grows. `Nat` subtraction being truncated, the hypothesis is consumed. -/
theorem length_bufBits_of_lt (R : RankedAlphabet) (buf : List Bool)
    (h : buf.length < R.width) : (bufBits R buf).length = R.width := by
  rw [bufBits, List.length_append, List.length_replicate, List.length_cons]
  omega

/-- The state word's length: the flag, the slot, and the pending count. -/
theorem length_stateWord_of_lt (R : RankedAlphabet) (s : Scan)
    (h : s.buf.length < R.width) :
    (stateWord R s).length = 1 + R.width + s.depth := by
  rw [stateWord, List.cons_append, List.length_cons, List.length_append,
    length_bufBits_of_lt R s.buf h, List.length_replicate]
  omega

/-- The slot past its padding is the sentinel followed by the block. -/
theorem dropWhile_bufBits (R : RankedAlphabet) (buf : List Bool) :
    (bufBits R buf).dropWhile (fun b ↦ !b) = true :: buf := by
  rw [bufBits, List.dropWhile_append_of_pos
    (fun a ha ↦ by rw [List.eq_of_mem_replicate ha]; rfl)]
  rfl

/-- The state word truncated to a window past the slot and zero-padded: the
flag, the slot, and the pending count capped at the window. Stated at an
arbitrary window rather than at `dispatchWidth`. -/
theorem ofFn_bits_stateWord (R : RankedAlphabet) (s : Scan) (p m : ℕ)
    (hp : p = 1 + R.width + m) (h : s.buf.length < R.width) :
    List.ofFn (bits p (stateWord R s)) =
      s.live :: (bufBits R s.buf ++
        (List.replicate (min m s.depth) true ++
          List.replicate (m - s.depth) false)) := by
  subst hp
  have hbuf : (bufBits R s.buf).length = R.width := length_bufBits_of_lt R s.buf h
  have hdw : 1 + R.width + m = (bufBits R s.buf).length + m + 1 := by
    rw [hbuf]
    omega
  have hpad : 1 + R.width + m - (stateWord R s).length = m - s.depth := by
    rw [length_stateWord_of_lt R s h]
    omega
  rw [ofFn_bits, hpad, stateWord, List.cons_append, hdw, List.take_succ_cons,
    List.take_length_add_append, List.take_replicate, List.cons_append,
    List.append_assoc]
```

- [ ] **Step 3: Import the module from the index**

In `Geb/Mathlib/Computability/Cobham.lean` add, in alphabetical position among
the existing `public import` lines:

```lean
public import Geb.Mathlib.Computability.Cobham.RankedTree
```

Without this the module is built by `lakefile.toml`'s glob but is outside the
`Geb` umbrella's import closure, so `lake lint` does not see it and
`scripts/tests/test-lint-driver.sh` fails outright on it, taking
`scripts/pre-push.sh` with it in Task 12. That test is also a second reason
Task 1 Step 1 removes the prototype: `Geb/Internal.lean` does not import it
either.

- [ ] **Step 4: Build**

Run: `lake build Geb.Mathlib.Computability.Cobham` and then `lake lint`, one
after the other rather than concurrently.
Expected: both succeed with no error and no warning. `lake lint` is the axiom
gate: the module is inside the `Geb` umbrella's import closure from Task 4
Step 3 onward, so a declaration reaching `Classical.choice` fails here rather
than nine commits later.

- [ ] **Step 5: Commit**

```bash
jj describe -m "feat(cobham): lay out the ranked scan's state as a bitstring"
jj new
```

---

### Task 5: Inverting the state word

**Files:**

- Modify: `Geb/Mathlib/Computability/Cobham/RankedTree.lean`

**Interfaces:**

- Consumes: `bufBits`, `stateWord`, `dispatchWidth`, `length_bufBits_of_lt`,
  `dropWhile_bufBits`, `ofFn_bits_stateWord` (Task 4);
  `RankedAlphabet.maxArity` (Task 1); `RankedAlphabet.Scan.ext` and
  `Cobham.bits`.
- Produces: `Cobham.decodeState (R : RankedAlphabet)
  (v : Fin (dispatchWidth R) → Bool) : Scan` and
  `Cobham.decodeState_stateWord_of_lt`.

- [ ] **Step 1: Add the decoder and its inversion**

After `ofFn_bits_stateWord`:

```lean
/-- The inverse of the state layout, read off `List.ofFn` of the bit family:
the flag is the head, the block is the slot past its padding and sentinel, and
the pending count is the run of `true` that follows the slot. Every operation
is structural, so no `Fin` arithmetic and no `Fintype`-derived decidability
arises. -/
@[expose] def decodeState (R : RankedAlphabet)
    (v : Fin (dispatchWidth R) → Bool) : Scan :=
  ⟨(((List.ofFn v).tail.take R.width).dropWhile (fun b ↦ !b)).tail,
    (((List.ofFn v).tail.drop R.width).takeWhile id).length,
    (List.ofFn v).headD false⟩

/-- The decoder inverts the layout, up to capping the pending count at the
depth window `R.maxArity + 1`. -/
theorem decodeState_stateWord_of_lt (R : RankedAlphabet) (s : Scan)
    (h : s.buf.length < R.width) :
    decodeState R (bits (dispatchWidth R) (stateWord R s)) =
      { s with depth := min s.depth (R.maxArity + 1) } := by
  have hbuf : (bufBits R s.buf).length = R.width := length_bufBits_of_lt R s.buf h
  have hword := ofFn_bits_stateWord R s (dispatchWidth R) (R.maxArity + 1)
    (by rw [dispatchWidth]; omega) h
  have hslot : ((List.ofFn (bits (dispatchWidth R) (stateWord R s))).tail.take
      R.width) = bufBits R s.buf := by
    rw [hword, List.tail_cons, List.take_left' hbuf]
  have htail : ((List.ofFn (bits (dispatchWidth R) (stateWord R s))).tail.drop
      R.width) = List.replicate (min (R.maxArity + 1) s.depth) true ++
        List.replicate (R.maxArity + 1 - s.depth) false := by
    rw [hword, List.tail_cons, List.drop_left' hbuf]
  refine Scan.ext ?_ ?_ ?_
  · rw [decodeState, hslot, dropWhile_bufBits]
    rfl
  · have hfalse : ∀ j : ℕ, (List.replicate j false).takeWhile id = [] := fun j ↦
      match j with
      | 0 => rfl
      | _ + 1 => rfl
    rw [decodeState, htail,
      List.takeWhile_append_of_pos (fun a ha ↦ by rw [List.eq_of_mem_replicate ha]; rfl),
      hfalse, List.append_nil, List.length_replicate]
    exact Nat.min_comm _ _
  · rw [decodeState, hword, List.headD_cons]
```

`hfalse` is written out rather than taken from `List.takeWhile_replicate`,
which depends on `Classical.choice` through `List.filter_replicate`.

- [ ] **Step 2: Extend the module docstring**

Add to `## Main definitions`:

```text
* `Cobham.decodeState` — the inverse of the state layout.
```

Add to `## Main statements`:

```text
* `Cobham.decodeState_stateWord_of_lt` — the decoder inverts the layout up to
  capping the pending count at the depth window.
```

Add to `## Implementation notes`:

```text
The branch family's domain is `Fin (dispatchWidth R) → Bool` at a symbolic
width, so recovering the fields index by index would carry a bound proof at
every step. `decodeState` avoids that by passing through `List.ofFn` and
reading the fields with the `List` API. This also keeps the module clear of
`DecidableEq (Fin n → Bool)`, which resolves through
`Fintype.decidablePiFintype`, measured as depending on `Classical.choice`,
while `DecidableEq (List Bool)` measures clean.

The run of `false` past the slot is cleared by a two-case reduction rather
than by `List.takeWhile_replicate`, which was measured to depend on
`Classical.choice` through `List.filter_replicate`. A proof shortened back
onto that lemma fails `lake lint`.
```

- [ ] **Step 3: Build**

Run: `lake build Geb.Mathlib.Computability.Cobham` and then `lake lint`, one
after the other rather than concurrently.
Expected: both succeed with no error and no warning. `lake lint` is the axiom
gate: the module is inside the `Geb` umbrella's import closure from Task 4
Step 3 onward, so a declaration reaching `Classical.choice` fails here rather
than nine commits later.

- [ ] **Step 4: Commit**

```bash
jj describe -m "feat(cobham): invert the ranked scan's state word"
jj new
```

---

### Task 6: The step's decomposition

**Files:**

- Modify: `Geb/Mathlib/Computability/Cobham/RankedTree.lean`

**Interfaces:**

- Consumes: `bufBits`, `stateWord`, `length_bufBits_of_lt` (Task 4);
  `RankedAlphabet.scanStep`, `RankedAlphabet.arOf`,
  `RankedAlphabet.decodeBits`, `RankedAlphabet.maxArity` (Task 1),
  `RankedAlphabet.le_maxArity_of_arOf_eq_some` (Task 2).
- Produces: `Cobham.dropCount (R : RankedAlphabet) (b : Bool) (s : Scan) : ℕ`,
  `Cobham.nextPrefix (R : RankedAlphabet) (b : Bool) (s : Scan) : List Bool`,
  `Cobham.dropCount_min_depth`, `Cobham.nextPrefix_min_depth`,
  `Cobham.stateWord_scanStep_of_lt`.

Both definitions repeat `RankedAlphabet.scanStep`'s `match` structure clause
for clause, so that a case split reduces the three in step.

- [ ] **Step 1: Add the two step components**

After `decodeState_stateWord_of_lt`:

```lean
/-- The bits a step drops from the state word: the flag and the slot, together
with the popped subterms where a completed block's symbol pops. -/
@[expose] def dropCount (R : RankedAlphabet) (b : Bool) (s : Scan) : ℕ :=
  match s.live with
  | false => 1 + R.width
  | true =>
    match decide ((b :: s.buf).length = R.width) with
    | false => 1 + R.width
    | true =>
      match R.arOf (decodeBits (b :: s.buf)) with
      | none => 1 + R.width
      | some r =>
        match decide (r ≤ s.depth) with
        | false => 1 + R.width
        | true => 1 + R.width + r

/-- The bits a step prepends to the state word: the rebuilt flag and slot,
together with the pushed subterm where a completed block's symbol pops. -/
@[expose] def nextPrefix (R : RankedAlphabet) (b : Bool) (s : Scan) :
    List Bool :=
  match s.live with
  | false => false :: bufBits R s.buf
  | true =>
    match decide ((b :: s.buf).length = R.width) with
    | false => true :: bufBits R (b :: s.buf)
    | true =>
      match R.arOf (decodeBits (b :: s.buf)) with
      | none => false :: bufBits R []
      | some r =>
        match decide (r ≤ s.depth) with
        | false => false :: bufBits R []
        | true => true :: bufBits R [] ++ [true]
```

- [ ] **Step 2: Add the two capping lemmas**

```lean
/-- Capping the pending count at the depth window `R.maxArity + 1` leaves the
bits dropped unchanged: the only test reading the count compares it with an
arity, which is at most the largest. -/
theorem dropCount_min_depth (R : RankedAlphabet) (b : Bool) (s : Scan) :
    dropCount R b { s with depth := min s.depth (R.maxArity + 1) } =
      dropCount R b s := by
  obtain ⟨buf, depth, live⟩ := s
  rw [dropCount, dropCount]
  dsimp only
  cases live
  · rfl
  · cases har : R.arOf (decodeBits (b :: buf))
    · rfl
    · rename_i r
      have hr : r ≤ R.maxArity := le_maxArity_of_arOf_eq_some R har
      dsimp only
      rcases Nat.le_total depth (R.maxArity + 1) with hle | hle
      · rw [Nat.min_eq_left hle]
      · rw [decide_eq_true (by omega : r ≤ min depth (R.maxArity + 1)),
          decide_eq_true (by omega : r ≤ depth)]

/-- Capping the pending count leaves the bits prepended unchanged, as
`dropCount_min_depth`. -/
theorem nextPrefix_min_depth (R : RankedAlphabet) (b : Bool) (s : Scan) :
    nextPrefix R b { s with depth := min s.depth (R.maxArity + 1) } =
      nextPrefix R b s := by
  obtain ⟨buf, depth, live⟩ := s
  rw [nextPrefix, nextPrefix]
  dsimp only
  cases live
  · rfl
  · cases har : R.arOf (decodeBits (b :: buf))
    · rfl
    · rename_i r
      have hr : r ≤ R.maxArity := le_maxArity_of_arOf_eq_some R har
      dsimp only
      rcases Nat.le_total depth (R.maxArity + 1) with hle | hle
      · rw [Nat.min_eq_left hle]
      · rw [decide_eq_true (by omega : r ≤ min depth (R.maxArity + 1)),
          decide_eq_true (by omega : r ≤ depth)]
```

The two `dsimp only` calls are load-bearing. Without the first, after
`rw [dropCount, dropCount]`, the record update's projections do not reduce and
`cases har` matches nothing. Without the second, placed after the `have hr`,
the `some r` match is unreduced and the `r` beneath it is that match's own
binder, so `rw` reports the pattern absent from a goal that visibly prints it.

- [ ] **Step 3: Add the step lemma**

```lean
/-- A step of the scan rewrites a bounded prefix of the state word and drops a
bounded number of its bits: the flag and the slot are rebuilt, and the pending
count in the tail is popped by the arity of a completed block's symbol. -/
theorem stateWord_scanStep_of_lt (R : RankedAlphabet) (b : Bool) (s : Scan)
    (h : s.buf.length < R.width) :
    stateWord R (R.scanStep b s) =
      nextPrefix R b s ++ (stateWord R s).drop (dropCount R b s) := by
  have hpre : (s.live :: bufBits R s.buf).length = 1 + R.width := by
    rw [List.length_cons, length_bufBits_of_lt R s.buf h]
    omega
  have hdrop : (stateWord R s).drop (1 + R.width) =
      List.replicate s.depth true := List.drop_left' hpre
  have hdropr : ∀ r : ℕ, (stateWord R s).drop (1 + R.width + r) =
      List.replicate (s.depth - r) true := fun r ↦ by
    rw [← List.drop_drop, hdrop, List.drop_replicate]
  obtain ⟨buf, depth, live⟩ := s
  rw [scanStep, dropCount, nextPrefix]
  dsimp only
  cases live
  · dsimp only
    rw [hdrop]
    rfl
  · cases hc : decide ((b :: buf).length = R.width)
    · dsimp only
      rw [hdrop]
      rfl
    · dsimp only
      cases har : R.arOf (decodeBits (b :: buf))
      · dsimp only
        rw [hdrop]
        rfl
      · rename_i r
        dsimp only
        cases hle : decide (r ≤ depth)
        · dsimp only
          rw [hdrop]
          rfl
        · dsimp only
          rw [hdropr r, stateWord, List.replicate_succ, List.append_assoc]
          rfl
```

- [ ] **Step 4: Extend the module docstring**

Add to `## Main definitions`:

```text
* `Cobham.dropCount`, `Cobham.nextPrefix` — the bits a step drops and
  prepends.
```

Add to `## Main statements`:

```text
* `Cobham.dropCount_min_depth`, `Cobham.nextPrefix_min_depth` — capping the
  pending count at the depth window changes neither.
* `Cobham.stateWord_scanStep_of_lt` — a step rewrites a bounded prefix and
  drops a bounded number of bits.
```

Add to `## Implementation notes`:

```text
The dispatch reads the flag and the slot together with the low
`R.maxArity + 1` bits of the pending count, which give
`min depth (R.maxArity + 1)`. Those bits decide `r ≤ depth` for every symbol:
if the count is at least `R.maxArity + 1` then every arity is below it, and
otherwise those bits are the count itself.
`RankedAlphabet.le_maxArity_of_arOf_eq_some` is what makes the window
sufficient, and it is what `dropCount_min_depth` and `nextPrefix_min_depth`
consume.
```

- [ ] **Step 5: Build**

Run: `lake build Geb.Mathlib.Computability.Cobham` and then `lake lint`, one
after the other rather than concurrently.
Expected: both succeed with no error and no warning. `lake lint` is the axiom
gate: the module is inside the `Geb` umbrella's import closure from Task 4
Step 3 onward, so a declaration reaching `Classical.choice` fails here rather
than nine commits later.

- [ ] **Step 6: Commit**

```bash
jj describe -m "feat(cobham): decompose the ranked scan's step"
jj new
```

---

### Task 7: The scan as an expression

**Files:**

- Modify: `Geb/Mathlib/Computability/Cobham/RankedTree.lean`

**Interfaces:**

- Consumes: `decodeState`, `decodeState_stateWord_of_lt` (Task 5);
  `stateWord`, `dispatchWidth`, `length_stateWord_of_lt` (Task 4);
  `Cobham.transport`; `dropCount`, `nextPrefix`,
  `dropCount_min_depth`, `nextPrefix_min_depth`, `stateWord_scanStep_of_lt`
  (Task 6); `RankedAlphabet.length_buf_scanFinal_lt`,
  `RankedAlphabet.depth_scanFinal_le_length` (Task 3); `Cobham.diagOf`,
  `Cobham.casesOf`, `Cobham.prependOf`, `Cobham.predIterOf`,
  `Cobham.constAtOf`, `Cobham.scanSem`, `Cobham.scan`, `Cobham.scanOf`,
  `Cobham.stepWord`, `Cobham.casesSem`, `Cobham.casesSem_eq`,
  `Cobham.stepWord_diagOf`, `Cobham.stepWord_prependOf`,
  `Cobham.stepWord_predIterOf`,
  `Cobham.baseWord_constAtOf`, `Cobham.scanSem_eq`, `Cobham.scanSem_eq_eval`,
  `Cobham.scanStepWord`; `RankedAlphabet.scanFinal_nil` and
  `RankedAlphabet.scanFinal_cons`.
- Produces: `Cobham.rankedStep (R : RankedAlphabet) (b : Bool) : COf 1`,
  `Cobham.rankedSem (R : RankedAlphabet) : Sem 1`,
  `Cobham.stepWord_rankedStep_of_lt`, `Cobham.rankedSem_eq`,
  `Cobham.length_rankedSem_le`, `Cobham.ranked (R : RankedAlphabet) : C`,
  `Cobham.rankedOf (R : RankedAlphabet) : COf 1`, `Cobham.rankedSem_eq_eval`.

- [ ] **Step 1: Add the step and the scan's meaning**

After `stateWord_scanStep_of_lt`:

```lean
/-- One step of the recognizer: dispatch on the state's leading bits, prepend
the rebuilt prefix and drop the consumed bits. Every branch has that one
shape. -/
@[expose] def rankedStep (R : RankedAlphabet) (b : Bool) : COf 1 :=
  diagOf (casesOf (dispatchWidth R) fun v ↦
    prependOf (nextPrefix R b (decodeState R v))
      (predIterOf (dropCount R b (decodeState R v))))

/-- The recognizer's scan, at the two steps and the growth the state layout
allows. -/
@[expose] def rankedSem (R : RankedAlphabet) : Sem 1 :=
  scanSem (constAtOf 0 (stateWord R ⟨[], 0, true⟩)) (rankedStep R false)
    (rankedStep R true) (R.width + 1)
```

- [ ] **Step 2: Add the step's correctness and the scan's**

```lean
/-- A step of the expression computes a step of the scan, on a state whose
incomplete block is short of the width. This is where the decoder, the two
capping lemmas and the step lemma meet. -/
theorem stepWord_rankedStep_of_lt (R : RankedAlphabet) (b : Bool) (s : Scan)
    (h : s.buf.length < R.width) :
    stepWord (rankedStep R b) (stateWord R s) = stateWord R (R.scanStep b s) := by
  rw [rankedStep, stepWord_diagOf]
  change casesSem (dispatchWidth R) _ ![stateWord R s, stateWord R s] = _
  rw [casesSem_eq, stepWord_prependOf, stepWord_predIterOf,
    decodeState_stateWord_of_lt R s h, nextPrefix_min_depth, dropCount_min_depth,
    stateWord_scanStep_of_lt R b s h]

/-- The expression computes the scan's state word on every input. -/
theorem rankedSem_eq (R : RankedAlphabet) (w : List Bool) :
    rankedSem R ![w] = stateWord R (R.scanFinal w) := by
  rw [rankedSem, scanSem_eq]
  refine List.rec ?_ ?_ w
  · rw [List.foldr_nil, baseWord_constAtOf, scanFinal_nil]
  · intro b v ih
    rw [List.foldr_cons, ih, scanFinal_cons]
    cases b
    · exact stepWord_rankedStep_of_lt R false _ (length_buf_scanFinal_lt R v)
    · exact stepWord_rankedStep_of_lt R true _ (length_buf_scanFinal_lt R v)
```

- [ ] **Step 3: Add the recursion bound and the expression**

```lean
/-- The value never exceeds the input by more than the state's fixed part, so
the scanner's recursion bound holds at growth `R.width + 1`. Stated at
`scanSem`, which is the form `Cobham.scan` consumes. At the empty word the
bound is tight. -/
theorem length_rankedSem_le (R : RankedAlphabet) (w : List Bool) :
    (scanSem (constAtOf 0 (stateWord R ⟨[], 0, true⟩)) (rankedStep R false)
      (rankedStep R true) (R.width + 1) ![w]).length ≤ w.length + (R.width + 1) := by
  have hlen := length_stateWord_of_lt R (R.scanFinal w) (length_buf_scanFinal_lt R w)
  have hdepth := depth_scanFinal_le_length R w
  rw [← rankedSem, rankedSem_eq, hlen]
  omega

/-- The scan as an expression of the class, its recursion bound discharged by
`length_rankedSem_le`. -/
@[expose] def ranked (R : RankedAlphabet) : C :=
  scan (constAtOf 0 (stateWord R ⟨[], 0, true⟩)) (rankedStep R false)
    (rankedStep R true) (R.width + 1) (length_rankedSem_le R)

/-- `ranked` at its declared arity. -/
@[expose] def rankedOf (R : RankedAlphabet) : COf 1 :=
  scanOf (constAtOf 0 (stateWord R ⟨[], 0, true⟩)) (rankedStep R false)
    (rankedStep R true) (R.width + 1) (length_rankedSem_le R)

/-- The meaning `rankedSem` reads at the raw tree is the meaning `ranked`
carries. -/
theorem rankedSem_eq_eval (R : RankedAlphabet) :
    transport (rankedOf R).2 (rankedOf R).1.eval = rankedSem R :=
  scanSem_eq_eval (constAtOf 0 (stateWord R ⟨[], 0, true⟩)) (rankedStep R false)
    (rankedStep R true) (R.width + 1) (length_rankedSem_le R)
```

- [ ] **Step 4: Extend the module docstring**

Widen the summary to "The validity scan of
`Geb/Mathlib/Data/Tree/Ranked/Preorder.lean`, at an arbitrary ranked alphabet,
as an expression of Cobham's class", and add a `## References` section between
`## Implementation notes` and `## Tags` whose sole entry is `* [Cobham1965]`,
the form `Cobham/{Basic,Scan,Cases,Tree}.lean` use.

Add to `## Main definitions`:

```text
* `Cobham.rankedStep`, `Cobham.rankedSem` — the recognizer's step and the
  meaning of its scan.
* `Cobham.ranked`, `Cobham.rankedOf` — the scan as an expression of `C`, and
  at its declared arity.
```

Add to `## Main statements`:

```text
* `Cobham.stepWord_rankedStep_of_lt`, `Cobham.rankedSem_eq` — the expression
  computes the scan, one step and then on every input.
* `Cobham.length_rankedSem_le` — the recursion bound the scanner asks for.
* `Cobham.rankedSem_eq_eval` — the meaning read at the raw tree is the meaning
  the expression carries.
```

- [ ] **Step 5: Build**

Run: `lake build Geb.Mathlib.Computability.Cobham` and then `lake lint`, one
after the other rather than concurrently.
Expected: both succeed with no error and no warning. `lake lint` is the axiom
gate: the module is inside the `Geb` umbrella's import closure from Task 4
Step 3 onward, so a declaration reaching `Classical.choice` fails here rather
than nine commits later.

- [ ] **Step 6: Commit**

```bash
jj describe -m "feat(cobham): give the ranked scan as an expression of the class"
jj new
```

---

### Task 8: The verdict test

**Files:**

- Modify: `Geb/Mathlib/Computability/Cobham/RankedTree.lean`

**Interfaces:**

- Consumes: `stateWord`, `bufBits`, `length_bufBits_of_lt`,
  `dropWhile_bufBits`, `ofFn_bits_stateWord` (Task 4); `Cobham.diagOf`,
  `Cobham.casesOf`, `Cobham.constAtOf`, `Cobham.casesSem`,
  `Cobham.casesSem_eq`, `Cobham.bits`, `Cobham.stepWord`,
  `Cobham.stepWord_diagOf`, `Cobham.stepWord_constAtOf`;
  `RankedAlphabet.width_pos`.
- Produces: `Cobham.acceptWord (R : RankedAlphabet) : List Bool`,
  `Cobham.ofFn_bits_stateWord_eq_iff`,
  `Cobham.acceptTest (R : RankedAlphabet) : COf 1`,
  `Cobham.stepWord_acceptTest`.

- [ ] **Step 1: Add the accepting word and the separating property**

After `rankedSem_eq_eval`:

```lean
/-- The accepting state's word: live, no incomplete block, one pending
subterm. -/
@[expose] def acceptWord (R : RankedAlphabet) : List Bool :=
  stateWord R ⟨[], 1, true⟩

/-- The verdict window separates the accepting state from every other state
whose block is short of the width. It reads one bit past the accepting word,
so a pending count above one is rejected. -/
theorem ofFn_bits_stateWord_eq_iff (R : RankedAlphabet) (s : Scan)
    (h : s.buf.length < R.width) :
    List.ofFn (bits (R.width + 3) (stateWord R s)) = acceptWord R ++ [false] ↔
      (s.live = true ∧ s.buf = [] ∧ s.depth = 1) := by
  have hbuf : (bufBits R s.buf).length = R.width := length_bufBits_of_lt R s.buf h
  have hnil : (bufBits R ([] : List Bool)).length = R.width :=
    length_bufBits_of_lt R [] R.width_pos
  have hleft := ofFn_bits_stateWord R s (R.width + 3) 2 (by omega) h
  have hright : acceptWord R ++ [false] =
      true :: (bufBits R [] ++ ([true] ++ [false])) := by
    rw [acceptWord, stateWord, List.cons_append, List.cons_append,
      List.append_assoc]
    rfl
  rw [hleft, hright]
  constructor
  · intro heq
    injection heq with hhead htail
    have hlen : (bufBits R s.buf).length = (bufBits R []).length := by
      rw [hbuf, hnil]
    obtain ⟨hslot, hrest⟩ := List.append_inj htail hlen
    have hbufnil : s.buf = [] := by
      have hd := congrArg (List.dropWhile (fun b ↦ !b)) hslot
      rw [dropWhile_bufBits, dropWhile_bufBits] at hd
      injection hd with _ hd'
    refine ⟨hhead, hbufnil, ?_⟩
    match hdep : s.depth with
    | 0 =>
      rw [hdep] at hrest
      exact absurd hrest (by decide)
    | 1 => rfl
    | (n + 2) =>
      rw [hdep, Nat.min_eq_left (by omega), (by omega : 2 - (n + 2) = 0)] at hrest
      exact absurd hrest (by decide)
  · intro hs
    rw [hs.1, hs.2.1, hs.2.2]
    rfl
```

- [ ] **Step 2: Add the test and its value**

```lean
/-- The verdict test: the branch at the accepting window returns `[true]`, and
every other branch the empty bitstring. The decision is taken on `List Bool`,
whose `DecidableEq` depends on no axiom, rather than on
`Fin (R.width + 3) → Bool`, whose instance routes through
`Fintype.decidablePiFintype` and `Classical.choice`. -/
@[expose] def acceptTest (R : RankedAlphabet) : COf 1 :=
  diagOf (casesOf (R.width + 3) fun v ↦
    if List.ofFn v = acceptWord R ++ [false] then constAtOf 1 [true]
    else constAtOf 1 [])

/-- The verdict test's value at the state it reads. -/
theorem stepWord_acceptTest (R : RankedAlphabet) (u : List Bool) :
    stepWord (acceptTest R) u =
      if List.ofFn (bits (R.width + 3) u) = acceptWord R ++ [false] then [true]
      else [] := by
  rw [acceptTest, stepWord_diagOf]
  change casesSem (R.width + 3) _ ![u, u] = _
  rw [casesSem_eq]
  by_cases hb : List.ofFn (bits (R.width + 3) u) = acceptWord R ++ [false]
  · rw [if_pos hb, if_pos hb, stepWord_constAtOf]
  · rw [if_neg hb, if_neg hb, stepWord_constAtOf]
```

- [ ] **Step 3: Extend the module docstring**

Widen `ofFn_bits_stateWord`'s docstring, whose window is now read at two
different values, to end "Stated at an arbitrary window, the dispatch and the
verdict reading different ones", and widen the corresponding
`## Implementation notes` sentence the same way.

Add to `## Main definitions`:

```text
* `Cobham.acceptWord`, `Cobham.acceptTest` — the accepting state's word and
  the test deciding it.
```

Add to `## Main statements`:

```text
* `Cobham.ofFn_bits_stateWord_eq_iff` — the verdict window separates the
  accepting state from every other reachable one.
* `Cobham.stepWord_acceptTest` — the test's value at the state it reads.
```

- [ ] **Step 4: Build**

Run: `lake build Geb.Mathlib.Computability.Cobham` and then `lake lint`, one
after the other rather than concurrently.
Expected: both succeed with no error and no warning. `lake lint` is the axiom
gate: the module is inside the `Geb` umbrella's import closure from Task 4
Step 3 onward, so a declaration reaching `Classical.choice` fails here rather
than nine commits later.

- [ ] **Step 5: Commit**

```bash
jj describe -m "feat(cobham): decide the ranked scan's accepting state"
jj new
```

---

### Task 9: The recognizer and the bridge

**Files:**

- Modify: `Geb/Mathlib/Computability/Cobham/RankedTree.lean`

**Interfaces:**

- Consumes: `acceptTest`, `stepWord_acceptTest`,
  `ofFn_bits_stateWord_eq_iff` (Task 8); `rankedOf`, `rankedSem`,
  `rankedSem_eq` (Task 7); `RankedAlphabet.length_buf_scanFinal_lt`,
  `RankedAlphabet.valid_iff_scanFinal` (Task 3);
  `RankedAlphabet.Valid`, `RankedAlphabet.Binary.valid_iff`,
  `Cobham.isTreeSem`,
  `Cobham.isTreeSem_eq_singleton_iff_valid`; `Cobham.semAt`,
  `Cobham.transport`, `Cobham.sig.WValid` and
  `Cobham.sig.wIndexValid_index_eq_wIndexRoot`.
- Produces: `Cobham.isRankedRaw`, `Cobham.wValid_isRankedRaw`,
  `Cobham.isRanked (R : RankedAlphabet) : C`, `Cobham.isRankedOf`,
  `Cobham.isRankedSem (R : RankedAlphabet) : Sem 1`,
  `Cobham.isRankedSem_apply`, `Cobham.isRankedSem_eq_ite`,
  `Cobham.isRankedSem_eq_singleton_iff_valid`, `Cobham.isRankedSem_eq_eval`,
  `Cobham.isRankedSem_binRanked_eq_singleton_iff_isTreeSem`.

- [ ] **Step 1: Extend the module's imports**

Replace the import block with:

```lean
public import Geb.Mathlib.Computability.Cobham.Cases
public import Geb.Mathlib.Computability.Cobham.Tree
public import Geb.Mathlib.Data.Tree.Ranked.Binary
```

`Ranked/Binary.lean` publicly imports `Ranked/Preorder.lean`, so the explicit
import of the latter becomes redundant; confirm with `lake shake` in Task 12
and restore it only if shake asks for it.

- [ ] **Step 2: Add the recognizer's tree and its expression**

After `stepWord_acceptTest`:

```lean
/-- The raw tree of the recognizer: the verdict test on the scan. -/
@[expose] def isRankedRaw (R : RankedAlphabet) : sig.toPFunctor.W :=
  WType.mk (.comp 1 1) fun d ↦
    match d with
    | .inl () => (acceptTest R).1.1.1
    | .inr _ => (rankedOf R).1.1.1

/-- The recognizer's tree is admissible, from its two components'. `decide`
does not apply: at a symbolic alphabet nothing reduces, so the pair of a case
analysis and the index condition's `funext` is written out. -/
theorem wValid_isRankedRaw (R : RankedAlphabet) : sig.WValid (isRankedRaw R) :=
  ⟨fun d ↦ match d with
    | .inl () => (acceptTest R).1.1.2
    | .inr _ => (rankedOf R).1.1.2,
  funext fun d ↦ match d with
    | .inl () => (sig.wIndexValid_index_eq_wIndexRoot _).trans (acceptTest R).2
    | .inr _ => (sig.wIndexValid_index_eq_wIndexRoot _).trans (rankedOf R).2⟩

/-- The recognizer as an expression of the class: whether a bitstring spells a
term of the alphabet. -/
@[expose] def isRanked (R : RankedAlphabet) : C :=
  ⟨⟨isRankedRaw R, wValid_isRankedRaw R⟩,
    ⟨trivial, fun d ↦ match d with
      | .inl () => (acceptTest R).1.2
      | .inr _ => (rankedOf R).1.2⟩⟩

/-- `isRanked` at its declared arity. -/
@[expose] def isRankedOf (R : RankedAlphabet) : COf 1 := ⟨isRanked R, rfl⟩

/-- The recognizer's meaning at its arity, read at the raw tree. -/
@[expose] def isRankedSem (R : RankedAlphabet) : Sem 1 :=
  semAt 1 ⟨isRankedRaw R, wValid_isRankedRaw R⟩ rfl

/-- The meaning `isRankedSem` reads at the raw tree is the meaning `isRanked`
carries. -/
theorem isRankedSem_eq_eval (R : RankedAlphabet) :
    transport (isRankedOf R).2 (isRankedOf R).1.eval = isRankedSem R := rfl
```

- [ ] **Step 3: Add the recognizer's value and correctness**

```lean
/-- One step of the recognizer: the verdict test on the scan's value. The
composition applies its head at `fun _ : Fin 1 ↦ r` while `stepWord` applies it
at `![r]`, and the two agree only by `funext`. -/
theorem isRankedSem_apply (R : RankedAlphabet) (w : List Bool) :
    isRankedSem R ![w] = stepWord (acceptTest R) (rankedSem R ![w]) :=
  congrArg (semAt 1 (acceptTest R).1.1 (acceptTest R).2)
    (funext fun i ↦ match i with | ⟨0, _⟩ => rfl)

/-- The recognizer's value on both branches: a rejected word receives the empty
bitstring, not merely something other than `[true]`. -/
theorem isRankedSem_eq_ite (R : RankedAlphabet) (w : List Bool) :
    isRankedSem R ![w] = if R.Valid w then [true] else [] := by
  have hsep := ofFn_bits_stateWord_eq_iff R (R.scanFinal w)
    (length_buf_scanFinal_lt R w)
  rw [isRankedSem_apply, rankedSem_eq, stepWord_acceptTest]
  by_cases hv : R.Valid w
  · rw [if_pos hv, if_pos (hsep.mpr ((valid_iff_scanFinal R w).mp hv))]
  · rw [if_neg hv, if_neg fun hw ↦ hv ((valid_iff_scanFinal R w).mpr (hsep.mp hw))]

/-- The recognizer accepts exactly the words spelling a term. -/
theorem isRankedSem_eq_singleton_iff_valid (R : RankedAlphabet) (w : List Bool) :
    isRankedSem R ![w] = [true] ↔ R.Valid w := by
  rw [isRankedSem_eq_ite]
  by_cases hv : R.Valid w
  · rw [if_pos hv]
    exact ⟨fun _ ↦ hv, fun _ ↦ rfl⟩
  · rw [if_neg hv]
    exact ⟨fun hw ↦ absurd hw (by nofun), fun h ↦ absurd h hv⟩

/-- At the two-symbol alphabet the generic recognizer accepts the language the
recognizer of `Cobham/Tree.lean` accepts. Every link relates semantic
predicates on `List Bool`, so neither `binRanked`'s `width` and `maxArity` nor
the two recognizers' differing failure conventions need reconciling. -/
theorem isRankedSem_binRanked_eq_singleton_iff_isTreeSem (w : List Bool) :
    isRankedSem RankedAlphabet.Binary.binRanked ![w] = [true] ↔
      isTreeSem ![w] = [true] :=
  (isRankedSem_eq_singleton_iff_valid _ w).trans
    ((RankedAlphabet.Binary.valid_iff w).trans
      (isTreeSem_eq_singleton_iff_valid w).symm)
```

- [ ] **Step 4: Complete the module docstring**

Add to `## Main definitions`:

```text
* `Cobham.isRankedRaw`, `Cobham.isRanked`, `Cobham.isRankedOf`,
  `Cobham.isRankedSem` — the recognizer's raw tree, the expression of `C` over
  it, that expression at its declared arity, and its meaning.
```

Add to `## Main statements`:

```text
* `Cobham.wValid_isRankedRaw` — the raw tree's admissibility, from its two
  components'.
* `Cobham.isRankedSem_apply`, `Cobham.isRankedSem_eq_ite` — the composition's
  value, and the value on both branches.
* `Cobham.isRankedSem_eq_singleton_iff_valid` — the recognizer accepts exactly
  the words spelling a term.
* `Cobham.isRankedSem_eq_eval` — the meaning read at the raw tree is the
  meaning the expression carries.
* `Cobham.isRankedSem_binRanked_eq_singleton_iff_isTreeSem` — at the
  two-symbol alphabet it accepts the language `Cobham.isTree` accepts.
```

Add to `## Implementation notes`:

```text
Neither `SmashFree (ranked R)` nor `SmashFree (isRanked R)` is stated here.
`smashFreeBool` is a `WType.elim` over the whole tree, so at a symbolic
alphabet it is not `decide`-dischargeable and needs a recursion mirroring
`wValid_casesRaw`, and at a concrete alphabet it forces every node. Nothing in
this module uses `smash`, so the statement is expected to hold and is left to
the branch that needs it. `Cobham/Tree.lean` keeps `comb` and
`isTree`, so `isTree_smashFree` and the [Strahm2003] Theorem 1(2) reasoning
keep their subject.

No equivalence here is discharged by `omega`, which pulls `Classical.choice`
on an `Iff` goal; each is built from its two implications or from
`Iff.trans`.

`isRankedSem_eq_ite` pins the value on the rejecting branch as well as the
accepting one. `isRankedSem_eq_singleton_iff_valid` alone would admit a
recognizer returning `[false]` on a rejected word, so correctness as a
function is not implied by correctness of the accepted set.

The containment this module realizes is an instance of Cobham's
characterisation of the polynomial-time functions; what it delivers is an
explicit expression computing the decision, not a new theorem.
```

Widen the summary to name the recognizer as well as the scan, add
`[Strahm2003]` to `## References`, and add `recognizer` to `## Tags`.

- [ ] **Step 5: Build**

Run: `lake build Geb.Mathlib.Computability.Cobham` and then `lake lint`, one
after the other rather than concurrently.
Expected: both succeed with no error and no warning. `lake lint` is the axiom
gate: the module is inside the `Geb` umbrella's import closure from Task 4
Step 3 onward, so a declaration reaching `Classical.choice` fails here rather
than nine commits later.

- [ ] **Step 6: Commit**

```bash
jj describe -m "feat(cobham): recognize the ranked preorder spellings"
jj new
```

---

### Task 10: The test mirror

**Files:**

- Create: `GebTests/Mathlib/Computability/Cobham/RankedTree.lean`
- Modify: `GebTests/Mathlib/Computability/Cobham.lean`

**Interfaces:**

- Consumes: `Cobham.isRankedSem`, `Cobham.isRankedOf`, `Cobham.decodeState`,
  `Cobham.dispatchWidth`, `Cobham.stateWord`, `Cobham.bufBits` and
  `Cobham.bits`; the fixtures
  `sampleAlphabet`, `narrowAlphabet` and `wordsUpTo` of
  `GebTests/Mathlib/Data/Tree/Ranked/Basic.lean`.
- Produces: nothing consumed downstream.

Every assertion below was compiled in the prototype, against its own copies of
`narrowAlphabet`, `sampleAlphabet` and `wordsUpTo`, `binRanked` being reached
from `Ranked/Binary.lean`. The sweep lengths are
measured, per
[the design](../specs/2026-08-10-cobham-cases-fold-ranked-design.md)
§ Test mirrors: at `sampleAlphabet` a sweep of length six exceeds the default
heartbeat limit and one of length five does not, while `narrowAlphabet` and
`binRanked` reach six. The prototype module, which carries these assertions
together with every symbolic-`R` declaration of Tasks 4 to 9, took 30 seconds
to build, the sweeps dominating; the mirror alone costs less than that but was
not timed separately. If it dominates `lake test`, lower a length and amend
the docstring's recorded length rather than raising `maxHeartbeats`.

- [ ] **Step 1: Create the mirror**

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Mathlib.Data.Tree.Ranked.Basic

import Geb.Mathlib.Computability.Cobham.RankedTree

/-!
# The generic ranked recognizer on worked alphabets

The recognizer's verdict on short accepted and rejected words at two worked
alphabets, the decoder's fields at each block length the scan reaches, and the
agreement of the recognizer with `RankedAlphabet.validBool` over an
enumeration of words at three alphabets.

## Main definitions

* `isRankedArity` — the recognizer at its declared arity.

## Main statements

The assertions below give the recognizer's value at `binRanked` on a leaf's
spelling, on a bare node and on a node over two leaves; its value at
`narrowAlphabet` on a nullary symbol's block, on a block spelling no symbol, on
a unary symbol over a nullary one, and on a symbol whose arity exceeds the
pending count; the decoder's fields on the initial state, on a state carrying
an incomplete block, on a failed state, and on a state whose pending count
exceeds the depth window `R.maxArity + 1`; the slot's length at a block
violating
`Cobham.length_bufBits_of_lt`'s hypothesis, pinning that the hypothesis is
consumed; and the agreement of `Cobham.isRankedSem` with
`RankedAlphabet.validBool` over every word of at most the length each sweep
records.

## Implementation notes

`RankedAlphabet.Scan` derives no `DecidableEq`, so the decoder's inversion is
asserted field by field rather than as one equation.

The sweep lengths are measured rather than conventional. `sampleAlphabet`'s
largest arity is one above `narrowAlphabet`'s, so its dispatch is one bit
wider and each reduction descends one dispatch level further; its sweep is
taken to length five, six exceeding the default heartbeat limit. The case
tree is a `Nat.rec`, so the elaborated term is of constant size and one
reduction follows a single root-to-leaf path; the cost is linear in the
number of bits dispatched on, not exponential in them.
`binRanked` has width one, so its block slot is the bare sentinel, and that
alphabet is the subject of the bridge to `Cobham.isTree`.

## Tags

Cobham, ranked alphabet, preorder, recognizer
-/

set_option linter.privateModule false

open Cobham RankedAlphabet

/-- The recognizer at its declared arity: this module's only use of
`Cobham.isRankedOf`, the assertions below reading `Cobham.isRankedSem`
instead. -/
def isRankedArity : COf 1 := isRankedOf narrowAlphabet

/-- At the two-symbol alphabet a leaf's spelling is accepted. -/
theorem isRankedSem_binRanked_leaf :
    isRankedSem RankedAlphabet.Binary.binRanked ![[false]] = [true] := by decide

/-- A bare node symbol has no children pending, and is rejected. -/
theorem isRankedSem_binRanked_bare_node :
    isRankedSem RankedAlphabet.Binary.binRanked ![[true]] = [] := by decide

/-- A node over two leaves is accepted. -/
theorem isRankedSem_binRanked_node :
    isRankedSem RankedAlphabet.Binary.binRanked ![[true, false, false]] =
      [true] := by decide

/-- A nullary symbol's block alone is accepted. -/
theorem isRankedSem_narrow_nullary :
    isRankedSem narrowAlphabet ![[false, false]] = [true] := by decide

/-- A block spelling no symbol is rejected. -/
theorem isRankedSem_narrow_no_symbol :
    isRankedSem narrowAlphabet ![[true, true]] = [] := by decide

/-- A unary symbol over a nullary one is accepted. -/
theorem isRankedSem_narrow_unary :
    isRankedSem narrowAlphabet ![[true, false, false, false]] = [true] := by decide

/-- A binary symbol with nothing pending is rejected. -/
theorem isRankedSem_narrow_underflow :
    isRankedSem narrowAlphabet ![[false, true]] = [] := by decide

/-- The decoder recovers the initial state's empty block. -/
theorem decodeState_initial_buf :
    (decodeState narrowAlphabet
      (bits (dispatchWidth narrowAlphabet)
        (stateWord narrowAlphabet ⟨[], 0, true⟩))).buf = [] := by decide

/-- And its pending count. -/
theorem decodeState_initial_depth :
    (decodeState narrowAlphabet
      (bits (dispatchWidth narrowAlphabet)
        (stateWord narrowAlphabet ⟨[], 0, true⟩))).depth = 0 := by decide

/-- And its flag. -/
theorem decodeState_initial_live :
    (decodeState narrowAlphabet
      (bits (dispatchWidth narrowAlphabet)
        (stateWord narrowAlphabet ⟨[], 0, true⟩))).live = true := by decide

/-- The decoder recovers a state carrying one bit of an incomplete block. -/
theorem decodeState_partial_buf :
    (decodeState narrowAlphabet
      (bits (dispatchWidth narrowAlphabet)
        (stateWord narrowAlphabet ⟨[true], 1, true⟩))).buf = [true] := by decide

/-- And a failed state's flag. -/
theorem decodeState_dead_live :
    (decodeState narrowAlphabet
      (bits (dispatchWidth narrowAlphabet)
        (stateWord narrowAlphabet ⟨[], 2, false⟩))).live = false := by decide

/-- A pending count above the depth window is recovered capped, which is what
`Cobham.decodeState_stateWord_of_lt`'s `min` states. That window is
`R.maxArity + 1`, three at `narrowAlphabet`, and is not `dispatchWidth`, which
is six there. -/
theorem decodeState_capped_depth :
    (decodeState narrowAlphabet
      (bits (dispatchWidth narrowAlphabet)
        (stateWord narrowAlphabet ⟨[], 5, true⟩))).depth = 3 := by decide

/-- A block of the alphabet's own width overflows the slot, so
`Cobham.length_bufBits_of_lt`'s hypothesis is consumed rather than
decorative. -/
theorem length_bufBits_overflow :
    (bufBits narrowAlphabet [false, true]).length = 3 := by decide

/-- The recognizer and the validity scan accept the same words, at the
alphabet reaching the block that spells no symbol, over every word of length
at most six. -/
theorem isRankedSem_eq_validBool_narrow :
    (wordsUpTo 6).all (fun w ↦
      (isRankedSem narrowAlphabet ![w] == [true]) ==
        narrowAlphabet.validBool w) = true := by
  set_option maxRecDepth 100000 in decide

/-- And at an alphabet every one of whose blocks spells a symbol, over every
word of length at most five. -/
theorem isRankedSem_eq_validBool_sample :
    (wordsUpTo 5).all (fun w ↦
      (isRankedSem sampleAlphabet ![w] == [true]) ==
        sampleAlphabet.validBool w) = true := by
  set_option maxRecDepth 100000 in decide

/-- And at the two-symbol alphabet, over every word of length at most six. -/
theorem isRankedSem_eq_validBool_binRanked :
    (wordsUpTo 6).all (fun w ↦
      (isRankedSem RankedAlphabet.Binary.binRanked ![w] == [true]) ==
        RankedAlphabet.Binary.binRanked.validBool w) = true := by
  set_option maxRecDepth 100000 in decide
```

`RankedAlphabet.Binary.binRanked` is reached through
`Geb/Mathlib/Computability/Cobham/RankedTree.lean`'s own public import of
`Geb/Mathlib/Data/Tree/Ranked/Binary.lean`, so the mirror adds no import for
it.

The decoder's inversion is asserted field by field because
`RankedAlphabet.Scan` carries no `DecidableEq` instance and derives none; a
`decide` on an equation of two `Scan` values fails instance synthesis.

- [ ] **Step 2: Import the mirror from the test index**

In `GebTests/Mathlib/Computability/Cobham.lean` add, in alphabetical position:

```lean
import GebTests.Mathlib.Computability.Cobham.RankedTree
```

- [ ] **Step 3: Build and test**

Run: `lake build GebTests.Mathlib.Computability.Cobham` and then `lake test`,
one after the other rather than concurrently.
Expected: both succeed with no error and no warning. Expect the sweeps to
dominate the module's build time; see the measurement above.

- [ ] **Step 4: Build**

Run: `lake build`, then `lake lint -- GebTests`.
Expected: both succeed with no error and no warning. The prototype went in
Task 1, so nothing else is removed here.

- [ ] **Step 5: Commit**

```bash
jj describe -m "test(cobham): mirror the generic ranked recognizer"
jj new
```

---

### Task 11: The catalogue and the roadmap

**Files:**

- Modify: `docs/index.md`
- Modify: `TODO.md`

- [ ] **Step 1: Catalogue the module**

In `docs/index.md`, in the section listing
`Geb/Mathlib/Computability/Cobham/*`, add an entry for
`Geb/Mathlib/Computability/Cobham/RankedTree.lean` in the position its
dependencies give it — after `Cases.lean` and `Tree.lean`, both of which it
imports. Follow the shape of the neighbouring entries: what the module
contains, and what it depends on. Do not count the module's declarations.

Extend the entries for
`Geb/Mathlib/Data/Tree/Ranked/{Basic,Code,Preorder}.lean` with the statements
Tasks 1 to 3 added.

- [ ] **Step 2: Record B6 as done**

In `TODO.md` § Extensions of the tree recognizers, mark B6 done in the shape
B1 and B2 use, and leave B3, B4 and B5 as they stand.

Add one deferral alongside the existing ones: `Cobham/Tree.lean`'s
`combSem_def` docstring states that a `def` carries no equation lemma, while
`length_rankedSem_le` here rewrites by `rankedSem`'s generated one. Whether
the same holds of `combSem`, which takes no argument, is untried; check
whether `rw [combSem]` closes where `combSem_def` is used, and correct the
docstring if it does. A short branch of its own either way.

- [ ] **Step 3: Check the Markdown gates**

Run, one after the other:

```bash
doctoc --update-only .
markdownlint-cli2 '**/*.md'
scripts/check-md-links.sh
```

Expected: no violation; `doctoc` reports no file changed, or re-commit the
regenerated tables of contents.

- [ ] **Step 4: Commit**

```bash
jj describe -m "doc(cobham): catalogue the generic ranked recognizer"
jj new
```

---

### Task 12: Verification, and the plan's removal

**Files:**

- Delete: `docs/superpowers/plans/2026-08-10-cobham-ranked-tree.md`
- Modify: `docs/superpowers/plans/2026-08-10-tree-recognizer-session-handoff.md`
- Modify: `docs/superpowers/plans/2026-08-10-ranked-tree-b2-b5-handoff.md`

- [ ] **Step 1: Run every gate**

Run each alone; two concurrent `lake` invocations corrupt package traces.

```bash
lake build
lake test
lake lint
lake lint -- GebTests
scripts/lint-imports.sh
scripts/pre-push.sh
```

Expected: each succeeds with no error and no warning. `lake lint` is what
establishes that every new declaration measures `{propext, Quot.sound}`.
`scripts/pre-push.sh` runs `lake shake --add-public --keep-implied
--keep-prefix Geb GebTests`, which is the invocation this repository uses and
which settles the import question Task 9 Step 1 raises; a bare `lake shake`
reports against different settings and is not run here.

- [ ] **Step 2: Read the segment as one body of work**

A task-scoped review cannot see a module-scoped defect: every per-task review
of the previous segment came back clean, and the whole-segment review then
found docstrings asserting the opposite of what their proofs did, and a pair of
tests that opened with a rewrite replacing the construction under test before
anything computed. This step is that review, and it runs before the plan is
removed so that any fix it produces lands among the implementation commits, as
[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape orders them.

Read the whole diff of the segment against `main` and check at least:

- every docstring against what its declaration actually proves, and every
  module docstring against what its module actually contains;
- every mirror assertion for a rewrite or `simp` that replaces the
  construction under test before anything computes;
- the module docstrings' sections for vacuity, order, and for claims the
  module does not support, including any attributed to another module;
- every line of every `.lean` file against the 100-character limit,
  `linter.style.longLine` being an error here;
- prose against
  [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Style and references, in
  particular counts of a population the project keeps adding to, and
  § Document only the persistent, in particular references to this plan or to
  the design.

Commit any fix it produces before continuing.

- [ ] **Step 3: Update the two handoffs**

In
[the workstream handoff](2026-08-10-ranked-tree-b2-b5-handoff.md), revise
every section recording B6 as outstanding — § Where the workstream stands,
§ B6: the generic ranked recognizer, and § What completion means — moving it
to done in the shape B2 and the case combinator use, and add to § Facts
established by building the facts § Facts this plan rests on records, which
outlive this plan. That section's preamble says each of its facts cost a
failed build during B1; generalise it in the same edit, these having cost one
during segment 2.

In
[the session handoff](2026-08-10-tree-recognizer-session-handoff.md), revise
§ Status of every roadmap item, § Where the line stands, § What this session
delivered and § What to pick up next: B6 is done, the next work is segment 3
(B3, the fold), and the design's § Segment 3 is its specification.

- [ ] **Step 4: Re-run the Markdown gates, then commit the handoff revisions**

Step 3 changes a heading in the workstream handoff, so its table of contents
moves; regenerate it before committing rather than letting it land in a later
commit.

```bash
doctoc --update-only .
markdownlint-cli2 '**/*.md'
jj describe -m "doc(cobham): hand off the workstream after the ranked recognizer"
jj new
```

- [ ] **Step 5: Remove this plan**

```bash
rm docs/superpowers/plans/2026-08-10-cobham-ranked-tree.md
```

[The design](../specs/2026-08-10-cobham-cases-fold-ranked-design.md) is
carried to segment 3 and removed there; this plan is transient to this
segment, per
[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape.

- [ ] **Step 6: Re-run the Markdown gates and the pre-push checklist**

```bash
doctoc --update-only .
markdownlint-cli2 '**/*.md'
scripts/pre-push.sh
```

Expected: each succeeds.

- [ ] **Step 7: Commit**

```bash
jj describe -m "doc(cobham): remove the transient plan"
jj new
```

- [ ] **Step 8: Set the segment's bookmark**

This is the last step: the bookmark must name the segment's head, and Steps 2,
4 and 7 each add commits after the implementation tasks.

```bash
jj bookmark set feat/cobham-ranked-tree -r @-
```

No push. [AGENTS.md](../../../AGENTS.md) § No `jj git push` without user
line-by-line review binds this segment, first creation included.
