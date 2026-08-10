# The scan combinator over Cobham's class — implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` (recommended) or
> `superpowers:executing-plans` to implement this plan task-by-task. Steps
> use checkbox (`- [ ]`) syntax for tracking.

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Global constraints](#global-constraints)
- [How verification works here](#how-verification-works-here)
- [File structure](#file-structure)
  - [Task 1: the transport-composition lemma](#task-1-the-transport-composition-lemma)
  - [Task 2: the raw layer](#task-2-the-raw-layer)
  - [Task 3: the meanings and their characterizations](#task-3-the-meanings-and-their-characterizations)
  - [Task 4: the expression](#task-4-the-expression)
  - [Task 5: the test mirror](#task-5-the-test-mirror)
  - [Task 6: rebuilding the recognizer](#task-6-rebuilding-the-recognizer)
  - [Task 7: the documentation index](#task-7-the-documentation-index)
  - [Task 8: the roadmap and the handoff](#task-8-the-roadmap-and-the-handoff)
  - [Task 9: removing the prototype and verifying the branch](#task-9-removing-the-prototype-and-verifying-the-branch)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

**Goal:** Package `Cobham.evalRec` as a scan combinator — a right-to-left
fold over a bitstring whose state is a bitstring — and rebuild
`Cobham.isTree`'s scan on it.

**Architecture:** Three layers, mirroring the existing
`combRaw`/`combSem`/`comb` shape. A raw layer assembles a `boundedRec`
node from a base, two arity-one steps lifted into `evalRec`'s step
shape, and a bound child prepending `growth` bits. A meaning layer reads
that node's semantics at the raw tree, before any recursion bound
exists, and characterizes it as a `List.foldr`. A smart constructor then
takes a length bound on that meaning and produces the member of `C`.

**Tech Stack:** Lean 4 (v4.33.0-rc2 via `lean-toolchain`), mathlib, lake.
No new dependencies.

Every declaration and proof in Tasks 1 to 4 has been compiled at
variable base, steps and growth in a prototype and measured
`[propext, Quot.sound]`. Transcribe the code as given; where a step says
a proof is `rfl`, it is `rfl`.

**Source spec:**
[docs/superpowers/specs/2026-08-10-cobham-scanner-design.md](../specs/2026-08-10-cobham-scanner-design.md).

## Global constraints

- **`jj` for every state-mutating VCS operation.** Never a mutating `git`
  subcommand — a `PreToolUse` hook blocks them. Commit with
  `jj commit <paths> -m "<message>"`. No pushing at any point in this
  plan.
- **Commit messages** follow
  [docs/rules/ci-and-workflow.md](../../rules/ci-and-workflow.md)
  § Commit-message convention: `type(scope): subject`, imperative present
  tense, no capital first letter, no trailing period. Types used here:
  `feat`, `fix`, `doc`, `test`, `refactor`.
- **No `noncomputable`, no `sorry` in a commit, no `native_decide`, no
  `admit`.** Every declaration's axioms must lie in
  `{propext, Quot.sound}`; `lake lint` enforces it.
- **Recursion only through recursors.** No `induction` tactic, no
  self-calling `def`, no `termination_by`. Use `Nat.rec`, `List.rec`,
  `WType.rec`; `cases` is permitted for non-recursive splits only.
- **Line length 100 characters; two-space indent; Unicode notation.**
- **Module system:** every `.lean` file opens with the copyright block
  then `module`. `public import` for what callers need, plain `import`
  otherwise; `public import`s grouped before plain ones, separated by a
  blank line.
- **Module docstrings** are mandatory after imports, with sections in
  order: `# Title`, summary, `## Main definitions`, `## Main statements`,
  `## Implementation notes`, `## References`, `## Tags` — each present
  when it has content, omitted (never a placeholder) when vacuous. Every
  `def` and every theorem of public interest carries a `/-- … -/`
  docstring. No empty lines inside a declaration.
- **`Geb/Mathlib/` may import only** `Mathlib.*`, `Batteries.*`,
  `Geb.Mathlib.*`; `GebTests/Mathlib/` adds `GebTests.Mathlib.*`. The
  prefix `Geb.Mathlib.` must not appear outside `^import` lines.
- **Markdown** edited in Tasks 7 and 8 must pass
  `markdownlint-cli2 '**/*.md'` and keep its `doctoc` table of contents
  current. Prose is formal, precise, dry; no value-laden adjectives; no
  counts over a population the project keeps adding to.

## How verification works here

This plan has no red-green test cycle in the usual sense. In Lean the
compiler is the test: a statement that is false does not build, and a
proof step that does not apply is an error. Each task therefore runs

```bash
lake build Geb.Mathlib.Computability.Cobham.Scan
```

or the equivalent target, and treats a clean build as the passing test.
Two further gates run at the end of tasks that touch semantics:

```bash
lake test   # builds GebTests, whose `rfl`/`decide` theorems assert values
lake lint   # runs the axiom linter over every Geb and GebTests declaration
```

`lakefile.toml` sets `weak.warningAsError = true`, so a linter warning
fails the build. Do not add `set_option` escapes to silence one; fix the
code. In particular `linter.flexible` requires a bare `simp` that
modifies the goal to be terminal, and `linter.style.show` requires a
`show` that changes the goal to be `change`.

## File structure

| File | Responsibility |
| --- | --- |
| `Geb/Mathlib/Computability/Cobham/Basic.lean` | Modified: gains `transport_transport`. |
| `Geb/Mathlib/Computability/Cobham/Scan.lean` | Created: the combinator, all three layers. |
| `Geb/Mathlib/Computability/Cobham/Tree.lean` | Modified: steps to arity one; scan rebuilt on the combinator. |
| `Geb/Mathlib/Computability/Cobham.lean` | Modified: index import. |
| `GebTests/Mathlib/Computability/Cobham/Scan.lean` | Created: the mirror. |
| `GebTests/Mathlib/Computability/Cobham.lean` | Modified: index import. |
| `docs/index.md` | Modified: entries for the new and changed modules. |
| `TODO.md` | Modified: the roadmap entry. |
| `docs/superpowers/plans/2026-08-10-ranked-tree-b2-b5-handoff.md` | Modified: its § B2 and its counts. |
| `Geb/Internal/ScanSpike.lean` | Deleted in Task 9. |

---

### Task 1: the transport-composition lemma

**Files:**

- Modify: `Geb/Mathlib/Computability/Cobham/Basic.lean` — add one theorem
  after `transport` (line 235) and one bullet to `## Main statements`
  (lines 82-88).

**Interfaces:**

- Consumes: `Cobham.transport` and `Cobham.Sem`, both already in the
  module.
- Produces: `Cobham.transport_transport {i j k : ℕ} (h : i = j)
  (g : j = k) (v : Sem i) : transport g (transport h v) =
  transport (h.trans g) v`. Task 3 uses it twice.

- [ ] **Step 1: add the theorem**

Insert immediately after the `transport` definition (which ends at line
235 with `transport {i j : ℕ} (h : i = j) (v : Sem i) : Sem j := h ▸ v`):

```lean
/-- Transport composes. A transport along a composite equality and the
composition of two transports agree, which is not definitional when
neither index reduces: at a variable expression the arity equation is
opaque, so neither `Eq.rec` fires. Named for its left-hand side, as
core's `cast_cast` is. -/
theorem transport_transport {i j k : ℕ} (h : i = j) (g : j = k) (v : Sem i) :
    transport g (transport h v) = transport (h.trans g) v := by
  subst h
  subst g
  rfl
```

- [ ] **Step 2: add its entry to the module docstring**

In `## Main statements` (which currently ends with the `condSem_eq`
bullet), append:

```text
* `Cobham.transport_transport` — transport along a composite equality is
  the composition of two transports.
```

- [ ] **Step 3: build**

Run: `lake build Geb.Mathlib.Computability.Cobham.Basic`
Expected: `Built Geb.Mathlib.Computability.Cobham.Basic`, no errors, no
warnings.

- [ ] **Step 4: commit**

```bash
jj commit Geb/Mathlib/Computability/Cobham/Basic.lean \
  -m "feat(cobham): add the transport-composition lemma"
```

---

### Task 2: the raw layer

**Files:**

- Create: `Geb/Mathlib/Computability/Cobham/Scan.lean`

**Interfaces:**

- Consumes: from `Cobham.Basic` — `sig`, `Shape`, `arity`, `C`, `COf`,
  `Sem`, `transport`, `fst_eval`; from
  `Geb.Mathlib.Data.PFunctor.Slice.W` (transitively) —
  `SlicePFunctor.wIndexRoot`, `SlicePFunctor.WValid`,
  `SlicePFunctor.wIndexValid_index_eq_wIndexRoot`.
- Produces, all used by Tasks 3 and 4:
  - `Cobham.boundRaw : ℕ → sig.toPFunctor.W`
  - `Cobham.wIndexRoot_boundRaw (growth : ℕ) :
    sig.wIndexRoot (boundRaw growth) = 1`
  - `Cobham.wValid_boundRaw (growth : ℕ) : sig.WValid (boundRaw growth)`
  - `Cobham.arity_boundRaw (growth : ℕ) :
    arity ⟨boundRaw growth, wValid_boundRaw growth⟩ = 1`
  - `Cobham.liftRaw (e : sig.toPFunctor.W) : sig.toPFunctor.W`
  - `Cobham.wIndexRoot_liftRaw (e : sig.toPFunctor.W) :
    sig.wIndexRoot (liftRaw e) = 2`
  - `Cobham.wValid_liftRaw (e : sig.toPFunctor.W) (he : sig.WValid e)
    (ha : sig.wIndexRoot e = 1) : sig.WValid (liftRaw e)`
  - `Cobham.scanRaw (base step₀ step₁ : sig.toPFunctor.W) (growth : ℕ) :
    sig.toPFunctor.W`
  - `Cobham.wIndexRoot_scanRaw`, `Cobham.wValid_scanRaw` (six hypotheses)
  - `Cobham.scanW (base : COf 0) (step₀ step₁ : COf 1) (growth : ℕ) : sig.W`
  - `Cobham.arity_scanW (base : COf 0) (step₀ step₁ : COf 1) (growth : ℕ) :
    arity (scanW base step₀ step₁ growth) = 1`

- [ ] **Step 1: create the file with its header, imports and docstring**

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Computability.Cobham.Basic

/-!
# The scan combinator over Cobham's class

A scanner is a right-to-left fold over a bitstring whose state is itself a
bitstring: a base value, one step per bit read, and a bound on how far the
state can exceed the input. `Cobham.evalRec` supplies the recursion, peeling
the word's last bit at each step and passing the rest of the word on; the
state is the recursive value it passes alongside.

`evalRec` applies its step to `Fin.cons v (Fin.cons (ih x) x)`: slot zero is
the rest of the word, slot one the recursive value, slots two upward the
ambient environment. A fold's step is a function of the state alone, so a
scanner's steps are `COf 1`, lifted into the shape `evalRec` applies by
composition with `proj 2 1`.

## Main definitions

* `Cobham.boundRaw` — the bound child, `succ true` iterated over `proj 1 0`.
* `Cobham.liftRaw` — a step of arity one in `evalRec`'s step shape.
* `Cobham.scanRaw` — the `boundedRec` node over a base, two lifted steps and
  a bound child.
* `Cobham.scanW` — that node over expressions, carrying admissibility.

## Main statements

* `Cobham.wValid_boundRaw`, `Cobham.wValid_liftRaw`, `Cobham.wValid_scanRaw`
  — admissibility of the three trees, the last from its components'.
* `Cobham.wIndexRoot_boundRaw`, `Cobham.wIndexRoot_liftRaw`,
  `Cobham.wIndexRoot_scanRaw`, `Cobham.arity_boundRaw`,
  `Cobham.arity_scanW` — their arities.

## Implementation notes

Admissibility of a node requires the children's index equations alongside
their own admissibility, `SlicePFunctor.wValid_mk` constraining
`wIndexRoot ∘ children`; that is where the raw layer and the expression
layer meet, and it is why `wValid_scanRaw` takes six hypotheses rather than
three. The equations are stated through
`SlicePFunctor.wIndexValid_index_eq_wIndexRoot`, the goal presenting the
index as `WIndex.index ∘ wIndexValid` rather than as `wIndexRoot`.

`decide` discharges none of these: at a variable child nothing reduces. It
remains available at a named constant, which is what the instances built on
this module use.

A child family indexed by `Fin 4` is bound as `fun d : Fin 4 ↦ …`. Instance
search stops at reducible transparency on the projection `sig.B a`, so
without the ascription a numeral index fails to elaborate.

## References

* [Cobham1965]

## Tags

Cobham, bounded recursion on notation, scan, fold, polynomial functor
-/

namespace Cobham

public section

end

end Cobham
```

- [ ] **Step 2: build the skeleton**

Run: `lake build Geb.Mathlib.Computability.Cobham.Scan`
Expected: builds clean. An empty `public section` is legal.

- [ ] **Step 3: add the bound child and its three lemmas**

Insert inside `public section`:

```lean
/-- The bound child: `succ true` iterated `growth` times over the recursion
variable, of arity one. `growth = 0` is the `Nat.rec` base, the bare
projection. -/
@[expose] def boundRaw : ℕ → sig.toPFunctor.W :=
  Nat.rec (WType.mk (.proj 1 0) Fin.elim0)
    fun _ ih ↦
      WType.mk (.comp 1 1) fun d ↦
        match d with
        | .inl () => WType.mk (.succ true) Fin.elim0
        | .inr _ => ih

/-- The bound child has arity one, at every growth. A case split, not a
recursion: both `Nat.rec` branches are nodes whose shape `q` sends to one. -/
theorem wIndexRoot_boundRaw (growth : ℕ) :
    sig.wIndexRoot (boundRaw growth) = 1 := by
  cases growth with
  | zero => rfl
  | succ _ => rfl

/-- The bound child is admissible, at every growth. -/
theorem wValid_boundRaw (growth : ℕ) : sig.WValid (boundRaw growth) :=
  Nat.rec ⟨fun c ↦ c.elim0, funext fun c ↦ c.elim0⟩
    (fun g ih ↦
      ⟨fun d ↦ match d with
        | .inl () => ⟨fun c ↦ c.elim0, funext fun c ↦ c.elim0⟩
        | .inr _ => ih,
      funext fun d ↦ match d with
        | .inl () => rfl
        | .inr _ =>
          (sig.wIndexValid_index_eq_wIndexRoot (boundRaw g)).trans
            (wIndexRoot_boundRaw g)⟩)
    growth

/-- The bound child's arity, in the form `fst_eval` composes with. -/
theorem arity_boundRaw (growth : ℕ) :
    arity ⟨boundRaw growth, wValid_boundRaw growth⟩ = 1 :=
  wIndexRoot_boundRaw growth
```

- [ ] **Step 4: build**

Run: `lake build Geb.Mathlib.Computability.Cobham.Scan`
Expected: builds clean.

- [ ] **Step 5: add the lift and its two lemmas**

```lean
/-- A step of arity one, carried into the shape `evalRec` applies: a `comp`
node whose head is the step and whose sole argument reaches the recursive
value through `proj 2 1`. -/
@[expose] def liftRaw (e : sig.toPFunctor.W) : sig.toPFunctor.W :=
  WType.mk (.comp 2 1) fun d ↦
    match d with
    | .inl () => e
    | .inr _ => WType.mk (.proj 2 1) Fin.elim0

/-- A lifted step has arity two, whatever it lifts. -/
theorem wIndexRoot_liftRaw (e : sig.toPFunctor.W) :
    sig.wIndexRoot (liftRaw e) = 2 := rfl

/-- A lifted step is admissible when what it lifts is admissible and of
arity one. -/
theorem wValid_liftRaw (e : sig.toPFunctor.W) (he : sig.WValid e)
    (ha : sig.wIndexRoot e = 1) : sig.WValid (liftRaw e) :=
  ⟨fun d ↦ match d with
    | .inl () => he
    | .inr _ => ⟨fun c ↦ c.elim0, funext fun c ↦ c.elim0⟩,
  funext fun d ↦ match d with
    | .inl () => (sig.wIndexValid_index_eq_wIndexRoot e).trans ha
    | .inr _ => rfl⟩
```

- [ ] **Step 6: build**

Run: `lake build Geb.Mathlib.Computability.Cobham.Scan`
Expected: builds clean.

- [ ] **Step 7: add the scan node, its two lemmas, and the expression form**

```lean
/-- The scan node: a `boundedRec` of ambient arity zero over a base, two
lifted steps and a bound child. -/
@[expose] def scanRaw (base step₀ step₁ : sig.toPFunctor.W) (growth : ℕ) :
    sig.toPFunctor.W :=
  WType.mk (.boundedRec 0)
    ![base, liftRaw step₀, liftRaw step₁, boundRaw growth]

/-- The scan node has arity one. -/
theorem wIndexRoot_scanRaw (base step₀ step₁ : sig.toPFunctor.W) (growth : ℕ) :
    sig.wIndexRoot (scanRaw base step₀ step₁ growth) = 1 := rfl

/-- The scan node is admissible when its base is, at arity zero, and its two
steps are, at arity one. These index equations are where the raw layer and
the expression layer meet. -/
theorem wValid_scanRaw (base step₀ step₁ : sig.toPFunctor.W) (growth : ℕ)
    (hb : sig.WValid base) (hb' : sig.wIndexRoot base = 0)
    (h₀ : sig.WValid step₀) (h₀' : sig.wIndexRoot step₀ = 1)
    (h₁ : sig.WValid step₁) (h₁' : sig.wIndexRoot step₁ = 1) :
    sig.WValid (scanRaw base step₀ step₁ growth) :=
  ⟨fun d : Fin 4 ↦ match d with
    | 0 => hb
    | 1 => wValid_liftRaw step₀ h₀ h₀'
    | 2 => wValid_liftRaw step₁ h₁ h₁'
    | 3 => wValid_boundRaw growth,
  funext fun d : Fin 4 ↦ match d with
    | 0 => (sig.wIndexValid_index_eq_wIndexRoot base).trans hb'
    | 1 => (sig.wIndexValid_index_eq_wIndexRoot _).trans (wIndexRoot_liftRaw step₀)
    | 2 => (sig.wIndexValid_index_eq_wIndexRoot _).trans (wIndexRoot_liftRaw step₁)
    | 3 => (sig.wIndexValid_index_eq_wIndexRoot _).trans (wIndexRoot_boundRaw growth)⟩

/-- The scan node over expressions, carrying its admissibility. -/
@[expose] def scanW (base : COf 0) (step₀ step₁ : COf 1) (growth : ℕ) :
    sig.W :=
  ⟨scanRaw base.1.1.1 step₀.1.1.1 step₁.1.1.1 growth,
    wValid_scanRaw _ _ _ growth base.1.1.2 base.2 step₀.1.1.2 step₀.2
      step₁.1.1.2 step₁.2⟩

/-- The scan node's arity, in the form `fst_eval` composes with. -/
theorem arity_scanW (base : COf 0) (step₀ step₁ : COf 1) (growth : ℕ) :
    arity (scanW base step₀ step₁ growth) = 1 := rfl
```

- [ ] **Step 8: build**

Run: `lake build Geb.Mathlib.Computability.Cobham.Scan`
Expected: builds clean.

- [ ] **Step 9: commit**

```bash
jj commit Geb/Mathlib/Computability/Cobham/Scan.lean \
  -m "feat(cobham): assemble the scan node and its admissibility"
```

---

### Task 3: the meanings and their characterizations

**Files:**

- Modify: `Geb/Mathlib/Computability/Cobham/Scan.lean` — append
  declarations and extend the docstring's two lists.

**Interfaces:**

- Consumes: everything Task 2 produces, plus `Cobham.transport_transport`
  from Task 1 and `Cobham.eval`, `Cobham.C.eval`, `Cobham.fst_eval` from
  `Basic`.
- Produces, used by Task 4 and by every downstream consumer:
  - `Cobham.boundSem (growth : ℕ) : Sem 1`
  - `Cobham.boundSem_eq : ∀ (growth : ℕ) (x : Fin 1 → List Bool),
    boundSem growth x = List.replicate growth true ++ x 0`
  - `Cobham.scanSem (base : COf 0) (step₀ step₁ : COf 1) (growth : ℕ) : Sem 1`
  - `Cobham.baseWord (base : COf 0) : List Bool`
  - `Cobham.stepWord (step : COf 1) (r : List Bool) : List Bool`
  - `Cobham.scanStepWord (step₀ step₁ : COf 1) (b : Bool)
    (r : List Bool) : List Bool`
  - `Cobham.baseWord_eq_eval`, `Cobham.stepWord_eq_eval`
  - `Cobham.scanSem_nil`, `Cobham.scanSem_cons`, `Cobham.scanSem_eq`

- [ ] **Step 1: add the bound child's meaning and its characterization**

Append inside `public section`:

```lean
/-- The meaning of the bound child at its arity. -/
@[expose] def boundSem (growth : ℕ) : Sem 1 :=
  transport ((fst_eval _).trans (arity_boundRaw growth))
    (eval ⟨boundRaw growth, wValid_boundRaw growth⟩).2

/-- The bound child prepends `growth` bits to the recursion variable. Stated
at an arbitrary environment, which is the form the recursion bound reads it
at; at `![u]` it does not match the goal `RecBoundedValue` presents. -/
theorem boundSem_eq : ∀ (growth : ℕ) (x : Fin 1 → List Bool),
    boundSem growth x = List.replicate growth true ++ x 0 :=
  Nat.rec (fun _ ↦ rfl)
    (fun g ih x ↦ by
      change true :: boundSem g x = _
      rw [ih x]
      rfl)
```

- [ ] **Step 2: build**

Run: `lake build Geb.Mathlib.Computability.Cobham.Scan`
Expected: builds clean. If the `change` fails, the `comp` node's argument
child is being applied at the wrong environment: it receives the ambient
`x` unchanged, not `fun _ ↦ x 0`.

- [ ] **Step 3: add the scan's meaning and the component words**

```lean
/-- The meaning of a scan at its arity, read at the raw tree. `Cobham.eval`
asks only for admissibility as a `sig`-tree, not for the recursion bound, so
a scanner is characterized before the expression carrying that bound
exists. -/
@[expose] def scanSem (base : COf 0) (step₀ step₁ : COf 1) (growth : ℕ) :
    Sem 1 :=
  transport ((fst_eval _).trans (arity_scanW base step₀ step₁ growth))
    (eval (scanW base step₀ step₁ growth)).2

/-- The word a base contributes, read at the raw tree. -/
@[expose] def baseWord (base : COf 0) : List Bool :=
  transport ((fst_eval base.1.1).trans base.2) (eval base.1.1).2 Fin.elim0

/-- The word a step contributes at the state it reads, read at the raw
tree. -/
@[expose] def stepWord (step : COf 1) (r : List Bool) : List Bool :=
  transport ((fst_eval step.1.1).trans step.2) (eval step.1.1).2 ![r]

/-- The semantic step of a scan: the bit selects which step reads the
state. -/
@[expose] def scanStepWord (step₀ step₁ : COf 1) (b : Bool) (r : List Bool) :
    List Bool :=
  if b then stepWord step₁ r else stepWord step₀ r
```

- [ ] **Step 4: build**

Run: `lake build Geb.Mathlib.Computability.Cobham.Scan`
Expected: builds clean.

- [ ] **Step 5: add the two bridges to `C.eval`**

```lean
/-- The base's word is the one its expression of `C` carries. Not a `rfl`:
a component's arity equation is opaque at a variable, so the transport along
the composite and the composition of two transports differ. -/
theorem baseWord_eq_eval (base : COf 0) :
    baseWord base = transport base.2 base.1.eval Fin.elim0 :=
  (congrFun (transport_transport (fst_eval base.1.1) base.2 (eval base.1.1).2)
    Fin.elim0).symm

/-- A step's word is the one its expression of `C` carries, as
`baseWord_eq_eval` for the base. -/
theorem stepWord_eq_eval (step : COf 1) (r : List Bool) :
    stepWord step r = transport step.2 step.1.eval ![r] :=
  (congrFun (transport_transport (fst_eval step.1.1) step.2 (eval step.1.1).2)
    ![r]).symm
```

- [ ] **Step 6: build**

Run: `lake build Geb.Mathlib.Computability.Cobham.Scan`
Expected: builds clean.

- [ ] **Step 7: add the three characterizations**

```lean
/-- The scan's value on the empty bitstring is the base's word. -/
theorem scanSem_nil (base : COf 0) (step₀ step₁ : COf 1) (growth : ℕ) :
    scanSem base step₀ step₁ growth ![[]] = baseWord base := rfl

/-- One step of the scan: the bit selects the step, which reads the value the
scan of the rest of the word returns. -/
theorem scanSem_cons (base : COf 0) (step₀ step₁ : COf 1) (growth : ℕ)
    (b : Bool) (w : List Bool) :
    scanSem base step₀ step₁ growth ![b :: w] =
      scanStepWord step₀ step₁ b (scanSem base step₀ step₁ growth ![w]) := by
  have hfun : ∀ r : List Bool, (fun _ : Fin 1 ↦ r) = ![r] :=
    fun r ↦ funext fun i ↦ match i with | ⟨0, _⟩ => rfl
  cases b
  · change transport ((fst_eval step₀.1.1).trans step₀.2) (eval step₀.1.1).2
      (fun _ ↦ scanSem base step₀ step₁ growth ![w]) = _
    exact congrArg _ (hfun _)
  · change transport ((fst_eval step₁.1.1).trans step₁.2) (eval step₁.1.1).2
      (fun _ ↦ scanSem base step₀ step₁ growth ![w]) = _
    exact congrArg _ (hfun _)

/-- A scanner computes the right fold of its steps over the word, from its
base. It holds at every growth, `evalValue`'s `boundedRec` clause not
consulting its bound child. -/
theorem scanSem_eq (base : COf 0) (step₀ step₁ : COf 1) (growth : ℕ)
    (w : List Bool) :
    scanSem base step₀ step₁ growth ![w] =
      w.foldr (scanStepWord step₀ step₁) (baseWord base) :=
  List.rec (scanSem_nil base step₀ step₁ growth)
    (fun b v ih ↦ (scanSem_cons base step₀ step₁ growth b v).trans
      (congrArg (scanStepWord step₀ step₁ b) ih)) w
```

- [ ] **Step 8: build**

Run: `lake build Geb.Mathlib.Computability.Cobham.Scan`
Expected: builds clean. If `scanSem_nil` is not `rfl`, `baseWord` has been
written with `base.1.eval` rather than in the composed-transport form; the
composed form is what makes it `rfl`.

- [ ] **Step 9: extend the module docstring**

Append to `## Main definitions`:

```text
* `Cobham.boundSem`, `Cobham.scanSem` — the meanings of the bound child and
  of the scan, at arity one.
* `Cobham.baseWord`, `Cobham.stepWord`, `Cobham.scanStepWord` — the words a
  base and a step contribute, and the semantic step of the fold.
```

Append to `## Main statements`:

```text
* `Cobham.boundSem_eq` — the bound child prepends `growth` bits.
* `Cobham.scanSem_nil`, `Cobham.scanSem_cons`, `Cobham.scanSem_eq` — the
  scan on the empty word, on one bit, and as a `List.foldr`.
* `Cobham.baseWord_eq_eval`, `Cobham.stepWord_eq_eval` — each component's
  word is the one its expression of `C` carries.
```

Append to `## Implementation notes`:

```text
Each component's meaning is transported along the composition of `fst_eval`
with the component's arity equation, in one step rather than two.
`transport` along an equation whose sides reduce to the same literal
disappears by proof irrelevance; along an opaque equation it does not, and a
transport along a composite equality is then not definitionally the
composition of two transports. The scan node's own arity reduces to one
whatever its children are, so its transport disappears; a component's arity
equation is `base.2` or `step.2` at a variable, which reduces to nothing.
The composed form is what keeps `scanSem_nil` a `rfl` and lets
`scanSem_cons`'s `change` land, at the price of making the two bridges to
`C.eval` theorems rather than definitions.

`scanSem_cons` is not definitional in its last step: the lifted step applies
its head at `fun _ : Fin 1 ↦ r`, while `stepWord` applies it at `![r]`, and
the two agree only by `funext`.
```

- [ ] **Step 10: build and commit**

Run: `lake build Geb.Mathlib.Computability.Cobham.Scan`
Expected: builds clean.

```bash
jj commit Geb/Mathlib/Computability/Cobham/Scan.lean \
  -m "feat(cobham): characterise the scan as a right fold"
```

---

### Task 4: the expression

**Files:**

- Modify: `Geb/Mathlib/Computability/Cobham/Scan.lean` — append
  declarations and extend the docstring's two lists.
- Modify: `Geb/Mathlib/Computability/Cobham.lean` — add the index import.

**Interfaces:**

- Consumes: everything Tasks 2 and 3 produce, plus `Cobham.RecBounded`
  from `Basic`.
- Produces:
  - `Cobham.recBounded_boundRaw`, `Cobham.recBounded_liftRaw`
  - `Cobham.scan (base : COf 0) (step₀ step₁ : COf 1) (growth : ℕ)
    (hbound : ∀ w : List Bool,
    (scanSem base step₀ step₁ growth ![w]).length ≤ w.length + growth) : C`
  - `Cobham.scanOf` with the same arguments, at `COf 1`
  - `Cobham.scanSem_eq_eval` — the bridge Task 6 and every later branch use

- [ ] **Step 1: add the two hereditary-bound lemmas**

```lean
/-- The bound child carries no recursion of its own, at every growth. -/
theorem recBounded_boundRaw (growth : ℕ) :
    RecBounded ⟨boundRaw growth, wValid_boundRaw growth⟩ :=
  Nat.rec ⟨trivial, fun c ↦ c.elim0⟩
    (fun _ ih ↦ ⟨trivial, fun d ↦ match d with
      | .inl () => ⟨trivial, fun c ↦ c.elim0⟩
      | .inr _ => ih⟩)
    growth

/-- A lifted step carries the recursions of what it lifts and no other, the
`comp` node's own condition being vacuous. -/
theorem recBounded_liftRaw (step : COf 1) :
    RecBounded ⟨liftRaw step.1.1.1, wValid_liftRaw _ step.1.1.2 step.2⟩ :=
  ⟨trivial, fun d ↦ match d with
    | .inl () => step.1.2
    | .inr _ => ⟨trivial, fun c ↦ c.elim0⟩⟩
```

- [ ] **Step 2: build**

Run: `lake build Geb.Mathlib.Computability.Cobham.Scan`
Expected: builds clean.

- [ ] **Step 3: add the smart constructor and its ascription**

```lean
/-- The scanner as an expression of `C`: the scan node with its recursion
bound discharged from a bound on the value the scan produces. The bound is an
argument rather than a field of a structure, no consumer holding a scanner as
a value. -/
@[expose] def scan (base : COf 0) (step₀ step₁ : COf 1) (growth : ℕ)
    (hbound : ∀ w : List Bool,
      (scanSem base step₀ step₁ growth ![w]).length ≤ w.length + growth) : C :=
  ⟨scanW base step₀ step₁ growth, by
    refine ⟨fun x ↦ ?_, ?_⟩
    · rw [(funext fun i ↦ i.elim0 : Fin.tail x = Fin.tail ![x 0])]
      change _ ≤ (boundSem growth x).length
      rw [boundSem_eq, List.length_append, List.length_replicate]
      exact Nat.le_trans (hbound (x 0)) (Nat.le_of_eq (Nat.add_comm _ _))
    · refine fun b : Fin 4 ↦ ?_
      match b with
      | 0 => exact base.1.2
      | 1 => exact recBounded_liftRaw step₀
      | 2 => exact recBounded_liftRaw step₁
      | 3 => exact recBounded_boundRaw growth⟩

/-- `scan` at its declared arity. -/
@[expose] def scanOf (base : COf 0) (step₀ step₁ : COf 1) (growth : ℕ)
    (hbound : ∀ w : List Bool,
      (scanSem base step₀ step₁ growth ![w]).length ≤ w.length + growth) :
    COf 1 :=
  ⟨scan base step₀ step₁ growth hbound, rfl⟩
```

Note on the bound obligation: `Nat.add_comm` must not be used as a rewrite
here — its motive is not type correct, the same numeral occurring on the
left. The `Nat.le_trans` term above is the working form.

- [ ] **Step 4: build**

Run: `lake build Geb.Mathlib.Computability.Cobham.Scan`
Expected: builds clean.

- [ ] **Step 5: add the bridge downstream consumers use**

```lean
/-- The meaning read at the raw tree is the meaning the expression carries.
Unlike a component's arity, the scan node's own reduces whatever its children
are, so this is a `rfl` at variable base, steps and growth. -/
theorem scanSem_eq_eval (base : COf 0) (step₀ step₁ : COf 1) (growth : ℕ)
    (hbound : ∀ w : List Bool,
      (scanSem base step₀ step₁ growth ![w]).length ≤ w.length + growth) :
    transport (scanOf base step₀ step₁ growth hbound).2
      (scanOf base step₀ step₁ growth hbound).1.eval =
      scanSem base step₀ step₁ growth := rfl
```

- [ ] **Step 6: extend the module docstring**

Append to `## Main definitions`:

```text
* `Cobham.scan`, `Cobham.scanOf` — the scanner as an expression of `C`, and
  at its declared arity.
```

Append to `## Main statements`:

```text
* `Cobham.recBounded_boundRaw`, `Cobham.recBounded_liftRaw` — the bound child
  and a lifted step carry no recursion of their own.
* `Cobham.scanSem_eq_eval` — the meaning read at the raw tree is the meaning
  the expression carries.
```

- [ ] **Step 7: add the index import**

In `Geb/Mathlib/Computability/Cobham.lean`, between the `Basic` and `Tree`
imports (the list is alphabetical by module name, and `Scan` sorts between
them):

```lean
public import Geb.Mathlib.Computability.Cobham.Scan
```

- [ ] **Step 8: build the whole package and check axioms**

Run: `lake build`
Expected: builds clean.

Run: `lake lint`
Expected: no axiom-linter failures.

- [ ] **Step 9: commit**

```bash
jj commit Geb/Mathlib/Computability/Cobham/Scan.lean \
  Geb/Mathlib/Computability/Cobham.lean \
  -m "feat(cobham): give the scanner as an expression of the class"
```

---

### Task 5: the test mirror

**Files:**

- Create: `GebTests/Mathlib/Computability/Cobham/Scan.lean`
- Modify: `GebTests/Mathlib/Computability/Cobham.lean`

**Interfaces:**

- Consumes: `Cobham.scanRaw`, `Cobham.scanSem`, `Cobham.scan`,
  `Cobham.boundSem`, `Cobham.boundSem_eq`, `Cobham.scanSem_eq` from Task 4;
  `Cobham.oneAtRaw`, `Cobham.incRaw`, `Cobham.predRaw`, `Cobham.oneAtOf`,
  `Cobham.incOf` from `Cobham/Tree.lean` and `Cobham/Basic.lean`.
- Produces: nothing consumed by later tasks.

What these samples carry, and what they do not: `scanSem_eq` already proves
the fold equation for every word, so sampling it proves nothing new about the
mathematics. The samples exist to witness two things a theorem does not — that
the meaning reduces in the kernel at named steps, and that the bit selects the
intended step. A transposition of the two step children is invisible to type
checking and to any test that uses one step twice, which is why the fixture
below uses two steps that compute differently.

- [ ] **Step 1: create the file**

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Computability.Cobham.Scan
public import Geb.Mathlib.Computability.Cobham.Tree

/-!
# Tests for the scan combinator

A scanner over two steps that compute differently, so that the samples
distinguish the two step children; the bound child at a growth other than
one and at zero; and a scanner whose recursion bound is discharged from
`Cobham.scanSem_eq`.
-/

namespace GebTests.Cobham.Scan

open Cobham

set_option linter.privateModule false

/-- A scan whose `false` step prepends a bit and whose `true` step drops
one, so that the two steps are told apart by their values. -/
def splitRaw : sig.toPFunctor.W := scanRaw (oneAtRaw 0) incRaw predRaw 1

/-- The meaning of that scan, read at the raw tree. -/
def splitSem : Sem 1 :=
  transport (fst_eval ⟨splitRaw, by decide⟩) (eval ⟨splitRaw, by decide⟩).2

/-- The scan of the empty word is the base, `[true]`. -/
theorem splitSem_nil : splitSem ![[]] = [true] := rfl

/-- The `true` step drops the base's bit and the `false` step prepends to
that, so the value is `[true]` again. Transposing the two step children
would prepend first and drop after, giving `[true]` as well at this word but
not at the next. -/
theorem splitSem_false_true : splitSem ![[false, true]] = [true] := rfl

/-- With the bits exchanged the order of application reverses: the `false`
step prepends to the base and the `true` step drops from that. -/
theorem splitSem_true_false : splitSem ![[true, false]] = [true] := rfl

/-- Two `true` bits drop both bits, leaving the empty word. -/
theorem splitSem_true_true : splitSem ![[true, true]] = [] := rfl

/-- The bound child at growth zero is the recursion variable itself. -/
theorem boundSem_zero (u : List Bool) : boundSem 0 ![u] = u := by
  rw [boundSem_eq]
  rfl

/-- The bound child at a growth other than one prepends that many bits. -/
theorem boundSem_three (u : List Bool) :
    boundSem 3 ![u] = [true, true, true] ++ u := by
  rw [boundSem_eq]
  rfl

/-- A scanner whose recursion bound is discharged from `scanSem_eq`: both
steps are the identity on the state, so the fold returns the base at every
word, of length one. -/
def constScan : C :=
  scan (oneAtOf 0) (⟨⟨⟨WType.mk (.proj 1 0) Fin.elim0, by decide⟩,
      ⟨trivial, fun c ↦ c.elim0⟩⟩, rfl⟩)
    (⟨⟨⟨WType.mk (.proj 1 0) Fin.elim0, by decide⟩,
      ⟨trivial, fun c ↦ c.elim0⟩⟩, rfl⟩) 1
    (fun w ↦ by
      rw [scanSem_eq]
      refine List.rec ?_ (fun b v ih ↦ ?_) w
      · exact Nat.le_add_left 1 0
      · rw [List.foldr_cons]
        cases b <;>
          (change (stepWord _ _).length ≤ _
           rw [stepWord]
           simp only [List.length_cons] at ih ⊢
           omega))

end GebTests.Cobham.Scan
```

- [ ] **Step 2: build the test module**

Run: `lake build GebTests.Mathlib.Computability.Cobham.Scan`
Expected: builds clean.

If `constScan`'s bound proof does not close, replace its body with the
simpler route: the two identity steps make `scanStepWord` the identity, so
`scanSem_eq` reduces the fold to `baseWord (oneAtOf 0) = [true]`; prove
`∀ w, (scanSem … ![w]).length ≤ w.length + 1` by `List.rec` with both cases
closing by `omega` after `rw [scanSem_eq]`. Do not reach for `native_decide`,
which is banned, and do not add a `set_option` to silence a linter.

- [ ] **Step 3: add the index import**

In `GebTests/Mathlib/Computability/Cobham.lean`, between the `Basic` and
`Tree` imports:

```lean
import GebTests.Mathlib.Computability.Cobham.Scan
```

- [ ] **Step 4: run the whole test suite**

Run: `lake test`
Expected: builds clean.

- [ ] **Step 5: commit**

```bash
jj commit GebTests/Mathlib/Computability/Cobham/Scan.lean \
  GebTests/Mathlib/Computability/Cobham.lean \
  -m "test(cobham): mirror the scan combinator"
```

---

### Task 6: rebuilding the recognizer

**Files:**

- Modify: `Geb/Mathlib/Computability/Cobham/Tree.lean`

**Interfaces:**

- Consumes: `Cobham.scanRaw`, `Cobham.scanSem`, `Cobham.scan`,
  `Cobham.scanSem_nil`, `Cobham.scanSem_cons`, `Cobham.wValid_scanRaw` from
  Tasks 2 to 4.
- Produces: no new names. Every existing name keeps its statement;
  `combFalseStepOf` and `combTrueStepOf` change type from `COf 2` to
  `COf 1`.

Everything in this task has been verified in the prototype at full size,
including the two `cons` proofs, which were the branch's last open question:
both steps rewritten to arity one elaborate with `by decide` admissibility,
and both `cons` lemmas close in exactly the form given below. What the
kernel must decide by `decide` was verified too:
admissibility of both rewritten steps, of the assembled node, and of the
recognizer over it; `smashFreeBool` over the node and over the recognizer;
and every `rfl` the existing test mirror asserts.

- [ ] **Step 1: add the import**

Change the import block to:

```lean
public import Geb.Mathlib.Computability.Cobham.Basic
public import Geb.Mathlib.Computability.Cobham.Scan
public import Geb.Mathlib.Data.Tree.Preorder
```

- [ ] **Step 2: drop the leaf step to arity one**

Replace `combFalseStepRaw` (currently lines 276-286) and `combFalseStep`
(288-299) and `combFalseStepOf` (301-302) with:

```lean
/-- The leaf step: push a level onto a live value, whose head is `true`, and
return the failure flag on a value that is empty or has head `false`. Of
arity one, the state being the sole argument a fold's step reads. -/
@[expose] def combFalseStepRaw : sig.toPFunctor.W :=
  WType.mk (.comp 1 4) fun d ↦
    match d with
    | .inl () => condRaw
    | .inr i =>
      ![WType.mk (.proj 1 0) Fin.elim0, falseAtRaw 1,
        WType.mk (.comp 1 1) (fun e ↦
          match e with
          | .inl () => incRaw
          | .inr _ => WType.mk (.proj 1 0) Fin.elim0),
        falseAtRaw 1] i

/-- The leaf step as an expression of arity one. -/
@[expose] def combFalseStep : C :=
  ⟨⟨combFalseStepRaw, by decide⟩,
    ⟨trivial, fun d ↦ match d with
      | .inl () => cond.1.2
      | .inr 0 => ⟨trivial, fun c ↦ c.elim0⟩
      | .inr 1 => (falseAt 1).2
      | .inr 2 =>
        ⟨trivial, fun e ↦ match e with
          | .inl () => inc.2
          | .inr _ => ⟨trivial, fun c ↦ c.elim0⟩⟩
      | .inr 3 => (falseAt 1).2⟩⟩

/-- `combFalseStep` at its declared arity. -/
@[expose] def combFalseStepOf : COf 1 := ⟨combFalseStep, rfl⟩
```

- [ ] **Step 3: drop the node step to arity one**

Replace `combTrueStepRaw` (306-323), `combTrueStep` (326-342) and
`combTrueStepOf` (344-345) with:

```lean
/-- The node step: pop a level when at least two remain, and return the
failure flag otherwise. An existing failure propagates, its guard being
empty. Of arity one, as `combFalseStep`. -/
@[expose] def combTrueStepRaw : sig.toPFunctor.W :=
  WType.mk (.comp 1 4) fun d ↦
    match d with
    | .inl () => condRaw
    | .inr i =>
      ![WType.mk (.comp 1 1) (fun e ↦
          match e with
          | .inl () => predPredRaw
          | .inr _ => WType.mk (.proj 1 0) Fin.elim0),
        falseAtRaw 1,
        WType.mk (.comp 1 1) (fun e ↦
          match e with
          | .inl () => predRaw
          | .inr _ => WType.mk (.proj 1 0) Fin.elim0),
        WType.mk (.comp 1 1) (fun e ↦
          match e with
          | .inl () => predRaw
          | .inr _ => WType.mk (.proj 1 0) Fin.elim0)] i

/-- The node step as an expression of arity one. -/
@[expose] def combTrueStep : C :=
  ⟨⟨combTrueStepRaw, by decide⟩,
    ⟨trivial, fun d ↦ match d with
      | .inl () => cond.1.2
      | .inr 0 =>
        ⟨trivial, fun e ↦ match e with
          | .inl () => predPred.2
          | .inr _ => ⟨trivial, fun c ↦ c.elim0⟩⟩
      | .inr 1 => (falseAt 1).2
      | .inr 2 =>
        ⟨trivial, fun e ↦ match e with
          | .inl () => pred.1.2
          | .inr _ => ⟨trivial, fun c ↦ c.elim0⟩⟩
      | .inr 3 =>
        ⟨trivial, fun e ↦ match e with
          | .inl () => pred.1.2
          | .inr _ => ⟨trivial, fun c ↦ c.elim0⟩⟩⟩⟩

/-- `combTrueStep` at its declared arity. -/
@[expose] def combTrueStepOf : COf 1 := ⟨combTrueStep, rfl⟩
```

- [ ] **Step 4: build**

Run: `lake build Geb.Mathlib.Computability.Cobham.Tree`
Expected: errors downstream at `combRaw`, `combSem_cons_false` and
`combSem_cons_true`, which the next steps fix. The two step definitions
themselves must elaborate; if `by decide` fails on either, stop and report —
that contradicts a verified result.

- [ ] **Step 5: rebuild the scan on the combinator**

Replace `combRaw` (350-352) with:

```lean
/-- The raw tree of the scan, as a scanner: base `[true]`, the empty
bitstring having depth zero and satisfying `ok`; growth one, the value being
never longer than the recursion variable by more than one bit. -/
@[expose] def combRaw : sig.toPFunctor.W :=
  scanRaw (oneAtRaw 0) combFalseStepRaw combTrueStepRaw 1
```

Replace `combSem` (357-358) with the definition together with its equation
lemma. The lemma is not optional: `combSem` is a `def` and carries no
equation lemma of its own, so `rw [combSem]` fails and the `cons` proofs
below have nothing to rewrite by.

```lean
/-- The scan's meaning at its arity, as the scanner's. `Cobham.eval` asks
only for admissibility as a `sig`-tree, so the scan is characterized before
the expression carrying its recursion bound exists. -/
@[expose] def combSem : Sem 1 :=
  scanSem (oneAtOf 0) combFalseStepOf combTrueStepOf 1

/-- The scan is the scanner at its two steps. Stated because a `def` carries
no equation lemma, and the `cons` lemmas rewrite by this one. -/
theorem combSem_def :
    combSem = scanSem (oneAtOf 0) combFalseStepOf combTrueStepOf 1 := rfl
```

- [ ] **Step 6: re-prove the two `cons` lemmas**

Replace the proofs of `combSem_cons_false` (365-374) and
`combSem_cons_true` (379-391), keeping both statements exactly as they
stand, with:

```lean
theorem combSem_cons_false (v : List Bool) :
    combSem ![false :: v] =
      (match combSem ![v] with
       | [] => [false]
       | true :: _ => true :: combSem ![v]
       | false :: _ => [false]) := by
  rw [combSem_def, scanSem_cons]
  change stepWord combFalseStepOf (scanSem (oneAtOf 0) combFalseStepOf
    combTrueStepOf 1 ![v]) = _
  generalize scanSem (oneAtOf 0) combFalseStepOf combTrueStepOf 1 ![v] = r
  match r with
  | [] | true :: _ | false :: _ => rfl

theorem combSem_cons_true (v : List Bool) :
    combSem ![true :: v] =
      (match (combSem ![v]).tail.tail with
       | [] => [false]
       | true :: _ => (combSem ![v]).tail
       | false :: _ => (combSem ![v]).tail) := by
  rw [combSem_def, scanSem_cons]
  change stepWord combTrueStepOf (scanSem (oneAtOf 0) combFalseStepOf
    combTrueStepOf 1 ![v]) = _
  generalize scanSem (oneAtOf 0) combFalseStepOf combTrueStepOf 1 ![v] = r
  match r with
  | [] => rfl
  | [c] => cases c <;> rfl
  | c :: d :: w =>
    cases c <;> cases d <;> (match w with | [] | true :: _ | false :: _ => rfl)
```

If the `change` does not land, `scanStepWord` has not reduced at the literal
bit: `scanStepWord step₀ step₁ false r` is `stepWord step₀ r` by `if_neg`,
and `simp only [scanStepWord]` before the `change` exposes it.

- [ ] **Step 7: build**

Run: `lake build Geb.Mathlib.Computability.Cobham.Tree`
Expected: the remaining error is at `comb`, which the next step fixes.

- [ ] **Step 8: rebuild the expression on the smart constructor**

Replace `comb` (435-453) with:

```lean
/-- The stack depth and the underflow verdict of a bitstring in one value.
Its recursion respects the bound because the value is `[false]`, of length
one, or the depth in unary offset by one, and the depth never exceeds the
word length (`BinTree.depth_le_length`). -/
@[expose] def comb : C :=
  scan (oneAtOf 0) combFalseStepOf combTrueStepOf 1 (by
    intro u
    rw [combSem_eq]
    cases BinTree.ok u
    · exact Nat.le_add_left 1 u.length
    · rw [if_pos rfl, List.length_replicate]
      exact Nat.succ_le_succ (BinTree.depth_le_length u))
```

Note that `comb` now sits after `combSem_eq` in the file, its bound
consuming that characterization; move the definition below `combSem_eq` if
it is not already there, keeping `combOf`, `combSem_eq_eval` and everything
after them in their present order.

- [ ] **Step 9: build**

Run: `lake build Geb.Mathlib.Computability.Cobham.Tree`
Expected: builds clean.

- [ ] **Step 10: correct the falsified documentation**

Each of these currently says something the rebuild makes false.

- Module docstring, the `## Main definitions` bullet for the two steps
  (49-50): "of arity two" becomes "of arity one".
- Module docstring (24-25): "which the successor `S₁` expresses as a term of
  arity one" becomes "which the scanner's bound child expresses at growth
  one".
- Module docstring (102-111): the sentence "both being the same transport
  along `fst_eval`" no longer holds, `combSem` now being a `scanSem`;
  replace with a sentence stating that `combSem` is the scanner's meaning
  and `combSem_eq_eval` reads it back through `C.eval`.
- Module docstring (120-127): the two `cons` lemmas are no longer proved by
  rewriting to the step's own application; they are corollaries of
  `scanSem_cons`. Rewrite the sentence accordingly.
- Module docstring (141-144): `isTreeSem_apply` is said to be proved "as
  `combSem_cons_false` and `combSem_cons_true` are"; that analogy is now
  false. State `isTreeSem_apply`'s own method without the comparison.
- `combFalseStep`'s and `combTrueStep`'s docstrings (288, 325): "as an
  expression of arity two" becomes "arity one" — already done in Steps 2
  and 3; verify.
- `combFalseStepRaw`'s docstring (274-275): "The recursive value is the
  second of the step's two arguments" becomes a statement that the state is
  the step's sole argument — already done in Step 2; verify.
- `combRaw`'s and `comb`'s docstrings (348-349, 433-434): the bound child
  described as `S₁` — already done in Steps 5 and 8; verify.

- [ ] **Step 11: build, test, lint**

Run: `lake build`
Expected: builds clean.

Run: `lake test`
Expected: builds clean. This is where the existing mirror's ten `rfl`
theorems — six on `combSem`, four on `isTreeSem` — are checked against the
rebuild.

Run: `lake lint`
Expected: no failures.

- [ ] **Step 12: commit**

```bash
jj commit Geb/Mathlib/Computability/Cobham/Tree.lean \
  -m "refactor(cobham): rebuild the recognizer's scan on the combinator"
```

---

### Task 7: the documentation index

**Files:**

- Modify: `docs/index.md`

- [ ] **Step 1: add the entry for the new module**

Insert between the `Cobham/Basic.lean` entry and the `Cobham/Tree.lean`
entry, matching their form:

```text
- `Geb/Mathlib/Computability/Cobham/Scan.lean` — the scan combinator: a
  right-to-left fold over a bitstring whose state is a bitstring, as a
  `boundedRec` node of `C`. `scanRaw` assembles the node from a base, two
  steps of arity one lifted into `evalRec`'s step shape by `liftRaw`, and
  the bound child `boundRaw` prepending `growth` bits; `wValid_scanRaw`
  gives its admissibility from its components' own together with their
  index equations. `scanSem` is the meaning read at the raw tree, before
  any recursion bound exists, and `scanSem_eq` identifies it with
  `List.foldr` of `scanStepWord` from `baseWord`. `scan` takes a length
  bound on that meaning and produces the member of `C`, with
  `scanSem_eq_eval` reading the meaning back through `C.eval`. Depends on
  `Geb.Mathlib.Computability.Cobham.Basic`. `Classical.choice`-free.
```

- [ ] **Step 2: update the two entries the branch changes**

In the `Cobham/Basic.lean` entry, add `transport_transport` to the
declarations it names.

In the `Cobham/Tree.lean` entry, change its dependency sentence to name
`Geb.Mathlib.Computability.Cobham.Scan` alongside
`Geb.Mathlib.Computability.Cobham.Basic` and
`Geb.Mathlib.Data.Tree.Preorder`, and state that `comb` is the scanner at
the leaf and node steps.

- [ ] **Step 3: lint the Markdown**

Run: `markdownlint-cli2 '**/*.md'`
Expected: `Summary: 0 issues`.

Run: `doctoc --dryrun --update-only .`
Expected: `Everything is OK.`

Run: `./scripts/check-md-links.sh`
Expected: all link targets resolve.

- [ ] **Step 4: commit**

```bash
jj commit docs/index.md \
  -m "doc(cobham): catalogue the scan combinator"
```

---

### Task 8: the roadmap and the handoff

**Files:**

- Modify: `TODO.md` § Extensions of the tree recognizers
- Modify: `docs/superpowers/plans/2026-08-10-ranked-tree-b2-b5-handoff.md`

Both are transient documents that describe B2 as pending and describe it
wrongly once this branch lands. CONTRIBUTING.md § Concern shape requires
that no active branch present superseded decisions as current. The handoff
stays in the tree, being still needed for B3 to B5; it is not this branch's
to remove.

- [ ] **Step 1: rewrite the roadmap entry**

In `TODO.md` § Extensions of the tree recognizers:

- Replace the `**B2**, depending on B1:` bullet with a `**B2 is done.**`
  bullet in the form the `**B1 is done.**` bullet above it uses: name what
  `Geb/Mathlib/Computability/Cobham/Scan.lean` gives — the combinator, its
  fold characterization, and the recognizer's scan rebuilt on it — and
  point at `docs/index.md`, written as a repo-relative link since TODO.md
  sits at the repository root.
- Add a `**B6**, depending on B2 and B1:` bullet for the generic ranked
  recognizer, carrying the two constraints the spec's § Out of scope
  records: the layout of `RankedAlphabet.Scan` as a bitstring is undecided,
  and the step must dispatch on `2 ^ width` block values against
  `RankedAlphabet.arOf`, so the dispatch is built by recursion on `width`
  rather than written out.
- Remove the section's opening count of branches ("Five branches over …")
  rather than correcting it, and the "part of none of the five" later in
  the section, per CONTRIBUTING.md § Document only the persistent. Name the
  members or state the property they share.
- Remove from the B2 text the two sentences this branch resolves — the
  length bound stated over the fold with `growth = 0` needing its own
  clause, and the `COf 1`-not-`COf 2` reading of `evalRec`'s step — and the
  claim that `combFalseStep` and `combTrueStep` "both reference slot 1
  only", which the arity-one rewrite falsifies.
- Remove the name `Scanner` from the B2 text and from the deferred
  Bellantoni-Cook port; no structure of that name is built.
- Leave the B3, B4 and B5 dependency lines against B2 in place.

- [ ] **Step 2: correct the handoff**

In `docs/superpowers/plans/2026-08-10-ranked-tree-b2-b5-handoff.md`:

- Replace § B2 with a pointer to the delivered module and to
  `docs/index.md`, dropping its `Scanner` interface prescription, its
  "a length bound cannot name `stepSem`/`baseSem` as fields" note, and its
  `growth = 0` clause — all three are now realized code.
- Remove the two counts, "part of any of the five" and "part of none of the
  five", as in Step 1.
- Remove the name `Scanner` from its deferral list.
- Regenerate its table of contents if any heading changed.

- [ ] **Step 3: lint the Markdown**

Run: `markdownlint-cli2 '**/*.md'`
Expected: `Summary: 0 issues`.

Run: `doctoc --update-only .` then `doctoc --dryrun --update-only .`
Expected: `Everything is OK.`

Run: `./scripts/check-md-links.sh`
Expected: all link targets resolve.

- [ ] **Step 4: commit**

```bash
jj commit TODO.md docs/superpowers/plans/2026-08-10-ranked-tree-b2-b5-handoff.md \
  -m "doc(cobham): record the scan combinator in the roadmap"
```

---

### Task 9: removing the prototype and verifying the branch

**Files:**

- Delete: `Geb/Internal/ScanSpike.lean`

The prototype exists only as evidence for the spec. Its content is now
`Geb/Mathlib/Computability/Cobham/Scan.lean` and its checks are the test
mirror; leaving it would be a second copy of the combinator under a name no
consumer uses, which CONTRIBUTING.md § Code is cost rules out.

- [ ] **Step 1: confirm nothing imports it**

Run: `grep -rn "ScanSpike" --include=*.lean --include=*.md --include=*.toml .`
Expected: matches only in `Geb/Internal/ScanSpike.lean` itself.

- [ ] **Step 2: delete it**

```bash
rm Geb/Internal/ScanSpike.lean
```

- [ ] **Step 3: full verification**

Run: `lake build`
Expected: builds clean.

Run: `lake test`
Expected: builds clean.

Run: `lake lint`
Expected: no failures.

Run: `./scripts/pre-push.sh`
Expected: every check passes. This runs the import linter, the Markdown
checks, the TOC check and `lake shake` in addition to the above.

- [ ] **Step 4: commit**

```bash
jj commit Geb/Internal/ScanSpike.lean \
  -m "chore(cobham): remove the scan prototype"
```

- [ ] **Step 5: report, do not push**

Report the branch's commits and the output of `./scripts/pre-push.sh` to
the user. Do not push: AGENTS.md § No `jj git push` without user
line-by-line review binds here, and the spec and this plan are removed in
the branch's final commits only after that review, per CONTRIBUTING.md
§ Concern shape.
