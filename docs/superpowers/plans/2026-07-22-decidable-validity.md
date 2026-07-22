# Decidable validity predicates implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task. Steps
> use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Supply `Decidable` instances for the six term-validity
predicates of the slice and presheaf polynomial functors, in the finitary
case, with proofs that the procedures decide them.

**Architecture:** Finiteness is carried as `FinEnum`, never `Fintype`,
because `Fintype`-routed decidability depends on `Classical.choice`.
Three choice-free `Decidable` instances over `FinEnum` sit in a new
`Data/FinEnum.lean`; a paramorphism and decidable equality are added to
`Data/W/Basic.lean`; `PFunctor.Finitary` is an `abbrev` for the finitary
binder; and two `Decidable.lean` modules specialize the slice and presheaf
predicates. The two recursive predicates are decided by `WType.elim` /
`WType.para` folds into `Bool`-carrying types, related to the `Prop` by a
single `WType.rec` proof each.

**Tech Stack:** Lean 4 (toolchain pinned by `lean-toolchain`), mathlib
(pinned in `lake-manifest.json`), `lake` for build and test,
`markdownlint-cli2` and `doctoc` for Markdown.

**Spec:** `docs/superpowers/specs/2026-07-22-decidable-validity-design.md`

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Global Constraints](#global-constraints)
- [File structure](#file-structure)
  - [Task 1: Spike the hereditary-naturality correctness proof](#task-1-spike-the-hereditary-naturality-correctness-proof)
  - [Task 2: `Geb/Mathlib/Data/FinEnum.lean`](#task-2-gebmathlibdatafinenumlean)
  - [Task 3: `WType.para`](#task-3-wtypepara)
  - [Task 4: `DecidableEq (WType β)`](#task-4-decidableeq-wtype-%CE%B2)
  - [Task 5: `PFunctor.Finitary`](#task-5-pfunctorfinitary)
  - [Task 6: Slice fiber and compatibility instances](#task-6-slice-fiber-and-compatibility-instances)
  - [Task 7: The `WValid` checker](#task-7-the-wvalid-checker)
  - [Task 8: The `IsNatural` instance](#task-8-the-isnatural-instance)
  - [Task 9: The hereditary-naturality checker](#task-9-the-hereditary-naturality-checker)
  - [Task 10: The hereditary-naturality fixture and reduction test](#task-10-the-hereditary-naturality-fixture-and-reduction-test)
  - [Task 11: Persistent documentation](#task-11-persistent-documentation)
  - [Task 12: Close the branch](#task-12-close-the-branch)

<!-- END doctoc -->

## Global Constraints

- **Axioms.** Every declaration in `Geb/` and `GebTests/` must depend
  only on `{propext, Quot.sound}`. No module is added to
  `GebMeta.classicalAllowedModules`. Verify with `#print axioms` while
  developing and `lake lint` before each commit.
- **No `Fintype`, `Finset`, or `FinCategory`** in any signature or body.
  `Lean.collectAxioms` traverses a declaration's type, so a signature
  mentioning `Fintype` carries `Classical.choice` however it is proved.
- **Pin every `Decidable` argument** that could resolve through
  `Fintype`. Left to inference, resolution takes mathlib's
  `[FinEnum α] : Fintype α` bridge.
- **No `noncomputable`.** No self-recursive `def`, no `termination_by`,
  no `induction` tactic. Recursion goes through `WType.elim`,
  `WType.para`, `WType.rec`, or `SlicePFunctor.W.induction`.
- **Module system.** Every `.lean` file opens with the copyright block
  then `module`. `@[expose]` on an `abbrev` or an `instance` is an
  error. An `@[expose]`d body may name only constants from
  `public import`s, and may not name a `private` declaration.
- **`@[expose]` set:** `para`, `paraStep`, `beq`, `wValidStep`,
  `wValidData`, `wValidBool`, `wRestrTreeRaw`,
  `isHereditarilyNaturalBoolCore`. Not the `abbrev`, not the instances.
- **Docstrings.** Module docstring mandatory after imports with the
  section list from `docs/rules/lean-coding.md`; `/-- … -/` mandatory on
  every `def`, `abbrev`, `instance`, and theorem of public interest.
- **Line length 100, indent 2, Unicode notation** per mathlib style.
- **Subtree imports.** `Geb/Mathlib/` may import only `Mathlib.*` and
  `Geb.Mathlib.*`; no `Geb.Mathlib.` prefix outside `import` lines.
- **Commit messages:** `<type>(<scope>): <imperative subject>`, no
  capital, no trailing period, type from
  `feat|fix|doc|style|refactor|test|chore|perf|ci`.
- **Markdown:** every `.md` touched passes `markdownlint-cli2` and
  `doctoc --update-only`.
- **No `git` mutations.** Use `jj` for all state-mutating VCS operations.
  To delete a tracked, non-ignored file, `rm` it — jj's working-copy
  snapshot records the deletion. `jj file untrack` is only for ignored
  paths and errors on a tracked file.
- **Test fixtures must be reducible.** A plain `def` fixture does not
  unfold at `instances` transparency, so a decidable instance stated over
  a general functor will not unify its projections (`F.A`, `F.B a`) with
  the fixture's concrete types, and `decide` gets stuck (its instance
  contains `sorryAx`). Declare every fixture polynomial functor as an
  `abbrev`, and give each `FinEnum`'s `decEq` field explicitly with a
  type ascription (`decEq := (inferInstance : DecidableEq Unit)`), not a
  bare `inferInstance` — the bare form asks for `DecidableEq (F.B a)`,
  which does not reduce.
- **Keep W-tree equations at the `WType` head.** `DecidableEq (WType β)`
  does not fire on `PFunctor.W` values: `PFunctor.W P` is a semireducible
  `def` wrapping `WType P.B`, and resolution does not unfold it to the
  `WType` head, so a mixed equation (`WType β` on one side, `PFunctor.W`
  on the other) decides on neither. `wRestrTreeRaw` therefore returns
  `WType β`, matching the `para` carrier, so the hereditary checker's
  tree equation is same-headed (Task 9). No `DecidableEq (PFunctor.W P)`
  instance is introduced.
- **Decidability through the `PresheafPFunctor` diamond.** A
  `decide (∀ b : Direction …)`
  does not elaborate over a `PresheafPFunctor`: instance synthesis cannot
  resolve `decidableForallDirection` through the `SliceDomPFunctor`
  diamond projection. The hereditary checker is therefore a classless core
  taking every finiteness and decidability datum explicitly, with a thin
  `instance` wrapper (Task 9). The slice checker and `IsNatural` are
  unaffected — no diamond — and keep the `decide (∀ …)` form.

## File structure

| File | Responsibility |
| --- | --- |
| `Geb/Mathlib/Data/FinEnum.lean` | three choice-free `Decidable` instances over `FinEnum` |
| `Geb/Mathlib/Data/W/Basic.lean` | existing fold lemmas, plus `para` and `DecidableEq (WType β)` |
| `Geb/Mathlib/Data/PFunctor/Univariate/Finitary.lean` | the `Finitary` abbrev |
| `Geb/Mathlib/Data/PFunctor/Slice/Decidable.lean` | slice instances and the `WValid` checker |
| `Geb/Mathlib/Data/PFunctor/Presheaf/Decidable.lean` | presheaf instances and the hereditary checker |
| `GebTests/Mathlib/Data/FinEnum.lean` | reduction tests for the three instances |
| `GebTests/Mathlib/Data/W/Basic.lean` | existing, plus `para` and `beq` tests |
| `GebTests/Mathlib/Data/PFunctor/Univariate/Finitary.lean` | resolution tests |
| `GebTests/Mathlib/Data/PFunctor/Slice/Decidable.lean` | slice fixtures and reduction tests |
| `GebTests/Mathlib/Data/PFunctor/Presheaf/Decidable.lean` | presheaf fixtures and reduction tests |
| `Geb/Mathlib/Data.lean`, `.../Data/PFunctor/{Slice,Presheaf,Univariate}.lean`, and the `GebTests/` mirrors | index entries |
| `docs/index.md`, `TODO.md`, `docs/references.bib` | persistent documentation |

---

### Task 1: Spike the hereditary-naturality correctness proof

The spec records `isHereditarilyNaturalBoolCore_eq_true_iff` as the
branch's one unverified obligation and gates the branch on it. This task
proves it
in a single throwaway file, before any polished module is written, so a
failure costs one task rather than eight.

**Files:**

- Create then remove: `Geb/Internal/Spike.lean`

**Interfaces:**

- Consumes: nothing.
- Produces: knowledge only. If the proof closes, Tasks 2–12 proceed
  unchanged. If it does not, stop and report — the spec names a
  restructuring fallback (a raw-tree predicate proved equivalent
  separately) that reopens the module's design, and that is the user's
  decision.

- [ ] **Step 1: Create the spike file with everything inlined**

Write `Geb/Internal/Spike.lean` containing, in one `module` with
`public section`: the three `FinEnum` instances of Task 2, `para` and
`para_mk` of Task 3, `beq` / `beq_eq_true_iff` / `WType.instDecidableEq`
of Task 4, the `Finitary` abbrev of Task 5, and then `wRestrTreeRaw`,
`wRestrTree_val`, `isHereditarilyNaturalBoolCore` and the target theorem
of Task 9. Copy the verified code from those tasks verbatim; the only new
content is the proof of the `iff`.

The definitions `wRestrTreeRaw`, `isHereditarilyNaturalBoolCore`, and the
wrapper are already verified to elaborate at `{Quot.sound}` (§ Task 9 and
the design's § Verification performed): the classless-core formulation is
what makes them do so through the diamond. This task's sole open question
is whether the correctness `iff` closes.

The target statement:

```lean
theorem isHereditarilyNaturalBoolCore_eq_true_iff {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    (decI : DecidableEq I) (feI : FinEnum I) (feHom : ∀ i i' : I, FinEnum (i' ⟶ i))
    (feB : ∀ a, FinEnum (F.toPFunctor.B a)) (decEqW : DecidableEq (WType F.toPFunctor.B))
    (z : F.toSlicePFunctor.W) :
    F.isHereditarilyNaturalBoolCore decI feI feHom feB decEqW z.1 = true ↔
      F.IsHereditarilyNatural z
```

- [ ] **Step 2: Prove it**

Drive the recursion with `SlicePFunctor.W.induction`, rewrite the
right-hand side one level with `F.isHereditarilyNatural_mk`, and the
left-hand side with `WType.para_mk` applied at
`WType.mk x.1.1 (Subtype.val ∘ x.1.2)` — the underlying tree of
`SlicePFunctor.W.mk x`, per `Slice/W.lean`'s `mk`. Obligations:

1. relate the `List.all` enumerations to the `∀` quantifiers, by
   `FinEnum.mem_toList` and `List.all_eq_true`;
2. the two `isTrue` branches are the ones taken on a valid node, their
   witnesses being `(F.compatible_iff _ _ _).mp x.2 b'` and the direction
   constraint; the `isFalse` branches are unreachable there, by
   proof irrelevance of the witnesses;
3. the tree equality decided by `decEqW` matches the subtype equality of
   `IsHereditarilyNatural`, by `decide_eq_true_iff` (the core tests it with
   the explicit `(decEqW A B).decide`, not `beq`), `wRestrTree_val`, and
   `Subtype.ext_iff`;
4. the children's conjunct is the induction hypothesis.

If a step resists, use `/lean4:prove` on that step alone. Do not `sorry`
past it; the point of this task is to learn whether the route closes.

- [ ] **Step 3: Check the axioms**

Run:

```bash
lake build Geb.Internal.Spike
```

Then add `#print axioms isHereditarilyNaturalBoolCore_eq_true_iff` and
rebuild. Expected: `[propext, Quot.sound]`. If `Classical.choice`
appears, find the tainted ingredient with `#print axioms` on each lemma
used and replace it.

- [ ] **Step 4: Record the proof and remove the spike**

Copy the completed proof into this plan's Task 9, Step 3, replacing the
`sorry` skeleton there. Then remove the file — jj snapshots the deletion,
no `untrack` needed (the file was never committed, so there is nothing to
untrack):

```bash
rm Geb/Internal/Spike.lean
```

- [ ] **Step 5: Report the gate result**

State whether the proof closed, and paste the axiom line. Do not commit
anything in this task — its deliverable is the proof text, now carried in
Task 9.

---

### Task 2: `Geb/Mathlib/Data/FinEnum.lean`

**Files:**

- Create: `Geb/Mathlib/Data/FinEnum.lean`
- Create: `GebTests/Mathlib/Data/FinEnum.lean`
- Modify: `Geb/Mathlib/Data.lean`, `GebTests/Mathlib/Data.lean` (index
  entries)

**Interfaces:**

- Consumes: nothing.
- Produces: `FinEnum.decidableForallFinEnum`,
  `FinEnum.decidableForallSubtype`, `FinEnum.decidablePiFinEnum`, all
  instances at default priority.

- [ ] **Step 1: Write the failing test**

Create `GebTests/Mathlib/Data/FinEnum.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.Data.FinEnum

/-!
# Tests for the choice-free `FinEnum` decidability instances

Each instance is exercised by a closed `decide`, in both directions, so
that a failure to reduce is caught. Verdicts are named `def`s rather than
bare `example`s: an `example` adds no constant to the environment, so the
axiom linter cannot see it.

## Tags

FinEnum, decidability, test
-/

set_option linter.privateModule false

/-- A choice-free `FinEnum Bool`, built from the structure fields. The
`Equiv` laws are proved by case analysis: `decide` would route through
`Bool`'s `Fintype` instance and reintroduce `Classical.choice`. -/
instance finEnumBool : FinEnum Bool where
  card := 2
  equiv :=
    { toFun := fun b ↦ if b then 1 else 0
      invFun := fun i ↦ i == 1
      left_inv := Bool.rec rfl rfl
      right_inv := Fin.cases rfl (Fin.cases rfl (fun i ↦ i.elim0)) }
  decEq := inferInstance

/-- A bounded `∀` that holds. -/
def forallTrue : Bool := decide (∀ b : Bool, b || !b)

/-- A bounded `∀` that fails. -/
def forallFalse : Bool := decide (∀ b : Bool, b)

/-- A `∀` over a decidable subtype that holds. -/
def subtypeTrue : Bool := decide (∀ x : { b : Bool // b = true }, x.1 = true)

/-- A `∀` over a decidable subtype that fails. -/
def subtypeFalse : Bool := decide (∀ x : { b : Bool // b = true }, x.1 = false)

/-- A function equality that holds. -/
def funTrue : Bool := decide ((fun b : Bool ↦ !b) = fun b : Bool ↦ !b)

/-- A function equality that fails. -/
def funFalse : Bool := decide ((fun b : Bool ↦ !b) = fun b : Bool ↦ b)

example : forallTrue = true := by decide
example : forallFalse = false := by decide
example : subtypeTrue = true := by decide
example : subtypeFalse = false := by decide
example : funTrue = true := by decide
example : funFalse = false := by decide
```

- [ ] **Step 2: Run the test to verify it fails**

Add `import GebTests.Mathlib.Data.FinEnum` to `GebTests/Mathlib/Data.lean`,
then run:

```bash
lake build GebTests.Mathlib.Data.FinEnum
```

Expected: FAIL, `unknown module prefix 'Geb.Mathlib.Data.FinEnum'`.

- [ ] **Step 3: Write the implementation**

Create `Geb/Mathlib/Data/FinEnum.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Mathlib.Data.FinEnum

/-!
# Choice-free decidability over a `FinEnum`

mathlib decides a bounded `∀` through `Fintype`, whose instance depends
on `Classical.choice`. `FinEnum` carries a `List` enumeration, and
deciding a quantifier by `List.decidableBAll` over `FinEnum.toList` is
choice-free. These three instances take that route.

The `Decidable` argument of each `decidable_of_iff` is supplied
explicitly. Left to inference, resolution reaches
`Fintype.decidableForallFintype` through mathlib's
`[FinEnum α] : Fintype α` bridge and the instance, while still
typechecking, acquires `Classical.choice`.

`decidableForallSubtype` decides a quantifier over a decidable subtype
without forming a `FinEnum` on the subtype: mathlib's
`FinEnum.Subtype.finEnum` is derived through `FinEnum.ofList` and is
choice-dependent.

## Main definitions

* `FinEnum.decidableForallFinEnum` — a bounded `∀` over the type.
* `FinEnum.decidableForallSubtype` — a bounded `∀` over a decidable
  subtype of it.
* `FinEnum.decidablePiFinEnum` — equality of functions out of it.

## Tags

FinEnum, decidability, constructive
-/

public section

universe u v

namespace FinEnum

/-- A universally quantified statement over a finitely enumerable type is
decidable. The analogue of `Fintype.decidableForallFintype`, routed
through `List.decidableBAll` so as not to depend on `Classical.choice`. -/
@[instance_reducible]
instance decidableForallFinEnum {α : Type u} {p : α → Prop} [DecidablePred p]
    [FinEnum α] : Decidable (∀ x, p x) :=
  @decidable_of_iff (∀ x, p x) (∀ x ∈ FinEnum.toList α, p x)
    ⟨fun h x ↦ h x (FinEnum.mem_toList x), fun h x _ ↦ h x⟩
    (List.decidableBAll p (FinEnum.toList α))

/-- A universally quantified statement over a decidable subtype of a
finitely enumerable type is decidable. Ranges over the ambient type's
enumeration and discharges the subtype's predicate inside the body, so no
`FinEnum` on the subtype is formed. -/
@[instance_reducible]
instance decidableForallSubtype {α : Type u} {p : α → Prop} [DecidablePred p]
    {q : Subtype p → Prop} [DecidablePred q] [FinEnum α] :
    Decidable (∀ x : Subtype p, q x) :=
  @decidable_of_iff (∀ x : Subtype p, q x) (∀ a ∈ FinEnum.toList α, ∀ h : p a, q ⟨a, h⟩)
    ⟨fun H x ↦ H x.1 (FinEnum.mem_toList x.1) x.2, fun H x _ h ↦ H ⟨x, h⟩⟩
    (List.decidableBAll _ (FinEnum.toList α))

/-- Equality of functions out of a finitely enumerable type is decidable.
The analogue of `Fintype.decidablePiFintype`, and weaker in its
hypothesis on the codomain: `List.Pi.finEnum` would require the codomain
finitely enumerable, where this needs only decidable equality. -/
@[instance_reducible]
instance decidablePiFinEnum {α : Type u} {Y : Type v} [DecidableEq Y] [FinEnum α] :
    DecidableEq (α → Y) :=
  fun f g ↦ @decidable_of_iff (f = g) (∀ x, f x = g x) funext_iff.symm
    (decidableForallFinEnum)

end FinEnum
```

Add `import Geb.Mathlib.Data.FinEnum` to `Geb/Mathlib/Data.lean`.

- [ ] **Step 4: Run the test to verify it passes**

```bash
lake build GebTests.Mathlib.Data.FinEnum
```

Expected: PASS, no errors.

- [ ] **Step 5: Verify the axioms**

Append to the test file, build, read the output, then remove the lines:

```lean
#print axioms FinEnum.decidableForallFinEnum
#print axioms FinEnum.decidableForallSubtype
#print axioms FinEnum.decidablePiFinEnum
#print axioms forallTrue
```

Expected: each `depends on axioms: [propext, Quot.sound]` or fewer. If
`Classical.choice` appears, the `@`-pin has been lost.

- [ ] **Step 6: Lint and commit**

```bash
lake build && lake test && lake lint
scripts/lint-imports.sh
jj commit -m "feat(finenum): decide bounded quantifiers without choice"
```

---

### Task 3: `WType.para`

**Files:**

- Modify: `Geb/Mathlib/Data/W/Basic.lean`
- Modify: `GebTests/Mathlib/Data/W/Basic.lean`

**Interfaces:**

- Consumes: nothing from this branch.
- Produces:

  ```lean
  WType.paraStep (γ : Type uC) (fγ : (Σ a : α, β a → WType β × γ) → γ) :
      (Σ a : α, β a → WType β × γ) → WType β × γ
  WType.para (γ : Type uC) (fγ : (Σ a : α, β a → WType β × γ) → γ) : WType β → γ
  WType.para_mk (fγ) (a : α) (f : β a → WType β) :
      para γ fγ (mk a f) = fγ ⟨a, fun b ↦ (f b, para γ fγ (f b))⟩
  ```

- [ ] **Step 1: Write the failing test**

Append to `GebTests/Mathlib/Data/W/Basic.lean`:

```lean
/-- Directions of the unary-numeral W-type: `true` branches once,
`false` is a leaf. An `abbrev` so `Nb true` / `Nb false` reduce at
instances transparency. -/
abbrev Nb : Bool → Type := fun b ↦ cond b Unit Empty

/-- Zero, as a `WType`. -/
def zeroW : WType Nb := WType.mk false Empty.elim

/-- Successor, as a `WType`. -/
def succW (w : WType Nb) : WType Nb := WType.mk true fun _ ↦ w

/-- A paramorphism that sees each node's children: the depth of a
numeral, computed by consulting the child subtree's folded depth. -/
def depthPara : WType Nb → Nat :=
  WType.para Nat fun x ↦
    match x with
    | ⟨true, c⟩ => (c ()).2 + 1
    | ⟨false, _⟩ => 0

example : depthPara (succW (succW zeroW)) = 2 := by decide
example : depthPara zeroW = 0 := by decide
```

- [ ] **Step 2: Run the test to verify it fails**

```bash
lake build GebTests.Mathlib.Data.W.Basic
```

Expected: FAIL, `unknown constant 'WType.para'`.

- [ ] **Step 3: Write the implementation**

Insert into `Geb/Mathlib/Data/W/Basic.lean`, before `end WType`:

```lean
/-- The algebra of the paramorphism fold: rebuild the node from the
children's reconstructed subtrees, and apply the step to the node. -/
@[expose] def paraStep {α : Type uA} {β : α → Type uB} (γ : Type uC)
    (fγ : (Σ a : α, β a → WType β × γ) → γ) :
    (Σ a : α, β a → WType β × γ) → WType β × γ :=
  fun x ↦ (mk x.1 fun b ↦ (x.2 b).1, fγ x)

/-- The fold's first component reconstructs its input. -/
private theorem paraStep_fst {α : Type uA} {β : α → Type uB} (γ : Type uC)
    (fγ : (Σ a : α, β a → WType β × γ) → γ) (w : WType β) :
    (elim (WType β × γ) (paraStep γ fγ) w).1 = w :=
  rec (motive := fun w ↦ (elim (WType β × γ) (paraStep γ fγ) w).1 = w)
    (fun a _f ih ↦ congrArg (mk a) (funext ih)) w

/-- The paramorphism of a W-type: a fold whose step sees each node's
children as subtrees together with their folded values. Obtained from
`elim` at the product carrier `WType β × γ`, whose first component
reconstructs the subtree, so no new recursion is introduced.
[Meertens1992] -/
@[expose] def para {α : Type uA} {β : α → Type uB} (γ : Type uC)
    (fγ : (Σ a : α, β a → WType β × γ) → γ) : WType β → γ :=
  fun w ↦ (elim (WType β × γ) (paraStep γ fγ) w).2

/-- The paramorphism's computation rule: it applies the step to the node's
children paired with their own paramorphisms. Unlike `elim_mk` this does
not hold by `rfl`; it is `paraStep_fst` under a `congrArg`. -/
@[simp] theorem para_mk {α : Type uA} {β : α → Type uB} {γ : Type uC}
    (fγ : (Σ a : α, β a → WType β × γ) → γ) (a : α) (f : β a → WType β) :
    para γ fγ (mk a f) = fγ ⟨a, fun b ↦ (f b, para γ fγ (f b))⟩ :=
  congrArg (fun h ↦ fγ ⟨a, h⟩)
    (funext fun b ↦ Prod.ext (paraStep_fst γ fγ (f b)) rfl)
```

Update the module docstring: retitle to cover the paramorphism, and add
`para`, `para_mk` to `## Main definitions` / `## Main statements`, and
`[Meertens1992]` to `## References`.

- [ ] **Step 4: Run the test to verify it passes**

```bash
lake build GebTests.Mathlib.Data.W.Basic
```

Expected: PASS.

- [ ] **Step 5: Commit**

```bash
lake build && lake test && lake lint
jj commit -m "feat(wtype): add the paramorphism and its computation rule"
```

---

### Task 4: `DecidableEq (WType β)`

**Files:**

- Modify: `Geb/Mathlib/Data/W/Basic.lean`
- Modify: `GebTests/Mathlib/Data/W/Basic.lean`

**Interfaces:**

- Consumes: `FinEnum.decidableForallFinEnum` (Task 2).
- Produces:

  ```lean
  WType.beq [DecidableEq α] [∀ a, FinEnum (β a)] : WType β → WType β → Bool
  WType.beq_mk : beq (mk a f) (mk a' f') =
      if h : a = a' then decide (∀ b, beq (f b) (f' (h ▸ b)) = true) else false
  WType.beq_eq_true_iff (s t : WType β) : beq s t = true ↔ s = t
  WType.instDecidableEq : DecidableEq (WType β)
  ```

- [ ] **Step 1: Write the failing test**

Append to `GebTests/Mathlib/Data/W/Basic.lean` (reusing `Nb`, `zeroW`,
`succW` from Task 3):

```lean
/-- A choice-free `FinEnum` for each direction type of `Nb`. Built from
the structure fields; `FinEnum.punit` and `FinEnum.empty` are derived
through `FinEnum.ofList` and depend on `Classical.choice`. `decEq` is
ascribed explicitly: `Nb b` does not reduce enough for a bare
`inferInstance` to find `DecidableEq (Nb b)`. -/
instance finEnumNb : ∀ b, FinEnum (Nb b)
  | true =>
    { card := 1
      equiv := { toFun := fun _ ↦ 0, invFun := fun _ ↦ (),
                 left_inv := fun _ ↦ rfl,
                 right_inv := fun i ↦ Fin.cases rfl (fun i ↦ i.elim0) i }
      decEq := (inferInstance : DecidableEq Unit) }
  | false =>
    { card := 0
      equiv := { toFun := Empty.elim, invFun := Fin.elim0,
                 left_inv := fun x ↦ x.elim, right_inv := fun i ↦ i.elim0 }
      decEq := (inferInstance : DecidableEq Empty) }

/-- Equal numerals compare equal. -/
def beqSame : Bool := decide (succW (succW zeroW) = succW (succW zeroW))

/-- Unequal numerals compare unequal. -/
def beqDiff : Bool := decide (succW zeroW = zeroW)

example : beqSame = true := by decide
example : beqDiff = false := by decide
```

- [ ] **Step 2: Run the test to verify it fails**

```bash
lake build GebTests.Mathlib.Data.W.Basic
```

Expected: FAIL, `failed to synthesize Decidable (succW (succW zeroW) = …)`.

- [ ] **Step 3: Write the implementation**

Insert into `Geb/Mathlib/Data/W/Basic.lean`, before `end WType`:

```lean
/-- Boolean equality of W-trees: compare the shapes, then compare the
children pointwise over the finite direction type. A fold by `elim` at
the carrier `WType β → Bool`, so no recursion is introduced. -/
@[expose] def beq {α : Type uA} {β : α → Type uB} [DecidableEq α]
    [∀ a, FinEnum (β a)] : WType β → WType β → Bool :=
  elim (WType β → Bool) fun x t' ↦
    if h : x.1 = (toSigma t').1 then
      decide (∀ b : β x.1, x.2 b ((toSigma t').2 (h ▸ b)) = true)
    else false

/-- `beq` unfolded on two constructor applications. -/
theorem beq_mk {α : Type uA} {β : α → Type uB} [DecidableEq α]
    [∀ a, FinEnum (β a)] (a : α) (f : β a → WType β) (a' : α)
    (f' : β a' → WType β) :
    beq (mk a f) (mk a' f') =
      if h : a = a' then decide (∀ b : β a, beq (f b) (f' (h ▸ b)) = true) else false :=
  rfl

/-- `beq` decides equality of W-trees. -/
theorem beq_eq_true_iff {α : Type uA} {β : α → Type uB} [DecidableEq α]
    [∀ a, FinEnum (β a)] (s t : WType β) : beq s t = true ↔ s = t :=
  rec (motive := fun s ↦ ∀ t, beq s t = true ↔ s = t)
    (fun a f ih t ↦
      match t with
      | mk a' f' =>
        match ‹DecidableEq α› a a' with
        | isTrue h => by
            subst h
            rw [beq_mk, dif_pos rfl, decide_eq_true_iff]
            exact ⟨fun hb ↦ congrArg (mk a) (funext fun b ↦ (ih b (f' b)).mp (hb b)),
              fun he b ↦ (ih b (f' b)).mpr (congrFun (eq_of_heq (mk.inj he).2) b)⟩
        | isFalse h => by
            rw [beq_mk, dif_neg h]
            exact ⟨fun hb ↦ Bool.noConfusion hb, fun he ↦ absurd (mk.inj he).1 h⟩)
    s t

/-- Equality of W-trees is decidable when shapes have decidable equality
and every direction type is finitely enumerable. mathlib reaches this
only through `Encodable`, which additionally requires the shape and
direction types countable. -/
instance instDecidableEq {α : Type uA} {β : α → Type uB} [DecidableEq α]
    [∀ a, FinEnum (β a)] : DecidableEq (WType β) :=
  fun s t ↦ decidable_of_iff _ (beq_eq_true_iff s t)
```

Add `import Geb.Mathlib.Data.FinEnum` as a `public import` to the file's
import block, and update the module docstring's `## Main definitions` /
`## Main statements`.

- [ ] **Step 4: Run the test to verify it passes**

```bash
lake build GebTests.Mathlib.Data.W.Basic
```

Expected: PASS.

- [ ] **Step 5: Verify the axioms and commit**

Add `#print axioms WType.instDecidableEq` temporarily; expect
`[propext, Quot.sound]`. Then:

```bash
lake build && lake test && lake lint
jj commit -m "feat(wtype): decide equality of finitely branching W-trees"
```

---

### Task 5: `PFunctor.Finitary`

**Files:**

- Create: `Geb/Mathlib/Data/PFunctor/Univariate/Finitary.lean`
- Create: `GebTests/Mathlib/Data/PFunctor/Univariate/Finitary.lean`
- Modify: `Geb/Mathlib/Data/PFunctor/Univariate.lean` and its test mirror

**Interfaces:**

- Consumes: nothing from this branch.
- Produces: `PFunctor.Finitary (P : PFunctor.{uA, uB}) : Type (max uA uB)`,
  a reducible abbreviation for `∀ a : P.A, FinEnum (P.B a)`. Binders are
  written `[F.Finitary]` at every layer.

- [ ] **Step 1: Write the failing test**

Create `GebTests/Mathlib/Data/PFunctor/Univariate/Finitary.lean` with the
copyright block, `module`, `import Geb.Mathlib.Data.PFunctor.Univariate.Finitary`,
a module docstring, `set_option linter.privateModule false`, and:

```lean
/-- `[P.Finitary]` supplies the direction enumeration. -/
def finitaryGivesFinEnum (P : PFunctor.{0, 0}) [P.Finitary] (a : P.A) :
    FinEnum (P.B a) := inferInstance

/-- `[P.Finitary]` supplies decidable equality of directions, through
`FinEnum`'s `decEq` field. -/
def finitaryGivesDecEq (P : PFunctor.{0, 0}) [P.Finitary] (a : P.A) :
    DecidableEq (P.B a) := inferInstance
```

- [ ] **Step 2: Run the test to verify it fails**

```bash
lake build GebTests.Mathlib.Data.PFunctor.Univariate.Finitary
```

Expected: FAIL, `unknown module prefix`.

- [ ] **Step 3: Write the implementation**

Create `Geb/Mathlib/Data/PFunctor/Univariate/Finitary.lean` with the
copyright block, `module`,
`public import Mathlib.Data.PFunctor.Univariate.Basic`,
`public import Mathlib.Data.FinEnum`, a module docstring, `public section`,
`universe uA uB`, and:

```lean
/-- A polynomial functor is finitary when every shape has finitely many
directions. An `abbrev`, so that `[P.Finitary]` is the binder
`[∀ a, FinEnum (P.B a)]` under a name: being reducible it is transparent
to instance resolution, where a `class`'s fields would be inert until
registered. Declared on `PFunctor` so that one binder serves the slice
and presheaf layers through their `toPFunctor` projections. -/
abbrev PFunctor.Finitary (P : PFunctor.{uA, uB}) : Type (max uA uB) :=
  ∀ a : P.A, FinEnum (P.B a)
```

- [ ] **Step 4: Run the test to verify it passes**

```bash
lake build GebTests.Mathlib.Data.PFunctor.Univariate.Finitary
```

Expected: PASS.

- [ ] **Step 5: Commit**

```bash
lake build && lake test && lake lint
scripts/lint-imports.sh
jj commit -m "feat(pfunctor): name the finitary condition on directions"
```

---

### Task 6: Slice fiber and compatibility instances

**Files:**

- Create: `Geb/Mathlib/Data/PFunctor/Slice/Decidable.lean`
- Create: `GebTests/Mathlib/Data/PFunctor/Slice/Decidable.lean`
- Modify: `Geb/Mathlib/Data/PFunctor/Slice.lean` and its test mirror

**Interfaces:**

- Consumes: Tasks 2 and 5.
- Produces: `SliceDomPFunctor.decidableDirectionOver`,
  `SlicePFunctor.decidableShapeOver`,
  `SliceDomPFunctor.decidableForallDirection`,
  `SliceDomPFunctor.decidableCompatible`.

- [ ] **Step 1: Write the failing test**

Create `GebTests/Mathlib/Data/PFunctor/Slice/Decidable.lean` with the
usual preamble and a locally declared fixture — the existing `wSlice` is
module-private and cannot be imported:

```lean
/-- A choice-free `FinEnum Bool` for the shape type. -/
instance finEnumBool : FinEnum Bool where
  card := 2
  equiv :=
    { toFun := fun b ↦ if b then 1 else 0
      invFun := fun i ↦ i == 1
      left_inv := Bool.rec rfl rfl
      right_inv := Fin.cases rfl (Fin.cases rfl (fun i ↦ i.elim0)) }
  decEq := inferInstance

/-- A slice endofunctor over `Bool`: shape `true` branches once, shape
`false` is a leaf. An `abbrev` so its projections unfold at instances
transparency; a plain `def` leaves `decide` stuck. -/
abbrev testSlice : SlicePFunctor.{0, 0, 0, 0} Bool Bool where
  A := Bool
  B := fun a ↦ cond a Unit Empty
  r := fun x ↦ x.1
  q := id

/-- The direction enumeration of `testSlice`, by cases on the shape.
`decEq` is ascribed explicitly, as a bare `inferInstance` asks for
`DecidableEq (testSlice.B a)`, which does not reduce. -/
instance finitaryTestSlice : testSlice.toPFunctor.Finitary
  | true => { card := 1
              equiv := { toFun := fun _ ↦ 0, invFun := fun _ ↦ (),
                         left_inv := fun _ ↦ rfl,
                         right_inv := fun i ↦ Fin.cases rfl (fun i ↦ i.elim0) i }
              decEq := (inferInstance : DecidableEq Unit) }
  | false => { card := 0
               equiv := { toFun := Empty.elim, invFun := Fin.elim0,
                          left_inv := fun x ↦ x.elim, right_inv := fun i ↦ i.elim0 }
               decEq := (inferInstance : DecidableEq Empty) }

/-- A direction lying over the index it is assigned. -/
def dirOverTrue : Bool := decide (testSlice.DirectionOver true true ())

/-- A direction not lying over the given index. -/
def dirOverFalse : Bool := decide (testSlice.DirectionOver true false ())

/-- A shape lying over its output index. -/
def shapeOverTrue : Bool := decide (testSlice.ShapeOver true true)

/-- A shape not lying over the given output index. -/
def shapeOverFalse : Bool := decide (testSlice.ShapeOver false true)

/-- A compatible direction assignment. -/
def compatTrue : Bool :=
  decide (testSlice.toSliceDomPFunctor.Compatible id true fun _ ↦ true)

/-- An incompatible direction assignment. -/
def compatFalse : Bool :=
  decide (testSlice.toSliceDomPFunctor.Compatible id true fun _ ↦ false)

example : dirOverTrue = true := by decide
example : dirOverFalse = false := by decide
example : shapeOverTrue = true := by decide
example : shapeOverFalse = false := by decide
example : compatTrue = true := by decide
example : compatFalse = false := by decide
```

- [ ] **Step 2: Run the test to verify it fails**

```bash
lake build GebTests.Mathlib.Data.PFunctor.Slice.Decidable
```

Expected: FAIL, `unknown module prefix`.

- [ ] **Step 3: Write the implementation**

Create `Geb/Mathlib/Data/PFunctor/Slice/Decidable.lean` with the
copyright block, `module`, the imports
`public import Geb.Mathlib.Data.PFunctor.Slice.W`,
`public import Geb.Mathlib.Data.PFunctor.Univariate.Finitary`,
`public import Geb.Mathlib.Data.FinEnum`,
`import Geb.Mathlib.Data.W.Basic` (plain; only `WType.elim_mk`, used in a
proof, is needed from it), a module docstring, `public section`,
`universe uA uB uD uC uI uX`, and:

```lean
namespace SliceDomPFunctor

/-- Whether a direction lies over a given base index is decidable when
the base has decidable equality. No finiteness is needed. -/
instance decidableDirectionOver {dom : Type uD} (F : SliceDomPFunctor.{uA, uB} dom)
    [DecidableEq dom] (a : F.A) (i : dom) : DecidablePred (F.DirectionOver a i) :=
  fun b ↦ decidable_of_iff (F.rCurried a b = i) Iff.rfl

/-- A quantifier over the directions of shape `a` lying over `i` is
decidable. Stated at `Direction` rather than left to
`FinEnum.decidableForallSubtype`: `Direction` is a `def`, and instance
resolution does not unfold it to a `Subtype`. -/
instance decidableForallDirection {dom : Type uD} (F : SliceDomPFunctor.{uA, uB} dom)
    [F.Finitary] [DecidableEq dom] (a : F.A) (i : dom)
    {q : F.Direction a i → Prop} [DecidablePred q] : Decidable (∀ b, q b) :=
  inferInstanceAs (Decidable (∀ b : Subtype (F.DirectionOver a i), q b))

/-- Compatibility of a direction assignment with a projection is
decidable: `Compatible p a v` is by definition the function equality
`p ∘ v = F.r ∘ Sigma.mk a` out of the finite direction type, decided by
`FinEnum.decidablePiFinEnum`. -/
instance decidableCompatible {dom : Type uD} (F : SliceDomPFunctor.{uA, uB} dom)
    [F.Finitary] [DecidableEq dom] {X : Type uX} (p : X → dom)
    (a : F.A) (v : F.B a → X) : Decidable (F.Compatible p a v) :=
  decidable_of_iff (p ∘ v = F.r ∘ Sigma.mk a) Iff.rfl

end SliceDomPFunctor

namespace SlicePFunctor

/-- Whether a shape lies over a given output index is decidable when the
codomain has decidable equality. -/
instance decidableShapeOver {dom : Type uD} {cod : Type uC}
    (F : SlicePFunctor.{uA, uB, uD, uC} dom cod) [DecidableEq cod] (j : cod) :
    DecidablePred (F.ShapeOver j) :=
  fun a ↦ decidable_of_iff (F.q a = j) Iff.rfl

end SlicePFunctor
```

Add `import Geb.Mathlib.Data.PFunctor.Slice.Decidable` to
`Geb/Mathlib/Data/PFunctor/Slice.lean`.

- [ ] **Step 4: Run the test to verify it passes**

```bash
lake build GebTests.Mathlib.Data.PFunctor.Slice.Decidable
```

Expected: PASS. If `decidableForallDirection` fails to fire, check that
`DirectionOver`'s `DecidablePred` instance is in scope — it is what makes
the `Subtype` decidable.

- [ ] **Step 5: Verify the axioms and commit**

Temporarily `#print axioms compatTrue`; expect `[propext, Quot.sound]`.

```bash
lake build && lake test && lake lint
scripts/lint-imports.sh
jj commit -m "feat(slice): decide the fiber and compatibility predicates"
```

---

### Task 7: The `WValid` checker

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/Slice/Decidable.lean`
- Modify: `GebTests/Mathlib/Data/PFunctor/Slice/Decidable.lean`

**Interfaces:**

- Consumes: Task 6, plus `WType.elim_mk` from the existing
  `Data/W/Basic.lean`.
- Produces:

  ```lean
  SlicePFunctor.wValidStep : F.toPFunctor.Obj (I × Bool) → I × Bool
  SlicePFunctor.wValidData  : F.toPFunctor.W → I × Bool
  SlicePFunctor.wValidBool  : F.toPFunctor.W → Bool
  SlicePFunctor.wValidBool_eq_true_iff : F.wValidBool w = true ↔ F.WValid w
  SlicePFunctor.decidableWValid : Decidable (F.WValid w)
  ```

- [ ] **Step 1: Write the failing test**

Append to the slice test module. Under `testSlice`'s `r := fun x ↦ x.1`
and `q := id`, a `true`-node's children must have root index
`rCurried true _ = true`, i.e. be further `true`-nodes; since no finite
tree is an infinite `true`-spine, the only admissible tree is the bare
leaf. The valid and invalid examples are chosen accordingly:

```lean
/-- The admissible tree: the bare leaf, whose `OverInput` is vacuous. -/
def leafTree : testSlice.toPFunctor.W := WType.mk false Empty.elim

/-- An admissible tree is admitted. -/
def wValidTrue : Bool := decide (testSlice.WValid leafTree)

/-- An inadmissible tree: a `true`-node whose child has root index
`false`, violating `OverInput`. -/
def branchTree : testSlice.toPFunctor.W :=
  WType.mk true fun _ ↦ WType.mk false Empty.elim

/-- An inadmissible tree is rejected. -/
def wValidFalse : Bool := decide (testSlice.WValid branchTree)

example : wValidTrue = true := by decide
example : wValidFalse = false := by decide
```

- [ ] **Step 2: Run the test to verify it fails**

```bash
lake build GebTests.Mathlib.Data.PFunctor.Slice.Decidable
```

Expected: FAIL, `failed to synthesize Decidable (testSlice.WValid …)`.

- [ ] **Step 3: Write the implementation**

Append to `Geb/Mathlib/Data/PFunctor/Slice/Decidable.lean`, inside
`namespace SlicePFunctor`:

```lean
/-- The algebra of the `WValid` fold: a node's index is its shape's
output index, and it is admitted when every child is admitted and the
children's index family equals the direction-input map. The `Bool`
analogue of `wIndexStep`. -/
@[expose] def wValidStep {I : Type uI} (F : SlicePFunctor.{uA, uB, uI, uI} I I)
    [F.Finitary] [DecidableEq I] :
    F.toPFunctor.Obj (I × Bool) → I × Bool :=
  fun x ↦ (F.q x.1,
    decide (∀ b, (x.2 b).2 = true) && decide (∀ b, (x.2 b).1 = F.rCurried x.1 b))

/-- The `WValid` fold: index and admissibility computed together, by a
single `WType.elim` at the carrier `I × Bool`. The index must be carried
even though it is non-recursive, because the step sees the children's
results and never the children. -/
@[expose] def wValidData {I : Type uI} (F : SlicePFunctor.{uA, uB, uI, uI} I I)
    [F.Finitary] [DecidableEq I] : F.toPFunctor.W → I × Bool :=
  WType.elim (I × Bool) (F.wValidStep)

/-- The admissibility component of the fold. -/
@[expose] def wValidBool {I : Type uI} (F : SlicePFunctor.{uA, uB, uI, uI} I I)
    [F.Finitary] [DecidableEq I] : F.toPFunctor.W → Bool :=
  fun w ↦ (F.wValidData w).2

/-- The index component of the fold is the root index. -/
@[simp] theorem wValidData_fst {I : Type uI} (F : SlicePFunctor.{uA, uB, uI, uI} I I)
    [F.Finitary] [DecidableEq I] (w : F.toPFunctor.W) :
    (F.wValidData w).1 = F.wIndexRoot w := by
  cases w with
  | mk a f => rfl

/-- `wValidBool` decides admissibility. -/
theorem wValidBool_eq_true_iff {I : Type uI} (F : SlicePFunctor.{uA, uB, uI, uI} I I)
    [F.Finitary] [DecidableEq I] (w : F.toPFunctor.W) :
    F.wValidBool w = true ↔ F.WValid w :=
  WType.rec (motive := fun w ↦ F.wValidBool w = true ↔ F.WValid w)
    (fun a f ih ↦ by
      rw [F.wValid_mk a f]
      change ((decide (∀ b, F.wValidBool (f b) = true)) &&
        decide (∀ b, (F.wValidData (f b)).1 = F.rCurried a b)) = true ↔ _
      rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
      refine and_congr (forall_congr' ih) ?_
      exact ⟨fun h ↦ funext fun b ↦ (F.wValidData_fst (f b)).symm.trans (h b),
        fun h b ↦ (F.wValidData_fst (f b)).trans (congrFun h b)⟩)
    w

/-- Admissibility of a slice W-tree is decidable. -/
instance decidableWValid {I : Type uI} (F : SlicePFunctor.{uA, uB, uI, uI} I I)
    [F.Finitary] [DecidableEq I] (w : F.toPFunctor.W) :
    Decidable (F.WValid w) :=
  decidable_of_iff _ (F.wValidBool_eq_true_iff w)
```

The `change` above states `wValidStep` unfolded at `WType.mk a f`, which
holds by `WType.elim_mk` definitionally. Use `change`, not `show`: the
`linter.style.show` rule (fatal under `warningAsError`) rejects a `show`
that alters the goal. The two conjuncts are `AllValid` and `OverInput`;
the `▸` rewrite in the closing term does not elaborate because the goal
carries `wIndexRoot ∘ f` rather than `wIndexRoot (f b)`, so `.symm.trans`
/ `.trans (congrFun …)` are used in its place.

- [ ] **Step 4: Run the test to verify it passes**

```bash
lake build GebTests.Mathlib.Data.PFunctor.Slice.Decidable
```

Expected: PASS.

- [ ] **Step 5: Verify the axioms and commit**

Temporarily `#print axioms wValidTrue`; expect `[propext, Quot.sound]`.

```bash
lake build && lake test && lake lint
jj commit -m "feat(slice): decide admissibility of slice W-trees"
```

---

### Task 8: The `IsNatural` instance

**Files:**

- Create: `Geb/Mathlib/Data/PFunctor/Presheaf/Decidable.lean`
- Create: `GebTests/Mathlib/Data/PFunctor/Presheaf/Decidable.lean`
- Modify: `Geb/Mathlib/Data/PFunctor/Presheaf.lean` and its test mirror

**Interfaces:**

- Consumes: Tasks 2, 5, 6.
- Produces: `PresheafDomPFunctorData.decidableIsNatural`.

- [ ] **Step 1: Write the failing test**

Create the presheaf test module with the usual preamble, re-declaring the
fixture data (the existing `presheafWitness` is module-private). It needs:
the preorder category on `Fin 2`; a choice-free `FinEnum (Fin 2)`; a
choice-free `FinEnum` for the hom-sets, **stated at the `⟶` head** — an
instance at `PLift` will not fire, because `Quiver.Hom` is a `def` that
instance resolution does not unfold; a presheaf-domain functor copying
`presheafWitnessData`; and a new input presheaf with a two-element fiber,
which is what makes `IsNatural` falsifiable. Then:

```lean
/-- A natural direction assignment. -/
def isNaturalTrue : Bool := decide (witness.IsNatural xGood)

/-- An unnatural direction assignment. -/
def isNaturalFalse : Bool := decide (witness.IsNatural xBad)

example : isNaturalTrue = true := by decide
example : isNaturalFalse = false := by decide
```

Both verdicts are known to reduce by kernel `rfl` on a fixture of this
shape, so `by decide` is the right tactic and a failure to reduce is a
real defect, not an expected limitation.

- [ ] **Step 2: Run the test to verify it fails**

```bash
lake build GebTests.Mathlib.Data.PFunctor.Presheaf.Decidable
```

Expected: FAIL, `unknown module prefix`.

- [ ] **Step 3: Write the implementation**

Create `Geb/Mathlib/Data/PFunctor/Presheaf/Decidable.lean` with the
copyright block, `module`, the imports
`public import Geb.Mathlib.Data.PFunctor.Presheaf.W`,
`public import Geb.Mathlib.Data.PFunctor.Slice.Decidable`,
`public import Geb.Mathlib.Data.W.Basic`, a module docstring,
`public section`, `open CategoryTheory`, `universe uI uA uB vI uZ`, and:

```lean
namespace PresheafDomPFunctorData

/-- Naturality of a direction assignment is decidable when the functor is
finitary, the index category has finitely many objects and finite
hom-sets, and the input presheaf's values have decidable equality. Its
subject is a slice object over `elemProj Z`, not a `PresheafDomPFunctorData.obj Z`:
the latter is the `IsNatural` subtype itself, on which the predicate
holds by projection. -/
instance decidableIsNatural {I : Type uI} [Category.{vI} I]
    (F : PresheafDomPFunctorData.{uI, uA, uB, vI} I) {Z : Iᵒᵖ ⥤ Type uZ}
    [F.Finitary] [FinEnum I] [∀ i i' : I, FinEnum (i' ⟶ i)]
    [∀ i : I, DecidableEq (Z.obj ⟨i⟩)]
    (x : F.toSliceDomPFunctor.Obj (elemProj Z)) : Decidable (F.IsNatural x) :=
  inferInstanceAs (Decidable (∀ ⦃i i' : I⦄ (f : i' ⟶ i)
    (b : F.toSliceDomPFunctor.Direction x.1.1 i),
      F.value x (F.directionRestr x.1.1 f b) = Z.map f.op (F.value x b)))

end PresheafDomPFunctorData
```

Add `import Geb.Mathlib.Data.PFunctor.Presheaf.Decidable` to
`Geb/Mathlib/Data/PFunctor/Presheaf.lean`.

- [ ] **Step 4: Run the test to verify it passes**

```bash
lake build GebTests.Mathlib.Data.PFunctor.Presheaf.Decidable
```

Expected: PASS, both verdicts reducing.

- [ ] **Step 5: Verify the axioms and commit**

Temporarily `#print axioms isNaturalTrue`; expect `[propext, Quot.sound]`.
If `Classical.choice` appears, a `FinEnum` in the fixture was reached
through `FinEnum.ofList` — rebuild it from the structure fields.

```bash
lake build && lake test && lake lint
scripts/lint-imports.sh
jj commit -m "feat(presheaf): decide naturality of a direction assignment"
```

---

### Task 9: The hereditary-naturality checker

**Files:**

- Modify: `Geb/Mathlib/Data/PFunctor/Presheaf/Decidable.lean`

**Interfaces:**

- Consumes: Tasks 3, 4, 6, 8.
- Produces:

  ```lean
  PresheafPFunctor.wRestrTreeRaw (g : j' ⟶ j) (w : F.toPFunctor.W)
      (hq : F.q (PFunctor.W.head w) = j) : WType F.toPFunctor.B
  PresheafPFunctor.wRestrTree_val : (F.wRestrTree g z hq).1 = F.wRestrTreeRaw g z.1 hq
  PresheafPFunctor.isHereditarilyNaturalBoolCore
      (decI : DecidableEq I) (feI : FinEnum I) (feHom : ∀ i i', FinEnum (i' ⟶ i))
      (feB : ∀ a, FinEnum (F.toPFunctor.B a)) (decEqW : DecidableEq (WType F.toPFunctor.B)) :
      F.toPFunctor.W → Bool
  PresheafPFunctor.isHereditarilyNaturalBoolCore_eq_true_iff : … ↔ F.IsHereditarilyNatural z
  PresheafPFunctor.decidableIsHereditarilyNatural :
      Decidable (F.IsHereditarilyNatural z)
  ```

This task follows the repository's typeclass-instance pattern
([docs/rules/lean-coding.md](../../rules/lean-coding.md)
§ Structure and typeclass patterns). The decision procedure is a
*classless* core taking every finiteness and decidability datum as an
explicit value, and the `Decidable` instance is a thin wrapper resolving
those instances at the boundary and passing them in. The reason is not
stylistic: `isHereditarilyNaturalBool` written as `decide (∀ b : Direction …)`
does not elaborate, because `PresheafPFunctor` has a `SliceDomPFunctor`
diamond and instance synthesis for `decide`'s quantifier cannot resolve
`decidableForallDirection` / `decidableDirectionOver` through the diamond
projection `F.toSliceDomPFunctor` (verified: it fails there while firing on
a bare `SliceDomPFunctor` and on `PresheafDomPFunctorData`, which is why
Task 8's `IsNatural` is unaffected). The classless core enumerates raw
directions with `FinEnum.toList` / `List.all` and never forces that
synthesis; the whole construction was verified to elaborate at
`{Quot.sound}`.

- [ ] **Step 1: Write `wRestrTreeRaw` and its agreement lemma**

`wRestrTree` is `SlicePFunctor.W.mk (F.objRestrElt g (dest z) _)`, and
`W.mk`'s underlying tree is `WType.mk x.1.1 (Subtype.val ∘ x.1.2)`. The
raw form drops the validity witness but keeps the head-index one, which
`objRestrElt` needs to form `⟨x.1.1, hq⟩ : F.Shape j`. Its result type is
`WType F.toPFunctor.B`, not `F.toPFunctor.W`: the core's tree equality is
against a `para`-carrier value of type `WType β`, and a `PFunctor.W`-typed
right side would make the equation mixed-headed, on which no `DecidableEq`
fires (verified). The two are definitionally equal, so `wRestrTree_val`
still closes by `cases` then `rfl`.

```lean
/-- The root-only restriction of a raw W-tree along a morphism: restrict
the root shape and reindex the direction assignment. The underlying-tree
form of `wRestrTree`, stated on the admissibility subtype; the head-index
witness `hq` is retained because `objRestrElt` consumes it. -/
@[expose] def wRestrTreeRaw {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I) ⦃j j' : I⦄ (g : j' ⟶ j)
    (w : F.toPFunctor.W) (hq : F.q (PFunctor.W.head w) = j) : WType F.toPFunctor.B :=
  match w, hq with
  | WType.mk a f, hq =>
      WType.mk (F.shapeRestr g ⟨a, hq⟩).1
        fun b' ↦ f (F.reindex g ⟨a, hq⟩ (i := F.rCurried _ b') ⟨b', rfl⟩).1

/-- The underlying tree of `wRestrTree` is `wRestrTreeRaw`. -/
theorem wRestrTree_val {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I) ⦃j j' : I⦄ (g : j' ⟶ j)
    (z : F.toSlicePFunctor.W) (hq : F.q (PFunctor.W.head z.1) = j) :
    (F.wRestrTree g z hq).1 = F.wRestrTreeRaw g z.1 hq := by
  obtain ⟨w, hw⟩ := z
  cases w with
  | mk a f => rfl
```

- [ ] **Step 2: Write the classless core**

Enumerate raw directions `b'` from `feB x.1` and admit `b'` as a direction
over `i` when `F.rCurried x.1 b' = i` (decided with `decI`), giving the
`Direction` element `⟨b', hb⟩`; then decide the head-index witness with
`decI` and compare the two trees with `decEqW`. All data explicit — no
inference through the diamond.

```lean
/-- Hereditary naturality as a `Bool`, classless. All finiteness and
decidability supplied explicitly; the raw directions of each node are
enumerated and filtered by an explicit equality test, so no typeclass
inference traverses the `PresheafPFunctor` diamond. -/
@[expose] def isHereditarilyNaturalBoolCore {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    (decI : DecidableEq I) (feI : FinEnum I) (feHom : ∀ i i' : I, FinEnum (i' ⟶ i))
    (feB : ∀ a, FinEnum (F.toPFunctor.B a)) (decEqW : DecidableEq (WType F.toPFunctor.B)) :
    F.toPFunctor.W → Bool :=
  WType.para Bool fun x ↦
    ((feI.toList).all fun i ↦ (feI.toList).all fun i' ↦
      ((feHom i i').toList).all fun g ↦
        ((feB x.1).toList).all fun b' ↦
          match decI (F.rCurried x.1 b') i with
          | isFalse _ => true
          | isTrue hb =>
            match decI (F.q (PFunctor.W.head (x.2 b').1)) i with
            | isFalse _ => true
            | isTrue hq =>
              (decEqW (x.2 (F.directionRestr x.1 g ⟨b', hb⟩).1).1
                (F.wRestrTreeRaw g (x.2 b').1 hq)).decide)
    && ((feB x.1).toList).all fun b' ↦ (x.2 b').2
```

- [ ] **Step 3: Add the correctness lemma**

The proof relates the `List.all` enumerations to the quantifiers of
`IsHereditarilyNatural` (`FinEnum.mem_toList` and `List.all_eq_true`), and
the per-node tree equation via `decide_eq_true_iff` — the core tests it
with the explicit `(decEqW A B).decide`, so `beq` is not invoked here —
together with `wRestrTree_val` and `Subtype.ext`. On a valid node the two
`isTrue` branches are the ones taken, their witnesses being the
compatibility datum `(F.compatible_iff _ _ _).mp x.2 b'` and the direction
constraint; the `isFalse` branches are unreachable there.

The proof below is the verified output of Task 1 (compiled sorry-free at
`{propext, Quot.sound}`). If Task 1 has not been completed, stop here.

```lean
/-- `isHereditarilyNaturalBoolCore` decides hereditary naturality. -/
theorem isHereditarilyNaturalBoolCore_eq_true_iff {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    (decI : DecidableEq I) (feI : FinEnum I) (feHom : ∀ i i' : I, FinEnum (i' ⟶ i))
    (feB : ∀ a, FinEnum (F.toPFunctor.B a)) (decEqW : DecidableEq (WType F.toPFunctor.B))
    (z : F.toSlicePFunctor.W) :
    F.isHereditarilyNaturalBoolCore decI feI feHom feB decEqW z.1 = true ↔
      F.IsHereditarilyNatural z := by
  refine SlicePFunctor.W.induction
    (motive := fun z ↦ F.isHereditarilyNaturalBoolCore decI feI feHom feB decEqW z.1 = true ↔
      F.IsHereditarilyNatural z)
    (fun x ih ↦ ?_) z
  rw [F.isHereditarilyNatural_mk x]
  simp only [SlicePFunctor.W.mk, isHereditarilyNaturalBoolCore, WType.para_mk]
  rw [Bool.and_eq_true]
  refine and_congr ?_ ?_
  · simp only [List.all_eq_true, FinEnum.mem_toList, forall_const]
    constructor
    · intro H i i' g b
      have hb : F.rCurried x.1.1 b.1 = i := b.2
      have hqval : F.q (PFunctor.W.head (x.1.2 b.1).1) = i :=
        (((F.toSliceDomPFunctor.compatible_iff F.toSlicePFunctor.wIndex x.1.1 x.1.2).mp
          x.2 b.1).trans hb)
      have hthis := H i i' g b.1
      split at hthis
      · exact absurd hb (by assumption)
      · split at hthis
        · exact absurd hqval (by assumption)
        · simp only [decide_eq_true_iff] at hthis
          exact Subtype.ext (hthis.trans (F.wRestrTree_val g (x.1.2 b.1) hqval).symm)
    · intro H i i' g b'
      split
      · rfl
      · split
        · rfl
        · simp only [decide_eq_true_iff]
          exact (congrArg Subtype.val (H g ⟨b', by assumption⟩)).trans
            (F.wRestrTree_val g (x.1.2 b') _)
  · rw [List.all_eq_true]
    constructor
    · intro H b
      exact (ih b).mp (H b (FinEnum.mem_toList b))
    · intro H b' _
      exact (ih b').mpr (H b')
```

Two tactic-level notes, both forced by Lean facts (the mathematical route
is unchanged). First, the one-level LHS unfolding is inline
(`simp only [SlicePFunctor.W.mk, isHereditarilyNaturalBoolCore, WType.para_mk]`),
not a separate `_mk` rewrite lemma: restating the `match` body in a lemma
forces a second matcher constant not defeq to the definition's own. Second,
the `decI` matches are dependent, so `split` / `split at` drive the case
analysis and `wRestrTree_val` is applied in term mode
(`.trans` / `.symm`), with `Subtype.ext` and proof irrelevance bridging the
raw-tree equality to the `F.toSlicePFunctor.W` equality.

- [ ] **Step 4: Add the wrapper instance**

The wrapper resolves each instance at the boundary — where the resolutions
are single and direct, not the diamond-fragile `decide (∀ Direction)` — and
passes them as explicit values.

```lean
/-- Hereditary naturality of a slice W-tree is decidable. -/
instance decidableIsHereditarilyNatural {I : Type uI} [Category.{vI} I]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} I I)
    [F.Finitary] [FinEnum I] [∀ i i' : I, FinEnum (i' ⟶ i)]
    [DecidableEq F.A] (z : F.toSlicePFunctor.W) :
    Decidable (F.IsHereditarilyNatural z) :=
  decidable_of_iff _ (F.isHereditarilyNaturalBoolCore_eq_true_iff inferInstance inferInstance
    inferInstance inferInstance inferInstance z)
```

- [ ] **Step 5: Build, verify the axioms, and commit**

```bash
lake build Geb.Mathlib.Data.PFunctor.Presheaf.Decidable
```

Expected: PASS with no `sorry` warning. Temporarily
`#print axioms PresheafPFunctor.decidableIsHereditarilyNatural`; expect
`[propext, Quot.sound]`.

```bash
lake build && lake test && lake lint
jj commit -m "feat(presheaf): decide hereditary naturality of slice W-trees"
```

---

### Task 10: The hereditary-naturality fixture and reduction test

This is the branch's largest test deliverable and nothing of its shape
exists to adapt.

**Files:**

- Modify: `GebTests/Mathlib/Data/PFunctor/Presheaf/Decidable.lean`

**Interfaces:**

- Consumes: Task 9.
- Produces: nothing later tasks depend on.

- [ ] **Step 1: Construct the fixture**

An endofunctor `PresheafPFunctor I I` meeting all of:

- an index category with a non-identity morphism (the preorder on
  `Fin 2` serves, reusing Task 8's hom `FinEnum`);
- a leaf shape, so the W-type is inhabited;
- a shape with at least two directions over distinct base indices, and
  two distinct admissible subtrees over a common index, so that a child
  and the root-restriction of its sibling can differ — without this the
  predicate is unfalsifiable;
- the seven functor laws (`directionRestr_id`, `directionRestr_comp`,
  `shapeRestr_id`, `shapeRestr_comp`, `reindex_naturality`, `reindex_id`,
  `reindex_comp`) proved directly. The existing fixture's
  `Subsingleton.elim` route depends on its own `r` and `q` and will not
  transfer.

Give each component a docstring recording which of these conditions it
supplies.

- [ ] **Step 2: Write the reduction test**

```lean
/-- A hereditarily natural tree. -/
def hereditaryTrue : Bool := decide (wFixture.IsHereditarilyNatural goodTree)

/-- A tree failing naturality at one node. -/
def hereditaryFalse : Bool := decide (wFixture.IsHereditarilyNatural badTree)

example : hereditaryTrue = true := by decide
example : hereditaryFalse = false := by decide
```

- [ ] **Step 3: Run the test**

```bash
lake build GebTests.Mathlib.Data.PFunctor.Presheaf.Decidable
```

Expected: PASS. If `decide` fails to reduce, the obstruction is the
`cast` in `PresheafDomPFunctorData.value` together with `objRestrElt`'s
and `wRestrTree`'s transports. First try choosing the fixture so the
transported types are definitionally equal at its concrete indices. If
that fails, stop and report: restating the checker to avoid the transport
is a design change and is the user's decision.

- [ ] **Step 4: Verify the axioms and commit**

Temporarily `#print axioms hereditaryTrue`; expect `[propext, Quot.sound]`.

```bash
lake build && lake test && lake lint
jj commit -m "test(presheaf): exercise the hereditary-naturality decision"
```

---

### Task 11: Persistent documentation

**Files:**

- Modify: `docs/index.md`, `TODO.md`, `docs/references.bib`

**Interfaces:**

- Consumes: every prior task's declarations.
- Produces: nothing.

- [ ] **Step 1: Add the four bibliography entries**

Append to `docs/references.bib`, matching the file's field alignment:
`Meertens1992` (Formal Aspects of Computing 4(5):413–424, 1992, doi
`10.1007/BF01211391`), `Leivant1999` (Annals of Pure and Applied Logic
96(1–3):209–229, 1999, doi `10.1016/S0168-0072(98)00040-2`),
`DalLagoMartiniZorzi2010` (EPTCS 23:47–62, 2010, doi
`10.4204/EPTCS.23.4`), `AvanziniDalLago2018` (Information and Computation
261:3–22, 2018, doi `10.1016/j.ic.2018.05.003`, eprint `1501.00894`). The
full blocks are in the spec's § Transcription or novel.

- [ ] **Step 2: Add the concepts to `docs/index.md`**

One entry per new module, in topological order after the existing
`Slice`/`Presheaf` entries, naming the declarations each contributes.

- [ ] **Step 3: Update `TODO.md`**

Remove roadmap item 1 and merge its content into `docs/index.md`. Add
the complexity conjecture to § Next up, quoting the spec's
§ Complexity of the checkers and citing the three keys. Note in
§ Triggers that the shared-presheaf-test-fixtures condition has been met,
and that the extraction is to be taken together with the test-module
import-visibility and test-declaration-privacy items, the first entailing
the other two.

- [ ] **Step 4: Lint the Markdown**

```bash
doctoc --update-only .
markdownlint-cli2 '**/*.md'
```

Expected: `Summary: 0 issues`.

- [ ] **Step 5: Commit**

```bash
jj commit -m "doc(pfunctor): document the decidable validity layer"
```

---

### Task 12: Close the branch

**Files:**

- Remove: the spec and this plan

**Interfaces:**

- Consumes: Tasks 1–11.
- Produces: a branch ready for review.

- [ ] **Step 1: Run the full pre-push checklist**

```bash
scripts/pre-push.sh
```

Expected: all checks pass — build, test, `lake lint`, `lake shake`,
import lint, markdownlint, doctoc, axiom linter.

- [ ] **Step 2: Fix any `lake shake` import findings**

Shake rejects an import whose constants are all reachable another way.
The spec predicts the plain-versus-`public` split; shake's verdict
governs. Adjust and re-run.

- [ ] **Step 3: Remove the transient documents**

```bash
rm docs/superpowers/specs/2026-07-22-decidable-validity-design.md
rm docs/superpowers/plans/2026-07-22-decidable-validity.md
jj commit -m "doc: remove the decidable-validity spec and plan"
```

- [ ] **Step 4: Report for review**

Summarize: the declarations added, the axiom readings, the open items
(none should remain), and confirm no push has been made. The user reviews
line-by-line before any push.
