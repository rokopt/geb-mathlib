# Bellantoni-Cook syntax and semantics — implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Define the function class `B` of [HeraudNowak2011] § 3.2 in Lean —
its syntax as the slice W-type of a signature functor over `ℕ × ℕ`, and its
interpretation by that type's eliminator.

**Architecture:** A non-recursive `Shape` type carries the seven constructor
forms with their arity parameters; `q : Shape → ℕ × ℕ` and
`rc : (a : Shape) → Direction a → ℕ × ℕ` encode the paper's arity relation as
data (conclusions and hypotheses respectively); `sig` bundles them as a
`SlicePFunctor (ℕ × ℕ) (ℕ × ℕ)`; `BC := sig.W` admits exactly the
well-formed terms; and `BC.eval` is one application of
`SlicePFunctor.W.elim` into the dependent target `Σ i, Sem i`.

**Tech Stack:** Lean 4 (toolchain v4.33.0-rc2), mathlib,
`Geb.Mathlib.Data.PFunctor.Slice.*`, `jj` for version control.

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Global Constraints](#global-constraints)
- [Commit sequence](#commit-sequence)
- [File structure](#file-structure)
- [Task 1: Branch, spec commit, plan commit](#task-1-branch-spec-commit-plan-commit)
- [Task 2: The signature functor](#task-2-the-signature-functor)
- [Task 3: Finiteness and decidable admissibility](#task-3-finiteness-and-decidable-admissibility)
- [Task 4: The syntax and the semantics](#task-4-the-syntax-and-the-semantics)
- [Task 5: The test module](#task-5-the-test-module)
- [Task 6: Documentation](#task-6-documentation)
- [Task 7: The pre-push gate](#task-7-the-pre-push-gate)
- [Task 8: Remove the spec and the plan](#task-8-remove-the-spec-and-the-plan)

<!-- END doctoc -->

## Global Constraints

Every task's requirements implicitly include these. They are the spec's
§ Constraints, verbatim in substance.

1. No `noncomputable`. `#print axioms` on every declaration lies within
   `{propext, Quot.sound}`. `Quot.sound` is permitted, not excluded.
2. No self-referential `inductive` and no self-calling `def`. `Shape` is
   non-recursive; the syntax's recursion is `sig.W`; the semantics'
   recursions are `SlicePFunctor.W.elim` and `List.rec`.
3. All four new `.lean` files declare `module`. The library module uses
   `public import` and a `public section`; the test module uses plain
   `import` with `set_option linter.privateModule false`.
4. `scripts/pre-push.sh` clean, `lake shake`, `lake lint` and
   `scripts/lint-imports.sh` included.
5. No `#guard`; every assertion is a `theorem` closing by `rfl`. `plusOf` and
   `multOf` are `def`s, `BCOf n s` being a type rather than a `Prop`.
6. Lambda notation uses `↦`, not `=>`, in `fun`.
7. Library imports: `Geb.Mathlib.Data.PFunctor.Slice.W`,
   `Geb.Mathlib.Data.PFunctor.Univariate.Finitary`,
   `Mathlib.Logic.Equiv.Fin.Basic`. The test module adds
   `Geb.Mathlib.Data.PFunctor.Slice.Decidable` and the library module.
   Neither module names `Mathlib.Data.Fin.Tuple.Basic` or
   `Mathlib.Data.Fin.VecNotation`, though both apply `Fin.append`,
   `Fin.cons`, `Fin.tail` and `![…]`: `Mathlib.Logic.Equiv.Fin.Basic`
   supplies both transitively, and naming either makes plain `lake shake`
   report the module carrying it.
8. Copyright headers take the form used throughout the tree:

   ```lean
   /-
   Copyright (c) 2026 Terence Rokop. All rights reserved.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: Terence Rokop
   -/
   ```

9. Commit messages follow the repository's Conventional-Commits-shaped
   convention (`feat` / `fix` / `doc` / `style` / `refactor` / `test` /
   `chore` / `perf` / `ci`), imperative present tense, no capital, no period.
10. **Version control is `jj`, not `git`.** A PreToolUse hook blocks
    mutating `git` subcommands. Commit with `jj commit -m "…"`, which
    commits the whole working copy and starts a fresh change.

## Commit sequence

The spec's § Placement fixes the phase order: spec, plan, library module,
test module, documentation, then a final commit removing the spec and the
plan. This plan spans the library phase over three commits (Tasks 2-4),
which refines that order without reordering it.

## File structure

| Path | Responsibility |
| --- | --- |
| `Geb/Mathlib/Computability.lean` | directory index; imports the content module |
| `Geb/Mathlib/Computability/BellantoniCook.lean` | the whole library: signature, finiteness, syntax, semantics |
| `GebTests/Mathlib/Computability.lean` | test directory index |
| `GebTests/Mathlib/Computability/BellantoniCook.lean` | the worked terms and the thirteen assertions |
| `Geb/Mathlib.lean` | gains one `public import` |
| `GebTests/Mathlib.lean` | gains one `import` |
| `docs/references.bib` | two entries |
| `docs/references.md` | one pointer |
| `docs/index.md` | one bullet |
| `TODO.md` | one `### Bellantoni-Cook` subsection, four trigger entries |

One content module, not a `Defs`/`Basic` split: this workstream states no
lemmas, so there is nothing to separate.

---

## Task 1: Branch, spec commit, plan commit

**Files:**

- Modify: none (version-control only)

**Interfaces:**

- Consumes: nothing
- Produces: a topic branch `feat/bellantoni-cook` whose first two commits
  carry the spec and this plan

- [ ] **Step 1: Create the topic branch on the current change**

```bash
jj bookmark create feat/bellantoni-cook -r @
```

- [ ] **Step 2: Confirm the working copy holds the spec and the plan**

Run: `jj status`
Expected: two `A` lines, the spec and this plan, in one change.

- [ ] **Step 3: Commit the spec alone**

`jj commit` with paths keeps the named paths in the current commit and moves
everything else to a new working-copy commit on top, which is how the spec
and the plan become two commits in the order § Placement fixes.

```bash
jj commit docs/superpowers/specs/2026-08-04-bellantoni-cook-design.md \
  -m "doc: add the Bellantoni-Cook design spec"
```

- [ ] **Step 4: Confirm the plan is now the only working-copy change**

Run: `jj status`
Expected: exactly one line, `A docs/superpowers/plans/2026-08-04-bellantoni-cook.md`

- [ ] **Step 5: Commit the plan**

```bash
jj commit -m "doc: add the Bellantoni-Cook implementation plan"
```

- [ ] **Step 6: Advance the bookmark to the new head**

```bash
jj bookmark set feat/bellantoni-cook -r @-
```

Run: `jj log -r 'feat/bellantoni-cook'`
Expected: the bookmark points at the plan commit.

---

## Task 2: The signature functor

**Files:**

- Create: `Geb/Mathlib/Computability.lean`
- Create: `Geb/Mathlib/Computability/BellantoniCook.lean`
- Modify: `Geb/Mathlib.lean`

**Interfaces:**

- Consumes: `SlicePFunctor` from `Geb.Mathlib.Data.PFunctor.Slice.W`
- Produces:
  - `BellantoniCook.Shape : Type` — seven constructors, listed below
  - `BellantoniCook.Direction : Shape → Type`
  - `BellantoniCook.rc : (a : Shape) → Direction a → ℕ × ℕ`
  - `BellantoniCook.q : Shape → ℕ × ℕ`
  - `BellantoniCook.sig : SlicePFunctor (ℕ × ℕ) (ℕ × ℕ)`

- [ ] **Step 1: Create the directory index**

Create `Geb/Mathlib/Computability.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Computability.BellantoniCook

/-!
# Computability — index
-/
```

The title must not name `Geb.Mathlib.`: `scripts/lint-imports.sh` rejects the
self-prefix outside an `^import` line, and a docstring title carrying it fails.

- [ ] **Step 2: Create the content module with its header, imports and signature**

Create `Geb/Mathlib/Computability/BellantoniCook.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.PFunctor.Slice.W
public import Geb.Mathlib.Data.PFunctor.Univariate.Finitary
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The function class `B` of Bellantoni and Cook

The syntax of the function class `B` and its interpretation, following
[HeraudNowak2011] § 3.2. Terms of `B` are built from a constant zero,
projections, two successors, a predecessor and a conditional, and are closed
under a composition and a recursion that distinguish normal from safe
argument positions; the distinction is what bounds the growth rate of the
definable functions.

The class defined here is the reformulation of § 3.2, not the class of
[BellantoniCook1992]. Two differences: the conditional takes four safe
arguments and branches three ways, on the empty, odd and even bitstrings,
where the original branches two ways on parity and treats the empty
bitstring as even; and the base case of the recursion is the empty
bitstring, where the original's is every bitstring denoting zero.

The two sources transpose the conditional's last two safe arguments. The
order here follows the authors' Coq development, that being the artifact
against which the paper's theorems were machine-checked.

## Main definitions

* `BellantoniCook.Shape` — the seven constructor forms, with their arities
  as parameters.
* `BellantoniCook.Direction` — the subterm positions of a shape.
* `BellantoniCook.rc` — the arity each subterm position must carry.
* `BellantoniCook.q` — the arity a shape produces.
* `BellantoniCook.sig` — the signature, as a slice polynomial functor over
  `ℕ × ℕ`.
* `BellantoniCook.BC` — an expression of `B`: a `sig`-tree whose every node
  respects `rc`.
* `BellantoniCook.BC.arity` — its pair of normal and safe arities.
* `BellantoniCook.BCOf` — the expressions of a given arity pair.
* `BellantoniCook.Sem` — the meaning of an arity pair: a function of a
  normal and a safe environment.
* `BellantoniCook.transport` — transport of a meaning along an equality of
  arity pairs.
* `BellantoniCook.evalRec` — the recursion on the consumed bitstring.
* `BellantoniCook.evalValue` — the meaning of one node from its children's.
* `BellantoniCook.evalStep` — `evalValue` as a slice algebra.
* `BellantoniCook.BC.eval` — the interpretation, by the slice W-type's
  eliminator.

## Implementation notes

This repository expresses all recursion through recursors, admitting
neither a self-referential `inductive` nor a self-calling `def`, so the
arity-indexed syntax is the slice W-type of `sig` and the interpretation is
one application of `SlicePFunctor.W.elim`. `Shape` is itself non-recursive
and so is the shape set of a `PFunctor`, not a datatype the rule reaches.

`evalValue` is separate from `evalStep` because the match on `Shape` must
generalize the compatibility hypothesis, which arrives bundled in
`SliceDomPFunctor.Obj`. A child's meaning carries the index it was built at
rather than the index `rc` prescribes, equal but not definitionally so;
`transport` carries it across, with the motive of `▸` fixed once instead of
at each of the six sites.

`Direction`, `rc` and `q` are `@[reducible]`. Instance search does not
delta-reduce a semireducible definition, and every numeral in `evalValue`
elaborates against `Fin (q a).1` or `Direction a`.

`finEnumFin` and `finEnumCompDirection` are `scoped`, and hand-built:
mathlib's `FinEnum` instances depend on `Classical.choice`, which
`lake lint` rejects, and an unscoped instance at the head symbol `FinEnum
(Fin _)` would compete with `FinEnum.fin` wherever `Geb` is imported.

## References

* [HeraudNowak2011]
* [BellantoniCook1992]

## Tags

Bellantoni-Cook, polytime, implicit computational complexity, safe
recursion, W-type, polynomial functor
-/

namespace BellantoniCook

public section

/-- The seven constructor forms of `B`, each carrying its arities as
parameters: `zero` the constant empty bitstring; `proj n s i` the `i`th of
`n` normal and `s` safe variables; `succ b` the successor appending the bit
`b`; `pred` the predecessor; `cond` the four-argument conditional;
`safeRec n s` the recursion producing arity `(n + 1, s)`; and `comp n s m k`
the composition of an expression of arity `(m, k)` with `m` normal and `k`
safe argument expressions of arity `(n, 0)` and `(n, s)`. -/
inductive Shape
  | zero
  | proj (n s : ℕ) (i : Fin (n + s))
  | succ (b : Bool)
  | pred
  | cond
  | safeRec (n s : ℕ)
  | comp (n s m k : ℕ)

/-- The subterm positions of a shape. The five base forms have none;
`safeRec` has three, its base and its two step expressions; `comp` has its
head, its `m` normal arguments and its `k` safe arguments. -/
@[expose, reducible] def Direction : Shape → Type
  | .zero => Fin 0
  | .proj _ _ _ => Fin 0
  | .succ _ => Fin 0
  | .pred => Fin 0
  | .cond => Fin 0
  | .safeRec _ _ => Fin 3
  | .comp _ _ m k => Unit ⊕ Fin m ⊕ Fin k

/-- The arity each subterm position must carry: the hypotheses of the
arity relation of [HeraudNowak2011] § 3.2. -/
@[expose, reducible] def rc : (a : Shape) → Direction a → ℕ × ℕ
  | .zero, i => i.elim0
  | .proj _ _ _, i => i.elim0
  | .succ _, i => i.elim0
  | .pred, i => i.elim0
  | .cond, i => i.elim0
  | .safeRec n s, ⟨0, _⟩ => (n, s)
  | .safeRec n s, _ => (n + 1, s + 1)
  | .comp _ _ m k, .inl () => (m, k)
  | .comp n _ _ _, .inr (.inl _) => (n, 0)
  | .comp n s _ _, .inr (.inr _) => (n, s)

/-- The arity a shape produces: the conclusions of the arity relation of
[HeraudNowak2011] § 3.2. -/
@[expose, reducible] def q : Shape → ℕ × ℕ
  | .zero => (0, 0)
  | .proj n s _ => (n, s)
  | .succ _ => (0, 1)
  | .pred => (0, 1)
  | .cond => (0, 4)
  | .safeRec n s => (n + 1, s)
  | .comp n s _ _ => (n, s)

/-- The signature of `B` as a slice polynomial functor over `ℕ × ℕ`, the
index being the pair of normal and safe arities. -/
@[expose] def sig : SlicePFunctor (ℕ × ℕ) (ℕ × ℕ) where
  A := Shape
  B := Direction
  r := fun x ↦ rc x.1 x.2
  q := q

end

end BellantoniCook
```

- [ ] **Step 3: Add the import to the subtree index**

Modify `Geb/Mathlib.lean`: add `public import Geb.Mathlib.Computability` to
the import block, keeping the block alphabetically ordered as the file has it.

- [ ] **Step 4: Build and verify zero diagnostics**

Run: `lake build Geb.Mathlib.Computability Geb.Mathlib`
Expected: builds with no output beyond the progress lines. Any warning is a
failure — the package sets `weak.warningAsError = true`. Naming the index
modules rather than the content module alone is what exercises Step 1's and
Step 3's edits; a typo in either would otherwise surface only at Task 7.

- [ ] **Step 5: Verify the arity relation transcribes correctly**

Run this scratch check (do not commit it); it asserts every row of the
spec's signature table:

```bash
cat > /tmp/bc-sig-check.lean <<'EOF'
import Geb.Mathlib.Computability.BellantoniCook
open BellantoniCook
example : q .zero = (0, 0) := rfl
example : q (.proj 2 3 0) = (2, 3) := rfl
example : q (.succ true) = (0, 1) := rfl
example : q .pred = (0, 1) := rfl
example : q .cond = (0, 4) := rfl
example : q (.safeRec 1 2) = (2, 2) := rfl
example : q (.comp 1 2 3 4) = (1, 2) := rfl
example : rc (.safeRec 1 2) 0 = (1, 2) := rfl
example : rc (.safeRec 1 2) 1 = (2, 3) := rfl
example : rc (.safeRec 1 2) 2 = (2, 3) := rfl
example : rc (.comp 1 2 3 4) (.inl ()) = (3, 4) := rfl
example : rc (.comp 1 2 3 4) (.inr (.inl 0)) = (1, 0) := rfl
example : rc (.comp 1 2 3 4) (.inr (.inr 0)) = (1, 2) := rfl
EOF
lake env lean /tmp/bc-sig-check.lean; rm -f /tmp/bc-sig-check.lean
```

Expected: no output, exit 0. A non-empty output means a row of `q` or `rc`
disagrees with the spec's table; fix the definition, not the check.

- [ ] **Step 6: Commit**

```bash
jj commit -m "feat(computability): add the Bellantoni-Cook signature functor"
```

---

## Task 3: Finiteness and decidable admissibility

**Files:**

- Modify: `Geb/Mathlib/Computability/BellantoniCook.lean`

**Interfaces:**

- Consumes: `sig`, `Direction`, `Shape` from Task 2;
  `PFunctor.Finitary` from `Geb.Mathlib.Data.PFunctor.Univariate.Finitary`
- Produces:
  - `BellantoniCook.finEnumFin (n : ℕ) : FinEnum (Fin n)` — `scoped`
  - `BellantoniCook.finEnumCompDirection (m k : ℕ) :
    FinEnum (Unit ⊕ Fin m ⊕ Fin k)` — `scoped`
  - `BellantoniCook.sigFinitary : sig.toPFunctor.Finitary`

- [ ] **Step 1: Add the three instances**

Insert into `Geb/Mathlib/Computability/BellantoniCook.lean`, after `sig` and
inside the `public section`:

```lean
/-- A choice-free `FinEnum (Fin n)`: the cardinality is `n` and the
enumeration is the identity. `scoped`, so that it does not compete with
mathlib's `FinEnum.fin` at the same head symbol outside this namespace. -/
scoped instance finEnumFin (n : ℕ) :
    FinEnum (Fin n) where
  card := n
  equiv := Equiv.refl _
  decEq := inferInstance

/-- A choice-free `FinEnum` for `comp`'s directions. `scoped`, for the same
reason as `finEnumFin`. -/
scoped instance finEnumCompDirection (m k : ℕ) :
    FinEnum (Unit ⊕ Fin m ⊕ Fin k) where
  card := 1 + (m + k)
  equiv := (Equiv.sumCongr finOneEquiv.symm finSumFinEquiv).trans finSumFinEquiv
  decEq := inferInstance

/-- Every shape has finitely many directions, which is what makes
admissibility of a `sig`-tree decidable. The branches ascribe their
instances explicitly: instance search stops at reducible transparency on the
projection `sig.B a`, so a bare `inferInstance` does not find them. -/
instance sigFinitary : sig.toPFunctor.Finitary
  | .zero => inferInstanceAs (FinEnum (Fin 0))
  | .proj _ _ _ => inferInstanceAs (FinEnum (Fin 0))
  | .succ _ => inferInstanceAs (FinEnum (Fin 0))
  | .pred => inferInstanceAs (FinEnum (Fin 0))
  | .cond => inferInstanceAs (FinEnum (Fin 0))
  | .safeRec _ _ => inferInstanceAs (FinEnum (Fin 3))
  | .comp _ _ m k => inferInstanceAs (FinEnum (Unit ⊕ Fin m ⊕ Fin k))
```

`sigFinitary` is an `instance`, not a `def`: as a `def` it does not fire for
`decidableWValid`, and it draws `Definition … of class type is
semireducible`, fatal under `weak.warningAsError`. It needs no attribute.

- [ ] **Step 2: Build**

Run: `lake build Geb.Mathlib.Computability.BellantoniCook`
Expected: builds, no output beyond progress lines.

- [ ] **Step 3: Verify the instances are choice-free**

Run:

```bash
cat > /tmp/bc-axiom-check.lean <<'EOF'
import Geb.Mathlib.Computability.BellantoniCook
#print axioms BellantoniCook.finEnumFin
#print axioms BellantoniCook.finEnumCompDirection
#print axioms BellantoniCook.sigFinitary
EOF
lake env lean /tmp/bc-axiom-check.lean; rm -f /tmp/bc-axiom-check.lean
```

Expected: `'BellantoniCook.finEnumFin' does not depend on any axioms`, and
`[propext, Quot.sound]` for the other two. **`Classical.choice` anywhere is a
failure** — it means a branch resolved through a mathlib instance instead of
the two above.

- [ ] **Step 4: Commit**

```bash
jj commit -m "feat(computability): add choice-free finiteness for the signature"
```

---

## Task 4: The syntax and the semantics

**Files:**

- Modify: `Geb/Mathlib/Computability/BellantoniCook.lean`

**Interfaces:**

- Consumes: `sig`, `Shape`, `Direction`, `rc`, `q` from Task 2;
  `sigFinitary` from Task 3; `SlicePFunctor.W`, `.wIndex`, `W.elim` from
  `Geb.Mathlib.Data.PFunctor.Slice.W`
- Produces:
  - `BellantoniCook.BC : Type`
  - `BellantoniCook.BC.arity : BC → ℕ × ℕ`
  - `BellantoniCook.BCOf (n s : ℕ) : Type`
  - `BellantoniCook.Sem : ℕ × ℕ → Type`
  - `BellantoniCook.transport {i j : ℕ × ℕ} (h : i = j) (v : Sem i) : Sem j`
  - `BellantoniCook.evalRec {n s : ℕ} (g : Sem (n, s))
    (h₀ h₁ : Sem (n + 1, s + 1)) : List Bool → Sem (n, s)`
  - `BellantoniCook.evalValue : (a : Shape) →
    (c : Direction a → Σ i, Sem i) → (∀ b, (c b).1 = rc a b) → Sem (q a)`
  - `BellantoniCook.evalStep :
    sig.toSliceDomPFunctor.Obj (Sigma.fst (β := Sem)) → Σ i, Sem i`
  - `BellantoniCook.BC.eval : BC → Σ i, Sem i`

- [ ] **Step 1: Add the syntax**

Insert after `sigFinitary`, inside the `public section`:

```lean
/-- An expression of `B`: a `sig`-tree every node of which carries children
at the indices `rc` prescribes. -/
@[expose] def BC : Type := sig.W

/-- The arity pair of an expression: its normal and safe arities. -/
@[expose] def BC.arity : BC → ℕ × ℕ := sig.wIndex

/-- The expressions of arity `(n, s)`, which is the arity relation of
[HeraudNowak2011] § 3.2 as a type rather than a side condition. -/
@[expose] def BCOf (n s : ℕ) : Type := { e : BC // e.arity = (n, s) }
```

- [ ] **Step 2: Add the semantic family and the transport**

```lean
/-- The meaning of an arity pair: a function of a normal and a safe
environment, each a tuple of bitstrings, returning a bitstring. -/
@[expose] def Sem : ℕ × ℕ → Type :=
  fun i ↦ (Fin i.1 → List Bool) → (Fin i.2 → List Bool) → List Bool

/-- Transport of a meaning along an equality of arity pairs. Named so that
the motive of `▸` is fixed once rather than inferred at each use in
`evalValue`. -/
@[expose] def transport {i j : ℕ × ℕ} (h : i = j) (v : Sem i) : Sem j := h ▸ v
```

- [ ] **Step 3: Add the recursion on the consumed bitstring**

```lean
/-- The recursion `safeRec` performs on its first normal argument, by
`List.rec`. The base case is the empty bitstring; a step consumes the low
bit `b`, passes the remaining bitstring `v` as the new first normal
argument, and passes the recursive value in safe position. -/
@[expose] def evalRec {n s : ℕ} (g : Sem (n, s))
    (h₀ h₁ : Sem (n + 1, s + 1)) : List Bool → Sem (n, s) :=
  List.rec g (fun b v ih x y ↦
    (if b then h₁ else h₀) (Fin.cons v x) (Fin.cons (ih x y) y))
```

- [ ] **Step 4: Add the algebra**

```lean
/-- The meaning of one node, from its children's meanings and the proof that
each child's index is the one `rc` prescribes. A separate definition from
`evalStep` because the match on `Shape` must generalize that proof.

`cond` reads its first safe argument and returns the second, third or fourth
according as it is empty, odd or even — the ordering of the authors' Coq
development. `comp` applies its head's meaning to the normal arguments'
meanings, each in the empty safe environment, and to the safe arguments'. -/
@[expose] def evalValue : (a : Shape) → (c : Direction a → Σ i, Sem i) →
    (∀ b, (c b).1 = rc a b) → Sem (q a)
  | .zero, _, _ => fun _ _ ↦ []
  | .proj _ _ i, _, _ => fun x y ↦ Fin.append x y i
  | .succ b, _, _ => fun _ y ↦ b :: y 0
  | .pred, _, _ => fun _ y ↦ (y 0).tail
  | .cond, _, _ => fun _ y ↦
      match y 0 with
      | [] => y 1
      | true :: _ => y 2
      | false :: _ => y 3
  | .safeRec _ _, c, h => fun x y ↦
      evalRec (transport (h 0) (c 0).2) (transport (h 1) (c 1).2)
        (transport (h 2) (c 2).2) (x 0) (Fin.tail x) y
  | .comp _ _ _ _, c, h => fun x y ↦
      transport (h (.inl ())) (c (.inl ())).2
        (fun i ↦ transport (h (.inr (.inl i))) (c (.inr (.inl i))).2 x Fin.elim0)
        (fun j ↦ transport (h (.inr (.inr j))) (c (.inr (.inr j))).2 x y)

/-- `evalValue` as an algebra for `sig` in the slice over `ℕ × ℕ`. Returning
the shape's own output index as the first component makes the eliminator's
coherence obligation hold by `rfl`. -/
@[expose] def evalStep :
    sig.toSliceDomPFunctor.Obj (Sigma.fst (β := Sem)) → Σ i, Sem i :=
  fun z ↦ ⟨sig.q z.1.1,
    evalValue z.1.1 z.1.2
      ((sig.toSliceDomPFunctor.compatible_iff _ z.1.1 z.1.2).mp z.2)⟩

/-- The interpretation of an expression: its arity pair together with its
meaning at that pair, by the slice W-type's eliminator. -/
@[expose] def BC.eval : BC → Σ i, Sem i :=
  SlicePFunctor.W.elim sig (Σ i, Sem i) (Sigma.fst (β := Sem)) evalStep rfl
```

Note `SlicePFunctor.W.elim sig …`, not `sig.W.elim …`: `sig.W` is a type,
not a term, so field notation does not chain through it.

- [ ] **Step 5: Build**

Run: `lake build Geb.Mathlib.Computability.BellantoniCook`
Expected: builds, no output beyond progress lines. In particular no
`failed to synthesize instance of type class OfNat …`, which would mean
`Direction`, `rc` or `q` lost its `@[reducible]`.

- [ ] **Step 6: Verify the axioms and run the linters**

Run:

```bash
cat > /tmp/bc-eval-axioms.lean <<'EOF'
import Geb.Mathlib.Computability.BellantoniCook
#print axioms BellantoniCook.BC.eval
#print axioms BellantoniCook.evalValue
#print axioms BellantoniCook.evalRec
EOF
lake env lean /tmp/bc-eval-axioms.lean; rm -f /tmp/bc-eval-axioms.lean
lake lint
scripts/lint-imports.sh
```

Expected: each line within `{propext, Quot.sound}` — some declarations
depend on fewer, which is not a failure. **`Classical.choice` anywhere is a
failure.** `lake lint` prints
`Running linter on specified modules: [Geb]` and
`-- Linting passed for Geb.`; `lint-imports.sh` prints
`lint-imports.sh: clean (N file(s) checked)`.

- [ ] **Step 7: Commit**

```bash
jj commit -m "feat(computability): add the Bellantoni-Cook syntax and semantics"
```

---

## Task 5: The test module

**Files:**

- Create: `GebTests/Mathlib/Computability.lean`
- Create: `GebTests/Mathlib/Computability/BellantoniCook.lean`
- Modify: `GebTests/Mathlib.lean`

**Interfaces:**

- Consumes: everything Task 4 produces, plus
  `SlicePFunctor.decidableWValid` from
  `Geb.Mathlib.Data.PFunctor.Slice.Decidable`
- Produces: nothing later tasks depend on

- [ ] **Step 1: Create the test directory index**

Create `GebTests/Mathlib/Computability.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import GebTests.Mathlib.Computability.BellantoniCook

/-!
# Computability tests — index
-/
```

- [ ] **Step 2: Write the test module — header, terms, and the first two assertions**

Create `GebTests/Mathlib/Computability/BellantoniCook.lean`:

```lean
/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.Computability.BellantoniCook
import Geb.Mathlib.Data.PFunctor.Slice.Decidable

/-!
# Worked expressions of the Bellantoni-Cook class

The `plus` and `mult` of [HeraudNowak2011] § 3.2, a recursion whose two step
expressions differ, four single-node expressions, and one inadmissible raw
tree. Each expression is built in two steps — a raw tree bound as its own
definition, then the admissible expression — because an inline `WType.mk`
application blocks the instance search that `decide` needs.

`plus` and `mult` are transcribed with the arities of the authors' Coq
development. The composition superscripts printed in § 3.2's `mult` are
`plus`'s and do not satisfy the paper's own arity relation.

## Main statements

The thirteen assertions below: twelve expected outputs of `BC.eval`, and one
inadmissible tree.

## References

* [HeraudNowak2011]

## Tags

Bellantoni-Cook, polytime, safe recursion
-/

set_option linter.privateModule false

open BellantoniCook

/-- The children of a `comp` node, in the order `Direction` gives them: the
head, then the normal arguments, then the safe arguments. -/
def compChildren {m k : ℕ} (h : sig.toPFunctor.W)
    (gN : Fin m → sig.toPFunctor.W) (gS : Fin k → sig.toPFunctor.W) :
    Unit ⊕ Fin m ⊕ Fin k → sig.toPFunctor.W :=
  Sum.elim (fun _ ↦ h) (Sum.elim gN gS)

/-- The step expression of `plus`: the successor appending `true`, applied
to the recursive value. -/
def plusStepRaw : sig.toPFunctor.W :=
  WType.mk (.comp 1 2 0 1)
    (compChildren (WType.mk (.succ true) Fin.elim0) Fin.elim0
      ![WType.mk (.proj 1 2 1) Fin.elim0])

/-- The step expression of `plus`, admissible. -/
def plusStep : BC := ⟨plusStepRaw, by decide⟩

/-- `plus`, of arity `(1, 1)`: it prepends one `true` per bit of its normal
argument to its safe argument. -/
def plusRaw : sig.toPFunctor.W :=
  WType.mk (.safeRec 0 1)
    ![WType.mk (.proj 0 1 0) Fin.elim0, plusStep.val, plusStep.val]

/-- `plus`, admissible. -/
def plus : BC := ⟨plusRaw, by decide⟩

/-- The base expression of `mult`: the constant empty bitstring at
arity `(1, 0)`. -/
def multBaseRaw : sig.toPFunctor.W :=
  WType.mk (.comp 1 0 0 0)
    (compChildren (WType.mk .zero Fin.elim0) Fin.elim0 Fin.elim0)

/-- The base expression of `mult`, admissible. -/
def multBase : BC := ⟨multBaseRaw, by decide⟩

/-- The step expression of `mult`: `plus` of the second normal argument and
the recursive value. -/
def multStepRaw : sig.toPFunctor.W :=
  WType.mk (.comp 2 1 1 1)
    (compChildren plus.val ![WType.mk (.proj 2 0 1) Fin.elim0]
      ![WType.mk (.proj 2 1 2) Fin.elim0])

/-- The step expression of `mult`, admissible. -/
def multStep : BC := ⟨multStepRaw, by decide⟩

/-- `mult`, of arity `(2, 0)`: it produces one `true` per pair of bits of
its two normal arguments. -/
def multRaw : sig.toPFunctor.W :=
  WType.mk (.safeRec 1 0) ![multBase.val, multStep.val, multStep.val]

/-- `mult`, admissible. -/
def mult : BC := ⟨multRaw, by decide⟩

/-- `plus` at its declared arity. Elaborating this is exactly the assertion
that `BC.arity plus` is `(1, 1)`. -/
def plusOf : BCOf 1 1 := ⟨plus, rfl⟩

/-- `mult` at its declared arity. -/
def multOf : BCOf 2 0 := ⟨mult, rfl⟩

/-- `plus` on an empty normal argument returns its safe argument. -/
theorem eval_plus_nil : (BC.eval plus).2 ![[]] ![[false]] = [false] := rfl

/-- `plus` prepends one `true` per bit of its normal argument. -/
theorem eval_plus_cons :
    (BC.eval plus).2 ![[true, true]] ![[false]] = [true, true, false] := rfl
```

- [ ] **Step 3: Build and check the first two assertions before writing the rest**

Run: `lake build GebTests.Mathlib.Computability.BellantoniCook`
Expected: builds. A `Not a definitional equality` here means a term or a
semantic clause is wrong; fix it before continuing, since every later
assertion rests on the same clauses.

- [ ] **Step 4: Add the remaining terms and assertions**

Append to `GebTests/Mathlib/Computability/BellantoniCook.lean`:

```lean
/-- `mult` produces one `true` per pair of bits of its two normal
arguments. -/
theorem eval_mult :
    (BC.eval mult).2 ![[true, true], [true, true, true]] ![] =
      List.replicate 6 true := rfl

/-- A recursion whose two step expressions differ: the `false` branch
returns the remaining bitstring, the `true` branch recurses. Without it no
assertion here would distinguish the two step expressions, `plus` and `mult`
passing the same expression as both. -/
def branchRecRaw : sig.toPFunctor.W :=
  WType.mk (.safeRec 0 0)
    ![WType.mk .zero Fin.elim0, WType.mk (.proj 1 1 0) Fin.elim0,
      WType.mk (.proj 1 1 1) Fin.elim0]

/-- The discriminating recursion, admissible. -/
def branchRec : BC := ⟨branchRecRaw, by decide⟩

/-- On a `false`-headed argument the `false` branch returns the remaining
bitstring. Arguments of length one do not discriminate the branches: both
readings return the empty bitstring. -/
theorem eval_branchRec_false :
    (BC.eval branchRec).2 ![[false, true]] ![] = [true] := rfl

/-- On a `true`-headed argument the `true` branch recurses. -/
theorem eval_branchRec_true :
    (BC.eval branchRec).2 ![[true, true]] ![] = [] := rfl

/-- The predecessor as a single node. -/
def predTermRaw : sig.toPFunctor.W := WType.mk .pred Fin.elim0

/-- The predecessor, admissible. -/
def predTerm : BC := ⟨predTermRaw, by decide⟩

/-- The predecessor of the empty bitstring is the empty bitstring. -/
theorem eval_predTerm_nil : (BC.eval predTerm).2 ![] ![[]] = [] := rfl

/-- The predecessor drops the low bit. -/
theorem eval_predTerm_cons :
    (BC.eval predTerm).2 ![] ![[true, false]] = [false] := rfl

/-- The conditional as a single node. -/
def condTermRaw : sig.toPFunctor.W := WType.mk .cond Fin.elim0

/-- The conditional, admissible. -/
def condTerm : BC := ⟨condTermRaw, by decide⟩

/-- On the empty bitstring the conditional returns its second safe
argument. -/
theorem eval_condTerm_empty :
    (BC.eval condTerm).2 ![] ![[], [false], [true], [true, true]] = [false] :=
  rfl

/-- On an odd bitstring it returns its third. The authors' Coq development
assigns the third to the odd case and the fourth to the even case; § 3.2
prints them the other way round. -/
theorem eval_condTerm_odd :
    (BC.eval condTerm).2 ![] ![[true], [false], [true], [true, true]] =
      [true] := rfl

/-- On an even bitstring it returns its fourth. -/
theorem eval_condTerm_even :
    (BC.eval condTerm).2 ![] ![[false], [false], [true], [true, true]] =
      [true, true] := rfl

/-- A projection onto a normal variable, as a single node. -/
def projNTermRaw : sig.toPFunctor.W := WType.mk (.proj 1 1 0) Fin.elim0

/-- The normal projection, admissible. -/
def projNTerm : BC := ⟨projNTermRaw, by decide⟩

/-- The normal projection returns the normal argument. -/
theorem eval_projNTerm :
    (BC.eval projNTerm).2 ![[true]] ![[false]] = [true] := rfl

/-- A projection onto a safe variable, as a single node. Together with
`projNTerm` this separates the two halves of `Fin.append`, which a
mistranscribed index would silently permute. -/
def projSTermRaw : sig.toPFunctor.W := WType.mk (.proj 1 1 1) Fin.elim0

/-- The safe projection, admissible. -/
def projSTerm : BC := ⟨projSTermRaw, by decide⟩

/-- The safe projection returns the safe argument. -/
theorem eval_projSTerm :
    (BC.eval projSTerm).2 ![[true]] ![[false]] = [false] := rfl

/-- `plusStepRaw` with its safe argument replaced by an expression of arity
`(2, 0)` where the signature demands `(1, 2)`. -/
def badRaw : sig.toPFunctor.W :=
  WType.mk (.comp 1 2 0 1)
    (compChildren (WType.mk (.succ true) Fin.elim0) Fin.elim0
      ![WType.mk (.proj 2 0 1) Fin.elim0])

/-- The inadmissible tree is rejected, so admissibility is not vacuous. -/
theorem wValid_badRaw_eq_false : decide (sig.WValid badRaw) = false := rfl
```

- [ ] **Step 5: Add the import to the test subtree index**

Modify `GebTests/Mathlib.lean`: add `import GebTests.Mathlib.Computability`,
in that file's existing plain-`import` form, keeping the block ordered.

- [ ] **Step 6: Build the tests**

Run: `lake build GebTests GebTests.Mathlib.Computability`
Expected: builds with no output beyond progress lines. The second target
exercises Steps 1 and 5, which the first does not reach: `GebTests` imports
the content module directly, not through the index.

- [ ] **Step 7: Verify the assertions discriminate**

The assertions must fail when the semantics is wrong. Check the three
clauses least covered elsewhere, restoring the file after each:

```bash
# 1. Transpose the two step expressions in evalValue's safeRec clause:
#    swap `(transport (h 1) (c 1).2)` and `(transport (h 2) (c 2).2)`.
lake build GebTests
# Expected: exactly eval_branchRec_false and eval_branchRec_true fail.
jj restore Geb/Mathlib/Computability/BellantoniCook.lean

# 2. Replace evalValue's `.zero` clause body with `fun _ _ ↦ [true]`.
lake build GebTests
# Expected: eval_mult and eval_branchRec_true fail — `zero` is the base
# child of branchRec as well as the head of multBase.
jj restore Geb/Mathlib/Computability/BellantoniCook.lean

# 3. Replace evalValue's `.succ` clause entirely with
#      | .succ _b, _, _ => fun _ y ↦ y 0
#    Renaming the binder to `_b` is required: dropping the bit while
#    leaving `b` bound fails the library build with
#    `Variable name 'b' is not explicitly referenced`, so the tests
#    would never be reached.
lake build GebTests
# Expected: eval_plus_cons and eval_mult fail.
jj restore Geb/Mathlib/Computability/BellantoniCook.lean
```

If any perturbation leaves the build green, the corresponding clause is
untested — stop and report it rather than proceeding.

- [ ] **Step 8: Run the test-side linters**

Run: `lake lint -- GebTests` then `scripts/lint-imports.sh`
Expected: `lake lint -- GebTests` prints three lines —
`Running linter on specified modules: [Geb, GebTests]`, then
`-- Linting passed for Geb.` and `-- Linting passed for GebTests.`; the
extra argument appends to `lintDriverArgs`, it does not replace it.
`scripts/lint-imports.sh` prints `lint-imports.sh: clean (N file(s)
checked)`.

- [ ] **Step 9: Commit**

```bash
jj commit -m "test(computability): add worked Bellantoni-Cook expressions"
```

---

## Task 6: Documentation

**Files:**

- Modify: `docs/references.bib`
- Modify: `docs/references.md`
- Modify: `docs/index.md`
- Modify: `TODO.md`

**Interfaces:**

- Consumes: the declaration names from Tasks 2-4
- Produces: nothing later tasks depend on

- [ ] **Step 1: Add the two bibliography entries**

Insert into `docs/references.bib` beside the implicit-complexity entries
already there (`Leivant1999`, `DalLagoMartiniZorzi2010`,
`AvanziniDalLago2018`), which is where the file groups this subject. Align
the `=` as the neighbouring entries do:

```bibtex
@inproceedings{HeraudNowak2011,
  author        = {H{\'e}raud, Sylvain and Nowak, David},
  title         = {A Formalization of Polytime Functions},
  booktitle     = {Interactive Theorem Proving (ITP 2011)},
  series        = {Lecture Notes in Computer Science},
  volume        = {6898},
  pages         = {119--134},
  publisher     = {Springer},
  year          = {2011},
  doi           = {10.1007/978-3-642-22863-6_11},
  eprint        = {1102.5495},
  archivePrefix = {arXiv},
  primaryClass  = {cs.CC},
  note          = {This repository cites the arXiv version's section and
                   page numbering.},
}

@article{BellantoniCook1992,
  author        = {Bellantoni, Stephen and Cook, Stephen},
  title         = {A new recursion-theoretic characterization of the
                   polytime functions},
  journal       = {Computational Complexity},
  volume        = {2},
  number        = {2},
  pages         = {97--110},
  year          = {1992},
  doi           = {10.1007/BF01201998},
}
```

- [ ] **Step 2: Add the reference-implementation pointer**

Add to `docs/references.md` § Computability:

```markdown
- [davidnowak/bellantonicook](https://github.com/davidnowak/bellantonicook)
  — the Coq development accompanying [HeraudNowak2011], at commit
  `1f03b9296104646ddc2b2b4b12e35a6619c17a99`. Licensed CeCILL; no code is
  taken from it.
```

- [ ] **Step 3: Add the docs/index.md bullet**

Add to `docs/index.md` § Implemented content, immediately after the bullet
for `Geb/Mathlib/Data/PFunctor/Slice/Decidable.lean` — the last of the
`Slice/` bullets, and the module this one is nearest in subject:

```markdown
- `Geb/Mathlib/Computability/BellantoniCook.lean` — the function class `B`
  of [HeraudNowak2011] § 3.2: its arity relation as a `SlicePFunctor` over
  `ℕ × ℕ`, its syntax as that functor's slice W-type, and its semantics by
  the W-type's eliminator. Depends on
  `Geb.Mathlib.Data.PFunctor.Slice.W` and
  `Geb.Mathlib.Data.PFunctor.Univariate.Finitary`. Every declaration of the
  module has axioms within `propext` and `Quot.sound`; `sig` and
  `finEnumFin` have none.
```

- [ ] **Step 4: Add the TODO.md subsection**

Add as the last `###` subsection of `## Next up`, in the form the
neighbouring subsections use:

```markdown
### Bellantoni-Cook

Three items, in dependency order, over
`Geb/Mathlib/Computability/BellantoniCook.lean`.

1. `MultiPoly`, the multivariate polynomial library of the reference
   development. Required by its `BC_to_Cobham.v:2`, by its
   `Cobham_to_BC.v:2`, and by Proposition 2, whose statement
   `polymax_bounding` (`BC.v:1128`) is over `poly_BC` (`:1075`), built from
   `pcst`, `pproj`, `pplus`, `pmult`, `pcomp`, `pshift` and `pplusl`.
   Returns the polynomial apparatus items 2 and 3 are stated over.
2. Proposition 2, the polymax bounding of `B`. Depends on 1. Returns the
   length bound the translation of item 3 requires.
3. Cobham's class and the translations of Theorems 1 and 2. Depends on 1
   and 2. Returns the characterization of the polynomial-time functions,
   and is the consumer that justifies the definitions already committed.
```

- [ ] **Step 5: Add the four trigger entries**

Add as the last four bullets of `## Triggers (do when condition fires)`, in
that section's `- **Bold title**: …` form:

```markdown
- **A workstream needs programmable building blocks for terms of `B`**:
  port the derived function library of the reference development's
  `BCLib.v`, which depends only on the syntax and semantics already
  committed.
- **A second consumer of `BellantoniCook.finEnumFin` or
  `finEnumCompDirection` appears**: move them to
  `Geb/Mathlib/Data/FinEnum.lean`, the repository's home for choice-free
  `FinEnum` support. They are `scoped` in
  `Geb/Mathlib/Computability/BellantoniCook.lean`.
- **A consumer needs `DecidableEq` or `Repr` for `BellantoniCook.BC`**:
  derive them on `Shape` and lift along `sig.W`'s subtype.
- **A workstream needs the polytime checker of [HeraudNowak2011] as a
  term-level artifact**: add an untyped `Ast` and
  `check : Ast → Option ((n s : ℕ) × BellantoniCook.BCOf n s)` over
  `SlicePFunctor.decidableWValid`.
```

- [ ] **Step 6: Regenerate the tables of contents and lint**

Run:

```bash
doctoc --update-only .
markdownlint-cli2 '**/*.md'
```

Expected: `Everything is OK.` and `Summary: 0 issues in 0 files`. `TODO.md`
carries a doctoc TOC and gains a heading, so it will change; commit that
change with the rest.

- [ ] **Step 7: Commit**

```bash
jj commit -m "doc: record the Bellantoni-Cook module and its follow-on work"
```

---

## Task 7: The pre-push gate

**Files:**

- Modify: none expected

**Interfaces:**

- Consumes: everything above
- Produces: evidence that the branch is shippable

- [ ] **Step 1: Run the full checklist**

Run: `scripts/pre-push.sh`
Expected: every step passes and the script exits 0.

`lake shake` may print a `PANIC at Option.get!` trace from
`Lake.Shake.visitModule` when the first module under a new
`GebTests/Mathlib/<Dir>/` appears. It exits 0 when it occurs and reproduces
with an unrelated control module at the same path, so it is a shake artifact
rather than a property of this branch. A non-zero exit is a real failure.

- [ ] **Step 2: Confirm the imports are minimal**

Run: `lake shake --add-public --keep-prefix Geb GebTests`
Expected: the two new modules are **absent** from the reported file list.
The presence of either means it names `Mathlib.Data.Fin.Tuple.Basic` or
`Mathlib.Data.Fin.VecNotation`; remove the import, since
`Mathlib.Logic.Equiv.Fin.Basic` supplies both.

The test module's declarations are module-private — it uses plain `import`
with no `public section` — so they cannot be inspected by `#print axioms`
from another file. `lake lint -- GebTests`, which Step 1 already ran, is what
enforces the axiom budget over them: it runs `GebMeta.detectNonstandardAxiom`
across the whole `GebTests` environment, private declarations included.

- [ ] **Step 3: Commit only if the gate changed something**

If the checklist regenerated a TOC or reformatted anything:

```bash
jj commit -m "chore: satisfy the pre-push checklist for the Bellantoni-Cook branch"
```

Otherwise skip — a clean gate leaves no change to commit.

---

## Task 8: Remove the spec and the plan

**Files:**

- Delete: `docs/superpowers/specs/2026-08-04-bellantoni-cook-design.md`
- Delete: `docs/superpowers/plans/2026-08-04-bellantoni-cook.md`

**Interfaces:**

- Consumes: nothing
- Produces: a branch whose working tree carries only persistent content

CONTRIBUTING.md § Concern shape: specs and plans record how the current
state was reached, not what it is, so they belong in history and not on an
active branch. They remain reachable in the commits of Task 1.

- [ ] **Step 1: Delete both files**

```bash
rm docs/superpowers/specs/2026-08-04-bellantoni-cook-design.md
rm docs/superpowers/plans/2026-08-04-bellantoni-cook.md
```

- [ ] **Step 2: Confirm nothing else changed**

Run: `jj status`
Expected: exactly two lines, both `D`.

- [ ] **Step 3: Re-check the Markdown**

The removal touches no `.lean` file, so the full checklist of Task 7 need
not run again; only its Markdown steps can be affected.

```bash
doctoc --dryrun --update-only .
markdownlint-cli2 '**/*.md'
```

Expected: `Everything is OK.` and `Summary: 0 issues in 0 files`.

- [ ] **Step 4: Commit**

```bash
jj commit -m "doc: remove the Bellantoni-Cook spec and plan"
```

- [ ] **Step 5: Advance the bookmark**

```bash
jj bookmark set feat/bellantoni-cook -r @-
```

Run: `jj log -r 'main..feat/bellantoni-cook'`
Expected: eight or nine commits — spec, plan, three library, tests, docs,
the removal, and the gate's only if it had something to commit.

**Do not push.** AGENTS.md § No `jj git push` without user line-by-line
review: every push, including a first creation, waits on the user reading
the diff.
