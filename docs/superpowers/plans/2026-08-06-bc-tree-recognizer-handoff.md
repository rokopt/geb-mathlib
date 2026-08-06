# Bellantoni-Cook tree recognizer — measured Lean

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Purpose and lifespan](#purpose-and-lifespan)
- [The four expressions](#the-four-expressions)
- [An inadmissible route for the guard](#an-inadmissible-route-for-the-guard)
- [The correctness proof](#the-correctness-proof)
- [The spelling experiment](#the-spelling-experiment)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Purpose and lifespan

The expressions and proof recorded here were built and run during the
brainstorming phase, to establish the § Verification evidence claims of
`2026-08-06-bc-tree-recognizer-design.md`. They lived in probe modules
under `GebTests/Mathlib/`, which is upstream-eligible and no place for
scratch code, so the modules were removed and their content is preserved
here instead.

This file is transient in the sense of CONTRIBUTING.md § Concern shape:
it is removed in the same commit as the spec and the plan, before the
segment merges. Its content is reference material for the
implementation, not a description of what the repository contains.

Nothing here is a specification. Where this file and the design spec
disagree, the spec governs.

## The four expressions

Common scaffolding. `compChildren` orders a `comp` node's children as
`Direction` gives them.

```lean
def compChildren {m k : ℕ} (h : sig.toPFunctor.W)
    (gN : Fin m → sig.toPFunctor.W) (gS : Fin k → sig.toPFunctor.W) :
    Unit ⊕ Fin m ⊕ Fin k → sig.toPFunctor.W :=
  Sum.elim (fun _ ↦ h) (Sum.elim gN gS)

/-- The empty bitstring at an arbitrary arity. -/
def zeroAt (n s : ℕ) : sig.toPFunctor.W :=
  WType.mk (.comp n s 0 0)
    (compChildren (WType.mk .zero Fin.elim0) Fin.elim0 Fin.elim0)

/-- The one-bit string `[true]` at an arbitrary arity. -/
def oneAt (n s : ℕ) : sig.toPFunctor.W :=
  WType.mk (.comp n s 0 1)
    (compChildren (WType.mk (.succ true) Fin.elim0) Fin.elim0 ![zeroAt n s])
```

`count`, of arity `(1, 0)`, returning the stack depth in unary.

```lean
def incRaw : sig.toPFunctor.W :=
  WType.mk (.comp 1 1 0 1)
    (compChildren (WType.mk (.succ true) Fin.elim0) Fin.elim0
      ![WType.mk (.proj 1 1 1) Fin.elim0])

def decRaw : sig.toPFunctor.W :=
  WType.mk (.comp 1 1 0 1)
    (compChildren (WType.mk .pred Fin.elim0) Fin.elim0
      ![WType.mk (.proj 1 1 1) Fin.elim0])

def countRaw : sig.toPFunctor.W :=
  WType.mk (.safeRec 0 0) ![WType.mk .zero Fin.elim0, incRaw, decRaw]

def count : BC := ⟨countRaw, by decide⟩
def countOf : BCOf 1 0 := ⟨count, rfl⟩
```

`noUnderflow`, of arity `(1, 0)`. The guard reaches `count` as the head
of an inner `comp 1 1 1 0`, whose head arity requirement is `(1, 0)`,
with the projection as its one normal child.

Every child family below is written `fun _ ↦ …`, not `![…]`. That is
device 3 of the spec's § Unfolding and it is what makes the `true`-step
lemma definitional; see § The spelling experiment.

```lean
def guardRaw : sig.toPFunctor.W :=
  WType.mk (.comp 1 1 0 1)
    (compChildren (WType.mk .pred Fin.elim0) Fin.elim0
      (fun _ ↦ WType.mk (.comp 1 1 1 0)
          (compChildren countRaw (fun _ ↦ WType.mk (.proj 1 0 0) Fin.elim0)
            (fun _ ↦ zeroAt 1 1))))

def nuTrueStep : sig.toPFunctor.W :=
  WType.mk (.comp 1 1 0 4)
    (compChildren (WType.mk .cond Fin.elim0) Fin.elim0
      ![guardRaw, zeroAt 1 1, WType.mk (.proj 1 1 1) Fin.elim0,
        WType.mk (.proj 1 1 1) Fin.elim0])

def noUnderflowRaw : sig.toPFunctor.W :=
  WType.mk (.safeRec 0 0)
    ![oneAt 0 0, WType.mk (.proj 1 1 1) Fin.elim0, nuTrueStep]

def noUnderflow : BC := ⟨noUnderflowRaw, by decide⟩
def noUnderflowOf : BCOf 1 0 := ⟨noUnderflow, rfl⟩
```

`eqOne`, of arity `(0, 1)`, and `isTree`, of arity `(1, 0)`.

```lean
def eqOneInner : sig.toPFunctor.W :=
  WType.mk (.comp 0 1 0 4)
    (compChildren (WType.mk .cond Fin.elim0) Fin.elim0
      ![WType.mk (.comp 0 1 0 1)
          (compChildren (WType.mk .pred Fin.elim0) Fin.elim0
            ![WType.mk (.proj 0 1 0) Fin.elim0]),
        oneAt 0 1, zeroAt 0 1, zeroAt 0 1])

def eqOneRaw : sig.toPFunctor.W :=
  WType.mk (.comp 0 1 0 4)
    (compChildren (WType.mk .cond Fin.elim0) Fin.elim0
      ![WType.mk (.proj 0 1 0) Fin.elim0, zeroAt 0 1, eqOneInner, eqOneInner])

def eqOne : BC := ⟨eqOneRaw, by decide⟩
def eqOneOf : BCOf 0 1 := ⟨eqOne, rfl⟩

def isTreeRaw : sig.toPFunctor.W :=
  WType.mk (.comp 1 0 0 4)
    (compChildren (WType.mk .cond Fin.elim0) Fin.elim0
      ![noUnderflowRaw, zeroAt 1 0,
        WType.mk (.comp 1 0 0 1) (compChildren eqOneRaw Fin.elim0 ![countRaw]),
        WType.mk (.comp 1 0 0 1) (compChildren eqOneRaw Fin.elim0 ![countRaw])])

def isTree : BC := ⟨isTreeRaw, by decide⟩
def isTreeOf : BCOf 1 0 := ⟨isTree, rfl⟩
```

Two properties of this form that cost an iteration each. The
`⟨WType.mk …, by decide⟩` form does not elaborate — instance search fails
against an inline `WType.mk` application — so every raw tree is bound as
its own `def` first. And `cond`'s even branch is dead in `eqOneInner`,
since a non-empty unary numeral always has head `true`, but it must still
be supplied.

## An inadmissible route for the guard

A negative control. It is not the shape the spec's § The expressions
rules out by arity: that shape puts `count` in a safe-child slot, whose
requirement is `(1, 1)`, whereas the tree below makes `count` the head of
an inner `comp 1 1 0 1`, whose head requirement is `(0, 1)`. Both are
inadmissible; only the first tests the arity argument.

```lean
def guardSafeRaw : sig.toPFunctor.W :=
  WType.mk (.comp 1 1 0 1)
    (compChildren (WType.mk .pred Fin.elim0) Fin.elim0
      ![WType.mk (.comp 1 1 0 1) (compChildren countRaw Fin.elim0
          ![WType.mk (.proj 1 1 0) Fin.elim0])])

theorem guardSafe_invalid : sig.wValidBool guardSafeRaw = false := rfl
```

## The correctness proof

`countS` and `nuS` ascribe the meanings at their arities, so that the
arity pair is reduced and rewriting under it typechecks. Without them the
`Sigma` projection blocks the rewrites below.

```lean
def countS : (Fin 1 → List Bool) → (Fin 0 → List Bool) → List Bool :=
  (BC.eval count).2

def nuS : (Fin 1 → List Bool) → (Fin 0 → List Bool) → List Bool :=
  (BC.eval noUnderflow).2
```

The step lemmas, all by `rfl`. Note they are stated at `Fin.cons`-shaped
environments, which is device 1 of § Unfolding.

```lean
theorem countS_nil : countS ![[]] ![] = [] := rfl

theorem countS_cons_false (v : List Bool) :
    countS ![false :: v] ![] = true :: countS ![v] ![] := rfl

theorem countS_cons_true (v : List Bool) :
    countS ![true :: v] ![] = (countS ![v] ![]).tail := rfl

theorem nuS_nil (x y : Fin 0 → List Bool) : nuS (Fin.cons [] x) y = [true] :=
  rfl

theorem nuS_step_false (v : List Bool) (x y : Fin 0 → List Bool) :
    nuS (Fin.cons (false :: v) x) y = nuS (Fin.cons v x) y := rfl

theorem nuS_step_true (v : List Bool) (x y : Fin 0 → List Bool) :
    nuS (Fin.cons (true :: v) x) y =
      (match (countS (fun _ ↦ v) (fun _ ↦ [])).tail with
       | [] => []
       | true :: _ => nuS (Fin.cons v x) y
       | false :: _ => nuS (Fin.cons v x) y) := rfl
```

The environment-normalization lemmas, device 2 of § Unfolding.

```lean
theorem countS_env (f : Fin 1 → List Bool) (g : Fin 0 → List Bool) :
    countS f g = countS ![f 0] ![] := by
  have hf : f = ![f 0] := funext fun i ↦ match i with | ⟨0, _⟩ => rfl
  have hg : g = ![] := Subsingleton.elim _ _
  conv_lhs => rw [hf, hg]

theorem nuS_env (f : Fin 1 → List Bool) (g : Fin 0 → List Bool) :
    nuS f g = nuS ![f 0] ![] := by
  have hf : f = ![f 0] := funext fun i ↦ match i with | ⟨0, _⟩ => rfl
  have hg : g = ![] := Subsingleton.elim _ _
  conv_lhs => rw [hf, hg]
```

The `count` characterization, and its form at an arbitrary environment.

```lean
theorem tail_replicate (n : ℕ) :
    (List.replicate n true).tail = List.replicate (n - 1) true := by
  cases n <;> rfl

theorem countS_eq (w : List Bool) :
    countS ![w] ![] = List.replicate (BinTree.depth w) true := by
  refine List.rec (motive := fun u ↦
    countS ![u] ![] = List.replicate (BinTree.depth u) true) rfl ?_ w
  intro b v ih
  cases b
  · rw [countS_cons_false, ih, BinTree.depth_cons_false, List.replicate_succ]
  · rw [countS_cons_true, ih, BinTree.depth_cons_true, tail_replicate]

theorem countS_apply (F : Fin 1 → List Bool) (G : Fin 0 → List Bool) :
    countS F G = List.replicate (BinTree.depth (F 0)) true := by
  rw [countS_env]; exact countS_eq _
```

The recognizer's correctness. The case split is on whether
`depth v - 1` is zero, which is what decides the `cond`'s branch.

```lean
theorem nuS_gen : ∀ (w : List Bool) (x y : Fin 0 → List Bool),
    nuS (Fin.cons w x) y = if BinTree.ok w then [true] else [] := by
  refine List.rec (motive := fun u ↦ ∀ (x y : Fin 0 → List Bool),
    nuS (Fin.cons u x) y = if BinTree.ok u then [true] else [])
    (fun x y ↦ by rw [nuS_nil]; simp) ?_
  intro b v ih x y
  cases b
  · rw [nuS_step_false, ih, BinTree.ok_cons_false]
  · rw [nuS_step_true, countS_apply, BinTree.ok_cons_true]
    simp only [tail_replicate]
    obtain (h1 | ⟨m, hm⟩) :
        BinTree.depth v - 1 = 0 ∨ ∃ m, BinTree.depth v - 1 = m + 1 := by
      rcases Nat.eq_zero_or_pos (BinTree.depth v - 1) with h | h
      · exact Or.inl h
      · exact Or.inr ⟨BinTree.depth v - 2, by omega⟩
    · simp only [h1, List.replicate_zero]
      change ([] : List Bool) = _
      simp [show ¬ (2 ≤ BinTree.depth v) by omega]
    · simp only [hm, List.replicate_succ]
      change nuS (Fin.cons v x) y = _
      rw [ih]
      simp [show 2 ≤ BinTree.depth v by omega]

theorem eval_noUnderflow_eq (w : List Bool) :
    nuS ![w] ![] = if BinTree.ok w then [true] else [] :=
  nuS_gen w _ _
```

## The spelling experiment

Six expressions differing only in how three child families are written,
with the same `true`-step lemma attempted against each. This is what
established device 3, and the outcomes are the table in the spec's
§ Unfolding.

The three families varied are the enclosing guard's safe family, and the
inner node's normal and safe families.

```lean
def innerVV : sig.toPFunctor.W :=
  WType.mk (.comp 1 1 1 0)
    (compChildren countRaw ![WType.mk (.proj 1 0 0) Fin.elim0] Fin.elim0)

def innerFV : sig.toPFunctor.W :=
  WType.mk (.comp 1 1 1 0)
    (compChildren countRaw (fun _ ↦ WType.mk (.proj 1 0 0) Fin.elim0)
      Fin.elim0)

def innerVF : sig.toPFunctor.W :=
  WType.mk (.comp 1 1 1 0)
    (compChildren countRaw ![WType.mk (.proj 1 0 0) Fin.elim0]
      (fun _ ↦ zeroAt 1 1))

def innerFF : sig.toPFunctor.W :=
  WType.mk (.comp 1 1 1 0)
    (compChildren countRaw (fun _ ↦ WType.mk (.proj 1 0 0) Fin.elim0)
      (fun _ ↦ zeroAt 1 1))

def guardV (inner : sig.toPFunctor.W) : sig.toPFunctor.W :=
  WType.mk (.comp 1 1 0 1)
    (compChildren (WType.mk .pred Fin.elim0) Fin.elim0 ![inner])

def guardF (inner : sig.toPFunctor.W) : sig.toPFunctor.W :=
  WType.mk (.comp 1 1 0 1)
    (compChildren (WType.mk .pred Fin.elim0) Fin.elim0 (fun _ ↦ inner))
```

Wrapping each guard in the `true`-step and the recursion gives the six
variants. The lemma attempted against each, with `nu` the variant:

```lean
theorem step (v : List Bool) (x y : Fin 0 → List Bool) :
    (BC.eval nu).2 (Fin.cons (true :: v) x) y =
      (match ((BC.eval count).2 (fun _ ↦ v) (fun _ ↦ [])).tail with
       | [] => []
       | true :: _ => (BC.eval nu).2 (Fin.cons v x) y
       | false :: _ => (BC.eval nu).2 (Fin.cons v x) y) := rfl
```

It holds for `guardV innerFF` and `guardF innerFF`, and fails for
`guardV innerVV`, `guardV innerFV`, `guardF innerVV` and `guardV innerVF`
— that is, it holds exactly when both of the inner node's families are
constant functions, irrespective of the enclosing family.
