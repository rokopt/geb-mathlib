/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Computability.Cobham.Basic
public import Geb.Mathlib.Data.Tree.Preorder

/-!
# The preorder stack scan in Cobham's class

An expression of `C` computing, in a single right-to-left pass over a
bitstring, the stack depth of the word read as the preorder spelling of a
binary tree, together with the verdict of `BinTree.ok`. The two are carried in
one recursive value, told apart by its head: while no node bit has been read
below depth two the value is the depth in unary offset by one, so its head is
`true`; once one has been, the value is `[false]`, which the node step
reproduces, that value's two predecessors being empty. Each bit is read once.

The recursion is a `boundedRec` node, so admissibility requires a bound: the
scan's value is never longer than the recursion variable by more than one bit,
which the successor `S₁` expresses as a term of arity one. That is the side
condition of bounded recursion on notation [Cobham1965], and discharging it is
what places the scan in `C` rather than merely in the syntax `sig` describes.

## Main definitions

* `Cobham.zeroAt`, `Cobham.oneAt`, `Cobham.falseAt` — the empty bitstring and
  the one-bit strings `[true]` and `[false]`, at an arbitrary arity.
* `Cobham.inc` — prepending `true`, of arity one.
* `Cobham.predPred` — the argument with two bits dropped, of arity one.
* `Cobham.combFalseStep`, `Cobham.combTrueStep` — the leaf step and the node
  step of the scan, of arity two.
* `Cobham.comb` — the stack depth and the underflow verdict in one value, of
  arity one.
* `Cobham.combSem` — the scan's meaning at its arity, over which every
  statement of the module is stated.

Each expression appears in three tiers: a raw tree `…Raw`, the expression `…`
of `C` carrying admissibility, and the ascription `…Of` at its reduced arity.

## Main statements

* `Cobham.combSem_nil`, `Cobham.combSem_cons_false`,
  `Cobham.combSem_cons_true` — the scan unfolded at each constructor of the
  recursion variable, with the recursive value exposed.
* `Cobham.combSem_eq` — the scan computes `BinTree.depth` in unary, offset by
  one, while `BinTree.ok` holds, and `[false]` once it has failed.

## Implementation notes

Each raw tree is named apart from the expression built on it because instance
search finds `Decidable (sig.WValid w)` when `w` is a constant but not when it
is a literal `WType.mk` application, so `decide` discharges admissibility only
of a named tree. `zeroAtRaw`, `oneAtRaw` and `falseAtRaw` carry a free arity,
at which `decide` does not apply; their admissibility is the pair of an
`Unit ⊕ Fin m` case analysis and the `funext` that the index condition asks
for. The admissibility of an expression embedding `pred` or `cond` reuses that
expression's own component rather than repeating its proof.

`combSem` is the meaning read at the raw tree rather than at `comb`.
`Cobham.eval` asks only for admissibility as a `sig`-tree, not for the
recursion bound, so the scan is characterized by `combSem_eq` before the
expression carrying that bound exists. The bound is then that characterization
together with `BinTree.depth_le_length`: the value is `[false]`, of length one,
or the depth in unary offset by one, and the depth never exceeds the word
length, while the bound child `S₁` returns one bit more than the recursion
variable. Reading `comb` back through `C.eval` returns `combSem`, both being
the same transport along `fst_eval`.

`cond` and `pred` are `boundedRec` nodes in this algebra rather than
generators, so a step's meaning reduces only once the value it scrutinizes is
in constructor form: `combSem_cons_false` and `combSem_cons_true` are therefore
not definitional, and each is proved by rewriting the scan to the step's own
application at the recursive value, generalizing that value, and matching on
it. The node step's guard drops two bits through two `pred` nodes, each of
which peels a bit only at a literal, so the match reaches the fourth
constructor layer of the value.

`combSem` names the meaning at the reduced arity, so that rewriting under it
type-checks. A meaning taken through the `Sigma` projection instead has a type
headed by that projection rather than by an arrow, and `rw` under it fails as
not type-correct at `implicit` transparency.

## References

* [Cobham1965]

## Tags

Cobham, bounded recursion on notation, binary tree, preorder, stack depth
-/

namespace Cobham

public section

/-- The empty bitstring at an arbitrary arity. -/
@[expose] def zeroAtRaw (n : ℕ) : sig.toPFunctor.W :=
  WType.mk (.comp n 0) fun d ↦
    match d with
    | .inl () => WType.mk .zero Fin.elim0
    | .inr i => i.elim0

/-- The empty bitstring as an expression of arity `n`. -/
@[expose] def zeroAt (n : ℕ) : C :=
  ⟨⟨zeroAtRaw n,
      ⟨fun d ↦ match d with
        | .inl () => ⟨fun c ↦ c.elim0, funext fun c ↦ c.elim0⟩
        | .inr i => i.elim0,
      funext fun d ↦ match d with
        | .inl () => rfl
        | .inr i => i.elim0⟩⟩,
    ⟨trivial, fun d ↦ match d with
      | .inl () => ⟨trivial, fun c ↦ c.elim0⟩
      | .inr i => i.elim0⟩⟩

/-- `zeroAt n` at its declared arity. -/
@[expose] def zeroAtOf (n : ℕ) : COf n := ⟨zeroAt n, rfl⟩

/-- The one-bit string `[true]` at an arbitrary arity. -/
@[expose] def oneAtRaw (n : ℕ) : sig.toPFunctor.W :=
  WType.mk (.comp n 1) fun d ↦
    match d with
    | .inl () => WType.mk (.succ true) Fin.elim0
    | .inr _ => zeroAtRaw n

/-- The one-bit string `[true]` as an expression of arity `n`. -/
@[expose] def oneAt (n : ℕ) : C :=
  ⟨⟨oneAtRaw n,
      ⟨fun d ↦ match d with
        | .inl () => ⟨fun c ↦ c.elim0, funext fun c ↦ c.elim0⟩
        | .inr _ => (zeroAt n).1.2,
      funext fun d ↦ match d with
        | .inl () => rfl
        | .inr _ => rfl⟩⟩,
    ⟨trivial, fun d ↦ match d with
      | .inl () => ⟨trivial, fun c ↦ c.elim0⟩
      | .inr _ => (zeroAt n).2⟩⟩

/-- `oneAt n` at its declared arity. -/
@[expose] def oneAtOf (n : ℕ) : COf n := ⟨oneAt n, rfl⟩

/-- The one-bit string `[false]` at an arbitrary arity. -/
@[expose] def falseAtRaw (n : ℕ) : sig.toPFunctor.W :=
  WType.mk (.comp n 1) fun d ↦
    match d with
    | .inl () => WType.mk (.succ false) Fin.elim0
    | .inr _ => zeroAtRaw n

/-- The one-bit string `[false]` as an expression of arity `n`. -/
@[expose] def falseAt (n : ℕ) : C :=
  ⟨⟨falseAtRaw n,
      ⟨fun d ↦ match d with
        | .inl () => ⟨fun c ↦ c.elim0, funext fun c ↦ c.elim0⟩
        | .inr _ => (zeroAt n).1.2,
      funext fun d ↦ match d with
        | .inl () => rfl
        | .inr _ => rfl⟩⟩,
    ⟨trivial, fun d ↦ match d with
      | .inl () => ⟨trivial, fun c ↦ c.elim0⟩
      | .inr _ => (zeroAt n).2⟩⟩

/-- `falseAt n` at its declared arity. -/
@[expose] def falseAtOf (n : ℕ) : COf n := ⟨falseAt n, rfl⟩

/-- Prepend `true` to the sole argument. -/
@[expose] def incRaw : sig.toPFunctor.W :=
  WType.mk (.comp 1 1) fun d ↦
    match d with
    | .inl () => WType.mk (.succ true) Fin.elim0
    | .inr _ => WType.mk (.proj 1 0) Fin.elim0

/-- Prepending `true`, as an expression of arity one. -/
@[expose] def inc : C :=
  ⟨⟨incRaw, by decide⟩,
    ⟨trivial, fun d ↦ match d with
      | .inl () => ⟨trivial, fun c ↦ c.elim0⟩
      | .inr _ => ⟨trivial, fun c ↦ c.elim0⟩⟩⟩

/-- `inc` at its declared arity. -/
@[expose] def incOf : COf 1 := ⟨inc, rfl⟩

/-- The sole argument with two bits dropped. It is empty exactly when the
argument is the failure flag, whose two predecessors truncate to the empty
bitstring, or a depth below two. -/
@[expose] def predPredRaw : sig.toPFunctor.W :=
  WType.mk (.comp 1 1) fun d ↦
    match d with
    | .inl () => predRaw
    | .inr _ =>
      WType.mk (.comp 1 1) fun e ↦
        match e with
        | .inl () => predRaw
        | .inr _ => WType.mk (.proj 1 0) Fin.elim0

/-- Dropping two bits, as an expression of arity one. -/
@[expose] def predPred : C :=
  ⟨⟨predPredRaw, by decide⟩,
    ⟨trivial, fun d ↦ match d with
      | .inl () => pred.1.2
      | .inr _ =>
        ⟨trivial, fun e ↦ match e with
          | .inl () => pred.1.2
          | .inr _ => ⟨trivial, fun c ↦ c.elim0⟩⟩⟩⟩

/-- `predPred` at its declared arity. -/
@[expose] def predPredOf : COf 1 := ⟨predPred, rfl⟩

/-- The leaf step: push a level onto a live value, whose head is `true`, and
return the failure flag on a value that is empty or has head `false`. The
recursive value is the second of the step's two arguments. -/
@[expose] def combFalseStepRaw : sig.toPFunctor.W :=
  WType.mk (.comp 2 4) fun d ↦
    match d with
    | .inl () => condRaw
    | .inr i =>
      ![WType.mk (.proj 2 1) Fin.elim0, falseAtRaw 2,
        WType.mk (.comp 2 1) (fun e ↦
          match e with
          | .inl () => incRaw
          | .inr _ => WType.mk (.proj 2 1) Fin.elim0),
        falseAtRaw 2] i

/-- The leaf step as an expression of arity two. -/
@[expose] def combFalseStep : C :=
  ⟨⟨combFalseStepRaw, by decide⟩,
    ⟨trivial, fun d ↦ match d with
      | .inl () => cond.1.2
      | .inr 0 => ⟨trivial, fun c ↦ c.elim0⟩
      | .inr 1 => (falseAt 2).2
      | .inr 2 =>
        ⟨trivial, fun e ↦ match e with
          | .inl () => inc.2
          | .inr _ => ⟨trivial, fun c ↦ c.elim0⟩⟩
      | .inr 3 => (falseAt 2).2⟩⟩

/-- `combFalseStep` at its declared arity. -/
@[expose] def combFalseStepOf : COf 2 := ⟨combFalseStep, rfl⟩

/-- The node step: pop a level when at least two remain, and return the failure
flag otherwise. An existing failure propagates, its guard being empty. -/
@[expose] def combTrueStepRaw : sig.toPFunctor.W :=
  WType.mk (.comp 2 4) fun d ↦
    match d with
    | .inl () => condRaw
    | .inr i =>
      ![WType.mk (.comp 2 1) (fun e ↦
          match e with
          | .inl () => predPredRaw
          | .inr _ => WType.mk (.proj 2 1) Fin.elim0),
        falseAtRaw 2,
        WType.mk (.comp 2 1) (fun e ↦
          match e with
          | .inl () => predRaw
          | .inr _ => WType.mk (.proj 2 1) Fin.elim0),
        WType.mk (.comp 2 1) (fun e ↦
          match e with
          | .inl () => predRaw
          | .inr _ => WType.mk (.proj 2 1) Fin.elim0)] i

/-- The node step as an expression of arity two. -/
@[expose] def combTrueStep : C :=
  ⟨⟨combTrueStepRaw, by decide⟩,
    ⟨trivial, fun d ↦ match d with
      | .inl () => cond.1.2
      | .inr 0 =>
        ⟨trivial, fun e ↦ match e with
          | .inl () => predPred.2
          | .inr _ => ⟨trivial, fun c ↦ c.elim0⟩⟩
      | .inr 1 => (falseAt 2).2
      | .inr 2 =>
        ⟨trivial, fun e ↦ match e with
          | .inl () => pred.1.2
          | .inr _ => ⟨trivial, fun c ↦ c.elim0⟩⟩
      | .inr 3 =>
        ⟨trivial, fun e ↦ match e with
          | .inl () => pred.1.2
          | .inr _ => ⟨trivial, fun c ↦ c.elim0⟩⟩⟩⟩

/-- `combTrueStep` at its declared arity. -/
@[expose] def combTrueStepOf : COf 2 := ⟨combTrueStep, rfl⟩

/-- The raw tree of the scan. The base is `[true]`, the empty bitstring having
depth zero and satisfying `ok`; the bound is `S₁`, whose value is one longer
than the recursion variable. -/
@[expose] def combRaw : sig.toPFunctor.W :=
  WType.mk (.boundedRec 0)
    ![oneAtRaw 0, combFalseStepRaw, combTrueStepRaw, WType.mk (.succ true) Fin.elim0]

/-- The scan's meaning at its arity, taken at the raw tree. `Cobham.eval`
asks only for admissibility as a `sig`-tree, so the scan is characterized
before the expression carrying its recursion bound is formed. -/
@[expose] def combSem : Sem 1 :=
  transport (fst_eval ⟨combRaw, by decide⟩) (eval ⟨combRaw, by decide⟩).2

/-- The scan's value on the empty bitstring: depth zero, offset by one. -/
theorem combSem_nil : combSem ![[]] = [true] := rfl

/-- A leaf bit pushes a level onto a live value, and is absorbed by a
failure. -/
theorem combSem_cons_false (v : List Bool) :
    combSem ![false :: v] =
      (match combSem ![v] with
       | [] => [false]
       | true :: _ => true :: combSem ![v]
       | false :: _ => [false]) := by
  change transport combFalseStepOf.2 combFalseStepOf.1.eval ![v, combSem ![v]] = _
  generalize combSem ![v] = r
  match r with
  | [] | true :: _ | false :: _ => rfl

/-- A node bit pops a level when at least two remain, and fails otherwise. The
guard is the value with two bits dropped, so a failure, whose two predecessors
are empty, propagates. -/
theorem combSem_cons_true (v : List Bool) :
    combSem ![true :: v] =
      (match (combSem ![v]).tail.tail with
       | [] => [false]
       | true :: _ => (combSem ![v]).tail
       | false :: _ => (combSem ![v]).tail) := by
  change transport combTrueStepOf.2 combTrueStepOf.1.eval ![v, combSem ![v]] = _
  generalize combSem ![v] = r
  match r with
  | [] => rfl
  | [c] => cases c <;> rfl
  | c :: d :: w =>
    cases c <;> cases d <;> (match w with | [] | true :: _ | false :: _ => rfl)

/-- The scan computes the stack depth in unary, offset by one, while `ok`
holds, and the absorbing value `[false]` once it has failed. -/
theorem combSem_eq (w : List Bool) :
    combSem ![w] =
      if BinTree.ok w then List.replicate (BinTree.depth w + 1) true
      else [false] := by
  refine List.rec (motive := fun u ↦ combSem ![u] =
    if BinTree.ok u then List.replicate (BinTree.depth u + 1) true else [false])
    rfl ?_ w
  intro b v ih
  cases hok : BinTree.ok v
  · have hv : combSem ![v] = [false] := by rw [ih, hok]; rfl
    cases b
    · rw [combSem_cons_false, hv, BinTree.ok_cons_false, hok]
      rfl
    · rw [combSem_cons_true, hv, BinTree.ok_cons_true, hok]
      rfl
  · have hv : combSem ![v] = List.replicate (BinTree.depth v + 1) true := by
      rw [ih, hok]; rfl
    cases b
    · rw [combSem_cons_false, hv, BinTree.ok_cons_false, hok,
        BinTree.depth_cons_false]
      rfl
    · rw [combSem_cons_true, hv, BinTree.ok_cons_true, hok,
        BinTree.depth_cons_true]
      -- the guard's two predecessors reduce only on a numeral of at least that
      -- size, so the depth is split into constructor forms
      have hsplit : ∀ d : ℕ, d = 0 ∨ d = 1 ∨ ∃ m, d = m + 2 := fun d ↦
        match d with
        | 0 => Or.inl rfl
        | 1 => Or.inr (Or.inl rfl)
        | (m + 2) => Or.inr (Or.inr ⟨m, rfl⟩)
      obtain (h0 | h1 | ⟨m, hm⟩) := hsplit (BinTree.depth v)
      · rw [h0]; rfl
      · rw [h1]; rfl
      · rw [hm]; rfl

/-- The stack depth and the underflow verdict of a bitstring in one value. Its
recursion respects the bound because the value is `[false]`, of length one, or
the depth in unary offset by one, and the depth never exceeds the word length
(`BinTree.depth_le_length`), while the bound child `S₁` returns one bit more
than the recursion variable. -/
@[expose] def comb : C :=
  ⟨⟨combRaw, by decide⟩, by
    have hb : ∀ u : List Bool, (combSem ![u]).length ≤ u.length + 1 := by
      intro u
      rw [combSem_eq]
      cases BinTree.ok u
      · exact Nat.le_add_left 1 u.length
      · rw [if_pos rfl, List.length_replicate]
        exact Nat.succ_le_succ (BinTree.depth_le_length u)
    refine ⟨fun x ↦ ?_, ?_⟩
    · change _ ≤ (x 0).length + 1
      rw [(funext fun i ↦ i.elim0 : Fin.tail x = Fin.tail ![x 0])]
      exact hb (x 0)
    · refine fun b : Fin 4 ↦ ?_
      match b with
      | 0 => exact (oneAt 0).2
      | 1 => exact combFalseStep.2
      | 2 => exact combTrueStep.2
      | 3 => exact ⟨trivial, fun c ↦ c.elim0⟩⟩

/-- `comb` at its declared arity. -/
@[expose] def combOf : COf 1 := ⟨comb, rfl⟩

end

end Cobham
