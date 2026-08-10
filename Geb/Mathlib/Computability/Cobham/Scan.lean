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

end

end Cobham
