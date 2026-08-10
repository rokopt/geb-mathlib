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
* `Cobham.boundSem`, `Cobham.scanSem` — the meanings of the bound child and
  of the scan, at arity one.
* `Cobham.baseWord`, `Cobham.stepWord`, `Cobham.scanStepWord` — the words a
  base and a step contribute, and the semantic step of the fold.

## Main statements

* `Cobham.wValid_boundRaw`, `Cobham.wValid_liftRaw`, `Cobham.wValid_scanRaw`
  — admissibility of the three trees, the last from its components'.
* `Cobham.wIndexRoot_boundRaw`, `Cobham.wIndexRoot_liftRaw`,
  `Cobham.wIndexRoot_scanRaw`, `Cobham.arity_boundRaw`,
  `Cobham.arity_scanW` — their arities.
* `Cobham.boundSem_eq` — the bound child prepends `growth` bits.
* `Cobham.scanSem_nil`, `Cobham.scanSem_cons`, `Cobham.scanSem_eq` — the
  scan on the empty word, on one bit, and as a `List.foldr`.
* `Cobham.baseWord_eq_eval`, `Cobham.stepWord_eq_eval` — each component's
  word is the one its expression of `C` carries.

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

end

end Cobham
