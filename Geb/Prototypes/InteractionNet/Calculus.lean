/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.Term
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# A sequential interaction calculus

A configuration has an ordered interface, equations, and the next unused natural-number
name. A rule names each port of the active pair and a finite set of internal wires. Rule
instantiation substitutes the actual ports and allocates the internal wires consecutively.

The reducer implements interaction and wire elimination in the textual presentation of
{cite}`HassanMackieSato2015`, Section 3. Wire elimination combines communication, substitution
and collection: it substitutes only when the eliminated name occurs exactly once elsewhere
and does not occur in its replacement. Equations are searched from left to right. An inert
equation does not prevent a later active pair from reducing. Rules can be registered in either
orientation; the lookup checks both orientations.

## Main definitions

* {lit}`Rule`, {lit}`Rule.Linear` — a rule and its interface condition.
* {lit}`Config`, {lit}`Config.WellFormed` — configurations and the wire invariant.
* {lit}`System.step` — one deterministic reduction, including explicit allocation.
* {lit}`System.run`, {lit}`System.Reaches` — bounded execution and finite reachability.

## Main statements

* {lit}`Rule.allocated_lt`, {lit}`Rule.allocated_injective` — fresh internal names.
* {lit}`System.reaches_trans` — finite executions compose.
* {lit}`System.run_of_normal` — a normal configuration is stable under execution.

## References

* {cite}`HassanMackieSato2015`, Section 3.

## Tags

interaction calculus, wire, substitution, allocation, sequential reduction
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

variable {α : Type} {arity : α → ℕ}

/-- The boundary of a pair of agents: the left and right auxiliary ports. -/
abbrev Boundary (arity : α → ℕ) (a b : α) := Fin (arity a) ⊕ Fin (arity b)

/-- A rule's internal wires and equations over its boundary and internal names. -/
structure Rule (arity : α → ℕ) (a b : α) where
  /-- The number of internal wires allocated by an interaction. -/
  fresh : ℕ
  /-- The replacement net; boundary variables stand for whole auxiliary-port terms. -/
  equations : List (Equation arity (Boundary arity a b ⊕ Fin fresh))

namespace Rule

/-- The occurrences of names on a rule's right-hand side. -/
def names {a b : α} (r : Rule arity a b) :=
  r.equations.flatMap fun e ↦ e.1.names ++ e.2.names

/-- A rule uses each boundary port once and each internal wire twice. -/
def Linear {a b : α} (r : Rule arity a b) : Prop :=
  (∀ i, r.names.count (.inl i) = 1) ∧ (∀ j, r.names.count (.inr j) = 2)

/-- The allocated name of an internal wire. -/
def allocated {a b : α} (r : Rule arity a b) (next : ℕ) (i : Fin r.fresh) : ℕ :=
  next + i.val

/-- An allocated name is below the updated supply. -/
theorem allocated_lt {a b : α} (r : Rule arity a b) (next : ℕ) (i : Fin r.fresh) :
    r.allocated next i < next + r.fresh := Nat.add_lt_add_left i.isLt next

/-- Distinct internal wires receive distinct names. -/
theorem allocated_injective {a b : α} (r : Rule arity a b) (next : ℕ) :
    Function.Injective (r.allocated next) := by
  intro i j h
  exact Fin.ext (Nat.add_left_cancel h)

/-- Substitute the active pair's ports and fresh internal names into a rule. -/
def instantiate {a b : α} (r : Rule arity a b) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    List (Equation arity ℕ) :=
  let σ := Sum.elim (Sum.elim xs ys) (fun i ↦ Term.var (r.allocated next i))
  r.equations.map fun e ↦ (e.1.subst σ, e.2.subst σ)

end Rule

/-- A net with an ordered interface and an explicit fresh-name supply. -/
structure Config (arity : α → ℕ) where
  /-- The terms at the observable ports. -/
  interface : List (Term arity ℕ)
  /-- The wires joining roots. -/
  equations : List (Equation arity ℕ)
  /-- The next unused name. -/
  nextName : ℕ

namespace Config

/-- Every occurrence of a name in a configuration. -/
def names (c : Config arity) : List ℕ :=
  c.interface.flatMap Term.names ++ c.equations.flatMap (fun e ↦ e.1.names ++ e.2.names)

/-- Names have at most two ends and are all below the next unused name. -/
def WellFormed (c : Config arity) : Prop :=
  (∀ x, c.names.count x ≤ 2) ∧ ∀ x ∈ c.names, x < c.nextName

/-- A finite check of both the wire multiplicities and the allocation bound. -/
def check (c : Config arity) : Bool :=
  c.names.all fun x ↦ decide (c.names.count x ≤ 2 ∧ x < c.nextName)

/-- The finite wire check is equivalent to the configuration invariant. -/
theorem check_iff (c : Config arity) : c.check = true ↔ c.WellFormed := by
  simp only [check, List.all_eq_true, decide_eq_true_eq, WellFormed]
  constructor
  · intro h
    constructor
    · intro x
      by_cases hx : x ∈ c.names
      · exact (h x hx).1
      · simp [List.count_eq_zero_of_not_mem hx]
    · exact fun x hx ↦ (h x hx).2
  · exact fun h x hx ↦ ⟨h.1 x, h.2 x hx⟩

/-- Substitute at every occurrence of a name, preserving the allocation supply. -/
def subst (σ : ℕ → Term arity ℕ) (c : Config arity) : Config arity :=
  { c with
    interface := c.interface.map (Term.subst σ)
    equations := c.equations.map fun e ↦ (e.1.subst σ, e.2.subst σ) }

/-- Eliminate one end of a wire when it has exactly one other end in the configuration. -/
def eliminate (x : ℕ) (t : Term arity ℕ) (rest : Config arity) : Option (Config arity) :=
  if x ∉ t.names ∧ rest.names.count x = 1 then
    some (rest.subst fun y ↦ if y = x then t else Term.var y)
  else none

end Config

/-- A collection of rules. Lookup is oriented; the reducer also checks the reverse pair. -/
structure System (arity : α → ℕ) where
  /-- At most one rule is registered for each ordered pair. -/
  rule : (a b : α) → Option (Rule arity a b)

namespace System

/-- Contract one equation, with the other equations and interface supplied separately. -/
def contract (s : System arity) (e : Equation arity ℕ) (rest : Config arity) :
    Option (Config arity) :=
  match e with
  | (.pure x, .pure y) =>
    (rest.eliminate x (Term.var y)).orElse fun _ ↦ rest.eliminate y (Term.var x)
  | (.pure x, t) => rest.eliminate x t
  | (t, .pure x) => rest.eliminate x t
  | (.liftBind a xs, .liftBind b ys) =>
    match s.rule a b with
    | some r => some { rest with
        equations := r.instantiate rest.nextName xs ys ++ rest.equations
        nextName := rest.nextName + r.fresh }
    | none => (s.rule b a).map fun r ↦ { rest with
        equations := r.instantiate rest.nextName ys xs ++ rest.equations
        nextName := rest.nextName + r.fresh }

/-- Reduce the first reducible equation, retaining earlier inert equations. -/
def step (s : System arity) (c : Config arity) : Option (Config arity) :=
  c.equations.zipIdx.findSome? fun (e, i) ↦
    s.contract e { c with equations := c.equations.take i ++ c.equations.drop (i + 1) }

/-- A reducible head equation is the next reduction. -/
theorem step_cons (s : System arity) (e : Equation arity ℕ) (c d : Config arity)
    (h : s.contract e c = some d) :
    s.step { c with equations := e :: c.equations } = some d := by
  simp [step, h]

/-- A normal configuration has no reducible equation. -/
def Normal (s : System arity) (c : Config arity) : Prop := s.step c = none

/-- A configuration without equations is normal. -/
theorem normal_of_equations_eq_nil (s : System arity) (c : Config arity)
    (h : c.equations = []) : s.Normal c := by
  simp [Normal, step, h]

/-- Run at most the given number of reductions, retaining a normal result once reached. -/
def run (s : System arity) (n : ℕ) (c : Config arity) : Config arity :=
  Nat.repeat (fun d ↦ (s.step d).getD d) n c

/-- The result is obtained after a finite number of reductions. -/
def Reaches (s : System arity) (c d : Config arity) : Prop := ∃ n, s.run n c = d

/-- Zero steps leave the configuration unchanged. -/
@[simp] theorem run_zero (s : System arity) (c : Config arity) : s.run 0 c = c := rfl

/-- A run can be split into a prefix and a suffix. -/
theorem run_add (s : System arity) (m n : ℕ) (c : Config arity) :
    s.run (m + n) c = s.run n (s.run m c) := by
  apply Nat.rec (motive := fun n ↦ s.run (m + n) c = s.run n (s.run m c)) rfl
    (fun n ih ↦ ?_) n
  change (s.step (s.run (m + n) c)).getD (s.run (m + n) c) =
    (s.step (s.run n (s.run m c))).getD (s.run n (s.run m c))
  rw [ih]

/-- Every configuration reaches itself. -/
theorem reaches_refl (s : System arity) (c : Config arity) : s.Reaches c c := ⟨0, rfl⟩

/-- One successful reduction is a finite execution. -/
theorem reaches_of_step (s : System arity) {c d : Config arity} (h : s.step c = some d) :
    s.Reaches c d := by
  refine ⟨1, ?_⟩
  change (s.step c).getD c = d
  rw [h]
  rfl

/-- Finite executions compose. -/
theorem reaches_trans (s : System arity) {c d e : Config arity}
    (h : s.Reaches c d) (k : s.Reaches d e) : s.Reaches c e := by
  obtain ⟨m, rfl⟩ := h
  obtain ⟨n, rfl⟩ := k
  exact ⟨m + n, s.run_add m n c⟩

/-- A normal configuration remains unchanged at every execution bound. -/
theorem run_of_normal (s : System arity) {c : Config arity} (h : s.Normal c) (n : ℕ) :
    s.run n c = c := by
  apply Nat.rec (motive := fun n ↦ s.run n c = c) rfl (fun n ih ↦ ?_) n
  change (s.step (s.run n c)).getD (s.run n c) = c
  rw [ih, h]
  rfl

end System

end Geb.InteractionNet

end
