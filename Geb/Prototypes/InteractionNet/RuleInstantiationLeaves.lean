/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.RuleLeafPartition
public import Geb.Prototypes.InteractionNet.RuleInstantiationCells
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Leaf occurrences under linear rule instantiation

Every rule boundary inserts one copy of its argument's leaves. Every internal occurrence
instead becomes the sole leaf of its freshly named variable. The resulting bijection
separates argument occurrences from internal wire occurrences and preserves their names.

## Main definitions

* {lit}`Rule.replacementOccurrencesEquiv` — reindex replacements by the rule leaf partition.
* {lit}`Rule.instantiateLeavesEquiv` — separate argument and internal leaves after instantiation.

## Tags

interaction net, compiler, rule, instantiation, leaf, occurrence, fresh name
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

variable {α ν μ : Type} {arity : α → ℕ}

namespace EquationGraph

/-- Substituted equation leaves retain their original occurrence and replacement leaf position. -/
def substLeavesEquiv (σ : ν → Term arity μ) (es : List (Equation arity ν)) :
    Leaf (es.map fun e ↦ (e.1.subst σ, e.2.subst σ)) ≃
      (Σ q : Leaf es, (σ (leafName es q)).fragment.Leaf) :=
  (familyEquiv (substRootEquiv σ es) (fun i ↦
    Term.fragmentLeafEquiv (term_subst σ es i))).trans
      ((sigmaCongrRight' (fun i ↦ Term.substLeafEquiv σ (term es i))).trans
        (Equiv.sigmaAssoc (fun i (q : (term es i).fragment.Leaf) ↦
          (σ ((term es i).fragment.name q)).fragment.Leaf)).symm)

/-- The replacement leaf carries exactly the name of the substituted equation occurrence. -/
theorem substLeavesEquiv_name (σ : ν → Term arity μ) (es : List (Equation arity ν))
    (p : Leaf (es.map fun e ↦ (e.1.subst σ, e.2.subst σ))) :
    let q := substLeavesEquiv σ es p
    (σ (leafName es q.1)).fragment.name q.2 =
      leafName (es.map fun e ↦ (e.1.subst σ, e.2.subst σ)) p :=
  (Term.substLeafEquiv_name σ (term es (substRootEquiv σ es p.1))
    (Term.fragmentLeafEquiv (term_subst σ es p.1) p.2)).trans
      (Term.fragment_name_cast (term_subst σ es p.1) p.2)

end EquationGraph

namespace Rule

variable {a b : α}

/-- Boundary ports supply their argument trees; internal positions supply fresh variable wires. -/
def partitionTerm (r : Rule arity a b) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    Boundary arity a b ⊕ r.InternalLeaf → Term arity ℕ :=
  Sum.elim (Sum.elim xs ys) (fun q ↦ Term.var (r.allocated next (r.internalLeafName q)))

/-- Partitioning an occurrence retains exactly the replacement term selected by its wire name. -/
theorem argumentSubstitution_partition (r : Rule arity a b) (linear : r.Linear) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (q : EquationGraph.Leaf r.equations) :
    r.argumentSubstitution next xs ys (EquationGraph.leafName r.equations q) =
      r.partitionTerm next xs ys (r.leafPartitionEquiv linear q) := by
  have h := congrArg (r.argumentSubstitution next xs ys) (r.leafPartitionEquiv_name linear q)
  cases he : r.leafPartitionEquiv linear q with
  | inl p => rw [he] at h; exact h.symm
  | inr q => rw [he] at h; exact h.symm

/-- Reindex any replacement-fragment occurrences by external ports and internal rule positions. -/
def replacementOccurrencesEquiv (r : Rule arity a b) (linear : r.Linear) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (F : TermFragment arity ℕ → Type) :
    (Σ q : EquationGraph.Leaf r.equations,
      F (r.argumentSubstitution next xs ys (EquationGraph.leafName r.equations q)).fragment) ≃
        (Σ q, F (r.partitionTerm next xs ys q).fragment) :=
  familyEquiv (r.leafPartitionEquiv linear) (fun q ↦
    { toFun := (congrArg (fun t ↦ F t.fragment) (r.argumentSubstitution_partition linear
        next xs ys q)).mp
      invFun := (congrArg (fun t ↦ F t.fragment) (r.argumentSubstitution_partition linear
        next xs ys q)).mpr
      left_inv := by intro p; exact cast_cast _ _ _
      right_inv := by intro p; exact cast_cast _ _ _ })

/-- Discard the singleton leaf position of an internal variable while retaining its occurrence. -/
def partitionLeavesEquiv (r : Rule arity a b) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    (Σ q, (r.partitionTerm next xs ys q).fragment.Leaf) ≃
      (Σ p : Boundary arity a b, (Sum.elim xs ys p).fragment.Leaf) ⊕ r.InternalLeaf where
  toFun p := match p with
    | ⟨.inl p, q⟩ => .inl ⟨p, q⟩
    | ⟨.inr q, _⟩ => .inr q
  invFun p := match p with
    | .inl ⟨p, q⟩ => ⟨.inl p, q⟩
    | .inr q => ⟨.inr q, ()⟩
  left_inv p := by rcases p with ⟨p | q, u⟩ <;> rfl
  right_inv p := by rcases p with ⟨p, q⟩ | q <;> rfl

/-- Replacement leaves consist of the argument leaves and the internal rule occurrences. -/
def replacementLeavesEquiv (r : Rule arity a b) (linear : r.Linear) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    (Σ q : EquationGraph.Leaf r.equations,
      (r.argumentSubstitution next xs ys (EquationGraph.leafName r.equations q)).fragment.Leaf) ≃
        (Σ p : Boundary arity a b, (Sum.elim xs ys p).fragment.Leaf) ⊕ r.InternalLeaf :=
  (r.replacementOccurrencesEquiv linear next xs ys (fun f ↦ f.Leaf)).trans
    (r.partitionLeavesEquiv next xs ys)

/-- Replacement occurrence names are the original argument names or the allocated internal names. -/
theorem replacementLeavesEquiv_name (r : Rule arity a b) (linear : r.Linear) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (q : Σ q : EquationGraph.Leaf r.equations,
      (r.argumentSubstitution next xs ys (EquationGraph.leafName r.equations q)).fragment.Leaf) :
    Sum.elim (fun p : Σ p : Boundary arity a b, (Sum.elim xs ys p).fragment.Leaf ↦
      (Sum.elim xs ys p.1).fragment.name p.2)
      (fun q ↦ r.allocated next (r.internalLeafName q))
        (r.replacementLeavesEquiv linear next xs ys q) =
        (r.argumentSubstitution next xs ys (EquationGraph.leafName r.equations q.1)).fragment.name
          q.2 := by
  have h := Term.fragment_name_cast (r.argumentSubstitution_partition linear next xs ys q.1) q.2
  have he (p : Σ q, (r.partitionTerm next xs ys q).fragment.Leaf) :
      Sum.elim (fun p : Σ p : Boundary arity a b, (Sum.elim xs ys p).fragment.Leaf ↦
        (Sum.elim xs ys p.1).fragment.name p.2)
        (fun q ↦ r.allocated next (r.internalLeafName q)) (r.partitionLeavesEquiv next xs ys p) =
          (r.partitionTerm next xs ys p.1).fragment.name p.2 := by
    rcases p with ⟨p | q, u⟩ <;> rfl
  exact (he (r.replacementOccurrencesEquiv linear next xs ys (fun f ↦ f.Leaf) q)).trans h

/-- Instantiated leaves are one copy of each argument's leaves and every internal occurrence. -/
def instantiateLeavesEquiv (r : Rule arity a b) (linear : r.Linear) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ) :
    EquationGraph.Leaf (r.instantiate next xs ys) ≃
      (Σ p : Boundary arity a b, (Sum.elim xs ys p).fragment.Leaf) ⊕ r.InternalLeaf :=
  (EquationGraph.substLeavesEquiv (r.argumentSubstitution next xs ys) r.equations).trans
    (r.replacementLeavesEquiv linear next xs ys)

/-- The complete instantiation bijection preserves argument names and allocates internal names. -/
theorem instantiateLeavesEquiv_name (r : Rule arity a b) (linear : r.Linear) (next : ℕ)
    (xs : Fin (arity a) → Term arity ℕ) (ys : Fin (arity b) → Term arity ℕ)
    (q : EquationGraph.Leaf (r.instantiate next xs ys)) :
    Sum.elim (fun p : Σ p : Boundary arity a b, (Sum.elim xs ys p).fragment.Leaf ↦
      (Sum.elim xs ys p.1).fragment.name p.2)
      (fun q ↦ r.allocated next (r.internalLeafName q))
        (r.instantiateLeavesEquiv linear next xs ys q) =
        EquationGraph.leafName (r.instantiate next xs ys) q :=
  (r.replacementLeavesEquiv_name linear next xs ys _).trans
    (EquationGraph.substLeavesEquiv_name _ _ q)

end Rule

end Geb.InteractionNet

end
