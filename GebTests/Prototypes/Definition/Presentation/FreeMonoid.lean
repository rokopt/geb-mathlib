/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Definition.Presentation.Free

set_option doc.verso true in
/-!
# The free monoid as a presentation

Binary trees with a unit, over variables {lit}`Γ`, modulo associativity and the two unit laws,
present the free monoid on {lit}`Γ`: their classes are the lists over {lit}`Γ`. The two sides of
associativity have depth two, and one side of each unit law is a bare variable, so no system of
one-step equations expresses them.

## Main definitions

* {lit}`monoid` — the presentation.
* {lit}`toList`, {lit}`fromList` — the value of a class in the lists, and a list as a term.
* {lit}`clsEquivList` — the classes as the lists.

## Main statements

* {lit}`listAlg_satisfies` — the lists satisfy the equations.
* {lit}`cls_fromList_append` — a product of two lists as terms has the class of their
  concatenation.
* {lit}`cls_fromList_toList` — every term has the class of its list of variables.

## Tags

free monoid, equational presentation, associativity, unit law, test
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Definition.FreeMonoidTests

open PFunctor GebProto Geb.Definition.Presentation

/-- The operations: a unit and a binary product. -/
inductive Op
  | unit
  | mul

/-- The arguments of an operation: none for the unit, two for the product, the left one at
{lit}`false`. -/
def arity : Op → Type
  | .unit => PEmpty
  | .mul => Bool

/-- The signature of binary trees with a unit. -/
abbrev sig : PFunctor.{0, 0} := ⟨Op, arity⟩

/-- The arguments of each operation, enumerated. -/
instance (a : sig.A) : FinEnum (sig.B a) :=
  match a with
  | .unit => finEnumPEmpty
  | .mul => finEnumBool

variable {Γ : Type}

/-- The unit. -/
def unit : sig.FreeM Γ := .liftBind Op.unit fun x : PEmpty ↦ nomatch x

/-- The product of two terms. -/
def mul (s t : sig.FreeM Γ) : sig.FreeM Γ := .liftBind Op.mul fun b : Bool ↦ cond b t s

/-- The variables of associativity. -/
inductive Three
  | x
  | y
  | z

/-- The equations: associativity and the left and right unit laws. -/
inductive Eqn
  | assoc
  | unitL
  | unitR

/-- The variables of an equation: three for associativity, one for each unit law. -/
def eqnVars : Eqn → Type
  | .assoc => Three
  | .unitL => Unit
  | .unitR => Unit

/-- The left side of each equation. -/
def lhs : (e : Eqn) → sig.FreeM (eqnVars e)
  | .assoc => mul (mul (.pure .x) (.pure .y)) (.pure .z)
  | .unitL => mul unit (.pure ())
  | .unitR => mul (.pure ()) unit

/-- The right side of each equation. -/
def rhs : (e : Eqn) → sig.FreeM (eqnVars e)
  | .assoc => mul (.pure .x) (mul (.pure .y) (.pure .z))
  | .unitL => .pure ()
  | .unitR => .pure ()

/-- The presentation of monoids. -/
def monoid : Presentation.{0, 0, 0} sig where
  E := ⟨Eqn, eqnVars⟩
  lhs := lhs
  rhs := rhs

/-- The lists over {lit}`Γ`: the empty list and concatenation. -/
def listAlg : sig.Obj (List Γ) → List Γ
  | ⟨.unit, _⟩ => []
  | ⟨.mul, k⟩ => k false ++ k true

/-- The lists satisfy the equations. -/
theorem listAlg_satisfies : monoid.Satisfies (listAlg (Γ := Γ)) := by
  intro e σ
  cases e
  · exact List.append_assoc (σ .x) (σ .y) (σ .z)
  · exact List.nil_append (σ ())
  · exact List.append_nil (σ ())

/-- The value of a class in the lists, each variable a singleton. -/
def toList : monoid.Cls Γ → List Γ := monoid.lift listAlg listAlg_satisfies fun x ↦ [x]

/-- A list as a term: the product of its elements, ending in the unit. -/
def fromList : List Γ → sig.FreeM Γ := List.foldr (fun x t ↦ mul (.pure x) t) unit

/-- The list of the term of a list is the list. -/
theorem toList_fromList (l : List Γ) : toList (monoid.cls (fromList l)) = l :=
  List.rec rfl (fun x _ ih ↦ congrArg (x :: ·) ih) l

/-- Substitution into a product is the product of the substitutions. -/
theorem mul_bind {Δ : Type} (s t : sig.FreeM Δ) (σ : Δ → sig.FreeM Γ) :
    (mul s t).bind σ = mul (s.bind σ) (t.bind σ) :=
  congrArg (FreeM.liftBind (P := sig) Op.mul) (funext fun b ↦ by cases b <;> rfl)

/-- Substitution into the unit is the unit. -/
theorem unit_bind {Δ : Type} (σ : Δ → sig.FreeM Γ) : (unit : sig.FreeM Δ).bind σ = unit :=
  congrArg (FreeM.liftBind (P := sig) Op.unit) (funext fun x ↦ nomatch x)

/-- The left unit law on classes. -/
theorem cls_unit_mul (t : sig.FreeM Γ) : monoid.cls (mul unit t) = monoid.cls t :=
  (congrArg monoid.cls ((mul_bind unit (.pure ()) fun _ : Unit ↦ t).trans
    (congrArg (fun u ↦ mul u t) (unit_bind _)))).symm.trans
      (monoid.cls_bind_lhs Eqn.unitL fun _ ↦ t)

/-- The right unit law on classes. -/
theorem cls_mul_unit (t : sig.FreeM Γ) : monoid.cls (mul t unit) = monoid.cls t :=
  (congrArg monoid.cls ((mul_bind (.pure ()) unit fun _ : Unit ↦ t).trans
    (congrArg (fun u ↦ mul t u) (unit_bind _)))).symm.trans
      (monoid.cls_bind_lhs Eqn.unitR fun _ ↦ t)

/-- Associativity on classes. -/
theorem cls_mul_assoc (s t u : sig.FreeM Γ) :
    monoid.cls (mul (mul s t) u) = monoid.cls (mul s (mul t u)) := by
  let σ : Three → sig.FreeM Γ := fun v ↦ Three.rec s t u v
  have hl : (mul (mul (.pure Three.x) (.pure Three.y)) (.pure Three.z)).bind σ = mul (mul s t) u :=
    (mul_bind _ _ σ).trans (congrArg (fun w ↦ mul w u) (mul_bind _ _ σ))
  have hr : (mul (.pure Three.x) (mul (.pure Three.y) (.pure Three.z))).bind σ = mul s (mul t u) :=
    (mul_bind _ _ σ).trans (congrArg (fun w ↦ mul s w) (mul_bind _ _ σ))
  exact (congrArg monoid.cls hl).symm.trans
    ((monoid.cls_bind_lhs Eqn.assoc σ).trans (congrArg monoid.cls hr))

/-- The product is congruent in each argument. -/
theorem cls_mul_congr {s s' t t' : sig.FreeM Γ} (hs : monoid.cls s = monoid.cls s')
    (ht : monoid.cls t = monoid.cls t') : monoid.cls (mul s t) = monoid.cls (mul s' t') :=
  monoid.cls_liftBind_congr Op.mul fun b ↦ by cases b <;> assumption

/-- The product of two lists as terms has the class of their concatenation. -/
theorem cls_fromList_append (l l' : List Γ) :
    monoid.cls (mul (fromList l) (fromList l')) = monoid.cls (fromList (l ++ l')) := by
  refine List.rec (cls_unit_mul (fromList l')) (fun x l ih ↦ ?_) l
  exact (cls_mul_assoc _ _ _).trans (cls_mul_congr rfl ih)

/-- Every term has the class of its list of variables. -/
theorem cls_fromList_toList (t : sig.FreeM Γ) :
    monoid.cls (fromList (toList (monoid.cls t))) = monoid.cls t := by
  refine FreeM.rec (motive := fun t ↦
    monoid.cls (fromList (toList (monoid.cls t))) = monoid.cls t) ?_ ?_ t
  · intro x
    exact cls_mul_unit (.pure x)
  · intro a ts ih
    cases a with
    | unit => exact congrArg (fun k ↦ monoid.cls (.liftBind Op.unit k)) (funext fun x ↦ nomatch x)
    | mul =>
      refine (cls_fromList_append _ _).symm.trans ((cls_mul_congr (ih false) (ih true)).trans ?_)
      exact congrArg (fun k ↦ monoid.cls (.liftBind Op.mul k)) (funext fun b ↦ by cases b <;> rfl)

/-- The classes of the presentation of monoids are the lists. -/
def clsEquivList : monoid.Cls Γ ≃ List Γ where
  toFun := toList
  invFun l := monoid.cls (fromList l)
  left_inv q := Quot.ind (β := fun q ↦ monoid.cls (fromList (toList q)) = q) cls_fromList_toList q
  right_inv := toList_fromList

/-- The class of a tree of four variables, in two bracketings with units interspersed. -/
def leftTree : sig.FreeM Bool :=
  mul (mul (mul (.pure true) unit) (.pure false)) (mul unit (mul (.pure false) (.pure true)))

/-- The same variables, bracketed to the right, without units. -/
def rightTree : sig.FreeM Bool :=
  mul (.pure true) (mul (.pure false) (mul (.pure false) (.pure true)))

example : toList (monoid.cls leftTree) = [true, false, false, true] := rfl

example : monoid.cls leftTree = monoid.cls rightTree :=
  clsEquivList.injective rfl

end Geb.Definition.FreeMonoidTests

end
