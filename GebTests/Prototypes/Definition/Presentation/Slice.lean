/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Definition.Presentation.Slice.Free

set_option doc.verso true in
/-!
# Lists with concatenation as a two-sorted presentation

Over two sorts, elements and lists, the operations {lit}`nil`, {lit}`cons` and {lit}`app`, with
the equations {lit}`app nil l = l` and {lit}`app (cons x l) l' = cons x (app l l')`, whose sides
have depth two and mix the sorts. The lists over the element variables, with each operation read
as its list operation, are a model; the value of a class of sort list there is its list, computed
by evaluation; the equations identify a concatenation with its result; and distinct lists keep
distinct classes.

## Main definitions

* {lit}`sig`, {lit}`listApp` — the signature and the presentation.
* {lit}`listAlg` — the lists, as an algebra over the sorts.
* {lit}`nilT`, {lit}`consT`, {lit}`appT` — the operations on well-sorted terms.
* {lit}`toList` — the list of a class of sort list.

## Main statements

* {lit}`listAlg_satisfies` — the lists satisfy the equations.
* {lit}`cls_appT_nilT`, {lit}`cls_appT_consT` — the equations on classes.
* {lit}`cls_app_cons` — a concatenation has the class of its result.

## Tags

many-sorted algebra, equational presentation, list, concatenation, test
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Definition.SliceTests

open PFunctor GebProto Geb.Definition.Slice Geb.Definition.Slice.Presentation

/-- The sorts: elements and lists. -/
inductive Srt
  | elem
  | list

/-- The operations: the empty list, adjoining an element, and concatenation. -/
inductive Op
  | nil
  | cons
  | app

/-- The arguments of an operation: none for the empty list, two for the others, the first at
{lit}`false`. -/
def arity : Op → Type
  | .nil => PEmpty
  | .cons => Bool
  | .app => Bool

/-- The input sort of each argument. -/
def inSort : (a : Op) → arity a → Srt
  | .nil, b => nomatch b
  | .cons, b => cond b .list .elem
  | .app, _ => .list

/-- The signature of lists with concatenation. -/
abbrev sig : SlicePFunctor.{0, 0, 0, 0} Srt Srt where
  A := Op
  B := arity
  r x := inSort x.1 x.2
  q _ := .list

/-- The arguments of each operation, enumerated. -/
instance (a : sig.A) : FinEnum (sig.B a) :=
  match a with
  | .nil => finEnumPEmpty
  | .cons => finEnumBool
  | .app => finEnumBool

/-- The variables of the equation for {lit}`cons`. -/
inductive Three
  | x
  | l
  | l'

/-- The equations: concatenation on the empty list and on an adjoined element. -/
inductive Eqn
  | appNil
  | appCons

/-- The variables of an equation. -/
def eqnVars : Eqn → Type
  | .appNil => Unit
  | .appCons => Three

/-- The sort of each variable of an equation. -/
def eqnSort : (e : Eqn) → eqnVars e → Srt
  | .appNil, _ => .list
  | .appCons, .x => .elem
  | .appCons, .l => .list
  | .appCons, .l' => .list

/-- The equations, each of sort list. -/
abbrev eqns : SlicePFunctor.{0, 0, 0, 0} Srt Srt where
  A := Eqn
  B := eqnVars
  r x := eqnSort x.1 x.2
  q _ := .list

variable {Γ : Type}

/-- The empty list. -/
def nil : sig.toPFunctor.FreeM Γ := .liftBind Op.nil fun x : PEmpty ↦ nomatch x

/-- An element adjoined to a list. -/
def cons (h t : sig.toPFunctor.FreeM Γ) : sig.toPFunctor.FreeM Γ :=
  .liftBind Op.cons fun b : Bool ↦ cond b t h

/-- The concatenation of two lists. -/
def app (s t : sig.toPFunctor.FreeM Γ) : sig.toPFunctor.FreeM Γ :=
  .liftBind Op.app fun b : Bool ↦ cond b t s

/-- The left sides. -/
def lhs : Derived sig.toPFunctor eqns.toPFunctor
  | .appNil => app nil (.pure ())
  | .appCons => app (cons (.pure Three.x) (.pure Three.l)) (.pure Three.l')

/-- The right sides. -/
def rhs : Derived sig.toPFunctor eqns.toPFunctor
  | .appNil => .pure ()
  | .appCons => cons (.pure Three.x) (app (.pure Three.l) (.pure Three.l'))

/-- The left sides are well sorted. -/
theorem lhs_sorted : DerivedSorted (F := sig) (Q := eqns) lhs
  | .appNil => ⟨fun b ↦ by
      cases b
      · exact ⟨rfl, fun x ↦ nomatch x⟩
      · exact ⟨rfl, trivial⟩, rfl⟩
  | .appCons => ⟨fun b ↦ by
      cases b
      · exact ⟨rfl, fun b ↦ by cases b <;> exact ⟨rfl, trivial⟩⟩
      · exact ⟨rfl, trivial⟩, rfl⟩

/-- The right sides are well sorted. -/
theorem rhs_sorted : DerivedSorted (F := sig) (Q := eqns) rhs
  | .appNil => ⟨trivial, rfl⟩
  | .appCons => ⟨fun b ↦ by
      cases b
      · exact ⟨rfl, trivial⟩
      · exact ⟨rfl, fun b ↦ by cases b <;> exact ⟨rfl, trivial⟩⟩, rfl⟩

/-- The presentation of concatenation by its recursion equations. -/
def listApp : Slice.Presentation.{0, 0, 0, 0} sig where
  E := eqns
  lhs := lhs
  rhs := rhs
  lhs_sorted := lhs_sorted
  rhs_sorted := rhs_sorted

/-- The sort of an element or a list. -/
def srtOf : Γ ⊕ List Γ → Srt := Sum.elim (fun _ ↦ .elem) fun _ ↦ .list

/-- The element of a value of sort element. -/
def getElem : (y : Γ ⊕ List Γ) → srtOf y = .elem → Γ
  | .inl x, _ => x
  | .inr _, h => nomatch h

/-- The list of a value of sort list. -/
def getList : (y : Γ ⊕ List Γ) → srtOf y = .list → List Γ
  | .inl _, h => nomatch h
  | .inr l, _ => l

/-- A value of sort list is its list. -/
theorem eq_inr_getList (y : Γ ⊕ List Γ) (h : srtOf y = .list) : y = .inr (getList y h) := by
  cases y with
  | inl _ => exact nomatch h
  | inr _ => rfl

/-- The list operations, on arguments of the input sorts. -/
def listOp : (a : Op) → (v : arity a → Γ ⊕ List Γ) → (∀ b, srtOf (v b) = inSort a b) → List Γ
  | .nil, _, _ => []
  | .cons, v, h => getElem (v false) (h false) :: getList (v true) (h true)
  | .app, v, h => getList (v false) (h false) ++ getList (v true) (h true)

/-- The lists over {lit}`Γ`, as an algebra over the sorts. -/
def listAlg : Alg.{0, 0, 0, 0} sig where
  carrier := Γ ⊕ List Γ
  p := srtOf
  g x := .inr (listOp x.1.1 x.1.2 (congrFun x.2))
  hg := rfl

/-- The lists satisfy the equations. -/
theorem listAlg_satisfies : listApp.Satisfies (listAlg (Γ := Γ)) := by
  intro e σ hσ
  cases e with
  | appNil =>
    exact (congrArg Sum.inr (List.nil_append _)).trans (eq_inr_getList (σ ()) _).symm
  | appCons =>
    exact congrArg Sum.inr List.cons_append

/-- The variables are elements. -/
abbrev elemSort : Γ → Srt := fun _ ↦ .elem

/-- The well-sorted terms of a sort. -/
abbrev T (Γ : Type) (s : Srt) : Type := Tm sig (elemSort (Γ := Γ)) s

/-- An element variable. -/
def varT (x : Γ) : T Γ .elem := ⟨.pure x, trivial, rfl⟩

/-- The empty list. -/
def nilT : T Γ .list := opTm (F := sig) elemSort Op.nil fun b : PEmpty ↦ nomatch b

/-- An element adjoined to a list. -/
def consT (h : T Γ .elem) (t : T Γ .list) : T Γ .list :=
  opTm (F := sig) elemSort Op.cons fun b : Bool ↦ match b with
    | false => h
    | true => t

/-- The concatenation of two lists. -/
def appT (s t : T Γ .list) : T Γ .list :=
  opTm (F := sig) elemSort Op.app fun b : Bool ↦ match b with
    | false => s
    | true => t

/-- The list of a class of sort list, each variable a singleton. -/
def toList (c : listApp.Cls (elemSort (Γ := Γ)) .list) : List Γ :=
  getList (listApp.lift listAlg_satisfies Sum.inl rfl .list c)
    (listApp.p_lift listAlg_satisfies Sum.inl rfl c)

example (x y : Γ) :
    toList (listApp.cls _ (appT (consT (varT x) nilT) (consT (varT y) nilT))) = [x, y] := rfl

/-- The equation for {lit}`nil`, on classes. -/
theorem cls_appT_nilT (l : T Γ .list) : listApp.cls _ (appT nilT l) = listApp.cls _ l :=
  (congrArg (listApp.cls _) (Subtype.ext (congrArg (FreeM.liftBind (P := sig.toPFunctor) Op.app)
    (funext fun b ↦ by
      cases b
      · exact congrArg (FreeM.liftBind (P := sig.toPFunctor) Op.nil) (funext fun x ↦ nomatch x)
      · rfl)))).trans (listApp.cls_bind_lhs _ Eqn.appNil (fun _ ↦ l.1) fun _ ↦ l.2)

/-- The equation for {lit}`cons`, on classes. -/
theorem cls_appT_consT (h : T Γ .elem) (l l' : T Γ .list) :
    listApp.cls _ (appT (consT h l) l') = listApp.cls _ (consT h (appT l l')) := by
  let σ : Three → sig.toPFunctor.FreeM Γ := fun v ↦ Three.rec h.1 l.1 l'.1 v
  have hσ : IsSorted (fun v ↦ eqns.r ⟨Eqn.appCons, v⟩) elemSort σ
    | .x => h.2
    | .l => l.2
    | .l' => l'.2
  refine (congrArg (listApp.cls _) (Subtype.ext ?_)).trans
    ((listApp.cls_bind_lhs _ Eqn.appCons σ hσ).trans (congrArg (listApp.cls _) (Subtype.ext ?_)))
  · refine congrArg (FreeM.liftBind (P := sig.toPFunctor) Op.app) (funext fun b ↦ ?_)
    cases b
    · exact congrArg (FreeM.liftBind (P := sig.toPFunctor) Op.cons)
        (funext fun b ↦ by cases b <;> rfl)
    · rfl
  · refine congrArg (FreeM.liftBind (P := sig.toPFunctor) Op.cons) (funext fun b ↦ ?_)
    cases b
    · rfl
    · exact congrArg (FreeM.liftBind (P := sig.toPFunctor) Op.app)
        (funext fun b ↦ by cases b <;> rfl)

/-- Adjoining an element respects classes of the tail. -/
theorem cls_consT_congr (h : T Γ .elem) {t t' : T Γ .list}
    (ht : listApp.cls _ t = listApp.cls _ t') :
    listApp.cls _ (consT h t) = listApp.cls _ (consT h t') :=
  listApp.cls_opTm_congr _ Op.cons fun b ↦ by
    cases b
    · rfl
    · exact ht

/-- A concatenation of two lists of one element has the class of its result. -/
theorem cls_app_cons (x y : Γ) :
    listApp.cls _ (appT (consT (varT x) nilT) (consT (varT y) nilT)) =
      listApp.cls _ (consT (varT x) (consT (varT y) nilT)) :=
  (cls_appT_consT _ _ _).trans (cls_consT_congr _ (cls_appT_nilT _))

example (x : Γ) : listApp.cls _ (consT (varT x) nilT) ≠ listApp.cls _ nilT := fun h ↦
  List.cons_ne_nil x [] (congrArg toList h)

end Geb.Definition.SliceTests

end
