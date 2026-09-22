/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.QuotientPRA.W
public import Mathlib.CategoryTheory.Discrete.Basic

meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Quotient W-types of a signature with one-step equations

A signature is a polynomial functor {lit}`P`: an operation {lit}`a : P.A` takes
arguments indexed by {lit}`P.B a`. An equation is one-step when each side is a single
operation applied to variables, an element of {lit}`P.Obj V` for the equation's type
of variables {lit}`V`. Commutativity of a binary operation is one-step; unit and
associativity laws are not.

{lit}`qpra P eqns` is the quotient presheaf polynomial functor of such a system, over
the one-object base: terms are built by the operations; witnesses are built by the
equations, in both orientations, and by a congruence for every operation, whose
arguments are witnesses between the arguments of two applications of the operation.
The congruences and the reversed orientations are added to the equations given; they
are the part of the equivalence and congruence closure that witness constructors can
express ({lit}`GebProto.QuotientPRA.Obstruction`).

Every arity is free: its directions are pairs of an argument and a morphism into the
argument's object, the elements of a coproduct of representable presheaves, and
restriction precomposes the morphism. Restriction of a congruence to an endpoint
postcomposes each argument's morphism with that endpoint's morphism, and restriction
of an equation to an endpoint reads each argument of the side's operation as the
variable the side assigns it.

## Main definitions

* {lit}`Equations` — a system of one-step equations over a signature.
* {lit}`Shape` — the operations, the congruences and the oriented equations.
* {lit}`qpra` — the quotient presheaf polynomial functor of the system.

## Main statements

* {lit}`isFunctorial` — the operations satisfy the functor laws.

## Implementation notes

The base is {lit}`Discrete PUnit × WalkingParallelPair`, whose first component is
trivial. Its objects are pairs, and {lit}`⟨⟨⟩⟩` is definitionally the only element of
{lit}`Discrete PUnit`, so every object is definitionally {lit}`objOf x` for its
{name}`CategoryTheory.Limits.WalkingParallelPair` component {lit}`x`.

The restrictions are defined by cases on the
{name}`CategoryTheory.Limits.WalkingParallelPairHom` component of a morphism, so the
identity morphism acts by the identity definitionally and the laws reduce to the
category laws of the base after a case split.

## References

* {cite}`FiorePittsSteenkamp2020`
* {cite}`Weber2007`

## Tags

quotient inductive type, W-type, polynomial functor, equational theory, congruence
-/

set_option doc.verso true

@[expose] public section

open CategoryTheory Limits

namespace GebProto.QuotientPRA.Signature

universe uA uB

/-- A system of one-step equations over the signature {lit}`P`: named equations, each
with a type of variables and two sides, each side one operation applied to
variables. -/
structure Equations (P : PFunctor.{uA, uB}) : Type (max (uA + 1) (uB + 1)) where
  /-- The names of the equations. -/
  E : Type uA
  /-- The variables of each equation. -/
  V : E → Type uB
  /-- The left side of each equation. -/
  lhs : (e : E) → P.Obj (V e)
  /-- The right side of each equation. -/
  rhs : (e : E) → P.Obj (V e)

variable {P : PFunctor.{uA, uB}}

/-- The side of an equation at an orientation: the left side for {lit}`false`, the
right side for {lit}`true`. -/
def Equations.side (eqns : Equations P) (e : eqns.E) : Bool → P.Obj (eqns.V e)
  | false => eqns.lhs e
  | true => eqns.rhs e

/-- The base: the one-object category times the walking parallel pair. -/
abbrev Obj : Type := Discrete PUnit.{1} × WalkingParallelPair

/-- The object of the base over a {name}`CategoryTheory.Limits.WalkingParallelPair`
object. -/
abbrev objOf (x : WalkingParallelPair) : Obj := (⟨⟨⟩⟩, x)

/-- The morphism of the base over a {name}`CategoryTheory.Limits.WalkingParallelPair`
morphism. -/
abbrev homOf {x' x : WalkingParallelPair} (h : x' ⟶ x) : objOf x' ⟶ objOf x := (𝟙 _, h)

/-- The endpoint morphism at an orientation: the source for {lit}`false`, the target
for {lit}`true`. -/
def endHom : Bool → (WalkingParallelPair.zero ⟶ WalkingParallelPair.one)
  | false => WalkingParallelPairHom.left
  | true => WalkingParallelPairHom.right

variable (P) (eqns : Equations P)

/-- The shapes: an operation, over terms; the congruence of an operation, and an
equation with an orientation, over witnesses. -/
def Shape : Type uA := P.A ⊕ P.A ⊕ eqns.E × Bool

variable {P eqns}

/-- The object of the walking parallel pair over which a shape lies. -/
def shapeObj : Shape P eqns → WalkingParallelPair
  | .inl _ => .zero
  | .inr _ => .one

/-- The arguments of a shape: those of the operation, for an operation and for its
congruence; the variables, for an equation. -/
def Gen : Shape P eqns → Type uB
  | .inl a => P.B a
  | .inr (.inl a) => P.B a
  | .inr (.inr p) => eqns.V p.1

/-- The object over which an argument lies: a witness, for a congruence; a term,
otherwise. -/
def genObj : (s : Shape P eqns) → Gen s → WalkingParallelPair
  | .inl _, _ => .zero
  | .inr (.inl _), _ => .one
  | .inr (.inr _), _ => .zero

/-- The directions of a shape: an argument with a morphism of the base into the
argument's object, an element of the free presheaf on the arguments. -/
def Dir (s : Shape P eqns) : Type uB := Σ g : Gen s, Σ c : Obj, (c ⟶ objOf (genObj s g))

/-- The shape an endpoint of a shape has: an operation, for an operation and for its
congruence; the operation of the side the orientation selects, for an equation. The
orientation {lit}`o` of the endpoint is combined with that of the equation, so the
target of an equation of orientation {lit}`o'` is the side {lit}`!o'`. -/
def endShape (o : Bool) : Shape P eqns → Shape P eqns
  | .inl a => .inl a
  | .inr (.inl a) => .inl a
  | .inr (.inr (e, o')) => .inl (eqns.side e (o ^^ o')).1

/-- The reindexing of the directions of an endpoint into those of the shape: for a
congruence, postcompose with the endpoint morphism; for an equation, read the side's
argument as its variable. -/
def endDir (o : Bool) : (s : Shape P eqns) → Dir (endShape o s) → Dir s
  | .inl _, d => d
  | .inr (.inl _), ⟨b, c, k⟩ => ⟨b, c, k ≫ homOf (endHom o)⟩
  | .inr (.inr (e, o')), ⟨b, c, k⟩ => ⟨(eqns.side e (o ^^ o')).2 b, c, k⟩

/-- The restriction of a shape along a morphism of the walking parallel pair. -/
def restrShape : {x' x : WalkingParallelPair} → (x' ⟶ x) → Shape P eqns → Shape P eqns
  | _, _, .id _, s => s
  | _, _, .left, s => endShape false s
  | _, _, .right, s => endShape true s

/-- The reindexing of directions along a morphism of the walking parallel pair. -/
def reindexDir : {x' x : WalkingParallelPair} → (h : x' ⟶ x) → (s : Shape P eqns) →
    Dir (restrShape h s) → Dir s
  | _, _, .id _, _, d => d
  | _, _, .left, s, d => endDir false s d
  | _, _, .right, s, d => endDir true s d

/-- The restriction of a direction lying over {lit}`i` along a morphism {lit}`i' ⟶ i`:
precompose its morphism. -/
def restrDir (s : Shape P eqns) {i i' : Obj} (g : i' ⟶ i) : (d : Dir s) → d.2.1 = i → Dir s
  | ⟨b, _, k⟩, rfl => ⟨b, i', g ≫ k⟩

/-- An endpoint of a shape lies over the terms. -/
theorem shapeObj_endShape (o : Bool) (s : Shape P eqns) :
    shapeObj (endShape o s) = WalkingParallelPair.zero := by
  rcases s with _ | _ | ⟨e, o'⟩ <;> rfl

/-- A restricted shape lies over the source of the restricting morphism. -/
theorem shapeObj_restrShape {x' x : WalkingParallelPair} (h : x' ⟶ x) (s : Shape P eqns)
    (hs : shapeObj s = x) : shapeObj (restrShape h s) = x' := by
  cases h with
  | id => exact hs
  | left => exact shapeObj_endShape false s
  | right => exact shapeObj_endShape true s

/-- Reindexing along an endpoint keeps the object of a direction. -/
theorem endDir_obj (o : Bool) (s : Shape P eqns) (d : Dir (endShape o s)) :
    (endDir o s d).2.1 = d.2.1 := by
  rcases s with _ | _ | ⟨e, o'⟩
  · rfl
  · rfl
  · rfl

/-- Reindexing keeps the object of a direction. -/
theorem reindexDir_obj {x' x : WalkingParallelPair} (h : x' ⟶ x) (s : Shape P eqns)
    (d : Dir (restrShape h s)) : (reindexDir h s d).2.1 = d.2.1 := by
  cases h with
  | id => rfl
  | left => exact endDir_obj false s d
  | right => exact endDir_obj true s d

variable (P eqns)

/-- The operations of the quotient presheaf polynomial functor of the system. -/
def data : PresheafPFunctorData.{0, 0, uA, uB, 0, 0} Obj Obj where
  A := Shape P eqns
  B := Dir
  r := fun x ↦ x.2.2.1
  q := fun s ↦ objOf (shapeObj s)
  directionRestr := fun s _ i' g d ↦ ⟨restrDir s g d.1 d.2, by obtain ⟨⟨b, c, k⟩, rfl⟩ := d; rfl⟩
  shapeRestr := fun _ j' g s ↦
    ⟨restrShape (Prod.snd g) s.1,
      Prod.ext rfl (shapeObj_restrShape (Prod.snd g) s.1 (congrArg Prod.snd s.2))⟩
  reindex := fun _ _ g s _ d ↦
    ⟨reindexDir (Prod.snd g) s.1 d.1, (reindexDir_obj (Prod.snd g) s.1 d.1).trans d.2⟩

variable {P eqns}

/-- Reindexing along an endpoint commutes with restricting directions. -/
theorem endDir_restrDir (o : Bool) (s : Shape P eqns) {c i' : Obj} (f : i' ⟶ c)
    (b : Gen (endShape o s)) (k : c ⟶ objOf (genObj (endShape o s) b)) :
    restrDir s f (endDir o s ⟨b, c, k⟩) (endDir_obj o s _) =
      endDir o s (restrDir (endShape o s) f ⟨b, c, k⟩ rfl) := by
  rcases s with _ | _ | ⟨e, o'⟩
  · rfl
  · exact Sigma.ext rfl (heq_of_eq (Sigma.ext rfl (heq_of_eq (Category.assoc _ _ _).symm)))
  · rfl

variable (P eqns)

/-- The operations of {lit}`data` satisfy the functor laws. -/
theorem isFunctorial : (data P eqns).IsFunctorial where
  directionRestr_id s i := by
    funext d
    obtain ⟨⟨b, c, k⟩, rfl⟩ := d
    rfl
  directionRestr_comp s i i' i'' f g := by
    funext d
    obtain ⟨⟨b, c, k⟩, rfl⟩ := d
    exact Subtype.ext
      (Sigma.ext rfl (heq_of_eq (Sigma.ext rfl (heq_of_eq (Category.assoc g f k)))))
  shapeRestr_id j := rfl
  shapeRestr_comp j j' j'' g h := by
    obtain ⟨_, x⟩ := j
    obtain ⟨_, x'⟩ := j'
    obtain ⟨_, x''⟩ := j''
    obtain ⟨_, g⟩ := g
    obtain ⟨_, h⟩ := h
    funext s
    cases g <;> cases h <;> rfl
  reindex_naturality j j' g s i i' f := by
    obtain ⟨_, x⟩ := j
    obtain ⟨_, x'⟩ := j'
    obtain ⟨_, g⟩ := g
    obtain ⟨s, hs⟩ := s
    funext d
    obtain ⟨⟨b, c, k⟩, rfl⟩ := d
    apply Subtype.ext
    cases g with
    | id => rfl
    | left => exact endDir_restrDir false s f b k
    | right => exact endDir_restrDir true s f b k
  reindex_id j s i b := rfl
  reindex_comp j j' j'' g h s i b := by
    obtain ⟨_, x⟩ := j
    obtain ⟨_, x'⟩ := j'
    obtain ⟨_, x''⟩ := j''
    obtain ⟨_, g⟩ := g
    obtain ⟨_, h⟩ := h
    cases g <;> cases h <;> rfl

/-- The quotient presheaf polynomial functor of a system of one-step equations: the
operations build terms, and the equations in both orientations and the congruences of
the operations build witnesses. -/
def qpra : PresheafPFunctor.{0, 0, uA, uB, 0, 0} Obj Obj where
  toPresheafPFunctorData := data P eqns
  isFunctorial := isFunctorial P eqns

section Node

universe w

variable {P eqns}

/-- A node of free arity over a presheaf {lit}`Z`, from the values of its arguments: at
the direction {lit}`⟨g, c, k⟩` it carries the restriction along {lit}`k` of the value of
the argument {lit}`g`. -/
def freeNode (Z : Objᵒᵖ ⥤ Type w) (s : Shape P eqns)
    (ts : (g : Gen s) → Z.obj ⟨objOf (genObj s g)⟩) :
    ((qpra P eqns).objPresheaf Z).obj ⟨objOf (shapeObj s)⟩ :=
  ⟨⟨⟨⟨s, fun d ↦ ⟨d.2.1, Z.map d.2.2.op (ts d.1)⟩⟩, rfl⟩, by
    intro i i' f b
    obtain ⟨⟨g, c, k⟩, rfl⟩ := b
    exact Functor.map_comp_apply Z k.op f.op (ts g)⟩, rfl⟩

/-- The source of an equation's witness is the side its orientation selects, applied to
the witness's variables. -/
theorem src_freeNode_eqn (e : eqns.E) (o : Bool)
    (ts : eqns.V e → (qpra P eqns).W.obj ⟨objOf .zero⟩) :
    src (qpra P eqns).W ⟨⟨⟩⟩ (PresheafPFunctor.W.mk (freeNode _ (.inr (.inr (e, o))) ts)) =
      PresheafPFunctor.W.mk (freeNode _ (.inl (eqns.side e (false ^^ o)).1)
        fun b ↦ ts ((eqns.side e (false ^^ o)).2 b)) :=
  rfl

/-- The target of an equation's witness is the other side, applied to the witness's
variables. -/
theorem tgt_freeNode_eqn (e : eqns.E) (o : Bool)
    (ts : eqns.V e → (qpra P eqns).W.obj ⟨objOf .zero⟩) :
    tgt (qpra P eqns).W ⟨⟨⟩⟩ (PresheafPFunctor.W.mk (freeNode _ (.inr (.inr (e, o))) ts)) =
      PresheafPFunctor.W.mk (freeNode _ (.inl (eqns.side e (true ^^ o)).1)
        fun b ↦ ts ((eqns.side e (true ^^ o)).2 b)) :=
  rfl

/-- Restricting a congruence node to an endpoint gives the operation's node on the
arguments restricted to that endpoint. -/
theorem map_freeNode_cong (Z : Objᵒᵖ ⥤ Type w) (o : Bool) (a : P.A)
    (ts : P.B a → Z.obj ⟨objOf .one⟩) :
    ((qpra P eqns).objPresheaf Z).map (homOf (endHom o)).op (freeNode Z (.inr (.inl a)) ts) =
      freeNode Z (.inl a) fun b ↦ Z.map (homOf (endHom o)).op (ts b) := by
  cases o <;> refine Subtype.ext (Subtype.ext (Subtype.ext
    (Sigma.ext rfl (heq_of_eq (funext fun d ↦ ?_))))) <;> obtain ⟨b, c, k⟩ := d
  · refine Sigma.ext rfl (heq_of_eq ?_)
    change Z.map (k ≫ homOf .left).op (ts b) = Z.map k.op (Z.map (homOf .left).op (ts b))
    exact Functor.map_comp_apply Z (homOf .left).op k.op (ts b)
  · refine Sigma.ext rfl (heq_of_eq ?_)
    change Z.map (k ≫ homOf .right).op (ts b) = Z.map k.op (Z.map (homOf .right).op (ts b))
    exact Functor.map_comp_apply Z (homOf .right).op k.op (ts b)

/-- An endpoint of a congruence's witness is the operation applied to the same endpoint
of the witnesses between its arguments. -/
theorem endpoint_freeNode_cong (o : Bool) (a : P.A)
    (ts : P.B a → (qpra P eqns).W.obj ⟨objOf .one⟩) :
    (qpra P eqns).W.map (homOf (endHom o)).op
        (PresheafPFunctor.W.mk (freeNode _ (.inr (.inl a)) ts)) =
      PresheafPFunctor.W.mk (freeNode _ (.inl a)
        fun b ↦ (qpra P eqns).W.map (homOf (endHom o)).op (ts b)) :=
  congrArg PresheafPFunctor.W.mk (map_freeNode_cong _ o a ts)

end Node

section Model

universe w

variable {P eqns}

/-- The constant presheaf on the one-object category at a type. -/
def constPsh (Y : Type w) : (Discrete PUnit.{1})ᵒᵖ ⥤ Type w where
  obj _ := Y
  map _ := 𝟙 Y

variable {Y : Type (max uA uB)} (S : P.Obj Y → Y)

/-- The value an algebra {lit}`S` of the signature gives a node from its arguments'
values: that of its source endpoint, an operation applied to arguments. -/
def algVal : (s : Shape P eqns) → (Dir s → Y) → Y
  | .inl a, v => S ⟨a, fun b ↦ v ⟨b, objOf .zero, 𝟙 _⟩⟩
  | .inr (.inl a), v => S ⟨a, fun b ↦ v ⟨b, objOf .zero, homOf .left⟩⟩
  | .inr (.inr (e, o)), v =>
    S ⟨(eqns.side e (false ^^ o)).1, fun b ↦ v ⟨(eqns.side e (false ^^ o)).2 b, objOf .zero, 𝟙 _⟩⟩

/-- An algebra of the signature satisfies the equations when both sides of each
equation receive the same value at every assignment of the variables. -/
def Satisfies : Prop :=
  ∀ (e : eqns.E) (ρ : eqns.V e → Y), S (P.map ρ (eqns.lhs e)) = S (P.map ρ (eqns.rhs e))

variable {S}

/-- Restriction preserves {lit}`algVal` on argument values that do not depend on the
morphism of a direction, given that the algebra satisfies the equations. -/
theorem algVal_restrShape (sat : Satisfies (eqns := eqns) S) {x' x : WalkingParallelPair}
    (h : x' ⟶ x) (s : Shape P eqns) (hs : shapeObj s = x) (v : Dir s → Y)
    (hv : ∀ (b : Gen s) (c c' : Obj) (f : c' ⟶ c) (k : c ⟶ objOf (genObj s b)),
      v ⟨b, c', f ≫ k⟩ = v ⟨b, c, k⟩) :
    algVal S (restrShape h s) (v ∘ reindexDir h s) = algVal S s v := by
  cases h with
  | id => rfl
  | left =>
    rcases s with a | a | ⟨e, o⟩
    · cases hs
    · rfl
    · rfl
  | right =>
    rcases s with a | a | ⟨e, o⟩
    · cases hs
    · exact congrArg S (Sigma.ext rfl (heq_of_eq (funext fun b ↦
        (hv b (objOf .one) (objOf .zero) (homOf .right) (𝟙 _)).trans
          (hv b (objOf .one) (objOf .zero) (homOf .left) (𝟙 _)).symm)))
    · cases o with
      | false => exact (sat e fun b ↦ v ⟨b, objOf .zero, 𝟙 _⟩).symm
      | true => exact sat e fun b ↦ v ⟨b, objOf .zero, 𝟙 _⟩

variable (S)

/-- The value of the model's algebra on a node over the discrete graph. -/
def modelApp {c : Objᵒᵖ}
    (n : ((qpra P eqns).objPresheaf (discrete (constPsh Y))).obj c) : Y :=
  algVal S n.1.1.1.1 fun d ↦ (n.1.1.1.2 d).2

/-- The model of the quotient presheaf polynomial functor given by an algebra of the
signature that satisfies the equations: a node goes to the value of its source
endpoint. -/
def model (sat : Satisfies (eqns := eqns) S) :
    NatTrans ((qpra P eqns).objPresheaf (discrete (constPsh Y))) (discrete (constPsh Y)) where
  app c := ↾ modelApp S
  naturality c c' g := by
    ext n
    obtain ⟨⟨n, hn⟩, hq⟩ := n
    exact algVal_restrShape sat (Prod.snd g.unop) n.1.1 (congrArg Prod.snd hq)
      (fun d ↦ (n.1.2 d).2) fun b c c' f k ↦ hn f ⟨⟨b, c, k⟩, rfl⟩

/-- The eliminator of the quotient W-type of the system into an algebra of the
signature that satisfies the equations. -/
def lift (sat : Satisfies (eqns := eqns) S) :
    NatTrans (quotient (qpra P eqns)) (constPsh Y) :=
  elim (qpra P eqns) (constPsh Y) (model S sat)

/-- The computation rule of {lit}`lift`: an operation applied to terms goes to the
algebra applied to the terms' values. -/
theorem lift_intro (sat : Satisfies (eqns := eqns) S) (a : P.A)
    (ts : P.B a → (qpra P eqns).W.obj ⟨objOf .zero⟩) :
    (lift S sat).app ⟨⟨⟨⟩⟩⟩ (intro (qpra P eqns) (freeNode _ (.inl a) ts)) =
      S ⟨a, fun b ↦ (lift S sat).app ⟨⟨⟨⟩⟩⟩ (quotientMk (qpra P eqns) (ts b))⟩ := by
  refine (elim_intro (qpra P eqns) (constPsh Y) (model S sat) _).trans
    (congrArg S (Sigma.ext rfl (heq_of_eq (funext fun b ↦ ?_))))
  change (PresheafPFunctor.W.elim (qpra P eqns) _ (model S sat)).app _
      ((qpra P eqns).W.map (𝟙 (objOf .zero)).op (ts b)) = _
  rw [op_id, Functor.map_id_apply]
  rfl

end Model

end GebProto.QuotientPRA.Signature
