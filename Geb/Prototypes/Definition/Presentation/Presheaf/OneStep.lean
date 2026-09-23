/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Definition.Presentation.Presheaf.Basic
public import Geb.Prototypes.QuotientPRA.Basic
public import Geb.Prototypes.QuotientPRA.FreeArity
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The presentation of a quotient presheaf polynomial functor

A quotient presheaf polynomial functor with free arities
({name}`GebProto.QuotientPRA.FreeArity` over {lit}`I × WalkingParallelPair`) has term shapes, over
objects {lit}`(i, zero)`, and witness shapes, over objects {lit}`(i, one)`. Its term shapes, with
their arguments taken at the objects of {lit}`I` their objects lie over, form a presheaf
polynomial endofunctor over {lit}`I` with free arities ({lit}`Presheaf.QPRA.termSig`): a term
shape restricts along a morphism of {lit}`I` as along the morphism of
{lit}`I × WalkingParallelPair` that is the identity on {lit}`WalkingParallelPair`.

Each witness shape gives an equation ({lit}`Presheaf.QPRA.witEqns`), whose variables are its
arguments, each at the object of {lit}`I` its object lies over, and whose sides are its two
endpoints: the endpoint's shape, the restriction of the witness shape along an endpoint morphism,
applied to the restrictions of the variables along the reindexing morphisms
({lit}`Presheaf.QPRA.endpoint`). An argument over a witness object is a variable like any other:
in the quotient, the two endpoints of a witness have one class, so the endpoints of a witness
shape relate the same classes whichever endpoints of its witness arguments they read. The sides
have depth two, a term shape over restrictions of variables; with the restrictions presented as
operations, every substitution into them is natural. The presentation of the functor is the
presentation over {lit}`termSig` with these equations ({lit}`Presheaf.QPRA.onestep`).

## Main definitions

* {lit}`Presheaf.QPRA.termSig` — the term shapes, as a presheaf polynomial endofunctor over
  {lit}`I`.
* {lit}`Presheaf.QPRA.endShape`, {lit}`Presheaf.QPRA.endpoint` — the endpoints of a witness shape.
* {lit}`Presheaf.QPRA.witEqns` — the equations of the witness shapes.
* {lit}`Presheaf.QPRA.onestep` — the presentation of the functor.

## References

* {cite}`FiorePittsSteenkamp2020`, for W-types with equations.
* {cite}`Weber2007`, for parametric right adjoints on presheaf categories.

## Tags

quotient inductive type, presheaf, equational presentation, witness, restriction
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Definition.Presheaf.QPRA

open CategoryTheory Limits PFunctor Geb.Definition.Slice GebProto.QuotientPRA

universe uA u v

variable {I : Type u} [Category.{v} I] (S : FreeArity.{u, v, uA, u} (I × WalkingParallelPair))

/-- The term shapes: the shapes over objects of terms. -/
abbrev TermShape : Type uA := {s : S.A // (S.q s).2 = .zero}

/-- The witness shapes: the shapes over objects of witnesses. -/
abbrev WitShape : Type uA := {s : S.A // (S.q s).2 = .one}

variable {S}

/-- A term shape lies over the object of terms over its object of {lit}`I`. -/
theorem q_term (s : TermShape S) : S.q s.1 = termObj (S.q s.1).1 := Prod.ext rfl s.2

/-- A witness shape lies over the object of witnesses over its object of {lit}`I`. -/
theorem q_wit (s : WitShape S) : S.q s.1 = eqObj (S.q s.1).1 := Prod.ext rfl s.2

variable (S)

/-- The term shapes as a presheaf polynomial endofunctor over {lit}`I`: a term shape restricts
along a morphism of {lit}`I` as along that morphism on terms. -/
def termSig : Sig.{uA} I where
  A := TermShape S
  q s := (S.q s.1).1
  Gen s := S.Gen s.1
  gobj s b := (S.gobj s.1 b).1
  restr s _ g := ⟨S.restr (termHom g) s.1,
    congrArg Prod.snd (S.q_restr (termHom g) s.1 (q_term s))⟩
  q_restr s _ g := congrArg Prod.fst (S.q_restr (termHom g) s.1 (q_term s))
  reindex s _ g b := ⟨(S.reindex (termHom g) s.1 b).1, (S.reindex (termHom g) s.1 b).2.1⟩

variable {S}

/-- The endpoint morphism of a witness shape at an orientation: from the object of terms to the
object of witnesses over its object of {lit}`I`. -/
abbrev endMorOf (o : Bool) (s : WitShape S) : termObj (S.q s.1).1 ⟶ eqObj (S.q s.1).1 :=
  (𝟙 _, endHom o)

/-- The endpoint of a witness shape at an orientation: its restriction along the endpoint
morphism, a term shape over its object of {lit}`I`. -/
def endShape (o : Bool) (s : WitShape S) : TermShape S :=
  ⟨S.restr (endMorOf o s) s.1, congrArg Prod.snd (S.q_restr (endMorOf o s) s.1 (q_wit s))⟩

/-- The endpoint of a witness shape lies over its object of {lit}`I`. -/
theorem q_endShape (o : Bool) (s : WitShape S) : (S.q (endShape o s).1).1 = (S.q s.1).1 := by
  have h := congrArg Prod.fst (S.q_restr (endMorOf o s) s.1 (q_wit s))
  exact h

variable (S)

/-- The equations of the witness shapes: each over its object of {lit}`I`, with its arguments as
variables, each at its object of {lit}`I`. -/
def witEqns : SlicePFunctor.{uA, u, u, u} I I where
  A := WitShape S
  B s := S.Gen s.1
  r x := (S.gobj x.1.1 x.2).1
  q s := (S.q s.1).1

variable {S}

/-- The side of a witness shape's equation at an orientation: its endpoint's shape applied to the
restrictions of the variables along the reindexing morphisms. -/
def endpoint (o : Bool) (s : WitShape S) : (ops (termSig S)).toPFunctor.FreeM (S.Gen s.1) :=
  opT (S := termSig S) (endShape o s) fun b ↦
    rT (S.reindex (endMorOf o s) s.1 b).2.1 (.pure (S.reindex (endMorOf o s) s.1 b).1)

/-- The sides of the witness shapes' equations are well sorted. -/
theorem endpoint_sorted (o : Bool) :
    DerivedSorted (F := ops (termSig S)) (Q := witEqns S) (endpoint o) :=
  fun s ↦ ⟨fun _ ↦ ⟨rfl, fun _ ↦ ⟨rfl, trivial⟩⟩, q_endShape o s⟩

variable (S)

/-- The presentation of the quotient presheaf polynomial functor: its term shapes, with one
equation for each witness shape. -/
def onestep : Presentation.{uA, uA} (termSig S) where
  E := witEqns S
  lhs := endpoint false
  rhs := endpoint true
  lhs_sorted := endpoint_sorted false
  rhs_sorted := endpoint_sorted true

end Geb.Definition.Presheaf.QPRA

end
