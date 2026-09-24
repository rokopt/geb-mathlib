/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Definition.Presentation.Presheaf.ClsModel
public import Geb.Prototypes.Definition.Presentation.Presheaf.QuotientAlg
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The classes of the presentation are the quotient

For a quotient presheaf polynomial functor {lit}`𝐅` with free finitary arities, term arguments
and congruences, the classes of closed terms of its presentation
({name}`Geb.Definition.Presheaf.QPRA.onestep`) at each object of {lit}`I` are its quotient W-type's
({lit}`Presheaf.QPRA.clsEquiv`).

The value of classes in the quotient, as an algebra satisfying the equations
({name}`Geb.Definition.Presheaf.QPRA.qAlg`), is {lit}`Presheaf.QPRA.ψ`; the eliminator of the
quotient into the presheaf of classes, as a model of {lit}`𝐅`
({name}`Geb.Definition.Presheaf.QPRA.clsModel`), is {lit}`Presheaf.QPRA.φ`. The eliminator after
the value is the identity ({lit}`Presheaf.QPRA.φψ_eq`): both are morphisms of algebras over
{lit}`I` out of the classes, which are free
({name}`Geb.Definition.Slice.Presentation.eq_liftAll`). The value is onto
({lit}`Presheaf.QPRA.exists_ψ_eq`), every class of the quotient being a term shape applied to
classes, by induction on the W-type; so the value after the eliminator is the identity too
({lit}`Presheaf.QPRA.ψ_φ`).

## Main definitions

* {lit}`Presheaf.QPRA.ψ` — the value of classes in the quotient.
* {lit}`Presheaf.QPRA.φ` — the eliminator of the quotient into the classes.
* {lit}`Presheaf.QPRA.clsEquiv` — the classes at an object as the quotient's.

## Main statements

* {lit}`Presheaf.QPRA.ψ_op`, {lit}`Presheaf.QPRA.ψ_restr` — the value commutes with the term shapes
  and the restrictions.
* {lit}`Presheaf.QPRA.φ_algTerm`, {lit}`Presheaf.QPRA.φ_quotientMk_freeNode` — the eliminator
  commutes with the term shapes.
* {lit}`Presheaf.QPRA.φψ_eq`, {lit}`Presheaf.QPRA.ψ_φ` — the two are mutually inverse.

## References

* {cite}`FiorePittsSteenkamp2020`, for W-types with equations.
* {cite}`KellyPower1993`, for presentations of finitary monads by operations and equations.

## Tags

quotient inductive type, initial algebra, presheaf, equational presentation, agreement
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Definition.Presheaf.QPRA

open CategoryTheory Limits PFunctor GebProto GebProto.QuotientPRA Geb.Definition.Slice

universe uA u v

variable {I : Type u} [Category.{v} I] {S : FreeArity.{u, v, uA, u} (I × WalkingParallelPair)}
  {restr_id : S.toData.ShapeRestrId} {restr_comp : S.toData.ShapeRestrComp}
  {reindex_id : S.toData.ReindexId restr_id} {reindex_comp : S.toData.ReindexComp restr_comp}

set_option hygiene false in
/-- The functor of the free-arity instance. -/
local notation "𝐅" => S.toPresheaf restr_id restr_comp reindex_id reindex_comp

variable [hfin : ∀ a, FinEnum (S.Gen a)] {ht : TermArguments S}
  (hcong : HasCongruences restr_id restr_comp reindex_id reindex_comp ht)

attribute [local instance] finEnumTermSig finEnumOps

/-- The empty assignment of closed terms in the quotient. -/
abbrev qEnv : PEmpty.{u + 1} → (qAlg hcong).carrier := fun x ↦ nomatch x

/-- The empty assignment lies over the sorts of the variables. -/
theorem qEnv_p : (qAlg hcong).p ∘ qEnv hcong = noVar I := funext fun x ↦ nomatch x

/-- The value of classes in the quotient. -/
def ψ : (Σ i, (onestep S).toSlice.Cls (noVar I) i) → Σ i, (quotient 𝐅).obj ⟨i⟩ :=
  (onestep S).toSlice.liftAll (satisfies_qAlg hcong) (qEnv hcong) (qEnv_p hcong)

/-- The value of a class lies over its object. -/
theorem ψ_fst (y : Σ i, (onestep S).toSlice.Cls (noVar I) i) : (ψ hcong y).1 = y.1 :=
  congrFun ((onestep S).toSlice.p_liftAll (satisfies_qAlg hcong) (qEnv hcong) (qEnv_p hcong)) y

/-- The value of classes commutes with the term shapes. -/
theorem ψ_op (s : TermShape S) (f : (b : S.Gen s.1) → (onestep S).toSlice.Cls (noVar I)
    ((S.gobj s.1 b).1)) :
    ψ hcong ⟨(S.q s.1).1, (onestep S).toSlice.op (noVar I) (.inl s) f⟩ =
      ⟨(S.q s.1).1, algTerm hcong (c := termObj (S.q s.1).1) s.1 (q_term s) rfl fun b ↦
        resortQ restr_id restr_comp reindex_id reindex_comp (ψ hcong ⟨_, f b⟩) (ψ_fst hcong _)⟩ :=
  (onestep S).toSlice.liftAll_g (satisfies_qAlg hcong) (qEnv hcong) (qEnv_p hcong)
    ⟨⟨.inl s, fun b ↦ ⟨_, f b⟩⟩, rfl⟩

/-- The value of classes commutes with the restrictions. -/
theorem ψ_restr {c c' : I} (g : c' ⟶ c) (y : (onestep S).toSlice.Cls (noVar I) c) :
    ψ hcong ⟨c', (onestep S).restrCls (noVar I) g y⟩ =
      ⟨c', (quotient 𝐅).map g.op
        (resortQ restr_id restr_comp reindex_id reindex_comp (ψ hcong ⟨c, y⟩) (ψ_fst hcong _))⟩ :=
  (onestep S).toSlice.liftAll_g (satisfies_qAlg hcong) (qEnv hcong) (qEnv_p hcong)
    ⟨⟨.inr ⟨c, c', g⟩, fun _ ↦ ⟨c, y⟩⟩, rfl⟩

variable (restr_id restr_comp reindex_id reindex_comp) in
/-- The eliminator of the quotient into the classes. -/
def φ : NatTrans (quotient 𝐅) (clsP S) := elim 𝐅 (clsP S) clsModel

set_option hygiene false in
/-- The eliminator of the quotient of the free-arity instance into the classes. -/
local notation "Φ" => φ restr_id restr_comp reindex_id reindex_comp

/-- The eliminator commutes with the term shapes. -/
theorem φ_algTerm (s : TermShape S) (w : (b : S.Gen s.1) → (discrete (quotient 𝐅)).obj
    ⟨S.gobj s.1 b⟩) :
    (Φ).app ⟨(S.q s.1).1⟩ (algTerm hcong (c := termObj (S.q s.1).1) s.1 (q_term s) rfl w) =
      (onestep S).toSlice.op (noVar I) (.inl s) fun b ↦ (Φ).app _ (w b) := by
  have h := isModelHom_elim hcong (clsP S) clsModel ⟨termObj (S.q s.1).1⟩
    (FreeArity.freeNode (discrete (quotient 𝐅)) s.1 (q_term s) w)
  rw [quotientModel_freeNode, FreeArity.mapPresheaf_freeNode] at h
  exact h.trans (αTerm_freeNode s.1 (q_term s) _)

include hcong in
/-- The eliminator sends the class of a term built by a term shape to the shape applied to the
eliminator's values at the arguments' classes. -/
theorem φ_quotientMk_freeNode (s : TermShape S) (ts : (b : S.Gen s.1) → 𝐅.W.obj ⟨S.gobj s.1 b⟩) :
    (Φ).app ⟨(S.q s.1).1⟩
      (quotientMk 𝐅 (PresheafPFunctor.W.mk (FreeArity.freeNode 𝐅.W s.1 (q_term s) ts))) =
        (onestep S).toSlice.op (noVar I) (.inl s) fun b ↦
          (Φ).app _ ((coeqUnit 𝐅.W).app _ (ts b)) :=
  (congrArg (fun q ↦ (Φ).app ⟨_⟩ q) (algTerm_unit hcong s.1 (q_term s) rfl ts).symm).trans
    (φ_algTerm hcong s _)

/-- The eliminator commutes with the restrictions. -/
theorem φ_restr {c c' : I} (g : c' ⟶ c) (q : (quotient 𝐅).obj ⟨c⟩) :
    (Φ).app ⟨c'⟩ ((quotient 𝐅).map g.op q) = (onestep S).restrCls (noVar I) g ((Φ).app ⟨c⟩ q) :=
  naturality_apply (Φ) g.op q

omit hfin in
/-- Re-sorting equal elements of the quotient gives equal elements. -/
theorem resortQ_congr {y y' : Σ i, (quotient 𝐅).obj ⟨i⟩} (hy : y = y') {j : I} (h : y.1 = j)
    (h' : y'.1 = j) :
    resortQ restr_id restr_comp reindex_id reindex_comp y h =
      resortQ restr_id restr_comp reindex_id reindex_comp y' h' := by
  subst hy
  rfl

/-- The eliminator after the value of classes, on the classes of all objects. -/
def φψ (y : Σ i, (onestep S).toSlice.Cls (noVar I) i) : Σ i, (onestep S).toSlice.Cls (noVar I) i :=
  ⟨y.1, (Φ).app ⟨y.1⟩ (resortQ restr_id restr_comp reindex_id reindex_comp (ψ hcong y)
    (ψ_fst hcong y))⟩

/-- The eliminator after the value of a re-sorted class is the re-sorted image. -/
theorem φψ_resort {j : I} (y : Σ i, (onestep S).toSlice.Cls (noVar I) i) (h : y.1 = j)
    (h₁ : (ψ hcong ⟨j, (onestep S).toSlice.resort (noVar I) y h⟩).1 = j) (h₂ : (φψ hcong y).1 = j) :
    (Φ).app ⟨j⟩ (resortQ restr_id restr_comp reindex_id reindex_comp
      (ψ hcong ⟨j, (onestep S).toSlice.resort (noVar I) y h⟩) h₁) =
        (onestep S).toSlice.resort (noVar I) (φψ hcong y) h₂ := by
  obtain ⟨j', c⟩ := y
  subst h
  rfl

/-- The enumeration of the variables of every equation of the presentation. -/
@[instance_reducible] def finEnumEqns (e : (onestep S).toSlice.E.A) :
    FinEnum ((onestep S).toSlice.E.B e) :=
  match e with
  | .inl (.nat a _) => hfin a.1
  | .inl (.id _) => finEnumPUnit
  | .inl (.comp _ _) => finEnumPUnit
  | .inr s => hfin s.1

attribute [local instance] finEnumEqns

/-- The empty assignment of closed terms in the classes. -/
abbrev clsEnv : PEmpty.{u + 1} → ((onestep S).toSlice.clsAlg (noVar I)).carrier :=
  fun x ↦ nomatch x

/-- The eliminator after the value of classes is a morphism of algebras over {lit}`I`. -/
theorem φψ_g (x : (ops (termSig S)).toSliceDomPFunctor.Obj
    ((onestep S).toSlice.clsAlg (noVar I)).p) :
    φψ hcong (((onestep S).toSlice.clsAlg (noVar I)).g x) =
      ((onestep S).toSlice.clsAlg (noVar I)).g
        ((ops (termSig S)).toSliceDomPFunctor.map (φψ hcong) rfl x) := by
  obtain ⟨⟨a, vals⟩, hv⟩ := x
  rcases a with s | ⟨c, c', g⟩
  · refine congrArg (Sigma.mk _) ?_
    refine (congrArg (fun q ↦ (Φ).app ⟨_⟩ q) (resortQ_congr (ψ_op hcong s _) _ rfl)).trans ?_
    refine (φ_algTerm hcong s _).trans (congrArg ((onestep S).toSlice.op (noVar I) (.inl s))
      (funext fun b ↦ ?_))
    exact φψ_resort hcong (vals b) (congrFun hv b) _ _
  · refine congrArg (Sigma.mk _) ?_
    refine (congrArg (fun q ↦ (Φ).app ⟨_⟩ q) (resortQ_congr (ψ_restr hcong g _) _ rfl)).trans ?_
    refine (φ_restr g _).trans (congrArg ((onestep S).restrCls (noVar I) g) ?_)
    exact φψ_resort hcong (vals ⟨⟩) (congrFun hv ⟨⟩) _ _

/-- The eliminator after the value of classes is the identity: both are morphisms of algebras over
{lit}`I` out of the free algebra of classes. -/
theorem φψ_eq (y : Σ i, (onestep S).toSlice.Cls (noVar I) i) : φψ hcong y = y := by
  have hsat := (onestep S).toSlice.satisfies_clsAlg (noVar I)
  have henv : ((onestep S).toSlice.clsAlg (noVar I)).p ∘ clsEnv = noVar I :=
    funext fun x ↦ nomatch x
  exact ((onestep S).toSlice.eq_liftAll hsat clsEnv henv (φψ hcong) rfl (φψ_g hcong)
    (fun x ↦ nomatch x) y).trans ((onestep S).toSlice.eq_liftAll hsat clsEnv henv id rfl
      (fun _ ↦ rfl) (fun x ↦ nomatch x) y).symm

/-- The value of classes is onto: every class of the quotient is a term shape applied to classes,
by induction on the W-type. -/
theorem exists_ψ_eq {c : I × WalkingParallelPair} (t : 𝐅.W.obj ⟨c⟩) (hc : c.2 = .zero) :
    ∃ y, ψ hcong y = ⟨c.1, (coeqUnit 𝐅.W).app ⟨c⟩ t⟩ := by
  refine FreeArity.W_induction (S := S) (motive := fun c t ↦ c.2 = .zero →
    ∃ y, ψ hcong y = ⟨c.1, (coeqUnit 𝐅.W).app ⟨c⟩ t⟩) (fun a ts ih hc ↦ ?_) t hc
  let _ : FinEnum (S.Gen a) := hfin a
  obtain ⟨ys, hys⟩ := exists_forall_of_finEnum fun b ↦ ih b (ht a b hc)
  have hfst : ∀ b, (ys b).1 = (S.gobj a b).1 := fun b ↦
    (ψ_fst hcong (ys b)).symm.trans (congrArg Sigma.fst (hys b))
  refine ⟨⟨(S.q a).1, (onestep S).toSlice.op (noVar I) (.inl ⟨a, hc⟩) fun b ↦
    (onestep S).toSlice.resort (noVar I) (ys b) (hfst b)⟩, ?_⟩
  refine (ψ_op hcong ⟨a, hc⟩ _).trans ?_
  refine (congrArg (fun w ↦ (⟨(S.q a).1, algTerm hcong (c := termObj (S.q a).1) a
    (q_term ⟨a, hc⟩) rfl w⟩ : Σ i, (quotient 𝐅).obj ⟨i⟩)) (funext fun b ↦ ?_)).trans
      ((sigma_algTerm hcong a (q_term ⟨a, hc⟩) rfl rfl hc _).trans
        (congrArg (Sigma.mk _) (algTerm_unit hcong a rfl hc ts)))
  refine (resortQ_congr (congrArg (ψ hcong) ((onestep S).toSlice.sigma_resort (noVar I) (ys b)
    (hfst b)).symm) _ (hfst b ▸ ψ_fst hcong (ys b))).trans ?_
  exact resortQ_congr (hys b) _ rfl

/-- The value of classes after the eliminator is the identity. -/
theorem ψ_φ (i : I) (q : (quotient 𝐅).obj ⟨i⟩) : ψ hcong ⟨i, (Φ).app ⟨i⟩ q⟩ = ⟨i, q⟩ := by
  refine Quot.ind (β := fun q ↦ ψ hcong ⟨i, (Φ).app ⟨i⟩ q⟩ = ⟨i, q⟩) (fun t ↦ ?_) q
  obtain ⟨⟨j, c⟩, hy⟩ := exists_ψ_eq hcong (c := termObj i) t rfl
  obtain rfl : j = i := (ψ_fst hcong ⟨j, c⟩).symm.trans (congrArg Sigma.fst hy)
  have hq : resortQ restr_id restr_comp reindex_id reindex_comp (ψ hcong ⟨j, c⟩)
      (ψ_fst hcong ⟨j, c⟩) = (coeqUnit 𝐅.W).app ⟨termObj j⟩ t :=
    resortQ_congr hy _ rfl
  have hφ := φψ_eq hcong ⟨j, c⟩
  simp only [φψ, hq] at hφ
  exact (congrArg (ψ hcong) hφ).trans hy

/-- The classes of closed terms of the presentation at an object are the quotient's. -/
def clsEquiv (i : I) : (onestep S).toSlice.Cls (noVar I) i ≃ (quotient 𝐅).obj ⟨i⟩ where
  toFun c := resortQ restr_id restr_comp reindex_id reindex_comp (ψ hcong ⟨i, c⟩)
    (ψ_fst hcong ⟨i, c⟩)
  invFun q := (Φ).app ⟨i⟩ q
  left_inv c := eq_of_heq (Sigma.mk.inj (φψ_eq hcong ⟨i, c⟩)).2
  right_inv q := resortQ_congr (ψ_φ hcong i q) _ rfl

end Geb.Definition.Presheaf.QPRA

end
