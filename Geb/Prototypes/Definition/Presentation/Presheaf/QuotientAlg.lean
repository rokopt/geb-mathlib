/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Definition.Presentation.Presheaf.OneStep
public import Geb.Prototypes.QuotientPRA.InitialModel
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The quotient of a quotient presheaf polynomial functor as a model of its presentation

For a quotient presheaf polynomial functor {lit}`𝐅` with free finitary arities, term arguments
and congruences, whose quotient W-type is its initial model
({name}`GebProto.QuotientPRA.existsUnique_isModelHom`), the quotient is an algebra over {lit}`I`
of the operations of its presentation ({name}`Geb.Definition.Presheaf.QPRA.onestep`)
({lit}`Presheaf.QPRA.qAlg`): a term shape applied to classes is the quotient's model applied to a
node with those arguments ({name}`GebProto.QuotientPRA.algTerm`), and a restriction is the
presheaf's. It satisfies the equations ({lit}`Presheaf.QPRA.satisfies_qAlg`): the equations of
naturality by the naturality of the quotient's model, those of identity and composition by the
presheaf's functor laws, and those of the witness shapes by the soundness of the model
({name}`GebProto.QuotientPRA.model_sound`), the endpoints of a node of a witness shape being nodes
of its endpoint shapes on restricted arguments
({name}`GebProto.QuotientPRA.FreeArity.map_freeNode`).

## Main definitions

* {lit}`Presheaf.QPRA.resortQ` — an element of the quotient lying over an object, at that object.
* {lit}`Presheaf.QPRA.qAlg` — the quotient as an algebra over {lit}`I`.

## Main statements

* {lit}`Presheaf.QPRA.quotientModel_freeNode` — the quotient's model on a node with given
  arguments.
* {lit}`Presheaf.QPRA.map_algTerm` — restriction of a term shape applied to classes.
* {lit}`Presheaf.QPRA.satisfies_qAlg` — the quotient satisfies the equations of the presentation.

## References

* {cite}`FiorePittsSteenkamp2020`, for W-types with equations.
* {cite}`KellyPower1993`, for presentations of finitary monads by operations and equations.

## Tags

quotient inductive type, initial algebra, presheaf, equational presentation, model
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

section Resort

variable (restr_id restr_comp reindex_id reindex_comp)

/-- An element of the quotient lying over {lit}`j`, as an element over {lit}`j`. -/
def resortQ {j : I} : (y : Σ i, (quotient 𝐅).obj ⟨i⟩) → y.1 = j → (quotient 𝐅).obj ⟨j⟩
  | ⟨_, x⟩, h => h ▸ x

/-- An element of the quotient is its re-sorting, as an element over any object. -/
theorem sigma_resortQ {j : I} (y : Σ i, (quotient 𝐅).obj ⟨i⟩) (h : y.1 = j) :
    y = ⟨j, resortQ restr_id restr_comp reindex_id reindex_comp y h⟩ := by
  obtain ⟨i, x⟩ := y
  subst h
  rfl

end Resort

variable [∀ a, FinEnum (S.Gen a)] {ht : TermArguments S}
  (hcong : HasCongruences restr_id restr_comp reindex_id reindex_comp ht)

/-- The quotient's model on a node over the terms with given arguments is the term shape applied
to them. -/
theorem quotientModel_freeNode (a : S.A) {i : I} (hq : S.q a = termObj i)
    (v : (b : S.Gen a) → (discrete (quotient 𝐅)).obj ⟨S.gobj a b⟩) :
    (quotientModel hcong).app ⟨termObj i⟩ (FreeArity.freeNode (discrete (quotient 𝐅)) a hq v) =
      algTerm hcong a hq rfl v :=
  congrArg (algTerm hcong a hq rfl)
    (funext fun _ ↦ Functor.map_id_apply (discrete (quotient 𝐅)) _ _)

/-- A term shape applied to classes lies over its object whichever equation of objects presents
it. -/
theorem sigma_algTerm (a : S.A) {c₁ c₂ : I × WalkingParallelPair} (h₁ : S.q a = c₁)
    (h₂ : S.q a = c₂) (hc₁ : c₁.2 = .zero) (hc₂ : c₂.2 = .zero)
    (v : (b : S.Gen a) → (discrete (quotient 𝐅)).obj ⟨S.gobj a b⟩) :
    (⟨c₁.1, algTerm hcong a h₁ hc₁ v⟩ : Σ i, (quotient 𝐅).obj ⟨i⟩) =
      ⟨c₂.1, algTerm hcong a h₂ hc₂ v⟩ := by
  subst h₁
  subst h₂
  rfl

/-- Restriction of a term shape applied to classes is the restricted shape applied to the
restricted classes: the naturality of the quotient's model. -/
theorem map_algTerm (a : S.A) {i i' : I} (hq : S.q a = termObj i) (g : i' ⟶ i)
    (v : (b : S.Gen a) → (discrete (quotient 𝐅)).obj ⟨S.gobj a b⟩) :
    (quotient 𝐅).map g.op (algTerm hcong a hq rfl v) =
      algTerm hcong (S.restr (termHom g) a) (S.q_restr (termHom g) a hq) rfl fun b ↦
        (discrete (quotient 𝐅)).map (S.reindex (termHom g) a b).2.op
          (v (S.reindex (termHom g) a b).1) := by
  rw [← quotientModel_freeNode hcong a hq v, ← quotientModel_freeNode hcong _ _]
  refine (naturality_apply (quotientModel hcong) (termHom g).op _).symm.trans ?_
  exact congrArg ((quotientModel hcong).app ⟨termObj i'⟩)
    (FreeArity.map_freeNode (discrete (quotient 𝐅)) a hq (termHom g) v)

/-- The quotient's operations on elements of the quotient of the input sorts: a term shape by the
quotient's model, a restriction by the presheaf's. -/
def qAlgFun : (a : (ops (termSig S)).A) → (vals : (ops (termSig S)).B a →
    Σ i, (quotient 𝐅).obj ⟨i⟩) → (∀ b, (vals b).1 = (ops (termSig S)).r ⟨a, b⟩) →
    Σ i, (quotient 𝐅).obj ⟨i⟩
  | .inl s, vals, h => ⟨(S.q s.1).1, algTerm hcong (c := termObj (S.q s.1).1) s.1 (q_term s) rfl
      fun b ↦ resortQ restr_id restr_comp reindex_id reindex_comp (vals b) (h b)⟩
  | .inr r, vals, h => ⟨r.2.1, (quotient 𝐅).map r.2.2.op
      (resortQ restr_id restr_comp reindex_id reindex_comp (vals ⟨⟩) (h ⟨⟩))⟩

/-- The quotient as an algebra over {lit}`I` of the operations of the presentation. -/
def qAlg : Alg.{max uA u v, u, u, max u v uA} (ops (termSig S)) where
  carrier := Σ i, (quotient 𝐅).obj ⟨i⟩
  p := Sigma.fst
  g x := qAlgFun hcong x.1.1 x.1.2 (congrFun x.2)
  hg := by
    funext x
    obtain ⟨⟨a, vals⟩, h⟩ := x
    cases a <;> rfl

/-- The quotient satisfies the equations of the presentation. -/
theorem satisfies_qAlg : (onestep S).toSlice.Satisfies (qAlg hcong) := by
  let mk : (i : I) → (quotient 𝐅).obj ⟨i⟩ → Σ i, (quotient 𝐅).obj ⟨i⟩ := Sigma.mk
  intro e σ hσ
  rcases e with ((⟨s, g⟩ | c | ⟨g, h⟩) | s)
  · -- naturality: the naturality of the quotient's model
    refine (congrArg (mk _) (map_algTerm hcong s.1 (q_term s) g _)).trans ?_
    exact sigma_algTerm hcong _ (S.q_restr (termHom g) s.1 (q_term s))
      (q_term ((termSig S).restr s g)) rfl rfl _
  · -- identity: the identity law of the presheaf
    refine (congrArg (mk c) (Functor.map_id_apply (quotient 𝐅) _ _)).trans ?_
    exact (sigma_resortQ restr_id restr_comp reindex_id reindex_comp (σ ⟨⟩) _).symm
  · -- composition: the composition law of the presheaf
    exact congrArg (mk _) (Functor.map_comp_apply (quotient 𝐅) g.op h.op _).symm
  · -- a witness shape: the soundness of the quotient's model on its node
    let v : (b : S.Gen s.1) → (discrete (quotient 𝐅)).obj ⟨S.gobj s.1 b⟩ := fun b ↦
      resortQ restr_id restr_comp reindex_id reindex_comp (σ b) (congrFun hσ b)
    have e : ∀ o : Bool, evalS (qAlg hcong) _ σ hσ (endpoint o s) (endpoint_sorted o s).1 =
        mk (S.q s.1).1 ((quotientModel hcong).app ⟨termObj (S.q s.1).1⟩
          ((𝐅.objPresheaf (discrete (quotient 𝐅))).map (endMorOf o s).op
            (FreeArity.freeNode (discrete (quotient 𝐅)) s.1 (q_wit s) v))) := by
      intro o
      rw [FreeArity.map_freeNode, quotientModel_freeNode]
      exact sigma_algTerm hcong _ (q_term (endShape o s))
        (S.q_restr (endMorOf o s) s.1 (q_wit s)) rfl rfl _
    exact (e false).trans ((congrArg (mk _) (model_sound (quotientModel hcong)
      (FreeArity.freeNode (discrete (quotient 𝐅)) s.1 (q_wit s) v))).trans (e true).symm)

end Geb.Definition.Presheaf.QPRA

end
