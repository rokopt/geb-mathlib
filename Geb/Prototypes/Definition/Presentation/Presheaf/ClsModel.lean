/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Definition.Presentation.Presheaf.OneStep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The classes of a presentation as a model of the quotient presheaf polynomial functor

For a quotient presheaf polynomial functor {lit}`𝐅` with free finitary arities, the presheaf of
classes of closed terms of its presentation ({name}`Geb.Definition.Presheaf.QPRA.onestep`) is a
model of {lit}`𝐅` ({lit}`Presheaf.QPRA.clsModel`): a node over the terms goes to its shape applied
to the classes it gives its arguments at their objects ({lit}`Presheaf.QPRA.αTerm`), and a node
over the witnesses to the value of its source endpoint.

The model is natural. Along a morphism of {lit}`I` on terms, a node's value restricts as the
restricted node's ({lit}`Presheaf.QPRA.αTerm_map`), by the naturality of the operations on
classes ({name}`Geb.Definition.Presheaf.Presentation.restrCls_op`). Along the endpoint morphisms,
the target endpoint of a node over the witnesses has the value of its source endpoint
({lit}`Presheaf.QPRA.αTerm_tgt`), by the equation of its witness shape.

## Main definitions

* {lit}`Presheaf.QPRA.clsP` — the presheaf of classes of closed terms.
* {lit}`Presheaf.QPRA.αTerm`, {lit}`Presheaf.QPRA.αApp` — the model's values on nodes.
* {lit}`Presheaf.QPRA.clsModel` — the model.

## Main statements

* {lit}`Presheaf.QPRA.αTerm_freeNode` — the value of a node with given arguments.
* {lit}`Presheaf.QPRA.αTerm_map` — naturality along a morphism on terms.
* {lit}`Presheaf.QPRA.αTerm_tgt` — the two endpoints of a node over the witnesses have one value.
* {lit}`Presheaf.QPRA.αApp_map` — naturality along every morphism.

## References

* {cite}`FiorePittsSteenkamp2020`, for W-types with equations.

## Tags

quotient inductive type, presheaf, model, equational presentation, naturality
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

set_option hygiene false in
/-- A node of the free-arity instance with given arguments. -/
local notation "fnode" => FreeArity.freeNode (restr_id := restr_id) (restr_comp := restr_comp)
  (reindex_id := reindex_id) (reindex_comp := reindex_comp)

variable [hfin : ∀ a, FinEnum (S.Gen a)]

/-- The arguments of each term shape, enumerated. -/
@[instance_reducible] def finEnumTermSig (s : (termSig S).A) : FinEnum ((termSig S).Gen s) :=
  hfin s.1

attribute [local instance] finEnumTermSig finEnumOps

variable (I) in
/-- The closed terms have no variables. -/
abbrev noVar : PEmpty.{u + 1} → I := PEmpty.elim

variable (S) in
/-- The presheaf of classes of closed terms of the presentation. -/
abbrev clsP : Iᵒᵖ ⥤ Type (max uA u v) := (onestep S).clsPsh (noVar I)

/-- The value of the model on a node over the terms: its shape applied to the classes it gives its
arguments at their objects. -/
def αTerm {i : I} (n : (𝐅.objPresheaf (discrete (clsP S))).obj ⟨termObj i⟩) : (clsP S).obj ⟨i⟩ :=
  (onestep S).toSlice.resort (noVar I) ⟨(S.q n.1.1.1.1).1,
    (onestep S).toSlice.op (noVar I) (.inl ⟨n.1.1.1.1, congrArg Prod.snd n.2⟩) fun b ↦
      PresheafDomPFunctorData.value _ n.1.1 ⟨⟨b, S.gobj n.1.1.1.1 b, 𝟙 _⟩, rfl⟩⟩
    (congrArg Prod.fst n.2)

/-- The value of the model on a node with given arguments. -/
theorem αTerm_freeNode (a : S.A) {i : I} (hq : S.q a = termObj i)
    (vals : (b : S.Gen a) → (discrete (clsP S)).obj ⟨S.gobj a b⟩) :
    αTerm (fnode (discrete (clsP S)) a hq vals) =
      (onestep S).toSlice.resort (noVar I) ⟨(S.q a).1,
        (onestep S).toSlice.op (noVar I) (.inl ⟨a, congrArg Prod.snd hq⟩) vals⟩
        (congrArg Prod.fst hq) :=
  congrArg (fun f ↦ (onestep S).toSlice.resort (noVar I) ⟨(S.q a).1,
      (onestep S).toSlice.op (noVar I) (.inl ⟨a, congrArg Prod.snd hq⟩) f⟩
      (congrArg Prod.fst hq))
    (funext fun _ ↦ Functor.map_id_apply (discrete (clsP S)) _ _)

/-- The value of the model on a node with given arguments restricts along a morphism of terms as
the value on the restricted node. -/
theorem αTerm_map_freeNode (a : S.A) {i i' : I} (hq : S.q a = termObj i) (f : i' ⟶ i)
    (vals : (b : S.Gen a) → (discrete (clsP S)).obj ⟨S.gobj a b⟩) :
    αTerm ((𝐅.objPresheaf (discrete (clsP S))).map (termHom f).op
        (fnode (discrete (clsP S)) a hq vals)) =
      (onestep S).restrCls (noVar I) f
        (αTerm (fnode (discrete (clsP S)) a hq vals)) := by
  rw [FreeArity.map_freeNode, αTerm_freeNode, αTerm_freeNode]
  obtain rfl : i = (S.q a).1 := (congrArg Prod.fst hq).symm
  exact (onestep S).toSlice.resort_congr (noVar I)
    ((onestep S).restrCls_op (noVar I) ⟨a, congrArg Prod.snd hq⟩ f vals).symm _ rfl

/-- The value of the model restricts along a morphism of terms as the value on the restricted
node. -/
theorem αTerm_map {i i' : I} (f : i' ⟶ i)
    (n : (𝐅.objPresheaf (discrete (clsP S))).obj ⟨termObj i⟩) :
    αTerm ((𝐅.objPresheaf (discrete (clsP S))).map (termHom f).op n) =
      (onestep S).restrCls (noVar I) f (αTerm n) := by
  have h := αTerm_map_freeNode (restr_id := restr_id) (restr_comp := restr_comp)
    (reindex_id := reindex_id) (reindex_comp := reindex_comp) n.1.1.1.1 n.2 f fun b ↦
    PresheafDomPFunctorData.value _ n.1.1 ⟨⟨b, S.gobj n.1.1.1.1 b, 𝟙 _⟩, rfl⟩
  rwa [← FreeArity.eq_freeNode n] at h

/-- The two endpoints of a node over the witnesses with given arguments have one value, by the
equation of its witness shape. -/
theorem αTerm_tgt_freeNode (s : S.A) {i : I} (hq : S.q s = eqObj i)
    (vals : (b : S.Gen s) → (discrete (clsP S)).obj ⟨S.gobj s b⟩) :
    αTerm ((𝐅.objPresheaf (discrete (clsP S))).map (tgtHom i).op
        (fnode (discrete (clsP S)) s hq vals)) =
      αTerm ((𝐅.objPresheaf (discrete (clsP S))).map (srcHom i).op
        (fnode (discrete (clsP S)) s hq vals)) := by
  obtain rfl : i = (S.q s).1 := (congrArg Prod.fst hq).symm
  let w : WitShape S := ⟨s, congrArg Prod.snd hq⟩
  let _ : FinEnum (S.Gen s) := hfin s
  obtain ⟨ts, hts⟩ := (onestep S).toSlice.exists_cls (noVar I) vals
  obtain rfl : vals = fun b ↦ (onestep S).toSlice.cls (noVar I) (ts b) := (funext hts).symm
  have hσ : IsSorted (fun b ↦ (witEqns S).r ⟨w, b⟩) (noVar I) fun b ↦ (ts b).1 :=
    fun b ↦ (ts b).2
  let sideTm : Bool → Tm (ops (termSig S)) (noVar I) (S.q s).1 := fun o ↦
    ⟨((onestep S).side o (.inr w)).bind fun b ↦ (ts b).1,
      (wellSorted_bind hσ _ ((onestep S).side_sorted o (.inr w)).1).1,
      (wellSorted_bind hσ _ ((onestep S).side_sorted o (.inr w)).1).2.trans
        ((onestep S).side_sorted o (.inr w)).2⟩
  have e : ∀ o : Bool, αTerm ((𝐅.objPresheaf (discrete (clsP S))).map (endMorOf o w).op
      (fnode (discrete (clsP S)) s hq fun b ↦ (onestep S).toSlice.cls (noVar I) (ts b))) =
        (onestep S).toSlice.cls (noVar I) (sideTm o) := by
    intro o
    refine (congrArg αTerm (FreeArity.map_freeNode (discrete (clsP S)) s hq (endMorOf o w) _)).trans
      ((αTerm_freeNode (restr_id := restr_id) (restr_comp := restr_comp)
        (reindex_id := reindex_id) (reindex_comp := reindex_comp) _
        (S.q_restr (endMorOf o w) s hq) _).trans ?_)
    have hop : (onestep S).toSlice.op (noVar I) (.inl (endShape o w)) (fun b ↦
        (discrete (clsP S)).map (S.reindex (endMorOf o w) s b).2.op
          ((onestep S).toSlice.cls (noVar I) (ts (S.reindex (endMorOf o w) s b).1))) =
        (onestep S).toSlice.cls (noVar I) (opTm (F := ops (termSig S)) (noVar I)
          (.inl (endShape o w)) fun b ↦
            Presentation.rTm (noVar I) (S.reindex (endMorOf o w) s b).2.1
              (ts (S.reindex (endMorOf o w) s b).1)) :=
      (congrArg _ (funext fun _ ↦ (onestep S).restrCls_cls (noVar I) _ _)).trans
        ((onestep S).toSlice.op_cls (noVar I) _ _)
    refine (congrArg (fun x ↦ (onestep S).toSlice.resort (noVar I) ⟨_, x⟩ _) hop).trans ?_
    refine ((onestep S).toSlice.resort_cls (noVar I) _ _).trans ?_
    cases o <;> exact congrArg ((onestep S).toSlice.cls (noVar I)) (Subtype.ext rfl)
  exact (e true).trans (((onestep S).toSlice.cls_bind_lhs (noVar I) (.inr w) _ hσ).symm.trans
    (e false).symm)

/-- The two endpoints of a node over the witnesses have one value. -/
theorem αTerm_tgt {i : I} (n : (𝐅.objPresheaf (discrete (clsP S))).obj ⟨eqObj i⟩) :
    αTerm ((𝐅.objPresheaf (discrete (clsP S))).map (tgtHom i).op n) =
      αTerm ((𝐅.objPresheaf (discrete (clsP S))).map (srcHom i).op n) := by
  have h := αTerm_tgt_freeNode (restr_id := restr_id) (restr_comp := restr_comp)
    (reindex_id := reindex_id) (reindex_comp := reindex_comp) n.1.1.1.1 n.2 fun b ↦
      PresheafDomPFunctorData.value _ n.1.1 ⟨⟨b, S.gobj n.1.1.1.1 b, 𝟙 _⟩, rfl⟩
  rwa [← FreeArity.eq_freeNode n] at h

/-- The model's values: on a node over the terms, {lit}`αTerm`; on a node over the witnesses, the
value of its source endpoint. -/
def αApp : (c : (I × WalkingParallelPair)ᵒᵖ) →
    (𝐅.objPresheaf (discrete (clsP S))).obj c → (discrete (clsP S)).obj c
  | ⟨(_, .zero)⟩, n => αTerm n
  | ⟨(i, .one)⟩, n => αTerm ((𝐅.objPresheaf (discrete (clsP S))).map (srcHom i).op n)

/-- The model's values commute with the restriction along every morphism of
{lit}`I × WalkingParallelPair`, by cases on its {lit}`WalkingParallelPair` component. -/
theorem αApp_map {i' i : I} {x' x : WalkingParallelPair} (f : i' ⟶ i) (h : x' ⟶ x)
    (n : (𝐅.objPresheaf (discrete (clsP S))).obj ⟨(i, x)⟩) :
    αApp ⟨(i', x')⟩ ((𝐅.objPresheaf (discrete (clsP S))).map
        (Quiver.Hom.op (X := (i', x')) (Y := (i, x)) (f, h)) n) =
      (clsP S).map f.op (αApp ⟨(i, x)⟩ n) := by
  cases h with
  | id =>
    cases x' with
    | zero => exact αTerm_map f n
    | one =>
      change αTerm ((𝐅.objPresheaf (discrete (clsP S))).map (srcHom i').op
          ((𝐅.objPresheaf (discrete (clsP S))).map (eqHom f).op n)) =
        (onestep S).restrCls (noVar I) f
          (αTerm ((𝐅.objPresheaf (discrete (clsP S))).map (srcHom i).op n))
      rw [← Functor.map_comp_apply, ← op_comp, srcHom_comp_eqHom, op_comp, Functor.map_comp_apply]
      exact αTerm_map f _
  | left =>
    change αTerm ((𝐅.objPresheaf (discrete (clsP S))).map (srcOver f).op n) =
      (onestep S).restrCls (noVar I) f
        (αTerm ((𝐅.objPresheaf (discrete (clsP S))).map (srcHom i).op n))
    rw [← termHom_comp_srcHom, op_comp, Functor.map_comp_apply]
    exact αTerm_map f _
  | right =>
    change αTerm ((𝐅.objPresheaf (discrete (clsP S))).map (tgtOver f).op n) =
      (onestep S).restrCls (noVar I) f
        (αTerm ((𝐅.objPresheaf (discrete (clsP S))).map (srcHom i).op n))
    rw [← termHom_comp_tgtHom, op_comp, Functor.map_comp_apply, αTerm_map, αTerm_tgt]

/-- The presheaf of classes of closed terms as a model of the quotient presheaf polynomial
functor. -/
def clsModel : NatTrans (𝐅.objPresheaf (discrete (clsP S))) (discrete (clsP S)) where
  app c := ↾ αApp c
  naturality c c' g := by
    obtain ⟨⟨i, x⟩⟩ := c
    obtain ⟨⟨i', x'⟩⟩ := c'
    obtain ⟨⟨f, h⟩⟩ := g
    ext n
    exact αApp_map f h n

end Geb.Definition.Presheaf.QPRA

end
