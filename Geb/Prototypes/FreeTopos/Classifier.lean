/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Recursion
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The subobject classifier of a model of the theory

The equalizers and the subobject classifier of a model of the theory of an elementary topos,
stated of the values of terms at an assignment, as the facts the logic of the internal language
rests on. An arrow into an equalizer is determined by its composite with the inclusion
({lit}`eqLift_cancel`), and one whose composite with the equalized arrows agree factors through
it ({lit}`eqLift_hom`). An arrow into the subobject classifier is true after an arrow exactly
when the arrow factors through the pullback of truth along it ({lit}`truthLift_hom`), and two
arrows into the classifier, each true on the other's pullback of truth, are equal
({lit}`omega_ext`): the characteristic map of a subobject is unique. The characteristic map of
the diagonal is true after a pairing only if its arrows are equal ({lit}`eq_of_chi_diag`).

The subobject on which each of a list of arrows into the classifier is true is the iterated
pullback of truth ({lit}`subObj`), through which an arrow factors when each is true after it
({lit}`subObj_lift`). An arrow into the classifier from the product of an object of parameters
with the natural numbers object, or with a list object, is true when it is true at zero, or at
the empty list, and, where it is true, at the successor, or at a construction
({lit}`truth_of_natInd`, {lit}`truth_of_listInd`): its pullback of truth is closed under the
recursion's generators, so a fold into it is a section of its inclusion, by the uniqueness of
the fold with a parameter.

## Main definitions

* {lit}`subObj` — the subobject on which arrows into the classifier are true.

## Main statements

* {lit}`eqLift_hom`, {lit}`eqLift_cancel` — the universal property of equalizers.
* {lit}`truthIncl_hom`, {lit}`truthLift_hom` — the pullback of truth along an arrow.
* {lit}`chi_truthIncl`, {lit}`omega_ext` — an arrow into the classifier is the characteristic
  map of its pullback of truth, and so is determined by it.
* {lit}`eq_of_chi_diag` — equality is the characteristic map of the diagonal.
* {lit}`subObj_hom`, {lit}`subObj_lift` — the universal property of the iterated pullback.
* {lit}`truth_of_natInd`, {lit}`truth_of_listInd` — induction on the natural numbers object
  and on a list object, with parameters.

## Tags

elementary topos, subobject classifier, equalizer, induction, model, partial Horn logic
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos

open PartialHorn Sorts
open scoped FinEnum

universe v

variable {defs : List Defn} {M : Model.{v} (ext defs).sig} {ρ : List M.Val}

section Equalizers

variable (hM : IsModel (ext defs) M)
include hM

/-- An arrow whose composites with two parallel arrows agree factors through their equalizer. -/
theorem eqLift_hom {f g k X Y Z : Tree} (hf : Hom M ρ f X Z) (hg : Hom M ρ g X Z)
    (hk : Hom M ρ k Y X) (hfk : eval M ρ (comp f k) = eval M ρ (comp g k)) :
    Hom M ρ (eqLift f g k) Y (eqz f g) ∧
      eval M ρ (comp (eqIncl f g) (eqLift f g k)) = eval M ρ k := by
  obtain ⟨hi, -⟩ := eqIncl_hom hM hf hg
  obtain ⟨e, he, -⟩ := hi.isObj_dom
  obtain ⟨wf, hwf, hfs⟩ := hf.exists_eval
  obtain ⟨wg, hwg, hgs⟩ := hg.exists_eval
  obtain ⟨wk, hwk, hks⟩ := hk.exists_eval
  obtain ⟨c, hc, -⟩ := (comp_hom hM hk hg).exists_eval
  have hts : [f, g, k].map (eval M ρ) = [wf, wg, wk].map Part.some := by simp [hwf, hwg, hwk]
  have hs : [wf, wg, wk].map Sigma.fst = [arr, arr, arr] := by simp [hfs, hgs, hks]
  obtain ⟨w, hw, -⟩ := ax_holds hM 38 rfl (by decide) hts hs
    (hs' := [⟨eqz f g, eqz f g⟩, ⟨comp f k, comp g k⟩]) rfl
    ⟨⟨e, he, he⟩, holds_of_eval_eq hfk hc⟩ (q := ⟨eqLift f g k, eqLift f g k⟩) rfl
  have hl : Eqn.Holds M ρ ⟨eqLift f g k, eqLift f g k⟩ := ⟨w, hw, hw⟩
  refine ⟨⟨w, hw, sort_of_eval_op rfl hw, hk.isObj_dom, ⟨e, he, sort_of_eval_op rfl he⟩, ?_, ?_⟩,
    ?_⟩
  · exact (eval_eq_of_holds (ax_holds hM 39 rfl (by decide) hts hs
      (hs' := [⟨eqLift f g k, eqLift f g k⟩]) rfl hl (q := ⟨dom (eqLift f g k), dom k⟩)
      rfl)).trans hk.eval_dom
  · exact eval_eq_of_holds (ax_holds hM 40 rfl (by decide) hts hs
      (hs' := [⟨eqLift f g k, eqLift f g k⟩]) rfl hl (q := ⟨cod (eqLift f g k), eqz f g⟩) rfl)
  · exact eval_eq_of_holds (ax_holds hM 41 rfl (by decide) hts hs
      (hs' := [⟨eqLift f g k, eqLift f g k⟩]) rfl hl
      (q := ⟨comp (eqIncl f g) (eqLift f g k), k⟩) rfl)

/-- Arrows into an equalizer with one composite with its inclusion are equal. -/
theorem eqLift_cancel {f g a b X Z W : Tree} (hf : Hom M ρ f X Z) (hg : Hom M ρ g X Z)
    (ha : Hom M ρ a W (eqz f g)) (hb : Hom M ρ b W (eqz f g))
    (h : eval M ρ (comp (eqIncl f g) a) = eval M ρ (comp (eqIncl f g) b)) :
    eval M ρ a = eval M ρ b := by
  obtain ⟨hi, -⟩ := eqIncl_hom hM hf hg
  obtain ⟨e, he, -⟩ := hi.isObj_dom
  obtain ⟨wf, hwf, hfs⟩ := hf.exists_eval
  obtain ⟨wg, hwg, hgs⟩ := hg.exists_eval
  have key : ∀ {c : Tree}, Hom M ρ c W (eqz f g) →
      eval M ρ (eqLift f g (comp (eqIncl f g) c)) = eval M ρ c := fun {c} hc ↦ by
    obtain ⟨wc, hwc, hcs⟩ := hc.exists_eval
    exact eval_eq_of_holds (ax_holds hM 42 rfl (by decide) (ts := [f, g, c])
      (ws := [wf, wg, wc]) (by simp [hwf, hwg, hwc]) (by simp [hfs, hgs, hcs])
      (hs' := [⟨eqz f g, eqz f g⟩, ⟨cod c, eqz f g⟩]) rfl
      ⟨⟨e, he, he⟩, holds_of_eval_eq hc.eval_cod he⟩
      (q := ⟨eqLift f g (comp (eqIncl f g) c), c⟩) rfl)
  exact (key ha).symm.trans ((eval_op₃_congr 12 rfl rfl h).trans (key hb))

/-- Truth after the arrow to the terminal object, after an arrow, is truth after the arrow to the
terminal object from its domain. -/
theorem truth_comp {h X Y : Tree} (hh : Hom M ρ h Y X) :
    eval M ρ (comp (comp tru (bang X)) h) = eval M ρ (comp tru (bang Y)) :=
  (comp_assoc hM hh (bang_hom hM hh.isObj_cod) (tru_hom hM)).symm.trans
    (eval_op₂_congr 3 rfl (comp_bang hM hh))

/-- Truth after the arrow to the terminal object is an arrow into the subobject classifier. -/
theorem truth_hom {X : Tree} (hX : IsObj M ρ X) : Hom M ρ (comp tru (bang X)) X omega :=
  comp_hom hM (bang_hom hM hX) (tru_hom hM)

/-- Truth after the arrow to the terminal object from an arrow's domain, for an arrow into the
subobject classifier. -/
theorem truth_dom_hom {F X : Tree} (hF : Hom M ρ F X omega) :
    Hom M ρ (comp tru (bang (dom F))) X omega :=
  (truth_hom hM hF.isObj_dom).congr (eval_op₂_congr 3 rfl (eval_op₁_congr 5 hF.eval_dom)) rfl rfl

/-- The pullback of truth along an arrow into the subobject classifier, on which it is true. -/
theorem truthIncl_hom {F X : Tree} (hF : Hom M ρ F X omega) :
    Hom M ρ (truthIncl F) (truthEq F) X ∧
      eval M ρ (comp F (truthIncl F)) = eval M ρ (comp tru (bang (truthEq F))) := by
  obtain ⟨hi, he⟩ := eqIncl_hom hM hF (truth_dom_hom hM hF)
  refine ⟨hi, he.trans ?_⟩
  exact (eval_op₂_congr 3 (eval_op₂_congr 3 rfl (eval_op₁_congr 5 hF.eval_dom)) rfl).trans
    (truth_comp hM hi)

/-- An arrow after which an arrow into the subobject classifier is true factors through its
pullback of truth. -/
theorem truthLift_hom {F h X Y : Tree} (hF : Hom M ρ F X omega) (hh : Hom M ρ h Y X)
    (hFh : eval M ρ (comp F h) = eval M ρ (comp tru (bang Y))) :
    Hom M ρ (truthLift F h) Y (truthEq F) ∧
      eval M ρ (comp (truthIncl F) (truthLift F h)) = eval M ρ h :=
  eqLift_hom hM hF (truth_dom_hom hM hF) hh (hFh.trans ((eval_op₂_congr 3
    (eval_op₂_congr 3 rfl (eval_op₁_congr 5 hF.eval_dom)) rfl).trans (truth_comp hM hh)).symm)

/-- Arrows into the pullback of truth with one composite with its inclusion are equal. -/
theorem truthIncl_cancel {F a b X W : Tree} (hF : Hom M ρ F X omega)
    (ha : Hom M ρ a W (truthEq F)) (hb : Hom M ρ b W (truthEq F))
    (h : eval M ρ (comp (truthIncl F) a) = eval M ρ (comp (truthIncl F) b)) :
    eval M ρ a = eval M ρ b :=
  eqLift_cancel hM hF (truth_dom_hom hM hF) ha hb h

end Equalizers

section Classifier

variable (hM : IsModel (ext defs) M)
include hM

/-- The inclusion of the pullback of truth along an arrow is a monomorphism: the projections of
its kernel pair are equal. -/
theorem holds_monoCond_truthIncl {F X : Tree} (hF : Hom M ρ F X omega) :
    (monoCond (truthIncl F)).Holds M ρ := by
  obtain ⟨hi, -⟩ := truthIncl_hom hM hF
  have hd := hi.eval_dom
  set a := dom (truthIncl F) with ha_def
  have hi' : Hom M ρ (truthIncl F) a X := hi.congr rfl hd rfl
  have hA := hi.isObj_dom.congr hd
  have hfst := fst_hom hM hA hA
  have hsnd := snd_hom hM hA hA
  obtain ⟨hk, hkk⟩ := eqIncl_hom hM (comp_hom hM hfst hi') (comp_hom hM hsnd hi')
  set k := eqIncl (comp (truthIncl F) (fst a a)) (comp (truthIncl F) (snd a a)) with hk_def
  have hfk := (comp_hom hM hk hfst).congr rfl rfl hd.symm
  have hsk := (comp_hom hM hk hsnd).congr rfl rfl hd.symm
  have he : eval M ρ (comp (fst a a) k) = eval M ρ (comp (snd a a) k) :=
    truthIncl_cancel hM hF hfk hsk ((comp_assoc hM hk hfst hi').trans
      (hkk.trans (comp_assoc hM hk hsnd hi').symm))
  obtain ⟨w, hw, -⟩ := hsk.exists_eval
  exact holds_of_eval_eq he hw

/-- An arrow into the subobject classifier is the characteristic map of a monomorphism
isomorphic to its pullback of truth. -/
theorem eq_chi_of_iso {m F a b W X : Tree} (hm : Hom M ρ m W X)
    (hmc : (monoCond m).Holds M ρ) (hF : Hom M ρ F X omega) (ha : Hom M ρ a W (truthEq F))
    (hb : Hom M ρ b (truthEq F) W) (h₁ : eval M ρ (comp (truthIncl F) a) = eval M ρ m)
    (h₂ : eval M ρ (comp a b) = eval M ρ (idt (truthEq F)))
    (h₃ : eval M ρ (comp b a) = eval M ρ (idt W)) : eval M ρ F = eval M ρ (chi m) := by
  obtain ⟨wm, hwm, hms⟩ := hm.exists_eval
  obtain ⟨wF, hwF, hFs⟩ := hF.exists_eval
  obtain ⟨wa, hwa, has⟩ := ha.exists_eval
  obtain ⟨wb, hwb, hbs⟩ := hb.exists_eval
  obtain ⟨wc, hwc, -⟩ := ax_holds hM 87 rfl (by decide) (ts := [m]) (ws := [wm])
    (by simp [hwm]) (by simp [hms]) (hs' := [monoCond m]) rfl hmc
    (q := ⟨chi m, chi m⟩) rfl
  obtain ⟨x, hx, -⟩ := hF.isObj_dom
  obtain ⟨o, ho, -⟩ := isObj_omega (ρ := ρ) hM
  obtain ⟨i, hi, -⟩ := (idt_hom hM ha.isObj_cod).exists_eval
  obtain ⟨j, hj, -⟩ := (idt_hom hM hb.isObj_cod).exists_eval
  exact eval_eq_of_holds (ax_holds hM 97 rfl (by decide) (ts := [m, F, a, b])
    (ws := [wm, wF, wa, wb]) (by simp [hwm, hwF, hwa, hwb]) (by simp [hms, hFs, has, hbs])
    (hs' := [⟨chi m, chi m⟩, ⟨dom F, cod m⟩, ⟨cod F, omega⟩, ⟨comp (truthIncl F) a, m⟩,
      ⟨comp a b, idt (truthEq F)⟩, ⟨comp b a, idt (dom m)⟩]) rfl
    ⟨⟨wc, hwc, hwc⟩, holds_of_eval_eq (hF.eval_dom.trans hm.eval_cod.symm) (hm.eval_cod.trans hx),
      holds_of_eval_eq hF.eval_cod ho, holds_of_eval_eq h₁ hwm, holds_of_eval_eq h₂ hi,
      holds_of_eval_eq (h₃.trans (eval_op₁_congr 2 hm.eval_dom.symm))
        ((eval_op₁_congr 2 hm.eval_dom).trans hj)⟩
    (q := ⟨F, chi m⟩) rfl)

/-- An arrow into the subobject classifier is the characteristic map of its pullback of
truth. -/
theorem chi_truthIncl {F X : Tree} (hF : Hom M ρ F X omega) :
    eval M ρ F = eval M ρ (chi (truthIncl F)) := by
  obtain ⟨hi, -⟩ := truthIncl_hom hM hF
  have hid := idt_hom hM hi.isObj_dom
  exact eq_chi_of_iso hM hi (holds_monoCond_truthIncl hM hF) hF hid hid (comp_idt hM hi)
    (idt_comp hM hid) (idt_comp hM hid)

/-- Two arrows into the subobject classifier, each true on the other's pullback of truth, are
equal. -/
theorem omega_ext {F P X : Tree} (hF : Hom M ρ F X omega) (hP : Hom M ρ P X omega)
    (h₁ : eval M ρ (comp P (truthIncl F)) = eval M ρ (comp tru (bang (truthEq F))))
    (h₂ : eval M ρ (comp F (truthIncl P)) = eval M ρ (comp tru (bang (truthEq P)))) :
    eval M ρ F = eval M ρ P := by
  obtain ⟨hiF, -⟩ := truthIncl_hom hM hF
  obtain ⟨hiP, -⟩ := truthIncl_hom hM hP
  obtain ⟨ha, ha₁⟩ := truthLift_hom hM hP hiF h₁
  obtain ⟨hb, hb₁⟩ := truthLift_hom hM hF hiP h₂
  have h₂' : eval M ρ (comp (truthLift P (truthIncl F)) (truthLift F (truthIncl P))) =
      eval M ρ (idt (truthEq P)) :=
    truthIncl_cancel hM hP (comp_hom hM hb ha) (idt_hom hM hiP.isObj_dom)
      ((comp_assoc hM hb ha hiP).trans ((eval_op₂_congr 3 ha₁ rfl).trans
        (hb₁.trans (comp_idt hM hiP).symm)))
  have h₃' : eval M ρ (comp (truthLift F (truthIncl P)) (truthLift P (truthIncl F))) =
      eval M ρ (idt (truthEq F)) :=
    truthIncl_cancel hM hF (comp_hom hM ha hb) (idt_hom hM hiF.isObj_dom)
      ((comp_assoc hM ha hb hiF).trans ((eval_op₂_congr 3 hb₁ rfl).trans
        (ha₁.trans (comp_idt hM hiF).symm)))
  exact (chi_truthIncl hM hF).trans (eq_chi_of_iso hM hiF (holds_monoCond_truthIncl hM hF) hP
    ha hb ha₁ h₂' h₃').symm

/-- The characteristic map of the diagonal is true after a pairing only if its arrows are
equal. -/
theorem eq_of_chi_diag {f g X A : Tree} (hf : Hom M ρ f X A) (hg : Hom M ρ g X A)
    (h : eval M ρ (comp (chi (diag A)) (pair f g)) = eval M ρ (comp tru (bang X))) :
    eval M ρ f = eval M ρ g := by
  have hA := hf.isObj_cod
  have hm := diag_hom hM hA
  have hφ := chi_diag_hom hM hA
  obtain ⟨wm, hwm, hms⟩ := hm.exists_eval
  obtain ⟨wc, hwc, -⟩ := hφ.exists_eval
  have hts : [diag A].map (eval M ρ) = [wm].map Part.some := by simp [hwm]
  have hs : [wm].map Sigma.fst = [arr] := by simp [hms]
  have hc : Eqn.Holds M ρ ⟨chi (diag A), chi (diag A)⟩ := ⟨wc, hwc, hwc⟩
  obtain ⟨wi, hwi, -⟩ := ax_holds hM 92 rfl (by decide) hts hs
    (hs' := [⟨chi (diag A), chi (diag A)⟩]) rfl hc (q := ⟨chiInv (diag A), chiInv (diag A)⟩) rfl
  obtain ⟨hincl, -⟩ := truthIncl_hom hM hφ
  have hci : Hom M ρ (chiInv (diag A)) (truthEq (chi (diag A))) A :=
    ⟨wi, hwi, sort_of_eval_op rfl hwi, hincl.isObj_dom, hA,
      eval_eq_of_holds (ax_holds hM 93 rfl (by decide) hts hs
        (hs' := [⟨chi (diag A), chi (diag A)⟩]) rfl hc
        (q := ⟨dom (chiInv (diag A)), truthEq (chi (diag A))⟩) rfl),
      (eval_eq_of_holds (ax_holds hM 94 rfl (by decide) hts hs
        (hs' := [⟨chi (diag A), chi (diag A)⟩]) rfl hc
        (q := ⟨cod (chiInv (diag A)), dom (diag A)⟩) rfl)).trans hm.eval_dom⟩
  have h90 := (eval_eq_of_holds (ax_holds hM 90 rfl (by decide) hts hs
    (hs' := [⟨chi (diag A), chi (diag A)⟩]) rfl hc
    (q := ⟨comp (chi (diag A)) (diag A), comp tru (bang (dom (diag A)))⟩) rfl)).trans
    (eval_op₂_congr 3 rfl (eval_op₁_congr 5 hm.eval_dom))
  obtain ⟨htl, htl₁⟩ := truthLift_hom hM hφ hm h90
  have h95 := eval_eq_of_holds (ax_holds hM 95 rfl (by decide) hts hs
    (hs' := [⟨chi (diag A), chi (diag A)⟩]) rfl hc
    (q := ⟨comp (truthLift (chi (diag A)) (diag A)) (chiInv (diag A)),
      idt (truthEq (chi (diag A)))⟩) rfl)
  -- the pullback of truth along the characteristic map is the diagonal after its inverse
  have hinc : eval M ρ (truthIncl (chi (diag A))) = eval M ρ (comp (diag A) (chiInv (diag A))) :=
    (comp_idt hM hincl).symm.trans ((eval_op₂_congr 3 rfl h95.symm).trans
      ((comp_assoc hM hci htl hincl).trans (eval_op₂_congr 3 htl₁ rfl)))
  have hk := pair_hom hM hf hg
  obtain ⟨hl, hl₁⟩ := truthLift_hom hM hφ hk h
  have hu := comp_hom hM hl hci
  -- the pairing is the diagonal after an arrow
  have hp : eval M ρ (pair f g) = eval M ρ
      (pair (comp (chiInv (diag A)) (truthLift (chi (diag A)) (pair f g)))
        (comp (chiInv (diag A)) (truthLift (chi (diag A)) (pair f g)))) :=
    hl₁.symm.trans ((eval_op₂_congr 3 hinc rfl).trans
      ((comp_assoc hM hl hci hm).symm.trans (diag_comp hM hu)))
  exact (fst_pair hM hf hg).symm.trans ((eval_op₂_congr 3 rfl hp).trans
    ((fst_pair hM hu hu).trans ((snd_pair hM hu hu).symm.trans
      ((eval_op₂_congr 3 rfl hp).symm.trans (snd_pair hM hf hg)))))

end Classifier

/-- The subobject of an object on which each of a list of arrows into the subobject classifier is
true, with its inclusion: the iterated pullback of truth. -/
def subObj (B : Tree) : List Tree → Tree × Tree :=
  List.rec (B, idt B) fun h _ p ↦ (truthEq (comp h p.2), comp p.2 (truthIncl (comp h p.2)))

/-- The subobject of an object on which arrows are true, with objects substituted, is the
subobject on which their substitutions are true. -/
theorem subst_subObj (θ : List Tree) (B : Tree) :
    ∀ hs : List Tree, (PartialHorn.subst θ (subObj B hs).1, PartialHorn.subst θ (subObj B hs).2) =
      subObj (PartialHorn.subst θ B) (hs.map (PartialHorn.subst θ)) :=
  List.rec (by simp [subObj, subst_idt]) fun h hs ih ↦ by
    change (PartialHorn.subst θ (truthEq (comp h (subObj B hs).2)),
      PartialHorn.subst θ (comp (subObj B hs).2 (truthIncl (comp h (subObj B hs).2)))) =
      (truthEq (comp (PartialHorn.subst θ h)
          (subObj (PartialHorn.subst θ B) (hs.map (PartialHorn.subst θ))).2),
        comp (subObj (PartialHorn.subst θ B) (hs.map (PartialHorn.subst θ))).2
          (truthIncl (comp (PartialHorn.subst θ h)
            (subObj (PartialHorn.subst θ B) (hs.map (PartialHorn.subst θ))).2)))
    rw [← ih]
    simp [truthEq, truthIncl, eqz, eqIncl, subst_comp, subst_op, subst_bang, tru, dom]

section Subobjects

variable (hM : IsModel (ext defs) M)
include hM

/-- The inclusion of the subobject on which arrows into the subobject classifier are true is an
arrow, after which each is true. -/
theorem subObj_hom {B : Tree} (hB : IsObj M ρ B) :
    ∀ hs : List Tree, (∀ h ∈ hs, Hom M ρ h B omega) →
      Hom M ρ (subObj B hs).2 (subObj B hs).1 B ∧
        ∀ h ∈ hs, eval M ρ (comp h (subObj B hs).2) =
          eval M ρ (comp tru (bang (subObj B hs).1)) :=
  List.rec (fun _ ↦ ⟨idt_hom hM hB, fun _ h ↦ by simp at h⟩) fun h hs ih hh ↦ by
    obtain ⟨hm, hms⟩ := ih fun h' hh' ↦ hh h' (List.mem_cons_of_mem _ hh')
    have hφ := comp_hom hM hm (hh h List.mem_cons_self)
    obtain ⟨hi, hφi⟩ := truthIncl_hom hM hφ
    refine ⟨comp_hom hM hi hm, fun h' hh' ↦ ?_⟩
    rcases List.mem_cons.mp hh' with rfl | hh'
    · exact (comp_assoc hM hi hm (hh h' List.mem_cons_self)).trans hφi
    · exact (comp_assoc hM hi hm (hh h' (List.mem_cons_of_mem _ hh'))).trans
        ((eval_op₂_congr 3 (hms h' hh') rfl).trans (truth_comp hM hi))

/-- An arrow after which arrows into the subobject classifier are true factors through the
subobject on which they are true. -/
theorem subObj_lift {B T X : Tree} (hB : IsObj M ρ B) (hT : Hom M ρ T X B) :
    ∀ hs : List Tree, (∀ h ∈ hs, Hom M ρ h B omega) →
      (∀ h ∈ hs, eval M ρ (comp h T) = eval M ρ (comp tru (bang X))) →
      ∃ l, Hom M ρ l X (subObj B hs).1 ∧ eval M ρ (comp (subObj B hs).2 l) = eval M ρ T :=
  List.rec (fun _ _ ↦ ⟨T, hT, idt_comp hM hT⟩) fun h hs ih hh hhT ↦ by
    have hh' : ∀ h' ∈ hs, Hom M ρ h' B omega := fun h' hh' ↦ hh h' (List.mem_cons_of_mem _ hh')
    obtain ⟨l₀, hl₀, hl₀T⟩ := ih hh' fun h' hh'' ↦ hhT h' (List.mem_cons_of_mem _ hh'')
    obtain ⟨hm, -⟩ := subObj_hom hM hB hs hh'
    have hhh := hh h List.mem_cons_self
    have hφ := comp_hom hM hm hhh
    obtain ⟨hl, hl₁⟩ := truthLift_hom hM hφ hl₀ ((comp_assoc hM hl₀ hm hhh).symm.trans
      ((eval_op₂_congr 3 rfl hl₀T).trans (hhT h List.mem_cons_self)))
    obtain ⟨hi, -⟩ := truthIncl_hom hM hφ
    exact ⟨_, hl, (comp_assoc hM hl hi hm).symm.trans ((eval_op₂_congr 3 rfl hl₁).trans hl₀T)⟩

end Subobjects

section Induction

variable (hM : IsModel (ext defs) M)
include hM

/-- Induction on the natural numbers object with a parameter: an arrow into the subobject
classifier from the product of an object of parameters with the natural numbers object that is
true at zero and, where it is true, at the successor, is true. -/
theorem truth_of_natInd {F P : Tree} (hP : IsObj M ρ P) (hF : Hom M ρ F (prod P nat) omega)
    (h₀ : eval M ρ (comp F (pair (idt P) (comp zeroN (bang P)))) =
      eval M ρ (comp tru (bang P)))
    (h₁ : eval M ρ (comp (comp F (pair (fst P nat) (comp succ (snd P nat)))) (truthIncl F)) =
      eval M ρ (comp tru (bang (truthEq F)))) :
    eval M ρ F = eval M ρ (comp tru (bang (prod P nat))) := by
  have hN := isObj_nat (ρ := ρ) hM
  have hPN := isObj_prod hM hP hN
  obtain ⟨hi, hFi⟩ := truthIncl_hom hM hF
  have hT := hi.isObj_dom
  have hid := idt_hom hM hP
  have hzb := comp_hom hM (bang_hom hM hP) (zeroN_hom hM)
  have hz0 := pair_hom hM hid hzb
  obtain ⟨hz, hz₁⟩ := truthLift_hom hM hF hz0 h₀
  have hfN := fst_hom hM hP hN
  have hsN := snd_hom hM hP hN
  have hsc := comp_hom hM hsN (succ_hom hM)
  have hk₁ := pair_hom hM hfN hsc
  have hki := comp_hom hM hi hk₁
  obtain ⟨hs, hs₁⟩ := truthLift_hom hM hF hki ((comp_assoc hM hi hk₁ hF).trans h₁)
  have hsT := snd_hom hM hP hT
  obtain ⟨f, hf, hf₀, hf₁⟩ := natRec_param_exists hM hP hz (comp_hom hM hsT hs)
  have hg := comp_hom hM hf hi
  have hidPN := idt_hom hM hPN
  have hsPN := snd_hom hM hP hPN
  have hS' := comp_hom hM hsPN hk₁
  -- the inclusion after the fold satisfies the recursion of the identity
  have e₀ : eval M ρ (comp (comp (truthIncl F) f) (pair (idt P) (comp zeroN (bang P)))) =
      eval M ρ (comp (idt (prod P nat)) (pair (idt P) (comp zeroN (bang P)))) :=
    (comp_assoc hM hz0 hf hi).symm.trans ((eval_op₂_congr 3 rfl hf₀).trans
      (hz₁.trans (idt_comp hM hz0).symm))
  have e₁ : eval M ρ (comp (comp (truthIncl F) f) (pair (fst P nat) (comp succ (snd P nat)))) =
      eval M ρ (comp (comp (pair (fst P nat) (comp succ (snd P nat))) (snd P (prod P nat)))
        (pair (fst P nat) (comp (truthIncl F) f))) := by
    refine (comp_assoc hM hk₁ hf hi).symm.trans ((eval_op₂_congr 3 rfl hf₁).trans ?_)
    refine (eval_op₂_congr 3 rfl ((comp_assoc hM (pair_hom hM hfN hf) hsT hs).symm.trans
      (eval_op₂_congr 3 rfl (snd_pair hM hfN hf)))).trans ?_
    refine (comp_assoc hM hf hs hi).trans ((eval_op₂_congr 3 hs₁ rfl).trans ?_)
    refine (comp_assoc hM hf hi hk₁).symm.trans ?_
    exact (eval_op₂_congr 3 rfl (snd_pair hM hfN hg).symm).trans
      (comp_assoc hM (pair_hom hM hfN hg) hsPN hk₁)
  have e₂ : eval M ρ (comp (idt (prod P nat)) (pair (fst P nat) (comp succ (snd P nat)))) =
      eval M ρ (comp (comp (pair (fst P nat) (comp succ (snd P nat))) (snd P (prod P nat)))
        (pair (fst P nat) (idt (prod P nat)))) :=
    (idt_comp hM hk₁).trans ((comp_idt hM hk₁).symm.trans ((eval_op₂_congr 3 rfl
      (snd_pair hM hfN hidPN).symm).trans (comp_assoc hM (pair_hom hM hfN hidPN) hsPN hk₁)))
  have hgid := natRec_param_unique hM hP hg hidPN hS' e₀ e₁ e₂
  exact (comp_idt hM hF).symm.trans ((eval_op₂_congr 3 rfl hgid.symm).trans
    ((comp_assoc hM hf hi hF).trans ((eval_op₂_congr 3 hFi rfl).trans (truth_comp hM hf))))

/-- Induction on a list object with a parameter: an arrow into the subobject classifier from the
product of an object of parameters with the list object that is true at the empty list and, at a
construction, where it is true at the tail, is true. -/
theorem truth_of_listInd {F P A : Tree} (hP : IsObj M ρ P) (hA : IsObj M ρ A)
    (hF : Hom M ρ F (prod P (list A)) omega)
    (h₀ : eval M ρ (comp F (pair (idt P) (comp (nil A) (bang P)))) =
      eval M ρ (comp tru (bang P)))
    (h₁ : eval M ρ (comp (comp F (pair (comp (fst P A) (fst (prod P A) (list A)))
        (comp (cons A) (pair (comp (snd P A) (fst (prod P A) (list A)))
          (snd (prod P A) (list A))))))
        (truthIncl (comp F (pair (comp (fst P A) (fst (prod P A) (list A)))
          (snd (prod P A) (list A)))))) =
      eval M ρ (comp tru (bang (truthEq (comp F (pair (comp (fst P A) (fst (prod P A) (list A)))
        (snd (prod P A) (list A)))))))) :
    eval M ρ F = eval M ρ (comp tru (bang (prod P (list A)))) := by
  have hL := isObj_list hM hA
  have hPL := isObj_prod hM hP hL
  have hPA := isObj_prod hM hP hA
  have hfQ := fst_hom hM hPA hL
  have hsQ := snd_hom hM hPA hL
  have hfPA := fst_hom hM hP hA
  have hsPA := snd_hom hM hP hA
  have hff := comp_hom hM hfQ hfPA
  have hsf := comp_hom hM hfQ hsPA
  have hel := pair_hom hM hsf hsQ
  have hcel := comp_hom hM hel (cons_hom hM hA)
  have hk₁ := pair_hom hM hff hcel
  have hk₂ := pair_hom hM hff hsQ
  have hFk₂ := comp_hom hM hk₂ hF
  have hFk₁ := comp_hom hM hk₁ hF
  obtain ⟨hi, hFi⟩ := truthIncl_hom hM hF
  have hT := hi.isObj_dom
  -- the start
  have hid := idt_hom hM hP
  have hnb := comp_hom hM (bang_hom hM hP) (nil_hom hM hA)
  have hz0 := pair_hom hM hid hnb
  obtain ⟨hz, hz₁⟩ := truthLift_hom hM hF hz0 h₀
  -- the arrow into the step's domain, from the element and a point of the lists' product
  have hfP := fst_hom hM hP hL
  have hsL := snd_hom hM hP hL
  have hfX := fst_hom hM hPA hPL
  have hsX := snd_hom hM hPA hPL
  have hr' := pair_hom hM (pair_hom hM (comp_hom hM hsX hfP) (comp_hom hM hfX hsPA))
    (comp_hom hM hsX hsL)
  have rp : ∀ {Y p l : Tree}, Hom M ρ p Y (prod P A) → Hom M ρ l Y (prod P (list A)) →
      eval M ρ (comp (pair (pair (comp (fst P (list A)) (snd (prod P A) (prod P (list A))))
          (comp (snd P A) (fst (prod P A) (prod P (list A)))))
          (comp (snd P (list A)) (snd (prod P A) (prod P (list A))))) (pair p l)) =
        eval M ρ (pair (pair (comp (fst P (list A)) l) (comp (snd P A) p))
          (comp (snd P (list A)) l)) := fun {Y p l} hp hl ↦ by
    have hpl := pair_hom hM hp hl
    refine (pair_comp hM (pair_hom hM (comp_hom hM hsX hfP) (comp_hom hM hfX hsPA))
      (comp_hom hM hsX hsL) hpl).trans (eval_op₂_congr 9 ?_ ?_)
    · exact (pair_comp hM (comp_hom hM hsX hfP) (comp_hom hM hfX hsPA) hpl).trans
        (eval_op₂_congr 9 ((comp_assoc hM hpl hsX hfP).symm.trans
          (eval_op₂_congr 3 rfl (snd_pair hM hp hl)))
          ((comp_assoc hM hpl hfX hsPA).symm.trans (eval_op₂_congr 3 rfl (fst_pair hM hp hl))))
    · exact (comp_assoc hM hpl hsX hsL).symm.trans (eval_op₂_congr 3 rfl (snd_pair hM hp hl))
  -- the pair of the parameter and the tail, after that arrow, is the point of the lists' product
  have hk₂r' : eval M ρ (comp (pair (comp (fst P A) (fst (prod P A) (list A)))
        (snd (prod P A) (list A)))
      (pair (pair (comp (fst P (list A)) (snd (prod P A) (prod P (list A))))
        (comp (snd P A) (fst (prod P A) (prod P (list A)))))
        (comp (snd P (list A)) (snd (prod P A) (prod P (list A)))))) =
      eval M ρ (snd (prod P A) (prod P (list A))) := by
    have hq1 := pair_hom hM (comp_hom hM hsX hfP) (comp_hom hM hfX hsPA)
    refine (pair_comp hM hff hsQ hr').trans (Eq.trans ?_ (pair_eta hM hP hL hsX))
    refine eval_op₂_congr 9 ((comp_assoc hM hr' hfQ hfPA).symm.trans ?_) (snd_pair hM hq1
      (comp_hom hM hsX hsL))
    exact (eval_op₂_congr 3 rfl (fst_pair hM hq1 (comp_hom hM hsX hsL))).trans
      (fst_pair hM (comp_hom hM hsX hfP) (comp_hom hM hfX hsPA))
  -- the step, on the subobject: the construction of the element onto the point's tail
  have hfT := fst_hom hM hPA hT
  have hsT := snd_hom hM hPA hT
  have hisT := comp_hom hM hsT hi
  have hu := pair_hom hM hfT hisT
  have hr := comp_hom hM hu hr'
  have hk₂r : eval M ρ (comp (comp F (pair (comp (fst P A) (fst (prod P A) (list A)))
        (snd (prod P A) (list A))))
      (comp (pair (pair (comp (fst P (list A)) (snd (prod P A) (prod P (list A))))
        (comp (snd P A) (fst (prod P A) (prod P (list A)))))
        (comp (snd P (list A)) (snd (prod P A) (prod P (list A)))))
        (pair (fst (prod P A) (truthEq F)) (comp (truthIncl F) (snd (prod P A) (truthEq F)))))) =
      eval M ρ (comp tru (bang (prod (prod P A) (truthEq F)))) := by
    refine (comp_assoc hM hr hk₂ hF).symm.trans (Eq.trans ?_ ((eval_op₂_congr 3 hFi rfl).trans
      (truth_comp hM hsT)))
    refine (eval_op₂_congr 3 rfl ?_).trans (comp_assoc hM hsT hi hF)
    exact (comp_assoc hM hu hr' hk₂).trans ((eval_op₂_congr 3 hk₂r' rfl).trans
      (snd_pair hM hfT hisT))
  obtain ⟨hincl', -⟩ := truthIncl_hom hM hFk₂
  obtain ⟨hrl, hrl₁⟩ := truthLift_hom hM hFk₂ hr hk₂r
  have hk₁r := (comp_assoc hM hr hk₁ hF).trans ((eval_op₂_congr 3 rfl hrl₁.symm).trans
    ((comp_assoc hM hrl hincl' hFk₁).trans ((eval_op₂_congr 3 h₁ rfl).trans
      (truth_comp hM hrl))))
  obtain ⟨hS, hS₁⟩ := truthLift_hom hM hF (comp_hom hM hr hk₁) hk₁r
  obtain ⟨f, hf, hf₀, hf₁⟩ := listRec_param_exists hM hP hA hz hS
  have hg := comp_hom hM hf hi
  have hidPL := idt_hom hM hPL
  have hS' := comp_hom hM hr' hk₁
  -- the inclusion after the fold satisfies the recursion of the identity
  have e₀ : eval M ρ (comp (comp (truthIncl F) f) (pair (idt P) (comp (nil A) (bang P)))) =
      eval M ρ (comp (idt (prod P (list A))) (pair (idt P) (comp (nil A) (bang P)))) :=
    (comp_assoc hM hz0 hf hi).symm.trans ((eval_op₂_congr 3 rfl hf₀).trans
      (hz₁.trans (idt_comp hM hz0).symm))
  have hw := pair_hom hM hfQ (comp_hom hM hk₂ hf)
  have hv := pair_hom hM hfQ (comp_hom hM hk₂ hg)
  have huw : eval M ρ (comp (pair (fst (prod P A) (truthEq F))
        (comp (truthIncl F) (snd (prod P A) (truthEq F))))
      (pair (fst (prod P A) (list A)) (comp f (pair (comp (fst P A) (fst (prod P A) (list A)))
        (snd (prod P A) (list A)))))) =
      eval M ρ (pair (fst (prod P A) (list A)) (comp (comp (truthIncl F) f)
        (pair (comp (fst P A) (fst (prod P A) (list A))) (snd (prod P A) (list A))))) :=
    (pair_comp hM hfT hisT hw).trans (eval_op₂_congr 9 (fst_pair hM hfQ (comp_hom hM hk₂ hf))
      ((comp_assoc hM hw hsT hi).symm.trans ((eval_op₂_congr 3 rfl
        (snd_pair hM hfQ (comp_hom hM hk₂ hf))).trans (comp_assoc hM hk₂ hf hi))))
  have e₁a := (comp_assoc hM hk₁ hf hi).symm.trans ((eval_op₂_congr 3 rfl hf₁).trans
    ((comp_assoc hM hw hS hi).trans (eval_op₂_congr 3 hS₁ rfl)))
  have e₁b := (comp_assoc hM hw hr hk₁).symm.trans (eval_op₂_congr 3 rfl
    ((comp_assoc hM hw hu hr').symm.trans (eval_op₂_congr 3 rfl huw)))
  have e₁ := e₁a.trans (e₁b.trans (comp_assoc hM hv hr' hk₁))
  have hv' := pair_hom hM hfQ (comp_hom hM hk₂ hidPL)
  have hid' : eval M ρ (comp (pair (pair (comp (fst P (list A)) (snd (prod P A) (prod P (list A))))
        (comp (snd P A) (fst (prod P A) (prod P (list A)))))
        (comp (snd P (list A)) (snd (prod P A) (prod P (list A)))))
      (pair (fst (prod P A) (list A)) (comp (idt (prod P (list A)))
        (pair (comp (fst P A) (fst (prod P A) (list A))) (snd (prod P A) (list A)))))) =
      eval M ρ (idt (prod (prod P A) (list A))) := by
    have hik := idt_comp hM hk₂
    refine (rp hfQ (comp_hom hM hk₂ hidPL)).trans ?_
    refine (eval_op₂_congr 9 (eval_op₂_congr 9 ((eval_op₂_congr 3 rfl hik).trans
      (fst_pair hM hff hsQ)) rfl) ((eval_op₂_congr 3 rfl hik).trans (snd_pair hM hff hsQ))).trans ?_
    exact (eval_op₂_congr 9 (pair_eta hM hP hA hfQ) rfl).trans (pair_fst_snd hM hPA hL)
  have e₂ : eval M ρ (comp (idt (prod P (list A))) (pair (comp (fst P A) (fst (prod P A) (list A)))
        (comp (cons A) (pair (comp (snd P A) (fst (prod P A) (list A)))
          (snd (prod P A) (list A)))))) = eval M ρ
      (comp (comp (pair (comp (fst P A) (fst (prod P A) (list A)))
          (comp (cons A) (pair (comp (snd P A) (fst (prod P A) (list A)))
            (snd (prod P A) (list A)))))
          (pair (pair (comp (fst P (list A)) (snd (prod P A) (prod P (list A))))
            (comp (snd P A) (fst (prod P A) (prod P (list A)))))
            (comp (snd P (list A)) (snd (prod P A) (prod P (list A))))))
        (pair (fst (prod P A) (list A)) (comp (idt (prod P (list A)))
          (pair (comp (fst P A) (fst (prod P A) (list A))) (snd (prod P A) (list A)))))) :=
    (idt_comp hM hk₁).trans (Eq.symm ((comp_assoc hM hv' hr' hk₁).symm.trans
      ((eval_op₂_congr 3 rfl hid').trans (comp_idt hM hk₁))))
  have hgid := listRec_param_unique hM hP hA hg hidPL hS' e₀ e₁ e₂
  exact (comp_idt hM hF).symm.trans ((eval_op₂_congr 3 rfl hgid.symm).trans
    ((comp_assoc hM hf hi hF).trans ((eval_op₂_congr 3 hFi rfl).trans (truth_comp hM hf))))


end Induction

end Geb.FreeTopos

end
