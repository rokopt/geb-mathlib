/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Arrows
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The folds of a model of the theory

The natural numbers object and the list objects of a model of the theory of an elementary topos,
stated of the values of terms at an assignment: the typings of zero, the successor, the empty
list and construction, and the computation and the uniqueness of the folds, each an instance of
an axiom. A fold is determined, in a cartesian closed category, by its equations with a
parameter ({cite}`EscardoSimpson2025`, Proposition 2.3): two arrows from the product of an
object of parameters with the natural numbers object that agree at zero and satisfy the
recursion equation of one step are equal ({lit}`natRec_param_unique`), and likewise from its
product with a list object ({lit}`listRec_param_unique`). The proof curries the two arrows
into arrows from the natural numbers object, or from the list object, into the exponential of
the parameters, which satisfy the equations of one fold without parameters.

## Main statements

* {lit}`natRec_zero`, {lit}`natRec_succ`, {lit}`natRec_unique` — the fold of the natural numbers
  object.
* {lit}`listRec_nil`, {lit}`listRec_cons`, {lit}`listRec_unique` — the fold of a list object.
* {lit}`natRec_param_unique`, {lit}`listRec_param_unique` — the uniqueness of the folds with a
  parameter.

## References

* {cite}`EscardoSimpson2025`

## Tags

elementary topos, natural numbers object, list object, parametrised recursion
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos

open PartialHorn Sorts
open scoped FinEnum

universe v

variable {defs : List Defn} {M : Model.{v} (ext defs).sig} {ρ : List M.Val}

/-- The product of an object with an arrow, stated at the arrow's domain. -/
theorem eval_prodMapRight {h L C : Tree} (A : Tree) (hh : Hom M ρ h L C) :
    eval M ρ (prodMapRight A h) = eval M ρ (pair (fst A L) (comp h (snd A L))) :=
  eval_op₂_congr 9 (eval_op₂_congr 7 rfl hh.eval_dom)
    (eval_op₂_congr 3 rfl (eval_op₂_congr 8 rfl hh.eval_dom))

section Folds

variable (hM : IsModel (ext defs) M)
include hM

/-- Zero is an arrow from the terminal object to the natural numbers object. -/
theorem zeroN_hom : Hom M ρ zeroN one nat := by
  have hd := eval_eq_of_holds (ax_holds (ρ := ρ) hM 98 rfl (by decide) (ts := []) (ws := []) rfl
    rfl rfl trivial (q := ⟨dom zeroN, one⟩) rfl)
  obtain ⟨o, ho, -⟩ := isObj_one (ρ := ρ) hM
  obtain ⟨w, hw⟩ := exists_eval_of_dom (hd.trans ho)
  exact ⟨w, hw, sort_of_eval_op rfl hw, isObj_one hM, isObj_nat hM, hd,
    eval_eq_of_holds (ax_holds (ρ := ρ) hM 99 rfl (by decide) (ts := []) (ws := []) rfl rfl rfl
      trivial (q := ⟨cod zeroN, nat⟩) rfl)⟩

/-- The successor is an arrow from the natural numbers object to itself. -/
theorem succ_hom : Hom M ρ succ nat nat := by
  have hd := eval_eq_of_holds (ax_holds (ρ := ρ) hM 100 rfl (by decide) (ts := []) (ws := [])
    rfl rfl rfl trivial (q := ⟨dom succ, nat⟩) rfl)
  obtain ⟨o, ho, -⟩ := isObj_nat (ρ := ρ) hM
  obtain ⟨w, hw⟩ := exists_eval_of_dom (hd.trans ho)
  exact ⟨w, hw, sort_of_eval_op rfl hw, isObj_nat hM, isObj_nat hM, hd,
    eval_eq_of_holds (ax_holds (ρ := ρ) hM 101 rfl (by decide) (ts := []) (ws := []) rfl rfl rfl
      trivial (q := ⟨cod succ, nat⟩) rfl)⟩

/-- The empty list is an arrow from the terminal object to the list object. -/
theorem nil_hom {A : Tree} (hA : IsObj M ρ A) : Hom M ρ (nil A) one (list A) := by
  obtain ⟨a, ha, has⟩ := hA
  have hts : [A].map (eval M ρ) = [a].map Part.some := by simp [ha]
  have hs : [a].map Sigma.fst = [obj] := by simp [has]
  have hd := eval_eq_of_holds (ax_holds hM 112 rfl (by decide) hts hs rfl trivial
    (q := ⟨dom (nil A), one⟩) rfl)
  obtain ⟨o, ho, -⟩ := isObj_one (ρ := ρ) hM
  obtain ⟨w, hw⟩ := exists_eval_of_dom (hd.trans ho)
  exact ⟨w, hw, sort_of_eval_op rfl hw, isObj_one hM, isObj_list hM ⟨a, ha, has⟩, hd,
    eval_eq_of_holds (ax_holds hM 113 rfl (by decide) hts hs rfl trivial
      (q := ⟨cod (nil A), list A⟩) rfl)⟩

/-- Construction is an arrow from the product of the element object and the list object to the
list object. -/
theorem cons_hom {A : Tree} (hA : IsObj M ρ A) : Hom M ρ (cons A) (prod A (list A)) (list A) := by
  have hL := isObj_list hM hA
  have hP := isObj_prod hM hA hL
  obtain ⟨a, ha, has⟩ := hA
  have hts : [A].map (eval M ρ) = [a].map Part.some := by simp [ha]
  have hs : [a].map Sigma.fst = [obj] := by simp [has]
  have hd := eval_eq_of_holds (ax_holds hM 114 rfl (by decide) hts hs rfl trivial
    (q := ⟨dom (cons A), prod A (list A)⟩) rfl)
  obtain ⟨p, hp, -⟩ := hP
  obtain ⟨w, hw⟩ := exists_eval_of_dom (hd.trans hp)
  exact ⟨w, hw, sort_of_eval_op rfl hw, isObj_prod hM ⟨a, ha, has⟩ hL, hL, hd,
    eval_eq_of_holds (ax_holds hM 115 rfl (by decide) hts hs rfl trivial
      (q := ⟨cod (cons A), list A⟩) rfl)⟩

/-- The fold of the natural numbers object at zero is the start. -/
theorem natRec_zero {z s C : Tree} (hz : Hom M ρ z one C) (hs : Hom M ρ s C C) :
    eval M ρ (comp (natRec z s) zeroN) = eval M ρ z := by
  obtain ⟨wz, hwz, hzs⟩ := hz.exists_eval
  obtain ⟨ws, hws, hss⟩ := hs.exists_eval
  obtain ⟨w, hw, -⟩ := (natRec_hom hM hz hs).exists_eval
  exact eval_eq_of_holds (ax_holds hM 108 rfl (by decide) (ts := [z, s]) (ws := [wz, ws])
    (by simp [hwz, hws]) (by simp [hzs, hss]) (hs' := [⟨natRec z s, natRec z s⟩]) rfl
    ⟨w, hw, hw⟩ (q := ⟨comp (natRec z s) zeroN, z⟩) rfl)

/-- The fold of the natural numbers object after the successor is the step after the fold. -/
theorem natRec_succ {z s C : Tree} (hz : Hom M ρ z one C) (hs : Hom M ρ s C C) :
    eval M ρ (comp (natRec z s) succ) = eval M ρ (comp s (natRec z s)) := by
  obtain ⟨wz, hwz, hzs⟩ := hz.exists_eval
  obtain ⟨ws, hws, hss⟩ := hs.exists_eval
  obtain ⟨w, hw, -⟩ := (natRec_hom hM hz hs).exists_eval
  exact eval_eq_of_holds (ax_holds hM 109 rfl (by decide) (ts := [z, s]) (ws := [wz, ws])
    (by simp [hwz, hws]) (by simp [hzs, hss]) (hs' := [⟨natRec z s, natRec z s⟩]) rfl
    ⟨w, hw, hw⟩ (q := ⟨comp (natRec z s) succ, comp s (natRec z s)⟩) rfl)

/-- An arrow from the natural numbers object that is the start at zero and the step after
itself at the successor is the fold. -/
theorem natRec_unique {h z s C : Tree} (hz : Hom M ρ z one C) (hs : Hom M ρ s C C)
    (hh : Hom M ρ h nat C) (h₀ : eval M ρ (comp h zeroN) = eval M ρ z)
    (h₁ : eval M ρ (comp h succ) = eval M ρ (comp s h)) :
    eval M ρ h = eval M ρ (natRec z s) := by
  obtain ⟨wz, hwz, hzs⟩ := hz.exists_eval
  obtain ⟨ws, hws, hss⟩ := hs.exists_eval
  obtain ⟨wh, hwh, hhs⟩ := hh.exists_eval
  obtain ⟨w, hw, -⟩ := (natRec_hom hM hz hs).exists_eval
  obtain ⟨n, hn, -⟩ := isObj_nat (ρ := ρ) hM
  obtain ⟨c, hc, -⟩ := (comp_hom hM hh hs).exists_eval
  exact eval_eq_of_holds (ax_holds hM 110 rfl (by decide) (ts := [z, s, h])
    (ws := [wz, ws, wh]) (by simp [hwz, hws, hwh]) (by simp [hzs, hss, hhs])
    (hs' := [⟨natRec z s, natRec z s⟩, ⟨dom h, nat⟩, ⟨comp h zeroN, z⟩,
      ⟨comp h succ, comp s h⟩]) rfl
    ⟨⟨w, hw, hw⟩, holds_of_eval_eq hh.eval_dom hn, holds_of_eval_eq h₀ hwz,
      holds_of_eval_eq h₁ hc⟩ (q := ⟨h, natRec z s⟩) rfl)

/-- The fold of a list object at the empty list is the start. -/
theorem listRec_nil {A z s C : Tree} (hA : IsObj M ρ A) (hz : Hom M ρ z one C)
    (hs : Hom M ρ s (prod A C) C) : eval M ρ (comp (listRec A z s) (nil A)) = eval M ρ z := by
  obtain ⟨a, ha, has⟩ := hA
  obtain ⟨wz, hwz, hzs⟩ := hz.exists_eval
  obtain ⟨ws, hws, hss⟩ := hs.exists_eval
  obtain ⟨w, hw, -⟩ := (listRec_hom hM ⟨a, ha, has⟩ hz hs).exists_eval
  exact eval_eq_of_holds (ax_holds hM 122 rfl (by decide) (ts := [A, z, s]) (ws := [a, wz, ws])
    (by simp [ha, hwz, hws]) (by simp [has, hzs, hss])
    (hs' := [⟨listRec A z s, listRec A z s⟩]) rfl ⟨w, hw, hw⟩
    (q := ⟨comp (listRec A z s) (nil A), z⟩) rfl)

/-- The fold of a list object after construction is the step after the element paired with the
fold of the tail. -/
theorem listRec_cons {A z s C : Tree} (hA : IsObj M ρ A) (hz : Hom M ρ z one C)
    (hs : Hom M ρ s (prod A C) C) :
    eval M ρ (comp (listRec A z s) (cons A)) =
      eval M ρ (comp s (pair (fst A (list A)) (comp (listRec A z s) (snd A (list A))))) := by
  have hr := listRec_hom hM hA hz hs
  obtain ⟨a, ha, has⟩ := hA
  obtain ⟨wz, hwz, hzs⟩ := hz.exists_eval
  obtain ⟨ws, hws, hss⟩ := hs.exists_eval
  obtain ⟨w, hw, -⟩ := hr.exists_eval
  refine (eval_eq_of_holds (ax_holds hM 123 rfl (by decide) (ts := [A, z, s])
    (ws := [a, wz, ws]) (by simp [ha, hwz, hws]) (by simp [has, hzs, hss])
    (hs' := [⟨listRec A z s, listRec A z s⟩]) rfl ⟨w, hw, hw⟩
    (q := ⟨comp (listRec A z s) (cons A), comp s (prodMapRight A (listRec A z s))⟩) rfl)).trans
    ?_
  exact eval_op₂_congr 3 rfl (eval_prodMapRight A hr)

/-- An arrow from a list object that is the start at the empty list and the step after the
element paired with itself at construction is the fold. -/
theorem listRec_unique {h A z s C : Tree} (hA : IsObj M ρ A) (hz : Hom M ρ z one C)
    (hs : Hom M ρ s (prod A C) C) (hh : Hom M ρ h (list A) C)
    (h₀ : eval M ρ (comp h (nil A)) = eval M ρ z)
    (h₁ : eval M ρ (comp h (cons A)) =
      eval M ρ (comp s (pair (fst A (list A)) (comp h (snd A (list A)))))) :
    eval M ρ h = eval M ρ (listRec A z s) := by
  have hL := isObj_list hM hA
  have hc := comp_hom hM (pair_hom hM (fst_hom hM hA hL) (comp_hom hM (snd_hom hM hA hL) hh)) hs
  obtain ⟨a, ha, has⟩ := hA
  obtain ⟨wz, hwz, hzs⟩ := hz.exists_eval
  obtain ⟨ws, hws, hss⟩ := hs.exists_eval
  obtain ⟨wh, hwh, hhs⟩ := hh.exists_eval
  obtain ⟨w, hw, -⟩ := (listRec_hom hM ⟨a, ha, has⟩ hz hs).exists_eval
  obtain ⟨l, hl, -⟩ := hL
  obtain ⟨c, hcv, -⟩ := hc.exists_eval
  exact eval_eq_of_holds (ax_holds hM 124 rfl (by decide) (ts := [A, z, s, h])
    (ws := [a, wz, ws, wh]) (by simp [ha, hwz, hws, hwh]) (by simp [has, hzs, hss, hhs])
    (hs' := [⟨listRec A z s, listRec A z s⟩, ⟨dom h, list A⟩, ⟨comp h (nil A), z⟩,
      ⟨comp h (cons A), comp s (prodMapRight A h)⟩]) rfl
    ⟨⟨w, hw, hw⟩, holds_of_eval_eq hh.eval_dom hl, holds_of_eval_eq h₀ hwz,
      holds_of_eval_eq (h₁.trans (eval_op₂_congr 3 rfl (eval_prodMapRight A hh)).symm)
        ((eval_op₂_congr 3 rfl (eval_prodMapRight A hh)).trans hcv)⟩
    (q := ⟨h, listRec A z s⟩) rfl)

end Folds

section Parameters

variable (hM : IsModel (ext defs) M)
include hM

/-- The pairing of a product's projections is its identity. -/
theorem pair_fst_snd {A B : Tree} (hA : IsObj M ρ A) (hB : IsObj M ρ B) :
    eval M ρ (pair (fst A B) (snd A B)) = eval M ρ (idt (prod A B)) :=
  (eval_op₂_congr 9 (comp_idt hM (fst_hom hM hA hB)).symm
    (comp_idt hM (snd_hom hM hA hB)).symm).trans
    (pair_eta hM hA hB (idt_hom hM (isObj_prod hM hA hB)))

/-- The exchange of a product's factors after a pairing is the exchanged pairing. -/
theorem swap_pair {f g X A B : Tree} (hf : Hom M ρ f X A) (hg : Hom M ρ g X B) :
    eval M ρ (comp (pair (snd A B) (fst A B)) (pair f g)) = eval M ρ (pair g f) :=
  (pair_comp hM (snd_hom hM hf.isObj_cod hg.isObj_cod) (fst_hom hM hf.isObj_cod hg.isObj_cod)
    (pair_hom hM hf hg)).trans (eval_op₂_congr 9 (snd_pair hM hf hg) (fst_pair hM hf hg))

/-- Two arrows from a product that agree after the exchange of its factors are equal. -/
theorem eq_of_comp_swap {F G A B C : Tree} (hA : IsObj M ρ A) (hB : IsObj M ρ B)
    (hF : Hom M ρ F (prod A B) C) (hG : Hom M ρ G (prod A B) C)
    (h : eval M ρ (comp F (pair (snd B A) (fst B A))) =
      eval M ρ (comp G (pair (snd B A) (fst B A)))) :
    eval M ρ F = eval M ρ G := by
  have hsw := pair_hom hM (snd_hom hM hB hA) (fst_hom hM hB hA)
  have hsw' := pair_hom hM (snd_hom hM hA hB) (fst_hom hM hA hB)
  have hid := (swap_pair hM (snd_hom hM hA hB) (fst_hom hM hA hB)).trans (pair_fst_snd hM hA hB)
  have key : ∀ {H : Tree}, Hom M ρ H (prod A B) C → eval M ρ H =
      eval M ρ (comp (comp H (pair (snd B A) (fst B A))) (pair (snd A B) (fst A B))) :=
    fun hH ↦ (comp_idt hM hH).symm.trans
      ((eval_op₂_congr 3 rfl hid.symm).trans (comp_assoc hM hsw' hsw hH))
  exact (key hF).trans ((eval_op₂_congr 3 h rfl).trans (key hG).symm)

/-- The currying, over the second factor, of an arrow from a product with its factors exchanged,
after an arrow into the first factor, is the currying of the arrow after the pairing of the
second factor with the arrow. -/
theorem curry_swap_comp {F h P D Y C : Tree} (hP : IsObj M ρ P) (hF : Hom M ρ F (prod P D) C)
    (hh : Hom M ρ h Y D) :
    eval M ρ (comp (curry D P (comp F (pair (snd D P) (fst D P)))) h) =
      eval M ρ (curry Y P (comp F (pair (snd Y P) (comp h (fst Y P))))) := by
  have hD := hh.isObj_cod
  have hY := hh.isObj_dom
  have hsw := pair_hom hM (snd_hom hM hD hP) (fst_hom hM hD hP)
  have hhf := comp_hom hM (fst_hom hM hY hP) hh
  have hk := pair_hom hM hhf (snd_hom hM hY hP)
  refine (curry_comp hM hP (comp_hom hM hsw hF) hh).trans (eval_op₃_congr 24 rfl rfl ?_)
  exact (comp_assoc hM hk hsw hF).symm.trans
    (eval_op₂_congr 3 rfl (swap_pair hM hhf (snd_hom hM hY hP)))

/-- Two arrows from a product whose curryings over its first factor, with the factors exchanged,
are equal are equal. -/
theorem eq_of_curry_swap {F G P D C : Tree} (hP : IsObj M ρ P) (hD : IsObj M ρ D)
    (hF : Hom M ρ F (prod P D) C) (hG : Hom M ρ G (prod P D) C)
    (h : eval M ρ (curry D P (comp F (pair (snd D P) (fst D P)))) =
      eval M ρ (curry D P (comp G (pair (snd D P) (fst D P))))) :
    eval M ρ F = eval M ρ G := by
  have hsw := pair_hom hM (snd_hom hM hD hP) (fst_hom hM hD hP)
  refine eq_of_comp_swap hM hP hD hF hG ?_
  exact (ev_curry hM hD hP (comp_hom hM hsw hF)).symm.trans
    ((eval_op₂_congr 3 rfl (eval_op₂_congr 9 (eval_op₂_congr 3 h rfl) rfl)).trans
      (ev_curry hM hD hP (comp_hom hM hsw hG)))

/-- The uniqueness of the fold of the natural numbers object with a parameter: two arrows from
the product of an object of parameters with the natural numbers object that agree at zero, and
each of which is at a successor the step after the parameter paired with its value, are
equal. -/
theorem natRec_param_unique {F G S P C : Tree} (hP : IsObj M ρ P)
    (hF : Hom M ρ F (prod P nat) C) (hG : Hom M ρ G (prod P nat) C)
    (hS : Hom M ρ S (prod P C) C)
    (h₀ : eval M ρ (comp F (pair (idt P) (comp zeroN (bang P)))) =
      eval M ρ (comp G (pair (idt P) (comp zeroN (bang P)))))
    (hF₁ : eval M ρ (comp F (pair (fst P nat) (comp succ (snd P nat)))) =
      eval M ρ (comp S (pair (fst P nat) F)))
    (hG₁ : eval M ρ (comp G (pair (fst P nat) (comp succ (snd P nat)))) =
      eval M ρ (comp S (pair (fst P nat) G))) :
    eval M ρ F = eval M ρ G := by
  have hN := isObj_nat (ρ := ρ) hM
  have h1 := isObj_one (ρ := ρ) hM
  have hC := hF.isObj_cod
  have hE := isObj_exp hM hP hC
  have hs1 := snd_hom hM h1 hP
  have hfN := fst_hom hM hN hP
  have hsN := snd_hom hM hN hP
  have hfP := fst_hom hM hP hN
  have hsP := snd_hom hM hP hN
  have hsw := pair_hom hM hsN hfN
  have hzb := comp_hom hM (bang_hom hM hP) (zeroN_hom hM)
  have hz0 := pair_hom hM (idt_hom hM hP) hzb
  have hsc := comp_hom hM hsP (succ_hom hM)
  have hstep := pair_hom hM hfP hsc
  have hsE := snd_hom hM hE hP
  have hev := ev_hom hM hP hC
  have hSb := comp_hom hM (pair_hom hM hsE hev) hS
  have hZ := curry_hom hM h1 hP (comp_hom hM hs1 (comp_hom hM hz0 hF))
  have hStep := curry_hom hM hE hP hSb
  -- the pairing of the successor with the parameter is the step after the exchange
  have e₁ : eval M ρ (pair (snd nat P) (comp succ (fst nat P))) =
      eval M ρ (comp (pair (fst P nat) (comp succ (snd P nat))) (pair (snd nat P) (fst nat P))) :=
    ((pair_comp hM hfP hsc hsw).trans (eval_op₂_congr 9 (fst_pair hM hsN hfN)
      ((comp_assoc hM hsw hsP (succ_hom hM)).symm.trans
        (eval_op₂_congr 3 rfl (snd_pair hM hsN hfN))))).symm
  -- the pairing of zero with the parameter is the start after the second projection
  have e₀ : eval M ρ (pair (snd one P) (comp zeroN (fst one P))) =
      eval M ρ (comp (pair (idt P) (comp zeroN (bang P))) (snd one P)) :=
    ((pair_comp hM (idt_hom hM hP) hzb hs1).trans (eval_op₂_congr 9 (idt_comp hM hs1)
      ((comp_assoc hM hs1 (bang_hom hM hP) (zeroN_hom hM)).symm.trans (eval_op₂_congr 3 rfl
        ((comp_bang hM hs1).trans (bang_unique hM (fst_hom hM h1 hP)).symm))))).symm
  -- the currying of each arrow is the fold
  have key : ∀ {H : Tree}, Hom M ρ H (prod P nat) C →
      eval M ρ (comp H (pair (idt P) (comp zeroN (bang P)))) =
        eval M ρ (comp F (pair (idt P) (comp zeroN (bang P)))) →
      eval M ρ (comp H (pair (fst P nat) (comp succ (snd P nat)))) =
        eval M ρ (comp S (pair (fst P nat) H)) →
      eval M ρ (curry nat P (comp H (pair (snd nat P) (fst nat P)))) =
        eval M ρ (natRec (curry one P (comp (comp F (pair (idt P) (comp zeroN (bang P))))
          (snd one P))) (curry (exp P C) P (comp S (pair (snd (exp P C) P) (ev P C))))) := by
    intro H hH hH₀ hH₁
    have hHsw := comp_hom hM hsw hH
    have hc := curry_hom hM hN hP hHsw
    have hcf := comp_hom hM hfN hc
    have hk := pair_hom hM hcf hsN
    refine natRec_unique hM hZ hStep hc ?_ ?_
    · refine (curry_swap_comp hM hP hH (zeroN_hom hM)).trans (eval_op₃_congr 24 rfl rfl ?_)
      exact (eval_op₂_congr 3 rfl e₀).trans
        ((comp_assoc hM hs1 hz0 hH).trans (eval_op₂_congr 3 hH₀ rfl))
    · refine (curry_swap_comp hM hP hH (succ_hom hM)).trans
        (Eq.trans ?_ (curry_comp hM hP hSb hc).symm)
      refine eval_op₃_congr 24 rfl rfl ?_
      refine ((eval_op₂_congr 3 rfl e₁).trans ((comp_assoc hM hsw hstep hH).trans
        ((eval_op₂_congr 3 hH₁ rfl).trans ((comp_assoc hM hsw (pair_hom hM hfP hH) hS).symm.trans
          (eval_op₂_congr 3 rfl ((pair_comp hM hfP hH hsw).trans
            (eval_op₂_congr 9 (fst_pair hM hsN hfN) rfl))))))).trans ?_
      exact Eq.symm ((comp_assoc hM hk (pair_hom hM hsE hev) hS).symm.trans
        (eval_op₂_congr 3 rfl ((pair_comp hM hsE hev hk).trans
          (eval_op₂_congr 9 (snd_pair hM hcf hsN) (ev_curry hM hN hP hHsw)))))
  exact eq_of_curry_swap hM hP hN hF hG ((key hF rfl hF₁).trans (key hG h₀.symm hG₁).symm)

/-- The uniqueness of the fold of a list object with a parameter: two arrows from the product of
an object of parameters with the list object that agree at the empty list, and each of which is
at a construction the step after the parameter and the element paired with its value at the
tail, are equal. -/
theorem listRec_param_unique {F G S P A C : Tree} (hP : IsObj M ρ P) (hA : IsObj M ρ A)
    (hF : Hom M ρ F (prod P (list A)) C) (hG : Hom M ρ G (prod P (list A)) C)
    (hS : Hom M ρ S (prod (prod P A) C) C)
    (h₀ : eval M ρ (comp F (pair (idt P) (comp (nil A) (bang P)))) =
      eval M ρ (comp G (pair (idt P) (comp (nil A) (bang P)))))
    (hF₁ : eval M ρ (comp F (pair (comp (fst P A) (fst (prod P A) (list A)))
        (comp (cons A) (pair (comp (snd P A) (fst (prod P A) (list A)))
          (snd (prod P A) (list A)))))) =
      eval M ρ (comp S (pair (fst (prod P A) (list A))
        (comp F (pair (comp (fst P A) (fst (prod P A) (list A))) (snd (prod P A) (list A)))))))
    (hG₁ : eval M ρ (comp G (pair (comp (fst P A) (fst (prod P A) (list A)))
        (comp (cons A) (pair (comp (snd P A) (fst (prod P A) (list A)))
          (snd (prod P A) (list A)))))) =
      eval M ρ (comp S (pair (fst (prod P A) (list A))
        (comp G (pair (comp (fst P A) (fst (prod P A) (list A))) (snd (prod P A) (list A))))))) :
    eval M ρ F = eval M ρ G := by
  have h1 := isObj_one (ρ := ρ) hM
  have hL := isObj_list hM hA
  have hC := hF.isObj_cod
  have hE := isObj_exp hM hP hC
  have hPA := isObj_prod hM hP hA
  have hR := isObj_prod hM hA hL
  have hAE := isObj_prod hM hA hE
  have hs1 := snd_hom hM h1 hP
  have hfPA := fst_hom hM hP hA
  have hsPA := snd_hom hM hP hA
  have hfQ := fst_hom hM hPA hL
  have hsQ := snd_hom hM hPA hL
  have hfAL := fst_hom hM hA hL
  have hsAL := snd_hom hM hA hL
  have hfRP := fst_hom hM hR hP
  have hsRP := snd_hom hM hR hP
  have hfLP := fst_hom hM hL hP
  have hsLP := snd_hom hM hL hP
  have hswL := pair_hom hM hsLP hfLP
  have hfE := fst_hom hM hAE hP
  have hsE := snd_hom hM hAE hP
  have hfAE := fst_hom hM hA hE
  have hsAE := snd_hom hM hA hE
  have hev := ev_hom hM hP hC
  have hcons := cons_hom hM hA
  have hnb := comp_hom hM (bang_hom hM hP) (nil_hom hM hA)
  have hn0 := pair_hom hM (idt_hom hM hP) hnb
  have hq := pair_hom hM (comp_hom hM hfQ hsPA) hsQ
  have hk₁ := pair_hom hM (comp_hom hM hfQ hfPA) (comp_hom hM hq hcons)
  have hk₂ := pair_hom hM (comp_hom hM hfQ hfPA) hsQ
  have hpe := pair_hom hM (comp_hom hM hfE hsAE) hsE
  have hbody := pair_hom hM (pair_hom hM hsE (comp_hom hM hfE hfAE)) (comp_hom hM hpe hev)
  have hSb := comp_hom hM hbody hS
  have hZ := curry_hom hM h1 hP (comp_hom hM hs1 (comp_hom hM hn0 hF))
  have hStep := curry_hom hM hAE hP hSb
  have hfr := pair_hom hM hsRP (comp_hom hM hfRP hfAL)
  have hr := pair_hom hM hfr (comp_hom hM hfRP hsAL)
  -- the arrow into the step's domain from the curried domain, and its components
  have fr := fst_pair hM hfr (comp_hom hM hfRP hsAL)
  have sr := snd_pair hM hfr (comp_hom hM hfRP hsAL)
  have pr : eval M ρ (comp (comp (fst P A) (fst (prod P A) (list A)))
      (pair (pair (snd (prod A (list A)) P) (comp (fst A (list A)) (fst (prod A (list A)) P)))
        (comp (snd A (list A)) (fst (prod A (list A)) P)))) =
      eval M ρ (snd (prod A (list A)) P) :=
    (comp_assoc hM hr hfQ hfPA).symm.trans
      ((eval_op₂_congr 3 rfl fr).trans (fst_pair hM hsRP (comp_hom hM hfRP hfAL)))
  have er : eval M ρ (comp (comp (snd P A) (fst (prod P A) (list A)))
      (pair (pair (snd (prod A (list A)) P) (comp (fst A (list A)) (fst (prod A (list A)) P)))
        (comp (snd A (list A)) (fst (prod A (list A)) P)))) =
      eval M ρ (comp (fst A (list A)) (fst (prod A (list A)) P)) :=
    (comp_assoc hM hr hfQ hsPA).symm.trans
      ((eval_op₂_congr 3 rfl fr).trans (snd_pair hM hsRP (comp_hom hM hfRP hfAL)))
  have k₁r := (pair_comp hM (comp_hom hM hfQ hfPA) (comp_hom hM hq hcons) hr).trans
    (eval_op₂_congr 9 pr ((comp_assoc hM hr hq hcons).symm.trans (eval_op₂_congr 3 rfl
      ((pair_comp hM (comp_hom hM hfQ hsPA) hsQ hr).trans
        ((eval_op₂_congr 9 er sr).trans (pair_eta hM hA hL hfRP))))))
  have k₂r := (pair_comp hM (comp_hom hM hfQ hfPA) hsQ hr).trans (eval_op₂_congr 9 pr sr)
  -- the pairing of the empty list with the parameter is the start after the second projection
  have e₀ : eval M ρ (pair (snd one P) (comp (nil A) (fst one P))) =
      eval M ρ (comp (pair (idt P) (comp (nil A) (bang P))) (snd one P)) :=
    ((pair_comp hM (idt_hom hM hP) hnb hs1).trans (eval_op₂_congr 9 (idt_comp hM hs1)
      ((comp_assoc hM hs1 (bang_hom hM hP) (nil_hom hM hA)).symm.trans (eval_op₂_congr 3 rfl
        ((comp_bang hM hs1).trans (bang_unique hM (fst_hom hM h1 hP)).symm))))).symm
  -- the currying of each arrow is the fold
  have key : ∀ {H : Tree}, Hom M ρ H (prod P (list A)) C →
      eval M ρ (comp H (pair (idt P) (comp (nil A) (bang P)))) =
        eval M ρ (comp F (pair (idt P) (comp (nil A) (bang P)))) →
      eval M ρ (comp H (pair (comp (fst P A) (fst (prod P A) (list A)))
          (comp (cons A) (pair (comp (snd P A) (fst (prod P A) (list A)))
            (snd (prod P A) (list A)))))) =
        eval M ρ (comp S (pair (fst (prod P A) (list A))
          (comp H (pair (comp (fst P A) (fst (prod P A) (list A)))
            (snd (prod P A) (list A)))))) →
      eval M ρ (curry (list A) P (comp H (pair (snd (list A) P) (fst (list A) P)))) =
        eval M ρ (listRec A (curry one P (comp (comp F (pair (idt P) (comp (nil A) (bang P))))
          (snd one P))) (curry (prod A (exp P C)) P (comp S
            (pair (pair (snd (prod A (exp P C)) P)
                (comp (fst A (exp P C)) (fst (prod A (exp P C)) P)))
              (comp (ev P C) (pair (comp (snd A (exp P C)) (fst (prod A (exp P C)) P))
                (snd (prod A (exp P C)) P))))))) := by
    intro H hH hH₀ hH₁
    have hHsw := comp_hom hM hswL hH
    have hc := curry_hom hM hL hP hHsw
    have hm := pair_hom hM hfAL (comp_hom hM hsAL hc)
    have hn := pair_hom hM (comp_hom hM hfRP hm) hsRP
    have ht := pair_hom hM (comp_hom hM hfRP hsAL) hsRP
    have hpc := pair_hom hM (comp_hom hM hfLP hc) hsLP
    refine listRec_unique hM hA hZ hStep hc ?_ ?_
    · refine (curry_swap_comp hM hP hH (nil_hom hM hA)).trans (eval_op₃_congr 24 rfl rfl ?_)
      exact (eval_op₂_congr 3 rfl e₀).trans
        ((comp_assoc hM hs1 hn0 hH).trans (eval_op₂_congr 3 hH₀ rfl))
    · refine (curry_swap_comp hM hP hH hcons).trans
        (Eq.trans ?_ (curry_comp hM hP hSb hm).symm)
      refine eval_op₃_congr 24 rfl rfl ?_
      -- the step's equation, after the arrow into its domain
      refine ((eval_op₂_congr 3 rfl k₁r.symm).trans ((comp_assoc hM hr hk₁ hH).trans
        ((eval_op₂_congr 3 hH₁ rfl).trans
          ((comp_assoc hM hr (pair_hom hM hfQ (comp_hom hM hk₂ hH)) hS).symm.trans
            (eval_op₂_congr 3 rfl ((pair_comp hM hfQ (comp_hom hM hk₂ hH) hr).trans
              (eval_op₂_congr 9 fr ((comp_assoc hM hr hk₂ hH).symm.trans
                (eval_op₂_congr 3 rfl k₂r))))))))).trans ?_
      -- the curried step, after the curried arrow paired with the element
      have f1n := fst_pair hM (comp_hom hM hfRP hm) hsRP
      have s1n := snd_pair hM (comp_hom hM hfRP hm) hsRP
      have an := (pair_comp hM hsE (comp_hom hM hfE hfAE) hn).trans (eval_op₂_congr 9 s1n
        ((comp_assoc hM hn hfE hfAE).symm.trans ((eval_op₂_congr 3 rfl f1n).trans
          ((comp_assoc hM hfRP hm hfAE).trans
            (eval_op₂_congr 3 (fst_pair hM hfAL (comp_hom hM hsAL hc)) rfl)))))
      have hx : eval M ρ (comp (pair (comp (snd A (exp P C)) (fst (prod A (exp P C)) P))
            (snd (prod A (exp P C)) P))
          (pair (comp (pair (fst A (list A)) (comp (curry (list A) P
              (comp H (pair (snd (list A) P) (fst (list A) P)))) (snd A (list A))))
            (fst (prod A (list A)) P)) (snd (prod A (list A)) P))) =
          eval M ρ (comp (pair (comp (curry (list A) P
              (comp H (pair (snd (list A) P) (fst (list A) P)))) (fst (list A) P))
            (snd (list A) P))
            (pair (comp (snd A (list A)) (fst (prod A (list A)) P)) (snd (prod A (list A)) P))) :=
        ((pair_comp hM (comp_hom hM hfE hsAE) hsE hn).trans (eval_op₂_congr 9
          ((comp_assoc hM hn hfE hsAE).symm.trans ((eval_op₂_congr 3 rfl f1n).trans
            ((comp_assoc hM hfRP hm hsAE).trans ((eval_op₂_congr 3
              (snd_pair hM hfAL (comp_hom hM hsAL hc)) rfl).trans
                (comp_assoc hM hfRP hsAL hc).symm))))
          s1n)).trans ((pair_comp hM (comp_hom hM hfLP hc) hsLP ht).trans (eval_op₂_congr 9
            ((comp_assoc hM ht hfLP hc).symm.trans (eval_op₂_congr 3 rfl
              (fst_pair hM (comp_hom hM hfRP hsAL) hsRP)))
            (snd_pair hM (comp_hom hM hfRP hsAL) hsRP))).symm
      have evn := (comp_assoc hM hn hpe hev).symm.trans ((eval_op₂_congr 3 rfl hx).trans
        ((comp_assoc hM ht hpc hev).trans ((eval_op₂_congr 3 (ev_curry hM hL hP hHsw) rfl).trans
          ((comp_assoc hM ht hswL hH).symm.trans (eval_op₂_congr 3 rfl
            (swap_pair hM (comp_hom hM hfRP hsAL) hsRP))))))
      exact Eq.symm ((comp_assoc hM hn hbody hS).symm.trans (eval_op₂_congr 3 rfl
        ((pair_comp hM (pair_hom hM hsE (comp_hom hM hfE hfAE)) (comp_hom hM hpe hev) hn).trans
          (eval_op₂_congr 9 an evn))))
  exact eq_of_curry_swap hM hP hL hF hG ((key hF rfl hF₁).trans (key hG h₀.symm hG₁).symm)

end Parameters

end Geb.FreeTopos

end
