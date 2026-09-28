/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Represent
public import Geb.Prototypes.FreeTopos.Internal.Semantics
public import Geb.Prototypes.FreeTopos.Translation
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The translation's library represents its specifications

Each definition of the translation's library ({name}`Geb.FreeTopos.Translation.lib`), compiled
with the definitions before it and unfolded, represents in the topos of types and functional
relations the Lean function it is written to compute: the bitstrings' constructions, the label
and children of a tree, the conditional and the case analysis of lists, the arithmetic,
comparison, logarithm and iteration of bitstrings, the applications of a list of functions, and
the equality of trees. A bit is represented by the element of the sum of the terminal type with
itself it is, a bitstring by its list of bits, and a tree by its nodes.

The arithmetic is specified through the index of a bitstring in the enumeration of
{cite}`Oitavem2010`, Remark 2.2, in which the bit zero is the digit one and the bit one the
digit two: each arithmetic definition represents the bitstring of the operation on the
indices.

## Main definitions

* {lit}`rankB`, {lit}`ofNum` — the index of a bitstring and the bitstring of an index.
* {lit}`ordB` — the comparison of indices, as the comparison type's elements.
* {lit}`zipAll` — the elementwise test of a list of trees by a list of functions.

## Main statements

* {lit}`rep_bnil`, {lit}`rep_b0`, {lit}`rep_b1`, {lit}`rep_lab`, {lit}`rep_unnode`,
  {lit}`rep_children` — the constructions of bitstrings and the parts of trees.
* {lit}`rep_cond`, {lit}`rep_tail`, {lit}`rep_headD`, {lit}`rep_lcase`, {lit}`rep_isNil`,
  {lit}`rep_length`, {lit}`rep_mapApp`, {lit}`rep_iter`, {lit}`rep_and` — the conditional, the
  operations on lists, and iteration, at every representation of the elements.
* {lit}`rep_succ`, {lit}`rep_pred`, {lit}`rep_dbl`, {lit}`rep_add`, {lit}`rep_sub`,
  {lit}`rep_mul`, {lit}`rep_divMod`, {lit}`rep_log2`, {lit}`rep_cmp`, {lit}`rep_ltB`,
  {lit}`rep_eqB` — the arithmetic and comparison of the indices.
* {lit}`rep_allZip`, {lit}`rep_equal` — the elementwise test and the equality of trees.

## Implementation notes

Each statement is proved by the representation of the definition's body
({name}`Geb.FreeTopos.Internal.rep_def`), assembled term by term from the representations of
the language's constructions, with each definition it applies represented by the statement
proved for it; the body's function is then shown equal to the specification by the fold
lemmas {lit}`foldr_eq`, {lit}`foldr_para` and {lit}`foldr_apply_eq`. The difference
{lit}`rep_subE` assumes the second index at most the first, as its callers do, so it is
stated of a function whose values are specified there alone.

## References

* {cite}`Oitavem2010`, Remark 2.2, for the enumeration of the bitstrings.

## Tags

translation, internal language, bitstring, representation, functional relation
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Translation

open PartialHorn (Tree)
open Internal (Term Defn Globals Definition RepC EnvRep RepEntry objs compileDefs repC_var
  repC_star repC_pair repC_fst repC_snd repC_lam repC_app repC_nil repC_cons repC_lnode repC_inl
  repC_inr repC_case repC_listRec repC_roseRec repC_call₀ repC_call₁ repC_call₂ repC_call₃
  envRep_ext envRep_listStep envRep_idt envRep_std₁ envRep_std₂ envRep_std₃ rep_def
  compiled_language)
open Sorts
open scoped Internal
open scoped FinEnum

/-- A bit: the left injection is zero and the right one. -/
abbrev Bit : Type := Unit ⊕ Unit

/-- The representation of a bit by itself. -/
abbrev RBit : Bit → Bit → Prop := Rep.sum Rep.unit Rep.unit

/-- The representation of a bitstring by itself, bit by bit. -/
abbrev RBits : List Bit → List Bit → Prop := Rep.list RBit

/-- The representation of a tree of bitstrings by itself, node by node. -/
abbrev RTree : RoseTree (List Bit) → RoseTree (List Bit) → Prop := Rep.rose RBits

/-- The object values of the translation's types, assembled from those of their parts. -/
scoped macro (name := objVal) "obj_val" : tactic =>
  `(tactic| (
    try simp only [bitTy, bitsTy, treeTy, ordTy, X₀, X₁, mkDefn, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.cons_append, Internal.ctxObj_nil,
      Internal.ctxObj_single, Internal.ctxObj_cons_cons]
    try simp only [one, prod, exp, coprod, list, lrose, subst_op, subst_x, List.map_cons,
      List.map_nil, List.getElem?_cons_zero, Option.getD_some]
    try simp_unfold
    repeat'
      first
      | exact eval_one
      | apply eval_prod
      | apply eval_coprod
      | apply eval_exp
      | apply eval_list
      | apply eval_lrose
      | exact Internal.objVal_x0
      | exact Internal.objVal_x1
      | assumption))

/-- The translation's types are types, at every constants. -/
scoped macro (name := isTy) "is_ty" : tactic =>
  `(tactic| simp (config := { failIfUnchanged := false }) [bitTy, bitsTy, treeTy, ordTy, X₀, X₁,
    mkDefn,
    Geb.FreeTopos.Internal.isTy_coprod,
    Geb.FreeTopos.Internal.isTy_one, Geb.FreeTopos.Internal.isTy_list,
    Geb.FreeTopos.Internal.isTy_prod, Geb.FreeTopos.Internal.isTy_exp,
    Geb.FreeTopos.Internal.isTy_lrose, Geb.FreeTopos.x, Geb.FreeTopos.Internal.isTy_var])

/-- The index of a bitstring in the enumeration of {cite}`Oitavem2010`, the bit one the digit
two. -/
def rankB (w : List Bit) : ℕ := Oitavem.rank (w.map Sum.isRight)

/-- The bitstring of an index in the enumeration of {cite}`Oitavem2010`. -/
def ofNum (n : ℕ) : List Bit := (Oitavem.unrank n).map fun b ↦ bif b then .inr () else .inl ()

@[simp] theorem rankB_nil : rankB [] = 0 := rfl

@[simp] theorem ofNum_zero : ofNum 0 = [] := by simp [ofNum]

@[simp] theorem rankB_cons_inl (w : List Bit) : rankB (.inl () :: w) = 2 * rankB w + 1 := by
  simp [rankB, Oitavem.rank_cons]

@[simp] theorem rankB_cons_inr (w : List Bit) : rankB (.inr () :: w) = 2 * rankB w + 2 := by
  simp [rankB, Oitavem.rank_cons]

@[simp] theorem ofNum_rankB (w : List Bit) : ofNum (rankB w) = w := by
  rw [ofNum, rankB, Oitavem.unrank_rank, List.map_map]
  conv_rhs => rw [← List.map_id w]
  exact List.map_congr_left fun b _ ↦ by rcases b with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> rfl

@[simp] theorem rankB_ofNum (n : ℕ) : rankB (ofNum n) = n := by
  rw [ofNum, rankB, List.map_map]
  conv_lhs => enter [1, 1]; rw [show (Sum.isRight ∘ fun b : Bool ↦
    bif b then (.inr () : Bit) else .inl ()) = id from funext fun b ↦ by cases b <;> rfl]
  rw [List.map_id, Oitavem.rank_unrank]

/-- Bitstrings are equal exactly when their indices are. -/
theorem rankB_inj {w u : List Bit} : rankB w = rankB u ↔ w = u :=
  ⟨fun h ↦ by rw [← ofNum_rankB w, h, ofNum_rankB], congrArg rankB⟩

/-- A bitstring is that of an index exactly when the index is its own. -/
theorem eq_ofNum_iff {w : List Bit} {n : ℕ} : w = ofNum n ↔ rankB w = n :=
  ⟨fun h ↦ h ▸ rankB_ofNum n, fun h ↦ h ▸ (ofNum_rankB w).symm⟩

@[simp] theorem ofNum_one : ofNum 1 = [.inl ()] := (eq_ofNum_iff.mpr (by simp)).symm

/-- The bit zero before the bitstring of an index is that of its double and one. -/
theorem cons_inl_ofNum (n : ℕ) : (.inl () :: ofNum n : List Bit) = ofNum (2 * n + 1) :=
  eq_ofNum_iff.mpr (by simp)

/-- The bit one before the bitstring of an index is that of its double and two. -/
theorem cons_inr_ofNum (n : ℕ) : (.inr () :: ofNum n : List Bit) = ofNum (2 * n + 2) :=
  eq_ofNum_iff.mpr (by simp)

/-- The index of a bitstring and one lie from two to its length to two to its length and one. -/
theorem rankB_bounds (w : List Bit) :
    2 ^ w.length ≤ rankB w + 1 ∧ rankB w + 1 < 2 ^ (w.length + 1) :=
  w.rec ⟨Nat.le_refl 1, Nat.one_lt_two⟩ fun b w ih ↦ by
    rcases b with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> simp only [rankB_cons_inl, rankB_cons_inr, List.length_cons,
      Nat.pow_succ] <;> constructor <;> omega

/-- A bitstring with a bit one has an index and one above two to its length. -/
theorem rankB_any_true (w : List Bit) (h : w.any Sum.isRight = true) :
    2 ^ w.length < rankB w + 1 := by
  refine w.rec (motive := fun w ↦ w.any Sum.isRight = true → 2 ^ w.length < rankB w + 1)
    (by simp) (fun b w ih h ↦ ?_) h
  have := rankB_bounds w
  rcases b with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
  · simp only [List.any_cons, Sum.isRight_inl, Bool.false_or] at h
    have := ih h
    simp only [rankB_cons_inl, List.length_cons, Nat.pow_succ]
    omega
  · simp only [rankB_cons_inr, List.length_cons, Nat.pow_succ]
    omega

/-- A bitstring of bits zero has an index and one equal to two to its length. -/
theorem rankB_any_false (w : List Bit) (h : w.any Sum.isRight = false) :
    rankB w + 1 = 2 ^ w.length := by
  refine w.rec (motive := fun w ↦ w.any Sum.isRight = false → rankB w + 1 = 2 ^ w.length)
    (fun _ ↦ rfl) (fun b w ih h ↦ ?_) h
  rcases b with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
  · simp only [List.any_cons, Sum.isRight_inl, Bool.false_or] at h
    have := ih h
    simp only [rankB_cons_inl, List.length_cons, Nat.pow_succ]
    omega
  · simp at h

/-- The base-two logarithm of a bitstring's index is its length when a bit is one and the
length's predecessor otherwise. -/
theorem log2_rankB (w : List Bit) :
    (rankB w).log2 = if w.any Sum.isRight = true then w.length else w.length - 1 := by
  obtain ⟨h₁, h₂⟩ := rankB_bounds w
  split_ifs with h
  · have h₃ := rankB_any_true w h
    rw [Nat.log2_eq_iff (by omega)]
    exact ⟨by omega, by omega⟩
  · have h₃ := rankB_any_false w (by simpa using h)
    rcases hw : w.length with _ | k
    · rw [hw] at h₃
      rw [show rankB w = 0 by simp only [Nat.pow_zero] at h₃; omega]
      rfl
    · rw [hw, Nat.pow_succ] at h₃
      rw [Nat.log2_eq_iff (by have := Nat.one_le_two_pow (n := k); omega), Nat.add_sub_cancel]
      exact ⟨by omega, by rw [Nat.pow_succ]; omega⟩

/-- The bitstrings of a quotient and a remainder are those of the division they satisfy. -/
theorem ofNum_divMod {N D Q R : ℕ} (h : R + D * Q = N) (hR : R < D) :
    (ofNum Q, ofNum R) = (ofNum (N / D), ofNum (N % D)) := by
  obtain ⟨h₁, h₂⟩ := (Nat.div_mod_unique (by omega)).mpr ⟨h, hR⟩
  rw [h₁, h₂]

/-- The comparison of two indices: less, equal or greater. -/
def ordB (m n : ℕ) : Unit ⊕ Bit :=
  if m < n then .inl () else if m = n then .inr (.inl ()) else .inr (.inr ())

/-- Whether a list of functions to bitstrings holds of a list of trees of its length,
elementwise: the bitstring one when each function's value at its tree is not empty and the
lengths agree, and the empty bitstring otherwise. -/
def zipAll : List (RoseTree (List Bit) → List Bit) → List (RoseTree (List Bit)) → List Bit :=
  List.rec (fun ts ↦ ts.rec [.inl ()] fun _ _ _ ↦ []) fun p _ r ts ↦
    ts.rec [] fun t ts' _ ↦ (p t).rec [] fun _ _ _ ↦ r ts'

variable {defs : List Defn} {ds : List PartialHorn.Defn}

/-- The elementwise test of a list of trees by the tests of equality with the trees of another
list is the test of the lists' equality. -/
theorem zipAll_map (g : RoseTree (List Bit) → RoseTree (List Bit) → List Bit)
    (cs : List (RoseTree (List Bit))) (h : ∀ c ∈ cs, ∀ u, g c u = ofNum (if c = u then 1 else 0)) :
    ∀ us, zipAll (cs.map g) us = ofNum (if cs = us then 1 else 0) := by
  refine List.rec (motive := fun cs ↦ (∀ c ∈ cs, ∀ u, g c u = ofNum (if c = u then 1 else 0)) →
    ∀ us, zipAll (cs.map g) us = ofNum (if cs = us then 1 else 0)) ?_ ?_ cs h
  · intro _ us
    rcases us with _ | ⟨u, us⟩ <;> simp [zipAll]
  · intro c cs ih h us
    rcases us with _ | ⟨u, us⟩
    · simp [zipAll]
    · change List.rec (motive := fun _ ↦ List Bit) [] (fun _ _ _ ↦ zipAll (cs.map g) us)
        (g c u) = _
      rw [h c List.mem_cons_self u, ih (fun c' hc' ↦ h c' (List.mem_cons_of_mem c hc')) us]
      by_cases hcu : c = u <;> simp [hcu]


/-- The side goals of a representation: the types' typing and values. -/
scoped macro (name := sideGoals) "side_goals" : tactic =>
  `(tactic| all_goals first
    | (is_ty; done)
    | (obj_val; done)
    | exact Internal.isTy_x (by decide)
    | (simp only [List.forall_mem_cons, Internal.sig_length]; decide))

/-- Repeating a function the sum of two numbers of times repeats it the second number of times
and then the first. -/
theorem repeat_add {α : Type} (f : α → α) (n : ℕ) (x : α) :
    ∀ m, Nat.repeat f (m + n) x = Nat.repeat f m (Nat.repeat f n x) :=
  Nat.rec (by rw [Nat.zero_add]; rfl) fun m ih ↦ by
    rw [Nat.succ_add]
    exact congrArg f ih

/-- Repeating a function twice a number of times and then some repeats it the number of times,
again, and then the rest. -/
theorem repeat_two_mul_add {α : Type} (f : α → α) (n k : ℕ) (x : α) :
    Nat.repeat f (2 * n + k) x = Nat.repeat f k (Nat.repeat f n (Nat.repeat f n x)) := by
  rw [Nat.add_comm, repeat_add, Nat.two_mul, repeat_add]

/-- A list fold computes each function whose value at the empty list is the start and at each
construction the step at the head and the tail's value. -/
theorem foldr_eq {α β : Type} (z : β) (f : α → β → β) (F : List α → β) (hz : z = F [])
    (hf : ∀ y l, f y (F l) = F (y :: l)) (l : List α) : l.foldr f z = F l :=
  l.rec hz fun y l ih ↦ by rw [List.foldr_cons, ih, hf]

/-- A list fold into functions agrees with a family of functions at each argument where a
predicate holds, when the start does and the step preserves the agreement. -/
theorem foldr_apply_eq {α γ δ : Type} (z : γ → δ) (f : α → (γ → δ) → γ → δ) (F : List α → γ → δ)
    (P : List α → γ → Prop) (hz : ∀ c, P [] c → z c = F [] c)
    (hf : ∀ y l g, (∀ c, P l c → g c = F l c) → ∀ c, P (y :: l) c → f y g c = F (y :: l) c)
    (l : List α) : ∀ c, P l c → l.foldr f z c = F l c :=
  l.rec hz fun y l ih ↦ hf y l _ ih

/-- A list fold into pairs whose first components rebuild the list computes, in its second, the
function whose value at each construction is the step at the head, the tail and the tail's
value: the paramorphism of the step. -/
theorem foldr_para {α β : Type} (z : β) (f : α → List α × β → β) (F : List α → β)
    (hz : z = F []) (hf : ∀ y l, f y (l, F l) = F (y :: l)) (l : List α) :
    l.foldr (fun y r ↦ (y :: r.1, f y r)) ([], z) = (l, F l) :=
  l.rec (by rw [hz]; rfl) fun y l ih ↦ by rw [List.foldr_cons, ih, hf]

/-- The representation of a comparison by itself: less, equal and greater. -/
abbrev ROrd : Unit ⊕ Bit → Unit ⊕ Bit → Prop := Rep.sum Rep.unit RBit

section Cases

variable {G : Globals} {n : ℕ} {ρ : List relTopos.model.Val} {X : Tree} {e : List (Tree × Tree)}
  {S A T C : Type}

/-- The variable an abstraction binds represents the second projection, in every environment. -/
theorem repC_var0 {a : Tree} {A' : Type} (hX : ObjVal ρ (unfoldTerm sig ds X) A)
    (ha : ObjVal ρ (unfoldTerm sig ds a) A') {R : S → A → Prop} {Ra : T → A' → Prop} :
    RepC G n ds ρ (Term.var 0) (prod X a) (Internal.extEnv X a e) a (Rep.prod R Ra) Ra
      Prod.snd :=
  ⟨snd X a, Internal.compile_var_iff.mpr ⟨rfl, rfl⟩, by
    simp_unfold
    exact represents_snd hX ha R Ra⟩

/-- A variable past the one an abstraction binds represents its function before the abstraction
after the first projection. -/
theorem repC_varS {a b : Tree} {i : ℕ} {A' B : Type} (hX : ObjVal ρ (unfoldTerm sig ds X) A)
    (ha : ObjVal ρ (unfoldTerm sig ds a) A') {R : S → A → Prop} {Ra : T → A' → Prop}
    {R' : C → B → Prop} {F : S → C} (h : RepC G n ds ρ (Term.var i) X e b R R' F) :
    RepC G n ds ρ (Term.var (i + 1)) (prod X a) (Internal.extEnv X a e) b (Rep.prod R Ra) R'
      (F ∘ Prod.fst) := by
  obtain ⟨f, hf, hF⟩ := h
  obtain ⟨-, hp⟩ := Internal.compile_var_iff.mp hf
  refine ⟨comp f (fst X a), Internal.compile_var_iff.mpr ⟨rfl, by simp [Internal.extEnv, hp]⟩, ?_⟩
  simp_unfold
  exact represents_comp (represents_fst hX ha R Ra) hF

/-- The case analysis of a bit, by abstractions over the terminal object ({name}`ifBit`),
represents the choice of the first branch's function at zero and of the second's at one, each at
the element of the terminal object. -/
theorem repC_ifBit {c : Tree} {b t u : Term} (hk : G.prims[5]? = some Internal.casePrim)
    (hc : Internal.IsTy G n c = true) {R : S → A → Prop} {Rc : T → C → Prop} {Fb : S → Bit}
    {Ft Fu : S × Unit → T} (hb : RepC G n ds ρ b X e bitTy R RBit Fb)
    (ht : RepC G n ds ρ t (prod X one) (Internal.extEnv X one e) c (Rep.prod R Rep.unit) Rc Ft)
    (hu : RepC G n ds ρ u (prod X one) (Internal.extEnv X one e) c (Rep.prod R Rep.unit) Rc Fu)
    (hX : ObjVal ρ (unfoldTerm sig ds X) A) (hC : ObjVal ρ (unfoldTerm sig ds c) C) :
    RepC G n ds ρ (Term.app (Term.arr 5 [one, one, c] (Term.pair (Term.lam one t)
      (Term.lam one u))) b) X e c R Rc
      fun s ↦ Sum.elim (fun x ↦ Ft (s, x)) (fun x ↦ Fu (s, x)) (Fb s) := by
  refine repC_app (repC_case hk ?_ ?_ hc (repC_pair
    (repC_lam ?_ hX ?_ ht) (repC_lam ?_ hX ?_ hu)) ?_ ?_ hC) hb ?_ hC
  side_goals

/-- The case analysis of a comparison ({name}`ifOrd`) represents the choice of the first branch's
function at less, the second's at equal and the third's at greater. -/
theorem repC_ifOrd {c : Tree} {o l m g : Term} (hk : G.prims[5]? = some Internal.casePrim)
    (hc : Internal.IsTy G n c = true) {R : S → A → Prop} {Rc : T → C → Prop}
    {Fo : S → Unit ⊕ Bit} {Fl : S × Unit → T} {Fm Fg : (S × Bit) × Unit → T}
    (ho : RepC G n ds ρ o X e ordTy R ROrd Fo)
    (hl : RepC G n ds ρ l (prod X one) (Internal.extEnv X one e) c (Rep.prod R Rep.unit) Rc Fl)
    (hm : RepC G n ds ρ m (prod (prod X bitTy) one)
      (Internal.extEnv (prod X bitTy) one (Internal.extEnv X bitTy e)) c
      (Rep.prod (Rep.prod R RBit) Rep.unit) Rc Fm)
    (hg : RepC G n ds ρ g (prod (prod X bitTy) one)
      (Internal.extEnv (prod X bitTy) one (Internal.extEnv X bitTy e)) c
      (Rep.prod (Rep.prod R RBit) Rep.unit) Rc Fg)
    (hX : ObjVal ρ (unfoldTerm sig ds X) A) (hC : ObjVal ρ (unfoldTerm sig ds c) C) :
    RepC G n ds ρ (Term.app (Term.arr 5 [one, bitTy, c] (Term.pair (Term.lam one l)
      (Term.lam bitTy (Term.app (Term.arr 5 [one, one, c] (Term.pair (Term.lam one m)
        (Term.lam one g))) (Term.var 0))))) o) X e c R Rc
      fun s ↦ Sum.elim (fun x ↦ Fl (s, x))
        (fun y ↦ Sum.elim (fun x ↦ Fm ((s, y), x)) (fun x ↦ Fg ((s, y), x)) y) (Fo s) := by
  have hXb : ObjVal ρ (unfoldTerm sig ds (prod X bitTy)) (A × Bit) := by
    simp only [bitTy]
    simp_unfold
    exact eval_prod hX (eval_coprod eval_one eval_one)
  refine repC_app (repC_case hk ?_ ?_ hc (repC_pair
    (repC_lam ?_ hX ?_ hl) (repC_lam ?_ hX ?_
      (repC_ifBit hk hc (repC_var0 hX ?_) hm hg hXb hC))) ?_ ?_ hC) ho ?_ hC
  side_goals

end Cases

/-- The empty bitstring represents the empty list. -/
theorem rep_bnil (hF : compileDefs (globals defs) = some ds) {fk : Tree}
    (hdk : ds[D.bnil]? = some ⟨[], arr, fk⟩) :
    Represents [] (unfoldTerm sig ds fk) Rep.unit RBits fun _ ↦ [] := by
  refine rep_def (τ' := []) hF (d := mkDefn 0 [] bitsTy (nilT bitTy)) rfl
    (repC_nil rfl ?_ (repC_star ?_ _) ?_ RBit) (fun _ ↦ rfl) hdk
  side_goals

/-- The bit zero before a bitstring represents the construction with zero. -/
theorem rep_b0 (hF : compileDefs (globals defs) = some ds) {fk : Tree}
    (hdk : ds[D.b0]? = some ⟨[], arr, fk⟩) :
    Represents [] (unfoldTerm sig ds fk) RBits RBits fun w ↦ .inl () :: w := by
  refine rep_def (τ' := []) hF
    (d := mkDefn 0 [bitsTy] bitsTy (consT bitTy bit0T (v 0))) rfl
    (repC_cons rfl ?_ (repC_pair
      (repC_inl rfl ?_ ?_ (repC_star ?_ _) ?_ ?_ Rep.unit)
      (repC_var (envRep_std₁ ?_ RBits) rfl)) ?_) (fun _ ↦ rfl) hdk
  side_goals

/-- The bit one before a bitstring represents the construction with one. -/
theorem rep_b1 (hF : compileDefs (globals defs) = some ds) {fk : Tree}
    (hdk : ds[D.b1]? = some ⟨[], arr, fk⟩) :
    Represents [] (unfoldTerm sig ds fk) RBits RBits fun w ↦ .inr () :: w := by
  refine rep_def (τ' := []) hF
    (d := mkDefn 0 [bitsTy] bitsTy (consT bitTy bit1T (v 0))) rfl
    (repC_cons rfl ?_ (repC_pair
      (repC_inr rfl ?_ ?_ (repC_star ?_ _) ?_ ?_ Rep.unit)
      (repC_var (envRep_std₁ ?_ RBits) rfl)) ?_) (fun _ ↦ rfl) hdk
  side_goals

/-- The label of a tree represents the label. -/
theorem rep_lab (hF : compileDefs (globals defs) = some ds) {fk : Tree}
    (hdk : ds[D.lab]? = some ⟨[], arr, fk⟩) :
    Represents [] (unfoldTerm sig ds fk) RTree RBits RoseTree.label := by
  refine rep_def (τ' := []) hF
    (d := mkDefn 0 [treeTy] bitsTy (Term.roseRec bitsTy (Term.fst (v 0)) (v 0))) rfl
    (repC_roseRec ?_ (repC_var (envRep_std₁ ?_ RTree) rfl)
      (repC_fst (repC_var
        (envRep_idt ?_ (Rep.prod RBits (Rep.list RBits))) rfl) ?_ ?_) ?_) ?hc hdk
  case hc =>
    intro t
    obtain ⟨l, cs, rfl⟩ : ∃ l cs, t = RoseTree.node l cs :=
      ⟨_, _, (RoseTree.node_label_children t).symm⟩
    simp [RoseTree.elim_node]
  side_goals

/-- The unfolding of a tree represents the pair of its label and its children. -/
theorem rep_unnode (hF : compileDefs (globals defs) = some ds) {fk : Tree}
    (hdk : ds[D.unnode]? = some ⟨[], arr, fk⟩) :
    Represents [] (unfoldTerm sig ds fk) RTree (Rep.prod RBits (Rep.list RTree))
      fun t ↦ (t.label, t.children) := by
  refine rep_def (τ' := []) hF
    (d := mkDefn 0 [treeTy] (prod bitsTy (list treeTy))
      (Term.roseRec (prod bitsTy (list treeTy))
        (Term.pair (Term.fst (v 0))
          (Term.listRec (nilT treeTy) (consT treeTy (nodeT (v 1)) (v 0)) (Term.snd (v 0))))
        (v 0))) rfl
    (repC_roseRec ?_ (repC_var (envRep_std₁ ?_ RTree) rfl)
      (repC_pair
        (repC_fst (repC_var (envRep_idt ?_
          (Rep.prod RBits (Rep.list (Rep.prod RBits (Rep.list RTree))))) rfl) ?_ ?_)
        (repC_listRec
          (repC_snd (repC_var (envRep_idt ?_
            (Rep.prod RBits (Rep.list (Rep.prod RBits (Rep.list RTree))))) rfl) ?_ ?_)
          (repC_nil rfl ?_ (repC_star ?_ _) ?_ RTree)
          (repC_cons rfl ?_ (repC_pair
            (repC_lnode rfl ?_ (repC_var
              (envRep_listStep ?_ ?_ (Rep.prod RBits (Rep.list RTree))
                (Rep.list RTree)) rfl) ?_)
            (repC_var (envRep_listStep ?_ ?_
              (Rep.prod RBits (Rep.list RTree)) (Rep.list RTree)) rfl)) ?_) ?_)) ?_) ?hc hdk
  case hc =>
    intro t
    refine RoseTree.ind (P := fun t ↦ _ = (t.label, t.children)) (fun l cs ih ↦ ?_) t
    simp only [RoseTree.elim_node, RoseTree.label_node, RoseTree.children_node, Prod.mk.injEq,
      id] at ih ⊢
    refine ⟨trivial, ?_⟩
    rw [← List.map_eq_foldr, List.map_map]
    conv_rhs => rw [← List.map_id cs]
    exact List.map_congr_left fun c hc ↦ by
      simp only [Function.comp_apply, ih c hc, RoseTree.node_label_children, id]
  side_goals

/-- The children of a tree represent its children. -/
theorem rep_children (hF : compileDefs (globals defs) = some ds)
    (hwf : PartialHorn.DefnsWF sig ds) {fk : Tree} (hdk : ds[D.children]? = some ⟨[], arr, fk⟩) :
    Represents [] (unfoldTerm sig ds fk) RTree (Rep.list RTree) RoseTree.children := by
  obtain ⟨fu, hfu⟩ := compiled_language hF (k := D.unnode)
    (d := mkDefn 0 [treeTy] (prod bitsTy (list treeTy))
      (Term.roseRec (prod bitsTy (list treeTy))
        (Term.pair (Term.fst (v 0))
          (Term.listRec (nilT treeTy) (consT treeTy (nodeT (v 1)) (v 0)) (Term.snd (v 0))))
        (v 0))) rfl
  refine rep_def (τ' := []) hF
    (d := mkDefn 0 [treeTy] (list treeTy) (Term.snd (call D.unnode [] [v 0]))) rfl
    (repC_snd (repC_call₁ (τ' := []) (a := prod bitsTy (list treeTy)) rfl rfl
      hwf hfu rfl (by simp) (by simp) .nil rfl rfl (rep_unnode hF hfu)
      (repC_var (envRep_std₁ ?_ RTree) rfl)) ?_ ?_) (fun _ ↦ rfl) hdk
  side_goals

/-- The conditional on a bitstring represents the choice of the second branch at the empty
bitstring and of the first otherwise, at every representation of the branches' values. -/
theorem rep_cond (hF : compileDefs (globals defs) = some ds) {fk : Tree}
    (hdk : ds[D.cond]? = some ⟨[obj], arr, fk⟩) {A S : Type} (R : S → A → Prop) :
    Represents (objs [A]) (unfoldTerm sig ds fk) (Rep.prod (Rep.prod RBits R) R) R
      fun p ↦ p.1.1.rec p.2 fun _ _ _ ↦ p.1.2 := by
  refine rep_def (τ' := [A]) hF
    (d := mkDefn 1 [bitsTy, X₀, X₀] X₀
      (Term.app (Term.app (Term.listRec (Term.lam X₀ (Term.lam X₀ (v 0)))
        (Term.lam X₀ (Term.lam X₀ (v 1))) (v 2)) (v 1)) (v 0))) rfl
    (repC_app (repC_app
      (repC_listRec
        (repC_var (envRep_std₃ ?_ ?_ ?_ RBits R R) rfl)
        (repC_lam ?_ ?_ ?_ (repC_lam ?_ ?_ ?_ (repC_var
          (envRep_ext ?_ ?_ (envRep_ext ?_ ?_ .nil R) R) rfl)))
        (repC_lam ?_ ?_ ?_ (repC_lam ?_ ?_ ?_ (repC_var
          (envRep_ext ?_ ?_ (envRep_ext ?_ ?_
            (envRep_listStep ?_ ?_ RBit (Rep.exp R (Rep.exp R R))) R) R) rfl)))
        ?_)
      (repC_var (envRep_std₃ ?_ ?_ ?_ RBits R R) rfl) ?_ ?_)
      (repC_var (envRep_std₃ ?_ ?_ ?_ RBits R R) rfl) ?_ ?_) ?hc hdk
  case hc =>
    rintro ⟨⟨_ | ⟨b, c⟩, t⟩, u⟩ <;> rfl
  side_goals

/-- The tail of a list represents the tail, at every representation of the elements. -/
theorem rep_tail (hF : compileDefs (globals defs) = some ds) {fk : Tree}
    (hdk : ds[D.tail]? = some ⟨[obj], arr, fk⟩) {A S : Type} (R : S → A → Prop) :
    Represents (objs [A]) (unfoldTerm sig ds fk) (Rep.list R) (Rep.list R) List.tail := by
  refine rep_def (τ' := [A]) hF
    (d := mkDefn 1 [list X₀] (list X₀)
      (Term.snd (Term.listRec (Term.pair (nilT X₀) (nilT X₀))
        (Term.pair (consT X₀ (v 1) (Term.fst (v 0))) (Term.fst (v 0))) (v 0)))) rfl
    (repC_snd (repC_listRec
      (repC_var (envRep_std₁ ?_ (Rep.list R)) rfl)
      (repC_pair (repC_nil rfl ?_ (repC_star ?_ _) ?_ R)
        (repC_nil rfl ?_ (repC_star ?_ _) ?_ R))
      (repC_pair
        (repC_cons rfl ?_ (repC_pair
          (repC_var (envRep_listStep ?_ ?_ R
            (Rep.prod (Rep.list R) (Rep.list R))) rfl)
          (repC_fst (repC_var (envRep_listStep ?_ ?_ R
            (Rep.prod (Rep.list R) (Rep.list R))) rfl) ?_ ?_)) ?_)
        (repC_fst (repC_var (envRep_listStep ?_ ?_ R
          (Rep.prod (Rep.list R) (Rep.list R))) rfl) ?_ ?_)) ?_) ?_ ?_) ?hc hdk
  case hc =>
    have hre : ∀ l : List S, (l.foldr (fun y r ↦ (y :: r.1, r.1)) ([], [])).1 = l := fun l ↦
      l.rec rfl fun y l ih ↦ by simp only [List.foldr_cons, ih]
    rintro (_ | ⟨y, l⟩)
    · rfl
    · exact hre l
  side_goals

/-- The head of a list, or a default, represents the head with the default, at every
representation of the elements. -/
theorem rep_headD (hF : compileDefs (globals defs) = some ds) {fk : Tree}
    (hdk : ds[D.headD]? = some ⟨[obj], arr, fk⟩) {A S : Type} (R : S → A → Prop) :
    Represents (objs [A]) (unfoldTerm sig ds fk) (Rep.prod R (Rep.list R)) R
      fun p ↦ p.2.headD p.1 := by
  refine rep_def (τ' := [A]) hF
    (d := mkDefn 1 [X₀, list X₀] X₀
      (Term.app (Term.listRec (Term.lam X₀ (v 0)) (Term.lam X₀ (v 2)) (v 0)) (v 1))) rfl
    (repC_app
      (repC_listRec (repC_var (envRep_std₂ ?_ ?_ R (Rep.list R)) rfl)
        (repC_lam ?_ ?_ ?_ (repC_var (envRep_ext ?_ ?_ .nil R) rfl))
        (repC_lam ?_ ?_ ?_ (repC_var (envRep_ext ?_ ?_
          (envRep_listStep ?_ ?_ R (Rep.exp R R)) R) rfl)) ?_)
      (repC_var (envRep_std₂ ?_ ?_ R (Rep.list R)) rfl) ?_ ?_) ?hc hdk
  case hc =>
    rintro ⟨d, _ | ⟨y, l⟩⟩ <;> rfl
  side_goals

/-- The first components of a list fold's values that construct the list from its elements are
the list. -/
theorem foldr_rebuild {α β γ : Type} (z : γ → β) (f : α → (γ → List α × β) → γ → β) (c : γ) :
    ∀ l : List α,
      (l.foldr (fun y r ↦ fun p ↦ (y :: (r p).1, f y r p)) (fun p ↦ ([], z p)) c).1 = l :=
  List.rec rfl fun y l ih ↦ by simp only [List.foldr_cons, ih]

/-- The case analysis of a list represents the case analysis, at every representation of the
elements and of the values. -/
theorem rep_lcase (hF : compileDefs (globals defs) = some ds) {fk : Tree}
    (hdk : ds[D.lcase]? = some ⟨[obj, obj], arr, fk⟩) {A₀ A₁ S₀ S₁ : Type}
    (R₀ : S₀ → A₀ → Prop) (R₁ : S₁ → A₁ → Prop) :
    Represents (objs [A₀, A₁]) (unfoldTerm sig ds fk)
      (Rep.prod (Rep.prod (Rep.list R₀) (Rep.exp Rep.unit R₁))
        (Rep.exp R₀ (Rep.exp (Rep.list R₀) R₁))) R₁
      fun p ↦ p.1.1.rec (p.1.2 ()) fun y r _ ↦ p.2 y r := by
  let RC := Rep.exp R₀ (Rep.exp (Rep.list R₀) R₁)
  let RP := Rep.prod (Rep.exp Rep.unit R₁) RC
  let RV := Rep.exp RP (Rep.prod (Rep.list R₀) R₁)
  refine rep_def (τ' := [A₀, A₁]) hF
    (d := mkDefn 2 [list X₀, exp one X₁, exp X₀ (exp (list X₀) X₁)] X₁
        (Term.snd (Term.app (Term.listRec
          (Term.lam (prod (exp one X₁) (exp X₀ (exp (list X₀) X₁)))
            (Term.pair (nilT X₀) (Term.app (Term.fst (v 0)) Term.star)))
          (Term.lam (prod (exp one X₁) (exp X₀ (exp (list X₀) X₁)))
            (Term.pair (consT X₀ (v 2) (Term.fst (Term.app (v 1) (v 0))))
              (Term.app (Term.app (Term.snd (v 0)) (v 2)) (Term.fst (Term.app (v 1) (v 0))))))
          (v 2)) (Term.pair (v 1) (v 0))))) rfl
    (repC_snd (repC_app
      (repC_listRec
        (repC_var (envRep_std₃ ?_ ?_ ?_ (Rep.list R₀) (Rep.exp Rep.unit R₁) RC)
          rfl)
        (repC_lam ?_ ?_ ?_ (repC_pair
          (repC_nil rfl ?_ (repC_star ?_ _) ?_ R₀)
          (repC_app (repC_fst
            (repC_var (envRep_ext ?_ ?_ .nil RP) rfl) ?_ ?_)
            (repC_star ?_ _) ?_ ?_)))
        (repC_lam ?_ ?_ ?_ (repC_pair
          (repC_cons rfl ?_ (repC_pair
            (repC_var (envRep_ext ?_ ?_ (envRep_listStep ?_ ?_ R₀ RV)
              RP) rfl)
            (repC_fst (repC_app
              (repC_var (envRep_ext ?_ ?_ (envRep_listStep ?_ ?_ R₀ RV)
                RP) rfl)
              (repC_var (envRep_ext ?_ ?_ (envRep_listStep ?_ ?_ R₀ RV)
                RP) rfl) ?_ ?_) ?_ ?_)) ?_)
          (repC_app (repC_app (repC_snd
            (repC_var (envRep_ext ?_ ?_ (envRep_listStep ?_ ?_ R₀ RV)
              RP) rfl) ?_ ?_)
            (repC_var (envRep_ext ?_ ?_ (envRep_listStep ?_ ?_ R₀ RV)
              RP) rfl) ?_ ?_)
            (repC_fst (repC_app
              (repC_var (envRep_ext ?_ ?_ (envRep_listStep ?_ ?_ R₀ RV)
                RP) rfl)
              (repC_var (envRep_ext ?_ ?_ (envRep_listStep ?_ ?_ R₀ RV)
                RP) rfl) ?_ ?_) ?_ ?_) ?_ ?_))) ?_)
      (repC_pair
        (repC_var (envRep_std₃ ?_ ?_ ?_ (Rep.list R₀) (Rep.exp Rep.unit R₁) RC)
          rfl)
        (repC_var (envRep_std₃ ?_ ?_ ?_ (Rep.list R₀) (Rep.exp Rep.unit R₁) RC)
          rfl)) ?_ ?_) ?_ ?_) ?hc hdk
  case hc =>
    rintro ⟨⟨_ | ⟨y, l⟩, n⟩, c⟩
    · rfl
    · exact congrArg (c y) (foldr_rebuild _ _ _ l)
  side_goals

/-- Whether a list is empty represents one at the empty list and zero otherwise, at every
representation of the elements. -/
theorem rep_isNil (hF : compileDefs (globals defs) = some ds) (hwf : PartialHorn.DefnsWF sig ds)
    {fk : Tree} (hdk : ds[D.isNil]? = some ⟨[obj], arr, fk⟩) {A S : Type} (R : S → A → Prop) :
    Represents (objs [A]) (unfoldTerm sig ds fk) (Rep.list R) RBits
      fun l ↦ l.rec [.inl ()] fun _ _ _ ↦ [] := by
  obtain ⟨fn, hfn⟩ := compiled_language hF (k := D.bnil)
    (d := mkDefn 0 [] bitsTy (nilT bitTy)) rfl
  obtain ⟨f0, hf0⟩ := compiled_language hF (k := D.b0)
    (d := mkDefn 0 [bitsTy] bitsTy (consT bitTy bit0T (v 0))) rfl
  refine rep_def (τ' := [A]) hF
    (d := mkDefn 1 [list X₀] bitsTy (Term.listRec trueT bnilT (v 0))) rfl
    (repC_listRec (repC_var (envRep_std₁ ?_ (Rep.list R)) rfl)
      (repC_call₁ (τ' := []) (a := bitsTy) rfl rfl hwf hf0 rfl (by simp) (by simp) .nil
        rfl rfl (rep_b0 hF hf0)
        (repC_call₀ rfl rfl hwf hfn rfl rfl (a := bitsTy) rfl ?_ (rep_bnil hF hfn)))
      (repC_call₀ rfl rfl hwf hfn rfl rfl (a := bitsTy) rfl ?_ (rep_bnil hF hfn)) ?_)
    ?hc hdk
  case hc =>
    rintro (_ | ⟨y, l⟩) <;> rfl
  side_goals

/-- The successor of a bitstring represents the successor. -/
theorem rep_succ (hF : compileDefs (globals defs) = some ds) (hwf : PartialHorn.DefnsWF sig ds)
    {fk : Tree} (hdk : ds[D.succ]? = some ⟨[], arr, fk⟩) :
    Represents [] (unfoldTerm sig ds fk) RBits RBits fun w ↦ ofNum (rankB w + 1) := by
  obtain ⟨fn, hfn⟩ := compiled_language hF (k := D.bnil)
    (d := mkDefn 0 [] bitsTy (nilT bitTy)) rfl
  obtain ⟨f0, hf0⟩ := compiled_language hF (k := D.b0)
    (d := mkDefn 0 [bitsTy] bitsTy (consT bitTy bit0T (v 0))) rfl
  obtain ⟨f1, hf1⟩ := compiled_language hF (k := D.b1)
    (d := mkDefn 0 [bitsTy] bitsTy (consT bitTy bit1T (v 0))) rfl
  let RV := Rep.prod RBits RBits
  refine rep_def (τ' := []) hF
    (d := mkDefn 0 [bitsTy] bitsTy
      (Term.snd (Term.listRec (Term.pair bnilT trueT)
        (Term.pair (consT bitTy (v 1) (Term.fst (v 0)))
          (ifBit bitsTy (v 1) (b1T (Term.fst (v 0))) (b0T (Term.snd (v 0)))))
        (v 0)))) rfl
    (repC_snd (repC_listRec
      (repC_var (envRep_std₁ ?_ RBits) rfl)
      (repC_pair
        (repC_call₀ rfl rfl hwf hfn rfl rfl (a := bitsTy) rfl ?_ (rep_bnil hF hfn))
        (repC_call₁ (τ' := []) (a := bitsTy) rfl rfl hwf hf0 rfl (by simp) (by simp)
          .nil rfl rfl (rep_b0 hF hf0)
          (repC_call₀ rfl rfl hwf hfn rfl rfl (a := bitsTy) rfl ?_ (rep_bnil hF hfn))))
      (repC_pair
        (repC_cons rfl ?_ (repC_pair
          (repC_var (envRep_listStep ?_ ?_ RBit RV) rfl)
          (repC_fst (repC_var (envRep_listStep ?_ ?_ RBit RV) rfl)
            ?_ ?_)) ?_)
        (repC_app (repC_case rfl ?_ ?_ ?_ (repC_pair
          (repC_lam ?_ ?_ ?_ (repC_call₁ (τ' := []) (a := bitsTy) rfl rfl hwf
            hf1 rfl (by simp) (by simp) .nil rfl rfl (rep_b1 hF hf1)
            (repC_fst (repC_var (envRep_ext ?_ ?_
              (envRep_listStep ?_ ?_ RBit RV) Rep.unit) rfl) ?_ ?_)))
          (repC_lam ?_ ?_ ?_ (repC_call₁ (τ' := []) (a := bitsTy) rfl rfl hwf
            hf0 rfl (by simp) (by simp) .nil rfl rfl (rep_b0 hF hf0)
            (repC_snd (repC_var (envRep_ext ?_ ?_
              (envRep_listStep ?_ ?_ RBit RV) Rep.unit) rfl) ?_ ?_)))) ?_ ?_ ?_)
          (repC_var (envRep_listStep ?_ ?_ RBit RV) rfl) ?_ ?_)) ?_) ?_ ?_)
    ?hc hdk
  case hc =>
    refine fun w ↦ congrArg Prod.snd (foldr_para _ _ (fun w ↦ ofNum (rankB w + 1)) ?_ ?_ w)
    · simp
    · rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩) l
      · simp [eq_ofNum_iff]
      · simp [eq_ofNum_iff]
        omega
  side_goals

/-- The length of a list represents the length, at every representation of the elements. -/
theorem rep_length (hF : compileDefs (globals defs) = some ds) (hwf : PartialHorn.DefnsWF sig ds)
    {fk : Tree} (hdk : ds[D.length]? = some ⟨[obj], arr, fk⟩) {A S : Type} (R : S → A → Prop) :
    Represents (objs [A]) (unfoldTerm sig ds fk) (Rep.list R) RBits fun l ↦ ofNum l.length := by
  obtain ⟨fn, hfn⟩ := compiled_language hF (k := D.bnil)
    (d := mkDefn 0 [] bitsTy (nilT bitTy)) rfl
  obtain ⟨fs, hfs⟩ := compiled_language hF (k := D.succ) (d := lib[D.succ]) rfl
  refine rep_def (τ' := [A]) hF
    (d := mkDefn 1 [list X₀] bitsTy (Term.listRec bnilT (call D.succ [] [v 0]) (v 0))) rfl
    (repC_listRec (repC_var (envRep_std₁ ?_ (Rep.list R)) rfl)
      (repC_call₀ rfl rfl hwf hfn rfl rfl (a := bitsTy) rfl ?_ (rep_bnil hF hfn))
      (repC_call₁ (τ' := []) (a := bitsTy) rfl rfl hwf hfs rfl (by simp) (by simp) .nil
        rfl rfl (rep_succ hF hwf hfs)
        (repC_var (envRep_listStep ?_ ?_ R RBits) rfl)) ?_) ?hc hdk
  case hc =>
    intro l
    dsimp only [id, Function.comp_apply]
    refine l.rec ofNum_zero.symm fun y l ih ↦ ?_
    rw [List.foldr_cons, ih, rankB_ofNum]
    rfl
  side_goals

/-- The predecessor of a bitstring represents the predecessor, with zero fixed. -/
theorem rep_pred (hF : compileDefs (globals defs) = some ds) (hwf : PartialHorn.DefnsWF sig ds)
    {fk : Tree} (hdk : ds[D.pred]? = some ⟨[], arr, fk⟩) :
    Represents [] (unfoldTerm sig ds fk) RBits RBits fun w ↦ ofNum (rankB w - 1) := by
  obtain ⟨fn, hfn⟩ := compiled_language hF (k := D.bnil) (d := lib[D.bnil]) rfl
  obtain ⟨f0, hf0⟩ := compiled_language hF (k := D.b0) (d := lib[D.b0]) rfl
  obtain ⟨f1, hf1⟩ := compiled_language hF (k := D.b1) (d := lib[D.b1]) rfl
  obtain ⟨fc, hfc⟩ := compiled_language hF (k := D.cond) (d := lib[D.cond]) rfl
  let RV := Rep.prod RBits RBits
  refine rep_def (τ' := []) hF
    (d := mkDefn 0 [bitsTy] bitsTy
      (Term.snd (Term.listRec (Term.pair bnilT bnilT)
        (Term.pair (consT bitTy (v 1) (Term.fst (v 0)))
          (ifBit bitsTy (v 1) (condT bitsTy (Term.fst (v 0)) (b1T (Term.snd (v 0))) bnilT)
            (b0T (Term.fst (v 0)))))
        (v 0)))) rfl
    (repC_snd (repC_listRec
      (repC_var (envRep_std₁ ?_ RBits) rfl)
      (repC_pair
        (repC_call₀ rfl rfl hwf hfn rfl rfl (a := bitsTy) rfl ?_ (rep_bnil hF hfn))
        (repC_call₀ rfl rfl hwf hfn rfl rfl (a := bitsTy) rfl ?_ (rep_bnil hF hfn)))
      (repC_pair
        (repC_cons rfl ?_ (repC_pair
          (repC_var (envRep_listStep ?_ ?_ RBit RV) rfl)
          (repC_fst (repC_var (envRep_listStep ?_ ?_ RBit RV) rfl)
            ?_ ?_)) ?_)
        (repC_app (repC_case rfl ?_ ?_ ?_ (repC_pair
          (repC_lam ?_ ?_ ?_ (repC_call₃ (τ' := [List Bit]) (a := bitsTy) rfl
            rfl hwf hfc rfl ?_ ?_ (.cons ?_ .nil) rfl rfl (rep_cond hF hfc RBits)
            (repC_fst (repC_var (envRep_ext ?_ ?_
              (envRep_listStep ?_ ?_ RBit RV) Rep.unit) rfl) ?_ ?_)
            (repC_call₁ (τ' := []) (a := bitsTy) rfl rfl hwf hf1 rfl (by simp)
              (by simp) .nil rfl rfl (rep_b1 hF hf1)
              (repC_snd (repC_var (envRep_ext ?_ ?_
                (envRep_listStep ?_ ?_ RBit RV) Rep.unit) rfl) ?_ ?_))
            (repC_call₀ rfl rfl hwf hfn rfl rfl (a := bitsTy) rfl ?_ (rep_bnil hF hfn))))
          (repC_lam ?_ ?_ ?_ (repC_call₁ (τ' := []) (a := bitsTy) rfl rfl hwf
            hf0 rfl (by simp) (by simp) .nil rfl rfl (rep_b0 hF hf0)
            (repC_fst (repC_var (envRep_ext ?_ ?_
              (envRep_listStep ?_ ?_ RBit RV) Rep.unit) rfl) ?_ ?_)))) ?_ ?_ ?_)
          (repC_var (envRep_listStep ?_ ?_ RBit RV) rfl) ?_ ?_)) ?_) ?_ ?_)
    ?hc hdk
  case hc =>
    refine fun w ↦ congrArg Prod.snd (foldr_para _ _ (fun w ↦ ofNum (rankB w - 1)) ?_ ?_ w)
    · simp
    · rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩) l
      · rcases l with _ | ⟨(⟨⟨⟩⟩ | ⟨⟨⟩⟩), l⟩ <;> simp [eq_ofNum_iff] <;> omega
      · simp [eq_ofNum_iff]
  side_goals

/-- Doubling a bitstring represents doubling. -/
theorem rep_dbl (hF : compileDefs (globals defs) = some ds) (hwf : PartialHorn.DefnsWF sig ds)
    {fk : Tree} (hdk : ds[D.dbl]? = some ⟨[], arr, fk⟩) :
    Represents [] (unfoldTerm sig ds fk) RBits RBits fun w ↦ ofNum (2 * rankB w) := by
  obtain ⟨fn, hfn⟩ := compiled_language hF (k := D.bnil) (d := lib[D.bnil]) rfl
  obtain ⟨f0, hf0⟩ := compiled_language hF (k := D.b0) (d := lib[D.b0]) rfl
  obtain ⟨f1, hf1⟩ := compiled_language hF (k := D.b1) (d := lib[D.b1]) rfl
  let RV := Rep.prod RBits RBits
  refine rep_def (τ' := []) hF
    (d := mkDefn 0 [bitsTy] bitsTy
      (Term.snd (Term.listRec (Term.pair bnilT bnilT)
        (Term.pair (consT bitTy (v 1) (Term.fst (v 0)))
          (ifBit bitsTy (v 1) (b1T (Term.snd (v 0))) (b1T (b0T (Term.fst (v 0))))))
        (v 0)))) rfl
    (repC_snd (repC_listRec
      (repC_var (envRep_std₁ ?_ RBits) rfl)
      (repC_pair
        (repC_call₀ rfl rfl hwf hfn rfl rfl (a := bitsTy) rfl ?_ (rep_bnil hF hfn))
        (repC_call₀ rfl rfl hwf hfn rfl rfl (a := bitsTy) rfl ?_ (rep_bnil hF hfn)))
      (repC_pair
        (repC_cons rfl ?_ (repC_pair
          (repC_var (envRep_listStep ?_ ?_ RBit RV) rfl)
          (repC_fst (repC_var (envRep_listStep ?_ ?_ RBit RV) rfl)
            ?_ ?_)) ?_)
        (repC_app (repC_case rfl ?_ ?_ ?_ (repC_pair
          (repC_lam ?_ ?_ ?_ (repC_call₁ (τ' := []) (a := bitsTy) rfl rfl hwf
            hf1 rfl (by simp) (by simp) .nil rfl rfl (rep_b1 hF hf1)
            (repC_snd (repC_var (envRep_ext ?_ ?_
              (envRep_listStep ?_ ?_ RBit RV) Rep.unit) rfl) ?_ ?_)))
          (repC_lam ?_ ?_ ?_ (repC_call₁ (τ' := []) (a := bitsTy) rfl rfl hwf
            hf1 rfl (by simp) (by simp) .nil rfl rfl (rep_b1 hF hf1)
            (repC_call₁ (τ' := []) (a := bitsTy) rfl rfl hwf hf0 rfl (by simp)
              (by simp) .nil rfl rfl (rep_b0 hF hf0)
              (repC_fst (repC_var (envRep_ext ?_ ?_
                (envRep_listStep ?_ ?_ RBit RV) Rep.unit) rfl) ?_ ?_))))) ?_ ?_ ?_)
          (repC_var (envRep_listStep ?_ ?_ RBit RV) rfl) ?_ ?_)) ?_) ?_ ?_)
    ?hc hdk
  case hc =>
    refine fun w ↦ congrArg Prod.snd (foldr_para _ _ (fun w ↦ ofNum (2 * rankB w)) ?_ ?_ w)
    · simp
    · rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩) l
      · simp [eq_ofNum_iff]
        omega
      · simp [eq_ofNum_iff]
        omega
  side_goals

/-- The sum of bitstrings represents the sum of their indices. -/
theorem rep_add (hF : compileDefs (globals defs) = some ds) (hwf : PartialHorn.DefnsWF sig ds)
    {fk : Tree} (hdk : ds[D.add]? = some ⟨[], arr, fk⟩) :
    Represents [] (unfoldTerm sig ds fk) (Rep.prod RBits RBits) RBits
      fun p ↦ ofNum (rankB p.1 + rankB p.2) := by
  obtain ⟨fn, hfn⟩ := compiled_language hF (k := D.bnil) (d := lib[D.bnil]) rfl
  obtain ⟨fs, hfs⟩ := compiled_language hF (k := D.succ) (d := lib[D.succ]) rfl
  obtain ⟨fl, hfl⟩ := compiled_language hF (k := D.lcase) (d := lib[D.lcase]) rfl
  let RV := Rep.prod RBits (Rep.exp RBits RBits)
  refine rep_def (τ' := []) hF
    (d := mkDefn 0 [bitsTy, bitsTy] bitsTy
      (Term.app (Term.snd (Term.listRec (Term.pair bnilT (Term.lam bitsTy (v 0)))
        (Term.pair (consT bitTy (v 1) (Term.fst (v 0)))
          (Term.lam bitsTy (lcaseB bitTy bitsTy (v 0) (consT bitTy (v 2) (Term.fst (v 1)))
            (Term.lam bitTy (Term.lam bitsTy (consT bitTy (digitT (v 1) (v 4))
              (Term.app (Term.lam bitsTy (ifBit bitsTy (v 2)
                  (ifBit bitsTy (v 5) (v 0) (call D.succ [] [v 0])) (call D.succ [] [v 0])))
                (Term.app (Term.snd (v 3)) (v 0)))))))))
        (v 0))) (v 1))) rfl
    (repC_app (repC_snd (repC_listRec
      (repC_var (envRep_std₂ ?_ ?_ RBits RBits) rfl)
      (repC_pair
        (repC_call₀ rfl rfl hwf hfn rfl rfl (a := bitsTy) rfl ?_ (rep_bnil hF hfn))
        (repC_lam ?_ ?_ ?_ (repC_var0 ?_ ?_)))
      (repC_pair
        (repC_cons rfl ?_ (repC_pair
          (repC_var (envRep_listStep ?_ ?_ RBit RV) rfl)
          (repC_fst (repC_var (envRep_listStep ?_ ?_ RBit RV) rfl) ?_ ?_)) ?_)
        (repC_lam ?_ ?_ ?_
          (repC_call₃ (τ' := [Bit, List Bit]) (a := bitsTy) rfl rfl hwf hfl rfl ?_ ?_
            (.cons ?_ (.cons ?_ .nil)) rfl rfl (rep_lcase hF hfl RBit RBits)
            (repC_var0 ?_ ?_)
            (repC_lam ?_ ?_ ?_ (repC_cons rfl ?_ (repC_pair
              (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_var (envRep_listStep ?_ ?_ RBit RV) rfl)))
              (repC_fst (repC_varS ?_ ?_ (repC_varS ?_ ?_
                (repC_var (envRep_listStep ?_ ?_ RBit RV) rfl))) ?_ ?_)) ?_))
            (repC_lam ?_ ?_ ?_ (repC_lam ?_ ?_ ?_ (repC_cons rfl ?_ (repC_pair
              (repC_ifBit rfl ?_ (repC_varS ?_ ?_ (repC_var0 ?_ ?_))
                (repC_ifBit rfl ?_ (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_varS ?_ ?_
                    (repC_varS ?_ ?_ (repC_var (envRep_listStep ?_ ?_ RBit RV) rfl)))))
                  (repC_inr rfl ?_ ?_ (repC_star ?_ _) ?_ ?_ Rep.unit)
                  (repC_inl rfl ?_ ?_ (repC_star ?_ _) ?_ ?_ Rep.unit) ?_ ?_)
                (repC_ifBit rfl ?_ (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_varS ?_ ?_
                    (repC_varS ?_ ?_ (repC_var (envRep_listStep ?_ ?_ RBit RV) rfl)))))
                  (repC_inl rfl ?_ ?_ (repC_star ?_ _) ?_ ?_ Rep.unit)
                  (repC_inr rfl ?_ ?_ (repC_star ?_ _) ?_ ?_ Rep.unit) ?_ ?_) ?_ ?_)
              (repC_app (repC_lam ?_ ?_ ?_
                (repC_ifBit rfl ?_ (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_var0 ?_ ?_)))
                  (repC_ifBit rfl ?_ (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_varS ?_ ?_
                      (repC_varS ?_ ?_ (repC_varS ?_ ?_
                        (repC_var (envRep_listStep ?_ ?_ RBit RV) rfl))))))
                    (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_var0 ?_ ?_)))
                    (repC_call₁ (τ' := []) (a := bitsTy) rfl rfl hwf hfs rfl (by simp)
                      (by simp) .nil rfl rfl (rep_succ hF hwf hfs)
                      (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_var0 ?_ ?_)))) ?_ ?_)
                  (repC_call₁ (τ' := []) (a := bitsTy) rfl rfl hwf hfs rfl (by simp)
                    (by simp) .nil rfl rfl (rep_succ hF hwf hfs)
                    (repC_varS ?_ ?_ (repC_var0 ?_ ?_))) ?_ ?_))
                (repC_app (repC_snd (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_varS ?_ ?_
                    (repC_var (envRep_listStep ?_ ?_ RBit RV) rfl)))) ?_ ?_)
                  (repC_var0 ?_ ?_) ?_ ?_) ?_ ?_)) ?_)))))) ?_) ?_ ?_)
      (repC_var (envRep_std₂ ?_ ?_ RBits RBits) rfl) ?_ ?_) ?hc hdk
  case hc =>
    rintro ⟨m, w⟩
    refine congrFun (congrArg Prod.snd
      (foldr_para _ _ (fun w m ↦ ofNum (rankB m + rankB w)) ?_ ?_ w)) m
    · funext m
      simp
    · intro y l
      funext m
      rcases m with _ | ⟨(⟨⟨⟩⟩ | ⟨⟨⟩⟩), m⟩ <;> rcases y with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;>
        simp [eq_ofNum_iff] <;> omega
  side_goals

/-- The comparison of bitstrings represents the comparison of their indices. -/
theorem rep_cmp (hF : compileDefs (globals defs) = some ds) (hwf : PartialHorn.DefnsWF sig ds)
    {fk : Tree} (hdk : ds[D.cmp]? = some ⟨[], arr, fk⟩) :
    Represents [] (unfoldTerm sig ds fk) (Rep.prod RBits RBits) ROrd
      fun p ↦ ordB (rankB p.1) (rankB p.2) := by
  obtain ⟨fc, hfc⟩ := compiled_language hF (k := D.cond) (d := lib[D.cond]) rfl
  obtain ⟨fl, hfl⟩ := compiled_language hF (k := D.lcase) (d := lib[D.lcase]) rfl
  let RV := Rep.exp RBits ROrd
  refine rep_def (τ' := []) hF
    (d := mkDefn 0 [bitsTy, bitsTy] ordTy
      (Term.app (Term.listRec (Term.lam bitsTy (condT ordTy (v 0) gtO eqO))
        (Term.lam bitsTy (lcaseB bitTy ordTy (v 0) ltO
          (Term.lam bitTy (Term.lam bitsTy
            (ifOrd ordTy (Term.app (v 3) (v 0)) ltO (bitOrdT (v 1) (v 4)) gtO)))))
        (v 0)) (v 1))) rfl
    (repC_app (repC_listRec (repC_var (envRep_std₂ ?_ ?_ RBits RBits) rfl)
      (repC_lam ?_ ?_ ?_ (repC_call₃ (τ' := [Unit ⊕ Bit]) (a := ordTy) rfl rfl hwf hfc rfl ?_ ?_
        (.cons ?_ .nil) rfl rfl (rep_cond hF hfc ROrd) (repC_var0 ?_ ?_)
        (repC_inr rfl ?_ ?_ (repC_inr rfl ?_ ?_ (repC_star ?_ _) ?_ ?_ Rep.unit) ?_ ?_ Rep.unit)
        (repC_inr rfl ?_ ?_ (repC_inl rfl ?_ ?_ (repC_star ?_ _) ?_ ?_ Rep.unit) ?_ ?_ Rep.unit)))
      (repC_lam ?_ ?_ ?_ (repC_call₃ (τ' := [Bit, Unit ⊕ Bit]) (a := ordTy) rfl rfl hwf hfl rfl
        ?_ ?_ (.cons ?_ (.cons ?_ .nil)) rfl rfl (rep_lcase hF hfl RBit ROrd) (repC_var0 ?_ ?_)
        (repC_lam ?_ ?_ ?_ (repC_inl rfl ?_ ?_ (repC_star ?_ _) ?_ ?_ RBit))
        (repC_lam ?_ ?_ ?_ (repC_lam ?_ ?_ ?_ (repC_ifOrd rfl ?_
          (repC_app (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_varS ?_ ?_
            (repC_var (envRep_listStep ?_ ?_ RBit RV) rfl)))) (repC_var0 ?_ ?_) ?_ ?_)
          (repC_inl rfl ?_ ?_ (repC_star ?_ _) ?_ ?_ RBit)
          (repC_ifBit rfl ?_ (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_var0 ?_ ?_))))
            (repC_ifBit rfl ?_ (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_varS ?_ ?_
                (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_varS ?_ ?_
                  (repC_var (envRep_listStep ?_ ?_ RBit RV) rfl)))))))
              (repC_inr rfl ?_ ?_ (repC_inl rfl ?_ ?_ (repC_star ?_ _) ?_ ?_ Rep.unit) ?_ ?_
                Rep.unit)
              (repC_inl rfl ?_ ?_ (repC_star ?_ _) ?_ ?_ RBit) ?_ ?_)
            (repC_ifBit rfl ?_ (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_varS ?_ ?_
                (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_varS ?_ ?_
                  (repC_var (envRep_listStep ?_ ?_ RBit RV) rfl)))))))
              (repC_inr rfl ?_ ?_ (repC_inr rfl ?_ ?_ (repC_star ?_ _) ?_ ?_ Rep.unit) ?_ ?_
                Rep.unit)
              (repC_inr rfl ?_ ?_ (repC_inl rfl ?_ ?_ (repC_star ?_ _) ?_ ?_ Rep.unit) ?_ ?_
                Rep.unit) ?_ ?_) ?_ ?_)
          (repC_inr rfl ?_ ?_ (repC_inr rfl ?_ ?_ (repC_star ?_ _) ?_ ?_ Rep.unit) ?_ ?_ Rep.unit)
          ?_ ?_))))) ?_)
      (repC_var (envRep_std₂ ?_ ?_ RBits RBits) rfl) ?_ ?_) ?hc hdk
  case hc =>
    rintro ⟨m, w⟩
    refine congrFun (foldr_eq _ _ (fun w m ↦ ordB (rankB m) (rankB w)) ?_ ?_ w) m
    · funext m
      rcases m with _ | ⟨(⟨⟨⟩⟩ | ⟨⟨⟩⟩), m⟩ <;> simp [ordB]
    · intro y l
      funext m
      rcases m with _ | ⟨(⟨⟨⟩⟩ | ⟨⟨⟩⟩), m⟩ <;> rcases y with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;>
        simp only [ordB, rankB_cons_inl, rankB_cons_inr, rankB_nil, Function.comp_apply] <;>
        split_ifs <;> first | rfl | omega
  side_goals

/-- Whether one bitstring's index is less than another's represents the index one or zero. -/
theorem rep_ltB (hF : compileDefs (globals defs) = some ds) (hwf : PartialHorn.DefnsWF sig ds)
    {fk : Tree} (hdk : ds[D.ltB]? = some ⟨[], arr, fk⟩) :
    Represents [] (unfoldTerm sig ds fk) (Rep.prod RBits RBits) RBits
      fun p ↦ ofNum (if rankB p.1 < rankB p.2 then 1 else 0) := by
  obtain ⟨fn, hfn⟩ := compiled_language hF (k := D.bnil) (d := lib[D.bnil]) rfl
  obtain ⟨f0, hf0⟩ := compiled_language hF (k := D.b0) (d := lib[D.b0]) rfl
  obtain ⟨fc, hfc⟩ := compiled_language hF (k := D.cmp) (d := lib[D.cmp]) rfl
  refine rep_def (τ' := []) hF
    (d := mkDefn 0 [bitsTy, bitsTy] bitsTy (ifOrd bitsTy (cmpT (v 1) (v 0)) trueT bnilT bnilT))
    rfl (repC_ifOrd rfl ?_
      (repC_call₂ (τ' := []) (a := ordTy) rfl rfl hwf hfc rfl (by simp) (by simp) .nil rfl rfl
        (rep_cmp hF hwf hfc) (repC_var (envRep_std₂ ?_ ?_ RBits RBits) rfl)
        (repC_var (envRep_std₂ ?_ ?_ RBits RBits) rfl))
      (repC_call₁ (τ' := []) (a := bitsTy) rfl rfl hwf hf0 rfl (by simp) (by simp) .nil rfl rfl
        (rep_b0 hF hf0) (repC_call₀ rfl rfl hwf hfn rfl rfl (a := bitsTy) rfl ?_ (rep_bnil hF hfn)))
      (repC_call₀ rfl rfl hwf hfn rfl rfl (a := bitsTy) rfl ?_ (rep_bnil hF hfn))
      (repC_call₀ rfl rfl hwf hfn rfl rfl (a := bitsTy) rfl ?_ (rep_bnil hF hfn)) ?_ ?_) ?hc hdk
  case hc =>
    rintro ⟨m, w⟩
    simp only [ordB, Function.comp_apply, id]
    split_ifs <;> rfl
  side_goals

/-- Whether two bitstrings' indices are equal represents the index one or zero. -/
theorem rep_eqB (hF : compileDefs (globals defs) = some ds) (hwf : PartialHorn.DefnsWF sig ds)
    {fk : Tree} (hdk : ds[D.eqB]? = some ⟨[], arr, fk⟩) :
    Represents [] (unfoldTerm sig ds fk) (Rep.prod RBits RBits) RBits
      fun p ↦ ofNum (if rankB p.1 = rankB p.2 then 1 else 0) := by
  obtain ⟨fn, hfn⟩ := compiled_language hF (k := D.bnil) (d := lib[D.bnil]) rfl
  obtain ⟨f0, hf0⟩ := compiled_language hF (k := D.b0) (d := lib[D.b0]) rfl
  obtain ⟨fc, hfc⟩ := compiled_language hF (k := D.cmp) (d := lib[D.cmp]) rfl
  refine rep_def (τ' := []) hF
    (d := mkDefn 0 [bitsTy, bitsTy] bitsTy (ifOrd bitsTy (cmpT (v 1) (v 0)) bnilT trueT bnilT))
    rfl (repC_ifOrd rfl ?_
      (repC_call₂ (τ' := []) (a := ordTy) rfl rfl hwf hfc rfl (by simp) (by simp) .nil rfl rfl
        (rep_cmp hF hwf hfc) (repC_var (envRep_std₂ ?_ ?_ RBits RBits) rfl)
        (repC_var (envRep_std₂ ?_ ?_ RBits RBits) rfl))
      (repC_call₀ rfl rfl hwf hfn rfl rfl (a := bitsTy) rfl ?_ (rep_bnil hF hfn))
      (repC_call₁ (τ' := []) (a := bitsTy) rfl rfl hwf hf0 rfl (by simp) (by simp) .nil rfl rfl
        (rep_b0 hF hf0) (repC_call₀ rfl rfl hwf hfn rfl rfl (a := bitsTy) rfl ?_ (rep_bnil hF hfn)))
      (repC_call₀ rfl rfl hwf hfn rfl rfl (a := bitsTy) rfl ?_ (rep_bnil hF hfn)) ?_ ?_) ?hc hdk
  case hc =>
    rintro ⟨m, w⟩
    simp only [ordB, Function.comp_apply, id]
    split_ifs <;> first | rfl | omega
  side_goals

/-- The difference of bitstrings, by the definition that assumes the second index at most the
first, represents a function whose value there is the bitstring of the difference. -/
theorem rep_subE (hF : compileDefs (globals defs) = some ds) (hwf : PartialHorn.DefnsWF sig ds)
    {fk : Tree} (hdk : ds[D.subE]? = some ⟨[], arr, fk⟩) :
    ∃ F : List Bit × List Bit → List Bit,
      Represents [] (unfoldTerm sig ds fk) (Rep.prod RBits RBits) RBits F ∧
        ∀ p, rankB p.2 ≤ rankB p.1 → F p = ofNum (rankB p.1 - rankB p.2) := by
  obtain ⟨fn, hfn⟩ := compiled_language hF (k := D.bnil) (d := lib[D.bnil]) rfl
  obtain ⟨f0, hf0⟩ := compiled_language hF (k := D.b0) (d := lib[D.b0]) rfl
  obtain ⟨fp, hfp⟩ := compiled_language hF (k := D.pred) (d := lib[D.pred]) rfl
  obtain ⟨fd, hfd⟩ := compiled_language hF (k := D.dbl) (d := lib[D.dbl]) rfl
  obtain ⟨fl, hfl⟩ := compiled_language hF (k := D.lcase) (d := lib[D.lcase]) rfl
  let RV := Rep.exp RBits RBits
  refine ⟨_, rep_def (τ' := []) hF
    (d := mkDefn 0 [bitsTy, bitsTy] bitsTy
      (Term.app (Term.listRec (Term.lam bitsTy (v 0))
        (Term.lam bitsTy (lcaseB bitTy bitsTy (v 0) bnilT
          (Term.lam bitTy (Term.lam bitsTy (Term.app (Term.lam bitsTy
            (ifBit bitsTy (v 2)
              (ifBit bitsTy (v 5) (call D.dbl [] [v 0]) (b0T (call D.pred [] [v 0])))
              (ifBit bitsTy (v 5) (b0T (v 0)) (call D.dbl [] [v 0]))))
            (Term.app (v 3) (v 0)))))))
        (v 0)) (v 1))) rfl
    (repC_app (repC_listRec (repC_var (envRep_std₂ ?_ ?_ RBits RBits) rfl)
      (repC_lam ?_ ?_ ?_ (repC_var0 ?_ ?_))
      (repC_lam ?_ ?_ ?_ (repC_call₃ (τ' := [Bit, List Bit]) (a := bitsTy) (p₁ := list bitTy)
        (p₂ := exp one bitsTy) (p₃ := exp bitTy (exp (list bitTy) bitsTy)) rfl rfl hwf hfl rfl
        ?_ ?_ (.cons ?_ (.cons ?_ .nil)) rfl rfl (rep_lcase hF hfl RBit RBits) (repC_var0 ?_ ?_)
        (repC_lam ?_ ?_ ?_
          (repC_call₀ rfl rfl hwf hfn rfl rfl (a := bitsTy) rfl ?_ (rep_bnil hF hfn)))
        (repC_lam ?_ ?_ ?_ (repC_lam ?_ ?_ ?_ (repC_app (repC_lam ?_ ?_ ?_
          (repC_ifBit rfl ?_ (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_var0 ?_ ?_)))
            (repC_ifBit rfl ?_ (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_varS ?_ ?_
                (repC_varS ?_ ?_ (repC_varS ?_ ?_
                  (repC_var (envRep_listStep ?_ ?_ RBit RV) rfl))))))
              (repC_call₁ (τ' := []) (a := bitsTy) rfl rfl hwf hfd rfl (by simp) (by simp) .nil
                rfl rfl (rep_dbl hF hwf hfd) (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_var0 ?_ ?_))))
              (repC_call₁ (τ' := []) (a := bitsTy) rfl rfl hwf hf0 rfl (by simp) (by simp) .nil
                rfl rfl (rep_b0 hF hf0)
                (repC_call₁ (τ' := []) (a := bitsTy) rfl rfl hwf hfp rfl (by simp) (by simp) .nil
                  rfl rfl (rep_pred hF hwf hfp)
                  (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_var0 ?_ ?_))))) ?_ ?_)
            (repC_ifBit rfl ?_ (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_varS ?_ ?_
                (repC_varS ?_ ?_ (repC_varS ?_ ?_
                  (repC_var (envRep_listStep ?_ ?_ RBit RV) rfl))))))
              (repC_call₁ (τ' := []) (a := bitsTy) rfl rfl hwf hf0 rfl (by simp) (by simp) .nil
                rfl rfl (rep_b0 hF hf0) (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_var0 ?_ ?_))))
              (repC_call₁ (τ' := []) (a := bitsTy) rfl rfl hwf hfd rfl (by simp) (by simp) .nil
                rfl rfl (rep_dbl hF hwf hfd) (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_var0 ?_ ?_))))
              ?_ ?_) ?_ ?_))
          (repC_app (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_varS ?_ ?_
            (repC_var (envRep_listStep ?_ ?_ RBit RV) rfl)))) (repC_var0 ?_ ?_) ?_ ?_) ?_ ?_)))))
      ?_)
      (repC_var (envRep_std₂ ?_ ?_ RBits RBits) rfl) ?_ ?_) (fun _ ↦ rfl) hdk, ?pre⟩
  case pre =>
    rintro ⟨m, w⟩ h
    refine foldr_apply_eq _ _ (fun w m ↦ ofNum (rankB m - rankB w)) (fun w m ↦ rankB w ≤ rankB m)
      ?_ ?_ w m h
    · intro c _
      simp
    · intro y l g ih c hc
      rcases c with _ | ⟨(⟨⟨⟩⟩ | ⟨⟨⟩⟩), c⟩ <;> rcases y with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;>
        simp only [rankB_cons_inl, rankB_cons_inr, rankB_nil] at hc
      all_goals try omega
      all_goals
        simp only [Function.comp_apply, ih c (by omega)]
        simp [eq_ofNum_iff]
        omega
  side_goals

/-- The truncated difference of bitstrings represents the truncated difference of their
indices. -/
theorem rep_sub (hF : compileDefs (globals defs) = some ds) (hwf : PartialHorn.DefnsWF sig ds)
    {fk : Tree} (hdk : ds[D.sub]? = some ⟨[], arr, fk⟩) :
    Represents [] (unfoldTerm sig ds fk) (Rep.prod RBits RBits) RBits
      fun p ↦ ofNum (rankB p.1 - rankB p.2) := by
  obtain ⟨fn, hfn⟩ := compiled_language hF (k := D.bnil) (d := lib[D.bnil]) rfl
  obtain ⟨fc, hfc⟩ := compiled_language hF (k := D.cond) (d := lib[D.cond]) rfl
  obtain ⟨fl, hfl⟩ := compiled_language hF (k := D.ltB) (d := lib[D.ltB]) rfl
  obtain ⟨fe, hfe⟩ := compiled_language hF (k := D.subE) (d := lib[D.subE]) rfl
  obtain ⟨FE, hFE, hFE'⟩ := rep_subE hF hwf hfe
  refine rep_def (τ' := []) hF
    (d := mkDefn 0 [bitsTy, bitsTy] bitsTy
      (condT bitsTy (call D.ltB [] [v 1, v 0]) bnilT (call D.subE [] [v 1, v 0]))) rfl
    (repC_call₃ (τ' := [List Bit]) (a := bitsTy) rfl rfl hwf hfc rfl ?_ ?_ (.cons ?_ .nil) rfl rfl
      (rep_cond hF hfc RBits)
      (repC_call₂ (τ' := []) (a := bitsTy) rfl rfl hwf hfl rfl (by simp) (by simp) .nil rfl rfl
        (rep_ltB hF hwf hfl) (repC_var (envRep_std₂ ?_ ?_ RBits RBits) rfl)
        (repC_var (envRep_std₂ ?_ ?_ RBits RBits) rfl))
      (repC_call₀ rfl rfl hwf hfn rfl rfl (a := bitsTy) rfl ?_ (rep_bnil hF hfn))
      (repC_call₂ (τ' := []) (a := bitsTy) rfl rfl hwf hfe rfl (by simp) (by simp) .nil rfl rfl
        hFE (repC_var (envRep_std₂ ?_ ?_ RBits RBits) rfl)
        (repC_var (envRep_std₂ ?_ ?_ RBits RBits) rfl))) ?hc hdk
  case hc =>
    rintro ⟨m, w⟩
    simp only [Function.comp_apply, id]
    split_ifs with h
    · simp only [ofNum_one]
      rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt h), ofNum_zero]
    · simp only [ofNum_zero]
      exact hFE' _ (Nat.le_of_not_lt h)
  side_goals

/-- The product of bitstrings represents the product of their indices. -/
theorem rep_mul (hF : compileDefs (globals defs) = some ds) (hwf : PartialHorn.DefnsWF sig ds)
    {fk : Tree} (hdk : ds[D.mul]? = some ⟨[], arr, fk⟩) :
    Represents [] (unfoldTerm sig ds fk) (Rep.prod RBits RBits) RBits
      fun p ↦ ofNum (rankB p.1 * rankB p.2) := by
  obtain ⟨fn, hfn⟩ := compiled_language hF (k := D.bnil) (d := lib[D.bnil]) rfl
  obtain ⟨fd, hfd⟩ := compiled_language hF (k := D.dbl) (d := lib[D.dbl]) rfl
  obtain ⟨fa, hfa⟩ := compiled_language hF (k := D.add) (d := lib[D.add]) rfl
  let RV := Rep.exp RBits RBits
  refine rep_def (τ' := []) hF
    (d := mkDefn 0 [bitsTy, bitsTy] bitsTy
      (Term.app (Term.listRec (Term.lam bitsTy bnilT)
        (Term.lam bitsTy (call D.add []
          [call D.dbl [] [Term.app (v 1) (v 0)], ifBit bitsTy (v 2) (v 0) (call D.dbl [] [v 0])]))
        (v 0)) (v 1))) rfl
    (repC_app (repC_listRec (repC_var (envRep_std₂ ?_ ?_ RBits RBits) rfl)
      (repC_lam ?_ ?_ ?_
        (repC_call₀ rfl rfl hwf hfn rfl rfl (a := bitsTy) rfl ?_ (rep_bnil hF hfn)))
      (repC_lam ?_ ?_ ?_ (repC_call₂ (τ' := []) (a := bitsTy) rfl rfl hwf hfa rfl (by simp)
        (by simp) .nil rfl rfl (rep_add hF hwf hfa)
        (repC_call₁ (τ' := []) (a := bitsTy) rfl rfl hwf hfd rfl (by simp) (by simp) .nil rfl rfl
          (rep_dbl hF hwf hfd) (repC_app (repC_varS ?_ ?_
            (repC_var (envRep_listStep ?_ ?_ RBit RV) rfl)) (repC_var0 ?_ ?_) ?_ ?_))
        (repC_ifBit rfl ?_ (repC_varS ?_ ?_ (repC_var (envRep_listStep ?_ ?_ RBit RV) rfl))
          (repC_varS ?_ ?_ (repC_var0 ?_ ?_))
          (repC_call₁ (τ' := []) (a := bitsTy) rfl rfl hwf hfd rfl (by simp) (by simp) .nil rfl
            rfl (rep_dbl hF hwf hfd) (repC_varS ?_ ?_ (repC_var0 ?_ ?_))) ?_ ?_))) ?_)
      (repC_var (envRep_std₂ ?_ ?_ RBits RBits) rfl) ?_ ?_) ?hc hdk
  case hc =>
    rintro ⟨m, w⟩
    refine congrFun (foldr_eq _ _ (fun w m ↦ ofNum (rankB m * rankB w)) ?_ ?_ w) m
    · funext m
      simp
    · intro y l
      funext m
      rcases y with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> simp [eq_ofNum_iff, Nat.mul_add, Nat.mul_left_comm (rankB m) 2]
      omega
  side_goals

/-- The quotient and the remainder of bitstrings represent those of their indices. -/
theorem rep_divMod (hF : compileDefs (globals defs) = some ds) (hwf : PartialHorn.DefnsWF sig ds)
    {fk : Tree} (hdk : ds[D.divMod]? = some ⟨[], arr, fk⟩) :
    Represents [] (unfoldTerm sig ds fk) (Rep.prod RBits RBits) (Rep.prod RBits RBits)
      fun p ↦ (ofNum (rankB p.1 / rankB p.2), ofNum (rankB p.1 % rankB p.2)) := by
  obtain ⟨fn, hfn⟩ := compiled_language hF (k := D.bnil) (d := lib[D.bnil]) rfl
  obtain ⟨f0, hf0⟩ := compiled_language hF (k := D.b0) (d := lib[D.b0]) rfl
  obtain ⟨f1, hf1⟩ := compiled_language hF (k := D.b1) (d := lib[D.b1]) rfl
  obtain ⟨fc, hfc⟩ := compiled_language hF (k := D.cond) (d := lib[D.cond]) rfl
  obtain ⟨fd, hfd⟩ := compiled_language hF (k := D.dbl) (d := lib[D.dbl]) rfl
  obtain ⟨fo, hfo⟩ := compiled_language hF (k := D.cmp) (d := lib[D.cmp]) rfl
  obtain ⟨fe, hfe⟩ := compiled_language hF (k := D.subE) (d := lib[D.subE]) rfl
  obtain ⟨FE, hFE, hFE'⟩ := rep_subE hF hwf hfe
  let RP := Rep.prod RBits RBits
  let RV := Rep.exp RBits RP
  refine rep_def (τ' := []) hF
    (d := mkDefn 0 [bitsTy, bitsTy] (prod bitsTy bitsTy)
      (condT (prod bitsTy bitsTy) (v 0)
        (Term.app (Term.listRec (Term.lam bitsTy (Term.pair bnilT bnilT))
          (Term.lam bitsTy (Term.app (Term.lam (prod bitsTy bitsTy) (Term.app (Term.lam bitsTy
              (ifOrd (prod bitsTy bitsTy) (cmpT (v 0) (v 2))
                (Term.pair (call D.dbl [] [Term.fst (v 1)]) (v 0))
                (Term.pair (b0T (Term.fst (v 1))) bnilT)
                (ifOrd (prod bitsTy bitsTy) (cmpT (v 0) (call D.dbl [] [v 2]))
                  (Term.pair (b0T (Term.fst (v 1))) (call D.subE [] [v 0, v 2]))
                  (Term.pair (b1T (Term.fst (v 1))) bnilT)
                  (Term.pair (b1T (Term.fst (v 1))) bnilT))))
              (consT bitTy (v 3) (Term.snd (v 0)))))
            (Term.app (v 1) (v 0))))
          (v 1)) (v 0))
        (Term.pair bnilT (v 1)))) rfl
    (repC_call₃ (τ' := [List Bit × List Bit]) (a := prod bitsTy bitsTy) rfl rfl hwf hfc rfl ?_ ?_
      (.cons ?_ .nil) rfl rfl (rep_cond hF hfc RP)
      (repC_var (envRep_std₂ ?_ ?_ RBits RBits) rfl)
      (repC_app (repC_listRec (repC_var (envRep_std₂ ?_ ?_ RBits RBits) rfl)
        (repC_lam ?_ ?_ ?_ (repC_pair
          (repC_call₀ rfl rfl hwf hfn rfl rfl (a := bitsTy) rfl ?_ (rep_bnil hF hfn))
          (repC_call₀ rfl rfl hwf hfn rfl rfl (a := bitsTy) rfl ?_ (rep_bnil hF hfn))))
        (repC_lam ?_ ?_ ?_ (repC_app (repC_lam ?_ ?_ ?_ (repC_app (repC_lam ?_ ?_ ?_
            (repC_ifOrd rfl ?_
              (repC_call₂ (τ' := []) (a := ordTy) rfl rfl hwf hfo rfl (by simp) (by simp) .nil rfl
                rfl (rep_cmp hF hwf hfo) (repC_var0 ?_ ?_)
                (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_var0 ?_ ?_))))
              (repC_pair
                (repC_call₁ (τ' := []) (a := bitsTy) rfl rfl hwf hfd rfl (by simp) (by simp) .nil
                  rfl rfl (rep_dbl hF hwf hfd)
                  (repC_fst (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_var0 ?_ ?_))) ?_ ?_))
                (repC_varS ?_ ?_ (repC_var0 ?_ ?_)))
              (repC_pair
                (repC_call₁ (τ' := []) (a := bitsTy) rfl rfl hwf hf0 rfl (by simp) (by simp) .nil
                  rfl rfl (rep_b0 hF hf0) (repC_fst (repC_varS ?_ ?_ (repC_varS ?_ ?_
                    (repC_varS ?_ ?_ (repC_var0 ?_ ?_)))) ?_ ?_))
                (repC_call₀ rfl rfl hwf hfn rfl rfl (a := bitsTy) rfl ?_ (rep_bnil hF hfn)))
              (repC_ifOrd rfl ?_
                (repC_call₂ (τ' := []) (a := ordTy) rfl rfl hwf hfo rfl (by simp) (by simp) .nil
                  rfl rfl (rep_cmp hF hwf hfo)
                  (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_var0 ?_ ?_)))
                  (repC_call₁ (τ' := []) (a := bitsTy) rfl rfl hwf hfd rfl (by simp) (by simp)
                    .nil rfl rfl (rep_dbl hF hwf hfd) (repC_varS ?_ ?_ (repC_varS ?_ ?_
                      (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_var0 ?_ ?_)))))))
                (repC_pair
                  (repC_call₁ (τ' := []) (a := bitsTy) rfl rfl hwf hf0 rfl (by simp) (by simp)
                    .nil rfl rfl (rep_b0 hF hf0) (repC_fst (repC_varS ?_ ?_ (repC_varS ?_ ?_
                      (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_var0 ?_ ?_))))) ?_ ?_))
                  (repC_call₂ (τ' := []) (a := bitsTy) rfl rfl hwf hfe rfl (by simp) (by simp)
                    .nil rfl rfl hFE
                    (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_var0 ?_ ?_))))
                    (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_varS ?_ ?_
                      (repC_varS ?_ ?_ (repC_var0 ?_ ?_))))))))
                (repC_pair
                  (repC_call₁ (τ' := []) (a := bitsTy) rfl rfl hwf hf1 rfl (by simp) (by simp)
                    .nil rfl rfl (rep_b1 hF hf1) (repC_fst (repC_varS ?_ ?_ (repC_varS ?_ ?_
                      (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_var0 ?_ ?_))))))
                      ?_ ?_))
                  (repC_call₀ rfl rfl hwf hfn rfl rfl (a := bitsTy) rfl ?_ (rep_bnil hF hfn)))
                (repC_pair
                  (repC_call₁ (τ' := []) (a := bitsTy) rfl rfl hwf hf1 rfl (by simp) (by simp)
                    .nil rfl rfl (rep_b1 hF hf1) (repC_fst (repC_varS ?_ ?_ (repC_varS ?_ ?_
                      (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_var0 ?_ ?_))))))
                      ?_ ?_))
                  (repC_call₀ rfl rfl hwf hfn rfl rfl (a := bitsTy) rfl ?_ (rep_bnil hF hfn)))
                ?_ ?_) ?_ ?_))
            (repC_cons rfl ?_ (repC_pair
              (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_var (envRep_listStep ?_ ?_ RBit RV) rfl)))
              (repC_snd (repC_var0 ?_ ?_) ?_ ?_)) ?_) ?_ ?_))
          (repC_app (repC_varS ?_ ?_ (repC_var (envRep_listStep ?_ ?_ RBit RV) rfl))
            (repC_var0 ?_ ?_) ?_ ?_) ?_ ?_)) ?_)
        (repC_var (envRep_std₂ ?_ ?_ RBits RBits) rfl) ?_ ?_)
      (repC_pair (repC_call₀ rfl rfl hwf hfn rfl rfl (a := bitsTy) rfl ?_ (rep_bnil hF hfn))
        (repC_var (envRep_std₂ ?_ ?_ RBits RBits) rfl))) ?hc hdk
  case hc =>
    rintro ⟨m, _ | ⟨b, d⟩⟩
    · simp
    · have hD : 0 < rankB (b :: d) := by rcases b with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> simp
      refine foldr_apply_eq _ _ (fun w c ↦ (ofNum (rankB w / rankB c), ofNum (rankB w % rankB c)))
        (fun _ c ↦ 0 < rankB c) ?_ ?_ m _ hD
      · intro c _
        simp
      · intro y l g ih c hc
        simp only [Function.comp_apply, ih c hc]
        have hL := Nat.mod_add_div (rankB l) (rankB c)
        have hr := Nat.mod_lt (rankB l) hc
        have e₀ := Nat.mul_left_comm (rankB c) 2 (rankB l / rankB c)
        have e₁ : rankB c * (2 * (rankB l / rankB c) + 1) =
            2 * (rankB c * (rankB l / rankB c)) + rankB c := by
          rw [Nat.mul_add, Nat.mul_one, e₀]
        have e₂ : rankB c * (2 * (rankB l / rankB c) + 2) =
            2 * (rankB c * (rankB l / rankB c)) + 2 * rankB c := by
          rw [Nat.mul_add, e₀, Nat.mul_comm (rankB c) 2]
        rcases y with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;>
          simp only [ordB, rankB_cons_inl, rankB_cons_inr, rankB_ofNum, cons_inl_ofNum,
            cons_inr_ofNum] <;> split_ifs <;> simp only [Sum.elim_inl, Sum.elim_inr]
        all_goals first
          | (exfalso; omega)
          | (rw [← ofNum_zero]; exact ofNum_divMod (by omega) (by omega))
          | (rw [hFE'] <;> simp only [rankB_ofNum]
             · exact ofNum_divMod (by omega) (by omega)
             · omega)
          | exact ofNum_divMod (by omega) (by omega)
  side_goals

/-- The base-two logarithm of a bitstring represents that of its index, zero at zero. -/
theorem rep_log2 (hF : compileDefs (globals defs) = some ds) (hwf : PartialHorn.DefnsWF sig ds)
    {fk : Tree} (hdk : ds[D.log2]? = some ⟨[], arr, fk⟩) :
    Represents [] (unfoldTerm sig ds fk) RBits RBits fun w ↦ ofNum (rankB w).log2 := by
  obtain ⟨fn, hfn⟩ := compiled_language hF (k := D.bnil) (d := lib[D.bnil]) rfl
  obtain ⟨f0, hf0⟩ := compiled_language hF (k := D.b0) (d := lib[D.b0]) rfl
  obtain ⟨fc, hfc⟩ := compiled_language hF (k := D.cond) (d := lib[D.cond]) rfl
  obtain ⟨fs, hfs⟩ := compiled_language hF (k := D.succ) (d := lib[D.succ]) rfl
  obtain ⟨fp, hfp⟩ := compiled_language hF (k := D.pred) (d := lib[D.pred]) rfl
  let RV := Rep.prod RBits RBits
  refine rep_def (τ' := []) hF
    (d := mkDefn 0 [bitsTy] bitsTy
      (Term.app (Term.lam (prod bitsTy bitsTy) (condT bitsTy (Term.snd (v 0)) (Term.fst (v 0))
          (call D.pred [] [Term.fst (v 0)])))
        (Term.listRec (Term.pair bnilT bnilT)
          (Term.app (Term.lam (prod bitsTy bitsTy) (Term.pair (call D.succ [] [Term.fst (v 0)])
            (ifBit bitsTy (v 2) (Term.snd (v 0)) trueT))) (v 0))
          (v 0)))) rfl
    (repC_app (repC_lam ?_ ?_ ?_ (repC_call₃ (τ' := [List Bit]) (a := bitsTy) rfl rfl hwf hfc rfl
        ?_ ?_ (.cons ?_ .nil) rfl rfl (rep_cond hF hfc RBits)
        (repC_snd (repC_var0 ?_ ?_) ?_ ?_) (repC_fst (repC_var0 ?_ ?_) ?_ ?_)
        (repC_call₁ (τ' := []) (a := bitsTy) rfl rfl hwf hfp rfl (by simp) (by simp) .nil rfl rfl
          (rep_pred hF hwf hfp) (repC_fst (repC_var0 ?_ ?_) ?_ ?_))))
      (repC_listRec (repC_var (envRep_std₁ ?_ RBits) rfl)
        (repC_pair
          (repC_call₀ rfl rfl hwf hfn rfl rfl (a := bitsTy) rfl ?_ (rep_bnil hF hfn))
          (repC_call₀ rfl rfl hwf hfn rfl rfl (a := bitsTy) rfl ?_ (rep_bnil hF hfn)))
        (repC_app (repC_lam ?_ ?_ ?_ (repC_pair
            (repC_call₁ (τ' := []) (a := bitsTy) rfl rfl hwf hfs rfl (by simp) (by simp) .nil rfl
              rfl (rep_succ hF hwf hfs) (repC_fst (repC_var0 ?_ ?_) ?_ ?_))
            (repC_ifBit rfl ?_ (repC_varS ?_ ?_ (repC_var (envRep_listStep ?_ ?_ RBit RV) rfl))
              (repC_snd (repC_varS ?_ ?_ (repC_var0 ?_ ?_)) ?_ ?_)
              (repC_call₁ (τ' := []) (a := bitsTy) rfl rfl hwf hf0 rfl (by simp) (by simp) .nil
                rfl rfl (rep_b0 hF hf0)
                (repC_call₀ rfl rfl hwf hfn rfl rfl (a := bitsTy) rfl ?_ (rep_bnil hF hfn)))
              ?_ ?_)))
          (repC_var (envRep_listStep ?_ ?_ RBit RV) rfl) ?_ ?_) ?_) ?_ ?_) ?hc hdk
  case hc =>
    intro w
    simp only [id, Function.comp_apply]
    rw [foldr_eq _ _ (fun w ↦ (ofNum w.length, ofNum (if w.any Sum.isRight then 1 else 0)))
      ?_ ?_ w]
    · rw [log2_rankB]
      cases w.any Sum.isRight <;>
        simp only [Bool.false_eq_true, ↓reduceIte, ofNum_zero, ofNum_one, rankB_ofNum]
    · simp only [List.length_nil, ofNum_zero, List.any_nil, Bool.false_eq_true, ↓reduceIte]
    · rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩) l <;> simp only [rankB_ofNum, List.length_cons, List.any_cons,
        Sum.isRight_inl, Sum.isRight_inr, Bool.false_or, Bool.true_or, ↓reduceIte, ofNum_one] <;>
        rfl
  side_goals

/-- Iteration by a bitstring represents the repetition of the function as many times as its
index, at every representation of the values. -/
theorem rep_iter (hF : compileDefs (globals defs) = some ds) {fk : Tree}
    (hdk : ds[D.iter]? = some ⟨[obj], arr, fk⟩) {A S : Type} (R : S → A → Prop) :
    Represents (objs [A]) (unfoldTerm sig ds fk) (Rep.prod (Rep.prod RBits (Rep.exp R R)) R) R
      fun p ↦ Nat.repeat p.1.2 (rankB p.1.1) p.2 := by
  let RV := Rep.exp (Rep.exp R R) (Rep.exp R R)
  refine rep_def (τ' := [A]) hF
    (d := mkDefn 1 [bitsTy, exp X₀ X₀, X₀] X₀
      (Term.app (Term.app (Term.listRec (Term.lam (exp X₀ X₀) (Term.lam X₀ (v 0)))
        (Term.lam (exp X₀ X₀) (Term.lam X₀ (Term.app (Term.lam X₀
            (ifBit X₀ (v 4) (Term.app (v 2) (v 0)) (Term.app (v 2) (Term.app (v 2) (v 0)))))
          (Term.app (Term.app (v 2) (v 1)) (Term.app (Term.app (v 2) (v 1)) (v 0))))))
        (v 2)) (v 1)) (v 0))) rfl
    (repC_app (repC_app (repC_listRec
        (repC_var (envRep_std₃ ?_ ?_ ?_ RBits (Rep.exp R R) R) rfl)
        (repC_lam ?_ ?_ ?_ (repC_lam ?_ ?_ ?_ (repC_var0 ?_ ?_)))
        (repC_lam ?_ ?_ ?_ (repC_lam ?_ ?_ ?_ (repC_app (repC_lam ?_ ?_ ?_
            (repC_ifBit rfl ?_ (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_varS ?_ ?_
                (repC_var (envRep_listStep ?_ ?_ RBit RV) rfl))))
              (repC_app (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_var0 ?_ ?_))))
                (repC_varS ?_ ?_ (repC_var0 ?_ ?_)) ?_ ?_)
              (repC_app (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_var0 ?_ ?_))))
                (repC_app (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_varS ?_ ?_ (repC_var0 ?_ ?_))))
                  (repC_varS ?_ ?_ (repC_var0 ?_ ?_)) ?_ ?_) ?_ ?_) ?_ ?_))
          (repC_app (repC_app (repC_varS ?_ ?_ (repC_varS ?_ ?_
              (repC_var (envRep_listStep ?_ ?_ RBit RV) rfl))) (repC_varS ?_ ?_ (repC_var0 ?_ ?_))
              ?_ ?_)
            (repC_app (repC_app (repC_varS ?_ ?_ (repC_varS ?_ ?_
                (repC_var (envRep_listStep ?_ ?_ RBit RV) rfl)))
                (repC_varS ?_ ?_ (repC_var0 ?_ ?_)) ?_ ?_) (repC_var0 ?_ ?_) ?_ ?_) ?_ ?_) ?_ ?_)))
        ?_)
      (repC_var (envRep_std₃ ?_ ?_ ?_ RBits (Rep.exp R R) R) rfl) ?_ ?_)
      (repC_var (envRep_std₃ ?_ ?_ ?_ RBits (Rep.exp R R) R) rfl) ?_ ?_) ?hc hdk
  case hc =>
    rintro ⟨⟨n, f⟩, x⟩
    refine congrFun (congrFun (foldr_eq _ _ (fun n f x ↦ Nat.repeat f (rankB n) x) ?_ ?_ n) f) x
    · rfl
    · rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩) l
      · funext f x
        rw [rankB_cons_inl, repeat_two_mul_add]
        rfl
      · funext f x
        rw [rankB_cons_inr, repeat_two_mul_add]
        rfl
  side_goals

/-- The applications of a list of functions to one argument represent the list of the
applications, at every representation of the arguments and of the values. -/
theorem rep_mapApp (hF : compileDefs (globals defs) = some ds) {fk : Tree}
    (hdk : ds[D.mapApp]? = some ⟨[obj, obj], arr, fk⟩) {A₀ A₁ S₀ S₁ : Type}
    (R₀ : S₀ → A₀ → Prop) (R₁ : S₁ → A₁ → Prop) :
    Represents (objs [A₀, A₁]) (unfoldTerm sig ds fk)
      (Rep.prod (Rep.list (Rep.exp R₀ R₁)) R₀) (Rep.list R₁) fun p ↦ p.1.map (· p.2) := by
  let RV := Rep.exp R₀ (Rep.list R₁)
  refine rep_def (τ' := [A₀, A₁]) hF
    (d := mkDefn 2 [list (exp X₀ X₁), X₀] (list X₁)
      (Term.app (Term.listRec (Term.lam X₀ (nilT X₁))
        (Term.lam X₀ (consT X₁ (Term.app (v 2) (v 0)) (Term.app (v 1) (v 0)))) (v 1)) (v 0))) rfl
    (repC_app (repC_listRec
        (repC_var (envRep_std₂ ?_ ?_ (Rep.list (Rep.exp R₀ R₁)) R₀) rfl)
        (repC_lam ?_ ?_ ?_ (repC_nil rfl ?_ (repC_star ?_ _) ?_ R₁))
        (repC_lam ?_ ?_ ?_ (repC_cons rfl ?_ (repC_pair
          (repC_app (repC_varS ?_ ?_ (repC_var (envRep_listStep ?_ ?_ (Rep.exp R₀ R₁) RV) rfl))
            (repC_var0 ?_ ?_) ?_ ?_)
          (repC_app (repC_varS ?_ ?_ (repC_var (envRep_listStep ?_ ?_ (Rep.exp R₀ R₁) RV) rfl))
            (repC_var0 ?_ ?_) ?_ ?_)) ?_)) ?_)
      (repC_var (envRep_std₂ ?_ ?_ (Rep.list (Rep.exp R₀ R₁)) R₀) rfl) ?_ ?_) ?hc hdk
  case hc =>
    rintro ⟨fs, x⟩
    refine congrFun (foldr_eq _ _ (fun fs x ↦ fs.map (· x)) rfl ?_ fs) x
    exact fun _ _ ↦ rfl
  side_goals

/-- Conjunction represents the choice of the second bitstring when the first is not empty and of
the empty bitstring otherwise. -/
theorem rep_and (hF : compileDefs (globals defs) = some ds) (hwf : PartialHorn.DefnsWF sig ds)
    {fk : Tree} (hdk : ds[D.and]? = some ⟨[], arr, fk⟩) :
    Represents [] (unfoldTerm sig ds fk) (Rep.prod RBits RBits) RBits
      fun p ↦ p.1.rec [] fun _ _ _ ↦ p.2 := by
  obtain ⟨fn, hfn⟩ := compiled_language hF (k := D.bnil) (d := lib[D.bnil]) rfl
  obtain ⟨fc, hfc⟩ := compiled_language hF (k := D.cond) (d := lib[D.cond]) rfl
  refine rep_def (τ' := []) hF
    (d := mkDefn 0 [bitsTy, bitsTy] bitsTy (condT bitsTy (v 1) (v 0) bnilT)) rfl
    (repC_call₃ (τ' := [List Bit]) (a := bitsTy) rfl rfl hwf hfc rfl ?_ ?_ (.cons ?_ .nil) rfl rfl
      (rep_cond hF hfc RBits) (repC_var (envRep_std₂ ?_ ?_ RBits RBits) rfl)
      (repC_var (envRep_std₂ ?_ ?_ RBits RBits) rfl)
      (repC_call₀ rfl rfl hwf hfn rfl rfl (a := bitsTy) rfl ?_ (rep_bnil hF hfn))) ?hc hdk
  case hc =>
    rintro ⟨_ | ⟨b, w⟩, u⟩ <;> rfl
  side_goals

/-- Whether a list of functions holds of a list of trees elementwise represents
{name}`zipAll`. -/
theorem rep_allZip (hF : compileDefs (globals defs) = some ds) (hwf : PartialHorn.DefnsWF sig ds)
    {fk : Tree} (hdk : ds[D.allZip]? = some ⟨[], arr, fk⟩) :
    Represents [] (unfoldTerm sig ds fk) (Rep.prod (Rep.list (Rep.exp RTree RBits))
      (Rep.list RTree)) RBits fun p ↦ zipAll p.1 p.2 := by
  obtain ⟨fn, hfn⟩ := compiled_language hF (k := D.bnil) (d := lib[D.bnil]) rfl
  obtain ⟨fc, hfc⟩ := compiled_language hF (k := D.cond) (d := lib[D.cond]) rfl
  obtain ⟨fi, hfi⟩ := compiled_language hF (k := D.isNil) (d := lib[D.isNil]) rfl
  obtain ⟨fh, hfh⟩ := compiled_language hF (k := D.headD) (d := lib[D.headD]) rfl
  obtain ⟨ft, hft⟩ := compiled_language hF (k := D.tail) (d := lib[D.tail]) rfl
  obtain ⟨fa, hfa⟩ := compiled_language hF (k := D.and) (d := lib[D.and]) rfl
  let RV := Rep.exp (Rep.list RTree) RBits
  refine rep_def (τ' := []) hF
    (d := mkDefn 0 [list (exp treeTy bitsTy), list treeTy] bitsTy
      (Term.app (Term.listRec
        (Term.lam (list treeTy) (call D.isNil [treeTy] [v 0]))
        (Term.lam (list treeTy) (condT bitsTy (call D.isNil [treeTy] [v 0]) bnilT
          (call D.and [] [Term.app (v 2) (call D.headD [treeTy] [leafT bnilT, v 0]),
            Term.app (v 1) (call D.tail [treeTy] [v 0])])))
        (v 1)) (v 0))) rfl
    (repC_app (repC_listRec
        (repC_var (envRep_std₂ ?_ ?_ (Rep.list (Rep.exp RTree RBits)) (Rep.list RTree)) rfl)
        (repC_lam ?_ ?_ ?_ (repC_call₁ (τ' := [RoseTree (List Bit)]) (a := bitsTy) rfl rfl hwf
          hfi rfl ?_ ?_ (.cons ?_ .nil) rfl rfl (rep_isNil hF hwf hfi RTree) (repC_var0 ?_ ?_)))
        (repC_lam ?_ ?_ ?_ (repC_call₃ (τ' := [List Bit]) (a := bitsTy) rfl rfl hwf hfc rfl ?_ ?_
          (.cons ?_ .nil) rfl rfl (rep_cond hF hfc RBits)
          (repC_call₁ (τ' := [RoseTree (List Bit)]) (a := bitsTy) rfl rfl hwf hfi rfl ?_ ?_
            (.cons ?_ .nil) rfl rfl (rep_isNil hF hwf hfi RTree) (repC_var0 ?_ ?_))
          (repC_call₀ rfl rfl hwf hfn rfl rfl (a := bitsTy) rfl ?_ (rep_bnil hF hfn))
          (repC_call₂ (τ' := []) (a := bitsTy) rfl rfl hwf hfa rfl (by simp) (by simp) .nil rfl rfl
            (rep_and hF hwf hfa)
            (repC_app (repC_varS ?_ ?_ (repC_var (envRep_listStep ?_ ?_ (Rep.exp RTree RBits) RV)
                rfl))
              (repC_call₂ (τ' := [RoseTree (List Bit)]) (a := treeTy) rfl rfl hwf hfh rfl ?_ ?_
                (.cons ?_ .nil) rfl rfl (rep_headD hF hfh RTree)
                (repC_lnode rfl ?_ (repC_pair
                  (repC_call₀ rfl rfl hwf hfn rfl rfl (a := bitsTy) rfl ?_ (rep_bnil hF hfn))
                  (repC_nil rfl ?_ (repC_star ?_ _) ?_ RTree)) ?_)
                (repC_var0 ?_ ?_)) ?_ ?_)
            (repC_app (repC_varS ?_ ?_ (repC_var (envRep_listStep ?_ ?_ (Rep.exp RTree RBits) RV)
                rfl))
              (repC_call₁ (τ' := [RoseTree (List Bit)]) (a := list treeTy) rfl rfl hwf hft rfl ?_ ?_
                (.cons ?_ .nil) rfl rfl (rep_tail hF hft RTree) (repC_var0 ?_ ?_)) ?_ ?_))))
        ?_)
      (repC_var (envRep_std₂ ?_ ?_ (Rep.list (Rep.exp RTree RBits)) (Rep.list RTree)) rfl) ?_ ?_)
    ?hc hdk
  case hc =>
    rintro ⟨ps, ts⟩
    refine congrFun (foldr_eq _ _ zipAll ?_ ?_ ps) ts
    · funext ts
      rcases ts with _ | ⟨t, ts⟩ <;> rfl
    · intro p l
      funext ts
      rcases ts with _ | ⟨t, ts⟩ <;> rfl
  side_goals

/-- The equality of trees represents the test of equality, one or zero. -/
theorem rep_equal (hF : compileDefs (globals defs) = some ds) (hwf : PartialHorn.DefnsWF sig ds)
    {fk : Tree} (hdk : ds[D.equal]? = some ⟨[], arr, fk⟩) :
    Represents [] (unfoldTerm sig ds fk) (Rep.prod RTree RTree) RBits
      fun p ↦ ofNum (if p.1 = p.2 then 1 else 0) := by
  obtain ⟨fa, hfa⟩ := compiled_language hF (k := D.and) (d := lib[D.and]) rfl
  obtain ⟨fe, hfe⟩ := compiled_language hF (k := D.eqB) (d := lib[D.eqB]) rfl
  obtain ⟨fl, hfl⟩ := compiled_language hF (k := D.lab) (d := lib[D.lab]) rfl
  obtain ⟨fz, hfz⟩ := compiled_language hF (k := D.allZip) (d := lib[D.allZip]) rfl
  obtain ⟨fc, hfc⟩ := compiled_language hF (k := D.children) (d := lib[D.children]) rfl
  let RP := Rep.prod RBits (Rep.list (Rep.exp RTree RBits))
  refine rep_def (τ' := []) hF
    (d := mkDefn 0 [treeTy, treeTy] bitsTy
      (Term.app (Term.roseRec (exp treeTy bitsTy)
        (Term.lam treeTy (call D.and []
          [call D.eqB [] [Term.fst (v 1), call D.lab [] [v 0]],
            call D.allZip [] [Term.snd (v 1), call D.children [] [v 0]]])) (v 1)) (v 0))) rfl
    (repC_app (repC_roseRec ?_ (repC_var (envRep_std₂ ?_ ?_ RTree RTree) rfl)
        (repC_lam ?_ ?_ ?_ (repC_call₂ (τ' := []) (a := bitsTy) rfl rfl hwf hfa rfl (by simp)
          (by simp) .nil rfl rfl (rep_and hF hwf hfa)
          (repC_call₂ (τ' := []) (a := bitsTy) rfl rfl hwf hfe rfl (by simp) (by simp) .nil rfl rfl
            (rep_eqB hF hwf hfe)
            (repC_fst (repC_varS ?_ ?_ (repC_var (envRep_idt ?_ RP) rfl)) ?_ ?_)
            (repC_call₁ (τ' := []) (a := bitsTy) rfl rfl hwf hfl rfl (by simp) (by simp) .nil rfl
              rfl (rep_lab hF hfl) (repC_var0 ?_ ?_)))
          (repC_call₂ (τ' := []) (a := bitsTy) rfl rfl hwf hfz rfl (by simp) (by simp) .nil rfl rfl
            (rep_allZip hF hwf hfz)
            (repC_snd (repC_varS ?_ ?_ (repC_var (envRep_idt ?_ RP) rfl)) ?_ ?_)
            (repC_call₁ (τ' := []) (a := list treeTy) rfl rfl hwf hfc rfl (by simp) (by simp) .nil
              rfl rfl (rep_children hF hwf hfc) (repC_var0 ?_ ?_))))) ?_)
      (repC_var (envRep_std₂ ?_ ?_ RTree RTree) rfl) ?_ ?_) ?hc hdk
  case hc =>
    rintro ⟨t, u⟩
    revert u
    refine RoseTree.ind (P := fun t ↦ ∀ u, _ = ofNum (if t = u then 1 else 0))
      (fun l cs ih u ↦ ?_) t
    rw [RoseTree.elim_node]
    simp only [id, Function.comp_apply] at ih ⊢
    rw [zipAll_map _ cs ih u.children]
    by_cases h₁ : l = u.label
    · by_cases h₂ : cs = u.children
      · simp [h₁, h₂]
      · have e : ¬RoseTree.node l cs = u := fun h ↦ h₂ (RoseTree.node_eq_iff.mp h).2
        simp only [e, h₂, ↓reduceIte]
        simp [h₁]
    · have e : ¬RoseTree.node l cs = u := fun h ↦ h₁ (RoseTree.node_eq_iff.mp h).1
      have e' : ¬rankB l = rankB u.label := fun h ↦ h₁ (rankB_inj.mp h)
      simp [e, e']
  side_goals

end Geb.FreeTopos.Translation

end
