/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Agreement.Language
public import GebTests.Prototypes.GoedelT.MirrorEquations
public import Geb.Prototypes.FreeTopos.Translation

set_option doc.verso true in
/-!
# The translation written in Geb

The functions of {lit}`bootstrap/free-topos/translation.geb`, in the Lean the bootstrap compiler
emits ({lit}`GebMirror.Metalogic`), agree with the Lean translation of the kernel into the
internal language ({name}`Geb.FreeTopos.Translation.term`) at every input: the types, the library,
the numerals and quoted trees, the kernel's constants and primitives, and the translation of
terms, programs, constants and theorems of Gödel's T.

## Main definitions

* {lit}`encTr` — a kernel type with a term of the language.
* {lit}`TRel` — the relation of the mirror's translation of a term to the translation's.

## Main statements

* {lit}`trTy_eq`, {lit}`lib_eq`, {lit}`trNumeral_eq`, {lit}`quoteT_eq`, {lit}`primT_eq` — the
  types, the library, numerals, quoted trees and primitives.
* {lit}`term_eq` — the translation of a term, in every context.
* {lit}`program_eq`, {lit}`trGlobals_eq`, {lit}`thm_eq` — programs, their constants and
  theorems of Gödel's T.

## Tags

translation, internal language, System T, agreement, mirror
-/

set_option doc.verso true

@[expose] public section

open GebMirror.Metalogic

namespace GebTests.Prototypes.FreeTopos.Agreement.Translation

open Geb Geb.Kernel Geb.FreeTopos GebTests.Prototypes.FreeTopos.Agreement.Encode
  GebTests.Prototypes.FreeTopos.Agreement.Fold GebTests.Prototypes.FreeTopos.Agreement.Base
  GebTests.Prototypes.FreeTopos.Agreement.Language
open Internal (Term)
open scoped FinEnum

/-- A kernel type with a term of the language, as the node of the type and the term. -/
def encTr (p : Tree × Term) : Tree := encPair (p.1, encTerm p.2)

/-- A translated program as the node of its globals' kernel types and its definitions. -/
def encProgram (p : List Tree × List Internal.Defn) : Tree :=
  encPair (RoseTree.node 0 p.1, RoseTree.node 0 (p.2.map encLDefn))

/-- The mirror's translation of a kernel type. -/
theorem trTy_eq (t : Tree) : «Translation.trTy» t = encOpt (Translation.ty t) := by
  unfold «Translation.trTy» Translation.ty
  refine fold_rel (fun v w ↦ v = encOpt w) _ _ (fun l xs hx ↦ ?_) t
  have e : xs.map Prod.fst = (xs.map Prod.snd).map encOpt := by
    rw [List.map_map]
    exact List.map_congr_left hx
  simp only [e]
  generalize xs.map Prod.snd = ws
  rcases ws with _ | ⟨x, _ | ⟨y, _ | ⟨z, r⟩⟩⟩ <;> rcases l with _ | _ | _ | _ | _ | n <;>
    mirror_simp [none_eq, some_eq, beq_iff_eq, Nat.reduceEqDiff, Nat.add_one_ne_zero,
      Option.bind_eq_bind, Option.pure_def]
  all_goals first
    | rfl
    | rcases x with _ | x <;> first | rfl | rcases y with _ | y <;> rfl

/-- The mirror's primitive arrows of a translated program. -/
theorem trPrims_eq : «Translation.trPrims» = Translation.prims.map encPrim := by rfl

set_option maxRecDepth 100000 in
/-- The mirror's library of definitions. -/
theorem lib_eq : «Translation.lib» = Translation.lib.map encLDefn := by rfl

/-- The mirror's empty list. -/
@[simp] theorem nilT_eq (a : Tree) : «Translation.nilT» a = encTerm (Translation.nilT a) :=
  rfl

/-- The mirror's construction of a list. -/
@[simp] theorem consT_eq (a : Tree) (h t : Term) :
    «Translation.consT» a (encTerm h) (encTerm t) = encTerm (Translation.consT a h t) :=
  rfl

/-- The mirror's conditional on a bitstring. -/
@[simp] theorem condT_eq (a : Tree) (c t u : Term) :
    «Translation.condT» a (encTerm c) (encTerm t) (encTerm u) =
      encTerm (Translation.condT a c t u) :=
  rfl

/-- The mirror's label of a tree. -/
@[simp] theorem labT_eq (t : Term) :
    «Translation.labT» (encTerm t) = encTerm (Translation.call Translation.D.lab [] [t]) :=
  rfl

/-- The mirror's application of a definition to no arguments. -/
@[simp] theorem call_nil_eq (k : ℕ) :
    «Translation.call» (leaf k) [] [] = encTerm (Translation.call k [] []) :=
  rfl

/-- The mirror's fold of trees. -/
@[simp] theorem foldT_eq (a : Tree) : «Translation.foldT» a = encTerm (Translation.foldT a) :=
  rfl

set_option maxRecDepth 10000 in
/-- The mirror's fold of trees whose step sees the node. -/
@[simp] theorem paraT_eq (a : Tree) : «Translation.paraT» a = encTerm (Translation.paraT a) :=
  rfl

/-- The mirror's iteration. -/
@[simp] theorem iterT_eq (a : Tree) : «Translation.iterT» a = encTerm (Translation.iterT a) :=
  rfl

/-- The mirror's right fold of lists. -/
@[simp] theorem foldrT_eq (a b : Tree) :
    «Translation.foldrT» a b = encTerm (Translation.foldrT a b) :=
  rfl

/-- The mirror's case analysis of lists. -/
@[simp] theorem lcaseT_eq (a b : Tree) :
    «Translation.lcaseT» a b = encTerm (Translation.lcaseT a b) :=
  rfl

/-- The mirror's primitive of an index. -/
theorem primT_eq (k : ℕ) :
    «Translation.primT» (leaf k) = encOpt ((Translation.primT k).map encTerm) := by
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 => rfl
  | n + 14 =>
    mirror_simp [«Translation.primT», Translation.primT, none_eq, beq_iff_eq,
      Nat.reduceEqDiff]

/-- The iteration of the mirror's low digits in base two: after {lit}`k` steps, the quotient by
{lit}`2 ^ k` and the low {lit}`k` digits, the most significant first. -/
theorem digits_repeat (m : ℕ) : ∀ k : ℕ,
    Nat.repeat (fun s : Tree × List Tree ↦ (Const.div s.1 (leaf 2), Const.mod s.1 (leaf 2) :: s.2))
        k (leaf m, []) =
      (leaf (m / 2 ^ k), ((List.range k).map fun i ↦ leaf (m / 2 ^ i % 2)).reverse) :=
  Nat.rec (by simp [Nat.repeat]) fun k ih ↦ by
    rw [Nat.repeat, ih]
    simp only [Const.div, Const.mod, label_leaf, List.range_succ, List.map_append,
      List.reverse_append, List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append, Nat.div_div_eq_div_mul, Nat.pow_succ]

/-- The mirror's low digits of a number in base two, the least significant first. -/
theorem digitsLsb_two (m k : ℕ) :
    «Prelude.digitsLsb» (leaf 2) (leaf m) (leaf k) =
      (List.range k).map fun i ↦ leaf (m / 2 ^ i % 2) := by
  simp only [«Prelude.digitsLsb», «Prelude.digitsMsb», Const.iter,
    label_leaf, digits_repeat, reverse_eq, List.reverse_reverse]

/-- A nonzero number's binary digits: the least significant, and those of half the number. -/
theorem bits_eq_cons (m : ℕ) (hm : m / 2 ≠ 0) : m.bits = decide (m % 2 = 1) :: (m / 2).bits := by
  rcases Nat.mod_two_eq_zero_or_one m with h | h
  · have e := Nat.bit0_bits (m / 2) hm
    rw [show 2 * (m / 2) = m by omega] at e
    rw [e, h]
    rfl
  · have e := Nat.bit1_bits (m / 2)
    rw [show 2 * (m / 2) + 1 = m by omega] at e
    rw [e, h]
    rfl

/-- The low digits of a nonzero number in base two below its most significant, the least
significant first, as truth values: its binary digits without the most significant. -/
theorem range_bits : ∀ k m : ℕ, m.log2 = k → m ≠ 0 →
    (List.range k).map (fun i ↦ decide (m / 2 ^ i % 2 = 1)) = m.bits.dropLast :=
  Nat.rec (fun m hk hm ↦ by
      rw [Nat.log2_def] at hk
      split_ifs at hk with h
      obtain rfl : m = 1 := by omega
      rfl)
    fun k ih m hk hm ↦ by
      rw [Nat.log2_def] at hk
      split_ifs at hk with h
      have hm2 : m / 2 ≠ 0 := by omega
      have hl : (List.range k).map (fun i ↦ decide (m / 2 ^ (i + 1) % 2 = 1)) =
          (List.range k).map (fun i ↦ decide (m / 2 / 2 ^ i % 2 = 1)) :=
        List.map_congr_left fun i _ ↦ by
          rw [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
      have hn : (m / 2).bits ≠ [] := by
        by_cases h1 : m / 2 / 2 = 0
        · rw [show m / 2 = 1 by omega, Nat.one_bits]
          exact List.cons_ne_nil _ _
        · rw [bits_eq_cons (m / 2) h1]
          exact List.cons_ne_nil _ _
      rw [List.range_succ_eq_map, List.map_cons, List.map_map, Function.comp_def, hl,
        ih (m / 2) (by omega) hm2, bits_eq_cons m hm2, List.dropLast_cons_of_ne_nil hn,
        Nat.pow_zero, Nat.div_one]

/-- The mirror's bitstring of the digits of leaves, each the bit one where the leaf is not zero,
the least significant first. -/
theorem foldr_bits_eq (bs : List Bool) :
    List.foldr
        (fun d w ↦ if d.label ≠ 0 then «Translation.b1T» w else «Translation.b0T» w)
        «Translation.bnilT» (bs.map fun b ↦ leaf (if b then 1 else 0)) =
      encTerm (bs.foldr (fun b w ↦ if b then Translation.b1T w else Translation.b0T w)
        Translation.bnilT) :=
  bs.rec rfl fun b bs ih ↦ by
    rw [List.map_cons, List.foldr_cons, List.foldr_cons, ih]
    cases b <;> rfl

/-- The mirror's numeral of a label. -/
@[simp] theorem trNumeral_eq (n : ℕ) :
    «Translation.trNumeral» (leaf n) = encTerm (Translation.numeral n) := by
  have hd : «Prelude.digitsLsb» (leaf 2) (leaf (n + 1)) (leaf (n + 1).log2) =
      (Oitavem.unrank n).map fun b ↦ leaf (if b then 1 else 0) := by
    rw [digitsLsb_two, Oitavem.unrank, ← range_bits _ (n + 1) rfl (Nat.succ_ne_zero n),
      List.map_map]
    refine List.map_congr_left fun i _ ↦ ?_
    rcases Nat.mod_two_eq_zero_or_one ((n + 1) / 2 ^ i) with h | h <;> simp [h]
  simp only [«Translation.trNumeral», add_leaf, Const.log2, label_leaf, foldr_eq, hd]
  exact foldr_bits_eq _

/-- The mirror's translation of a quoted tree. -/
@[simp] theorem quoteT_eq (t : Tree) :
    «Translation.quoteT» t = encTerm (Translation.quoteT t) := by
  unfold «Translation.quoteT» Translation.quoteT
  refine fold_rel (fun v w ↦ v = encTerm w) _ _ (fun l xs hx ↦ ?_) t
  have e : xs.map Prod.fst = (xs.map Prod.snd).map encTerm := by
    rw [List.map_map]
    exact List.map_congr_left hx
  have hf : ∀ cs : List Term, List.foldr («Translation.consT» «Translation.treeTy»)
      («Translation.nilT» «Translation.treeTy») (cs.map encTerm) =
        encTerm (cs.foldr (Translation.consT Translation.treeTy)
          (Translation.nilT Translation.treeTy)) :=
    fun cs ↦ cs.rec rfl fun c cs ih ↦ by rw [List.map_cons, List.foldr_cons, ih]; rfl
  simp only [e, foldr_eq, hf, trNumeral_eq]
  rfl

/-! The kernel checker's functions, which the program shares with the checker of Gödel's T. -/

/-- The mirror's test of a kernel type. -/
theorem kIsTy_eq (t : Tree) : «Check.isTy» t = ofBool (Ty.IsTy t) :=
  (rfl : «Check.isTy» t = GebMirror.GoedelT.«Check.isTy» t).trans
    (GoedelT.MirrorTyping.isTy_eq t)

/-- The mirror's kernel function type. -/
@[simp] theorem kTyArrow_eq (A B : Tree) : «Check.tyArrow» A B = tArrow A B :=
  GoedelT.MirrorTyping.tyArrow_eq A B

/-- The mirror's kernel list type. -/
@[simp] theorem kTyList_eq (A : Tree) : «Check.tyList» A = tList A :=
  GoedelT.MirrorTyping.tyList_eq A

/-- The mirror's type of the fold of trees. -/
@[simp] theorem kFoldTy_eq (A : Tree) : «Check.foldTy» A = foldTy A :=
  GoedelT.MirrorTyping.foldTy_eq A

/-- The mirror's type of iteration. -/
@[simp] theorem kIterTy_eq (A : Tree) : «Check.iterTy» A = iterTy A :=
  GoedelT.MirrorTyping.iterTy_eq A

/-- The mirror's type of the right fold of lists. -/
@[simp] theorem kFoldrTy_eq (A B : Tree) : «Check.foldrTy» A B = foldrTy A B :=
  GoedelT.MirrorTyping.foldrTy_eq A B

/-- The mirror's type of case analysis of lists. -/
@[simp] theorem kLcaseTy_eq (A B : Tree) : «Check.lcaseTy» A B = lcaseTy A B :=
  GoedelT.MirrorTyping.lcaseTy_eq A B

/-- The mirror's types of the kernel's primitives. -/
@[simp] theorem kPrimTypes_eq : «Check.primTypes» = Kernel.prims.map (·.1) :=
  GoedelT.MirrorTyping.primTypes_eq

/-- The mirror's kernel product type. -/
@[simp] theorem kProd_eq (A B : Tree) : «Reader.node2» (leaf 2) A B = tProd A B := by
  rw [tProd, GoedelT.MirrorTyping.node2_eq]
  rfl

/-- The mirror's domain and codomain of a kernel function type. -/
theorem kArrowParts_eq (t : Tree) :
    «Translation.kArrowParts» t = encOpt ((Translation.arrowParts t).map encPair) := by
  obtain ⟨l, cs, rfl⟩ : ∃ l cs, t = RoseTree.node l cs :=
    ⟨t.label, t.children, (RoseTree.node_label_children t).symm⟩
  rcases cs with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩ <;>
    mirror_simp [«Translation.kArrowParts», Translation.arrowParts, none_eq, some_eq,
      beq_iff_eq, Nat.add_one_ne_zero, Nat.reduceEqDiff]
  all_goals split_ifs <;> first | rfl | simp_all

/-- The mirror's factors of a kernel product type. -/
theorem kProdParts_eq (t : Tree) :
    «Translation.kProdParts» t = encOpt ((Translation.prodParts t).map encPair) := by
  obtain ⟨l, cs, rfl⟩ : ∃ l cs, t = RoseTree.node l cs :=
    ⟨t.label, t.children, (RoseTree.node_label_children t).symm⟩
  rcases cs with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩ <;>
    mirror_simp [«Translation.kProdParts», Translation.prodParts, none_eq, some_eq,
      beq_iff_eq, Nat.add_one_ne_zero, Nat.reduceEqDiff]
  all_goals split_ifs <;> first | rfl | simp_all

/-- The mirror's element type of a kernel list type. -/
theorem kListPart_eq (t : Tree) :
    «Translation.kListPart» t = encOpt (Translation.listPart t) := by
  obtain ⟨l, cs, rfl⟩ : ∃ l cs, t = RoseTree.node l cs :=
    ⟨t.label, t.children, (RoseTree.node_label_children t).symm⟩
  rcases cs with _ | ⟨a, _ | ⟨b, cs⟩⟩ <;>
    mirror_simp [«Translation.kListPart», Translation.listPart, none_eq, some_eq,
      beq_iff_eq, Nat.add_one_ne_zero, Nat.reduceEqDiff]
  all_goals split_ifs <;> first | rfl | simp_all

/-! The translation of terms. -/

/-- The mirror's translation of a term and the translation's are related when they agree at every
list of the globals' types and every context. -/
def TRel (v : List Tree → List Tree → Tree) (w : Translation.Tr) : Prop :=
  ∀ gt Γ, v gt Γ = encOpt ((w gt Γ).map encTr)

/-- A list of translations without its head. -/
@[simp] theorem trTail_eq (rs : List (List Tree → List Tree → Tree)) :
    «Translation.trTail» rs = rs.tail := by
  cases rs <;> rfl

/-- The translation of a child at a position, nothing out of range. -/
@[simp] theorem trAt_eq (rs : List (List Tree → List Tree → Tree)) (i : ℕ) :
    «Translation.trAt» rs (leaf i) = rs[i]?.getD fun _ _ ↦ «Prelude.none» := by
  have hr : ∀ i : ℕ, Nat.repeat «Translation.trTail» i rs = rs.drop i :=
    Nat.rec rfl fun i ih ↦ by rw [Nat.repeat, ih, trTail_eq, List.tail_drop]
  simp only [«Translation.trAt», iter_leaf, hr]
  cases h : rs.drop i with
  | nil =>
    rw [List.drop_eq_nil_iff] at h
    rw [List.getElem?_eq_none h]
    rfl
  | cons r rest =>
    rw [← List.head?_drop, h]
    rfl

/-- The simplification of a case of the mirror's step of the translation of terms: the lemmas of
{lit}`mirror_simp`, the step's lists, pairs and term builders, and the given lemmas. -/
local macro "tr_simp" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  mirror_simp [«Translation.termStep», Translation.termStep, trAt_eq, none_eq, some_eq,
    pr_eq, p1_eq, p2_eq, encTr, beq_iff_eq, Nat.add_one_ne_zero, Nat.reduceEqDiff,
    Option.map_bind, Option.bind_eq_bind, Option.pure_def, Option.map_map, Option.bind_map,
    Option.elim_map, Option.map_some, Option.map_none, Option.bind_some, Option.bind_none,
    Function.comp_def, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    mVar_eq, mLam_eq, mApp_eq, mPair_eq, mFst_eq, mSnd_eq, mStar_eq, kIsTy_eq, trTy_eq,
    kArrowParts_eq, kProdParts_eq, kListPart_eq, List.mem_cons, true_or, or_true,
    kTyArrow_eq, kTyList_eq, kFoldTy_eq, kIterTy_eq, kFoldrTy_eq, kLcaseTy_eq, kPrimTypes_eq,
    quoteT_eq, nilT_eq, consT_eq, condT_eq, labT_eq, call_nil_eq, foldT_eq, paraT_eq, iterT_eq,
    foldrT_eq, lcaseT_eq, primT_eq, kProd_eq, decide_true, decide_false, Bool.false_eq_true,
    ↓reduceIte, $ls,*])

set_option maxHeartbeats 4000000 in
-- each label's case evaluates the chain of the step's tests of label and arity
/-- The mirror's step of the translation of terms at a node is the translation's step at the
node, at related translations of the children. -/
theorem termStep_eq (l : ℕ) (xs : List (Tree × (List Tree → List Tree → Tree) × Translation.Tr))
    (hx : ∀ x ∈ xs, TRel x.2.1 x.2.2) :
    TRel («Translation.termStep» (RoseTree.node l (xs.map Prod.fst)) (xs.map fun x ↦ x.2.1))
      (Translation.termStep l (xs.map fun x ↦ (x.1, x.2.2))) := by
  intro gt Γ
  have h0 : ∀ x ∈ xs, ∀ gt Γ, x.2.1 gt Γ = encOpt ((x.2.2 gt Γ).map encTr) := hx
  match l with
  | 8 =>
    rcases xs with _ | ⟨x0, _ | ⟨x1, r⟩⟩ <;> tr_simp []
    rcases Γ[x0.1.label]? with _ | A <;> rfl
  | 9 =>
    rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, r⟩⟩⟩ <;> tr_simp [h0]
    by_cases hA : Ty.IsTy x0.1 = true <;> tr_simp [hA]
    rcases x1.2.2 gt (x0.1 :: Γ) with _ | ⟨B, t⟩ <;> tr_simp []
    rcases Translation.ty x0.1 with _ | a <;> tr_simp []
  | 10 =>
    rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, r⟩⟩⟩ <;> tr_simp [h0]
    rcases x0.2.2 gt Γ with _ | ⟨F, f⟩ <;> tr_simp []
    rcases x1.2.2 gt Γ with _ | ⟨X, x⟩ <;> tr_simp []
    rcases Translation.arrowParts F with _ | ⟨A, B⟩ <;> tr_simp []
    by_cases h : X = A <;> tr_simp [h]
  | 11 =>
    rcases xs with _ | ⟨x0, r⟩ <;> tr_simp []
    rfl
  | 12 =>
    rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, r⟩⟩⟩ <;> tr_simp [h0]
    rcases x0.2.2 gt Γ with _ | ⟨A, a⟩ <;> tr_simp []
    rcases x1.2.2 gt Γ with _ | ⟨B, b⟩ <;> tr_simp []
  | 13 | 14 =>
    rcases xs with _ | ⟨x0, _ | ⟨x1, r⟩⟩ <;> tr_simp [h0]
    rcases x0.2.2 gt Γ with _ | ⟨P, p⟩ <;> tr_simp []
    rcases Translation.prodParts P with _ | ⟨A, B⟩ <;> tr_simp []
  | 15 =>
    rcases xs with _ | ⟨x0, _ | ⟨x1, r⟩⟩ <;> tr_simp []
    rfl
  | 16 =>
    rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, r⟩⟩⟩⟩ <;> tr_simp [h0]
    rcases x0.2.2 gt Γ with _ | ⟨C, c⟩ <;> tr_simp []
    rcases x1.2.2 gt Γ with _ | ⟨A, a⟩ <;> tr_simp []
    rcases x2.2.2 gt Γ with _ | ⟨B, b⟩ <;> tr_simp []
    by_cases hC : C = leaf 0 <;> by_cases hB : B = A <;>
      tr_simp [hC, hB, tT, and_self, and_false, false_and, ite_self]
    rcases Translation.ty A with _ | a' <;> tr_simp []
  | 17 | 18 | 19 | 25 =>
    rcases xs with _ | ⟨x0, _ | ⟨x1, r⟩⟩ <;> tr_simp []
    rcases Translation.ty x0.1 with _ | a <;> tr_simp []
  | 20 =>
    rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, r⟩⟩⟩ <;> tr_simp [h0]
    rcases x0.2.2 gt Γ with _ | ⟨X, x⟩ <;> tr_simp []
    rcases x1.2.2 gt Γ with _ | ⟨L, t⟩ <;> tr_simp []
    rcases Translation.listPart L with _ | A <;> tr_simp []
    by_cases h : X = A <;> tr_simp [h]
    rcases Translation.ty A with _ | a <;> tr_simp []
  | 21 | 24 =>
    rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, r⟩⟩⟩ <;> tr_simp []
    rcases Translation.ty x0.1 with _ | a <;> tr_simp []
    rcases Translation.ty x1.1 with _ | b <;> tr_simp []
  | 22 =>
    rcases xs with _ | ⟨x0, _ | ⟨x1, r⟩⟩ <;> tr_simp [List.getElem?_map]
    rcases Kernel.prims[x0.1.label]? with _ | P <;> tr_simp []
    rcases Translation.primT x0.1.label with _ | t <;> tr_simp []
  | 23 =>
    rcases xs with _ | ⟨x0, _ | ⟨x1, r⟩⟩ <;> tr_simp [lib_eq, List.length_map]
    rcases gt[x0.1.label]? with _ | A <;> tr_simp []
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | _ + 26 =>
    rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, r⟩⟩⟩⟩ <;> tr_simp []

/-- The mirror's translation of a term in a context, with the types of the globals. -/
theorem term_eq (gt Γ : List Tree) (t : Tree) :
    «Translation.term» gt Γ t = encOpt ((Translation.term gt Γ t).map encTr) :=
  para_rel TRel «Translation.termStep» Translation.termStep
    (fun l xs hx ↦ termStep_eq l xs hx) t gt Γ

/-! Programs, their constants, and theorems of Gödel's T. -/

/-- The mirror's definition in object parameters from parameters of types. -/
@[simp] theorem mkDefn_eq (n : ℕ) (ps : List Tree) (ty : Tree) (b : Term) :
    «Translation.mkDefn» (leaf n) ps ty (encTerm b) =
      encLDefn (Translation.mkDefn n ps ty b) := by
  simp [«Translation.mkDefn», «Language.ldefn», Translation.mkDefn, encLDefn]

/-- The mirror's translation of a program's definitions. -/
theorem program_eq (ds : List Tree) :
    «Translation.program» ds = encOpt ((Translation.program ds).map encProgram) := by
  simp only [«Translation.program», foldr_eq, reverse_eq, List.foldr_reverse,
    Translation.program]
  refine List.foldl_hom
    (fun o : Option (List Tree × List Internal.Defn) ↦ encOpt (o.map encProgram))
    (init := some ([], [])) fun acc t ↦ ?_
  rcases acc with _ | ⟨gt, defs⟩
  · rfl
  tr_simp [encProgram, term_eq, mkDefn_eq]
  rcases Translation.term gt [] t with _ | ⟨A, u⟩ <;> tr_simp []
  rcases Translation.ty A with _ | a <;> tr_simp [mkDefn_eq, List.map_append]

/-- The mirror's definition of the language as a definition of either kind. -/
@[simp] theorem defLang_eq (d : Internal.Defn) :
    «Language.defLang» (encLDefn d) = encDefinition (.language d) :=
  rfl

/-- The mirror's constants of a translated program. -/
theorem trGlobals_eq (defs : List Internal.Defn) :
    «Translation.trGlobals» (defs.map encLDefn) = encGlobals (Translation.globals defs) := by
  simp only [«Translation.trGlobals», trPrims_eq, lib_eq, append_eq, mapT_eq,
    ← List.map_append, List.map_map, Function.comp_def, defLang_eq, length_eq,
    Theory.sig_eq, List.length_map, Translation.globals]
  rw [← globals_eq, List.map_map]
  rfl

/-- The mirror's translation of a theorem of Gödel's T, with the types of the globals. -/
theorem thm_eq (gt : List Tree) (a : GoedelT.Thm) :
    «Translation.thm» gt (GoedelT.MirrorEquations.encThm a) =
      encOpt ((Translation.thm gt a).map encThm) := by
  have hc : a.ctx.map «Translation.trTy» = a.ctx.map fun t ↦ encOpt (Translation.ty t) :=
    List.map_congr_left fun t _ ↦ trTy_eq t
  tr_simp [«Translation.thm», GoedelT.MirrorEquations.encThm,
    GoedelT.MirrorEquations.encEqn, List.getD_cons_zero, List.getD_cons_succ, hc, allSomeT_eq,
    term_eq, Translation.thm]
  rcases a.ctx.mapM Translation.ty with _ | Γ <;> tr_simp []
  rcases Translation.term gt a.ctx a.eqn.lhs with _ | ⟨A, l⟩ <;> tr_simp []
  rcases Translation.term gt a.ctx a.eqn.rhs with _ | ⟨B, r⟩ <;> tr_simp [mEq_eq]
  rfl

end GebTests.Prototypes.FreeTopos.Agreement.Translation

end
