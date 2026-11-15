/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Agreement.Derivation
public import GebTests.Prototypes.FreeTopos.Agreement.Translation
public import Geb.Prototypes.FreeTopos.Literals

set_option doc.verso true in
/-!
# The evaluation at literals written in Geb

The functions of {lit}`bootstrap/free-topos/literals.geb`, in the Lean the bootstrap compiler
emits ({lit}`GebMirror.Metalogic`), agree with the evaluation of the library's arithmetic at
numerals ({name}`Geb.FreeTopos.Literals.eval`) at every encoded input: the definition a term's
root applies, the value of a definition at literals, the value of a term, the term of a value, the
definitions' equations at the numerals' bits and the test of readiness.

A literal is encoded by the numbers its bitstrings denote, their indices in the enumeration of
bitstrings ({name}`Geb.FreeTopos.Literals.val`), which the kernel's labels are, so that the mirror
computes the definitions by the kernel's arithmetic where the evaluation computes them by the
arithmetic of the natural numbers at those indices.

## Main definitions

* {lit}`encVal` — the encoding of a literal.
* {lit}`symPos` — the position of a definition evaluated among them.

## Main statements

* {lit}`host_eq` — the mirror's value of a definition at literals.
* {lit}`valueOf_eq`, {lit}`litEval_eq` — the mirror's value of a term, and the term of that value.
* {lit}`lemmas_eq` — the mirror's equations at the numerals' bits.
* {lit}`ready_eq` — the mirror's test of the conditions under which the evaluation is a rewriting.

## Tags

internal language, arithmetic, numeral, literal, agreement, mirror
-/

set_option doc.verso true

@[expose] public section

open GebMirror.Metalogic

namespace GebTests.Prototypes.FreeTopos.Agreement.Literals

open Geb Geb.Kernel Geb.FreeTopos GebTests.Prototypes.FreeTopos.Agreement.Encode
  GebTests.Prototypes.FreeTopos.Agreement.Fold GebTests.Prototypes.FreeTopos.Agreement.Base
  GebTests.Prototypes.FreeTopos.Agreement.Language
  GebTests.Prototypes.FreeTopos.Agreement.Derivation
  GebTests.Prototypes.FreeTopos.Agreement.Translation
open Internal (Term)
open Geb.FreeTopos.Literals (Val Sym val num truth)
open scoped FinEnum

/-- The position of a comparison's result: less, equal, greater. -/
def ordPos : Ordering → ℕ
  | .lt => 0
  | .eq => 1
  | .gt => 2

/-- A literal as the node of its kind's position over the numbers its bitstrings denote, or its
comparison's result. -/
def encVal : Val → Tree
  | .bits w => RoseTree.node 0 [leaf (val w)]
  | .ord o => RoseTree.node 1 [leaf (ordPos o)]
  | .pair a b => RoseTree.node 2 [leaf (val a), leaf (val b)]

/-- The position of a definition evaluated among the definitions evaluated. -/
def symPos : Sym → ℕ
  | .bnil => 0
  | .b0 => 1
  | .b1 => 2
  | .isNil => 3
  | .succ => 4
  | .dbl => 5
  | .pred => 6
  | .condB => 7
  | .condO => 8
  | .add => 9
  | .mul => 10
  | .eqB => 11
  | .cmp => 12
  | .ltB => 13
  | .subE => 14
  | .sub => 15
  | .divMod => 16
  | .log2 => 17

/-- A bitstring denotes zero exactly when it is empty. -/
theorem val_eq_zero (w : List Bool) : val w = 0 ↔ w = [] := by
  cases w with
  | nil => exact ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩
  | cons b w => simp [Geb.FreeTopos.Literals.val_cons]

/-- The number of a bitstring that is empty or not. -/
theorem isEmpty_eq_decide (w : List Bool) : w.isEmpty = decide (val w = 0) := by
  cases w with
  | nil => rfl
  | cons b w => simp [Geb.FreeTopos.Literals.val_cons]

/-- The number a test's truth value denotes. -/
theorem val_truth (b : Bool) : val (truth b) = if b then 1 else 0 := by
  cases b <;> rfl

/-- The mirror's number of a list of one bitstring. -/
theorem bits1_eq (vs : List Val) :
    «Literals.bits1» (vs.map encVal) = encOpt (match vs with
      | [.bits w] => some (leaf (val w))
      | _ => none) := by
  rcases vs with _ | ⟨v, _ | ⟨v', vs⟩⟩
  · rfl
  · cases v <;> rfl
  · cases v <;> rfl

/-- The mirror's numbers of a list of two bitstrings. -/
theorem bits2_eq (vs : List Val) :
    «Literals.bits2» (vs.map encVal) = encOpt (match vs with
      | [.bits a, .bits b] => some (encPair (leaf (val a), leaf (val b)))
      | _ => none) := by
  rcases vs with _ | ⟨v, _ | ⟨v', _ | ⟨v'', vs⟩⟩⟩
  · rfl
  · cases v <;> rfl
  · cases v <;> cases v' <;> rfl
  · cases v <;> cases v' <;> rfl

/-- The mirror's conditional on a number at numbers of bitstrings. -/
theorem hostCond_bits (k a b : ℕ) :
    «Literals.hostCond» (leaf 7)
        [RoseTree.node 0 [leaf k], RoseTree.node 0 [leaf a], RoseTree.node 0 [leaf b]] =
      encOpt (some (RoseTree.node 0 [leaf (if k = 0 then b else a)])) := by
  cases k <;> rfl

/-- The mirror's conditional on a number at comparisons' results. -/
theorem hostCond_ord (k a b : ℕ) :
    «Literals.hostCond» (leaf 8)
        [RoseTree.node 0 [leaf k], RoseTree.node 1 [leaf a], RoseTree.node 1 [leaf b]] =
      encOpt (some (RoseTree.node 1 [leaf (if k = 0 then b else a)])) := by
  cases k <;> rfl

/-- The mirror's conditional on a bitstring at bitstrings and at comparisons. -/
theorem hostCond_eq (s : Sym) (hs : s = .condB ∨ s = .condO) (vs : List Val) :
    «Literals.hostCond» (leaf (symPos s)) (vs.map encVal) = encOpt ((s.host vs).map encVal) := by
  rcases vs with _ | ⟨c, _ | ⟨t, _ | ⟨u, _ | ⟨x, vs⟩⟩⟩⟩
  · rcases hs with rfl | rfl <;> rfl
  · rcases hs with rfl | rfl <;> cases c <;> rfl
  · rcases hs with rfl | rfl <;> cases c <;> cases t <;> rfl
  · rcases hs with rfl | rfl <;> cases c <;> cases t <;> cases u <;>
      first
        | rfl
        | (rename_i c t u
           refine (hostCond_bits (val c) (val t) (val u)).trans ?_
           simp only [Sym.host, Option.map_some, encVal, isEmpty_eq_decide, decide_eq_true_eq]
           split <;> rfl)
        | (rename_i c t u
           refine (hostCond_ord (val c) (ordPos t) (ordPos u)).trans ?_
           simp only [Sym.host, Option.map_some, encVal, isEmpty_eq_decide, decide_eq_true_eq]
           split <;> rfl)
  · rcases hs with rfl | rfl <;> cases c <;> cases t <;> cases u <;> rfl

/-- The value of a definition of one bitstring at a number, by the arithmetic of the natural
numbers. -/
def hostN₁ : Sym → ℕ → ℕ
  | .b0, w => 2 * w + 1
  | .b1, w => 2 * w + 2
  | .isNil, w => if w = 0 then 1 else 0
  | .succ, w => w + 1
  | .dbl, w => 2 * w
  | .pred, w => w - 1
  | .log2, w => w.log2
  | _, _ => 0

/-- The definitions of one bitstring. -/
def Unary (s : Sym) : Prop :=
  s = .b0 ∨ s = .b1 ∨ s = .isNil ∨ s = .succ ∨ s = .dbl ∨ s = .pred ∨ s = .log2

/-- The mirror's value of a definition of one bitstring at a number. -/
theorem host_unary (s : Sym) (hs : Unary s) (w : ℕ) :
    «Literals.host» (leaf (symPos s)) [RoseTree.node 0 [leaf w]] =
      encOpt (some (RoseTree.node 0 [leaf (hostN₁ s w)])) := by
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  case inr.inr.inl => cases w <;> rfl
  all_goals rfl

/-- The value of a definition of two bitstrings at numbers, by the arithmetic of the natural
numbers, encoded. -/
def hostN₂ : Sym → ℕ → ℕ → Option Tree
  | .add, a, b => some (RoseTree.node 0 [leaf (a + b)])
  | .mul, a, b => some (RoseTree.node 0 [leaf (a * b)])
  | .eqB, a, b => some (RoseTree.node 0 [leaf (if a = b then 1 else 0)])
  | .cmp, a, b => some (RoseTree.node 1 [leaf (ordPos (compare a b))])
  | .ltB, a, b => some (RoseTree.node 0 [leaf (if a < b then 1 else 0)])
  | .subE, a, b => if b ≤ a then some (RoseTree.node 0 [leaf (a - b)]) else none
  | .sub, a, b => some (RoseTree.node 0 [leaf (a - b)])
  | .divMod, a, b => some (RoseTree.node 2 [leaf (a / b), leaf (a % b)])
  | _, _, _ => none

/-- The definitions of two bitstrings. -/
def Binary (s : Sym) : Prop :=
  s = .add ∨ s = .mul ∨ s = .eqB ∨ s = .cmp ∨ s = .ltB ∨ s = .subE ∨ s = .sub ∨ s = .divMod

/-- A conditional on the order of two labels, as the compiler emits it. -/
theorem ite_lt {α : Type} (a b : ℕ) (x y : α) :
    (if (Const.lt (leaf a) (leaf b)).label ≠ 0 then x else y) = if a < b then x else y :=
  if_congr (by simp only [lt_leaf, label_ne_zero, ofBool_bne, decide_eq_true_eq]) rfl rfl

/-- A conditional on the equality of two labels, as the compiler emits it. -/
theorem ite_eq {α : Type} (a b : ℕ) (x y : α) :
    (if (Const.eq (leaf a) (leaf b)).label ≠ 0 then x else y) = if a = b then x else y :=
  if_congr (by simp only [eq_leaf, label_ne_zero, ofBool_bne, Nat.beq_eq_true_eq]) rfl rfl

/-- The mirror's value of a definition of two bitstrings at numbers. -/
theorem host_binary (s : Sym) (hs : Binary s) (a b : ℕ) :
    «Literals.host» (leaf (symPos s)) [RoseTree.node 0 [leaf a], RoseTree.node 0 [leaf b]] =
      encOpt (hostN₂ s a b) := by
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · rfl
  · refine (rfl : _ = encOpt (some (RoseTree.node 0
      [if (Const.eq (leaf a) (leaf b)).label ≠ 0 then leaf 1 else leaf 0]))).trans ?_
    rw [ite_eq]
    by_cases h : a = b <;> simp only [h, ↓reduceIte, hostN₂]
  · refine (rfl : _ = encOpt (some (RoseTree.node 1
      [if (Const.lt (leaf a) (leaf b)).label ≠ 0 then leaf 0
        else if (Const.eq (leaf a) (leaf b)).label ≠ 0 then leaf 1 else leaf 2]))).trans ?_
    rw [ite_lt, ite_eq]
    have hc : compare a b = if a < b then Ordering.lt else if a = b then .eq else .gt := rfl
    by_cases h : a < b
    · simp only [h, ↓reduceIte, hostN₂, hc, ordPos]
    · by_cases h' : a = b
      · subst h'
        simp only [Nat.lt_irrefl, ↓reduceIte, hostN₂, hc, ordPos]
      · simp only [h, h', ↓reduceIte, hostN₂, hc, ordPos]
  · refine (rfl : _ = encOpt (some (RoseTree.node 0
      [if (Const.lt (leaf a) (leaf b)).label ≠ 0 then leaf 1 else leaf 0]))).trans ?_
    rw [ite_lt]
    by_cases h : a < b <;> simp only [h, ↓reduceIte, hostN₂]
  · refine (rfl : _ = (if (Const.lt (leaf a) (leaf b)).label ≠ 0 then encOpt none
      else encOpt (some (RoseTree.node 0 [leaf (a - b)])))).trans ?_
    rw [ite_lt]
    by_cases h : a < b
    · have h' : ¬ b ≤ a := by omega
      simp only [h, h', ↓reduceIte, hostN₂]
    · have h' : b ≤ a := by omega
      simp only [h, h', ↓reduceIte, hostN₂]
  · rfl
  · rfl

/-- A definition is the empty bitstring, a conditional, a definition of one bitstring or a
definition of two. -/
theorem sym_cases (s : Sym) : s = .bnil ∨ (s = .condB ∨ s = .condO) ∨ Unary s ∨ Binary s := by
  cases s <;> simp only [Unary, Binary, reduceCtorEq, or_true, or_false]

/-- The mirror's value of a definition at literals, the first argument first. -/
theorem host_eq (s : Sym) (vs : List Val) :
    «Literals.host» (leaf (symPos s)) (vs.map encVal) = encOpt ((s.host vs).map encVal) := by
  rcases sym_cases s with rfl | hc | hu | hb
  · rcases vs with _ | ⟨v, vs⟩ <;> rfl
  · have h : «Literals.host» (leaf (symPos s)) (vs.map encVal) =
        «Literals.hostCond» (leaf (symPos s)) (vs.map encVal) := by
      rcases hc with rfl | rfl <;> rfl
    rw [h, hostCond_eq s hc]
  · rcases vs with _ | ⟨v, _ | ⟨v', vs⟩⟩
    · rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · cases v with
      | bits w =>
        rw [show [Val.bits w].map encVal = [RoseTree.node 0 [leaf (val w)]] from rfl,
          host_unary s hu]
        rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [hostN₁, Sym.host, Geb.FreeTopos.Literals.ofBits₁, Option.map_some, encVal,
            Geb.FreeTopos.Literals.val_cons, Geb.FreeTopos.Literals.val_num, Bool.toNat_false,
            Bool.toNat_true, Nat.add_zero, val_truth, isEmpty_eq_decide, decide_eq_true_eq]
      | ord o => rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
      | pair a b => rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases v <;> rfl
  · rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, vs⟩⟩⟩
    · rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases a <;> rfl
    · cases a with
      | bits a =>
        cases b with
        | bits b =>
          rw [show [Val.bits a, Val.bits b].map encVal =
              [RoseTree.node 0 [leaf (val a)], RoseTree.node 0 [leaf (val b)]] from rfl,
            host_binary s hb]
          rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            simp only [hostN₂, Sym.host, Geb.FreeTopos.Literals.ofBits₂, Option.map_some,
              Option.map_ite, encVal, Geb.FreeTopos.Literals.val_num, val_truth,
              decide_eq_true_eq]
        | ord o => rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
        | pair x y => rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
      | ord o => rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases b <;> rfl
      | pair x y =>
        rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases b <;> rfl
    · rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases a <;> cases b <;> rfl

/-- The mirror's pair of two bitstrings, or component of a pair of bitstrings, at a node of a
label from its children's values. -/
theorem pairStep_eq (l : Internal.Label) (vs : List Val) :
    «Literals.pairStep» (leaf (labelData l).1) (vs.map encVal) =
      encOpt ((Geb.FreeTopos.Literals.pairStep l vs).map encVal) := by
  rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, vs⟩⟩⟩
  · cases l <;> rfl
  · cases l <;> cases a <;> rfl
  · cases l <;> cases a <;> cases b <;> rfl
  · cases l <;> cases a <;> cases b <;> rfl

/-- The definitions evaluated, each at its position. -/
theorem symPos_all : Sym.all.map symPos = List.range 18 := by decide

/-- A definition evaluated as the node of its index among the library's definitions, the node of
the objects it is applied at, the node of the types of its arguments, the last first, and the type
of its value. -/
def encSym (s : Sym) : Tree :=
  RoseTree.node 0 [leaf s.index, RoseTree.node 0 s.objs, RoseTree.node 0 s.args.reverse, s.res]

/-- The mirror's definitions evaluated are the encodings of the definitions evaluated, in
order. -/
theorem syms_eq : «Literals.syms» = Sym.all.map encSym := by decide +kernel

/-- The mirror's search of encoded definitions for the first of an index and objects, from a
position: the position of the definition found, where the definitions' positions are the
positions from that one on. -/
theorem symFold_eq (k : ℕ) (θ : List Tree) : ∀ (ss : List Sym) (i : ℕ),
    ss.map symPos = List.range' i ss.length →
    List.foldr
        (fun row (rest : Tree → Tree) i ↦
          if ((Const.child row (leaf 0)).label == k &&
              decide ((Const.child row (leaf 1)).children = θ)) = true then
            «Prelude.some» i
          else rest (Const.add i (leaf 1)))
        (fun _ ↦ «Prelude.none») (ss.map encSym) (leaf i) =
      encOpt ((ss.find? fun s ↦ decide (s.index = k ∧ s.objs = θ)).map fun s ↦
        leaf (symPos s)) :=
  List.rec (fun _ _ ↦ rfl) fun s ss ih i h ↦ by
    simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at h
    have hc : ((Const.child (encSym s) (leaf 0)).label == k &&
        decide ((Const.child (encSym s) (leaf 1)).children = θ)) =
        decide (s.index = k ∧ s.objs = θ) := by
      simp only [encSym, child_node, List.getD_cons_zero, List.getD_cons_succ, label_leaf,
        RoseTree.children_node, Bool.decide_and]
      congr 1
    simp only [List.map_cons, List.foldr_cons, List.find?_cons, hc]
    cases hp : decide (s.index = k ∧ s.objs = θ)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact ih (i + 1) h.2
    · simp only [↓reduceIte, Option.map_some, ← h.1]
      rfl

/-- The mirror's definition of the library an encoded node's root applies, where it is one of
those evaluated. -/
theorem symOf_eq (l : Internal.Label) (cs : List Term) :
    «Literals.symOf» (encTerm (RoseTree.node l cs)) =
      encOpt ((Sym.ofLabel l).map fun s ↦ leaf (symPos s)) := by
  cases l with
  | defn k θ =>
    have h := symFold_eq k θ Sym.all 0 (by decide)
    mirror_simp [«Literals.symOf», encTerm_node, labelData, «Language.mD», «Language.mData»,
      at_eq, syms_eq]
    exact h
  | _ => rfl

/-! The evaluation. -/

/-- The mirror's terms of the comparisons' results. -/
theorem ordT_eq (o : Ordering) :
    (match o with
      | .lt => «Translation.ltO»
      | .eq => «Translation.eqO»
      | .gt => «Translation.gtO») = encTerm (Geb.FreeTopos.Literals.ordT o) := by
  cases o <;> rfl

/-- The values of a list of optional values, each present, encoded. -/
theorem mapM_id_map (os : List (Option Val)) :
    (os.mapM id).map (List.map encVal) =
      if os.all Option.isSome = true then some ((os.map fun o ↦ o.map encVal).filterMap id)
      else none :=
  List.rec rfl (fun o os ih ↦ by
    rw [List.mapM_cons, List.all_cons, List.map_cons]
    cases o with
    | none => rfl
    | some v =>
      cases hm : os.mapM id with
      | none =>
        rw [hm] at ih
        cases ha : os.all Option.isSome <;> simp_all
      | some vs =>
        rw [hm] at ih
        cases ha : os.all Option.isSome <;> simp_all) os

/-- The comparison's result a term is: the first of less, equal and greater whose term it is. -/
theorem ordOf_eq (t : Term) :
    Geb.FreeTopos.Literals.ordOf t =
      if t = Translation.ltO then some .lt else if t = Translation.eqO then some .eq
      else if t = Translation.gtO then some .gt else none := by
  by_cases h1 : t = Translation.ltO
  · subst h1
    simp [Geb.FreeTopos.Literals.ordOf, Geb.FreeTopos.Literals.ordT]
  have h1' : ¬Translation.ltO = t := fun e ↦ h1 e.symm
  by_cases h2 : t = Translation.eqO
  · subst h2
    simp [Geb.FreeTopos.Literals.ordOf, Geb.FreeTopos.Literals.ordT, h1, h1']
  have h2' : ¬Translation.eqO = t := fun e ↦ h2 e.symm
  by_cases h3 : t = Translation.gtO
  · subst h3
    simp [Geb.FreeTopos.Literals.ordOf, Geb.FreeTopos.Literals.ordT, h1, h1', h2, h2']
  have h3' : ¬Translation.gtO = t := fun e ↦ h3 e.symm
  simp [Geb.FreeTopos.Literals.ordOf, Geb.FreeTopos.Literals.ordT, h1, h1', h2, h2', h3, h3']

/-- The mirror's step of the evaluation at an encoded term, from the values of its children:
a comparison's result, or the step past it. -/
theorem evalStep_ord (t : Term) (rs : List Tree) :
    «Literals.evalStep» (encTerm t) rs =
      if t = Translation.ltO then encOpt (some (encVal (.ord .lt)))
      else if t = Translation.eqO then encOpt (some (encVal (.ord .eq)))
      else if t = Translation.gtO then encOpt (some (encVal (.ord .gt)))
      else
        if (Templates.allJust (rs.tail)).1.label ≠ 0 then
          if («Prelude.isSome» («Literals.symOf» (encTerm t))).label ≠ 0 then
            «Literals.host» («Prelude.get» («Literals.symOf» (encTerm t)))
              ((Templates.allJust (rs.tail)).2.reverse)
          else «Literals.pairStep» (leaf (encTerm t).label) (Templates.allJust (rs.tail)).2
        else encOpt none := by
  have hlt : «Translation.ltO» = encTerm Translation.ltO := rfl
  have heq : «Translation.eqO» = encTerm Translation.eqO := rfl
  have hgt : «Translation.gtO» = encTerm Translation.gtO := rfl
  simp only [«Literals.evalStep», hlt, heq, hgt, equal_eq, encTerm_eq_iff, label_ne_zero,
    ofBool_bne, decide_eq_true_eq, template, tail_eq, reverse_eq, label_eq]
  rfl

/-- The mirror's step of the evaluation at an encoded node, from the encoded values of its
children. -/
theorem evalStep_eq (l : Internal.Label) (v : Tree) (xs : List (Term × Tree × Option Val))
    (hx : ∀ x ∈ xs, x.2.1 = encOpt (x.2.2.map encVal)) :
    «Literals.evalStep» (encTerm (RoseTree.node l (xs.map Prod.fst)))
        (v :: xs.map fun x ↦ x.2.1) =
      encOpt ((Geb.FreeTopos.Literals.evalStep l (xs.map fun x ↦ (x.1, x.2.2))).map encVal) := by
  have hfst : (xs.map fun x ↦ (x.1, x.2.2)).map Prod.fst = xs.map Prod.fst := by
    rw [List.map_map]
    rfl
  have hsnd : (xs.map fun x ↦ (x.1, x.2.2)).map Prod.snd = xs.map fun x ↦ x.2.2 := by
    rw [List.map_map]
    rfl
  have htail : (v :: xs.map fun x ↦ x.2.1).tail =
      ((xs.map fun x ↦ x.2.2).map fun o ↦ o.map encVal).map encOpt := by
    rw [List.tail_cons, List.map_map, List.map_map]
    exact List.map_congr_left hx
  have hall : ((xs.map fun x ↦ x.2.2).map fun o ↦ o.map encVal).all Option.isSome =
      (xs.map fun x ↦ x.2.2).all Option.isSome := by
    rw [List.all_map]
    congr 1
    funext o
    cases o <;> rfl
  have hm := mapM_id_map (xs.map fun x ↦ x.2.2)
  rw [evalStep_ord, Geb.FreeTopos.Literals.evalStep, hfst, hsnd, ordOf_eq, htail,
    tmpl_allJust_eq, hall, symOf_eq]
  by_cases h1 : RoseTree.node l (xs.map Prod.fst) = Translation.ltO
  · simp only [h1, ↓reduceIte]
    rfl
  by_cases h2 : RoseTree.node l (xs.map Prod.fst) = Translation.eqO
  · simp only [h2, ↓reduceIte]
    rfl
  by_cases h3 : RoseTree.node l (xs.map Prod.fst) = Translation.gtO
  · simp only [h3, ↓reduceIte]
    rfl
  simp only [h1, h2, h3, ↓reduceIte]
  cases hos : (xs.map fun x ↦ x.2.2).all Option.isSome
  · rw [hos] at hm
    have hn : (xs.map fun x ↦ x.2.2).mapM id = none := by
      cases h : List.mapM id (xs.map fun x ↦ x.2.2) with
      | none => rfl
      | some vs => simp [h] at hm
    rw [hn]
    rfl
  · rw [hos] at hm
    obtain ⟨vs, hvs, hvs'⟩ : ∃ vs, (xs.map fun x ↦ x.2.2).mapM id = some vs ∧
        vs.map encVal = ((xs.map fun x ↦ x.2.2).map fun o ↦ o.map encVal).filterMap id := by
      cases h : List.mapM id (xs.map fun x ↦ x.2.2) with
      | none => simp [h] at hm
      | some vs => exact ⟨vs, rfl, by simpa [h] using hm⟩
    rw [hvs, ← hvs', ← List.map_reverse]
    cases hl : Sym.ofLabel l with
    | none =>
      simp only [Option.map_none, isSome_eq, Option.isSome_none, ofBool_false, label_leaf,
        ne_eq, not_true_eq_false, ↓reduceIte, ofBool_true, one_ne_zero, not_false_eq_true,
        Option.bind_eq_bind, Option.bind_some, encTerm_node, RoseTree.label_node]
      exact pairStep_eq l vs
    | some s =>
      simp only [Option.map_some, isSome_eq, Option.isSome_some, ofBool_true, label_leaf,
        ne_eq, one_ne_zero, not_false_eq_true, ↓reduceIte, get_eq, Option.bind_eq_bind,
        Option.bind_some]
      exact host_eq s vs.reverse

/-- The mirror's value of an encoded term built of the definitions evaluated over literals. -/
theorem valueOf_eq (t : Term) :
    «Literals.valueOf» (encTerm t) = encOpt ((Geb.FreeTopos.Literals.eval t).map encVal) :=
  para_enc (fun l ↦ (labelData l).1) (fun l ↦ RoseTree.node 0 (labelData l).2)
    (fun (v : Tree) (w : Option Val) ↦ v = encOpt (w.map encVal)) «Literals.evalStep»
    Geb.FreeTopos.Literals.evalStep (fun l v xs hx ↦ evalStep_eq l v xs hx) t

/-- The numeral of the number a bitstring denotes is the bitstring's numeral. -/
theorem numeral_val (w : List Bool) :
    Translation.numeral (val w) = Geb.FreeTopos.Literals.bitsT w := by
  simp only [Translation.numeral, Oitavem.unrank_rank, Geb.FreeTopos.Literals.bitsT]
  rfl

/-- The mirror's term of an encoded literal. -/
theorem litTerm_eq (v : Val) : «Literals.litTerm» (encVal v) = encTerm v.term := by
  cases v with
  | bits w => exact (trNumeral_eq (val w)).trans (congrArg encTerm (numeral_val w))
  | ord o => cases o <;> rfl
  | pair a b =>
    refine (rfl : _ = «Language.mPair» («Translation.trNumeral» (leaf (val a)))
      («Translation.trNumeral» (leaf (val b)))).trans ?_
    rw [trNumeral_eq, trNumeral_eq, mPair_eq, numeral_val, numeral_val]
    rfl

/-- The mirror's term of the value of an encoded term, where it has one. -/
theorem litEval_eq (t : Term) :
    «Literals.litEval» (encTerm t) =
      encOpt ((Geb.FreeTopos.Literals.eval t).map fun v ↦ encTerm v.term) := by
  simp only [«Literals.litEval», valueOf_eq]
  cases Geb.FreeTopos.Literals.eval t with
  | none => rfl
  | some v => exact congrArg (fun x ↦ encOpt (some x)) (litTerm_eq v)

/-! The equations and the test of readiness. -/

/-- The mirror's equations are the encodings of the definitions' equations at the numerals' bits,
in order. -/
theorem lemmas_eq : «Literals.lemmas» = Geb.FreeTopos.Literals.lemmas.map encThm := by
  decide +kernel

/-- Encoded theorems are equal exactly when their arities, contexts, hypotheses and conclusions
are. -/
theorem encThm_eq_iff (a b : Internal.Thm) :
    encThm b = encThm a ↔
      b.arity = a.arity ∧ b.ctx = a.ctx ∧ b.hyps = a.hyps ∧ b.concl = a.concl := by
  simp only [encThm, node_inj, List.cons.injEq, leaf_inj, true_and, and_true, encTerm_eq_iff,
    (List.map_injective_iff.mpr encTerm_inj).eq_iff]

/-- The mirror's theorem among encoded entries at a position. -/
theorem thmAt_eq (E : Array Internal.Entry) (k : ℕ) :
    «Derivation.thmAt» (E.toList.map encEntry) (leaf k) =
      encOpt (((E[k]?).bind Internal.Entry.language?).map encThm) := by
  simp only [template, nth_eq, List.getElem?_map, Array.getElem?_toList]
  rcases E[k]? with _ | (a | s) <;> rfl

/-- One step of the mirror's test that the theorems of the entries from a position on are given
theorems: the test at the first, and the test of the rest from the next position. -/
def lemStep (E' : List Tree) (j' : Tree) (a : Tree) (rest : Tree → Tree) (i : Tree) : Tree :=
  «Prelude.and»
    (if (Const.eq (Const.label («Derivation.thmAt» E' (Const.add j' i))) (leaf 1)).label ≠ 0 then
      Const.equal
        (Const.lcase (Const.children («Derivation.thmAt» E' (Const.add j' i))) (leaf 0)
          fun x _ ↦ x) a
    else leaf 0)
    (rest (Const.add i (leaf 1)))

/-- The mirror's test that the theorems of the entries from a position on are the equations is
the fold of its step over the equations. -/
theorem lemmasIn_def (E' : List Tree) (j' : Tree) :
    «Literals.lemmasIn» E' j' =
      Const.foldr (lemStep E' j') (fun _ ↦ leaf 1) «Literals.lemmas» (leaf 0) := rfl

/-- The fold of the mirror's step over encoded theorems, from a position. -/
theorem lemFold_eq (E : Array Internal.Entry) (j : ℕ) : ∀ (as : List Internal.Thm) (i : ℕ),
    Const.foldr (lemStep (E.toList.map encEntry) (leaf j)) (fun _ ↦ leaf 1) (as.map encThm)
        (leaf i) =
      ofBool ((as.zipIdx i).all fun (a, i) ↦
        match (E[j + i]?).bind Internal.Entry.language? with
        | some b => decide (b.arity = a.arity ∧ b.ctx = a.ctx ∧ b.hyps = a.hyps ∧
            b.concl = a.concl)
        | none => false) :=
  List.rec (fun _ ↦ rfl) fun a as ih i ↦ by
    simp only [List.map_cons, foldr_eq, List.foldr_cons, List.zipIdx_cons, List.all_cons]
    rw [← foldr_eq, lemStep, add_leaf, add_leaf, ih (i + 1), thmAt_eq]
    cases (E[j + i]?).bind Internal.Entry.language? with
    | none => rfl
    | some b =>
      simp only [Option.map_some, label_eq, encOpt_some_label, eq_leaf, beq_self_eq_true,
        ofBool_true, label_leaf, ne_eq, one_ne_zero, not_false_eq_true, ↓reduceIte, children_eq,
        lcase_children_head, child_encOpt_some, equal_eq, encThm_eq_iff, and_eq]

/-- The mirror's test that the theorems of encoded entries from a position on are the
equations. -/
theorem lemmasIn_eq (E : Array Internal.Entry) (j : ℕ) :
    «Literals.lemmasIn» (E.toList.map encEntry) (leaf j) =
      ofBool (Geb.FreeTopos.Literals.lemmasIn E j) := by
  rw [lemmasIn_def, lemmas_eq, lemFold_eq]
  rfl

/-- The mirror's test that the definition of an index among encoded constants is the one
evaluated, in its objects, its arguments' types and its value's type. -/
theorem sigOk_eq (G : Internal.Globals) (n : ℕ) (s : Sym) :
    «Literals.sigOk» (encGlobals G) (leaf n) (leaf s.index) s.objs s.args.reverse s.res =
      ofBool (Geb.FreeTopos.Literals.sigOk G n s) := by
  mirror_simp [«Literals.sigOk», Geb.FreeTopos.Literals.sigOk, template, gDefs_eq,
    List.getElem?_map, Option.map_bind, defLanguage_eq]
  rcases G.defs[s.index]? with _ | (d | ⟨m, b⟩)
  · rfl
  · simp only [Option.map_some, Option.elim_some, defLanguage_eq, Internal.Definition.language?,
      encOpt_some_label, beq_self_eq_true, ↓reduceIte, child_encOpt_some, ldArity_eq, eq_leaf,
      allT_isTy, ldParams_eq, ldType_eq, and_eq, Option.bind_some, PartialHorn.phSubst_eq,
      beq_eq_decide]
  · rfl

/-- The mirror's test that the definitions evaluated are those of encoded constants. -/
theorem sigs_eq (G : Internal.Globals) (n : ℕ) :
    «Literals.sigs» (encGlobals G) (leaf n) =
      ofBool (Sym.all.all (Geb.FreeTopos.Literals.sigOk G n)) := by
  simp only [«Literals.sigs», syms_eq]
  exact allT_map _ encSym _ Sym.all fun s _ ↦ by
    simp only [encSym, child_node, List.getD_cons_zero, List.getD_cons_succ, children_eq,
      RoseTree.children_node]
    exact sigOk_eq G n s

/-- The mirror's test of the conditions under which the evaluation is a rewriting, at encoded
constants and entries. -/
theorem ready_eq (G : Internal.Globals) (E : Array Internal.Entry) (j : ℕ) :
    «Literals.ready» (encGlobals G) (E.toList.map encEntry) (leaf j) =
      ofBool (Geb.FreeTopos.Literals.ready G E j) := by
  have hlt : «Translation.ltO» = encTerm Translation.ltO := rfl
  have heq : «Translation.eqO» = encTerm Translation.eqO := rfl
  have hgt : «Translation.gtO» = encTerm Translation.gtO := rfl
  have ho : «Prelude.some» «Translation.ordTy» = encOpt (some Translation.ordTy) := rfl
  simp only [«Literals.ready», lemmasIn_eq, sigs_eq, hlt, heq, hgt, ho, typeIn_eq, equal_eq,
    encOpt_inj, and_eq, Geb.FreeTopos.Literals.ready, List.all_cons, List.all_nil, Bool.and_true,
    Geb.FreeTopos.Literals.ordT, Bool.and_assoc]
  rfl

end GebTests.Prototypes.FreeTopos.Agreement.Literals

end
