/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Agreement.Base
public import GebTests.Prototypes.FreeTopos.Agreement.Fold
public import GebTests.Prototypes.Kernel.Modules
public import Geb.Prototypes.Kernel.Printer
public import GebTests.Prototypes.CheckMirror

set_option doc.verso true in
/-!
# The printer written in Geb

The functions of {lit}`bootstrap/printer.geb`, in the Lean the bootstrap compiler emits
({lit}`GebMirror.Metalogic`), agree with the Lean printer of kernel terms
({name}`Geb.Kernel.printTerm`): the numerals the datatype language writes, types, quoted trees
and well-formed terms, each printed as the encoding of the Lean S-expression, and the test of
well-formed terms ({name}`Geb.Kernel.TermWf`) by which the partial printer decides what it
prints.

## Main definitions

## Main statements

* {lit}`decimalChars_eq` — the numeral of a natural number.
* {lit}`printType_eq`, {lit}`printDatum_eq` — types and quoted trees.
* {lit}`printTerm_eq` — a well-formed term printed under binders to a depth.
* {lit}`termWf_eq` — the well-formedness of a term under binders to a depth.

## Tags

printer, agreement, mirror
-/

set_option doc.verso true

@[expose] public section

open GebMirror.Metalogic

namespace GebTests.Prototypes.FreeTopos.Agreement.Printer

open Geb Geb.Kernel GebTests.Prototypes.FreeTopos.Agreement.Base
  GebTests.Prototypes.FreeTopos.Agreement.Fold
open Geb.Kernel.ModulesTests (sexpTree)
open scoped FinEnum

/-! ## Numerals -/

/-- Iteration applies its step first. -/
theorem repeat_succ' {α : Type} (f : α → α) :
    ∀ (n : ℕ) (a : α), Nat.repeat f (n + 1) a = Nat.repeat f n (f a) :=
  Nat.rec (fun _ ↦ rfl) fun n ih a ↦ by
    change f (Nat.repeat f (n + 1) a) = f (Nat.repeat f n (f a))
    rw [ih]

/-- No digits of zero. -/
theorem digitsLEAux_zero_right : ∀ f : ℕ, Csexp.digitsLEAux f 0 = [] :=
  Nat.rec rfl fun _ _ ↦ rfl

/-- The digits of a number below a power of ten are found within as many steps. -/
theorem digitsLEAux_stable : ∀ (f g n : ℕ), n < 10 ^ f → f ≤ g →
    Csexp.digitsLEAux g n = Csexp.digitsLEAux f n :=
  Nat.rec
    (fun g n hn _ ↦ by
      have : n = 0 := by rw [Nat.pow_zero] at hn; omega
      subst this
      rw [digitsLEAux_zero_right, digitsLEAux_zero_right])
    (fun f ih g n hn hfg ↦ by
      obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
      rw [Csexp.digitsLEAux_succ, Csexp.digitsLEAux_succ]
      split
      · rfl
      · have : n / 10 < 10 ^ f := by
          rw [Nat.pow_succ] at hn
          exact (Nat.div_lt_iff_lt_mul (by decide)).mpr hn
        rw [ih g (n / 10) this (by omega)])

/-- A number is below ten to the power of one more than its base-two logarithm. -/
theorem lt_ten_pow_log2 (n : ℕ) : n < 10 ^ (n.log2 + 1) :=
  Nat.lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_left (by decide) _)

/-- A positive number's base-two logarithm is below it. -/
theorem log2_lt_self {n : ℕ} (h : n ≠ 0) : n.log2 < n :=
  Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.log2_self_le h)

/-- The quotient of two labels. -/
@[simp] theorem div_leaf (a b : ℕ) : Const.div (leaf a) (leaf b) = leaf (a / b) := rfl

/-- The remainder of two labels. -/
@[simp] theorem mod_leaf (a b : ℕ) : Const.mod (leaf a) (leaf b) = leaf (a % b) := rfl

/-- The step of the count of a numeral's digits: one more digit and the number divided by ten,
until the number is zero. -/
def countStep (p : Tree × Tree) : Tree × Tree :=
  if (Const.eq p.2 (leaf 0)).label ≠ 0 then p
  else (Const.add p.1 (leaf 1), Const.div p.2 (leaf 10))

/-- The count of a number's digits within a number of steps. -/
theorem repeat_countStep : ∀ (j c m : ℕ),
    (Nat.repeat countStep j (leaf c, leaf m)).1 = leaf (c + (Csexp.digitsLEAux j m).length) :=
  Nat.rec (fun _ _ ↦ rfl) fun j ih c m ↦ by
    rw [repeat_succ', Csexp.digitsLEAux_succ]
    by_cases hm : m = 0
    · subst hm
      have : countStep (leaf c, leaf 0) = (leaf c, leaf 0) := rfl
      rw [this, ih, digitsLEAux_zero_right]
      rfl
    · have : countStep (leaf c, leaf m) = (leaf (c + 1), leaf (m / 10)) := by
        simp [countStep, hm]
      rw [this, ih, ite_eq_right_iff.mpr (fun h ↦ absurd h hm), List.length_cons]
      congr 1
      omega

/-- The low digits of a number, as many as asked, least significant first, zeros included. -/
def lowDigits : ℕ → ℕ → List ℕ := Nat.rec (fun _ ↦ []) fun _ ih q ↦ q % 10 :: ih (q / 10)

/-- The step of the digits of a number, most significant first: the number divided by ten, and
its last digit before the digits so far. -/
def msbStep (p : Tree × List Tree) : Tree × List Tree :=
  (Const.div p.1 (leaf 10), Const.mod p.1 (leaf 10) :: p.2)

/-- The digits of a number taken in a number of steps, most significant first. -/
theorem repeat_msbStep : ∀ (k q : ℕ) (ds : List Tree),
    (Nat.repeat msbStep k (leaf q, ds)).2 = (lowDigits k q).reverse.map leaf ++ ds :=
  Nat.rec (fun _ _ ↦ rfl) fun k ih q ds ↦ by
    rw [repeat_succ']
    change (Nat.repeat msbStep k (leaf (q / 10), leaf (q % 10) :: ds)).2 = _
    rw [ih]
    simp [lowDigits]

/-- As many low digits as a number has are its digits. -/
theorem lowDigits_length : ∀ (f n : ℕ),
    lowDigits (Csexp.digitsLEAux f n).length n = Csexp.digitsLEAux f n :=
  Nat.rec (fun _ ↦ rfl) fun f ih n ↦ by
    rw [Csexp.digitsLEAux_succ]
    split
    · rfl
    · rw [List.length_cons]
      change n % 10 :: lowDigits _ (n / 10) = _
      rw [ih]

/-- A digit's character's code point. -/
theorem toNat_digitChar : ∀ d : Fin 10, (Csexp.digitChar d).toNat = d + 48 := by decide

/-- Digits, each written as the leaf of its character's code point. -/
theorem foldr_digits : ∀ L : List ℕ, (∀ d ∈ L, d < 10) →
    (L.map leaf).foldr (fun x2 x3 ↦ Const.add x2 (leaf 48) :: x3) [] =
      L.map ((fun c : Char ↦ leaf c.toNat) ∘ Csexp.digitChar) :=
  List.rec (fun _ ↦ rfl) fun d L ih h ↦ by
    rw [List.map_cons, List.foldr_cons, ih fun x hx ↦ h x (List.mem_cons_of_mem d hx),
      List.map_cons, add_leaf, Function.comp_apply, toNat_digitChar ⟨d, h d List.mem_cons_self⟩]

/-- The numeral the datatype language writes is the decimal spelling of the number. -/
theorem decimalChars_eq (n : ℕ) :
    «Datatype.decimalChars» (leaf n) = (Csexp.decOf n).map fun c ↦ leaf c.toNat := by
  unfold «Datatype.decimalChars» Csexp.decOf
  by_cases hn : n = 0
  · subst hn
    rfl
  · simp only [eq_leaf, ofBool_label_eq_zero, beq_eq_false_iff_ne, ne_eq, hn, not_false_eq_true,
      not_true_eq_false, ↓reduceIte, Const.log2, add_leaf, iter_leaf, foldr_eq, label_leaf]
    have hc := repeat_countStep (n.log2 + 1) 0 n
    rw [show (fun (x1 : Tree × Tree) ↦ if (Const.eq x1.2 (leaf 0)).label ≠ 0 then x1
        else (Const.add x1.1 (leaf 1), Const.div x1.2 (leaf 10))) = countStep from rfl, hc,
      Nat.zero_add]
    unfold «Prelude.digitsMsb»
    rw [iter_leaf, show (fun (x3 : Tree × List Tree) ↦ (Const.div x3.1 (leaf 10),
        Const.mod x3.1 (leaf 10) :: x3.2)) = msbStep from rfl, repeat_msbStep,
      List.append_nil, lowDigits_length,
      ← digitsLEAux_stable (n.log2 + 1) n n (lt_ten_pow_log2 n) (log2_lt_self hn)]
    change _ = ((Csexp.digitsLE n).reverse.map Csexp.digitChar).map _
    rw [List.map_map]
    exact foldr_digits _ fun d hd ↦ Csexp.digitsLE_lt n d (List.mem_reverse.mp hd)

/-! ## Atoms, types and data -/

/-- The characters of a word as leaves of their code points. -/
def charsT (s : List Char) : List Tree := s.map fun c ↦ leaf c.toNat

/-- An atom's encoding. -/
theorem sexpTree_atomS (s : List Char) : sexpTree (atomS s) = RoseTree.node 1 (charsT s) := by
  simp only [sexpTree, atomS, RoseTree.elim_node]
  rfl

/-- A list's encoding. -/
theorem sexpTree_listS (cs : List SExp) :
    sexpTree (listS cs) = RoseTree.node 2 (cs.map sexpTree) := by
  simp only [sexpTree, listS, RoseTree.elim_node]

/-- The atom of a name. -/
theorem atomOf_eq (s : List Char) : «Printer.atomOf» (nameTree s) = sexpTree (atomS s) := by
  rw [sexpTree_atomS, «Printer.atomOf», nameTree, children_eq, RoseTree.children_node]
  rfl

/-- A list of S-expressions. -/
theorem listOf_eq (cs : List SExp) :
    «Printer.listOf» (cs.map sexpTree) = sexpTree (listS cs) := (sexpTree_listS cs).symm

/-- The atom of a numeral. -/
theorem numAtom_eq (n : ℕ) : «Printer.numAtom» (leaf n) = sexpTree (numeralS n) := by
  simp only [«Printer.numAtom», decimalChars_eq, node_leaf, numeralS, sexpTree_atomS, charsT]

/-- The atom of a binder's name. -/
theorem binderAtom_eq (d : ℕ) :
    «Printer.binderAtom» (leaf d) = sexpTree (atomS (binderName d)) := by
  simp only [«Printer.binderAtom», decimalChars_eq, node_leaf, binderName, sexpTree_atomS, charsT,
    List.map_cons]
  rfl

/-- A keyword applied to a list of S-expressions. -/
theorem kwList1_eq (s : List Char) (cs : List SExp) :
    «Printer.kwList1» (nameTree s) (cs.map sexpTree) = sexpTree (listS (atomS s :: cs)) := by
  rw [«Printer.kwList1», atomOf_eq, ← List.map_cons, listOf_eq]

/-- The mirror's test of a list's having an element. -/
theorem nonEmpty_eq (xs : List Tree) : «Reader.nonEmpty» xs = ofBool !xs.isEmpty := by
  cases xs <;> rfl

/-- A type printed structurally. -/
theorem printType_eq (A : Tree) : «Printer.printType» A = sexpTree (printType A) := by
  refine fold_rel (fun v w ↦ v = sexpTree w) _ printTypeStep (fun l xs hxs ↦ ?_) A
  have hm : xs.map Prod.fst = (xs.map Prod.snd).map sexpTree := by
    rw [List.map_map]
    exact List.map_congr_left fun x hx ↦ hxs x hx
  rw [hm]
  have hk : ∀ (s : List Char) (cs : List SExp), «Printer.listOf» («Printer.atomOf» (nameTree s) ::
      cs.map sexpTree) = sexpTree (listS (atomS s :: cs)) := kwList1_eq
  match l with
  | 0 => exact atomOf_eq ['T']
  | 1 => exact atomOf_eq ['U', 'n', 'i', 't']
  | 2 => exact hk ['P', 'r', 'o', 'd'] _
  | 3 => exact hk ['A', 'r', 'r', 'o', 'w'] _
  | l + 4 => exact hk ['L', 'i', 's', 't'] _

/-- A quoted tree written as a datum. -/
theorem printDatum_eq (t : Tree) : «Printer.printDatum» t = sexpTree (printDatum t) := by
  refine fold_rel (fun v w ↦ v = sexpTree w) _ _ (fun l xs hxs ↦ ?_) t
  have hm : xs.map Prod.fst = (xs.map Prod.snd).map sexpTree := by
    rw [List.map_map]
    exact List.map_congr_left fun x hx ↦ hxs x hx
  rw [hm, nonEmpty_eq, List.isEmpty_map]
  cases xs with
  | nil => exact numAtom_eq l
  | cons x xs =>
    rw [numAtom_eq, ← List.map_cons, listOf_eq]
    rfl

/-! ## Terms -/

/-- The printings of a node's children at a binder depth, each child at the depth under the
binders the node gives it. -/
def prKids (l : Tree) (rs : List (Tree → Tree)) (e i : Tree) : List Tree :=
  List.foldr (fun (r : Tree → Tree) (c : Tree → Tree → List Tree) (e i : Tree) ↦
      r (if («Prelude.and» (Const.eq l (leaf 9)) (Const.eq i (leaf 1))).label ≠ 0 then
          Const.add e (leaf 1)
        else e) :: c e (Const.add i (leaf 1)))
    (fun _ _ ↦ []) rs e i

/-- The mirror's printing of a term at a node, from its children's printings. -/
theorem printTerm_mnode (defs : List Tree) (l : ℕ) (cs : List Tree) (e : Tree) :
    «Printer.printTerm» defs (RoseTree.node l cs) e =
      «Printer.printStep» defs (RoseTree.node l cs)
        (prKids (leaf l) (cs.map fun c ↦ «Printer.printTerm» defs c) e (leaf 0)) e := by
  unfold «Printer.printTerm»
  rw [Const.para_node]
  simp only [foldr_eq, prKids]
  rfl

/-- The printings of a node's children at a label other than an abstraction's, each at the
node's depth. -/
theorem prKids_other (l : ℕ) (hl : l ≠ 9) (rs : List (Tree → Tree)) (e : Tree) :
    ∀ i : ℕ, prKids (leaf l) rs e (leaf i) = rs.map fun r ↦ r e := by
  have h : (l == 9) = false := by simpa using hl
  refine rs.rec (fun _ ↦ rfl) fun r rs ih i ↦ ?_
  have := ih (i + 1)
  simp only [prKids, List.foldr_cons, List.map_cons, eq_leaf, h, and_eq, Bool.false_and,
    ofBool_label, ne_eq, Bool.false_eq_true, ↓reduceIte, add_leaf] at this ⊢
  rw [this]

/-- The printings of an abstraction's children: the body's under one more binder. -/
theorem prKids_lam (a b : Tree → Tree) (e : Tree) :
    prKids (leaf 9) [a, b] e (leaf 0) = [a e, b (Const.add e (leaf 1))] := rfl

/-- The mirror's list of S-expressions. -/
theorem listOf_def (xs : List Tree) : «Printer.listOf» xs = RoseTree.node 2 xs := rfl

/-- The mirror's list headed by a keyword. -/
theorem kwList1_def (k : Tree) (xs : List Tree) :
    «Printer.kwList1» k xs = RoseTree.node 2 («Printer.atomOf» k :: xs) := rfl

/-- The keyword of abstractions. -/
theorem kwAtom_lam : «Printer.atomOf» «Reader.kwLam» = sexpTree (atomS ['l', 'a', 'm']) :=
  atomOf_eq ['l', 'a', 'm']

/-- The Lean printing of an abstraction. -/
theorem printStep_lam_eq (defs : List (List Char)) (A b : Tree) (d : ℕ) :
    printStep defs Label.lam [(A, printTerm defs A), (b, printTerm defs b)] d =
      listS [atomS ['l', 'a', 'm'], listS [atomS (binderName d), printType A],
        printTerm defs b (d + 1)] := rfl

/-- The Lean printing of a keyword over its arguments. -/
theorem printStep_kw_eq (defs : List (List Char)) (rs : List (Tree × (ℕ → SExp))) (d : ℕ) :
    printStep defs Label.pair rs d = listS (atomS ['p', 'a', 'i', 'r'] :: rs.map fun r ↦ r.2 d) ∧
    printStep defs Label.fst rs d = listS (atomS ['f', 's', 't'] :: rs.map fun r ↦ r.2 d) ∧
    printStep defs Label.snd rs d = listS (atomS ['s', 'n', 'd'] :: rs.map fun r ↦ r.2 d) ∧
    printStep defs Label.cond rs d = listS (atomS ['i', 'f'] :: rs.map fun r ↦ r.2 d) ∧
    printStep defs Label.cons rs d = listS (atomS ['c', 'o', 'n', 's'] :: rs.map fun r ↦ r.2 d) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A keyword's atom in the mirror. -/
theorem atomOf_kw (k : Tree) : «Printer.atomOf» k = RoseTree.node 1 k.children := rfl

/-- The Lean printing of an application. -/
theorem printStep_app_eq (defs : List (List Char)) (f x : Tree) (d : ℕ) :
    printStep defs Label.app [(f, printTerm defs f), (x, printTerm defs x)] d =
      listS [printTerm defs f d, printTerm defs x d] := rfl

/-- The unfolding of the mirror's printing at a node, its label and children read. -/
local macro "pr_node" : tactic => `(tactic|
  (simp only [«Printer.printStep», label_eq, children_eq, RoseTree.label_node,
      RoseTree.children_node]
   rfl))

/-- The mirror's printing of a variable. -/
theorem printStep_var (defs : List Tree) (cs ps : List Tree) (e : Tree) :
    «Printer.printStep» defs (RoseTree.node Label.var cs) ps e = «Printer.binderAtom» (Const.sub
      (Const.sub e (leaf 1)) (Const.label («Prelude.at» cs (leaf 0)))) := by
  pr_node

/-- The mirror's printing of an abstraction. -/
theorem printStep_lam (defs : List Tree) (cs ps : List Tree) (e : Tree) :
    «Printer.printStep» defs (RoseTree.node Label.lam cs) ps e = «Printer.kwList1» «Reader.kwLam»
      («Printer.listOf» («Printer.binderAtom» e :: «Prelude.single» («Printer.printType»
        («Prelude.at» cs (leaf 0)))) ::
        «Prelude.single» («Prelude.at» ps (leaf 1))) := by
  pr_node

/-- The mirror's printing of an application. -/
theorem printStep_app (defs : List Tree) (cs ps : List Tree) (e : Tree) :
    «Printer.printStep» defs (RoseTree.node Label.app cs) ps e = «Printer.listOf» ps := rfl

/-- The mirror's printing of the unit. -/
theorem printStep_unit (defs : List Tree) (cs ps : List Tree) (e : Tree) :
    «Printer.printStep» defs (RoseTree.node Label.unit cs) ps e =
      «Printer.atomOf» «Reader.kwUnitValue» := rfl

/-- The mirror's printing of a quotation. -/
theorem printStep_quote (defs : List Tree) (cs ps : List Tree) (e : Tree) :
    «Printer.printStep» defs (RoseTree.node Label.quote cs) ps e =
      let c := «Prelude.at» cs (leaf 0)
      if («Reader.nonEmpty» (Const.children c)).label ≠ 0 then
        «Printer.kwList1» «Reader.kwQuote» («Prelude.single» («Printer.printDatum» c))
      else «Printer.numAtom» (Const.label c) := by
  pr_node

/-- The mirror's printing of a primitive. -/
theorem printStep_prim (defs : List Tree) (cs ps : List Tree) (e : Tree) :
    «Printer.printStep» defs (RoseTree.node Label.prim cs) ps e =
      «Printer.nameAt» «Reader.primNames»
      (Const.label («Prelude.at» cs (leaf 0))) := by
  pr_node

/-- The mirror's printing of a reference. -/
theorem printStep_ref (defs : List Tree) (cs ps : List Tree) (e : Tree) :
    «Printer.printStep» defs (RoseTree.node Label.ref cs) ps e = «Printer.nameAt» defs
      (Const.label («Prelude.at» cs (leaf 0))) := by
  pr_node

/-- The mirror's printing of the form {lit}`pair`. -/
theorem printStep_pair (defs : List Tree) (cs ps : List Tree) (e : Tree) :
    «Printer.printStep» defs (RoseTree.node Label.pair cs) ps e =
      «Printer.kwList1» «Reader.kwPair» ps := rfl

/-- The mirror's printing of the form {lit}`fst`. -/
theorem printStep_fst (defs : List Tree) (cs ps : List Tree) (e : Tree) :
    «Printer.printStep» defs (RoseTree.node Label.fst cs) ps e =
      «Printer.kwList1» «Reader.kwFst» ps := rfl

/-- The mirror's printing of the form {lit}`snd`. -/
theorem printStep_snd (defs : List Tree) (cs ps : List Tree) (e : Tree) :
    «Printer.printStep» defs (RoseTree.node Label.snd cs) ps e =
      «Printer.kwList1» «Reader.kwSnd» ps := rfl

/-- The mirror's printing of the form {lit}`cond`. -/
theorem printStep_cond (defs : List Tree) (cs ps : List Tree) (e : Tree) :
    «Printer.printStep» defs (RoseTree.node Label.cond cs) ps e =
      «Printer.kwList1» «Reader.kwIf» ps := rfl

/-- The mirror's printing of the form {lit}`cons`. -/
theorem printStep_cons (defs : List Tree) (cs ps : List Tree) (e : Tree) :
    «Printer.printStep» defs (RoseTree.node Label.cons cs) ps e =
      «Printer.kwList1» «Reader.kwCons» ps := rfl

/-- The mirror's printing of the form {lit}`nil`. -/
theorem printStep_nil (defs : List Tree) (cs ps : List Tree) (e : Tree) :
    «Printer.printStep» defs (RoseTree.node Label.nil cs) ps e =
      «Printer.kwList1» «Reader.kwNil» («Printer.printTypes» cs) := by
  pr_node

/-- The mirror's printing of the form {lit}`fold`. -/
theorem printStep_fold (defs : List Tree) (cs ps : List Tree) (e : Tree) :
    «Printer.printStep» defs (RoseTree.node Label.fold cs) ps e =
      «Printer.kwList1» «Reader.kwFold» («Printer.printTypes» cs) := by
  pr_node

/-- The mirror's printing of the form {lit}`para`. -/
theorem printStep_para (defs : List Tree) (cs ps : List Tree) (e : Tree) :
    «Printer.printStep» defs (RoseTree.node Label.para cs) ps e =
      «Printer.kwList1» «Reader.kwPara» («Printer.printTypes» cs) := by
  pr_node

/-- The mirror's printing of the form {lit}`iter`. -/
theorem printStep_iter (defs : List Tree) (cs ps : List Tree) (e : Tree) :
    «Printer.printStep» defs (RoseTree.node Label.iter cs) ps e =
      «Printer.kwList1» «Reader.kwIter» («Printer.printTypes» cs) := by
  pr_node

/-- The mirror's printing of the form {lit}`foldr`. -/
theorem printStep_foldr (defs : List Tree) (cs ps : List Tree) (e : Tree) :
    «Printer.printStep» defs (RoseTree.node Label.foldr cs) ps e =
      «Printer.kwList1» «Reader.kwFoldr» («Printer.printTypes» cs) := by
  pr_node

/-- The mirror's printing of the form {lit}`lcase`. -/
theorem printStep_lcase (defs : List Tree) (cs ps : List Tree) (e : Tree) :
    «Printer.printStep» defs (RoseTree.node Label.lcase cs) ps e =
      «Printer.kwList1» «Reader.kwLcase» («Printer.printTypes» cs) := by
  pr_node

/-- Types printed structurally, in a list. -/
theorem printTypes_eq (cs : List Tree) : «Printer.printTypes» cs = cs.map «Printer.printType» := by
  unfold «Printer.printTypes»
  rw [foldr_eq]
  exact cs.rec rfl fun _ _ ih ↦ by rw [List.foldr_cons, ih]; rfl

/-- The mirror's primitive's name at an index of the primitives. -/
theorem at_primNames {k : ℕ} (hk : k < primNames.length) :
    «Prelude.at» «Reader.primNames» (leaf k) = nameTree (primNames.getD k []) := by
  match k, hk with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _
  | 12, _ | 13, _ => rfl

/-- The name at an index of a list of names, as a tree. -/
theorem getD_map_nameTree {defs : List (List Char)} {k : ℕ} (h : k < defs.length) :
    (defs.map nameTree).getD k (leaf 0) = nameTree (defs.getD k []) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h, Option.map_some,
    Option.getD_some, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

/-- A well-formed term printed under binders to a depth. -/
theorem printTerm_eq (defs : List (List Char)) : ∀ (t : Tree) (d : ℕ),
    TermWf defs.length t d = true →
      «Printer.printTerm» (defs.map nameTree) t (leaf d) = sexpTree (printTerm defs t d) :=
  RoseTree.ind fun l cs ih d h ↦ by
    rw [printTerm_mnode, printTerm_node]
    have ih' : ∀ c ∈ cs, ∀ d, TermWf defs.length c d = true →
        «Printer.printTerm» (defs.map nameTree) c (leaf d) = sexpTree (printTerm defs c d) := ih
    rcases termWf_cases h with ⟨rfl, c, rfl, hc, hlt⟩ | ⟨rfl, A, b, rfl, hA, hb⟩ |
      ⟨rfl, f, x, rfl, hf, hx⟩ | ⟨rfl, rfl⟩ | ⟨hl, hcs⟩ | ⟨rfl, c, rfl⟩ | ⟨hl, A, rfl, hA⟩ |
      ⟨hl, A, B, rfl, hA, hB⟩ | ⟨rfl, c, rfl, hc, hlt⟩ | ⟨rfl, c, rfl, hc, hlt⟩
    · simp only [printStep_var, List.map_cons, List.map_nil, at_eq,
        List.getD_cons_zero, label_eq, sub_leaf, binderAtom_eq]
      rfl
    · have hb' := ih' b (List.mem_cons_of_mem _ List.mem_cons_self) (d + 1) hb
      simp only [List.map_cons, List.map_nil, prKids_lam, printStep_lam, at_eq,
        List.getD_cons_zero, List.getD_cons_succ, add_leaf, hb', printType_eq,
        binderAtom_eq, single_eq, kwList1_def, listOf_def, kwAtom_lam]
      simp only [printStep_lam_eq, sexpTree_listS, List.map_cons, List.map_nil]
    · have hf' := ih' f List.mem_cons_self d hf
      have hx' := ih' x (List.mem_cons_of_mem _ List.mem_cons_self) d hx
      rw [prKids_other _ (by decide)]
      simp only [printStep_app, List.map_cons, List.map_nil, hf', hx', listOf_def]
      simp only [printStep_app_eq, sexpTree_listS, List.map_cons, List.map_nil]
    · exact atomOf_eq ['u', 'n', 'i', 't']
    · have hps : ((cs.map fun c ↦ «Printer.printTerm» (defs.map nameTree) c).map
            fun r ↦ r (leaf d)) =
          ((cs.map fun c ↦ (c, printTerm defs c)).map fun r ↦ r.2 d).map sexpTree := by
        simp only [List.map_map, Function.comp_def]
        exact List.map_congr_left fun c hc ↦ ih' c hc d (hcs c hc)
      rcases hl with rfl | rfl | rfl | rfl | rfl
      all_goals
        rw [prKids_other _ (by decide)]
        simp only [printStep_pair, printStep_fst, printStep_snd, printStep_cond,
          printStep_cons, hps, kwList1_def, (printStep_kw_eq defs _ d).1,
          (printStep_kw_eq defs _ d).2.1, (printStep_kw_eq defs _ d).2.2.1,
          (printStep_kw_eq defs _ d).2.2.2.1, (printStep_kw_eq defs _ d).2.2.2.2, sexpTree_listS,
          atomOf_kw]
        rfl
    · obtain ⟨cl, ccs, rfl⟩ : ∃ cl ccs, c = RoseTree.node cl ccs :=
        ⟨_, _, (RoseTree.node_label_children c).symm⟩
      simp only [printStep_quote, List.map_cons, List.map_nil, at_eq,
        List.getD_cons_zero, children_eq, RoseTree.children_node, nonEmpty_eq, label_eq,
        RoseTree.label_node]
      cases ccs with
      | nil => exact numAtom_eq cl
      | cons y ys =>
        have hq : printStep defs Label.quote [(RoseTree.node cl (y :: ys),
            printTerm defs (RoseTree.node cl (y :: ys)))] d =
            listS [atomS ['q', 'u', 'o', 't', 'e'], printDatum (RoseTree.node cl (y :: ys))] := by
          change (if (RoseTree.node cl (y :: ys)).children.isEmpty then _ else _) = _
          rw [RoseTree.children_node]
          rfl
        rw [printDatum_eq, kwList1_def, single_eq, hq, sexpTree_listS]
        rfl
    · rcases hl with rfl | rfl | rfl | rfl
      all_goals
        simp only [printStep_nil, printStep_fold, printStep_para, printStep_iter, List.map_cons,
          List.map_nil, kwList1_def, printTypes_eq, printType_eq,
          atomOf_kw]
        rfl
    · rcases hl with rfl | rfl
      all_goals
        simp only [printStep_foldr, printStep_lcase, List.map_cons,
          List.map_nil, kwList1_def, printTypes_eq, printType_eq, atomOf_kw]
        rfl
    · obtain ⟨k, rfl⟩ : ∃ k, c = leaf k := ⟨c.label, (leaf_label hc).symm⟩
      rw [label_leaf] at hlt
      simp only [printStep_prim, List.map_cons, List.map_nil,
        «Printer.nameAt»]
      rw [show «Prelude.at» [leaf k] (leaf 0) = leaf k from rfl, label_eq, label_leaf,
        at_primNames hlt, atomOf_eq]
      rfl
    · obtain ⟨k, rfl⟩ : ∃ k, c = leaf k := ⟨c.label, (leaf_label hc).symm⟩
      rw [label_leaf] at hlt
      simp only [printStep_ref, List.map_cons, List.map_nil,
        «Printer.nameAt»]
      rw [show «Prelude.at» [leaf k] (leaf 0) = leaf k from rfl, label_eq, label_leaf, at_eq,
        getD_map_nameTree hlt, atomOf_eq]
      rfl

/-! ## Well-formed terms -/

/-- The mirror's test of a kernel type, which the program shares with the kernel's checker. -/
theorem isTy_eq (t : Tree) : «Check.isTy» t = ofBool (Ty.IsTy t) :=
  (rfl : «Check.isTy» t = GebMirror.Kernel.«Check.isTy» t).trans
    (GebTests.Prototypes.CheckMirror.isTy_eq t)

/-- The mirror's test of a single leaf below a bound among trees. -/
theorem leafBelow_eq (cs : List Tree) (n : ℕ) :
    «Printer.leafBelow» cs (leaf n) = ofBool (match cs with
      | [c] => c.children.isEmpty && decide (c.label < n)
      | _ => false) := by
  match cs with
  | [] => rfl
  | [c] =>
    obtain ⟨l, ccs, rfl⟩ : ∃ l ccs, c = RoseTree.node l ccs :=
      ⟨_, _, (RoseTree.node_label_children c).symm⟩
    cases ccs with
    | nil => rfl
    | cons x xs =>
      unfold «Printer.leafBelow»
      simp only [length_eq, eq_leaf, at_eq, children_eq, nonEmpty_eq, List.getD_cons_zero,
        RoseTree.children_node, List.length_singleton]
      rfl
  | _ :: _ :: _ => rfl

/-- The mirror's test of every child's well-formedness at a depth. -/
theorem allAt_eq (cs : List Tree) (F : Tree → Tree → Tree) (G : Tree → ℕ → Bool) (d : ℕ)
    (h : ∀ c ∈ cs, F c (leaf d) = ofBool (G c d)) :
    «Printer.allAt» (cs.map fun c ↦ F c (leaf d)) =
      ofBool ((cs.map fun c ↦ (c, G c)).all (·.2 d)) := by
  unfold «Printer.allAt»
  rw [foldr_eq]
  revert h
  refine List.rec (fun _ ↦ rfl) (fun c cs ih h ↦ ?_) cs
  rw [List.map_cons, List.foldr_cons, ih fun x hx ↦ h x (List.mem_cons_of_mem c hx)]
  simp only [h c List.mem_cons_self, List.map_cons, List.all_cons]
  cases G c d <;> rfl

/-- The mirror's test of a number of children, each a type. -/
theorem tysOf_eq (k : ℕ) (cs : List Tree) :
    «Printer.tysOf» (leaf k) cs = ofBool (cs.length == k && cs.all Ty.IsTy) := by
  unfold «Printer.tysOf»
  rw [length_eq, eq_leaf]
  cases cs.length == k
  · rfl
  · change Const.foldr _ (leaf 1) cs = ofBool (cs.all Ty.IsTy)
    rw [foldr_eq]
    exact List.rec rfl (fun c cs ih ↦ by
      rw [List.foldr_cons, ih, isTy_eq, List.all_cons]
      cases Ty.IsTy c <;> rfl) cs

/-- The well-formedness of a node's children at a binder depth: of an abstraction's body under
one more binder, of the terms of an application or a form at the depth, and of no other child. -/
def wfKids (l : Tree) (rs : List (Tree → Tree)) (e i : Tree) : List Tree :=
  List.foldr (fun (r : Tree → Tree) (c : Tree → Tree → List Tree) (e i : Tree) ↦
      (if (Const.eq l (leaf 9)).label ≠ 0 then
          if (Const.eq i (leaf 1)).label ≠ 0 then r (Const.add e (leaf 1)) else leaf 0
        else if («Prelude.or» (Const.eq l (leaf 10)) («Prelude.or» (Const.eq l (leaf 12))
            («Prelude.or» (Const.eq l (leaf 13)) («Prelude.or» (Const.eq l (leaf 14))
              («Prelude.or» (Const.eq l (leaf 16)) (Const.eq l (leaf 20))))))).label ≠ 0 then r e
        else leaf 0) :: c e (Const.add i (leaf 1)))
    (fun _ _ ↦ []) rs e i

/-- The mirror's well-formedness of a term at a node, from its children's. -/
theorem termWf_mnode (n : Tree) (l : ℕ) (cs : List Tree) (e : Tree) :
    «Printer.termWf» n (RoseTree.node l cs) e =
      «Printer.wfStep» n (RoseTree.node l cs)
        (wfKids (leaf l) (cs.map fun c ↦ «Printer.termWf» n c) e (leaf 0)) e := by
  unfold «Printer.termWf»
  rw [Const.para_node]
  simp only [foldr_eq, wfKids]
  rfl

/-- The well-formedness of the terms of an application or a form, each at the node's depth. -/
theorem wfKids_read (l : ℕ) (hl : l = 10 ∨ l = 12 ∨ l = 13 ∨ l = 14 ∨ l = 16 ∨ l = 20)
    (rs : List (Tree → Tree)) (e : Tree) :
    ∀ i : ℕ, wfKids (leaf l) rs e (leaf i) = rs.map fun r ↦ r e := by
  refine rs.rec (fun _ ↦ rfl) fun r rs ih i ↦ ?_
  have := ih (i + 1)
  simp only [wfKids, List.foldr_cons, List.map_cons, add_leaf] at this ⊢
  rw [this]
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The simplification of a case of the mirror's well-formedness: the node's label and children,
the tests of its arity and labels, and the given lemmas. -/
local macro "wf_simp" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  simp only [«Printer.wfStep», wfStep, label_eq, children_eq, RoseTree.label_node,
    RoseTree.children_node, length_eq, eq_leaf, nonEmpty_eq, tysOf_eq, Nat.reduceBEq, ofBool_true,
    ofBool_false, label_leaf, ne_eq, one_ne_zero, not_false_eq_true, not_true_eq_false,
    ofBool_label_eq_zero, Bool.not_eq_false, ↓reduceIte, Label.var, Label.lam, Label.app,
    Label.unit, Label.pair, Label.fst, Label.snd, Label.cond, Label.cons, Label.quote, Label.nil,
    Label.fold, Label.para, Label.iter, Label.foldr, Label.lcase, Label.prim, Label.ref,
    Nat.reduceEqDiff, or_false, or_true, $ls,*])

/-- One node's well-formedness, as the mirror decides it, from its children's. -/
theorem wfStep_eq (n l d : ℕ) (cs : List Tree) (F : Tree → Tree → Tree)
    (h : ∀ c ∈ cs, ∀ d, F c (leaf d) = ofBool (TermWf n c d)) :
    «Printer.wfStep» (leaf n) (RoseTree.node l cs)
        (wfKids (leaf l) (cs.map F) (leaf d) (leaf 0)) (leaf d) =
      ofBool (wfStep n l (cs.map fun c ↦ (c, TermWf n c)) d) := by
  have hS : (cs.map fun c ↦ (c, TermWf n c)).map Prod.fst = cs := by
    rw [List.map_map]
    exact List.map_id' cs
  have hA : (cs.map F).map (fun r ↦ r (leaf d)) = cs.map fun c ↦ F c (leaf d) := by
    rw [List.map_map]
    rfl
  have hB := allAt_eq cs F (TermWf n) d fun c hc ↦ h c hc d
  match l with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => rfl
  | m + 26 => rfl
  | 9 =>
    match cs, h with
    | [A, b], h =>
      change (if («Check.isTy» A).label ≠ 0 then F b (leaf (d + 1)) else leaf 0) =
        ofBool (Ty.IsTy A && TermWf n b (d + 1))
      rw [isTy_eq, h b (List.mem_cons_of_mem _ List.mem_cons_self) (d + 1)]
      cases Ty.IsTy A <;> rfl
    | [], _ => rfl
    | [_], _ => rfl
    | _ :: _ :: _ :: r, _ =>
      have hk : (r.length + 1 + 1 + 1 == 2) = false := rfl
      wf_simp [List.length_cons, hk]
      all_goals rfl
  | 10 | 12 | 13 | 14 | 16 | 20 =>
    rw [wfKids_read _ (by decide), hA]
    wf_simp [hS, hB]
    all_goals (cases cs.length == 2 <;> rfl)
  | 8 | 11 | 15 | 17 | 18 | 19 | 21 | 22 | 23 | 24 | 25 =>
    wf_simp [hS]
    all_goals first
      | exact leafBelow_eq _ _
      | (cases cs.isEmpty <;> rfl)

/-- A term's well-formedness under binders to a depth, given the number of definitions, as the
mirror decides it. -/
theorem termWf_eq (n : ℕ) : ∀ (t : Tree) (d : ℕ),
    «Printer.termWf» (leaf n) t (leaf d) = ofBool (TermWf n t d) :=
  RoseTree.ind fun l cs ih d ↦ by
    rw [termWf_mnode, termWf_node]
    exact wfStep_eq n l d cs _ ih

end GebTests.Prototypes.FreeTopos.Agreement.Printer

end
