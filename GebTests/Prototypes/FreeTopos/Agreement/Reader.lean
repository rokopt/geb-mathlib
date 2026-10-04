/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Agreement.Printer

set_option doc.verso true in
/-!
# The reader's resolution written in Geb

The resolution of {lit}`bootstrap/reader.geb`, in the Lean the bootstrap compiler emits
({lit}`GebMirror.Metalogic`), agrees with the Lean reader's ({name}`Geb.Kernel.resolve`) at every
well-formed S-expression, in every scope, given any type abbreviations and names of definitions:
numerals, names, types, quoted data and binders, and the forms of terms. An S-expression is
well formed when no atom has children, as every S-expression the readers read is; at an atom with
children the Lean reader's binders read the children and the mirror's do not. With the agreement
of the printer written in Geb ({lit}`GebTests.Prototypes.FreeTopos.Agreement.Printer`), the
retraction of the Lean printer by the Lean reader ({name}`Geb.Kernel.resolve_printTerm`) carries
across: the reader written in Geb inverts the printer written in Geb.

## Main definitions

* {lit}`encTys` — type abbreviations as the reader written in Geb represents them.

## Main statements

* {lit}`numeral_eq`, {lit}`indexOf_eq` — the value of a numeral and the position of a name.
* {lit}`readType_eq`, {lit}`readDatum_eq` — types and quoted data.
* {lit}`resolve_eq` — the resolution of a well-formed S-expression.
* {lit}`readBack_printTerm_eq` — the reader written in Geb inverts the printer written in Geb.

## Tags

reader, resolution, agreement, mirror
-/

set_option doc.verso true

@[expose] public section

open GebMirror.Metalogic

namespace GebTests.Prototypes.FreeTopos.Agreement.Reader

open Geb Geb.Kernel GebTests.Prototypes.FreeTopos.Agreement.Base
  GebTests.Prototypes.FreeTopos.Agreement.Encode GebTests.Prototypes.FreeTopos.Agreement.Fold
  GebTests.Prototypes.FreeTopos.Agreement.Printer
open Geb.Kernel.ModulesTests (sexpTree)
open scoped FinEnum

/-! ## Numerals -/

/-- A digit's value. -/
def digitVal (c : Char) : ℕ := c.toNat - 48

/-- A character is a digit when its code point is from 48 to 57. -/
theorem isDigit_eq (c : Char) : c.isDigit = (decide (48 ≤ c.toNat) && decide (c.toNat ≤ 57)) := by
  simp only [Char.isDigit, Char.toNat]
  rfl

/-- A numeral's value and the power of ten past its digits, read from the right as the mirror
reads it, skipping a character that is not a digit. -/
def valR : List Char → ℕ × ℕ :=
  List.rec (0, 1) fun c _ r ↦ if c.isDigit then (r.1 + digitVal c * r.2, 10 * r.2) else r

/-- The step of the mirror's numeral. -/
def numStep (c : Tree) (s : Tree × (Tree × Tree)) : Tree × (Tree × Tree) :=
  if (Const.lt c (leaf 48)).label ≠ 0 then (leaf 0, s.2)
  else if (Const.lt (leaf 57) c).label ≠ 0 then (leaf 0, s.2)
  else (s.1, (Const.add s.2.1 (Const.mul (Const.sub c (leaf 48)) s.2.2), Const.mul (leaf 10) s.2.2))

/-- The mirror's step at a character that is not a digit. -/
theorem numStep_not_digit {c : Char} (h : c.isDigit = false) (f v p : Tree) :
    numStep (leaf c.toNat) (f, (v, p)) = (leaf 0, (v, p)) := by
  rw [isDigit_eq] at h
  unfold numStep
  by_cases h1 : c.toNat < 48
  · rw [ite_eq_left_of_eq_true _ _
      (eq_true (by rw [lt_leaf, ofBool_label]; exact decide_eq_true h1))]
  · have h48 : 48 ≤ c.toNat := Nat.le_of_not_lt h1
    have h2 : 57 < c.toNat := Nat.lt_of_not_le fun h57 ↦ by
      rw [decide_eq_true h48, decide_eq_true h57] at h
      exact Bool.noConfusion h
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by
        rw [lt_leaf, ofBool_label]; exact fun h' ↦ h1 (of_decide_eq_true h'))),
      ite_eq_left_of_eq_true _ _ (eq_true (by rw [lt_leaf, ofBool_label]; exact decide_eq_true h2))]

/-- The mirror's step at a digit. -/
theorem numStep_digit {c : Char} (h : c.isDigit = true) (f : Tree) (v p : ℕ) :
    numStep (leaf c.toNat) (f, (leaf v, leaf p)) =
      (f, (leaf (v + digitVal c * p), leaf (10 * p))) := by
  rw [isDigit_eq] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  unfold numStep
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by simp [lt_leaf, ofBool]; omega)),
    ite_eq_right_of_eq_false _ _ (eq_false (by simp [lt_leaf, ofBool]; omega))]
  rfl

/-- The mirror's reading of a numeral's characters: whether every one is a digit, its value and
the power of ten past it. -/
theorem foldr_numStep : ∀ s : List Char,
    (charsT s).foldr numStep (leaf 1, (leaf 0, leaf 1)) =
      (ofBool (s.all Char.isDigit), (leaf (valR s).1, leaf (valR s).2)) :=
  List.rec rfl fun c s ih ↦ by
    simp only [charsT, List.map_cons, List.foldr_cons] at ih ⊢
    rw [ih]
    by_cases hd : c.isDigit = true
    · rw [numStep_digit hd]
      simp only [List.all_cons, hd, Bool.true_and, valR, ↓reduceIte]
    · rw [Bool.not_eq_true] at hd
      rw [numStep_not_digit hd]
      simp only [List.all_cons, hd, Bool.false_and, valR, Bool.false_eq_true, ↓reduceIte]
      rfl

/-- The step of {name}`numeral?`. -/
def numFold (n : Option ℕ) (c : Char) : Option ℕ :=
  n.bind fun n ↦ if c.isDigit then some (10 * n + (c.toNat - '0'.toNat)) else none

/-- A failed numeral stays failed. -/
theorem foldl_numFold_none : ∀ s : List Char, s.foldl numFold none = none :=
  List.rec rfl fun _ _ ih ↦ ih

/-- The value of digits after a value, and the power of ten past them. -/
theorem foldl_numFold : ∀ (s : List Char) (a : ℕ), s.foldl numFold (some a) =
    if s.all Char.isDigit then some (a * (valR s).2 + (valR s).1) else none :=
  List.rec (fun a ↦ by simp [valR]) fun c s ih a ↦ by
    rw [List.foldl_cons]
    by_cases hd : c.isDigit = true
    · have hf : numFold (some a) c = some (10 * a + digitVal c) := by
        simp only [numFold, Option.bind_some, hd, ↓reduceIte, digitVal]
        rfl
      rw [hf, ih]
      simp only [List.all_cons, hd, Bool.true_and, valR, ↓reduceIte]
      split
      · congr 1
        change (10 * a + digitVal c) * (valR s).2 + (valR s).1 =
          a * (10 * (valR s).2) + ((valR s).1 + digitVal c * (valR s).2)
        rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_left_comm a 10, Nat.add_assoc,
          Nat.add_comm (digitVal c * _)]
      · rfl
    · rw [Bool.not_eq_true] at hd
      have hf : numFold (some a) c = none := by simp [numFold, hd]
      rw [hf, foldl_numFold_none]
      simp [hd]

/-- The value of a numeral, as the mirror reads it from its characters. -/
theorem numeral_eq (s : List Char) :
    «Reader.numeral» (charsT s) = encOpt ((numeral? s).map leaf) := by
  unfold «Reader.numeral»
  rw [foldr_eq, show (fun (x1 : Tree) (x2 : Tree × (Tree × Tree)) ↦
      if (Const.lt x1 (leaf 48)).label ≠ 0 then (leaf 0, x2.2)
      else if (Const.lt (leaf 57) x1).label ≠ 0 then (leaf 0, x2.2)
      else (x2.1, (Const.add x2.2.1 (Const.mul (Const.sub x1 (leaf 48)) x2.2.2),
        Const.mul (leaf 10) x2.2.2))) = numStep from rfl, foldr_numStep, nonEmpty_eq]
  cases s with
  | nil => rfl
  | cons c cs =>
    have hn : numeral? (c :: cs) = (c :: cs).foldl numFold (some 0) := rfl
    rw [hn, foldl_numFold]
    simp only [charsT, List.map_cons, List.isEmpty_cons, Bool.not_false, ofBool]
    by_cases hall : (c :: cs).all Char.isDigit = true
    · simp only [hall, ↓reduceIte, label_leaf, ne_eq, Option.map_some, Nat.zero_mul,
        Nat.zero_add, some_eq, one_ne_zero, not_false_eq_true]
    · simp only [Bool.not_eq_true] at hall
      simp only [hall, Bool.false_eq_true, ↓reduceIte, label_leaf, ne_eq,
        not_true_eq_false, Option.map_none, none_eq, ite_self]

/-! ## Names -/

/-- Words with the same characters' code points are the same word. -/
theorem charsT_inj {a b : List Char} (h : charsT a = charsT b) : a = b := by
  refine List.map_injective_iff.mpr (fun x y hxy ↦ ?_) h
  exact Char.ext (UInt32.toNat_inj.mp (leaf_inj.mp hxy))

/-- Names with the same trees are the same name. -/
theorem nameTree_inj {a b : List Char} : nameTree a = nameTree b ↔ a = b :=
  ⟨fun h ↦ charsT_inj (by simpa [nameTree, charsT] using congrArg RoseTree.children h),
    congrArg nameTree⟩

/-- The mirror's test of the equality of two names. -/
theorem equal_nameTree (a b : List Char) :
    Const.equal (nameTree a) (nameTree b) = ofBool (a == b) := by
  rw [equal_eq]
  congr 1
  by_cases h : a = b
  · subst h
    rw [decide_eq_true rfl]
    exact (beq_iff_eq.mpr rfl).symm
  · rw [decide_eq_false (fun he ↦ h (nameTree_inj.mp he))]
    exact (beq_eq_false_iff_ne.mpr h).symm

/-- The position of a name among names, as the mirror finds it. -/
theorem indexOf_eq (n : List Char) : ∀ names : List (List Char),
    «Reader.indexOf» (nameTree n) (names.map nameTree) = encOpt ((names.idxOf? n).map leaf) :=
  List.rec rfl fun y ys ih ↦ by
    unfold «Reader.indexOf» at ih ⊢
    rw [List.map_cons, foldr_eq, List.foldr_cons, ← foldr_eq, ih, equal_nameTree, List.idxOf?_cons]
    by_cases h : y = n
    · subst h
      have hy : (y == y) = true := beq_iff_eq.mpr rfl
      simp only [hy, ofBool, ↓reduceIte, label_leaf, ne_eq, one_ne_zero, not_false_eq_true,
        Option.map_some, some_eq]
    · have h' : (n == y) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
      have h'' : (y == n) = false := beq_eq_false_iff_ne.mpr h
      rcases hi : ys.idxOf? n with _ | i
      · simp [h', h'', ofBool, none_eq]
      · simp [h', h'', ofBool, some_eq]

/-- The mirror's names of the primitives. -/
theorem primNames_eq : «Reader.primNames» = primNames.map nameTree := rfl

/-- The mirror's keyword of the unit. -/
theorem kwUnitValue_eq : «Reader.kwUnitValue» = nameTree ['u', 'n', 'i', 't'] := rfl

/-- The children of an atom's encoding. -/
theorem children_atomS (s : List Char) : (sexpTree (atomS s)).children = charsT s := by
  rw [sexpTree_atomS, RoseTree.children_node]

/-- The mirror's name of an atom. -/
theorem nameOf_atomS (s : List Char) : «Reader.nameOf» (sexpTree (atomS s)) = nameTree s := by
  rw [«Reader.nameOf», children_eq, children_atomS]
  rfl

/-- The resolution of an atom: a numeral, a bound name, a definition's name, a primitive's name
or the unit. -/
theorem resolveAtom_eq (tys : TypeNames) (defs scope : List (List Char)) (s : List Char)
    (cs : List (SExp × (List (List Char) → Option Tree))) :
    «Reader.resolveAtom» (defs.map nameTree) (sexpTree (atomS s)) (scope.map nameTree) =
      encOpt (resolveStep tys defs (some s) cs scope) := by
  unfold «Reader.resolveAtom»
  dsimp only
  rw [children_eq, children_atomS, numeral_eq, nameOf_atomS, indexOf_eq, indexOf_eq, primNames_eq,
    indexOf_eq, kwUnitValue_eq, equal_nameTree]
  simp only [resolveStep]
  rcases h1 : numeral? s with _ | n
  · rcases h2 : scope.idxOf? s with _ | i
    · rcases h3 : defs.idxOf? s with _ | j
      · rcases h4 : primNames.idxOf? s with _ | k
        · by_cases h5 : s = ['u', 'n', 'i', 't']
          · subst h5
            rfl
          · have h5' : (s == ['u', 'n', 'i', 't']) = false := beq_eq_false_iff_ne.mpr h5
            simp only [Option.map_none, isSome_eq, Option.isSome_none, ofBool, h5', none_eq]
            rfl
        · simp only [Option.map_none, Option.map_some, isSome_eq, Option.isSome_none,
            Option.isSome_some, get_eq, some_eq]
          rfl
      · simp only [Option.map_none, Option.map_some, isSome_eq, Option.isSome_none,
          Option.isSome_some, get_eq, some_eq]
        rfl
    · simp only [Option.map_none, Option.map_some, isSome_eq, Option.isSome_none,
        Option.isSome_some, get_eq, some_eq]
      rfl
  · simp only [Option.map_some, isSome_eq, Option.isSome_some, get_eq, some_eq]
    rfl

/-! ## Types -/

/-- Type abbreviations as the mirror represents them: each the node of its name and its type. -/
def encTys (tys : TypeNames) : List Tree := tys.map fun p ↦ RoseTree.node 0 [nameTree p.1, p.2]

/-- The subtrees a fold's results carry. -/
theorem rtTrees_eq (rs : List (Tree × Tree)) : «Reader.rtTrees» rs = rs.map Prod.fst := by
  unfold «Reader.rtTrees»
  rw [foldr_eq]
  exact rs.rec rfl fun _ _ ih ↦ by rw [List.foldr_cons, ih]; rfl

/-- The values a fold's results carry. -/
theorem rtValues_eq (rs : List (Tree × Tree)) : «Reader.rtValues» rs = rs.map Prod.snd := by
  unfold «Reader.rtValues»
  rw [foldr_eq]
  exact rs.rec rfl fun _ _ ih ↦ by rw [List.foldr_cons, ih]; rfl

/-- The label of an S-expression's encoding: one for an atom, two for a list. -/
theorem label_sexpTree (e : SExp) : (sexpTree e).label = if e.label.isSome then 1 else 2 := by
  rw [← RoseTree.node_label_children e]
  rcases e.label with _ | s
  · simp [sexpTree, RoseTree.elim_node]
  · simp [sexpTree, RoseTree.elim_node]

/-- Whether an S-expression is an atom of a name. -/
theorem named_eq (e : SExp) (k : List Char) :
    «Reader.named» (sexpTree e) (nameTree k) = ofBool (e.label == some k) := by
  unfold «Reader.named» «Reader.isAtom»
  rw [label_eq, eq_leaf, label_sexpTree]
  rw [← RoseTree.node_label_children e]
  rcases e.label with _ | s
  · simp only [RoseTree.label_node, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    rfl
  · simp only [RoseTree.label_node, Option.isSome_some, ↓reduceIte]
    rw [show ((1 : ℕ) == 1) = true from rfl]
    simp only [ofBool, ↓reduceIte, label_leaf, ne_eq, one_ne_zero, not_false_eq_true]
    rw [show sexpTree (RoseTree.node (some s) e.children) = sexpTree (atomS s) by
      simp [sexpTree, atomS, RoseTree.elim_node], nameOf_atomS, equal_nameTree]
    congr 1

/-- The empty list's head, as the mirror takes it, is no name. -/
theorem named_leaf (k : Tree) : «Reader.named» (leaf 0) k = leaf 0 := rfl

/-- The type an abbreviation names. -/
theorem lookupAbbrev_eq (n : List Char) : ∀ tys : TypeNames,
    «Reader.lookupAbbrev» (nameTree n) (encTys tys) = encOpt (tys.lookup n) :=
  List.rec rfl fun p ps ih ↦ by
    obtain ⟨k, A⟩ := p
    change (if (Const.equal (nameTree n) (Const.child (RoseTree.node 0 [nameTree k, A])
      (leaf 0))).label ≠ 0 then «Prelude.some» (Const.child (RoseTree.node 0 [nameTree k, A])
      (leaf 1)) else «Reader.lookupAbbrev» (nameTree n) (encTys ps)) = _
    rw [ih, child_node, child_node, List.getD_cons_zero, List.getD_cons_succ, List.getD_cons_zero,
      equal_nameTree, List.lookup_cons]
    by_cases h : n = k
    · subst h
      rw [beq_iff_eq.mpr rfl]
      rfl
    · rw [beq_eq_false_iff_ne.mpr h]
      rfl

/-- The step of the mirror's reading of a type. -/
def readTypeFold (x0 : List Tree) (x2 : Tree) (x3 : List (Tree × Tree)) : Tree × Tree :=
  let x4 : Tree := Const.node x2 («Reader.rtTrees» x3)
  let x5 : List Tree := «Reader.rtValues» x3
  (x4,
    if («Reader.isAtom» x4).label ≠ 0 then
      let x6 : Tree := «Reader.nameOf» x4
      if (Const.equal x6 «Reader.kwT»).label ≠ 0 then «Prelude.some» (leaf 0)
      else if (Const.equal x6 «Reader.kwUnit»).label ≠ 0 then «Prelude.some» (leaf 1)
      else «Reader.lookupAbbrev» x6 x0
    else if («Reader.isList» x4).label ≠ 0 then
      let x6 : Tree := «Prelude.at» (Const.children x4) (leaf 0)
      let x7 : Tree := Const.arity x4
      if («Reader.named» x6 «Reader.kwProd»).label ≠ 0 then
        if (Const.eq x7 (leaf 3)).label ≠ 0 then
          «Reader.some2» (leaf 2) («Prelude.at» x5 (leaf 1)) («Prelude.at» x5 (leaf 2))
        else «Prelude.none»
      else if («Reader.named» x6 «Reader.kwArrow»).label ≠ 0 then
        if (Const.eq x7 (leaf 3)).label ≠ 0 then
          «Reader.some2» (leaf 3) («Prelude.at» x5 (leaf 1)) («Prelude.at» x5 (leaf 2))
        else «Prelude.none»
      else if («Reader.named» x6 «Reader.kwList»).label ≠ 0 then
        if (Const.eq x7 (leaf 2)).label ≠ 0 then
          if («Prelude.isSome» («Prelude.at» x5 (leaf 1))).label ≠ 0 then
            «Prelude.some» (Const.node (leaf 4) («Prelude.single» («Prelude.get»
              («Prelude.at» x5 (leaf 1)))))
          else «Prelude.none»
        else «Prelude.none»
      else «Prelude.none»
    else «Prelude.none»)

/-- The mirror's reading of a type is its fold. -/
theorem readType_fold (x0 : List Tree) (x1 : Tree) :
    «Reader.readType» x0 x1 = (Const.fold (readTypeFold x0) x1).2 := rfl

/-- The mirror's reading of a type pairs each node with its value. -/
theorem pairStep_readTypeFold (x0 : List Tree) : PairStep (readTypeFold x0) := fun l rs ↦ by
  simp only [readTypeFold, rtTrees_eq]

/-- The first component of the Lean reading of a type is the atom an S-expression is. -/
theorem elim_readTypeStep_fst (tys : TypeNames) (e : SExp) :
    (RoseTree.elim (readTypeStep tys) e).1 = e.label := by
  rw [← RoseTree.node_label_children e, RoseTree.elim_node, RoseTree.label_node]
  unfold readTypeStep
  split <;> simp_all

/-- The mirror's encoding of an atom, whatever children the S-expression has. -/
theorem sexpTree_atom (s : List Char) (cs : List SExp) :
    sexpTree (RoseTree.node (some s) cs) = sexpTree (atomS s) := by
  simp only [sexpTree, atomS, RoseTree.elim_node]

/-- The mirror's fold over an atom's encoding. -/
theorem fold_atomS {V : Type} {st : Tree → List (Tree × V) → Tree × V} (hst : PairStep st)
    (s : List Char) : Const.fold st (sexpTree (atomS s)) =
      st (leaf 1) ((charsT s).map fun c ↦ (c, (Const.fold st c).2)) := by
  rw [sexpTree_atomS, fold_node, map_fold_pair hst]

/-- An atom read as a type: the base type, the unit, or an abbreviation. -/
theorem readType_atom (tys : TypeNames) (s : List Char) (cs : List SExp) :
    readType tys (RoseTree.node (some s) cs) =
      if s = ['T'] then some tT else if s = ['U', 'n', 'i', 't'] then some tUnit
      else tys.lookup s := by
  unfold readType
  rw [RoseTree.elim_node]
  by_cases h1 : s = ['T']
  · subst h1
    rfl
  · by_cases h2 : s = ['U', 'n', 'i', 't']
    · subst h2
      rfl
    · rw [ite_eq_right_iff.mpr (fun h ↦ absurd h h1), ite_eq_right_iff.mpr (fun h ↦ absurd h h2)]
      unfold readTypeStep
      split
      · exact absurd (Option.some.inj ‹_›) h1
      · exact absurd (Option.some.inj ‹_›) h2
      · rename_i heq
        rw [Option.some.inj heq]
      · exact absurd ‹_› (Option.some_ne_none s)
      · exact absurd ‹_› (Option.some_ne_none s)
      · exact absurd ‹_› (Option.some_ne_none s)
      · exact absurd ‹_› (Option.some_ne_none s)

/-- The mirror's test of an atom on an S-expression's encoding. -/
theorem isAtom_sexpTree (e : SExp) : «Reader.isAtom» (sexpTree e) = ofBool e.label.isSome := by
  unfold «Reader.isAtom»
  rw [label_eq, eq_leaf, label_sexpTree]
  cases e.label.isSome <;> rfl

/-- An atom's encoding is an atom. -/
theorem isAtom_atomS (s : List Char) : «Reader.isAtom» (sexpTree (atomS s)) = leaf 1 := by
  rw [isAtom_sexpTree]
  rfl

/-- A list's encoding is no atom. -/
theorem isAtom_node2 (xs : List Tree) : «Reader.isAtom» (RoseTree.node 2 xs) = leaf 0 := rfl

/-- A list's encoding is a list. -/
theorem isList_node2 (xs : List Tree) : «Reader.isList» (RoseTree.node 2 xs) = leaf 1 := rfl

/-- A list's encoding as the node of its elements' encodings. -/
theorem sexpTree_listS' (cs : List SExp) :
    sexpTree (RoseTree.node none cs) = RoseTree.node 2 (cs.map sexpTree) := sexpTree_listS cs

/-- The mirror's test of a list on an S-expression's encoding. -/
theorem isList_sexpTree (e : SExp) : «Reader.isList» (sexpTree e) = ofBool e.label.isNone := by
  unfold «Reader.isList»
  rw [label_eq, eq_leaf, label_sexpTree]
  cases h : e.label <;> rfl

/-- A list headed by a name that is no type constructor's is no type. -/
theorem readTypeStep_other (tys : TypeNames) (p : List Char) (v : Option Tree)
    (rs : List (Option (List Char) × Option Tree)) (hP : p ≠ ['P', 'r', 'o', 'd'])
    (hA : p ≠ ['A', 'r', 'r', 'o', 'w']) (hL : p ≠ ['L', 'i', 's', 't']) :
    (readTypeStep tys none ((some p, v) :: rs)).2 = none := by
  unfold readTypeStep
  split
  all_goals first
    | rfl
    | contradiction
    | (rename_i heq
       simp only [List.cons.injEq, Prod.mk.injEq, Option.some.injEq] at heq
       first | exact absurd heq.1.1 hP | exact absurd heq.1.1 hA | exact absurd heq.1.1 hL)

/-- A type read from an S-expression, given type abbreviations. -/
theorem fold_readType (tys : TypeNames) : ∀ e : SExp,
    Const.fold (readTypeFold (encTys tys)) (sexpTree e) =
      (sexpTree e, encOpt (readType tys e)) :=
  RoseTree.ind fun a cs ih ↦ by
    refine Prod.ext (fold_pair_fst (pairStep_readTypeFold _) _) ?_
    cases a with
    | some s =>
      rw [sexpTree_atom, fold_atomS (pairStep_readTypeFold _), readType_atom]
      have hr : Const.node (leaf 1) («Reader.rtTrees» ((charsT s).map fun c ↦
          (c, (Const.fold (readTypeFold (encTys tys)) c).2))) = sexpTree (atomS s) := by
        rw [rtTrees_eq, List.map_map, sexpTree_atomS]
        exact congrArg (RoseTree.node 1) (List.map_id' _)
      simp only [readTypeFold, hr, isAtom_atomS, label_leaf, ne_eq, one_ne_zero,
        not_false_eq_true, ↓reduceIte]
      rw [nameOf_atomS, show «Reader.kwT» = nameTree ['T'] from rfl,
        show «Reader.kwUnit» = nameTree ['U', 'n', 'i', 't'] from rfl, equal_nameTree,
        equal_nameTree, lookupAbbrev_eq]
      by_cases h1 : s = ['T']
      · subst h1
        rfl
      · by_cases h2 : s = ['U', 'n', 'i', 't']
        · subst h2
          rfl
        · rw [beq_eq_false_iff_ne.mpr h1, beq_eq_false_iff_ne.mpr h2,
            ite_eq_right_iff.mpr (fun h ↦ absurd h h1), ite_eq_right_iff.mpr (fun h ↦ absurd h h2)]
          rfl
    | none =>
      rw [sexpTree_listS', fold_node, map_fold_pair (pairStep_readTypeFold _)]
      have hrs : (cs.map sexpTree).map (fun c ↦ (c, (Const.fold (readTypeFold (encTys tys)) c).2)) =
          cs.map fun c ↦ (sexpTree c, encOpt (readType tys c)) := by
        rw [List.map_map]
        exact List.map_congr_left fun c hc ↦ by rw [Function.comp_apply, ih c hc]
      have hlean : readType tys (RoseTree.node none cs) =
          (readTypeStep tys none (cs.map fun c ↦ (c.label, readType tys c))).2 := by
        unfold readType
        rw [RoseTree.elim_node]
        congr 2
        exact List.map_congr_left fun c _ ↦ Prod.ext (elim_readTypeStep_fst tys c) rfl
      rw [hrs, hlean]
      simp only [readTypeFold, rtTrees_eq, rtValues_eq, List.map_map, Function.comp_def,
        node_leaf, isAtom_node2, isList_node2, label_leaf, ne_eq, not_true_eq_false,
        one_ne_zero, not_false_eq_true, ↓reduceIte, children_eq, RoseTree.children_node,
        arity_eq, at_eq]
      rw [show «Reader.kwProd» = nameTree ['P', 'r', 'o', 'd'] from rfl,
        show «Reader.kwArrow» = nameTree ['A', 'r', 'r', 'o', 'w'] from rfl,
        show «Reader.kwList» = nameTree ['L', 'i', 's', 't'] from rfl]
      match cs with
      | [] => rfl
      | c1 :: rest =>
        simp only [List.map_cons, List.getD_cons_zero, named_eq, List.length_cons, eq_leaf]
        rcases h1 : c1.label with _ | p
        · rcases rest with _ | ⟨c2, _ | ⟨c3, _ | ⟨c4, r⟩⟩⟩ <;> rfl
        · by_cases hP : p = ['P', 'r', 'o', 'd']
          · subst hP
            rcases rest with _ | ⟨c2, _ | ⟨c3, _ | ⟨c4, r⟩⟩⟩
            · rfl
            · simp only [List.map_cons, List.map_nil]
              rcases readType tys c2 with _ | A <;> rfl
            · simp only [List.map_cons, List.map_nil]
              rcases readType tys c2 with _ | A <;> rcases readType tys c3 with _ | B
              all_goals first
                | rfl
                | (change _ = encOpt (some (tProd A B))
                   rw [tProd_eq]
                   rfl)
            · simp only [List.map_cons]
              rcases readType tys c2 with _ | A <;> rcases readType tys c3 with _ | B <;> rfl
          by_cases hA : p = ['A', 'r', 'r', 'o', 'w']
          · subst hA
            rcases rest with _ | ⟨c2, _ | ⟨c3, _ | ⟨c4, r⟩⟩⟩
            · rfl
            · simp only [List.map_cons, List.map_nil]
              rcases readType tys c2 with _ | A <;> rfl
            · simp only [List.map_cons, List.map_nil]
              rcases readType tys c2 with _ | A <;> rcases readType tys c3 with _ | B
              all_goals first
                | rfl
                | (change _ = encOpt (some (tArrow A B))
                   rw [tArrow_eq]
                   rfl)
            · simp only [List.map_cons]
              rcases readType tys c2 with _ | A <;> rcases readType tys c3 with _ | B <;> rfl
          by_cases hL : p = ['L', 'i', 's', 't']
          · subst hL
            rcases rest with _ | ⟨c2, _ | ⟨c3, _ | ⟨c4, r⟩⟩⟩
            · rfl
            · simp only [List.map_cons, List.map_nil]
              rcases readType tys c2 with _ | A
              · rfl
              · change _ = encOpt (some (tList A))
                rw [tList_eq]
                rfl
            · simp only [List.map_cons, List.map_nil]
              rcases readType tys c2 with _ | A <;> rcases readType tys c3 with _ | B <;> rfl
            · simp only [List.map_cons]
              rcases readType tys c2 with _ | A <;> rcases readType tys c3 with _ | B <;> rfl
          rw [beq_eq_false_iff_ne.mpr (fun h ↦ hP (Option.some.inj h)),
            beq_eq_false_iff_ne.mpr (fun h ↦ hA (Option.some.inj h)),
            beq_eq_false_iff_ne.mpr (fun h ↦ hL (Option.some.inj h)),
            readTypeStep_other tys p _ _ hP hA hL]
          rfl

/-- A type read from an S-expression, given type abbreviations, as the mirror reads it. -/
theorem readType_eq (tys : TypeNames) (e : SExp) :
    «Reader.readType» (encTys tys) (sexpTree e) = encOpt (readType tys e) := by
  rw [readType_fold, fold_readType]

/-! ## Quoted data -/

/-- The mirror's test that two optional trees are both present. -/
theorem both_eq (a b : Option Tree) :
    «Reader.both» (encOpt a) (encOpt b) = ofBool (a.isSome && b.isSome) := by
  cases a <;> cases b <;> rfl

/-- The step of the mirror's values of a list of optional trees. -/
def allStep (x1 : Tree) (x2 : Tree × List Tree) : Tree × List Tree :=
  («Reader.both» x1 x2.1, «Prelude.get» x1 :: x2.2)

/-- The mirror's run over a list of optional trees: whether every one is present, and their
values. -/
theorem foldr_allStep : ∀ xs : List (Option Tree),
    (xs.map encOpt).foldr allStep (leaf 1, []) =
      (ofBool (xs.all Option.isSome), xs.map (·.getD (leaf 0))) :=
  List.rec rfl fun x xs ih ↦ by
    rw [List.map_cons, List.foldr_cons, ih]
    unfold allStep
    dsimp only
    rw [get_encOpt, List.all_cons, List.map_cons]
    cases x <;> cases xs.all Option.isSome <;> rfl

/-- The values of a list of optional trees, when every one is present. -/
theorem mapM_id_eq : ∀ xs : List (Option Tree),
    xs.mapM id = if xs.all Option.isSome then some (xs.map (·.getD (leaf 0))) else none :=
  List.rec rfl fun x xs ih ↦ by
    rw [List.mapM_cons, ih, List.all_cons]
    cases x <;> cases h : xs.all Option.isSome <;> rfl

/-- The mirror's values of a list of optional trees, when every one is present. -/
theorem allSome_eq (xs : List (Option Tree)) :
    «Reader.allSome» (xs.map encOpt) = encOpt ((xs.mapM id).map (RoseTree.node 0)) := by
  unfold «Reader.allSome»
  dsimp only
  rw [foldr_eq, show (fun (x1 : Tree) (x2 : Tree × List Tree) ↦
      («Reader.both» x1 x2.1, «Prelude.get» x1 :: x2.2)) = allStep from rfl, foldr_allStep,
    mapM_id_eq]
  cases xs.all Option.isSome <;> rfl

/-- The step of the mirror's reading of a quoted datum. -/
def datumFold (x1 : Tree) (x2 : List (Tree × Tree)) : Tree × Tree :=
  let x3 : Tree := Const.node x1 («Reader.rtTrees» x2)
  (x3,
    if («Reader.isAtom» x3).label ≠ 0 then
      let x4 : Tree := «Reader.numeral» (Const.children x3)
      if («Prelude.isSome» x4).label ≠ 0 then
        «Prelude.some» (Const.node (leaf 0) («Prelude.single»
          (Const.node («Prelude.get» x4) ([] : List Tree))))
      else «Prelude.some» (Const.node (leaf 0) (Const.children x3))
    else if («Reader.isList» x3).label ≠ 0 then
      Const.lcase (Const.children x3) «Prelude.none» fun (x4 : Tree) (_ : List Tree) ↦
        let x6 : Tree := if («Reader.isAtom» x4).label ≠ 0 then
          «Reader.numeral» (Const.children x4) else «Prelude.none»
        let x7 : Tree := «Reader.allSome» («Prelude.tail» («Reader.rtValues» x2))
        if («Reader.both» x6 x7).label ≠ 0 then
          «Prelude.some» (Const.node (leaf 0) («Prelude.single» (Const.node («Prelude.get» x6)
            (Const.foldr (fun (x8 : Tree) (x9 : List Tree) ↦
              «Prelude.append» (Const.children x8) x9) ([] : List Tree)
              (Const.children («Prelude.get» x7))))))
        else «Prelude.none»
    else «Prelude.none»)

/-- The mirror's reading of a quoted datum pairs each node with its contribution. -/
theorem pairStep_datumFold : PairStep datumFold := fun l rs ↦ by
  simp only [datumFold, rtTrees_eq]

/-- The trees a node of a quoted datum contributes, as the mirror represents them. -/
def encD (o : Option (List Tree)) : Tree := encOpt (o.map (RoseTree.node 0))

/-- The numeral of a quoted datum's node, as Lean reads it: an atom's, if it is a numeral. -/
theorem elim_datumStep_fst (c : SExp) :
    (RoseTree.elim datumStep c).1 = c.label.bind numeral? := by
  rw [← RoseTree.node_label_children c, RoseTree.elim_node, RoseTree.label_node]
  rcases c.label with _ | s
  · unfold datumStep
    split <;> first | rfl | contradiction
  · unfold datumStep
    dsimp only
    rw [Option.bind_some]
    cases numeral? s <;> rfl

/-- The mirror's numeral of a datum's head. -/
theorem headNumeral_eq (c : SExp) :
    (if («Reader.isAtom» (sexpTree c)).label ≠ 0 then «Reader.numeral» (Const.children (sexpTree c))
      else «Prelude.none») = encOpt ((c.label.bind numeral?).map leaf) := by
  rw [← RoseTree.node_label_children c]
  rcases c.label with _ | s
  · rw [sexpTree_listS', isAtom_node2]
    rfl
  · rw [sexpTree_atom, isAtom_atomS, children_eq, children_atomS, numeral_eq]
    rfl

/-- The mirror's numeral of a datum's head, its tests simplified. -/
theorem headNumeral_eq' (c : SExp) :
    (if ¬(«Reader.isAtom» (sexpTree c)).label = 0 then «Reader.numeral» (sexpTree c).children
      else «Prelude.none») = encOpt ((c.label.bind numeral?).map leaf) :=
  headNumeral_eq c

/-- Traversing mapped optional lists is mapping the traversal. -/
theorem mapM_map_option {α β : Type} (f : α → β) : ∀ os : List (Option α),
    (os.map (·.map f)).mapM id = (os.mapM id).map (·.map f) :=
  List.rec rfl fun o os ih ↦ by
    rw [List.map_cons, List.mapM_cons, List.mapM_cons, ih]
    cases o <;> cases os.mapM id <;> rfl

/-- Traversing the second components is traversing the list of them. -/
theorem mapM_snd {α β : Type} : ∀ xs : List (α × Option β),
    xs.mapM Prod.snd = (xs.map Prod.snd).mapM id :=
  List.rec rfl fun x xs ih ↦ by
    rw [List.map_cons, List.mapM_cons, List.mapM_cons, ih]
    rfl

/-- The mirror's joining of lists, each as the node of label zero over it. -/
theorem foldr_append_children : ∀ tss : List (List Tree),
    Const.foldr (fun (x8 : Tree) (x9 : List Tree) ↦ «Prelude.append» x8.children x9) []
      (tss.map (RoseTree.node 0)) = tss.flatten :=
  List.rec rfl fun ts tss ih ↦ by
    rw [List.map_cons, foldr_eq, List.foldr_cons, ← foldr_eq, ih, append_eq,
      RoseTree.children_node, List.flatten_cons]

/-- A list of data contributes the node of its head's numeral over its elements'
contributions. -/
theorem datumStep_none_cons (n1 : Option ℕ) (v1 : Option (List Tree))
    (ds : List (Option ℕ × Option (List Tree))) :
    datumStep none ((n1, v1) :: ds) = match n1 with
      | some l => (none, (ds.mapM Prod.snd).map fun ts ↦ [RoseTree.node l ts.flatten])
      | none => (none, none) := by
  cases n1 <;> rfl

/-- The trees a quoted datum's node contributes, as the mirror reads them. -/
theorem fold_readDatum : ∀ e : SExp,
    Const.fold datumFold (sexpTree e) = (sexpTree e, encD (RoseTree.elim datumStep e).2) :=
  RoseTree.ind fun a cs ih ↦ by
    refine Prod.ext (fold_pair_fst pairStep_datumFold _) ?_
    cases a with
    | some s =>
      rw [sexpTree_atom, fold_atomS pairStep_datumFold, RoseTree.elim_node]
      have hr : Const.node (leaf 1) («Reader.rtTrees» ((charsT s).map fun c ↦
          (c, (Const.fold datumFold c).2))) = sexpTree (atomS s) := by
        rw [rtTrees_eq, List.map_map, sexpTree_atomS]
        exact congrArg (RoseTree.node 1) (List.map_id' _)
      simp only [datumFold, hr, isAtom_atomS, label_leaf, ne_eq, one_ne_zero,
        not_false_eq_true, ↓reduceIte, children_eq, children_atomS, numeral_eq]
      unfold datumStep
      dsimp only
      cases numeral? s with
      | none => rfl
      | some n =>
        rw [Option.map_some, isSome_eq, get_encOpt]
        rfl
    | none =>
      rw [sexpTree_listS', fold_node, map_fold_pair pairStep_datumFold, RoseTree.elim_node]
      have hrs : (cs.map sexpTree).map (fun c ↦ (c, (Const.fold datumFold c).2)) =
          cs.map fun c ↦ (sexpTree c, encD (RoseTree.elim datumStep c).2) := by
        rw [List.map_map]
        exact List.map_congr_left fun c hc ↦ by rw [Function.comp_apply, ih c hc]
      rw [hrs]
      simp only [datumFold, rtTrees_eq, rtValues_eq, List.map_map, Function.comp_def,
        node_leaf, isAtom_node2, isList_node2, label_leaf, ne_eq, not_true_eq_false,
        one_ne_zero, not_false_eq_true, ↓reduceIte, children_eq, RoseTree.children_node]
      match cs with
      | [] => rfl
      | c1 :: rest =>
        rw [List.map_cons, lcase_cons, headNumeral_eq', List.map_cons, tail_eq, List.tail_cons]
        have hv : rest.map (fun c ↦ encD (RoseTree.elim datumStep c).2) =
            (((rest.map fun c ↦ (RoseTree.elim datumStep c).2).map
              (·.map (RoseTree.node 0)))).map encOpt := by
          rw [List.map_map, List.map_map]
          rfl
        rw [hv, allSome_eq, mapM_map_option, List.map_cons,
          show RoseTree.elim datumStep c1 = (c1.label.bind numeral?, (RoseTree.elim datumStep c1).2)
            from Prod.ext (elim_datumStep_fst c1) rfl]
        rw [datumStep_none_cons, mapM_snd, List.map_map]
        rcases c1.label.bind numeral? with _ | l
        · rfl
        · simp only [Function.comp_def]
          rcases (rest.map fun c ↦ (RoseTree.elim datumStep c).2).mapM id with _ | tss
          · rfl
          · simp only [Option.map_some, both_eq, Option.isSome_some, Bool.and_true,
              ofBool, ↓reduceIte, label_leaf, one_ne_zero, not_false_eq_true, get_encOpt,
              Option.getD_some, single_eq, RoseTree.children_node, node_leaf, encD]
            rw [foldr_append_children]
            rfl

/-- The mirror's reading of a quoted datum, through its fold. -/
theorem readDatum_fold (x0 : Tree) : «Reader.readDatum» x0 =
    if («Reader.isAtom» x0).label ≠ 0 then
      (let x1 := «Reader.numeral» (Const.children x0)
       if («Prelude.isSome» x1).label ≠ 0 then «Prelude.some» (Const.node («Prelude.get» x1) [])
       else «Prelude.none»)
    else
      (let x1 := (Const.fold datumFold x0).2
       if («Prelude.isSome» x1).label ≠ 0 then
         «Prelude.some» (Const.child («Prelude.get» x1) (leaf 0))
       else «Prelude.none») := rfl

/-- A list of data contributes no tree or one. -/
theorem elim_datumStep_list (cs : List SExp) :
    (RoseTree.elim datumStep (RoseTree.node none cs)).2 = none ∨
      ∃ t, (RoseTree.elim datumStep (RoseTree.node none cs)).2 = some [t] := by
  rw [RoseTree.elim_node]
  match cs with
  | [] => exact Or.inl rfl
  | c1 :: rest =>
    rw [List.map_cons, show RoseTree.elim datumStep c1 =
      ((RoseTree.elim datumStep c1).1, (RoseTree.elim datumStep c1).2) from rfl,
      datumStep_none_cons]
    rcases (RoseTree.elim datumStep c1).1 with _ | l
    · exact Or.inl rfl
    · rcases (rest.map (RoseTree.elim datumStep)).mapM Prod.snd with _ | tss
      · exact Or.inl rfl
      · exact Or.inr ⟨_, rfl⟩

/-- A quoted datum read from an S-expression, as the mirror reads it. -/
theorem readDatum_eq (e : SExp) : «Reader.readDatum» (sexpTree e) = encOpt (readDatum e) := by
  rw [readDatum_fold, ← RoseTree.node_label_children e]
  rcases e.label with _ | s
  · rw [isAtom_sexpTree, fold_readDatum]
    simp only [RoseTree.label_node, ofBool, ↓reduceIte, label_leaf, ne_eq,
      not_true_eq_false, ↓reduceIte, Option.isSome_none, Bool.false_eq_true]
    unfold readDatum
    rw [RoseTree.label_node]
    rcases elim_datumStep_list e.children with h | ⟨t, h⟩
    · rw [h]
      rfl
    · rw [h]
      simp only [encD, Option.map_some, isSome_eq, Option.isSome_some, ofBool, ↓reduceIte,
        label_leaf, one_ne_zero, not_false_eq_true, get_encOpt, Option.getD_some, child_node,
        List.getD_cons_zero, some_eq]
  · rw [sexpTree_atom, isAtom_atomS, children_eq, children_atomS, numeral_eq]
    change _ = encOpt ((numeral? s).map leaf)
    rcases numeral? s with _ | n
    · rfl
    · rfl

/-! ## Resolution -/

/-- The subtrees the resolution's results carry. -/
theorem rrTrees_eq (rs : List (Tree × (List Tree → Tree))) :
    «Reader.rrTrees» rs = rs.map Prod.fst := by
  unfold «Reader.rrTrees»
  rw [foldr_eq]
  exact rs.rec rfl fun _ _ ih ↦ by rw [List.foldr_cons, ih]; rfl

/-- The resolutions of the results in a scope. -/
theorem rrApply_eq (rs : List (Tree × (List Tree → Tree))) (s : List Tree) :
    «Reader.rrApply» rs s = rs.map fun r ↦ r.2 s := by
  unfold «Reader.rrApply»
  rw [foldr_eq]
  exact rs.rec rfl fun _ _ ih ↦ by rw [List.foldr_cons, ih]; rfl

/-- The results after the first ones. -/
theorem iter_tail (n : ℕ) : ∀ rs : List (Tree × (List Tree → Tree)),
    Const.iter «Reader/RRs.tail» rs (leaf n) = rs.drop n := by
  refine Nat.rec (fun _ ↦ rfl) (fun n ih rs ↦ ?_) n
  change Nat.repeat «Reader/RRs.tail» (n + 1) rs = rs.drop (n + 1)
  rw [repeat_succ']
  cases rs with
  | nil => exact (ih []).trans (List.drop_nil)
  | cons r rs => exact ih rs

/-- The resolution of the result at a position. -/
theorem rrAt_eq (rs : List (Tree × (List Tree → Tree))) (i : ℕ) (s : List Tree) :
    «Reader.rrAt» rs (leaf i) s = match rs.drop i with
      | [] => «Prelude.none»
      | r :: _ => r.2 s := by
  unfold «Reader.rrAt»
  rw [iter_tail]
  cases rs.drop i <;> rfl

/-- The resolutions of the results from a position. -/
theorem argsOf_eq (rs : List (Tree × (List Tree → Tree))) (n : ℕ) (s : List Tree) :
    «Reader.argsOf» rs (leaf n) s = «Reader.allSome» ((rs.drop n).map fun r ↦ r.2 s) := by
  unfold «Reader.argsOf»
  rw [iter_tail, rrApply_eq]

/-- The mirror's application. -/
theorem app_eq (f x : Tree) : «Reader.app» f x = mk Label.app [f, x] := rfl

/-- The mirror's applications of a term to arguments in turn. -/
theorem apps_eq (f : Tree) (xs : List Tree) : «Reader.apps» f xs = Kernel.apps f xs := by
  unfold «Reader.apps» Kernel.apps
  rw [reverse_eq, foldr_eq, List.foldr_reverse]
  rfl

/-- Traversing a mapped list is traversing by the composite. -/
theorem mapM_map_id {α β : Type} (f : α → Option β) : ∀ xs : List α,
    (xs.map f).mapM id = xs.mapM f :=
  List.rec rfl fun x xs ih ↦ by rw [List.map_cons, List.mapM_cons, List.mapM_cons, ih]; rfl

/-- The mirror's node of a label over a present tree. -/
theorem some1_eq (l : ℕ) (o : Option Tree) :
    «Reader.some1» (leaf l) (encOpt o) = encOpt (o.map fun t ↦ mk l [t]) := by
  cases o <;> rfl

/-- The mirror's node of a label over present trees. -/
theorem mkArgs_eq (l : ℕ) (o : Option (List Tree)) :
    «Reader.mkArgs» (leaf l) (encOpt (o.map (RoseTree.node 0))) = encOpt (o.map (mk l)) := by
  cases o with
  | none => rfl
  | some ts =>
    unfold «Reader.mkArgs»
    rw [Option.map_some, isSome_eq, get_encOpt]
    simp only [Option.isSome_some, ofBool, ↓reduceIte, label_leaf, ne_eq, one_ne_zero,
      not_false_eq_true, Option.getD_some, children_eq, RoseTree.children_node, node_leaf,
      some_eq, Option.map_some]

/-- The mirror's applications of a present term to present arguments. -/
theorem appsOpt_eq (f : Option Tree) (o : Option (List Tree)) :
    «Reader.appsOpt» (encOpt f) (encOpt (o.map (RoseTree.node 0))) =
      encOpt (do Kernel.apps (← f) (← o)) := by
  cases f with
  | none => rfl
  | some f =>
    cases o with
    | none => rfl
    | some ts =>
      unfold «Reader.appsOpt»
      rw [Option.map_some, both_eq, get_encOpt, get_encOpt]
      simp only [Option.isSome_some, Bool.and_self, ofBool, ↓reduceIte, label_leaf, ne_eq,
        one_ne_zero, not_false_eq_true, Option.getD_some, children_eq, RoseTree.children_node,
        apps_eq, some_eq]
      rfl

/-- The resolutions of encoded results from a position, as the Lean reader's. -/
theorem argsOf_map (cs : List (SExp × (List (List Char) → Option Tree)))
    (G : SExp × (List (List Char) → Option Tree) → List Tree → Tree)
    (hG : ∀ c ∈ cs, ∀ scope, G c (scope.map nameTree) = encOpt (c.2 scope))
    (n : ℕ) (scope : List (List Char)) :
    «Reader.argsOf» (cs.map fun c ↦ (sexpTree c.1, G c)) (leaf n) (scope.map nameTree) =
      encOpt (((cs.drop n).mapM fun (c : SExp × (List (List Char) → Option Tree)) ↦
        c.2 scope).map (RoseTree.node 0)) := by
  rw [argsOf_eq, ← List.map_drop, List.map_map]
  have : (cs.drop n).map ((fun r ↦ r.2 (scope.map nameTree)) ∘ fun c ↦ (sexpTree c.1, G c)) =
      ((cs.drop n).map fun c ↦ c.2 scope).map encOpt := by
    rw [List.map_map]
    exact List.map_congr_left fun c hc ↦ hG c (List.mem_of_mem_drop hc) scope
  rw [this, allSome_eq, mapM_map_id]

/-- The resolution of the encoded result at a position, as the Lean reader's. -/
theorem rrAt_map (cs : List (SExp × (List (List Char) → Option Tree)))
    (G : SExp × (List (List Char) → Option Tree) → List Tree → Tree)
    (hG : ∀ c ∈ cs, ∀ scope, G c (scope.map nameTree) = encOpt (c.2 scope))
    (i : ℕ) (scope : List (List Char)) :
    «Reader.rrAt» (cs.map fun c ↦ (sexpTree c.1, G c)) (leaf i) (scope.map nameTree) =
      encOpt (match cs.drop i with
        | [] => none
        | c :: _ => c.2 scope) := by
  rw [rrAt_eq, ← List.map_drop]
  rcases h : cs.drop i with _ | ⟨c, _⟩
  · rfl
  · exact hG c (List.mem_of_mem_drop (h ▸ List.mem_cons_self)) scope

/-! ## Binders -/

/-- A well-formed atom has no children. -/
theorem children_of_wf_atom {s : List Char} {cs : List SExp}
    (h : Document.SExp.wf (RoseTree.node (some s) cs)) : cs = [] := by
  rw [Document.SExp.wf_atom, List.isEmpty_iff] at h
  exact h

/-- The binders of an abstraction, as the mirror takes them. -/
theorem binders_eq (b : SExp) (hb : Document.SExp.wf b) :
    «Reader.binders» (sexpTree b) = (binders b).map sexpTree := by
  obtain ⟨a, cs, rfl⟩ : ∃ a cs, b = RoseTree.node a cs :=
    ⟨_, _, (RoseTree.node_label_children b).symm⟩
  cases a with
  | none =>
    unfold «Reader.binders» binders
    rw [sexpTree_listS', isList_node2, RoseTree.children_node]
    simp only [label_leaf, ne_eq, one_ne_zero, not_false_eq_true, ↓reduceIte, arity_eq,
      RoseTree.children_node, List.length_map, eq_leaf, children_eq]
    match cs with
    | [] => rfl
    | [c] => rfl
    | [x, y] =>
      rw [child_node, List.map_cons, List.getD_cons_zero, isAtom_sexpTree]
      change _ = List.map sexpTree (if x.label.isSome then [RoseTree.node none [x, y]] else [x, y])
      cases x.label.isSome
      · rfl
      · change _ = [sexpTree (RoseTree.node none [x, y])]
        rw [sexpTree_listS']
        rfl
    | x :: y :: z :: r => rfl
  | some s =>
    rw [children_of_wf_atom hb, sexpTree_atom]
    rfl

/-- One binder read, as Lean reads it: a name with a type. -/
def leanBinder (tys : TypeNames) (c : SExp) : Option (List Char × Tree) :=
  match c.children with
  | [x, A] => do some (← x.label, ← readType tys A)
  | _ => none

/-- A name with a type, as the mirror represents it. -/
def encB (p : List Char × Tree) : Tree := RoseTree.node 0 [nameTree p.1, p.2]

/-- One binder read, as the mirror reads it. -/
def binderT (x0 : List Tree) (x2 : Tree) : Tree :=
  if («Reader.isList» x2).label ≠ 0 then
    if (Const.eq (Const.arity x2) (leaf 2)).label ≠ 0 then
      if («Reader.isAtom» (Const.child x2 (leaf 0))).label ≠ 0 then
        let x4 : Tree := «Reader.readType» x0 (Const.child x2 (leaf 1))
        if («Prelude.isSome» x4).label ≠ 0 then
          «Prelude.some» («Reader.node2» (leaf 0) («Reader.nameOf» (Const.child x2 (leaf 0)))
            («Prelude.get» x4))
        else «Prelude.none»
      else «Prelude.none»
    else «Prelude.none»
  else «Prelude.none»

/-- The mirror's reading of binders is its reading of each. -/
theorem readBinders_map (x0 x1 : List Tree) :
    «Reader.readBinders» x0 x1 = «Reader.allSome» (x1.map (binderT x0)) := by
  unfold «Reader.readBinders»
  rw [foldr_eq]
  congr 1
  exact x1.rec rfl fun _ _ ih ↦ by rw [List.foldr_cons, ih]; rfl

/-- One well-formed binder read, as the mirror reads it. -/
theorem binderT_eq (tys : TypeNames) (c : SExp) (hc : Document.SExp.wf c) :
    binderT (encTys tys) (sexpTree c) = encOpt ((leanBinder tys c).map encB) := by
  obtain ⟨a, cs, rfl⟩ : ∃ a cs, c = RoseTree.node a cs :=
    ⟨_, _, (RoseTree.node_label_children c).symm⟩
  cases a with
  | none =>
    unfold binderT leanBinder
    rw [sexpTree_listS', isList_node2, RoseTree.children_node]
    simp only [label_leaf, ne_eq, one_ne_zero, not_false_eq_true, ↓reduceIte, arity_eq,
      RoseTree.children_node, List.length_map, eq_leaf]
    match cs with
    | [] => rfl
    | [x] => rfl
    | [x, A] =>
      simp only [child_node, List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ,
        isAtom_sexpTree, readType_eq]
      rw [← RoseTree.node_label_children x]
      rcases x.label with _ | n
      · rfl
      · simp only [RoseTree.label_node, Option.isSome_some, ofBool, ↓reduceIte, label_leaf,
          one_ne_zero, not_false_eq_true]
        rw [sexpTree_atom, nameOf_atomS]
        rcases readType tys A with _ | B
        · rfl
        · rfl
    | x :: y :: z :: r => rfl
  | some s =>
    rw [children_of_wf_atom hc, sexpTree_atom]
    rfl

/-- Well-formed binders read, as the mirror reads them. -/
theorem readBinders_eq (tys : TypeNames) (bs : List SExp) (hbs : ∀ c ∈ bs, Document.SExp.wf c) :
    «Reader.readBinders» (encTys tys) (bs.map sexpTree) =
      encOpt ((bs.mapM (leanBinder tys)).map fun ps ↦ RoseTree.node 0 (ps.map encB)) := by
  rw [readBinders_map, List.map_map]
  have : bs.map (binderT (encTys tys) ∘ sexpTree) =
      ((bs.map (leanBinder tys)).map (·.map encB)).map encOpt := by
    rw [List.map_map, List.map_map]
    exact List.map_congr_left fun c hc ↦ binderT_eq tys c (hbs c hc)
  rw [this, allSome_eq, mapM_map_option, mapM_map_id, Option.map_map]
  rfl

/-! ## Lists -/

/-- The mirror's keywords of the forms of terms, as names. -/
theorem kw_names : «Reader.kwLam» = nameTree ['l', 'a', 'm'] ∧
    «Reader.kwLet» = nameTree ['l', 'e', 't'] ∧
    «Reader.kwPair» = nameTree ['p', 'a', 'i', 'r'] ∧
    «Reader.kwFst» = nameTree ['f', 's', 't'] ∧
    «Reader.kwSnd» = nameTree ['s', 'n', 'd'] ∧
    «Reader.kwIf» = nameTree ['i', 'f'] ∧
    «Reader.kwQuote» = nameTree ['q', 'u', 'o', 't', 'e'] ∧
    «Reader.kwCons» = nameTree ['c', 'o', 'n', 's'] ∧
    «Reader.kwNil» = nameTree ['n', 'i', 'l'] ∧
    «Reader.kwFold» = nameTree ['f', 'o', 'l', 'd'] ∧
    «Reader.kwPara» = nameTree ['p', 'a', 'r', 'a'] ∧
    «Reader.kwIter» = nameTree ['i', 't', 'e', 'r'] ∧
    «Reader.kwFoldr» = nameTree ['f', 'o', 'l', 'd', 'r'] ∧
    «Reader.kwLcase» = nameTree ['l', 'c', 'a', 's', 'e'] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The mirror's node of a label over two present trees. -/
theorem some2_eq (l : ℕ) (a b : Option Tree) :
    «Reader.some2» (leaf l) (encOpt a) (encOpt b) = encOpt (do some (mk l [← a, ← b])) := by
  cases a <;> cases b <;> rfl

/-- One is below a length of two or more. -/
theorem lt_one_leaf (n : ℕ) : Const.lt (leaf 1) (leaf (n + 1 + 1)) = leaf 1 := by
  rw [lt_leaf, decide_eq_true (Nat.succ_lt_succ (Nat.succ_pos n))]
  rfl

/-- Two is below a length of three or more. -/
theorem lt_two_leaf (n : ℕ) : Const.lt (leaf 2) (leaf (n + 1 + 1 + 1)) = leaf 1 := by
  rw [lt_leaf, decide_eq_true (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos n)))]
  rfl

/-- The binders of a well-formed S-expression are well formed. -/
theorem wf_binders (b : SExp) (hb : Document.SExp.wf b) : ∀ c ∈ binders b, Document.SExp.wf c := by
  obtain ⟨a, cs, rfl⟩ : ∃ a cs, b = RoseTree.node a cs :=
    ⟨_, _, (RoseTree.node_label_children b).symm⟩
  cases a with
  | some s =>
    rw [children_of_wf_atom hb]
    intro c hc
    exact absurd hc List.not_mem_nil
  | none =>
    have hcs : ∀ c ∈ cs, Document.SExp.wf c := List.all_eq_true.mp (by
      rw [Document.SExp.wf_list] at hb
      exact hb)
    unfold binders
    rw [RoseTree.children_node]
    match cs, hcs with
    | [x, y], hcs =>
      dsimp only
      split
      · intro c hc
        rw [List.mem_singleton] at hc
        subst hc
        exact hb
      · exact hcs
    | [], hcs => exact hcs
    | [x], hcs => exact hcs
    | x :: y :: z :: r, hcs => exact hcs

/-- The names of encoded binders. -/
theorem foldr_child0 (ps : List (List Char × Tree)) :
    Const.foldr (fun (x9 : Tree) (x10 : List Tree) ↦ Const.child x9 (leaf 0) :: x10) []
      (ps.map encB) = ps.map (nameTree ∘ Prod.fst) := by
  rw [foldr_eq]
  exact ps.rec rfl fun p ps ih ↦ by
    rw [List.map_cons, List.foldr_cons, ih, List.map_cons, encB, child_node]
    rfl

/-- The abstractions over encoded binders. -/
theorem foldr_lam (ps : List (List Char × Tree)) (t : Tree) :
    Const.foldr (fun (x10 : Tree) (x11 : Tree) ↦ «Reader.node2» (leaf 9) (Const.child x10 (leaf 1))
      x11) t (ps.map encB) = ps.foldr (fun p u ↦ mk Label.lam [p.2, u]) t := by
  rw [foldr_eq]
  exact ps.rec rfl fun p ps ih ↦ by
    rw [List.map_cons, List.foldr_cons, ih, List.foldr_cons, encB, child_node]
    rfl

/-- The resolution of a list whose head is no keyword, as the mirror resolves it: the head applied
to the rest. -/
theorem resolveList_app (tys : TypeNames) (defs : List (List Char)) (h : SExp)
    (rh : List (List Char) → Option Tree) (rest : List (SExp × (List (List Char) → Option Tree)))
    (G : SExp × (List (List Char) → Option Tree) → List Tree → Tree)
    (hG : ∀ c ∈ (h, rh) :: rest, ∀ scope, G c (scope.map nameTree) = encOpt (c.2 scope))
    (scope : List (List Char)) (hh : HeadOk h) :
    «Reader.appsOpt» («Reader.rrAt» (((h, rh) :: rest).map fun c ↦ (sexpTree c.1, G c)) (leaf 0)
        (scope.map nameTree))
      («Reader.argsOf» (((h, rh) :: rest).map fun c ↦ (sexpTree c.1, G c)) (leaf 1)
        (scope.map nameTree)) =
      encOpt (resolveStep tys defs none ((h, rh) :: rest) scope) := by
  rw [rrAt_map _ G hG, argsOf_map _ G hG, appsOpt_eq, resolveStep_app _ _ _ _ _ _ hh]
  rfl

/-- The resolution of a list of resolved elements, as the mirror resolves it. -/
theorem resolveList_eq (tys : TypeNames) (defs : List (List Char))
    (cs : List (SExp × (List (List Char) → Option Tree)))
    (G : SExp × (List (List Char) → Option Tree) → List Tree → Tree)
    (hG : ∀ c ∈ cs, ∀ scope, G c (scope.map nameTree) = encOpt (c.2 scope))
    (hwf : ∀ c ∈ cs, Document.SExp.wf c.1) (scope : List (List Char)) :
    «Reader.resolveList» (encTys tys) (RoseTree.node 2 (cs.map fun c ↦ sexpTree c.1))
        (cs.map fun c ↦ (sexpTree c.1, G c)) (scope.map nameTree) =
      encOpt (resolveStep tys defs none cs scope) := by
  unfold «Reader.resolveList»
  dsimp only
  simp only [children_eq, RoseTree.children_node, arity_eq, List.length_map, eq_leaf, at_eq]
  match cs, hG, hwf with
  | [], _, _ => rfl
  | (h, rh) :: rest, hG, hwf =>
    obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14⟩ := kw_names
    simp only [rrAt_map _ G hG, argsOf_map _ G hG]
    simp only [List.map_cons, List.getD_cons_zero, List.length_cons, k1, k2, k3, k4, k5, k6, k7,
      k8, k9, k10, k11, k12, k13, k14, named_eq, List.drop_zero, List.drop_succ_cons]
    have hdef : HeadOk h → encOpt (do Kernel.apps (← rh scope) (← rest.mapM fun c ↦ c.2 scope)) =
        encOpt (resolveStep tys defs none ((h, rh) :: rest) scope) := fun hh ↦ by
      rw [resolveStep_app _ _ _ _ _ _ hh]
    by_cases hb : (h.label.all fun k ↦ !formKeywords.contains k) = true
    · have hk : HeadOk h := fun k hl hm ↦ by
        rw [hl, Option.all_some, Bool.not_eq_true'] at hb
        exact Bool.false_ne_true (hb.symm.trans (List.contains_iff_mem.mpr hm))
      have hn : ∀ k ∈ formKeywords, (h.label == some k) = false := fun k hk' ↦
        beq_eq_false_iff_ne.mpr fun he ↦ hk k he hk'
      simp only [formKeywords, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hn
      obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14⟩ := hn
      have h0 : (rest.length + 1 == 0) = false := rfl
      simp only [n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, ofBool, h0,
        Bool.false_eq_true, ↓reduceIte, label_leaf, ne_eq, not_true_eq_false]
      rw [appsOpt_eq]
      exact hdef hk
    · obtain ⟨k, hl, hm⟩ : ∃ k, h.label = some k ∧ k ∈ formKeywords := by
        rcases hx : h.label with _ | k
        · rw [hx] at hb
          exact absurd rfl hb
        · rw [hx, Option.all_some, Bool.not_eq_true, Bool.not_eq_false', List.contains_iff_mem]
            at hb
          exact ⟨k, rfl, hb⟩
      have h0 : (rest.length + 1 == 0) = false := rfl
      simp only [formKeywords, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl
      all_goals
        simp (config := {decide := true}) only [hl, ofBool, h0, Bool.false_eq_true, ↓reduceIte,
          label_leaf, ne_eq]
      · rcases rest with _ | ⟨⟨b, rb⟩, _ | ⟨⟨bd, rbd⟩, _ | ⟨c3, r⟩⟩⟩
        · simp (config := {decide := true}) only [↓reduceIte]
          rw [appsOpt_eq]
          unfold resolveStep
          dsimp only
          rw [hl]
          rfl
        · simp (config := {decide := true}) only [List.length_cons, List.length_nil, ↓reduceIte]
          rw [appsOpt_eq]
          unfold resolveStep
          dsimp only
          rw [hl]
          rfl
        · simp (config := {decide := true}) only [List.length_cons, List.length_nil, ↓reduceIte,
            List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero]
          have hwfb : Document.SExp.wf b := hwf (b, rb) (List.mem_cons_of_mem _ List.mem_cons_self)
          rw [binders_eq b hwfb, readBinders_eq tys _ (wf_binders b hwfb)]
          rw [show resolveStep tys defs none [(h, rh), (b, rb), (bd, rbd)] scope =
              (do
                let bs ← (binders b).mapM (leanBinder tys)
                if bs.isEmpty then none
                else
                  let t ← rbd ((bs.map Prod.fst).reverse ++ scope)
                  some (bs.foldr (fun p u ↦ mk Label.lam [p.2, u]) t)) by
            unfold resolveStep
            dsimp only
            rw [hl]
            rfl]
          rcases (binders b).mapM (leanBinder tys) with _ | ps
          · rfl
          · simp only [Option.map_some, isSome_eq, Option.isSome_some, ofBool, ↓reduceIte,
              label_leaf, get_encOpt, Option.getD_some, RoseTree.children_node,
              nonEmpty_eq, List.isEmpty_map, foldr_child0, reverse_eq, append_eq,
              Option.bind_eq_bind, Option.bind_some]
            cases hps : ps.isEmpty
            · have hr := rrAt_map _ G hG 2 (ps.reverse.map Prod.fst ++ scope)
              simp only [List.map_cons, List.map_nil, List.map_append, List.map_map,
                List.drop_succ_cons, List.drop_zero] at hr
              rw [← List.map_reverse, hr, List.map_reverse]
              rcases rbd ((ps.map Prod.fst).reverse ++ scope) with _ | t
              · rfl
              · simp only [isSome_eq, Option.isSome_some, ofBool, ↓reduceIte, label_leaf,
                  get_encOpt, Option.getD_some, foldr_lam]
                rfl
            · rfl
        · simp (config := {decide := true}) only [List.length_cons]
          rw [appsOpt_eq]
          unfold resolveStep
          dsimp only
          rw [hl]
          rfl
      · rcases rest with _ | ⟨⟨x, rx⟩, _ | ⟨⟨A, rA⟩, _ | ⟨⟨e, re⟩, _ | ⟨⟨bd, rbd⟩, _ | ⟨c5, r⟩⟩⟩⟩⟩
        · simp (config := {decide := true}) only [↓reduceIte]
          rw [appsOpt_eq]
          unfold resolveStep
          dsimp only
          rw [hl]
          rfl
        · simp (config := {decide := true}) only [List.length_cons, List.length_nil, ↓reduceIte]
          rw [appsOpt_eq]
          unfold resolveStep
          dsimp only
          rw [hl]
          rfl
        · simp (config := {decide := true}) only [List.length_cons, List.length_nil, ↓reduceIte]
          rw [appsOpt_eq]
          unfold resolveStep
          dsimp only
          rw [hl]
          rfl
        · simp (config := {decide := true}) only [List.length_cons, List.length_nil, ↓reduceIte]
          rw [appsOpt_eq]
          unfold resolveStep
          dsimp only
          rw [hl]
          rfl
        · simp (config := {decide := true}) only [List.length_cons, List.length_nil, ↓reduceIte,
            List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero,
            List.drop_succ_cons, List.drop_zero, readType_eq, isAtom_sexpTree]
          rw [show resolveStep tys defs none [(h, rh), (x, rx), (A, rA), (e, re), (bd, rbd)] scope =
              (do
                let name ← x.label
                some (mk Label.app [mk Label.lam [← readType tys A, ← rbd (name :: scope)],
                  ← re scope])) by
            unfold resolveStep
            dsimp only
            rw [hl]
            rfl]
          obtain ⟨a, xs, rfl⟩ : ∃ a xs, x = RoseTree.node a xs :=
            ⟨_, _, (RoseTree.node_label_children x).symm⟩
          cases a with
          | none => rfl
          | some n =>
            simp only [RoseTree.label_node, Option.isSome_some, ofBool, ↓reduceIte, label_leaf,
              Option.bind_eq_bind, Option.bind_some]
            have hr := rrAt_map _ G hG 4 (n :: scope)
            simp only [List.map_cons, List.map_nil, List.drop_succ_cons, List.drop_zero] at hr
            rw [sexpTree_atom] at hr
            rw [sexpTree_atom, nameOf_atomS, hr]
            rcases readType tys A with _ | A' <;> rcases rbd (n :: scope) with _ | B' <;>
              rcases re scope with _ | E' <;> rfl
        · simp (config := {decide := true}) only [List.length_cons]
          rw [appsOpt_eq]
          unfold resolveStep
          dsimp only
          rw [hl]
          rfl
      · rw [mkArgs_eq]
        unfold resolveStep
        dsimp only
        rw [hl]
        rfl
      · rw [mkArgs_eq]
        unfold resolveStep
        dsimp only
        rw [hl]
        rfl
      · rw [mkArgs_eq]
        unfold resolveStep
        dsimp only
        rw [hl]
        rfl
      · rw [mkArgs_eq]
        unfold resolveStep
        dsimp only
        rw [hl]
        rfl
      · rcases rest with _ | ⟨⟨d, rd⟩, _ | ⟨c2, r⟩⟩
        · simp (config := {decide := true}) only [↓reduceIte]
          rw [appsOpt_eq]
          unfold resolveStep
          dsimp only
          rw [hl]
          rfl
        · simp (config := {decide := true}) only [List.length_nil, List.length_cons,
            ↓reduceIte, List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero,
            readDatum_eq, some1_eq]
          unfold resolveStep
          dsimp only
          rw [hl]
          rfl
        · simp (config := {decide := true}) only [List.length_cons]
          rw [appsOpt_eq]
          unfold resolveStep
          dsimp only
          rw [hl]
          rfl
      · rw [mkArgs_eq]
        unfold resolveStep
        dsimp only
        rw [hl]
        rfl
      · rcases rest with _ | ⟨⟨d, rd⟩, _ | ⟨c2, r⟩⟩
        · simp (config := {decide := true}) only [↓reduceIte]
          rw [appsOpt_eq]
          unfold resolveStep
          dsimp only
          rw [hl]
          rfl
        · simp (config := {decide := true}) only [List.length_nil, List.length_cons,
            ↓reduceIte, List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero,
            readType_eq, some1_eq]
          unfold resolveStep
          dsimp only
          rw [hl]
          rfl
        · simp (config := {decide := true}) only [List.length_cons]
          rw [appsOpt_eq]
          unfold resolveStep
          dsimp only
          rw [hl]
          rfl
      · rcases rest with _ | ⟨⟨A, rA⟩, xs⟩
        · simp (config := {decide := true}) only [↓reduceIte]
          rw [appsOpt_eq]
          unfold resolveStep
          dsimp only
          rw [hl]
          rfl
        · simp only [List.length_cons, lt_one_leaf, label_leaf, one_ne_zero,
            not_false_eq_true, ↓reduceIte, List.map_cons, List.getD_cons_succ, List.getD_cons_zero,
            readType_eq, List.drop_succ_cons, List.drop_zero, isSome_eq]
          rw [show resolveStep tys defs none ((h, rh) :: (A, rA) :: xs) scope =
              (do Kernel.apps (mk Label.fold [← readType tys A]) (← xs.mapM fun c ↦ c.2 scope)) by
            unfold resolveStep
            dsimp only
            rw [hl]
            rfl]
          rcases readType tys A with _ | B
          · rfl
          · simp only [Option.isSome_some, ofBool, ↓reduceIte, label_leaf, one_ne_zero,
              not_false_eq_true, get_encOpt, Option.getD_some, single_eq, node_leaf]
            rw [show «Prelude.some» (RoseTree.node 17 [B]) = encOpt (some (mk 17 [B])) from rfl,
              appsOpt_eq]
            rfl
      · rcases rest with _ | ⟨⟨A, rA⟩, xs⟩
        · simp (config := {decide := true}) only [↓reduceIte]
          rw [appsOpt_eq]
          unfold resolveStep
          dsimp only
          rw [hl]
          rfl
        · simp only [List.length_cons, lt_one_leaf, label_leaf, one_ne_zero,
            not_false_eq_true, ↓reduceIte, List.map_cons, List.getD_cons_succ, List.getD_cons_zero,
            readType_eq, List.drop_succ_cons, List.drop_zero, isSome_eq]
          rw [show resolveStep tys defs none ((h, rh) :: (A, rA) :: xs) scope =
              (do Kernel.apps (mk Label.para [← readType tys A]) (← xs.mapM fun c ↦ c.2 scope)) by
            unfold resolveStep
            dsimp only
            rw [hl]
            rfl]
          rcases readType tys A with _ | B
          · rfl
          · simp only [Option.isSome_some, ofBool, ↓reduceIte, label_leaf, one_ne_zero,
              not_false_eq_true, get_encOpt, Option.getD_some, single_eq, node_leaf]
            rw [show «Prelude.some» (RoseTree.node 25 [B]) = encOpt (some (mk 25 [B])) from rfl,
              appsOpt_eq]
            rfl
      · rcases rest with _ | ⟨⟨A, rA⟩, xs⟩
        · simp (config := {decide := true}) only [↓reduceIte]
          rw [appsOpt_eq]
          unfold resolveStep
          dsimp only
          rw [hl]
          rfl
        · simp only [List.length_cons, lt_one_leaf, label_leaf, one_ne_zero,
            not_false_eq_true, ↓reduceIte, List.map_cons, List.getD_cons_succ, List.getD_cons_zero,
            readType_eq, List.drop_succ_cons, List.drop_zero, isSome_eq]
          rw [show resolveStep tys defs none ((h, rh) :: (A, rA) :: xs) scope =
              (do Kernel.apps (mk Label.iter [← readType tys A]) (← xs.mapM fun c ↦ c.2 scope)) by
            unfold resolveStep
            dsimp only
            rw [hl]
            rfl]
          rcases readType tys A with _ | B
          · rfl
          · simp only [Option.isSome_some, ofBool, ↓reduceIte, label_leaf, one_ne_zero,
              not_false_eq_true, get_encOpt, Option.getD_some, single_eq, node_leaf]
            rw [show «Prelude.some» (RoseTree.node 18 [B]) = encOpt (some (mk 18 [B])) from rfl,
              appsOpt_eq]
            rfl
      · rcases rest with _ | ⟨⟨A, rA⟩, _ | ⟨⟨B, rB⟩, xs⟩⟩
        · simp (config := {decide := true}) only [↓reduceIte]
          rw [appsOpt_eq]
          unfold resolveStep
          dsimp only
          rw [hl]
          rfl
        · simp (config := {decide := true}) only [List.length_cons, List.length_nil, lt_leaf,
            ↓reduceIte]
          rw [appsOpt_eq]
          unfold resolveStep
          dsimp only
          rw [hl]
          rfl
        · simp only [List.length_cons, lt_two_leaf, label_leaf, one_ne_zero,
            not_false_eq_true, ↓reduceIte, List.map_cons, List.getD_cons_succ, List.getD_cons_zero,
            readType_eq, List.drop_succ_cons, List.drop_zero, some2_eq, isSome_eq]
          rw [show resolveStep tys defs none ((h, rh) :: (A, rA) :: (B, rB) :: xs) scope =
              (do Kernel.apps (mk Label.foldr [← readType tys A,
                ← readType tys B]) (← xs.mapM fun c ↦ c.2 scope)) by
            unfold resolveStep
            dsimp only
            rw [hl]
            rfl]
          rcases readType tys A with _ | A' <;> rcases readType tys B with _ | B'
          · rfl
          · rfl
          · rfl
          · simp only [ofBool, label_leaf]
            rw [show (do some (mk 21 [← some A', ← some B'])) = some (mk 21 [A', B']) from rfl,
              appsOpt_eq]
            rfl
      · rcases rest with _ | ⟨⟨A, rA⟩, _ | ⟨⟨B, rB⟩, xs⟩⟩
        · simp (config := {decide := true}) only [↓reduceIte]
          rw [appsOpt_eq]
          unfold resolveStep
          dsimp only
          rw [hl]
          rfl
        · simp (config := {decide := true}) only [List.length_cons, List.length_nil, lt_leaf,
            ↓reduceIte]
          rw [appsOpt_eq]
          unfold resolveStep
          dsimp only
          rw [hl]
          rfl
        · simp only [List.length_cons, lt_two_leaf, label_leaf, one_ne_zero,
            not_false_eq_true, ↓reduceIte, List.map_cons, List.getD_cons_succ, List.getD_cons_zero,
            readType_eq, List.drop_succ_cons, List.drop_zero, some2_eq, isSome_eq]
          rw [show resolveStep tys defs none ((h, rh) :: (A, rA) :: (B, rB) :: xs) scope =
              (do Kernel.apps (mk Label.lcase [← readType tys A,
                ← readType tys B]) (← xs.mapM fun c ↦ c.2 scope)) by
            unfold resolveStep
            dsimp only
            rw [hl]
            rfl]
          rcases readType tys A with _ | A' <;> rcases readType tys B with _ | B'
          · rfl
          · rfl
          · rfl
          · simp only [ofBool, label_leaf]
            rw [show (do some (mk 24 [← some A', ← some B'])) = some (mk 24 [A', B']) from rfl,
              appsOpt_eq]
            rfl

/-! ## The resolution -/

/-- The step of the mirror's resolution. -/
def resolveFold (x0 x1 : List Tree) (x4 : Tree) (x5 : List (Tree × (List Tree → Tree))) :
    Tree × (List Tree → Tree) :=
  let x6 : Tree := Const.node x4 («Reader.rrTrees» x5)
  (x6, fun (x7 : List Tree) ↦
    if («Reader.isAtom» x6).label ≠ 0 then «Reader.resolveAtom» x1 x6 x7
    else if («Reader.isList» x6).label ≠ 0 then «Reader.resolveList» x0 x6 x5 x7
    else «Prelude.none»)

/-- The mirror's resolution is its fold. -/
theorem resolve_fold (x0 x1 : List Tree) (x2 : Tree) (x3 : List Tree) :
    «Reader.resolve» x0 x1 x2 x3 = (Const.fold (resolveFold x0 x1) x2).2 x3 := rfl

/-- The mirror's resolution pairs each node with its resolution. -/
theorem pairStep_resolveFold (x0 x1 : List Tree) : PairStep (resolveFold x0 x1) := fun l rs ↦ by
  simp only [resolveFold, rrTrees_eq]

/-- The resolution of a well-formed S-expression, in every scope. -/
theorem fold_resolve (tys : TypeNames) (defs : List (List Char)) : ∀ e : SExp,
    Document.SExp.wf e → ∀ scope : List (List Char),
      (Const.fold (resolveFold (encTys tys) (defs.map nameTree)) (sexpTree e)).2
          (scope.map nameTree) = encOpt (resolve tys defs e scope) :=
  RoseTree.ind fun a cs ih hwf scope ↦ by
    rw [resolve_node]
    cases a with
    | some s =>
      rw [sexpTree_atom, fold_atomS (pairStep_resolveFold _ _)]
      have hr : Const.node (leaf 1) («Reader.rrTrees» ((charsT s).map fun c ↦
          (c, (Const.fold (resolveFold (encTys tys) (defs.map nameTree)) c).2))) =
            sexpTree (atomS s) := by
        rw [rrTrees_eq, List.map_map, sexpTree_atomS]
        exact congrArg (RoseTree.node 1) (List.map_id' _)
      simp only [resolveFold, hr, isAtom_atomS, label_leaf, ne_eq, one_ne_zero,
        not_false_eq_true, ↓reduceIte]
      exact resolveAtom_eq tys defs scope s _
    | none =>
      have hcs : ∀ c ∈ cs, Document.SExp.wf c := List.all_eq_true.mp (by
        rw [Document.SExp.wf_list] at hwf
        exact hwf)
      rw [sexpTree_listS', fold_node, map_fold_pair (pairStep_resolveFold _ _)]
      simp only [resolveFold, rrTrees_eq, List.map_map, Function.comp_def, node_leaf,
        isAtom_node2, isList_node2, label_leaf, ne_eq, not_true_eq_false, one_ne_zero,
        not_false_eq_true, ↓reduceIte]
      have := resolveList_eq tys defs (cs.map fun c ↦ (c, resolve tys defs c))
        (fun c ↦ (Const.fold (resolveFold (encTys tys) (defs.map nameTree)) (sexpTree c.1)).2)
        (fun c hc scope' ↦ by
          obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
          exact ih c' hc' (hcs c' hc') scope')
        (fun c hc ↦ by
          obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
          exact hcs c' hc') scope
      simpa only [List.map_map, Function.comp_def] using this

/-- The resolution written in Geb agrees with the Lean reader's at every well-formed
S-expression, in every scope, given any type abbreviations and names of definitions. -/
theorem resolve_eq (tys : TypeNames) (defs : List (List Char)) (e : SExp)
    (he : Document.SExp.wf e) (scope : List (List Char)) :
    «Reader.resolve» (encTys tys) (defs.map nameTree) (sexpTree e) (scope.map nameTree) =
      encOpt (resolve tys defs e scope) := by
  rw [resolve_fold, fold_resolve tys defs e he scope]

/-! ## The reader's inverse -/

/-- An atom is well formed. -/
theorem wf_atomS (s : List Char) : Document.SExp.wf (atomS s) := rfl

/-- A list of well-formed S-expressions is well formed. -/
theorem wf_listS {cs : List SExp} (h : ∀ c ∈ cs, Document.SExp.wf c) :
    Document.SExp.wf (listS cs) := by
  rw [listS, Document.SExp.wf_list]
  exact List.all_eq_true.mpr h

/-- A choice between well-formed S-expressions is well formed. -/
theorem wf_ite {p : Prop} [Decidable p] {a b : SExp} (ha : Document.SExp.wf a)
    (hb : Document.SExp.wf b) : Document.SExp.wf (if p then a else b) := by
  split
  · exact ha
  · exact hb

/-- A printed type is well formed. -/
theorem wf_printType : ∀ A : Tree, Document.SExp.wf (printType A) :=
  RoseTree.ind fun l cs ih ↦ by
    rw [printType_node]
    unfold printTypeStep
    repeat' refine wf_ite ?_ ?_
    all_goals first
      | exact wf_atomS _
      | (refine wf_listS fun c hc ↦ ?_
         rcases List.mem_cons.mp hc with rfl | hc
         · exact wf_atomS _
         · obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
           exact ih c' hc')

/-- A printed datum is well formed. -/
theorem wf_printDatum : ∀ t : Tree, Document.SExp.wf (printDatum t) :=
  RoseTree.ind fun l cs ih ↦ by
    rw [printDatum_node]
    refine wf_ite (wf_atomS _) (wf_listS fun c hc ↦ ?_)
    rcases List.mem_cons.mp hc with rfl | hc
    · exact wf_atomS _
    · obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
      exact ih c' hc'

/-- A printed term is well formed. -/
theorem wf_printTerm (defs : List (List Char)) : ∀ (t : Tree) (d : ℕ),
    Document.SExp.wf (printTerm defs t d) :=
  RoseTree.ind fun l cs ih d ↦ by
    rw [printTerm_node]
    unfold printStep
    dsimp only
    have hps : ∀ e : ℕ, ∀ c ∈ (cs.map fun c ↦ (c, printTerm defs c)).map fun r ↦ r.2 e,
        Document.SExp.wf c := fun e c hc ↦ by
      rw [List.map_map] at hc
      obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
      exact ih c' hc' e
    repeat' refine wf_ite ?_ ?_
    all_goals first
      | exact wf_atomS _
      | exact wf_listS (hps d)
      | (refine wf_listS fun c hc ↦ ?_
         rcases List.mem_cons.mp hc with rfl | hc
         · exact wf_atomS _
         · first
             | exact hps d c hc
             | (obtain ⟨c', -, rfl⟩ := List.mem_map.mp hc
                exact wf_printType c'))
      | (split
         · rename_i A sA x b heq
           exact wf_listS fun c hc ↦ by
             simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
             rcases hc with rfl | rfl | rfl
             · exact wf_atomS _
             · exact wf_listS fun c hc ↦ by
                 simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
                 rcases hc with rfl | rfl
                 · exact wf_atomS _
                 · exact wf_printType _
             · exact hps (d + 1) _ (by
                 rw [heq, List.map_cons, List.map_cons]
                 exact List.mem_cons_of_mem _ List.mem_cons_self)
         · exact wf_listS fun c hc ↦ absurd hc List.not_mem_nil)
      | (split
         · refine wf_ite (wf_atomS _) (wf_listS fun c hc ↦ ?_)
           simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
           rcases hc with rfl | rfl
           · exact wf_atomS _
           · exact wf_printDatum _
         · exact wf_listS fun c hc ↦ absurd hc List.not_mem_nil)

/-- The resolution with no type abbreviations, the printer's reading back, agrees with the Lean
reader's at every well-formed S-expression. -/
theorem readBack_eq (defs : List (List Char)) (e : SExp) (he : Document.SExp.wf e)
    (scope : List (List Char)) :
    «Printer.readBack» (defs.map nameTree) (sexpTree e) (scope.map nameTree) =
      encOpt (resolve [] defs e scope) :=
  resolve_eq [] defs e he scope

/-- The reader written in Geb inverts the printer written in Geb: a well-formed term printed by
the mirror's printer under binders to a depth, given the names of the definitions, is read back,
in the scope of those binders, to itself. -/
theorem readBack_printTerm_eq (defs : List (List Char)) (hnd : defs.Nodup)
    (hok : ∀ n ∈ defs, NameOk n) (t : Tree) (d : ℕ) (ht : TermWf defs.length t d = true) :
    «Printer.readBack» (defs.map nameTree) («Printer.printTerm» (defs.map nameTree) t (leaf d))
      ((scopeOf d).map nameTree) = encOpt (some t) := by
  rw [printTerm_eq defs t d ht, readBack_eq defs _ (wf_printTerm defs t d) (scopeOf d),
    resolve_printTerm [] defs hnd hok t d ht]

end GebTests.Prototypes.FreeTopos.Agreement.Reader

end
