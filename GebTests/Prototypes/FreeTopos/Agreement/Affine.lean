/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Agreement.Base
public import GebTests.Prototypes.FreeTopos.Agreement.Fold
public import GebTests.Prototypes.FreeTopos.Agreement.Printer
public import GebTests.Prototypes.FreeTopos.Agreement.Translation
public import GebTests.Prototypes.Affine.Decoration -- shake: keep
public meta import GebTests.Prototypes.Affine.Decoration -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.Agreement.Base -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The check of elementary-affine certificates written in Geb

The functions of {lit}`bootstrap/affine.geb`, in the Lean the bootstrap compiler emits
({lit}`GebMirror.Metalogic`), agree with the check of certificates {name}`Geb.Affine.check` at every
program and certificate, the terms and the certificate being trees in both: a decorated type, a
place, a result of a check, an entry of a context and an instance are encoded as trees, and the
check written in Geb gives the encoding of what the Lean check gives, nothing where it gives
nothing. The check of a term is one function of a mode: at mode zero it is the Lean check, and at
mode one, at the case analysis of lists applied to some of its arguments, it gives the checks of
those arguments, which the Lean check keeps in its spine.

## Main definitions

* {lit}`encD`, {lit}`encPl`, {lit}`encRes`, {lit}`encR`, {lit}`encEntry`, {lit}`encInst` —
  the encodings.
* {lit}`SemRel` — the relation of the mirror's check of a term to the Lean one.

## Main statements

* {lit}`decorate_eq`, {lit}`contracts_eq`, {lit}`termPlace_eq`, {lit}`occurrence_eq`,
  {lit}`enter_eq`, {lit}`lcaseSat_eq`, {lit}`abstraction_eq` — the check's functions.
* {lit}`mcheck_rel` — the check of a term, at mode zero and at its spine.
* {lit}`check_eq` — the check of a certificate.

## Tags

elementary affine logic, certificate, agreement, mirror
-/

set_option doc.verso true

@[expose] public section

open GebMirror.Metalogic

namespace GebTests.Prototypes.FreeTopos.Agreement.Affine

open Geb Geb.Kernel Geb.Affine Geb.Affine.DTy GebTests.Prototypes.FreeTopos.Agreement.Base
  GebTests.Prototypes.FreeTopos.Agreement.Encode GebTests.Prototypes.FreeTopos.Agreement.Fold
open GebTests.Prototypes.FreeTopos.Agreement.Printer (isTy_eq)
open GebTests.Prototypes.FreeTopos.Agreement.Translation (kTyList_eq kTyArrow_eq kPrimTypes_eq)
open Geb.Affine.DecorationTests
open scoped FinEnum

/-- A decorated type as a tree: each node the node of its simple type's label over the leaf of its
number of {lit}`!` and its children. -/
def encD : DTy → Tree := encWith (·.1) fun l ↦ leaf l.2

/-- A path as the node of label zero over its positions. -/
def encPath (p : List ℕ) : Tree := RoseTree.node 0 (p.map leaf)

/-- A place as the node of label zero over its variable and its path. -/
def encPl (pl : ℕ × List ℕ) : Tree := RoseTree.node 0 [leaf pl.1, encPath pl.2]

/-- A check's result as the node of label zero over its decorated type and its occurrences. -/
def encRes (r : DTy × Usage) : Tree :=
  RoseTree.node 0 [encD r.1, RoseTree.node 0 (r.2.map encPl)]

/-- An optional result of a check as a tree. -/
def encR (o : Option (DTy × Usage)) : Tree := encOpt (o.map encRes)

/-- A context's entry as the node of label zero over its decorated type and its binder's depth. -/
def encEntry (e : DTy × ℕ) : Tree := RoseTree.node 0 [encD e.1, leaf e.2]

/-- An instance as the node of label zero over its definition and its decorated type. -/
def encInst (e : ℕ × DTy) : Tree := RoseTree.node 0 [leaf e.1, encD e.2]

/-! ## Decorated types -/

/-- The encoding of a node of a decorated type. -/
theorem encD_node (l b : ℕ) (cs : List DTy) :
    encD (RoseTree.node (l, b) cs) = RoseTree.node l (leaf b :: cs.map encD) :=
  encWith_node _ _ _ _

/-- A decorated type is a node. -/
theorem dty_cases (d : DTy) : ∃ l b cs, d = RoseTree.node (l, b) cs :=
  ⟨d.label.1, d.label.2, d.children, (RoseTree.node_label_children d).symm⟩

/-- The label of a decorated type's encoding. -/
theorem label_encD (d : DTy) : Const.label (encD d) = leaf d.label.1 := by
  obtain ⟨l, b, cs, rfl⟩ := dty_cases d
  rw [encD_node]
  rfl

/-- The mirror's number of {lit}`!` at a root. -/
theorem dBang_eq (d : DTy) : «Affine.dBang» (encD d) = leaf d.bang := by
  obtain ⟨l, b, cs, rfl⟩ := dty_cases d
  rw [encD_node]
  simp only [«Affine.dBang», child_node, List.getD_cons_zero, label_eq, label_leaf]
  rfl

/-- The mirror's children of a decorated type. -/
theorem dKids_eq (d : DTy) : «Affine.dKids» (encD d) = d.children.map encD := by
  obtain ⟨l, b, cs, rfl⟩ := dty_cases d
  rw [encD_node]
  simp only [«Affine.dKids», children_eq, RoseTree.children_node, tail_eq, List.tail_cons]

/-- The mirror's node of a decorated type. -/
theorem dMk_eq (l b : ℕ) (cs : List DTy) :
    «Affine.dMk» (leaf l) (leaf b) (cs.map encD) = encD (DTy.mk l b cs) := by
  simp only [«Affine.dMk», DTy.mk, encD_node, node_leaf]

/-- The mirror's simple type of a decorated type. -/
theorem dTy_eq (d : DTy) : «Affine.dTy» (encD d) = d.ty := by
  refine RoseTree.ind (P := fun d : DTy ↦ «Affine.dTy» (encD d) = d.ty) (fun lb cs ih ↦ ?_) d
  obtain ⟨l, b⟩ := lb
  rw [encD_node]
  have h : (cs.map encD).map (Const.fold fun x1 x2 ↦ Const.node x1 x2.tail) = cs.map DTy.ty := by
    rw [List.map_map]
    refine List.map_congr_left fun c hc ↦ ?_
    simpa only [«Affine.dTy», tail_eq, Function.comp_apply] using ih c hc
  simp only [«Affine.dTy», tail_eq, fold_node, List.map_cons, List.tail_cons, h, node_leaf]
  simp only [DTy.ty, RoseTree.map_node]
  rfl

/-- The mirror's test of a type without arrows. -/
theorem isData_eq (t : Tree) : «Affine.isData» t = ofBool (IsData t) := by
  simp only [«Affine.isData», IsData]
  refine fold_rel (fun v w ↦ v = ofBool w) _ _ (fun l xs hxs ↦ ?_) t
  have hm : xs.map Prod.fst = (xs.map Prod.snd).map fun x ↦ ofBool (id x) := by
    rw [List.map_map]
    exact List.map_congr_left fun x hx ↦ hxs x hx
  rw [hm, allT_ofBool, eq_leaf, not_eq, and_eq]
  simp only [bne, Label.tyArrow]

/-- The mirror's test of a decorated type without arrows. -/
theorem dData_eq (d : DTy) : «Affine.dData» (encD d) = ofBool d.data := by
  simp only [«Affine.dData», dTy_eq, isData_eq, DTy.data]

/-- A decorated node is data when its label is not an arrow's and its children are data. -/
theorem data_node (l b : ℕ) (cs : List DTy) :
    DTy.data (RoseTree.node (l, b) cs) = (l != Label.tyArrow && cs.all DTy.data) := by
  simp only [DTy.data, DTy.ty, RoseTree.map_node, IsData, RoseTree.elim_node, List.map_map,
    List.all_map, Function.comp_def, id_eq]
  rfl

/-- The mirror's simple type with no {lit}`!`. -/
theorem dZero_eq (A : Tree) : «Affine.dZero» A = encD (zero A) := by
  refine RoseTree.ind (P := fun A ↦ «Affine.dZero» A = encD (zero A)) (fun l cs ih ↦ ?_) A
  have h : cs.map (Const.fold fun x1 x2 ↦ Const.node x1 (leaf 0 :: x2)) =
      cs.map fun c ↦ encD (zero c) := List.map_congr_left ih
  unfold «Affine.dZero»
  simp only [fold_node, h, node_leaf, DTy.zero, RoseTree.map_node, encD_node, List.map_map,
    Function.comp_def]

/-- The mirror's replacement of a root's number of {lit}`!`. -/
theorem withBang_eq (d : DTy) (b : ℕ) :
    «Affine.withBang» (encD d) (leaf b) = encD (d.withBang b) := by
  simp only [«Affine.withBang», dData_eq, DTy.withBang, label_encD, dKids_eq, dMk_eq]
  cases d.data <;> rfl

/-- The mirror's type under more {lit}`!`. -/
theorem dShift_eq (d : DTy) (e : ℕ) : «Affine.dShift» (encD d) (leaf e) = encD (d.shift e) := by
  simp only [«Affine.dShift», dBang_eq, add_leaf, withBang_eq, DTy.shift]

/-- The mirror's type with one {lit}`!` fewer. -/
theorem dUnbox_eq (d : DTy) : «Affine.dUnbox» (encD d) = encD d.unbox := by
  simp only [«Affine.dUnbox», dBang_eq, sub_leaf, withBang_eq, DTy.unbox]

/-- The mirror's function type with no {lit}`!` at its root. -/
theorem dArrow_eq (a b : DTy) : «Affine.dArrow» (encD a) (encD b) = encD (arrow a b) := by
  simpa only [«Affine.dArrow», List.map_cons, List.map_nil, single_eq, arrow] using
    dMk_eq Label.tyArrow 0 [a, b]

/-- The mirror's list type with no {lit}`!` at its root. -/
theorem dList_eq (a : DTy) : «Affine.dList» (encD a) = encD (list a) := by
  simpa only [«Affine.dList», List.map_cons, List.map_nil, single_eq, DTy.list] using
    dMk_eq Label.tyList 0 [a]

/-! ## The decoration of a simple type -/

/-- The checks of a decorated type's children: as many as the tree of numbers has children. -/
def kidsD (rs : List (Tree → Option DTy)) (bs : List Tree) : Option (List DTy) :=
  if rs.length = bs.length then
    (rs.zip bs).mapM fun p : (Tree → Option DTy) × Tree ↦ p.1 p.2
  else none

/-- The Lean step of the decoration of a simple type. -/
theorem decorateStep_eq (l : ℕ) (rs : List (Tree → Option DTy)) (b : Tree) :
    decorateStep l rs b = (kidsD rs b.children).map fun cs ↦
      DTy.mk l (if (l != Label.tyArrow && cs.all DTy.data) = true then 0 else b.label) cs := by
  unfold decorateStep kidsD
  by_cases h : rs.length = b.children.length
  · simp only [h, guard, ↓reduceIte]
    change ((rs.zip b.children).mapM fun p : (Tree → Option DTy) × Tree ↦ p.1 p.2).bind _ = _
    cases (rs.zip b.children).mapM (fun p : (Tree → Option DTy) × Tree ↦ p.1 p.2) <;> rfl
  · simp only [h, guard, ↓reduceIte]
    rfl

/-- The mirror's decorations of a node's children by the children of a tree of numbers. -/
def decKids (rs : List (Tree → Tree)) : List Tree → Tree :=
  List.foldr (fun (r : Tree → Tree) (c : List Tree → Tree) (bs : List Tree) ↦
      Const.lcase bs «Prelude.none» fun x r' ↦
        «Base.bindO» (r x) fun d ↦
          «Base.mapO» (fun ds ↦ Const.node (leaf 0) (d :: Const.children ds)) (c r'))
    (fun bs ↦ if («Base.isEmpty» bs).label ≠ 0 then «Prelude.some» (Const.node (leaf 0) [])
      else «Prelude.none») rs

/-- The mirror's decoration at a node, from its children's. -/
theorem decorate_mnode (l : ℕ) (cs : List Tree) (y : Tree) :
    «Affine.decorate» (RoseTree.node l cs) y =
      «Base.mapO» (fun x ↦ «Affine.dMk» (leaf l)
          (if («Prelude.and» («Base.not» (Const.eq (leaf l) (leaf 3)))
              («Base.allT» «Affine.dData» (Const.children x))).label ≠ 0 then leaf 0
            else Const.label y) (Const.children x))
        (decKids (cs.map «Affine.decorate») (Const.children y)) := by
  unfold «Affine.decorate»
  rw [fold_node]
  simp only [foldr_eq, decKids]

/-- The mirror's decorations of children, from their decorations. -/
theorem decKids_eq (f : Tree → Tree → Tree) (g : Tree → Tree → Option DTy) :
    ∀ cs : List Tree, (∀ c ∈ cs, ∀ b, f c b = encOpt ((g c b).map encD)) → ∀ bs,
      decKids (cs.map f) bs =
        encOpt ((kidsD (cs.map g) bs).map fun ds ↦ RoseTree.node 0 (ds.map encD)) := by
  refine List.rec (fun _ bs ↦ ?_) (fun c cs ih h bs ↦ ?_)
  · cases bs <;> rfl
  · cases bs with
    | nil => rfl
    | cons b bs =>
      have ih' := ih (fun x hx ↦ h x (List.mem_cons_of_mem c hx)) bs
      have hk : kidsD (g c :: cs.map g) (b :: bs) =
          (g c b).bind fun d ↦ (kidsD (cs.map g) bs).map (d :: ·) := by
        unfold kidsD
        by_cases hl : (cs.map g).length = bs.length
        · simp only [List.length_cons, hl, ↓reduceIte, List.zip_cons_cons, List.mapM_cons]
          cases g c b <;> cases List.mapM (fun p : (Tree → Option DTy) × Tree ↦ p.1 p.2)
            ((cs.map g).zip bs) <;> rfl
        · have hl' : ¬ (cs.map g).length + 1 = bs.length + 1 := fun e ↦ hl (Nat.succ.inj e)
          simp only [List.length_cons, hl, hl', ↓reduceIte]
          cases g c b <;> rfl
      have hs : decKids (f c :: cs.map f) (b :: bs) =
          «Base.bindO» (f c b) fun d ↦ «Base.mapO»
            (fun ds ↦ Const.node (leaf 0) (d :: Const.children ds)) (decKids (cs.map f) bs) := rfl
      rw [List.map_cons, List.map_cons, hs, hk, h c List.mem_cons_self, ih']
      cases hg : g c b with
      | none => rfl
      | some d =>
        cases kidsD (cs.map g) bs with
        | none => rfl
        | some v =>
          simp only [Option.map_some, Option.bind_some, bindO_eq, Option.elim_some, mapO_eq,
            children_eq, RoseTree.children_node, node_leaf, List.map_cons]

/-- The mirror's test that every decorated type of a list is data. -/
theorem allT_dData (ds : List DTy) :
    «Base.allT» «Affine.dData» (ds.map encD) = ofBool (ds.all DTy.data) :=
  allT_map _ _ _ _ fun d _ ↦ dData_eq d

/-- The mirror's decoration of a simple type by a tree of numbers. -/
theorem decorate_eq (A : Tree) : ∀ b, «Affine.decorate» A b = encOpt ((decorate A b).map encD) := by
  refine RoseTree.ind (P := fun A ↦ ∀ b, «Affine.decorate» A b = encOpt ((decorate A b).map encD))
    (fun l cs ih y ↦ ?_) A
  rw [decorate_mnode, children_eq, decKids_eq _ decorate cs ih, DTy.decorate, RoseTree.elim_node,
    decorateStep_eq]
  change _ = encOpt (((kidsD (cs.map decorate) y.children).map _).map encD)
  cases kidsD (cs.map decorate) y.children with
  | none => rfl
  | some ds =>
    simp only [Option.map_some, mapO_eq, children_eq, RoseTree.children_node, allT_dData, eq_leaf,
      not_eq, and_eq, label_eq, Label.tyArrow]
    have hb : (!(l == 3) && ds.all DTy.data) = (l != 3 && ds.all DTy.data) := rfl
    rw [hb]
    cases l != 3 && ds.all DTy.data
    · simp only [ofBool_false, label_leaf, ne_eq, not_true_eq_false, Bool.false_eq_true, ↓reduceIte,
        dMk_eq]
    · simp only [ofBool_true, label_leaf, ne_eq, one_ne_zero, not_false_eq_true, ↓reduceIte,
        dMk_eq]

/-! ## Paths and places -/

/-- Paths' encodings are equal exactly when the paths are. -/
theorem encPath_inj {p q : List ℕ} : encPath p = encPath q ↔ p = q := by
  simp only [encPath, node_inj, true_and, map_leaf_inj]

/-- Places' encodings are equal exactly when the places are. -/
theorem encPl_inj {a b : ℕ × List ℕ} : encPl a = encPl b ↔ a = b := by
  simp only [encPl, node_inj, true_and, List.cons.injEq, and_true, leaf_inj, encPath_inj,
    Prod.ext_iff]

/-- The mirror's test of a path's being a prefix of another. -/
theorem isPrefix_eq (p q : List ℕ) :
    «Affine.isPrefix» (encPath p) (encPath q) = ofBool (p.isPrefixOf q) := by
  have h : decide (p = q.take p.length) = p.isPrefixOf q := by
    rw [Bool.eq_iff_iff, decide_eq_true_iff, List.isPrefixOf_iff_prefix, List.prefix_iff_eq_take]
  simp only [«Affine.isPrefix», encPath, children_eq, RoseTree.children_node, length_eq,
    List.length_map, take_eq, ← List.map_take, node_leaf, equal_eq, node_inj, true_and,
    map_leaf_inj, h]

/-- The mirror's extension of a path by a position. -/
theorem snocPath_eq (p : List ℕ) (i : ℕ) :
    «Affine.snocPath» (encPath p) (leaf i) = encPath (p ++ [i]) := by
  simp only [«Affine.snocPath», encPath, children_eq, RoseTree.children_node, single_eq, append_eq,
    node_leaf, List.map_append, List.map_cons, List.map_nil]

/-- The mirror's count of a path among paths. -/
theorem countPath_eq (p : List ℕ) (paths : List (List ℕ)) :
    «Affine.countPath» (encPath p) (paths.map encPath) = leaf (paths.count p) := by
  simp only [«Affine.countPath», foldr_eq]
  refine paths.rec rfl fun q r ih ↦ ?_
  rw [List.map_cons, List.foldr_cons, ih, List.count_cons, equal_eq]
  by_cases h : q = p
  · simp only [h, decide_true, ofBool_true, label_leaf, ne_eq, one_ne_zero,
      not_false_eq_true, ↓reduceIte, add_leaf, beq_self_eq_true]
  · simp only [encPath_inj, h, decide_false, ofBool_false, label_leaf, ne_eq, not_true_eq_false,
      ↓reduceIte, beq_iff_eq, add_zero]

/-- The mirror's test that some element of an encoded list passes a test. -/
theorem anyT_map {α : Type} (f : Tree → Tree) (e : α → Tree) (p : α → Bool) :
    ∀ xs : List α, (∀ x ∈ xs, f (e x) = ofBool (p x)) →
      «Base.anyT» f (xs.map e) = ofBool (xs.any p) :=
  List.rec (fun _ ↦ rfl) fun x r ih h ↦ by
    have ih' := ih fun y hy ↦ h y (List.mem_cons_of_mem x hy)
    simp only [«Base.anyT», foldr_eq, List.map_cons, List.foldr_cons] at ih' ⊢
    rw [ih', h x List.mem_cons_self, or_eq, List.any_cons]

/-- The mirror's test of a path below a path among paths. -/
theorem belowPath_eq (p : List ℕ) (paths : List (List ℕ)) :
    «Affine.belowPath» (encPath p) (paths.map encPath) =
      ofBool (paths.any fun q ↦ decide (p.length < q.length) && p.isPrefixOf q) := by
  refine anyT_map _ _ _ _ fun q _ ↦ ?_
  simp only [encPath, children_eq, RoseTree.children_node, length_eq, List.length_map, lt_leaf]
  have := isPrefix_eq p q
  simp only [encPath] at this
  rw [this, and_eq]

/-- The mirror's checks of a node's children, each at its path, the positions counted from a
position. -/
def ctKids (ps : List Tree) (rs : List (Tree → Tree → Tree)) (p e i : Tree) : Tree :=
  List.foldr (fun (r : Tree → Tree → Tree) (c : Tree → Tree → Tree → Tree) (p e i : Tree) ↦
      «Prelude.and»
        (if («Base.anyT» (fun x ↦ «Affine.isPrefix» («Affine.snocPath» p i) x) ps).label ≠ 0 then
          r («Affine.snocPath» p i) e else leaf 1)
        (c p e (Const.add i (leaf 1))))
    (fun _ _ _ ↦ leaf 1) rs p e i

/-- The mirror's checks of a node's children, from their checks. -/
theorem ctKids_eq (paths : List (List ℕ)) (p : List ℕ) (e : ℕ) (f : DTy → Tree → Tree → Tree)
    (g : DTy → Bool × (List ℕ → ℕ → Bool)) :
    ∀ cs : List DTy, (∀ c ∈ cs, ∀ p e, f c (encPath p) (leaf e) = ofBool ((g c).2 p e)) → ∀ i,
      ctKids (paths.map encPath) (cs.map f) (encPath p) (leaf e) (leaf i) =
        ofBool (((cs.map g).zipIdx i).all fun x ↦
          !(paths.any ((p ++ [x.2]).isPrefixOf ·)) || x.1.2 (p ++ [x.2]) e) := by
  refine List.rec (fun _ _ ↦ rfl) (fun c cs ih h i ↦ ?_)
  have ih' := ih (fun x hx ↦ h x (List.mem_cons_of_mem c hx)) (i + 1)
  have hs : ctKids (paths.map encPath) (f c :: cs.map f) (encPath p) (leaf e) (leaf i) =
      «Prelude.and»
        (if («Base.anyT» (fun x ↦ «Affine.isPrefix» («Affine.snocPath» (encPath p) (leaf i)) x)
            (paths.map encPath)).label ≠ 0 then
          f c («Affine.snocPath» (encPath p) (leaf i)) (leaf e) else leaf 1)
        (ctKids (paths.map encPath) (cs.map f) (encPath p) (leaf e) (leaf (i + 1))) := rfl
  have ha : «Base.anyT» (fun x ↦ «Affine.isPrefix» (encPath (p ++ [i])) x) (paths.map encPath) =
      ofBool (paths.any ((p ++ [i]).isPrefixOf ·)) :=
    anyT_map _ _ _ _ fun q _ ↦ isPrefix_eq _ _
  rw [List.map_cons, List.map_cons, hs, snocPath_eq, ha, h c List.mem_cons_self, ih',
    List.zipIdx_cons, List.all_cons]
  cases paths.any ((p ++ [i]).isPrefixOf ·) <;> cases (g c).2 (p ++ [i]) e <;> rfl

/-- Tests that agree on a list's elements agree on the list. -/
theorem all_congr_mem {α : Type} {p q : α → Bool} :
    ∀ xs : List α, (∀ x ∈ xs, p x = q x) → xs.all p = xs.all q :=
  List.rec (fun _ ↦ rfl) fun x r ih h ↦ by
    rw [List.all_cons, List.all_cons, h x List.mem_cons_self,
      ih fun y hy ↦ h y (List.mem_cons_of_mem x hy)]

/-- The mirror's check of a variable's places, related to the Lean one's. -/
theorem ct_rel (paths : List (List ℕ)) (d : DTy) :
    (∀ p e, Const.para («Affine.ctStep» (paths.map encPath)) (encD d) (encPath p) (leaf e) =
      ofBool ((RoseTree.elim (contractsStep paths) d).2 p e)) ∧
    (RoseTree.elim (contractsStep paths) d).1 = d.data := by
  refine RoseTree.ind (P := fun d : DTy ↦
    (∀ p e, Const.para («Affine.ctStep» (paths.map encPath)) (encD d) (encPath p) (leaf e) =
      ofBool ((RoseTree.elim (contractsStep paths) d).2 p e)) ∧
    (RoseTree.elim (contractsStep paths) d).1 = d.data) (fun lb cs ih ↦ ?_) d
  obtain ⟨l, b⟩ := lb
  have hdata : (RoseTree.elim (contractsStep paths) (RoseTree.node (l, b) cs)).1 =
      DTy.data (RoseTree.node (l, b) cs) := by
    rw [data_node, RoseTree.elim_node]
    simp only [contractsStep, List.all_map, Function.comp_def]
    congr 1
    exact all_congr_mem cs fun c hc ↦ (ih c hc).2
  refine ⟨fun p e ↦ ?_, hdata⟩
  have hk := ctKids_eq paths p (b + e)
    (fun c ↦ Const.para («Affine.ctStep» (paths.map encPath)) (encD c))
    (RoseTree.elim (contractsStep paths)) cs (fun c hc ↦ (ih c hc).1) 0
  have hs : Const.para («Affine.ctStep» (paths.map encPath)) (encD (RoseTree.node (l, b) cs))
      (encPath p) (leaf e) =
      if («Affine.dData» (encD (RoseTree.node (l, b) cs))).label ≠ 0 then leaf 1
      else if («Prelude.or» (Const.lt (leaf 1) («Affine.countPath» (encPath p) (paths.map encPath)))
          («Prelude.and» (Const.lt (leaf 0) («Affine.countPath» (encPath p) (paths.map encPath)))
            («Affine.belowPath» (encPath p) (paths.map encPath)))).label ≠ 0 then
        Const.lt (leaf 0) (Const.add («Affine.dBang» (encD (RoseTree.node (l, b) cs))) (leaf e))
      else «Prelude.or» (Const.lt (leaf 0) («Affine.countPath» (encPath p) (paths.map encPath)))
        (ctKids (paths.map encPath)
          (cs.map fun c ↦ Const.para («Affine.ctStep» (paths.map encPath)) (encD c)) (encPath p)
          (Const.add («Affine.dBang» (encD (RoseTree.node (l, b) cs))) (leaf e)) (leaf 0)) := by
    conv_lhs => rw [encD_node, Const.para_node]
    simp only [«Affine.ctStep», List.map_cons, ← encD_node, foldr_eq, ctKids, List.map_map,
      Function.comp_def]
    rfl
  rw [hs, dData_eq, dBang_eq, countPath_eq, belowPath_eq, RoseTree.elim_node]
  simp only [DTy.bang, RoseTree.label_node, add_leaf, hk, lt_leaf, and_eq, or_eq, contractsStep]
  rw [← hdata, RoseTree.elim_node]
  simp only [contractsStep]
  cases (l != Label.tyArrow && (cs.map (RoseTree.elim (contractsStep paths))).all (·.1)) <;>
    simp only [ofBool_true, ofBool_false, label_leaf, ne_eq, one_ne_zero, not_false_eq_true,
      not_true_eq_false, ↓reduceIte, Bool.true_or, Bool.false_or]
  · have h2 : decide (1 < paths.count p) = decide (2 ≤ paths.count p) := rfl
    have h1 : decide (0 < paths.count p) = decide (1 ≤ paths.count p) := rfl
    have h3 : decide (0 < b + e) = decide (1 ≤ b + e) := rfl
    have h4 : decide (1 ≤ paths.count p) = (paths.count p != 0) := by
      cases paths.count p <;> rfl
    rw [h2, h1, h3]
    cases (decide (2 ≤ paths.count p) || (decide (1 ≤ paths.count p) &&
        paths.any fun q ↦ decide (p.length < q.length) && p.isPrefixOf q)) with
    | true => rfl
    | false =>
      simp only [ofBool_false, label_leaf, not_true_eq_false, ↓reduceIte, h4]
      rfl

/-- The mirror's test that a variable of a decorated type admits occurrences of its places at
these paths. -/
theorem contracts_eq (paths : List (List ℕ)) (d : DTy) :
    «Affine.contracts» (paths.map encPath) (encD d) = ofBool (DTy.contracts paths d) :=
  ((ct_rel paths d).1 [] 0)

/-- The mirror's decorated type of a place. -/
theorem dPlace_eq : ∀ (path : List ℕ) (d : DTy),
    «Affine.dPlace» (encD d) (path.map leaf) = encOpt ((DTy.place d path).map encD) := by
  refine List.rec (fun _ ↦ rfl) (fun i path ih d ↦ ?_)
  have hs : «Affine.dPlace» (encD d) (leaf i :: path.map leaf) =
      «Base.bindO» («Prelude.nth» («Affine.dKids» (encD d)) (leaf i)) fun c ↦
        «Affine.dPlace» (if («Affine.dData» (encD d)).label ≠ 0 then c
          else «Affine.dShift» c («Affine.dBang» (encD d))) (path.map leaf) := rfl
  have hp : DTy.place d (i :: path) = (d.children[i]?.map fun c ↦
      if d.data then c else DTy.shift c d.bang).bind fun d' ↦ DTy.place d' path := rfl
  rw [List.map_cons, hs, nth_eq, dKids_eq, List.getElem?_map, hp, dData_eq, dBang_eq]
  cases d.children[i]? with
  | none => rfl
  | some c =>
    simp only [Option.map_some, bindO_eq, Option.elim_some, Option.bind_some]
    cases d.data
    · simpa only [ofBool_false, label_leaf, ne_eq, not_true_eq_false, ↓reduceIte, dShift_eq,
        Bool.false_eq_true] using ih (DTy.shift c (DTy.bang d))
    · simpa only [ofBool_true, label_leaf, ne_eq, one_ne_zero, not_false_eq_true, ↓reduceIte]
        using ih c

/-! ## The places a term reaches -/

/-- The mirror's place of a variable and a path. -/
theorem plMk_eq (n : ℕ) (p : List ℕ) : «Affine.plMk» (leaf n) (encPath p) = encPl (n, p) := rfl

/-- The mirror's variable of a place. -/
theorem plVar_eq (pl : ℕ × List ℕ) : «Affine.plVar» (encPl pl) = leaf pl.1 := by
  simp only [«Affine.plVar», encPl, child_node, List.getD_cons_zero]

/-- The mirror's path of a place. -/
theorem plPath_eq (pl : ℕ × List ℕ) : «Affine.plPath» (encPl pl) = encPath pl.2 := by
  simp only [«Affine.plPath», encPl, child_node, List.getD_cons_succ, List.getD_cons_zero]

/-- The mirror's place of a projection of a place. -/
theorem projPlace_eq (i : ℕ) (o : Option (ℕ × List ℕ)) :
    «Base.mapO» (fun x ↦ «Affine.plMk» («Affine.plVar» x) («Affine.snocPath» («Affine.plPath» x)
        (leaf i))) (encOpt (o.map encPl)) =
      encOpt ((o.map fun x ↦ (x.1, x.2 ++ [i])).map encPl) := by
  cases o with
  | none => rfl
  | some x =>
    simp only [Option.map_some, mapO_eq, plVar_eq, plPath_eq, snocPath_eq, plMk_eq]

/-- The mirror's place a term reaches. -/
theorem termPlace_eq (t : Tree) :
    «Affine.termPlace» t = encOpt ((Geb.Affine.place t).map encPl) := by
  simp only [«Affine.termPlace», Geb.Affine.place]
  refine para_rel (fun v (w : Option (ℕ × List ℕ)) ↦ v = encOpt (w.map encPl)) _ _
    (fun l xs hxs ↦ ?_) t
  by_cases h8 : l = 8
  · subst h8
    match xs, hxs with
    | [], _ => rfl
    | [x], _ => rfl
    | x :: y :: r, _ =>
      simp only [List.map_cons, length_eq, List.length_cons, eq_leaf, label_eq, RoseTree.label_node]
      rfl
  by_cases h13 : l = 13
  · subst h13
    match xs, hxs with
    | [], _ => rfl
    | [x], h =>
      have := projPlace_eq 0 x.2.2
      rw [← h x List.mem_cons_self] at this
      exact this
    | x :: y :: r, _ =>
      simp only [List.map_cons, length_eq, List.length_cons, eq_leaf, label_eq, RoseTree.label_node]
      rfl
  by_cases h14 : l = 14
  · subst h14
    match xs, hxs with
    | [], _ => rfl
    | [x], h =>
      have := projPlace_eq 1 x.2.2
      rw [← h x List.mem_cons_self] at this
      exact this
    | x :: y :: r, _ =>
      simp only [List.map_cons, length_eq, List.length_cons, eq_leaf, label_eq, RoseTree.label_node]
      rfl
  have h8' : (l == 8) = false := by simpa using h8
  have h13' : (l == 13) = false := by simpa using h13
  have h14' : (l == 14) = false := by simpa using h14
  simp only [label_eq, RoseTree.label_node, eq_leaf, h8', h13', h14', ofBool_false, label_leaf,
    ne_eq, not_true_eq_false, ↓reduceIte]
  split <;> first | rfl | contradiction

/-! ## Occurrences -/

/-- The mirror's removal of the first occurrence of a place, after an occurrence was removed. -/
theorem eraseFrom_done (a : ℕ × List ℕ) (l : List (ℕ × List ℕ)) :
    List.foldr (fun (x2 : Tree) (x3 : Tree → List Tree) (x4 : Tree) ↦
        if («Prelude.and» («Base.not» x4) (Const.equal x2 (encPl a))).label ≠ 0 then x3 (leaf 1)
        else x2 :: x3 x4)
      (fun _ ↦ []) (l.map encPl) (leaf 1) = l.map encPl := by
  refine l.rec rfl fun x r ih ↦ ?_
  simp only [List.map_cons, List.foldr_cons]
  rw [show «Base.not» (leaf 1) = ofBool false from rfl, equal_eq, and_eq]
  simp only [Bool.false_and, ofBool_false, label_leaf, ne_eq, not_true_eq_false, ↓reduceIte, ih]

/-- The mirror's removal of the first occurrence of a place. -/
theorem eraseT_eq (a : ℕ × List ℕ) (l : List (ℕ × List ℕ)) :
    «Affine.eraseT» (encPl a) (l.map encPl) = (l.erase a).map encPl := by
  simp only [«Affine.eraseT», foldr_eq]
  refine l.rec rfl fun x r ih ↦ ?_
  simp only [List.map_cons, List.foldr_cons, List.erase_cons]
  rw [show «Base.not» (leaf 0) = ofBool true from rfl, equal_eq, and_eq]
  by_cases h : x = a
  · simp only [h, decide_true, Bool.and_self, ofBool_true, label_leaf, ne_eq, one_ne_zero,
      not_false_eq_true, ↓reduceIte, beq_self_eq_true, eraseFrom_done]
  · have h' : (x == a) = false := beq_eq_false_iff_ne.mpr h
    have h'' : encPl x ≠ encPl a := fun e ↦ h (encPl_inj.mp e)
    simp only [h'', decide_false, Bool.and_false, ofBool_false, label_leaf, ne_eq,
      not_true_eq_false, ↓reduceIte, h', Bool.false_eq_true, ih, List.map_cons]

/-- The mirror's occurrences of one list without those of another. -/
theorem diffT_eq (u : List (ℕ × List ℕ)) : ∀ v : List (ℕ × List ℕ),
    «Affine.diffT» (v.map encPl) (u.map encPl) = (v.diff u).map encPl := by
  refine u.rec (fun _ ↦ rfl) fun a u ih v ↦ ?_
  have h := ih (v.erase a)
  simp only [«Affine.diffT», foldr_eq] at h ⊢
  simp only [List.map_cons, List.foldr_cons, eraseT_eq, h, List.diff_cons]

/-- The mirror's occurrences of two additive branches. -/
theorem usageMax_eq (u v : Usage) :
    «Affine.usageMax» (u.map encPl) (v.map encPl) = (Usage.max u v).map encPl := by
  simp only [«Affine.usageMax», diffT_eq, append_eq, Usage.max, List.map_append]

/-- The mirror's result of a check. -/
theorem res_eq (d : DTy) (u : Usage) :
    «Affine.res» (encD d) (u.map encPl) = encR (some (d, u)) := rfl

/-- The mirror's decorated type of a result. -/
theorem rD_eq (r : DTy × Usage) : «Affine.rD» (encRes r) = encD r.1 := by
  simp only [«Affine.rD», encRes, child_node, List.getD_cons_zero]

/-- The mirror's occurrences of a result. -/
theorem rU_eq (r : DTy × Usage) : «Affine.rU» (encRes r) = r.2.map encPl := by
  simp only [«Affine.rU», encRes, child_node, List.getD_cons_succ, List.getD_cons_zero,
    children_eq, RoseTree.children_node]

/-- A guard that holds. -/
theorem guard_some {p : Prop} [Decidable p] (h : p) : (guard p : Option Unit) = some () :=
  ite_eq_left h

/-- A guard that fails. -/
theorem guard_none {p : Prop} [Decidable p] (h : ¬p) : (guard p : Option Unit) = none :=
  ite_eq_right h

/-- The mirror's occurrence of a place at a depth. -/
theorem occurrence_eq (Γ : Geb.Affine.Ctx) (depth : ℕ) (pl : ℕ × List ℕ) :
    «Affine.occurrence» (Γ.map encEntry) (leaf depth) (encPl pl) =
      encR (occurrence Γ depth pl) := by
  unfold «Affine.occurrence» Geb.Affine.occurrence «Affine.ctxAt»
  simp only [plVar_eq, nth_eq, List.getElem?_map, plPath_eq]
  cases hΓ : Γ[pl.1]? with
  | none => rfl
  | some e =>
    obtain ⟨d0, bound⟩ := e
    simp only [Option.map_some, bindO_eq, Option.elim_some, encEntry, child_node,
      List.getD_cons_zero, List.getD_cons_succ, encPath, children_eq, RoseTree.children_node,
      dPlace_eq]
    change _ = encR ((d0.place pl.2).bind _)
    cases d0.place pl.2 with
    | none => rfl
    | some d =>
      simp only [Option.map_some, Option.elim_some, Option.bind_some, lt_leaf]
      by_cases hb : depth < bound
      · rw [guard_none (Nat.not_le.mpr hb)]
        simp only [hb, decide_true, ofBool_true, label_leaf, ne_eq, one_ne_zero,
          not_false_eq_true, ↓reduceIte]
        rfl
      · rw [guard_some (Nat.not_lt.mp hb)]
        simp only [hb, decide_false, ofBool_false, label_leaf, ne_eq, not_true_eq_false,
          ↓reduceIte, dData_eq, dBang_eq, sub_leaf, lt_leaf, withBang_eq, single_eq]
        change _ = encR (if d.data = true then some (d, [pl]) else _)
        cases d.data with
        | true =>
          simp only [ofBool_true, label_leaf, one_ne_zero, not_false_eq_true, ↓reduceIte]
          exact res_eq d [pl]
        | false =>
          simp only [ofBool_false, label_leaf, not_true_eq_false, Bool.false_eq_true, ↓reduceIte]
          by_cases hd : DTy.bang d < depth - bound
          · rw [guard_none (Nat.not_le.mpr hd)]
            simp only [hd, decide_true, ofBool_true, label_leaf, one_ne_zero, not_false_eq_true,
              ↓reduceIte]
            rfl
          · rw [guard_some (Nat.not_lt.mp hd)]
            simp only [hd, decide_false, ofBool_false, label_leaf, not_true_eq_false, ↓reduceIte]
            exact res_eq _ [pl]

/-- The mirror's test that no occurrence is of a variable bound deeper than a depth. -/
theorem enterAll_eq (Γ : Geb.Affine.Ctx) (c : ℕ) (u : Usage) :
    «Base.allT» (fun x ↦
        if («Prelude.isSome» («Affine.ctxAt» (Γ.map encEntry) («Affine.plVar» x))).label ≠ 0 then
          «Base.not» (Const.lt (leaf c)
            (Const.child («Prelude.get» («Affine.ctxAt» (Γ.map encEntry) («Affine.plVar» x)))
              (leaf 1)))
        else leaf 0) (u.map encPl) =
      ofBool (u.all fun pl ↦ Γ[pl.1]?.any fun e ↦ decide (e.2 ≤ c)) := by
  refine allT_map _ _ _ _ fun pl _ ↦ ?_
  simp only [«Affine.ctxAt», plVar_eq, nth_eq, List.getElem?_map]
  cases hΓ : Γ[pl.1]? with
  | none => rfl
  | some e =>
    obtain ⟨d0, bound⟩ := e
    simp only [Option.map_some, isSome_eq, Option.isSome_some, ofBool_true, label_leaf, ne_eq,
      one_ne_zero, not_false_eq_true, ↓reduceIte, get_encOpt, Option.getD_some, encEntry,
      child_node, List.getD_cons_succ, List.getD_cons_zero, lt_leaf, not_eq, Option.any_some]
    congr 1
    rw [← decide_not]
    exact decide_eq_decide.mpr Nat.not_lt

/-- The mirror's entry of a result into a child's depth. -/
theorem enter_eq (Γ : Geb.Affine.Ctx) (depth c : ℕ) (r : DTy × Usage) :
    «Affine.enter» (Γ.map encEntry) (leaf depth) (leaf c) (encRes r) =
      encR (enter Γ depth c r) := by
  unfold «Affine.enter» Geb.Affine.enter
  simp only [rU_eq, enterAll_eq, rD_eq, dData_eq, dBang_eq, add_leaf, lt_leaf, sub_leaf,
    withBang_eq]
  by_cases hu : (r.2.all fun pl ↦ Γ[pl.1]?.any fun e ↦ decide (e.2 ≤ c)) = true
  · rw [guard_some hu]
    simp only [hu, ofBool_true, label_leaf, ne_eq, one_ne_zero, not_false_eq_true, ↓reduceIte]
    change _ = encR (if r.1.data = true then some r else _)
    cases r.1.data with
    | true =>
      simp only [ofBool_true, label_leaf, one_ne_zero, not_false_eq_true, ↓reduceIte]
      rfl
    | false =>
      simp only [ofBool_false, label_leaf, not_true_eq_false, Bool.false_eq_true, ↓reduceIte]
      by_cases hd : DTy.bang r.1 + c < depth
      · rw [guard_none (Nat.not_le.mpr hd)]
        simp only [hd, decide_true, ofBool_true, label_leaf, one_ne_zero, not_false_eq_true,
          ↓reduceIte]
        rfl
      · rw [guard_some (Nat.not_lt.mp hd)]
        simp only [hd, decide_false, ofBool_false, label_leaf, not_true_eq_false, ↓reduceIte]
        exact res_eq _ _
  · rw [guard_none hu]
    simp only [Bool.not_eq_true] at hu
    simp only [hu, ofBool_false, label_leaf, ne_eq, not_true_eq_false, ↓reduceIte]
    rfl

/-- The mirror's check of a child entered from a depth. -/
theorem subOf_eq (Γ : Geb.Affine.Ctx) (depth : ℕ) (o : Option (DTy × Usage)) (d : Tree) :
    «Affine.subOf» (Γ.map encEntry) (leaf depth) (encR o) d =
      encR (o >>= enter Γ depth d.label) := by
  cases o with
  | none => rfl
  | some r =>
    simp only [«Affine.subOf», encR, Option.map_some, bindO_eq, Option.elim_some, label_eq]
    exact enter_eq Γ depth d.label r

/-! ## The constants -/

/-- The mirror's type of iteration. -/
theorem iterD_eq (a : DTy) : «Affine.iterD» (encD a) = encD (iterD a) := by
  have h := dMk_eq Label.tyArrow 1 [a, a]
  simp only [List.map_cons, List.map_nil] at h
  simp only [«Affine.iterD», single_eq, dShift_eq, dZero_eq]
  rw [show (leaf 3 : Tree) = leaf Label.tyArrow from rfl, h]
  simp only [dArrow_eq]
  rfl

/-- The mirror's type of the folds of trees. -/
theorem foldD_eq (a : DTy) : «Affine.foldD» (encD a) = encD (foldD a) := by
  have h := dMk_eq Label.tyArrow 1 [zero (leaf 0), arrow (DTy.list a) a]
  simp only [List.map_cons, List.map_nil] at h
  simp only [«Affine.foldD», single_eq, dShift_eq, dZero_eq, dList_eq, dArrow_eq]
  rw [show (leaf 3 : Tree) = leaf Label.tyArrow from rfl, h, dArrow_eq]
  rfl

/-- The mirror's type of the right fold of lists. -/
theorem foldrD_eq (a b : DTy) : «Affine.foldrD» (encD a) (encD b) = encD (foldrD a b) := by
  have h := dMk_eq Label.tyArrow 1 [DTy.unbox a, arrow b b]
  simp only [List.map_cons, List.map_nil] at h
  simp only [«Affine.foldrD», single_eq, dShift_eq, dUnbox_eq, dList_eq, dArrow_eq]
  rw [show (leaf 3 : Tree) = leaf Label.tyArrow from rfl, h]
  simp only [dArrow_eq]
  rfl

/-- The mirror's type of case analysis of lists. -/
theorem lcaseD_eq (a b : DTy) : «Affine.lcaseD» (encD a) (encD b) = encD (lcaseD a b) := by
  simp only [«Affine.lcaseD», dList_eq, dArrow_eq]
  rfl

/-! ## The rules' results -/

/-- A conditional on a truth value of the mirror. -/
theorem if_ofBool {α : Type} (b : Bool) (x y : α) :
    (if (ofBool b).label ≠ 0 then x else y) = if b = true then x else y := by
  cases b <;> rfl

/-- Decorated types' encodings are equal exactly when the decorated types are. -/
theorem encD_inj {a b : DTy} : encD a = encD b ↔ a = b :=
  ⟨fun h ↦ encWith_inj _ _ (fun _ _ hl hd ↦ Prod.ext hl (leaf_inj.mp hd)) h, congrArg encD⟩

/-- The mirror's test of a root's having no {lit}`!` to derelict. -/
theorem noBang_eq (d : DTy) :
    «Affine.noBang» (encD d) = ofBool (d.data || decide (DTy.bang d = 0)) := by
  simp only [«Affine.noBang», dData_eq, dBang_eq, eq_leaf, or_eq, beq_eq_decide]

/-- The mirror's projection of a term that is not a place. -/
theorem project_eq (i : ℕ) (r : DTy × Usage) :
    «Affine.project» (leaf i) (encRes r) = encR (project i r) := by
  unfold «Affine.project» Geb.Affine.project
  simp only [rD_eq, label_encD, eq_leaf, noBang_eq, and_eq, dKids_eq, nth_eq, List.getElem?_map,
    if_ofBool, mapO_eq]
  by_cases h : r.1.label.1 = Label.tyProd ∧ (r.1.data || decide (DTy.bang r.1 = 0)) = true
  · rw [guard_some h]
    have hb : (r.1.label.1 == 2 && (r.1.data || decide (DTy.bang r.1 = 0))) = true := by
      rw [Bool.and_eq_true, beq_iff_eq]
      exact h
    rw [ite_eq_left hb]
    cases r.1.children[i]? with
    | none => rfl
    | some c =>
      simp only [encRes, Option.map_some, child_node, List.getD_cons_succ, List.getD_cons_zero]
      rfl
  · rw [guard_none h]
    have hb : ¬ (r.1.label.1 == 2 && (r.1.data || decide (DTy.bang r.1 = 0))) = true := by
      rw [Bool.and_eq_true, beq_iff_eq]
      exact h
    rw [ite_eq_right hb]
    rfl

/-- The mirror's paths of a list of occurrences at the variable of index zero. -/
theorem paths0_eq (u : Usage) :
    List.foldr (fun x3 x4 ↦
        if (Const.eq («Affine.plVar» x3) (leaf 0)).label ≠ 0 then «Affine.plPath» x3 :: x4 else x4)
      [] (u.map encPl) =
      (u.filterMap fun x ↦ if x.1 = 0 then some x.2 else none).map encPath := by
  refine u.rec rfl fun x r ih ↦ ?_
  simp only [List.map_cons, List.foldr_cons, ih, plVar_eq, plPath_eq, eq_leaf, if_ofBool,
    List.filterMap_cons, beq_iff_eq]
  by_cases h : x.1 = 0 <;> simp only [h, ↓reduceIte, List.map_cons]

/-- The mirror's occurrences at the other variables, each index one less. -/
theorem pathsRest_eq (u : Usage) :
    List.foldr (fun x3 x4 ↦
        if (Const.eq («Affine.plVar» x3) (leaf 0)).label ≠ 0 then x4
        else «Affine.plMk» (Const.sub («Affine.plVar» x3) (leaf 1)) («Affine.plPath» x3) :: x4)
      [] (u.map encPl) =
      (u.filterMap fun x ↦ if x.1 = 0 then none else some (x.1 - 1, x.2)).map encPl := by
  refine u.rec rfl fun x r ih ↦ ?_
  simp only [List.map_cons, List.foldr_cons, ih, plVar_eq, plPath_eq, eq_leaf, if_ofBool,
    List.filterMap_cons, beq_iff_eq, sub_leaf, plMk_eq]
  by_cases h : x.1 = 0 <;> simp only [h, ↓reduceIte, List.map_cons]

/-- The mirror's abstraction, from its variable's decorated type and its body's check. -/
theorem abstraction_eq (a : DTy) (rb : DTy × Usage) :
    «Affine.abstraction» (encD a) (encRes rb) = encR (abstraction a rb) := by
  unfold «Affine.abstraction» Geb.Affine.abstraction
  simp only [rU_eq, foldr_eq, paths0_eq, pathsRest_eq, contracts_eq, if_ofBool, rD_eq, dArrow_eq,
    res_eq]
  by_cases h : DTy.contracts (rb.2.filterMap fun x ↦ if x.1 = 0 then some x.2 else none) a = true
  · rw [ite_eq_left h, guard_some h]
    rfl
  · rw [ite_eq_right h, guard_none h]
    rfl

/-- The mirror's case analysis of lists applied to all its arguments. -/
theorem lcaseSat_eq (A B : Tree) (rl rn rc : DTy × Usage) :
    «Affine.lcaseSat» A B (encRes rl) (encRes rn) (encRes rc) = encR (lcaseSat A B rl rn rc) := by
  obtain ⟨dl, ul⟩ := rl
  obtain ⟨dn, un⟩ := rn
  obtain ⟨dc, uc⟩ := rc
  unfold «Affine.lcaseSat» Geb.Affine.lcaseSat
  simp only [rD_eq, rU_eq, dTy_eq, dKids_eq, noBang_eq, length_eq, List.length_map, eq_leaf,
    equal_eq, and_eq, if_ofBool, kTyList_eq, kTyArrow_eq]
  by_cases h1 : dl.ty = tList A ∧ dn.ty = B ∧ dc.ty = tArrow A (tArrow (tList A) B)
  · rw [guard_some h1]
    obtain ⟨h1a, h1b, h1c⟩ := h1
    by_cases h2 : (dl.data || decide (DTy.bang dl = 0)) = true
    · rw [guard_some h2]
      simp only [h1a, h1b, h1c, decide_true, Bool.true_and, h2]
      rcases hk : dc.children with _ | ⟨ca, _ | ⟨cr, _ | ⟨x, xs⟩⟩⟩
      · rfl
      · rfl
      · simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceBEq,
          ↓reduceIte, List.map_cons, List.map_nil, at_eq, List.getD_cons_zero, List.getD_cons_succ,
          dKids_eq, List.length_map, eq_leaf, dBang_eq, and_eq, if_ofBool]
        rcases hk' : cr.children with _ | ⟨crl, _ | ⟨crb, _ | ⟨y, ys⟩⟩⟩
        · rfl
        · rfl
        · have hs : «Prelude.some» (encD ca) = «Prelude.nth» (dl.children.map encD) (leaf 0) ↔
              some ca = dl.children[0]? := by
            rw [nth_eq, List.getElem?_map, some_eq, encOpt_inj]
            cases dl.children[0]? with
            | none => exact ⟨fun h ↦ (by cases h), fun h ↦ (by cases h)⟩
            | some x =>
              simp only [Option.map_some, Option.some.injEq, encD_inj]
          have hc : (([crl, crb].length == 2 && ((DTy.bang dc == 0) && ((DTy.bang cr == 0) &&
              (decide («Prelude.some» (encD ca) = «Prelude.nth» (dl.children.map encD) (leaf 0)) &&
                (decide (([crl, crb].map encD).getD 0 (leaf 0) = encD dl) &&
                  decide (([crl, crb].map encD).getD 1 (leaf 0) = encD dn)))))) = true) ↔
              (DTy.bang dc = 0 ∧ DTy.bang cr = 0 ∧ some ca = dl.children[0]? ∧ crl = dl ∧
                crb = dn) := by
            simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.map_cons,
              List.getD_cons_zero, List.getD_cons_succ, encD_inj, hs, List.length_cons,
              List.length_nil, zero_add, Nat.reduceAdd, true_and]
          change _ = encR (guard (DTy.bang dc = 0 ∧ DTy.bang cr = 0 ∧ some ca = dl.children[0]? ∧
            crl = dl ∧ crb = dn) >>= fun _ ↦ some (dn, ul ++ Usage.max un uc))
          by_cases h3 : DTy.bang dc = 0 ∧ DTy.bang cr = 0 ∧ some ca = dl.children[0]? ∧ crl = dl ∧
              crb = dn
          · rw [ite_eq_left (hc.mpr h3), guard_some h3, usageMax_eq, append_eq, ← List.map_append]
            exact res_eq _ _
          · rw [ite_eq_right (fun e ↦ h3 (hc.mp e)), guard_none h3]
            rfl
        · have hb : (ys.length + 1 + 1 + 1 == 2) = false := rfl
          simp only [List.length_cons, hb, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
          rfl
      · have hb : (xs.length + 1 + 1 + 1 == 2) = false := rfl
        simp only [List.length_cons, hb, Bool.false_eq_true, ↓reduceIte]
        rfl
    · rw [guard_none h2]
      simp only [h2, Bool.false_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      rfl
  · rw [guard_none h1]
    have : ¬ (decide (dl.ty = tList A) && (decide (dn.ty = B) &&
        (decide (dc.ty = tArrow A (tArrow (tList A) B)) &&
          ((dl.data || decide (DTy.bang dl = 0)) && (dc.children.length == 2))))) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact fun h ↦ h1 ⟨h.1, h.2.1, h.2.2.1⟩
    rw [ite_eq_right this]
    rfl

/-! ## The rules of the check -/

/-- The mirror's check of a term: from a mode, instances, a context and a tree. -/
abbrev MSem : Type := Tree → List Tree → List Tree → Tree → Tree

/-- The mirror's check of a child related to a Lean one: at mode zero, at encoded instances and
context, it is the encoding of the Lean check. -/
def SemRel (m : MSem) (s : Geb.Affine.Sem) : Prop :=
  ∀ (E : Env) (Γ : Geb.Affine.Ctx) (D : Tree),
    m (leaf 0) (E.map encInst) (Γ.map encEntry) D = encR (s E Γ D)

/-- The mirror's binding of a result of a check. -/
theorem bindR_eq (o : Option (DTy × Usage)) (f : Tree → Tree)
    (g : DTy × Usage → Option (DTy × Usage))
    (h : ∀ r, f (encRes r) = encR (g r)) : «Base.bindO» (encR o) f = encR (o >>= g) := by
  cases o with
  | none => rfl
  | some r =>
    simp only [encR, Option.map_some, bindO_eq, Option.elim_some] at h ⊢
    exact h r

/-- The mirror's test of a condition on a result. -/
theorem one_eq (b : Bool) (x : Tree) :
    «Affine.one» (ofBool b) x = if b = true then x else encR none := by
  cases b <;> rfl

/-- The mirror's test of a list's length, at another length. -/
theorem one_len {ds : List Tree} {k : ℕ} (h : ds.length ≠ k) (x : Tree) :
    «Affine.one» (Const.eq («Prelude.length» ds) (leaf k)) x = encR none := by
  rw [length_eq, eq_leaf, beq_eq_false_iff_ne.mpr h]
  rfl

/-- The mirror's check of a child, entered from a depth. -/
theorem subAt_eq {m : MSem} {s : Geb.Affine.Sem} (h : SemRel m s)
    (E : Env) (Γ : Geb.Affine.Ctx) (depth : ℕ) (d : Tree) :
    «Affine.subAt» m (E.map encInst) (Γ.map encEntry) (leaf depth) d =
      encR (s E Γ d >>= enter Γ depth d.label) := by
  simp only [«Affine.subAt», h E Γ d, subOf_eq]

/-- A list of at least three elements does not have two. -/
theorem beq_len3_2 (n : ℕ) : (n + 1 + 1 + 1 == 2) = false := rfl

/-- A list of at least four elements does not have three. -/
theorem beq_len4_3 (n : ℕ) : (n + 1 + 1 + 1 + 1 == 3) = false := rfl

/-- Rewrites the mirror's primitives, tests and results at encoded arguments, with further lemmas.
-/
local macro "aff_simp" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  simp only [length_eq, List.length_cons, List.length_nil, List.length_map, zero_add, Nat.reduceAdd,
    eq_leaf, Nat.reduceBEq, one_eq, if_ofBool, ↓reduceIte, at_eq, List.getD_cons_zero,
    List.getD_cons_succ, List.map_cons, List.map_nil, rD_eq, rU_eq, dTy_eq, dKids_eq, dBang_eq,
    dData_eq, label_encD, equal_eq, encD_inj, and_eq, or_eq, append_eq, ← List.map_append,
    usageMax_eq, res_eq, Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false,
    Bool.false_eq_true, single_eq, $ls,*])

/-- The rule of an application to two arguments. -/
theorem semApp_eq {mf mx : MSem} {sf sx : Geb.Affine.Sem}
    (hf : SemRel mf sf) (hx : SemRel mx sx) (E : Env) (Γ : Geb.Affine.Ctx) (depth : ℕ)
    (df dx : Tree) :
    «Affine.semApp» mf mx (E.map encInst) (Γ.map encEntry) (leaf depth) [df, dx] =
      encR (do
        let (rf, uf) ← sf E Γ df >>= enter Γ depth df.label
        let (rx, ux) ← sx E Γ dx >>= enter Γ depth dx.label
        let [a, b] := rf.children | none
        guard (rf.label.1 = Label.tyArrow ∧ DTy.bang rf = 0 ∧ a = rx)
        some (b, uf ++ ux)) := by
  aff_simp [«Affine.semApp», subAt_eq hf, subAt_eq hx]
  refine bindR_eq _ _ _ fun rf ↦ bindR_eq _ _ _ fun rx ↦ ?_
  obtain ⟨dF, uf⟩ := rf
  obtain ⟨dX, ux⟩ := rx
  aff_simp []
  rcases hk : dF.children with _ | ⟨a, _ | ⟨b, _ | ⟨y, ys⟩⟩⟩
  · rfl
  · rfl
  · aff_simp []
    change _ = encR (guard (dF.label.1 = Label.tyArrow ∧ DTy.bang dF = 0 ∧ a = dX) >>=
      fun _ ↦ some (b, uf ++ ux))
    by_cases h : dF.label.1 = Label.tyArrow ∧ DTy.bang dF = 0 ∧ a = dX
    · rw [guard_some h]
      obtain ⟨h1, h2, h3⟩ := h
      have hb : (dF.label.1 == 3 && ((DTy.bang dF == 0) && decide (a = dX))) = true := by
        rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq, decide_eq_true_eq]
        exact ⟨h1, h2, h3⟩
      rw [hb, ite_eq_left rfl]
      rfl
    · rw [guard_none h]
      have hb : ¬ (dF.label.1 == 3 && ((DTy.bang dF == 0) && decide (a = dX))) = true := by
        rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq, decide_eq_true_eq]
        exact h
      rw [ite_eq_right hb]
      rfl
  · have hb : (ys.length + 1 + 1 + 1 == 2) = false := rfl
    aff_simp [hb]

/-- The rule of a pair. -/
theorem semPair_eq {ma mb : MSem} {sa sb : Geb.Affine.Sem}
    (ha : SemRel ma sa) (hb : SemRel mb sb) (E : Env) (Γ : Geb.Affine.Ctx) (depth : ℕ)
    (da db : Tree) :
    «Affine.semPair» ma mb (E.map encInst) (Γ.map encEntry) (leaf depth) [da, db] =
      encR (do
        let (ra, ua) ← sa E Γ da >>= enter Γ depth da.label
        let (rb, ub) ← sb E Γ db >>= enter Γ depth db.label
        some (DTy.mk Label.tyProd 0 [ra, rb], ua ++ ub)) := by
  aff_simp [«Affine.semPair», subAt_eq ha, subAt_eq hb]
  refine bindR_eq _ _ _ fun ra ↦ bindR_eq _ _ _ fun rb ↦ ?_
  have h := dMk_eq Label.tyProd 0 [ra.1, rb.1]
  simp only [List.map_cons, List.map_nil] at h
  aff_simp []
  rw [show (leaf 2 : Tree) = leaf Label.tyProd from rfl, h]
  exact res_eq _ _

/-- The rule of a conditional. -/
theorem semCond_eq {mc ma mb : MSem} {sc sa sb : Geb.Affine.Sem}
    (hc : SemRel mc sc) (ha : SemRel ma sa) (hb : SemRel mb sb) (E : Env) (Γ : Geb.Affine.Ctx)
    (depth : ℕ) (dc da db : Tree) :
    «Affine.semCond» mc ma mb (E.map encInst) (Γ.map encEntry) (leaf depth) [dc, da, db] =
      encR (do
        let (rc, uc) ← sc E Γ dc >>= enter Γ depth dc.label
        let (ra, ua) ← sa E Γ da >>= enter Γ depth da.label
        let (rb, ub) ← sb E Γ db >>= enter Γ depth db.label
        guard (rc.ty = tT ∧ ra = rb)
        some (ra, uc ++ Usage.max ua ub)) := by
  aff_simp [«Affine.semCond», subAt_eq hc, subAt_eq ha, subAt_eq hb]
  refine bindR_eq _ _ _ fun rc ↦ bindR_eq _ _ _ fun ra ↦ bindR_eq _ _ _ fun rb ↦ ?_
  obtain ⟨dC, uc⟩ := rc
  obtain ⟨dA, ua⟩ := ra
  obtain ⟨dB, ub⟩ := rb
  aff_simp []
  change _ = encR (guard (DTy.ty dC = tT ∧ dA = dB) >>= fun _ ↦ some (dA, uc ++ Usage.max ua ub))
  by_cases h : DTy.ty dC = tT ∧ dA = dB
  · rw [guard_some h]
    have ht : DTy.ty dC = leaf 0 := h.1
    simp only [ht, decide_true, Bool.true_and, h.2, ↓reduceIte]
    rfl
  · rw [guard_none h]
    have hn : ¬ (decide (DTy.ty dC = leaf 0) && decide (dA = dB)) = true := by
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      exact h
    rw [ite_eq_right hn]
    rfl

/-- The rule of a list's head on a tail. -/
theorem semCons_eq {mx ml : MSem} {sx sl : Geb.Affine.Sem}
    (hx : SemRel mx sx) (hl : SemRel ml sl) (E : Env) (Γ : Geb.Affine.Ctx) (depth : ℕ)
    (dx dl : Tree) :
    «Affine.semCons» mx ml (E.map encInst) (Γ.map encEntry) (leaf depth) [dx, dl] =
      encR (do
        let (rx, ux) ← sx E Γ dx >>= enter Γ depth dx.label
        let (rl, ul) ← sl E Γ dl >>= enter Γ depth dl.label
        guard (rl.ty = tList rx.ty ∧ (rl.data || (DTy.bang rl = 0 ∧ rl.children = [rx])))
        some (DTy.list rx, ux ++ ul)) := by
  aff_simp [«Affine.semCons», subAt_eq hx, subAt_eq hl]
  refine bindR_eq _ _ _ fun rx ↦ bindR_eq _ _ _ fun rl ↦ ?_
  obtain ⟨dX, ux⟩ := rx
  obtain ⟨dL, ul⟩ := rl
  have hc : Const.node (leaf 0) (dL.children.map encD) = Const.node (leaf 0) [encD dX] ↔
      dL.children = [dX] := by
    rw [node_leaf, node_leaf, node_inj]
    constructor
    · intro h
      exact map_inj_of_mem encD _ (fun _ _ _ e ↦ encD_inj.mp e) [dX] h.2
    · intro h
      simp only [h, List.map_cons, List.map_nil, and_self]
  aff_simp [kTyList_eq, hc, dList_eq]
  change _ = encR (guard (DTy.ty dL = tList (DTy.ty dX) ∧
    (dL.data || (DTy.bang dL = 0 ∧ dL.children = [dX]))) >>= fun _ ↦ some (DTy.list dX, ux ++ ul))
  have hb : (decide (DTy.ty dL = tList (DTy.ty dX)) && (dL.data || ((DTy.bang dL == 0) &&
      decide (dL.children = [dX])))) = decide (DTy.ty dL = tList (DTy.ty dX) ∧
        (dL.data || (DTy.bang dL = 0 ∧ dL.children = [dX]))) := by
    simp only [Bool.decide_and, beq_eq_decide, Bool.decide_eq_true]
  rw [hb]
  by_cases h : DTy.ty dL = tList (DTy.ty dX) ∧
      (dL.data || (DTy.bang dL = 0 ∧ dL.children = [dX]))
  · rw [guard_some h, decide_eq_true h, ite_eq_left rfl]
    rfl
  · rw [guard_none h, decide_eq_false h]
    rfl

/-- The rule of a constant at one type: the empty list, iteration or a fold of trees. -/
theorem semOne_eq (l : ℕ) (A dA : Tree) :
    «Affine.semOne» (leaf l) [A] [dA] = encR (do
      guard (Ty.IsTy A)
      let a ← decorate A dA
      some (if l = 19 then DTy.list a else if l = 18 then iterD a else foldD a, [])) := by
  aff_simp [«Affine.semOne», isTy_eq, decorate_eq]
  cases hA : Ty.IsTy A with
  | false =>
    rw [guard_none (by simp)]
    rfl
  | true =>
    rw [guard_some rfl]
    cases decorate A dA with
    | none => rfl
    | some a =>
      have e : (if (ofBool (l == 19)).label ≠ 0 then «Affine.dList» (encD a)
          else if (ofBool (l == 18)).label ≠ 0 then «Affine.iterD» (encD a)
          else «Affine.foldD» (encD a)) =
          encD (if l = 19 then DTy.list a else if l = 18 then iterD a else foldD a) := by
        by_cases h19 : l = 19
        · subst h19
          exact dList_eq a
        · by_cases h18 : l = 18
          · subst h18
            exact iterD_eq a
          · have h19' : (l == 19) = false := beq_eq_false_iff_ne.mpr h19
            have h18' : (l == 18) = false := beq_eq_false_iff_ne.mpr h18
            simp only [h19', h18', h19, h18, ofBool_false, label_leaf, ne_eq, not_true_eq_false,
              ↓reduceIte]
            exact foldD_eq a
      simp only [Option.map_some, bindO_eq, Option.elim_some]
      exact (congrArg (fun x ↦ «Affine.res» x []) e).trans (res_eq _ [])

/-- The rule of a constant at two types: the right fold of lists or case analysis of them. -/
theorem semTwo_eq (l : ℕ) (A B dA dB : Tree) :
    «Affine.semTwo» (leaf l) [A, B] [dA, dB] = encR (do
      guard (Ty.IsTy A && Ty.IsTy B)
      let a ← decorate A dA
      let b ← decorate B dB
      if l = Label.lcase then some (lcaseD a b, [])
      else do
        guard (a.data || 1 ≤ DTy.bang a)
        some (foldrD a b, [])) := by
  aff_simp [«Affine.semTwo», isTy_eq, decorate_eq]
  cases hA : Ty.IsTy A && Ty.IsTy B with
  | false =>
    rw [guard_none (by simp)]
    rfl
  | true =>
    rw [guard_some rfl]
    simp only [↓reduceIte]
    cases decorate A dA with
    | none => rfl
    | some a =>
      simp only [Option.map_some, bindO_eq, Option.elim_some]
      cases decorate B dB with
      | none => rfl
      | some b =>
        aff_simp [Option.map_some, bindO_eq, Option.elim_some, beq_iff_eq, lcaseD_eq, lt_leaf,
          foldrD_eq, Label.lcase]
        by_cases hl : l = 24
        · simp only [hl, ↓reduceIte]
          exact res_eq _ []
        · simp only [hl, ↓reduceIte]
          by_cases hb : (a.data || decide (0 < DTy.bang a)) = true
          · have hb' : (a.data || decide (1 ≤ DTy.bang a)) = true := hb
            change _ = encR (guard ((a.data || decide (1 ≤ DTy.bang a)) = true) >>=
              fun _ ↦ some (foldrD a b, []))
            rw [ite_eq_left hb, guard_some hb']
            exact res_eq _ []
          · have hb' : ¬ (a.data || decide (1 ≤ DTy.bang a)) = true := hb
            change _ = encR (guard ((a.data || decide (1 ≤ DTy.bang a)) = true) >>=
              fun _ ↦ some (foldrD a b, []))
            rw [ite_eq_right hb, guard_none hb']
            rfl

/-- The rule of a primitive. -/
theorem semPrim_eq (k : Tree) :
    «Affine.semPrim» [k] [] = encR (prims[k.label]?.map fun g ↦ (zero g.1, [])) := by
  aff_simp [«Affine.semPrim», isEmpty_eq, List.isEmpty_nil, kPrimTypes_eq, label_eq, nth_eq,
    List.getElem?_map]
  cases prims[k.label]? with
  | none => rfl
  | some g =>
    simp only [Option.map_some, mapO_eq, dZero_eq, node_leaf]
    rfl

/-- The rule of a reference. -/
theorem semRef_eq (E : Env) (n di dk : Tree) :
    «Affine.semRef» (E.map encInst) [n] [di, dk] = encR (do
      let (i, d) ← E[di.label]?
      guard (i = n.label ∧ di.children = [] ∧ dk.children = [])
      some (DTy.shift d dk.label, [])) := by
  aff_simp [«Affine.semRef», label_eq, nth_eq, List.getElem?_map]
  cases hE : E[di.label]? with
  | none => rfl
  | some e =>
    obtain ⟨i, d⟩ := e
    aff_simp [Option.map_some, bindO_eq, Option.elim_some, encInst, child_node, dShift_eq,
      isEmpty_eq, children_eq, Option.bind_some]
    change _ = encR (guard (i = n.label ∧ di.children = [] ∧ dk.children = []) >>=
      fun _ ↦ some (DTy.shift d dk.label, []))
    by_cases h : i = n.label ∧ di.children = [] ∧ dk.children = []
    · rw [guard_some h]
      obtain ⟨h1, h2, h3⟩ := h
      simp only [h1, beq_self_eq_true, h2, h3, List.isEmpty_nil, Bool.and_self, ↓reduceIte]
      exact res_eq _ []
    · rw [guard_none h]
      have hb : ¬ ((i == n.label) && (di.children.isEmpty && dk.children.isEmpty)) = true := by
        rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff, List.isEmpty_iff]
        exact h
      rw [ite_eq_right hb]
      rfl

/-- The rule of a projection of a term. -/
theorem semProj_eq {m : MSem} {s : Geb.Affine.Sem} (hs : SemRel m s) (i : ℕ) (E : Env)
    (Γ : Geb.Affine.Ctx) (depth : ℕ) (c : Tree) (ds : List Tree) :
    «Affine.semProj» (leaf i) m (E.map encInst) (Γ.map encEntry) (leaf depth) [c] ds =
      encR (match Geb.Affine.place c, ds with
        | some (n, q), [] => occurrence Γ depth (n, q ++ [i])
        | none, [dp] => s E Γ dp >>= enter Γ depth dp.label >>= project i
        | _, _ => none) := by
  have hb : ∀ o, «Base.bindO» (encR o) («Affine.project» (leaf i)) = encR (o >>= project i) :=
    fun o ↦ bindR_eq o _ _ (project_eq i)
  aff_simp [«Affine.semProj», termPlace_eq, isSome_eq, isEmpty_eq]
  cases hp : Geb.Affine.place c with
  | none =>
    match ds with
    | [] => rfl
    | [dp] =>
      aff_simp [Option.map_none, Option.isSome_none, subAt_eq hs]
      exact hb _
    | x :: y :: r =>
      have hk : (r.length + 1 + 1 == 1) = false := rfl
      aff_simp [Option.map_none, Option.isSome_none, hk]
  | some pl =>
    obtain ⟨n, q⟩ := pl
    match ds with
    | [] =>
      aff_simp [Option.map_some, Option.isSome_some, List.isEmpty_nil, get_encOpt,
        Option.getD_some, plVar_eq, plPath_eq, snocPath_eq, plMk_eq, occurrence_eq]
    | x :: r =>
      aff_simp [Option.map_some, Option.isSome_some, List.isEmpty_cons]

/-- The rule of an abstraction. -/
theorem semLam_eq {m : MSem} {s : Geb.Affine.Sem} (hs : SemRel m s) (E : Env)
    (Γ : Geb.Affine.Ctx) (depth : ℕ) (A b dA db : Tree) :
    «Affine.semLam» m (E.map encInst) (Γ.map encEntry) (leaf depth) [A, b] [dA, db] =
      encR (do
        guard (Ty.IsTy A)
        let a ← decorate A dA
        let Γ' := (a, depth) :: Γ
        abstraction a (← s E Γ' db >>= enter Γ' depth db.label)) := by
  aff_simp [«Affine.semLam», isTy_eq, decorate_eq]
  cases hA : Ty.IsTy A with
  | false =>
    rw [guard_none (by simp)]
    rfl
  | true =>
    rw [guard_some rfl]
    cases decorate A dA with
    | none => rfl
    | some a =>
      simp only [Option.map_some, bindO_eq, Option.elim_some, ↓reduceIte]
      have hG : RoseTree.node 0 [encD a, leaf depth] :: Γ.map encEntry =
          ((a, depth) :: Γ).map encEntry := rfl
      simp only [node_leaf, hG, subAt_eq hs]
      exact bindR_eq _ _ _ (abstraction_eq a)

/-- The rule of case analysis of lists applied to all its arguments. -/
theorem semSat_eq {mf mx : MSem} {sl sn sx : Geb.Affine.Sem} (A B : Tree) (f : Tree)
    (hA : «Affine.spineTy» f (leaf 0) = A) (hB : «Affine.spineTy» f (leaf 1) = B)
    (hf : ∀ (E : Env) (Γ : Geb.Affine.Ctx) (dl dn : Tree),
      mf (leaf 1) (E.map encInst) (Γ.map encEntry) (RoseTree.node 0 [dl, dn]) =
        RoseTree.node 0 [encR (sl E Γ dl), encR (sn E Γ dn)])
    (hx : SemRel mx sx) (E : Env) (Γ : Geb.Affine.Ctx) (depth : ℕ) (dl dn dc : Tree) :
    «Affine.semSat» f mf mx (E.map encInst) (Γ.map encEntry) (leaf depth) [dl, dn, dc] =
      encR (do
        lcaseSat A B (← sl E Γ dl >>= enter Γ depth dl.label)
          (← sn E Γ dn >>= enter Γ depth dn.label)
          (← sx E Γ dc >>= enter Γ depth dc.label)) := by
  aff_simp [«Affine.semSat», hA, hB, node_leaf, hf, children_eq, RoseTree.children_node, subOf_eq,
    subAt_eq hx]
  exact bindR_eq _ _ _ fun rl ↦ bindR_eq _ _ _ fun rn ↦ bindR_eq _ _ _ fun rc ↦
    lcaseSat_eq A B rl rn rc

/-! ## The spine of case analysis of lists -/

/-- The check of a term, with its spine. -/
abbrev checkOf (t : Tree) : Geb.Affine.Sem × Spine := RoseTree.para step t

/-- Each child with its check and spine. -/
abbrev kids (cs : List Tree) : List (Tree × Geb.Affine.Sem × Spine) :=
  cs.map fun c ↦ (c, checkOf c)

/-- The term of case analysis of lists applied to two arguments. -/
def spine2 (A B l n : Tree) : Tree :=
  RoseTree.node Label.app
    [RoseTree.node Label.app [RoseTree.node Label.lcase [A, B], l], n]

/-- The spine of a node. -/
theorem spine_node (l : ℕ) (cs : List Tree) :
    (checkOf (RoseTree.node l cs)).2 = spine l (kids cs) := by
  simp only [checkOf, RoseTree.para_node]
  rfl

/-- The check of a node. -/
theorem check_node (l : ℕ) (cs : List Tree) :
    (checkOf (RoseTree.node l cs)).1 = Geb.Affine.semStep l (kids cs) := by
  simp only [checkOf, RoseTree.para_node]
  rfl

/-- A node with a spine is case analysis of lists or an application of a term with a spine. -/
theorem spine_some {l : ℕ} {cs : List Tree} {A B : Tree} {ss : List Geb.Affine.Sem}
    (h : spine l (kids cs) = some (A, B, ss)) :
    (l = Label.lcase ∧ cs = [A, B] ∧ ss = []) ∨
      (l = Label.app ∧ ∃ f x ss', cs = [f, x] ∧ (checkOf f).2 = some (A, B, ss') ∧
        ss = ss' ++ [(checkOf x).1]) := by
  by_cases hl : l = Label.lcase
  · subst hl
    match cs, h with
    | [a, b], h =>
      change some (a, b, []) = some (A, B, ss) at h
      obtain ⟨rfl, rfl, rfl⟩ : a = A ∧ b = B ∧ [] = ss := by
        simpa only [Option.some.injEq, Prod.mk.injEq] using h
      exact Or.inl ⟨rfl, rfl, rfl⟩
    | [], h | [_], h | _ :: _ :: _ :: _, h =>
      change none = _ at h
      cases h
  by_cases hl' : l = Label.app
  · subst hl'
    match cs, h with
    | [f, x], h =>
      cases hp : (checkOf f).2 with
      | none =>
        have : spine Label.app (kids [f, x]) = none := by
          change spine Label.app [(f, (checkOf f).1, (checkOf f).2), (x, checkOf x)] = none
          rw [hp]
          rfl
        rw [this] at h
        cases h
      | some p =>
        obtain ⟨A', B', ss'⟩ := p
        have : spine Label.app (kids [f, x]) = some (A', B', ss' ++ [(checkOf x).1]) := by
          change spine Label.app [(f, (checkOf f).1, (checkOf f).2), (x, checkOf x)] = _
          rw [hp]
          rfl
        rw [this] at h
        obtain ⟨rfl, rfl, rfl⟩ : A' = A ∧ B' = B ∧ ss' ++ [(checkOf x).1] = ss := by
          simpa only [Option.some.injEq, Prod.mk.injEq] using h
        exact Or.inr ⟨rfl, f, x, ss', rfl, hp, rfl⟩
    | [], h =>
      change none = _ at h
      cases h
    | [a], h =>
      change spine Label.app [(a, (checkOf a).1, (checkOf a).2)] = _ at h
      cases hp : (checkOf a).2 with
      | none =>
        rw [hp] at h
        change none = _ at h
        cases h
      | some p =>
        rw [hp] at h
        change none = _ at h
        cases h
    | a :: b :: c :: r, h =>
      change spine Label.app ((a, (checkOf a).1, (checkOf a).2) :: (b, checkOf b) ::
        kids (c :: r)) = _ at h
      cases hp : (checkOf a).2 with
      | none =>
        rw [hp] at h
        change none = _ at h
        cases h
      | some p =>
        rw [hp] at h
        change none = _ at h
        cases h
  · have : spine l (kids cs) = none := by
      unfold spine
      split
      · exact absurd rfl hl
      · exact absurd rfl hl'
      · rfl
    rw [this] at h
    cases h

/-- An application of a term with a spine has a spine. -/
theorem spine_app (f x : Tree) {A B : Tree} {ss : List Geb.Affine.Sem}
    (h : (checkOf f).2 = some (A, B, ss)) :
    (checkOf (RoseTree.node Label.app [f, x])).2 = some (A, B, ss ++ [(checkOf x).1]) := by
  rw [spine_node]
  change spine Label.app [(f, (checkOf f).1, (checkOf f).2), (x, checkOf x)] = _
  rw [h]
  rfl

/-- A term with a spine of two arguments is case analysis of lists applied to two arguments. -/
theorem spine_len {f A B : Tree} {ss : List Geb.Affine.Sem} (h : (checkOf f).2 = some (A, B, ss))
    (hl : ss.length = 2) :
    ∃ l n, f = spine2 A B l n ∧ ss = [(checkOf l).1, (checkOf n).1] := by
  obtain ⟨lf, cf, rfl⟩ : ∃ lf cf, f = RoseTree.node lf cf :=
    ⟨_, _, (RoseTree.node_label_children f).symm⟩
  rw [spine_node] at h
  rcases spine_some h with ⟨-, -, rfl⟩ | ⟨rfl, f1, n, ss1, rfl, h1, rfl⟩
  · cases hl
  obtain ⟨lf1, cf1, rfl⟩ : ∃ lf cf, f1 = RoseTree.node lf cf :=
    ⟨_, _, (RoseTree.node_label_children f1).symm⟩
  rw [spine_node] at h1
  rcases spine_some h1 with ⟨-, -, rfl⟩ | ⟨rfl, f2, l, ss2, rfl, h2, rfl⟩
  · cases hl
  obtain ⟨lf2, cf2, rfl⟩ : ∃ lf cf, f2 = RoseTree.node lf cf :=
    ⟨_, _, (RoseTree.node_label_children f2).symm⟩
  rw [spine_node] at h2
  rcases spine_some h2 with ⟨rfl, rfl, rfl⟩ | ⟨rfl, f3, x3, ss3, rfl, -, rfl⟩
  · exact ⟨l, n, rfl, rfl⟩
  · simp only [List.length_append, List.length_cons, List.length_nil] at hl
    exact absurd hl (Nat.ne_of_gt (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_pos _))))

/-- The mirror's test of case analysis of lists applied to two arguments holds of it. -/
theorem isSpine2_spine2 (A B l n : Tree) :
    «Affine.isSpine2» (spine2 A B l n) = leaf 1 := rfl

/-- The mirror's test of case analysis of lists applied to two arguments holds only of it. -/
theorem isSpine2_shape {f : Tree} (h : («Affine.isSpine2» f).label ≠ 0) :
    ∃ A B l n, f = spine2 A B l n := by
  have hb : ((«Affine.isSpine2» f).label != 0) = true := bne_iff_ne.mpr h
  simp only [«Affine.isSpine2», and_label, eq_label, Bool.and_eq_true, beq_iff_eq, label_eq,
    label_leaf, children_eq, length_eq, at_eq] at hb
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5, h6⟩ := hb
  obtain ⟨f1, n, hc⟩ := List.length_eq_two.mp h2
  rw [hc] at h3 h4 h5 h6
  simp only [List.getD_cons_zero] at h3 h4 h5 h6
  obtain ⟨f2, l, hc1⟩ := List.length_eq_two.mp h4
  rw [hc1] at h5 h6
  simp only [List.getD_cons_zero] at h5 h6
  obtain ⟨A, B, hc2⟩ := List.length_eq_two.mp h6
  refine ⟨A, B, l, n, ?_⟩
  rw [← RoseTree.node_label_children f, h1, hc, ← RoseTree.node_label_children f1, h3, hc1,
    ← RoseTree.node_label_children f2, h5, hc2]
  rfl

/-! ## The check of a term -/

/-- The mirror's check of a term. -/
abbrev mcheck (t : Tree) : MSem := Const.para «Affine.semThree» t

/-- The mirror's check at a node, from its first three children's. -/
theorem mcheck_node (l : ℕ) (cs : List Tree) :
    mcheck (RoseTree.node l cs) = «Affine.semStep» (RoseTree.node l cs)
      ((cs.map mcheck).getD 0 «Affine.sem0») ((cs.map mcheck).getD 1 «Affine.sem0»)
      ((cs.map mcheck).getD 2 «Affine.sem0») := by
  rw [mcheck, Const.para_node]
  match cs with
  | [] | [_] | [_, _] | _ :: _ :: _ :: _ => rfl

/-- The unfolding of the mirror's step at a node, its label and children read. -/
local macro "step_node" : tactic => `(tactic|
  (simp only [«Affine.semStep», label_eq, children_eq, RoseTree.label_node, RoseTree.children_node]
   rfl))

/-- The mirror's step at a variable. -/
theorem step_var (cs : List Tree) (r0 r1 r2 : MSem) (m : Tree) (E G : List Tree) (D : Tree) :
    «Affine.semStep» (RoseTree.node 8 cs) r0 r1 r2 m E G D =
      «Affine.semVar» G (leaf D.label) cs D.children := by
  step_node

/-- The mirror's step at an abstraction. -/
theorem step_lam (cs : List Tree) (r0 r1 r2 : MSem) (m : Tree) (E G : List Tree) (D : Tree) :
    «Affine.semStep» (RoseTree.node 9 cs) r0 r1 r2 m E G D =
      «Affine.semLam» r1 E G (leaf D.label) cs D.children := by
  step_node

/-- The mirror's step at an application at mode zero. -/
theorem step_app0 (f x : Tree) (r0 r1 r2 : MSem) (E G : List Tree) (D : Tree) :
    «Affine.semStep» (RoseTree.node 10 [f, x]) r0 r1 r2 (leaf 0) E G D =
      if («Affine.isSpine2» f).label ≠ 0 then
        «Affine.semSat» f r0 r1 E G (leaf D.label) D.children
      else «Affine.semApp» r0 r1 E G (leaf D.label) D.children := by
  step_node

/-- The mirror's step at an application at mode one. -/
theorem step_app1 (f x : Tree) (r0 r1 r2 : MSem) (E G : List Tree) (D : Tree) :
    «Affine.semStep» (RoseTree.node 10 [f, x]) r0 r1 r2 (leaf 1) E G D =
      «Affine.semSpine» r0 r1 E G D.children := by
  step_node

/-- The mirror's step at a pair. -/
theorem step_pair (cs : List Tree) (r0 r1 r2 : MSem) (m : Tree) (E G : List Tree) (D : Tree) :
    «Affine.semStep» (RoseTree.node 12 cs) r0 r1 r2 m E G D =
      «Affine.one» (Const.eq («Prelude.length» cs) (leaf 2))
        («Affine.semPair» r0 r1 E G (leaf D.label) D.children) := by
  step_node

/-- The mirror's step at a first projection. -/
theorem step_fst (cs : List Tree) (r0 r1 r2 : MSem) (m : Tree) (E G : List Tree) (D : Tree) :
    «Affine.semStep» (RoseTree.node 13 cs) r0 r1 r2 m E G D =
      «Affine.semProj» (leaf 0) r0 E G (leaf D.label) cs D.children := by
  step_node

/-- The mirror's step at a second projection. -/
theorem step_snd (cs : List Tree) (r0 r1 r2 : MSem) (m : Tree) (E G : List Tree) (D : Tree) :
    «Affine.semStep» (RoseTree.node 14 cs) r0 r1 r2 m E G D =
      «Affine.semProj» (leaf 1) r0 E G (leaf D.label) cs D.children := by
  step_node

/-- The mirror's step at a conditional. -/
theorem step_cond (cs : List Tree) (r0 r1 r2 : MSem) (m : Tree) (E G : List Tree) (D : Tree) :
    «Affine.semStep» (RoseTree.node 16 cs) r0 r1 r2 m E G D =
      «Affine.one» (Const.eq («Prelude.length» cs) (leaf 3))
        («Affine.semCond» r0 r1 r2 E G (leaf D.label) D.children) := by
  step_node

/-- The mirror's step at a list's head on a tail. -/
theorem step_cons (cs : List Tree) (r0 r1 r2 : MSem) (m : Tree) (E G : List Tree) (D : Tree) :
    «Affine.semStep» (RoseTree.node 20 cs) r0 r1 r2 m E G D =
      «Affine.one» (Const.eq («Prelude.length» cs) (leaf 2))
        («Affine.semCons» r0 r1 E G (leaf D.label) D.children) := by
  step_node

/-- The mirror's step at a node that reads no check of a child, at mode zero. -/
theorem step_leaf (l : ℕ) (hl : l = 11 ∨ l = 15 ∨ l = 17 ∨ l = 18 ∨ l = 19 ∨ l = 21 ∨ l = 22 ∨
      l = 23 ∨ l = 24 ∨ l = 25) (cs : List Tree) (r0 r1 r2 : MSem) (E G : List Tree) (D : Tree) :
    «Affine.semStep» (RoseTree.node l cs) r0 r1 r2 (leaf 0) E G D =
      «Affine.semLeaf» (leaf l) E cs D.children := by
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> step_node

/-- The mirror's step at case analysis of lists at mode one. -/
theorem step_lcase1 (cs : List Tree) (r0 r1 r2 : MSem) (E G : List Tree) (D : Tree) :
    «Affine.semStep» (RoseTree.node 24 cs) r0 r1 r2 (leaf 1) E G D =
      RoseTree.node 0 [] := by
  step_node

/-- The mirror's check at a label without a rule. -/
theorem step_none (l : ℕ) (hl : l < 8 ∨ 26 ≤ l) (cs : List Tree) (r0 r1 r2 : MSem) (E G : List Tree)
    (D : Tree) :
    «Affine.semStep» (RoseTree.node l cs) r0 r1 r2 (leaf 0) E G D = encR none := by
  rcases hl with hl | hl
  · have h9 : (l < 9) := by omega
    have h8 : (l == 8) = false := beq_eq_false_iff_ne.mpr (by omega)
    simp only [«Affine.semStep», label_eq, RoseTree.label_node, lt_leaf, eq_leaf, h9, h8,
      decide_true, ofBool_true, ofBool_false, label_leaf, ne_eq, one_ne_zero, not_false_eq_true,
      not_true_eq_false, ↓reduceIte]
    rfl
  · obtain ⟨m, rfl⟩ : ∃ m, l = m + 26 := ⟨l - 26, by omega⟩
    rfl

/-! ## The rules at the mirror's node -/

/-- The mirror's check of a child related to the Lean check of the same child. -/
abbrev MR (c : Tree) : Prop := SemRel (mcheck c) (checkOf c).1

/-- The Lean check of a node, the children of its decoration given. -/
local macro "spec_at" h:ident : tactic => `(tactic|
  (unfold Geb.Affine.semStep; simp only [$h:ident]))

/-- The rule of a variable, at any children. -/
theorem rule_var (cs : List Tree) (E : Env) (Γ : Geb.Affine.Ctx) (D : Tree) :
    «Affine.semVar» (Γ.map encEntry) (leaf D.label) cs D.children =
      encR (Geb.Affine.semStep 8 (kids cs) E Γ D) := by
  match cs with
  | [] => aff_simp [«Affine.semVar», isEmpty_eq]; rfl
  | [n] =>
    rcases hds : D.children with _ | ⟨x, r⟩
    · spec_at hds
      exact occurrence_eq Γ D.label (n.label, [])
    · spec_at hds
      rfl
  | a :: b :: r => aff_simp [«Affine.semVar», isEmpty_eq]; rfl

/-- The rule of an abstraction, at any children. -/
theorem rule_lam (cs : List Tree) (h : ∀ c ∈ cs, MR c) (E : Env) (Γ : Geb.Affine.Ctx) (D : Tree) :
    «Affine.semLam» ((cs.map mcheck).getD 1 «Affine.sem0») (E.map encInst) (Γ.map encEntry)
        (leaf D.label) cs D.children = encR (Geb.Affine.semStep 9 (kids cs) E Γ D) := by
  match cs, h with
  | [], _ => aff_simp [«Affine.semLam», isTy_eq]; rfl
  | [_], _ => aff_simp [«Affine.semLam», isTy_eq]; rfl
  | [A, b], h =>
    have hb := h b (List.mem_cons_of_mem _ List.mem_cons_self)
    rcases hds : D.children with _ | ⟨dA, _ | ⟨db, _ | ⟨x, xs⟩⟩⟩
    · spec_at hds
      aff_simp [«Affine.semLam», isTy_eq]
      rfl
    · spec_at hds
      aff_simp [«Affine.semLam», isTy_eq]
      rfl
    · spec_at hds
      exact semLam_eq hb E Γ D.label A b dA db
    · spec_at hds
      aff_simp [«Affine.semLam», isTy_eq, beq_len3_2]
      rfl
  | _ :: _ :: _ :: _, _ => aff_simp [«Affine.semLam», isTy_eq, beq_len3_2]; rfl

/-- The rule of a pair, at any children. -/
theorem rule_pair (cs : List Tree) (h : ∀ c ∈ cs, MR c) (E : Env) (Γ : Geb.Affine.Ctx) (D : Tree) :
    «Affine.one» (Const.eq («Prelude.length» cs) (leaf 2))
        («Affine.semPair» ((cs.map mcheck).getD 0 «Affine.sem0»)
          ((cs.map mcheck).getD 1 «Affine.sem0») (E.map encInst) (Γ.map encEntry) (leaf D.label)
          D.children) = encR (Geb.Affine.semStep 12 (kids cs) E Γ D) := by
  match cs, h with
  | [], _ | [_], _ | _ :: _ :: _ :: _, _ =>
    rw [one_len (by simp only [List.length_cons, List.length_nil]; omega)]
    rfl
  | [a, b], h =>
    have ha := h a List.mem_cons_self
    have hb := h b (List.mem_cons_of_mem _ List.mem_cons_self)
    rcases hds : D.children with _ | ⟨da, _ | ⟨db, _ | ⟨x, xs⟩⟩⟩
    · spec_at hds
      rfl
    · spec_at hds
      rfl
    · spec_at hds
      exact semPair_eq ha hb E Γ D.label da db
    · spec_at hds
      aff_simp [«Affine.semPair», beq_len3_2]
      rfl

/-- The rule of a list's head on a tail, at any children. -/
theorem rule_cons (cs : List Tree) (h : ∀ c ∈ cs, MR c) (E : Env) (Γ : Geb.Affine.Ctx) (D : Tree) :
    «Affine.one» (Const.eq («Prelude.length» cs) (leaf 2))
        («Affine.semCons» ((cs.map mcheck).getD 0 «Affine.sem0»)
          ((cs.map mcheck).getD 1 «Affine.sem0») (E.map encInst) (Γ.map encEntry) (leaf D.label)
          D.children) = encR (Geb.Affine.semStep 20 (kids cs) E Γ D) := by
  match cs, h with
  | [], _ | [_], _ | _ :: _ :: _ :: _, _ =>
    rw [one_len (by simp only [List.length_cons, List.length_nil]; omega)]
    rfl
  | [a, b], h =>
    have ha := h a List.mem_cons_self
    have hb := h b (List.mem_cons_of_mem _ List.mem_cons_self)
    rcases hds : D.children with _ | ⟨da, _ | ⟨db, _ | ⟨x, xs⟩⟩⟩
    · spec_at hds
      rfl
    · spec_at hds
      rfl
    · spec_at hds
      exact semCons_eq ha hb E Γ D.label da db
    · spec_at hds
      aff_simp [«Affine.semCons», beq_len3_2]
      rfl

/-- The rule of a conditional, at any children. -/
theorem rule_cond (cs : List Tree) (h : ∀ c ∈ cs, MR c) (E : Env) (Γ : Geb.Affine.Ctx) (D : Tree) :
    «Affine.one» (Const.eq («Prelude.length» cs) (leaf 3))
        («Affine.semCond» ((cs.map mcheck).getD 0 «Affine.sem0»)
          ((cs.map mcheck).getD 1 «Affine.sem0») ((cs.map mcheck).getD 2 «Affine.sem0»)
          (E.map encInst) (Γ.map encEntry) (leaf D.label) D.children) =
      encR (Geb.Affine.semStep 16 (kids cs) E Γ D) := by
  match cs, h with
  | [], _ | [_], _ | [_, _], _ | _ :: _ :: _ :: _ :: _, _ =>
    rw [one_len (by simp only [List.length_cons, List.length_nil]; omega)]
    rfl
  | [c, a, b], h =>
    have hc := h c List.mem_cons_self
    have ha := h a (List.mem_cons_of_mem _ List.mem_cons_self)
    have hb := h b (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    rcases hds : D.children with _ | ⟨dc, _ | ⟨da, _ | ⟨db, _ | ⟨x, xs⟩⟩⟩⟩
    · spec_at hds
      rfl
    · spec_at hds
      rfl
    · spec_at hds
      rfl
    · spec_at hds
      exact semCond_eq hc ha hb E Γ D.label dc da db
    · spec_at hds
      aff_simp [«Affine.semCond», beq_len4_3]
      rfl

/-- The rule of a projection, at any children. -/
theorem rule_proj (i l : ℕ) (hl : (i = 0 ∧ l = 13) ∨ (i = 1 ∧ l = 14)) (cs : List Tree)
    (h : ∀ c ∈ cs, MR c) (E : Env) (Γ : Geb.Affine.Ctx) (D : Tree) :
    «Affine.semProj» (leaf i) ((cs.map mcheck).getD 0 «Affine.sem0») (E.map encInst)
        (Γ.map encEntry) (leaf D.label) cs D.children =
      encR (Geb.Affine.semStep l (kids cs) E Γ D) := by
  match cs, h with
  | [], _ => rcases hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  | a :: b :: r, _ =>
    have hk : (r.length + 1 + 1 == 1) = false := rfl
    rcases hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> (aff_simp [«Affine.semProj», hk]; rfl)
  | [c], h =>
    have hc := h c List.mem_cons_self
    rw [show ([c].map mcheck).getD 0 «Affine.sem0» = mcheck c from rfl, semProj_eq hc]
    cases hp : Geb.Affine.place c with
    | none =>
      rcases hds : D.children with _ | ⟨dp, _ | ⟨x, xs⟩⟩ <;>
        rcases hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        (unfold Geb.Affine.semStep; simp only [hds, kids, List.map_cons, List.map_nil, hp])
    | some pl =>
      obtain ⟨n, q⟩ := pl
      rcases hds : D.children with _ | ⟨x, xs⟩ <;>
        rcases hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        (unfold Geb.Affine.semStep; simp only [hds, kids, List.map_cons, List.map_nil, hp])

/-- The Lean rule of an application reduces at each spine other than one of two arguments. -/
local macro "spine_cases" pf:ident hne:ident : tactic => `(tactic|
  cases $pf:ident with
  | none => rfl
  | some p =>
    obtain ⟨A, B, ss⟩ := p
    match ss, $hne:ident A B ss rfl with
    | [], _ | [_], _ | _ :: _ :: _ :: _, _ => rfl)

/-- The Lean rule of an application to two decorations, whose function has no spine of two
arguments. -/
theorem spec_app_two (f x : Tree) (sf sx : Geb.Affine.Sem) (pf px : Spine)
    (hne : ∀ A B ss, pf = some (A, B, ss) → ss.length ≠ 2) (E : Env) (Γ : Geb.Affine.Ctx) (D : Tree)
    {df dx : Tree} (hds : D.children = [df, dx]) :
    Geb.Affine.semStep 10 [(f, sf, pf), (x, sx, px)] E Γ D = (do
      let (rf, uf) ← sf E Γ df >>= enter Γ D.label df.label
      let (rx, ux) ← sx E Γ dx >>= enter Γ D.label dx.label
      let [a, b] := rf.children | none
      guard (rf.label.1 = Label.tyArrow ∧ DTy.bang rf = 0 ∧ a = rx)
      some (b, uf ++ ux)) := by
  spec_at hds
  spine_cases pf hne

/-- The Lean rule of an application at another number of decorations, whose function has no spine
of two arguments. -/
theorem spec_app_other (f x : Tree) (sf sx : Geb.Affine.Sem) (pf px : Spine)
    (hne : ∀ A B ss, pf = some (A, B, ss) → ss.length ≠ 2) (E : Env) (Γ : Geb.Affine.Ctx) (D : Tree)
    (hds : D.children.length ≠ 2) :
    Geb.Affine.semStep 10 [(f, sf, pf), (x, sx, px)] E Γ D = none := by
  rcases hd : D.children with _ | ⟨d0, _ | ⟨d1, _ | ⟨d2, r⟩⟩⟩
  · spec_at hd
    spine_cases pf hne
  · spec_at hd
    spine_cases pf hne
  · rw [hd] at hds
    exact absurd rfl hds
  · spec_at hd
    spine_cases pf hne

/-- The rule of an application, from the checks of the function at its spine. -/
theorem rule_app (f x : Tree) (hf : MR f) (hx : MR x)
    (hC : ∀ A B ss, (checkOf f).2 = some (A, B, ss) →
      ∀ (E : Env) (Γ : Geb.Affine.Ctx) (ds : List Tree), ds.length = ss.length →
        mcheck f (leaf 1) (E.map encInst) (Γ.map encEntry) (RoseTree.node 0 ds) =
          RoseTree.node 0 (List.zipWith (fun s d ↦ encR (s E Γ d)) ss ds))
    (E : Env) (Γ : Geb.Affine.Ctx) (D : Tree) :
    (if («Affine.isSpine2» f).label ≠ 0 then
        «Affine.semSat» f (mcheck f) (mcheck x) (E.map encInst) (Γ.map encEntry) (leaf D.label)
          D.children
      else «Affine.semApp» (mcheck f) (mcheck x) (E.map encInst) (Γ.map encEntry) (leaf D.label)
        D.children) = encR (Geb.Affine.semStep 10 (kids [f, x]) E Γ D) := by
  by_cases hsp : («Affine.isSpine2» f).label ≠ 0
  · rw [ite_eq_left hsp]
    obtain ⟨A, B, l', n', rfl⟩ := isSpine2_shape hsp
    have hs : (checkOf (spine2 A B l' n')).2 = some (A, B, [(checkOf l').1, (checkOf n').1]) := by
      have h0 : (checkOf (RoseTree.node Label.lcase [A, B])).2 = some (A, B, []) := by
        rw [spine_node]
        rfl
      exact spine_app _ _ (spine_app _ _ h0)
    have hC' := hC A B _ hs
    have hk : kids [spine2 A B l' n', x] =
        [(spine2 A B l' n', (checkOf (spine2 A B l' n')).1,
          some (A, B, [(checkOf l').1, (checkOf n').1])), (x, (checkOf x).1, (checkOf x).2)] := by
      rw [← hs]
      rfl
    rw [hk]
    rcases hds : D.children with _ | ⟨dl, _ | ⟨dn, _ | ⟨dc, _ | ⟨y, ys⟩⟩⟩⟩
    · spec_at hds
      rfl
    · spec_at hds
      rfl
    · spec_at hds
      rfl
    · spec_at hds
      exact semSat_eq A B _ rfl rfl (fun E Γ dl dn ↦ hC' E Γ [dl, dn] rfl) hx E Γ D.label dl dn dc
    · spec_at hds
      aff_simp [«Affine.semSat», beq_len4_3]
  · rw [ite_eq_right hsp]
    have hne : ∀ A B ss, (checkOf f).2 = some (A, B, ss) → ss.length ≠ 2 := fun A B ss h hl ↦ by
      obtain ⟨l', n', rfl, -⟩ := spine_len h hl
      exact hsp (by rw [isSpine2_spine2]; exact one_ne_zero)
    change _ = encR (Geb.Affine.semStep 10 [(f, (checkOf f).1, (checkOf f).2),
      (x, (checkOf x).1, (checkOf x).2)] E Γ D)
    by_cases h2 : D.children.length = 2
    · obtain ⟨df, dx, hds⟩ := List.length_eq_two.mp h2
      rw [spec_app_two f x _ _ _ _ hne E Γ D hds, hds, semApp_eq hf hx]
    · rw [spec_app_other f x _ _ _ _ hne E Γ D h2]
      exact one_len h2 _

/-- The rule of an application at other than two children. -/
theorem rule_app_other (cs : List Tree) (h : cs.length ≠ 2) (E : Env) (Γ : Geb.Affine.Ctx)
    (D : Tree) : Geb.Affine.semStep 10 (kids cs) E Γ D = none := by
  match cs, h with
  | [], _ => rfl
  | [a], _ =>
    change Geb.Affine.semStep 10 [(a, (checkOf a).1, (checkOf a).2)] E Γ D = none
    cases (checkOf a).2 with
    | none => rfl
    | some p =>
      obtain ⟨A, B, ss⟩ := p
      match ss with
      | [] | [_] | [_, _] | _ :: _ :: _ :: _ => rfl
  | [_, _], h => exact absurd rfl h
  | a :: b :: c :: r, _ =>
    change Geb.Affine.semStep 10 ((a, (checkOf a).1, (checkOf a).2) :: (b, checkOf b) ::
      kids (c :: r)) E Γ D = none
    cases (checkOf a).2 with
    | none => rfl
    | some p =>
      obtain ⟨A, B, ss⟩ := p
      match ss with
      | [] | [_] | [_, _] | _ :: _ :: _ :: _ => rfl

/-- The rule of the unit. -/
theorem rule_unit (cs : List Tree) (E : Env) (Γ : Geb.Affine.Ctx) (D : Tree) :
    «Affine.semLeaf» (leaf 11) (E.map encInst) cs D.children =
      encR (Geb.Affine.semStep 11 (kids cs) E Γ D) := by
  have hL : «Affine.semLeaf» (leaf 11) (E.map encInst) cs D.children =
      «Affine.one» («Prelude.and» («Base.isEmpty» cs) («Base.isEmpty» D.children))
        («Affine.res» («Affine.dZero» (leaf 1)) []) := rfl
  rw [hL, isEmpty_eq, isEmpty_eq, and_eq, one_eq]
  match cs with
  | [] =>
    rcases hds : D.children with _ | ⟨x, r⟩
    · spec_at hds
      rfl
    · spec_at hds
      rfl
  | _ :: _ => rfl

/-- The rule of a quoted tree. -/
theorem rule_quote (cs : List Tree) (E : Env) (Γ : Geb.Affine.Ctx) (D : Tree) :
    «Affine.semLeaf» (leaf 15) (E.map encInst) cs D.children =
      encR (Geb.Affine.semStep 15 (kids cs) E Γ D) := by
  have hL : «Affine.semLeaf» (leaf 15) (E.map encInst) cs D.children =
      «Affine.one» («Prelude.and» (Const.eq («Prelude.length» cs) (leaf 1))
        («Base.isEmpty» D.children)) («Affine.res» («Affine.dZero» (leaf 0)) []) := rfl
  rw [hL, isEmpty_eq, length_eq, eq_leaf, and_eq, one_eq]
  match cs with
  | [] => rfl
  | [c] =>
    rcases hds : D.children with _ | ⟨x, r⟩
    · spec_at hds
      rfl
    · spec_at hds
      rfl
  | a :: b :: r =>
    have hk : (r.length + 1 + 1 == 1) = false := rfl
    simp only [List.length_cons, hk, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    rfl

/-- The rule of a primitive. -/
theorem rule_prim (cs : List Tree) (E : Env) (Γ : Geb.Affine.Ctx) (D : Tree) :
    «Affine.semLeaf» (leaf 22) (E.map encInst) cs D.children =
      encR (Geb.Affine.semStep 22 (kids cs) E Γ D) := by
  have hL : «Affine.semLeaf» (leaf 22) (E.map encInst) cs D.children =
      «Affine.semPrim» cs D.children := rfl
  rw [hL]
  match cs with
  | [] => aff_simp [«Affine.semPrim», isEmpty_eq]; rfl
  | [k] =>
    rcases hds : D.children with _ | ⟨x, r⟩
    · spec_at hds
      exact semPrim_eq k
    · spec_at hds
      aff_simp [«Affine.semPrim», isEmpty_eq, List.isEmpty_cons]
  | a :: b :: r =>
    have hk : (r.length + 1 + 1 == 1) = false := rfl
    aff_simp [«Affine.semPrim», isEmpty_eq, hk]
    rfl

/-- The rule of a reference. -/
theorem rule_ref (cs : List Tree) (E : Env) (Γ : Geb.Affine.Ctx) (D : Tree) :
    «Affine.semLeaf» (leaf 23) (E.map encInst) cs D.children =
      encR (Geb.Affine.semStep 23 (kids cs) E Γ D) := by
  have hL : «Affine.semLeaf» (leaf 23) (E.map encInst) cs D.children =
      «Affine.semRef» (E.map encInst) cs D.children := rfl
  rw [hL]
  match cs with
  | [] => aff_simp [«Affine.semRef»]; rfl
  | [n] =>
    rcases hds : D.children with _ | ⟨di, _ | ⟨dk, _ | ⟨x, xs⟩⟩⟩
    · spec_at hds
      rfl
    · spec_at hds
      rfl
    · spec_at hds
      exact semRef_eq E n di dk
    · spec_at hds
      aff_simp [«Affine.semRef», beq_len3_2]
  | a :: b :: r =>
    have hk : (r.length + 1 + 1 == 1) = false := rfl
    aff_simp [«Affine.semRef», hk]
    rfl

/-- The rule of a constant at one type. -/
theorem rule_one (l : ℕ) (hl : l = 17 ∨ l = 18 ∨ l = 19 ∨ l = 25) (cs : List Tree) (E : Env)
    (Γ : Geb.Affine.Ctx) (D : Tree) :
    «Affine.semOne» (leaf l) cs D.children = encR (Geb.Affine.semStep l (kids cs) E Γ D) := by
  match cs with
  | [] =>
    aff_simp [«Affine.semOne», isTy_eq]
    rcases hl with rfl | rfl | rfl | rfl <;> rfl
  | [A] =>
    rcases hds : D.children with _ | ⟨dA, _ | ⟨x, xs⟩⟩
    · aff_simp [«Affine.semOne», isTy_eq]
      rcases hl with rfl | rfl | rfl | rfl <;> (spec_at hds)
    · rw [semOne_eq]
      rcases hl with rfl | rfl | rfl | rfl <;> (spec_at hds; rfl)
    · have hk : (xs.length + 1 + 1 == 1) = false := rfl
      aff_simp [«Affine.semOne», isTy_eq, hk]
      rcases hl with rfl | rfl | rfl | rfl <;> (spec_at hds)
  | a :: b :: r =>
    have hk : (r.length + 1 + 1 == 1) = false := rfl
    aff_simp [«Affine.semOne», isTy_eq, hk]
    rcases hl with rfl | rfl | rfl | rfl <;> rfl

/-- The rule of the right fold of lists and of case analysis of lists. -/
theorem rule_two (l : ℕ) (hl : l = 21 ∨ l = 24) (cs : List Tree) (E : Env) (Γ : Geb.Affine.Ctx)
    (D : Tree) :
    «Affine.semTwo» (leaf l) cs D.children = encR (Geb.Affine.semStep l (kids cs) E Γ D) := by
  match cs with
  | [] =>
    aff_simp [«Affine.semTwo», isTy_eq]
    rcases hl with rfl | rfl <;> rfl
  | [_] =>
    aff_simp [«Affine.semTwo», isTy_eq]
    rcases hl with rfl | rfl <;> rfl
  | [A, B] =>
    rcases hds : D.children with _ | ⟨dA, _ | ⟨dB, _ | ⟨x, xs⟩⟩⟩
    · aff_simp [«Affine.semTwo», isTy_eq]
      rcases hl with rfl | rfl <;> (spec_at hds)
    · aff_simp [«Affine.semTwo», isTy_eq]
      rcases hl with rfl | rfl <;> (spec_at hds)
    · rw [semTwo_eq]
      rcases hl with rfl | rfl
      · spec_at hds
        change _ = encR ((guard (Ty.IsTy A && Ty.IsTy B) : Option Unit) >>= fun _ ↦
          decorate A dA >>= fun a ↦ guard (a.data || 1 ≤ DTy.bang a) >>= fun _ ↦
            decorate B dB >>= fun b ↦ some (foldrD a b, []))
        cases (guard (Ty.IsTy A && Ty.IsTy B) : Option Unit) with
        | none => rfl
        | some _ =>
          cases decorate A dA with
          | none => rfl
          | some a =>
            cases decorate B dB with
            | some b => rfl
            | none =>
              by_cases hg : (a.data || decide (1 ≤ DTy.bang a)) = true
              · change encR none = encR ((guard ((a.data || decide (1 ≤ DTy.bang a)) = true) :
                  Option Unit) >>= fun _ ↦ none)
                rw [guard_some hg]
                rfl
              · change encR none = encR ((guard ((a.data || decide (1 ≤ DTy.bang a)) = true) :
                  Option Unit) >>= fun _ ↦ none)
                rw [guard_none hg]
                rfl
      · spec_at hds
        rfl
    · have hk : (xs.length + 1 + 1 + 1 == 2) = false := rfl
      aff_simp [«Affine.semTwo», isTy_eq, hk]
      rcases hl with rfl | rfl <;> (spec_at hds)
  | a :: b :: c :: r =>
    have hk : (r.length + 1 + 1 + 1 == 2) = false := rfl
    aff_simp [«Affine.semTwo», isTy_eq, hk]
    rcases hl with rfl | rfl <;> rfl

/-- The checks of a term at mode zero and at the spine it has: the mirror's are the encodings of
the Lean ones. -/
theorem mcheck_rel (t : Tree) :
    SemRel (mcheck t) (checkOf t).1 ∧
      ∀ A B ss, (checkOf t).2 = some (A, B, ss) →
        ∀ (E : Env) (Γ : Geb.Affine.Ctx) (ds : List Tree), ds.length = ss.length →
          mcheck t (leaf 1) (E.map encInst) (Γ.map encEntry) (RoseTree.node 0 ds) =
            RoseTree.node 0 (List.zipWith (fun s d ↦ encR (s E Γ d)) ss ds) := by
  refine RoseTree.ind (P := fun t ↦
    SemRel (mcheck t) (checkOf t).1 ∧
      ∀ A B ss, (checkOf t).2 = some (A, B, ss) →
        ∀ (E : Env) (Γ : Geb.Affine.Ctx) (ds : List Tree), ds.length = ss.length →
          mcheck t (leaf 1) (E.map encInst) (Γ.map encEntry) (RoseTree.node 0 ds) =
            RoseTree.node 0 (List.zipWith (fun s d ↦ encR (s E Γ d)) ss ds))
    (fun l cs ih ↦ ⟨fun E Γ D ↦ ?_, fun A B ss hs E Γ ds hlen ↦ ?_⟩) t
  · have hL : (checkOf (RoseTree.node l cs)).1 E Γ D = Geb.Affine.semStep l (kids cs) E Γ D := by
      rw [check_node]
    rw [hL, mcheck_node]
    have hR : ∀ c ∈ cs, MR c := fun c hc ↦ (ih c hc).1
    have hn : ∀ k (hk : k < 8 ∨ 26 ≤ k), «Affine.semStep» (RoseTree.node k cs)
        ((cs.map mcheck).getD 0 «Affine.sem0») ((cs.map mcheck).getD 1 «Affine.sem0»)
        ((cs.map mcheck).getD 2 «Affine.sem0») (leaf 0) (E.map encInst) (Γ.map encEntry) D =
        encR none := fun k hk ↦ step_none k hk _ _ _ _ _ _ _
    match l with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact hn _ (Or.inl (by decide))
    | m + 26 => exact hn _ (Or.inr (Nat.le_add_left 26 m))
    | 8 => exact (step_var _ _ _ _ _ _ _ _).trans (rule_var cs E Γ D)
    | 9 => exact (step_lam _ _ _ _ _ _ _ _).trans (rule_lam cs hR E Γ D)
    | 10 =>
      by_cases h2 : cs.length = 2
      · obtain ⟨f, x, rfl⟩ := List.length_eq_two.mp h2
        exact (step_app0 _ _ _ _ _ _ _ _).trans (rule_app f x (hR f List.mem_cons_self)
          (hR x (List.mem_cons_of_mem _ List.mem_cons_self)) (ih f List.mem_cons_self).2 E Γ D)
      · rw [rule_app_other cs h2]
        simp only [«Affine.semStep», label_eq, children_eq, RoseTree.label_node,
          RoseTree.children_node]
        exact one_len h2 _
    | 11 => exact (step_leaf _ (by decide) _ _ _ _ _ _ _).trans (rule_unit cs E Γ D)
    | 12 => exact (step_pair _ _ _ _ _ _ _ _).trans (rule_pair cs hR E Γ D)
    | 13 => exact (step_fst _ _ _ _ _ _ _ _).trans (rule_proj 0 13 (by decide) cs hR E Γ D)
    | 14 => exact (step_snd _ _ _ _ _ _ _ _).trans (rule_proj 1 14 (by decide) cs hR E Γ D)
    | 15 => exact (step_leaf _ (by decide) _ _ _ _ _ _ _).trans (rule_quote cs E Γ D)
    | 16 => exact (step_cond _ _ _ _ _ _ _ _).trans (rule_cond cs hR E Γ D)
    | 17 => exact (step_leaf _ (by decide) _ _ _ _ _ _ _).trans (rule_one 17 (by decide) cs E Γ D)
    | 18 => exact (step_leaf _ (by decide) _ _ _ _ _ _ _).trans (rule_one 18 (by decide) cs E Γ D)
    | 19 => exact (step_leaf _ (by decide) _ _ _ _ _ _ _).trans (rule_one 19 (by decide) cs E Γ D)
    | 20 => exact (step_cons _ _ _ _ _ _ _ _).trans (rule_cons cs hR E Γ D)
    | 21 => exact (step_leaf _ (by decide) _ _ _ _ _ _ _).trans (rule_two 21 (by decide) cs E Γ D)
    | 22 => exact (step_leaf _ (by decide) _ _ _ _ _ _ _).trans (rule_prim cs E Γ D)
    | 23 => exact (step_leaf _ (by decide) _ _ _ _ _ _ _).trans (rule_ref cs E Γ D)
    | 24 => exact (step_leaf _ (by decide) _ _ _ _ _ _ _).trans (rule_two 24 (by decide) cs E Γ D)
    | 25 => exact (step_leaf _ (by decide) _ _ _ _ _ _ _).trans (rule_one 25 (by decide) cs E Γ D)
  · rw [spine_node] at hs
    rcases spine_some hs with ⟨rfl, rfl, rfl⟩ | ⟨rfl, f, x, ss', rfl, hf, rfl⟩
    · obtain rfl : ds = [] := List.length_eq_zero_iff.mp hlen
      rw [mcheck_node]
      exact step_lcase1 _ _ _ _ _ _ _
    · have hfr := (ih f List.mem_cons_self).2 A B ss' hf E Γ
      have hxr := (ih x (List.mem_cons_of_mem _ List.mem_cons_self)).1 E Γ
      obtain ⟨init, d, rfl⟩ : ∃ init d, ds = init ++ [d] := by
        rcases List.eq_nil_or_concat ds with rfl | ⟨init, d, rfl⟩
        · rw [List.length_nil, List.length_append] at hlen
          exact absurd hlen (Nat.ne_of_lt (Nat.succ_pos _))
        · exact ⟨init, d, List.concat_eq_append⟩
      have hi : init.length = ss'.length := by
        simpa only [List.length_append, List.length_cons, List.length_nil, zero_add,
          Nat.add_right_cancel_iff] using hlen
      rw [mcheck_node]
      refine (step_app1 _ _ _ _ _ _ _ _).trans ?_
      simp only [«Affine.semSpine», List.map_cons, List.map_nil, List.getD_cons_zero,
        List.getD_cons_succ, children_eq, RoseTree.children_node, length_eq, sub_leaf, take_eq,
        at_eq, List.length_append, List.length_cons, List.length_nil, zero_add,
        Nat.add_sub_cancel, List.take_left', node_leaf, single_eq, append_eq, hfr init hi, hxr]
      rw [List.getD_eq_getElem?_getD, List.getElem?_concat_length, Option.getD_some,
        List.zipWith_append hi.symm]
      rfl

/-- The mirror's check at mode zero is the encoding of the Lean check. -/
theorem sem_eq (t : Tree) (E : Env) (Γ : Geb.Affine.Ctx) (D : Tree) :
    «Affine.sem» t (leaf 0) (E.map encInst) (Γ.map encEntry) D = encR (Geb.Affine.sem t E Γ D) :=
  (mcheck_rel t).1 E Γ D

/-- The mirror's check of an instance after the instances before it. -/
theorem instanceOf_eq (prog : List Tree) (E : Env) (inst : Tree) :
    «Affine.instanceOf» prog (E.map encInst) inst =
      encOpt ((instance? prog E inst).map fun E' ↦ RoseTree.node 0 (E'.map encInst)) := by
  obtain ⟨li, is, rfl⟩ : ∃ li is, inst = RoseTree.node li is :=
    ⟨_, _, (RoseTree.node_label_children inst).symm⟩
  unfold «Affine.instanceOf» instance?
  simp only [label_eq, children_eq, RoseTree.label_node, RoseTree.children_node, nth_eq, bindO_eq]
  cases prog[li]? with
  | none => rfl
  | some body =>
    match is with
    | [] => rfl
    | [D] =>
      aff_simp [Option.elim_some, label_leaf, beq_iff_eq]
      change _ = encOpt (Option.map _ (guard (D.label = 0) >>= fun _ ↦ _))
      by_cases hD : D.label = 0
      · rw [guard_some hD, ite_eq_left hD]
        have h := sem_eq body E [] D
        simp only [List.map_nil] at h
        rw [h]
        cases Geb.Affine.sem body E [] D with
        | none => rfl
        | some r =>
          obtain ⟨d, u⟩ := r
          simp only [encR, Option.map_some, mapO_eq, encRes, child_node, List.getD_cons_zero,
            node_leaf]
          change _ = encOpt (some (RoseTree.node 0 ((E ++ [(li, d)]).map encInst)))
          rw [List.map_append]
          rfl
      · rw [guard_none hD, ite_eq_right hD]
        rfl
    | y :: z :: r =>
      have hb : (r.length + 1 + 1 == 1) = false := rfl
      aff_simp [Option.elim_some, hb]
      rfl

/-- The mirror's check of the instances after those before them. -/
theorem checkFrom_eq (prog : List Tree) (insts : List Tree) : ∀ E : Env,
    List.foldr (fun (x2 : Tree) (x3 : List Tree → Tree) (x4 : List Tree) ↦
        «Base.bindO» («Affine.instanceOf» prog x4 x2) fun x5 ↦ x3 (Const.children x5))
      (fun x2 ↦ «Prelude.some» (Const.node (leaf 0) x2)) insts (E.map encInst) =
      encOpt ((insts.foldlM (instance? prog) E).map fun E' ↦
        RoseTree.node 0 (E'.map encInst)) := by
  refine insts.rec (fun _ ↦ rfl) fun inst r ih E ↦ ?_
  simp only [List.foldr_cons, List.foldlM_cons, instanceOf_eq, bindO_eq]
  change _ = encOpt (Option.map _ ((instance? prog E inst).bind _))
  cases instance? prog E inst with
  | none => rfl
  | some E' =>
    simp only [Option.map_some, Option.elim_some, Option.bind_some, children_eq,
      RoseTree.children_node]
    exact ih E'

/-- The check of a certificate written in Geb gives the encoding of what
{name}`Geb.Affine.check` gives. -/
theorem check_eq (prog : List Tree) (cert : Tree) :
    «Affine.check» prog cert =
      encOpt ((check prog cert).map fun E ↦ RoseTree.node 0 (E.map encInst)) := by
  simp only [«Affine.check», foldr_eq, children_eq]
  exact checkFrom_eq prog cert.children []

#guard (do
  let prog ← program examples.toList
  let cert ← certificate examplesCert.toList
  some («Affine.check» prog cert ==
    encOpt ((check prog cert).map fun E ↦ RoseTree.node 0 (E.map encInst)))) == some true

#guard (do
  let prog ← program examples.toList
  let cert ← certificate examplesCert.toList
  let cert' := RoseTree.node cert.label cert.children.reverse
  some («Affine.check» prog cert' ==
    encOpt ((check prog cert').map fun E ↦ RoseTree.node 0 (E.map encInst)))) == some true

#guard (do
  let prog ← program examples.toList
  some ((«Affine.check» prog (← certificate twice.toList)).label,
    («Affine.check» prog (← certificate twiceLinear.toList)).label)) == some (1, 0)

end GebTests.Prototypes.FreeTopos.Agreement.Affine

end
