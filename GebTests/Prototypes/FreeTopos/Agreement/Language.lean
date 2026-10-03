/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Agreement.Infer

set_option doc.verso true in
/-!
# The internal language in the checker written in Geb

The functions of {lit}`bootstrap/free-topos/language.geb`, in the Lean the bootstrap compiler
emits ({lit}`GebMirror.Metalogic`), agree with the internal language's Lean definitions at every
encoded input: the constructors and accessors of terms, their renaming and substitution of
variables and substitution of objects, the types, and the compilation of terms, definitions and
equations to the combinators.

## Main definitions

* {lit}`travL` — the traversal of a term's variables of which renaming and substitution are
  instances.
* {lit}`CRel` — the relation of the mirror's compilation of a term to the compilation's.

## Main statements

* {lit}`rename_eq`, {lit}`subst_eq`, {lit}`osubst_eq` — renaming, substitution and object
  substitution.
* {lit}`encTerm_inj` — the encoding of terms is injective.
* {lit}`isTy_eq` — the test of a type in object variables.
* {lit}`compile_eq` — the compilation of a term, at every encoded environment.
* {lit}`ldCompile_eq`, {lit}`compileDefs_eq`, {lit}`compileEq_eq` — the compilation of
  definitions, of the constants' definitions and of equations.
* {lit}`primOk_eq`, {lit}`objOk_eq` — the tests of primitive arrows and of objects by the
  checker's inference.

## Tags

internal language, renaming, substitution, compilation, agreement, mirror
-/

set_option doc.verso true

@[expose] public section

open GebMirror.Metalogic

namespace GebTests.Prototypes.FreeTopos.Agreement.Language

open Geb Geb.Kernel Geb.FreeTopos GebTests.Prototypes.FreeTopos.Agreement.Encode
  GebTests.Prototypes.FreeTopos.Agreement.Fold GebTests.Prototypes.FreeTopos.Agreement.Base
  GebTests.Prototypes.FreeTopos.Agreement.PartialHorn GebTests.Prototypes.FreeTopos.Agreement.Theory
  GebTests.Prototypes.FreeTopos.Agreement.Infer
open Internal (Term Label)
open scoped FinEnum

/-- The encoding of a node of a term. -/
theorem encTerm_node (l : Label) (cs : List Term) :
    encTerm (RoseTree.node l cs) =
      RoseTree.node (labelData l).1 (RoseTree.node 0 (labelData l).2 :: cs.map encTerm) :=
  encWith_node _ _ l cs

/-- The label of an encoded term. -/
@[simp] theorem label_encTerm (t : Term) : (encTerm t).label = (labelData t.label).1 := by
  rw [← RoseTree.node_label_children t, encTerm_node]
  rfl

/-- The mirror's data of an encoded term's label. -/
@[simp] theorem mData_eq (t : Term) :
    «Language.mData» (encTerm t) = (labelData t.label).2 := by
  rw [← RoseTree.node_label_children t, encTerm_node]
  simp [«Language.mData»]

/-- The mirror's children of an encoded term. -/
@[simp] theorem mArgs_eq (t : Term) :
    «Language.mArgs» (encTerm t) = t.children.map encTerm := by
  rw [← RoseTree.node_label_children t, encTerm_node]
  simp [«Language.mArgs»]

/-- The mirror's test of an encoded term's label and number of children. -/
@[simp] theorem mIs_eq (a b : ℕ) (t : Term) :
    «Language.mIs» (leaf a) (leaf b) (encTerm t) =
      ofBool ((labelData t.label).1 == a && t.children.length == b) := by
  simp [«Language.mIs»]

/-- The mirror's child of an encoded term at a position. -/
@[simp] theorem mArg_eq (t : Term) (i : ℕ) :
    «Language.mArg» (encTerm t) (leaf i) = (t.children.map encTerm).getD i (leaf 0) := by
  simp [«Language.mArg»]

/-- The mirror's datum of an encoded term's label at a position. -/
@[simp] theorem mD_eq (t : Term) (i : ℕ) :
    «Language.mD» (encTerm t) (leaf i) = (labelData t.label).2.getD i (leaf 0) := by
  simp [«Language.mD»]

/-- A label is determined by its constructor's position and its data. -/
theorem labelData_inj (l l' : Label) (h1 : (labelData l).1 = (labelData l').1)
    (h2 : RoseTree.node 0 (labelData l).2 = RoseTree.node 0 (labelData l').2) : l = l' := by
  rw [node_inj] at h2
  cases l <;> cases l' <;> simp_all [labelData, leaf_inj, node_inj]

/-- The encoding of terms is injective. -/
theorem encTerm_inj : Function.Injective encTerm :=
  encWith_inj _ _ fun l l' h1 h2 ↦ labelData_inj l l' h1 h2

/-- Encoded terms are equal exactly when the terms are. -/
@[simp] theorem encTerm_eq_iff {t u : Term} : encTerm t = encTerm u ↔ t = u :=
  encTerm_inj.eq_iff

/-- The mirror's node of a term's label over its data and its encoded children. -/
theorem mNode_eq (l : Label) (cs : List Term) :
    «Language.mNode» (leaf (labelData l).1) (labelData l).2 (cs.map encTerm) =
      encTerm (RoseTree.node l cs) :=
  (encTerm_node l cs).symm

/-- The mirror's element of the terminal type. -/
@[simp] theorem mStar_eq : «Language.mStar» = encTerm Internal.Term.star :=
  mNode_eq .star []

/-- The mirror's pair of encoded terms. -/
@[simp] theorem mPair_eq (t u : Term) :
    «Language.mPair» (encTerm t) (encTerm u) = encTerm (Internal.Term.pair t u) :=
  mNode_eq .pair [t, u]

/-- The mirror's first projection of an encoded term. -/
@[simp] theorem mFst_eq (t : Term) :
    «Language.mFst» (encTerm t) = encTerm (Internal.Term.fst t) :=
  mNode_eq .fst [t]

/-- The mirror's second projection of an encoded term. -/
@[simp] theorem mSnd_eq (t : Term) :
    «Language.mSnd» (encTerm t) = encTerm (Internal.Term.snd t) :=
  mNode_eq .snd [t]

/-- The mirror's abstraction of an encoded term. -/
@[simp] theorem mLam_eq (a : Tree) (t : Term) :
    «Language.mLam» a (encTerm t) = encTerm (Internal.Term.lam a t) :=
  mNode_eq (.lam a) [t]

/-- The mirror's application of encoded terms. -/
@[simp] theorem mApp_eq (t u : Term) :
    «Language.mApp» (encTerm t) (encTerm u) = encTerm (Internal.Term.app t u) :=
  mNode_eq .app [t, u]

/-- The mirror's primitive arrow applied to an encoded term. -/
@[simp] theorem mArr_eq (k : ℕ) (θ : List Tree) (t : Term) :
    «Language.mArr» (leaf k) θ (encTerm t) = encTerm (Internal.Term.arr k θ t) :=
  mNode_eq (.arr k θ) [t]

/-- The mirror's fold of the natural numbers of encoded terms. -/
@[simp] theorem mNatRec_eq (z s t : Term) :
    «Language.mNatRec» (encTerm z) (encTerm s) (encTerm t) =
      encTerm (Internal.Term.natRec z s t) :=
  mNode_eq .natRec [z, s, t]

/-- The mirror's fold of lists of encoded terms. -/
@[simp] theorem mListRec_eq (z s t : Term) :
    «Language.mListRec» (encTerm z) (encTerm s) (encTerm t) =
      encTerm (Internal.Term.listRec z s t) :=
  mNode_eq .listRec [z, s, t]

/-- The mirror's fold of rose trees of encoded terms. -/
@[simp] theorem mRoseRec_eq (c : Tree) (s t : Term) :
    «Language.mRoseRec» c (encTerm s) (encTerm t) =
      encTerm (Internal.Term.roseRec c s t) :=
  mNode_eq (.roseRec c) [s, t]

/-- The mirror's application of a definition to encoded terms. -/
@[simp] theorem mDefn_eq (k : ℕ) (θ : List Tree) (ts : List Term) :
    «Language.mDefn» (leaf k) θ (ts.map encTerm) = encTerm (Internal.Term.defn k θ ts) :=
  mNode_eq (.defn k θ) ts

/-- The mirror's equation of encoded terms. -/
@[simp] theorem mEq_eq (t u : Term) :
    «Language.mEq» (encTerm t) (encTerm u) = encTerm (Internal.Term.eq t u) :=
  mNode_eq .eq [t, u]

/-- One step of a traversal of a term's variables by a map, lifted under each binder, of which
renaming and substitution are the instances: the variable of an index is the map's value there,
and the start and the step of a fold are left in place. -/
def travL {M : Type} (V : M → ℕ → Term) (L : M → M) (l : Label)
    (cs : List (Term × (M → Term))) (f : M) : Term :=
  match l, cs with
    | .var i, _ => V f i
    | .lam a, [(_, t)] => RoseTree.node (.lam a) [t (L f)]
    | .natRec, [(z, _), (s, _), (_, n)] => RoseTree.node .natRec [z, s, n f]
    | .listRec, [(z, _), (s, _), (_, n)] => RoseTree.node .listRec [z, s, n f]
    | .roseRec c, [(s, _), (_, n)] => RoseTree.node (.roseRec c) [s, n f]
    | l, cs => RoseTree.node l (cs.map fun c ↦ c.2 f)

/-- Renaming is the traversal whose variable is renamed. -/
theorem renameStep_eq :
    Internal.Term.renameStep = travL (fun f i ↦ Internal.Term.var (f i)) Internal.Term.liftR := by
  funext l cs f
  cases l <;> rcases cs with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, cs⟩⟩⟩⟩ <;> rfl

/-- Substitution is the traversal whose variable is replaced. -/
theorem substStep_eq : Internal.Term.substStep = travL (fun σ i ↦ σ i) Internal.Term.liftS := by
  funext l cs f
  cases l <;> rcases cs with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, cs⟩⟩⟩⟩ <;> rfl

/-- The terms of a list of terms with their traversals. -/
@[simp] theorem rpTrees_eq (rs : List (Tree × ((Tree → Tree) → Tree))) :
    «Language.rpTrees» rs = rs.map Prod.fst :=
  rs.rec rfl fun _ _ ih ↦ by
    simp only [«Language.rpTrees», foldr_eq, List.foldr_cons] at ih ⊢
    rw [ih]
    rfl

/-- A list of terms with their traversals without its head. -/
@[simp] theorem rpTail_eq (rs : List (Tree × ((Tree → Tree) → Tree))) :
    «Language.rpTail» rs = rs.tail := by
  cases rs <;> rfl

/-- The traversals of a list of terms by a map. -/
@[simp] theorem rpAll_eq (rs : List (Tree × ((Tree → Tree) → Tree))) (f : Tree → Tree) :
    «Language.rpAll» rs f = rs.map fun r ↦ r.2 f :=
  rs.rec rfl fun _ _ ih ↦ by
    simp only [«Language.rpAll», foldr_eq, List.foldr_cons] at ih ⊢
    rw [ih]
    rfl

/-- Dropping the head of a list of terms with their traversals as many times as a label. -/
theorem repeat_rpTail (rs : List (Tree × ((Tree → Tree) → Tree))) :
    ∀ i : ℕ, Nat.repeat «Language.rpTail» i rs = rs.drop i :=
  Nat.rec rfl fun i ih ↦ by rw [Nat.repeat, ih, rpTail_eq, List.tail_drop]

/-- The traversal of a term at a position by a map, the leaf of label zero out of range. -/
@[simp] theorem rpAt_eq (rs : List (Tree × ((Tree → Tree) → Tree))) (i : ℕ) (f : Tree → Tree) :
    «Language.rpAt» rs (leaf i) f = (rs[i]?.map fun r ↦ r.2 f).getD (leaf 0) := by
  simp only [«Language.rpAt», iter_leaf, repeat_rpTail]
  cases h : rs.drop i with
  | nil =>
    rw [List.drop_eq_nil_iff] at h
    rw [List.getElem?_eq_none h]
    rfl
  | cons r rest =>
    have : rs[i]? = some r := by
      rw [← List.head?_drop, h]
      rfl
    rw [this]
    rfl

/-- The mirror's traversal step at an encoded node is the traversal step at the node it encodes,
at maps and children's traversals related by the traversal's relation. -/
theorem travStep_eq {M : Type} (Rel : (Tree → Tree) → M → Prop) (V : M → ℕ → Term) (L : M → M)
    (lift : (Tree → Tree) → Tree → Tree) (wrap : Tree → Tree)
    (hV : ∀ f f', Rel f f' → ∀ i, wrap (f (leaf i)) = encTerm (V f' i))
    (hL : ∀ f f', Rel f f' → Rel (lift f) (L f')) (l : Label) (v : (Tree → Tree) → Tree)
    (xs : List (Term × ((Tree → Tree) → Tree) × (M → Term)))
    (hx : ∀ x ∈ xs, ∀ f f', Rel f f' → x.2.1 f = encTerm (x.2.2 f')) (f : Tree → Tree) (f' : M)
    (hf : Rel f f') :
    «Language.travStep» lift wrap (leaf (labelData l).1)
        ((RoseTree.node 0 (labelData l).2, v) :: xs.map fun x ↦ (encTerm x.1, x.2.1)) f =
      encTerm (travL V L l (xs.map fun x ↦ (x.1, x.2.2)) f') := by
  have h0 : ∀ x ∈ xs, x.2.1 f = encTerm (x.2.2 f') := fun x h ↦ hx x h f f' hf
  have h1 : ∀ x ∈ xs, x.2.1 (lift f) = encTerm (x.2.2 (L f')) :=
    fun x h ↦ hx x h (lift f) (L f') (hL f f' hf)
  have hxs : xs.map (fun x ↦ x.2.1 f) = xs.map (fun x ↦ encTerm (x.2.2 f')) :=
    List.map_congr_left h0
  cases l
  case var i =>
    mirror_simp [«Language.travStep», labelData, travL, rpTrees_eq, rpTail_eq]
    exact hV f f' hf i
  all_goals
    rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, r⟩⟩⟩⟩ <;>
      mirror_simp [«Language.travStep», labelData, travL, rpTrees_eq, rpTail_eq,
        rpAt_eq, rpAll_eq, encTerm_node, h0, h1, List.mem_cons, true_or, or_true, beq_iff_eq,
        Nat.add_right_cancel_iff, Nat.add_one_ne_zero, «Theory.l2»,
        «Theory.l3»]
  all_goals
    rw [List.map_congr_left fun x hx ↦ h0 x (by simp [hx])]
    try split
    all_goals first | omega | rfl

/-- The mirror's traversal of an encoded term is the traversal of the term, at maps related by
the traversal's relation. -/
theorem trav_eq {M : Type} (Rel : (Tree → Tree) → M → Prop) (V : M → ℕ → Term) (L : M → M)
    (lift : (Tree → Tree) → Tree → Tree) (wrap : Tree → Tree)
    (hV : ∀ f f', Rel f f' → ∀ i, wrap (f (leaf i)) = encTerm (V f' i))
    (hL : ∀ f f', Rel f f' → Rel (lift f) (L f')) (t : Term) (f : Tree → Tree) (f' : M)
    (hf : Rel f f') :
    «Language.trav» lift wrap (encTerm t) f = encTerm (RoseTree.para (travL V L) t f') :=
  fold_pair_enc (fun l ↦ (labelData l).1) (fun l ↦ RoseTree.node 0 (labelData l).2)
    (fun v w ↦ ∀ f f', Rel f f' → v f = encTerm (w f'))
    (fun l rs ↦ by simp only [rpTrees_eq]) (travL V L)
    (fun l v xs hx f f' hf ↦ travStep_eq Rel V L lift wrap hV hL l v xs hx f f' hf) t f f' hf

/-- The mirror's variable of an index is the encoded variable. -/
@[simp] theorem mVar_eq (i : ℕ) :
    «Language.mVar» (leaf i) = encTerm (Internal.Term.var i) := rfl

/-- The mirror's renaming of an encoded term is the renaming of the term, at a renaming of
leaves. -/
theorem rename_eq (t : Term) (f : Tree → Tree) (f' : ℕ → ℕ) (hf : ∀ i, f (leaf i) = leaf (f' i)) :
    «Language.rename» (encTerm t) f = encTerm (Internal.Term.rename t f') := by
  simp only [«Language.rename», Internal.Term.rename, renameStep_eq]
  refine trav_eq (fun f f' ↦ ∀ i, f (leaf i) = leaf (f' i)) _ _ _ _ (fun f f' hf i ↦ ?_)
    (fun f f' hf i ↦ ?_) t f f' hf
  · rw [hf]
    rfl
  · cases i <;> mirror_simp [«Language.liftR», Internal.Term.liftR, hf, beq_iff_eq,
      Nat.add_one_ne_zero, Nat.add_sub_cancel]

/-- The mirror's substitution in an encoded term is the substitution in the term, at a
substitution of encoded terms for leaves. -/
theorem subst_eq (t : Term) (σ : Tree → Tree) (σ' : ℕ → Term)
    (hσ : ∀ i, σ (leaf i) = encTerm (σ' i)) :
    «Language.subst» (encTerm t) σ = encTerm (Internal.Term.subst t σ') := by
  simp only [«Language.subst», Internal.Term.subst, substStep_eq]
  refine trav_eq (fun σ σ' ↦ ∀ i, σ (leaf i) = encTerm (σ' i)) _ _ _ _ (fun σ σ' hσ i ↦ hσ i)
    (fun σ σ' hσ i ↦ ?_) t σ σ' hσ
  cases i with
  | zero => rfl
  | succ j =>
    mirror_simp [«Language.liftS», Internal.Term.liftS, hσ]
    exact rename_eq _ _ _ fun i ↦ by mirror_simp []

/-- The mirror's substitution of a list of encoded terms for variables. -/
theorem substList_eq (ts : List Term) (i : ℕ) :
    «Language.substList» (ts.map encTerm) (leaf i) =
      encTerm (Internal.Term.substList ts i) := by
  simp only [«Language.substList», Internal.Term.substList, nth_eq, getD_eq,
    List.getElem?_map, mVar_eq]
  cases ts[i]? <;> rfl

/-- The position of a label's constructor is unchanged by object substitution. -/
@[simp] theorem labelData_osubst_fst (θ : List Tree) (l : Label) :
    (labelData (l.osubst θ)).1 = (labelData l).1 := by
  cases l <;> rfl

/-- The mirror's object substitution in a label's data. -/
theorem dataOsubst_eq (θ : List Tree) (l : Label) :
    «Language.dataOsubst» θ (leaf (labelData l).1) (labelData l).2 =
      (labelData (l.osubst θ)).2 := by
  cases l <;> mirror_simp [«Language.dataOsubst», labelData, Internal.Label.osubst,
    phSubst_eq, «Theory.l2», funext (phSubst_eq θ)]

/-- The mirror's object substitution in an encoded term. -/
theorem osubst_eq (θ : List Tree) (t : Term) :
    «Language.osubst» θ (encTerm t) = encTerm (t.osubst θ) := by
  simp only [«Language.osubst», Internal.Term.osubst, elim_eq_para]
  refine fold_pair_enc _ _ (fun v w ↦ v = encTerm w) (fun l rs ↦ by simp) _
    (fun l v xs hx ↦ ?_) t
  mirror_simp [ptTrees_eq, ptValues_eq, dataOsubst_eq, encTerm_node, List.map_map,
    Function.comp_def, labelData_osubst_fst]
  rw [List.map_congr_left hx]

/-- The mirror's pair of two trees. -/
@[simp] theorem pr_eq (a b : Tree) : «Language.pr» a b = encPair (a, b) := rfl

/-- The mirror's first component of an encoded pair. -/
@[simp] theorem p1_eq (p : Tree × Tree) : «Language.p1» (encPair p) = p.1 := rfl

/-- The mirror's second component of an encoded pair. -/
@[simp] theorem p2_eq (p : Tree × Tree) : «Language.p2» (encPair p) = p.2 := rfl

/-- Encoded pairs are equal exactly when the pairs are. -/
theorem encPair_inj {p q : Tree × Tree} : encPair p = encPair q ↔ p = q := by
  refine ⟨fun h ↦ ?_, congrArg encPair⟩
  have h' := congrArg RoseTree.children h
  simp only [encPair, RoseTree.children_node, List.cons.injEq, and_true] at h'
  exact Prod.ext h'.1 h'.2

/-- The mirror's operations that build types. -/
theorem tyOps_eq :
    «Language.tyOps» = Internal.tyOps.map fun p ↦ encPair (leaf p.1, leaf p.2) := rfl

/-- The mirror's parts of a tree of two children built by an operation. -/
theorem binParts_eq (mk : Tree → Tree → Tree) (p : Tree) :
    «Language.binParts» mk p =
      encOpt ((match p.children with
        | [a, b] => if p = mk a b then some (a, b) else none
        | _ => none).map encPair) := by
  obtain ⟨l, cs, rfl⟩ : ∃ l cs, p = RoseTree.node l cs :=
    ⟨p.label, p.children, (RoseTree.node_label_children p).symm⟩
  rcases cs with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩ <;>
    mirror_simp [«Language.binParts», none_eq, some_eq, decide_eq_true_eq, beq_iff_eq,
      Nat.add_right_cancel_iff, Nat.add_one_ne_zero]
  all_goals split_ifs <;> first | rfl | omega

/-- The mirror's factors of a product. -/
theorem prodParts_eq (p : Tree) :
    «Language.prodParts» p = encOpt ((Internal.prodParts p).map encPair) :=
  binParts_eq _ p

/-- The mirror's summands of a coproduct. -/
theorem coprodParts_eq (p : Tree) :
    «Language.coprodParts» p = encOpt ((Internal.coprodParts p).map encPair) :=
  binParts_eq _ p

/-- The mirror's domain and codomain of an exponential. -/
theorem expParts_eq (p : Tree) :
    «Language.expParts» p = encOpt ((Internal.expParts p).map encPair) :=
  binParts_eq _ p

/-- The mirror's element type of a list object. -/
theorem listPart_eq (p : Tree) :
    «Language.listPart» p = encOpt (Internal.listPart p) := by
  obtain ⟨l, cs, rfl⟩ : ∃ l cs, p = RoseTree.node l cs :=
    ⟨p.label, p.children, (RoseTree.node_label_children p).symm⟩
  rcases cs with _ | ⟨a, _ | ⟨b, cs⟩⟩ <;>
    mirror_simp [«Language.listPart», Internal.listPart, none_eq, some_eq,
      decide_eq_true_eq, mirror_list, beq_iff_eq]
  all_goals split_ifs <;> first | rfl | omega

/-- The mirror's type of labels of a rose-tree object. -/
theorem roseLabel_eq (p : Tree) :
    «Language.roseLabel» p = encOpt ((Internal.roseParts p).map Prod.fst) := by
  obtain ⟨l, cs, rfl⟩ : ∃ l cs, p = RoseTree.node l cs :=
    ⟨p.label, p.children, (RoseTree.node_label_children p).symm⟩
  by_cases hr : RoseTree.node l cs = rose
  · mirror_simp [«Language.roseLabel», Internal.roseParts, hr, some_eq, mirror_rose,
      mirror_nat, decide_true]
  · rcases cs with _ | ⟨a, _ | ⟨b, cs⟩⟩ <;>
      mirror_simp [«Language.roseLabel», Internal.roseParts, hr, none_eq, some_eq,
        decide_eq_true_eq, mirror_rose, mirror_lrose, beq_iff_eq]
    all_goals split_ifs <;> first | rfl | omega

/-- The mirror's fold of a rose-tree object by a step. -/
theorem roseFold_eq (p s a : Tree) (fold : Tree → Tree)
    (h : Internal.roseParts p = some (a, fold)) : «Language.roseFold» p s = fold s := by
  obtain ⟨l, cs, rfl⟩ : ∃ l cs, p = RoseTree.node l cs :=
    ⟨p.label, p.children, (RoseTree.node_label_children p).symm⟩
  by_cases hr : RoseTree.node l cs = rose
  · simp only [Internal.roseParts, hr, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    mirror_simp [«Language.roseFold», hr, mirror_rose, mirror_roseRec, decide_true]
  · rcases cs with _ | ⟨b, _ | ⟨c, cs⟩⟩ <;>
      simp only [Internal.roseParts, hr, ↓reduceIte, RoseTree.children_node,
        reduceCtorEq] at h
    split_ifs at h with hb
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    mirror_simp [«Language.roseFold», hr, mirror_rose, mirror_lroseRec, decide_false]

/-- The mirror's product of a context's types. -/
@[simp] theorem ctxObj_eq (Γ : List Tree) : «Language.ctxObj» Γ = Internal.ctxObj Γ := by
  simp only [«Language.ctxObj», foldr_eq]
  refine congrArg Prod.fst (?_ : _ = (Internal.ctxObj Γ, leaf (if Γ.isEmpty then 0 else 1)))
  refine Γ.rec rfl fun a Γ ih ↦ ?_
  rw [List.foldr_cons, ih]
  cases Γ <;> rfl

/-- The mirror's extension of an encoded environment by a variable. -/
@[simp] theorem extendEnv_eq (X a : Tree) (e : List (Tree × Tree)) :
    «Language.extendEnv» X a (e.map encPair) = (Internal.extEnv X a e).map encPair := by
  mirror_simp [«Language.extendEnv», Internal.extEnv, pr_eq, p1_eq, p2_eq, mirror_comp,
    mirror_cFst, mirror_cSnd]

/-- The mirror's environment of a context's projections. -/
@[simp] theorem stdEnv_eq (Γ : List Tree) :
    «Language.stdEnv» Γ = (Internal.stdEnv Γ).map encPair := by
  simp only [«Language.stdEnv», foldr_eq]
  refine congrArg Prod.fst (?_ : _ = ((Internal.stdEnv Γ).map encPair, Γ))
  refine Γ.rec rfl fun a Γ ih ↦ ?_
  rw [List.foldr_cons, ih]
  cases Γ <;> mirror_simp [Internal.stdEnv, extendEnv_eq, ctxObj_eq, pr_eq, mirror_idt,
    List.isEmpty_cons, List.isEmpty_nil]

/-- The mirror's tuple of arrows. -/
@[simp] theorem tuple_eq (X : Tree) (fs : List Tree) :
    «Language.tuple» X fs = Internal.tuple X fs := by
  simp only [«Language.tuple», foldr_eq]
  refine congrArg Prod.fst (?_ : _ = (Internal.tuple X fs, leaf (if fs.isEmpty then 0 else 1)))
  refine fs.rec rfl fun f fs ih ↦ ?_
  rw [List.foldr_cons, ih]
  cases fs <;> rfl

/-- The mirror's number of a definition's object parameters. -/
@[simp] theorem ldArity_eq (d : Internal.Defn) :
    «Language.ldArity» (encLDefn d) = leaf d.arity := rfl

/-- The mirror's types of a definition's parameters. -/
@[simp] theorem ldParams_eq (d : Internal.Defn) :
    «Language.ldParams» (encLDefn d) = d.params := by
  simp [«Language.ldParams», encLDefn]

/-- The mirror's type of a definition's value. -/
@[simp] theorem ldType_eq (d : Internal.Defn) :
    «Language.ldType» (encLDefn d) = d.type := rfl

/-- The mirror's body of a definition. -/
@[simp] theorem ldBody_eq (d : Internal.Defn) :
    «Language.ldBody» (encLDefn d) = encTerm d.body := rfl

/-- The mirror's number of a primitive arrow's object parameters. -/
@[simp] theorem prArity_eq (p : Internal.Prim) :
    «Language.prArity» (encPrim p) = leaf p.arity := rfl

/-- The mirror's arrow of a primitive arrow. -/
@[simp] theorem prArrow_eq (p : Internal.Prim) :
    «Language.prArrow» (encPrim p) = p.arrow := rfl

/-- The mirror's domain of a primitive arrow. -/
@[simp] theorem prDom_eq (p : Internal.Prim) : «Language.prDom» (encPrim p) = p.dom :=
  rfl

/-- The mirror's codomain of a primitive arrow. -/
@[simp] theorem prCod_eq (p : Internal.Prim) : «Language.prCod» (encPrim p) = p.cod :=
  rfl

/-- The mirror's definition of the language a definition is, where it is one. -/
@[simp] theorem defLanguage_eq (d : Internal.Definition) :
    «Language.defLanguage» (encDefinition d) =
      encOpt (d.language?.map encLDefn) := by
  cases d <;> rfl

/-- The mirror's primitive arrows of the constants. -/
@[simp] theorem gPrims_eq (G : Internal.Globals) :
    «Language.gPrims» (encGlobals G) = G.prims.map encPrim := by
  simp [«Language.gPrims», encGlobals]

/-- The mirror's definitions of the constants. -/
@[simp] theorem gDefs_eq (G : Internal.Globals) :
    «Language.gDefs» (encGlobals G) = G.defs.map encDefinition := by
  simp [«Language.gDefs», encGlobals]

/-- The mirror's index of the first definition's operation. -/
@[simp] theorem gBase_eq (G : Internal.Globals) :
    «Language.gBase» (encGlobals G) = leaf G.base := rfl

/-- The mirror's constants of encoded primitive arrows and definitions. -/
@[simp] theorem globals_eq (ps : List Internal.Prim) (ds : List Internal.Definition) (b : ℕ) :
    «Language.globals» (RoseTree.node 0 (ps.map encPrim))
        (RoseTree.node 0 (ds.map encDefinition)) (leaf b) = encGlobals ⟨ps, ds, b⟩ := rfl

/-- The mirror's test of an operation that builds types. -/
theorem isTyOp_eq (G : Internal.Globals) (k m : ℕ) :
    «Language.isTyOp» (encGlobals G) (leaf k) (leaf m) = ofBool (G.isTyOp k m) := by
  have ht : «Base.anyT» (fun t ↦ Const.equal t (encPair (leaf k, leaf m)))
      «Language.tyOps» = ofBool (decide ((k, m) ∈ Internal.tyOps)) := by
    rw [anyT_eq (fun t ↦ Const.equal t (encPair (leaf k, leaf m)))
      (fun t ↦ decide (t = encPair (leaf k, leaf m))) _ fun _ _ ↦ rfl, tyOps_eq]
    congr 1
    rw [Bool.eq_iff_iff]
    simp [encPair_inj, leaf_inj]
  rw [«Language.isTyOp», pr_eq, ht]
  mirror_simp [gBase_eq, gDefs_eq, Internal.Globals.isTyOp]
  cases G.defs[k - G.base]? with
  | none => mirror_simp [none_eq, ← ofBool_false, Bool.or_false]
  | some d =>
    cases d
    · mirror_simp [encDefinition, some_eq, ← ofBool_false, Bool.or_false]
    · mirror_simp [encDefinition, some_eq, ← decide_not, Nat.not_lt]

/-- The mirror's test of a type in object variables. -/
theorem isTy_eq (G : Internal.Globals) (n : ℕ) (t : Tree) :
    «Language.mIsTy» (encGlobals G) (leaf n) t = ofBool (Internal.IsTy G n t) := by
  simp only [«Language.mIsTy», Internal.IsTy]
  apply fold_pair_snd (fun (v : Tree) (w : Bool) ↦ v = ofBool w)
  · intro l rs
    simp
  intro l xs hx
  have hv : (xs.map fun x ↦ (x.1, x.2.1)).map Prod.snd = xs.map fun x ↦ ofBool x.2.2 := by
    simp only [List.map_map, Function.comp_def]
    exact List.map_congr_left hx
  cases l with
  | zero =>
    rcases xs with _ | ⟨x, _ | ⟨y, r⟩⟩ <;>
      mirror_simp [ptTrees_eq, beq_iff_eq, Nat.reduceEqDiff] <;> rfl
  | succ k =>
    mirror_simp [ptTrees_eq, ptValues_eq, hv, isTyOp_eq, allT_ofBool, Nat.add_sub_cancel,
      beq_iff_eq, Nat.add_one_ne_zero]

/-- The mirror's compilation of a term and the compilation's are related when they agree at
every encoded environment. -/
def CRel (v : Tree → List Tree → Tree)
    (w : Tree → List (Tree × Tree) → Option (Tree × Tree)) : Prop :=
  ∀ X e, v X (e.map encPair) = encOpt ((w X e).map encPair)

/-- The terms of a list of terms with their compilations. -/
@[simp] theorem cpTrees_eq (rs : List (Tree × (Tree → List Tree → Tree))) :
    «Language.cpTrees» rs = rs.map Prod.fst :=
  rs.rec rfl fun _ _ ih ↦ by
    simp only [«Language.cpTrees», foldr_eq, List.foldr_cons] at ih ⊢
    rw [ih]
    rfl

/-- A list of terms with their compilations without its head. -/
@[simp] theorem cpTail_eq (rs : List (Tree × (Tree → List Tree → Tree))) :
    «Language.cpTail» rs = rs.tail := by
  cases rs <;> rfl

/-- Dropping the head of a list of terms with their compilations as many times as a label. -/
theorem repeat_cpTail (rs : List (Tree × (Tree → List Tree → Tree))) :
    ∀ i : ℕ, Nat.repeat «Language.cpTail» i rs = rs.drop i :=
  Nat.rec rfl fun i ih ↦ by rw [Nat.repeat, ih, cpTail_eq, List.tail_drop]

/-- The compilation of a term at a position, nothing out of range. -/
@[simp] theorem cpAt_eq (rs : List (Tree × (Tree → List Tree → Tree))) (i : ℕ) :
    «Language.cpAt» rs (leaf i) =
      (rs[i]?.map Prod.snd).getD fun _ _ ↦ «Prelude.none» := by
  simp only [«Language.cpAt», iter_leaf, repeat_cpTail]
  cases h : rs.drop i with
  | nil =>
    rw [List.drop_eq_nil_iff] at h
    rw [List.getElem?_eq_none h]
    rfl
  | cons r rest =>
    have : rs[i]? = some r := by
      rw [← List.head?_drop, h]
      rfl
    rw [this]
    rfl

/-- The compilations of a list of terms in an environment. -/
@[simp] theorem cpAll_eq (rs : List (Tree × (Tree → List Tree → Tree))) (X : Tree)
    (e : List Tree) : «Language.cpAll» rs X e = rs.map fun r ↦ r.2 X e :=
  rs.rec rfl fun _ _ ih ↦ by
    simp only [«Language.cpAll», foldr_eq, List.foldr_cons] at ih ⊢
    rw [ih]
    rfl

/-- The simplification of a case of the mirror's compilation step: the lemmas of
{lit}`mirror_simp`, the step's lists, pairs and combinators, and the given lemmas. -/
local macro "compile_simp" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  mirror_simp [«Language.compileStep», labelData, Internal.compileStep, cpTrees_eq,
    cpTail_eq, cpAt_eq, cpAll_eq, none_eq, some_eq, pr_eq, p1_eq, p2_eq, beq_iff_eq,
    Nat.add_one_ne_zero, Nat.reduceEqDiff, Option.elim_map, Option.map_bind, Option.bind_eq_bind,
    Option.pure_def, Bool.and_eq_true, decide_eq_true_eq, List.mem_cons,
    true_or, or_true, mirror_idt, mirror_comp, mirror_one, mirror_bang, mirror_prod, mirror_cFst,
    mirror_cSnd, mirror_cPair, mirror_exp, mirror_ev, mirror_curry, mirror_omega, mirror_chi,
    mirror_nat, mirror_natRec, mirror_list, mirror_listRec, mirror_diag, $ls,*])

/-- The mirror's compilation step at an encoded node is the compilation step at the node it
encodes, at related compilations of the children. -/
theorem compileStep_eq (G : Internal.Globals) (n : ℕ) (l : Label) (v : Tree → List Tree → Tree)
    (xs : List (Term × (Tree → List Tree → Tree) ×
      (Tree → List (Tree × Tree) → Option (Tree × Tree))))
    (hx : ∀ x ∈ xs, CRel x.2.1 x.2.2) (X : Tree) (e : List (Tree × Tree)) :
    «Language.compileStep» (encGlobals G) (leaf n) (leaf (labelData l).1)
        ((RoseTree.node 0 (labelData l).2, v) :: xs.map fun x ↦ (encTerm x.1, x.2.1)) X
        (e.map encPair) =
      encOpt ((Internal.compileStep G n l (xs.map fun x ↦ (x.1, x.2.2)) X e).map encPair) := by
  have h0 : ∀ x ∈ xs, ∀ X e, x.2.1 X (e.map encPair) = encOpt ((x.2.2 X e).map encPair) := hx
  have h1 : ∀ x ∈ xs, ∀ X, x.2.1 X [] = encOpt ((x.2.2 X []).map encPair) :=
    fun x h X ↦ hx x h X []
  have h2 : ∀ x ∈ xs, ∀ X p, x.2.1 X [encPair p] = encOpt ((x.2.2 X [p]).map encPair) :=
    fun x h X p ↦ hx x h X [p]
  have h3 : ∀ x ∈ xs, ∀ X p q,
      x.2.1 X [encPair p, encPair q] = encOpt ((x.2.2 X [p, q]).map encPair) :=
    fun x h X p q ↦ hx x h X [p, q]
  cases l
  case var i => rcases xs with _ | ⟨x0, r⟩ <;> compile_simp []
  case star => rcases xs with _ | ⟨x0, r⟩ <;> compile_simp []
  case pair =>
    rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, r⟩⟩⟩ <;> compile_simp [h0]
    rcases x0.2.2 X e with _ | ⟨f, a⟩ <;> rcases x1.2.2 X e with _ | ⟨g, b⟩ <;> compile_simp []
  case fst | snd =>
    rcases xs with _ | ⟨x0, _ | ⟨x1, r⟩⟩ <;> compile_simp [h0]
    rcases x0.2.2 X e with _ | ⟨f, p⟩ <;> compile_simp [prodParts_eq]
    rcases Internal.prodParts p with _ | ⟨a, b⟩ <;> compile_simp []
  case lam a =>
    rcases xs with _ | ⟨x0, _ | ⟨x1, r⟩⟩ <;> compile_simp [h0, isTy_eq, extendEnv_eq]
    by_cases ha : Internal.IsTy G n a <;> compile_simp [ha]
    rcases x0.2.2 (prod X a) (Internal.extEnv X a e) with _ | ⟨f, b⟩ <;> compile_simp []
  case app =>
    rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, r⟩⟩⟩ <;> compile_simp [h0]
    rcases x0.2.2 X e with _ | ⟨f, p⟩ <;> compile_simp [expParts_eq]
    rcases Internal.expParts p with _ | ⟨a, b⟩ <;> compile_simp []
    rcases x1.2.2 X e with _ | ⟨g, a'⟩ <;> compile_simp []
    split_ifs with h <;> simp [h]
  case eq =>
    rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, r⟩⟩⟩ <;> compile_simp [h0]
    rcases x0.2.2 X e with _ | ⟨f, a⟩ <;> rcases x1.2.2 X e with _ | ⟨g, b⟩ <;> compile_simp []
    split_ifs with h <;> simp [h]
  case natRec =>
    rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, r⟩⟩⟩⟩ <;> compile_simp [h0, h1, h2]
    rcases x0.2.2 one [] with _ | ⟨z, c⟩ <;> compile_simp []
    rcases x1.2.2 c [(idt c, c)] with _ | ⟨s, c'⟩ <;> compile_simp []
    rcases x2.2.2 X e with _ | ⟨m, t⟩ <;> compile_simp []
    split_ifs with h <;> simp [h]
  case listRec =>
    rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, r⟩⟩⟩⟩ <;>
      compile_simp [h0, h1, h3, listPart_eq, «Theory.l2»]
    rcases x2.2.2 X e with _ | ⟨m, t⟩ <;> compile_simp []
    rcases Internal.listPart t with _ | a <;> compile_simp []
    rcases x0.2.2 one [] with _ | ⟨z, c⟩ <;> compile_simp []
    rcases x1.2.2 (prod a c) [(snd a c, c), (fst a c, a)] with _ | ⟨s, c'⟩ <;> compile_simp []
    split_ifs with h <;> simp [h]
  case roseRec c =>
    rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, r⟩⟩⟩ <;>
      compile_simp [h0, h2, isTy_eq, roseLabel_eq]
    by_cases hc : Internal.IsTy G n c <;> compile_simp [hc]
    rcases x1.2.2 X e with _ | ⟨m, t⟩ <;> compile_simp []
    rcases hr : Internal.roseParts t with _ | ⟨a, fold⟩ <;> compile_simp []
    have hf : ∀ s, «Language.roseFold» t s = fold s := fun s ↦ roseFold_eq t s a fold hr
    rcases x0.2.2 (prod a (list c)) [(idt (prod a (list c)), prod a (list c))] with _ | ⟨s, c'⟩ <;>
      compile_simp [hf]
    split_ifs <;> simp
  case arr k θ =>
    have hall : «Base.allT» («Language.mIsTy» (encGlobals G) (leaf n)) θ =
        ofBool (θ.all (Internal.IsTy G n)) := allT_eq _ _ θ fun t _ ↦ isTy_eq G n t
    rcases xs with _ | ⟨x0, _ | ⟨x1, r⟩⟩ <;>
      compile_simp [h0, gPrims_eq, hall, phSubst_eq, prArity_eq, prArrow_eq, prDom_eq, prCod_eq]
    rcases G.prims[k]? with _ | pm <;> compile_simp [prArity_eq, prArrow_eq, prDom_eq, prCod_eq]
    rcases x0.2.2 X e with _ | ⟨g, d⟩ <;> compile_simp []
    split_ifs with h <;> simp only [h, and_self, ↓reduceIte, Option.map_some, Option.map_none]
  case defn k θ =>
    have hall : «Base.allT» («Language.mIsTy» (encGlobals G) (leaf n)) θ =
        ofBool (θ.all (Internal.IsTy G n)) := allT_eq _ _ θ fun t _ ↦ isTy_eq G n t
    have hxs : xs.map (fun x ↦ x.2.1 X (e.map encPair)) =
        xs.map fun x ↦ encOpt ((x.2.2 X e).map encPair) :=
      List.map_congr_left fun x hx ↦ h0 x hx X e
    compile_simp [gDefs_eq, gBase_eq, hall, hxs, allSomeT_eq, mapM_map_option, List.mapM_map,
      funext (phSubst_eq θ), phSubst_eq, phOp_eq, tuple_eq, mapT_eq]
    rcases G.defs[k]? with _ | (d | ⟨m, b⟩) <;>
      compile_simp [defLanguage_eq, Internal.Definition.language?, ldArity_eq, ldParams_eq,
        ldType_eq]
    cases hm : List.mapM (fun x ↦ x.2.2 X e) xs <;> compile_simp [hm]
    split_ifs <;> simp

/-- The mirror's compilation of an encoded term. -/
theorem compile_eq (G : Internal.Globals) (n : ℕ) (t : Term) :
    CRel («Language.compile» (encGlobals G) (leaf n) (encTerm t))
      (Internal.compile G n t) :=
  fold_pair_enc (fun l ↦ (labelData l).1) (fun l ↦ RoseTree.node 0 (labelData l).2) CRel
    (fun l rs ↦ by simp only [cpTrees_eq]) (Internal.compileStep G n)
    (fun l v xs hx X e ↦ compileStep_eq G n l v xs hx X e) t

/-- The mirror's test that a list of objects are types. -/
theorem allT_isTy (G : Internal.Globals) (n : ℕ) (ts : List Tree) :
    «Base.allT» («Language.mIsTy» (encGlobals G) (leaf n)) ts =
      ofBool (ts.all (Internal.IsTy G n)) :=
  allT_eq _ _ ts fun t _ ↦ isTy_eq G n t

/-- The mirror's compilation of a definition of the language. -/
theorem ldCompile_eq (G : Internal.Globals) (d : Internal.Defn) :
    «Language.ldCompile» (encGlobals G) (encLDefn d) =
      encOpt ((d.compile G).map encDefn) := by
  have hc := compile_eq G d.arity d.body (Internal.ctxObj d.params) (Internal.stdEnv d.params)
  simp only [«Language.ldCompile», ldArity_eq, ldBody_eq, ldParams_eq, ldType_eq,
    ctxObj_eq, stdEnv_eq, hc, Internal.Defn.compile]
  rcases Internal.compile G d.arity d.body (Internal.ctxObj d.params) (Internal.stdEnv d.params)
    with _ | ⟨f, c⟩ <;>
    mirror_simp [allT_isTy, none_eq, some_eq, p1_eq, p2_eq, «PartialHorn.pdefn», encDefn,
      List.map_replicate, Option.bind_eq_bind, Option.pure_def, Option.elim_map, Bool.and_eq_true,
      decide_eq_true_eq]
  split_ifs with h <;>
    simp only [h, and_self, ↓reduceIte, Option.map_some, Option.map_none,
      encDefn, List.map_replicate]

/-- The mirror's compilation of a definition of either kind. -/
theorem defCompile_eq (G : Internal.Globals) (d : Internal.Definition) :
    «Language.defCompile» (encGlobals G) (encDefinition d) =
      encOpt ((d.compile G).map encDefn) := by
  cases d with
  | language d =>
    mirror_simp [«Language.defCompile», encDefinition, Internal.Definition.compile]
    exact ldCompile_eq G d
  | object m b =>
    mirror_simp [«Language.defCompile», encDefinition, Internal.Definition.compile,
      some_eq, «PartialHorn.pdefn», encDefn, List.map_replicate]

/-- The positions of a list, each with its encoded element, are the list's indexed elements. -/
theorem range_getD_eq {α β : Type} (ds : List α) (enc : α → Tree) (f : ℕ → Tree → β) :
    (List.range ds.length).map (fun i ↦ f i ((ds.map enc).getD i (leaf 0))) =
      ds.zipIdx.map fun p ↦ f p.2 (enc p.1) := by
  refine List.ext_getElem (by simp) fun i h₁ h₂ ↦ ?_
  simp only [List.getElem_map, List.getElem_range, List.getElem_zipIdx, zero_add,
    List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (show i < ds.length by simpa using h₂), Option.map_some,
    Option.getD_some]

/-- The mirror's compilation of the definitions of the constants. -/
theorem compileDefs_eq (G : Internal.Globals) :
    «Language.compileDefs» (encGlobals G) =
      encOpt ((Internal.compileDefs G).map fun ds ↦ RoseTree.node 0 (ds.map encDefn)) := by
  simp only [«Language.compileDefs», gDefs_eq, gPrims_eq, gBase_eq, length_eq,
    List.length_map, range_eq, mapT_eq, List.map_map, Function.comp_def, take_eq, at_eq,
    ← List.map_take, node_leaf, globals_eq]
  rw [range_getD_eq G.defs encDefinition fun i t ↦ «Language.defCompile»
    (encGlobals ⟨G.prims, G.defs.take i, G.base⟩) t]
  simp only [defCompile_eq, allSomeT_eq, mapM_map_option, Option.map_map, Function.comp_def,
    Internal.compileDefs]

/-- The mirror's compilation of an equation of two terms in a context. -/
theorem compileEq_eq (G : Internal.Globals) (n : ℕ) (Γ : List Tree) (t u : Term) :
    «Language.compileEq» (encGlobals G) (leaf n) Γ (encTerm t) (encTerm u) =
      encOpt ((Internal.compileEq G n Γ t u).map encSeq) := by
  have ht := compile_eq G n t (Internal.ctxObj Γ) (Internal.stdEnv Γ)
  have hu := compile_eq G n u (Internal.ctxObj Γ) (Internal.stdEnv Γ)
  simp only [«Language.compileEq», ctxObj_eq, stdEnv_eq, ht, hu, Internal.compileEq]
  rcases Internal.compile G n t (Internal.ctxObj Γ) (Internal.stdEnv Γ) with _ | ⟨f, a⟩ <;>
    rcases Internal.compile G n u (Internal.ctxObj Γ) (Internal.stdEnv Γ) with _ | ⟨g, b⟩ <;>
    mirror_simp [allT_isTy, none_eq, some_eq, p1_eq, p2_eq, eqn_eq,
      «PartialHorn.mkSeq», «PartialHorn.seq», Option.bind_eq_bind, Option.pure_def,
      Option.elim_map, Bool.and_eq_true, decide_eq_true_eq]
  split_ifs with h <;>
    simp only [h, and_self, ↓reduceIte, Option.map_some, Option.map_none,
      encSeq, List.map_replicate, List.map_nil]

/-- The mirror's test that an optional sort is a given sort. -/
theorem decide_sort (o : Option ℕ) (s : ℕ) :
    decide (encOpt (o.map leaf) = «Prelude.some» (leaf s)) = (o == some s) := by
  cases o <;> simp [some_eq, encOpt_inj, leaf_inj, beq_eq_decide]

/-- The mirror's conjunction with the leaf of label zero. -/
theorem and_leaf_zero (a : Bool) :
    «Prelude.and» (ofBool a) (leaf 0) = ofBool false := by
  cases a <;> rfl

/-- The mirror's sort of a term in object parameters. -/
theorem sortOf_objs (S : PartialHorn.Sig) (m : ℕ) (t : Tree) :
    «PartialHorn.sortOf» (S.map encOpSig) (List.replicate m (leaf 0)) t =
      encOpt ((PartialHorn.sortOf S (List.replicate m Sorts.obj) t).map leaf) := by
  simpa only [List.map_replicate] using sortOf_eq S (List.replicate m Sorts.obj) t

/-- The mirror's inference in object parameters under no hypotheses. -/
theorem infers_objs (E : ExtEnv) (m : ℕ) (t : Tree) :
    («Infer.infers» (encExtEnv E) (List.replicate m (leaf 0)) []
        «Infer.inferFuel»).2 t =
      encOpt (((infers E (List.replicate m Sorts.obj) [] inferFuel).2 t).map encAnn) := by
  simpa only [List.map_replicate, List.map_nil, «Infer.inferFuel», inferFuel] using
    (infers_eq E (List.replicate m Sorts.obj) [] inferFuel).2 t

/-- The mirror's test of a primitive arrow's form. -/
theorem primWf_eq (G : Internal.Globals) (S : PartialHorn.Sig) (p : Internal.Prim) :
    «Language.primWf» (encGlobals G) (S.map encOpSig) (encPrim p) =
      ofBool (p.wf G S) := by
  mirror_simp [«Language.primWf», prArity_eq, prArrow_eq, prDom_eq, prCod_eq,
    scoped_eq, isTy_eq, sortOf_objs, decide_sort, Internal.Prim.wf, Bool.and_assoc]

/-- The mirror's test of a primitive arrow. -/
theorem primOk_eq (G : Internal.Globals) (E : ExtEnv) (p : Internal.Prim) :
    «Language.primOk» (encGlobals G) (encExtEnv E) (encPrim p) =
      ofBool (p.ok G E) := by
  mirror_simp [«Language.primOk», envSg_eq, primWf_eq, prArity_eq, prArrow_eq,
    prDom_eq, prCod_eq, infers_objs, Internal.Prim.ok]
  rcases (infers E (List.replicate p.arity Sorts.obj) [] inferFuel).2 p.arrow with _ | a <;>
    rcases (infers E (List.replicate p.arity Sorts.obj) [] inferFuel).2 p.dom with _ | d <;>
    rcases (infers E (List.replicate p.arity Sorts.obj) [] inferFuel).2 p.cod with _ | c <;>
    mirror_simp [annSort_eq, annLo_eq, annHi_eq, and_leaf_zero, Bool.and_assoc, beq_eq_decide]

/-- The mirror's test of an object in object parameters. -/
theorem objOk_eq (E : ExtEnv) (m : ℕ) (b : Tree) :
    «Language.objOk» (encExtEnv E) (leaf m) b = ofBool (Internal.objOk E m b) := by
  mirror_simp [«Language.objOk», envSg_eq, sortOf_objs, decide_sort, infers_objs,
    Internal.objOk, Option.isSome_map]

end GebTests.Prototypes.FreeTopos.Agreement.Language

end
