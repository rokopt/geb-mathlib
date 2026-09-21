/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.BitStream.Oitavem.Edge
public import Geb.Prototypes.BitStream.Oitavem.Bundle
public import Geb.Prototypes.BitStream.Oitavem.Stream
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The recognizer of Oitavem-coded bitstreams

A word codes a bitstream when it is the spelling of a bundle: an admissible
tree of the bundle signature whose root is the root shape, which is to say
an expression of Logs with one normal and no safe argument under a root
node. The recognizer of the coded signature's admissible trees, with the
label and edge checks of the bundle signature, accepts every admissible tree
whatever its root; the root is the root shape exactly when the spelling
begins with the root's fixed prefix, since the root shape alone produces the
root index and no shape requires it of a child. The recognizer of coded
bitstreams is the conjunction of the prefix test with that recognizer, as an
expression of the logspace subalgebra, and a recognized word denotes the
stream its expression codes.

# Main definitions

* {lit}`startsWithExpr` — the test of a fixed prefix at a pointer.
* {lit}`recognize`, {lit}`recognizer` — the recognizer, and the recognizer
  as an expression.
* {lit}`spellExpr`, {lit}`decodeExpr`, {lit}`decodeStream` — the word coding
  an expression's stream, the expression a word spells, and the stream a
  word codes.

# Main statements

* {lit}`sem_startsWithExpr` — the prefix test reads as the prefix relation.
* {lit}`head_none_of_prefix` — a spelling with the root's prefix is the
  spelling of a tree with the root shape at its root.
* {lit}`recognize_iff`, {lit}`recognize_iff_spellExpr` — the recognizer
  accepts exactly the spellings of bundles, which are the words coding the
  streams of expressions.
* {lit}`recognizerSem_eq`, {lit}`recognizerSem_eq_singleton_iff` — the
  expression's value is the recognizer's verdict as a word, and it accepts
  exactly the words the recognizer accepts.
* {lit}`decodeExpr_spellExpr`, {lit}`decodeStream_spellExpr` — a coding
  word decodes to the expression it spells, and to that expression's
  stream.

# References

* {cite}`Oitavem2010`, Definition 3.1.
* {cite}`Kristiansen2005`

# Tags

bitstream, M-type, logspace, recognizer, coded signature
-/

set_option doc.verso true

namespace Geb.BitStream.Oitavem

open Geb.SizeBounded.Logspace (LOf tailAppL sem_tailAppL constL sem_constL projL)
open Geb.SizeBounded.Logspace.WTree (CodedSig boolWord isTrueWord onBitAt sem_onBitAt recognizeExpr
  spine)
open Geb.SizeBounded.Logspace.WTree.SigLabel (andF sem_andF boolWord_decide boolWord_decide_congr
  sem_onBitAt_nil)
open Geb.BitTree (Tree leaf fork)
open Geb.BitTree.Elias (encode encodeNat)
open Geb.Oitavem (Expr)

public section

variable {n : ℕ}

/-- The test of a fixed prefix at a pointer: the dispatch on each bit of the
prefix in turn. -/
@[expose] def startsWithExpr : List Bool → LOf n → LOf n
  | [], _ => constL n [true]
  | b :: bs, p =>
    onBitAt p (constL n [])
      (if b then startsWithExpr bs (tailAppL p) else constL n [])
      (if b then constL n [] else startsWithExpr bs (tailAppL p))

/-- The prefix test reads as the prefix relation. -/
theorem sem_startsWithExpr (x : Fin n → List Bool) : ∀ (P : List Bool) (p : LOf n),
    (startsWithExpr P p).sem x = boolWord (decide (P <+: p.sem x))
  | [], p => by
    rw [startsWithExpr, sem_constL, boolWord_decide, ite_eq_left List.nil_prefix]
  | b :: bs, p => by
    cases hw : p.sem x with
    | nil =>
      rw [startsWithExpr, sem_onBitAt_nil _ _ _ _ x hw, sem_constL, boolWord_decide,
        ite_eq_right (by rw [List.prefix_nil]; exact List.cons_ne_nil b bs)]
    | cons c w =>
      have ht : (tailAppL p).sem x = w := by rw [sem_tailAppL, hw]; rfl
      rw [startsWithExpr, sem_onBitAt _ _ _ _ x c w hw]
      cases b <;> cases c
      · rw [ite_eq_right (by decide), ite_eq_right (by decide), sem_startsWithExpr x bs _, ht]
        exact boolWord_decide_congr _ _ (List.cons_prefix_cons.trans (and_iff_right rfl)).symm
      · rw [ite_eq_left rfl, ite_eq_right (by decide), sem_constL, boolWord_decide,
          ite_eq_right fun h ↦ Bool.noConfusion (List.cons_prefix_cons.mp h).1]
      · rw [ite_eq_right (by decide), ite_eq_left rfl, sem_constL, boolWord_decide,
          ite_eq_right fun h ↦ Bool.noConfusion (List.cons_prefix_cons.mp h).1]
      · rw [ite_eq_left rfl, ite_eq_left rfl, sem_startsWithExpr x bs _, ht]
        exact boolWord_decide_congr _ _ (List.cons_prefix_cons.trans (and_iff_right rfl)).symm

/-- The recognizer: the coded signature's recognizer, and the root's prefix. -/
@[expose] def recognize (w : List Bool) : Bool := coded.recognize w && decide (rootPrefix <+: w)

/-- The recognizer as an expression of the subalgebra. -/
@[expose] def recognizer : LOf 1 :=
  andF (startsWithExpr rootPrefix (projL 1 0)) (recognizeExpr LabelExpr.labelOk EdgeExpr.edgeOk)

/-- The word coding an expression's stream: the spelling of the expression
under a root. -/
@[expose] def spellExpr (e : Expr 1 0) : List Bool := coded.spell (wrap e).1.1

/-- The encoding of a left spine: one set bit per fork, the encoding of the
leftmost tree, and the encodings of the children. -/
theorem encode_spine (t : Tree) : ∀ cs : List Tree,
    encode (spine t cs) = List.replicate cs.length true ++ (encode t ++ cs.flatMap encode)
  | [] => by simp only [spine, List.foldl_nil, List.length_nil, List.replicate_zero,
      List.nil_append, List.flatMap_nil, List.append_nil]
  | c :: cs => by
    rw [spine, List.foldl_cons, ← spine, encode_spine (fork t c) cs, List.length_cons,
      List.replicate_succ', List.append_assoc, List.singleton_append, Geb.BitTree.Elias.encode_fork,
      List.flatMap_cons, List.cons_append, List.append_assoc]

/-- The spelling of a tree with the root shape at its root: the prefix, then
the spelling of the child. -/
theorem spell_mk_none (f : Unit → sig.toPFunctor.W) :
    coded.spell (WType.mk none f) = rootPrefix ++ coded.spell (f ()) := by
  change encode (spine (leaf (code none)) (List.ofFn fun i : Fin 1 ↦ coded.toTree (f ()))) = _
  rw [List.ofFn_succ, List.ofFn_zero]
  rfl

/-- A tree whose spelling begins with the root's prefix has the root shape at
its root. -/
theorem head_none_of_prefix (t : sig.toPFunctor.W) (h : rootPrefix <+: coded.spell t) :
    PFunctor.W.head t = none := by
  obtain ⟨rest, hrest⟩ := h
  cases t with
  | mk a f =>
    have hspell : coded.spell (WType.mk a f) =
        encode (spine (leaf (coded.code a)) (List.ofFn fun i ↦ coded.toTree (f (coded.dir a i)))) :=
      congrArg encode (coded.toTree_mk a f)
    have hrest := hrest.trans hspell
    generalize List.ofFn (fun i ↦ coded.toTree (f (coded.dir a i))) = cs at hrest
    rw [encode_spine] at hrest
    match cs, hrest with
    | [], hrest =>
      rw [List.length_nil, List.replicate_zero, List.nil_append, Geb.BitTree.Elias.encode_leaf,
        rootPrefix, List.cons_append] at hrest
      cases hrest
    | [c], hrest =>
      rw [List.length_singleton, List.replicate_one, List.singleton_append,
        Geb.BitTree.Elias.encode_leaf, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        rootPrefix, List.cons_append, List.cons_append, List.append_assoc, List.cons_append,
        List.append_assoc] at hrest
      have h1 := (List.cons.inj (List.cons.inj hrest).2).2
      have h2 := Geb.BitTree.Elias.readNat_encodeNat_append (coded.code a).length
        (coded.code a ++ encode c)
      rw [← h1, Geb.BitTree.Elias.readNat_encodeNat_append, Option.some.injEq, Prod.mk.injEq] at h2
      have h3 := List.append_inj_left h2.2 h2.1
      have h4 : coded.decode (coded.code a) = some a := coded.decode_code a
      rw [← h3] at h4
      have h5 : coded.decode (coded.code none) = some none := coded.decode_code none
      exact (Option.some.inj (h5.symm.trans h4)).symm
    | c₁ :: c₂ :: cs, hrest =>
      rw [List.length_cons, List.length_cons, List.replicate_succ, List.replicate_succ,
        List.cons_append, List.cons_append, rootPrefix, List.cons_append, List.cons_append] at hrest
      cases (List.cons.inj hrest).2

/-- The recognizer accepts exactly the spellings of bundles. -/
theorem recognize_iff (w : List Bool) :
    recognize w = true ↔ ∃ b : Bundle, coded.spell b.1.1 = w := by
  rw [recognize, Bool.and_eq_true, decide_eq_true_eq, coded.recognize_iff]
  constructor
  · rintro ⟨⟨t, hv, rfl⟩, hp⟩
    refine ⟨⟨⟨t, hv⟩, ?_⟩, rfl⟩
    change sig.q (PFunctor.W.head t) = none
    rw [head_none_of_prefix t hp]
    rfl
  · rintro ⟨b, rfl⟩
    refine ⟨⟨b.1.1, b.1.2, rfl⟩, ?_⟩
    rw [bundle_eq b]
    exact (congrArg (fun z ↦ rootPrefix <+: z) (spell_mk_none fun _ ↦ child b.1.1)).mpr
      (List.prefix_append _ _)

/-- The recognizer accepts exactly the words coding the streams of
expressions. -/
theorem recognize_iff_spellExpr (w : List Bool) :
    recognize w = true ↔ ∃ e : Expr 1 0, spellExpr e = w := by
  rw [recognize_iff]
  exact ⟨fun ⟨b, hb⟩ ↦ ⟨unwrap b,
      (congrArg (fun z : Bundle ↦ coded.spell z.1.1) (bundleEquiv.left_inv b)).trans hb⟩,
    fun ⟨e, he⟩ ↦ ⟨wrap e, he⟩⟩

/-- The expression's value: {lit}`[true]` when the recognizer accepts, the
empty word otherwise. -/
theorem recognizerSem_eq (w : List Bool) : recognizer.sem ![w] = boolWord (recognize w) := by
  rw [recognizer, sem_andF _ _ _ _ _ (sem_startsWithExpr ![w] rootPrefix (projL 1 0))
    (coded.recognizeExprSem_eq _ _ w (LabelExpr.computesLabel w) (EdgeExpr.computesEdge w)),
    recognize, Bool.and_comm]
  rfl

/-- The expression accepts exactly the words the recognizer accepts. -/
theorem recognizerSem_eq_singleton_iff (w : List Bool) :
    recognizer.sem ![w] = [true] ↔ recognize w = true := by
  rw [recognizerSem_eq]
  cases recognize w <;> decide

/-- The expression a word spells: the tree read from the word, when it is an
admissible tree at the root index, as an expression. -/
@[expose] def decodeExpr (w : List Bool) : Option (Expr 1 0) :=
  (Geb.BitTree.Elias.decode w).bind fun t ↦ (coded.readW t).bind fun raw ↦
    if hv : sig.wValidBool raw = true then
      if hi : sig.wIndex ⟨raw, (sig.wValidBool_eq_true_iff raw).mp hv⟩ = none then
        some (bundleEquiv ⟨⟨raw, (sig.wValidBool_eq_true_iff raw).mp hv⟩, hi⟩)
      else none
    else none

/-- The stream a word codes: the stream of the expression the word spells,
when it spells one. -/
@[expose] def decodeStream (w : List Bool) : Option WConstruction.Stream :=
  (decodeExpr w).map toStream

/-- A coding word decodes to the expression it spells. -/
theorem decodeExpr_spellExpr (e : Expr 1 0) : decodeExpr (spellExpr e) = some e := by
  rw [decodeExpr, spellExpr]
  change (Geb.BitTree.Elias.decode (encode (coded.toTree (wrap e).1.1))).bind _ = _
  have h := coded.readW_toTree (wrap e).1.1
  rw [Geb.BitTree.Elias.decode_encode, Option.bind_some, h]
  change (if hv : sig.wValidBool (wrap e).1.1 = true then
      if hi : sig.wIndex ⟨(wrap e).1.1, (sig.wValidBool_eq_true_iff _).mp hv⟩ = none then
        some (bundleEquiv ⟨⟨(wrap e).1.1, (sig.wValidBool_eq_true_iff _).mp hv⟩, hi⟩)
      else none
    else none) = some e
  rw [dite_eq_left ((sig.wValidBool_eq_true_iff _).mpr (wrap e).1.2),
    dite_eq_left (show sig.wIndex ⟨(wrap e).1.1, (sig.wValidBool_eq_true_iff _).mp
      ((sig.wValidBool_eq_true_iff _).mpr (wrap e).1.2)⟩ = none from (wrap e).2)]
  exact congrArg some (bundleEquiv.right_inv e)

/-- The stream a coding word decodes to is the stream of the expression. -/
theorem decodeStream_spellExpr (e : Expr 1 0) : decodeStream (spellExpr e) = some (toStream e) := by
  rw [decodeStream, decodeExpr_spellExpr]
  rfl

end

end Geb.BitStream.Oitavem
