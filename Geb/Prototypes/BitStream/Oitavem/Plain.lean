/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.BitStream.Oitavem.Label
public import Geb.Prototypes.BitStream.Oitavem.Edge
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The recognizer of expressions of Logs at every arity

The signature of Logs as a coded signature, {name}`Geb.BitStream.Oitavem.codedPlain`,
carries the bundle signature's codes without the root, so its admissible
trees are the expressions of Logs at every arity, and the recognizer of the
coded signature's admissible trees accepts exactly their spellings. Its
label check is the bundle signature's after a dispatch on the first tag
bit, which the root alone sets; its edge check is the bundle signature's
unchanged, since the edge condition constrains only labels that decode, and
a root child is rejected there already. The recognizer as an expression of
the logspace subalgebra follows, and so does the machine it compiles to,
in the machine module.

# Main definitions

* {lit}`labelOkPlain`, {lit}`recognizerPlain` — the label check, and the
  recognizer as an expression.

# Main statements

* {lit}`computesLabelPlain`, {lit}`computesEdgePlain` — the label and
  edge checks compute the signature's conditions on every word.
* {lit}`recognizerPlainSem_eq`, {lit}`recognizerPlainSem_eq_singleton_iff`
  — the expression's value is the recognizer's verdict as a word, and it
  accepts exactly the spellings of expressions of Logs.

# References

* {cite}`Oitavem2010`, Definition 3.1.
* {cite}`Kristiansen2005`

# Tags

bitstream, logspace, recognizer, coded signature
-/

set_option doc.verso true

namespace Geb.BitStream.Oitavem

open Geb.SizeBounded.Logspace (LOf tailAppL sem_tailAppL constL sem_constL)
open Geb.SizeBounded.Logspace.WTree (CodedSig boolWord isTrueWord onBitAt sem_onBitAt recognizeExpr
  Loc labelAt)
open Geb.SizeBounded.Logspace.WTree.SigLabel (L4 envL sem_L4 sem_onBitAt_nil)
open Geb.Oitavem (Shape)

public section

/-- A word that decodes to a shape of Logs begins with a set bit and a clear
bit, the label's set bit and the first tag bit. -/
theorem decodePlain_eq_some {w : List Bool} {c : Shape} (h : decodePlain w = some c) :
    ∃ r, w = true :: false :: r := by
  obtain ⟨bs, hbs⟩ := EdgeExpr.tag_kind_some c
  refine ⟨bs ++ codes (List.ofFn (fields (some c))), ?_⟩
  rw [← codePlain_of_decodePlain h, codePlain, LabelExpr.code_eq, hbs]
  rfl

/-- The label condition of the signature of Logs fails at a word that does
not begin with a set bit and a clear bit. -/
theorem labelSpecPlain_eq_false (s : List Bool) (k : ℕ) (h : ∀ r, s ≠ true :: false :: r) :
    codedPlain.labelSpec s k = false := by
  unfold CodedSig.labelSpec
  cases hd : codedPlain.decode s with
  | none => rfl
  | some c =>
    obtain ⟨r, hr⟩ := decodePlain_eq_some hd
    exact absurd hr (h r)

/-- The label condition of the signature of Logs is the bundle signature's at
a word that does not begin with two set bits, the root's. -/
theorem labelSpecPlain_eq (s : List Bool) (k : ℕ) (h : ∀ r, s ≠ true :: true :: r) :
    codedPlain.labelSpec s k = coded.labelSpec s k := by
  unfold CodedSig.labelSpec
  rw [show codedPlain.decode = decodePlain from rfl, show coded.decode = decode from rfl]
  unfold decodePlain
  cases hd : decode s with
  | none => rfl
  | some a =>
    cases a with
    | none => exact absurd (by rw [← code_of_decode hd]; rfl) (h _)
    | some c => rfl

/-- The edge condition of the signature of Logs is the bundle signature's at
words that decode to shapes of Logs. -/
theorem edgeSpecPlain_eq (s s' : List Bool) (j : ℕ) (a c : Shape)
    (hs : decode s = some (some a)) (hs' : decode s' = some (some c)) :
    codedPlain.edgeSpec s j s' = coded.edgeSpec s j s' := by
  have hp : decodePlain s = some a := by rw [decodePlain, hs]
  have hp' : decodePlain s' = some c := by rw [decodePlain, hs']
  unfold CodedSig.edgeSpec
  rw [show codedPlain.decode = decodePlain from rfl, show coded.decode = decode from rfl, hp, hp',
    hs, hs']
  change (if h : j < coded.card (some a) then
      decide (Geb.Oitavem.resultArity c =
        Geb.Oitavem.childArity a (coded.dir (some a) ⟨j, h⟩)) else false) =
    if h : j < coded.card (some a) then
      decide (some (Geb.Oitavem.resultArity c) =
        some (Geb.Oitavem.childArity a (coded.dir (some a) ⟨j, h⟩))) else false
  simp only [Option.some.injEq]

/-- The label check of the signature of Logs: the bundle signature's after
the dispatch on the first tag bit, which rejects the root. -/
@[expose] def labelOkPlain : LOf 4 :=
  onBitAt (tailAppL L4) (constL 4 []) (constL 4 []) LabelExpr.labelOk

/-- A label beginning with two bits is at a word beginning with them. -/
theorem drop_of_labelAt (y : List Bool) (l : Loc) (a b : Bool) (r : List Bool)
    (h : labelAt y l = a :: b :: r) : ∃ r', y.drop l.pos = a :: b :: r' := by
  obtain ⟨t, ht⟩ := List.take_prefix l.len (y.drop l.pos)
  change labelAt y l ++ t = _ at ht
  exact ⟨r ++ t, by rw [← ht, h]; rfl⟩

/-- At a sound label and an arity below the word's length, the label check
reads as the signature's label condition. -/
theorem labelOkPlain_eq (y : List Bool) (l : Loc) (k : ℕ) (hs : Loc.Sound y l)
    (hk : k + 1 ≤ y.length) :
    isTrueWord (labelOkPlain.sem (envL y l k)) = codedPlain.labelSpec (labelAt y l) k := by
  rcases hw : y.drop l.pos with _ | ⟨b, _ | ⟨c, w'⟩⟩
  · rw [labelOkPlain, sem_onBitAt_nil _ _ _ _ _ (by rw [sem_tailAppL, sem_L4, hw]; rfl), sem_constL,
      labelSpecPlain_eq_false _ _ fun r h ↦ ?_]
    · rfl
    · obtain ⟨r', hr'⟩ := drop_of_labelAt y l _ _ r h
      rw [hw] at hr'
      cases hr'
  · rw [labelOkPlain, sem_onBitAt_nil _ _ _ _ _ (by rw [sem_tailAppL, sem_L4, hw]; rfl), sem_constL,
      labelSpecPlain_eq_false _ _ fun r h ↦ ?_]
    · rfl
    · obtain ⟨r', hr'⟩ := drop_of_labelAt y l _ _ r h
      rw [hw] at hr'
      cases (List.cons.inj hr').2
  · cases c
    · rw [labelOkPlain, sem_onBitAt _ _ _ _ _ false w' (by rw [sem_tailAppL, sem_L4, hw]; rfl),
        ite_eq_right (by decide), LabelExpr.labelOk_eq y l k hs hk,
        labelSpecPlain_eq _ _ fun r h ↦ ?_]
      obtain ⟨r', hr'⟩ := drop_of_labelAt y l _ _ r h
      rw [hw] at hr'
      exact Bool.noConfusion (List.cons.inj (List.cons.inj hr').2).1
    · rw [labelOkPlain, sem_onBitAt _ _ _ _ _ true w' (by rw [sem_tailAppL, sem_L4, hw]; rfl),
        ite_eq_left rfl, sem_constL, labelSpecPlain_eq_false _ _ fun r h ↦ ?_]
      · rfl
      · obtain ⟨r', hr'⟩ := drop_of_labelAt y l _ _ r h
        rw [hw] at hr'
        exact Bool.noConfusion (List.cons.inj (List.cons.inj hr').2).1

/-- The label check computes the signature's label condition on every word. -/
theorem computesLabelPlain (y : List Bool) : codedPlain.ComputesLabel labelOkPlain y :=
  fun l k hs hk ↦ labelOkPlain_eq y l k hs hk

/-- The bundle signature's edge check computes the signature's edge condition
on every word. -/
theorem computesEdgePlain (y : List Bool) : codedPlain.ComputesEdge EdgeExpr.edgeOk y := by
  intro l l' j hs hs' hj hd hd'
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hd
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hd'
  have ha' : decode (labelAt y l) = some (some a) := decode_of_decodePlain ha
  have hc' : decode (labelAt y l') = some (some c) := decode_of_decodePlain hc
  rw [edgeSpecPlain_eq _ _ j a c ha' hc']
  exact EdgeExpr.computesEdge y l l' j hs hs' hj (Option.isSome_iff_exists.mpr ⟨_, ha'⟩)
    (Option.isSome_iff_exists.mpr ⟨_, hc'⟩)

/-- The recognizer of the spellings of expressions of Logs at every arity, as
an expression of the subalgebra. -/
@[expose] def recognizerPlain : LOf 1 := recognizeExpr labelOkPlain EdgeExpr.edgeOk

/-- The expression's value: {lit}`[true]` when the recognizer accepts, the
empty word otherwise. -/
theorem recognizerPlainSem_eq (w : List Bool) :
    recognizerPlain.sem ![w] = boolWord (codedPlain.recognize w) :=
  codedPlain.recognizeExprSem_eq _ _ w (computesLabelPlain w) (computesEdgePlain w)

/-- The expression accepts exactly the spellings of expressions of Logs, at
every arity. -/
theorem recognizerPlainSem_eq_singleton_iff (w : List Bool) :
    recognizerPlain.sem ![w] = [true] ↔ ∃ t, Geb.Oitavem.sig.WValid t ∧ codedPlain.spell t = w :=
  codedPlain.recognizeExprSem_eq_singleton_iff_isW _ _ w (computesLabelPlain w)
    (computesEdgePlain w)

end

end Geb.BitStream.Oitavem
