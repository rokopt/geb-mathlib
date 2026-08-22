/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.CobhamFoldProto

/-!
# The fold over recognized terms, on samples

`Geb.CobhamFold.foldOut` at the two-symbol alphabet and a four-element carrier,
checked by kernel evaluation against the fold of the term the word spells and
against absence at a word spelling none.

The algebra counts a term's nodes modulo four, which distinguishes the fold
from the recognizer it generalizes: the value depends on the term, not only on
its validity.

## Main definitions

* `sizeMod4` — the algebra counting nodes modulo four.
* `sampleTerm`, `sampleWord`, `sampleFold` — a term, its spelling, and the fold
  of that spelling.
* `rejectWord`, `rejectFold` — a word spelling no term, and the fold's value on
  it.
* `unitSampleFold`, `unitRejectFold` — the same two words under the terminal
  algebra.
* `unitExpr`, `parityExpr` — the fixed-width construction at the terminal
  algebra and at the two-valued parity algebra, with `encBool`, `decBool` and
  `parityAlg` the second's ingredients and `parityFold` the semantic sample at
  the same algebra.
* `leftHeavy`, `rightHeavy`, `leftHeavyFold` — an algebra distinguishing the
  order in which the scan presents a symbol's children, its transpose, and the
  fold at the first.
* `leafCountAlg`, `leafCountOf`, `leafCountExpr` — the bitstring construction at
  an algebra counting a term's leaves in unary, with its operations as
  expressions of Cobham's class.

## Main statements

* `spell_sampleTerm` — the sample word is the sample term's spelling.
* `sampleFold_eq` — the fold of the sample word is the sample term's node count
  modulo four.
* `sampleFold_eq_termFold` — and it is the term algebra's fold at the same
  algebra.
* `rejectFold_eq` — a word spelling no term folds to nothing.
* `leftHeavy_ne_rightHeavy`, `leftHeavyFold_eq_termFold`,
  `leftHeavyFold_ne_rightHeavy` — the scan presents a symbol's children to the
  algebra in index order, checked against an algebra that distinguishes the two
  orders.
* `unitSampleFold_eq`, `unitRejectFold_eq` — at the terminal algebra the fold is
  the recognizer's verdict.
* `smashFree_unitExpr`, `smashFree_parityExpr` — the expressions at the terminal
  algebra and at the two-valued parity algebra lie in the subalgebra
  `Cobham.SmashFree` names, the first by kernel evaluation and the second by
  `Geb.CobhamFold.smashFree_foldOutExpr`.
* `decBool_encBool`, `parityFold_eq`, `two_le_two_mul_width` — the one-bit
  encoding's retraction, the parity fold's value, and the multiplier the
  fixed-width construction takes at that carrier.
* `semAt_leafCountOf`, `growth_leafCountAlg`, `smashFreeBool_leafCountOf` — the
  bitstring construction's hypotheses at the leaf-counting algebra. The
  remaining two it takes are discharged inline: the linear-growth hypothesis by
  `Geb.CobhamFold.stackSize_le_of_growth` applied to `growth_leafCountAlg`, and
  the constraint on the multiplier by `decide`.
* `leafCountFold_eq` — the sample term has three leaves.
* `smashFree_leafCountExpr` — that instance lies in `Cobham.SmashFree`, by
  `Geb.CobhamFold.smashFree_foldOutExprV`.

## Implementation notes

`sampleWord` is the literal bitstring, with `spell_sampleTerm` relating it to
the spelling, rather than `RankedAlphabet.spell` applied to the term.

`sizeMod4` folds `List.ofFn` of its argument rather than matching on the
symbol's arity, so no branch needs `binRanked.arity` to reduce to a numeral at
elaboration.

`sizeMod4` is symmetric in a symbol's children, so it cannot witness the order
in which the scan presents them, which
`Geb.CobhamFold.foldScanFrom_code` fixes symbolically. `leftHeavy` and its
transpose `rightHeavy` cross-check it, `leftHeavy_ne_rightHeavy` establishing that the two differ
on the sample term and so that the check is not vacuous.

The samples exercise `Geb.CobhamFold.foldOut`, which is the fold scan's
semantics. `Geb.CobhamFold.foldOutSem_eq` identifies the expression of Cobham's
class with it symbolically, so no sample forces the expression's
`Cobham.casesOf` tree, which has `2 ^ Geb.CobhamFold.dispatchWidthF` branches.

`smashFree_unitExpr` does force that tree, at dispatch width five, and
cross-checks `Geb.CobhamFold.smashFree_foldOutExpr` against kernel evaluation.
The tree's normal form grows by about a factor of three per bit of dispatch
width — 21318 nodes at `unitExpr`, 547695 at `parityExpr` — so what the
carrier's width ends is normalization, not construction: the term elaborates at every
width, `Cobham.casesOf` taking its branch family as a function, while a `decide`
succeeds outright at width five, needs a raised `maxRecDepth` at width eight,
and exceeds the heartbeat limit at width eleven whatever the depth.
`smashFree_parityExpr` therefore applies the symbolic theorem at width eight
rather than raising a limit. `smashFree_leafCountExpr` applies
`Geb.CobhamFold.smashFree_foldOutExprV` for the same reason, its dispatch being
`Cobham.dispatchWidth` wide whatever the carrier but its algebra's own
expressions adding depth of their own.

## References

* [Strahm2003]

## Tags

Cobham, ranked alphabet, fold, catamorphism, test
-/

@[expose] public section

namespace GebTests.CobhamFold

open Geb.CobhamFold RankedAlphabet RankedAlphabet.Binary

/-- The algebra counting a term's nodes modulo four: one for the symbol itself,
plus its children's counts. -/
def sizeMod4 (i : Fin binRanked.card) (ch : Fin (binRanked.arity i) → Fin 4) :
    Fin 4 :=
  (List.ofFn ch).foldr (· + ·) 1

/-- A term of five nodes. -/
def sampleTerm : binRanked.Term := node (node leaf leaf) leaf

/-- That term's preorder spelling, as a literal. -/
def sampleWord : List Bool := [true, true, false, false, false]

/-- The literal is the sample term's spelling. -/
theorem spell_sampleTerm : binRanked.spell sampleTerm = sampleWord := by
  rw [sampleTerm, spell_node, spell_node, spell_leaf]
  rfl

/-- The fold of the sample word. -/
def sampleFold : Option (Fin 4) := foldOut binRanked sizeMod4 sampleWord

/-- Five nodes modulo four is one. -/
theorem sampleFold_eq : sampleFold = some 1 := by decide

/-- The fold of the spelling is the term algebra's fold of the term. -/
theorem sampleFold_eq_termFold :
    sampleFold = some (Term.fold binRanked sizeMod4 sampleTerm) := by decide

/-- A word spelling no term: a node symbol with nothing to its right. -/
def rejectWord : List Bool := [true]

/-- The fold of that word. -/
def rejectFold : Option (Fin 4) := foldOut binRanked sizeMod4 rejectWord

/-- A word spelling no term folds to nothing. -/
theorem rejectFold_eq : rejectFold = none := by decide

/-- An algebra sensitive to the order of a symbol's children: a leaf is one, and
a node is its first child plus twice its second. Matching on `List.ofFn` of the
argument rather than indexing it keeps `binRanked.arity` out of the numerals. -/
def leftHeavy (i : Fin binRanked.card) (ch : Fin (binRanked.arity i) → Fin 4) :
    Fin 4 :=
  match List.ofFn ch with
  | [] => 1
  | [a] => a
  | a :: b :: _ => a + 2 * b

/-- The same algebra with its two children exchanged. -/
def rightHeavy (i : Fin binRanked.card) (ch : Fin (binRanked.arity i) → Fin 4) :
    Fin 4 :=
  match List.ofFn ch with
  | [] => 1
  | [a] => a
  | a :: b :: _ => b + 2 * a

/-- The fold of the sample word at the order-sensitive algebra. -/
def leftHeavyFold : Option (Fin 4) := foldOut binRanked leftHeavy sampleWord

/-- The two algebras disagree on the sample term, so the checks below would fail
were the scan to present a symbol's children to the algebra transposed. -/
theorem leftHeavy_ne_rightHeavy :
    Term.fold binRanked leftHeavy sampleTerm ≠
      Term.fold binRanked rightHeavy sampleTerm := by decide

/-- The scan presents a symbol's children to the algebra in index order: the
stack's head is child zero. -/
theorem leftHeavyFold_eq_termFold :
    leftHeavyFold = some (Term.fold binRanked leftHeavy sampleTerm) := by decide

/-- And it is not the transposed value. -/
theorem leftHeavyFold_ne_rightHeavy :
    leftHeavyFold ≠ some (Term.fold binRanked rightHeavy sampleTerm) := by decide

/-- The sample word under the terminal algebra. -/
def unitSampleFold : Option Unit := foldOut binRanked (algUnit binRanked) sampleWord

/-- The rejected word under the terminal algebra. -/
def unitRejectFold : Option Unit := foldOut binRanked (algUnit binRanked) rejectWord

/-- At the terminal algebra the fold is present on a spelling. -/
theorem unitSampleFold_eq : unitSampleFold = some () := by decide

/-- At the terminal algebra the fold is absent on a word spelling no term. -/
theorem unitRejectFold_eq : unitRejectFold = none := by decide

/-- The fold expression at the terminal algebra and the two-symbol alphabet. -/
def unitExpr : Cobham.C :=
  foldOutExpr binRanked 0 encUnit decUnit decUnit_encUnit (algUnit binRanked) 1
    (one_le_one_mul_width binRanked)

/-- That expression carries no `smash` node, so it lies in the subalgebra
`Cobham.SmashFree` names, which [Strahm2003] Theorem 1(2) contains in the
functions computable simultaneously in polynomial time and linear space. This is
the kernel's verdict at one instance, which
`Geb.CobhamFold.smashFree_foldOutExpr` reaches symbolically at every alphabet
and carrier width. -/
theorem smashFree_unitExpr : Cobham.SmashFree unitExpr := by decide

/-- A one-bit encoding of the carrier `Bool`. -/
def encBool : Bool → Fin 1 → Bool := fun b _ ↦ b

/-- The inverse of that encoding. -/
def decBool : (Fin 1 → Bool) → Bool := fun v ↦ v 0

/-- The encoding's retraction. -/
theorem decBool_encBool : ∀ b : Bool, decBool (encBool b) = b := fun _ ↦ rfl

/-- The algebra giving a term's node count modulo two: a symbol contributes
itself, and its children contribute their own counts. -/
def parityAlg (i : Fin binRanked.card)
    (ch : Fin (binRanked.arity i) → Bool) : Bool :=
  (List.ofFn ch).foldr xor true

/-- The multiplier two meets the bound at the two-symbol alphabet and a one-bit
carrier. -/
theorem two_le_two_mul_width : 1 + 1 ≤ 2 * binRanked.width := by decide

/-- The fold of the sample word at the parity algebra. -/
def parityFold : Option Bool := foldOut binRanked parityAlg sampleWord

/-- Five nodes is an odd number. -/
theorem parityFold_eq : parityFold = some true := by decide

/-- The fold expression at the parity algebra, whose carrier has two values and
so is not the recognizer's. -/
def parityExpr : Cobham.C :=
  foldOutExpr binRanked 1 encBool decBool decBool_encBool parityAlg 2
    two_le_two_mul_width

/-- The parity fold's expression carries no `smash` node either, so it lies in
the subalgebra [Strahm2003] Theorem 1(2) contains in the functions computable
simultaneously in polynomial time and linear space. The carrier has two values,
so this is the statement at a carrier the recognizer does not cover. -/
theorem smashFree_parityExpr : Cobham.SmashFree parityExpr :=
  smashFree_foldOutExpr binRanked encBool decBool decBool_encBool parityAlg 2
    two_le_two_mul_width

/-- The algebra counting a term's leaves in unary: a leaf contributes one
`true`, a node the concatenation of its children's counts. Non-constant, and
lengthening by at most one bit per symbol, so the growth bridge applies at
`c = 1`. -/
def leafCountAlg :
    (i : Fin binRanked.card) → (Fin (binRanked.arity i) → List Bool) → List Bool
  | ⟨0, _⟩, _ => [true]
  | ⟨1, _⟩, f => (List.ofFn f).flatten

/-- That algebra's operations as expressions of Cobham's class: a constant word
at a leaf, and the concatenation of the two arguments at a node. The node's
expression concatenates onto `Cobham.zeroAtOf 2` rather than onto the second
argument directly, so that its value is `f 0 ++ (f 1 ++ [])`, which is
`(List.ofFn f).flatten` definitionally and lets `semAt_leafCountOf`'s node case
be `rfl`. -/
def leafCountOf : (i : Fin binRanked.card) → Cobham.COf (binRanked.arity i)
  | ⟨0, _⟩ => Cobham.constAtOf 0 [true]
  | ⟨1, _⟩ =>
    concatCompOf 2 (concatCompOf 2 (Cobham.zeroAtOf 2) (projOf 2 1)) (projOf 2 0)

/-- The sample term has three leaves. -/
theorem leafCountFold_eq :
    foldOut binRanked leafCountAlg sampleWord = some [true, true, true] := by
  decide

/-- The expressions compute the algebra. -/
theorem semAt_leafCountOf : ∀ (i : Fin binRanked.card)
    (f : Fin (binRanked.arity i) → List Bool),
    Cobham.semAt (binRanked.arity i) (leafCountOf i).1.1 (leafCountOf i).2 f =
      leafCountAlg i f
  | ⟨0, _⟩, f => semAt_constAtOf 0 [true] f
  | ⟨1, _⟩, _f => rfl

/-- The algebra lengthens by at most one bit per symbol. -/
theorem growth_leafCountAlg : ∀ (i : Fin binRanked.card)
    (f : Fin (binRanked.arity i) → List Bool),
    (leafCountAlg i f).length ≤ (List.ofFn fun d ↦ (f d).length).sum + 1
  | ⟨0, _⟩, _f => Nat.succ_le_succ (Nat.zero_le _)
  | ⟨1, _⟩, f => by
    change ((List.ofFn f).flatten).length ≤
      (List.ofFn fun d ↦ (f d).length).sum + 1
    rw [List.length_flatten, List.map_ofFn]
    exact Nat.le_succ _

/-- The expressions carry no `smash`. -/
theorem smashFreeBool_leafCountOf : ∀ i : Fin binRanked.card,
    Cobham.smashFreeBool (leafCountOf i).1.1.1 = true
  | ⟨0, _⟩ => smashFreeBool_constAtOf 0 _
  | ⟨1, _⟩ =>
    smashFreeBool_concatCompOf 2 _ _
      (smashFreeBool_concatCompOf 2 _ _ (smashFreeBool_zeroAtOf 2)
        (smashFreeBool_projOf 2 1))
      (smashFreeBool_projOf 2 0)

/-- The fold at a bitstring carrier, witnessed: an instance of
`Geb.CobhamFold.foldOutExprV` at an algebra that is not constant, whose growth
hypothesis is discharged by `Geb.CobhamFold.stackSize_le_of_growth` from the
per-symbol condition alone. -/
def leafCountExpr : Cobham.C :=
  foldOutExprV binRanked leafCountOf leafCountAlg semAt_leafCountOf 4 1
    (stackSize_le_of_growth binRanked leafCountAlg 1 growth_leafCountAlg)
    (by decide)

/-- That instance lies in the subalgebra `Cobham.SmashFree` names, so with
[Strahm2003] Theorem 1(2)'s left-to-right inclusion it is computable
simultaneously in polynomial time and linear space. -/
theorem smashFree_leafCountExpr : Cobham.SmashFree leafCountExpr :=
  smashFree_foldOutExprV binRanked leafCountOf smashFreeBool_leafCountOf
    leafCountAlg semAt_leafCountOf 4 1
    (stackSize_le_of_growth binRanked leafCountAlg 1 growth_leafCountAlg)
    (by decide)

end GebTests.CobhamFold

end
