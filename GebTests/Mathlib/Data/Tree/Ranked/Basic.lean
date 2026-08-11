/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.Tree.Ranked.Basic
public import Mathlib.Data.Fin.VecNotation

/-!
# A worked ranked alphabet

The alphabet the assertions of this directory's mirrors are stated at: four
symbols of arities zero to three, spelled by two bits each, so that a block
carries more than one bit and the arities are not all equal, and its largest
arity is neither zero nor the alphabet's own size. Two of its terms and an
enumeration of short words are declared here and used by the other mirrors.

## Main definitions

* `sampleAlphabet` — the alphabet.
* `narrowAlphabet` — an alphabet with a block spelling no symbol.
* `sampleNullary`, `sampleBinary` — the two terms.
* `wordsUpTo` — the words over `Bool` of at most a given length.

## Main statements

The assertions below give the node counts of the two terms, the largest
arity of each alphabet, and the length of the enumeration the other mirrors
sweep.

## Tags

ranked alphabet, term algebra, arity
-/

@[expose] public section

open RankedAlphabet

/-- Four symbols of arities zero to three, two bits to a block. Its `card` is
`2 ^ width`, so every block spells a symbol. -/
def sampleAlphabet : RankedAlphabet := ⟨4, 2, by decide, by decide, ![0, 1, 2, 3]⟩

/-- Three symbols of arities zero to two, two bits to a block. Its `card` is
below `2 ^ width`, so the block `[true, true]` spells no symbol and the
rejection `arOf` returns `none` for is reachable from a word. -/
def narrowAlphabet : RankedAlphabet := ⟨3, 2, by decide, by decide, ![0, 1, 2]⟩

/-- The nullary symbol. A symbol index is named rather than written at each
use site: an index whose bound proof is an unassigned metavariable blocks
`arity` from reducing, and the child family then does not elaborate. -/
def sampleSym0 : Fin sampleAlphabet.card := ⟨0, by decide⟩

/-- The binary symbol. -/
def sampleSym2 : Fin sampleAlphabet.card := ⟨2, by decide⟩

/-- The term with the nullary head symbol. -/
def sampleNullary : sampleAlphabet.Term :=
  Term.mk sampleAlphabet sampleSym0 fun d ↦
    absurd (show d.val < 0 from d.isLt) (by omega)

/-- The term with the binary head symbol and two nullary children. -/
def sampleBinary : sampleAlphabet.Term :=
  Term.mk sampleAlphabet sampleSym2 fun _ ↦ sampleNullary

/-- The words over `Bool` of at most the given length, each once. -/
def wordsUpTo : ℕ → List (List Bool) :=
  Nat.rec [[]] fun _ ih ↦ [] :: ih.flatMap fun w ↦ [false :: w, true :: w]

/-- A nullary term is one node. -/
theorem size_sampleNullary : sampleNullary.size = 1 := rfl

/-- A binary term over two nullary children is three. -/
theorem size_sampleBinary : sampleBinary.size = 3 := rfl

/-- The enumeration the `Preorder` mirror sweeps holds every word of length
at most six. -/
theorem length_wordsUpTo_six : (wordsUpTo 6).length = 127 := by
  set_option maxRecDepth 100000 in decide

/-- The enumeration the `Binary` mirror sweeps holds every word of length at
most eight. -/
theorem length_wordsUpTo_eight : (wordsUpTo 8).length = 511 := by
  set_option maxRecDepth 100000 in decide

/-- The largest arity at an alphabet whose arities run up to three. -/
theorem maxArity_sampleAlphabet : sampleAlphabet.maxArity = 3 := by decide

/-- And at the narrow alphabet, whose arities stop at two. -/
theorem maxArity_narrowAlphabet : narrowAlphabet.maxArity = 2 := by decide

end
