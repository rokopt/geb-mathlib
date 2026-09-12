/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Mazzanti.Words
public import Geb.Prototypes.Computability.BitTree.Encoding
meta import GebMeta -- shake: keep

set_option doc.verso true

/-!
# A growth obstruction for tree-calculus contraction

Under the unshared applicative encoding of the bitstring-metalogic design,
triage rule (2) can increase the size of arbitrarily large inputs. Consequently
any endofunction implementing this root contraction fails the paper's
non-size-increase condition, despite the linear bound on one contraction's output.

## Main definitions

* {lit}`dupInput` and {lit}`dupOutput` instantiate the duplication rule with
  both of its other operands equal to the constant leaf.
* {lit}`stemChain` supplies arbitrarily large expressions using empty leaves only.

## Main statements

* {lit}`not_nonSizeIncreasing_of_duplication` excludes a fixed size cutoff for
  any function implementing these contractions.

## References

* {cite}`TreeCalculusSpecification`, rule (2).

## Tags

tree calculus, bitstring, non-size-increasing function, output size
-/

@[expose] public section

namespace Geb.Mazzanti.Growth

open Geb.BitTree (Tree leaf fork encode)

/-- The constant of applicative tree syntax. -/
def delta : Tree := leaf []

/-- An iterated stem, containing no payload bits. -/
def stemChain : ℕ → Tree := Nat.rec delta (fun _ t ↦ fork delta t)

/-- Every additional stem adds one application bit and a two-bit constant. -/
theorem length_encode_stemChain (n : ℕ) : (encode (stemChain n)).length = 3 * n + 2 :=
  Nat.rec rfl (fun n ih ↦ by
    change (encode (fork delta (stemChain n))).length = _
    simp only [Geb.BitTree.encode_fork, List.length_cons, List.length_append, ih]
    change 2 + (3 * n + 2) + 1 = _
    omega) n

/-- The redex {lit}`D (D D) D z`, with application represented by binary fork. -/
def dupInput (z : Tree) : Tree := fork (fork (fork delta (fork delta delta)) delta) z

/-- Its rule-(2) reduct {lit}`D z (D z)`. -/
def dupOutput (z : Tree) : Tree := fork (fork delta z) (fork delta z)

/-- The input contains one copy of the variable subtree. -/
theorem length_encode_dupInput (z : Tree) :
    (encode (dupInput z)).length = 12 + (encode z).length := by
  simp [dupInput, delta]
  omega

/-- The output contains two copies of the variable subtree. -/
theorem length_encode_dupOutput (z : Tree) :
    (encode (dupOutput z)).length = 7 + 2 * (encode z).length := by
  simp [dupOutput, delta]
  omega

/-- No constant cutoff accommodates all these root contractions. This concerns
materialized unshared syntax, not a Boolean check of a proposed contraction. -/
theorem not_nonSizeIncreasing_of_duplication (f : List Bool → List Bool)
    (hf : ∀ n, f (encode (dupInput (stemChain n))) = encode (dupOutput (stemChain n))) :
    ¬ WordNonSizeIncreasing f := by
  rintro ⟨k, hk⟩
  have h := hk (encode (dupInput (stemChain (k + 2))))
  rw [hf, length_encode_dupInput, length_encode_dupOutput, length_encode_stemChain] at h
  omega

end Geb.Mazzanti.Growth
