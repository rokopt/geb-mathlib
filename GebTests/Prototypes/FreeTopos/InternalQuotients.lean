/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.InternalLogic -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.InternalLogic -- shake: keep

set_option doc.verso true in
/-!
# Quotient types in the internal language

The quotient of the pairs of natural numbers by the relation of equal sums, declared in a
development: the coequalizer of the relation's projections, the projection to it, and the theorem
that related pairs have equal images, which the development applies to a pair and the pair whose
second component has zero added. The sum and the sum with zero added respect the relation, each
by a theorem of the language, and descend to the quotient; their descents agree on every element
of the quotient, by induction on the quotient, after their computations at an image and the
computation of addition at zero. The development checks; a descent citing a theorem that is not
its function's respect of the relation does not, nor an induction on the codomain of a primitive
arrow that is not a quotient's projection.

## Main definitions

* {lit}`sameSum` — the relation of equal sums.
* {lit}`development` — the development.

## Tags

internal language, quotient, coequalizer, descent, induction, development
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.InternalQuotients

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Sorts
open GebTests.Prototypes.FreeTopos.Internal
open Geb.FreeTopos.Internal (Term Thm Entry Decl Globals checkDev checkThms)
open Geb.FreeTopos.Internal.Logic (nd)

/-- The pairs of natural numbers. -/
def P : Tree := prod nat nat

/-- The sum of the components of the pair that is the variable of an index. -/
def sumT (i : ℕ) : Term := addT (Term.fst (Term.var i)) (Term.snd (Term.var i))

/-- The sum of the components of the pair that is the variable of an index, with zero added. -/
def sum0T (i : ℕ) : Term := addT (sumT i) zeroT

/-- The relation of equal sums, between the pairs that are the innermost two variables. -/
def sameSum : Term := Term.eq (sumT 1) (sumT 0)

/-- The quotient, the object definition after appending and addition. -/
def Q : Tree := op (sig.length + 2) []

/-- The projection to the quotient, the primitive arrow after those of lists and numbers. -/
def qT (t : Term) : Term := Term.arr 4 [] t

/-- The descent of the sum. -/
def descT (t : Term) : Term := Term.arr 5 [] t

/-- The descent of the sum with zero added. -/
def desc0T (t : Term) : Term := Term.arr 6 [] t

/-- The sum respects the relation: the relation itself. -/
def respectSum : Thm := ⟨0, [P, P], [sameSum], sameSum⟩

/-- The sum with zero added respects the relation. -/
def respectSum0 : Thm := ⟨0, [P, P], [sameSum], Term.eq (sum0T 1) (sum0T 0)⟩

/-- The descents agree on every element of the quotient. -/
def descAgree : Thm := ⟨0, [Q], [], Term.eq (desc0T (Term.var 0)) (descT (Term.var 0))⟩

/-- A pair and the pair whose second component has zero added have one image in the
quotient. -/
def addZeroImage : Thm :=
  ⟨0, [nat, nat], [], Term.eq (qT (Term.pair (Term.var 1) (addT (Term.var 0) zeroT)))
    (qT (Term.pair (Term.var 1) (Term.var 0)))⟩

/-- The equations the normalizer applies. -/
def eqns : List Internal.NormRule := [.rule .beta, .rule .fstPair, .rule .sndPair,
  .rule (.natZero 2), .rule (.natSucc 3), .delta 1]

/-- The development: the quotient, the respect of the relation by the sum, its descent, the
respect by the sum with zero added, its descent, the agreement of the descents by induction on
the quotient, and the image of a pair with zero added. -/
def development : Option (List Decl) := do
  let ds₁ : List Decl := [Decl.quotient 0 P sameSum,
    Decl.language respectSum (nd (.hyp 0)), Decl.descent 4 nat (sumT 0) 1]
  let (G₁, E₁) ← checkDev G #[] ds₁
  let d₁ ← Internal.byNorm G₁ E₁ 0 [.hyp 0] 16 [P, P] [sameSum] (sum0T 1) (sum0T 0)
  let ds₂ := ds₁ ++ [Decl.language respectSum0 d₁, Decl.descent 4 nat (sum0T 0) 3]
  let (G₂, E₂) ← checkDev G #[] ds₂
  -- at an image, the two descents compute to the sum with zero added and the sum
  let d₂ ← Internal.byNorm G₂ E₂ 0 (eqns ++ [.thm 4 [], .thm 2 []]) 64 [P] []
    (desc0T (qT (Term.var 0))) (descT (qT (Term.var 0)))
  -- the pair with zero added has the pair's sum
  let d₃ ← Internal.byNorm G₂ E₂ 0 eqns 64 [nat, nat] []
    (addT (Term.fst (Term.pair (Term.var 1) (addT (Term.var 0) zeroT)))
      (Term.snd (Term.pair (Term.var 1) (addT (Term.var 0) zeroT))))
    (addT (Term.fst (Term.pair (Term.var 1) (Term.var 0)))
      (Term.snd (Term.pair (Term.var 1) (Term.var 0))))
  pure (ds₂ ++ [Decl.language descAgree (nd (.quotInd 4 []) [d₂]),
    Decl.language addZeroImage (nd (.apply 0 []
      [Term.pair (Term.var 1) (Term.var 0), Term.pair (Term.var 1) (addT (Term.var 0) zeroT)])
      [d₃])])

-- the development checks
#guard development.any fun ds ↦ checkThms G ds #[]

-- a descent citing the relation's theorem, not its function's respect of it, does not check
#guard development.any fun ds ↦ !checkThms G (ds.take 2 ++ [Decl.descent 4 nat (sumT 0) 0]) #[]

-- an induction on the codomain of the successor, not a quotient's projection, does not check
#guard development.any fun ds ↦ !checkThms G (ds.take 5 ++
  [Decl.language ⟨0, [nat], [], Term.eq (Term.var 0) (Term.var 0)⟩
    (nd (.quotInd 3 []) [nd .join [nd .refl, nd .refl]])]) #[]

end GebTests.Prototypes.FreeTopos.InternalQuotients

end
