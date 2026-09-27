/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.InternalCitations -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.InternalCitations -- shake: keep

set_option doc.verso true in
/-!
# The citation of a theorem's sequent

The rule by which the internal language is complete cites a certificate of the sequent a theorem
compiles to, under the theorem's hypotheses. The development of the
citations between the two checkers is extended: the equation of appending the empty list twice is
proved again by the certificate of its sequent; a theorem with a hypothesis, proved by the
hypothesis, is proved again by the certificate that cites its own sequent, which states its
conclusion on the subobject on which its hypothesis is true. The development checks; the latter
certificate does not prove the theorem without the hypothesis.

## Main definitions

* {lit}`appendNilHyp` — the theorem with a hypothesis.
* {lit}`development` — the development.

## Tags

internal language, completeness, certificate, citation, development
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.InternalCompleteness

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Sorts
open GebTests.Prototypes.FreeTopos.Internal
open GebTests.Prototypes.FreeTopos.InternalCitations (appendNil appendNilTwice developmentWith)
open Geb.FreeTopos.Internal (Term Thm Decl checkThms)
open Geb.FreeTopos.Internal.Logic (nd)

/-- Appending the empty list to a list gives the list, under that hypothesis. -/
def appendNilHyp : Thm := ⟨1, [L], [appendNil.concl], appendNil.concl⟩

/-- The development of the citations, extended by the equation of appending the empty list twice
proved by the certificate of its sequent, and the theorem with a hypothesis proved by the
hypothesis and then by the certificate that cites its sequent. The result's last component is
that certificate. -/
def developmentWith : Option (List Decl × Tree) := do
  let (ds, c) ← InternalCitations.developmentWith
  let ds₁ := ds ++ [Decl.language appendNilTwice (nd (.certSeq c)),
    Decl.language appendNilHyp (nd (.hyp 0))]
  let c₁ := Scope.cite ⟨[obj], []⟩ (ds₁.length - 1)
  pure (ds₁ ++ [Decl.language appendNilHyp (nd (.certSeq c₁))], c₁)

/-- The development. -/
def development : Option (List Decl) := developmentWith.map Prod.fst

-- the development checks
#guard development.any fun ds ↦ checkThms G ds #[]

-- the certificate of the theorem's sequent does not prove it without its hypothesis
#guard developmentWith.any fun (ds, c) ↦
  !checkThms G (ds.dropLast ++ [Decl.language appendNil (nd (.certSeq c))]) #[]

end GebTests.Prototypes.FreeTopos.InternalCompleteness

end
