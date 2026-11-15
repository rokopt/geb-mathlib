/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Compile
public meta import Geb.Prototypes.FreeTopos.Internal.Holes.Sequent -- shake: keep

set_option doc.verso true in
/-!
# Weakening embedded sequent certificates

Certificates are restricted to the subobject on which additional hypotheses hold. The
generated certificates are checked in the original theorem environment.

## Main definitions

* {lit}`G` — constants with no declared definitions or primitive arrows.

## Tags

internal language, proof certificate, weakening, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.InternalHolesSequent

open Geb Geb.FreeTopos Geb.FreeTopos.Internal

/-- Constants with no declared definitions or primitive arrows. -/
def G : Globals := ⟨[], [], sig.length⟩

#guard
  let a : Thm := ⟨0, [nat], [], Term.eq (Term.var 0) (Term.var 0)⟩
  let E := #[Entry.language a]
  let c := PartialHorn.Cert.cut (PartialHorn.Cert.thm 0 [] [] []) (PartialHorn.Cert.hyp 0)
  (ProofHoles.Sequent.weaken G E a [a.concl] c).any fun p ↦
    certifies G E p ({ a with hyps := [a.concl] }.seq G)

#guard
  let φ := Term.eq (Term.var 0) (Term.var 1)
  let t := Term.eq Term.star Term.star
  let a : Thm := ⟨0, [nat, nat], [φ], φ⟩
  let E := #[Entry.language a]
  let c := PartialHorn.Cert.thm 0 [] [] []
  (ProofHoles.Sequent.weaken G E a [t, φ, t] c).any fun p ↦
    certifies G E p ({ a with hyps := [t, φ, t] }.seq G)

-- Object arguments of theorem instances remain terms when cut citations are reindexed.
#guard
  let a : Thm := ⟨1, [x 0], [], Term.eq (Term.var 0) (Term.var 0)⟩
  let E := #[Entry.language a]
  let s := a.seq G
  let c := (⟨s.ctx, s.hyps⟩ : PartialHorn.Scope).cite 0
  (ProofHoles.Sequent.weaken G E a [a.concl] c).any fun p ↦
    certifies G E p ({ a with hyps := [a.concl] }.seq G)

-- Removing an essential hypothesis cannot supply a factor through its truth subobject.
#guard
  let φ := Term.eq (Term.var 0) (Term.var 1)
  let a : Thm := ⟨0, [nat, nat], [φ], φ⟩
  (ProofHoles.Sequent.weaken G #[Entry.language a] a []
    (PartialHorn.Cert.thm 0 [] [] [])).isNone

end GebTests.Prototypes.FreeTopos.InternalHolesSequent

end
