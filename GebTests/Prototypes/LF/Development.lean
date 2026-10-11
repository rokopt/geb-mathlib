/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.LF.Topos.Development
public import GebTests.Prototypes.LF.Proofs
public meta import Geb.Prototypes.LF.Topos.Development -- shake: keep
public meta import Geb.Prototypes.LF.Topos.Rules -- shake: keep
public meta import GebTests.Prototypes.LF.Proofs -- shake: keep

/-!
# Tests for the signature of a development

A development declares the quotient of a type, in one object parameter, by the relation true,
the theorem that the constant function to the terminal object respects the relation, and the
descent of that function through the quotient, a primitive arrow with the theorem of its
computation at an image. Its signature declares the quotient, the projection and the descent, the
induction on the quotient, and the three theorems of the development, the relation's among them;
the induction on the descent, which does not project onto a coequalizer, is not declared. In it,
the descent is the element of the terminal object at every element of the quotient of the
natural numbers, by induction on the quotient, its premise the computation of the descent at an
image; the proof checks in LF, and its decoding is accepted by the checker. The signature of a
development whose object definition's operation is the product's is not formed, the operations
of its type operations not unique.

## Tags

prototype, logical framework, LF, signature, development, quotient, descent
-/

@[expose] public section

namespace Geb.LF.Topos.Tests

open FreeTopos.Internal (Globals Entry Decl Thm)

/-- The constant function to the terminal object respects the relation true: in one object
parameter, at two variables of it related by truth, the element of the terminal object equals
itself. -/
def respectStar : Thm := ⟨1, [PartialHorn.var 0, PartialHorn.var 0], [truth], truth⟩

/-- The quotient by the relation true, the respect of it by the constant function to the
terminal object, and the descent of that function, the primitive arrow of index {lit}`10`. -/
def descDev : Option (Globals × Array Entry) :=
  FreeTopos.Internal.checkDev quotBase #[]
    [.quotient 1 (PartialHorn.var 0) truth, .language respectStar (RoseTree.node (.hyp 0) []),
      .descent 9 FreeTopos.one FreeTopos.Internal.Term.star 1]

/-- The constants after the development. -/
def descGlobals : Globals := (descDev.map Prod.fst).getD quotBase

/-- The environment after the development. -/
def descEntries : Array Entry := (descDev.map Prod.snd).getD #[]

/-- The table of the development. -/
def descIdx : PrimIdx := devIdx pfIdx descGlobals descEntries

/-- The signature of the development. -/
def descSig : Sig := (devSig pfIdx descGlobals descEntries).getD []

/-- The descent is the element of the terminal object at every element of the quotient of the
natural numbers, by induction on the quotient: the motive that the descent at an element is that
element of the terminal object, proved at the projection's image of a variable by the computation
of the descent there. -/
def descStar : Expr :=
  Expr.const 60 [nat, Expr.lam (eq one (Expr.const 59 [nat, v 0]) star),
    Expr.lam (Expr.const 63 [nat, v 0]), v 0]

-- The development checks, and its table names the quotient, the projection, the descent, the
-- induction on the quotient and the three theorems.
#guard descDev.isSome
#guard descIdx.ext == [.obj FreeTopos.sig.length 1, .tm (.arr 9) 1 1, .tm (.arr 10) 1 1,
  .quotInd 9 1 FreeTopos.sig.length, .thm 0 1 2, .thm 1 1 2, .thm 2 1 1]
#guard (devSig pfIdx descGlobals descEntries).isSome && descSig.length == sig.length + 7

-- The descent at every element of the quotient, in LF and decoded.
#guard Checks descSig [tm (Expr.const 57 [nat])] descStar
  (pf (eq one (Expr.const 59 [nat, v 0]) star))
#guard match decPf descIdx descStar [none] 0, dec descIdx (eq one (Expr.const 59 [nat, v 0]) star) 1
    with
  | some D, some φ => Thm.checks descGlobals descEntries ⟨0, [quotNat], [], φ⟩ D
  | _, _ => false

/-- The development of reflexivity at the natural numbers, a theorem of the language. -/
def reflDev : Option (Globals × Array Entry) :=
  FreeTopos.Internal.checkDev pfGlobals #[]
    [.language ⟨0, [FreeTopos.nat], [], FreeTopos.Internal.Term.eq (FreeTopos.Internal.Term.var 0)
      (FreeTopos.Internal.Term.var 0)⟩
      (RoseTree.node .join [RoseTree.node .refl [], RoseTree.node .refl []])]

/-- The constants after the development of reflexivity. -/
def reflGlobals : Globals := (reflDev.map Prod.fst).getD pfGlobals

/-- The environment after the development of reflexivity. -/
def reflEntries : Array Entry := (reflDev.map Prod.snd).getD #[]

/-- Reflexivity applied at the first component of the pair of two variables, a proof that the
first variable equals itself modulo the computation rules of pairs. -/
def reflFst : Expr := Expr.const sig.length [fst nat nat (pair nat nat (v 1) (v 0))]

-- Reflexivity applied at an instance normal only after the computation rules: the proof checks
-- in LF modulo the rules, and its decoding, the theorem's instance converted to the formula it
-- proves, is accepted by the conversion checker.
#guard reflDev.isSome && (devIdx pfIdx reflGlobals reflEntries).ext == [.thm 0 0 1]
#guard match devSig pfIdx reflGlobals reflEntries with
  | some S => ChecksMod rules 64 S [tm nat, tm nat] reflFst (pf (eq nat (v 1) (v 1)))
  | none => false
#guard match decPfMod (devIdx pfIdx reflGlobals reflEntries) reflEntries reflFst [none, none] 0,
    dec (devIdx pfIdx reflGlobals reflEntries) (eq nat (v 1) (v 1)) 2 with
  | some D, some φ => Thm.convChecks reflGlobals reflEntries ⟨0, [FreeTopos.nat, FreeTopos.nat],
      [], φ⟩ D
  | _, _ => false

-- An object definition whose operation is the product's: the signature is not formed.
#guard (devSig pfIdx { pfGlobals with defs := [.object 2 (PartialHorn.var 0)], base := 6 }
  #[]).isNone

end Geb.LF.Topos.Tests

end
