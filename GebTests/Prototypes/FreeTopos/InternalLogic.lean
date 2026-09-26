/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.InternalDerivation -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.InternalDerivation -- shake: keep

set_option doc.verso true in
/-!
# Logic in the internal language

The connectives' definitions ({name}`Geb.FreeTopos.Internal.Logic.defs`) placed after appending
and addition, and their introduction and elimination rules
({name}`Geb.FreeTopos.Internal.Logic.theorems`) checked, with the introduction of an implication
and of a universal quantification by the functions of derivations that make them. The theorems
of addition and appending proved by induction with the step of their recursions are proved again
by induction with the induction hypothesis.

## Main definitions

* {lit}`GL` — the constants, the connectives' definitions among them.
* {lit}`theorems` — the rules, the introductions and the inductions, each with its proof.
* {lit}`development` — the development of their derivations.

## Tags

internal language, local set theory, derivation, induction
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.InternalLogic

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Sorts
open GebTests.Prototypes.FreeTopos.Internal
open Geb.FreeTopos.Internal (Term Thm Deriv Rule byNatIndHyp byListIndHyp checkThms compileDefs)
open Geb.FreeTopos.Internal.Logic (nd tt imp all impI allI)

/-- The constants: the primitive arrows, and appending, addition and the connectives. -/
def GL : Internal.Globals := ⟨prims, defs ++ Internal.Logic.defs 2, sig.length⟩

-- the definitions compile, each to a well-formed definition of the combinators over the
-- signature the earlier ones extend, and the constants are well formed
#guard (compileDefs GL).any fun cs ↦
  cs.zipIdx.all (fun (d, i) ↦
    sortOf (sig ++ (cs.take i).map fun d ↦ (d.ctx, d.sort)) d.ctx d.body == some d.sort &&
      (List.range d.ctx.length).all fun j ↦ Occurs j d.body) &&
    GL.ok (ExtEnv.ofDefs cs)

/-- The theorems, each with its proof from the theorems before it: the connectives' rules, a
formula's implication of itself, the reflexivity of equality under a universal quantifier, and
the two inductions. -/
def theorems : List (Thm × (Array Thm → Option Deriv)) :=
  (Internal.Logic.theorems 2 0).map (fun (a, d) ↦ (a, fun _ ↦ some d)) ++ [
  (⟨0, [omega], [], imp 2 (Term.var 0) (Term.var 0)⟩,
    fun _ ↦ some (impI 0 0 (Term.var 0) (Term.var 0) (nd (.hyp 0)))),
  (⟨1, [], [], all 2 (x 0) (Term.lam (x 0) (Term.eq (Term.var 0) (Term.var 0)))⟩,
    fun _ ↦ some (allI (nd .join [nd .refl, nd .refl]))),
  (⟨0, [nat], [], Term.eq (addT zeroT (Term.var 0)) (Term.var 0)⟩,
    fun E ↦ byNatIndHyp GL E 0 2 3 (InternalDerivation.eqns ++ [.delta 1]) 64 [nat] []
      (addT zeroT (Term.var 0)) (Term.var 0)),
  (⟨1, [L], [], Term.eq (appendT (Term.var 0) nilT) (Term.var 0)⟩,
    fun E ↦ byListIndHyp GL E 1 0 1 (InternalDerivation.eqns ++ [.delta 0]) 64 [L] []
      (appendT (Term.var 0) nilT) (Term.var 0))]

/-- The development: each theorem with its derivation, from those before it. -/
def development : Option (List (Thm × Deriv)) :=
  (theorems.foldl (fun acc (a, p) ↦ acc.bind fun (E, ds) ↦
    (p E).map fun d ↦ (E.push a, ds ++ [(a, d)])) (some (#[], []))).map Prod.snd

-- every theorem is proved, and the development checks
#guard development.any fun ds ↦ ds.length == theorems.length && checkThms GL ds #[]

end GebTests.Prototypes.FreeTopos.InternalLogic

end
