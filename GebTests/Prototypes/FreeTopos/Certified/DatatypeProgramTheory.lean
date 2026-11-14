/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Certified.DatatypeAccepted
public import GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramSound
public meta import GebTests.Prototypes.FreeTopos.Certified.DatatypeAccepted -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramSound -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The soundness of a whole program in the models of the theory of a topos

The soundness of a whole program of the datatype language's stage-1 compiler, as one formula
without hypotheses, is valid in every model of the program
({lit}`DatatypeProgramSound.programClosed_valid`), a model of the theory of a topos extended by
the definitions the program's constants compile to. The constants are ones the check accepts,
which compile to well-formed definitions ({lit}`DatatypeAccepted.accepted`), so the formula
compiles to an arrow that, with every definition unfolded, is true in every model of the theory
itself ({name}`Geb.FreeTopos.Internal.valid_unfoldAll_holds_of_valid`): in the topos of types
and functional relations among them, where the arrow's value is a functional relation between
Lean's types.

## Main statements

* {lit}`programClosed_unfolded` — the soundness of a whole program, unfolded, is true in every
  model of the theory of a topos.

## References

* {cite}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, datatypes, certificate, definitional extension, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramTheory

open Geb Geb.FreeTopos GebTests.Prototypes.FreeTopos.Datatypes
open GebTests.Prototypes.FreeTopos.Weakening (Prog)
open GebTests.Prototypes.FreeTopos.Normalization (Defs)
open PartialHorn (Model IsModel)
open Sorts

universe v

variable {PST : Prog × Defs × Defs3} (h : extended3 = some PST)

include h

/-- The soundness of a whole program of the datatype language's stage-1 compiler, as one
formula without hypotheses ({name}`programClosedThm`), compiles to an arrow that, with every
definition of the program's constants unfolded, is true in every model of the theory of a
topos: it is valid in every model of the extension by the constants' definitions
({name}`DatatypeProgramSound.programClosed_valid`), the one-point model among them, which gives
that it is a formula in a context of types. -/
theorem programClosed_unfolded {a : Internal.Thm}
    (ha : programClosedThm PST.1 PST.2.1 PST.2.2 = some a) :
    ∃ cds C, Internal.compileDefs PST.1.G = some cds ∧
      Internal.compile PST.1.G a.arity a.concl (Internal.ctxObj a.ctx) (Internal.stdEnv a.ctx) =
        some (C, omega) ∧
      ∀ (M : Model.{v} theory.sig), IsModel theory M →
        (PartialHorn.unfoldAll sig cds ⟨List.replicate a.arity obj, [],
          ⟨C, comp tru (bang (Internal.ctxObj a.ctx))⟩⟩).Valid M := by
  obtain ⟨cds, hc, hbase, hok, hwf⟩ := Internal.Globals.of_accepted (DatatypeAccepted.accepted h)
  have hbase' : PST.1.G.base = sig.length + ([] : List PartialHorn.Defn).length := by
    simpa using hbase
  have hnil : a.hyps = [] := by
    simp only [programClosedThm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at ha
    obtain ⟨_, -, rfl⟩ := ha
    rfl
  -- the context's types and the formula's type, from its validity in the one-point model
  have hpoint := DatatypeProgramSound.programClosed_valid h
    ⟨[], cds, PartialHorn.pointModel (ext cds).sig,
      Internal.isModel_point_ext (pre := []) hwf, hc, hbase',
      Internal.devInv_init (Internal.isModel_point_ext (pre := []) hwf) hbase' hok hc
        (Internal.Globals.Le.refl _) hc⟩ ha
  obtain ⟨C, hC, hM⟩ := Internal.valid_unfoldAll_holds_of_valid (pre := []) hbase' hok hc hwf
    hpoint.1 hpoint.2.2.1 hnil
    (fun N hN hinv ↦ DatatypeProgramSound.programClosed_valid h
      ⟨[], cds, N, hN, hc, hbase', hinv⟩ ha)
  exact ⟨cds, C, hc, hC, hM⟩

end GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramTheory

end
