/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Certified.DatatypeMirror
public import GebTests.Prototypes.FreeTopos.Certified.DatatypeNumerals
public import GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramExplicit
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The soundness of a whole program, of the compilers' mirror

The soundness of a whole program of the datatype language's stage-1 compiler, as a statement of
the kernel's lists of forms ({lit}`DatatypeProgramExplicit.program_sound_explicit`), is about the
values of the globals the kernel loads for the compilers' definitions, in an extended program in
which the soundness is stated. Those values are the definitions of the compilers' mirror
({lit}`DatatypeMirror.passFns_loaded`, {lit}`DatatypeMirror.evalFns_loaded`,
{lit}`DatatypeMirror.hypFns_loaded`), the extended program exists with the soundness stated in
it ({lit}`DatatypeAccepted.exists_programForms`), and the two facts about the numerals' digits
that the soundness assumes hold of the mirror ({lit}`DatatypeNumerals.numeral_decimalChars`,
{lit}`DatatypeNumerals.charsFixed_decimalChars`). The soundness is therefore a statement about
functions of Lean, the Lean the bootstrap compiler emits from the compilers' sources, with no
other parameter than a program's forms.

## Main statements

* {lit}`program_sound_mirror` — the soundness of a whole program, of the mirror's definitions.

## References

* {cite}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, datatypes, kernel, evaluator, mirror, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramMirror

open Geb GebTests.Prototypes.FreeTopos.Datatypes
open GebTests.Prototypes.FreeTopos.Certified.DatatypeAccepted (exists_programForms)
open GebTests.Prototypes.FreeTopos.Certified.DatatypeTranslated (translated)
open GebTests.Prototypes.FreeTopos.Certified.DatatypePasses (PassFns)
open GebTests.Prototypes.FreeTopos.Certified.DatatypeConclusion (Concl)
open GebTests.Prototypes.FreeTopos.Certified.DatatypeHypotheses (HypFns)
open GebTests.Prototypes.FreeTopos.Certified.DatatypeMirror
open GebTests.Prototypes.FreeTopos.Certified.DatatypeNumerals
open GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramExplicit (program_sound_explicit)

/-- The soundness of a whole program of the datatype language's stage-1 compiler, of the
compilers' mirror: at every list of forms on which the passes the mirror defines succeed
({name}`PassFns.passes`), whose definitions' bodies are source forms ({name}`HypFns.PlainOk`),
whose markers are those their datatypes' atoms find ({name}`HypFns.MarkersOk`), are named by
atoms other than the trees' type's and the unit type's ({name}`HypFns.NamesOk`) and have at
most one constructor of each label ({name}`HypFns.CtorsOk`), and whose forms declare no name
of the implementation's ({name}`HypFns.FormsOk`), the definitions are
related to the typing environment's and the recognizers decide membership, as the mirror's
evaluator computes them ({name}`Concl`). -/
theorem program_sound_mirror (ks : List Kernel.Tree) (hpass : ∀ p ∈ passFns.passes, p ks)
    (hplain : hypFns.PlainOk ks) (hmark : hypFns.MarkersOk ks)
    (hnames : hypFns.NamesOk (hypFns.msK ks)) (hctors : hypFns.CtorsOk (hypFns.msK ks))
    (hforms : hypFns.FormsOk ks) : Concl passFns evalFns ks := by
  obtain ⟨PST, a, h, ha⟩ := exists_programForms
  obtain ⟨L⟩ := translated h
  exact program_sound_explicit h ha L (passFns_loaded L) (evalFns_loaded L) (hypFns_loaded L) ks
    hpass hplain hmark ⟨hnames, hctors, numeral_decimalChars, charsFixed_decimalChars⟩ hforms

end GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramMirror

end
