/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Certified.DatatypeEntry
public import GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramMirror
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The soundness of the programs the compiler accepts

The soundness of a whole program of the datatype language's stage-1 compiler, of the compilers'
mirror ({lit}`DatatypeProgramMirror.program_sound_mirror`), assumes that the compiler's passes
succeed on a program's forms. They do where each step of the compiler from the expansion on
gives a result ({lit}`DatatypeEntry.passes_of_accepts`): the expansion of the program, the
insertion of the recognizers, the reader and the kernel's typing, as the compiler applies them
to the forms module elaboration gives it. The soundness is therefore one of the forms the
compiler accepts, under the conditions on what the expansion writes for them and on the names
they declare that it keeps as hypotheses.

## Main statements

* {lit}`program_sound_accepted` — the soundness of a whole program, of the forms the compiler's
  steps from the expansion on accept.

## References

* {citeKey}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, datatypes, kernel, evaluator, compiler, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramAccepted

open Geb
open GebTests.Prototypes.FreeTopos.Certified.DatatypeConclusion (Concl)
open GebTests.Prototypes.FreeTopos.Certified.DatatypeHypotheses (HypFns)
open GebTests.Prototypes.FreeTopos.Certified.DatatypeMirror
open GebTests.Prototypes.FreeTopos.Certified.DatatypeEntry (Accepts passes_of_accepts)
open GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramMirror (program_sound_mirror)

/-- The soundness of a whole program of the datatype language's stage-1 compiler, of the forms
the compiler accepts: at every list of forms at which each step of the compiler from the
expansion on gives a result ({name}`Accepts`), whose definitions' bodies are source forms
({name}`HypFns.PlainOk`), whose markers are those their datatypes' atoms find
({name}`HypFns.MarkersOk`), are named by atoms other than the trees' type's and the unit
type's ({name}`HypFns.NamesOk`) and have at most one constructor of each label
({name}`HypFns.CtorsOk`), and whose forms declare no name of the
implementation's ({name}`HypFns.FormsOk`), the definitions are related to the typing
environment's and the recognizers decide membership, as the mirror's evaluator computes them
({name}`Concl`). -/
theorem program_sound_accepted (es : List Kernel.Tree) (hacc : Accepts es)
    (hplain : hypFns.PlainOk es) (hmark : hypFns.MarkersOk es)
    (hnames : hypFns.NamesOk (hypFns.msK es)) (hctors : hypFns.CtorsOk (hypFns.msK es))
    (hforms : hypFns.FormsOk es) : Concl passFns evalFns es :=
  program_sound_mirror es (passes_of_accepts hacc) hplain hmark hnames hctors hforms

end GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramAccepted

end
