/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebBench.Prototypes.FreeTopos.TranslationProofs
public import GebTests.Prototypes.FreeTopos.Machine

set_option doc.verso true in
/-!
# The library's arithmetic at numerals, checked five ways

For each definition of the library's arithmetic at numerals of growing sizes, the equation of its
application and its value's numeral proved five ways, in the development of
{lit}`GebTests.Prototypes.FreeTopos.Literals`: by the derivation the prover's normalization
computes, reducing each side to its normal form, weak head normal forms first, checked by the
base checker; by that reduction of each side, its derivation computed and not checked; by a step
of conversion that performs that reduction computing its result alone
({name}`Geb.FreeTopos.Internal.evalR`); by a step of evaluation, the arithmetic of the natural
numbers; and by a step of the environment machine at each side
({name}`Geb.FreeTopos.Internal.machineReduce`). Each row gives the derivation's nodes and the
least of three times each check takes, in microseconds.

## Main definitions

* {lit}`cases` — the definitions and numbers measured.
* {lit}`run` — the measurements.

## Tags

internal language, conversion, arithmetic, numeral, measurement, benchmark
-/

set_option doc.verso true

@[expose] public section

namespace GebBench.Prototypes.FreeTopos.Literals

open Geb Geb.FreeTopos
open GebTests.Prototypes.FreeTopos.Literals (G rs entries bin lit proves)
open GebBench.Prototypes.FreeTopos.TranslationProofs (derivSize timeUs)
open Geb.FreeTopos.Literals (Sym)
open Internal (Term Thm ConvDeriv)

/-- The definitions and numbers measured: addition, multiplication, equality, less and the
truncated difference, at numbers of two, four and six decimal digits. -/
def cases : List (String × Sym × ℕ × ℕ) :=
  ([(12, 34), (1234, 5678), (123456, 654321)] : List (ℕ × ℕ)).flatMap
    fun (a, b) ↦ [("add", .add, a, b), ("mul", .mul, a, b), ("eq", .eqB, a, a),
      ("lt", .ltB, a, b), ("sub", .sub, b, a)]

/-- The certificate of an equation by a step of conversion reducing each side to its normal
form. -/
def byReduction : ConvDeriv :=
  RoseTree.node (.base .join)
    [RoseTree.node (.eval rs 4096 .full) [], RoseTree.node (.eval rs 4096 .full) []]

set_option compiler.extract_closed false in
/-- The measurement of a definition at two numbers, printed, and an error where a check fails. -/
def report (name : String) (s : Sym) (a b : ℕ) : IO Unit := do
  let t := bin s a b
  let some v := Geb.FreeTopos.Literals.eval t | throw (IO.userError s!"{name}: no value")
  let a' : Thm := ⟨0, [], [], Term.eq t v.term⟩
  let some d := Tactics.byMode .full G entries 0 rs [] [] t v.term
    | throw (IO.userError s!"{name}: no derivation")
  let (okB, tB) ← timeUs fun _ ↦ a'.checks G entries d
  let (okD, tD) ← timeUs fun _ ↦
    match Internal.eval G entries 0 rs 4096 .full [] [] t,
        Internal.eval G entries 0 rs 4096 .full [] [] v.term with
    | some (l, _), some (r, _) => l == r
    | _, _ => false
  let (okN, tN) ← timeUs fun _ ↦ a'.convChecks G entries byReduction
  let (okL, tL) ← timeUs fun _ ↦ proves t v.term
  let (okM, tM) ← timeUs fun _ ↦ GebTests.Prototypes.FreeTopos.Machine.proves t v.term
  if !(okB && okD && okN && okL && okM) then
    throw (IO.userError s!"{name} {a} {b}: a check fails ({okB} {okD} {okN} {okL} {okM})")
  IO.println (",".intercalate ([name] ++ [a, b, derivSize d, tB, tD, tN, tL, tM].map toString))

set_option compiler.extract_closed false in
/-- The measurements. Closed terms are not extracted, so that each check runs when it is timed
rather than when the program starts. -/
def run : IO Unit := do
  IO.println "operation,a,b,derivation_nodes,base_microseconds,derivation_reduction_microseconds,\
    reduction_microseconds,evaluation_microseconds,machine_microseconds"
  for (name, s, a, b) in cases do report name s a b

end GebBench.Prototypes.FreeTopos.Literals

end
