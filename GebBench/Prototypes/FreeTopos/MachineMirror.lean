/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Literals
public import GebTests.Prototypes.FreeTopos.Agreement.Conversion
public import Geb.Prototypes.FreeTopos.Tactics.Reduction
public import GebMirror.Metalogic.Tactics

set_option doc.verso true in
/-!
# The environment machine written in Geb beside the machine in Lean

For products of numerals of growing sizes, in the development of
{lit}`GebTests.Prototypes.FreeTopos.Literals`, the time the conversion checker takes to accept a
step of the environment machine at each side of the equation of the product and its value's
numeral: by the checker in Lean ({name}`Geb.FreeTopos.Internal.convCheck`), whose machine delays a
value and computes it when it is first read; by the checker written in Geb
({lit}`bootstrap/free-topos/conversion.geb`), in the Lean the bootstrap compiler emits, whose
reduction by the machine is bound to the machine in Lean
({name}`Geb.FreeTopos.Internal.Accelerate.machineRun`), which reads the encoded constants,
entries and term at each step; and the time the reduction written in Geb takes at the two sides
with no function bound to it, whose machine computes a delayed value where it builds the node.
The machines are one function of the term reduced, so the checkers accept the same
certificates; the table measures what reading the encoded data costs the bound reduction, and
what computing each delayed value costs the reduction written in Geb. The measurements of the
latter stop after the first product at which it takes longer than a bound. The final two columns
time the Lean and Geb tactics and check their answers against the expected certificate.

## Main definitions

* {lit}`byMachineAt` — the certificate of an equation by a step of the machine at each side,
  within a depth of recursion.
* {lit}`provesLean`, {lit}`provesGeb` — whether the checker in Lean, and the checker written in
  Geb, accepts that certificate for an equation of closed terms.
* {lit}`reducesGeb` — whether the reduction written in Geb, with no function bound to it, reduces
  the sides of an equation of closed terms to one term.
* {lit}`sizes` — the factors measured.
* {lit}`run` — the measurements.

## Tags

internal language, abstract machine, lazy evaluation, mirror, measurement, benchmark
-/

set_option doc.verso true

@[expose] public section

open GebMirror.Metalogic

namespace GebBench.Prototypes.FreeTopos.MachineMirror

open Geb Geb.Kernel Geb.FreeTopos
open GebTests.Prototypes.FreeTopos.Agreement.Encode
  GebTests.Prototypes.FreeTopos.Agreement.Provers
  GebTests.Prototypes.FreeTopos.Agreement.Conversion
open GebTests.Prototypes.FreeTopos.Literals (G entries bin lit)
open Internal (Term)

/-- The certificate of an equation by a step of the machine at each side within a depth of
recursion, every definition of the library unfolded. -/
def byMachineAt (fuel : ℕ) : Internal.ConvDeriv :=
  RoseTree.node (.base .join)
    [RoseTree.node (.machine fuel Translation.lib.length [] 0 1 []) [],
      RoseTree.node (.machine fuel Translation.lib.length [] 0 1 []) []]

/-- Whether the checker in Lean accepts a step of the machine at each side of an equation of
closed terms, within a depth of recursion. -/
def provesLean (fuel : ℕ) (t u : Term) : Bool :=
  (⟨0, [], [], Term.eq t u⟩ : Internal.Thm).convChecks G entries [] (byMachineAt fuel)

/-- Whether the checker written in Geb accepts a step of the machine at each side of an equation
of closed terms, within a depth of recursion. -/
def provesGeb (fuel : ℕ) (t u : Term) : Bool :=
  («Conversion.thmConvChecks» (encGlobals G) (entries.toList.map encEntry) []
    (encThm ⟨0, [], [], Term.eq t u⟩) (encConv (byMachineAt fuel))).label != 0

/-- Whether the reduction written in Geb at the data of a step, in the Lean the compiler emits
from it, to which no function is bound, reduces the sides of an equation of closed terms to one
term within a depth of recursion: what the checker written in Geb decides at the certificate of
{name}`byMachineAt`, where the machine written in Geb runs. -/
def reducesGeb (fuel : ℕ) (t u : Term) : Bool :=
  let run (s : Term) : Tree :=
    «Conversion.machineRun$geb» (encGlobals G) (entries.toList.map encEntry) (leaf 0)
      (Internal.Accelerate.encMachineData ⟨fuel, Translation.lib.length, [], 0, 1, []⟩) [] []
      (encTerm s)
  (run t).label != 0 && run t == run u

/-- The factors measured, each multiplied by itself: the numbers one less than the powers of
two, of one bit more at each. -/
def sizes : List ℕ := (List.range 12).map fun i ↦ 2 ^ (i + 1) - 1

/-- The time to evaluate a Boolean once, in microseconds, with its value. -/
def timeOnce (f : Unit → Bool) : IO (Bool × ℕ) := do
  let t₀ ← IO.monoNanosNow
  let b ← IO.lazyPure fun _ ↦ f ()
  let t₁ ← IO.monoNanosNow
  pure (b, (t₁ - t₀) / 1000)

set_option compiler.extract_closed false in
/-- Each row records the factor, whether the checkers accept, and the times in microseconds for
the two checkers, the unaccelerated Geb reduction and the two tactics. The unaccelerated reduction
is timed up to the first product at which it takes longer than the bound. The benchmark checks
agreement of the verdicts and the certificates. Closed terms are evaluated when timed. -/
def run (fuel : ℕ := 256) (bound : ℕ := 2000000) : IO Unit := do
  IO.println ("factor,accepted,lean_checker_microseconds,geb_checker_microseconds," ++
    "geb_machine_microseconds,lean_tactic_microseconds,geb_tactic_microseconds")
  (← IO.getStdout).flush
  let mut unbound := true
  for a in sizes do
    let t := bin .mul a a
    let u := lit (a * a)
    let (okL, tL) ← timeOnce fun _ ↦ provesLean fuel t u
    let (okG, tG) ← timeOnce fun _ ↦ provesGeb fuel t u
    if okL != okG then throw (IO.userError s!"mul {a} {a}: the checkers differ ({okL} {okG})")
    let expected := if okL then some (encConv (byMachineAt fuel)) else none
    let (sameL, tTL) ← timeOnce fun _ ↦
      ((Tactics.byMachine G entries 0 fuel Translation.lib.length [] 0 1 [] [] [] t u).map
        encConv) == expected
    let (sameG, tTG) ← timeOnce fun _ ↦
      «Tactics.byMachine» (encGlobals G) (entries.toList.map encEntry) (leaf 0) (leaf fuel)
        (leaf Translation.lib.length) [] (leaf 0) (leaf 1) [] [] [] (encTerm t) (encTerm u) ==
          encOpt expected
    if !(sameL && sameG) then throw (IO.userError s!"mul {a} {a}: unexpected tactic certificate")
    let mut cell := ""
    if unbound then
      let (okM, tM) ← timeOnce fun _ ↦ reducesGeb fuel t u
      if okL != okM then throw (IO.userError s!"mul {a} {a}: the machines differ ({okL} {okM})")
      cell := toString tM
      if tM > bound then unbound := false
    IO.println (",".intercalate [toString a, toString okL, toString tL, toString tG, cell,
      toString tTL, toString tTG])
    (← IO.getStdout).flush

end GebBench.Prototypes.FreeTopos.MachineMirror

end
