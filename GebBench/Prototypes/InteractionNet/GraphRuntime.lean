/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.KernelGraph
public import Geb.Prototypes.Kernel.Modules
public import GebTests.Prototypes.Kernel

set_option doc.verso true in
/-!
# The phases of the graph runtime's steps

The runs of the kernel programs {lit}`size` and {lit}`mirror` through the graph compiler and
partner-array runtime ({name}`Geb.InteractionNet.Kernel.graphRun`) at the trees of three and five
nodes that {lit}`GebTests.Prototypes.InteractionNet.CompilerGraph` and
{lit}`GebSlow.Prototypes.InteractionNet.CompilerGraph` check, each step of the default schedule
({name}`Geb.InteractionNet.GraphRuntime.step`) taken in its phases and each phase timed: the scan
of the principal neighbors ({name}`Geb.InteractionNet.GraphRuntime.candidates`); the selection of
the first redex with a rule, which repeats the scan and looks up the rule
({name}`Geb.InteractionNet.GraphRuntime.select`); the storage of the rule's replacement in array
form ({name}`Geb.InteractionNet.ArrayNet.encode`); its allocation after the net's endpoints and
the splices of the pair's auxiliary wires ({name}`Geb.InteractionNet.ArrayNet.gluePair`); the
compaction of the surviving endpoints ({name}`Geb.InteractionNet.ArrayWiring.pullback`); and the
materialization of the cells' labels ({name}`Geb.InteractionNet.GraphRuntime.cache`). The phases
compose {name}`Geb.InteractionNet.GraphRuntime.contract` as it is defined, so the run is the
default schedule's, and its normal form is read back and compared with the tree the tests expect.

For each run, a line of totals: its steps, the most cells and endpoints of a state, the
milliseconds of the run, and those of each phase; the run's time includes the scan twice, apart
and within the selection, and a step's time is that of the phases but the scan apart. Every
thousandth step, a line of the state's cells and endpoints, the microseconds of the step, and
those of computing the number of the state's endpoints
({lit}`FinEnum.card`) and of the array position of its last cell's principal port
({lit}`FinEnum.equiv`), which every step's indexing of endpoints computes.

## Main definitions

* {lit}`Phases` — the nanoseconds of each phase, summed over a run.
* {lit}`measure` — the measurement of one run.
* {lit}`run` — the measurements.

## Tags

interaction net, graph runtime, partner array, compaction, measurement, benchmark
-/

set_option doc.verso true

@[expose] public section

namespace GebBench.Prototypes.InteractionNet.GraphRuntime

open scoped FinEnum

open Geb.InteractionNet Geb.InteractionNet.GraphRuntime

/-- The value of a computation and its time, in nanoseconds. -/
@[noinline] def timed {β : Type} (f : Unit → β) : IO (β × ℕ) := do
  let t₀ ← IO.monoNanosNow
  let b ← IO.lazyPure f
  let t₁ ← IO.monoNanosNow
  pure (b, t₁ - t₀)

/-- The nanoseconds of each phase of the runtime's steps, summed over a run. -/
structure Phases where
  /-- The scans of the principal neighbors. -/
  scan : ℕ := 0
  /-- The selections of a redex with a rule, each repeating the scan. -/
  select : ℕ := 0
  /-- The storage of the replacements in array form. -/
  encode : ℕ := 0
  /-- The allocations of the replacements and the splices of the pairs' auxiliary wires. -/
  glue : ℕ := 0
  /-- The compactions of the surviving endpoints. -/
  compact : ℕ := 0
  /-- The materializations of the cells' labels. -/
  labels : ℕ := 0

variable {α : Type} {arity : α → ℕ}

/-- The number of a state's endpoints, its boundary port and its cells' ports. -/
def endpoints (n : State arity 1) : ℕ := FinEnum.card (Endpoint arity n.2.1 (Fin 1))

set_option compiler.extract_closed false in
/-- The cells and endpoints of a state, and the microseconds of computing the number of its
endpoints and the array position of its last cell's principal port, as a line. -/
def sample (step : ℕ) (n : State arity 1) (stepNs : ℕ) : IO Unit := do
  let (e, cardNs) ← timed fun _ ↦ endpoints n
  let indexNs ← if h : 0 < n.1 then do
      let (_, ns) ← timed fun _ ↦
        (FinEnum.equiv (PortNet.principal arity n.2.1 ⟨n.1 - 1, by omega⟩ :
          Endpoint arity n.2.1 (Fin 1))).val
      pure ns
    else pure 0
  IO.println s!"  {step},{n.1},{e},{stepNs / 1000},{cardNs / 1000},{indexNs / 1000}"

set_option compiler.extract_closed false in
/-- Take steps of the default schedule from a state, at most {lit}`fuel`, each in its timed
phases: the state reached, the number of steps, the most cells and endpoints of a state, the
phases' times, and whether the state reached is normal. -/
def execute (s : PortSystem arity) (fuel : ℕ) (n₀ : State arity 1) :
    IO (State arity 1 × ℕ × ℕ × ℕ × Phases × Bool) := do
  let mut n := n₀
  let mut steps := 0
  let mut cells := n₀.1
  let mut ends := endpoints n₀
  let mut p : Phases := {}
  let mut normal := false
  for _ in [0:fuel] do
    let (_, scan) ← timed fun _ ↦ (candidates n).length
    let (r?, select) ← timed fun _ ↦ GraphRuntime.select s n
    let some r := r?
      | normal := true
        break
    let (rhs, encode) ← timed fun _ ↦ ArrayNet.encode r.rhs.2.2
    let (⟨g, hg⟩, glue) ← timed fun _ ↦
      (⟨n.2.2.gluePair r.active rhs, rfl⟩ : {g // g = n.2.2.gluePair r.active rhs})
    let (w, compact) ← timed fun _ ↦
      g.1.pullback (ArrayNet.livePorts arity n.2.1 r.rhs.2.1 (PortNet.active_ne r.active))
        (ArrayWiring.closed_of_respects (hg ▸ n.2.2.livePorts_respects r.active rhs))
    let (m, labels) ← timed fun _ ↦ cache ⟨_, _, ⟨w, g.2⟩⟩
    p := ⟨p.scan + scan, p.select + select, p.encode + encode, p.glue + glue,
      p.compact + compact, p.labels + labels⟩
    steps := steps + 1
    n := m
    cells := max cells n.1
    ends := max ends (endpoints n)
    if steps % 1000 = 0 then
      sample steps n (select + encode + glue + compact + labels)
  pure (n, steps, cells, ends, p, normal)

set_option compiler.extract_closed false in
/-- The measurement of the run of a program's last definition at a tree, its normal form compared
with the expected tree, printed, and an error where the program does not compile, the run does
not reach a normal form, or its tree is not the one expected. -/
def measure (name : String) (text : String) (fuel : ℕ) (input expected : Geb.Kernel.Tree) :
    IO Unit := do
  let some ds := Geb.Kernel.readProgram text.toList
    | throw (IO.userError s!"{name}: the program does not read")
  let P := ds.map Prod.snd
  let some t := P.getLast? | throw (IO.userError s!"{name}: the program is empty")
  let some n₀ := Kernel.graphInitial t input
    | throw (IO.userError s!"{name}: the definition does not compile")
  let t₀ ← IO.monoNanosNow
  let (m, steps, cells, ends, p, normal) ← execute (Kernel.graphSystem P) fuel (encode n₀)
  let t₁ ← IO.monoNanosNow
  unless normal do throw (IO.userError s!"{name}: no normal form within {fuel} steps")
  unless readTree Kernel.graphTreeTag m = some expected do
    throw (IO.userError s!"{name}: the normal form is not the tree expected")
  let ms (ns : ℕ) : ℕ := ns / 1000000
  IO.println s!"{name},{steps},{cells},{ends},{ms (t₁ - t₀)},{ms p.scan},{ms p.select},\
    {ms p.encode},{ms p.glue},{ms p.compact},{ms p.labels}"

open Geb Geb.Kernel in
set_option compiler.extract_closed false in
/-- The measurements, the runs at three nodes first. Closed terms are not extracted, so that each
runs when it is timed rather than when the program starts. -/
def run : IO Unit := do
  IO.println "run,steps,cells,endpoints,milliseconds,scan,select,encode,glue,compact,labels"
  IO.println "  step,cells,endpoints,step_microseconds,card_microseconds,index_microseconds"
  let three := RoseTree.node 1 [leaf 2, leaf 3]
  let five := RoseTree.node 1 [leaf 2, RoseTree.node 3 [leaf 4, leaf 5]]
  measure "size-3" Tests.size 6000 three (leaf 3)
  measure "mirror-3" Tests.mirror 6000 three (RoseTree.node 1 [leaf 3, leaf 2])
  measure "size-5" Tests.size 20000 five (leaf 5)
  measure "mirror-5" Tests.mirror 40000 five
    (RoseTree.node 1 [RoseTree.node 3 [leaf 5, leaf 4], leaf 2])

end GebBench.Prototypes.InteractionNet.GraphRuntime

end
