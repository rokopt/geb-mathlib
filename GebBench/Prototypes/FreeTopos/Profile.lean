/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.DatatypeBase
public import GebTests.Prototypes.FreeTopos.Stored
public import GebTests.Prototypes.FreeTopos.Substitution

set_option doc.verso true in
/-!
# Where the base checker's time goes

The base checker's time on a stored development, divided among the rules of its derivations'
nodes. Each node's rewriting and proving is timed, and its time less its children's is its own:
the rule's computation at the node, its substitutions, comparisons and inferences of types
included. A theorem's own time is that of the tests of its context, hypotheses and conclusion.
For each development: each rule's number of nodes and own milliseconds, by mode, and the
theorems that take longest, with their derivations' sizes and their numbers of nodes rewriting
by a hypothesis, by a theorem and joining. Timing a node costs two readings of the clock, which
the times include. Probes repeat computations the checker performs within a node's, the
contexts of a congruence's children, the test and comparison of a theorem's instance and the
inference of a formula's types, and time them apart, the node's own time excluding them. The
timers deepen the stack by a frame at each node, so the profile runs with the stack limit
raised, as {lit}`slow-checks.yml` runs the benchmarks.

## Main definitions

* {lit}`profiledChecks` — the base checker's test of a theorem, each node timed.
* {lit}`measure` — the profile of one development.
* {lit}`run` — the profiles.

## Tags

internal language, derivation, checker, profile, benchmark
-/

set_option doc.verso true

@[expose] public section

namespace GebBench.Prototypes.FreeTopos.Profile

open Geb Geb.FreeTopos Geb.FreeTopos.Internal
open GebTests.Prototypes.FreeTopos
open PartialHorn (Tree)
open scoped FinEnum

/-- The names of the rules, in the order of their constructors. -/
def ruleNames : Array String :=
  #["refl", "trans", "cong", "beta", "fstPair", "sndPair", "pairEta", "unitEta", "delta",
    "natZero", "natSucc", "listNil", "listCons", "roseNode", "caseInl", "caseInr", "thm",
    "rwHyp", "join", "natInd", "listInd", "hyp", "cut", "conv", "convFrom", "propExt", "funExt",
    "apply", "natIndHyp", "listIndHyp", "cert", "certSeq", "roseInd", "roseIndHyp", "coprodInd",
    "zeroInd", "quotInd"]

/-- The key of a theorem's own time, after the keys of the rules' two modes. -/
def thmKey : ℕ := 2 * ruleNames.size

/-- The names of the probes, whose keys follow {name}`thmKey`: the contexts of a congruence's
children, the test of a theorem's instance, the comparison with the theorem's instantiated
side or conclusion, and the inference of the types the propositional and functional
extensionalities, the cut and the conversion from a formula test. -/
def probeNames : Array String :=
  #["congruence contexts", "instance test", "instance comparison", "inferred types"]

/-- The tally: for each key, the own nanoseconds and the number of calls. -/
abbrev Tally := IO.Ref (Array (ℕ × ℕ))

/-- The implementation of {lit}`timed`, which reads the clock. -/
@[noinline] unsafe def timedImpl {α : Type} (tally : Tally) (inner : IO.Ref ℕ) (key : ℕ)
    (f : Unit → α) : α :=
  match unsafeIO (do
      let saved ← inner.swap 0
      let t₀ ← IO.monoNanosNow
      let r ← IO.lazyPure f
      let t₁ ← IO.monoNanosNow
      let c ← inner.get
      tally.modify fun a ↦ a.modify key fun (s, k) ↦ (s + (t₁ - t₀ - c), k + 1)
      inner.set (saved + (t₁ - t₀))
      pure r) with
  | .ok r => r
  | .error _ => f ()

/-- A computation's result, its time less the time the computations it calls record added to
the tally at a key; {lit}`inner` holds the time recorded within the computation enclosing it. -/
@[implemented_by timedImpl] def timed {α : Type} (_tally : Tally) (_inner : IO.Ref ℕ) (_key : ℕ)
    (f : Unit → α) : α :=
  f ()

/-- The implementation of {lit}`probe`, which times the computation and reads its result's
address, so that the computation is not removed as unused. -/
@[noinline] unsafe def probeImpl {α β : Type} (tally : Tally) (inner : IO.Ref ℕ) (key : ℕ)
    (f : Unit → α) (r : Unit → β) : β :=
  match unsafeIO (do
      let v ← IO.lazyPure fun _ ↦ timedImpl tally inner key f
      if ptrAddrUnsafe v == 0 then tally.modify id
      IO.lazyPure r) with
  | .ok r => r
  | .error _ => r ()

/-- A result, after a computation it does not use is timed at a key: the time of a computation
the checker performs within a node's, the checker's own computation repeated. -/
@[implemented_by probeImpl] def probe {α β : Type} (_tally : Tally) (_inner : IO.Ref ℕ)
    (_key : ℕ) (_f : Unit → α) (r : Unit → β) : β :=
  r ()

/-- The probes' computations at a node's rewriting, timed before it. -/
def probeRewrite (tally : Tally) (inner : IO.Ref ℕ) (G : Globals) (E : Array Entry) (n : ℕ)
    (l : Rule) (ds : List Deriv) (Γ : List Tree) (Φ : List Term) (t : Term) {β : Type}
    (r : Unit → β) : β := match l with
  | .cong => probe tally inner (thmKey + 1) (fun _ ↦ congCtxs G n t.label t.children Γ Φ ds) r
  | .thm j θ σ flip => match (E[j]?).bind Entry.language? with
    | some a => match eqParts a.concl with
      | some lr => probe tally inner (thmKey + 1 + 1) (fun _ ↦ instOk G n Γ a θ σ) fun _ ↦
          probe tally inner (thmKey + 1 + 2)
            (fun _ ↦ decide (t = instTerm θ σ (if flip then lr.2 else lr.1))) r
      | none => r ()
    | none => r ()
  | _ => r ()

/-- The probes' computations at a node's proving, timed before it. -/
def probeProve (tally : Tally) (inner : IO.Ref ℕ) (G : Globals) (E : Array Entry) (n : ℕ)
    (l : Rule) (Γ : List Tree) (φ : Term) {β : Type} (r : Unit → β) : β :=
  let types (ts : List Term) := probe tally inner (thmKey + 1 + 3)
    (fun _ ↦ ts.map (typeIn G n Γ)) r
  match l with
  | .apply j θ σ => match (E[j]?).bind Entry.language? with
    | some a => probe tally inner (thmKey + 1 + 1) (fun _ ↦ instOk G n Γ a θ σ) fun _ ↦
        probe tally inner (thmKey + 1 + 2) (fun _ ↦ decide (φ = instTerm θ σ a.concl)) r
    | none => r ()
  | .propExt => match eqParts φ with
    | some (α, β) => types [α, β]
    | none => r ()
  | .funExt => match eqParts φ with
    | some (f, _) => types [f]
    | none => r ()
  | .cut ψ => types [ψ]
  | .convFrom ψ => types [ψ]
  | _ => r ()

/-- The checker's step at a node, its rewriting and its proving each timed at the rule's key,
after the probes. -/
def profiledStep (tally : Tally) (inner : IO.Ref ℕ) (G : Globals) (E : Array Entry)
    (n : ℕ) (l : Rule) (cs : List (Deriv × Checks)) : Checks :=
  let c := checkStep G E n l cs
  (fun Γ Φ t ↦ timed tally inner (2 * l.ctorIdx) fun _ ↦
    probeRewrite tally inner G E n l (cs.map Prod.fst) Γ Φ t fun _ ↦ c.1 Γ Φ t,
   fun Γ Φ φ ↦ timed tally inner (2 * l.ctorIdx + 1) fun _ ↦
    probeProve tally inner G E n l Γ φ fun _ ↦ c.2 Γ Φ φ)

/-- {name}`Thm.checks`, each node of the derivation timed, the tests of the theorem's context,
hypotheses and conclusion at {name}`thmKey`. -/
def profiledChecks (tally : Tally) (inner : IO.Ref ℕ) (G : Globals) (E : Array Entry)
    (a : Thm) (d : Deriv) : Bool :=
  timed tally inner thmKey fun _ ↦
    a.ctx.all (IsTy G a.arity) && a.hyps.all (fun h ↦ typeIn G a.arity a.ctx h = some omega) &&
      decide (typeIn G a.arity a.ctx a.concl = some omega) &&
      (RoseTree.para (profiledStep tally inner G E a.arity) d).2 a.ctx a.hyps a.concl

/-- The number of a derivation's nodes whose rule a test accepts. -/
def countRule (p : Rule → Bool) (d : Deriv) : ℕ :=
  RoseTree.elim (fun l ns ↦ (if p l then 1 else 0) + ns.sum) d

/-- The profile of a development from the constants of {lit}`G`, of its theorems whose indices
{lit}`sel` selects, printed: each rule's mode, nodes and own milliseconds and each probe's calls
and milliseconds, then the ten theorems that take longest. The theorems it does not select
enter the environment unchecked. -/
def measure (name : String) (G : Globals) (ds : List Decl) (sel : ℕ → Bool) : IO Unit := do
  let keys := thmKey + 1 + probeNames.size
  let tally ← IO.mkRef (Array.replicate keys (0, 0))
  let inner ← IO.mkRef 0
  let mut st : Globals × Array Entry := (G, #[])
  let mut times : Array (ℕ × ℕ × Deriv) := #[]
  for (d, i) in ds.zipIdx do
    match d with
    | .language a der =>
      if !sel i then
        st := (st.1, st.2.push (.language a))
        continue
      let t₀ ← IO.monoNanosNow
      let ok ← IO.lazyPure fun _ ↦ profiledChecks tally inner st.1 st.2 a der
      let t₁ ← IO.monoNanosNow
      if !ok then throw (IO.userError s!"{name}: theorem {i} does not check")
      times := times.push (i, t₁ - t₀, der)
      st := (st.1, st.2.push (.language a))
    | d => match d.step st.1 st.2 with
      | some st' => st := st'
      | none => throw (IO.userError s!"{name}: declaration {i} does not check")
  let rows := (← tally.get).zipIdx.filter (·.1.2 > 0) |>.qsort (·.1.1 > ·.1.1)
  for ((ns, k), key) in rows do
    let rule := if key = thmKey then "theorem" else if key > thmKey then
      probeNames.getD (key - thmKey - 1) "?" else ruleNames.getD (key / 2) "?"
    let mode := if key ≥ thmKey then "" else if key % 2 = 0 then "rewrite" else "prove"
    IO.println s!"{name},{rule},{mode},{k},{ns / 1000000}"
  for (i, ns, der) in (times.qsort (·.2.1 > ·.2.1)).take 10 do
    let count (p : Rule → Bool) := countRule p der
    IO.println s!"{name},theorem {i},{ns / 1000000},{countRule (fun _ ↦ true) der},\
      {count fun | .rwHyp _ _ => true | _ => false},\
      {count fun | .thm _ _ _ _ => true | _ => false},{count fun | .join => true | _ => false},\
      {count fun | .roseIndHyp _ _ _ => true | .roseInd _ _ _ _ => true | _ => false}"

/-- The declarations a stored certificate holds, read at run time. -/
def stored (name : String) : IO (List Decl) := do
  let text ← IO.FS.readFile s!"bootstrap/certificates/{name}.cert"
  let some ds := Stored.declsOfText text | throw (IO.userError s!"{name} does not read")
  pure ds

set_option compiler.extract_closed false in
/-- The profiles of the development of substitution and of a theorem of the datatype language's
soundness at the keywords' forms, after the base's and the atom's developments.
Closed terms are not extracted, so that each runs when it is timed rather than when the program
starts. -/
def run : IO Unit := do
  IO.println "certificate,rule,mode,nodes,own_milliseconds"
  IO.println "certificate,theorem,milliseconds,nodes,hypothesis_rewritings,\
    theorem_rewritings,joins,rose_inductions"
  if let some P := Substitution.program then
    measure "substitution" (Weakening.Prog.G P) (← stored "substitution") fun _ ↦ true
  if let some (P, _, _) := Datatypes.extended3 then
    let pre := (← stored "datatype-base") ++ (← stored "datatype-atom")
    measure "datatype-list" P.G (pre ++ (← stored "datatype-list"))
      fun i ↦ i = 348

end GebBench.Prototypes.FreeTopos.Profile

end
