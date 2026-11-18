/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Conversion
public import Geb.Prototypes.FreeTopos.Internal.Encoding

set_option doc.verso true in
/-!
# The environment machine in place of the machine written in Geb

An acceleration of a program written in Geb is native code run in place of the program's own,
bound to it by the program's name and proved to compute what the program computes. The reduction
by the environment machine that the conversion checker written in Geb calls
({lit}`bootstrap/free-topos/conversion.geb`, {lit}`Conversion.machineRun`) is accelerated by the
machine in Lean ({name}`Geb.FreeTopos.Internal.machineReduceBy`): the machine written in Geb, a
tree holding no function, computes a delayed value where it builds the node, and so reduces both
branches of a conditional, where the machine in Lean computes it when it is first read.

The reduction written in Geb is a function of trees. {lit}`machineRun` takes that function and
gives a function of the same trees: where every argument is the representation of a datum of the
checker ({lit}`Geb.FreeTopos.Internal.Encode`), the representation of the machine's result at
those data, and elsewhere the given function's value. The two are equal at every argument
({lit}`machineRun_eq`) for a given function that agrees with the machine at the representations
({lit}`Agrees`), which the agreement of the machine written in Geb states of the Lean the
bootstrap compiler emits from it; the reading of an argument has a value only at a
representation, so no argument is given to the machine in Lean that the agreement does not
cover. The Lean the compiler emits is bound to {lit}`machineRun` at the program's definition by
{lit}`scripts/bootstrap.sh`.

## Main definitions

* {lit}`MachineRun` — the type of the reduction as the checker written in Geb calls it.
* {lit}`MachineData` — the data of a step of the machine.
* {lit}`machineRunAt` — the reduction by the machine in Lean at the data of a step.
* {lit}`machineRun` — the reduction by the machine in Lean at the representations, and the
  given reduction elsewhere.
* {lit}`Agrees` — a reduction of trees agrees with the machine in Lean at the representations.
* {lit}`machineRunShadow` — the accelerated reduction run beside the given one and compared.

## Main statements

* {lit}`machineRun_eq`, {lit}`machineRunShadow_eq` — the accelerated reduction, and the
  accelerated reduction run beside the given one and compared, is the given one, where that
  agrees with the machine in Lean at the representations.

## Tags

internal language, abstract machine, acceleration, agreement
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal.Accelerate

open Geb.PartialHorn (Tree)
open Encode
open scoped FinEnum

/-- A reduction by the machine as the conversion checker written in Geb calls it, every argument
a tree: of the constants, the entries, the number of object variables, the data of the step,
the context, the hypotheses and the term, to the optional result. -/
abbrev MachineRun : Type :=
  Tree → List Tree → Tree → List Tree → List Tree → List Tree → Tree → Tree

/-- The data of a step of the machine: the depth of its recursion, the bound of the definitions
it unfolds and those among them it does not, the indices of the primitives that build a list, and
the rules it rewrites by at the roots of its normal form. -/
structure MachineData where
  /-- The depth of the recursion. -/
  fuel : ℕ
  /-- The bound of the indices of the definitions unfolded. -/
  bound : ℕ
  /-- The definitions below the bound that are not unfolded. -/
  except : List ℕ
  /-- The index of the primitive of the empty list. -/
  kl : ℕ
  /-- The index of the primitive of the construction of a list. -/
  kc : ℕ
  /-- The rules of the normalizer rewritten by at the roots of the normal form. -/
  rules : List NormRule

/-- The data of a step of the machine as the trees a certificate holds. -/
def encMachineData (d : MachineData) : List Tree :=
  [Kernel.leaf d.fuel, Kernel.leaf d.bound, RoseTree.node 0 (d.except.map Kernel.leaf),
    Kernel.leaf d.kl, Kernel.leaf d.kc, RoseTree.node 0 (d.rules.map encRule)]

/-- The data of a step of the machine that trees represent, where they represent one whose rules
are neither rules of the checker nor prepared theorems. -/
def decMachineData (dt : List Tree) : Option MachineData := match dt with
  | [fuel, m, ex, kl, kc, rs] => (decLeaf fuel).bind fun fuel ↦ (decLeaf m).bind fun m ↦
      (decList ex).bind fun ex ↦ (ex.mapM decLeaf).bind fun ex ↦ (decLeaf kl).bind fun kl ↦
        (decLeaf kc).bind fun kc ↦ (decList rs).bind fun rs ↦
          (rs.mapM decRule).map fun rs ↦ ⟨fuel, m, ex, kl, kc, rs⟩
  | _ => none

/-- Rules of the normalizer none of which is a prepared theorem, whose matching no tree
represents. -/
def Unprepared (rs : List NormRule) : Prop := ∀ r ∈ rs, ∀ j θ root m k, r ≠ .thmAt j θ root m k

/-- Trees read as the data of a step of the machine are those data's representation, and none of
the rules read is a prepared theorem. -/
theorem encMachineData_of_dec {dt : List Tree} {d : MachineData}
    (h : decMachineData dt = some d) : encMachineData d = dt ∧ Unprepared d.rules := by
  unfold decMachineData at h
  split at h
  · next fuel m ex kl kc rs =>
    obtain ⟨fuel', hfuel, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨m', hm, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ex', hex, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ns, hns, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨kl', hkl, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨kc', hkc, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rs', hrs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rules, hrules, rfl⟩ := Option.map_eq_some_iff.mp h
    refine ⟨?_, fun r hr j θ root mt k ↦ ?_⟩
    · rw [encMachineData, leaf_of_decLeaf hfuel, leaf_of_decLeaf hm,
        map_of_mapM_all (fun _ _ ↦ leaf_of_decLeaf) hns, node_of_decList hex,
        leaf_of_decLeaf hkl, leaf_of_decLeaf hkc,
        map_of_mapM_all encRule_of_decRule hrules, node_of_decList hrs]
    · obtain ⟨x, hx⟩ := exists_of_mem_mapM rs' rules hrules r hr
      exact decRule_unprepared hx j θ root mt k
  · cases h

/-- The reduction of a term by the machine in Lean at the data of a step: every definition of an
index below the bound unfolded but those excepted. -/
def machineRunAt (G : Globals) (E : Array Entry) (n : ℕ) (d : MachineData) (Γ : List Tree)
    (Φ : List Term) (t : Term) : Option Term :=
  machineReduceBy G E n (fun j ↦ decide (j < d.bound) && !d.except.contains j) d.kl d.kc
    d.rules d.fuel Γ Φ t

/-- The data a reduction's trees represent, where each represents one: the constants, the
entries, the number of object variables, the data of the step, the hypotheses and the term. -/
structure Args where
  /-- The constants. -/
  G : Globals
  /-- The entries. -/
  E : List Entry
  /-- The number of object variables. -/
  n : ℕ
  /-- The data of the step. -/
  d : MachineData
  /-- The hypotheses. -/
  Φ : List Term
  /-- The term. -/
  t : Term

/-- The data a reduction's trees represent, where each represents one. -/
def decArgs (Gt : Tree) (Et : List Tree) (nt : Tree) (dt hs : List Tree) (t : Tree) :
    Option Args :=
  (decGlobals Gt).bind fun G ↦ (Et.mapM decEntry).bind fun E ↦ (decLeaf nt).bind fun n ↦
    (decMachineData dt).bind fun d ↦ (hs.mapM decTerm).bind fun Φ ↦
      (decTerm t).map fun t ↦ ⟨G, E, n, d, Φ, t⟩

/-- Trees read as a reduction's data are those data's representations. -/
theorem enc_of_decArgs {Gt : Tree} {Et : List Tree} {nt : Tree} {dt hs : List Tree} {t : Tree}
    {a : Args} (h : decArgs Gt Et nt dt hs t = some a) :
    encGlobals a.G = Gt ∧ a.E.map encEntry = Et ∧ Kernel.leaf a.n = nt ∧
      encMachineData a.d = dt ∧ Unprepared a.d.rules ∧ a.Φ.map encTerm = hs ∧
        encTerm a.t = t := by
  unfold decArgs at h
  obtain ⟨G, hG, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨E, hE, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨n, hn, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨d, hd, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨Φ, hΦ, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨encGlobals_of_decGlobals hG, map_of_mapM_all encEntry_of_decEntry hE,
    leaf_of_decLeaf hn, (encMachineData_of_dec hd).1, (encMachineData_of_dec hd).2,
    map_of_mapM_all encTerm_of_decTerm hΦ, encTerm_of_decTerm t u hu⟩

/-- The reduction by the machine in Lean in place of a reduction of trees: at trees that
represent the checker's data, the representation of the machine's result at those data, and the
given reduction's value elsewhere. -/
def machineRun (geb : MachineRun) : MachineRun := fun Gt Et nt dt g hs t ↦
  match decArgs Gt Et nt dt hs t with
  | some a => encOpt ((machineRunAt a.G a.E.toArray a.n a.d g a.Φ a.t).map encTerm)
  | none => geb Gt Et nt dt g hs t

/-- A reduction of trees agrees with the machine in Lean at the representations: at the
representations of constants, entries, a number of object variables, the data of a step none of
whose rules is a prepared theorem, hypotheses and a term, in any context, its value is the
representation of the machine's result. -/
def Agrees (geb : MachineRun) : Prop :=
  ∀ (G : Globals) (E : List Entry) (n : ℕ) (d : MachineData), Unprepared d.rules →
    ∀ (Γ : List Tree) (Φ : List Term) (t : Term),
      geb (encGlobals G) (E.map encEntry) (Kernel.leaf n) (encMachineData d) Γ (Φ.map encTerm)
          (encTerm t) =
        encOpt ((machineRunAt G E.toArray n d Γ Φ t).map encTerm)

/-- The accelerated reduction is the given one, where the given one agrees with the machine in
Lean at the representations. -/
theorem machineRun_eq {geb : MachineRun} (h : Agrees geb) : machineRun geb = geb := by
  funext Gt Et nt dt g hs t
  unfold machineRun
  split
  · next a ha =>
    obtain ⟨rfl, rfl, rfl, rfl, hr, rfl, rfl⟩ := enc_of_decArgs ha
    exact (h a.G a.E a.n a.d hr g a.Φ a.t).symm
  · rfl

/-- The accelerated reduction run beside the given one and compared: the accelerated
reduction's value where the two are one, and otherwise the given reduction's, with a report of
the difference on the standard error. The Lean the compiler emits is bound to it in place of
{name}`machineRun` where the environment variable {lit}`GEB_ACCELERATION` is {lit}`shadow`
when {lit}`scripts/bootstrap.sh` emits it, so that a run compares the machine in Lean with the
reduction written in Geb at every reduction it makes. -/
def machineRunShadow (geb : MachineRun) : MachineRun := fun Gt Et nt dt g hs t ↦
  let a := machineRun geb Gt Et nt dt g hs t
  let b := geb Gt Et nt dt g hs t
  if a = b then a
  else dbgTrace "acceleration: the machine in Lean differs from Conversion.machineRun" fun _ ↦ b

/-- The accelerated reduction run beside the given one and compared is the given one, where the
given one agrees with the machine in Lean at the representations. -/
theorem machineRunShadow_eq {geb : MachineRun} (h : Agrees geb) : machineRunShadow geb = geb := by
  funext Gt Et nt dt g hs t
  unfold machineRunShadow
  rw [machineRun_eq h]
  simp only [↓reduceIte]

end Geb.FreeTopos.Internal.Accelerate

end
