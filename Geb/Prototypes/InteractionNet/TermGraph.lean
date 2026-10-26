/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.FinEnum
public import Geb.Prototypes.InteractionNet.Term
public import Geb.Prototypes.InteractionNet.PortNetOperations
public import Geb.Prototypes.InteractionNet.FinitePorts
import Geb.Cslib.Foundations.Data.PFunctor.Free
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Term trees as open port graphs

A term becomes a finite graph with one root boundary and a separate boundary for each
variable occurrence. Repeated variable names remain separate at this stage. An agent
adds one cell: its principal port meets the root boundary, and each auxiliary port takes
the place of the corresponding child's root boundary. No wire gluing or name identification
is needed within a term tree.

## Main definitions

* {lit}`TermFragment` — an open term graph, with named and ordered leaf occurrences.
* {lit}`TermFragment.var`, {lit}`TermFragment.agent` — variable and agent fragments.
* {lit}`Term.fragment` — interpret arbitrary interaction-calculus terms as open graphs.

## Main statements

* {lit}`Term.fragment_names` — graph leaves have exactly the term's name occurrences.

## Tags

interaction net, term, tree, graph, syntax, interpretation
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

open scoped FinEnum

variable {α ν μ : Type} {arity : α → ℕ}

/-- A term tree with one root and a boundary for every named leaf occurrence. -/
structure TermFragment (arity : α → ℕ) (ν : Type) where
  /-- Cells retain their structural positions in the term. -/
  Cell : Type
  /-- An explicit finite cell enumeration. -/
  cellEnum : FinEnum Cell
  /-- Variable occurrences retain their structural positions. -/
  Leaf : Type
  /-- An explicit finite leaf enumeration. -/
  leafEnum : FinEnum Leaf
  /-- The agent symbol of each cell. -/
  label : Cell → α
  /-- The wire name at each leaf occurrence. -/
  name : Leaf → ν
  /-- The leaf occurrences in syntax order. -/
  order : List Leaf
  /-- Every occurrence appears at most once in syntax order. -/
  unique : order.Nodup
  /-- Every occurrence appears in syntax order. -/
  cover : ∀ p, p ∈ order
  /-- The tree's wires, with its root and leaves exposed. -/
  net : PortNet arity label (Unit ⊕ Leaf)

attribute [instance] TermFragment.cellEnum TermFragment.leafEnum

namespace TermFragment

/-- Compare fragment endpoints using the supplied finite cell and leaf indices. -/
@[instance_reducible] def endpointDecidableEq (f : TermFragment arity ν) :
    DecidableEq (Endpoint arity f.label (Unit ⊕ f.Leaf)) :=
  let : DecidableEq f.Cell := f.cellEnum.decEq
  let : DecidableEq f.Leaf := f.leafEnum.decEq
  inferInstanceAs (DecidableEq ((Unit ⊕ f.Leaf) ⊕ (Σ c, Fin (arity (f.label c) + 1))))

/-- The ordered names of the exposed leaf occurrences. -/
def names (f : TermFragment arity ν) : List ν := f.order.map f.name

/-- Change leaf names while retaining the fragment's cells, occurrence positions and wires. -/
def rename (σ : ν → μ) (f : TermFragment arity ν) : TermFragment arity μ where
  Cell := f.Cell
  cellEnum := f.cellEnum
  Leaf := f.Leaf
  leafEnum := f.leafEnum
  label := f.label
  name p := σ (f.name p)
  order := f.order
  unique := f.unique
  cover := f.cover
  net := f.net

/-- A variable is a wire connecting the root to its sole named leaf. -/
def var (x : ν) : TermFragment arity ν where
  Cell := Fin 0
  cellEnum := inferInstance
  Leaf := Unit
  leafEnum := inferInstance
  label := Fin.elim0
  name _ := x
  order := [()]
  unique := by simp
  cover p := by cases p; exact List.mem_cons_self
  net := PortNet.identity arity Unit

/-- The parent cell is followed by the indexed families of child cells. -/
def agentLabel (a : α) (f : Fin (arity a) → TermFragment arity ν) :
    Unit ⊕ (Σ i, (f i).Cell) → α := Sum.elim (fun _ ↦ a) (fun c ↦ (f c.1).label c.2)

/-- Replace each child's root boundary by the corresponding parent auxiliary port. -/
def agentEndpointEquiv (a : α) (f : Fin (arity a) → TermFragment arity ν) :
    (Unit ⊕ Unit) ⊕ (Σ i, Endpoint arity (f i).label (Unit ⊕ (f i).Leaf)) ≃
      Endpoint arity (agentLabel a f) (Unit ⊕ (Σ i, (f i).Leaf)) where
  toFun p := match p with
    | .inl (.inl _) => .inl (.inl ())
    | .inl (.inr _) => .inr ⟨.inl (), 0⟩
    | .inr ⟨i, .inl (.inl _)⟩ => .inr ⟨.inl (), i.succ⟩
    | .inr ⟨i, .inl (.inr p)⟩ => .inl (.inr ⟨i, p⟩)
    | .inr ⟨i, .inr ⟨c, p⟩⟩ => .inr ⟨.inr ⟨i, c⟩, p⟩
  invFun p := match p with
    | .inl (.inl _) => .inl (.inl ())
    | .inl (.inr ⟨i, p⟩) => .inr ⟨i, .inl (.inr p)⟩
    | .inr ⟨.inl _, p⟩ => Fin.cases (.inl (.inr ()))
        (fun i ↦ .inr ⟨i, .inl (.inl ())⟩) p
    | .inr ⟨.inr ⟨i, c⟩, p⟩ => .inr ⟨i, .inr ⟨c, p⟩⟩
  left_inv p := by
    rcases p with (u | v) | ⟨i, (u | p) | ⟨c, p⟩⟩ <;> rfl
  right_inv p := by
    rcases p with (u | ⟨i, p⟩) | ⟨u | ⟨i, c⟩, p⟩
    · rfl
    · rfl
    · exact Fin.cases rfl (fun _ ↦ rfl) p
    · rfl

/-- A single root-to-principal wire, before its endpoints are placed in the parent graph. -/
def rootWire : Wiring (Unit ⊕ Unit) where
  partner := Sum.swap
  involutive p := by cases p <;> rfl
  fixedPointFree p h := by cases p <;> cases h

/-- Enumerate the child leaves in port order, retaining each child's internal leaf order. -/
def agentOrder (a : α) (f : Fin (arity a) → TermFragment arity ν) :
    List (Σ i, (f i).Leaf) :=
  (List.finRange (arity a)).flatMap fun i ↦ (f i).order.map (Sigma.mk i)

/-- Combining distinct child positions cannot duplicate a leaf occurrence. -/
theorem agentOrder_unique (a : α) (f : Fin (arity a) → TermFragment arity ν) :
    (agentOrder a f).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro i _
    exact (f i).unique.map (fun _ _ h ↦ eq_of_heq (Sigma.mk.inj_iff.mp h).2)
  · apply (List.nodup_finRange (arity a)).imp
    intro i j hij x hx y hy hxy
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hy
    exact hij (congrArg Sigma.fst hxy)

/-- Every child leaf occurs in the combined syntax order. -/
theorem agentOrder_cover (a : α) (f : Fin (arity a) → TermFragment arity ν)
    (p : Σ i, (f i).Leaf) : p ∈ agentOrder a f :=
  List.mem_flatMap.mpr ⟨p.1, List.mem_finRange p.1,
    List.mem_map.mpr ⟨p.2, (f p.1).cover p.2, rfl⟩⟩

/-- Attach a parent cell to the roots of its child term graphs. -/
def agent (a : α) (f : Fin (arity a) → TermFragment arity ν) : TermFragment arity ν where
  Cell := Unit ⊕ (Σ i, (f i).Cell)
  cellEnum := let := sigmaEnum (C := fun i ↦ (f i).Cell); inferInstance
  Leaf := Σ i, (f i).Leaf
  leafEnum := sigmaEnum
  label := agentLabel a f
  name p := (f p.1).name p.2
  order := agentOrder a f
  unique := agentOrder_unique a f
  cover := agentOrder_cover a f
  net :=
    ⟨(rootWire.sum (Wiring.sigma fun i ↦ (f i).net.wiring)).map (agentEndpointEquiv a f),
      ((List.finRange (arity a)).map fun i ↦ (f i).net.loops).sum⟩

/-- Attaching a parent cell concatenates its children's ordered name occurrences. -/
theorem names_agent (a : α) (f : Fin (arity a) → TermFragment arity ν) :
    (agent a f).names = (List.ofFn fun i ↦ (f i).names).flatten := by
  simp only [names, agent, agentOrder, List.map_flatMap, List.map_map, Function.comp_def,
    List.ofFn_eq_map]
  rfl

end TermFragment

namespace Term

/-- Expose the root and all variable occurrences of an arbitrary term as graph boundaries. -/
def fragment : Term arity ν → TermFragment arity ν :=
  PFunctor.FreeM.rec TermFragment.var (fun a _ fs ↦ TermFragment.agent a fs)

/-- The graph's exposed leaves are exactly the term's ordered name occurrences. -/
theorem fragment_names (t : Term arity ν) : t.fragment.names = t.names :=
  PFunctor.FreeM.rec (fun _ ↦ rfl) (fun a ts ih ↦ by
    change (TermFragment.agent a (fun i ↦ fragment (ts i))).names =
      (List.ofFn fun i ↦ names (ts i)).flatten
    rw [TermFragment.names_agent]
    simp only [ih]) t

/-- A term tree has no closed wire component. -/
theorem fragment_loops (t : Term arity ν) : t.fragment.net.loops = 0 :=
  PFunctor.FreeM.rec (fun _ ↦ rfl) (fun a ts ih ↦ by
    change ((List.finRange (arity a)).map fun i ↦ (fragment (ts i)).net.loops).sum = 0
    simp [ih]) t

/-- Renaming syntax variables changes only the names of the graph's exposed leaves. -/
theorem fragment_rename (σ : ν → μ) (t : Term arity ν) :
    (t.subst (fun x ↦ var (σ x))).fragment = t.fragment.rename σ :=
  PFunctor.FreeM.rec (fun _ ↦ rfl) (fun a ts ih ↦ by
    change TermFragment.agent a (fun i ↦ fragment (subst (fun x ↦ var (σ x)) (ts i))) =
      (TermFragment.agent a (fun i ↦ fragment (ts i))).rename σ
    simp only [ih]
    have he : TermFragment.agentEndpointEquiv a (fun i ↦ (fragment (ts i)).rename σ) =
        TermFragment.agentEndpointEquiv a (fun i ↦ fragment (ts i)) := by
      apply Equiv.ext
      intro p
      rcases p with (u | v) | ⟨i, (u | p) | ⟨c, p⟩⟩ <;> rfl
    simp only [TermFragment.agent]
    rw [he]
    rfl) t

end Term

end Geb.InteractionNet

end
