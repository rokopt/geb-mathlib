/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Composition
public import GebTests.Prototypes.FreeTopos.Stored

set_option doc.verso true in
/-!
# Developments proving theorems

A development of the internal language proves a theorem when the checker
({name}`Geb.FreeTopos.Internal.checkDev`) accepts it from no entries and its last declaration
states the theorem. The modules of {lit}`GebTests.Prototypes.FreeTopos.Certified` state, for each
development whose certificate {lit}`bootstrap/certificates/` stores, that it proves its theorem in
the program the theorem is about. The statement is decided by Lean's evaluator, and declared by
the command {lit}`evaluation_axiom` as an axiom after the evaluation accepts it, in either loading
mode: the kernel's reduction of a check of that size is out of reach. The axioms are permitted by
the axiom linter in the modules of {lit}`GebMeta.evaluationAxiomModules` alone.

## Main definitions

* {lit}`Proves` — a development proves a theorem.
* {lit}`proves` — its decision.
* {lit}`provedIn` — the decision in a program where one is given.
* {lit}`Checks`, {lit}`checkedIn` — a development checks, and the decision in a program.
* {lit}`checkedAfterIn` — the decision that a development checks after the theorems of others.
* {lit}`statesLastIn` — the decision that a development's last declaration states a theorem.
* {lit}`ProgramModel` — a model of a program's constants, in which developments' theorems are valid.
* {lit}`ofText` — the declarations a certificate's text stores.

## Main statements

* {lit}`proves_eq_true`, {lit}`provedIn_eq_true` — a development the decision accepts proves
  the theorem.
* {lit}`checkedIn_eq_true` — a development the decision accepts checks.

## Tags

internal language, development, certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified

open Geb Geb.FreeTopos
open Internal (Thm Decl Globals checkDev thmsOf)
open scoped FinEnum

/-- Theorems are equal when their arities, contexts, hypotheses and conclusions are. -/
instance decEqThm : DecidableEq Thm
  | ⟨n, c, h, φ⟩, ⟨n', c', h', φ'⟩ =>
    if e : n = n' ∧ c = c' ∧ h = h' ∧ φ = φ' then
      isTrue (by obtain ⟨rfl, rfl, rfl, rfl⟩ := e; rfl)
    else isFalse fun h₀ ↦ e (by cases h₀; exact ⟨rfl, rfl, rfl, rfl⟩)

/-- A development proves a theorem: the checker accepts it from no entries, and its last
declaration states the theorem. -/
def Proves (G : Globals) (ds : List Decl) (a : Thm) : Prop :=
  (checkDev G #[] ds).isSome = true ∧ ∃ d, ds.getLast? = some (.language a d)

/-- Whether a development proves a theorem. -/
def proves (G : Globals) (ds : List Decl) (a : Thm) : Bool :=
  (checkDev G #[] ds).isSome && match ds.getLast? with
    | some (.language a' _) => decide (a' = a)
    | _ => false

/-- A development the decision accepts proves the theorem. -/
theorem proves_eq_true {G : Globals} {ds : List Decl} {a : Thm} (h : proves G ds a = true) :
    Proves G ds a := by
  simp only [proves, Bool.and_eq_true] at h
  refine ⟨h.1, ?_⟩
  obtain ⟨-, h⟩ := h
  split at h
  · next a' d hl => exact ⟨d, by rw [hl, of_decide_eq_true h]⟩
  · exact absurd h Bool.false_ne_true

/-- Whether a development proves, in a program where one is given, the statement about it. -/
def provedIn {α : Type} (o : Option α) (G : α → Globals) (ds : List Decl) (a : α → Thm) : Bool :=
  match o with
  | some P => proves (G P) ds (a P)
  | none => false

/-- A development the decision accepts in a given program proves the statement about it. -/
theorem provedIn_eq_true {α : Type} {o : Option α} {G : α → Globals} {ds : List Decl}
    {a : α → Thm} (h : provedIn o G ds a = true) : ∃ P, o = some P ∧ Proves (G P) ds (a P) := by
  cases o with
  | some P => exact ⟨P, rfl, proves_eq_true h⟩
  | none => exact absurd h Bool.false_ne_true

/-- A development checks: the checker accepts it from no entries. -/
def Checks (G : Globals) (ds : List Decl) : Prop := (checkDev G #[] ds).isSome = true

/-- Whether a development checks in a program where one is given. -/
def checkedIn {α : Type} (o : Option α) (G : α → Globals) (ds : List Decl) : Bool :=
  match o with
  | some P => (checkDev (G P) #[] ds).isSome
  | none => false

/-- A development the decision accepts in a given program checks there. -/
theorem checkedIn_eq_true {α : Type} {o : Option α} {G : α → Globals} {ds : List Decl}
    (h : checkedIn o G ds = true) : ∃ P, o = some P ∧ Checks (G P) ds := by
  cases o with
  | some P => exact ⟨P, rfl, h⟩
  | none => exact absurd h Bool.false_ne_true

/-- Whether a development of theorems checks, after the theorems of the given declarations, in a
program where one is given. -/
def checkedAfterIn {α : Type} (o : Option α) (G : α → Globals) (before ds : List Decl) : Bool :=
  match o with
  | some P => Internal.checkAfter (G P) (thmsOf before) ds
  | none => false

/-- A development the decision accepts in a program checks after the theorems given there. -/
theorem checkedAfterIn_some {α : Type} {o : Option α} {P : α} {G : α → Globals}
    {before ds : List Decl} (ho : o = some P) (h : checkedAfterIn o G before ds = true) :
    Internal.checkAfter (G P) (thmsOf before) ds = true := by
  subst ho
  exact h

/-- Whether the last declaration of a development states a theorem, in a program where one is
given. -/
def statesLastIn {α : Type} (o : Option α) (ds : List Decl) (a : α → Thm) : Bool :=
  match o, ds.getLast? with
  | some P, some (.language a' _) => decide (a' = a P)
  | _, _ => false

/-- The theorem the last declaration of a development states is among its theorems. -/
theorem mem_thmsOf_of_statesLastIn {α : Type} {o : Option α} {P : α} {ds : List Decl}
    {a : α → Thm} (ho : o = some P) (h : statesLastIn o ds a = true) : a P ∈ thmsOf ds := by
  subst ho
  simp only [statesLastIn] at h
  cases hl : ds.getLast? with
  | none => simp [hl] at h
  | some e =>
    cases e with
    | language a' d =>
      have ha : a' = a P := by simpa [hl] using h
      subst ha
      exact List.mem_filterMap.mpr ⟨.language _ d, List.mem_of_getLast? hl, rfl⟩
    | _ => simp [hl] at h

universe v

/-- A model of a program's constants: of the theory extended by the definitions the constants
compile to, in which their invariant holds with no entries. -/
structure ProgramModel (G : Globals) : Type (v + 1) where
  /-- The combinators' definitions before the constants'. -/
  pre : List PartialHorn.Defn
  /-- The definitions the constants compile to. -/
  defs : List PartialHorn.Defn
  /-- The model. -/
  M : PartialHorn.Model.{v} (ext (pre ++ defs)).sig
  /-- It is a model of the extended theory. -/
  isModel : PartialHorn.IsModel (ext (pre ++ defs)) M
  /-- The constants compile. -/
  compiles : Internal.compileDefs G = some defs
  /-- The constants come after the combinators' definitions. -/
  base : G.base = sig.length + pre.length
  /-- The invariant of the constants, with no entries. -/
  inv : Internal.DevInv M G G #[]

/-- The theorems of the given declarations are valid in the model. -/
def ProgramModel.Valid {G : Globals} (m : ProgramModel.{v} G) (ds : List Decl) : Prop :=
  ∀ a ∈ thmsOf ds, a.Valid m.M G

/-- The theorems of two developments are valid where those of each are. -/
theorem ProgramModel.Valid.append {G : Globals} {m : ProgramModel.{v} G} {xs ys : List Decl}
    (hx : m.Valid xs) (hy : m.Valid ys) : m.Valid (xs ++ ys) := fun a ha ↦ by
  simp only [thmsOf, List.filterMap_append, List.mem_append] at ha
  exact ha.elim (hx a) (hy a)

/-- The theorems of a development that checks after the theorems of valid declarations are valid
({name}`Geb.FreeTopos.Internal.valid_of_checkAfter`). -/
theorem ProgramModel.Valid.after {G : Globals} {m : ProgramModel.{v} G} {before ds : List Decl}
    (hb : m.Valid before) (h : Internal.checkAfter G (thmsOf before) ds = true) : m.Valid ds :=
  Internal.valid_of_checkAfter m.isModel m.compiles m.base m.inv hb h

/-- The declarations a certificate's text stores, none where it stores none. -/
def ofText (s : String) : List Decl := (Stored.declsOfText s).getD []

end GebTests.Prototypes.FreeTopos.Certified

end
