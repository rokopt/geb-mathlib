/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Certified.Basic

set_option doc.verso true in
/-!
# Developments checked one after another

A list of developments of theorems checks in order when each checks after the theorems of given
declarations and of the developments before it in the list. One evaluation decides it
({lit}`checkedChainIn`), and the theorems of all the developments are then valid in a model in
which those of the given declarations are ({lit}`ProgramModel.Valid.chain`). A module of
{lit}`GebTests.Prototypes.FreeTopos.Certified` states in this way the check of the certificates
one search writes, in the search's order, as one fact Lean's evaluator decides.

## Main definitions

* {lit}`checkedChainIn` — whether each development of a list checks after those before it.

## Main statements

* {lit}`ProgramModel.Valid.chain` — the theorems of developments that check one after another
  are valid.
* {lit}`ProgramModel.Valid.left` — the theorems of the first of two developments are valid where
  those of both are.

## Tags

internal language, development, certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified

open Geb Geb.FreeTopos
open Internal (Decl Globals)

universe v

/-- Whether each of a list of developments of theorems checks after the theorems of the given
declarations and of the developments before it, in a program where one is given. -/
def checkedChainIn {α : Type} (o : Option α) (G : α → Globals) (dss : List (List Decl)) :
    List Decl → Bool :=
  dss.foldr (fun ds k before ↦ checkedAfterIn o G before ds && k (before ++ ds)) fun _ ↦ true

/-- The theorems of developments that check one after another, after the theorems of valid
declarations, are valid with them: by recursion on the developments, each valid after those
before it ({name}`ProgramModel.Valid.after`). -/
theorem ProgramModel.Valid.chain {α : Type} {o : Option α} {P : α} {G : α → Globals}
    (ho : o = some P) {m : ProgramModel.{v} (G P)} (dss : List (List Decl)) :
    ∀ {before : List Decl}, m.Valid before → checkedChainIn o G dss before = true →
      m.Valid (before ++ dss.flatten) :=
  List.rec (motive := fun dss ↦ ∀ {before : List Decl}, m.Valid before →
      checkedChainIn o G dss before = true → m.Valid (before ++ dss.flatten))
    (fun {before} hb _ ↦ by simpa using hb)
    (fun ds dss ih {before} hb h ↦ by
      have h' : checkedAfterIn o G before ds = true ∧
          checkedChainIn o G dss (before ++ ds) = true := by
        simpa [checkedChainIn] using h
      have hds : m.Valid ds := hb.after (checkedAfterIn_some ho h'.1)
      simpa [List.append_assoc] using ih (hb.append hds) h'.2) dss

/-- The theorems of the first of two developments are valid where those of both are. -/
theorem ProgramModel.Valid.left {G : Globals} {m : ProgramModel.{v} G} {xs ys : List Decl}
    (h : m.Valid (xs ++ ys)) : m.Valid xs := fun a ha ↦
  h a (by
    simp only [Internal.thmsOf, List.filterMap_append, List.mem_append]
    exact Or.inl ha)

end GebTests.Prototypes.FreeTopos.Certified

end
