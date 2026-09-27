/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Graphs -- shake: keep
public meta import Geb.Prototypes.FreeTopos.Graphs -- shake: keep
public import Geb.Prototypes.FreeTopos.Prover -- shake: keep
public meta import Geb.Prototypes.FreeTopos.Prover -- shake: keep

set_option doc.verso true in
/-!
# A theorem about Lean's functions from a development of the theory

The fold of the list object of an object with the empty list and construction is the object's
identity, proved by the prover by induction through the uniqueness of the fold. At the
assignment of a type, the fold's side evaluates in the topos of types and functional relations
to the graph of the right fold of lists with the empty list and construction, and the identity's
side to the graph of the identity, so that any development of the theory that checks and proves
the sequent proves, in Lean, that the right fold is the identity.

## Main definitions

* {lit}`listRecNilCons` — the sequent.
* {lit}`development` — the library's development, extended by the sequent's proof.

## Main statements

* {lit}`foldr_cons_nil` — the right fold with the empty list and construction is the identity.

## Tags

functional relation, graph of a function, list object, soundness, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Graphs

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Prover Geb.FreeTopos.Sorts
open Geb.FreeTopos.ChosenTopos

/-- The fold of the list object of an object with the empty list and construction is its
identity. -/
def listRecNilCons : Seq :=
  ⟨[obj], [], ⟨listRec (x 0) (nil (x 0)) (cons (x 0)), idt (list (x 0))⟩⟩

/-- The library's development, its typing certified by lemmas, extended by the sequent, proved
by induction. -/
def development : Option Development := (libraryWith false).bind fun (i, d) ↦
  ((proveSeq listRecNilCons (byListInduction (rules i) (x 0) (nil (x 0)) (cons (x 0))
    listRecNilCons.concl)).run d).map Prod.snd

-- the development checks, and its last theorem is the sequent
#guard development.any fun D ↦ checkDevelopment theory D &&
  D.getLast?.any fun (a, _) ↦ a.ctx == listRecNilCons.ctx && a.hyps == listRecNilCons.hyps &&
    a.concl == listRecNilCons.concl

/-- The fold's side, at a type, is the graph of the right fold with the empty list and
construction. -/
theorem eval_lhs (α : relTopos.Obj) :
    eval relTopos.model [⟨obj, ⟨α⟩⟩] listRecNilCons.concl.lhs =
      Part.some ⟨arr, ⟨List α, List α, .ofFun (List.foldr (fun a l ↦ a :: l) [])⟩⟩ := by
  simp_terms (disch := and_intros <;> rfl) [listRecNilCons, mk_eq_some, Part.some_inj, true_and]
  exact congrArg (fun f ↦ (⟨List α, List α, f⟩ : Σ A B : Type, FunRel A B))
    (FunRel.listRec_ofFun (fun _ ↦ []) fun p ↦ p.1 :: p.2)

/-- The identity's side, at a type, is the graph of the identity. -/
theorem eval_rhs (α : relTopos.Obj) :
    eval relTopos.model [⟨obj, ⟨α⟩⟩] listRecNilCons.concl.rhs =
      Part.some ⟨arr, ⟨List α, List α, .ofFun id⟩⟩ := by
  simp_terms [listRecNilCons]
  rfl

/-- The right fold of lists with the empty list and construction is the identity, by any
development of the theory that checks and proves the sequent. -/
theorem foldr_cons_nil {D : Development} (hD : checkDevelopment theory D = true)
    (ha : listRecNilCons ∈ D.map Prod.fst) (α : Type) :
    List.foldr (fun a l ↦ a :: l) [] = (id : List α → List α) :=
  eq_of_checkDevelopment hD ha rfl (fun _ h ↦ (List.not_mem_nil h).elim) (eval_lhs α)
    (eval_rhs α)

end GebTests.Prototypes.FreeTopos.Graphs

end
