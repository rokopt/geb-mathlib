/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal -- shake: keep
public meta import Geb.Prototypes.FreeTopos.Internal -- shake: keep

set_option doc.verso true in
/-!
# The internal language's definitions and equations, compiled

Appending lists and addition, defined in the internal language by folds into exponentials, and
the equations of the computational core's theorems about them, stated in the internal language.
The definitions compile to well-formed definitions of the combinators whose arrows have the types
they name, and the equations, and their unfoldings, compile to sequents of the combinators.

## Main definitions

* {lit}`defs` — appending and addition.
* {lit}`statements` — the equations, each in its context.

## Tags

internal language, compilation, definition, lists, natural numbers
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Internal

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Sorts
open Geb.FreeTopos.Internal (Term compileDefs compileEq unfold unfoldBodies)

/-- The element type of the lists, the object variable. -/
def A : Tree := x 0

/-- The list object of the element type. -/
def L : Tree := list A

/-- The primitive arrows: the empty list and the construction of a list, of an object
parameter, zero and the successor. -/
def prims : List Internal.Prim := [
  ⟨1, nil (x 0), one, list (x 0)⟩,
  ⟨1, cons (x 0), prod (x 0) (list (x 0)), list (x 0)⟩,
  ⟨0, zeroN, one, nat⟩,
  ⟨0, succ, nat, nat⟩]

/-- The empty list. -/
def nilT : Term := Term.arr 0 [A] Term.star

/-- The list of an element before a list. -/
def consT (h t : Term) : Term := Term.arr 1 [A] (Term.pair h t)

/-- Zero. -/
def zeroT : Term := Term.arr 2 [] Term.star

/-- The successor of a number. -/
def succT (n : Term) : Term := Term.arr 3 [] n

/-- Appending two lists: the fold of the first into functions of the second. -/
def appendD : Internal.Defn := ⟨1, [L, L], L,
  Term.app (Term.listRec (Term.lam L (Term.var 0))
      (Term.lam L (consT (Term.var 2) (Term.app (Term.var 1) (Term.var 0)))) (Term.var 1))
    (Term.var 0)⟩

/-- Adding two numbers: the fold of the second into functions of the first. -/
def addD : Internal.Defn := ⟨0, [nat, nat], nat,
  Term.app (Term.natRec (Term.lam nat (Term.var 0))
      (Term.lam nat (succT (Term.app (Term.var 1) (Term.var 0)))) (Term.var 0))
    (Term.var 1)⟩

/-- The definitions. -/
def defs : List Internal.Defn := [appendD, addD]

/-- The constants: the primitive arrows and the definitions, whose operations follow the
signature's. -/
def G : Internal.Globals := ⟨prims, defs, sig.length⟩

/-- The application of appending to two lists. -/
def appendT (xs ys : Term) : Term := Term.defn 0 [A] [ys, xs]

/-- The application of addition to two numbers. -/
def addT (m n : Term) : Term := Term.defn 1 [] [n, m]

/-- The equations of the computational core's theorems, each with its number of object
variables and its context. -/
def statements : List (ℕ × List Tree × Term × Term) := [
  (1, [L], appendT nilT (Term.var 0), Term.var 0),
  (1, [L], appendT (Term.var 0) nilT, Term.var 0),
  (1, [L, L, L], appendT (appendT (Term.var 2) (Term.var 1)) (Term.var 0),
    appendT (Term.var 2) (appendT (Term.var 1) (Term.var 0))),
  (1, [L], appendT (appendT (Term.var 0) nilT) nilT, Term.var 0),
  (0, [nat], addT (Term.var 0) zeroT, Term.var 0),
  (0, [nat, nat], addT (Term.var 1) (succT (Term.var 0)), succT (addT (Term.var 1) (Term.var 0))),
  (0, [nat], addT zeroT (Term.var 0), Term.var 0)]

-- the definitions compile, each to a well-formed definition of the combinators over the
-- signature the earlier ones extend, and the constants are well formed, the primitive arrows
-- of the types they name
#guard (compileDefs G).any fun cs ↦
  cs.zipIdx.all (fun (d, i) ↦
    sortOf (sig ++ (cs.take i).map fun d ↦ (d.ctx, d.sort)) d.ctx d.body == some d.sort &&
      (List.range d.ctx.length).all fun j ↦ Occurs j d.body) &&
    G.ok (ExtEnv.ofDefs cs)

-- each equation compiles to a well-sorted sequent of the extension by the definitions, as does
-- its unfolding
#guard (compileDefs G).any fun cs ↦ statements.all fun (n, Γ, t, u) ↦
  let S := sig ++ cs.map fun d ↦ (d.ctx, d.sort)
  let ok (t u : Term) := (compileEq G n Γ t u).any fun a ↦
    sortOf S a.ctx a.concl.lhs == some arr && sortOf S a.ctx a.concl.rhs == some arr
  let ubs := unfoldBodies defs
  ok t u && ok (unfold ubs t) (unfold ubs u)

end GebTests.Prototypes.FreeTopos.Internal

end
