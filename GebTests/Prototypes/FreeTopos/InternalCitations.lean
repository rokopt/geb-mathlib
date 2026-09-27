/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Prover -- shake: keep
public import GebTests.Prototypes.FreeTopos.InternalDerivation -- shake: keep
public meta import Geb.Prototypes.FreeTopos.Prover -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.InternalDerivation -- shake: keep

set_option doc.verso true in
/-!
# Citations between the internal language and the combinators

A development that mixes the two checkers. The prover's library of the combinators opens it,
its certificates citing one another; the language proves that appending the empty list to a
list gives the list, by induction on lists; the prover proves the sequent that appending the
empty list twice compiles to, rewriting with the language's theorem, which a certificate cites
by the sequent it compiles to; and the language states the same equation, proved by a
derivation that cites the prover's certificate. The development checks, and the citation of
the certificate for another equation does not.

## Main definitions

* {lit}`appendNil`, {lit}`appendNilTwice` — the theorems of the language.
* {lit}`development` — the development, its declarations of both kinds in order.

## Tags

internal language, combinators, certificate, citation, development
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.InternalCitations

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Prover Geb.FreeTopos.Sorts
open GebTests.Prototypes.FreeTopos.Internal
open Geb.FreeTopos.Internal (Term Thm Deriv Entry Decl byListInd checkThms compileDefs compileEq)
open Geb.FreeTopos.Internal.Logic (nd)

/-- The definitions of the combinators that appending and addition compile to. -/
def cds : List PartialHorn.Defn := (compileDefs G).getD []

/-- Appending the empty list to a list gives the list. -/
def appendNil : Thm := ⟨1, [L], [], Term.eq (appendT (Term.var 0) nilT) (Term.var 0)⟩

/-- Appending the empty list to a list twice gives the list. -/
def appendNilTwice : Thm :=
  ⟨1, [L], [], Term.eq (appendT (appendT (Term.var 0) nilT) nilT) (Term.var 0)⟩

/-- The development: the prover's library, the language's theorem that appending the empty list
gives the list, the prover's proof that appending it twice does by rewriting with that theorem,
and the language's statement of the latter, citing the prover's certificate. The result's last
component is the certificate the language cites. -/
def developmentWith : Option (List Decl × Tree) := do
  let (i, lib) ← libraryWith false
  let E₀ : Array Entry := (lib.map fun (s, _) ↦ Entry.combinators s).toArray
  let d₁ ← byListInd G E₀ 1 0 1 InternalDerivation.consStep
    (InternalDerivation.eqns ++ [.delta 0]) 64 [L] []
    (appendT (Term.var 0) nilT) (Term.var 0)
  let k₁ := lib.length
  let lrs := rules i ++ [deltaRule 0]
  -- the language's theorem, by the sequent it compiles to, which the prover rewrites with
  let dev₁ := lib ++ [(appendNil.seq G, RoseTree.node 0 [])]
  let q ← compileEq G 1 [L] (appendT (appendT (Term.var 0) nilT) nilT) (Term.var 0)
  let (k₂, dev₂) ← (normalizeThm lrs k₁ cds).run dev₁
  let (k₃, dev₃) ← (proveSeq q (byNorm (lrs ++ [{ src := .thm k₂ }]) q.concl) cds).run dev₂
  let c := Scope.cite ⟨[obj], []⟩ k₃
  pure (lib.map (fun (s, c) ↦ Decl.combinators s c) ++ [Decl.language appendNil d₁] ++
    (dev₃.drop (k₁ + 1)).map (fun (s, c) ↦ Decl.combinators s c) ++
    [Decl.language appendNilTwice (nd (.cert c))], c)

/-- The development. -/
def development : Option (List Decl) := developmentWith.map Prod.fst

-- the development checks, its declarations of both kinds
#guard development.any fun ds ↦ checkThms G ds #[]

-- the certificate does not prove another equation
#guard developmentWith.any fun (ds, c) ↦ !checkThms G (ds.dropLast ++
  [Decl.language ⟨1, [L], [], Term.eq (appendT (Term.var 0) nilT) nilT⟩ (nd (.cert c))]) #[]

end GebTests.Prototypes.FreeTopos.InternalCitations

end
