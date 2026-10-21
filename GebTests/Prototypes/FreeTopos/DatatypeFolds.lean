/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.DatatypeAssembly
public meta import GebTests.Prototypes.FreeTopos.DatatypeAssembly -- shake: keep
public import GebTests.Prototypes.FreeTopos.NormalizationRel
public meta import GebTests.Prototypes.FreeTopos.NormalizationRel -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The datatype language's soundness at the kernel's constants

The constants of the kernel but the primitives, the folds of trees, iteration, the right fold of
lists and case analysis of lists, related at their types in the datatype language
({lit}`GebTests.Prototypes.FreeTopos.DatatypeBase`): the lemmas of the normalization proof on the
evaluator's folds and constants ({name}`GebTests.Prototypes.FreeTopos.Normalization.constDev`,
{name}`GebTests.Prototypes.FreeTopos.Normalization.foldRelDev`) at the relation at the datatype
language's types ({lit}`relTSpec`). The types a constant carries are quantified apart from the types
it is related at: the evaluator reads a fold's type only into the empty list values it builds,
whose elements no type constrains, and the reader gives a constant the erasure of the type the
typing reads.

## Main definitions

* {lit}`relTSpec` — the relation at the datatype language's types, as the normalization proof's
  lemmas take a relation.
* {lit}`foldsDev3` — the development.
* {lit}`foldsCertificates` — the development, stored as the certificate {lit}`datatype-folds`.

## References

* {cite}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, datatypes, soundness, fold, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Datatypes

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Translation Geb.FreeTopos.Tactics
open GebTests.Prototypes.FreeTopos.Weakening
open scoped FinEnum

open Internal (Term)
open GebTests.Prototypes.FreeTopos.Normalization

/-- A type of the datatype language of a label over types, as the typing writes it. -/
def tyNode (l : ℕ) (tys : List Term) : Term :=
  nodeT (Term.pair (numeral l) (tys.foldr (consT treeTy) (nilT treeTy)))

/-- The relation at the datatype language's types: its context the program's definitions and the
markers of its datatypes, the evaluator's definitions the context's first component, its types
the typing's, the constants' types the typing's, the types the constants carry quantified apart,
and its equations at a node of a type those of the trees, the arrows and the lists. -/
def relTSpec (P : Prog) (T : Defs3) : RelSpec where
  ctxTy := Defs3.ctxTy
  rel := T.relT
  defs := Term.fst
  tyTree := tyNode Kernel.Label.tyTree []
  tyArrow A B := tyNode Kernel.Label.tyArrow [A, B]
  tyList A := tyNode Kernel.Label.tyList [A]
  foldTy A := pc P "Typing.foldTyOf" [A]
  iterTy A := pc P "Typing.iterTyOf" [A]
  foldrTy A B := pc P "Typing.foldrTyOf" [A, B]
  lcaseTy A B := pc P "Typing.lcaseTyOf" [A, B]
  annotated := true
  more := ["relTTree", "relTArrow", "relTList1"]
  name := (· ++ "T")

/-- The development of the constants' relations at the datatype language's types: the
normalization proof's lemmas on the evaluator's folds and on the constants but the primitives, at
the relation {name}`relTSpec`. -/
def foldsDev3 (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  constDev P S (relTSpec P T) false ++ foldRelDev P S (relTSpec P T)

/-- The development of the constants' relations ({name}`foldsDev3`), after the base's, the atom's,
the list's, the stage functions' at applications, the applications', the list expansion's and the
soundness at applications', stored as the certificate {lit}`datatype-folds`. -/
def foldsCertificates (P : Prog) (S : Defs) (T : Defs3) (before : List Internal.Thm) :
    Except String (List (String × List Internal.Decl)) := do
  let some names := listNames P S T | throw "the base is not stated"
  certifyAfter P (names ++ (stagesDev3 P S T).map (·.1) ++ (applyDev3 P S T).map (·.1) ++
    (expansionDev3 P S T).map (·.1) ++ (assemblyDev3 P S T).map (·.1)) "datatype-folds"
    (foldsDev3 P S T) before

end GebTests.Prototypes.FreeTopos.Datatypes

end
