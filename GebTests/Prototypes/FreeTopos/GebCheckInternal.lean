/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.GebCheck
public meta import GebTests.Prototypes.FreeTopos.GebCheck -- shake: keep
public import GebTests.Prototypes.FreeTopos.InternalCitations
public meta import GebTests.Prototypes.FreeTopos.InternalCitations -- shake: keep
public import GebTests.Prototypes.FreeTopos.InternalCompleteness
public meta import GebTests.Prototypes.FreeTopos.InternalCompleteness -- shake: keep
public import GebTests.Prototypes.FreeTopos.InternalConstants
public meta import GebTests.Prototypes.FreeTopos.InternalConstants -- shake: keep
public import GebTests.Prototypes.FreeTopos.InternalCoproducts
public meta import GebTests.Prototypes.FreeTopos.InternalCoproducts -- shake: keep
public import GebTests.Prototypes.FreeTopos.InternalDerivation
public meta import GebTests.Prototypes.FreeTopos.InternalDerivation -- shake: keep
public import GebTests.Prototypes.FreeTopos.InternalLogic
public meta import GebTests.Prototypes.FreeTopos.InternalLogic -- shake: keep
public import GebTests.Prototypes.FreeTopos.InternalQuotients
public meta import GebTests.Prototypes.FreeTopos.InternalQuotients -- shake: keep
public import GebTests.Prototypes.FreeTopos.InternalRoseTrees
public meta import GebTests.Prototypes.FreeTopos.InternalRoseTrees -- shake: keep

set_option doc.verso true in
/-!
# The internal language's checker written in Geb, compared with Lean's

The internal language's terms, their compilation to the combinators, and the checker of its
derivations and developments, written in the datatype language ({lit}`bootstrap/free-topos/`), are
read by the stage-0 compiler's front end with the metalogic's checker and loaded by the kernel, and
compared with the Lean definitions they transcribe at the developments of the test modules of the
internal language and at variants of each with a declaration removed. Inputs are encoded as the
Geb program represents them, by the encodings of
{lit}`GebTests.Prototypes.FreeTopos.Agreement.Encode`.

## Main definitions

* {lit}`developments` — the developments of the test modules, each with its constants.
* {lit}`alterations`, {lit}`subVariants` — the alterations of a declaration, and the variants of a
  declaration of the language with its derivation replaced by a proper subtree.
* {lit}`variants` — declarations with the states before them, the checkers compared at each.

## Tags

internal language, proof checker, differential testing, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.GebCheckInternal

open Geb Geb.PartialHorn Geb.FreeTopos GebTests.Prototypes.FreeTopos.GebCheck
  GebTests.Prototypes.FreeTopos.Agreement.Encode

/-- The language and the checker of derivations. -/
def languageGeb : String := include_str "../../../bootstrap/free-topos/language.geb"

/-- The checker of derivations and developments. -/
def derivationGeb : String := include_str "../../../bootstrap/free-topos/derivation.geb"

/-- The program: the metalogic's checker, the language and the checker of derivations. -/
def internalProgram : String := program ++ languageGeb ++ "\n" ++ derivationGeb ++ "\n"

/-- The developments of the test modules of the internal language, each with its constants. -/
def developments : List (String × Internal.Globals × List Internal.Decl) :=
  [("derivation", Internal.G, InternalDerivation.development.getD []),
   ("logic", InternalLogic.GL, InternalLogic.development.getD []),
   ("coproducts", InternalCoproducts.GC,
     InternalCoproducts.theorems.map fun (a, d) ↦ .language a d),
   ("rose trees", InternalRoseTrees.GR,
     InternalRoseTrees.theorems.map fun (a, d) ↦ .language a d),
   ("citations", Internal.G, InternalCitations.development.getD []),
   ("completeness", Internal.G, InternalCompleteness.development.getD []),
   ("constants", Internal.G, InternalConstants.development.getD []),
   ("quotients", Internal.G, InternalQuotients.development.getD [])]

/-- The proper subtrees of a derivation. -/
def subderivs : Internal.Deriv → List Internal.Deriv :=
  RoseTree.para fun _ cs ↦ cs.flatMap fun (c, r) ↦ c :: r

/-- A certificate removed where there is one, and a leaf of label zero where there is none. -/
def toggle : Option Tree → Option Tree
  | some _ => none
  | none => some (Kernel.leaf 0)

/-- The alterations of a declaration: an equation's sides exchanged, a type, an arity, an object
or an index changed, or a certificate removed or supplied. -/
def alterations : Internal.Decl → List Internal.Decl
  | .language a d => (Internal.eqParts a.concl).toList.map fun (t, u) ↦
      .language { a with concl := Internal.Term.eq u t } d
  | .combinators s c => [.combinators { s with concl := ⟨s.concl.rhs, s.concl.lhs⟩ } c]
  | .definition d =>
    [.definition { d with type := one }, .definition { d with arity := d.arity + 1 }]
  | .constant p c => [.constant p (toggle c), .constant { p with cod := p.dom } c]
  | .object m b c => [.object m b (toggle c), .object (m + 1) b c]
  | .quotient n A R => [.quotient n nat R, .quotient (n + 1) A R]
  | .descent kq C h jr => [.descent kq C h (jr + 1), .descent kq nat h jr]

/-- The variants of a declaration of the language: its derivation replaced by each proper
subtree. -/
def subVariants : Internal.Decl → List Internal.Decl
  | .language a d => (subderivs d).map (.language a)
  | _ => []

/-- A declaration, and the state of a development before it. -/
abbrev Staged : Type := Internal.Decl × Internal.Globals × Array Internal.Entry

/-- One declaration's check, recording the state before it. -/
def stageStep (acc : List Staged × Internal.Globals × Array Internal.Entry) (d : Internal.Decl) :
    Option (List Staged × Internal.Globals × Array Internal.Entry) :=
  (d.step acc.2.1 acc.2.2).map fun s ↦ (acc.1 ++ [(d, acc.2)], s)

/-- The state of a development before each of its declarations, where each checks. -/
def withStates (G : Internal.Globals) (ds : List Internal.Decl) : Option (List Staged) :=
  (ds.foldlM stageStep ([], G, #[])).map Prod.fst

/-- The variants compared, each with the state it is checked in: in a development of at most
sixteen declarations, each declaration's alterations and subtree variants; in a larger one, the
alterations of each declaration that is not a theorem or a sequent, and of every thirty-second. -/
def variants : List Staged :=
  developments.flatMap fun (_, G, ds) ↦ ((withStates G ds).getD []).zipIdx.flatMap
    fun ((d, s), i) ↦ (if ds.length ≤ 16 then alterations d ++ subVariants d
      else match d with
        | .language _ _ | .combinators _ _ => if i % 32 = 0 then alterations d else []
        | _ => alterations d).map (·, s)

-- the checker of developments at every development, which the Lean checker accepts
#guard ((loaded Geb.Kernel.Stage0Tests.bundler.toList internalProgram.toList).bind fun P ↦ do
  let cd : Tree → List Tree → List Tree → Tree ←
    fn P "Derivation.checkDev".toList (arrow tyT (arrow tyTs (arrow tyTs tyT)))
  pure <| developments.all fun (_, G, ds) ↦ (Internal.checkDev G #[] ds).isSome &&
    cd (encGlobals G) [] (ds.map encDecl) == encOpt ((Internal.checkDev G #[] ds).map encState)
  ).getD false

-- the checker of developments at every development of at most sixteen declarations with each
-- declaration removed
#guard ((loaded Geb.Kernel.Stage0Tests.bundler.toList internalProgram.toList).bind fun P ↦ do
  let cd : Tree → List Tree → List Tree → Tree ←
    fn P "Derivation.checkDev".toList (arrow tyT (arrow tyTs (arrow tyTs tyT)))
  pure <| developments.all fun (_, G, ds) ↦ ds.length > 16 ||
    (List.range ds.length).all fun i ↦
      cd (encGlobals G) [] ((ds.eraseIdx i).map encDecl) ==
        encOpt ((Internal.checkDev G #[] (ds.eraseIdx i)).map encState)).getD false

-- one declaration's check at each variant, in the state before the declaration it varies
#guard ((loaded Geb.Kernel.Stage0Tests.bundler.toList internalProgram.toList).bind fun P ↦ do
  let st : Tree → List Tree → Tree → Tree ←
    fn P "Derivation.declStep".toList (arrow tyT (arrow tyTs (arrow tyT tyT)))
  pure <| variants.all fun (d, G, E) ↦
    st (encGlobals G) (E.toList.map encEntry) (encDecl d) == encOpt ((d.step G E).map encState)
  ).getD false

end GebTests.Prototypes.FreeTopos.GebCheckInternal

end
