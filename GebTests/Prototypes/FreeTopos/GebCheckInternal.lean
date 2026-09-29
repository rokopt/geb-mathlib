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
Geb program represents them.

## Main definitions

* {lit}`encTerm`, {lit}`encDeriv` — terms and derivations as trees.
* {lit}`encGlobals`, {lit}`encDecl`, {lit}`encState` — constants, declarations and the state of a
  development as trees.

## Tags

internal language, proof checker, differential testing, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.GebCheckInternal

open Geb Geb.PartialHorn Geb.FreeTopos GebTests.Prototypes.FreeTopos.GebCheck

/-- The language and the checker of derivations. -/
def languageGeb : String := include_str "../../../bootstrap/free-topos/language.geb"

/-- The checker of derivations and developments. -/
def derivationGeb : String := include_str "../../../bootstrap/free-topos/derivation.geb"

/-- The program: the metalogic's checker, the language and the checker of derivations. -/
def internalProgram : String := program ++ languageGeb ++ "\n" ++ derivationGeb ++ "\n"

/-- The position of a label's constructor, and its data. -/
def labelData : Internal.Label → ℕ × List Tree
  | .var i => (0, [Kernel.leaf i])
  | .star => (1, [])
  | .pair => (2, [])
  | .fst => (3, [])
  | .snd => (4, [])
  | .lam a => (5, [a])
  | .app => (6, [])
  | .arr k θ => (7, [Kernel.leaf k, RoseTree.node 0 θ])
  | .natRec => (8, [])
  | .listRec => (9, [])
  | .roseRec c => (10, [c])
  | .defn k θ => (11, [Kernel.leaf k, RoseTree.node 0 θ])
  | .eq => (12, [])

/-- A term as the node of its label's position over the node of the label's data and its
children. -/
def encTerm : Internal.Term → Tree :=
  RoseTree.elim fun l cs ↦ RoseTree.node (labelData l).1 (RoseTree.node 0 (labelData l).2 :: cs)

/-- The position of a rule's constructor, and its data. -/
def ruleData : Internal.Rule → ℕ × List Tree
  | .refl => (0, [])
  | .trans => (1, [])
  | .cong => (2, [])
  | .beta => (3, [])
  | .fstPair => (4, [])
  | .sndPair => (5, [])
  | .pairEta => (6, [])
  | .unitEta => (7, [])
  | .delta => (8, [])
  | .natZero k => (9, [Kernel.leaf k])
  | .natSucc k => (10, [Kernel.leaf k])
  | .listNil k => (11, [Kernel.leaf k])
  | .listCons k => (12, [Kernel.leaf k])
  | .roseNode kn kl kc => (13, [Kernel.leaf kn, Kernel.leaf kl, Kernel.leaf kc])
  | .caseInl kc kl => (14, [Kernel.leaf kc, Kernel.leaf kl])
  | .caseInr kc kr => (15, [Kernel.leaf kc, Kernel.leaf kr])
  | .thm j θ σ flip =>
    (16, [Kernel.leaf j, RoseTree.node 0 θ, RoseTree.node 0 (σ.map encTerm), encBool flip])
  | .rwHyp i flip => (17, [Kernel.leaf i, encBool flip])
  | .join => (18, [])
  | .natInd kz ks s => (19, [Kernel.leaf kz, Kernel.leaf ks, encTerm s])
  | .listInd kn kc s => (20, [Kernel.leaf kn, Kernel.leaf kc, encTerm s])
  | .hyp i => (21, [Kernel.leaf i])
  | .cut φ => (22, [encTerm φ])
  | .conv => (23, [])
  | .convFrom φ => (24, [encTerm φ])
  | .propExt => (25, [])
  | .funExt => (26, [])
  | .apply j θ σ => (27, [Kernel.leaf j, RoseTree.node 0 θ, RoseTree.node 0 (σ.map encTerm)])
  | .natIndHyp kz ks => (28, [Kernel.leaf kz, Kernel.leaf ks])
  | .listIndHyp kn kc => (29, [Kernel.leaf kn, Kernel.leaf kc])
  | .cert c => (30, [c])
  | .certSeq c => (31, [c])
  | .roseInd kn kl kc s => (32, [Kernel.leaf kn, Kernel.leaf kl, Kernel.leaf kc, encTerm s])
  | .roseIndHyp kn kl kc => (33, [Kernel.leaf kn, Kernel.leaf kl, Kernel.leaf kc])
  | .coprodInd kl kr => (34, [Kernel.leaf kl, Kernel.leaf kr])
  | .zeroInd i => (35, [Kernel.leaf i])
  | .quotInd kq θ => (36, [Kernel.leaf kq, RoseTree.node 0 θ])

/-- A derivation as the node of its rule's position over the node of the rule's data and its
children. -/
def encDeriv : Internal.Deriv → Tree :=
  RoseTree.elim fun r cs ↦ RoseTree.node (ruleData r).1 (RoseTree.node 0 (ruleData r).2 :: cs)

/-- A primitive arrow as the node of its arity, arrow, domain and codomain. -/
def encPrim (p : Internal.Prim) : Tree :=
  RoseTree.node 0 [Kernel.leaf p.arity, p.arrow, p.dom, p.cod]

/-- A definition of the language as the node of its arity, its parameters' types, its type and
its body. -/
def encLDefn (d : Internal.Defn) : Tree :=
  RoseTree.node 0 [Kernel.leaf d.arity, RoseTree.node 0 d.params, d.type, encTerm d.body]

/-- A definition of either kind as the node of its kind's position over its fields. -/
def encDefinition : Internal.Definition → Tree
  | .language d => RoseTree.node 0 [encLDefn d]
  | .object m b => RoseTree.node 1 [Kernel.leaf m, b]

/-- The constants as the node of the node of the primitive arrows, the node of the definitions
and the index of the first definition's operation. -/
def encGlobals (G : Internal.Globals) : Tree :=
  RoseTree.node 0 [RoseTree.node 0 (G.prims.map encPrim),
    RoseTree.node 0 (G.defs.map encDefinition), Kernel.leaf G.base]

/-- A theorem as the node of its arity, context, hypotheses and conclusion. -/
def encThm (a : Internal.Thm) : Tree :=
  RoseTree.node 0 [Kernel.leaf a.arity, RoseTree.node 0 a.ctx,
    RoseTree.node 0 (a.hyps.map encTerm), encTerm a.concl]

/-- An entry as the node of its kind's position over its theorem or sequent. -/
def encEntry : Internal.Entry → Tree
  | .language a => RoseTree.node 0 [encThm a]
  | .combinators s => RoseTree.node 1 [encSeq s]

/-- A declaration as the node of its constructor's position over its fields. -/
def encDecl : Internal.Decl → Tree
  | .language a d => RoseTree.node 0 [encThm a, encDeriv d]
  | .combinators s c => RoseTree.node 1 [encSeq s, c]
  | .definition d => RoseTree.node 2 [encLDefn d]
  | .constant p c => RoseTree.node 3 [encPrim p, encOpt c]
  | .object m b c => RoseTree.node 4 [Kernel.leaf m, b, encOpt c]
  | .quotient n A R => RoseTree.node 5 [Kernel.leaf n, A, encTerm R]
  | .descent kq C h jr => RoseTree.node 6 [Kernel.leaf kq, C, encTerm h, Kernel.leaf jr]

/-- The state of a development as the pair of its constants and the node of its entries. -/
def encState (s : Internal.Globals × Array Internal.Entry) : Tree :=
  RoseTree.node 0 [encGlobals s.1, RoseTree.node 0 (s.2.toList.map encEntry)]

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
#guard ((loaded GoedelT.ProofTests.bundler.toList internalProgram.toList).bind fun P ↦ do
  let cd : Tree → List Tree → List Tree → Tree ←
    fn P "checkDev".toList (arrow tyT (arrow tyTs (arrow tyTs tyT)))
  pure <| developments.all fun (_, G, ds) ↦ (Internal.checkDev G #[] ds).isSome &&
    cd (encGlobals G) [] (ds.map encDecl) == encOpt ((Internal.checkDev G #[] ds).map encState)
  ).getD false

-- the checker of developments at every development of at most sixteen declarations with each
-- declaration removed
#guard ((loaded GoedelT.ProofTests.bundler.toList internalProgram.toList).bind fun P ↦ do
  let cd : Tree → List Tree → List Tree → Tree ←
    fn P "checkDev".toList (arrow tyT (arrow tyTs (arrow tyTs tyT)))
  pure <| developments.all fun (_, G, ds) ↦ ds.length > 16 ||
    (List.range ds.length).all fun i ↦
      cd (encGlobals G) [] ((ds.eraseIdx i).map encDecl) ==
        encOpt ((Internal.checkDev G #[] (ds.eraseIdx i)).map encState)).getD false

-- one declaration's check at each variant, in the state before the declaration it varies
#guard ((loaded GoedelT.ProofTests.bundler.toList internalProgram.toList).bind fun P ↦ do
  let st : Tree → List Tree → Tree → Tree ←
    fn P "declStep".toList (arrow tyT (arrow tyTs (arrow tyT tyT)))
  pure <| variants.all fun (d, G, E) ↦
    st (encGlobals G) (E.toList.map encEntry) (encDecl d) == encOpt ((d.step G E).map encState)
  ).getD false

end GebTests.Prototypes.FreeTopos.GebCheckInternal

end
