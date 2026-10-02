/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos
public import GebTests.Prototypes.FreeTopos.Agreement.Fold

set_option doc.verso true in
/-!
# The metalogic's data as the checker written in Geb represents it

The checker written in Geb, {lit}`bootstrap/free-topos/`, represents the data of the Lean
checker as trees: an optional tree as the reader represents it, a truth value as a label, a
natural number as the leaf of its label, a value of a structure or of an inductive type as the
node of its constructor's position over its fields, a list as the node of label zero over its
elements, and a term of the internal language or a derivation as the node of its label's or its
rule's position over the node of the label's or the rule's data followed by its children.

## Main definitions

* {lit}`encOpt`, {lit}`encSeq`, {lit}`encTheory`, {lit}`encExtEnv` — optional trees, sequents,
  theories and the inference's environments.
* {lit}`encTerm`, {lit}`encDeriv`, {lit}`encRule` — terms, derivations and the prover's rules.
* {lit}`encCond` — a conditional's parts, as the tactics find them.
* {lit}`encRw`, {lit}`encDevEntry`, {lit}`encLib` — the combinator prover's rewriting rules,
  developments and library.
* {lit}`encGlobals`, {lit}`encEntry`, {lit}`encDecl`, {lit}`encState` — constants, entries,
  declarations and the state of a development.

## Tags

encoding, rose tree, internal language, agreement
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Agreement.Encode

open Geb Geb.PartialHorn Geb.FreeTopos GebTests.Prototypes.FreeTopos.Agreement.Fold

/-- An optional tree as the reader represents it. -/
def encOpt : Option Tree → Tree
  | some t => RoseTree.node 1 [t]
  | none => Kernel.leaf 0

/-- An operation's signature: the node of its arguments' sorts and its sort. -/
def encOpSig (o : List ℕ × ℕ) : Tree :=
  RoseTree.node 0 [RoseTree.node 0 (o.1.map Kernel.leaf), Kernel.leaf o.2]

/-- An equation as the node of its sides. -/
def encEqn (q : Eqn) : Tree := RoseTree.node 0 [q.lhs, q.rhs]

/-- A sequent as the node of its context's sorts, its hypotheses and its conclusion. -/
def encSeq (a : Seq) : Tree :=
  RoseTree.node 0 [RoseTree.node 0 (a.ctx.map Kernel.leaf), RoseTree.node 0 (a.hyps.map encEqn),
    encEqn a.concl]

/-- A theory as the node of its signature and its axioms. -/
def encTheory (T : Theory) : Tree :=
  RoseTree.node 0 [RoseTree.node 0 (T.sig.map encOpSig), RoseTree.node 0 (T.axioms.map encSeq)]

/-- A definition as the node of its arguments' sorts, its sort and its body. -/
def encDefn (d : Defn) : Tree :=
  RoseTree.node 0 [RoseTree.node 0 (d.ctx.map Kernel.leaf), Kernel.leaf d.sort, d.body]

/-- A definedness rule as the node of its kind's position over an axiom's index. -/
def encDfdRule : DfdRule → Tree
  | .direct j => RoseTree.node 0 [Kernel.leaf j]
  | .strict j => RoseTree.node 1 [Kernel.leaf j]
  | .rhs j => RoseTree.node 2 [Kernel.leaf j]

/-- A typing as the node of its sort and its canonical forms. -/
def encAnn (a : Ann) : Tree := RoseTree.node 0 [Kernel.leaf a.sort, a.lo, a.hi]

/-- A typed term as the node of the term and its typing. -/
def encTyped (p : Tree × Ann) : Tree := RoseTree.node 0 [p.1, encAnn p.2]

/-- An extension's environment as the node of its definitions, axioms, signature and rule
tables. -/
def encExtEnv (E : ExtEnv) : Tree :=
  RoseTree.node 0 [RoseTree.node 0 (E.defs.map encDefn), RoseTree.node 0 (E.axs.toList.map encSeq),
    RoseTree.node 0 (E.sg.toList.map encOpSig),
    RoseTree.node 0 (E.dfds.toList.map fun r ↦ encOpt (r.map encDfdRule)),
    RoseTree.node 0 (E.doms.toList.map fun r ↦ encOpt (r.map Kernel.leaf)),
    RoseTree.node 0 (E.cods.toList.map fun r ↦ encOpt (r.map Kernel.leaf))]

/-- A pair of trees as the node of label zero over them. -/
def encPair (p : Tree × Tree) : Tree := RoseTree.node 0 [p.1, p.2]

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
  encWith (fun l ↦ (labelData l).1) fun l ↦ RoseTree.node 0 (labelData l).2

/-- A conditional's parts, its type, test and branches, as the node of the type and the terms. -/
def encCond (p : Tree × Internal.Term × Internal.Term × Internal.Term) : Tree :=
  RoseTree.node 0 [p.1, encTerm p.2.1, encTerm p.2.2.1, encTerm p.2.2.2]

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
    (16, [Kernel.leaf j, RoseTree.node 0 θ, RoseTree.node 0 (σ.map encTerm), Kernel.ofBool flip])
  | .rwHyp i flip => (17, [Kernel.leaf i, Kernel.ofBool flip])
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
  encWith (fun r ↦ (ruleData r).1) fun r ↦ RoseTree.node 0 (ruleData r).2

/-- A rule of the prover's normalizer as the node of its constructor's position over its
fields: a prepared theorem's matching, a function, is left out, the leaf of label zero standing
for its root's label. -/
def encRule : Internal.NormRule → Tree
  | .rule r => RoseTree.node 0 [Kernel.leaf (ruleData r).1, RoseTree.node 0 (ruleData r).2]
  | .delta k => RoseTree.node 1 [Kernel.leaf k]
  | .deltaBelow m ks => RoseTree.node 2 [Kernel.leaf m, RoseTree.node 0 (ks.map Kernel.leaf)]
  | .unitVar => RoseTree.node 3 []
  | .thm j θ => RoseTree.node 4 [Kernel.leaf j, RoseTree.node 0 θ]
  | .thmAt j θ _ _ k => RoseTree.node 5 [Kernel.leaf j, RoseTree.node 0 θ, Kernel.leaf 0,
      Kernel.leaf k]
  | .hyp i => RoseTree.node 6 [Kernel.leaf i]

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

/-- A rewriting rule's source, an axiom or a theorem of the development, as the node of its kind
over its index. -/
def encSrc : Prover.Src → Tree
  | .ax j => RoseTree.node 0 [Kernel.leaf j]
  | .thm j => RoseTree.node 1 [Kernel.leaf j]

/-- A rewriting rule as the node of its source, its direction and the node of the root labels it
avoids. -/
def encRw (r : Prover.RwRule) : Tree :=
  RoseTree.node 0 [encSrc r.src, Kernel.ofBool r.flip, RoseTree.node 0 (r.avoid.map Kernel.leaf)]

/-- An entry of a development as the node of its sequent and its certificate. -/
def encDevEntry (e : Seq × Tree) : Tree := RoseTree.node 0 [encSeq e.1, e.2]

/-- The indices of the library's derived equations as the node of their leaves. -/
def encIdx (i : Prover.LibIdx) : Tree := RoseTree.node 0
  ([i.compPair, i.pairFstSnd, i.evCurry, i.evCurry0, i.curryNat, i.bangOne].map Kernel.leaf)

/-- The library's optional indices and development. -/
def encLib (r : Option (Prover.LibIdx × Development)) : Tree :=
  encOpt (r.map fun p ↦ RoseTree.node 0 [encIdx p.1, RoseTree.node 0 (p.2.map encDevEntry)])

end GebTests.Prototypes.FreeTopos.Agreement.Encode

end
