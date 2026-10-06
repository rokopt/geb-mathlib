/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Substitution -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.Substitution -- shake: keep
public import GebTests.Prototypes.FreeTopos.TreeCases -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.TreeCases -- shake: keep

set_option doc.verso true in
/-!
# The datatype language's expansion of kernel forms

The expansion of the datatype language ({lit}`bootstrap/datatype.geb`) is the identity on programs
of kernel forms, proved in the internal language about the translation of the programs: for every
list {lit}`es` of trees of which each is a kernel form, {lit}`expandProgram es` is
{lit}`some (node 0 es)`. A kernel expression is a tree no list of which has a head that the reader
names by the atom {lit}`case`, {lit}`cata`, {lit}`rep`, {lit}`decode` or {lit}`datum`; a kernel form
is a list of three trees whose head it names by {lit}`def`, with a kernel expression as the third,
or by {lit}`deftype` or {lit}`defnum`.
The predicates are folds written in Geb beside the statement, and the statement is an equation of
two functions of the forms, each a mask: the conditional on the predicate of the forms between a
side and {lit}`none`. The program is the prelude, the reader, the type checker and the expansion,
with those definitions.

The proof is a development of lemmas, each an equation of two functions under a mask, in four
stages. The expression's identity: under the mask of the expression's predicate, the expansion of
an expression in any scope is the expression, by induction on rose trees with the induction
hypothesis. At a construction the label's bits are split to decide whether the tree is a list, and
the tests of the heads' names are generalized and split; at a list whose head names neither form,
the induction hypothesis gives the equation of the lists of the two sides' functions at the
children, and the accumulation of the children's expansions is rewritten under the mask of the
children's predicate to the children. The step's identity at a form: under the mask of the form's
predicate, the expansion's step at a form adds it to the output and, at {lit}`deftype`, its alias
to the environment; the form's children are split to three and the tests of the keywords
generalized and split, the test of {lit}`def` moved to the outer mask, under which the head is that
atom, and a definition's body rewritten by the expression's identity. The run's identity: by
induction on the forms, the run of the steps from an environment and an output is, under the mask
of the forms' predicate, the forms reversed onto the output. The program's: the run's at the
empty environment and output, projected through the conditional, and the reversal of a reversal.

Rewriting under a mask is the absorption lemma of
{name}`Geb.FreeTopos.Tactics.maskRw`, applied where a hypothesis equates a
conditional with one on the same test; a compound term is generalized to a new variable, which
case analysis of trees then splits.

## Main definitions

* {lit}`statement` — the predicates, the two sides and the terms of the lemmas, in Geb.
* {lit}`exprSteps`, {lit}`formSteps`, {lit}`runSteps`, {lit}`programSteps` — the identities of
  the expression, the step at a form, the run and the program.
* {lit}`development` — the lemmas, each with its proof.

## Tags

internal language, datatype language, expansion, rose trees, induction, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Expansion

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Translation Geb.FreeTopos.Tactics
open GebTests.Prototypes.FreeTopos.TranslationProofs
open GebTests.Prototypes.FreeTopos.Weakening
open GebTests.Prototypes.FreeTopos.TreeCases
open GebTests.Prototypes.FreeTopos.Translation (baseRules)
open Internal (Term NormRule Entry Deriv Decl Definition)
open scoped FinEnum

/-- The expansion at a node of a variable label and children, and at a form, as definitions. -/
def statement : String := "
(import Prelude) (import Reader) (import Datatype)
(deftype KP (Prod T T))
(def kTrees (lam ((ps (List KP)))
  (foldr KP Ts (lam ((p KP) (acc Ts)) (cons (fst p) acc)) (nil T) ps)))
(def kAll (lam ((ps (List KP))) (foldr KP T (lam ((p KP) (r T)) (and (snd p) r)) 1 ps)))
(def kstep (lam ((l T) (ps (List KP)))
  (let raw T (node l (kTrees ps))
    (pair raw
      (and (kAll ps)
        (if (isList raw)
          (let h T (at (children raw) 0)
            (if (named h kwCase) 0
              (if (named h kwCata) 0
                (if (named h kwRep) 0
                  (if (named h kwDecode) 0 (if (named h kwDatum) 0 1))))))
          1))))))
(def ke (lam ((e T)) (snd (fold KP kstep e))))
(def allKe (lam ((cs Ts)) (foldr T T (lam ((c T) (r T)) (and (ke c) r)) 1 cs)))
(def xL (lam ((e T) (s Ts)) (if (ke e) (expandExpr s e) none)))
(def xR (lam ((e T) (s Ts)) (if (ke e) (some e) none)))
(deftype XF (Arrow Ts T))
(def xLs (lam ((cs Ts))
  (foldr T (List XF) (lam ((c T) (acc (List XF))) (cons (xL c) acc)) (nil XF) cs)))
(def xRs (lam ((cs Ts))
  (foldr T (List XF) (lam ((c T) (acc (List XF))) (cons (xR c) acc)) (nil XF) cs)))
(def accOf (lam ((ms Ts))
  (foldr T Opts (lam ((m T) (acc Opts)) (pair (both m (fst acc)) (cons (get m) (snd acc))))
    (pair 1 (nil T)) ms)))
(def expAll (lam ((cs Ts) (s Ts))
  (foldr T Ts (lam ((c T) (acc Ts)) (cons (expandExpr s c) acc)) (nil T) cs)))
(def appAll (lam ((fs (List XF)) (s Ts))
  (foldr XF Ts (lam ((f XF) (acc Ts)) (cons (f s) acc)) (nil T) fs)))
(def g1L (lam ((cs Ts) (s Ts)) (if (and (allKe cs) 1) (accOf (expAll cs s)) (pair 0 (nil T)))))
(def g1R (lam ((cs Ts) (s Ts))
  (if (and (allKe cs) 1) (accOf (appAll (xLs cs) s)) (pair 0 (nil T)))))
(def g2L (lam ((cs Ts) (s Ts))
  (if (and (allKe cs) 1) (accOf (appAll (xRs cs) s)) (pair 0 (nil T)))))
(def g2R (lam ((cs Ts) (s Ts)) (if (and (allKe cs) 1) (pair 1 cs) (pair 0 (nil T)))))
(def formOk (lam ((e T))
  (if (isList e)
    (if (eq (arity e) 3)
      (let h T (at (children e) 0)
        (if (named h kwData) 0
          (if (named h kwTreeData) 0
            (if (named h kwDef) (ke (at (children e) 2))
              (if (named h kwDeftype) 1 (named h kwDefnum))))))
      0)
    0)))
(def envAfter (lam ((e T) (env Ts))
  (let es Ts (children e)
    (if (named (at es 0) kwDeftype)
      (append env (single (node2 7 (nameOf (at es 1)) (expandAliases env (at es 2)))))
      env))))
(def fL (lam ((e T) (env Ts) (out Ts)) (if (formOk e) (xpStep (pair 1 (pair env out)) e) xpFail)))
(def long3 (lam ((r Ts)) (eq (arity (node 0 (cons 0 (cons 0 (cons 0 (cons 0 r)))))) 3)))
(def kf (lam ((es Ts)) (foldr T T (lam ((e T) (r T)) (and (formOk e) r)) 1 es)))
(def runX (lam ((es Ts) (s XP))
  ((foldr T XPK (lam ((e T) (k XPK) (s XP)) (k (xpStep s e))) (lam ((s XP)) s) es) s)))
(def revApp (lam ((es Ts) (acc Ts))
  ((foldr T Endo (lam ((x T) (k Endo) (acc Ts)) (k (cons x acc))) (lam ((acc Ts)) acc) es) acc)))
(def rL (lam ((es Ts) (env Ts) (out Ts))
  (if (kf es) (let s XP (runX es (pair 1 (pair env out))) (pair (fst s) (snd (snd s))))
    (pair 0 (nil T)))))
(def rR (lam ((es Ts) (env Ts) (out Ts)) (if (kf es) (pair 1 (revApp es out)) (pair 0 (nil T)))))
(def pL (lam ((es Ts)) (if (kf es) (expandProgram es) none)))
(def pR (lam ((es Ts)) (if (kf es) (some (node 0 es)) none)))
(def revL (lam ((xs Ts) (zs Ts) (acc Ts)) (revApp (revApp xs acc) zs)))
(def revR (lam ((xs Ts) (zs Ts) (acc Ts)) (revApp acc (append xs zs))))
(def fR (lam ((e T) (env Ts) (out Ts))
  (if (formOk e) (pair 1 (pair (envAfter e env) (cons e out))) xpFail)))"

/-- The program: the prelude, the reader, the type checker, the expansion of the datatype language
and the statement. -/
def programText : String :=
  Kernel.Stage0Tests.prelude ++ "\n" ++ Kernel.Stage0Tests.reader ++ "\n" ++
    Kernel.Stage0Tests.check ++ "\n" ++ Kernel.Stage0Tests.datatype ++ "\n" ++ statement

/-! The folds at a construction. -/

/-- A kernel fold at a tree, as the translation presents it: the rose-tree fold into functions of
the kernel's step, of the result type {lit}`c` by the generic step {lit}`g`, applied to the step
{lit}`st`. -/
structure KFold where
  /-- The result type of the rose-tree fold, the functions of the step. -/
  c : Tree
  /-- The generic step of the rose-tree fold. -/
  g : Term
  /-- The kernel's step. -/
  st : Term

/-- The kernel fold of a definition's application to variables of the given types, the first in
its weak normal form. -/
def kfoldOf (P : Prog) (name : String) (Γ : List Tree) : Option KFold :=
  let w := weakNF P (baseNorm P) 0 Γ
    (apps (call (P.idx name) [] []) ((List.range Γ.length).reverse.map v))
  (openSubterms w).findSome? fun u ↦ match u.label, u.children with
    | .app, [f, st] => match f.label, f.children with
      | .roseRec c, [g, _] => some ⟨c, g, st⟩
      | _, _ => none
    | _, _ => none

namespace KFold

/-- The fold at a term. -/
def ap (k : KFold) (t : Term) : Term := Term.app (Term.roseRec k.c k.g t) k.st

/-- The type of the kernel's step and the fold's result type. -/
def types (k : KFold) : Option (Tree × Tree) := Internal.expParts k.c

/-- The list of the folds' values at the children, the innermost variable, as the computation of
the fold at a construction presents it: the applications of the rose-tree folds of the children
to the step. -/
def children (k : KFold) : Option Term := do
  let (f, a) ← k.types
  pure (call D.mapApp [f, a] [Term.listRec (Term.arr 0 [k.c] Term.star)
    (Term.arr 1 [k.c] (Term.pair (Term.roseRec k.c k.g (Term.var 1)) (Term.var 0))) (Term.var 0),
    k.st])

end KFold

/-- The first components of the folds of the expansion and of the predicate: of the children's
values, the trees their names give, the first component at each; the first component of each
fold, the tree, by the uniqueness of the fold; and the first components of the children's
values, the children. -/
def firstLemmas (P : Prog) : Option (List Step) := do
  let kF ← kfoldOf P "Datatype.expandExpr" [treeTy, list treeTy]
  let kK ← kfoldOf P "ke" [treeTy]
  let steps (tag name : String) (k : KFold) : Option (List Step) := do
    let kids ← k.children
    let firsts := Term.listRec (nilT treeTy)
      (consT treeTy (Term.fst (k.ap (Term.var 1))) (Term.var 0)) (Term.var 0)
    let trees := apps (call (P.idx name) [] []) [kids]
    let fu := weakThm P 0 [list treeTy] trees firsts
    let fi : Internal.Thm := ⟨0, [treeTy], [], Term.eq (Term.fst (k.ap (Term.var 0))) (Term.var 0)⟩
    let wh := weakThm P 0 [list treeTy] trees (Term.var 0)
    pure [step s!"fu{tag}" fu (fun _ E ↦ side fu (byListIndHypWeak P.G E 0 (baseNorm P))),
      step s!"first{tag}" fi (fun ix E ↦
        let rs := baseNorm P ++ [.thm (ix s!"fu{tag}") [], .thm (ix "mapId") []]
        side fi (byRoseIndWith P.G 0 (nodeT (Term.pair (Term.var 1) (Term.var 0)))
          (byWeak P.G E 0 rs))),
      step s!"trees{tag}" wh (fun ix E ↦ side wh (byMode .full P.G E 0 (baseNorm P ++
        [.thm (ix s!"fu{tag}") [], .thm (ix s!"first{tag}") [], .thm (ix "mapId") []])))]
  pure ((← steps "F" "Reader.rrTrees" kF) ++ (← steps "K" "kTrees" kK))

/-- The conjunction of the predicate's values at the children is the conjunction of the predicate
at the children. -/
def conjLemmas (P : Prog) : Option (List Step) := do
  let kK ← kfoldOf P "ke" [treeTy]
  let kids ← kK.children
  let allK := weakThm P 0 [list treeTy] (apps (call (P.idx "kAll") [] []) [kids])
    (apps (call (P.idx "allKe") [] []) [Term.var 0])
  pure [step "allK" allK (fun _ E ↦ side allK (byListIndHypWeak P.G E 0 (baseNorm P)))]

/-! The expression's node. -/

/-- The proof of an equation by case analysis on the truth of each application of
{lit}`named`, in turn: the application generalized to a new tree variable, split, and its label
split into the empty one, false, and a bit before a bitstring, true; each truth case by
{lit}`p`, and once no application is left, the equation by {lit}`q`. -/
def byNamedCases (P : Prog) (E : Array Entry) (lk : ℕ) (rs : List NormRule)
    (p q : Internal.Prover) (d : ℕ) : Internal.Prover :=
  d.rec q fun _ rec ↦ byNF P.G E 0 rs .weak fun Γ Φ t u ↦
    match (appsOf (P.idx "Reader.named") t ++ appsOf (P.idx "Reader.named") u).head? with
    | none => q Γ Φ t u
    | some N => byGeneralize treeTy N (byTreeSplit lk 0
        (byListSplit P.G 0 1 rec p)) Γ Φ t u

/-! The induction hypothesis as an equation of lists. -/

/-- The equation of the lists of the two sides' functions at the children, from the hypothesis of
induction on rose trees, as an implication equal to truth, by induction on the children: at a
construction the implication is introduced, the hypothesis's head and tail are its lists' heads
and tails, the head equates the sides at the first child, and the tail discharges the induction
hypothesis by modus ponens. -/
def mapEqSteps (P : Prog) : List Step :=
  let φ := Term.eq (apps (call (P.idx "xL") [] []) [v 0]) (apps (call (P.idx "xR") [] []) [v 0])
  let A := Internal.roseHyp 0 1 φ
  let B := Term.eq (apps (call (P.idx "xLs") [] []) [v 0]) (apps (call (P.idx "xRs") [] []) [v 0])
  let a : Internal.Thm := ⟨0, [list treeTy], [], Term.eq (Internal.Logic.imp P.o A B)
    (Internal.Logic.tt P.o)⟩
  let rs (ix : String → ℕ) : List NormRule :=
    baseRules ++ [.unitVar, .deltaBelow P.o (["xL", "xR"].map P.idx),
      .thm (ix "rebLF") [omega, list omega], .thm (ix "tailReb") [omega]]
  let refl : Deriv := RoseTree.node .refl []
  let tailReb : Option Internal.Thm := do
    let (z, sT) ← (lib[D.tail]?).bind fun d ↦ firstFold d.body
    pure ⟨1, [list (x 0)], [], Term.eq (Term.fst (Term.listRec z sT (v 0))) (v 0)⟩
  (match tailReb with
    | some tr => [step "tailReb" tr (fun _ E ↦ side tr (byListIndHypWeak P.G E 1 (baseNorm P)))]
    | none => []) ++
  [step "mapEq" a (fun ix E ↦
    let rs := rs ix
    let consP : Internal.Prover := fun Γ Φ l r ↦ do
      let iA := Φ.length - 1
      let (L, R) ← Internal.eqParts (← Φ[iA]?)
      let dΩ := Term.eq Term.star Term.star
      let hd (w : Term) : Term := call D.headD [omega] [dΩ, w]
      let tl (w : Term) : Term := call D.tail [omega] [w]
      let (h₁, dh₁, _) ← Internal.eval P.G E 0 rs 4096 .head Γ Φ (hd L)
      let (h₂, dh₂, _) ← Internal.eval P.G E 0 rs 4096 .head Γ Φ (hd R)
      let (t₁, dt₁, _) ← Internal.eval P.G E 0 rs 4096 .head Γ Φ (tl L)
      let (t₂, dt₂, _) ← Internal.eval P.G E 0 rs 4096 .head Γ Φ (tl R)
      let dHd := RoseTree.node (.convFrom (Term.eq (hd L) (hd R))) [RoseTree.node .cong [dh₁, dh₂],
        RoseTree.node .join [RoseTree.node .cong [RoseTree.node (.rwHyp iA false) [], refl], refl]]
      let dTl := RoseTree.node (.convFrom (Term.eq (tl L) (tl R))) [RoseTree.node .cong [dt₁, dt₂],
        RoseTree.node .join [RoseTree.node .cong [RoseTree.node (.rwHyp iA false) []], refl]]
      let Φ₁ := Φ ++ [Term.eq h₁ h₂, Term.eq t₁ t₂]
      -- the first child's sides equal, from its formula's equality with the terminal equation
      let dx := RoseTree.node .conv [RoseTree.node (.rwHyp Φ.length false) [],
        RoseTree.node .join [refl, refl]]
      let Φ₂ := Φ₁ ++ [h₁]
      let rest ← withImpElim P.o logicBase (Φ.length + 1) [0] (fun concls ↦
        withWeakHyps P.G E 0 rs (concls.filterMap hypIndex) (fun extra ↦
          byWeak P.G E 0 (extra ++ [.hyp (Φ₁.length)] ++ rs)) (m := .weak)) Γ Φ₂ l r
      pure (RoseTree.node (.cut (Term.eq h₁ h₂)) [dHd, RoseTree.node (.cut (Term.eq t₁ t₂))
        [dTl, RoseTree.node (.cut h₁) [dx, rest]]])
    side a (Internal.byListIndWith P.G 0 0 1 (byImpI P.G E P.o logicBase (byWeak P.G E 0 rs))
      (byImpI P.G E P.o logicBase consP)))]

/-! Rewriting under a mask by a hypothesis. -/

/-- The conditional's computation at an empty test and at a bit before a bitstring. -/
def condSteps (P : Prog) : List Step :=
  let X := x 0
  let nilR : Internal.Thm := ⟨1, [X, X], [], Term.eq (condT X (nilT bitTy) (v 1) (v 0)) (v 0)⟩
  let consR : Internal.Thm := ⟨1, [X, X, bitsTy, bitTy], [], Term.eq
    (condT X (consT bitTy (v 3) (v 2)) (v 1) (v 0)) (v 1)⟩
  let same : Internal.Thm := ⟨1, [bitsTy, X], [], Term.eq (condT X (v 0) (v 1) (v 1)) (v 1)⟩
  [step "condAtNil" nilR (fun _ E ↦ side nilR (byWeak P.G E 1 (baseNorm P))),
    step "condAtCons" consR (fun _ E ↦ side consR (byWeak P.G E 1 (baseNorm P))),
    step "condSame" same (fun ix E ↦ side same (bitsCases P.G 1 (byWeak P.G E 1
      (baseRules ++ [.unitVar, .deltaBelow P.o [D.cond], .thm (ix "condAtNil") [X],
        .thm (ix "condAtCons") [X]]))))]

/-- The applications of the definition of index {lit}`k` to one argument among a term's
subterms outside binders and folds' starts and steps. -/
def apps1Of (k : ℕ) (t : Term) : List Term :=
  (openSubterms t).filter fun u ↦ match u.label, u.children with
    | .app, [f, _] => f.label = .defn k []
    | _, _ => false

/-- The rules with the library's conditional folded: the language's equations, the unfolding of
the definitions but the conditional and those named, the conditional's computation at the types
it is taken at, and the rewritings of the folds' first components, the conjunction and the
children. -/
def rsC (P : Prog) (ix : String → ℕ) (folded : List String) : List NormRule :=
  let types := [treeTy, bitsTy, list treeTy, prod treeTy (list treeTy),
    prod treeTy (prod (list treeTy) (list treeTy)), prod (list treeTy) (list treeTy),
    exp (list treeTy) treeTy]
  baseRules ++ [.unitVar, .deltaBelow P.o (D.cond :: folded.map P.idx)] ++
    types.flatMap (fun a ↦ [.thm (ix "condAtNil") [a], .thm (ix "condAtCons") [a],
      .thm (ix "condSame") [a]]) ++
    [.thm (ix "treesF") [], .thm (ix "treesK") [], .thm (ix "allK") [],
      .thm (ix "childrenNode") [], .thm (ix "lambek") []] ++
    [(bitTy, bitsTy), (bitTy, treeTy), (treeTy, treeTy), (treeTy, list treeTy)].map
      fun (a, b) ↦ .thm (ix "rebLF") [a, b]

/-- The accumulations under the mask of the children's predicate, each by induction on the
children: that of the expansions of the children is that of the applications of the first side's
functions, and that of the applications of the second side's functions is the children, all
present. At a construction, the induction hypothesis's instance at the scope, the predicate at the
first child generalized and split, and in the true case the tail's accumulation rewritten under the
mask by that instance. -/
def accSteps (P : Prog) : List Step :=
  let folded := ["ke", "Reader.named", "Datatype.expandCase", "Datatype.expandCata",
    "Datatype.expandDecode"]
  let accLemma (name l r : String) : Step :=
    let a : Internal.Thm := ⟨0, [list treeTy], [], Term.eq (apps (call (P.idx l) [] []) [v 0])
      (apps (call (P.idx r) [] []) [v 0])⟩
    step name a (fun ix E ↦
      let rs := rsC P ix folded
      let w := byWeak P.G E 0 rs
      let closeTrue : Internal.Prover :=
        byMaskSubs P.G E (ix "absorb") (ix "condSame") rs 1 fun extra ↦
          byWeak P.G E 0 (extra ++ rs)
      let split : Internal.Prover := byNF P.G E 0 rs .weak fun Γ Φ t u ↦
        match apps1Of (P.idx "ke") t with
        | K :: _ => byGeneralize treeTy K (byTreeSplit (ix "lambek") 0
            (byListSplit P.G 0 1 w closeTrue)) Γ Φ t u
        | [] => none
      side a (Internal.byListIndWith P.G 0 0 1 (Internal.byFunExt P.G 0 w)
        (Internal.byFunExt P.G 0 fun Γ Φ t u ↦
          withInsts P.G E 0 rs 0 [[v 0]] (fun _ ↦ split) (m := .weak) Γ Φ t u)))
  [accLemma "acc1" "g1L" "g1R", accLemma "acc2" "g2L" "g2R"]

/-- The applications of the children's folds of the expansion to a scope are the expansions of
the children at it, by induction on the children. -/
def applySteps (P : Prog) : Option (List Step) := do
  let kF ← kfoldOf P "Datatype.expandExpr" [treeTy, list treeTy]
  let kids ← kF.children
  let a := weakThm P 0 [list treeTy, list treeTy]
    (apps (call (P.idx "Reader.rrApply") [] []) [kids, v 1])
    (apps (call (P.idx "expAll") [] []) [v 0, v 1])
  pure [step "applyF" a (fun _ E ↦ side a (byListIndHypWeak P.G E 0 (baseNorm P)))]

/-- The expression's identity, by induction on rose trees with the induction hypothesis: at a
construction, the label split to decide a list; in the list case the applications of
{lit}`named` split; and at a list whose head names neither form, the equation of the lists of the
sides' functions at the children from the induction hypothesis, and the expansions' accumulation
rewritten under the mask of the children's predicate, first to that of the first side's
functions, which are the second side's, and then to the children. -/
def exprSteps (P : Prog) : List Step :=
  let a : Internal.Thm := ⟨0, [treeTy], [], Term.eq (apps (call (P.idx "xL") [] []) [v 0])
    (apps (call (P.idx "xR") [] []) [v 0])⟩
  [step "exprId" a (fun ix E ↦
    let rs := rsC P ix ["Reader.named", "Datatype.expandCase", "Datatype.expandCata",
      "Datatype.expandDecode"] ++
      [.thm (ix "applyF") []]
    let w := byWeak P.G E 0 rs
    let refl : Deriv := RoseTree.node .refl []
    let rest : Internal.Prover := fun Γ Φ t u ↦ do
      let n := Γ.length
      let csv := v (n - 2)
      let sv := v (n - 3)
      let some (Entry.language me) := E[ix "mapEq"]? | none
      let impInst := Internal.instTerm [] [csv] me.concl
      let Φ₁ := Φ ++ [impInst]
      let instEq (name gL gR : String) : Term × Deriv :=
        (Term.eq (Term.app (apps (call (P.idx gL) [] []) [csv]) sv)
          (Term.app (apps (call (P.idx gR) [] []) [csv]) sv),
         RoseTree.node .join [RoseTree.node .cong
          [RoseTree.node (.thm (ix name) [] [csv] false) [], refl], refl])
      let (e₁, d₁) := instEq "acc1" "g1L" "g1R"
      let (e₂, d₂) := instEq "acc2" "g2L" "g2R"
      let k ← withImpElim P.o logicBase 0 [Φ.length] (fun concls ↦
        withWeakHyps P.G E 0 rs (concls.filterMap hypIndex ++ [Φ₁.length, Φ₁.length + 1])
          (fun extra ↦
            let rs' := extra ++ rs
            byMaskSubs P.G E (ix "absorb") (ix "condSame") rs' 2 fun more ↦
              byWeak P.G E 0 (more ++ rs'))
          (m := .weak)) Γ (Φ₁ ++ [e₁, e₂]) t u
      pure (RoseTree.node (.cut impInst) [RoseTree.node (.apply (ix "mapEq") [] [csv]) [],
        RoseTree.node (.cut e₁) [d₁, RoseTree.node (.cut e₂) [d₂, k]]])
    let leaf : Internal.Prover := fun Γ Φ t u ↦ (w Γ Φ t u).orElse fun _ ↦
      byNamedCases P E (ix "lambek") rs w rest 6 Γ Φ t u
    side a (Internal.byRoseIndHyp 2 0 1 (Internal.byFunExt P.G 0 (byBits P.G leaf 3 2))))]

/-! The forms. -/

/-- The lemmas of the step at a form: a conditional on the label of a conditional is the
conditional on the inner test between the conditionals on the branches' labels, and a tree the
reader names by the atom {lit}`def` is that atom, each in the normal form of the rules
{lit}`rs`, with the named definitions folded. -/
def formLemmas (P : Prog) (rs : (String → ℕ) → List NormRule) : List Step :=
  let X := x 0
  let lab (t : Term) : Term := call D.lab [] [t]
  let raw : Term × Term :=
    (condT X (lab (condT treeTy (lab (v 4)) (v 3) (v 2))) (v 1) (v 0),
      condT X (lab (v 4)) (condT X (lab (v 3)) (v 1) (v 0)) (condT X (lab (v 2)) (v 1) (v 0)))
  let named (h : Term) : Term :=
    apps (call (P.idx "Reader.named") [] []) [h, call (P.idx "Reader.kwDef") [] []]
  let aDef := call (P.idx "Datatype.aDef") [] []
  let hdRaw : Term × Term := (condT treeTy (lab (named (v 0))) (v 0) aDef, aDef)
  let nf (G : Internal.Globals) (E : Array Entry) (ix : String → ℕ) (n : ℕ) (Γ : List Tree)
      (t : Term) : Option (Term × Deriv) :=
    (Internal.eval G E n (rs ix) 4096 .weak Γ [] t).map fun (w, d, _) ↦ (w, d)
  [("long", fun ix E ↦ do
      let raw := call D.lab [] [apps (call (P.idx "long3") [] []) [v 0]]
      let zero := nilT bitTy
      let (l, dl) ← nf P.G E ix 0 [list treeTy] raw
      let a : Internal.Thm := ⟨0, [list treeTy], [], Term.eq l zero⟩
      -- the tail's length generalized to a bitstring, whose bits then decide the equality
      let genLen : Internal.Prover := byNF P.G E 0 (rs ix) .weak fun Γ Φ t u ↦
        match (openSubterms t).find? (fun w ↦ match w.label, w.children with
            | .listRec, [_, _, m] => m = v 0
            | _, _ => false) with
        | some L => byGeneralize bitsTy L (byAutoC P.G E 0 (ix "lambek") (rs ix) 12) Γ Φ t u
        | none => none
      let d ← genLen [list treeTy] [] raw zero
      pure (a, RoseTree.node (.convFrom (Term.eq raw zero)) [RoseTree.node .cong [dl,
        RoseTree.node .refl []], d])),
    ("maskSplit", fun ix E ↦ do
      let Γ := [X, X, treeTy, treeTy, treeTy]
      let (l, dl) ← nf P.G E ix 1 Γ raw.1
      let (r, dr) ← nf P.G E ix 1 Γ raw.2
      let a : Internal.Thm := ⟨1, Γ, [], Term.eq l r⟩
      let rsX := rs ix ++ [.thm (ix "condAtNil") [X], .thm (ix "condAtCons") [X],
        .thm (ix "condSame") [X]]
      let d ← byAutoC P.G E 1 (ix "lambek") rsX 12 Γ [] raw.1 raw.2
      pure (a, RoseTree.node (.convFrom (Term.eq raw.1 raw.2)) [RoseTree.node .cong [dl, dr], d])),
    ("headDefN", fun ix E ↦ do
      let (l, dl) ← nf P.G E ix 0 [treeTy] hdRaw.1
      let (r, dr) ← nf P.G E ix 0 [treeTy] hdRaw.2
      let a : Internal.Thm := ⟨0, [treeTy], [], Term.eq l r⟩
      pure (a, RoseTree.node (.convFrom (Term.eq hdRaw.1 hdRaw.2))
        [RoseTree.node .cong [dl, dr], RoseTree.node .join
          [RoseTree.node (.thm (ix "headDef") [] [v 0] false) [], RoseTree.node .refl []]]))]

/-- The step of the expansion at a form of the kernel's, under the mask of the predicate of forms:
a node whose label is split to decide a list and whose children are split to three; the tests of
the atoms {lit}`data` and {lit}`tree-data` generalized and split; the test of {lit}`def` moved to
the outer mask, under which the head is that atom, both sides rewritten; that test generalized and
split, a definition's body's expansion rewritten under the mask of its predicate by the
expression's identity; and the tests of {lit}`deftype` and {lit}`defnum` generalized and split. -/
def formSteps (P : Prog) : List Step :=
  let XP := prod treeTy (prod (list treeTy) (list treeTy))
  let foldedF := ["ke", "Datatype.expandExpr", "Datatype.expandCase", "Datatype.expandCata",
    "Datatype.expandDecode", "Datatype.expandAliases", "Datatype.dataDecl", "Datatype.marker",
    "Reader.named", "Datatype.kwData", "Datatype.kwTreeData", "Reader.kwDef", "Reader.kwDeftype",
    "Reader.kwDefnum"]
  let rsF (ix : String → ℕ) : List NormRule := rsC P ix foldedF
  let rsFS (ix : String → ℕ) : List NormRule :=
    .thm (ix "maskSplit") [XP] :: .thm (ix "long") [] :: rsF ix
  let rsU (ix : String → ℕ) : List NormRule := rsC P ix (foldedF.take 8)
  let a : Internal.Thm := ⟨0, [treeTy], [], Term.eq (apps (call (P.idx "fL") [] []) [v 0])
    (apps (call (P.idx "fR") [] []) [v 0])⟩
  formLemmas P rsF ++
  [step "form" a (fun ix E ↦
    let rs := rsF ix
    let w := byWeak P.G E 0 rs
    let refl : Deriv := RoseTree.node .refl []
    let kw (name : String) (t : Term) : Option Term :=
      (appsOf (P.idx "Reader.named") t).find? fun u ↦ match u.children with
        | [_, k] => k = call (P.idx name) [] [] | _ => false
    -- the generalization and split of a keyword's test, the true case by p and the false by q
    let byKw (name : String) (p q : Internal.Prover) : Internal.Prover :=
      byNF P.G E 0 (rsFS ix) .weak fun Γ Φ t u ↦ match (kw name t).orElse fun _ ↦ kw name u with
        | some K => byGeneralize treeTy K (byTreeSplit (ix "lambek") 0
            (byListSplit P.G 0 1 q p)) Γ Φ t u
        | none => none
    let defCase : Internal.Prover :=
      byMaskSubs P.G E (ix "absorb") (ix "condSame") (rsU ix) 2 fun extra ↦
        byWeak P.G E 0 (extra ++ rsU ix)
    let tyCase : Internal.Prover := byKw "Reader.kwDeftype" w (byKw "Reader.kwDefnum" w w)
    let three : Internal.Prover := fun Γ Φ t u ↦ do
      let n := Γ.length
      let bv := v 1
      let hv := v 5
      let envv := v (n - 2)
      let χ := Term.eq (Term.app (apps (call (P.idx "xL") [] []) [bv]) envv)
        (Term.app (apps (call (P.idx "xR") [] []) [bv]) envv)
      let dχ := RoseTree.node .join [RoseTree.node .cong
        [RoseTree.node (.thm (ix "exprId") [] [bv] false) [], refl], refl]
      let some (Entry.language hd) := E[ix "headDefN"]? | none
      let ψ := Internal.instTerm [] [hv] hd.concl
      let dψ := RoseTree.node .join [RoseTree.node (.thm (ix "headDefN") [] [hv] false) [], refl]
      let k ← withWeakHyps P.G E 0 (rsU ix) [Φ.length] (fun _ ↦
          byKw "Datatype.kwData" w (byKw "Datatype.kwTreeData" w (byNF P.G E 0 (rsFS ix) .weak
            (byMaskSubs P.G E (ix "absorb") (ix "condSame") (rsFS ix) 6 fun _ ↦
              byKw "Reader.kwDef" defCase tyCase)))) (m := .weak) Γ (Φ ++ [χ, ψ]) t u
      pure (RoseTree.node (.cut χ) [dχ, RoseTree.node (.cut ψ) [dψ, k]])
    let listCase : Internal.Prover := fun Γ Φ t u ↦
      byLength3 P.G (Γ.length - 5) three (byWeak P.G E 0 (rsFS ix)) Γ Φ t u
    let leaf : Internal.Prover := fun Γ Φ t u ↦ (w Γ Φ t u).orElse fun _ ↦ listCase Γ Φ t u
    side a (Internal.byFunExt P.G 0 (Internal.byFunExt P.G 0
      (byTreeSplit (ix "lambek") 2 (byBits P.G leaf 3 1)))))]

/-! The program. -/

/-- The lemmas of reversal: appending the empty list, and the continuation-passing reversal of a
list onto an accumulator reversed onto another as the accumulator reversed onto the list before
the other, by induction on the list as a function of the accumulator, and its instance at empty
accumulators. -/
def revSteps (P : Prog) : List Step :=
  let appNil := weakThm P 0 [list treeTy]
    (apps (call (P.idx "Prelude.append") [] []) [v 0, nilT treeTy]) (v 0)
  let side2 (name : String) : Term :=
    Term.lam (list treeTy) (apps (call (P.idx name) [] []) [v 1, v 2, v 0])
  let revGen : Internal.Thm := ⟨0, [list treeTy, list treeTy], [],
    Term.eq (side2 "revL") (side2 "revR")⟩
  let revRev := weakThm P 0 [list treeTy]
    (apps (call (P.idx "revApp") [] []) [apps (call (P.idx "revApp") [] []) [v 0, nilT treeTy],
      nilT treeTy]) (v 0)
  [step "appendNil" appNil (fun _ E ↦ side appNil (byListIndHypWeak P.G E 0 (baseNorm P))),
    step "revGen" revGen (fun ix E ↦
      let rs := baseNorm P ++ [.thm (ix "appendNil") []]
      side revGen (Internal.byListIndWith P.G 0 0 1
        (Internal.byFunExt P.G 0 (byWeak P.G E 0 rs))
        (Internal.byFunExt P.G 0 fun Γ Φ t u ↦
          withInsts P.G E 0 rs 0 [[consT treeTy (v 2) (v 0)]] (fun extra ↦
            byWeak P.G E 0 (extra ++ rs)) (m := .weak) Γ Φ t u))),
    pointwise P (fun _ ↦ baseNorm P) .weak "revGenP" "revGen" (list treeTy),
    step "revRev" revRev (fun ix E ↦ side revRev (byWeak P.G E 0
      (baseNorm P ++ [.thm (ix "revGenP") [], .thm (ix "appendNil") []])))]

/-- The run of the expansion over a program of kernel forms, under the mask of their predicate:
its flag and its output, as functions of the environment and the output it starts with, by
induction on the forms; at a form before the rest, the mask of the conjunction split, the step
rewritten under the form's mask by the step's lemma, and the rest's run under the rest's mask by
the induction hypothesis at the environment and the output the step leaves. -/
def runSteps (P : Prog) : List Step :=
  let prodTs := prod treeTy (list treeTy)
  let XP := prod treeTy (prod (list treeTy) (list treeTy))
  let a : Internal.Thm := ⟨0, [list treeTy], [], Term.eq (apps (call (P.idx "rL") [] []) [v 0])
    (apps (call (P.idx "rR") [] []) [v 0])⟩
  let folded := ["formOk", "Datatype.xpStep", "envAfter", "ke", "Datatype.expandExpr",
    "Datatype.expandCase", "Datatype.expandCata", "Datatype.expandDecode", "Datatype.expandAliases",
    "Datatype.dataDecl", "Datatype.marker", "Reader.named"]
  [step "run" a (fun ix E ↦
    let rs := [.thm (ix "maskSplit") [prodTs], .thm (ix "maskSplit") [XP]] ++ rsC P ix folded
    let refl : Deriv := RoseTree.node .refl []
    let consP : Internal.Prover := fun Γ Φ t u ↦ do
      -- context [out, env, rest, form]; the step's lemma at the form, the environment and the
      -- output, and the induction hypothesis at the environment and output after the step
      let (outv, envv, ev) := (v 0, v 1, v 3)
      let app3 (name : String) : Term :=
        apps (call (P.idx name) [] []) [ev, envv, outv]
      let χ := Term.eq (app3 "fL") (app3 "fR")
      let dχ := RoseTree.node .join [RoseTree.node .cong [RoseTree.node .cong
        [RoseTree.node (.thm (ix "form") [] [ev] false) [], refl], refl], refl]
      let env' := apps (call (P.idx "envAfter") [] []) [ev, envv]
      let out' := consT treeTy ev outv
      withInsts P.G E 0 rs 0 [[env', out']] (fun _ ↦ fun Γ Φ t u ↦ do
        let k ← withWeakHyps P.G E 0 rs [Φ.length] (fun _ ↦
          byMaskSubs P.G E (ix "absorb") (ix "condSame") rs 4 fun extra ↦
            byWeak P.G E 0 (extra ++ rs))
          (m := .weak) Γ (Φ ++ [χ]) t u
        pure (RoseTree.node (.cut χ) [dχ, k])) (m := .weak) Γ Φ t u
    side a (Internal.byListIndWith P.G 0 0 1
      (Internal.byFunExt P.G 0 (Internal.byFunExt P.G 0 (byWeak P.G E 0 rs)))
      (Internal.byFunExt P.G 0 (Internal.byFunExt P.G 0 consP))))]

/-- The projections of a conditional between pairs: the conditional between the projections. -/
def projSteps (P : Prog) : List Step :=
  let X := x 0
  let Y := x 1
  let PX := prod X Y
  let fstC : Internal.Thm := ⟨2, [bitsTy, PX, PX], [], Term.eq
    (Term.fst (condT PX (v 0) (v 1) (v 2))) (condT X (v 0) (Term.fst (v 1)) (Term.fst (v 2)))⟩
  let sndC : Internal.Thm := ⟨2, [bitsTy, PX, PX], [], Term.eq
    (Term.snd (condT PX (v 0) (v 1) (v 2))) (condT Y (v 0) (Term.snd (v 1)) (Term.snd (v 2)))⟩
  let rs := baseNorm P
  [step "condFst" fstC (fun _ E ↦ side fstC (bitsCases P.G 2 (byWeak P.G E 2 rs))),
    step "condSnd" sndC (fun _ E ↦ side sndC (bitsCases P.G 2 (byWeak P.G E 2 rs)))]

/-- The expansion's identity on a program of kernel forms, under the mask of their predicate: the
run's lemma at the empty environment and output, its flag and output projected through the
conditional, both rewritten under the mask, and the reversal of the output reversed. -/
def programSteps (P : Prog) : List Step :=
  let a : Internal.Thm := ⟨0, [list treeTy], [], Term.eq (apps (call (P.idx "pL") [] []) [v 0])
    (apps (call (P.idx "pR") [] []) [v 0])⟩
  let folded := ["formOk", "Datatype.xpStep", "envAfter", "ke", "Datatype.expandExpr",
    "Datatype.expandCase", "Datatype.expandCata", "Datatype.expandDecode", "Datatype.expandAliases",
    "Datatype.dataDecl", "Datatype.marker", "Reader.named"]
  [step "expansion" a (fun ix E ↦
    let rs := [.thm (ix "condFst") [treeTy, list treeTy], .thm (ix "condSnd") [treeTy, list treeTy],
      .thm (ix "revRev") [], .thm (ix "maskSplit") [treeTy]] ++ rsC P ix folded
    let refl : Deriv := RoseTree.node .refl []
    let es := v 0
    let nil := nilT treeTy
    let run (name : String) : Term := apps (call (P.idx name) [] []) [es, nil, nil]
    let χ := Term.eq (run "rL") (run "rR")
    let dχ := RoseTree.node .join [RoseTree.node .cong [RoseTree.node .cong
      [RoseTree.node (.thm (ix "run") [] [es] false) [], refl], refl], refl]
    let proj (f : Term → Term) (i : ℕ) : Term × Deriv :=
      (Term.eq (f (run "rL")) (f (run "rR")),
        RoseTree.node .join [RoseTree.node .cong [RoseTree.node (.rwHyp i false) []], refl])
    let prover : Internal.Prover := fun Γ Φ t u ↦ do
      let i := Φ.length
      let (φf, df) := proj Term.fst i
      let (φs, ds) := proj Term.snd i
      let k ← withWeakHyps P.G E 0 rs [i + 1, i + 2] (fun _ ↦
        byMaskSubs P.G E (ix "absorb") (ix "condSame") rs 4 fun extra ↦
          byWeak P.G E 0 (extra ++ rs))
        (m := .weak) Γ (Φ ++ [χ, φf, φs]) t u
      pure (RoseTree.node (.cut χ) [dχ, RoseTree.node (.cut φf) [df,
        RoseTree.node (.cut φs) [ds, k]]])
    side a prover)]

/-- The development: the lemmas on the unfolding of trees and of logic, the conditional lemmas and
the lemmas of trees, then the expression's identity, the step's at a form, the run's and the
program's, each with the lemmas it needs. -/
def development (P : Prog) : Option (List Step) := do
  pure (unfoldingThms P ++ logicThms P ++ (← TreeCases.genericLemmas P) ++
    TreeCases.headLemmas P ++ (← firstLemmas P) ++ (← conjLemmas P) ++ mapEqSteps P ++
    condSteps P ++ accSteps P ++ (← applySteps P) ++ exprSteps P ++ formSteps P ++ revSteps P ++
    runSteps P ++ projSteps P ++ programSteps P)

/-- The development found and checked, and the measurement: the nodes of its derivations and the
milliseconds its proof and its check take; an error where a lemma is not proved or the
development does not check. -/
def checkDevelopment (P : Prog) : IO Unit := do
  let some dev := development P | throw (IO.userError "the development is not stated")
  let t₀ ← IO.monoMsNow
  let decls ← match developNamed dev with
    | .ok decls => pure decls
    | .error name => throw (IO.userError s!"the lemma {name} is not proved")
  let t₁ ← IO.monoMsNow
  let some _ := Internal.checkDev P.G #[] decls
    | throw (IO.userError "the development does not check")
  let t₂ ← IO.monoMsNow
  let nodes := (decls.filterMap fun | Decl.language _ d => some (derivSize d) | _ => none).sum
  IO.println "development_nodes,proof_milliseconds,check_milliseconds"
  IO.println s!"{nodes},{t₁ - t₀},{t₂ - t₁}"

#eval show IO Unit from do
  let some ds := bundled GoedelT.ProofTests.bundler.toList programText.toList
    | throw (IO.userError "the program does not read")
  let some P := prog? ds fun name ↦ (defIndex ds name.toList).getD 0
    | throw (IO.userError "the program does not translate")
  checkDevelopment P

end GebTests.Prototypes.FreeTopos.Expansion

end
