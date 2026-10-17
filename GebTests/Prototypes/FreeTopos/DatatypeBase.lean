/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.NormalizationRel -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.NormalizationRel -- shake: keep
public import GebTests.Prototypes.Stage1 -- shake: keep
public meta import GebTests.Prototypes.Stage1 -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The base of the datatype language's soundness

The soundness of the datatype language's stage-1 compiler, stated in the internal language about
the programs written in Geb ({lit}`datatypeφ`): a source form that expands, whose expansion the
stage-1 typing gives a type, and whose expansion's erasure, its numeral abbreviations expanded,
the reader resolves, resolves to a term whose evaluation converges to a value related at that type
by the relation of the datatype language ({lit}`relDefn`). The relation extends the fundamental
lemma's ({lit}`GebTests.Prototypes.FreeTopos.Normalization`) at the kernel's types by the
datatypes, whose values are their members' quotations. The statement's hypotheses relate the
environment to the named context, position by position, and the definitions to the typing
environment's, by names; they take the reader's numeral abbreviations and names coherent with the
typing environment's and with the keywords, the form a source form, one whose atoms' characters
the expansion of numeral abbreviations fixes, and the resolved term typed by the kernel's checker,
as the pipeline checks it. The reader resolves in the scope of the named context's names as it
reads binders, each numeral abbreviation expanded ({lit}`scopeOf`).

The statement composes folds of rose trees, the stage functions of the pipeline, each defined in
the extended program ({lit}`extend3`) by its argument and its fold, so that the proofs keep it
folded and rewrite it by its vocabulary ({lit}`foldVocab`): its value at a node, and the fusion of
its map over the children with the fold of the children's values. This module proves the case of
an atom ({lit}`atomCase`): the typing's tests at an atom, decided in their order with the reader's,
give a numeral's quotation, a variable's value in the environment, a definition's, a primitive,
and the unit value, each related at its type; the primitive's index is decided name by name, and
the primitive related by the fundamental lemma's relation of the primitives ({lit}`relTPrim`); the
reader's scope agrees with the named context at the name ({lit}`lookupAgreeA`,
{lit}`lookupAgreeB`). The base and the case of an atom are stored as the certificates
{lit}`bootstrap/certificates/datatype-base.cert` and
{lit}`bootstrap/certificates/datatype-atom.cert`, the second's search continuing from the
first.

## Main definitions

* {lit}`extend3` — the program extended by the relation, the environments' relations, the
  coherences, and each fold's definitions.
* {lit}`datatypeφ` — the soundness of the datatype language's typing at a source form.
* {lit}`foldVocab` — the vocabulary of a fold.
* {lit}`atomCase` — the soundness at an atom.
* {lit}`baseDev3`, {lit}`atomDev3` — the developments.

## References

* {cite}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, datatypes, soundness, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Datatypes

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Translation Geb.FreeTopos.Tactics
open GebTests.Prototypes.FreeTopos.Weakening
open scoped FinEnum

open Internal (Term)
open GebTests.Prototypes.FreeTopos.Normalization

/-- The source forms the reader gives, at a function on trees: atoms, whose characters the function
fixes, and lists of source forms. The statement takes the function to be the expansion of numeral
abbreviations, which fixes the reader's characters, leaves not labelled as atoms, at any
abbreviations. One fold gives, at each tree and function, the tree rebuilt and whether it is a
source form. The weakening proof's statement before it imports the prelude. -/
def sourceForms : String := "
(deftype SF (Prod T T))
(def charsFixed (lam ((f (Arrow T T)) (cs Ts))
  (equal (node 0 (foldr T Ts (lam ((c T) (a Ts)) (cons (f c) a)) (nil T) cs)) (node 0 cs))))
(def srcForm (lam ((f (Arrow T T)) (e T))
  (snd ((fold (Arrow (Arrow T T) SF)
    (lam ((l T) (rs (List (Arrow (Arrow T T) SF))))
      (lam ((g (Arrow T T)))
        (let ps (List SF)
          (foldr (Arrow (Arrow T T) SF) (List SF)
            (lam ((r (Arrow (Arrow T T) SF)) (a (List SF))) (cons (r g) a)) (nil SF) rs)
          (let cs Ts (foldr SF Ts (lam ((p SF) (a Ts)) (cons (fst p) a)) (nil T) ps)
            (pair (node l cs)
              (if (eq l 1) (charsFixed g cs)
                (if (eq l 2) (foldr SF T (lam ((p SF) (a T)) (and (snd p) a)) 1 ps) 0)))))))
    e) f))))"

/-- The reader's name of a named context's variable: a name the numeral abbreviations abbreviate is
the name of its numeral's atom, as the reader reads a binder once the abbreviations are expanded;
any other is itself. -/
def scopeNames : String := "
(import Reader)
(def expName (lam ((nums Ts) (n T))
  (let a T (lookupAbbrev n nums) (if (isSome a) (nameOf (get a)) n))))"

/-- The program: the prelude, the reader, the kernel's type checker, the lists of the datatype
language, the stage-1 typing and expansion, the recognizers, the traversal of kernel terms, the
evaluator, and the weakening proof's statement, whose development the base of the fundamental lemma
proves. -/
def programText : String :=
  Kernel.Stage0Tests.prelude ++ "\n" ++ Kernel.Stage0Tests.reader ++ "\n" ++
    Kernel.Stage0Tests.check ++ "\n" ++ Kernel.Stage1Tests.seq ++ "\n" ++
    Kernel.Stage1Tests.typing ++ "\n" ++ Kernel.Stage1Tests.datatype ++ "\n" ++
    Kernel.Stage0Tests.recognize ++ "\n" ++ Kernel.Stage0Tests.subst ++ "\n" ++
    Kernel.EvalTests.evalGeb ++ "\n" ++ Weakening.statement ++ "\n" ++ sourceForms ++ "\n" ++
    scopeNames

/-- The number of folds the statement composes, each defined by its argument and its fold. -/
def nFolds : ℕ := 6

/-- The indices of the definitions the datatype language's soundness states, after the fundamental
lemma's, and the types its relations take. -/
structure Defs3 where
  /-- The index of the first definition. -/
  q : ℕ
  /-- The type of the typing's environments. -/
  envTy : Tree

namespace Defs3

variable (T : Defs3)

/-- The context of the relation: the program's definitions and the markers of its datatypes. -/
def ctxTy : Tree := prod (list treeTy) (list treeTy)

/-- The relation at a type of the datatype language, a predicate on values, in a context. -/
def relT (R A : Term) : Term := call T.q [] [R, A]

/-- The relation of an environment to a named context. -/
def envT (R cx env : Term) : Term := call (T.q + 1) [] [R, cx, env]

/-- The relation of the definitions to the typing environment's definitions, by their names. -/
def globT (R E names : Term) : Term := call (T.q + 2) [] [R, E, names]

/-- The index of the argument the fold of index k of {lit}`foldSpecs` is applied to, a function
of the parameters it uses. -/
def argIdx (k : ℕ) : ℕ := T.q + 3 + 2 * k

/-- The index of the definition of the fold of index k of {lit}`foldSpecs`. -/
def foldIdx (k : ℕ) : ℕ := T.q + 4 + 2 * k

/-- The coherence of the reader's numeral abbreviations with the typing environment's numeral
names: each name the environment has abbreviates a numeral's atom, and each name abbreviated is
one the environment has. -/
def numsT (E nums : Term) : Term := call (T.q + 3 + 2 * nFolds) [] [E, nums]

/-- The coherence of the reader's names of definitions with the typing environment's definitions:
each name with an index has a type. -/
def defsT (E names : Term) : Term := call (T.q + 4 + 2 * nFolds) [] [E, names]

/-- The coherence of the reader's numeral abbreviations with its keywords: no name abbreviated is
reserved. -/
def kwsT (nums : Term) : Term := call (T.q + 5 + 2 * nFolds) [] [nums]

/-- The fold of index k of {lit}`foldSpecs` at a tree, applied to the parameters its step uses,
the outermost first. -/
def foldAt (k : ℕ) (params : List Term) (x : Term) : Term := call (T.foldIdx k) [] (params ++ [x])

end Defs3

/-- The relation at a type of the datatype language, by the fold of the type's tree whose value at
a node pairs the node rebuilt with the relation: at the trees, the unit type, products, function
types and lists as the kernel's relation, at a datatype its members' quotations, by the typing's
membership in the markers' datatypes, and at an opaque sort none. -/
def relDefn (P : Prog) (S : Defs) : Internal.Defn :=
  let o := P.o
  let ff := Internal.Logic.ff o
  let ex := Internal.Logic.ex o
  let all := Internal.Logic.all o
  let conj := Internal.Logic.conj o
  let imp := Internal.Logic.imp o
  let R := Defs3.ctxTy
  let relC := prod treeTy (exp R (exp treeTy omega))
  let ffC : Term := Term.pair (leafT bnilT) (Term.lam R (Term.lam treeTy ff))
  -- the first two children's pairs, at a depth of binders below the value
  let H (d : ℕ) : Term :=
    Term.listRec (Term.pair ffC ffC) (Term.pair (v 1) (Term.fst (v 0))) (Term.snd (v (2 + d)))
  -- context: the value, the context, the pair of the label and the children's pairs
  let r0 (d : ℕ) (R x : Term) : Term := Term.app (Term.app (Term.snd (Term.fst (H d))) R) x
  let r1 (d : ℕ) (R x : Term) : Term := Term.app (Term.app (Term.snd (Term.snd (H d))) R) x
  let raw0 (d : ℕ) : Term := Term.fst (Term.fst (H d))
  let test (k : ℕ) (t u : Term) : Term :=
    condT omega (call D.eqB [] [Term.fst (v 2), numeral k]) t u
  let body : Term :=
    test Kernel.Label.tyTree
      (ex treeTy (Term.lam treeTy (Term.eq (v 1) (pc P "Eval.valQuote" [v 0]))))
    (test Kernel.Label.tyUnit (Term.eq (v 0) (pc P "Eval.valUnit" []))
    (test Kernel.Label.tyProd
      (ex treeTy (Term.lam treeTy (ex treeTy (Term.lam treeTy
        (conj (Term.eq (v 2) (pc P "Eval.valPair" [v 1, v 0]))
          (conj (r0 2 (v 3) (v 1)) (r1 2 (v 3) (v 0))))))))
    (test Kernel.Label.tyArrow
      (all treeTy (Term.lam treeTy (imp (r0 1 (v 2) (v 0))
        (S.conv (Term.lam nat (apps (Term.snd (S.levelN (Term.fst (v 3)) (v 0))) [v 2, v 1]))
          (Term.lam treeTy (r1 2 (v 3) (v 0)))))))
    (test Kernel.Label.tyList
      (conj (truth o (pc P "Prelude.isSome" [pc P "Eval.listOf" [v 0]]))
        (S.allL (Term.lam treeTy (r0 1 (v 2) (v 0)))
          (call D.children [] [pc P "Prelude.get" [pc P "Eval.listOf" [v 0]]])))
    -- a datatype: a member's quotation, the datatype's atom read off its name
    (test 5
      (ex treeTy (Term.lam treeTy (conj (Term.eq (v 1) (pc P "Eval.valQuote" [v 0]))
        (truth o (pc P "Typing.memberOf" [Term.snd (v 2),
          nodeT (Term.pair (numeral 1) (call D.children [] [raw0 1])), v 0])))))
      ff)))))
  let rebuilt : Term := nodeT (Term.pair (Term.fst (v 0))
    (Term.listRec (nilT treeTy) (consT treeTy (Term.fst (v 1)) (v 0)) (Term.snd (v 0))))
  let step : Term := Term.pair rebuilt (Term.lam R (Term.lam treeTy body))
  ⟨0, [treeTy, R], exp treeTy omega, Term.app (Term.snd (Term.roseRec relC step (v 0))) (v 1)⟩

/-- The variables below a bound free in a term, the innermost first. -/
def freeVars (t : Term) (bound : ℕ := 32) : List ℕ :=
  (List.range bound).filter (Term.occurs t)

/-- A fold of rose trees in a term: its type, its step, the tree it folds, and the parameters it is
applied to where it is applied. -/
def firstFold : Term → Option (Tree × Term × Term × Option Term) := RoseTree.para fun l cs ↦
  match l, cs with
  | .app, [(f, rf), (x, rx)] => match f.label, f.children with
    | .roseRec c, [s, t] => some (c, s, t, some x)
    | _, _ => rf.orElse fun _ ↦ rx
  | .roseRec c, [(s, _), (t, _)] => some (c, s, t, none)
  | _, cs => cs.findSome? (·.2)

/-- A fold of the stage-1 pipeline at a tree: the program's function, the types of its context,
the tree's first, and its arguments in that context. -/
structure FoldSpec where
  /-- The function's name. -/
  name : String
  /-- The context's types, the tree's first. -/
  ctx : List Tree
  /-- The function's arguments in the context. -/
  args : List Term

/-- The folds the statement composes: the expansion, the typing, the erasure, the expansion of
numeral abbreviations, the resolution, and the test of source forms at the expansion of numeral
abbreviations, each at the tree of index 0. -/
def foldSpecs (P : Prog) (envTy : Tree) : List FoldSpec :=
  [⟨"Datatype.expandExpr", [treeTy, list treeTy], [v 1, v 0]⟩,
    ⟨"Typing.synIn", [treeTy, list treeTy, envTy], [v 2, v 1, v 0]⟩,
    ⟨"Datatype.eraseExpr", [treeTy], [v 0]⟩,
    ⟨"Reader.expandNums", [treeTy, list treeTy], [v 1, v 0]⟩,
    ⟨"Reader.resolve", [treeTy, list treeTy, list treeTy, list treeTy], [v 3, v 2, v 0, v 1]⟩,
    ⟨"srcForm", [treeTy, list treeTy],
      [Term.lam treeTy (pc P "Reader.expandNums" [v 2, v 0]), v 0]⟩]

/-- A fold's definitions: the argument the fold is applied to, in the parameters the argument
uses; and the fold at the tree, by its step, applied to the argument of index {lit}`argIdx`, in
the tree and those parameters, the tree's first. With them, the fold's type and step, the
parameters' positions in the spec's context, and the argument's application to the parameters in
the fold's definition's context. The step of a datatype's fold is the generic step of rose trees
and is kept; the argument holds the fold's cases. -/
def foldDefn (P : Prog) (f : FoldSpec) (argIdx : ℕ) :
    Option (Internal.Defn × Internal.Defn × Tree × Term × List ℕ × Term) := do
  let (C, s, _, F?) ← firstFold (weakNF P (baseNorm P) 0 f.ctx (pc P f.name f.args))
  let F ← F?
  let used := (freeVars F).filter (0 < ·)
  -- the parameters, the innermost first, as the argument's own context
  let renA (i : ℕ) : ℕ := (used.idxOf? i).getD i
  let (X, R) ← Internal.expParts C
  let ptys := used.map fun i ↦ f.ctx.getD i treeTy
  let tys := f.ctx.headD treeTy :: ptys
  let argD : Internal.Defn := ⟨0, ptys, X, Term.rename F renA⟩
  let Fc := call argIdx [] ((List.range used.length).reverse.map fun i ↦ v (i + 1))
  pure (argD, ⟨0, tys, R, Term.app (Term.roseRec C s (v 0)) Fc⟩, C, s, used, Fc)

/-- The definitions of the stage-1 pipeline the proofs keep folded: the folds the statement
composes and their steps at a node, each decided by a node's label or a list's head, whose
equations the vocabulary states one keyword at a time; and the lookups of names, which the proofs
decide by their results. -/
def foldedStage1 : List String :=
  ["Reader.resolveAtom", "Reader.resolveList", "Typing.synAtom", "Typing.synList",
    "Datatype.expandCase", "Datatype.expandCata", "Datatype.expandExpr", "Typing.synIn",
    "Datatype.eraseExpr", "Reader.expandNums", "Reader.resolve", "Reader.lookupAbbrev",
    "Reader.indexOf", "Reader.numeral", "Typing.lookupName", "Typing.hasName", "srcForm",
    "charsFixed"]

/-- The scope the reader resolves a term in, given the numeral abbreviations: the names of a named
context's variables, each as the reader reads it. -/
def scopeOf (P : Prog) (nums cx : Term) : Term :=
  Term.listRec (nilT treeTy)
    (consT treeTy (pc P "expName" [Term.subst nums fun i ↦ v (i + 2),
      apps ((primT Kernel.Prim.child).getD Term.star) [v 1, leafT bnilT]]) (v 0)) cx

/-- The type of a named context's entry, its second field, as the typing's lookup gives it. -/
def tyOf (p : Term) : Term :=
  apps ((primT Kernel.Prim.child).getD Term.star) [p, leafT (numeral 1)]

/-- The program extended for the datatype language's soundness: the fundamental lemma's
extension, and the relation at the datatype language's types, the relation of an environment to a
named context, and the relation of the definitions to the typing environment's definitions. -/
def extend3 (P : Prog) (S : Defs) : Option (Prog × Defs3) := do
  let o := P.o
  let all := Internal.Logic.all o
  let ex := Internal.Logic.ex o
  let conj := Internal.Logic.conj o
  let imp := Internal.Logic.imp o
  let some (.language envDefsD) := P.G.defs[P.idx "Typing.envDefs"]? | none
  let (envTy, _) ← Internal.expParts envDefsD.type
  let T : Defs3 := ⟨P.G.defs.length, envTy⟩
  let R := Defs3.ctxTy
  let defs : List Internal.Defn := [
    relDefn P S,
    -- the relation of an environment to a named context: at each position of the context, the
    -- environment has some value related at the type of the context's entry there
    ⟨0, [list treeTy, list treeTy, R], omega,
      all treeTy (Term.lam treeTy (imp
        (truth o (pc P "Prelude.isSome" [pc P "Prelude.nth" [v 2, v 0]]))
        (ex treeTy (Term.lam treeTy (conj
          (Term.eq (pc P "Prelude.nth" [v 2, v 1]) (pc P "Prelude.some" [v 0]))
          (Term.app (T.relT (v 4) (tyOf (pc P "Prelude.get" [pc P "Prelude.nth" [v 3, v 1]])))
            (v 0)))))))⟩,
    -- the relation of the definitions to the typing environment's definitions: at each name the
    -- environment gives some type, the names of the reader give an index, at which the
    -- definitions have some term whose evaluation in the empty environment converges to a value
    -- related at that type
    ⟨0, [list treeTy, envTy, R], omega,
      all treeTy (Term.lam treeTy (imp (truth o (pc P "Prelude.isSome"
          [pc P "Typing.lookupName" [v 0, pc P "Typing.envDefs" [v 2]]]))
        (ex treeTy (Term.lam treeTy (conj (Term.eq (pc P "Reader.indexOf" [v 1, v 2])
            (pc P "Prelude.some" [v 0]))
          (ex treeTy (Term.lam treeTy (conj
            (Term.eq (pc P "Prelude.nth" [Term.fst (v 5), v 1]) (pc P "Prelude.some" [v 0]))
            (S.conv (Term.lam nat (S.evN (Term.fst (v 6)) (v 0) (nilT treeTy) (v 1)))
              (T.relT (v 5) (pc P "Prelude.get"
                [pc P "Typing.lookupName" [v 2, pc P "Typing.envDefs" [v 4]]])))))))))))⟩] ++
    (← ((foldSpecs P envTy).zipIdx.mapM fun (f, k) ↦
      (foldDefn P f (T.argIdx k)).map fun r ↦ [r.1, r.2.1])).flatten ++ [
    -- the numeral abbreviations: at each name, the environment's numeral names having it gives an
    -- abbreviation, the atom of some numeral; and an abbreviation gives the name among them
    ⟨0, [list treeTy, envTy], omega,
      all treeTy (Term.lam treeTy (conj
        (imp (truth o (pc P "Typing.hasName" [v 0, pc P "Typing.envNums" [v 2]]))
          (ex (list treeTy) (Term.lam (list treeTy) (conj
            (Term.eq (pc P "Reader.lookupAbbrev" [v 1, v 2])
              (pc P "Prelude.some" [nodeT (Term.pair (numeral 1) (v 0))]))
            (truth o (pc P "Prelude.isSome" [pc P "Reader.numeral" [v 0]]))))))
        (imp (truth o (pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev" [v 0, v 1]]))
          (truth o (pc P "Typing.hasName" [v 0, pc P "Typing.envNums" [v 2]])))))⟩,
    -- the reader's names: each name with an index has a type among the environment's definitions
    ⟨0, [list treeTy, envTy], omega,
      all treeTy (Term.lam treeTy (imp
        (truth o (pc P "Prelude.isSome" [pc P "Reader.indexOf" [v 0, v 1]]))
        (truth o (pc P "Prelude.isSome"
          [pc P "Typing.lookupName" [v 0, pc P "Typing.envDefs" [v 2]]]))))⟩,
    -- the keywords: no name the numeral abbreviations abbreviate is reserved
    ⟨0, [list treeTy], omega,
      all treeTy (Term.lam treeTy (imp
        (truth o (pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev" [v 0, v 1]]))
        (imp (truth o (pc P "Prelude.isSome" [pc P "Reader.indexOf" [v 0,
            pc P "Reader.reservedNames" []]]))
          (Internal.Logic.ff o))))⟩]
  pure (⟨⟨P.G.prims, P.G.defs ++ defs.map .language, P.G.base⟩, P.o, P.idx, foldedStage1⟩, T)

/-- The number of quantifiers of {lit}`datatypeφ`. -/
def nQ : ℕ := 10

/-- The type and the resolved term of a form under the quantifiers of {lit}`datatypeφ`: the
typing's optional type of the form's expansion, and the reader's optional resolution of the
expansion's erasure, its numeral abbreviations expanded, in the scope of the context's names. -/
def datatypeTerms (P : Prog) (form : Term) : Term × Term :=
  let x := pc P "Prelude.get" [pc P "Datatype.expandExpr" [v 7, form]]
  (pc P "Typing.synIn" [v 6, v 5, x],
    pc P "Reader.resolve" [v 4, v 2,
      pc P "Reader.expandNums" [v 3, pc P "Datatype.eraseExpr" [x]], scopeOf P (v 3) (v 5)])

/-- The hypotheses and the conclusion of the soundness at a form, a term under the quantifiers of
{lit}`datatypeφ`: the relation's context R v0, the environment v1, the reader's names v2 and
numeral abbreviations v3 and type abbreviations v4, the named context v5, the typing environment
v6, the expansion's declarations v7, and the kernel's context v8 and globals' types v9. -/
def datatypeParts (P : Prog) (S : Defs) (T : Defs3) (form : Term) : List Term × Term :=
  let isSomeT (t : Term) : Term := truth P.o (pc P "Prelude.isSome" [t])
  let get (t : Term) : Term := pc P "Prelude.get" [t]
  let (ty, k) := datatypeTerms P form
  ([T.globT (v 0) (v 6) (v 2), T.envT (v 0) (v 5) (v 1), T.numsT (v 6) (v 3),
      T.defsT (v 6) (v 2),
      truth P.o (pc P "srcForm" [Term.lam treeTy (pc P "Reader.expandNums" [v 4, v 0]),
        get (pc P "Datatype.expandExpr" [v 7, form])]),
      isSomeT (pc P "Datatype.expandExpr" [v 7, form]), isSomeT ty, isSomeT k,
      isSomeT (pc P "Check.typeIn" [v 9, v 8, get k]), T.kwsT (v 3)],
    S.conv
      (Term.lam nat (S.evN (Term.fst (v 1)) (v 0) (v 2) (get (Term.subst k fun i ↦ v (i + 1)))))
      (T.relT (v 0) (get ty)))

/-- The soundness of the datatype language's typing at a source form, the variable of index 0:
for all globals' types and contexts of the kernel, declarations of the expansion, typing
environments, named contexts, type and numeral abbreviations and definitions' names of the reader,
environments and contexts of the relation, if the definitions are related to the typing
environment's and the environment to the named context, the reader's numeral abbreviations and
names cohere with the typing environment's, the form expands to a source form, its expansion
has a type, the expansion's erasure, its numeral abbreviations expanded, resolves in the scope of
the context's names, the resolved term has a type in the kernel, and no numeral abbreviation is a
keyword, then the resolved term's evaluation in the environment converges to a value related at
the type. The kernel's typing is the check that follows the reader in the pipeline, which rejects
the nodes the reader writes for a keyword at another arity than its own. -/
def datatypeφ (P : Prog) (S : Defs) (T : Defs3) : Term :=
  let (hs, goal) := datatypeParts P S T (v nQ)
  let q (A : Tree) (b : Term) : Term := Internal.Logic.all P.o A (Term.lam A b)
  q (list treeTy) (q (list treeTy) (q (list treeTy) (q T.envTy (q (list treeTy) (q (list treeTy)
    (q (list treeTy) (q (list treeTy) (q (list treeTy) (q Defs3.ctxTy
      (hs.foldr (Internal.Logic.imp P.o) goal))))))))))

/-- The map of a fold's definition over a list, the list of index 0 and the parameters after it,
the innermost first, at the fold's value type {lit}`R`. -/
def mapFold (T : Defs3) (k : ℕ) (R : Tree) (tys : List Tree) : Term :=
  match tys with
  | [] => Term.listRec (nilT R) (consT R (T.foldAt k [] (v 1)) (v 0)) (v 0)
  | [a] => Term.app (Term.listRec (Term.lam a (nilT R))
      (Term.lam a (consT R (T.foldAt k [v 0] (v 2)) (Term.app (v 1) (v 0)))) (v 0)) (v 1)
  | [a, b] => Term.app (Term.listRec (Term.lam (prod b a) (nilT R))
      (Term.lam (prod b a) (consT R (T.foldAt k [Term.fst (v 0), Term.snd (v 0)] (v 2))
        (Term.app (v 1) (v 0)))) (v 0)) (Term.pair (v 2) (v 1))
  | _ => Term.star

/-- The fusion of the map of the fold of index k at the children, applied to the parameters, with
the map of the fold's definition, by induction on the children; or the reason it fails. -/
def fusion (P : Prog) (T : Defs3) (k : ℕ) (ix : String → ℕ) (E : Array Internal.Entry) :
    Except String (Internal.Thm × Internal.Deriv) := do
  let some f := (foldSpecs P T.envTy)[k]? | throw "no fold"
  let some (_, d, C, st, _, F) := foldDefn P f (T.argIdx k)
    | throw "no definition"
  let rs := vRules P ix
  -- the map's object arguments, from the step's body
  let some θ := defnObjs D.mapApp st | throw "no map in the step"
  let Γ := list treeTy :: d.params.tail
  let lhs := call D.mapApp θ [Term.listRec (nilT C) (consT C (Term.roseRec C st (v 1)) (v 0))
    (v 0), F]
  let some l := nfE P.G E rs Γ lhs
    | let bare := (Internal.eval P.G E 0 [] 4096 .full Γ [] lhs).map fun (t, _) ↦ showT t
      -- the shortest prefix of the rules without a normal form, and its last rule
      let n := ((List.range (rs.length + 1)).find? fun n ↦
        (nfE P.G E (rs.take n) Γ lhs).isNone).getD 0
      let last := match rs[n - 1]? with
        | some (.thm j _) => match E[j]? with
          | some (Internal.Entry.language a) => s!"theorem {j}: {showT a.concl}"
          | _ => s!"theorem {j}"
        | some (.delta j) => s!"delta {j}"
        | some (.deltaBelow m _) => s!"deltaBelow {m}"
        | some _ => "another rule"
        | none => "none"
      throw s!"the left side has no normal form; without rules: {bare}; \
        the rules fail from {n} of {rs.length}, the last {last}"
  let some r := nfE P.G E rs Γ (mapFold T k d.type d.params.tail)
    | throw "the right side has no normal form"
  let some dv := Internal.byListIndHyp P.G E 0 0 1 (rs ++ [.delta (T.foldIdx k)]) 4096 Γ [] l r
    | throw s!"not proved by induction:\n{showT l}\n  =\n{showT r}"
  pure (⟨0, Γ, [], Term.eq l r⟩, dv)

/-- Where a fold rebuilds its tree as the first component of its values: nowhere, in the step,
or in the argument it is applied to. -/
inductive Rebuild where
  /-- The fold's values are not pairs. -/
  | none
  /-- The step pairs the node rebuilt with the argument's value. -/
  | step
  /-- The argument pairs the node rebuilt with another value. -/
  | argument
  /-- The argument gives a function whose values pair the node rebuilt with another value. -/
  | applied

/-- The vocabulary of the fold of index k: the fusion of the map of the folds at the children,
applied to the parameters, with the map of the fold's definition, by induction on the children;
the fold's definition at a node, unfolded at the root alone; and, where the fold's values pair
the node rebuilt with another value, the rebuilding lemmas. -/
def foldVocab (P : Prog) (T : Defs3) (k : ℕ) (rebuilds : Rebuild) : List Step :=
  match (foldSpecs P T.envTy)[k]? with
  | none => []
  | some f =>
  match foldDefn P f (T.argIdx k) with
  | none => []
  | some (_, d, C, st, _, F) =>
  let tys := d.params.tail
  let tag := s!"fold{k}"
  let ps (n : ℕ) : List Term := (List.range tys.length).reverse.map fun i ↦ v (i + 1 + n)
  let fus : Step := (s!"{tag}Fus", fun ix E ↦ (fusion P T k ix E).toOption)
  let node : Step := genRoot P s!"{tag}Node" ([list treeTy, bitsTy] ++ tys)
    (T.foldAt k (ps 1) (nodeT (Term.pair (v 1) (v 0)))) (T.foldIdx k) [s!"{tag}Fus"]
  let rebuild : List Step := match rebuilds, Internal.expParts C, tys with
    | .step, some (FX, _), _ => rebuildLemmas P tag FX
        (fun x G ↦ Term.fst (Term.app (Term.roseRec C st x) G)) tys
        (T.foldAt k (ps 0) (v 0)) F (some (T.foldIdx k))
    -- the parameters as one value, the fold's argument unfolded
    | .argument, _, [a] => rebuildLemmas P tag a
        (fun x G ↦ Term.fst (T.foldAt k [G] x)) tys (T.foldAt k (ps 0) (v 0)) (v 1) none
        fun ix ↦ [.thm (ix s!"{tag}Node") [], .delta (T.argIdx k)]
    | .argument, _, [a, b] => rebuildLemmas P tag (prod b a)
        (fun x G ↦ Term.fst (T.foldAt k [Term.fst G, Term.snd G] x)) tys
        (T.foldAt k (ps 0) (v 0)) (Term.pair (v 2) (v 1)) none
        fun ix ↦ [.thm (ix s!"{tag}Node") [], .delta (T.argIdx k)]
    -- the function's argument a variable after the tree
    | .applied, some (_, R), [] => match Internal.expParts R with
      | some (FA, _) => rebuildLemmas P tag FA
          (fun x G ↦ Term.fst (Term.app (T.foldAt k [] x) G)) [FA]
          (Term.app (T.foldAt k [] (v 0)) (v 1)) (v 1) none
          fun ix ↦ [.thm (ix s!"{tag}Node") [], .delta (T.argIdx k)]
      | none => []
    | _, _, _ => []
  fus :: node :: rebuild

/-- The names of the datatype language's vocabulary used as rules after it. -/
def vocab3 : List String :=
  (List.range nFolds).flatMap fun k ↦
    [s!"fold{k}Def", s!"fold{k}Node", s!"fold{k}Fst", s!"fold{k}Kids", s!"atom{k}"]

/-- The rules of the datatype language's vocabulary among the first {lit}`proved` theorems: each
stage function as its fold, each fold at a node, its rebuilding and its children's where it
rebuilds, each stage function at an atom, and the rules of the normalization proof's
vocabulary. -/
def vRules3 (P : Prog) (ix : String → ℕ) (proved : ℕ) : List Internal.NormRule :=
  (vocab3 ++ ["charsMap", "handlerAtom3"]).filterMap
    (fun nm ↦ if 0 < ix nm ∧ ix nm < proved then some (.thm (ix nm) []) else none) ++ vRules P ix

/-- The prelude's right fold of a list of elements of type {lit}`A` into a value of type
{lit}`B`, by a function and a value. -/
def foldrT (A B : Tree) (f z xs : Term) : Term :=
  let X := prod (exp A (exp B B)) B
  Term.app (Term.listRec (Term.lam X (Term.snd (v 0)))
    (Term.lam X (Term.app (Term.app (Term.fst (v 0)) (v 2)) (Term.app (v 1) (v 0)))) xs)
    (Term.pair f z)

/-- How a rebuilding fold's values at the children of a node give the children: the first
components, by a fold of lists or by the prelude's right fold; or the first components of the
values' applications to the variable after the list, by the prelude's right folds. -/
inductive KidsShape where
  /-- The first components by a fold of lists. -/
  | list
  /-- The first components by the prelude's right fold. -/
  | foldr
  /-- The values applied to the variable after the list, then the first components, each by the
  prelude's right fold. -/
  | applied

/-- The first components of a rebuilding fold's values at the children of a node, the list of
index 0, its parameters or the argument of its values after it, are the children. -/
def kidsEq (P : Prog) (T : Defs3) (k : ℕ) (shape : KidsShape) : Step :=
  (s!"fold{k}Kids", fun ix E ↦ do
    let f ← (foldSpecs P T.envTy)[k]?
    let (_, d, _, _, _, _) ← foldDefn P f (T.argIdx k)
    let tys := d.params.tail
    let L := list treeTy
    let M := mapFold T k d.type tys
    let firstsOf (A : Tree) (xs : Term) : Term :=
      foldrT A L (Term.lam A (Term.lam L (consT treeTy (Term.fst (v 1)) (v 0)))) (nilT treeTy) xs
    let (Γ, firsts) ← match shape with
      | .list => some (L :: tys, Term.listRec (nilT treeTy) (consT treeTy (Term.fst (v 1)) (v 0)) M)
      | .foldr => some (L :: tys, firstsOf d.type M)
      | .applied => do
        let (FA, B) ← Internal.expParts d.type
        -- the argument the variable of index 1, two binders deeper in the function
        let applied := foldrT d.type (list B)
          (Term.lam d.type (Term.lam (list B) (consT B (Term.app (v 1) (v 3)) (v 0)))) (nilT B) M
        some ([L, FA], firstsOf B applied)
    let rs := vRules3 P ix E.size
    let some l := nfE P.G E rs Γ firsts | dbgTrace s!"fold{k}Kids: left" fun _ ↦ none
    let some dv := Internal.byListIndHyp P.G E 0 0 1 rs 4096 Γ [] l (v 0)
      | dbgTrace s!"fold{k}Kids: {showT l}" fun _ ↦ none
    pure (⟨0, Γ, [], Term.eq l (v 0)⟩, dv))

/-- The program, translated and extended for the datatype language's soundness. -/
def extended3 : Option (Prog × Defs × Defs3) := do
  let ds ← bundled Geb.Kernel.Stage0Tests.bundler.toList programText.toList
  let (P, S) ← extendedOf ds fun name ↦ (defIndex ds name.toList).getD 0
  let (P3, T) ← extend3 P S
  pure (P3, S, T)

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let t₀ ← IO.monoMsNow
  let some (P, _, T) := extended3 | throwError "the program does not extend"
  let t₁ ← IO.monoMsNow
  let new := P.G.defs.drop T.q
  let checks := new.zipIdx.map fun (e, i) ↦ match e with
    | .language d => d.checks { P.G with defs := P.G.defs.take (T.q + i) }
    | _ => false
  logInfo m!"extended in {t₁ - t₀} ms: {P.G.defs.length} definitions, the new ones check {checks}"
  let some (_, S, _) := extended3 | throwError "the program does not extend"
  logInfo m!"the statement is a formula: \
    {Internal.typeIn P.G 0 [treeTy] (datatypeφ P S T) == some omega}"

/-- A term with an application of a rose tree's fold to an argument replaced, the first child
containing one replaced at each node, with whether the term contains one. -/
def replaceFold (by_ : Term) (t : Term) : Term :=
  (RoseTree.para (fun (l : Internal.Label) (cs : List (Term × (Term × Bool))) ↦
    let isFold := match l, cs with
      | .app, [(f, _), _] => match f.label with
        | .roseRec _ => true
        | _ => false
      | _, _ => false
    if isFold then (by_, true) else
    match cs.findIdx? (·.2.2) with
    | some i => (RoseTree.node l (cs.mapIdx fun j c ↦ if j = i then c.2.1 else c.1), true)
    | none => (RoseTree.node l (cs.map Prod.fst), false)) t).1

/-- A stage function in terms of its fold: the function at its arguments equal to its weak normal
form with the fold replaced by the fold's definition, both sides reducing to one normal form with
the function, the fold's definition and its argument unfolded and the other stage functions kept
folded. -/
def foldDefEq (P : Prog) (T : Defs3) (k : ℕ) : Step :=
  (s!"fold{k}Def", fun _ E ↦ do
    let f ← (foldSpecs P T.envTy)[k]?
    let used ← (foldDefn P f (T.argIdx k)).map (·.2.2.2.2.1)
    let ps := used.reverse.map v
    let lhs := pc P f.name f.args
    let W := replaceFold (T.foldAt k ps (v 0)) (weakNF P (baseNorm P) 0 f.ctx lhs)
    let rs := vBase P ++ [.delta (P.idx f.name), .delta (T.argIdx k), .delta (T.foldIdx k)]
    let some dv := byMode .full P.G E 0 rs f.ctx [] lhs W
      | dbgTrace s!"fold{k}Def: unequal" fun _ ↦ none
    pure (⟨0, f.ctx, [], Term.eq lhs W⟩, dv))

/-- An atom's node over the characters of index 0. -/
def atomT : Term := nodeT (Term.pair (numeral 1) (v 0))

/-- Each stage function at an atom's node, the characters of index 0: its context and term. -/
def atomSpecs (P : Prog) (envTy : Tree) : List (List Tree × Term) :=
  [([list treeTy, list treeTy], pc P "Datatype.expandExpr" [v 1, atomT]),
    ([list treeTy, list treeTy, envTy], pc P "Typing.synIn" [v 2, v 1, atomT]),
    ([list treeTy], pc P "Datatype.eraseExpr" [atomT]),
    ([list treeTy, list treeTy], pc P "Reader.expandNums" [v 1, atomT]),
    ([list treeTy, list treeTy, list treeTy, list treeTy],
      pc P "Reader.resolve" [v 3, v 2, atomT, v 1]),
    ([list treeTy, list treeTy],
      pc P "srcForm" [Term.lam treeTy (pc P "Reader.expandNums" [v 2, v 0]), atomT])]

/-- The equations of the stage functions at an atom's node: the term's normal form by the
vocabulary's rules, and its normal form with the fold's argument unfolded as well. -/
def atomEqs (P : Prog) (T : Defs3) : List Step :=
  (atomSpecs P T.envTy).zipIdx.map fun ((Γ, t), k) ↦ (s!"atom{k}", fun ix E ↦ do
    let rs := vRules3 P ix E.size
    let some l := nfE P.G E rs Γ t | dbgTrace s!"atom{k}: left" fun _ ↦ none
    let some (r, d, _) := Internal.eval P.G E 0 (rs ++ [.delta (T.argIdx k)]) 4096 .full Γ [] l
      | dbgTrace s!"atom{k}: right" fun _ ↦ none
    pure (⟨0, Γ, [], Term.eq l r⟩, nd .join [d, nd .refl]))

/-- The characters of an atom, the list of index 0, expanded at the numeral abbreviations of
index 1, as the source forms' test maps them and as the expansion of a node's children does. -/
def charsMap (P : Prog) (T : Defs3) : Step :=
  ("charsMap", fun ix E ↦ do
    let f ← (foldSpecs P T.envTy)[3]?
    let (_, d, _, _, _, _) ← foldDefn P f (T.argIdx 3)
    let L := list treeTy
    let Γ := [L, L]
    let rs := vRules3 P ix E.size
    let mapped := foldrT treeTy L
      (Term.lam treeTy (Term.lam L (consT treeTy (pc P "Reader.expandNums" [v 3, v 1]) (v 0))))
      (nilT treeTy) (v 0)
    let some l := nfE P.G E rs Γ mapped | dbgTrace "charsMap: left" fun _ ↦ none
    let some r := nfE P.G E rs Γ (mapFold T 3 d.type d.params.tail)
      | dbgTrace "charsMap: right" fun _ ↦ none
    let some dv := Internal.byListIndHyp P.G E 0 0 1 rs 4096 Γ [] l r
      | dbgTrace s!"charsMap: {showT l}\n  = {showT r}" fun _ ↦ none
    pure (⟨0, Γ, [], Term.eq l r⟩, dv))

/-- The characters of an atom, the list of index 0, fixed by the expansion of the numeral
abbreviations of index 1 when the source forms' test says so: the test unfolded to the equality
of the names, sound, whose children are the expanded characters and the characters. -/
def charsFixedEq (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("charsFixedEq", fun ix E ↦ do
    let f ← (foldSpecs P T.envTy)[3]?
    let (_, d, _, _, _, _) ← foldDefn P f (T.argIdx 3)
    let L := list treeTy
    let Γ := [L, L]
    let fn := Term.lam treeTy (pc P "Reader.expandNums" [v 2, v 0])
    let φ := Internal.Logic.imp P.o (truth P.o (pc P "charsFixed" [fn, v 0]))
      (Term.eq (mapFold T 3 d.type d.params.tail) (v 0))
    let K : Kit := ⟨P, S, E, ix,
      (vocab3 ++ ["charsMap"]).filter fun nm ↦ 0 < ix nm ∧ ix nm < E.size⟩
    let mapped := foldrT treeTy L
      (Term.lam treeTy (Term.lam L (consT treeTy (pc P "Reader.expandNums" [v 3, v 1]) (v 0))))
      (nilT treeTy) (v 0)
    let A := nodeT (Term.pair (numeral 0) mapped)
    let B := nodeT (Term.pair (numeral 0) (v 0))
    let childrenT ← primT Kernel.Prim.children
    let deducer : Deducer := dImpI K.L fun Γ Φ ψ ↦
      -- the test unfolded, then the equality's soundness at the two names
      dRwHyp (evalRw K.G K.E (K.rules Φ ++ [.delta (P.idx "charsFixed")]) .full) 0
        (K.cutThm "equalSound" (fun _ ↦ [A]) (K.allEΓ (fun _ ↦ B) (K.impE (K.byHyp 0)
          (fun Γ Φ ψ ↦ K.image (Φ.length - 1) (fun t ↦ apps childrenT [t]) K.byNorm Γ Φ ψ))))
        Γ Φ ψ
    let some dv := deducer Γ [] φ | dbgTrace "charsFixedEq: not proved" fun _ ↦ none
    pure (⟨0, Γ, [], φ⟩, dv))

/-- The reflexivity of the equality of trees and its symmetry: the equality of bitstrings
reflexive, by induction on the bitstring, its bits split; the elementwise equality of a list with
itself given each element's reflexivity, by induction on the list; the induction hypothesis on rose
trees as every child's reflexivity; the equality of trees reflexive, by induction on the tree, its
label's test decided; and the equality symmetric, by its soundness and reflexivity. -/
def equalReflLemmas (P : Prog) (S : Defs) : List Step :=
  let kit (ix : String → ℕ) (E : Array Internal.Entry) : Kit := ⟨P, S, E, ix, []⟩
  let reflφ (K : Kit) : Term := K.truthB (call D.equal [] [v 0, v 0])
  [("eqBRefl", fun ix E ↦ do
      let K := kit ix E
      let φ := K.truthB (call D.eqB [] [v 0, v 0])
      let d₀ ← K.solve 2 [] [] (Term.subst φ (Internal.instVar (Term.arr 0 [bitTy] Term.star)))
      -- a construction: its bit split, each case by the induction hypothesis
      let byIH : Deducer := fun Γ Φ ψ ↦ (K.solve 2 Γ Φ ψ).orElse fun _ ↦ K.byHyp 0 Γ Φ ψ
      let cons : Deducer := fun Γ Φ ψ ↦ (K.bitCase (v 0) byIH byIH Γ Φ ψ).orElse fun _ ↦
        K.bitCase (v 1) byIH byIH Γ Φ ψ
      let d₁ ← cons [list bitTy, bitTy] [Internal.weakenElem φ] (Internal.listConsAt 1 bitTy φ)
      pure (⟨0, [bitsTy], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁])),
    ("allZipRefl", fun ix E ↦ do
      let K := kit ix E
      let L := K.L
      let φ := Internal.Logic.imp P.o (S.allL (Term.lam treeTy (reflφ K)) (v 0))
        (K.truthB (call D.allZip [] [← mapEq (v 0), v 0]))
      let d₀ ← dImpI L (K.solve 2) [] [] (Term.subst φ (Internal.instVar
        (Term.arr 0 [treeTy] Term.star)))
      -- a construction: the head's reflexivity and the rest's from the hypothesis on all the
      -- elements; the head's test decided, empty refuted; the rest's by the induction hypothesis
      let cons : Deducer := dImpI L fun Γ₁ Φ₁ ψ₁ ↦
        let h := Φ₁.length - 1
        dRwHyp (evalRw K.G K.E (K.rules Φ₁) .full) h (K.conjE fun Γ Φ ψ ↦
          -- the conjunction unfolded: the head's formula, then the rest's
          let hHead := Φ.length - 2
          let hRest := Φ.length - 1
          -- the context's outermost variable is the head
          let head := v (Γ.length - 1)
          let X := (nfE K.G K.E (K.rules Φ) Γ (call D.equal [] [head, head])).getD Term.star
          K.listCase bitTy X (K.hypFalse hHead)
            (dImpE L 0 (K.byHyp hRest) fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ) Γ Φ ψ) Γ₁ Φ₁ ψ₁
      let d₁ ← cons [list treeTy, treeTy] [Internal.weakenElem φ]
        (Internal.listConsAt 1 treeTy φ)
      pure (⟨0, [list treeTy], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁])),
    roseAllFor P S "roseAllRefl" (reflφ ⟨P, S, #[], fun _ ↦ 0, []⟩),
    ("equalRefl", fun ix E ↦ do
      let K := kit ix E
      let φ := reflφ K
      let withLast (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
      -- context: the children, the label
      let node : Deducer := fun Γ Φ ψ ↦
        -- the label and the children, the outermost variables
        let l := v (Γ.length - 1)
        let cs (Γ : List Tree) : Term := v (Γ.length - 2)
        let X := (nfE K.G K.E (vRules P ix) Γ (call D.eqB [] [l, l])).getD Term.star
        K.cutThm "eqBRefl" (fun _ ↦ [l]) (withLast fun hl ↦
          K.listCase bitTy X (K.hypFalse hl)
            ((K.cutThm "roseAllRefl" (fun Γ ↦ [cs Γ]) (K.impE dHyp
              (withLast fun all ↦
              K.cutThm "allZipRefl" (fun Γ ↦ [cs Γ])
                (K.impE (fun _ _ _ ↦ some (nd (.hyp all)))
                  fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ)))))) Γ Φ ψ
      let d ← node [list treeTy, bitsTy] [Internal.roseHyp 0 1 φ]
        (Internal.roseNodeAt 2 treeTy bitsTy φ)
      pure (⟨0, [treeTy], [], φ⟩, nd (.roseIndHyp 2 0 1) [d])),
    ("equalSymm", fun ix E ↦ do
      let K := kit ix E
      let L := K.L
      let φ := Internal.Logic.imp P.o (K.truthB (call D.equal [] [v 1, v 0]))
        (K.truthB (call D.equal [] [v 0, v 1]))
      let d ← dImpI L (K.cutThm "equalSound" (fun _ ↦ [v 1]) (K.allEΓ (fun _ ↦ v 0)
        (K.impE (K.byHyp 0) (K.cutThm "equalRefl" (fun _ ↦ [v 0])
          (fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ))))) [treeTy, treeTy] [] φ
      pure (⟨0, [treeTy, treeTy], [], φ⟩, d))]

/-- A term with each occurrence of a subterm replaced. -/
def replaceSub (u w : Term) (t : Term) : Term :=
  RoseTree.para (fun (l : Internal.Label) (cs : List (Term × Term)) ↦
    let orig := RoseTree.node l (cs.map Prod.fst)
    if orig == u then w else RoseTree.node l (cs.map Prod.snd)) t

/-- The equations of a program's fold of lists, kept folded, at the empty list and at a
construction: the function of {lit}`name` at the arguments {lit}`args` of the list, in the
context {lit}`Γ` after the list's head and tail, the tail of index 0 and the head of index 1; at
the empty list its normal form with the function unfolded, and at the construction that normal
form with the function's normal form at the tail replaced by the function at the tail. -/
def listFoldEqs (P : Prog) (tag name : String) (Γ : List Tree) (elem : Tree)
    (args : Term → List Term) : List Step :=
  let rsU := vBase P ++ [.delta (P.idx name)]
  let nf (G : Internal.Globals) (E : Array Internal.Entry) (Γ : List Tree) (t : Term) :
      Option Term := (Internal.eval G E 0 rsU 4096 .full Γ [] t).map Prod.fst
  let ΓN := Γ.drop 2
  let lower (t : Term) : Term := Term.subst t fun i ↦ v (i - 2)
  [(s!"{tag}Nil", fun _ E ↦ do
      let t := pc P name ((args (nilT elem)).map lower)
      let r ← nf P.G E ΓN t
      let d ← byMode .full P.G E 0 rsU ΓN [] t r
      pure (⟨0, ΓN, [], Term.eq t r⟩, d)),
    (s!"{tag}Cons", fun _ E ↦ do
      let t := pc P name (args (consT elem (v 1) (v 0)))
      let tail := pc P name (args (v 0))
      let r ← nf P.G E Γ t
      let rt ← nf P.G E Γ tail
      let r' := replaceSub rt tail r
      let d ← byMode .full P.G E 0 rsU Γ [] t r'
      pure (⟨0, Γ, [], Term.eq t r'⟩, d))]

/-- The names of the lookups' equations at the empty list and at a construction. -/
def lookupEqNames : List String :=
  ["indexOfNil", "indexOfCons", "lookupNameNil", "lookupNameCons"]

/-- The lookups' equations: the reader's index of a name among names, and the typing's type of a
name among named types; each in the context of the tail, the head and the name. -/
def lookupEqs (P : Prog) : List Step :=
  let Γ := [list treeTy, treeTy, treeTy]
  listFoldEqs P "indexOf" "Reader.indexOf" Γ treeTy (fun xs ↦ [v 2, xs]) ++
    listFoldEqs P "lookupName" "Typing.lookupName" Γ treeTy (fun xs ↦ [v 2, xs])

/-- A deducer's failure traced: the message, the goal in normal form and the last hypotheses. -/
def traceK (K : Kit) (msg : String) : Deducer := fun Γ Φ ψ ↦
  dbgTrace s!"{msg}: {Γ.length} vars, {Φ.length} hyps; goal {
    ((evalRw K.G K.E (K.rules Φ) .full Γ Φ ψ).map fun r ↦ showT r.1).getD "none"}
    last hyps {(Φ.drop (Φ.length - 8)).map showT}"
    fun _ ↦ none

/-- A deducer, its failure traced with a message. -/
def linkK (K : Kit) (msg : String) (k : Deducer) : Deducer := fun Γ Φ ψ ↦
  (k Γ Φ ψ).orElse fun _ ↦ traceK K msg Γ Φ ψ

/-- The truth of a test decided, its label's bitstring empty, by {lit}`kF`, or not, by {lit}`kT`;
where the test's normal form by the base rules and the rebuildings differs from the vocabulary's,
its equation with that normal form cut in first, so that the case's equation applies to both. -/
def decideTest (K : Kit) (t : List Tree → Term) (kF kT : Deducer) : Deducer := fun Γ Φ ψ ↦
  let lt := call D.lab [] [t Γ]
  let cheap := ["kids", "mapId", "lambek"].map (fun nm ↦ Internal.NormRule.thm (K.ix nm) []) ++
    [.thm (K.ix "rebTail") [treeTy]] ++ rebRules K.ix ++ vBase K.P
  match nfE K.G K.E (K.rules []) Γ lt, nfE K.G K.E cheap Γ lt with
  | some X, some Xc =>
    let split := K.listCase bitTy X kF kT
    if Xc == X then split Γ Φ ψ else do
      let d ← byMode .full K.G K.E 0 (K.rules []) Γ [] Xc X
      dCut (Term.eq Xc X) d split Γ Φ ψ
  | _, _ => dbgTrace s!"a test without a normal form: {showT (t Γ)}" fun _ ↦ none

/-- The last hypothesis normalized without itself. -/
def normLastK (K : Kit) (k : Deducer) : Deducer := fun Γ Φ ψ ↦
  dRwHyp (evalRw K.G K.E (K.rulesEx Φ (Φ.length - 1)) .full) (Φ.length - 1) k Γ Φ ψ

/-- Some hypothesis normalized to falsity, the last first. -/
def anyFalse (K : Kit) : Deducer := fun Γ Φ ψ ↦
  (List.range Φ.length).reverse.findSome? fun h ↦ K.hypFalse h Γ Φ ψ

/-- The negation of a formula, its implying falsity. -/
def notT (o : ℕ) (φ : Term) : Term := Internal.Logic.imp o φ (Internal.Logic.ff o)

/-- The truth of a test decided in the hypotheses' normal form: its label's bitstring empty, by
{lit}`kF`, or not, by {lit}`kT`, the case's equation the last hypothesis. -/
def decideIn (K : Kit) (t : List Tree → Term) (kF kT : Deducer) : Deducer := fun Γ Φ ψ ↦
  match evalRw K.G K.E (K.rules Φ) .full Γ Φ (call D.lab [] [t Γ]) with
  | some (X, _) => K.listCase bitTy X kF kT Γ Φ ψ
  | none => dbgTrace s!"a test without a normal form: {showT (t Γ)}" fun _ ↦ none

/-- A name the numeral abbreviations do not abbreviate, with a type in a named context, has an
index in the reader's scope of the context's names: by induction on the context; at a
construction, the head's name equal to the name or not. Equal, the scope's head is the name,
which is not abbreviated, at the first index; unequal, the induction hypothesis gives the rest's
index, shifted where the scope's head is not the name. -/
def lookupAgreeA (P : Prog) (S : Defs) : Step :=
  ("lookupAgreeA", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, lookupEqNames⟩
    let L := K.L
    let o := P.o
    let isSomeT (t : Term) : Term := truth o (pc P "Prelude.isSome" [t])
    let imp := Internal.Logic.imp o
    -- under the quantifiers: the name v0, the numeral abbreviations v1, the context v2
    let φ := Internal.Logic.all o (list treeTy) (Term.lam (list treeTy)
      (Internal.Logic.all o treeTy (Term.lam treeTy (imp
        (notT o (isSomeT (pc P "Reader.lookupAbbrev" [v 0, v 1])))
        (imp (isSomeT (pc P "Typing.lookupName" [v 0, v 2]))
          (isSomeT (pc P "Reader.indexOf" [v 0, scopeOf P (v 1) (v 2)])))))))
    let childT ← primT Kernel.Prim.child
    let equalT ← primT Kernel.Prim.equal
    let lastFalse : Deducer := fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ
    let d₀ ← dAllI L (dAllI L (dImpI L (dImpI L (linkK K "agreeA empty" lastFalse)))) [] []
      (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
    -- context: the name, the abbreviations, the tail, the head; hypotheses: the induction
    -- hypothesis, the quantifiers' truths, the name's not being abbreviated, its type's
    let cons : Deducer := dAllI L (dAllI L (dImpI L (dImpI L fun Γ₁ Φ₁ ψ₁ ↦
      let g := Φ₁.length - 2
      let ty := Φ₁.length - 1
      let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
      let nums := at_ 2
      let n := at_ 3
      let m (Γ : List Tree) : Term := apps childT [at_ 0 Γ, leafT bnilT]
      let eN (Γ : List Tree) : Term := pc P "expName" [nums Γ, m Γ]
      -- the head's name the name: the name not abbreviated, the scope's head is the name
      let equalCase : Deducer := linkK K "agreeA equal" <|
        K.cutThm "equalSound" (fun Γ ↦ [m Γ]) (K.allEΓ n (K.impE (K.solve 3) (normLastK K
          (decideIn K (fun Γ ↦ pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev" [n Γ, nums Γ]])
            (K.cutThm "equalRefl" (fun Γ ↦ [n Γ])
              (decideIn K (fun Γ ↦ apps equalT [n Γ, n Γ]) (anyFalse K) (K.solve 3)))
            (dImpE L g (K.solve 3) lastFalse)))))
      -- unequal: the induction hypothesis at the abbreviations and the name; the scope's head's
      -- test decided, then the rest's index's
      let rest : Deducer := linkK K "agreeA rest" fun Γ Φ ψ ↦
        dAllE L K.G K.E 0 (nums Γ) (K.allEΓ n (K.impE (K.byHyp g) (K.impE (K.byHyp ty)
          (decideIn K (fun Γ ↦ apps equalT [n Γ, eN Γ])
            (decideIn K (fun Γ ↦ pc P "Prelude.isSome"
                [pc P "Reader.indexOf" [n Γ, scopeOf P (nums Γ) (at_ 1 Γ)]])
              (anyFalse K) (K.solve 3))
            (K.solve 3))))) Γ Φ ψ
      linkK K "agreeA construction" (decideIn K (fun Γ ↦ apps equalT [m Γ, n Γ]) rest equalCase)
        Γ₁ Φ₁ ψ₁)))
    let d₁ ← cons [list treeTy, treeTy] [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, [list treeTy], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The index the evaluator reads a variable at: the leaf of the label of an optional index's
value. -/
def leafIndex (P : Prog) (i : Term) : Term := leafT (call D.lab [] [pc P "Prelude.get" [i]])

/-- A name that is neither a numeral nor abbreviated, with an index in the reader's scope of a
named context's names, has in the context the type of the entry at that index: by induction on
the context; at a construction, the scope's head equal to the name or not. Equal, the head's name
is the name, since an abbreviated head's is a numeral's, and the index is the first; unequal, the
head's name is not the name, since the name is not abbreviated, and the induction hypothesis gives
the rest's entry, at the index's predecessor. -/
def lookupAgreeB (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("lookupAgreeB", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, lookupEqNames ++ ["nthConsSucc"]⟩
    let L := K.L
    let o := P.o
    let isSomeT (t : Term) : Term := truth o (pc P "Prelude.isSome" [t])
    let imp := Internal.Logic.imp o
    let conj := Internal.Logic.conj o
    -- under the quantifiers: the name v0, the typing environment v1, the abbreviations v2, the
    -- context v3
    let idx := pc P "Reader.indexOf" [v 0, scopeOf P (v 2) (v 3)]
    let entry := pc P "Prelude.nth" [v 3, leafIndex P idx]
    let φ := Internal.Logic.all o (list treeTy) (Term.lam (list treeTy)
      (Internal.Logic.all o T.envTy (Term.lam T.envTy
      (Internal.Logic.all o treeTy (Term.lam treeTy (imp (T.numsT (v 1) (v 2))
        (imp (notT o (isSomeT (pc P "Reader.numeral" [call D.children [] [v 0]])))
          (imp (notT o (isSomeT (pc P "Reader.lookupAbbrev" [v 0, v 2])))
            (imp (isSomeT idx)
              (conj (Term.eq (pc P "Typing.lookupName" [v 0, v 3])
                  (pc P "Prelude.some" [tyOf (pc P "Prelude.get" [entry])]))
                (isSomeT entry)))))))))))
    let childT ← primT Kernel.Prim.child
    let equalT ← primT Kernel.Prim.equal
    let lastFalse : Deducer := fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ
    let d₀ ← dAllI L (dAllI L (dAllI L (dImpI L (dImpI L (dImpI L (dImpI L
      (linkK K "agreeB empty" lastFalse))))))) [] []
      (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
    -- context: the name, the typing environment, the abbreviations, the tail, the head;
    -- hypotheses: the induction hypothesis, the quantifiers' truths, the coherence, the name's
    -- being no numeral and not abbreviated, its index's truth
    let cons : Deducer := dAllI L (dAllI L (dAllI L (dImpI L (dImpI L (dImpI L (dImpI L
      fun Γ₁ Φ₁ ψ₁ ↦
      let hN := Φ₁.length - 4
      let gNum := Φ₁.length - 3
      let gAb := Φ₁.length - 2
      let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
      let nums := at_ 2
      let Ev := at_ 3
      let n := at_ 4
      let m (Γ : List Tree) : Term := apps childT [at_ 0 Γ, leafT bnilT]
      let eN (Γ : List Tree) : Term := pc P "expName" [nums Γ, m Γ]
      let abbrevOf (t : List Tree → Term) (Γ : List Tree) : Term :=
        pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev" [t Γ, nums Γ]]
      -- the name the scope's head, an abbreviated head's: the coherence at the head's name, its
      -- abbreviation a numeral's atom, whose name the name is, refuting the name's being none
      let numeralHead : Deducer := linkK K "agreeB numeral head" fun Γ Φ ψ ↦
        dRwHyp (evalRw K.G K.E [.delta (T.q + 3 + 2 * nFolds)] .head) hN
          (K.allEΓ m (K.conjE fun Γ Φ ψ ↦
            let a₁ := Φ.length - 2
            let a₂ := Φ.length - 1
            dImpE L a₂ (K.solve 3) (dImpE L a₁ (fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ)
              (K.exE (K.conjE fun Γ Φ ψ ↦
                dRwHyp (evalRw K.G K.E (K.rules (Φ.take (Φ.length - 2))) .full)
                  (Φ.length - 2) (dImpE L gNum (fun Γ Φ ψ ↦ K.byHyp (Φ.length - 2) Γ Φ ψ)
                    lastFalse) Γ Φ ψ))) Γ Φ ψ)) Γ Φ ψ
      -- the scope's head the name: the name the head's name, its entry the first
      let headCase : Deducer := linkK K "agreeB scope's head" <|
        K.cutThm "equalSound" (fun Γ ↦ [n Γ]) (K.allEΓ eN (K.impE (K.solve 3) (normLastK K
          (decideIn K (abbrevOf m)
            (K.cutThm "equalRefl" (fun Γ ↦ [m Γ])
              (decideIn K (fun Γ ↦ apps equalT [m Γ, m Γ]) (anyFalse K) (K.solve 4)))
            numeralHead))))
      -- the scope's head not the name: the head's name not the name, the induction hypothesis
      let restCase : Deducer := linkK K "agreeB rest" fun Γ₂ Φ₂ ψ₂ ↦
        let hcR := Φ₂.length - 1
        -- the head's name the name refuted: the name not abbreviated, the reader's test of the
        -- name with itself
        let headName : Deducer := linkK K "agreeB head's name" <|
          K.cutThm "equalSound" (fun Γ ↦ [m Γ]) (K.allEΓ n (K.impE (K.solve 3) (normLastK K
            (decideIn K (abbrevOf n)
              (fun Γ Φ ψ ↦ dRwHyp (evalRw K.G K.E (K.rulesEx Φ hcR) .full) hcR
                (K.cutThm "equalRefl" (fun Γ ↦ [n Γ]) lastFalse) Γ Φ ψ)
              (dImpE L gAb (K.solve 3) lastFalse)))))
        let ih : Deducer := linkK K "agreeB induction" fun Γ Φ ψ ↦
          dAllE L K.G K.E 0 (nums Γ) (K.allEΓ Ev (K.allEΓ n (K.impE (K.byHyp hN)
            (K.impE (K.byHyp gNum) (K.impE (K.byHyp gAb) (K.impE (K.solve 3)
              (K.conjE (dConjI L (K.solve 3) fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ)))))))) Γ Φ ψ
        decideIn K (fun Γ ↦ pc P "Prelude.isSome"
            [pc P "Reader.indexOf" [n Γ, scopeOf P (nums Γ) (at_ 1 Γ)]]) (anyFalse K)
          (decideIn K (fun Γ ↦ apps equalT [m Γ, n Γ]) ih headName) Γ₂ Φ₂ ψ₂
      decideIn K (fun Γ ↦ apps equalT [n Γ, eN Γ]) restCase headCase Γ₁ Φ₁ ψ₁))))))
    let d₁ ← cons [list treeTy, treeTy] [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, [list treeTy], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The typing's type of the primitive of index k: the element of its list of the primitives'
types, in normal form. -/
def primTyT (P : Prog) (k : ℕ) : Term :=
  let t := pc P "Typing/Tys.atOr" [pc P "Typing.tyT" [], pc P "Typing.primTys" [],
    leafT (numeral k)]
  (nfE P.G #[] (vBase P) [] t).getD t

/-- The primitive of index k related at its type in the typing, by the relation of the datatype
language: the fundamental lemma's relation at the kernel's type, at the definitions of the
relation's context, both relations unfolded at the types to one formula. -/
def relTPrim (P : Prog) (S : Defs) (T : Defs3) (k : ℕ) : Step :=
  (s!"relTPrim{k}", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let φ := Term.app (T.relT (v 0) (primTyT P k)) (primConst k)
    let rs (Φ : List Term) : List Internal.NormRule := K.rules Φ ++ [.delta T.q]
    let close : Deducer := fun Γ Φ ψ ↦
      let h := Φ.length - 1
      let nf (t : Term) : Option Term := (evalRw K.G K.E (rs Φ) .full Γ Φ t).map Prod.fst
      match (Φ[h]?).bind nf, nf ψ with
      | some a, some b => if a == b then
          dRwHyp (evalRw K.G K.E (rs Φ) .full) h (fun Γ Φ ψ ↦
            dRwBy (evalRw K.G K.E (rs Φ) .full) dHyp Γ Φ ψ) Γ Φ ψ
        else dbgTrace s!"relTPrim{k}: {(firstDiff a b).map fun (x, y) ↦
          s!"{showT x}\n  vs {showT y}"}" fun _ ↦ none
      | _, _ => dbgTrace s!"relTPrim{k}: no normal form" fun _ ↦ none
    let some d := K.cutThm s!"relPrim{k}" (fun Γ ↦ [Term.fst (v (Γ.length - 1))]) close
        [Defs3.ctxTy] [] φ
      | none
    pure (⟨0, [Defs3.ctxTy], [], φ⟩, d))

/-- The heads and the tails of a list's constructions, in normal form, the outermost first. -/
def consCells : Term → List (Term × Term) := RoseTree.para fun l cs ↦
  match l, cs with
  | .arr 1 _, [(_, r)] => r
  | .pair, [(h, _), (t, r)] => (h, t) :: r
  | _, _ => []

/-- The applications of the definition of index k to all its parameters and the arguments its
curried value takes, among a term's subterms, each once. -/
def appsOf (G : Internal.Globals) (k : ℕ) (t : Term) : List Term :=
  -- the parameters, and the arguments the value's curried function type takes
  let arrows : Tree → ℕ := fun A ↦ (List.range 16).foldl (fun (acc : Tree × ℕ) _ ↦
    match Internal.expParts acc.1 with
    | some (_, B) => (B, acc.2 + 1)
    | none => acc) (A, 0) |>.2
  let arity := match G.defs[k]? with
    | some (.language d) => d.params.length + arrows d.type
    | _ => 0
  -- at each subterm: the number of arguments of its spine headed by the definition, and the
  -- applications found
  (RoseTree.para (fun (l : Internal.Label) (cs : List (Term × (Option ℕ × List Term))) ↦
    let n : Option ℕ := match l, cs with
      | .defn k' _, [] => if k' = k then some 0 else none
      | .app, [(_, (hf, _)), _] => hf.map (· + 1)
      | _, _ => none
    let below := cs.flatMap (·.2.2)
    (n, if n = some arity then RoseTree.node l (cs.map Prod.fst) :: below else below)) t).2
    |>.eraseDups

/-- The soundness at an atom, the characters of index 0. -/
def atomThm (P : Prog) (S : Defs) (T : Defs3) : Internal.Thm :=
  ⟨0, [list treeTy], [], Internal.instTerm [] [atomT] (datatypeφ P S T)⟩

/-- The soundness at an atom: the hypotheses introduced; the characters fixed by the expansion
of numeral abbreviations; the coherences and the definitions' relation at the atom's name; then
the typing's tests decided in its order, each with the reader's, the reader's scope before the
typing's named context, which agree on the name by {lit}`lookupAgreeA` and
{lit}`lookupAgreeB`. -/
def atomCase (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("atomCase", fun ix E ↦ do
    let a := atomThm P S T
    let more := (vocab3 ++ ["charsMap", "handlerAtom3"]).filter fun nm ↦
      0 < ix nm ∧ ix nm < E.size
    let K : Kit := ⟨P, S, E, ix, more⟩
    let L := K.L
    -- the variables, by their positions from the outermost: the characters 0, the kernel's
    -- globals' types 1 and context 2, the declarations 3, the typing environment 4, the named
    -- context 5, the type abbreviations 6, the numeral abbreviations 7, the reader's names 8, the
    -- environment 9, the relation's context 10
    let outer (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
    -- the atom's name, its label in normal form, so that the equations instantiated at it match
    -- normalized terms
    let label0 := (nfE K.G K.E (vBase P) [] (numeral 0)).getD (numeral 0)
    let nm (Γ : List Tree) : Term := nodeT (Term.pair label0 (outer 0 Γ))
    let unfoldAt (h k : ℕ) (next : Deducer) : Deducer :=
      dRwHyp (evalRw K.G K.E [.delta k] .head) h next
    let tr (msg : String) : Deducer := fun Γ Φ ψ ↦
      dbgTrace s!"atomCase {msg}: {Γ.length} vars, {Φ.length} hyps; goal {
        ((evalRw K.G K.E (K.rules Φ) .full Γ Φ ψ).map fun r ↦ showT r.1).getD "none"}
        last hyps {(Φ.drop (Φ.length - 8)).map showT}"
        fun _ ↦ none
    let link (msg : String) (k : Deducer) : Deducer := fun Γ Φ ψ ↦ (k Γ Φ ψ).orElse fun _ ↦
      tr msg Γ Φ ψ
    -- the statement's hypotheses, after the variables' truths
    let hyp (i : ℕ) : ℕ := nQ + i
    -- the typing's and the reader's steps at an atom, each application in the type's and the
    -- resolution's hypotheses, outside any binder, evaluated once by the base rules and the
    -- hypotheses' equations, its equation cut in after the hypotheses
    let unfoldLocal (k : Deducer) : Deducer := fun Γ₀ Φ₀ ψ₀ ↦ do
      let ks := [P.idx "Typing.synAtom", P.idx "Reader.resolveAtom"]
      -- the base rules with the rebuilding of trees by the primitives
      let base : List Internal.NormRule :=
        ["kids", "mapId", "lambek"].map (fun nm ↦ .thm (ix nm) []) ++
          [.thm (ix "rebTail") [treeTy]] ++ rebRules ix ++ vBase P
      -- each equation among the statement's hypotheses and after, also in those rules'
      -- normal form, after the hypotheses
      let eqs := (List.range Φ₀.length).filter fun i ↦
        nQ ≤ i ∧ ((Φ₀[i]?).bind Internal.eqParts).isSome
      let main : Deducer := fun Γ Φ ψ ↦ do
        let nfs := [Φ[hyp 6]?, Φ[hyp 7]?].filterMap id |>.filterMap fun t ↦
          (evalRw K.G K.E (K.rules Φ) .full Γ Φ t).map Prod.fst
        let apps := (ks.flatMap fun j ↦ nfs.flatMap (appsOf K.G j)).eraseDups
        let cheap := eqHyps Φ ++ base ++ ks.map .delta
        let cuts := apps.filterMap fun a ↦ (Internal.eval K.G K.E 0 cheap 4096 .full Γ Φ a).map
          fun (r, d, _) ↦ (Term.eq a r, nd .join [d, nd .refl])
        cuts.foldr (fun (e, d) k ↦ dCut e d k) k Γ Φ ψ
      eqs.foldr (fun i k ↦ dRwHyp (evalRw K.G K.E base .full) i k) main Γ₀ Φ₀ ψ₀
    -- the relation unfolded at a type
    let normR (k : Deducer) : Deducer := fun Γ Φ ψ ↦
      dRwBy (evalRw K.G K.E (K.rules Φ ++ [.delta T.q]) .full) k Γ Φ ψ
    let byNormR : Deducer := fun Γ Φ ψ ↦
      dEq (byMode .full K.G K.E 0 (K.rules Φ ++ [.delta T.q])) Γ Φ ψ
    let hypFalseLast : Deducer := fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ
    let solveD : Deducer := K.solve 3
    -- the truth of a test decided: its label's bitstring empty or not
    -- where the test's normal form by the base rules and the rebuildings differs, its equation
    -- with the vocabulary's normal form cut in first, so that the case's equation applies to both
    let decide (t : List Tree → Term) (kF kT : Deducer) : Deducer := fun Γ Φ ψ ↦
      let lt := call D.lab [] [t Γ]
      let cheap := ["kids", "mapId", "lambek"].map (fun nm ↦ Internal.NormRule.thm (ix nm) []) ++
        [.thm (ix "rebTail") [treeTy]] ++ rebRules ix ++ vBase P
      match nfE K.G K.E (K.rules []) Γ lt, nfE K.G K.E cheap Γ lt with
      | some X, some Xc =>
        let split := K.listCase bitTy X kF kT
        if Xc == X then split Γ Φ ψ else do
          let d ← byMode .full K.G K.E 0 (K.rules []) Γ [] Xc X
          dCut (Term.eq Xc X) d split Γ Φ ψ
      | _, _ => dbgTrace s!"atomCase test without a normal form: {showT (t Γ)}" fun _ ↦ none
    let isSomeOf (t : Term) : Term := pc P "Prelude.isSome" [t]
    -- the statement's terms in the context
    let inΓ (Γ : List Tree) (t : Term) : Term := Term.rename t fun i ↦ i + Γ.length - (nQ + 1)
    let kOf (Γ : List Tree) : Term :=
      inΓ Γ (datatypeTerms P (nodeT (Term.pair (numeral 1) (v nQ)))).2
    let childT := (primT Kernel.Prim.child).getD Term.star
    -- the tests: of the typing at an atom, and of the reader
    let t1 (Γ : List Tree) : Term := isSomeOf (pc P "Reader.numeral" [outer 0 Γ])
    let r0 (Γ : List Tree) : Term := isSomeOf (pc P "Reader.lookupAbbrev" [nm Γ, outer 7 Γ])
    let t2 (Γ : List Tree) : Term :=
      pc P "Typing.hasName" [nm Γ, pc P "Typing.envNums" [outer 4 Γ]]
    let t3 (Γ : List Tree) : Term := isSomeOf (pc P "Typing.lookupName" [nm Γ, outer 5 Γ])
    let r2 (Γ : List Tree) : Term :=
      isSomeOf (pc P "Reader.indexOf" [nm Γ, scopeOf P (outer 7 Γ) (outer 5 Γ)])
    let t4 (Γ : List Tree) : Term :=
      isSomeOf (pc P "Typing.lookupName" [nm Γ, pc P "Typing.envDefs" [outer 4 Γ]])
    let r3 (Γ : List Tree) : Term := isSomeOf (pc P "Reader.indexOf" [nm Γ, outer 8 Γ])
    let t5 (Γ : List Tree) : Term :=
      isSomeOf (pc P "Reader.indexOf" [nm Γ, pc P "Reader.primNames" []])
    let t6 (Γ : List Tree) : Term := pc P "Reader.named"
      [nodeT (Term.pair (numeral 1) (outer 0 Γ)), pc P "Reader.kwUnitValue" []]
    -- a quotation's value at fuel one, related at the tree type
    let quoteClose : Deducer := link "quote" <| unfoldLocal <| link "quote, unfolded" <|
      K.norm fun Γ Φ ψ ↦
      let c := (evalRw K.G K.E (K.rules Φ) .full Γ Φ
        (apps childT [pc P "Prelude.get" [kOf Γ], leafT bnilT])).map Prod.fst |>.getD Term.star
      dConv L K.G K.E S (succN zeroN) (pc P "Eval.valQuote" [c]) K.byNorm
        (link "quote related" (normR (dExI L K.G K.E c byNormR))) Γ Φ ψ
    let unitClose : Deducer := link "unit" <| unfoldLocal <| link "unit, unfolded" <|
      K.norm fun Γ Φ ψ ↦
      dConv L K.G K.E S (succN zeroN) (pc P "Eval.valUnit" []) (link "unit stable" K.byNorm)
        (link "unit related" (normR byNormR)) Γ Φ ψ
    -- the negation of a test decided false: the test assumed, then refuted by the case's equation
    let notGuard : Deducer := dImpI L hypFalseLast
    -- a variable: the reader's index's agreement with the typing's lookup, the named context's
    -- entry at the index and the environment's value there, related at the entry's type; the
    -- agreement's instance at the context, the abbreviations, the typing environment and the
    -- name, its antecedents the coherence, the name's being no numeral and not abbreviated, and
    -- the index's truth
    let varClose : Deducer := link "variable" <|
      K.cutThm "lookupAgreeB" (fun Γ ↦ [outer 5 Γ]) <| K.allEΓ (outer 7) <|
      K.allEΓ (outer 4) <| K.allEΓ nm <| K.impE (K.byHyp (hyp 2)) <| K.impE notGuard <|
      K.impE notGuard <| K.impE solveD <| K.conjE fun Γ₀ Φ₀ ψ₀ ↦
        let isN := Φ₀.length - 1
        let i (Γ : List Tree) : Term :=
          leafIndex P (pc P "Reader.indexOf" [nm Γ, scopeOf P (outer 7 Γ) (outer 5 Γ)])
        -- the environment's relation at the index: a value there, related at the entry's type;
        -- the value's equation normalized so that it rewrites the evaluator's lookup
        unfoldAt (hyp 1) (T.q + 1) (fun Γ Φ ψ ↦ dAllE L K.G K.E (Φ.length - 1) (i Γ)
          (K.impE (K.byHyp isN) (K.exE (K.conjE fun Γ Φ ψ ↦
            let w := v (Γ.length - Γ₀.length - 1)
            let e := Φ.length - 2
            let r := Φ.length - 1
            dRwHyp (evalRw K.G K.E (K.rulesEx Φ e) .full) e (unfoldLocal (link
              "variable, unfolded" (K.norm (dConv L K.G K.E S (succN zeroN) w
                (link "variable stable" K.byNorm) (link "variable related" (K.byHyp r))))))
              Γ Φ ψ))) Γ Φ ψ) Γ₀ Φ₀ ψ₀
    -- a name with a type in the named context and no index in the scope: refuted by the
    -- agreement, at the context, the abbreviations and the name
    let unscoped : Deducer := link "scope refuted" <|
      K.cutThm "lookupAgreeA" (fun Γ ↦ [outer 5 Γ]) <| K.allEΓ (outer 7) <| K.allEΓ nm <|
        K.impE notGuard <| K.impE solveD hypFalseLast
    -- a reference: the definition's evaluation's threshold and value, its relation
    let refClose : Deducer := link "reference" fun Γ₀ Φ₀ ψ₀ ↦
      K.exE (K.conjE (K.exE (K.conjE fun Γ₁ Φ₁ ψ₁ ↦
        -- the definition's equation, normalized so that it rewrites the evaluator's lookup
        let e := Φ₁.length - 2
        K.unfoldConv (K.exE (K.exE (K.conjE fun Γ Φ ψ ↦
          let st := Φ.length - 2
          let r := Φ.length - 1
          let n := v (Γ.length - Γ₁.length - 1)
          let w := v (Γ.length - Γ₁.length - 2)
          dRwHyp (evalRw K.G K.E (K.rulesEx Φ e) .full) e (unfoldLocal (link
            "reference, unfolded" (K.norm (dConv L K.G K.E S (succN n) w
              (link "reference stable" fun Γ Φ ψ ↦ dAllE L K.G K.E st (v 0) (fun Γ Φ ψ ↦
                dRwHyp (evalRw K.G K.E (K.rules Φ.dropLast) .full) (Φ.length - 1)
                  K.byNorm Γ Φ ψ) Γ Φ ψ)
              (link "reference related" (K.byHyp r)))))) Γ Φ ψ))) Γ₁ Φ₁ ψ₁))) Γ₀ Φ₀ ψ₀
    -- a primitive: the tests of the name's equality to the primitives' names decided in their
    -- order; at the first equal name, the index's equation at each suffix of the names, from
    -- that name's outward, each by the lookup's equation at a construction under the equation
    -- after it, and the primitive related at its type by its lemma; at none, the index none at
    -- each suffix, which refutes the index's test, its truth cut in first, from the case's
    -- equation; the typing and the reader unfolded first, their tests but the index's decided
    let primClose : Deducer := unfoldLocal fun Γ₀ Φ₀ ψ₀ ↦ do
      let hT := Φ₀.length
      let ns ← nfE K.G K.E (K.rules []) [] (pc P "Reader.primNames" [])
      let cells := consCells ns
      let equalT ← primT Kernel.Prim.equal
      let suffix (l : ℕ) : Term := if l = 0 then ns else ((cells[l - 1]?).map Prod.snd).getD ns
      let headAt (l : ℕ) : Term := ((cells[l]?).map Prod.fst).getD Term.star
      -- the equations at the suffixes from position l outward, of the values val
      let chain (l : ℕ) (val : ℕ → Term) (k : Deducer) : Deducer :=
        (List.range (l + 1)).reverse.foldr (fun i k Γ Φ ψ ↦ do
          let φ := Term.eq (pc P "Reader.indexOf" [nm Γ, suffix i]) (val i)
          let pf : Deducer := if i < cells.length then
              K.cutThm "indexOfCons" (fun Γ ↦ [suffix (i + 1), headAt i, nm Γ]) K.byNorm
            else K.cutThm "indexOfNil" (fun Γ ↦ [nm Γ]) K.byNorm
          let d ← (link s!"index at {i}" pf) Γ Φ φ
          dCut φ d k Γ Φ ψ) k
      let leaf (j : ℕ) : Deducer := link s!"primitive {j}" <|
        K.norm fun Γ Φ ψ ↦
        dConv L K.G K.E S (succN zeroN) (primConst j) (link "primitive stable" K.byNorm)
          (link "primitive related" (K.cutThm s!"relTPrim{j}"
            (fun Γ ↦ [outer 10 Γ]) fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ)) Γ Φ ψ
      let found (j : ℕ) : Deducer :=
        chain j (fun i ↦ pc P "Prelude.some" [leafT (numeral (j - i))]) (leaf j)
      let none' : Deducer :=
        chain cells.length (fun _ ↦ pc P "Prelude.none" []) (link "index refuted" (K.hypFalse hT))
      let truth := K.truthB (call D.lab [] [t5 Γ₀])
      let some dT := K.solve 3 Γ₀ Φ₀ truth | tr "index's truth" Γ₀ Φ₀ truth
      dCut truth dT ((List.range cells.length).foldr (fun l k ↦
        decide (fun Γ ↦ apps equalT [nm Γ, headAt l]) k (found l)) none') Γ₀ Φ₀ ψ₀
    -- the cases, after the instances: n₁ and n₂ the numeral abbreviations' coherence, d₁ the
    -- names', g₁ the definitions' relation
    let cases (n₁ n₂ d₁ g₁ : ℕ) : Deducer :=
      -- the abbreviation's numeral atom: its characters' test decided, false refuted by the
      -- coherence's, true a quotation
      let numeralAtom : Deducer := fun Γ₀ Φ₀ ψ₀ ↦ K.exE (K.conjE fun Γ Φ ψ ↦
        let h := Φ.length - 1
        decide (fun Γ' ↦ isSomeOf (pc P "Reader.numeral" [v (Γ'.length - Γ₀.length - 1)]))
          (K.hypFalse h) quoteClose Γ Φ ψ) Γ₀ Φ₀ ψ₀
      let fromAbbrev : Deducer := dImpE L n₁ solveD numeralAtom
      let notNums : Deducer :=
        decide r2 (decide t3 (decide t4 (decide r3 (decide t5
              (decide t6 (link "no type" (unfoldLocal (K.hypFalse (hyp 6)))) unitClose)
              primClose)
            (link "names refuted" (dImpE L d₁ solveD hypFalseLast)))
            (link "definition" (dImpE L g₁ solveD refClose)))
          unscoped)
          varClose
      decide t1
        (decide t2 (decide r0 notNums
            (link "abbreviation refuted" (dImpE L n₂ solveD hypFalseLast)))
          (link "numeral abbreviation" fromAbbrev))
        (decide r0 quoteClose
          (link "numeral's abbreviation" (dImpE L n₂ solveD (dImpE L n₁
            (fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ) numeralAtom))))
    -- the instances at the atom's name, each after the hypotheses: the numeral abbreviations'
    -- coherence, both parts; the names' coherence; and the definitions' relation
    let instAt (h k : ℕ) (next : ℕ → Deducer) : Deducer :=
      link s!"unfold {h}" <| unfoldAt h k fun Γ Φ ψ ↦
        -- the unfolded hypothesis, the last
        link s!"instance {h}" (dAllE L K.G K.E (Φ.length - 1) (nm Γ) fun Γ Φ ψ ↦
          next (Φ.length - 1) Γ Φ ψ) Γ Φ ψ
    let numsI : Deducer := instAt (hyp 2) (T.q + 3 + 2 * nFolds) fun _ ↦ K.conjE fun Γ Φ ψ ↦
      let n₁ := Φ.length - 2
      let n₂ := Φ.length - 1
      instAt (hyp 3) (T.q + 4 + 2 * nFolds) (fun d₁ ↦ instAt (hyp 0) (T.q + 2) fun g₁ ↦
        cases n₁ n₂ d₁ g₁) Γ Φ ψ
    -- the characters fixed, the equation after the hypotheses
    let chars : Deducer :=
      K.cutThm "charsFixedEq" (fun Γ ↦ [outer 0 Γ, outer 7 Γ]) (K.impE (K.byHyp (hyp 4)) numsI)
    let nH := (datatypeParts P S T (v nQ)).1.length
    let intros : Deducer → Deducer := fun k ↦
      (List.range nQ).foldr (fun _ k ↦ dAllI L k) ((List.range nH).foldr (fun _ k ↦ dImpI L k) k)
    let some d := intros chars [list treeTy] [] a.concl
      | dbgTrace "atomCase: not proved" fun _ ↦ none
    pure (a, d))

/-- The argument of the expansion of numeral abbreviations at an atom's label, applied to the
children's values, a list variable of index 0, at the abbreviations of index 1: unfolded. -/
def handlerAtom3 (P : Prog) (T : Defs3) : Step :=
  ("handlerAtom3", fun ix E ↦ do
    let f ← (foldSpecs P T.envTy)[3]?
    let (_, d, _, _, _, _) ← foldDefn P f (T.argIdx 3)
    let Γ := [list d.type, list treeTy]
    let t := Term.app (Term.app (call (T.argIdx 3) [] [v 1]) (nodeT (Term.pair (numeral 1)
      (nilT treeTy)))) (v 0)
    let rs := vRules3 P ix E.size
    let some l := nfE P.G E rs Γ t | dbgTrace "handlerAtom3: left" fun _ ↦ none
    let some (r, dv, _) := Internal.eval P.G E 0 (rs ++ [.delta (T.argIdx 3)]) 4096 .full Γ [] l
      | dbgTrace "handlerAtom3: right" fun _ ↦ none
    pure (⟨0, Γ, [], Term.eq l r⟩, nd .join [dv, nd .refl]))

/-- The fundamental lemma's relations of the primitives at their types, with the lemmas their
proofs use: the relation of lists and the quotations' and unquotations' lists. -/
def primRelDev (P : Prog) (S : Defs) : List Step :=
  [allMonoLemma P S, allConvLemma P S, relOfListLemma P S] ++ spineLemmas P ++
    [quoteAllLemma P S, unquoteAllLemma P S] ++ primIndices.flatMap fun k ↦
      apConstLemmas P s!"apPrim{k}" (fun _ ↦ primConst k) 0 (primArgs k) ++ [relPrimLemma P S k]

/-- The base development: the fundamental lemma's base and the primitives' relations, and each
fold's vocabulary with the lemmas of the lookups and of the equality of trees. -/
def baseDev3 (P : Prog) (S : Defs) (T : Defs3) : Option (List Step) := do
  let modes := [Rebuild.step, .step, .step, .none, .argument, .applied]
  pure ((← baseDev P S) ++ primRelDev P S ++ (modes.zipIdx.flatMap fun (m, k) ↦
      foldVocab P T k m ++ [foldDefEq P T k]) ++
    ([(0, KidsShape.list), (1, .list), (2, .list), (4, .foldr), (5, .applied)].map
      fun (k, b) ↦ kidsEq P T k b) ++
    atomEqs P T ++ [handlerAtom3 P T, charsMap P T, charsFixedEq P S T] ++ equalReflLemmas P S ++
    lookupEqs P)

/-- The development of the soundness at an atom: the agreement of the reader's scope with the
named context, the primitives related at their types in the typing, and the soundness. -/
def atomDev3 (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  [lookupAgreeA P S, lookupAgreeB P S T] ++ (List.range 14).map (relTPrim P S T) ++
    [atomCase P S T]

/-- A development's declarations, each checked after those before it, given the entries before
them; the first that does not, named. -/
def checkAfter (G : Internal.Globals) (E : Array Internal.Entry) (names : List String)
    (ds : List Internal.Decl) : Except String Unit := do
  let _ ← names.zip ds |>.foldlM (fun (st : Internal.Globals × Array Internal.Entry)
      (nm, d) ↦ match d.step st.1 st.2 with
    | some st' => Except.ok st'
    | none => Except.error s!"the lemma {nm} does not check") (G, E)

/-- The base development, stored as the certificate {lit}`datatype-base`, each declaration checked
as it is stored. -/
def certificates (P : Prog) (S : Defs) (T : Defs3) :
    Except String (List (String × List Internal.Decl)) := do
  let some dev := baseDev3 P S T | throw "the base is not stated"
  let (_, _, ds) ← developAfter [] #[] dev
  checkAfter P.G #[] (dev.map (·.1)) ds
  pure [("datatype-base", ds)]

/-- The development of the soundness at an atom, after the base development's declarations, stored
as the certificate {lit}`datatype-atom`, each declaration checked as it is stored. -/
def atomCertificates (P : Prog) (S : Defs) (T : Defs3) (base : List Internal.Thm) :
    Except String (List (String × List Internal.Decl)) := do
  let some dev := baseDev3 P S T | throw "the base is not stated"
  let E : Array Internal.Entry := (base.map Internal.Entry.language).toArray
  let names := dev.map (·.1)
  unless names.length = E.size do throw "the base's certificate is not the base's"
  let atom := atomDev3 P S T
  let (_, _, ds) ← developAfter names E atom
  checkAfter P.G E (atom.map (·.1)) ds
  pure [("datatype-atom", ds)]

end GebTests.Prototypes.FreeTopos.Datatypes

end
