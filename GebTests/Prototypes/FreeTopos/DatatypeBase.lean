/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.NormalizationBase -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.NormalizationBase -- shake: keep
public import GebTests.Prototypes.Stage1 -- shake: keep
public meta import GebTests.Prototypes.Stage1 -- shake: keep

set_option doc.verso true in
/-!
# The base of the datatype language's soundness

probe
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Datatypes

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Translation Geb.FreeTopos.Tactics
open GebTests.Prototypes.FreeTopos.Weakening
open scoped FinEnum

open Internal (Term)
open GebTests.Prototypes.FreeTopos.Normalization (Defs extendedOf pc truth baseDev developAfter
  vRules vBase nfE defnObjs rebuildLemmas genRoot showT)

/-- The program: the prelude, the reader, the kernel's type checker, the lists of the datatype
language, the stage-1 typing and expansion, the recognizers, the traversal of kernel terms, the
evaluator, and the weakening proof's statement, whose development the base of the fundamental lemma
proves. -/
def programText : String :=
  Kernel.Stage0Tests.prelude ++ "\n" ++ Kernel.Stage0Tests.reader ++ "\n" ++
    Kernel.Stage0Tests.check ++ "\n" ++ Kernel.Stage1Tests.seq ++ "\n" ++
    Kernel.Stage1Tests.typing ++ "\n" ++ Kernel.Stage1Tests.datatype ++ "\n" ++
    Kernel.Stage0Tests.recognize ++ "\n" ++ Kernel.Stage0Tests.subst ++ "\n" ++
    Kernel.EvalTests.evalGeb ++ "\n" ++ Weakening.statement

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
numeral abbreviations and the resolution, each at the tree of index 0. -/
def foldSpecs (envTy : Tree) : List FoldSpec :=
  [⟨"Datatype.expandExpr", [treeTy, list treeTy], [v 1, v 0]⟩,
    ⟨"Typing.synIn", [treeTy, list treeTy, envTy], [v 2, v 1, v 0]⟩,
    ⟨"Datatype.eraseExpr", [treeTy], [v 0]⟩,
    ⟨"Reader.expandNums", [treeTy, list treeTy], [v 1, v 0]⟩,
    ⟨"Reader.resolve", [treeTy, list treeTy, list treeTy, list treeTy], [v 3, v 2, v 0, v 1]⟩]

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

/-- The definitions of the stage-1 pipeline the proofs keep folded: the steps of the folds the
statement composes at a node, each decided by a node's label or a list's head, whose equations
the vocabulary states one keyword at a time. -/
def foldedStage1 : List String :=
  ["Reader.resolveAtom", "Reader.resolveList", "Typing.synAtom", "Typing.synList",
    "Datatype.expandCase", "Datatype.expandCata", "Datatype.expandExpr", "Typing.synIn",
    "Datatype.eraseExpr", "Reader.expandNums", "Reader.resolve"]

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
  let some childT := primT Kernel.Prim.child | none
  let childAt (t : Term) (k : ℕ) : Term := apps childT [t, leafT (numeral k)]
  let defs : List Internal.Defn := [
    relDefn P S,
    -- the relation of an environment to a named context: at each index where the context has
    -- some name with a type, the environment has some value related at the type
    ⟨0, [list treeTy, list treeTy, R], omega,
      all treeTy (Term.lam treeTy (imp
        (truth o (pc P "Prelude.isSome" [pc P "Prelude.nth" [v 2, v 0]]))
        (ex treeTy (Term.lam treeTy
          (conj (Term.eq (pc P "Prelude.nth" [v 2, v 1]) (pc P "Prelude.some" [v 0]))
            (Term.app (T.relT (v 4) (childAt (pc P "Prelude.get"
              [pc P "Prelude.nth" [v 3, v 1]]) 1)) (v 0)))))))⟩,
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
    (← ((foldSpecs envTy).zipIdx.mapM fun (f, k) ↦
      (foldDefn P f (T.argIdx k)).map fun r ↦ [r.1, r.2.1])).flatten
  pure (⟨⟨P.G.prims, P.G.defs ++ defs.map .language, P.G.base⟩, P.o, P.idx, foldedStage1⟩, T)

/-- The names of a named context, the scope the reader resolves a term in. -/
def namesOf (cx : Term) : Term :=
  Term.listRec (nilT treeTy)
    (consT treeTy (apps ((primT Kernel.Prim.child).getD Term.star) [v 1, leafT bnilT]) (v 0)) cx

/-- The soundness of the datatype language's typing at a source form, the variable of index 0:
for all declarations of the expansion, typing environments, named contexts, type and numeral
abbreviations and definitions' names of the reader, environments and contexts of the relation,
if the definitions are related to the typing environment's and the environment to the named
context, and the form expands, its expansion has a type, and the expansion's erasure, its
numeral abbreviations expanded, resolves in the context's names, then the resolved term's
evaluation in the environment converges to a value related at the type. -/
def datatypeφ (P : Prog) (S : Defs) (T : Defs3) : Term :=
  let all := Internal.Logic.all P.o
  let imp := Internal.Logic.imp P.o
  let isSomeT (t : Term) : Term := truth P.o (pc P "Prelude.isSome" [t])
  let get (t : Term) : Term := pc P "Prelude.get" [t]
  -- under the eight quantifiers: R v0, env v1, names v2, nums v3, tys v4, cx v5, E v6, Δ v7,
  -- the form v8
  let x := get (pc P "Datatype.expandExpr" [v 7, v 8])
  let ty := pc P "Typing.synIn" [v 6, v 5, x]
  let k := pc P "Reader.resolve" [v 4, v 2,
    pc P "Reader.expandNums" [v 3, pc P "Datatype.eraseExpr" [x]], namesOf (v 5)]
  let body := imp (T.globT (v 0) (v 6) (v 2)) (imp (T.envT (v 0) (v 5) (v 1))
    (imp (isSomeT (pc P "Datatype.expandExpr" [v 7, v 8])) (imp (isSomeT ty) (imp (isSomeT k)
      (S.conv
        (Term.lam nat (S.evN (Term.fst (v 1)) (v 0) (v 2) (get (Term.subst k fun i ↦ v (i + 1)))))
        (T.relT (v 0) (get ty)))))))
  let q (A : Tree) (b : Term) : Term := all A (Term.lam A b)
  q (list treeTy) (q T.envTy (q (list treeTy) (q (list treeTy) (q (list treeTy)
    (q (list treeTy) (q (list treeTy) (q Defs3.ctxTy body)))))))

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
  let some f := (foldSpecs T.envTy)[k]? | throw "no fold"
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
          | some (Internal.Entry.language a) => s!"theorem {j}: {(showT a.concl).take 600}"
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

/-- The vocabulary of the fold of index k: the fusion of the map of the folds at the children,
applied to the parameters, with the map of the fold's definition, by induction on the children;
the fold's definition at a node, unfolded at the root alone; and, where the fold's values pair
the node rebuilt with the value, the rebuilding lemmas. -/
def foldVocab (P : Prog) (T : Defs3) (k : ℕ) (pairs : Bool) : List Step :=
  match (foldSpecs T.envTy)[k]? with
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
  let rebuild : List Step := if pairs then
      match Internal.expParts C with
      | some (FX, _) => rebuildLemmas P tag FX
          (fun x G ↦ Term.fst (Term.app (Term.roseRec C st x) G)) tys
          (T.foldAt k (ps 0) (v 0)) F (some (T.foldIdx k))
      | none => []
    else []
  fus :: node :: rebuild

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

/-- The rules of the datatype language's vocabulary: each fold at a node, its rebuilding where it
rebuilds, and the rules of the normalization proof's vocabulary. -/
def vRules3 (P : Prog) (ix : String → ℕ) : List Internal.NormRule :=
  ((List.range 5).flatMap fun k ↦ [s!"fold{k}Node", s!"fold{k}Fst"]).filterMap
    (fun nm ↦ if ix nm = 0 then none else some (.thm (ix nm) [])) ++ vRules P ix

/-- The base development: the fundamental lemma's base, and each fold's vocabulary. -/
def baseDev3 (P : Prog) (S : Defs) (T : Defs3) : Option (List Step) := do
  pure ((← baseDev P S) ++ [(0, true), (1, true), (2, true), (3, false), (4, false)].flatMap
    fun (k, pairs) ↦ foldVocab P T k pairs)

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let some (P, S, T) := extended3 | throwError "the program does not extend"
  let some dev := baseDev3 P S T | throwError "the base is not stated"
  -- each lemma's name before it is proved and its time after, appended to a file as it runs
  let log := "/tmp/user/1000/claude-1000/datatype-base-progress.txt"
  IO.FS.writeFile log ""
  IO.FS.writeFile (log ++ ".nodes") ""
  let names := dev.map (·.1)
  let ix (name : String) : ℕ := (names.findIdx? (· == name)).getD 0
  let mut E : Array Internal.Entry := #[]
  for x in dev do
    let h ← IO.FS.Handle.mk log .append
    h.putStrLn s!"start {x.1}"
    h.flush
    let t₀ ← IO.monoMsNow
    match x.2 ix E with
    | some (a, _) => E := E.push (Internal.Entry.language a)
    | none =>
      let why := if x.1.endsWith "Fus" ∧ x.1.startsWith "fold" then
          match fusion P T ((x.1.drop 4).takeWhile Char.isDigit).toNat! ix E with
          | .error e => e
          | .ok _ => "proved here"
        else ""
      IO.FS.writeFile (log ++ ".why") why
      throwError m!"the lemma {x.1} is not proved: {why.take 3000}"
    let h ← IO.FS.Handle.mk log .append
    h.putStrLn s!"done {x.1} {(← IO.monoMsNow) - t₀} ms"
    h.flush
  logInfo m!"base: {E.size} theorems"
  -- each fold at a node of an atom's label and of a list's, its argument unfolded
  for (f, k) in (foldSpecs T.envTy).zipIdx do
    let some (_, d, _, _, _, _) := foldDefn P f (T.argIdx k) | throwError "no definition"
    let tys := d.params.tail
    let ps := (List.range tys.length).reverse.map fun i ↦ v (i + 1)
    for lab in [1, 2] do
      let t := T.foldAt k ps (nodeT (Term.pair (numeral lab) (v 0)))
      let Γ := list treeTy :: tys
      let rs := vRules3 P ix ++ [.delta (T.argIdx k)]
      let t₀ ← IO.monoMsNow
      let w := (Internal.eval P.G E 0 rs 4096 .weak Γ [] t).map fun (u, _) ↦ showT u
      let t₁ ← IO.monoMsNow
      let fl := (Internal.eval P.G E 0 rs 4096 .full Γ [] t).map fun (u, _) ↦ (showT u).length
      let h ← IO.FS.Handle.mk (log ++ ".nodes") .append
      h.putStrLn s!"{f.name} at {lab}: weak {t₁ - t₀} ms {w.map String.length}, \
        full {(← IO.monoMsNow) - t₁} ms {fl}\n  {(w.getD "").take 1500}"
      h.flush

end GebTests.Prototypes.FreeTopos.Datatypes

end
