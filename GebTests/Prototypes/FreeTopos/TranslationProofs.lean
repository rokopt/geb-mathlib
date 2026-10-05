/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Translation -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.Translation -- shake: keep
public import GebTests.Prototypes.Stage0 -- shake: keep
public meta import GebTests.Prototypes.Stage0 -- shake: keep
public import Geb.Prototypes.FreeTopos.Internal.Prove -- shake: keep
public meta import Geb.Prototypes.FreeTopos.Internal.Prove -- shake: keep
public import Geb.Prototypes.FreeTopos.Tactics -- shake: keep
public meta import Geb.Prototypes.FreeTopos.Tactics -- shake: keep

set_option doc.verso true in
/-!
# Theorems about kernel programs, translated

Equations between kernel programs, statements of Gödel's T, each given as two definitions
abstracting its sides over its context, with the programs they are about, translated into the
internal language, whose labels are bitstrings, and proved there by its prover: the prelude's
appending by normalization and induction; the labels' addition by rewriting with lemmas on the
bitstrings' addition, which the development proves first by induction on the bitstrings, case
analysis of their bits and, for the functions of the first summand, extensionality; the kernel's
type checker at a quoted tree and a program by structural recursion by normalization, weak head
normal forms first, rewriting by Lambek's lemma, which follows from two lemmas on lists by the
uniqueness of the rose tree's fold. Each development checks, and the report prints, for each file,
the nodes of the language's derivations of its theorems, the bit steps among them, and the time
the checker takes, and the same for the lemmas proved before the theorems.

## Main definitions

* {lit}`files` — the texts of the files, each the programs and the theorems' statements.
* {lit}`theoremsOf` — a file's program and its theorems, from the statements' definitions.
* {lit}`treeLemmas` — the fold of a list by construction, the fusion of the rebuilding of trees
  with their unfolding, and Lambek's lemma.
* {lit}`preludeDev`, {lit}`natDev`, {lit}`checkDev`, {lit}`treeDev` — the developments.
* {lit}`reports` — the measurement.

## Tags

internal language, Gödel's T, translation, measurement, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.TranslationProofs

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Translation Geb.FreeTopos.Tactics
open GebTests.Prototypes.FreeTopos.Translation (sizeM baseRules)
open scoped FinEnum

/-- The statements of the prelude's theorems: appending the empty list on either side, the
associativity of appending, and appending the empty list twice. -/
def preludeStatements : String := "
(import Prelude)
(def appendNilLeftL (lam ((ys Ts)) (append (nil T) ys)))
(def appendNilLeftR (lam ((ys Ts)) ys))
(def appendNilL (lam ((xs Ts)) (append xs (nil T))))
(def appendNilR (lam ((xs Ts)) xs))
(def appendAssocL (lam ((ys Ts) (zs Ts) (xs Ts)) (append (append xs ys) zs)))
(def appendAssocR (lam ((ys Ts) (zs Ts) (xs Ts)) (append xs (append ys zs))))
(def appendNilTwiceL (lam ((xs Ts)) (append (append xs (nil T)) (nil T))))
(def appendNilTwiceR (lam ((xs Ts)) xs))"

/-- The statements of the labels' addition: zero on the right, the successor on the right, and
zero on the left. -/
def natStatements : String := "
(import Prelude)
(def addZeroL (lam ((m T)) (add m 0)))
(def addZeroR (lam ((m T)) (label m)))
(def addSuccL (lam ((m T) (n T)) (add m (add n 1))))
(def addSuccR (lam ((m T) (n T)) (add (add m n) 1)))
(def addZeroLeftL (lam ((n T)) (add 0 n)))
(def addZeroLeftR (lam ((n T)) (label n)))"

/-- The statement of the type checker's type of a quoted tree. -/
def checkStatements : String := "
(import Prelude) (import Reader) (import Check)
(def typeQuoteL (lam ((G Ts) (ctx Ts) (x T)) (typeIn G ctx (node Label.quote (single x)))))
(def typeQuoteR (lam ((G Ts) (ctx Ts) (x T)) (some Label.tyTree)))"

/-- A program by structural recursion over a datatype, and the statements of its recursion
equations. -/
def datatypeStatements : String := "
(import Prelude) (import Reader) (import Check)
(data Nat (zero) (succ Nat))
(defn plus ((m Nat) (n Nat)) Nat (cata Nat Nat m ((zero) n) ((succ r) (succ r))))
(def plusZeroL (lam ((n Nat)) (plus zero n)))
(def plusZeroR (lam ((n Nat)) n))
(def plusSuccL (lam ((m Nat) (n Nat)) (plus (succ m) n)))
(def plusSuccR (lam ((m Nat) (n Nat)) (succ (plus m n))))"

/-- The texts of the files, each the programs its theorems are about and their statements, with
the number of its theorems: the prelude, the labels, the kernel's type checker and a program by
structural recursion. -/
def files : List (String × ℕ) :=
  let pr := Kernel.Stage0Tests.prelude
  let prc := pr ++ "\n" ++ Kernel.Stage0Tests.reader ++ "\n" ++ Kernel.Stage0Tests.check
  [(pr ++ "\n" ++ preludeStatements, 4), (pr ++ "\n" ++ natStatements, 3),
    (prc ++ "\n" ++ checkStatements, 1), (prc ++ "\n" ++ datatypeStatements, 2)]

/-- The binders' types of a term's abstractions, innermost first, and the body under them, at most
{lit}`n` of them. -/
def unLams : ℕ → Tree → List Tree × Tree
  | 0, t => ([], t)
  | n + 1, t =>
    match t.children with
    | [A, b] => if t.label == Kernel.Label.lam then
        let r := unLams n b
        (r.1 ++ [A], r.2)
      else ([], t)
    | _ => ([], t)

/-- A file's program and theorems, from its definitions, the last two for each theorem its
statement: the program's definitions before them, and each theorem, whose context and sides are
the abstractions of its two definitions and whose type is its left side's. -/
def theoremsOf (ds : List (List Char × Tree)) (k : ℕ) : List Tree × List GoedelT.Thm :=
  let n := ds.length - 2 * k
  let D := (ds.take n).map Prod.snd
  let G := (Kernel.load D).getD []
  let ss := (ds.drop n).map Prod.snd
  (D, (List.range k).map fun i ↦
    let (Γ, l) := unLams 64 (ss.getD (2 * i) (Kernel.leaf 0))
    let r := (unLams 64 (ss.getD (2 * i + 1) (Kernel.leaf 0))).2
    ⟨Γ, ⟨(GoedelT.typeOf G Γ l).getD (Kernel.leaf 0), l, r⟩⟩)

/-- The programs and theorems of the files, each read and expanded by the stage-0 compiler's front
end. -/
def results (bundler : List Char) (files : List (List Char × ℕ)) :
    Option (List (List Tree × List GoedelT.Thm)) :=
  files.mapM fun (text, k) ↦ do
    let r ← Kernel.runMain bundler (Kernel.nameTree text)
    let b ← if r.label == 1 then r.children.head? else none
    pure (theoremsOf (← Kernel.unbundle b) k)

open Internal (Term Deriv Decl Entry NormRule Rule)

/-- The terms a rule names. -/
def ruleTerms : Rule → List Term
  | .thm _ _ σ _ | .apply _ _ σ => σ
  | .natInd _ _ s | .listInd _ _ s | .roseInd _ _ _ s => [s]
  | .cut φ | .convFrom φ => [φ]
  | _ => []

/-- The number of nodes of a derivation, the terms its rules name counted. -/
def derivSize : Deriv → ℕ := RoseTree.elim fun l rs ↦ 1 + rs.sum + ((ruleTerms l).map sizeM).sum

/-- The unfolding of every definition below an index. -/
def deltas (m : ℕ) : List NormRule := (List.range m).map NormRule.delta

/-- The unfolding of every definition below an index but those of a list. -/
def deltasExcept (m : ℕ) (ks : List ℕ) : List NormRule :=
  ((List.range m).filter (· ∉ ks)).map NormRule.delta

/-- A development: each theorem with the derivation its prover computes from the entries
before it. -/
def develop (ts : List (Internal.Thm × (Array Entry → Option Deriv))) : Option (List Decl) :=
  (ts.foldl (fun acc (a, p) ↦ acc.bind fun (E, ds) ↦
    (p E).map fun d ↦ (E.push (.language a), ds ++ [.language a d])) (some (#[], []))).map
    Prod.snd

/-- The translation of a file's program and theorems: the constants, the number of definitions,
and the translated theorems. -/
def translate (D : List Tree) (ts : List GoedelT.Thm) :
    Option (Internal.Globals × ℕ × List Internal.Thm) := do
  let (gt, defs) ← program D
  pure (globals defs, lib.length + defs.length, ← ts.mapM (thm gt))

/-- The sides of a translated theorem's equation. -/
def sides (a : Internal.Thm) : Term × Term :=
  (a.concl.children.getD 0 Term.star, a.concl.children.getD 1 Term.star)

/-- The proof by normalization of a theorem with rules. -/
def norm (G : Internal.Globals) (rs : List NormRule) (fuel : ℕ) (a : Internal.Thm)
    (E : Array Entry) : Option Deriv :=
  Internal.byNorm G E 0 rs fuel a.ctx a.hyps (sides a).1 (sides a).2

/-- The proof by normalization, weak head normal forms first, of a theorem with rules. -/
def normW (G : Internal.Globals) (rs : List NormRule) (fuel : ℕ) (a : Internal.Thm)
    (E : Array Entry) : Option Deriv :=
  Internal.byNormW G E 0 rs fuel a.ctx a.hyps (sides a).1 (sides a).2

/-- The proof of a theorem by induction on its innermost list variable with a step. -/
def listInd (G : Internal.Globals) (s : Term) (rs : List NormRule) (fuel : ℕ)
    (a : Internal.Thm) (E : Array Entry) : Option Deriv :=
  Internal.byListInd G E 0 0 1 s rs fuel a.ctx a.hyps (sides a).1 (sides a).2

/-- The prelude's development: the unit laws and the associativity of appending, and appending
the empty list twice by rewriting with the right unit law. -/
def preludeDev (G : Internal.Globals) (m : ℕ) (ts : List Internal.Thm) : Option (List Decl) :=
  let rs := baseRules ++ deltas m
  let step := consT treeTy (Term.var 1) (Term.var 0)
  match ts with
  | [t₀, t₁, t₂, t₃] => develop [(t₀, norm G rs 256 t₀), (t₁, listInd G step rs 256 t₁),
      (t₂, listInd G step rs 256 t₂), (t₃, norm G (baseRules ++ [.thm 1 []]) 256 t₃)]
  | _ => none

/-- The first fold of a term, in preorder: its start and its step. -/
def firstFold : Term → Option (Term × Term) := RoseTree.para fun l cs ↦ match l, cs with
  | .listRec, [(z, _), (s, _), _] => some (z, s)
  | _, cs => cs.findSome? (·.2)

/-- The normal form of a term in a context, in object variables, by rules, or the term. -/
def nf (G : Internal.Globals) (rs : List NormRule) (k : ℕ) (Γ : List Tree) (t : Term) : Term :=
  ((Internal.normalizeW G #[] k rs 4096 Γ [] t).map Prod.fst).getD t

/-- The rebuilding of a bitstring by the fold of the definition of an index that pairs the list
with its value: the first component of the fold is the list, its side in normal form. -/
def rebuild (G : Internal.Globals) (rs : List NormRule) (k : ℕ) : Option Internal.Thm := do
  let (z, s) ← (lib[k]?).bind fun d ↦ firstFold d.body
  pure ⟨0, [bitsTy], [], Term.eq (nf G rs 0 [bitsTy] (Term.fst (Term.listRec z s (v 0)))) (v 0)⟩

/-- The rebuilding of a list by the fold of the case analysis of lists, at any pair of cases: the
first component of the fold applied to the pair is the list, its side in normal form. -/
def lcaseRebuild (G : Internal.Globals) (rs : List NormRule) : Option Internal.Thm := do
  let (z, s) ← (lib[D.lcase]?).bind fun d ↦ firstFold d.body
  let P := prod (exp one X₁) (exp X₀ (exp (list X₀) X₁))
  pure ⟨2, [list X₀, P], [], Term.eq
    (nf G rs 2 [list X₀, P] (Term.fst (Term.app (Term.listRec z s (v 0)) (v 1)))) (v 0)⟩

/-- The numeral one in normal form. -/
def oneN : Term := consT bitTy bit0T (nilT bitTy)

/-- The labels' development: the rebuilding of bitstrings by the folds of addition, of the
successor and of the case analysis of lists; addition of one is the successor, addition to
zero is the identity, and addition of a successor is the successor of the sum, by induction on
the bitstrings and case analysis of their bits, the last first for the functions of the first
summand; and then the theorems, the first by normalization and the others by rewriting with
these lemmas. -/
def natDev (G : Internal.Globals) (m : ℕ) (ts : List Internal.Thm) : Option (List Decl) := do
  let rs := baseRules ++ deltas m
  let [t₀, t₁, t₂] := ts | none
  let rA ← rebuild G rs D.add
  let rS ← rebuild G rs D.succ
  let rL ← lcaseRebuild G rs
  let (zA, sA) ← (lib[D.add]?).bind fun d ↦ firstFold d.body
  let rsR : List NormRule := [.thm 0 [], .thm 1 [], .thm 2 [bitTy, bitsTy]] ++ rs
  let side (a : Internal.Thm) (p : Internal.Prover) : Option Deriv :=
    p a.ctx a.hyps (sides a).1 (sides a).2
  let addOne : Internal.Thm :=
    ⟨0, [bitsTy], [], Term.eq (call D.add [] [v 0, oneN]) (call D.succ [] [v 0])⟩
  let addZero : Internal.Thm := ⟨0, [bitsTy], [], Term.eq (call D.add [] [nilT bitTy, v 0]) (v 0)⟩
  let addSuccF : Internal.Thm := ⟨0, [bitsTy], [], Term.eq
    (nf G rs 0 [bitsTy] (Term.snd (Term.listRec zA sA (call D.succ [] [v 0]))))
    (Term.lam bitsTy (call D.succ [] [call D.add [] [v 0, v 1]]))⟩
  let addSucc : Internal.Thm := ⟨0, [bitsTy, bitsTy], [], Term.eq
    (call D.add [] [v 1, call D.succ [] [v 0]]) (call D.succ [] [call D.add [] [v 1, v 0]])⟩
  let byFun (E : Array Entry) : Internal.Prover :=
    Internal.byFunExt G 0 (bitsInd G 0 (normH G E rsR) (normH G E rsR))
  develop [
    (rA, listInd G (consT bitTy (v 1) (v 0)) rs 256 rA),
    (rS, listInd G (consT bitTy (v 1) (v 0)) rs 256 rS),
    (rL, fun E ↦ Internal.byListInd G E 2 0 1 (consT X₀ (v 1) (v 0)) rs 256 rL.ctx rL.hyps
      (sides rL).1 (sides rL).2),
    (addOne, fun E ↦ side addOne (bitsInd G 0 (normH G E rsR) (normH G E rsR))),
    (addZero, fun E ↦ side addZero
      (Internal.byListIndWith G 0 0 1 (normH G E rsR) (normH G E rsR))),
    (addSuccF, fun E ↦ side addSuccF (Internal.byListIndWith G 0 0 1 (byFun E)
      (Internal.bySplit 3 4 1 (byFun E)))),
    (addSucc, fun E ↦ side addSucc (normH G E (.thm 5 [] :: rs))),
    (t₀, fun E ↦ side t₀ (normH G E rs)),
    (t₁, fun E ↦ side t₁
      (normH G E ([.thm 3 [], .thm 6 []] ++ baseRules ++ deltasExcept m [D.add, D.succ]))),
    (t₂, fun E ↦ side t₂ (normH G E (.thm 4 [] :: baseRules ++ deltasExcept m [D.add])))]

/-- The least time, over three evaluations, to evaluate a Boolean, in microseconds, with its
value. -/
def timeUs (f : Unit → Bool) : IO (Bool × ℕ) := do
  let mut best := 0
  let mut b := false
  for i in [0, 1, 2] do
    let t₀ ← IO.monoNanosNow
    b ← IO.lazyPure fun _ ↦ f ()
    let t₁ ← IO.monoNanosNow
    let d := (t₁ - t₀) / 1000
    if i = 0 ∨ d < best then best := d
  pure (b, best)

/-- The fold of a list of trees by construction is the list. -/
def mapId : Internal.Thm :=
  ⟨0, [list treeTy], [], Term.eq (Term.listRec (nilT treeTy)
    (consT treeTy (Term.var 1) (Term.var 0)) (Term.var 0)) (Term.var 0)⟩

/-- The trees rebuilt from the unfoldings of a list of trees are the rebuilt unfoldings. -/
def mapFusion : Internal.Thm :=
  ⟨0, [list treeTy], [], Term.eq
    (Term.listRec (nilT treeTy) (consT treeTy (nodeT (Term.var 1)) (Term.var 0))
      (Term.listRec (nilT unnodeTy) (consT unnodeTy (unnodeU (Term.var 1)) (Term.var 0))
        (Term.var 0)))
    (Term.listRec (nilT treeTy) (consT treeTy (nodeT (unnodeU (Term.var 1))) (Term.var 0))
      (Term.var 0))⟩

/-- A tree is rebuilt from its unfolding, by Lambek's lemma. -/
def lambek : Internal.Thm :=
  ⟨0, [treeTy], [], Term.eq (nodeT (unnodeU (Term.var 0))) (Term.var 0)⟩

/-- The lemmas on the unfolding of trees, each with its proof: the fold by construction and the
fusion of the rebuilding with the unfolding by list induction, and Lambek's lemma by the
uniqueness of the fold, rewriting by them. -/
def treeLemmas (G : Internal.Globals) : List (Internal.Thm × (Array Entry → Option Deriv)) :=
  [(mapId, listInd G (consT treeTy (Term.var 1) (Term.var 0)) baseRules 64 mapId),
   (mapFusion, listInd G (consT treeTy (nodeT (unnodeU (Term.var 1))) (Term.var 0)) baseRules 64
      mapFusion),
   (lambek, fun E ↦ Internal.byRoseInd G E 0 2 0 1 (nodeT (Term.pair (Term.var 1) (Term.var 0)))
      (baseRules ++ [.thm 0 [], .thm 1 []]) 64 lambek.ctx (sides lambek).1 (sides lambek).2)]

/-- The prelude's development, weak head normal forms first. -/
def preludeDevW (G : Internal.Globals) (m : ℕ) (ts : List Internal.Thm) : Option (List Decl) :=
  let rs := baseRules ++ deltas m
  let step := consT treeTy (Term.var 1) (Term.var 0)
  match ts with
  | [t₀, t₁, t₂, t₃] => develop [(t₀, normW G rs 256 t₀), (t₁, listInd G step rs 256 t₁),
      (t₂, listInd G step rs 256 t₂), (t₃, normW G (baseRules ++ [.thm 1 []]) 256 t₃)]
  | _ => none

/-- The type checker's development: the quoted tree's type, weak head normal forms first,
every definition unfolded. -/
def checkDev (G : Internal.Globals) (m : ℕ) (ts : List Internal.Thm) : Option (List Decl) :=
  develop (ts.map fun t ↦ (t, normW G (baseRules ++ deltas m) 4096 t))

/-- A development of the tree lemmas and then theorems each by normalization, weak head normal
forms first, every definition unfolded and Lambek's lemma rewriting. -/
def treeDev (G : Internal.Globals) (m : ℕ) (ts : List Internal.Thm) : Option (List Decl) :=
  develop (treeLemmas G ++
    ts.map fun t ↦ (t, normW G (.thm 2 [] :: baseRules ++ deltas m) 4096 t))

/-- The bit steps of a derivation: the case analyses of bits, which only the arithmetic of the
labels performs. -/
def bitSteps : Deriv → ℕ := RoseTree.elim fun l rs ↦
  (match l with | .caseInl _ _ | .caseInr _ _ => 1 | _ => 0) + rs.sum

/-- The report of a file, printed, and an error when a development does not check: the nodes of the
language's derivations of the file's theorems, the bit steps among them, and the least of three
times the checker takes, in microseconds; and a row of the same for the lemmas the development
proves before the theorems; the file's name alone where no development is computed. -/
def report (name : String) (D : List Tree) (ts : List GoedelT.Thm)
    (dev : Internal.Globals → ℕ → List Internal.Thm → Option (List Decl)) : IO Unit := do
  match translate D ts with
  | none => throw (IO.userError s!"{name}: no translation")
  | some (G, m, ts) => match dev G m ts with
    | none => IO.println s!"{name},no development"
    | some ds => do
      let k := ds.length - ts.length
      let (okA, tA) ← timeUs fun _ ↦ Internal.checkThms G (ds.take k) #[]
      let some (G₁, E₁) := Internal.checkDev G #[] (ds.take k)
        | throw (IO.userError s!"{name}: the lemmas do not check")
      let (okL, tL) ← timeUs fun _ ↦ Internal.checkThms G₁ (ds.drop k) E₁
      if !(okA && okL) then throw (IO.userError s!"{name}: a development does not check")
      let dvs (l : List Decl) : List Deriv :=
        l.filterMap fun | Decl.language _ d => some d | _ => none
      let row (xs : List ℕ) : String := ",".intercalate (xs.map toString)
      if k > 0 then
        IO.println (name ++ "-lemmas," ++ row [((dvs (ds.take k)).map derivSize).sum,
          ((dvs (ds.take k)).map bitSteps).sum, tA])
      IO.println (name ++ "," ++ row [((dvs (ds.drop k)).map derivSize).sum,
        ((dvs (ds.drop k)).map bitSteps).sum, tL])

/-- The reports of the files, the prelude's development both by innermost normalization and weak
head normal forms first. -/
def reports (rs : Option (List (List Tree × List GoedelT.Thm))) : IO Unit := do
  match rs with
  | some [(D₀, t₀), (D₁, t₁), (D₂, t₂), (D₃, t₃)] => do
    IO.println "file,language_nodes,bit_steps,language_microseconds"
    report "prelude" D₀ t₀ preludeDev
    report "prelude-whnf" D₀ t₀ preludeDevW
    report "nat" D₁ t₁ natDev
    report "check" D₂ t₂ checkDev
    report "datatype" D₃ t₃ treeDev
  | _ => throw (IO.userError "the files do not read")

#eval reports (results Kernel.Stage0Tests.bundler.toList (files.map fun (t, k) ↦ (t.toList, k)))

end GebTests.Prototypes.FreeTopos.TranslationProofs

end
