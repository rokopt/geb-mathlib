/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Weakening -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.Weakening -- shake: keep
public import GebTests.Prototypes.Kernel.Eval -- shake: keep
public meta import GebTests.Prototypes.Kernel.Eval -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The base of the fundamental lemma

The program of the prelude, the reader, the type checker, the traversal of kernel terms and the
evaluator, {lit}`bootstrap/eval.geb`, translated to the internal language and extended by the
definitions the fundamental lemma states: addition and the fuel of a natural number, the stable
convergence of a function of the fuel, the relation at a type by the fold of the type tree into
the predicates on values, the relations of an environment to a context and of a program's
definitions to the types of its globals, and the evaluator's functions at a level of fuel. The
module states the development the lemma rests on, whose declarations the certificate
{lit}`bootstrap/certificates/normalization-base.cert` stores, and the proving of a development's
steps after the theorems of those before it ({lit}`developAfter`), by which the modules importing
it prove theirs.

The proofs are found by deducers: functions from a context, hypotheses and a goal to a derivation
of the internal language, where one is found, composed from the language's rules, its
normalization by rewriting, and case analysis of the data a term's reduction waits on. A
vocabulary of equations is proved first and used as rewriting rules: equations of the checker's
and the evaluator's folds at nodes and of their rebuilding of trees, the relation at each type
former, and the lemmas of addition and stability. The equality of trees is kept folded, sound by
induction on trees ({lit}`equalSound`), so that a test of it is decided by case analysis of its
value; the type tests are inverted to the nodes they test for ({lit}`isArrowInv` and the lemmas
beside it).

## Main definitions

* {lit}`extend` — the program extended by the statement's definitions.
* {lit}`Kit` — the deducers at a development's entries.
* {lit}`fundamental` — the fundamental lemma's formula at a term.
* {lit}`baseDev` — the development.
* {lit}`developAfter` — a development's steps proved after an earlier one's theorems.
* {lit}`extended` — the extended program, as the front end reads it.

## Implementation notes

A deducer adds hypotheses after the given ones: the rewriting of a hypothesis appends the
rewritten one, and a universal introduction appends truth. An equation among the hypotheses is a
rewriting rule from its left side to its right, matched against normal forms, so that an equation
entering by an elimination is normalized before it is used; an equation of a term with itself is
not a rule.

## References

* {cite}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, evaluator, type checker, rewriting, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Normalization

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Translation Geb.FreeTopos.Tactics
open GebTests.Prototypes.FreeTopos.TranslationProofs
open GebTests.Prototypes.FreeTopos.Weakening
open GebTests.Prototypes.FreeTopos.Translation (baseRules)
open Internal (Term NormRule Entry Deriv Decl Definition)
open scoped FinEnum

/-! Deductions. -/

/-- A deduction: a derivation of a formula in a context under hypotheses, when one is found. -/
abbrev Deducer : Type := List Tree → List Term → Term → Option Deriv

/-- A derivation's node of a rule. -/
abbrev nd (l : Internal.Rule) (cs : List Deriv := []) : Deriv := RoseTree.node l cs

/-- The connectives' definitions from the index {lit}`o` and their rules from the index
{lit}`j`. -/
structure Conn where
  /-- The index of the connectives' first definition. -/
  o : ℕ
  /-- The index of the connectives' first rule. -/
  j : ℕ

/-- The node of a definition's application: its index, objects and arguments, the last first. -/
def defnParts (φ : Term) : Option (ℕ × List Tree × List Term) := match φ.label with
  | .defn k θ => some (k, θ, φ.children)
  | _ => none

/-- The proof of an equation by a prover. -/
def dEq (p : Internal.Prover) : Deducer := fun Γ Φ φ ↦ do
  let (t, u) ← Internal.eqParts φ
  p Γ Φ t u

/-- The proof of a formula among the hypotheses. -/
def dHyp : Deducer := fun _ Φ φ ↦ (Φ.findIdx? (· == φ)).map fun i ↦ nd (.hyp i)

/-- The proof of a formula rewritten by a rewriting derivation found for it. -/
def dRwBy (rw : List Tree → List Term → Term → Option (Term × Deriv)) (k : Deducer) :
    Deducer := fun Γ Φ φ ↦ do
  let (φ', d) ← rw Γ Φ φ
  pure (nd .conv [d, ← k Γ Φ φ'])

/-- The rewriting of a term by the evaluator, by rules, to a depth. -/
def evalRw (G : Internal.Globals) (E : Array Entry) (rs : List NormRule) (m : Internal.Depth) :
    List Tree → List Term → Term → Option (Term × Deriv) := fun Γ Φ t ↦
  (Internal.eval G E 0 rs 4096 m Γ Φ t).map fun (t', d, _) ↦ (t', d)

/-- The rewriting of a term by a rewriting derivation, as the checker performs it. -/
def rwWith (G : Internal.Globals) (E : Array Entry) (d : Deriv) :
    List Tree → List Term → Term → Option (Term × Deriv) := fun Γ Φ t ↦
  ((Internal.check G E 0 d).1 Γ Φ t).map (·, d)

/-- A hypothesis rewritten, added after the hypotheses. -/
def dRwHyp (rw : List Tree → List Term → Term → Option (Term × Deriv)) (i : ℕ) (k : Deducer) :
    Deducer := fun Γ Φ φ ↦ do
  let ψ ← Φ[i]?
  let (ψ', d) ← rw Γ Φ ψ
  pure (nd (.cut ψ') [nd (.convFrom ψ) [d, nd (.hyp i)], ← k Γ (Φ ++ [ψ']) φ])

/-- The introduction of an implication. -/
def dImpI (L : Conn) (k : Deducer) : Deducer := fun Γ Φ φ ↦ do
  let (i, _, cs) ← defnParts φ
  match cs with
  | [q, p] =>
    if i = L.o + 2 then pure (Internal.Logic.impI L.j Φ.length p q (← k Γ (Φ ++ [p]) q))
    else none
  | _ => none

/-- The introduction of a universal quantification of an abstraction, its body proved at a new
variable under the hypotheses, weakened, and truth. -/
def dAllI (L : Conn) (k : Deducer) : Deducer := fun Γ Φ φ ↦ do
  let (i, θ, cs) ← defnParts φ
  match θ, cs with
  | [a], [P] => match P.label, P.children with
    | .lam _, [b] =>
      if i = L.o + 3 then
        pure (Internal.Logic.allI (← k (a :: Γ) (Φ.map Internal.weaken1 ++ [Internal.Logic.tt L.o])
          b))
      else none
    | _, _ => none
  | _, _ => none

/-- The introduction of an existential quantification at a witness, the instance proved after
β-reduction. -/
def dExI (L : Conn) (G : Internal.Globals) (E : Array Entry) (w : Term) (k : Deducer) :
    Deducer := fun Γ Φ φ ↦ do
  let (i, θ, cs) ← defnParts φ
  match θ, cs with
  | [a], [P] =>
    if i = L.o + 7 then do
      let d ← dRwBy (rwWith G E (nd .beta)) k Γ Φ (Term.app P w)
      pure (nd (.apply (L.j + 10) [a] [w, P]) [d])
    else none
  | _, _ => none

/-- The introduction of a conjunction. -/
def dConjI (L : Conn) (k₁ k₂ : Deducer) : Deducer := fun Γ Φ φ ↦ do
  let (i, _, cs) ← defnParts φ
  match cs with
  | [q, p] =>
    if i = L.o + 1 then pure (nd (.apply (L.j + 1) [] [q, p]) [← k₁ Γ Φ p, ← k₂ Γ Φ q])
    else none
  | _ => none

/-- The elimination of a conjunction among the hypotheses: its two formulas added after them. -/
def dConjE (L : Conn) (h : ℕ) (k : Deducer) : Deducer := fun Γ Φ φ ↦ do
  let (i, _, cs) ← defnParts (← Φ[h]?)
  match cs with
  | [q, p] =>
    if i = L.o + 1 then
      pure (nd (.cut p) [nd (.apply (L.j + 2) [] [q, p]) [nd (.hyp h)],
        nd (.cut q) [nd (.apply (L.j + 3) [] [q, p]) [nd (.hyp h)], ← k Γ (Φ ++ [p, q]) φ]])
    else none
  | _ => none

/-- The elimination of an implication among the hypotheses: its antecedent proved, its
consequent added after them. -/
def dImpE (L : Conn) (h : ℕ) (kp : Deducer) (k : Deducer) : Deducer := fun Γ Φ φ ↦ do
  let (i, _, cs) ← defnParts (← Φ[h]?)
  match cs with
  | [q, p] =>
    if i = L.o + 2 then
      pure (nd (.cut q) [nd (.apply (L.j + 4) [] [q, p]) [nd (.hyp h), ← kp Γ Φ p],
        ← k Γ (Φ ++ [q]) φ])
    else none
  | _ => none

/-- The elimination of a universal quantification of an abstraction among the hypotheses at a
term: its instance, β-reduced, added after them. -/
def dAllE (L : Conn) (G : Internal.Globals) (E : Array Entry) (h : ℕ) (t : Term) (k : Deducer) :
    Deducer := fun Γ Φ φ ↦ do
  let (i, θ, cs) ← defnParts (← Φ[h]?)
  match θ, cs with
  | [a], [P] =>
    if i = L.o + 3 then do
      let (ψ, _) ← rwWith G E (nd .beta) Γ Φ (Term.app P t)
      pure (nd (.cut ψ) [nd (.convFrom (Term.app P t)) [nd .beta,
        nd (.apply (L.j + 5) [a] [t, P]) [nd (.hyp h)]], ← k Γ (Φ ++ [ψ]) φ])
    else none
  | _, _ => none

/-- The elimination of an existential quantification of an abstraction among the hypotheses:
the formula proved at a new variable under the hypotheses, weakened, truth, and the instance at
the variable, β-reduced. -/
def dExE (L : Conn) (G : Internal.Globals) (E : Array Entry) (h : ℕ) (k : Deducer) :
    Deducer := fun Γ Φ φ ↦ do
  let (i, θ, cs) ← defnParts (← Φ[h]?)
  match θ, cs with
  | [a], [P] =>
    if i = L.o + 7 then do
      let some (Entry.language r) := E[L.j + 11]? | none
      let all ← r.hyps[1]?
      let A := Internal.instTerm [a] [φ, P] all
      -- the universal quantification's body: the implication, its antecedent β-reduced
      let body : Deducer := dImpI L fun Γ' Φ' φ' ↦
        dRwHyp (rwWith G E (nd .beta)) (Φ'.length - 1) k Γ' Φ' φ'
      pure (nd (.apply (L.j + 11) [a] [φ, P]) [nd (.hyp h), ← dAllI L body Γ Φ A])
    else none
  | _, _ => none

/-- The introduction of a disjunction, by its first or its second formula. -/
def dDisjI (L : Conn) (second : Bool) (k : Deducer) : Deducer := fun Γ Φ φ ↦ do
  let (i, _, cs) ← defnParts φ
  match cs with
  | [q, p] =>
    if i = L.o + 6 then
      if second then pure (nd (.apply (L.j + 8) [] [q, p]) [← k Γ Φ q])
      else pure (nd (.apply (L.j + 7) [] [q, p]) [← k Γ Φ p])
    else none
  | _ => none

/-- The elimination of a disjunction among the hypotheses: the formula proved under each of its
formulas. -/
def dDisjE (L : Conn) (h : ℕ) (k₁ k₂ : Deducer) : Deducer := fun Γ Φ φ ↦ do
  let (i, _, cs) ← defnParts (← Φ[h]?)
  match cs with
  | [q, p] =>
    if i = L.o + 6 then
      pure (nd (.apply (L.j + 9) [] [φ, q, p]) [nd (.hyp h),
        ← dImpI L k₁ Γ Φ (Internal.Logic.imp L.o p φ),
        ← dImpI L k₂ Γ Φ (Internal.Logic.imp L.o q φ)])
    else none
  | _ => none

/-- The proof of a formula from falsity, proved. -/
def dFalse (L : Conn) (k : Deducer) : Deducer := fun Γ Φ φ ↦ do
  pure (nd (.apply (L.j + 6) [] [φ]) [← k Γ Φ (Internal.Logic.ff L.o)])

/-! The program and its extension. -/

/-- The program: the prelude, the reader, the type checker, the traversal of kernel terms, the
evaluator, and the weakening proof's statement. -/
def programText : String :=
  Kernel.Stage0Tests.prelude ++ "\n" ++ Kernel.Stage0Tests.reader ++ "\n" ++
    Kernel.Stage0Tests.check ++ "\n" ++ Kernel.Stage0Tests.subst ++ "\n" ++
    Kernel.EvalTests.evalGeb ++ "\n" ++ Weakening.statement

/-- The index of the primitive zero, after the translation's primitives. -/
def kZero : ℕ := prims.length

/-- The index of the primitive successor. -/
def kSucc : ℕ := prims.length + 1

/-- The successor of a natural number. -/
def succN (t : Term) : Term := Term.arr kSucc [] t

/-- The natural number zero. -/
def zeroN : Term := Term.arr kZero [] Term.star

/-- The definitions of the statement, from the index {lit}`q`, for the translated program
{lit}`P`: the addition of natural numbers, the fuel of a natural number, convergence, the
relation, the relation of environments, and the relation of the definitions. -/
structure Defs where
  /-- The index of the first definition. -/
  q : ℕ
  /-- The type of the checker's fold's values. -/
  rr : Tree
  /-- The type of the evaluator's fold's values. -/
  re : Tree
  /-- The checker's fold: its type, its step, and the step of the fold's function. -/
  cr : Tree × Term × Term
  /-- The evaluator's fold: its type and its step. -/
  ce : Tree × Term

namespace Defs

variable (S : Defs)

/-- Addition. -/
def add (m n : Term) : Term := call S.q [] [m, n]

/-- The fuel of a natural number: the leaf whose label is its bitstring. -/
def fuel (k : Term) : Term := call (S.q + 1) [] [k]

/-- Convergence of a function of the fuel to a value the predicate holds of. -/
def conv (F Pr : Term) : Term := call (S.q + 2) [] [F, Pr]

/-- The relation at a type, a predicate on values, with the program's definitions. -/
def rel (D A : Term) : Term := call (S.q + 3) [] [D, A]

/-- The relation of an environment to a context. -/
def envR (D c env : Term) : Term := call (S.q + 4) [] [D, c, env]

/-- Every element of a list satisfies a predicate. -/
def allL (Pr xs : Term) : Term := call (S.q + 5) [] [Pr, xs]

/-- The evaluator's functions at a level of fuel, a natural number. -/
def levelN (D k : Term) : Term := call (S.q + 6) [] [D, k]

/-- The relation of the program's definitions to the types of the globals. -/
def globR (D GT : Term) : Term := call (S.q + 7) [] [D, GT]

/-- The evaluation of a term in an environment at a level. -/
def evN (D k env t : Term) : Term := apps (Term.fst (S.levelN D k)) [env, t]

/-- The type checker's fold at a tree, applied to its step at the globals' types: the pair of
the rebuilt tree and its type as a function of the context. -/
def rrC (GT x : Term) : Term := call (S.q + 8) [] [GT, x]

/-- The evaluator's fold at a tree, applied to its step at the definitions and the functions of
the level below: the pair of the rebuilt tree and its value as a function of the
environment. -/
def peC (D p x : Term) : Term := call (S.q + 9) [] [D, p, x]

end Defs

/-- The truth of a test, a tree whose label is not zero. -/
def truth (o : ℕ) (b : Term) : Term :=
  condT omega (call D.lab [] [b]) (Internal.Logic.tt o) (Internal.Logic.ff o)

/-- The type of the evaluator's functions at a level: evaluation and application. -/
def fnsTy : Tree :=
  prod (exp (list treeTy) (exp treeTy treeTy)) (exp treeTy (exp treeTy treeTy))

/-- The extended program: its constants with the primitives of the natural numbers and the
statement's definitions. -/
def extend (P : Prog) : Option (Prog × Defs) := do
  let (_, (CR, sR, fG)) ← folds P
  let (_, RR) ← Internal.expParts CR
  let w := weakNF P (baseNorm P) 0 [treeTy, list treeTy, fnsTy, list treeTy]
    (apps (Term.fst (apps (call (P.idx "Eval.next") [] []) [v 3, v 2])) [v 1, v 0])
  let (CE, sE, _) ← firstFoldApp w
  let (_, RE) ← Internal.expParts CE
  let S : Defs := ⟨P.G.defs.length, RR, RE, (CR, sR, fG), (CE, sE)⟩
  let o := P.o
  let ff := Internal.Logic.ff o
  let tt := Internal.Logic.tt o
  let ex := Internal.Logic.ex o
  let all := Internal.Logic.all o
  let conj := Internal.Logic.conj o
  let imp := Internal.Logic.imp o
  let pc (name : String) (args : List Term) : Term := apps (call (P.idx name) [] []) args
  let someT (t : Term) : Term := pc "Prelude.some" [t]
  let relC := exp (list treeTy) (exp treeTy omega)
  let ffC := Term.lam (list treeTy) (Term.lam treeTy ff)
  -- the step of the relation's fold, in the children's values and the label, under the
  -- definitions and the value: the first two children's values at the definitions
  let relStep : Term :=
    -- the first two children's values, at a depth of binders below the value
    let H (d : ℕ) : Term :=
      Term.listRec (Term.pair ffC ffC) (Term.pair (v 1) (Term.fst (v 0))) (Term.snd (v (2 + d)))
    let body : Term :=
      -- context: the value, the definitions, the pair of the label and the children's values
      let r0 (d : ℕ) (D x : Term) : Term := Term.app (Term.app (Term.fst (H d)) D) x
      let r1 (d : ℕ) (D x : Term) : Term := Term.app (Term.app (Term.snd (H d)) D) x
      let test (k : ℕ) (t u : Term) : Term :=
        condT omega (call D.eqB [] [Term.fst (v 2), numeral k]) t u
      test Kernel.Label.tyTree
        (ex treeTy (Term.lam treeTy (Term.eq (v 1) (pc "Eval.valQuote" [v 0]))))
      (test Kernel.Label.tyUnit (Term.eq (v 0) (pc "Eval.valUnit" []))
      (test Kernel.Label.tyProd
        (ex treeTy (Term.lam treeTy (ex treeTy (Term.lam treeTy
          (conj (Term.eq (v 2) (pc "Eval.valPair" [v 1, v 0]))
            (conj (r0 2 (v 3) (v 1)) (r1 2 (v 3) (v 0))))))))
      (test Kernel.Label.tyArrow
        (all treeTy (Term.lam treeTy (imp (r0 1 (v 2) (v 0))
          (S.conv (Term.lam nat (apps (Term.snd (S.levelN (v 3) (v 0))) [v 2, v 1]))
            (Term.lam treeTy (r1 2 (v 3) (v 0)))))))
      (test Kernel.Label.tyList
        (conj (truth o (pc "Prelude.isSome" [pc "Eval.listOf" [v 0]]))
          (S.allL (Term.lam treeTy (r0 1 (v 2) (v 0)))
            (call D.children [] [pc "Prelude.get" [pc "Eval.listOf" [v 0]]])))
        ff))))
    Term.lam (list treeTy) (Term.lam treeTy body)
  let defs : List Internal.Defn := [
    -- addition, by recursion on the second summand into functions of the first
    ⟨0, [nat, nat], nat, Term.app (Term.natRec (Term.lam nat (v 0))
      (Term.lam nat (succN (Term.app (v 1) (v 0)))) (v 0)) (v 1)⟩,
    -- the fuel of a natural number
    ⟨0, [nat], treeTy, leafT (Term.natRec bnilT (call D.succ [] [v 0]) (v 0))⟩,
    -- convergence: from some fuel on, the function's value is one value the predicate holds of
    ⟨0, [exp treeTy omega, exp nat treeTy], omega,
      ex nat (Term.lam nat (ex treeTy (Term.lam treeTy
        (conj (all nat (Term.lam nat
            (Term.eq (Term.app (v 4) (S.add (v 2) (v 0))) (someT (v 1)))))
          (Term.app (v 2) (v 0))))))⟩,
    -- the relation at a type, by the fold of the type
    ⟨0, [treeTy, list treeTy], exp treeTy omega,
      Term.app (Term.roseRec relC relStep (v 0)) (v 1)⟩,
    -- the relation of an environment to a context: at each index where the context has some
    -- type, the environment has some value related at the type
    ⟨0, [list treeTy, list treeTy, list treeTy], omega,
      all treeTy (Term.lam treeTy (imp (truth o (pc "Prelude.isSome" [pc "Prelude.nth" [v 2, v 0]]))
        (ex treeTy (Term.lam treeTy
          (conj (Term.eq (pc "Prelude.nth" [v 2, v 1]) (someT (v 0)))
            (Term.app (S.rel (v 4) (pc "Prelude.get" [pc "Prelude.nth" [v 3, v 1]])) (v 0)))))))⟩,
    -- every element of a list satisfies a predicate
    ⟨0, [list treeTy, exp treeTy omega], omega,
      Term.app (Term.listRec (Term.lam (exp treeTy omega) tt)
        (Term.lam (exp treeTy omega) (conj (Term.app (v 0) (v 2)) (Term.app (v 1) (v 0))))
        (v 0)) (v 1)⟩,
    -- the evaluator's functions at a level, by the fold of the level from the level zero
    ⟨0, [nat, list treeTy], fnsTy,
      Term.app (Term.natRec (Term.lam (list treeTy) (pc "Eval.level" [v 0, leafT bnilT]))
        (Term.lam (list treeTy) (pc "Eval.next" [v 0, Term.app (v 1) (v 0)])) (v 0)) (v 1)⟩,
    -- the relation of the definitions to the types of the globals: at each index where a
    -- global's type is some type, a definition is some term, whose evaluation in the empty
    -- environment converges to a value related at the type
    ⟨0, [list treeTy, list treeTy], omega,
      all treeTy (Term.lam treeTy (imp (truth o (pc "Prelude.isSome" [pc "Prelude.nth" [v 1, v 0]]))
        (ex treeTy (Term.lam treeTy
          (conj (Term.eq (pc "Prelude.nth" [v 3, v 1]) (someT (v 0)))
            (S.conv (Term.lam nat (S.evN (v 4) (v 0) (nilT treeTy) (v 1)))
              (S.rel (v 3) (pc "Prelude.get" [pc "Prelude.nth" [v 2, v 1]]))))))))⟩,
    -- the type checker's fold at a tree, applied to its step at the globals' types
    ⟨0, [treeTy, list treeTy], RR, Term.app (Term.roseRec CR sR (v 0)) fG⟩,
    -- the evaluator's fold at a tree, applied to its step
    ⟨0, [treeTy, fnsTy, list treeTy], RE,
      Term.app (Term.roseRec CE sE (v 0)) (pc "Eval.evStep" [v 2, v 1])⟩]
  pure (⟨⟨P.G.prims ++ [Internal.zeroPrim, Internal.succPrim], P.G.defs ++ defs.map .language,
    P.G.base⟩, P.o, P.idx, P.folded⟩, S)

/-! The development. -/

/-- A term, printed. -/
def showT : Term → String := RoseTree.para fun l cs ↦
  let ch := " ".intercalate (cs.map Prod.snd)
  let h : String := match l with
    | .var i => s!"v{i}"
    | .star => "*"
    | .pair => "pair"
    | .fst => "fst"
    | .snd => "snd"
    | .lam _ => "lam"
    | .app => "app"
    | .arr k _ => s!"arr{k}"
    | .natRec => "natRec"
    | .listRec => "listRec"
    | .roseRec _ => "roseRec"
    | .defn k _ => s!"d{k}"
    | .eq => "eq"
  if cs.isEmpty then h else s!"({h} {ch})"

/-- The rules of the natural numbers: their folds at zero and at successors, after the base
rules. -/
def natRules (P : Prog) : List NormRule :=
  baseNorm P ++ [.rule (.natZero kZero), .rule (.natSucc kSucc)]

/-- The normal form of a term by rules, or the term. -/
def nfBy (P : Prog) (rs : List NormRule) (Γ : List Tree) (t : Term) : Term :=
  ((Internal.eval P.G #[] 0 rs 4096 .full Γ [] t).map Prod.fst).getD t

/-- A theorem whose sides are stated in normal form by rules. -/
def nfThm (P : Prog) (rs : List NormRule) (Γ : List Tree) (t u : Term) : Internal.Thm :=
  ⟨0, Γ, [], Term.eq (nfBy P rs Γ t) (nfBy P rs Γ u)⟩

/-- The rules of addition: its lemmas, from left to right, after {name}`natRules`. -/
def addRules (P : Prog) (ix : String → ℕ) : List NormRule :=
  ["natAddZero", "natAddSucc", "natZeroAdd", "natSuccAdd", "natAddAssoc"].map
      (fun nm ↦ .thm (ix nm) []) ++
    natRules P

/-- The lemmas on addition, unfolded: zero and a successor on the right, by its computation; zero
and a successor on the left, associativity and commutativity, by induction on the innermost
variable with the induction hypothesis. -/
def natLemmas (P : Prog) (S : Defs) : List Step :=
  let rs := natRules P
  let rsD := rs ++ [.delta S.q]
  let addZero := nfThm P rs [nat] (S.add (v 0) zeroN) (v 0)
  let addSucc := nfThm P rs [nat, nat] (S.add (v 1) (succN (v 0))) (succN (S.add (v 1) (v 0)))
  let zeroAdd := nfThm P rs [nat] (S.add zeroN (v 0)) (v 0)
  let succAdd := nfThm P rs [nat, nat] (S.add (succN (v 1)) (v 0)) (succN (S.add (v 1) (v 0)))
  let addAssoc := nfThm P rs [nat, nat, nat] (S.add (S.add (v 2) (v 1)) (v 0))
    (S.add (v 2) (S.add (v 1) (v 0)))
  let addComm := nfThm P rs [nat, nat] (S.add (v 1) (v 0)) (S.add (v 0) (v 1))
  let ind (names : List String) (a : Internal.Thm) (ix : String → ℕ) (E : Array Entry) :
      Option Deriv :=
    Internal.byNatIndHyp P.G E 0 kZero kSucc (names.map (fun nm ↦ .thm (ix nm) []) ++ rsD) 4096
      a.ctx [] (sides a).1 (sides a).2
  let comp (a : Internal.Thm) (_ : String → ℕ) (E : Array Entry) : Option Deriv :=
    byMode .full P.G E 0 rsD a.ctx [] (sides a).1 (sides a).2
  [step "natAddZero" addZero (comp addZero), step "natAddSucc" addSucc (comp addSucc),
    step "natZeroAdd" zeroAdd (ind [] zeroAdd), step "natSuccAdd" succAdd (ind [] succAdd),
    step "natAddAssoc" addAssoc (ind [] addAssoc),
    step "natAddComm" addComm (ind ["natZeroAdd", "natSuccAdd"] addComm)]

/-- The application of a constant of the program to arguments. -/
def pc (P : Prog) (name : String) (args : List Term) : Term := apps (call (P.idx name) [] []) args

/-- Stability: from the threshold {lit}`n` on, the function of the fuel {lit}`F` is the optional
value of {lit}`w`. -/
def stab (P : Prog) (S : Defs) (F n w : Term) : Term :=
  Internal.Logic.all P.o nat (Term.lam nat (Term.eq
    (Term.app (Internal.weaken1 F) (S.add (Internal.weaken1 n) (v 0)))
    (pc P "Prelude.some" [Internal.weaken1 w])))

/-- The lemmas on stability: a later threshold, on either side of an addition. -/
def stabLemmas (P : Prog) (S : Defs) : List Step :=
  let L : Conn := ⟨P.o, logicBase⟩
  -- context: the added number, the threshold, the value, the function of the fuel
  let Γ := [nat, nat, treeTy, exp nat treeTy]
  let h := stab P S (v 3) (v 1) (v 2)
  let stabR : Internal.Thm := ⟨0, Γ, [h], stab P S (v 3) (S.add (v 1) (v 0)) (v 2)⟩
  let stabL : Internal.Thm := ⟨0, Γ, [h], stab P S (v 3) (S.add (v 0) (v 1)) (v 2)⟩
  -- under the new variable: the hypothesis at the added number and the variable, then the
  -- goal by normalization with its instance
  let byInst (pre : (String → ℕ) → Array Entry → Deducer → Deducer) (ix : String → ℕ)
      (E : Array Entry) : Deducer :=
    dAllI L fun Γ Φ φ ↦ pre ix E (dAllE L P.G E 0 (S.add (v 1) (v 0)) fun Γ Φ φ ↦
      dEq (byMode .full P.G E 0 (.hyp (Φ.length - 1) :: addRules P ix)) Γ Φ φ) Γ Φ φ
  let run (a : Internal.Thm) (pre : (String → ℕ) → Array Entry → Deducer → Deducer)
      (ix : String → ℕ) (E : Array Entry) : Option Deriv :=
    byInst pre ix E a.ctx a.hyps a.concl
  [step "stabR" stabR (run stabR fun _ _ k ↦ k),
    -- the sum's commutation, cut in and rewritten by first
    step "stabL" stabL (run stabL fun ix E k Γ Φ φ ↦ do
      let σ := [v 2, v 1]
      let some (Entry.language c) := E[ix "natAddComm"]? | none
      let ψ := Internal.instTerm [] σ c.concl
      let q ← dRwBy (evalRw P.G E [.hyp Φ.length] .full) k Γ (Φ ++ [ψ]) φ
      pure (nd (.cut ψ) [nd (.apply (ix "natAddComm") [] σ), q]))]

/-- The case lemmas: a list is empty or a construction, at an object; a tree is a node; a bit is
zero or one. -/
def caseLemmas (P : Prog) : List Step :=
  let L : Conn := ⟨P.o, logicBase⟩
  let ex := Internal.Logic.ex P.o
  let disj := Internal.Logic.disj P.o
  let refl (E : Array Entry) : Deducer := dEq (byWeak P.G E 0 (baseNorm P))
  let listCases : Internal.Thm := ⟨1, [list (x 0)], [], disj (Term.eq (v 0) (nilT (x 0)))
    (ex (x 0) (Term.lam (x 0) (ex (list (x 0)) (Term.lam (list (x 0))
      (Term.eq (v 2) (consT (x 0) (v 1) (v 0)))))))⟩
  let treeNode : Internal.Thm := ⟨0, [treeTy], [], ex bitsTy (Term.lam bitsTy
    (ex (list treeTy) (Term.lam (list treeTy) (Term.eq (v 2) (nodeT (Term.pair (v 1) (v 0)))))))⟩
  let bitCases : Internal.Thm := ⟨0, [bitTy], [], disj (Term.eq (v 0) bit0T) (Term.eq (v 0) bit1T)⟩
  [step "listCases" listCases (fun _ E ↦ do
      let d₀ ← dDisjI L false (refl E) [] [] (Term.subst listCases.concl (Internal.instVar
        (Term.arr 0 [x 0] Term.star)))
      let d₁ ← dDisjI L true (dExI L P.G E (v 1) (dExI L P.G E (v 0) (refl E)))
        [list (x 0), x 0] [] (Internal.listConsAt 1 (x 0) listCases.concl)
      pure (nd (.listIndHyp 0 1) [d₀, d₁])),
    step "treeNode" treeNode (fun _ E ↦ do
      let d ← dExI L P.G E (v 1) (dExI L P.G E (v 0) (refl E)) [list treeTy, bitsTy]
        [Internal.roseHyp 0 1 treeNode.concl] (Internal.roseNodeAt 2 treeTy bitsTy treeNode.concl)
      pure (nd (.roseIndHyp 2 0 1) [d])),
    step "bitCases" bitCases (fun _ E ↦ do
      let inj (k : ℕ) : Term := Term.subst bitCases.concl
        (Internal.atVar0 (Term.arr k [one, one] (v 0)))
      let d₀ ← dDisjI L false (refl E) [one] [] (inj 3)
      let d₁ ← dDisjI L true (refl E) [one] [] (inj 4)
      pure (nd (.coprodInd 3 4) [d₀, d₁]))]

/-! The case analysis of terms. -/

/-- A formula proved and cut in, used as a hypothesis after the hypotheses. -/
def dCut (ψ : Term) (dψ : Deriv) (k : Deducer) : Deducer := fun Γ Φ φ ↦ do
  pure (nd (.cut ψ) [dψ, ← k Γ (Φ ++ [ψ]) φ])

/-- The case analysis of a list term of elements of the type {lit}`a`, by the lemma of index
{lit}`jL`: the formula proved by {lit}`kNil` under the term's equation with the empty list, and
by {lit}`kCons` at two new variables, the head and the tail, under its equation with their
construction; each equation the last hypothesis. -/
def dListCase (L : Conn) (G : Internal.Globals) (E : Array Entry) (jL : ℕ) (a : Tree) (X : Term)
    (kNil kCons : Deducer) : Deducer := fun Γ Φ φ ↦ do
  let some (Entry.language c) := E[jL]? | none
  let ψ := Internal.instTerm [a] [X] c.concl
  dCut ψ (nd (.apply jL [a] [X])) (dDisjE L Φ.length kNil fun Γ' Φ' φ' ↦
    dExE L G E (Φ'.length - 1) (fun Γ'' Φ'' φ'' ↦ dExE L G E (Φ''.length - 1) kCons Γ'' Φ'' φ'')
      Γ' Φ' φ') Γ Φ φ

/-- The case analysis of a bit term, by the lemma of index {lit}`jB`: zero, then one, each
equation the last hypothesis. -/
def dBitCase (L : Conn) (jB : ℕ) (X : Term) (k₀ k₁ : Deducer) : Deducer := fun Γ Φ φ ↦ do
  let some _ := (some () : Option Unit) | none
  let ψ := Internal.Logic.disj L.o (Term.eq X bit0T) (Term.eq X bit1T)
  dCut ψ (nd (.apply jB [] [X])) (dDisjE L Φ.length k₀ k₁) Γ Φ φ

/-- The case analysis of a bitstring term, the bits split to a depth: at each list of bits the
bitstring ends with, the formula proved by {lit}`leaf` at those bits, and past the depth by
{lit}`leaf` at none. -/
def dBits (L : Conn) (G : Internal.Globals) (E : Array Entry) (jL jB : ℕ)
    (leaf : Option (List Bool) → Deducer) (depth : ℕ) : List Bool → Term → Deducer :=
  depth.rec (fun bs X ↦ dListCase L G E jL bitTy X (leaf (some bs)) (leaf none))
    fun _ rec bs X ↦ dListCase L G E jL bitTy X (leaf (some bs))
      (dBitCase L jB (v 1) (rec (bs ++ [false]) (v 0)) (rec (bs ++ [true]) (v 0)))

/-- The rewriting rules of the equations among the hypotheses past the first, but those of a term
with itself. -/
def eqHyps (Φ : List Term) : List NormRule :=
  (List.range Φ.length).filterMap fun i ↦
    if i = 0 then none else (Φ[i]?).bind fun ψ ↦ (Internal.eqParts ψ).bind fun (t, u) ↦
      -- an equation of a term with itself would rewrite it to itself without end
      if t == u then none else some (.hyp i)

/-! The library's functions kept folded, and their equations. -/

/-- The library's functions the reasoning keeps folded: the equality of trees alone, whose value a
case analysis decides at once; the others unfolded, so that a conditional's test reaches its weak
head normal form and the conditional selects its branch before the branches are reduced. -/
def folded : List ℕ := [D.equal]

/-- The rules with the folded functions kept folded: the base rules, every other definition
below the connectives unfolded, and the natural numbers' folds. -/
def foldedRules (P : Prog) : List NormRule :=
  baseRules ++ [.unitVar, .deltaBelow P.o folded, .rule (.natZero kZero), .rule (.natSucc kSucc)]

/-- The normal form of a term by rules with the entries, or nothing. -/
def nfE (G : Internal.Globals) (E : Array Entry) (rs : List NormRule) (Γ : List Tree)
    (t : Term) : Option Term :=
  (Internal.eval G E 0 rs 4096 .full Γ [] t).map Prod.fst

/-- The rest of a construction of a bitstring. -/
def kidsOf' (t : Term) : Option Term := match t.label, t.children with
  | .arr 1 _, [p] => match p.label, p.children with
    | .pair, [_, r] => some r
    | _, _ => none
  | _, _ => none

/-- The rules of the rebuildings of bitstrings and lists by the folds of the successor, in normal
form, and of addition, the successor, the predecessor and the case analysis of lists. -/
def rebRules (ix : String → ℕ) : List NormRule :=
  [.thm (ix "rebSucc") [], .thm (ix "rebA") [], .thm (ix "rebS") [], .thm (ix "rebP") [],
    .thm (ix "rebL") [bitTy, ordTy], .thm (ix "rebL") [bitTy, bitsTy]]

/-- The rebuilding of a bitstring by the successor's fold, in normal form: the rest of the
successor of a bit zero before it, by induction on it. -/
def rebLemmas (P : Prog) : List Step :=
  [("rebSucc", fun _ E ↦ do
    let rs := foldedRules P
    let t ← nfE P.G E rs [bitsTy] (call D.succ [] [consT bitTy bit0T (v 0)])
    let r ← kidsOf' t
    let a : Internal.Thm := ⟨0, [bitsTy], [], Term.eq r (v 0)⟩
    let d ← Internal.byListIndHyp P.G E 0 0 1 rs 4096 a.ctx [] r (v 0)
    pure (a, d))]

/-- The rules of the inequalities of successors with numerals, before {name}`foldedRules`. -/
def eqnRules (P : Prog) (ix : String → ℕ) : List NormRule :=
  ["neq0", "neq1", "neq2", "neq3"].map (fun nm ↦ .thm (ix nm) []) ++ rebRules ix ++
    foldedRules P

/-- The inequalities of a bitstring's successors with the numerals below their number, in normal
form, by case analysis of the innermost bitstring with the inequalities before. -/
def eqnLemmas (P : Prog) : List Step :=
  let rs := foldedRules P
  let sc (t : Term) : Term := call D.succ [] [t]
  let neq (n : ℕ) : Internal.Thm :=
    nfThm P rs [bitsTy] (call D.eqB [] [n.rec (sc (v 0)) fun _ t ↦ sc t, numeral n]) bnilT
  let byBit (a : Internal.Thm) (ix : String → ℕ) (E : Array Entry) : Option Deriv :=
    let p (tag : String) : Internal.Prover := fun Γ Φ t u ↦
      (byMode .full P.G E 0 (eqnRules P ix) Γ Φ t u).orElse fun _ ↦
        let nf (w : Term) : String := ((Internal.eval P.G E 0 (eqnRules P ix) 4096 .full Γ Φ w).map
          fun (r : Term × Deriv × Bool) ↦ showT r.1).getD "none"
        dbgTrace s!"{tag}: {nf t} = {nf u}" fun _ ↦ none
    -- the innermost bitstring empty, or a bit, zero or one, before a rest
    byListSplit P.G 0 0 (p "nil") (bySplit2 3 4 1 (p "zero") (p "one")) a.ctx [] (sides a).1
      (sides a).2
  (List.range 4).map fun n ↦ step s!"neq{n}" (neq n) (byBit (neq n))

/-! The vocabulary kept folded, and the equations that unfold it one node at a time. -/

/-- The kernel's term labels. -/
def termLabels : List ℕ :=
  [Kernel.Label.var, Kernel.Label.lam, Kernel.Label.app, Kernel.Label.unit, Kernel.Label.pair,
    Kernel.Label.fst, Kernel.Label.snd, Kernel.Label.quote, Kernel.Label.cond, Kernel.Label.fold,
    Kernel.Label.iter, Kernel.Label.nil, Kernel.Label.cons, Kernel.Label.foldr, Kernel.Label.prim,
    Kernel.Label.ref, Kernel.Label.lcase, Kernel.Label.para]

/-- The program's constants kept folded: the type checker, its case at a node, the evaluator's
step and application, its functions at a level from those below, and the program's further
folded definitions. -/
def foldedProg (P : Prog) : List ℕ :=
  (["Check.typeIn", "Check.checkNode", "Eval.evStep", "Eval.apStep", "Eval.next"] ++
    P.folded).map P.idx

/-- The rules of the vocabulary: the base rules, every definition below the connectives but the
folded ones unfolded, and the natural numbers' folds. -/
def vBase (P : Prog) : List NormRule :=
  baseRules ++ [.unitVar, .deltaBelow P.o (folded ++ foldedProg P), .rule (.natZero kZero),
    .rule (.natSucc kSucc)]

/-- The names of the vocabulary's equations, used as rules from left to right. -/
def vNames : List String :=
  ["equalFold", "equalNode", "neq0", "neq1", "neq2", "neq3", "typeInRr", "nextFst", "nextSnd",
    "levelSucc", "rrNode",
    "peNode", "peFst", "rrFst", "plFst", "lambek", "kids", "mapId", "apStepClo", "rAddOne",
    "rCmpSucc",
    "rLtZeroSucc", "nthConsSucc"] ++
  (termLabels.map fun k ↦ s!"checkNode{k}") ++ (termLabels.map fun k ↦ s!"evStep{k}") ++
  ((List.range 5).map fun k ↦ s!"rel{k}")

/-- The rules of the vocabulary's equations and the lengths' equations at lists of trees, before
{name}`vBase`. -/
def vRules (P : Prog) (ix : String → ℕ) : List NormRule :=
  vNames.map (fun nm ↦ .thm (ix nm) []) ++
    [.thm (ix "rebTail") [treeTy], .thm (ix "rIterSucc") [list treeTy]] ++ rebRules ix ++
    vBase P

/-- An equation of the vocabulary, generated: a term's normal form by the vocabulary's rules
before it, and its reduction to the depth {lit}`m` with the definitions of {lit}`unfold` unfolded
as well, the reduction's derivation its proof. -/
def genEq (P : Prog) (name : String) (Γ : List Tree) (t : Term) (unfold : List ℕ)
    (m : Internal.Depth := .weak) (extra : List String := []) : Step :=
  (name, fun ix E ↦ do
    let rs := vRules P ix
    let some l := nfE P.G E rs Γ t | dbgTrace s!"{name}: left" fun _ ↦ none
    let rsU := extra.map (fun nm ↦ .thm (ix nm) []) ++ rs ++ unfold.map .delta
    let some (r, d, _) := Internal.eval P.G E 0 rsU 4096 m Γ [] l
      | dbgTrace s!"{name}: right" fun _ ↦ none
    pure (⟨0, Γ, [], Term.eq l r⟩, nd .join [d, nd .refl]))

/-- An equation of the vocabulary unfolding a definition at a term's root: the term's normal form
by the vocabulary's rules before it, the definition of index {lit}`k` unfolded at the root
alone, and the result normalized with the rules of the names {lit}`extra` before the
vocabulary's, the folded definition kept folded below the root. -/
def genRoot (P : Prog) (name : String) (Γ : List Tree) (t : Term) (k : ℕ) (extra : List String) :
    Step :=
  (name, fun ix E ↦ do
    let rs := vRules P ix
    let some l := nfE P.G E rs Γ t | dbgTrace s!"{name}: left" fun _ ↦ none
    let some (l₁, d₁, _) := Internal.eval P.G E 0 [.delta k] 4096 .head Γ [] l
      | dbgTrace s!"{name}: root" fun _ ↦ none
    let some (r, d₂, _) := Internal.eval P.G E 0 (extra.map (fun nm ↦ .thm (ix nm) []) ++ rs)
        4096 .full Γ [] l₁
      | dbgTrace s!"{name}: right" fun _ ↦ none
    pure (⟨0, Γ, [], Term.eq l r⟩, nd .join [nd .trans [d₁, d₂], nd .refl]))

/-- An equation of the vocabulary between two terms, each in normal form by the vocabulary's
rules before it, proved by normalizing both with the definitions of {lit}`unfold` unfolded. -/
def genEq2 (P : Prog) (name : String) (Γ : List Tree) (t u : Term) (unfold : List ℕ) : Step :=
  (name, fun ix E ↦ do
    let rs := vRules P ix
    let some l := nfE P.G E rs Γ t | dbgTrace s!"{name}: left" fun _ ↦ none
    let some r := nfE P.G E rs Γ u | dbgTrace s!"{name}: right" fun _ ↦ none
    let some d := byMode .full P.G E 0 (rs ++ unfold.map .delta) Γ [] l r
      | dbgTrace s!"{name}: unequal" fun _ ↦ none
    pure (⟨0, Γ, [], Term.eq l r⟩, d))

/-- The object parameters of the first application of the definition of an index in a term. -/
def defnObjs (k : ℕ) : Term → Option (List Tree) := RoseTree.para fun l cs ↦ match l with
  | .defn k' θ => if k' = k then some θ else cs.findSome? (·.2)
  | _ => cs.findSome? (·.2)

/-- The map of the checker's folded fold over a list of trees, at the globals' types. -/
def mapRr (S : Defs) (GT cs : Term) : Term :=
  Term.app (Term.listRec (Term.lam (list treeTy) (nilT S.rr))
    (Term.lam (list treeTy) (consT S.rr (S.rrC (v 0) (v 2)) (Term.app (v 1) (v 0)))) cs) GT

/-- The map of the evaluator's folded fold over a list of trees, at the definitions and the
functions of the level below. -/
def mapPe (S : Defs) (D p cs : Term) : Term :=
  Term.app (Term.listRec (Term.lam (prod (list treeTy) fnsTy) (nilT S.re))
    (Term.lam (prod (list treeTy) fnsTy)
      (consT S.re (S.peC (Term.fst (v 0)) (Term.snd (v 0)) (v 2)) (Term.app (v 1) (v 0)))) cs)
    (Term.pair D p)

/-- The folds at a node: the fusion of the map of the children's folds with the application to
the step, by induction on the children, and each fold at a node, its children's folds folded. -/
def nodeLemmas (P : Prog) (S : Defs) : List Step :=
  let (CR, sR, fG) := S.cr
  let (CE, sE) := S.ce
  let node (l cs : Term) : Term := nodeT (Term.pair l cs)
  [("rrFus", fun ix E ↦ do
      let rs := vRules P ix
      let θ ← defnObjs D.mapApp sR
      let Γ := [list treeTy, list treeTy]
      let lhs := call D.mapApp θ [Term.listRec (nilT CR)
        (consT CR (Term.roseRec CR sR (v 1)) (v 0)) (v 0), fG]
      let l ← nfE P.G E rs Γ lhs
      let r ← nfE P.G E rs Γ (mapRr S (v 1) (v 0))
      let d ← Internal.byListIndHyp P.G E 0 0 1 (rs ++ [.delta (S.q + 8)]) 4096 Γ [] l r
      pure (⟨0, Γ, [], Term.eq l r⟩, d)),
    ("peFus", fun ix E ↦ do
      let rs := vRules P ix
      let θ ← defnObjs D.mapApp sE
      let Γ := [list treeTy, fnsTy, list treeTy]
      let lhs := call D.mapApp θ [Term.listRec (nilT CE)
        (consT CE (Term.roseRec CE sE (v 1)) (v 0)) (v 0), pc P "Eval.evStep" [v 2, v 1]]
      let l ← nfE P.G E rs Γ lhs
      let r ← nfE P.G E rs Γ (mapPe S (v 2) (v 1) (v 0))
      let d ← Internal.byListIndHyp P.G E 0 0 1 (rs ++ [.delta (S.q + 9)]) 4096 Γ [] l r
      pure (⟨0, Γ, [], Term.eq l r⟩, d)),
    genRoot P "rrNode" [list treeTy, bitsTy, list treeTy] (S.rrC (v 2) (node (v 1) (v 0)))
      (S.q + 8) ["rrFus"],
    genRoot P "peNode" [list treeTy, bitsTy, fnsTy, list treeTy]
      (S.peC (v 3) (v 2) (node (v 1) (v 0))) (S.q + 9) ["peFus"]]

/-- The rebuilding of a tree by a fold, whose value at a node pairs the node rebuilt from its
children's first components with another value: the first component, as a function of a
parameter {lit}`F` of the type {lit}`FX` given by {lit}`fstAt`, is the identity, by induction on
rose trees with the fusion of the children's first components with the map of the functions, and
the map of constant functions, each by induction on the children; and its instance at the
parameter {lit}`inst` in the context {lit}`Γd` below the tree, the folded definition of index
{lit}`unfold` unfolded first where given, whose first component is thereby the tree. -/
def rebuildLemmas (P : Prog) (tag : String) (FX : Tree) (fstAt : Term → Term → Term)
    (Γd : List Tree) (folded : Term) (inst : Term) (unfold : Option ℕ) : List Step :=
  -- the step of the induction, in the children's functions and the label
  let sF := Term.lam FX (nodeT (Term.pair (v 2) (call D.mapApp [FX, treeTy] [v 1, v 0])))
  let mapF := Term.listRec (nilT (exp FX treeTy))
    (consT (exp FX treeTy) (Term.lam FX (fstAt (v 2) (v 0))) (v 0)) (v 0)
  let fstAbs : Internal.Thm := ⟨0, [treeTy], [], Term.eq (Term.lam FX (fstAt (v 1) (v 0)))
    (Term.lam FX (v 1))⟩
  [(s!"{tag}KidsFus", fun ix E ↦ do
      let rs := vRules P ix
      let some t := nfE P.G E rs [list treeTy, bitsTy, FX]
          (fstAt (nodeT (Term.pair (v 1) (v 0))) (v 2))
        | dbgTrace s!"{tag}KidsFus: no normal form" fun _ ↦ none
      let some kids := kidsOf t | dbgTrace s!"{tag}KidsFus: {showT t}" fun _ ↦ none
      let l := Term.rename kids fun j ↦ if j = 2 then 1 else j
      let r ← nfE P.G E rs [list treeTy, FX] (call D.mapApp [FX, treeTy] [mapF, v 1])
      let some d := Internal.byListIndHyp P.G E 0 0 1 rs 4096 [list treeTy, FX] [] l r
        | dbgTrace s!"{tag}KidsFus: {showT l}\n  = {showT r}" fun _ ↦ none
      pure (⟨0, [list treeTy, FX], [], Term.eq l r⟩, d)),
    (s!"{tag}Const", fun ix E ↦ do
      let rs := vRules P ix
      let Γ := [list treeTy, FX]
      let l ← nfE P.G E rs Γ (call D.mapApp [FX, treeTy] [Term.listRec (nilT (exp FX treeTy))
        (consT (exp FX treeTy) (Term.lam FX (v 2)) (v 0)) (v 0), v 1])
      let d ← Internal.byListIndHyp P.G E 0 0 1 rs 4096 Γ [] l (v 0)
      pure (⟨0, Γ, [], Term.eq l (v 0)⟩, d)),
    (s!"{tag}FstAbs", fun ix E ↦ do
      let rs := [.thm (ix s!"{tag}KidsFus") [], .thm (ix s!"{tag}Const") []] ++ vRules P ix
      let some d := byRoseIndWith P.G 0 sF (Internal.byFunExt P.G 0 (byMode .full P.G E 0 rs))
          fstAbs.ctx [] (sides fstAbs).1 (sides fstAbs).2
        | dbgTrace s!"{tag}FstAbs: not proved" fun _ ↦ none
      pure (fstAbs, d)),
    (s!"{tag}Fst", fun ix E ↦ do
      let rs := vRules P ix
      let Γ := treeTy :: Γd
      let l ← nfE P.G E rs Γ (Term.fst folded)
      -- the instance of the first component as a function of the parameter
      let Fa := Internal.instTerm [] [v 0] (sides fstAbs).1
      let Ha := Internal.instTerm [] [v 0] (sides fstAbs).2
      let e := Term.eq (Term.app Fa inst) (Term.app Ha inst)
      let de := nd (.convFrom e) [nd .cong [nd .beta, nd .beta],
        nd .join [nd .cong [nd (.thm (ix s!"{tag}FstAbs") [] [v 0] false), nd .refl], nd .refl]]
      let d ← match unfold with
        | some k => do
          let (_, d₁, _) ← Internal.eval P.G E 0 [.delta k] 4096 .head Γ [] (Term.fst folded)
          pure (nd .conv [nd .cong [d₁, nd .refl], de])
        | none => do
          -- the first component's normal form, from the first component
          let (_, dn, _) ← Internal.eval P.G E 0 rs 4096 .full Γ [] (Term.fst folded)
          pure (nd (.convFrom (Term.eq (Term.fst folded) (v 0))) [nd .cong [dn, nd .refl], de])
      pure (⟨0, Γ, [], Term.eq l (v 0)⟩, d))]

/-- The first subterms, in preorder, at which two terms differ. -/
def firstDiff (t u : Term) : Option (Term × Term) :=
  (RoseTree.para (fun l (cs : List (Term × (Term → Option (Term × Term)))) (u : Term) ↦
    if l == u.label ∧ cs.length == u.children.length then
      (cs.zip u.children).findSome? fun ((_, f), c) ↦ f c
    else some (RoseTree.node l (cs.map Prod.fst), u)) t) u

/-- A theorem of the weakening proof's development restated in the vocabulary's normal form: its
sides' normal forms, by converting from its instance at its own variables. -/
def restate (P : Prog) (name src : String) : Step :=
  (name, fun ix E ↦ do
    let some (Entry.language a) := E[ix src]? | none
    let (l, r) ← Internal.eqParts a.concl
    let rs := vRules P ix
    let (l', dl, _) ← Internal.eval P.G E a.arity rs 4096 .full a.ctx [] l
    let (r', dr, _) ← Internal.eval P.G E a.arity rs 4096 .full a.ctx [] r
    let θ := (List.range a.arity).map x
    let σ := (List.range a.ctx.length).map v
    pure (⟨a.arity, a.ctx, [], Term.eq l' r'⟩,
      nd (.convFrom (Term.eq l r)) [nd .cong [dl, dr], nd (.apply (ix src) θ σ)]))

/-- The lemmas on lookups: the weakening proof's lemmas at successors restated, a bitstring empty
or a successor, and the lookup in a construction at a successor's index; and the application of
a closure. -/
def lookupLemmas (P : Prog) : List Step :=
  let ex := Internal.Logic.ex P.o
  let disj := Internal.Logic.disj P.o
  let L : Conn := ⟨P.o, logicBase⟩
  let sc (t : Term) : Term := call D.succ [] [t]
  let node (l cs : Term) : Term := nodeT (Term.pair l cs)
  let ls (ts : List Term) : Term := ts.foldr (consT treeTy) (nilT treeTy)
  [("rebTail", fun ix E ↦ do
      let rs := vRules P ix
      let X := x 0
      let t := Term.fst (Term.listRec (Term.pair (nilT X) (nilT X))
        (Term.pair (consT X (v 1) (Term.fst (v 0))) (Term.fst (v 0))) (v 0))
      let l ← (Internal.eval P.G E 1 rs 4096 .full [list X] [] t).map Prod.fst
      let d ← Internal.byListIndHyp P.G E 1 0 1 rs 4096 [list X] [] l (v 0)
      pure (⟨1, [list X], [], Term.eq l (v 0)⟩, d)),
    restate P "rIterSucc" "iterSuccP", restate P "rIterComm" "iterCommP",
    restate P "rCmpSucc" "cmpSuccP", restate P "rSuccPred" "succPredP",
    restate P "rAddOne" "addOne", restate P "rLtZeroSucc" "ltZeroSucc",
    ("bitsSucc", fun ix E ↦ do
      let a : Internal.Thm := ⟨0, [bitsTy], [], disj (Term.eq (v 0) bnilT)
        (ex bitsTy (Term.lam bitsTy (Term.eq (v 1) (sc (v 0)))))⟩
      let rs := [.thm (ix "rSuccPred") []] ++ vRules P ix
      let byN : Deducer := dEq (byMode .full P.G E 0 rs)
      let d₀ ← dDisjI L false byN [] [] (Term.subst a.concl (Internal.instVar
        (Term.arr 0 [bitTy] Term.star)))
      let d₁ ← dDisjI L true (dExI L P.G E (call D.pred [] [consT bitTy (v 1) (v 0)]) byN)
        [bitsTy, bitTy] [] (Internal.listConsAt 1 bitTy a.concl)
      pure (a, nd (.listIndHyp 0 1) [d₀, d₁])),
    ("nthConsSucc", fun ix E ↦ do
      let rs := [.thm (ix "rAddOne") [], .thm (ix "rCmpSucc") [],
        .thm (ix "rIterSucc") [list treeTy]] ++ vRules P ix
      let Γ := [bitsTy, list treeTy, treeTy]
      let l ← nfE P.G E rs Γ (pc P "Prelude.nth" [consT treeTy (v 2) (v 1), leafT (sc (v 0))])
      let r ← nfE P.G E rs Γ (pc P "Prelude.nth" [v 1, leafT (v 0)])
      let some d := byMode .full P.G E 0 rs Γ [] l r
        | dbgTrace s!"nthConsSucc differs: {(firstDiff l r).map fun (a, b) ↦
            s!"{showT a}\n  vs {showT b}"}" fun _ ↦ none
      pure (⟨0, Γ, [], Term.eq l r⟩, d)),
    genEq P "apStepClo" [treeTy, treeTy, treeTy, list treeTy, fnsTy]
      (pc P "Eval.apStep" [v 4, node (numeral 26) (ls [node (numeral 0) (v 3), v 2, v 1]), v 0])
      [P.idx "Eval.apStep"]]

/-- The relation of environments extended: an environment related to a context and a value
related at a type, the environment with the value related to the context with the type, by case
analysis of the index's label, empty or a successor. -/
def envConsLemma (P : Prog) (S : Defs) : Step :=
  ("envCons", fun ix E ↦ do
    let L : Conn := ⟨P.o, logicBase⟩
    let G := P.G
    -- context: the value, the type, the environment, the context, the definitions
    let a : Internal.Thm := ⟨0, [treeTy, treeTy, list treeTy, list treeTy, list treeTy],
      [S.envR (v 4) (v 3) (v 2), Term.app (S.rel (v 4) (v 1)) (v 0)],
      S.envR (v 4) (consT treeTy (v 1) (v 3)) (consT treeTy (v 0) (v 2))⟩
    let rules (Φ : List Term) : List NormRule :=
      eqHyps Φ ++ [.thm (ix "nthConsSucc") []] ++ vRules P ix
    let norm : Deducer → Deducer := fun k Γ Φ ψ ↦ dRwBy (evalRw G E (rules Φ) .full) k Γ Φ ψ
    let byNorm : Deducer := fun Γ Φ ψ ↦ (dEq (byMode .full G E 0 (rules Φ)) Γ Φ ψ).orElse fun _ ↦
      match Internal.eqParts ψ with
      | some (t, u) =>
        let nf (w : Term) : Option Term := (evalRw G E (rules Φ) .full Γ Φ w).map Prod.fst
        dbgTrace s!"unequal: {((nf t).bind fun a ↦ (nf u).bind fun b ↦ firstDiff a b).map
          fun (a, b) ↦ s!"{showT a}\n  vs {showT b}"}" fun _ ↦ none
      | none => none
    -- a hypothesis normalized, and the normalized goal found among the hypotheses
    let byHyp (h : ℕ) : Deducer := fun Γ Φ ψ ↦
      dRwHyp (evalRw G E (rules Φ.dropLast) .full) h (norm dHyp) Γ Φ ψ
    let unfold (k : ℕ) (h : ℕ) (kd : Deducer) : Deducer := fun Γ Φ ψ ↦
      dRwHyp (evalRw G E [.delta k] .head) h kd Γ Φ ψ
    let last (Φ : List Term) : ℕ := Φ.length - 1
    let exE (k : Deducer) : Deducer := fun Γ Φ ψ ↦ dExE L G E (last Φ) k Γ Φ ψ
    let conjE (k : Deducer) : Deducer := fun Γ Φ ψ ↦ dConjE L (last Φ) k Γ Φ ψ
    let allE (t : Term) (k : Deducer) : Deducer := fun Γ Φ ψ ↦ dAllE L G E (last Φ) t k Γ Φ ψ
    let impE (kp k : Deducer) : Deducer := fun Γ Φ ψ ↦ dImpE L (last Φ) kp k Γ Φ ψ
    let some (Entry.language bs) := E[ix "bitsSucc"]? | none
    -- the lookup's equation and the relation, the last two hypotheses: the equation normalized
    -- without them, and the value the witness
    let witness : Deducer := fun Γ Φ ψ ↦
      let r := Φ.length - 1
      dRwHyp (evalRw G E (rules (Φ.take (Φ.length - 2))) .full) (Φ.length - 2)
        (dExI L G E (v 0) (dConjI L byNorm (byHyp r))) Γ Φ ψ
    let succ : Deducer :=
      exE (unfold (S.q + 4) 0 (allE (leafT (v 0)) (impE (byHyp 3) (exE (conjE witness)))))
    let body : Deducer := dAllI L (dImpI L fun Γ Φ ψ ↦ do
      -- context: the index; hypotheses: the relations, truth and the lookup's truth
      let X ← nfE G E (vRules P ix) Γ (call D.lab [] [v 0])
      let cases := Internal.instTerm [] [X] bs.concl
      dCut cases (nd (.apply (ix "bitsSucc") [] [X]))
        -- the empty label: the value itself; a successor's: the environment's relation at its
        -- predecessor
        (dDisjE L (last Φ + 1) (dExI L G E (v 1) (dConjI L byNorm (byHyp 1))) succ) Γ Φ ψ)
    let some d := dRwBy (evalRw G E [.delta (S.q + 4)] .head) body a.ctx a.hyps a.concl
      | dbgTrace "envCons: not proved" fun _ ↦ none
    pure (a, d))

/-- The relation at each type's node, its children's relations folded: the tree type, the unit
type, products, function types and lists. -/
def relLemmas (P : Prog) (S : Defs) : List Step :=
  let o := P.o
  let ex := Internal.Logic.ex o
  let all := Internal.Logic.all o
  let conj := Internal.Logic.conj o
  let imp := Internal.Logic.imp o
  let node (l cs : Term) : Term := nodeT (Term.pair l cs)
  let ls (ts : List Term) : Term := ts.foldr (consT treeTy) (nilT treeTy)
  let relAt (D A x : Term) : Term := Term.app (S.rel D A) x
  [genEq2 P "rel0" [list treeTy] (S.rel (v 0) (node (numeral 0) (ls [])))
      (Term.lam treeTy (ex treeTy (Term.lam treeTy
        (Term.eq (v 1) (pc P "Eval.valQuote" [v 0]))))) [S.q + 3],
    genEq2 P "rel1" [list treeTy] (S.rel (v 0) (node (numeral 1) (ls [])))
      (Term.lam treeTy (Term.eq (v 0) (pc P "Eval.valUnit" []))) [S.q + 3],
    -- context: the second type, the first, the definitions
    genEq2 P "rel2" [treeTy, treeTy, list treeTy] (S.rel (v 2) (node (numeral 2) (ls [v 1, v 0])))
      (Term.lam treeTy (ex treeTy (Term.lam treeTy (ex treeTy (Term.lam treeTy
        (conj (Term.eq (v 2) (pc P "Eval.valPair" [v 1, v 0]))
          (conj (relAt (v 5) (v 4) (v 1)) (relAt (v 5) (v 3) (v 0))))))))) [S.q + 3],
    genEq2 P "rel3" [treeTy, treeTy, list treeTy] (S.rel (v 2) (node (numeral 3) (ls [v 1, v 0])))
      (Term.lam treeTy (all treeTy (Term.lam treeTy (imp (relAt (v 4) (v 3) (v 0))
        (S.conv (Term.lam nat (apps (Term.snd (S.levelN (v 5) (v 0))) [v 2, v 1]))
          (Term.lam treeTy (relAt (v 5) (v 3) (v 0)))))))) [S.q + 3],
    genEq2 P "rel4" [treeTy, list treeTy] (S.rel (v 1) (node (numeral 4) (ls [v 0])))
      (Term.lam treeTy (conj (truth o (pc P "Prelude.isSome" [pc P "Eval.listOf" [v 0]]))
        (S.allL (Term.lam treeTy (relAt (v 3) (v 2) (v 0)))
          (call D.children [] [pc P "Prelude.get" [pc P "Eval.listOf" [v 0]]])))) [S.q + 3]]

/-- The vocabulary's equations: the checker as its fold's second component, the functions at a
level as the evaluator's fold and its application, the level at a successor, the folds at a
node, and the checker's case, the evaluator's step and the relation at each label. -/
def vLemmas (P : Prog) (S : Defs) : List Step :=
  let fns := pc P "Eval.next"
  let node (l cs : Term) : Term := nodeT (Term.pair l cs)
  [("equalFold", fun ix E ↦ do
      let d ← lib[D.equal]?
      let Γ := [treeTy, treeTy]
      -- the definition's body at the two trees: the fold at the first applied to the second
      let raw := Term.subst d.body (Term.substList [v 0, v 1])
      let rs := vRules P ix
      let some l := nfE P.G E rs Γ raw | none
      let r := call D.equal [] [v 1, v 0]
      let pr ← byMode .full P.G E 0 (rs ++ [.delta D.equal]) Γ [] l r
      pure (⟨0, Γ, [], Term.eq l r⟩, pr)),
    genRoot P "equalNode" [list treeTy, bitsTy, list treeTy, bitsTy]
      (call D.equal [] [nodeT (Term.pair (v 3) (v 2)), nodeT (Term.pair (v 1) (v 0))]) D.equal [],
    genEq2 P "typeInRr" [treeTy, list treeTy, list treeTy] (pc P "Check.typeIn" [v 2, v 1, v 0])
      (Term.app (Term.snd (S.rrC (v 2) (v 0))) (v 1)) [P.idx "Check.typeIn", S.q + 8],
    genEq2 P "nextFst" [treeTy, list treeTy, fnsTy, list treeTy]
      (apps (Term.fst (fns [v 3, v 2])) [v 1, v 0])
      (Term.app (Term.snd (S.peC (v 3) (v 2) (v 0))) (v 1))
      [P.idx "Eval.next", S.q + 9],
    genEq P "nextSnd" [treeTy, treeTy, fnsTy, list treeTy]
      (apps (Term.snd (fns [v 3, v 2])) [v 1, v 0]) [P.idx "Eval.next"],
    genEq2 P "levelSucc" [nat, list treeTy] (S.levelN (v 1) (succN (v 0)))
      (fns [v 1, S.levelN (v 1) (v 0)]) [S.q + 6]] ++
  (termLabels.map fun k ↦ genEq P s!"checkNode{k}"
    [list treeTy, list S.rr, list treeTy, list treeTy]
    (pc P "Check.checkNode" [v 3, node (numeral k) (v 2), v 1, v 0]) [P.idx "Check.checkNode"]) ++
  (termLabels.map fun k ↦ genEq P s!"evStep{k}"
    [list treeTy, list (exp (list treeTy) treeTy), list treeTy, fnsTy, list treeTy]
    (pc P "Eval.evStep" [v 4, v 3, node (numeral k) (v 2), v 1, v 0]) [P.idx "Eval.evStep"]) ++
  relLemmas P S ++ nodeLemmas P S ++
  (match Internal.expParts S.ce.1 with
    | some (FE, _) => rebuildLemmas P "pe" FE
        (fun x F ↦ Term.fst (Term.app (Term.roseRec S.ce.1 S.ce.2 x) F)) [fnsTy, list treeTy]
        (S.peC (v 2) (v 1) (v 0)) (pc P "Eval.evStep" [v 2, v 1]) (some (S.q + 9))
    | none => []) ++
  rebuildLemmas P "rr" (list treeTy) (fun x GT ↦ Term.fst (S.rrC GT x)) [list treeTy]
    (S.rrC (v 1) (v 0)) (v 1) none ++
  (match firstFoldApp (weakNF P (baseNorm P) 0 [treeTy] (pc P "Eval.listOf" [v 0])) with
    | some (CP, sP, FP) => match Internal.expParts CP with
      | some (FX, _) => rebuildLemmas P "pl" FX
          (fun x F ↦ Term.fst (Term.app (Term.roseRec CP sP x) F)) []
          (Term.app (Term.roseRec CP sP (v 0)) FP) FP none
      | none => []
    | none => []) ++
  lookupLemmas P ++ [envConsLemma P S]

/-- The number of children of the kernel's term of a label. -/
def arityOf' (l : ℕ) : Option ℕ :=
  if l = Kernel.Label.unit then some 0
  else if l = Kernel.Label.var ∨ l = Kernel.Label.fst ∨ l = Kernel.Label.snd ∨
    l = Kernel.Label.quote ∨ l = Kernel.Label.fold ∨ l = Kernel.Label.para ∨
    l = Kernel.Label.iter ∨ l = Kernel.Label.nil ∨ l = Kernel.Label.prim ∨
    l = Kernel.Label.ref then some 1
  else if l = Kernel.Label.lam ∨ l = Kernel.Label.app ∨ l = Kernel.Label.pair ∨
    l = Kernel.Label.cons ∨ l = Kernel.Label.foldr ∨ l = Kernel.Label.lcase then some 2
  else if l = Kernel.Label.cond then some 3
  else none

/-- The rules of addition's lemmas, before the rules with the folded functions kept folded. -/
def addLemmaRules (ix : String → ℕ) : List NormRule :=
  ["natAddZero", "natAddSucc", "natZeroAdd", "natSuccAdd", "natAddAssoc"].map
    fun nm ↦ .thm (ix nm) []

/-- The proof of convergence from a threshold to a value: the stability's equation proved by
{lit}`stable` at a new variable, and the predicate's instance by {lit}`related`. -/
def dConv (L : Conn) (G : Internal.Globals) (E : Array Entry) (S : Defs) (n w : Term)
    (stable related : Deducer) : Deducer :=
  dRwBy (evalRw G E [.delta (S.q + 2)] .head) (dExI L G E n
    (dExI L G E w (dConjI L (dAllI L stable) related)))

/-! The statement. -/

/-- The fundamental lemma's formula at a term, the variable of index 0: for all types of the
globals, definitions, contexts and environments, if the definitions are related to the types,
the environment to the context, and the term has some type in the context, then its evaluation
in the environment converges to a value related at that type. -/
def fundamental (P : Prog) (S : Defs) : Term :=
  let all := Internal.Logic.all P.o
  let imp := Internal.Logic.imp P.o
  -- context: the environment, the context, the definitions, the globals' types, the term
  let ty := pc P "Check.typeIn" [v 3, v 1, v 4]
  all (list treeTy) (Term.lam (list treeTy) (all (list treeTy) (Term.lam (list treeTy)
    (all (list treeTy) (Term.lam (list treeTy) (all (list treeTy) (Term.lam (list treeTy)
      (imp (S.globR (v 2) (v 3)) (imp (S.envR (v 2) (v 1) (v 0))
        (imp (truth P.o (pc P "Prelude.isSome" [ty]))
          (S.conv (Term.lam nat (S.evN (v 3) (v 0) (v 1) (v 5)))
            (S.rel (v 2) (pc P "Prelude.get" [ty])))))))))))))

/-- A development's steps after an earlier one, given the names of the earlier one's theorems and
the entries after it: each step proved with the entries before it, its theorem added to them. The
names of all the theorems, the entries after the steps and the steps' declarations; the name of
the first step not proved, where one is not. -/
def developAfter (names : List String) (E : Array Entry) (xs : List Step) :
    Except String (List String × Array Entry × List Decl) := do
  let names' := names ++ xs.map (·.1)
  let ix (name : String) : ℕ := (names'.findIdx? (· == name)).getD 0
  let (E', ds) ← xs.foldlM (fun (acc : Array Entry × List Decl) (x : Step) ↦ match x.2 ix acc.1 with
    | some (a, d) => Except.ok (acc.1.push (Entry.language a), acc.2 ++ [Decl.language a d])
    | none => Except.error s!"the lemma {x.1} is not proved") (E, [])
  pure (names', E', ds)

/-- A term under one binder that does not use the binder's variable, outside it. -/
def lower1 (t : Term) : Term := Term.subst t fun i ↦ v (i - 1)

/-- The parts of a stability formula, its function of the fuel, its threshold and its value,
outside its binder; the connectives' definitions from {lit}`o` and addition the definition of
index {lit}`kAdd`. -/
def stabParts (o kAdd : ℕ) (ψ : Term) : Option (Term × Term × Term) := do
  let (i, _, cs) ← defnParts ψ
  if i ≠ o + 3 then none else
  let [P] := cs | none
  let .lam _ := P.label | none
  let [b] := P.children | none
  let (l, r) ← Internal.eqParts b
  let .app := l.label | none
  let [F, a] := l.children | none
  let (ka, _, as) ← defnParts a
  if ka ≠ kAdd then none else
  -- the addition's arguments, the last first
  let [_, n] := as | none
  let .app := r.label | none
  let [_, w] := r.children | none
  pure (lower1 F, lower1 n, lower1 w)

/-- Whether a term is a construction of a list or a bit, or of a coproduct: a primitive arrow among
the empty list, construction and the injections. -/
def isCtor (t : Term) : Bool := match t.label with
  | .arr k _ => k = 0 ∨ k = 1 ∨ k = 3 ∨ k = 4
  | _ => false

/-- Whether a term is the construction of a tree. -/
def isCtorTree (t : Term) : Bool := match t.label with
  | .arr k _ => k = 2
  | _ => false

/-- Whether a term is a variable. -/
def isVar (t : Term) : Bool := match t.label with
  | .var _ => true
  | _ => false

/-- The data a term's weak head normal form is blocked on, along its head, the outermost first:
the datum of a fold or of a case analysis at the head, and the data that datum is blocked on. -/
def blocking : Term → List Term := RoseTree.para fun l cs ↦
  match l, cs with
  | .listRec, [_, _, (d, rd)] => if isCtor d then [] else d :: rd
  | .roseRec _, [_, (d, rd)] => if isCtorTree d then [] else d :: rd
  | .natRec, [_, _, (_, rd)] => rd
  | .app, [(f, rf), (x, rx)] => match f.label with
    | .arr 5 _ => if isCtor x then rf else x :: rx
    | _ => rf
  | .fst, [(_, r)] | .snd, [(_, r)] => r
  | _, _ => []

/-! The deduction kit. -/

/-- The context of the deductions: the extended program, its definitions, the entries proved and
the index of each named one. -/
structure Kit where
  /-- The extended program. -/
  P : Prog
  /-- The statement's definitions. -/
  S : Defs
  /-- The entries proved. -/
  E : Array Entry
  /-- The index of a named entry. -/
  ix : String → ℕ
  /-- The names of further equations used as rules. -/
  more : List String

namespace Kit

variable (K : Kit)

/-- The constants. -/
def G : Internal.Globals := K.P.G

/-- The connectives. -/
def L : Conn := ⟨K.P.o, logicBase⟩

/-- The rules: the equations among the hypotheses, addition's, the further equations, the
vocabulary's, every element of a list satisfying a predicate unfolded, and the tail's rebuilding of
lists of formulas. -/
def rules (Φ : List Term) : List NormRule :=
  eqHyps Φ ++ addLemmaRules K.ix ++ K.more.map (fun nm ↦ .thm (K.ix nm) []) ++ vRules K.P K.ix ++
    [.delta (K.S.q + 5), .thm (K.ix "rebTail") [omega]]

/-- The rules but the hypothesis of index i. -/
def rulesEx (Φ : List Term) (i : ℕ) : List NormRule :=
  (K.rules Φ).filter fun r ↦ match r with
    | .hyp j => j ≠ i
    | _ => true

/-- The goal normalized. -/
def norm (k : Deducer) : Deducer := fun Γ Φ ψ ↦ dRwBy (evalRw K.G K.E (K.rules Φ) .full) k Γ Φ ψ

/-- An equation by normalization. -/
def byNorm : Deducer := fun Γ Φ ψ ↦ dEq (byMode .full K.G K.E 0 (K.rules Φ)) Γ Φ ψ

/-- A hypothesis normalized, then the goal normalized and found among the hypotheses. -/
def byHyp (h : ℕ) : Deducer := fun Γ Φ ψ ↦
  (dRwHyp (evalRw K.G K.E (K.rulesEx Φ h) .full) h (K.norm dHyp) Γ Φ ψ).orElse fun _ ↦
    let nf (t : Term) : Option Term := (evalRw K.G K.E (K.rulesEx Φ h) .full Γ Φ t).map Prod.fst
    let d := ((Φ[h]?).bind nf).bind fun a ↦ (nf ψ).bind fun b ↦ firstDiff a b
    dbgTrace s!"byHyp {h}: {d.map fun (a, b) ↦
      s!"{showT a}\n  vs {showT b}"}" fun _ ↦ none

/-- A hypothesis normalized to falsity, refuting the goal. -/
def hypFalse (h : ℕ) : Deducer := fun Γ Φ ψ ↦
  dRwHyp (evalRw K.G K.E (K.rulesEx Φ h) .full) h (dFalse K.L dHyp) Γ Φ ψ

/-- The hypothesis of index h refuted, else k. -/
def orFalse (h : ℕ) (k : Deducer) : Deducer := fun Γ Φ ψ ↦
  (K.hypFalse h Γ Φ ψ).orElse fun _ ↦ k Γ Φ ψ

/-- Truth, conjunctions and equations, after normalization, to a depth. -/
def solve (d : ℕ) : Deducer := d.rec (fun _ _ _ ↦ none) fun _ rec ↦ K.norm fun Γ Φ ψ ↦
  if ψ == Internal.Logic.tt K.P.o then some Internal.Logic.trueI else
  match defnParts ψ with
  | some (i, _, _) => if i = K.P.o + 1 then dConjI K.L rec rec Γ Φ ψ else none
  | none => K.byNorm Γ Φ ψ

/-- The last hypothesis, a universal quantification, at a term of the context. -/
def allEΓ (t : List Tree → Term) (k : Deducer) : Deducer := fun Γ Φ ψ ↦
  dAllE K.L K.G K.E (Φ.length - 1) (t Γ) k Γ Φ ψ

/-- The last hypothesis, an implication, eliminated. -/
def impE (kp k : Deducer) : Deducer := fun Γ Φ ψ ↦ dImpE K.L (Φ.length - 1) kp k Γ Φ ψ

/-- The last hypothesis, a convergence, unfolded. -/
def unfoldConv (k : Deducer) : Deducer := fun Γ Φ ψ ↦
  dRwHyp (evalRw K.G K.E [.delta (K.S.q + 2)] .head) (Φ.length - 1) k Γ Φ ψ

/-- The last hypothesis, an existential quantification, eliminated. -/
def exE (k : Deducer) : Deducer := fun Γ Φ ψ ↦ dExE K.L K.G K.E (Φ.length - 1) k Γ Φ ψ

/-- The last hypothesis, a conjunction, eliminated. -/
def conjE (k : Deducer) : Deducer := fun Γ Φ ψ ↦ dConjE K.L (Φ.length - 1) k Γ Φ ψ

/-- A tree term a node of new variables, its label and its children. -/
def treeNode (X : Term) (k : Deducer) : Deducer := fun Γ Φ ψ ↦ do
  let some (Entry.language c) := K.E[K.ix "treeNode"]? | none
  dCut (Internal.instTerm [] [X] c.concl) (nd (.apply (K.ix "treeNode") [] [X]))
    (K.exE (K.exE k)) Γ Φ ψ

/-- The case analysis of a list term of elements of a type. -/
def listCase (a : Tree) (X : Term) (k₀ k₁ : Deducer) : Deducer :=
  dListCase K.L K.G K.E (K.ix "listCases") a X k₀ k₁

/-- The case analysis of a bit term. -/
def bitCase (X : Term) (k₀ k₁ : Deducer) : Deducer := dBitCase K.L (K.ix "bitCases") X k₀ k₁

/-- A hypothesis decided by case analysis of the bits its weak head normal form is blocked on,
to a depth, each case refuted where it reduces to falsity, else proved by k. -/
def splitHyp (h : ℕ) (k : Deducer) (depth : ℕ := 6) : Deducer := (Nat.rec
  (motive := fun _ ↦ Deducer) (fun Γ Φ ψ ↦ (K.hypFalse h Γ Φ ψ).orElse fun _ ↦ k Γ Φ ψ)
  (fun _ rec Γ Φ ψ ↦ (K.hypFalse h Γ Φ ψ).orElse fun _ ↦ do
    let (t, _) ← evalRw K.G K.E (K.rulesEx Φ h) .head Γ Φ (← Φ[h]?)
    let some X := (blocking t).reverse.find? fun X ↦
        let ty := Internal.typeIn K.G 0 Γ X
        ty = some bitsTy ∨ ty = some bitTy
      | k Γ Φ ψ
    if Internal.typeIn K.G 0 Γ X = some bitTy then K.bitCase X rec rec Γ Φ ψ
    else K.listCase bitTy X rec rec Γ Φ ψ) depth)

/-- From the hypothesis h, an equation of two terms, the equation of their images by f, each
normalized, cut in after the hypotheses. -/
def image (h : ℕ) (f : Term → Term) (k : Deducer) : Deducer := fun Γ Φ ψ ↦ do
  let (L, R) ← Internal.eqParts (← Φ[h]?)
  let (A', dA, _) ← Internal.eval K.G K.E 0 (K.rulesEx Φ h) 4096 .full Γ Φ (f L)
  let (B', dB, _) ← Internal.eval K.G K.E 0 (K.rulesEx Φ h) 4096 .full Γ Φ (f R)
  let (_, dAh, _) ← Internal.eval K.G K.E 0 [.hyp h] 4096 .weak Γ Φ (f L)
  pure (nd (.cut (Term.eq A' B')) [nd (.convFrom (Term.eq (f L) (f R)))
    [nd .cong [dA, dB], nd .join [dAh, nd .refl]], ← k Γ (Φ ++ [Term.eq A' B']) ψ])

/-- A formula equal to truth, the last hypothesis, cut in itself. -/
def trueOf (_ : Kit) (k : Deducer) : Deducer := fun Γ Φ ψ ↦ do
  let (A', _) ← Internal.eqParts (← Φ[Φ.length - 1]?)
  pure (nd (.cut A') [nd .conv [nd (.rwHyp (Φ.length - 1) false),
    nd .join [nd .refl, nd .refl]], ← k Γ (Φ ++ [A']) ψ])

/-- The instance of the named theorem at terms of the context, cut in after the hypotheses. -/
def cutThm (name : String) (σ : List Tree → List Term) (k : Deducer) : Deducer :=
  fun Γ Φ ψ ↦ do
    let some (Entry.language b) := K.E[K.ix name]? | none
    dCut (Internal.instTerm [] (σ Γ) b.concl) (nd (.apply (K.ix name) [] (σ Γ))) k Γ Φ ψ

/-- The truth of a bitstring test: its not being empty. -/
def truthB (t : Term) : Term :=
  condT omega t (Internal.Logic.tt K.P.o) (Internal.Logic.ff K.P.o)

/-- The formula of the equality's soundness at a tree, the innermost variable. -/
def eqφ : Term := Internal.Logic.all K.P.o treeTy (Term.lam treeTy
  (Internal.Logic.imp K.P.o (K.truthB (call D.equal [] [v 1, v 0])) (Term.eq (v 1) (v 0))))

end Kit

/-- The fold of the equality of trees: its type and its step. -/
def eqFold : Option (Tree × Term) := do
  let d ← lib[D.equal]?
  let [f, _] := d.body.children | none
  let .roseRec c := f.label | none
  let [s, _] := f.children | none
  pure (c, s)

/-- The elements' folds of the equality, as its step receives them. -/
def mapEq (cs : Term) : Option Term := do
  let (cE, sE) ← eqFold
  pure (Term.listRec (nilT cE) (consT cE (Term.roseRec cE sE (v 1)) (v 0)) cs)

/-- The soundness of the equality of trees: the equality of bitstrings, by induction on the
second; the elementwise equality of lists of trees given each element's soundness, by induction
on the first; the induction hypothesis on rose trees as the soundness of every child, by
induction on the children; and the equality of trees, by induction on the first, the second a
node, its label's and its children's tests decided. -/
def equalLemmas (P : Prog) (S : Defs) : List Step :=
  let kit (ix : String → ℕ) (E : Array Entry) : Kit := ⟨P, S, E, ix, []⟩
  [("eqBSound", fun ix E ↦ do
      let K := kit ix E
      let L := K.L
      -- context: the second; under the quantifier, the first
      let φ := Internal.Logic.all P.o bitsTy (Term.lam bitsTy (Internal.Logic.imp P.o
        (K.truthB (call D.eqB [] [v 0, v 1])) (Term.eq (v 0) (v 1))))
      let lc (X : List Tree → Term) (k₀ k₁ : Deducer) : Deducer := fun Γ Φ ψ ↦
        K.listCase bitTy (X Γ) k₀ k₁ Γ Φ ψ
      let bc (X : List Tree → Term) (k₀ k₁ : Deducer) : Deducer := fun Γ Φ ψ ↦
        K.bitCase (X Γ) k₀ k₁ Γ Φ ψ
      -- the empty second: the first empty, or a construction, refuted
      let d₀ ← dAllI L (dImpI L fun Γ₁ Φ₁ ψ₁ ↦
        lc (fun Γ ↦ v (Γ.length - Γ₁.length)) K.byNorm (K.hypFalse (Φ₁.length - 1)) Γ₁ Φ₁ ψ₁)
        [] [] (Term.subst φ (Internal.instVar (Term.arr 0 [bitTy] Term.star)))
      -- a construction: the first empty, refuted; or a construction, its bits split, unequal
      -- bits refuted, equal ones by the induction hypothesis at the rests
      let cons : Deducer := dAllI L (dImpI L fun Γ₁ Φ₁ ψ₁ ↦
        let h := Φ₁.length - 1
        -- context past Γ₁: the first's rest, its bit; the second's bit is the outermost
        let same : Deducer := fun Γ Φ ψ ↦
          dAllE L K.G K.E 0 (v (Γ.length - Γ₁.length - 2)) (fun Γ Φ ψ ↦
            dImpE L (Φ.length - 1) (K.byHyp h) K.byNorm Γ Φ ψ) Γ Φ ψ
        lc (fun Γ ↦ v (Γ.length - Γ₁.length)) (K.hypFalse h)
          (bc (fun Γ ↦ v (Γ.length - Γ₁.length - 1))
            (bc (fun Γ ↦ v (Γ.length - 1)) (K.orFalse h same) (K.orFalse h same))
            (bc (fun Γ ↦ v (Γ.length - 1)) (K.orFalse h same) (K.orFalse h same)))
          Γ₁ Φ₁ ψ₁)
      let d₁ ← cons [list bitTy, bitTy] [Internal.weakenElem φ] (Internal.listConsAt 1 bitTy φ)
      pure (⟨0, [bitsTy], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁])),
    ("allZipSound", fun ix E ↦ do
      let K := kit ix E
      let L := K.L
      let imp := Internal.Logic.imp P.o
      let all := Internal.Logic.all P.o
      -- the predicate of an element's soundness: equal to every tree it tests equal to
      let Pr : Term := Term.lam treeTy K.eqφ
      let φ := all (list treeTy) (Term.lam (list treeTy) (imp (S.allL Pr (v 1))
        (imp (K.truthB (call D.allZip [] [← mapEq (v 1), v 0])) (Term.eq (v 1) (v 0)))))
      let lc (X : List Tree → Term) (k₀ k₁ : Deducer) : Deducer := fun Γ Φ ψ ↦
        K.listCase treeTy (X Γ) k₀ k₁ Γ Φ ψ
      -- the empty first: the second empty, or a construction, refuted
      let d₀ ← dAllI L (dImpI L (dImpI L fun Γ₁ Φ₁ ψ₁ ↦
        lc (fun Γ ↦ v (Γ.length - Γ₁.length)) K.byNorm (K.hypFalse (Φ₁.length - 1))
          Γ₁ Φ₁ ψ₁)) [] [] (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
      -- a construction: the second empty, refuted; or a construction, the heads' equality by
      -- the first head's soundness, the rests' by the induction hypothesis
      let cons : Deducer := dAllI L (dImpI L (dImpI L fun Γ₁ Φ₁ ψ₁ ↦
        let hA := Φ₁.length - 2
        let hZ := Φ₁.length - 1
        -- context past Γ₁: the second's rest, its head
        let rest' (Γ : List Tree) : Term := v (Γ.length - Γ₁.length - 2)
        let head' (Γ : List Tree) : Term := v (Γ.length - Γ₁.length - 1)
        let both : Deducer := fun Γ Φ ψ ↦
          -- the first's soundness and its rest's, from the hypothesis on all the elements
          -- the rests equal by the induction hypothesis, then the heads by the first head's
          -- soundness, the last hypothesis
          let inst (q : ℕ) : Deducer := fun Γ Φ ψ ↦
            let pc := Φ.length - 1
            dAllE L K.G K.E 0 (rest' Γ) (K.impE (K.byHyp q) (K.impE (K.byHyp hZ)
              (fun Γ Φ ψ ↦ dAllE L K.G K.E pc (head' Γ) (K.impE (K.solve 2) K.byNorm) Γ Φ ψ)))
              Γ Φ ψ
          dRwHyp (evalRw K.G K.E (K.rules Φ) .head) hA (K.conjE fun Γ Φ ψ ↦
            dRwHyp (evalRw K.G K.E [.rule .beta] .head) (Φ.length - 2) (inst (Φ.length - 1))
              Γ Φ ψ) Γ Φ ψ
        -- the heads' equality decided: unequal refuted
        let heads : Deducer := fun Γ Φ ψ ↦
          K.listCase bitTy (call D.equal [] [v (Γ.length - 1), head' Γ]) (K.hypFalse hZ) both
            Γ Φ ψ
        lc (fun Γ ↦ v (Γ.length - Γ₁.length)) (K.hypFalse hZ) heads
          Γ₁ Φ₁ ψ₁))
      let d₁ ← cons [list treeTy, treeTy] [Internal.weakenElem φ]
        (Internal.listConsAt 1 treeTy φ)
      pure (⟨0, [list treeTy], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁])),
    ("roseAll", fun ix E ↦ do
      let K := kit ix E
      let L := K.L
      let φ := Internal.Logic.imp P.o (Internal.roseHyp 0 1 K.eqφ)
        (S.allL (Term.lam treeTy K.eqφ) (v 0))
      let d₀ ← dImpI L (K.solve 3) [] [] (Term.subst φ (Internal.instVar
        (Term.arr 0 [treeTy] Term.star)))
      -- a construction: the head's formula and the rests' equation, from the hypothesis's;
      -- hypotheses: the induction hypothesis, the construction's, the heads' equation, the
      -- head's formula, the rests' equation; then the rest's soundness
      let cons : Deducer := dImpI L fun Γ₁ Φ₁ ψ₁ ↦
        let h := Φ₁.length - 1
        let tl : Deducer := fun Γ Φ ψ ↦
          dImpE L 0 K.byNorm (K.norm (dConjI L (K.byHyp 3) (K.byHyp 5))) Γ Φ ψ
        K.image h (fun t ↦ call D.headD [omega] [Term.eq Term.star Term.star, t])
          (K.trueOf (K.image h (fun t ↦ call D.tail [omega] [t]) tl)) Γ₁ Φ₁ ψ₁
      let d₁ ← cons [list treeTy, treeTy] [Internal.weakenElem φ]
        (Internal.listConsAt 1 treeTy φ)
      pure (⟨0, [list treeTy], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁])),
    ("equalSound", fun ix E ↦ do
      let K := kit ix E
      let L := K.L
      let withLast (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
      let node : Deducer := dAllI L (dImpI L fun Γ₁ Φ₁ ψ₁ ↦
        -- context: the second tree, the children, the label; then its label and children
        let h := Φ₁.length - 1
        let l (Γ : List Tree) : Term := v (Γ.length - 1)
        let cs (Γ : List Tree) : Term := v (Γ.length - 2)
        K.treeNode (v 0) (fun Γ₂ Φ₂ ψ₂ ↦
          let l' (Γ : List Tree) : Term := v (Γ.length - Γ₂.length + 1)
          let cs' (Γ : List Tree) : Term := v (Γ.length - Γ₂.length)
          -- the two tests, of the labels and of the children, each empty refuted
          let X := (nfE K.G K.E (vRules P ix) Γ₂ (call D.eqB [] [l Γ₂, l' Γ₂])).getD Term.star
          let Y := ((mapEq (cs Γ₂)).bind fun me ↦
            nfE K.G K.E (vRules P ix) Γ₂ (call D.allZip [] [me, cs' Γ₂])).getD Term.star
          -- the labels equal, the children's soundness, the children equal
          let eqs : Deducer :=
            K.cutThm "eqBSound" (fun Γ ↦ [l' Γ]) (K.allEΓ l (K.impE (K.solve 2)
              (K.cutThm "roseAll" (fun Γ ↦ [cs Γ]) (K.impE dHyp (withLast fun all ↦
                K.cutThm "allZipSound" (fun Γ ↦ [cs Γ]) (K.allEΓ cs'
                  (K.impE (fun _ _ _ ↦ some (nd (.hyp all))) (K.impE (K.solve 2) K.byNorm))))))))
          let lc (T : Term) (k : Deducer) : Deducer := K.listCase bitTy T (K.hypFalse h) k
          -- the second test, in the first's case, weakened past its two variables
          lc X (lc (Internal.weaken1 (Internal.weaken1 Y)) eqs) Γ₂ Φ₂ ψ₂) Γ₁ Φ₁ ψ₁)
      let d ← node [list treeTy, bitsTy] [Internal.roseHyp 0 1 K.eqφ]
        (Internal.roseNodeAt 2 treeTy bitsTy K.eqφ)
      pure (⟨0, [treeTy], [], K.eqφ⟩, nd (.roseIndHyp 2 0 1) [d]))]

/-- The inversion of a type test, named: a tree the test of the label {lit}`lbl` and the arity
{lit}`n` holds of is a node of that label over n new trees, by its children split to n, each
other number refuted once the label is decided. -/
def typeInv (P : Prog) (S : Defs) (name test : String) (lbl n : ℕ) : Step :=
  (name, fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let L := K.L
    let ex := Internal.Logic.ex P.o
    let ls (ts : List Term) : Term := ts.foldr (consT treeTy) (nilT treeTy)
    let concl : Term := (List.range n).foldr (fun _ b ↦ ex treeTy (Term.lam treeTy b))
      (Term.eq (v n) (nodeT (Term.pair (numeral lbl) (ls ((List.range n).reverse.map v)))))
    let φ := Internal.Logic.imp P.o (truth P.o (pc P test [v 0])) concl
    -- the children split to n, each other number refuted; at n, the label decided and the
    -- children's heads the witnesses, the first outermost
    let kids (h : ℕ) (Γ₁ : List Tree) : Deducer :=
      let leaf : Deducer := K.splitHyp h (fun Γ Φ ψ ↦
        let d := Γ.length - Γ₁.length
        ((List.range n).map fun p ↦ v (d - 2 * p - 1)).foldr (fun w k ↦ dExI L K.G K.E w k)
          K.byNorm Γ Φ ψ) 8
      let no : Deducer := K.splitHyp h (fun _ _ _ ↦ none) 8
      let go : ℕ → Deducer := fun m ↦ m.rec
        (fun Γ Φ ψ ↦ K.listCase treeTy (v 0) leaf no Γ Φ ψ)
        fun _ rec Γ Φ ψ ↦ K.listCase treeTy (v 0) no rec Γ Φ ψ
      fun Γ Φ ψ ↦ match n with
        | 0 => K.listCase treeTy (v 0) leaf no Γ Φ ψ
        | m + 1 => K.listCase treeTy (v 0) no (go m) Γ Φ ψ
    let d ← dImpI L (fun Γ₁ Φ₁ ψ₁ ↦
      K.treeNode (v 0) (fun Γ Φ ψ ↦ kids (Φ₁.length - 1) Γ Γ Φ ψ) Γ₁ Φ₁ ψ₁) [treeTy] [] φ
    pure (⟨0, [treeTy], [], φ⟩, d))

/-- The program, translated and extended, from its definitions with their names, as the front end
reads them, and the index of each named definition. -/
def extendedOf (ds : List (List Char × Tree)) (idx : String → ℕ) : Option (Prog × Defs) := do
  extend (← prog? ds idx)

/-- The base development: the weakening proof's, and the lemmas on addition, stability, cases,
rebuildings, numerals and the vocabulary. -/
def baseDev (P : Prog) (S : Defs) : Option (List Step) := do
  pure ((← Weakening.development P) ++ natLemmas P S ++ stabLemmas P S ++ caseLemmas P ++
    rebLemmas P ++ eqnLemmas P ++ vLemmas P S ++ equalLemmas P S ++
    [typeInv P S "isArrowInv" "Check.isArrow" Kernel.Label.tyArrow 2,
      typeInv P S "isProdInv" "Check.isProd" Kernel.Label.tyProd 2,
      typeInv P S "isListInv" "Check.isListTy" Kernel.Label.tyList 1])

/-- The extended program, from the program's definitions as the front end reads them. -/
def extended : Option (Prog × Defs) := do
  let ds ← bundled Geb.Kernel.Stage0Tests.bundler.toList programText.toList
  extendedOf ds fun name ↦ (defIndex ds name.toList).getD 0

end GebTests.Prototypes.FreeTopos.Normalization

end
