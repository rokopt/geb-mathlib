/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.DatatypeCaseSound
public meta import GebTests.Prototypes.FreeTopos.DatatypeCaseSound -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The recognizers of datatypes

The recognizer the expansion of the datatype language writes for a datatype decides membership in
it: the S-expressions {lit}`Recognize.recognizer` writes, read by the reader, evaluate to a
function deciding {lit}`Typing.memberOf`. An expression denotes a value where its reading, its
numeral abbreviations expanded, is a term converging to that value ({lit}`denT`), and the
development proceeds by what each of the writer's forms denotes.

## Main definitions

* {lit}`denT` — that an S-expression denotes a value.
* {lit}`denCertificates` — what the writer's forms denote, stored as the certificate
  {lit}`datatype-den`.
* {lit}`walkCertificates` — the walk of a constructor's fields, stored as the certificate
  {lit}`datatype-walk`.
* {lit}`recognizerCertificates` — the decisions of a recognizer's tests, stored as the certificate
  {lit}`datatype-recognizer`.
* {lit}`recognizerFoldCertificates` — a recognizer's fold and abstraction, stored as the certificate
  {lit}`datatype-recognizer-fold`.

## Main statements

* {lit}`recognizerDen` — a marker's recognizer as the writer gives it denotes a function which at
  the quotation of every tree converges to the quotation of a bit true exactly where the tree is a
  member.

## References

* {cite}`Tait1967`, for the logical relation the recognizers' decisions serve.

## Tags

internal language, datatypes, recognizer, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Datatypes

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Translation Geb.FreeTopos.Tactics
open GebTests.Prototypes.FreeTopos.Weakening
open scoped FinEnum

open Internal (Term)
open GebTests.Prototypes.FreeTopos.Normalization

/-- That the S-expression {lit}`e` denotes the value {lit}`w` in the environment {lit}`env`: its
numeral abbreviations expanded, the reader resolves it in the scope {lit}`scope` to some term,
which converges to the value at the definitions of the relation's context {lit}`D`. -/
def denT (P : Prog) (S : Defs) (D tys names nums scope env e w : Term) : Term :=
  Internal.Logic.ex P.o treeTy (Term.lam treeTy (Internal.Logic.conj P.o
    (Term.eq (pc P "Reader.resolve" [sh 1 tys, sh 1 names, pc P "Reader.expandNums" [sh 1 nums,
      sh 1 e], sh 1 scope]) (pc P "Prelude.some" [v 0]))
    (S.conv (Term.lam nat (S.evN (Term.fst (sh 2 D)) (v 0) (sh 2 env) (v 1)))
      (Term.lam treeTy (Term.eq (v 0) (sh 2 w))))))

/-- The tests that an atom's name is neither in a scope nor among the definitions' names, by which
the reader resolves it past them. -/
def absentTests (P : Prog) (a scope names : Term) : List Term :=
  [pc P "Prelude.isSome" [pc P "Reader.indexOf" [atomNameT a, scope]],
    pc P "Prelude.isSome" [pc P "Reader.indexOf" [atomNameT a, names]]]

/-- The kit of the writer's forms: the walk's rules and the primitives' evaluation, a numeral's
digits kept folded. -/
def denKit (P : Prog) (S : Defs) (ix : String → ℕ) (E : Array Internal.Entry) : Kit :=
  ⟨{ walkProg P with folded := (walkProg P).folded ++ ["Typing.decimalChars"] }, S, E, ix,
    walkMore ix E ++ evalPrims.filter fun nm ↦ 0 < ix nm ∧ ix nm < E.size⟩

/-- A hypothesis that an expression denotes a value ({name}`denT`) opened: the term of index 0 in
the continuation's arguments' order, the resolution normalized, the threshold and the value, the
value's equation normalized; the continuation is given the positions of the term, the threshold
and the value, and the indices of the resolution and of the stability. -/
def denE (K : Kit) (h : ℕ) (k : ℕ → ℕ → ℕ → ℕ → Deducer) : Deducer :=
  dExE K.L K.G K.E h <| K.conjE fun Γ₁ Φ₁ ψ₁ ↦
    let (res, cv, pt) := (Φ₁.length - 2, Φ₁.length - 1, Γ₁.length - 1)
    dRwHyp (evalRw K.G K.E [.delta (K.S.q + 2)] .head) cv (K.exE <| K.exE <| K.conjE
      fun Γ₂ Φ₂ ψ₂ ↦
      normLastK K (fun Γ₃ Φ₃ ψ₃ ↦
        dRwHyp (evalRw K.G K.E (K.rulesEx Φ₃ res) .full) res
          (k pt (Γ₂.length - 2) (Γ₂.length - 1) (Φ₂.length - 2)) Γ₃ Φ₃ ψ₃) Γ₂ Φ₂ ψ₂) Γ₁ Φ₁ ψ₁

/-- A subexpression of one of the writer's forms: the value it denotes, in the form's scope and
environment or others, evaluated at the form's level or a number of levels above the
subexpressions' thresholds. -/
structure DenSub where
  /-- The subexpression. -/
  e : Term
  /-- The value it denotes. -/
  w : Term
  /-- Its scope, where not the form's. -/
  scope : Option Term := none
  /-- Its environment, where not the form's. -/
  env : Option Term := none
  /-- The levels above the thresholds at which it evaluates, where not the form's. -/
  lift : Option ℕ := none

/-- A subexpression in the form's scope and environment, evaluated at the form's level. -/
def sub (e w : Term) : DenSub := { e, w }

/-- A rule of what one of the writer's forms denotes, in a context of the rule's own variables
around the relation's context, the numeral abbreviations, the definitions' names, the type
abbreviations, the scope and the environment, at positions 0 to 5. -/
structure DenRule where
  /-- The rule's name. -/
  name : String
  /-- The types of the rule's variables, the innermost first. -/
  vars : List Tree := []
  /-- The atoms the reader resolves past the scope and the definitions' names. -/
  absent : List Term := []
  /-- The atoms no numeral abbreviation abbreviates. -/
  plain : List Term := []
  /-- The rule's further hypotheses. -/
  more : List Term := []
  /-- The form's subexpressions, each with the value it denotes. -/
  subs : List DenSub := []
  /-- The form. -/
  form : Term
  /-- The value the form denotes. -/
  value : Term
  /-- The levels above the subexpressions' thresholds at which the form evaluates. -/
  levels : ℕ
  /-- The tree whose label's case analysis the evaluation is blocked on. -/
  split : Option Term := none
  /-- The further equations of the evaluation. -/
  rules : List String := []
  /-- Whether a numeral's value is given by a hypothesis rather than computed from its digits. -/
  numeralGiven : Bool := false
  /-- Further hypotheses of convergence, after the subexpressions, each with the levels above the
  thresholds at which it applies. -/
  convs : List (Term × ℕ) := []
  /-- The proof of the evaluation's equation at the sum of the thresholds, where not by
  normalization, given the kit and the sum. -/
  finish : Option (Kit → (List Tree → Term) → Deducer) := none
  /-- A step before the form's subexpressions are opened, given the kit and the shift of a term of
  the rule's context. -/
  pre : Kit → (Term → List Tree → Term) → Deducer → Deducer := fun _ _ k ↦ k

/-- The context of a rule of what a form denotes. -/
def denCtx (vars : List Tree) : List Tree :=
  vars ++ [list treeTy, list treeTy, list treeTy, list treeTy, list treeTy, Defs3.ctxTy]

/-- The variable at a position of the context of a rule's variables: the rule's own after the
fixed ones. -/
def denAt (vars : List Tree) (i : ℕ) : Term := atPos i (denCtx vars)

/-- That an expression denotes a value, in the context of a rule's variables. -/
def denIn (P : Prog) (S : Defs) (vars : List Tree) (e w : Term) (scope env : Option Term := none) :
    Term :=
  let at_ := denAt vars
  denT P S (at_ 0) (at_ 3) (at_ 2) (at_ 1) (scope.getD (at_ 4)) (env.getD (at_ 5)) e w

/-- The statement of a rule of what a form denotes. -/
def denThm (P : Prog) (S : Defs) (r : DenRule) : Internal.Thm :=
  let at_ := denAt r.vars
  let tests := r.absent.flatMap (absentTests P · (at_ 4) (at_ 2)) ++
    r.plain.map fun a ↦ pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev" [atomNameT a, at_ 1]]
  ⟨0, denCtx r.vars, tests.map (notTest P.o) ++ r.more ++
      r.subs.map (fun c ↦ denIn P S r.vars c.e c.w c.scope c.env) ++ r.convs.map (·.1),
    denIn P S r.vars r.form r.value⟩

/-- The hypotheses that the subexpressions denote their values opened in turn, the thresholds'
positions and the stabilities' indices, the first first, given to the continuation. -/
def denOpen (K : Kit) (hs : List ℕ) : (List (ℕ × ℕ) → Deducer) → Deducer :=
  hs.foldr (fun h acc k ↦ denE K h fun _ n _ s ↦ acc fun rs ↦ k ((n, s) :: rs)) fun k ↦ k []

/-- A stability shifted on the right by the sum of the thresholds {lit}`rights` and on the left by
that of the thresholds {lit}`lefts`, where there are any; the index of the result is given to the
continuation. -/
def denShiftOne (K : Kit) (sum : List ℕ → List Tree → Term) (lefts rights : List ℕ) (s : ℕ)
    (k : ℕ → Deducer) : Deducer :=
  let onLeft (i : ℕ) : Deducer := if lefts.isEmpty then k i else
    shiftK K i true (sum lefts) fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
  if rights.isEmpty then onLeft s else
    shiftK K s false (sum rights) fun Γ Φ ψ ↦ onLeft (Φ.length - 1) Γ Φ ψ

/-- The stabilities of the subexpressions shifted to the sum of their thresholds, the final
stabilities' indices given to the continuation. -/
def denShift (K : Kit) (sum : List ℕ → List Tree → Term) (opened : List (ℕ × ℕ)) :
    (List ℕ → Deducer) → Deducer :=
  let ns := opened.map (·.1)
  opened.zipIdx.foldr (fun ((_, s), i) acc k ↦
    denShiftOne K sum (ns.take i) (ns.drop (i + 1)) s fun last ↦ acc fun ls ↦ k (last :: ls))
    fun k ↦ k []

/-- A rule of what a form denotes: the tests decided, true refuting their hypotheses; the
subexpressions' denotations opened and their stabilities shifted to the sum of their thresholds;
the term the form's resolution in normal form; its value at the given number of levels above the
sum, each subexpression evaluated at that level. -/
def denRule (P : Prog) (S : Defs) (T : Defs3) (r : DenRule) : Step :=
  (r.name, fun ix E ↦ do
    let K₀ := denKit P S ix E
    let K : Kit := { K₀ with more := K₀.more ++ r.rules }
    let P := K.P
    let L := K.L
    let thm := denThm P S r
    let Γ₀ := thm.ctx
    let up (t : Term) (Γ : List Tree) : Term := sh (Γ.length - Γ₀.length) t
    let at_ := denAt r.vars
    let tests := r.absent.flatMap (absentTests P · (at_ 4) (at_ 2)) ++
      r.plain.map fun a ↦ pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev" [atomNameT a, at_ 1]]
    let numeralIdx := P.idx "Reader.numeral"
    let unfold := ((resolveRules P T ix E).filter fun rule ↦ match rule with
      | .delta i => !(r.numeralGiven && i == numeralIdx)
      | _ => true) ++ [.delta (T.argIdx 3)]
    let resolved (Γ : List Tree) : Term := pc P "Reader.resolve"
      [atPos 3 Γ, atPos 2 Γ, pc P "Reader.expandNums" [atPos 1 Γ, up r.form Γ], atPos 4 Γ]
    let sum (ns : List ℕ) (Γ : List Tree) : Term :=
      match ns with
      | [] => zeroN
      | n :: ms => ms.foldl (fun acc m ↦ S.add acc (atPos m Γ)) (atPos n Γ)
    let liftBy (n : ℕ) (t : Term) : Term := (List.range n).foldr (fun _ t ↦ succN t) t
    let lift (t : Term) : Term := liftBy r.levels t
    let firstDen := tests.length + r.more.length
    let body (ns : List ℕ) (ss : List ℕ) : Deducer := fun Γ Φ ψ ↦ do
      let some (Y, _) := evalRw K.G K.E (K.rules Φ ++ unfold) .full Γ Φ
          (pc P "Prelude.get" [resolved Γ])
        | dbgTrace s!"{r.name}: no term" fun _ ↦ none
      let lifts := r.subs.map (fun c ↦ c.lift.getD r.levels) ++ r.convs.map (·.2)
      let stable : Deducer := (ss.zip lifts).foldr (fun (s, l) k ↦
          instNK K s (fun _ ↦ liftBy l (v 0)) k)
        (fun Γ Φ ψ ↦ linkK K s!"{r.name}: the equation" (match r.finish with
          | none => K.byNorm
          | some f => f K (sum ns)) Γ Φ ψ)
      dExI L K.G K.E Y (dConjI L
        (linkK K s!"{r.name}: the resolution" fun Γ Φ ψ ↦
          dEq (fun Γ Φ t u ↦ byMode .full K.G K.E 0 (K.rules Φ ++ unfold) Γ
            (rwHyps (K.rules Φ) Φ) t u) Γ Φ ψ)
        (dConv L K.G K.E S (lift (sum ns Γ)) (up r.value Γ)
          (linkK K s!"{r.name}: stable" stable)
          (linkK K s!"{r.name}: the value" (K.solve 3)))) Γ Φ ψ
    let convOpen (hs : List ℕ) : (List (ℕ × ℕ) → Deducer) → Deducer :=
      hs.foldr (fun h acc k ↦
        dRwHyp (evalRw K.G K.E [.delta (K.S.q + 2)] .head) h (K.exE <| K.exE <| K.conjE
          fun Γ Φ ψ ↦
          let (n, st) := (Γ.length - 2, Φ.length - 2)
          normLastK K (acc fun rs ↦ k ((n, st) :: rs)) Γ Φ ψ)) fun k ↦ k []
    let opened : Deducer :=
      denOpen K ((List.range r.subs.length).map (firstDen + ·)) fun opened₁ ↦
      convOpen ((List.range r.convs.length).map (firstDen + r.subs.length + ·)) fun opened₂ ↦
      let opened := opened₁ ++ opened₂
      denShift K sum opened fun ss ↦ body (opened.map (·.1)) ss
    -- the further hypotheses in normal form, in which their equations apply as rules
    let main : Deducer := (List.range r.more.length).foldr (fun i k Γ Φ ψ ↦
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ (tests.length + i)) .full) (tests.length + i) k Γ Φ ψ)
      (r.pre K up opened)
    let split : Deducer := match r.split with
      | none => main
      | some x => decideIn K (up x) main main
    let decisions : Deducer → Deducer := fun k ↦
      tests.zipIdx.foldr (fun (t, i) k ↦
        decideIn K (up t) k
          (linkK K s!"{r.name}: test {i} true" fun Γ Φ ψ ↦
            dImpE L i (K.solve 3) (fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ) Γ Φ ψ)) k
    let some d := decisions split thm.ctx thm.hyps thm.concl
      | dbgTrace s!"{r.name}: not proved" fun _ ↦ none
    pure (thm, d))

/-- The quotation of a tree. -/
def quoteV (P : Prog) (t : Term) : Term := pc P "Eval.valQuote" [t]

/-- The writer's application of a primitive of two arguments to two expressions denoting
quotations denotes the quotation of the primitive at their trees. -/
def denPrim2 (P : Prog) (nm : String) (a : Term) (k : ℕ) : DenRule :=
  let vars := [treeTy, treeTy, treeTy, treeTy]
  let at_ := denAt vars
  let (e₁, e₂, x, y) := (at_ 6, at_ 7, at_ 8, at_ 9)
  { name := s!"denPrim2/{nm}", vars, absent := [a], plain := [a],
    subs := [sub e₁ (quoteV P x), sub e₂ (quoteV P y)], form := pc P "Recognize.s3" [a, e₁, e₂],
    value := quoteV P (apps ((primT k).getD Term.star) [x, y]), levels := 2 }

/-- The writer's application of a primitive of one argument to an expression denoting a quotation
denotes the quotation of the primitive at its tree. -/
def denPrim1 (P : Prog) (nm : String) (a : Term) (k : ℕ) : DenRule :=
  let vars := [treeTy, treeTy]
  let at_ := denAt vars
  let (e, x) := (at_ 6, at_ 7)
  { name := s!"denPrim1/{nm}", vars, absent := [a], plain := [a], subs := [sub e (quoteV P x)],
    form := pc P "Recognize.s2" [a, e],
    value := quoteV P (apps ((primT k).getD Term.star) [x]), levels := 2 }

/-- The writer's numerals of zero and one denote their quotations. -/
def denDigit (P : Prog) (nm : String) (a : String) (n : ℕ) : DenRule :=
  { name := s!"denDigit/{nm}", plain := [pc P a []], form := pc P a [],
    value := quoteV P (leafT (numeral n)), levels := 1 }

/-- The writer's conditional of expressions denoting quotations denotes the quotation of the
branch the condition's label selects. -/
def denIf (P : Prog) : DenRule :=
  let vars := [treeTy, treeTy, treeTy, treeTy, treeTy, treeTy]
  let at_ := denAt vars
  let (c, a, b, x, y, z) := (at_ 6, at_ 7, at_ 8, at_ 9, at_ 10, at_ 11)
  let lab := call D.lab [] [x]
  { name := "denIf", vars, plain := [pc P "Recognize.rIf" []],
    subs := [sub c (quoteV P x), sub a (quoteV P y),
      sub b (quoteV P z)],
    form := pc P "Recognize.s4" [pc P "Recognize.rIf" [], c, a, b],
    value := quoteV P (condT treeTy lab y z), levels := 1, split := some x }

/-- An atom of the writer's denotes the value the environment holds at its index in the scope. -/
def denVar (P : Prog) (nm : String) (a : Term) : DenRule :=
  let vars := [treeTy, treeTy]
  let at_ := denAt vars
  let (i, w) := (at_ 6, at_ 7)
  { name := s!"denVar/{nm}", vars, plain := [a],
    more := [Term.eq (pc P "Reader.indexOf" [atomNameT a, at_ 4]) (pc P "Prelude.some" [i]),
      Term.eq (pc P "Prelude.nth" [at_ 5, leafT (call D.lab [] [i])]) (pc P "Prelude.some" [w])],
    form := a, value := w, levels := 1 }

/-- The writer's numeral denotes its quotation, where its digits read as it and are fixed by the
expansion of the numeral abbreviations. -/
def denNum (P : Prog) : DenRule :=
  let vars := [treeTy]
  let n := denAt vars 6
  let form := pc P "Recognize.num" [n]
  let chars := pc P "Typing.decimalChars" [n]
  let fn := Term.lam treeTy (pc P "Reader.expandNums" [sh 1 (denAt vars 1), v 0])
  { name := "denNum", vars, plain := [form],
    more := [Term.eq (pc P "Reader.numeral" [chars]) (pc P "Prelude.some" [n]),
      truth P.o (pc P "charsFixed" [fn, chars])],
    form, value := quoteV P n, levels := 1, numeralGiven := true,
    pre := fun K up k ↦ K.cutThm "charsFixedEq" (fun Γ ↦ [up chars Γ, atPos 1 Γ])
      (K.impE (K.byHyp 2) (normLastK K k)) }

/-- The writer's empty list of trees denotes the list value without elements. -/
def denNil (P : Prog) : DenRule :=
  { name := "denNil", plain := [pc P "Recognize.rNil" [], pc P "Recognize.rT" []],
    form := pc P "Recognize.s2" [pc P "Recognize.rNil" [], pc P "Recognize.rT" []],
    value := treeList P (nilT treeTy), levels := 1 }

/-- The writer's construction of a list denotes the list value of the head's value and the rest's
values. -/
def denCons (P : Prog) : DenRule :=
  let vars := [list treeTy, treeTy, treeTy, treeTy]
  let at_ := denAt vars
  let (e, l, x, xs) := (at_ 6, at_ 7, at_ 8, at_ 9)
  { name := "denCons", vars, plain := [pc P "Recognize.rCons" []],
    subs := [sub e x, sub l (treeList P xs)],
    form := pc P "Recognize.s3" [pc P "Recognize.rCons" [], e, l],
    value := treeList P (consT treeTy x xs), levels := 1 }

/-- An equation over a list of elements of a type, the variable of index 0, both sides in the normal
form of the writer's rules: by induction on the list, the induction hypothesis normalized. -/
def listEq (P : Prog) (S : Defs) (name : String) (A : Tree) (lhs rhs : Term) : Step :=
  (name, fun ix E ↦ do
    let K := denKit P S ix E
    let Γ := [list A]
    let l ← nfE K.G E (K.rules []) Γ lhs
    let r ← nfE K.G E (K.rules []) Γ rhs
    let φ := Term.eq l r
    let d₀ ← linkK K s!"{name}: empty" K.byNorm [] []
      (Term.subst φ (Internal.instVar (Term.arr 0 [A] Term.star)))
    let cons : Deducer := linkK K s!"{name}: construction" fun Γ Φ ψ ↦
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ 0) .full) 0 K.byNorm Γ Φ ψ
    let d₁ ← cons [list A, A] [Internal.weakenElem φ] (Internal.listConsAt 1 A φ)
    pure (⟨0, Γ, [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- A list value's elements are the list's values. -/
def listOfOf (P : Prog) (S : Defs) : Step :=
  listEq P S "listOfOf" treeTy (pc P "Eval.listOf" [treeList P (v 0)])
    (pc P "Prelude.some" [node0 (v 0)])

/-- The trees the quotations of a list of trees quote are the list's trees. -/
def unquotesOf (P : Prog) (S : Defs) : Step :=
  listEq P S "unquotesOf" treeTy (pc P "Eval.allSomeT"
      [pc P "Eval.mapT" [Term.lam treeTy (pc P "Eval.unquote" [v 0]), quotesT P (v 0)]])
    (pc P "Prelude.some" [node0 (v 0)])

/-- The writer's application of the node primitive to an expression denoting a quotation and to one
denoting the list value of quotations denotes the quotation of the node. -/
def denNode (P : Prog) : DenRule :=
  let vars := [list treeTy, treeTy, treeTy, treeTy]
  let at_ := denAt vars
  let (e, l, t, xs) := (at_ 6, at_ 7, at_ 8, at_ 9)
  let a := pc P "Recognize.rNode" []
  { name := "denNode", vars, absent := [a], plain := [a],
    subs := [sub e (quoteV P t), sub l (treeList P (quotesT P xs))],
    form := pc P "Recognize.s3" [a, e, l],
    value := quoteV P (nodeT (Term.pair (call D.lab [] [t]) xs)), levels := 2,
    rules := ["listOfOf", "unquotesOf"] }

/-- The writer's binding of an atom to the value of an expression, around a body denoting a value
in the scope and the environment it extends, denotes that value. -/
def denLet (P : Prog) (nm : String) (x : Term) : DenRule :=
  let vars := [treeTy, treeTy, treeTy, treeTy]
  let at_ := denAt vars
  let (e, b, w, r) := (at_ 6, at_ 7, at_ 8, at_ 9)
  let (rLet, rT) := (pc P "Recognize.rLet" [], pc P "Recognize.rT" [])
  { name := s!"denLet/{nm}", vars, plain := [rLet, rT, x],
    subs := [sub e w, ⟨b, r, some (consT treeTy (atomNameT x) (at_ 4)),
      some (consT treeTy w (at_ 5)), some 0⟩],
    form := pc P "Recognize.sx" [consT treeTy rLet (consT treeTy x (consT treeTy rT
      (consT treeTy e (consT treeTy b (nilT treeTy)))))],
    value := r, levels := 2 }

/-- The development of what the writer's forms denote: the list values' lemmas and a rule for each
form, at each primitive and at each atom the recognizers' terms bind. -/
def denDev (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  let atom (nm a : String) : DenRule := denVar P nm (pc P a [])
  [listOfOf P S, unquotesOf P S] ++
  ([denNode P, denLet P "n" (pc P "Recognize.vN" []), denNum P, denNil P, denCons P,
      denPrim2 P "child" (pc P "Recognize.rChild" []) Kernel.Prim.child,
      denPrim2 P "eq" (pc P "Recognize.rEq" []) Kernel.Prim.eq,
      denPrim2 P "lt" (pc P "Recognize.rLt" []) Kernel.Prim.lt,
      denPrim2 P "add" (pc P "Recognize.rAdd" []) Kernel.Prim.add,
      denPrim1 P "arity" (pc P "Recognize.rArity" []) Kernel.Prim.arity,
      denDigit P "zero" "Recognize.zero" 0, denDigit P "one" "Recognize.one" 1,
      denIf P, atom "n" "Recognize.vN", atom "l" "Recognize.vL", atom "r" "Recognize.vR",
      atom "c" "Recognize.vC", atom "a" "Recognize.vA", atom "t" "Recognize.vT"].map
    (denRule P S T))

/-- The development of {name}`denDev`, after the declarations of {name}`caseNames` and of the
walk's development ({name}`caseDev`), stored as the certificate {lit}`datatype-den`. -/
def denCertificates (P : Prog) (S : Defs) (T : Defs3) (before : List Internal.Thm) :
    Except String (List Stored.Cert) := do
  let some names := caseNames P S T | throw "the base is not stated"
  certifyAfter P (names ++ (caseDev P S T).map (·.1)) "datatype-den" (denDev P S T) before

/-- An expression denotes at most one value: the terms it resolves to are equal, by the two
resolutions' equations; both stabilities at the sum of the thresholds give the values' equation. In
the context of the values and the expression, around the fixed variables. -/
def denDet (P : Prog) (S : Defs) : Step :=
  ("denDet", fun ix E ↦ do
    let K := denKit P S ix E
    let vars := [treeTy, treeTy, treeTy]
    let at_ := denAt vars
    let (e, w₁, w₂) := (at_ 6, at_ 7, at_ 8)
    let thm : Internal.Thm := ⟨0, denCtx vars, [denIn P S vars e w₁, denIn P S vars e w₂],
      Term.eq w₁ w₂⟩
    let getT (t : Term) : Term := pc K.P "Prelude.get" [t]
    -- both stabilities at the sum: the second, normalized, by the first the values' equation
    let values (a b : ℕ) : Deducer := instNK K a (fun _ ↦ zeroN) <|
      instNK K b (fun _ ↦ zeroN) fun Γ Φ ψ ↦ K.image (Φ.length - 1) getT K.byNorm Γ Φ ψ
    -- the second resolution, normalized by the first, gives the terms' equation
    let main : Deducer := denE K 0 fun _ n₁ _ s₁ ↦ denE K 1 fun _ n₂ _ s₂ Γ Φ ψ ↦
      K.image (Φ.length - 1) getT (shiftK K s₁ false (atPos n₂) fun Γ Φ ψ ↦
        let a := Φ.length - 1
        shiftK K s₂ true (atPos n₁) (fun Γ Φ ψ ↦
          linkK K "denDet: the values" (values a (Φ.length - 1)) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
    let some d := main thm.ctx thm.hyps thm.concl
      | dbgTrace "denDet: not proved" fun _ ↦ none
    pure (thm, d))

/-- That two formulas are equivalent. -/
def iffT (o : ℕ) (a b : Term) : Term :=
  Internal.Logic.conj o (Internal.Logic.imp o a b) (Internal.Logic.imp o b a)

/-- That an expression denotes the quotation of a tree whose truth is that of the formula
{lit}`A`, in the context of a rule's variables. -/
def denBIn (P : Prog) (S : Defs) (vars : List Tree) (e A : Term) (scope env : Option Term := none) :
    Term :=
  let at_ := denAt vars
  Internal.Logic.ex P.o treeTy (Term.lam treeTy (Internal.Logic.conj P.o
    (denT P S (sh 1 (at_ 0)) (sh 1 (at_ 3)) (sh 1 (at_ 2)) (sh 1 (at_ 1))
      (sh 1 (scope.getD (at_ 4))) (sh 1 (env.getD (at_ 5))) (sh 1 e) (quoteV P (v 0)))
    (iffT P.o (truth P.o (v 0)) (sh 1 A))))

/-- That an expression denotes the quotation of a tree, of which a formula in the tree, the variable
of index 0, holds. -/
def denWith (P : Prog) (S : Defs) (vars : List Tree) (e A : Term) : Term :=
  let at_ := denAt vars
  Internal.Logic.ex P.o treeTy (Term.lam treeTy (Internal.Logic.conj P.o
    (denT P S (sh 1 (at_ 0)) (sh 1 (at_ 3)) (sh 1 (at_ 2)) (sh 1 (at_ 1)) (sh 1 (at_ 4))
      (sh 1 (at_ 5)) (sh 1 e) (quoteV P (v 0))) A))

/-- The numerals of the writer read as themselves at every number: the digits read as the number,
fixed by the numeral abbreviations' expansion, and the numeral not abbreviated. In the context of
the numeral abbreviations {lit}`nums`. -/
def numT (P : Prog) (nums : Term) : Term :=
  let n := v 0
  let chars := pc P "Typing.decimalChars" [n]
  let nums' := sh 1 nums
  let fn := Term.lam treeTy (pc P "Reader.expandNums" [sh 2 nums, v 0])
  Internal.Logic.all P.o treeTy (Term.lam treeTy (Internal.Logic.conj P.o
    (notTest P.o (pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev"
      [atomNameT (pc P "Recognize.num" [n]), nums']]))
    (Internal.Logic.conj P.o
      (Term.eq (pc P "Reader.numeral" [chars]) (pc P "Prelude.some" [n]))
      (truth P.o (pc P "charsFixed" [fn, chars])))))

/-- That no marker's datatype is named as the trees' type. -/
def noTreeMarkerT (P : Prog) (ms : Term) : Term :=
  Internal.Logic.all P.o treeTy (Term.lam treeTy (Internal.Logic.imp P.o
    (truth P.o (pc P "Prelude.isSome"
      [pc P "Reader.indexOf" [v 0, pc P "Typing.markerNames" [sh 1 ms]]]))
    (notTest P.o (pc P "Reader.named" [v 0, pc P "Reader.kwT" []]))))

/-- That the tree {lit}`r` holds the bits of a tree whose memberships are {lit}`q`: at each
datatype of the closure {lit}`cl`, its bit at the datatype's position has the truth of the test of
a field of that datatype at the memberships. -/
def bitsOkT (P : Prog) (ms cl r q : Term) : Term :=
  let childT := (primT Kernel.Prim.child).getD Term.star
  let pos := pc P "Reader.indexOf" [v 0, sh 1 cl]
  Internal.Logic.all P.o treeTy (Term.lam treeTy (Internal.Logic.imp P.o
    (truth P.o (pc P "Prelude.isSome" [pos]))
    (iffT P.o (truth P.o (apps childT [sh 1 r, pc P "Prelude.get" [pos]]))
      (truth P.o (pc P "Typing.fieldOk" [sh 1 ms, v 0, sh 1 q])))))

/-- The fixed variables of a context, in a rule's instance's order. -/
def denFixed (Γ : List Tree) : List Term :=
  [atPos 5 Γ, atPos 4 Γ, atPos 3 Γ, atPos 2 Γ, atPos 1 Γ, atPos 0 Γ]

/-- Equal expressions denote the same values: the second's denotation rewritten by the equation.
In the context of the value and the expressions. -/
def denCong (P : Prog) (S : Defs) : Step :=
  ("denCong", fun ix E ↦ do
    let K := denKit P S ix E
    let vars := [treeTy, treeTy, treeTy]
    let at_ := denAt vars
    let (e₁, e₂, w) := (at_ 6, at_ 7, at_ 8)
    let thm : Internal.Thm := ⟨0, denCtx vars, [Term.eq e₁ e₂, denIn P S vars e₂ w],
      denIn P S vars e₁ w⟩
    let some d := dRwBy (evalRw K.G K.E [.hyp 0] .full) dHyp thm.ctx thm.hyps thm.concl
      | dbgTrace "denCong: not proved" fun _ ↦ none
    pure (thm, d))

/-- A goal that an expression {lit}`l` denotes {lit}`w`, from a hypothesis that {lit}`r` does: the
expressions' equation by normalization under further rules ({name}`denCong`). -/
def denAsWith (K : Kit) (extra : List Internal.NormRule) (w l r : List Tree → Term) : Deducer :=
  applyThm K "denCong" (fun Γ ↦ [w Γ, r Γ, l Γ] ++ denFixed Γ)
    [linkK K "denAs: the expressions" (fun Γ Φ ψ ↦
      dEq (fun Γ Φ t u ↦ byMode .full K.G K.E 0 (K.rules Φ ++ extra) Γ
        (rwHyps (K.rules Φ) Φ) t u) Γ Φ ψ), dHyp] dHyp

/-- {name}`denAsWith` without further rules. -/
def denAs (K : Kit) (w l r : List Tree → Term) : Deducer := denAsWith K [] w l r

/-- The test of a field of the type {lit}`ty`, of a value the expression {lit}`e` denotes, where
the writer gives one, denotes a bit, which at memberships the value holds the bits of has the truth
of the field's test. The type's name the trees' type's: the numeral one, the field's test true as
no marker has that name. Otherwise the type's position in the closure, by which the writer gives a
test: the child at that position, whose truth the bits give. -/
def fieldDen (P : Prog) (S : Defs) : Step :=
  ("fieldDen", fun ix E ↦ do
    let K := denKit P S ix E
    let P := K.P
    let L := K.L
    let Ls := list treeTy
    let vars := [treeTy, treeTy, treeTy, Ls, Ls]
    let at_ := denAt vars
    let (cl, ms, ty, e, r) := (at_ 6, at_ 7, at_ 8, at_ 9, at_ 10)
    let rChild := pc P "Recognize.rChild" []
    let test := pc P "Recognize.fieldTest" [cl, ty, e]
    let thm : Internal.Thm := ⟨0, denCtx vars,
      [truth P.o (pc P "Prelude.isSome" [test]), denIn P S vars e (quoteV P r),
        noTreeMarkerT P ms, numT P (at_ 1)] ++
        (absentTests P rChild (at_ 4) (at_ 2) ++
          [pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev" [atomNameT rChild, at_ 1]],
            pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev"
              [atomNameT (pc P "Recognize.one" []), at_ 1]]]).map (notTest P.o),
      denWith P S vars (pc P "Prelude.get" [test])
        (Internal.Logic.all P.o Ls (Term.lam Ls (Internal.Logic.imp P.o
          (bitsOkT P (sh 2 ms) (sh 2 cl) (sh 2 r) (v 0))
          (iffT P.o (truth P.o (v 1)) (truth P.o (pc P "Typing.fieldOk"
            [sh 2 ms, sh 2 ty, v 0]))))))⟩
    let tyAt := atPos 8
    let named (Γ : List Tree) : Term := pc P "Reader.named" [tyAt Γ, pc P "Reader.kwT" []]
    let last : Deducer := fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ
    let testAt (Γ : List Tree) : Term := pc P "Prelude.get"
      [pc P "Recognize.fieldTest" [atPos 6 Γ, tyAt Γ, atPos 9 Γ]]
    -- the trees' type: the field's test true, its index absent by the markers' names
    let treeCase : Deducer := fun Γ Φ ψ ↦
      dExI L K.G K.E (leafT (numeral 1)) (dConjI L
        (linkK K "fieldDen: the numeral one" <|
          applyThm K "denDigit/one" denFixed [K.byHyp 7]
            (denAs K (fun _ ↦ quoteV P (leafT (numeral 1))) testAt
              fun _ ↦ pc P "Recognize.one" []))
        (linkK K "fieldDen: the tree's test" <| dAllI L <| dImpI L <| K.norm <| dConjI L
          (dImpI L <| decideIn K (fun Γ ↦ pc P "Prelude.isSome"
              [pc P "Reader.indexOf" [tyAt Γ, pc P "Typing.markerNames" [atPos 7 Γ]]])
            (linkK K "fieldDen: not a marker's" fun Γ Φ ψ ↦
              dRwBy (evalRw K.G K.E (K.rules Φ ++ [.delta (P.idx "Typing.fieldOk")]) .full)
                (K.solve 3) Γ Φ ψ)
            (linkK K "fieldDen: a marker's" fun Γ Φ ψ ↦
              dAllE L K.G K.E 2 (tyAt Γ) (K.impE (K.solve 3) (K.impE (K.solve 3)
                fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ)) Γ Φ ψ))
          (dImpI L (K.solve 3)))) Γ Φ ψ
    let childT ← primT Kernel.Prim.child
    let pos (Γ : List Tree) : Term := pc P "Prelude.get" [pc P "Reader.indexOf"
      [tyAt Γ, atPos 6 Γ]]
    -- a position in the closure: the child at that position
    let posCase : Deducer := fun Γ Φ ψ ↦
      dExI L K.G K.E (apps childT [atPos 10 Γ, pos Γ]) (dConjI L
        (linkK K "fieldDen: the child" <|
          dAllE L K.G K.E 3 (pos Γ) <| normLastK K <| K.conjE fun Γ₁ Φ₁ ψ₁ ↦
            let h₁ := Φ₁.length - 2
            K.conjE (fun Γ₂ Φ₂ ψ₂ ↦
              let h₄ := Φ₂.length - 1
              applyThm K "denNum" (fun Γ ↦ pos Γ :: denFixed Γ) [K.byHyp h₁, K.byNorm,
                K.byHyp h₄] (fun Γ Φ ψ ↦
                applyThm K "denPrim2/child" (fun Γ ↦ [pos Γ, atPos 10 Γ,
                    pc P "Recognize.num" [pos Γ], atPos 9 Γ] ++ denFixed Γ)
                  [K.byHyp 4, K.byHyp 5, K.byHyp 6, dHyp, dHyp]
                  (denAs K (fun Γ ↦ quoteV P (apps childT [atPos 10 Γ, pos Γ])) testAt
                    fun Γ ↦ pc P "Recognize.s3"
                      [pc P "Recognize.rChild" [], atPos 9 Γ, pc P "Recognize.num" [pos Γ]]) Γ Φ ψ)
                Γ₂ Φ₂ ψ₂) Γ₁ Φ₁ ψ₁)
        (linkK K "fieldDen: the bit" <| dAllI L <| dImpI L fun Γ Φ ψ ↦
          dAllE L K.G K.E (Φ.length - 1) (tyAt Γ) (K.impE (K.solve 3) last) Γ Φ ψ)) Γ Φ ψ
    let bits : Deducer :=
      decideIn K named
        (decideIn K (fun Γ ↦ pc P "Prelude.isSome" [pc P "Reader.indexOf" [tyAt Γ, atPos 6 Γ]])
          (linkK K "fieldDen: no test" (K.hypFalse 0))
          (linkK K "fieldDen: a position" posCase))
        (linkK K "fieldDen: the trees' type" treeCase)
    let some d := bits thm.ctx thm.hyps thm.concl
      | dbgTrace "fieldDen: not proved" fun _ ↦ none
    pure (thm, d))

/-- An implication between truths of decided tests and their conjunctions: its hypothesis, or a
conjunct of it, refuted; or its conclusion by the hypotheses. -/
def impAuto (K : Kit) : Deducer :=
  dImpI K.L fun Γ Φ ψ ↦ (K.hypFalse (Φ.length - 1) Γ Φ ψ).orElse fun _ ↦
    (K.conjE (fun Γ Φ ψ ↦ (K.hypFalse (Φ.length - 2) Γ Φ ψ).orElse fun _ ↦
      (K.hypFalse (Φ.length - 1) Γ Φ ψ).orElse fun _ ↦ K.auto 4 Γ Φ ψ) Γ Φ ψ).orElse fun _ ↦
    K.auto 4 Γ Φ ψ

/-- An equivalence of truths of decided tests and their conjunctions. -/
def iffAuto (K : Kit) : Deducer := K.norm <| dConjI K.L (impAuto K) (impAuto K)

/-- The writer's conjunction of expressions denoting quotations denotes the quotation of a tree
true exactly where both are. Where an expression is the numeral one, its tree is the numeral's
({name}`denDet`), and the conjunction is the other expression; otherwise it is the conditional. -/
def conjDen (P : Prog) (S : Defs) : Step :=
  ("conjDen", fun ix E ↦ do
    let K := denKit P S ix E
    let P := K.P
    let L := K.L
    let vars := [treeTy, treeTy, treeTy, treeTy]
    let at_ := denAt vars
    let (a, b, x, y) := (at_ 6, at_ 7, at_ 8, at_ 9)
    let (one, zero) := (pc P "Recognize.one" [], pc P "Recognize.zero" [])
    let rIf := pc P "Recognize.rIf" []
    let plain (t : Term) : Term :=
      notTest P.o (pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev" [atomNameT t, at_ 1]])
    let spec : Term := Internal.Logic.conj P.o (truth P.o x) (truth P.o y)
    let thm : Internal.Thm := ⟨0, denCtx vars,
      [denIn P S vars a (quoteV P x), denIn P S vars b (quoteV P y), plain one, plain zero,
        plain rIf],
      denBIn P S vars (pc P "Recognize.conj" [a, b]) spec⟩
    let (aAt, bAt, xAt, yAt) := (atPos 6, atPos 7, atPos 8, atPos 9)
    let formAt (Γ : List Tree) : Term := pc P "Recognize.conj" [aAt Γ, bAt Γ]
    let equalT ← primT Kernel.Prim.equal
    let oneAt (_ : List Tree) : Term := one
    -- the expression of the hypothesis of index h is the numeral one: its tree true
    let isOne (e w : List Tree → Term) (k : Deducer) : Deducer :=
      K.cutThm "equalSound" (fun Γ ↦ [e Γ]) <| K.allEΓ oneAt <| K.impE (K.solve 3) <|
        normLastK K fun Γ Φ ψ ↦
        applyThm K "denDigit/one" denFixed [K.byHyp 2] (fun Γ Φ ψ ↦
          let dOne := Φ.length - 1
          applyThm K "denDet" (fun Γ ↦ [quoteV P (leafT (numeral 1)), quoteV P (w Γ), e Γ] ++
              denFixed Γ)
            [dHyp, fun Γ Φ ψ ↦
              dRwBy (evalRw K.G K.E [.hyp (dOne - 2)] .full) (fun Γ Φ ψ ↦ dHyp Γ Φ ψ) Γ Φ ψ]
            (fun Γ Φ ψ ↦ K.image (Φ.length - 1)
              (fun t ↦ apps ((primT Kernel.Prim.child).getD
              Term.star) [t, leafT bnilT]) k Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
    let oneArm (e w other otherW : List Tree → Term) : Deducer :=
      isOne e w fun Γ Φ ψ ↦
        dExI L K.G K.E (otherW Γ) (dConjI L
          (denAs K (fun Γ ↦ quoteV P (otherW Γ)) formAt other) (iffAuto K)) Γ Φ ψ
    let condArm : Deducer := fun Γ Φ ψ ↦
      let form := pc P "Recognize.s4" [rIf, aAt Γ, bAt Γ, zero]
      let value := condT treeTy (call D.lab [] [xAt Γ]) (yAt Γ) (leafT (numeral 0))
      applyThm K "denDigit/zero" denFixed [K.byHyp 3] (fun Γ Φ ψ ↦
        applyThm K "denIf" (fun Γ ↦ [leafT (numeral 0), yAt Γ, xAt Γ, zero, bAt Γ, aAt Γ] ++
            denFixed Γ) [K.byHyp 4, dHyp, dHyp, dHyp] (fun Γ Φ ψ ↦
          dExI L K.G K.E value (dConjI L
            (denAs K (fun _ ↦ quoteV P value) formAt (fun _ ↦ form))
            (linkK K "conjDen: the conditional's truth" <|
              decideIn K xAt (iffAuto K) (iffAuto K))) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
    let main : Deducer :=
      decideIn K (fun Γ ↦ apps equalT [aAt Γ, one])
        (decideIn K (fun Γ ↦ apps equalT [bAt Γ, one]) condArm
          (linkK K "conjDen: the second one" (oneArm bAt yAt aAt xAt)))
        (linkK K "conjDen: the first one" (oneArm aAt xAt bAt yAt))
    let some d := main thm.ctx thm.hyps thm.concl
      | dbgTrace "conjDen: not proved" fun _ ↦ none
    pure (thm, d))

/-- The kit of the writer's larger forms: that of {name}`denKit`, the writer's builders and tests
kept folded. -/
def writerKit (P : Prog) (S : Defs) (ix : String → ℕ) (E : Array Internal.Entry) : Kit :=
  let K := denKit P S ix E
  { K with P := { K.P with folded := K.P.folded ++ ["Recognize.fieldTest", "Recognize.conj",
    "Reader.allSome", "Recognize.s2", "Recognize.s3", "Recognize.s4", "Recognize.num",
    "Recognize.sx", "Recognize.dropE", "Reader.both"] } }

/-- The number of a list's elements after a number, by the prelude's right fold, as the prelude's
length counts them from zero. -/
def lenFrom (b xs : Term) : Term :=
  foldrT treeTy treeTy (Term.lam treeTy (Term.lam treeTy
    (apps ((primT Kernel.Prim.add).getD Term.star) [v 0, leafT (numeral 1)])))
    (leafT b) xs

/-- The number of a list's elements after a number's successor is the successor of their number
after it: by induction on the list. In the context of the list and the number. -/
def lenFromSucc (P : Prog) (S : Defs) : Step :=
  ("lenFromSucc", fun ix E ↦ do
    let K := writerKit P S ix E
    let L := K.L
    -- under the quantifier: the number v0, the list v1
    let φ := Internal.Logic.all P.o bitsTy (Term.lam bitsTy
      (Term.eq (lenFrom (call D.succ [] [v 0]) (v 1))
        (apps ((primT Kernel.Prim.add).getD Term.star) [lenFrom (v 0) (v 1), leafT (numeral 1)])))
    let d₀ ← linkK K "lenFromSucc: empty" (dAllI L K.byNorm) [] []
      (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
    let cons : Deducer := linkK K "lenFromSucc: construction" <| dAllI L fun Γ Φ ψ ↦
      dAllE L K.G K.E 0 (atPos (Γ.length - 1) Γ) (normLastK K K.byNorm) Γ Φ ψ
    let d₁ ← cons [list treeTy, treeTy] [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, [list treeTy], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- {name}`lenFromSucc` as a rule, both sides in normal form. In the context of the number and the
list. -/
def lenFromSuccR (P : Prog) (S : Defs) : Step :=
  ("lenFromSuccR", fun ix E ↦ do
    let K := writerKit P S ix E
    let Γ := [bitsTy, list treeTy]
    let l ← nfE K.G E (K.rules []) Γ (lenFrom (call D.succ [] [v 0]) (v 1))
    let r ← nfE K.G E (K.rules []) Γ
      (apps ((primT Kernel.Prim.add).getD Term.star) [lenFrom (v 0) (v 1), leafT (numeral 1)])
    let thm : Internal.Thm := ⟨0, Γ, [], Term.eq l r⟩
    let some d := K.cutThm "lenFromSucc" (fun _ ↦ [v 1]) (K.allEΓ (fun _ ↦ v 0)
        (normLastK K (linkK K "lenFromSuccR" K.byNorm))) thm.ctx thm.hyps thm.concl
      | dbgTrace "lenFromSuccR: not proved" fun _ ↦ none
    pure (thm, d))

/-- The predecessor of a successor by one, as a tree, in the normal form of the writer's kit: by
the bits of the number. -/
def subOneK (P : Prog) (S : Defs) : Step :=
  ("subOneK", fun ix E ↦ do
    let K := writerKit P S ix E
    let Γ := [bitsTy]
    let subT ← primT Kernel.Prim.sub
    let addT ← primT Kernel.Prim.add
    let succ := apps addT [leafT (v 0), leafT (numeral 1)]
    let l ← nfE K.G E (K.rules []) Γ (apps subT [succ, leafT (numeral 1)])
    let r ← nfE K.G E (K.rules []) Γ (leafT (v 0))
    let thm : Internal.Thm := ⟨0, Γ, [], Term.eq l r⟩
    let some d := byBitsSplit K K.P ix 3 thm | dbgTrace "subOneK: not proved" fun _ ↦ none
    pure (thm, d))

/-- The writer's walk of a constructor's field types from the last, at a closure, from the state of
a number and no tests: at each type, the number's predecessor and the test of a child at it before
the tests. -/
def fieldsFold (P : Prog) (cl z fts : Term) : Term :=
  let X := prod treeTy (list treeTy)
  let subT := (primT Kernel.Prim.sub).getD Term.star
  let pred := apps subT [Term.fst (v 0), leafT (numeral 1)]
  foldrT treeTy X (Term.lam treeTy (Term.lam X (Term.pair pred (consT treeTy
    (pc P "Recognize.fieldTest" [sh 2 cl, v 1, pc P "Recognize.s3" [pc P "Recognize.rChild" [],
      pc P "Recognize.vN" [], pc P "Recognize.num" [pred]]]) (Term.snd (v 0))))))
    (Term.pair z (nilT treeTy)) fts

/-- The number in the writer's walk of field types from the number of the types after a number is
that number: by induction on the types, the number's successor by {name}`lenFromSucc`, its
predecessor taken. In the context of the types, the closure and, under the quantifier, the
number. -/
def fieldsCount (P : Prog) (S : Defs) : Step :=
  ("fieldsCount", fun ix E ↦ do
    let K₀ := writerKit P S ix E
    let K : Kit := { K₀ with more := K₀.more ++ ["lenFromSuccR", "subOneK"] }
    let L := K.L
    -- under the quantifier: the number v0, the types v1, the closure v2
    let body (b fts cl : Term) : Term :=
      Term.eq (Term.fst (fieldsFold P cl (lenFrom b fts) fts)) (leafT b)
    let φ := Internal.Logic.all P.o bitsTy (Term.lam bitsTy (body (v 0) (v 1) (v 2)))
    let d₀ ← linkK K "fieldsCount: empty" (dAllI L K.byNorm) [list treeTy] []
      (Term.subst φ fun i ↦ if i = 0 then nilT treeTy else v (i - 1))
    let cons : Deducer := linkK K "fieldsCount: construction" <| dAllI L fun Γ Φ ψ ↦
      dAllE L K.G K.E 0 (call D.succ [] [atPos (Γ.length - 1) Γ])
        (normLastK K (linkK K "fieldsCount: inner" K.byNorm)) Γ Φ ψ
    let d₁ ← cons [list treeTy, treeTy, list treeTy] [Internal.weakenElem φ]
      (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, [list treeTy, list treeTy], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- Of a list of optional trees of which each is present, as {lit}`Reader.allSome` tests: at a
construction, that of the head and the rest. In the context of the rest and the head. -/
def allSomeCons (P : Prog) (S : Defs) (head : Bool) : Step :=
  (if head then "allSomeHead" else "allSomeRest", fun ix E ↦ do
    let K := writerKit P S ix E
    let Γ := [list treeTy, treeTy]
    let some' (t : Term) : Term := truth K.P.o (pc K.P "Prelude.isSome" [t])
    let all (xs : Term) : Term := pc K.P "Reader.allSome" [xs]
    let thm : Internal.Thm := ⟨0, Γ, [some' (all (consT treeTy (v 1) (v 0)))],
      if head then some' (v 1) else some' (all (v 0))⟩
    let unfold : List Internal.NormRule := [.delta (K.P.idx "Reader.allSome"),
      .delta (K.P.idx "Reader.both")]
    -- the hypothesis unfolded and split on the bits it is blocked on, each case refuted or the
    -- goal by the unfolding
    let solve : Deducer := fun Γ Φ ψ ↦
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ 0 ++ unfold) .full) 0 (fun Γ Φ ψ ↦
        K.splitHyp (Φ.length - 1) (linkK K "allSomeCons: the goal" fun Γ Φ ψ ↦
          dRwBy (evalRw K.G K.E (K.rules Φ ++ unfold) .full) (K.solve 3) Γ Φ ψ) 8 Γ Φ ψ) Γ Φ ψ
    let some d := solve thm.ctx thm.hyps thm.concl
      | dbgTrace "allSomeCons: not proved" fun _ ↦ none
    pure (thm, d))

/-- The children of a node of optional trees' values at a construction, where they are present: the
head's value before the rest's. In the context of the rest and the head. -/
def allSomeKids (P : Prog) (S : Defs) : Step :=
  ("allSomeKids", fun ix E ↦ do
    let K := writerKit P S ix E
    let Γ := [list treeTy, treeTy]
    let all (xs : Term) : Term := pc K.P "Reader.allSome" [xs]
    let kids (xs : Term) : Term := call D.children [] [pc K.P "Prelude.get" [all xs]]
    let thm : Internal.Thm := ⟨0, Γ,
      [truth K.P.o (pc K.P "Prelude.isSome" [all (consT treeTy (v 1) (v 0))])],
      Term.eq (kids (consT treeTy (v 1) (v 0)))
        (consT treeTy (pc K.P "Prelude.get" [v 1]) (kids (v 0)))⟩
    let unfold : List Internal.NormRule := [.delta (K.P.idx "Reader.allSome"),
      .delta (K.P.idx "Reader.both")]
    let solve : Deducer := fun Γ Φ ψ ↦
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ 0 ++ unfold) .full) 0 (fun Γ Φ ψ ↦
        K.splitHyp (Φ.length - 1) (linkK K "allSomeKids: the sides" fun Γ Φ ψ ↦
          dEq (fun Γ Φ t u ↦ byMode .full K.G K.E 0 (K.rules Φ ++ unfold) Γ
            (rwHyps (K.rules Φ) Φ) t u) Γ Φ ψ) 8 Γ Φ ψ) Γ Φ ψ
    let some d := solve thm.ctx thm.hyps thm.concl
      | dbgTrace "allSomeKids: not proved" fun _ ↦ none
    pure (thm, d))

/-- The removal of a number of elements commutes with that of the first: the instance of
{lit}`rIterComm` at the rest of a list, both sides in normal form. In the context of the number
and the list. -/
def dropTail (P : Prog) (S : Defs) : Step :=
  ("dropTail", fun ix E ↦ do
    let K := writerKit P S ix E
    let Γ := [bitsTy, list treeTy]
    let some (Internal.Entry.language a) := E[ix "rIterComm"]? | none
    let θ := [list treeTy]
    let σ := [v 1, v 0, tailFn]
    let l ← nfE K.G E (K.rules []) Γ (dropT (v 0) (Term.app tailFn (v 1)))
    let r ← nfE K.G E (K.rules []) Γ (Term.app tailFn (dropT (v 0) (v 1)))
    let thm : Internal.Thm := ⟨0, Γ, [], Term.eq l r⟩
    let some d := dCut (Internal.instTerm θ σ a.concl) (nd (.apply (ix "rIterComm") θ σ))
        (normLastK K (linkK K "dropTail" K.byNorm)) thm.ctx thm.hyps thm.concl
      | dbgTrace "dropTail: not proved" fun _ ↦ none
    pure (thm, d))

/-- The kit of the walk of a constructor's fields: the writer's, comparisons of lengths, iteration
at a successor and the walk's own equations. -/
def fieldsKit (P : Prog) (S : Defs) (ix : String → ℕ) (E : Array Internal.Entry) : Kit :=
  let K := writerKit P S ix E
  { K with
    P := { K.P with folded := K.P.folded.filter (· != "Typing.ctorOk") }
    more := K.more ++ (lenRules ++ ["lcaseRebuild", "lcaseRebuildL", "dropTail", "lenFromSuccR",
      "subOneK"]).filter fun nm ↦ 0 < ix nm ∧ ix nm < E.size }

/-- The typing's test of a constructor at the label zero, of the position zero, the field types
{lit}`fts` and the last field's flag and type: the walk of the fields, the label's test holding. -/
def walkT (P : Prog) (ms flag rty fts qs : Term) : Term :=
  let zero := leafT bnilT
  pc P "Typing.ctorOk" [ms, node0 (consT treeTy zero (consT treeTy (node0 fts)
    (consT treeTy flag (consT treeTy rty (nilT treeTy))))), zero, qs]

/-- The memberships of a list of trees in the markers' datatypes. -/
def membershipsT (P : Prog) (ms cs : Term) : Term :=
  mapListsT (Term.lam treeTy (pc P "Typing.memberships" [sh 1 ms, v 0])) cs

/-- The optional node of the tests the writer's walk of field types gives, from the number of the
types after a number. -/
def fieldsAll (P : Prog) (cl b fts : Term) : Term :=
  pc P "Reader.allSome" [Term.snd (fieldsFold P cl (lenFrom b fts) fts)]

/-- The writer's conjunction of the tests of an optional node with an expression, by the prelude's
right fold. -/
def conjsT (P : Prog) (vt all : Term) : Term :=
  foldrT treeTy treeTy (pc P "Recognize.conj" []) vt (call D.children [] [pc P "Prelude.get" [all]])

/-- The statement of the walk of a constructor's fields. Under the quantifiers, the types v4 and:
if the walk's number is one after which the bits of the children's values, the function {lit}`R` of
index 7 at the children of index 8, are the values at the children {lit}`cs'` of index 2, the tests
the writer gives are present, and an expression denotes the quotation of the tree {lit}`y`, then
the conjunction of the tests with that expression denotes a bit which, at children holding the bits
and enough of them, with {lit}`y` true exactly where the walk's end holds at the children left, is
true exactly where the walk of the fields holds. -/
def fieldsφ (P : Prog) (S : Defs) (fts : Term) : Term :=
  let o := P.o
  let imp := Internal.Logic.imp o
  let Ls := list treeTy
  let ltT := (primT Kernel.Prim.lt).getD Term.star
  let addT := (primT Kernel.Prim.add).getD Term.star
  -- beneath the four quantifiers: y v0, vt v1, cs' v2, b v3; the context after them
  let up (i : ℕ) : Term := v (i + 5)
  let (ftsI, rty, flag, R, cs, ms, cl, env, scope, tys, names, nums, Dv) :=
    (sh 4 fts, up 0, up 1, up 2, up 3, up 4, up 5, up 6, up 7, up 8, up 9, up 10, up 11)
  let all := fieldsAll P cl (v 3) ftsI
  let conjs := conjsT P (v 1) all
  -- beneath the bit v0 as well
  let bump (t : Term) : Term := sh 1 t
  let qs := membershipsT P (bump ms) (v 3)
  let lenOf (t : Term) : Term := pc P "Prelude.length" [t]
  let bitsAll := S.allL (Term.lam treeTy (bitsOkT P (sh 2 ms) (sh 2 cl)
    (Term.app (sh 2 R) (v 0)) (pc P "Typing.memberships" [sh 2 ms, v 0]))) (v 3)
  let enough := truth o (apps ltT [lenOf (bump ftsI), apps addT [lenOf (v 3),
    leafT (numeral 1)]])
  let left := membershipsT P (bump ms) (dropT (call D.lab [] [lenOf (bump ftsI)]) (v 3))
  let atEnd := walkT P (bump ms) (bump flag) (bump rty) (nilT treeTy) left
  let walk := walkT P (bump ms) (bump flag) (bump rty) (bump ftsI) qs
  let concl := Internal.Logic.ex o treeTy (Term.lam treeTy (Internal.Logic.conj o
    (denT P S (bump Dv) (bump tys) (bump names) (bump nums) (bump scope) (bump env) (bump conjs)
      (quoteV P (v 0)))
    (imp bitsAll (imp enough (imp (iffT o (truth o (v 1)) (truth o atEnd))
      (iffT o (truth o (v 0)) (truth o walk)))))))
  Internal.Logic.all o bitsTy (Term.lam bitsTy (Internal.Logic.all o Ls (Term.lam Ls
    (Internal.Logic.all o treeTy (Term.lam treeTy (Internal.Logic.all o treeTy (Term.lam treeTy
      (imp (Term.eq (dropT (v 3) (mapFnT R cs)) (mapFnT R (v 2)))
        (imp (truth o (pc P "Prelude.isSome" [all]))
          (imp (denT P S Dv tys names nums scope env (v 1) (quoteV P (v 0))) concl))))))))))

/-- The context of the walk of a constructor's fields: the types, the last field's type and flag,
the function of a child's bits, the children, the markers and the closure, around the fixed
variables. -/
def fieldsVars : List Tree :=
  [list treeTy, treeTy, treeTy, exp treeTy treeTy, list treeTy, list treeTy, list treeTy]

/-- The hypotheses of the walk of a constructor's fields: the variable of the node denotes the
quotation of the node over the children's bits, the markers name no trees' type, the numerals read
as themselves, and the atoms of the writer resolve as the primitive's and are not abbreviated. -/
def fieldsHyps (P : Prog) (S : Defs) : List Term :=
  let at_ := denAt fieldsVars
  let (ms, cs, R) := (at_ 7, at_ 8, at_ 9)
  let rChild := pc P "Recognize.rChild" []
  let plain (t : Term) : Term :=
    notTest P.o (pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev" [atomNameT t, at_ 1]])
  [denIn P S fieldsVars (pc P "Recognize.vN" []) (quoteV P (node0 (mapFnT R cs))),
    noTreeMarkerT P ms, numT P (at_ 1)] ++
    (absentTests P rChild (at_ 4) (at_ 2)).map (notTest P.o) ++
    [plain rChild, plain (pc P "Recognize.one" []), plain (pc P "Recognize.zero" []),
      plain (pc P "Recognize.rIf" [])]

/-- The walk of a constructor's fields: by induction on the types. No types: no tests, the bit the
expression's tree, the walk's end the walk. A construction, where the writer's number is the number
{lit}`b`: the test of the child at {lit}`b` ({name}`fieldDen`) and the induction hypothesis at the
successor and the children's rest, whose conjunction ({name}`conjDen`) is the bit; at children
holding the bits, enough of them, the head's test by the bits and the rest's by the induction
hypothesis. In the context of the fixed variables and the walk's. -/
def fieldsWalk (P : Prog) (S : Defs) : Step :=
  ("fieldsWalk", fun ix E ↦ do
    let K := fieldsKit P S ix E
    let P := K.P
    let L := K.L
    let Ls := list treeTy
    let φ := fieldsφ P S (v 0)
    let Γ₀ := denCtx fieldsVars
    let hyps := fieldsHyps P S
    let some lowered := Internal.lowerHyps P.G 0 Γ₀.tail hyps
      | dbgTrace "fieldsWalk: the hypotheses" fun _ ↦ none
    let all4 (k : Deducer) : Deducer := dAllI L <| dAllI L <| dAllI L <| dAllI L k
    let imp3 (k : Deducer) : Deducer := dImpI L <| dImpI L <| dImpI L k
    let last : Deducer := fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ
    let unfoldAll : List Internal.NormRule := [.delta (P.idx "Reader.allSome")]
    -- the positions: the fixed variables, closure 6, markers 7, children 8, function 9, flag 10,
    -- last type 11, after them the list's parts, then the number, the children, the expression and
    -- the tree
    let (clAt, msAt, csAt, RAt, _, _) :=
      (atPos 6, atPos 7, atPos 8, atPos 9, atPos 10, atPos 11)
    -- no types
    let d₀ ← (all4 <| imp3 fun Γ Φ ψ ↦
        let (bAt, vtAt, yAt) := (atPos 12, atPos 14, atPos 15)
        dExI L K.G K.E (yAt Γ) (dConjI L
          (linkK K "fields: the empty conjunction"
            (denAsWith K unfoldAll (fun Γ ↦ quoteV P (yAt Γ))
              (fun Γ ↦ conjsT P (vtAt Γ) (fieldsAll P (clAt Γ) (bAt Γ) (nilT treeTy))) vtAt))
          (linkK K "fields: the empty walk" <| dImpI L <| dImpI L <| dImpI L last)) Γ Φ ψ)
      Γ₀.tail lowered (Term.subst φ fun i ↦ if i = 0 then nilT treeTy else v (i - 1))
    -- a construction: head 12, rest 13, number 14, children 15, expression 16, tree 17
    let ih := hyps.length
    let (h₁, r₁, b₁, cs₁, vt₁, y₁) := (atPos 12, atPos 13, atPos 14, atPos 15, atPos 16, atPos 17)
    let rChild := pc P "Recognize.rChild" []
    let childT ← primT Kernel.Prim.child
    let succB (Γ : List Tree) : Term := call D.succ [] [b₁ Γ]
    let nodeAt (Γ : List Tree) : Term := node0 (mapFnT (RAt Γ) (csAt Γ))
    let eAt (Γ : List Tree) : Term := pc P "Recognize.s3" [rChild, pc P "Recognize.vN" [],
      pc P "Recognize.num" [leafT (b₁ Γ)]]
    let headT' (Γ : List Tree) : Term := pc P "Recognize.fieldTest" [clAt Γ, h₁ Γ, eAt Γ]
    let restT (Γ : List Tree) : Term :=
      Term.snd (fieldsFold P (clAt Γ) (lenFrom (succB Γ) (r₁ Γ)) (r₁ Γ))
    let rAt (Γ : List Tree) : Term := apps childT [nodeAt Γ, leafT (b₁ Γ)]
    let restE (Γ : List Tree) : Term := conjsT P (vt₁ Γ) (pc P "Reader.allSome" [restT Γ])
    let getHead (Γ : List Tree) : Term := pc P "Prelude.get" [headT' Γ]
    -- the rest of the children {lit}`tl`, from the case analysis of the children, and the guard
    -- at the indices of the head's bits, the rest's guard and the conjunction's equivalence
    let main (dPres : ℕ) (tl : List Tree → Term) (guard : ℕ → ℕ → ℕ → ℕ → ℕ → Deducer) :
        Deducer :=
      let final (uBits uPos vGuard vPos : ℕ) : Deducer := K.exE <| K.conjE fun Γ Φ ψ ↦
        let (wPos, wIff) := (Γ.length - 1, Φ.length - 1)
        dExI L K.G K.E (atPos wPos Γ) (dConjI L
          (linkK K "fields: the conjunction" (denAs K (fun _ ↦ quoteV P (atPos wPos Γ))
            (fun Γ ↦ conjsT P (vt₁ Γ)
              (fieldsAll P (clAt Γ) (b₁ Γ) (consT treeTy (h₁ Γ) (r₁ Γ))))
            (fun Γ ↦ pc P "Recognize.conj" [getHead Γ, restE Γ])))
          (guard uBits vGuard wIff uPos vPos)) Γ Φ ψ
      let conjStage (uBits uPos vGuard vPos : ℕ) : Deducer :=
        applyThm K "conjDen" (fun Γ ↦ [atPos vPos Γ, atPos uPos Γ, restE Γ, getHead Γ] ++
            denFixed Γ) [dHyp, dHyp, K.byHyp 6, K.byHyp 7, K.byHyp 8]
          (final uBits uPos vGuard vPos)
      let ihStage (hRest uBits uPos : ℕ) : Deducer := fun Γ Φ ψ ↦
        dAllE L K.G K.E ih (succB Γ) (K.allEΓ tl <| K.allEΓ vt₁ <| K.allEΓ y₁ <|
          K.impE (linkK K "fields: the rest's values" K.byNorm) <|
          K.impE (K.byHyp hRest) <| K.impE dHyp <| K.exE <| K.conjE fun Γ Φ ψ ↦
            conjStage uBits uPos (Φ.length - 1) (Γ.length - 1) Γ Φ ψ) Γ Φ ψ
      let fieldStage (hHead hRest : ℕ) : Deducer :=
        applyThm K "fieldDen" (fun Γ ↦ [rAt Γ, eAt Γ, h₁ Γ, msAt Γ, clAt Γ] ++ denFixed Γ)
          [K.byHyp hHead, dHyp, dHyp, dHyp, K.byHyp 3, K.byHyp 4, K.byHyp 5, K.byHyp 6] <|
        K.exE <| K.conjE fun Γ Φ ψ ↦ ihStage hRest (Φ.length - 1) (Γ.length - 1) Γ Φ ψ
      let childStage (hHead hRest h₃ h₅ : ℕ) : Deducer :=
        applyThm K "denNum" (fun Γ ↦ leafT (b₁ Γ) :: denFixed Γ) [K.byHyp h₃, K.byNorm,
          K.byHyp h₅] <|
        applyThm K "denPrim2/child" (fun Γ ↦ [leafT (b₁ Γ), nodeAt Γ,
            pc P "Recognize.num" [leafT (b₁ Γ)], pc P "Recognize.vN" []] ++ denFixed Γ)
          [K.byHyp 3, K.byHyp 4, K.byHyp 5, dHyp, dHyp] (fieldStage hHead hRest)
      let numStage (hHead hRest : ℕ) : Deducer := fun Γ Φ ψ ↦
        dAllE L K.G K.E 2 (leafT (b₁ Γ)) (normLastK K <| K.conjE fun Γ₁ Φ₁ ψ₁ ↦
          let h₃ := Φ₁.length - 2
          K.conjE (fun Γ₂ Φ₂ ψ₂ ↦ childStage hHead hRest h₃ (Φ₂.length - 1) Γ₂ Φ₂ ψ₂) Γ₁ Φ₁ ψ₁)
          Γ Φ ψ
      -- the removal's equation normalized, a rule; the writer's number at the rest's walk, the
      -- tests' presence and the conjunction's list
      fun Γ Φ ψ ↦ dRwHyp (evalRw K.G K.E (K.rulesEx Φ (dPres - 1)) .full) (dPres - 1) (
      K.cutThm "fieldsCount" (fun Γ ↦ [r₁ Γ, clAt Γ]) <| K.allEΓ succB <| normLastK K <|
      applyThm K "allSomeHead" (fun Γ ↦ [restT Γ, headT' Γ]) [K.byHyp dPres] fun Γ Φ ψ ↦
        let hHead := Φ.length - 1
        applyThm K "allSomeRest" (fun Γ ↦ [restT Γ, headT' Γ]) [K.byHyp dPres] (fun Γ Φ ψ ↦
          let hRest := Φ.length - 1
          applyThm K "allSomeKids" (fun Γ ↦ [restT Γ, headT' Γ]) [K.byHyp dPres]
            (normLastK K (numStage hHead hRest)) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
    -- no children left: not enough of them
    let noKids (dPres : ℕ) : Deducer := main dPres (fun _ ↦ nilT treeTy) fun _ _ _ _ _ ↦
      linkK K "fields: no children" <| dImpI L <| dImpI L fun Γ Φ ψ ↦
        K.splitHyp (Φ.length - 1) (fun _ _ _ ↦ none) 6 Γ Φ ψ
    let someKids (dPres : ℕ) : Deducer := fun Γ Φ ψ ↦
      let (c₁, tl₁) := (atPos (Γ.length - 2), atPos (Γ.length - 1))
      let qAt (Γ : List Tree) : Term := pc P "Typing.memberships" [msAt Γ, c₁ Γ]
      let okAt (Γ : List Tree) : Term := pc P "Typing.fieldOk" [msAt Γ, h₁ Γ, qAt Γ]
      let mp (h : ℕ) (prem k : Deducer) : Deducer := dImpE L h prem k
      -- the equivalences split, the implications at the last indices; the test of the head's field
      -- decided, each direction through it
      let finish (hA hB : ℕ) : Deducer := fun Γ Φ ψ ↦
        K.conjE (fun Γ Φ ψ ↦
          let (wToC, cToW) := (Φ.length - 2, Φ.length - 1)
          dConjE L hA (fun Γ Φ ψ ↦
            let (uToA, aToU) := (Φ.length - 2, Φ.length - 1)
            dConjE L hB (fun Γ Φ ψ ↦
              let (vToB, bToV) := (Φ.length - 2, Φ.length - 1)
              let forward (aTrue : Bool) : Deducer := dImpI L fun Γ Φ ψ ↦
                let hw := Φ.length - 1
                mp wToC (K.byHyp hw) (K.conjE fun Γ Φ ψ ↦
                  let (hu, hv) := (Φ.length - 2, Φ.length - 1)
                  if aTrue then mp vToB (K.byHyp hv) (fun Γ Φ ψ ↦
                    K.byHyp (Φ.length - 1) Γ Φ ψ) Γ Φ ψ
                  else mp uToA (K.byHyp hu) (fun Γ Φ ψ ↦
                    K.hypFalse (Φ.length - 1) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
              let backward (aTrue : Bool) : Deducer := dImpI L fun Γ Φ ψ ↦
                let hW := Φ.length - 1
                if aTrue then
                  mp aToU (K.solve 3) (fun Γ Φ ψ ↦
                    let hu := Φ.length - 1
                    mp bToV (K.byHyp hW) (fun Γ Φ ψ ↦
                      let hv := Φ.length - 1
                      mp cToW (K.norm (dConjI L (K.byHyp hu) (K.byHyp hv))) (fun Γ Φ ψ ↦
                        K.byHyp (Φ.length - 1) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
                else K.hypFalse hW Γ Φ ψ
              decideIn K okAt
                (linkK K "fields: the head's test false" <| K.norm <|
                  dConjI L (linkK K "fields: false forward" (forward false))
                    (linkK K "fields: false backward" (backward false)))
                (linkK K "fields: the head's test true" <| K.norm <|
                  dConjI L (linkK K "fields: true forward" (forward true))
                    (linkK K "fields: true backward" (backward true))) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ)
          Γ Φ ψ
      let guard (uBits vGuard wIff _uPos _vPos : ℕ) : Deducer :=
        dImpI L <| normLastK K <| K.conjE fun Γ Φ ψ ↦
          let (bHead, bRest) := (Φ.length - 2, Φ.length - 1)
          (dImpI L <| dImpI L fun Γ Φ ψ ↦
            let (en, bs) := (Φ.length - 2, Φ.length - 1)
            dAllE L K.G K.E uBits (qAt Γ) (K.impE (K.byHyp bHead) fun Γ Φ ψ ↦
              let hA := Φ.length - 1
              mp vGuard (K.byHyp bRest) (K.impE (K.byHyp en) (K.impE (K.byHyp bs)
                fun Γ Φ ψ ↦
                  let hB := Φ.length - 1
                  dCut (Φ.getD wIff Term.star) (nd (.hyp wIff))
                    (finish hA hB) Γ Φ ψ)) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
      main dPres tl₁ (fun a b c d e ↦ linkK K "fields: the children" (guard a b c d e)) Γ Φ ψ
    let cons : Deducer := all4 <| imp3 fun Γ Φ ψ ↦
      K.listCase treeTy (cs₁ Γ) (linkK K "fields: no children left" (noKids (Φ.length - 2)))
        (linkK K "fields: children left" (someKids (Φ.length - 2))) Γ Φ ψ
    let d₁ ← cons (Ls :: treeTy :: Γ₀.tail)
      (lowered.map Internal.weaken2 ++ [Internal.weakenElem φ])
      (Internal.listConsAt 1 treeTy φ)
    let thm : Internal.Thm := ⟨0, Γ₀, hyps, φ⟩
    pure (thm, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- That a list of trees has at least the number of elements of a list of field types: the
comparison of the lengths, as the writer's arity test makes it where a last field takes the rest. -/
def enoughT (P : Prog) (fts cs : Term) : Term :=
  apps ((primT Kernel.Prim.lt).getD Term.star) [pc P "Prelude.length" [fts],
    apps ((primT Kernel.Prim.add).getD Term.star) [pc P "Prelude.length" [cs], leafT (numeral 1)]]

/-- The walk's end, at the children left after the fields. -/
def atEndT (P : Prog) (ms flag rty fts cs : Term) : Term :=
  walkT P ms flag rty (nilT treeTy)
    (membershipsT P ms (dropT (call D.lab [] [pc P "Prelude.length" [fts]]) cs))

/-- The walk of a constructor's fields, where it holds, has enough children and its end holds: by
induction on the types, the children generalized and split. In the context of the types, the last
field's type and flag and the markers. -/
def walkEnough (P : Prog) (S : Defs) : Step :=
  ("walkEnough", fun ix E ↦ do
    let K := fieldsKit P S ix E
    let P := K.P
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    -- under the quantifier: the children v0, the types v1, the last type v2, the flag v3, the
    -- markers v4
    let φ := Internal.Logic.all o Ls (Term.lam Ls (Internal.Logic.imp o
      (truth o (walkT P (v 4) (v 3) (v 2) (v 1) (membershipsT P (v 4) (v 0))))
      (Internal.Logic.conj o (truth o (enoughT P (v 1) (v 0)))
        (truth o (atEndT P (v 4) (v 3) (v 2) (v 1) (v 0))))))
    let Γ₀ := [Ls, treeTy, treeTy, Ls]
    let d₀ ← linkK K "walkEnough: no types" (dAllI L <| dImpI L fun Γ Φ ψ ↦
        K.norm (dConjI L (K.solve 3) (K.byHyp (Φ.length - 1))) Γ Φ ψ) Γ₀.tail []
      (Term.subst φ fun i ↦ if i = 0 then nilT treeTy else v (i - 1))
    let cons : Deducer := dAllI L <| dImpI L fun Γ Φ ψ ↦
      let hw := Φ.length - 1
      let csAt := atPos (Γ.length - 1)
      K.listCase treeTy (csAt Γ)
        (linkK K "walkEnough: no children" (K.hypFalse hw))
        (linkK K "walkEnough: children" fun Γ Φ ψ ↦
          let tl := atPos (Γ.length - 1)
          let c := atPos (Γ.length - 2)
          let (msAt, hAt) := (atPos 0, atPos 3)
          decideIn K (fun Γ ↦ pc P "Typing.fieldOk" [msAt Γ, hAt Γ,
              pc P "Typing.memberships" [msAt Γ, c Γ]])
            (linkK K "walkEnough: the head false" (K.hypFalse hw))
            (linkK K "walkEnough: the head true" fun Γ Φ ψ ↦
              dAllE L K.G K.E 0 (tl Γ) (K.impE (K.byHyp hw) (K.conjE fun Γ Φ ψ ↦
                let (en, ae) := (Φ.length - 2, Φ.length - 1)
                K.norm (dConjI L (K.byHyp en) (K.byHyp ae)) Γ Φ ψ)) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
    let d₁ ← linkK K "walkEnough: construction" cons (Ls :: treeTy :: Γ₀.tail)
      [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, Γ₀, [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The arithmetic of the equality of numbers at successors: zero is no successor, and the equality
of successors is that of the numbers, by induction on the second as functions of the first; then
the instance at a number and its restatement in the normal form of the writer's kit. -/
def eqSuccLemmas (P : Prog) (S : Defs) : List Step :=
  let sc (t : Term) : Term := call D.succ [] [t]
  let eqZS := weakThm P 0 [bitsTy] (call D.eqB [] [bnilT, sc (v 0)]) bnilT
  let eqSucc : Internal.Thm := ⟨0, [bitsTy], [], Term.eq
    (Term.lam bitsTy (call D.eqB [] [sc (v 0), sc (v 1)]))
    (Term.lam bitsTy (call D.eqB [] [v 0, v 1]))⟩
  let rs (ix : String → ℕ) : List Internal.NormRule :=
    [.thm (ix "eqZeroSuccB") []] ++ rulesNth P ix
  let auto (ix : String → ℕ) (E : Array Internal.Entry) : Internal.Prover :=
    byAuto P.G E 0 (rs ix) 2 .open
  let side (a : Internal.Thm) (p : Internal.Prover) : Option Internal.Deriv :=
    p a.ctx [] (TranslationProofs.sides a).1 (TranslationProofs.sides a).2
  [step "eqZeroSuccB" eqZS (fun ix E ↦
      side eqZS (bitsCases P.G 0 (byAuto P.G E 0 (rulesNth P ix) 2 .open))),
    step "eqSuccB" eqSucc (fun ix E ↦
      let bit (i : ℕ) (p : Internal.Prover) : Internal.Prover := bySplit2 3 4 i p p
      side eqSucc (Internal.byListIndWith P.G 0 0 1
        (Internal.byFunExt P.G 0 (byAuto P.G E 0 (rs ix) 8 .open))
        (Internal.byFunExt P.G 0 (bit 2 (byListSplit P.G 0 1 (auto ix E)
          (bit 1 (auto ix E))))))),
    pointwise P rs .open "eqSuccPB" "eqSuccB" bitsTy,
    ("eqSuccK", fun ix E ↦ do
      let K := writerKit P S ix E
      let Γ := [bitsTy, bitsTy]
      let l ← nfE K.G E (K.rules []) Γ (call D.eqB [] [sc (v 1), sc (v 0)])
      let r ← nfE K.G E (K.rules []) Γ (call D.eqB [] [v 1, v 0])
      let thm : Internal.Thm := ⟨0, Γ, [], Term.eq l r⟩
      let some (Internal.Entry.language a) := E[ix "eqSuccPB"]? | none
      let σ := [v 1, v 0]
      let some d := dCut (Internal.instTerm [] σ a.concl) (nd (.apply (ix "eqSuccPB") [] σ))
          (normLastK K (linkK K "eqSuccK" K.byNorm)) thm.ctx thm.hyps thm.concl
        | dbgTrace "eqSuccK: not proved" fun _ ↦ none
      pure (thm, d))]

/-- An implication refuted by its hypothesis split on the bits it is blocked on, or proved by the
hypotheses. -/
def impSplit (K : Kit) : Deducer := fun Γ Φ ψ ↦
  (impAuto K Γ Φ ψ).orElse fun _ ↦
    dImpI K.L (fun Γ Φ ψ ↦
      let split (h : ℕ) : Deducer := K.splitHyp h (fun Γ Φ ψ ↦ K.auto 4 Γ Φ ψ) 6
      (K.conjE (fun Γ Φ ψ ↦ (split (Φ.length - 2) Γ Φ ψ).orElse fun _ ↦
        split (Φ.length - 1) Γ Φ ψ) Γ Φ ψ).orElse fun _ ↦ split (Φ.length - 1) Γ Φ ψ) Γ Φ ψ

/-- The children's number equal to that of the field types exactly where there are enough of them
and, no last field taking the rest, the walk's end holds: by induction on the types, the children
generalized and split, the equality at successors by {name}`eqSuccLemmas`. In the context of the
types, the last field's type and the markers. -/
def eqEnd (P : Prog) (S : Defs) : Step :=
  ("eqEnd", fun ix E ↦ do
    let K₀ := fieldsKit P S ix E
    let K : Kit := { K₀ with more := K₀.more ++ ["eqSuccK"] }
    let P := K.P
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    let eqT ← primT Kernel.Prim.eq
    let zero := leafT bnilT
    -- under the quantifier: the children v0, the types v1, the last type v2, the markers v3
    let φ := Internal.Logic.all o Ls (Term.lam Ls (iffT o
      (truth o (apps eqT [pc P "Prelude.length" [v 0], pc P "Prelude.length" [v 1]]))
      (Internal.Logic.conj o (truth o (enoughT P (v 1) (v 0)))
        (truth o (atEndT P (v 3) zero (v 2) (v 1) (v 0))))))
    let Γ₀ := [Ls, treeTy, Ls]
    let bothSplit : Deducer := K.norm <| dConjI L (impSplit K) (impSplit K)
    let d₀ ← (dAllI L fun Γ Φ ψ ↦ K.listCase treeTy (atPos (Γ.length - 1) Γ)
        (linkK K "eqEnd: no types, no children" bothSplit)
        (linkK K "eqEnd: no types, children" bothSplit) Γ Φ ψ) Γ₀.tail []
      (Term.subst φ fun i ↦ if i = 0 then nilT treeTy else v (i - 1))
    let cons : Deducer := dAllI L fun Γ Φ ψ ↦
      K.listCase treeTy (atPos (Γ.length - 1) Γ)
        (linkK K "eqEnd: types, no children" bothSplit)
        (linkK K "eqEnd: types and children" fun Γ Φ ψ ↦
          dAllE L K.G K.E 0 (atPos (Γ.length - 1) Γ)
            (fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
    let d₁ ← linkK K "eqEnd: construction" cons (Ls :: treeTy :: Γ₀.tail)
      [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, Γ₀, [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- A kernel term's node of a label over a list of terms. -/
def kNode (l : ℕ) (xs : List Term) : Term :=
  nodeT (Term.pair (numeral l) (xs.foldr (consT treeTy) (nilT treeTy)))

/-- The kernel's variable of an index. -/
def kVar (i : ℕ) : Term := kNode Kernel.Label.var [leafT (numeral i)]

/-- The kernel's type of a list of trees. -/
def kListT : Term := kNode Kernel.Label.tyList [tyTreeT]

/-- The kernel's term of the body of the writer's rest of a list of trees: the case analysis of the
variable, the empty list at the empty list and the rest at a construction. -/
def tailBody : Term :=
  appT (appT (appT (kNode Kernel.Label.lcase [tyTreeT, kListT]) (kVar 0))
    (kNode Kernel.Label.nil [tyTreeT]))
    (lamT tyTreeT (lamT kListT (kVar 0)))

/-- That the reader resolves an expression, its numeral abbreviations expanded, to a term, in the
context of a rule's variables. -/
def readIn (P : Prog) (vars : List Tree) (e t : Term) (scope : Option Term := none) : Term :=
  let at_ := denAt vars
  Term.eq (pc P "Reader.resolve" [at_ 3, at_ 2, pc P "Reader.expandNums" [at_ 1, e],
    scope.getD (at_ 4)]) (pc P "Prelude.some" [t])

/-- A rule of what the reader resolves one of the writer's forms to, in the context of a rule of
what a form denotes: from what it resolves its subexpressions to. -/
structure ReadRule where
  /-- The rule's name. -/
  name : String
  /-- The types of the rule's variables, the innermost first. -/
  vars : List Tree := []
  /-- The atoms no numeral abbreviation abbreviates. -/
  plain : List Term := []
  /-- The rule's further hypotheses. -/
  more : List Term := []
  /-- The form's subexpressions, each with its term and its scope, where not the form's. -/
  subs : List (Term × Term × Option Term) := []
  /-- The tests among the further hypotheses, each with its index among them, decided before the
  sides, false refuting the hypothesis. -/
  tests : List (ℕ × Term) := []
  /-- The form. -/
  form : Term
  /-- The term the form resolves to. -/
  term : Term

/-- The statement of a rule of what the reader resolves a form to. -/
def readThm (P : Prog) (r : ReadRule) : Internal.Thm :=
  let at_ := denAt r.vars
  let tests := r.plain.map fun a ↦
    pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev" [atomNameT a, at_ 1]]
  ⟨0, denCtx r.vars, tests.map (notTest P.o) ++ r.more ++
      r.subs.map (fun (e, t, sc) ↦ readIn P r.vars e t sc),
    readIn P r.vars r.form r.term⟩

/-- A rule of what the reader resolves a form to: the tests decided, true refuting their hypotheses,
the hypotheses normalized, and both sides by normalization with the reader's cases unfolded. -/
def readRule (P : Prog) (S : Defs) (T : Defs3) (r : ReadRule) : Step :=
  (r.name, fun ix E ↦ do
    let K := denKit P S ix E
    let P := K.P
    let thm := readThm P r
    let Γ₀ := thm.ctx
    let up (t : Term) (Γ : List Tree) : Term := sh (Γ.length - Γ₀.length) t
    let at_ := denAt r.vars
    let tests := r.plain.map fun a ↦
      pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev" [atomNameT a, at_ 1]]
    let unfold := resolveRules P T ix E ++ [.delta (T.argIdx 3)]
    let side : Deducer := fun Γ Φ ψ ↦
      (dEq (fun Γ Φ t u ↦ byMode .full K.G K.E 0 (K.rules Φ ++ unfold) Γ
        (rwHyps (K.rules Φ) Φ) t u) Γ Φ ψ).orElse fun _ ↦ do
        let (lhs, rhs) ← Internal.eqParts ψ
        let (l', _) ← evalRw K.G K.E (K.rules Φ ++ unfold) .full Γ Φ lhs
        let (r', _) ← evalRw K.G K.E (K.rules Φ ++ unfold) .full Γ Φ rhs
        dbgTrace s!"{r.name}: the sides: {(firstDiff l' r').map fun (a, b) ↦
          s!"{showT a}\n  vs {showT b}"}" fun _ ↦ none
    -- the hypotheses after the tests in normal form, in which their equations apply as rules
    let decided : Deducer := r.tests.foldr (fun (i, t) k ↦
      decideIn K (up t) (fun Γ Φ ψ ↦
        K.hypFalse (tests.length + i) Γ Φ ψ) k) side
    let normed : Deducer := (List.range (r.more.length + r.subs.length)).foldr (fun i k Γ Φ ψ ↦
      let h := tests.length + i
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ h) .full) h k Γ Φ ψ) decided
    let decisions : Deducer → Deducer := fun k ↦
      tests.zipIdx.foldr (fun (t, i) k ↦
        decideIn K (up t) k
          (linkK K s!"{r.name}: test {i} true" fun Γ Φ ψ ↦
            dImpE K.L i (K.solve 3) (fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ) Γ Φ ψ)) k
    let some d := decisions normed thm.ctx thm.hyps thm.concl
      | dbgTrace s!"{r.name}: not proved" fun _ ↦ none
    pure (thm, d))

/-- The names of a node's binders, as the reader takes them. -/
def binderNames (ps : Term) : Term :=
  let Ls := list treeTy
  foldrT treeTy Ls (Term.lam treeTy (Term.lam Ls (consT treeTy
    (apps ((primT Kernel.Prim.child).getD Term.star) [v 1, leafT bnilT]) (v 0)))) (nilT treeTy) ps

/-- The reader's scope of an abstraction's body: the binders' names, the last first, before the
scope. -/
def lamScope (P : Prog) (ps scope : Term) : Term :=
  pc P "Prelude.append" [pc P "Prelude.reverse" [binderNames ps], scope]

/-- The abstractions over a list of binders of the term of a body. -/
def lamsT (ps t : Term) : Term :=
  foldrT treeTy treeTy (Term.lam treeTy (Term.lam treeTy (lamT
    (apps ((primT Kernel.Prim.child).getD Term.star) [v 1, leafT (numeral 1)]) (v 0)))) t ps

/-- The reader's resolution of the writer's abstraction, from the reading of its binders, a form of
which nothing else is read, and its body's in the scope of their names. -/
def readLam (P : Prog) : ReadRule :=
  let vars := [list treeTy, treeTy, treeTy, treeTy]
  let at_ := denAt vars
  let (b, e, t, ps) := (at_ 6, at_ 7, at_ 8, at_ 9)
  let rLam := pc P "Recognize.rLam" []
  { name := "readLam", vars, plain := [rLam],
    more := [Term.eq (pc P "Reader.readBinders" [at_ 3, pc P "Reader.binders"
        [pc P "Reader.expandNums" [at_ 1, b]]]) (pc P "Prelude.some" [node0 ps]),
      truth P.o (pc P "Reader.nonEmpty" [ps])],
    subs := [(e, t, some (lamScope P ps (at_ 4)))],
    tests := [(1, pc P "Reader.nonEmpty" [ps])],
    form := pc P "Recognize.s3" [rLam, b, e], term := lamsT ps t }

/-- A number of successors of a natural number. -/
def succs (n : ℕ) (t : Term) : Term := (List.range n).foldr (fun _ t ↦ succN t) t

/-- The application at a level above a constant, in a context ending in the level and the relation's
context. -/
def tailApT (S : Defs) (Γ : List Tree) : Term :=
  Term.snd (S.levelN (Term.fst (atPos 0 Γ)) (succs 8 (atPos 1 Γ)))

/-- The closure of {name}`tailBody` at an environment. -/
def tailClo (P : Prog) (env : Term) : Term := pc P "Eval.valClo" [env, kListT, tailBody]

/-- The closure of {name}`tailBody` applied to a list value gives the list value of the list's
rest, at every level above a constant: the list split, each case by normalization. In the context
of the list, the closure's environment, the level and the relation's context. Both sides in normal
form. -/
def tailAp (P : Prog) (S : Defs) : Step :=
  ("tailAp", fun ix E ↦ do
    let K := denKit P S ix E
    let Ls := list treeTy
    let Γ := [Ls, Ls, nat, Defs3.ctxTy]
    let l ← nfE K.G E (K.rules []) Γ (apps (tailApT S Γ) [tailClo K.P (v 1), treeList K.P (v 0)])
    let r ← nfE K.G E (K.rules []) Γ (pc K.P "Prelude.some" [treeList K.P (Term.app tailFn (v 0))])
    let thm : Internal.Thm := ⟨0, Γ, [], Term.eq l r⟩
    let some d := K.listCase treeTy (v 0) (linkK K "tailAp: empty" K.byNorm)
        (linkK K "tailAp: construction" K.byNorm) thm.ctx thm.hyps thm.concl
      | dbgTrace "tailAp: not proved" fun _ ↦ none
    pure (thm, d))

/-- The evaluator's iteration of the closure of {name}`tailBody` from a list value, a number of
times given by a tree of a label. -/
def tailIter (P : Prog) (S : Defs) (Γ : List Tree) (env xs b : Term) : Term :=
  pc P "Eval.iterVal" [tailApT S Γ, tailClo P env, treeList P xs, leafT b]

/-- The iteration of {name}`tailBody`'s closure from the empty list value stays there: by induction
on the number's bits, the iteration of the rest's number applying the removal to its own result,
then the bit decided. In the context of the number, the environment, the level and the relation's
context. -/
def tailIterNil (P : Prog) (S : Defs) : Step :=
  ("tailIterNil", fun ix E ↦ do
    let K₀ := denKit P S ix E
    let K : Kit := { K₀ with more := K₀.more ++ ["tailAp"] }
    let Ls := list treeTy
    let Γ := [bitsTy, Ls, nat, Defs3.ctxTy]
    let goal := Term.eq (tailIter K.P S Γ (v 1) (nilT treeTy) (v 0))
      (pc K.P "Prelude.some" [treeList K.P (nilT treeTy)])
    let l ← nfE K.G E (K.rules []) Γ (Internal.eqParts goal |>.map Prod.fst |>.getD Term.star)
    let r ← nfE K.G E (K.rules []) Γ (Internal.eqParts goal |>.map Prod.snd |>.getD Term.star)
    let φ := Term.eq l r
    let byIH : Deducer := fun Γ Φ ψ ↦
      dRwBy (evalRw K.G K.E (.hyp 0 :: K.rules Φ) .full) (fun _ _ ψ ↦
        match Internal.eqParts ψ with
        | some (a, b) => if a == b then some (nd .join [nd .refl, nd .refl]) else none
        | none => none) Γ Φ ψ
    let d₀ ← linkK K "tailIterNil: zero" K.byNorm Γ.tail []
      (Term.subst φ (Internal.instVar (Term.arr 0 [bitTy] Term.star)))
    let d₁ ← linkK K "tailIterNil: a bit" (fun Γ Φ ψ ↦
        dRwHyp (evalRw K.G K.E (K.rulesEx Φ 0) .full) 0 (K.bitCase (v 1) byIH byIH) Γ Φ ψ)
      (list bitTy :: bitTy :: Γ.tail) [Internal.weakenElem φ] (Internal.listConsAt 1 bitTy φ)
    pure (⟨0, Γ, [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The iteration of {name}`tailBody`'s closure from a list value gives the list value of the list
after the removal of that number of elements: by induction on the list, the number generalized. The
empty list by {name}`tailIterNil` and {lit}`dropNil`. At a construction, the number empty, or a
successor ({lit}`bitsSucc`), by which the iteration and the removal are the rest's after one fewer
({lit}`rIterSucc`): the induction hypothesis at it. In the context of the list, the environment, the
level and the relation's context, under the number. -/
def tailIterList (P : Prog) (S : Defs) : Step :=
  ("tailIterList", fun ix E ↦ do
    let K₀ := denKit P S ix E
    let K : Kit := { K₀ with more := K₀.more ++ ["tailIterNil", "dropNil", "tailAp"] }
    let L := K.L
    let Ls := list treeTy
    let Γ := [Ls, Ls, nat, Defs3.ctxTy]
    let Γb := bitsTy :: Γ
    -- under the quantifier: the number v0, the list v1
    let φ := Internal.Logic.all K.P.o bitsTy (Term.lam bitsTy (Term.eq
      (tailIter K.P S Γb (v 2) (v 1) (v 0))
      (pc K.P "Prelude.some" [treeList K.P (dropT (v 0) (v 1))])))
    let d₀ ← (dAllI L (linkK K "tailIterList: empty" fun Γ Φ ψ ↦
        K.cutThm "tailIterNil" (fun Γ ↦ [atPos (Γ.length - 1) Γ, atPos 2 Γ, atPos 1 Γ, atPos 0 Γ])
          (fun Γ Φ ψ ↦ dRwHyp (evalRw K.G K.E (K.rules []) .full) (Φ.length - 1) (fun Γ Φ ψ ↦
            dRwBy (evalRw K.G K.E (K.rules []) .full) dHyp Γ Φ ψ) Γ Φ ψ) Γ Φ ψ)) Γ.tail []
      (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
    let some (Internal.Entry.language bs) := E[ix "bitsSucc"]? | none
    let succRules : List Internal.NormRule :=
      [.thm (ix "rIterSucc") [list treeTy], .thm (ix "rIterSucc") [treeTy]]
    let refl : Deducer := fun _ _ ψ ↦ match Internal.eqParts ψ with
      | some (a, b) => if a == b then some (nd .join [nd .refl, nd .refl]) else none
      | none => none
    let cons : Deducer := dAllI L fun Γ₁ Φ₁ ψ₁ ↦
      let n := atPos (Γ₁.length - 1)
      let cases := Internal.instTerm [] [n Γ₁] bs.concl
      let succ : Deducer := K.exE fun Γ Φ ψ ↦
        let pred := atPos (Γ.length - 1)
        dRwBy (evalRw K.G K.E (K.rules Φ ++ succRules) .full) (fun Γ Φ ψ ↦
          dAllE L K.G K.E 0 (pred Γ) (normLastK K fun Γ Φ ψ ↦
            dRwBy (evalRw K.G K.E (K.rules Φ ++ succRules) .full) refl Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
      dCut cases (nd (.apply (ix "bitsSucc") [] [n Γ₁]))
        (dDisjE L Φ₁.length (linkK K "tailIterList: the number empty" K.byNorm)
          (linkK K "tailIterList: a successor" succ)) Γ₁ Φ₁ ψ₁
    let d₁ ← linkK K "tailIterList: construction" cons (Ls :: treeTy :: Γ.tail)
      [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, Γ, [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The reader's resolution of one of the writer's atoms, from its index in the scope. -/
def readVar (P : Prog) (nm : String) (a : Term) : ReadRule :=
  let vars := [treeTy]
  let i := denAt vars 6
  { name := s!"readVar/{nm}", vars, plain := [a],
    more := [Term.eq (pc P "Reader.indexOf" [atomNameT a, denAt vars 4]) (pc P "Prelude.some" [i])],
    form := a, term := kNode Kernel.Label.var [i] }

/-- The reader's resolution of the writer's empty list of trees. -/
def readNil (P : Prog) : ReadRule :=
  { name := "readNil", plain := [pc P "Recognize.rNil" [], pc P "Recognize.rT" []],
    form := pc P "Recognize.s2" [pc P "Recognize.rNil" [], pc P "Recognize.rT" []],
    term := kNode Kernel.Label.nil [tyTreeT] }

/-- The reader's resolution of the writer's application of a constant over two types to three
expressions, the case analysis of lists or the right fold, from the types' readings and the
expressions' resolutions. -/
def readConst2 (P : Prog) (nm : String) (kw : Term) (label : ℕ) : ReadRule :=
  let Tt := treeTy
  let vars := [Tt, Tt, Tt, Tt, Tt, Tt, Tt, Tt, Tt, Tt]
  let at_ := denAt vars
  let (a₁, a₂, x₁, x₂, x₃, A, B, t₁, t₂, t₃) :=
    (at_ 6, at_ 7, at_ 8, at_ 9, at_ 10, at_ 11, at_ 12, at_ 13, at_ 14, at_ 15)
  let readT (a t : Term) : Term := Term.eq
    (pc P "Reader.readType" [at_ 3, pc P "Reader.expandNums" [at_ 1, a]]) (pc P "Prelude.some" [t])
  { name := s!"readConst2/{nm}", vars, plain := [kw], more := [readT a₁ A, readT a₂ B],
    subs := [(x₁, t₁, none), (x₂, t₂, none), (x₃, t₃, none)],
    form := pc P "Recognize.sx" [consT treeTy kw (consT treeTy a₁ (consT treeTy a₂
      (consT treeTy x₁ (consT treeTy x₂ (consT treeTy x₃ (nilT treeTy))))))],
    term := appT (appT (appT (kNode label [A, B]) t₁) t₂) t₃ }

/-- The writer's rest of a list as a form, its parts written out. -/
def tailForm (P : Prog) : Term :=
  let (rLam, rLcase, rT, tList) := (pc P "Recognize.rLam" [], pc P "Recognize.rLcase" [],
    pc P "Recognize.rT" [], pc P "Recognize.tList" [])
  let (vX, vH, vU) := (pc P "Recognize.vX" [], pc P "Recognize.vH" [], pc P "Recognize.vU" [])
  pc P "Recognize.s3" [rLam, pc P "Recognize.bind1" [vX, tList],
    pc P "Recognize.sx" [consT treeTy rLcase (consT treeTy rT (consT treeTy tList (consT treeTy vX
      (consT treeTy (pc P "Recognize.s2" [pc P "Recognize.rNil" [], rT])
        (consT treeTy (pc P "Recognize.s3" [rLam, pc P "Recognize.bind2" [vH, rT, vU, tList], vU])
          (nilT treeTy))))))]]

/-- The writer's rest of a list denotes the closure of its environment over {name}`tailBody`: its
forms read from the inside, each by a rule of one level, the abstraction evaluating at once. -/
def denTail (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("denTail", fun ix E ↦ do
    let K := denKit P S ix E
    let P := K.P
    let L := K.L
    let at_ := denAt []
    let (rLam, rLcase, rT, rList, rNil) := (pc P "Recognize.rLam" [], pc P "Recognize.rLcase" [],
      pc P "Recognize.rT" [], pc P "Recognize.rList" [], pc P "Recognize.rNil" [])
    let (vX, vH, vU) := (pc P "Recognize.vX" [], pc P "Recognize.vH" [], pc P "Recognize.vU" [])
    let tList := pc P "Recognize.tList" []
    let atoms := [rLam, vX, rList, rT, rLcase, rNil, vH, vU]
    let isAbbrev (a : Term) : Term :=
      pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev" [atomNameT a, at_ 1]]
    let thm : Internal.Thm := ⟨0, denCtx [], atoms.map fun a ↦ notTest P.o (isAbbrev a),
      denIn P S [] (tailForm P) (tailClo P (at_ 5))⟩
    let Γ₀ := thm.ctx
    let up (t : Term) (Γ : List Tree) : Term := sh (Γ.length - Γ₀.length) t
    let binder (a t : Term) : Term := kNode 0 [atomNameT a, t]
    let ps₁ := consT treeTy (binder vX kListT) (nilT treeTy)
    let ps₂ := consT treeTy (binder vH tyTreeT) (consT treeTy (binder vU kListT) (nilT treeTy))
    let fx (sc : List Tree → Term) (Γ : List Tree) : List Term :=
      [atPos 5 Γ, sc Γ, atPos 3 Γ, atPos 2 Γ, atPos 1 Γ, atPos 0 Γ]
    let s₀ (Γ : List Tree) : Term := atPos 4 Γ
    let s₁ (Γ : List Tree) : Term := lamScope P ps₁ (s₀ Γ)
    let s₂ (Γ : List Tree) : Term := lamScope P ps₂ (s₁ Γ)
    let zero := leafT (numeral 0)
    let bind₁ := pc P "Recognize.bind1" [vX, tList]
    let bind₂ := pc P "Recognize.bind2" [vH, rT, vU, tList]
    let lam₂ := lamsT ps₂ (kVar 0)
    let inner := pc P "Recognize.s3" [rLam, bind₂, vU]
    let nilF := pc P "Recognize.s2" [rNil, rT]
    let lcaseF := pc P "Recognize.sx" [consT treeTy rLcase (consT treeTy rT (consT treeTy tList
      (consT treeTy vX (consT treeTy nilF (consT treeTy inner (nilT treeTy))))))]
    let nilK := kNode Kernel.Label.nil [tyTreeT]
    let body := appT (appT (appT (kNode Kernel.Label.lcase [tyTreeT, kListT]) (kVar 0)) nilK) lam₂
    let Y := lamsT ps₁ body
    let unfold := resolveRules P T ix E ++ [.delta (T.argIdx 3)]
    let byU (msg : String) : Deducer := linkK K s!"denTail: {msg}" fun Γ Φ ψ ↦
      dEq (fun Γ Φ t u ↦ byMode .full K.G K.E 0 (K.rules Φ ++ unfold) Γ
        (rwHyps (K.rules Φ) Φ) t u) Γ Φ ψ
    let chain : Deducer :=
      applyThm K "readVar/u" (fun Γ ↦ zero :: fx s₂ Γ) [K.byHyp 7, byU "u's index"] <|
      applyThm K "readLam" (fun Γ ↦ [ps₂, kVar 0, vU, bind₂] ++ fx s₁ Γ)
        [K.byHyp 0, byU "the second binders",
          linkK K "denTail: nonempty" (K.solve 3), linkK K "denTail: u's reading" dHyp] <|
      applyThm K "readVar/x" (fun Γ ↦ zero :: fx s₁ Γ) [K.byHyp 1, byU "x's index"] <|
      applyThm K "readNil" (fx s₁) [K.byHyp 5, K.byHyp 3] <|
      applyThm K "readConst2/lcase" (fun Γ ↦ [lam₂, nilK, kVar 0, kListT, tyTreeT, inner, nilF, vX,
          tList, rT] ++ fx s₁ Γ)
        [K.byHyp 4, byU "the first type", byU "the second type", dHyp, dHyp, dHyp] <|
      applyThm K "readLam" (fun Γ ↦ [ps₁, body, lcaseF, bind₁] ++ fx s₀ Γ)
        [K.byHyp 0, byU "the first binders", K.solve 3, dHyp] <|
      fun Γ Φ ψ ↦ dExI L K.G K.E Y (dConjI L dHyp
        (dConv L K.G K.E S (succN zeroN) (up (tailClo P (at_ 5)) Γ)
          (linkK K "denTail: stable" K.byNorm) (linkK K "denTail: the value" (K.solve 3)))) Γ Φ ψ
    let decisions : Deducer → Deducer := fun k ↦
      atoms.zipIdx.foldr (fun (a, i) k ↦
        decideIn K (up (isAbbrev a)) k
          (linkK K s!"denTail: test {i} true" fun Γ Φ ψ ↦
            dImpE L i (K.solve 3) (fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ) Γ Φ ψ)) k
    let some d := decisions chain thm.ctx thm.hyps thm.concl
      | dbgTrace "denTail: not proved" fun _ ↦ none
    pure (thm, d))

/-- The reader's resolution of the writer's iteration, from the type's reading and the expressions'
resolutions. -/
def readIter (P : Prog) : ReadRule :=
  let Tt := treeTy
  let vars := [Tt, Tt, Tt, Tt, Tt, Tt, Tt, Tt]
  let at_ := denAt vars
  let (a, f, z, n, A, tf, tz, tn) :=
    (at_ 6, at_ 7, at_ 8, at_ 9, at_ 10, at_ 11, at_ 12, at_ 13)
  let rIter := pc P "Recognize.rIter" []
  { name := "readIter", vars, plain := [rIter],
    more := [Term.eq (pc P "Reader.readType" [at_ 3, pc P "Reader.expandNums" [at_ 1, a]])
      (pc P "Prelude.some" [A])],
    subs := [(f, tf, none), (z, tz, none), (n, tn, none)],
    form := pc P "Recognize.sx" [consT treeTy rIter (consT treeTy a (consT treeTy f
      (consT treeTy z (consT treeTy n (nilT treeTy)))))],
    term := appT (appT (appT (kNode Kernel.Label.iter [A]) tf) tz) tn }

/-- The writer's iteration at a type of an expression from an expression, a number of times given by
an expression. -/
def iterForm (P : Prog) (a f r e : Term) : Term :=
  pc P "Recognize.sx" [consT treeTy (pc P "Recognize.rIter" []) (consT treeTy a (consT treeTy f
    (consT treeTy r (consT treeTy e (nilT treeTy)))))]

/-- The writer's iteration, by an expression denoting the closure of the rest of a list, from one
denoting a list value, a number of times one denotes the quotation of, denotes the list value after
the removal of that number of elements: at levels a constant above the sum of the thresholds, the
iteration of the closure ({name}`tailIterList`). The type's reading is given, a form of which
nothing else is read. -/
def denDrop (P : Prog) (S0 : Defs) : DenRule :=
  let vars := [list treeTy, treeTy, treeTy, treeTy, treeTy, treeTy, treeTy]
  let at_ := denAt vars
  let (a, A, f, r, e, n, rs) := (at_ 6, at_ 7, at_ 8, at_ 9, at_ 10, at_ 11, at_ 12)
  let value := treeList P (dropT (call D.lab [] [n]) rs)
  { name := "denDrop", vars, plain := [pc P "Recognize.rIter" []],
    more := [Term.eq (pc P "Reader.readType" [at_ 3, pc P "Reader.expandNums" [at_ 1, a]])
      (pc P "Prelude.some" [A])],
    subs := [sub f (tailClo P (at_ 5)), sub r (treeList P rs), sub e (quoteV P n)],
    form := iterForm P a f r e, value, levels := 10, rules := apNames "apIter" 3,
    finish := some fun K sum Γ Φ ψ ↦
      let k := atPos (Γ.length - 1)
      (K.cutThm "tailIterList" (fun Γ ↦ [atPos 12 Γ, atPos 5 Γ, S0.add (sum Γ) (k Γ), atPos 0 Γ]) <|
        K.allEΓ (fun Γ ↦ call D.lab [] [atPos 11 Γ]) <| normLastK K fun Γ Φ ψ ↦
          linkK K "denDrop: the value" K.byNorm Γ Φ ψ) Γ Φ ψ }

/-- The closure of the writer's step of the test of the rest of a constructor's children: two
abstractions, over a child's bits and the test so far, over a body. -/
def restClo (P : Prog) (env tB : Term) : Term :=
  pc P "Eval.valClo" [env, tyTreeT, lamT tyTreeT tB]

/-- The statement of the fold of the test of the rest of a constructor's children. In the context of
the children, the body's term, the function of a child's bits, the last field's type, the closure,
the markers, the closure's environment and the relation's context: there is a bit to which the right
fold of the closure of the step over the quotations of the children's bits converges from the
numeral one, which, where each child holds its bits, is true exactly where the walk's end holds. -/
def restφ (P : Prog) (S : Defs) (cs : Term) : Term :=
  let o := P.o
  let imp := Internal.Logic.imp o
  -- beneath the bit v0: the context's variables, the children first
  let (tB, R, rty, cl, ms, env, Dv) := (v 2, v 3, v 4, v 5, v 6, v 7, v 8)
  let csI := sh 1 cs
  let F := Term.lam nat (pc P "Eval.foldrVal" [Term.snd (S.levelN (Term.fst (sh 1 Dv)) (v 0)),
    restClo P (sh 1 env) (sh 1 tB), quoteV P (leafT (numeral 1)),
    quotesT P (mapFnT (sh 1 R) (sh 1 csI))])
  let bitsAll := S.allL (Term.lam treeTy (bitsOkT P (sh 1 ms) (sh 1 cl)
    (Term.app (sh 1 R) (v 0)) (pc P "Typing.memberships" [sh 1 ms, v 0]))) csI
  let atEnd := walkT P ms (leafT (numeral 1)) rty (nilT treeTy) (membershipsT P ms csI)
  Internal.Logic.ex o treeTy (Term.lam treeTy (Internal.Logic.conj o
    (S.conv F (Term.lam treeTy (Term.eq (v 0) (quoteV P (v 1)))))
    (imp bitsAll (iffT o (truth o (v 0)) (truth o atEnd)))))

/-- The hypothesis of the fold of the test of the rest of a constructor's children: at each bit so
far and child's bits, the step's body converges to a quotation which, at memberships the child's
bits hold, is true exactly where the bit so far and the field's test are. In the context after the
children of {name}`restφ`. -/
def restBodyT (P : Prog) (S : Defs) (tB _R rty cl ms env Dv : Term) : Term :=
  let o := P.o
  let Ls := list treeTy
  -- beneath the bit v0, the child's bits v1 and the bit so far v2
  let F := Term.lam nat (S.evN (Term.fst (sh 4 Dv)) (v 0)
    (consT treeTy (quoteV P (v 3)) (consT treeTy (quoteV P (v 2)) (sh 4 env))) (sh 4 tB))
  let spec := Internal.Logic.all o Ls (Term.lam Ls (Internal.Logic.imp o
    (bitsOkT P (sh 4 ms) (sh 4 cl) (v 2) (v 0))
    (iffT o (truth o (v 1)) (Internal.Logic.conj o (truth o (v 3))
      (truth o (pc P "Typing.fieldOk" [sh 4 ms, sh 4 rty, v 0]))))))
  Internal.Logic.all o treeTy (Term.lam treeTy (Internal.Logic.all o treeTy (Term.lam treeTy
    (Internal.Logic.ex o treeTy (Term.lam treeTy (Internal.Logic.conj o
      (S.conv F (Term.lam treeTy (Term.eq (v 0) (quoteV P (v 1))))) spec))))))

/-- The fold of the test of the rest of a constructor's children ({name}`restφ`): by induction on
the children. No children: the numeral one at once, the walk's end true. A construction: the
induction hypothesis's bit and the body's at it and the head's bits, the sum of their thresholds a
constant below the level at which the fold evaluates; at memberships the bits hold, the head's test
decided, each direction through it. In the context of {name}`restφ`. -/
def restFold (P : Prog) (S : Defs) : Step :=
  ("restFold", fun ix E ↦ do
    let K := fieldsKit P S ix E
    let P := K.P
    let L := K.L
    let Ls := list treeTy
    let Γ₀ := [Ls, treeTy, exp treeTy treeTy, treeTy, Ls, Ls, Ls, Defs3.ctxTy]
    let φ := restφ P S (v 0)
    let hyp := restBodyT P S (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)
    let some lowered := Internal.lowerHyps P.G 0 Γ₀.tail [hyp]
      | dbgTrace "restFold: the hypothesis" fun _ ↦ none
    let (msAt, rtyAt, RAt) := (atPos 2, atPos 4, atPos 5)
    let one := leafT (numeral 1)
    let d₀ ← (fun Γ Φ ψ ↦ dExI L K.G K.E one (dConjI L
        (K.conv (fun _ ↦ zeroN) (fun _ ↦ quoteV P one)
          (linkK K "restFold: empty stable" K.byNorm) (linkK K "restFold: empty value" (K.solve 3)))
        (dImpI L (linkK K "restFold: empty truth" (iffAuto K)))) Γ Φ ψ) Γ₀.tail lowered
      (Term.subst φ fun i ↦ if i = 0 then nilT treeTy else v (i - 1))
    let cAt := atPos 7
    let qAt (Γ : List Tree) : Term := pc P "Typing.memberships" [msAt Γ, cAt Γ]
    let okAt (Γ : List Tree) : Term := pc P "Typing.fieldOk" [msAt Γ, rtyAt Γ, qAt Γ]
    let mp (h : ℕ) (prem k : Deducer) : Deducer := dImpE L h prem k
    let lastHyp : Deducer := fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ
    -- the head's test decided, the equivalences' implications at their indices
    let decide (uTo toU vTo toV : ℕ) : Deducer :=
      let forward (aTrue : Bool) : Deducer := dImpI L fun Γ Φ ψ ↦
        let hu := Φ.length - 1
        mp uTo (K.byHyp hu) (K.conjE fun Γ Φ ψ ↦
          let (hv, ha) := (Φ.length - 2, Φ.length - 1)
          if aTrue then mp vTo (K.byHyp hv) lastHyp Γ Φ ψ else K.hypFalse ha Γ Φ ψ) Γ Φ ψ
      let backward (aTrue : Bool) : Deducer := dImpI L fun Γ Φ ψ ↦
        let hW := Φ.length - 1
        if aTrue then
          mp toV (K.byHyp hW) (fun Γ Φ ψ ↦
            let hv := Φ.length - 1
            mp toU (K.norm (dConjI L (K.byHyp hv) (K.solve 3))) lastHyp Γ Φ ψ) Γ Φ ψ
        else K.hypFalse hW Γ Φ ψ
      decideIn K okAt
        (linkK K "restFold: the head false" <| K.norm <|
          dConjI L (forward false) (backward false))
        (linkK K "restFold: the head true" <| K.norm <|
          dConjI L (forward true) (backward true))
    -- the truth at memberships the bits hold
    let guard (specH guardI : ℕ) : Deducer :=
      dImpI L <| normLastK K <| K.conjE fun Γ Φ ψ ↦
        let (bHead, bRest) := (Φ.length - 2, Φ.length - 1)
        dAllE L K.G K.E specH (qAt Γ) (K.impE (K.byHyp bHead) <| K.conjE fun Γ Φ ψ ↦
          let (uTo, toU) := (Φ.length - 2, Φ.length - 1)
          mp guardI (K.byHyp bRest) (K.conjE fun Γ Φ ψ ↦
            let (vTo, toV) := (Φ.length - 2, Φ.length - 1)
            decide uTo toU vTo toV Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
    -- the bit and the convergence, the stabilities at the sum
    let finish (uPos nA nB a b specH guardI : ℕ) : Deducer := fun Γ Φ ψ ↦
      dExI L K.G K.E (atPos uPos Γ) (dConjI L
        (K.conv (fun Γ ↦ succs 2 (S.add (atPos nA Γ) (atPos nB Γ)))
          (fun Γ ↦ quoteV P (atPos uPos Γ))
          (linkK K "restFold: stable" <|
            instNK K a (fun _ ↦ succs 2 (v 0)) <|
            instNK K b (fun _ ↦ succs 1 (v 0)) (linkK K "restFold: the fold" K.byNorm))
          (linkK K "restFold: the value" (K.solve 3)))
        (linkK K "restFold: the truth" (guard specH guardI))) Γ Φ ψ
    let shifted (uPos nA sA nB sB specH guardI : ℕ) : Deducer :=
      shiftK K sA false (atPos nB) fun Γ Φ ψ ↦
        let a := Φ.length - 1
        shiftK K sB true (atPos nA) (fun Γ Φ ψ ↦
          finish uPos nA nB a (Φ.length - 1) specH guardI Γ Φ ψ) Γ Φ ψ
    let bodyAt (nA sA guardI : ℕ) : Deducer := K.exE <| K.conjE fun Γ Φ ψ ↦
      let (uPos, cvB, specH) := (Γ.length - 1, Φ.length - 2, Φ.length - 1)
      dRwHyp (evalRw K.G K.E [.delta (S.q + 2)] .head) cvB (K.exE <| K.exE <| K.conjE
        fun Γ Φ ψ ↦
        let (nB, sB) := (Γ.length - 2, Φ.length - 2)
        normLastK K (shifted uPos nA sA nB sB specH guardI) Γ Φ ψ) Γ Φ ψ
    let cons : Deducer := fun Γ₁ Φ₁ ψ₁ ↦
      dExE L K.G K.E (Φ₁.length - 1) (K.conjE fun Γ Φ ψ ↦
        let (v₁, cvI, guardI) := (Γ.length - 1, Φ.length - 2, Φ.length - 1)
        dRwHyp (evalRw K.G K.E [.delta (S.q + 2)] .head) cvI (K.exE <| K.exE <| K.conjE
          fun Γ Φ ψ ↦
          let (nA, sA) := (Γ.length - 2, Φ.length - 2)
          normLastK K (fun Γ Φ ψ ↦
            dAllE L K.G K.E 0 (atPos v₁ Γ) (K.allEΓ (fun Γ ↦ Term.app (RAt Γ) (cAt Γ))
              (bodyAt nA sA guardI)) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ) Γ₁ Φ₁ ψ₁
    let d₁ ← linkK K "restFold: construction" cons (Ls :: treeTy :: Γ₀.tail)
      (lowered.map Internal.weaken2 ++ [Internal.weakenElem φ]) (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, Γ₀, [hyp], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The removal of a number of elements from the quotations of the map of a function is that of the
removal: by induction on the list, as {name}`headDropMap`. In the context of the list, under the
function and the number. -/
def dropQuotes (P : Prog) (S : Defs) : Step :=
  ("dropQuotes", fun ix E ↦ do
    let K₀ := denKit P S ix E
    let K : Kit := { K₀ with more := K₀.more ++ ["dropNil"] }
    let L := K.L
    let Fn := exp treeTy treeTy
    let Ls := list treeTy
    let qm (g xs : Term) : Term := quotesT K.P (mapFnT g xs)
    -- under the quantifiers: the number v0, the function v1, the list v2
    let φ := Internal.Logic.all K.P.o Fn (Term.lam Fn (Internal.Logic.all K.P.o bitsTy
      (Term.lam bitsTy (Term.eq (dropT (v 0) (qm (v 1) (v 2))) (qm (v 1) (dropT (v 0) (v 2)))))))
    let d₀ ← linkK K "dropQuotes: empty" (dAllI L (dAllI L K.byNorm)) [] []
      (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
    let some (Internal.Entry.language bs) := E[ix "bitsSucc"]? | none
    let cons : Deducer := dAllI L <| dAllI L fun Γ₁ Φ₁ ψ₁ ↦
      let (g, n) := (atPos 2, atPos 3)
      let cases := Internal.instTerm [] [n Γ₁] bs.concl
      let succ : Deducer := K.exE fun Γ Φ ψ ↦
        let pred := atPos (Γ.length - 1)
        dAllE L K.G K.E 0 (g Γ) (K.allEΓ pred (normLastK K
          (linkK K "dropQuotes: the successor" K.byNorm))) Γ Φ ψ
      dCut cases (nd (.apply (ix "bitsSucc") [] [n Γ₁]))
        (dDisjE L Φ₁.length (linkK K "dropQuotes: the number empty" K.byNorm) succ) Γ₁ Φ₁ ψ₁
    let d₁ ← linkK K "dropQuotes: construction" cons [Ls, treeTy] [Internal.weakenElem φ]
      (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, [Ls], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The writer's abstraction over two binders denotes the closure of its environment over the
abstraction of the second over the body's term, from the binders' reading and the body's. The
binders' reading is given, a form of which nothing else is read. -/
def denLam2 (P : Prog) : DenRule :=
  let Tt := treeTy
  let vars := [Tt, Tt, Tt, Tt, Tt, Tt, Tt]
  let at_ := denAt vars
  let (b, e, x, A, y, B, t) := (at_ 6, at_ 7, at_ 8, at_ 9, at_ 10, at_ 11, at_ 12)
  let rLam := pc P "Recognize.rLam" []
  let ps := consT treeTy (kNode 0 [x, A]) (consT treeTy (kNode 0 [y, B]) (nilT treeTy))
  { name := "denLam2", vars, plain := [rLam],
    more := [Term.eq (pc P "Reader.readBinders" [at_ 3, pc P "Reader.binders"
        [pc P "Reader.expandNums" [at_ 1, b]]]) (pc P "Prelude.some" [node0 ps]),
      Term.eq (pc P "Reader.resolve" [at_ 3, at_ 2, pc P "Reader.expandNums" [at_ 1, e],
        consT treeTy y (consT treeTy x (at_ 4))]) (pc P "Prelude.some" [t])],
    form := pc P "Recognize.s3" [rLam, b, e],
    value := pc P "Eval.valClo" [at_ 5, A, lamT B t], levels := 1 }

/-- The writer's right fold of the test of the rest of a constructor's children, by an expression
denoting a function, denotes the quotation of the bit to which the fold of the function converges
({name}`restFold`): at levels two above the sum of the thresholds, the fold's application a level
below. The types' readings are given. -/
def denFoldr (P : Prog) (S0 : Defs) : DenRule :=
  let Tt := treeTy
  let Ls := list treeTy
  let vars := [Tt, exp Tt Tt, Ls, Tt, Tt, Tt, Tt, Tt, Tt, Tt, Tt]
  let at_ := denAt vars
  let (a₁, A, a₂, B, f, z, d, clo, cs, R, u) :=
    (at_ 6, at_ 7, at_ 8, at_ 9, at_ 10, at_ 11, at_ 12, at_ 13, at_ 14, at_ 15, at_ 16)
  let rFoldr := pc P "Recognize.rFoldr" []
  let readT (a t : Term) : Term := Term.eq
    (pc P "Reader.readType" [at_ 3, pc P "Reader.expandNums" [at_ 1, a]]) (pc P "Prelude.some" [t])
  let qs := quotesT P (mapFnT R cs)
  let F := Term.lam nat (pc P "Eval.foldrVal" [Term.snd (S0.levelN (Term.fst (sh 1 (at_ 0))) (v 0)),
    sh 1 clo, quoteV P (leafT (numeral 1)), sh 1 qs])
  { name := "denFoldr", vars, plain := [rFoldr], more := [readT a₁ A, readT a₂ B],
    subs := [sub f clo, sub z (quoteV P (leafT (numeral 1))), sub d (treeList P qs)],
    convs := [(S0.conv F (Term.lam treeTy (Term.eq (v 0) (quoteV P (sh 1 u)))), 0)],
    form := pc P "Recognize.sx" [consT treeTy rFoldr (consT treeTy a₁ (consT treeTy a₂
      (consT treeTy f (consT treeTy z (consT treeTy d (nilT treeTy))))))],
    value := quoteV P u, levels := 2,
    rules := apNames "apFoldr" 3 ++ ["listOfOf"] }

/-- The writer's scope and environment of the body of the step of the test of the rest of a
constructor's children: the bit so far before the child's bits, before those of the context. -/
def restScope (P : Prog) (scope : Term) : Term :=
  consT treeTy (atomNameT (pc P "Recognize.vA" [])) (consT treeTy
    (atomNameT (pc P "Recognize.vC" [])) scope)

/-- The writer's conditional of the test of a child's bits with the bit so far. -/
def restBodyForm (P : Prog) (cl rty : Term) : Term :=
  let t := pc P "Prelude.get" [pc P "Recognize.fieldTest" [cl, rty, pc P "Recognize.vC" []]]
  pc P "Recognize.s4" [pc P "Recognize.rIf" [], t, pc P "Recognize.vA" [],
    pc P "Recognize.zero" []]

/-- The writer's conditional of the step of the test of the rest of a constructor's children, at any
bit so far and child's bits, denotes a bit true exactly where the bit so far and the field's test
are, at memberships the child's bits hold: the child's test by {name}`fieldDen` at the variable of
the child's bits, the conditional by the rule of conditionals. In the context of the fixed
variables but the environment's first two values, with the bit so far, the child's bits, the last
field's type, the closure and the markers. -/
def restBodyDen (P : Prog) (S : Defs) : Step :=
  ("restBodyDen", fun ix E ↦ do
    let K := fieldsKit P S ix E
    let P := K.P
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    let vars := [treeTy, treeTy, treeTy, Ls, Ls]
    let at_ := denAt vars
    let (cl, ms, rty, x, r) := (at_ 6, at_ 7, at_ 8, at_ 9, at_ 10)
    let rChild := pc P "Recognize.rChild" []
    let (vA, vC) := (pc P "Recognize.vA" [], pc P "Recognize.vC" [])
    let plain (a : Term) : Term :=
      notTest o (pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev" [atomNameT a, at_ 1]])
    let scope₂ := restScope P (at_ 4)
    let env₂ := consT treeTy (quoteV P x) (consT treeTy (quoteV P r) (at_ 5))
    let test := pc P "Recognize.fieldTest" [cl, rty, vC]
    let atoms := [rChild, pc P "Recognize.one" [], pc P "Recognize.zero" [],
      pc P "Recognize.rIf" [], vA, vC]
    let hyps : List Term :=
      [truth o (pc P "Prelude.isSome" [test]), noTreeMarkerT P ms, numT P (at_ 1),
        notTest o (pc P "Prelude.isSome" [pc P "Reader.indexOf" [atomNameT rChild, at_ 4]]),
        notTest o (pc P "Prelude.isSome" [pc P "Reader.indexOf" [atomNameT rChild, at_ 2]])] ++
      atoms.map plain
    -- beneath the bit v0
    let concl := Internal.Logic.ex o treeTy (Term.lam treeTy (Internal.Logic.conj o
      (denT P S (sh 1 (at_ 0)) (sh 1 (at_ 3)) (sh 1 (at_ 2)) (sh 1 (at_ 1)) (sh 1 scope₂)
        (sh 1 env₂) (sh 1 (restBodyForm P cl rty)) (quoteV P (v 0)))
      (Internal.Logic.all o Ls (Term.lam Ls (Internal.Logic.imp o
        (bitsOkT P (sh 2 ms) (sh 2 cl) (sh 2 r) (v 0))
        (iffT o (truth o (v 1)) (Internal.Logic.conj o (truth o (sh 2 x))
          (truth o (pc P "Typing.fieldOk" [sh 2 ms, sh 2 rty, v 0])))))))))
    let thm : Internal.Thm := ⟨0, denCtx vars, hyps, concl⟩
    let fxIn (Γ : List Tree) : List Term :=
      [consT treeTy (quoteV P (atPos 9 Γ)) (consT treeTy (quoteV P (atPos 10 Γ)) (atPos 5 Γ)),
        restScope P (atPos 4 Γ), atPos 3 Γ, atPos 2 Γ, atPos 1 Γ, atPos 0 Γ]
    let unfold : List Internal.NormRule := (lookupEqNames.filter fun nm ↦
      0 < ix nm ∧ ix nm < E.size).map fun nm ↦ .thm (ix nm) []
    let byU : Deducer := fun Γ Φ ψ ↦
      dEq (fun Γ Φ t u ↦ byMode .full K.G K.E 0 (K.rules Φ ++ unfold ++
          [.delta (P.idx "Reader.indexOf")]) Γ (rwHyps (K.rules Φ) Φ) t u) Γ Φ ψ
    let zero := pc P "Recognize.zero" []
    let getTest (Γ : List Tree) : Term := pc P "Prelude.get"
      [pc P "Recognize.fieldTest" [atPos 6 Γ, atPos 8 Γ, vC]]
    let denV : Deducer :=
      -- the variables of the bit so far and of the child's bits, by their indices
      applyThm K "denVar/a" (fun Γ ↦ [quoteV P (atPos 9 Γ), leafT (numeral 0)] ++ fxIn Γ)
        [K.byHyp 9, linkK K "restBodyDen: a's index" byU,
          linkK K "restBodyDen: a's value" K.byNorm] <|
      applyThm K "denVar/c" (fun Γ ↦ [quoteV P (atPos 10 Γ), leafT (numeral 1)] ++ fxIn Γ)
        [K.byHyp 10, linkK K "restBodyDen: c's index" byU,
          linkK K "restBodyDen: c's value" K.byNorm] <|
      applyThm K "denDigit/zero" fxIn [K.byHyp 7] <|
      applyThm K "fieldDen" (fun Γ ↦ [atPos 10 Γ, vC, atPos 8 Γ, atPos 7 Γ, atPos 6 Γ] ++ fxIn Γ)
        [K.byHyp 0, dHyp, dHyp, dHyp,
          linkK K "restBodyDen: child absent" (dImpI L fun Γ Φ ψ ↦
            let hp := Φ.length - 1
            -- the name's presence in the scope's tail decided: refuted, or unfolding refutes
            decideIn K (fun Γ ↦ pc P "Prelude.isSome" [pc P "Reader.indexOf"
                [atomNameT rChild, atPos 4 Γ]])
              (fun Γ Φ ψ ↦ dRwHyp (evalRw K.G K.E (K.rulesEx Φ hp ++ unfold) .full) hp
                (dFalse K.L dHyp) Γ Φ ψ)
              (dImpE L 3 (K.solve 3) fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ) Γ Φ ψ),
          K.byHyp 4, K.byHyp 5, K.byHyp 6] <|
      K.exE <| K.conjE fun Γ Φ ψ ↦
        let (uPos, uBits) := (Γ.length - 1, Φ.length - 1)
        let uAt := atPos uPos
        let value (Γ : List Tree) : Term :=
          condT treeTy (call D.lab [] [uAt Γ]) (atPos 9 Γ) (leafT (numeral 0))
        (applyThm K "denIf" (fun Γ ↦ [leafT (numeral 0), atPos 9 Γ, uAt Γ, zero, vA, getTest Γ] ++
            fxIn Γ) [K.byHyp 8, dHyp, dHyp, dHyp] fun Γ Φ ψ ↦
          dExI L K.G K.E (value Γ) (dConjI L dHyp
            (linkK K "restBodyDen: the spec" <| dAllI L <| dImpI L fun Γ Φ ψ ↦
              dAllE L K.G K.E uBits (atPos (Γ.length - 1) Γ) (K.impE (K.byHyp (Φ.length - 1))
                (K.conjE fun Γ Φ ψ ↦
                  let (uTo, toU) := (Φ.length - 2, Φ.length - 1)
                  let lastFalse : Deducer := fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ
                  decideIn K uAt
                    (K.norm <| dConjI L (dImpI L lastFalse)
                      (dImpI L (K.conjE fun Γ Φ ψ ↦
                        dImpE L toU (K.byHyp (Φ.length - 1)) lastFalse Γ Φ ψ)))
                    (K.norm <| dConjI L
                      (dImpI L fun Γ Φ ψ ↦
                        let hx := Φ.length - 1
                        dImpE L uTo (K.solve 3) (fun Γ Φ ψ ↦
                          K.norm (dConjI L (K.byHyp hx) (K.byHyp (Φ.length - 1))) Γ Φ ψ) Γ Φ ψ)
                      (dImpI L (K.conjE fun Γ Φ ψ ↦ K.byHyp (Φ.length - 2) Γ Φ ψ))) Γ Φ ψ))
                Γ Φ ψ)) Γ Φ ψ) Γ Φ ψ
    let some d := linkK K "restBodyDen" denV thm.ctx thm.hyps thm.concl
      | dbgTrace "restBodyDen: not proved" fun _ ↦ none
    pure (thm, d))

/-- The atoms the writer's terms name, the names of the recognizers' forms. -/
def writerAtoms : List String :=
  ["rChild", "one", "zero", "rIf", "vA", "vC", "rLam", "vX", "rList", "rT", "rLcase", "rNil", "vH",
    "vU", "rIter", "rFoldr", "rEq", "rLt", "rAdd", "rArity", "vN", "vR", "vL", "vT", "rLet",
    "rCons", "rNode", "rFold"]

/-- The primitives the writer's terms name. -/
def writerPrims : List String := ["rChild", "rArity", "rEq", "rLt", "rAdd", "rNode"]

/-- The hypotheses of the writer's larger forms, at the fixed variables of a context: the markers
{lit}`ms` name no trees' type, the numerals read as themselves, each primitive's name in neither
the scope nor the definitions' names, and no atom the writer's terms name abbreviated. -/
def writerHyps (P : Prog) (ms at1 at2 at4 : Term) : List Term :=
  [noTreeMarkerT P ms, numT P at1] ++
  writerPrims.flatMap (fun a ↦
    (absentTests P (pc P s!"Recognize.{a}" []) at4 at2).map (notTest P.o)) ++
  writerAtoms.map fun a ↦ notTest P.o (pc P "Prelude.isSome"
    [pc P "Reader.lookupAbbrev" [atomNameT (pc P s!"Recognize.{a}" []), at1]])

/-- The index, after a number of hypotheses, of the hypothesis that a writer's atom is not
abbreviated ({name}`writerHyps`). -/
def atomHyp (base : ℕ) (a : String) : ℕ :=
  base + 2 + 2 * writerPrims.length + writerAtoms.idxOf a

/-- The index, after a number of hypotheses, of the first of the two hypotheses that a primitive's
name is absent ({name}`writerHyps`). -/
def primHyp (base : ℕ) (a : String) : ℕ := base + 2 + 2 * writerPrims.idxOf a

/-- The writer's right fold of the test of the rest of a constructor's children as a form, the
expressions of the abstraction's binders and body and of the removal given. -/
def restForm (P : Prog) (cl rty nf : Term) : Term :=
  let (rT, tList) := (pc P "Recognize.rT" [], pc P "Recognize.tList" [])
  let (vA, vC) := (pc P "Recognize.vA" [], pc P "Recognize.vC" [])
  pc P "Recognize.sx" [consT treeTy (pc P "Recognize.rFoldr" []) (consT treeTy rT (consT treeTy rT
    (consT treeTy (pc P "Recognize.s3" [pc P "Recognize.rLam" [],
        pc P "Recognize.bind2" [vC, rT, vA, rT], restBodyForm P cl rty])
      (consT treeTy (pc P "Recognize.one" []) (consT treeTy
        (iterForm P tList (tailForm P) (pc P "Recognize.vR" []) (pc P "Recognize.num" [nf]))
        (nilT treeTy))))))]

/-- The writer's test of the rest of a constructor's children denotes a bit which, where the
children left after the fields hold their bits, is true exactly where the walk's end holds. The
step's body's term from its denotation at a first environment ({name}`restBodyDen`), the same at
every other by the reading's equation; the fold ({name}`restFold`); the abstraction, the removal
and the fold constant by their rules. -/
def restDen (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("restDen", fun ix E ↦ do
    -- the writer's builders unfolded, in concrete forms of a level
    let Kd := denKit P S ix E
    let K := fieldsKit P S ix E
    let P := K.P
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    let Fn := exp treeTy treeTy
    let vars := [treeTy, Fn, Ls, treeTy, Ls, Ls]
    let at_ := denAt vars
    let (cl, ms, rty, cs, R, nf) := (at_ 6, at_ 7, at_ 8, at_ 9, at_ 10, at_ 11)
    let atomT (a : String) : Term := pc P s!"Recognize.{a}" []
    let (vC, vR, rT) := (atomT "vC", atomT "vR", atomT "rT")
    let test := pc P "Recognize.fieldTest" [cl, rty, vC]
    let qs := quotesT P (mapFnT R cs)
    let left := dropT (call D.lab [] [nf]) cs
    let hyps : List Term := [truth o (pc P "Prelude.isSome" [test]),
        denIn P S vars vR (treeList P qs),
        denIn P S vars (pc P "Recognize.num" [nf]) (quoteV P nf)] ++
      writerHyps P ms (at_ 1) (at_ 2) (at_ 4)
    let bitsAll : Term := S.allL (Term.lam treeTy (bitsOkT P (sh 2 ms) (sh 2 cl)
      (Term.app (sh 2 R) (v 0)) (pc P "Typing.memberships" [sh 2 ms, v 0]))) (sh 1 left)
    let atEnd := walkT P (sh 1 ms) (leafT (numeral 1)) (sh 1 rty) (nilT treeTy)
      (membershipsT P (sh 1 ms) (sh 1 left))
    let concl := Internal.Logic.ex o treeTy (Term.lam treeTy (Internal.Logic.conj o
      (denT P S (sh 1 (at_ 0)) (sh 1 (at_ 3)) (sh 1 (at_ 2)) (sh 1 (at_ 1)) (sh 1 (at_ 4))
        (sh 1 (at_ 5)) (sh 1 (restForm P cl rty nf)) (quoteV P (v 0)))
      (Internal.Logic.imp o bitsAll (iffT o (truth o (v 0)) (truth o atEnd)))))
    let thm : Internal.Thm := ⟨0, denCtx vars, hyps, concl⟩
    let base := 3
    let (clAt, msAt, rtyAt, csAt, RAt, nfAt) :=
      (atPos 6, atPos 7, atPos 8, atPos 9, atPos 10, atPos 11)
    let hA (a : String) : Deducer := K.byHyp (atomHyp base a)
    let unfold := resolveRules P T ix E ++ [.delta (T.argIdx 3)]
    let byU (msg : String) : Deducer := fun Γ Φ ψ ↦
      (dEq (fun Γ Φ t u ↦ byMode .full Kd.G Kd.E 0 (Kd.rules Φ ++ unfold) Γ
        (rwHyps (Kd.rules Φ) Φ) t u) Γ Φ ψ).orElse fun _ ↦ do
        let (lhs, rhs) ← Internal.eqParts ψ
        let (l', _) ← evalRw Kd.G Kd.E (Kd.rules Φ ++ unfold) .full Γ Φ lhs
        let (r', _) ← evalRw Kd.G Kd.E (Kd.rules Φ ++ unfold) .full Γ Φ rhs
        dbgTrace s!"restDen: {msg}: {(firstDiff l' r').map fun (a, b) ↦
          s!"{showT a}\n  vs {showT b}"}" fun _ ↦ none
    let getT (t : Term) : Term := pc P "Prelude.get" [t]
    -- the premises of the body's denotation at the bit so far and the child's bits
    let bodyAt (r x : List Tree → Term) (k : Deducer) : Deducer :=
      applyThm K "restBodyDen" (fun Γ ↦ [r Γ, x Γ, rtyAt Γ, msAt Γ, clAt Γ] ++ denFixed Γ)
        [K.byHyp 0, dHyp, dHyp, K.byHyp (base + 2), K.byHyp (base + 3), hA "rChild", hA "one",
          hA "zero", hA "rIf", hA "vA", hA "vC"] k
    let zero := leafT (numeral 0)
    let isAbbrev (a : String) (Γ : List Tree) : Term := pc P "Prelude.isSome"
      [pc P "Reader.lookupAbbrev" [atomNameT (atomT a), atPos 1 Γ]]
    -- the atoms' abbreviations decided, true refuting their hypotheses
    let decided (names : List String) (k : Deducer) : Deducer :=
      names.foldr (fun a k ↦ decideIn K (isAbbrev a) k
        (dImpE L (atomHyp base a) (K.solve 3) fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ)) k
    let lastFold (t₀ : ℕ) : Deducer :=
      let tOf := atPos t₀
      applyThm K "restFold" (fun Γ ↦ [dropT (call D.lab [] [nfAt Γ]) (csAt Γ), tOf Γ, RAt Γ,
          rtyAt Γ, clAt Γ, msAt Γ, atPos 5 Γ, atPos 0 Γ]) [dHyp] <|
      K.exE <| K.conjE fun Γ Φ ψ ↦
        let (vPos, guardI) := (Γ.length - 1, Φ.length - 1)
        let tList := pc P "Recognize.tList" []
        let bindF := pc P "Recognize.bind2" [vC, rT, atomT "vA", rT]
        let leftAt (Γ : List Tree) : Term := dropT (call D.lab [] [nfAt Γ]) (csAt Γ)
        let qsAt (Γ : List Tree) : Term := quotesT P (mapFnT (RAt Γ) (csAt Γ))
        let numAt (Γ : List Tree) : Term := pc P "Recognize.num" [nfAt Γ]
        let bodyF (Γ : List Tree) : Term := restBodyForm P (clAt Γ) (rtyAt Γ)
        let lamF (Γ : List Tree) : Term :=
          pc P "Recognize.s3" [atomT "rLam", bindF, bodyF Γ]
        let iterF (Γ : List Tree) : Term := iterForm P tList (tailForm P) vR (numAt Γ)
        let cloAt (Γ : List Tree) : Term := restClo P (atPos 5 Γ) (tOf Γ)
        (decided ["vC", "vA", "rT", "rList"] <|
        applyThm K "denLam2" (fun Γ ↦ [tOf Γ, tyTreeT, atomNameT (atomT "vA"), tyTreeT,
            atomNameT vC, bodyF Γ, bindF] ++ denFixed Γ)
          [hA "rLam", byU "the binders", linkK K "restDen: the body's reading" K.byNorm] <|
        applyThm K "denTail" denFixed [hA "rLam", hA "vX", hA "rList", hA "rT", hA "rLcase",
          hA "rNil", hA "vH", hA "vU"] <|
        applyThm K "denDrop" (fun Γ ↦ [qsAt Γ, nfAt Γ, numAt Γ, vR, tailForm P, kListT, tList] ++
            denFixed Γ)
          [hA "rIter", byU "the list's type", linkK K "restDen: the rest's closure" dHyp,
            linkK K "restDen: the children" dHyp, linkK K "restDen: the number" dHyp] <|
        fun Γ Φ ψ ↦
        let dDrop := Φ.length - 1
        K.cutThm "dropQuotes" (fun Γ ↦ [csAt Γ]) (K.allEΓ RAt (K.allEΓ
          (fun Γ ↦ call D.lab [] [nfAt Γ]) fun Γ Φ ψ ↦
          let eqn := Φ.length - 1
          dRwHyp (evalRw K.G K.E [.hyp eqn] .full) dDrop (fun Γ Φ ψ ↦
            applyThm K "denDigit/one" denFixed [hA "one"] (
            applyThm K "denFoldr" (fun Γ ↦ [atPos vPos Γ, RAt Γ, leftAt Γ, cloAt Γ, iterF Γ,
                atomT "one", lamF Γ, tyTreeT, rT, tyTreeT, rT] ++ denFixed Γ)
              [hA "rFoldr", byU "the first type", byU "the second type",
                linkK K "restDen: the abstraction" dHyp, linkK K "restDen: one" dHyp,
                linkK K "restDen: the removal" dHyp, linkK K "restDen: the fold" dHyp]
              fun Γ Φ ψ ↦
              dExI L K.G K.E (atPos vPos Γ) (dConjI L (linkK K "restDen: the conclusion" dHyp)
                (linkK K "restDen: the guard" fun Γ Φ ψ ↦
                  (dHyp Γ Φ ψ).orElse fun _ ↦ K.byHyp guardI Γ Φ ψ)) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ)) Γ Φ ψ)
        Γ Φ ψ
    -- the body's hypothesis at the term of the first denotation
    let hStep : Deducer :=
      dAllI L <| dAllI L fun Γ₁ Φ₁ ψ₁ ↦
      let (x, r) := (atPos (Γ₁.length - 2), atPos (Γ₁.length - 1))
      bodyAt r x (K.exE <| K.conjE fun Γ Φ ψ ↦
        let (uPos, dU, spec) := (Γ.length - 1, Φ.length - 2, Φ.length - 1)
        denE K dU (fun _ n _ st Γ Φ ψ ↦
          K.image (Φ.length - 1) getT (fun Γ Φ ψ ↦
            dExI L K.G K.E (atPos uPos Γ) (dConjI L
              (K.conv (atPos n) (fun Γ ↦ quoteV P (atPos uPos Γ))
                (linkK K "restDen: the body stable" <| instNK K st (fun _ ↦ v 0) K.byNorm)
                (linkK K "restDen: the body's value" (K.solve 3)))
              (linkK K "restDen: the body's spec" fun Γ Φ ψ ↦
                (dHyp Γ Φ ψ).orElse fun _ ↦ K.byHyp spec Γ Φ ψ)) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ) Γ₁ Φ₁ ψ₁
    let main : Deducer :=
      bodyAt (fun _ ↦ zero) (fun _ ↦ zero) <| K.exE <| K.conjE fun Γ Φ ψ ↦
        denE K (Φ.length - 2) (fun t₀ _ _ _ ↦ fun Γ Φ ψ ↦
          let hT (Γ : List Tree) : Term := restBodyT P S (atPos t₀ Γ) (RAt Γ) (rtyAt Γ) (clAt Γ)
            (msAt Γ) (atPos 5 Γ) (atPos 0 Γ)
          do
            let dH ← hStep Γ Φ (hT Γ)
            dCut (hT Γ) dH (lastFold t₀) Γ Φ ψ) Γ Φ ψ
    let some d := linkK K "restDen" main thm.ctx thm.hyps thm.concl
      | dbgTrace "restDen: not proved" fun _ ↦ none
    pure (thm, d))

/-- The development of the walk of a constructor's fields: the denotation's determinacy and
congruence, the field's and the conjunction's denotations, the arithmetic of the walk's number, the
walk, the comparisons of its lengths, the rest of a list. -/
def walkDev (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  [denDet P S, denCong P S, fieldDen P S, conjDen P S, lenFromSucc P S, lenFromSuccR P S,
    subOneK P S,
    fieldsCount P S, allSomeCons P S true, allSomeCons P S false, allSomeKids P S, dropTail P S,
    fieldsWalk P S, walkEnough P S] ++ eqSuccLemmas P S ++ [eqEnd P S] ++
    ([readLam P].map (readRule P S T)) ++ [tailAp P S, tailIterNil P S, tailIterList P S] ++
    ([readVar P "u" (pc P "Recognize.vU" []), readVar P "x" (pc P "Recognize.vX" []), readNil P,
      readConst2 P "lcase" (pc P "Recognize.rLcase" []) Kernel.Label.lcase].map (readRule P S T)) ++
    [denTail P S T] ++ ([readIter P].map (readRule P S T)) ++
    [denRule P S T (denDrop P S), restFold P S, dropQuotes P S, denRule P S T (denLam2 P),
      denRule P S T (denFoldr P S), restBodyDen P S, restDen P S T]

/-- The declarations the walk's development continues from. -/
def walkAfter (P : Prog) (S : Defs) (T : Defs3) : Option (List String) := do
  let names ← caseNames P S T
  pure (names ++ (caseDev P S T).map (·.1) ++ (clausesDev P S T).map (·.1) ++
    (caseSoundDev P S T).map (·.1) ++ (denDev P S T).map (·.1))

/-- The development of {name}`walkDev`, after {name}`walkAfter`, stored as the certificate
{lit}`datatype-walk`. -/
def walkCertificates (P : Prog) (S : Defs) (T : Defs3) (before : List Internal.Thm) :
    Except String (List Stored.Cert) := do
  let some names := walkAfter P S T | throw "the base is not stated"
  certifyAfter P names "datatype-walk" (walkDev P S T) before

/-- The number of elements of a list's map is that of the list: by induction on the list. In the
context of the list and the function. Both sides in the normal form of the walk's kit. -/
def lenMap (P : Prog) (S : Defs) : Step :=
  ("lenMap", fun ix E ↦ do
    let K := fieldsKit P S ix E
    let Γ := [list treeTy, exp treeTy treeTy]
    let l ← nfE K.G E (K.rules []) Γ (pc K.P "Prelude.length" [mapFnT (v 1) (v 0)])
    let r ← nfE K.G E (K.rules []) Γ (pc K.P "Prelude.length" [v 0])
    let φ := Term.eq l r
    let d₀ ← linkK K "lenMap: empty" K.byNorm Γ.tail []
      (Term.subst φ fun i ↦ if i = 0 then nilT treeTy else v (i - 1))
    let d₁ ← linkK K "lenMap: construction" (fun Γ Φ ψ ↦
        dRwHyp (evalRw K.G K.E (K.rulesEx Φ 0) .full) 0 K.byNorm Γ Φ ψ)
      (list treeTy :: treeTy :: Γ.tail) [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, Γ, [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The label of the arity of a node over a list's map is that of the list's number of elements:
by induction on the list. In the context of the list and the function. Both sides in the normal form
of the walk's kit. -/
def arityMap (P : Prog) (S : Defs) : Step :=
  ("arityMap", fun ix E ↦ do
    let K := fieldsKit P S ix E
    let arityT ← primT Kernel.Prim.arity
    let Γ := [list treeTy, exp treeTy treeTy]
    let l ← nfE K.G E (K.rules []) Γ (call D.lab [] [apps arityT [node0 (mapFnT (v 1) (v 0))]])
    let r ← nfE K.G E (K.rules []) Γ (call D.lab [] [pc K.P "Prelude.length" [v 0]])
    let φ := Term.eq l r
    let d₀ ← linkK K "arityMap: empty" K.byNorm Γ.tail []
      (Term.subst φ fun i ↦ if i = 0 then nilT treeTy else v (i - 1))
    let d₁ ← linkK K "arityMap: construction" (fun Γ Φ ψ ↦
        dRwHyp (evalRw K.G K.E (K.rulesEx Φ 0) .full) 0 K.byNorm Γ Φ ψ)
      (list treeTy :: treeTy :: Γ.tail) [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, Γ, [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- Each element of a list satisfying a predicate, each element after the removal of any number
does: by induction on the list, the number generalized, empty or a successor. In the context of the
list and the predicate. -/
def allDrop (P : Prog) (S : Defs) : Step :=
  ("allDrop", fun ix E ↦ do
    let K₀ := denKit P S ix E
    let K : Kit := { K₀ with more := K₀.more ++ ["dropNil"] }
    let L := K.L
    let o := K.P.o
    let Pred := exp treeTy omega
    let φ := Internal.Logic.all o bitsTy (Term.lam bitsTy (Internal.Logic.imp o
      (S.allL (v 2) (v 1)) (S.allL (v 2) (dropT (v 0) (v 1)))))
    let d₀ ← linkK K "allDrop: empty" (dAllI L (dImpI L (K.solve 3))) [Pred] []
      (Term.subst φ fun i ↦ if i = 0 then nilT treeTy else v (i - 1))
    let some (Internal.Entry.language bs) := E[ix "bitsSucc"]? | none
    let cons : Deducer := dAllI L <| dImpI L fun Γ₁ Φ₁ ψ₁ ↦
      let hy := Φ₁.length - 1
      let n := atPos (Γ₁.length - 1)
      let cases := Internal.instTerm [] [n Γ₁] bs.concl
      let succ : Deducer := K.exE fun Γ Φ ψ ↦
        let pred := atPos (Γ.length - 1)
        dRwHyp (evalRw K.G K.E (K.rulesEx Φ hy) .full) hy (K.conjE fun Γ Φ ψ ↦
          let tl := Φ.length - 1
          dAllE L K.G K.E 0 (pred Γ) (K.impE (K.byHyp tl) fun Γ Φ ψ ↦
            K.byHyp (Φ.length - 1) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
      dCut cases (nd (.apply (ix "bitsSucc") [] [n Γ₁]))
        (dDisjE L Φ₁.length (linkK K "allDrop: the number empty" (K.byHyp hy))
          (linkK K "allDrop: a successor" succ)) Γ₁ Φ₁ ψ₁
    let d₁ ← linkK K "allDrop: construction" cons [list treeTy, treeTy, Pred]
      [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, [list treeTy, Pred], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- A last field of the trees' type holds of any children: the field's test at each true, as no
marker has that name. By induction on the children. In the context of the children, the last
field's type and the markers. -/
def allTrees (P : Prog) (S : Defs) : Step :=
  ("allTrees", fun ix E ↦ do
    let K := fieldsKit P S ix E
    let P := K.P
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    let one := leafT (numeral 1)
    let φ := truth o (walkT P (v 2) one (v 1) (nilT treeTy) (membershipsT P (v 2) (v 0)))
    let Γ := [Ls, treeTy, Ls]
    let hyps := [noTreeMarkerT P (v 2), truth o (pc P "Reader.named" [v 1, pc P "Reader.kwT" []])]
    let some lowered := Internal.lowerHyps P.G 0 Γ.tail hyps
      | dbgTrace "allTrees: the hypotheses" fun _ ↦ none
    let d₀ ← linkK K "allTrees: empty" (K.solve 3) Γ.tail lowered
      (Term.subst φ fun i ↦ if i = 0 then nilT treeTy else v (i - 1))
    let (msAt, rtyAt) := (atPos 0, atPos 1)
    let cons : Deducer := fun Γ Φ ψ ↦
      let okDelta : List Internal.NormRule := [.delta (P.idx "Typing.fieldOk")]
      decideIn K (fun Γ ↦ pc P "Prelude.isSome" [pc P "Reader.indexOf"
          [rtyAt Γ, pc P "Typing.markerNames" [msAt Γ]]])
        (linkK K "allTrees: not a marker's" fun Γ Φ ψ ↦ do
          -- the head's test true, by its unfolding at the index absent
          let okEq := Term.eq (pc P "Typing.fieldOk" [msAt Γ, rtyAt Γ,
            pc P "Typing.memberships" [msAt Γ, atPos 2 Γ]]) one
          let dOk ← dEq (fun Γ Φ t u ↦ byMode .full K.G K.E 0 (K.rules Φ ++ okDelta) Γ
            (rwHyps (K.rules Φ) Φ) t u) Γ Φ okEq
          dCut okEq dOk (normLastK K (K.byHyp 2)) Γ Φ ψ)
        (linkK K "allTrees: a marker's" fun Γ Φ ψ ↦
          dAllE L K.G K.E 0 (rtyAt Γ) (K.impE (K.solve 3) (K.impE (K.byHyp 1) fun Γ Φ ψ ↦
            K.hypFalse (Φ.length - 1) Γ Φ ψ)) Γ Φ ψ) Γ Φ ψ
    let d₁ ← linkK K "allTrees: construction" cons (Ls :: treeTy :: Γ.tail)
      (lowered.map Internal.weaken2 ++ [Internal.weakenElem φ]) (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, Γ, hyps, φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The context of the writer's test of a constructor: the children, the function of a child's bits,
the constructor, the markers and the closure. -/
def ctorVars : List Tree :=
  [list treeTy, exp treeTy treeTy, treeTy, list treeTy, list treeTy]

/-- The field types, the flag of a last field and its type, of a constructor. -/
def ctorParts (c : Term) : Term × Term × Term :=
  let childT := (primT Kernel.Prim.child).getD Term.star
  let childrenT := (primT Kernel.Prim.children).getD Term.star
  (apps childrenT [apps childT [c, leafT (numeral 1)]], apps childT [c, leafT (numeral 2)],
    apps childT [c, leafT (numeral 3)])

/-- The statement of the writer's test of a constructor: where the writer gives one, it denotes a
bit which, where the children hold their bits, is true exactly where the walk of the fields holds.
-/
def ctorThm (P : Prog) (S : Defs) : Internal.Thm :=
  let vars := ctorVars
  let at_ := denAt vars
  let (cl, ms, c, R, cs) := (at_ 6, at_ 7, at_ 8, at_ 9, at_ 10)
  let test := pc P "Recognize.ctorTest" [cl, c]
  let (fts, flag, rty) := ctorParts c
  let bitsAll : Term := S.allL (Term.lam treeTy (bitsOkT P (sh 2 ms) (sh 2 cl)
    (Term.app (sh 2 R) (v 0)) (pc P "Typing.memberships" [sh 2 ms, v 0]))) (sh 1 cs)
  let walk := walkT P (sh 1 ms) (sh 1 flag) (sh 1 rty) (sh 1 fts)
    (membershipsT P (sh 1 ms) (sh 1 cs))
  ⟨0, denCtx vars,
    [truth P.o (pc P "Prelude.isSome" [test]),
      denIn P S vars (pc P "Recognize.vN" []) (quoteV P (node0 (mapFnT R cs))),
      denIn P S vars (pc P "Recognize.vR" []) (treeList P (quotesT P (mapFnT R cs)))] ++
      writerHyps P ms (at_ 1) (at_ 2) (at_ 4),
    Internal.Logic.ex P.o treeTy (Term.lam treeTy (Internal.Logic.conj P.o
      (denT P S (sh 1 (at_ 0)) (sh 1 (at_ 3)) (sh 1 (at_ 2)) (sh 1 (at_ 1)) (sh 1 (at_ 4))
        (sh 1 (at_ 5)) (sh 1 (pc P "Prelude.get" [test])) (quoteV P (v 0)))
      (Internal.Logic.imp P.o bitsAll (iffT P.o (truth P.o (v 0)) (truth P.o walk)))))⟩

/-- The writer's test of a constructor ({name}`ctorThm`). Its last field's flag decided. No last
field: the arity's equality, the walk at the numeral one ({name}`fieldsWalk`), and their conjunction
({name}`conjDen`), the equality exactly where there are enough children and the walk's end holds
({name}`eqEnd`, {name}`walkEnough`). -/
def ctorDen (P : Prog) (S : Defs) : Step :=
  ("ctorDen", fun ix E ↦ do
    let K₀ := fieldsKit P S ix E
    let K : Kit := { K₀ with
      P := { K₀.P with folded := K₀.P.folded.filter (· != "Reader.both") }
      more := K₀.more ++ ["lenMap", "arityMap"] }
    let P := K.P
    let L := K.L
    let thm := ctorThm P S
    let base := 3
    let (clAt, msAt, cAt, RAt, csAt) := (atPos 6, atPos 7, atPos 8, atPos 9, atPos 10)
    let hA (a : String) : Deducer := K.byHyp (atomHyp base a)
    let hAbs (a : String) : List Deducer :=
      [K.byHyp (primHyp base a), K.byHyp (primHyp base a + 1), hA a]
    let atomT (a : String) : Term := pc P s!"Recognize.{a}" []
    let lastHyp : Deducer := fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ
    let eqT ← primT Kernel.Prim.eq
    let arityT ← primT Kernel.Prim.arity
    let ftsAt (Γ : List Tree) : Term := (ctorParts (cAt Γ)).1
    let flagAt (Γ : List Tree) : Term := (ctorParts (cAt Γ)).2.1
    let rtyAt (Γ : List Tree) : Term := (ctorParts (cAt Γ)).2.2
    let nfAt (Γ : List Tree) : Term := pc P "Prelude.length" [ftsAt Γ]
    let nodeAt (Γ : List Tree) : Term := node0 (mapFnT (RAt Γ) (csAt Γ))
    let arityE (_ : List Tree) : Term := pc P "Recognize.s2" [atomT "rArity", atomT "vN"]
    let numE (Γ : List Tree) : Term := pc P "Recognize.num" [nfAt Γ]
    let arityV (Γ : List Tree) : Term := apps arityT [nodeAt Γ]
    -- the numeral of the number of fields, its denotation the last hypothesis
    let withNum (k : Deducer) : Deducer := fun Γ Φ ψ ↦
      dAllE L K.G K.E (base + 1) (nfAt Γ) (normLastK K <| K.conjE fun Γ₁ Φ₁ ψ₁ ↦
        let h₁ := Φ₁.length - 2
        K.conjE (fun Γ₂ Φ₂ ψ₂ ↦
          applyThm K "denNum" (fun Γ ↦ nfAt Γ :: denFixed Γ) [K.byHyp h₁, K.byNorm,
            K.byHyp (Φ₂.length - 1)] k Γ₂ Φ₂ ψ₂) Γ₁ Φ₁ ψ₁) Γ Φ ψ
    let withArity (k : Deducer) : Deducer :=
      applyThm K "denPrim1/arity" (fun Γ ↦ [nodeAt Γ, atomT "vN"] ++ denFixed Γ)
        (hAbs "rArity" ++ [dHyp]) k
    -- the walk of the fields from the expression vt denoting the tree y
    let walkAt (vt y : List Tree → Term) (k : ℕ → ℕ → ℕ → Deducer) : Deducer :=
      applyThm K "fieldsWalk" (fun Γ ↦ [ftsAt Γ, rtyAt Γ, flagAt Γ, RAt Γ, csAt Γ, msAt Γ,
          clAt Γ] ++ denFixed Γ)
        ([dHyp, dHyp, dHyp] ++ hAbs "rChild" ++ [hA "one", hA "zero", hA "rIf"]) <|
      K.allEΓ (fun _ ↦ bnilT) <| K.allEΓ csAt <| K.allEΓ vt <| K.allEΓ y <|
      K.impE (linkK K "ctorDen: the walk's start" K.byNorm) <|
      K.impE (linkK K "ctorDen: the tests' presence" (K.solve 3)) <|
      K.impE dHyp <| K.exE <| K.conjE fun Γ Φ ψ ↦
        k (Γ.length - 1) (Φ.length - 2) (Φ.length - 1) Γ Φ ψ
    let allOf (Γ : List Tree) : Term := fieldsAll P (clAt Γ) bnilT (ftsAt Γ)
    let mp (h : ℕ) (prem k : Deducer) : Deducer := dImpE L h prem k
    let one := leafT (numeral 1)
    -- the truth with no last field: the conjunction's bit through the arity's equality and the walk
    let truthNoRest (wIff vGuard : ℕ) : Deducer :=
      dImpI L fun Γ Φ ψ ↦
      let hb := Φ.length - 1
      (K.cutThm "eqEnd" (fun Γ ↦ [ftsAt Γ, rtyAt Γ, msAt Γ]) <| K.allEΓ csAt <| K.conjE
        fun Γ Φ ψ ↦
        let (eTo, toE) := (Φ.length - 2, Φ.length - 1)
        K.cutThm "walkEnough" (fun Γ ↦ [ftsAt Γ, rtyAt Γ, flagAt Γ, msAt Γ]) (K.allEΓ csAt
          fun Γ Φ ψ ↦
          let we := Φ.length - 1
          dConjE L wIff (fun Γ Φ ψ ↦
            let (wToC, cToW) := (Φ.length - 2, Φ.length - 1)
            let iff1 (ae : ℕ) : Deducer := K.norm <|
              dConjI L (dImpI L (K.byHyp ae)) (dImpI L (K.solve 3))
            let walkIff (en ae : ℕ) (k : ℕ → ℕ → Deducer) : Deducer :=
              mp vGuard (K.byHyp hb) (K.impE (K.byHyp en) (K.impE (iff1 ae) (K.conjE fun Γ Φ ψ ↦
                k (Φ.length - 2) (Φ.length - 1) Γ Φ ψ)))
            let forward : Deducer := dImpI L fun Γ Φ ψ ↦
              let hw := Φ.length - 1
              mp wToC (K.byHyp hw) (K.conjE fun Γ Φ ψ ↦
                let (ha, hv) := (Φ.length - 2, Φ.length - 1)
                mp eTo (K.byHyp ha) (K.conjE fun Γ Φ ψ ↦
                  walkIff (Φ.length - 2) (Φ.length - 1) (fun vTo _ ↦
                    mp vTo (K.byHyp hv) lastHyp) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
            let backward : Deducer := dImpI L fun Γ Φ ψ ↦
              let hW := Φ.length - 1
              mp we (K.byHyp hW) (K.conjE fun Γ Φ ψ ↦
                let (en, ae) := (Φ.length - 2, Φ.length - 1)
                mp toE (K.norm (dConjI L (K.byHyp en) (K.byHyp ae))) (fun Γ Φ ψ ↦
                  let ha := Φ.length - 1
                  walkIff en ae (fun _ toV ↦ mp toV (K.byHyp hW) fun Γ Φ ψ ↦
                    mp cToW (K.norm (dConjI L (K.byHyp ha) (K.byHyp (Φ.length - 1)))) lastHyp
                      Γ Φ ψ) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
            K.norm (dConjI L (linkK K "ctorDen: forward" forward)
              (linkK K "ctorDen: backward" backward)) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
    let noRest : Deducer :=
      let arE (Γ : List Tree) : Term := pc P "Recognize.s3" [atomT "rEq", arityE Γ, numE Γ]
      let arV (Γ : List Tree) : Term := apps eqT [arityV Γ, nfAt Γ]
      let oneE (_ : List Tree) : Term := atomT "one"
      withNum <| withArity <|
      applyThm K "denPrim2/eq" (fun Γ ↦ [nfAt Γ, arityV Γ, numE Γ, arityE Γ] ++ denFixed Γ)
        (hAbs "rEq" ++ [dHyp, dHyp]) <|
      applyThm K "denDigit/one" denFixed [hA "one"] <|
      walkAt oneE (fun _ ↦ one) fun vPos _dV vGuard ↦
        let conjsE (Γ : List Tree) : Term := conjsT P (oneE Γ) (allOf Γ)
        applyThm K "conjDen" (fun Γ ↦ [atPos vPos Γ, arV Γ, conjsE Γ, arE Γ] ++ denFixed Γ)
          [dHyp, dHyp, hA "one", hA "zero", hA "rIf"] <|
        K.exE <| K.conjE fun Γ Φ ψ ↦
          let (wPos, wIff) := (Γ.length - 1, Φ.length - 1)
          dExI L K.G K.E (atPos wPos Γ) (dConjI L
            (linkK K "ctorDen: the test" (denAs K (fun _ ↦ quoteV P (atPos wPos Γ))
              (fun Γ ↦ pc P "Prelude.get" [pc P "Recognize.ctorTest" [clAt Γ, cAt Γ]])
              (fun Γ ↦ pc P "Recognize.conj" [arE Γ, conjsE Γ])))
            (linkK K "ctorDen: the truth, no last field" (truthNoRest wIff vGuard))) Γ Φ ψ
    -- the truth with a last field: the comparison is that there are enough children, the bit of
    -- the walk's end given as an equivalence by endIff under the bits
    let truthRest (wIff vGuard : ℕ) (endIff : ℕ → Deducer) : Deducer :=
      dImpI L fun Γ Φ ψ ↦
      let hb := Φ.length - 1
      (K.cutThm "walkEnough" (fun Γ ↦ [ftsAt Γ, rtyAt Γ, flagAt Γ, msAt Γ]) (K.allEΓ csAt
        fun Γ Φ ψ ↦
        let we := Φ.length - 1
        dConjE L wIff (fun Γ Φ ψ ↦
          let (wToC, cToW) := (Φ.length - 2, Φ.length - 1)
          let walkIff (en : ℕ) (k : ℕ → ℕ → Deducer) : Deducer :=
            mp vGuard (K.byHyp hb) (K.impE (K.byHyp en) (K.impE (endIff hb) (K.conjE fun Γ Φ ψ ↦
              k (Φ.length - 2) (Φ.length - 1) Γ Φ ψ)))
          let forward : Deducer := dImpI L fun Γ Φ ψ ↦
            let hw := Φ.length - 1
            mp wToC (K.byHyp hw) (K.conjE fun Γ Φ ψ ↦
              let (ha, hv) := (Φ.length - 2, Φ.length - 1)
              walkIff ha (fun vTo _ ↦ mp vTo (K.byHyp hv) lastHyp) Γ Φ ψ) Γ Φ ψ
          let backward : Deducer := dImpI L fun Γ Φ ψ ↦
            let hW := Φ.length - 1
            mp we (K.byHyp hW) (K.conjE fun Γ Φ ψ ↦
              let en := Φ.length - 2
              walkIff en (fun _ toV ↦ mp toV (K.byHyp hW) fun Γ Φ ψ ↦
                mp cToW (K.norm (dConjI L (K.byHyp en) (K.byHyp (Φ.length - 1)))) lastHyp
                  Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
          K.norm (dConjI L (linkK K "ctorDen: last forward" forward)
            (linkK K "ctorDen: last backward" backward)) Γ Φ ψ) Γ Φ ψ)) Γ Φ ψ
    -- the comparison of the arity, the denotation the last hypothesis
    let addE (Γ : List Tree) : Term := pc P "Recognize.s3" [atomT "rAdd", arityE Γ, atomT "one"]
    let ltE (Γ : List Tree) : Term := pc P "Recognize.s3" [atomT "rLt", numE Γ, addE Γ]
    let addT ← primT Kernel.Prim.add
    let ltT ← primT Kernel.Prim.lt
    let addV (Γ : List Tree) : Term := apps addT [arityV Γ, one]
    let ltV (Γ : List Tree) : Term := apps ltT [nfAt Γ, addV Γ]
    let withCompare (k : Deducer) : Deducer :=
      withNum <| withArity <|
      applyThm K "denDigit/one" denFixed [hA "one"] <|
      applyThm K "denPrim2/add" (fun Γ ↦ [one, arityV Γ, atomT "one", arityE Γ] ++ denFixed Γ)
        (hAbs "rAdd" ++ [dHyp, dHyp]) <|
      applyThm K "denPrim2/lt" (fun Γ ↦ [addV Γ, nfAt Γ, addE Γ, numE Γ] ++ denFixed Γ)
        (hAbs "rLt" ++ [dHyp, dHyp]) k
    let restWith (vtE y : List Tree → Term) (extra : List Internal.NormRule)
        (endIff : ℕ → Deducer) : Deducer :=
      walkAt vtE y fun vPos _dV vGuard ↦
        let conjsE (Γ : List Tree) : Term := conjsT P (vtE Γ) (allOf Γ)
        applyThm K "conjDen" (fun Γ ↦ [atPos vPos Γ, ltV Γ, conjsE Γ, ltE Γ] ++ denFixed Γ)
          [dHyp, dHyp, hA "one", hA "zero", hA "rIf"] <|
        K.exE <| K.conjE fun Γ Φ ψ ↦
          let (wPos, wIff) := (Γ.length - 1, Φ.length - 1)
          dExI L K.G K.E (atPos wPos Γ) (dConjI L
            (linkK K "ctorDen: the last field's test" (denAsWith K extra
              (fun _ ↦ quoteV P (atPos wPos Γ))
              (fun Γ ↦ pc P "Prelude.get" [pc P "Recognize.ctorTest" [clAt Γ, cAt Γ]])
              (fun Γ ↦ pc P "Recognize.conj" [ltE Γ, conjsE Γ])))
            (linkK K "ctorDen: the truth, a last field" (truthRest wIff vGuard endIff))) Γ Φ ψ
    -- a last field of the trees' type: the numeral one, the walk's end true at any children
    let treesArm : Deducer :=
      let oneE (_ : List Tree) : Term := atomT "one"
      withCompare <| restWith oneE (fun _ ↦ one) [] fun _ ↦
        linkK K "ctorDen: the trees' end" fun Γ Φ ψ ↦
          let leftAt (Γ : List Tree) : Term :=
            dropT (call D.lab [] [nfAt Γ]) (csAt Γ)
          applyThm K "allTrees" (fun Γ ↦ [leftAt Γ, rtyAt Γ, msAt Γ])
            [dHyp, K.solve 3] (fun Γ Φ ψ ↦
              let hE := Φ.length - 1
              K.norm (dConjI L (dImpI L (K.byHyp hE)) (dImpI L (K.solve 3))) Γ Φ ψ) Γ Φ ψ
    -- a last field of a datatype: the fold over the children left
    let dataArm (nfR : List Tree → Term) : Deducer :=
      let vtE (Γ : List Tree) : Term := restForm P (clAt Γ) (rtyAt Γ) (nfR Γ)
      withCompare <|
      applyThm K "restDen" (fun Γ ↦ [nfR Γ, RAt Γ, csAt Γ, rtyAt Γ, msAt Γ, clAt Γ] ++ denFixed Γ)
        ([K.solve 3, dHyp, dHyp, dHyp, dHyp] ++
          (writerPrims.flatMap fun a ↦ [K.byHyp (primHyp base a), K.byHyp (primHyp base a + 1)]) ++
          writerAtoms.map hA) <|
      K.exE <| K.conjE fun Γ Φ ψ ↦
        let (yPos, yGuard) := (Γ.length - 1, Φ.length - 1)
        restWith vtE (atPos yPos)
          [.delta (P.idx "Recognize.dropE"), .delta (P.idx "Recognize.tailE")]
          (fun hb ↦ linkK K "ctorDen: the fold's end" fun Γ Φ ψ ↦
            K.cutThm "allDrop" (fun Γ ↦ [csAt Γ, Term.lam treeTy (bitsOkT P
                (sh 1 (msAt Γ)) (sh 1 (clAt Γ)) (Term.app (sh 1 (RAt Γ)) (v 0))
                (pc P "Typing.memberships" [sh 1 (msAt Γ), v 0]))])
              (K.allEΓ (fun Γ ↦ call D.lab [] [nfR Γ]) (K.impE (K.byHyp hb) fun Γ Φ ψ ↦
                let hL := Φ.length - 1
                dImpE L yGuard (K.byHyp hL) lastHyp Γ Φ ψ)) Γ Φ ψ) Γ Φ ψ
    let equalT ← primT Kernel.Prim.equal
    let tTest (Γ : List Tree) : Term := pc P "Recognize.fieldTest" [clAt Γ, rtyAt Γ, atomT "vC"]
    -- a last field of a datatype: its test is no numeral, its form a list
    let notOne (k : Deducer) : Deducer :=
      let unfoldT : List Internal.NormRule := [.delta (P.idx "Recognize.fieldTest"),
        .delta (P.idx "Recognize.s3"), .delta (P.idx "Recognize.sx"),
        .delta (P.idx "Recognize.num"), .delta (P.idx "Recognize.bitOf")]
      let refute (h : ℕ) : Deducer := fun Γ Φ ψ ↦
        dRwHyp (evalRw K.G K.E (K.rulesEx Φ h ++ unfoldT) .full) h (dFalse K.L dHyp) Γ Φ ψ
      decideIn K (fun Γ ↦ apps equalT [pc P "Prelude.get" [tTest Γ], atomT "one"]) k
        (linkK K "ctorDen: the test the numeral one" fun Γ Φ ψ ↦
          let hEq (Γ : List Tree) : Term := apps equalT [pc P "Prelude.get" [tTest Γ], atomT "one"]
          do
            let tr := truth P.o (hEq Γ)
            let dT ← K.solve 3 Γ Φ tr
            dCut tr dT (fun Γ Φ ψ ↦
              let ht := Φ.length - 1
              decideIn K (fun Γ ↦ pc P "Prelude.isSome" [pc P "Reader.indexOf" [rtyAt Γ, clAt Γ]])
                (refute ht) (refute ht) Γ Φ ψ) Γ Φ ψ)
    let lastField : Deducer := fun Γ Φ ψ ↦
      let test (Γ : List Tree) : Term := pc P "Prelude.isSome" [tTest Γ]
      decideIn K (fun Γ ↦ pc P "Prelude.isSome" [allOf Γ])
        (linkK K "ctorDen: no tests, a last field" (K.hypFalse 0))
        (decideIn K test (linkK K "ctorDen: no last test" (K.hypFalse 0))
          (decideIn K (fun Γ ↦ pc P "Reader.named" [rtyAt Γ, pc P "Reader.kwT" []])
            (linkK K "ctorDen: a datatype's last field" (notOne (dataArm nfAt)))
            (linkK K "ctorDen: a last field of trees" fun Γ Φ ψ ↦ do
              -- the test the numeral one, by its unfolding at the name decided
              let eqn := Term.eq (tTest Γ) (pc P "Prelude.some" [atomT "one"])
              let dq ← dEq (fun Γ Φ t u ↦ byMode .full K.G K.E 0
                (K.rules Φ ++ [.delta (P.idx "Recognize.fieldTest")]) Γ
                (rwHyps (K.rules Φ) Φ) t u) Γ Φ eqn
              dCut eqn dq (normLastK K treesArm) Γ Φ ψ))) Γ Φ ψ
    let main : Deducer :=
      decideIn K flagAt (linkK K "ctorDen: no last field" fun Γ Φ ψ ↦
          decideIn K (fun Γ ↦ pc P "Prelude.isSome" [allOf Γ])
            (linkK K "ctorDen: no tests" (K.hypFalse 0))
            noRest Γ Φ ψ)
        (linkK K "ctorDen: a last field" lastField)
    let some d := main thm.ctx thm.hyps thm.concl
      | dbgTrace "ctorDen: not proved" fun _ ↦ none
    pure (thm, d))

/-- The equality of a number with itself holds: by induction on its bits. -/
def eqSelfB (P : Prog) (S : Defs) : Step :=
  ("eqSelfB", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let φ := Term.eq (call D.eqB [] [v 0, v 0]) (numeral 1)
    let d₀ ← K.solve 2 [] [] (Term.subst φ (Internal.instVar (Term.arr 0 [bitTy] Term.star)))
    let byIH : Deducer := fun Γ Φ ψ ↦
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ 0) .full) 0 (K.solve 2) Γ Φ ψ
    let cons : Deducer := fun Γ Φ ψ ↦ K.bitCase (v 1) byIH byIH Γ Φ ψ
    let d₁ ← cons [list bitTy, bitTy] [Internal.weakenElem φ] (Internal.listConsAt 1 bitTy φ)
    pure (⟨0, [bitsTy], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The truth of the equality of trees' labels is symmetric: the labels equal ({lit}`eqBSound`), the
other equality that of a number with itself ({name}`eqSelfB`). In the context of the trees. -/
def eqSym (P : Prog) (S : Defs) : Step :=
  ("eqSym", fun ix E ↦ do
    let K := writerKit P S ix E
    let eqT ← primT Kernel.Prim.eq
    let o := K.P.o
    let Γ := [treeTy, treeTy]
    let lb (t : Term) : Term := call D.lab [] [t]
    let thm : Internal.Thm := ⟨0, Γ, [truth o (apps eqT [v 1, v 0])],
      truth o (apps eqT [v 0, v 1])⟩
    let some d := (K.cutThm "eqBSound" (fun Γ ↦ [lb (atPos 1 Γ)]) <|
        K.allEΓ (fun Γ ↦ lb (atPos 0 Γ)) <|
        K.impE (linkK K "eqSym: the premise" (K.byHyp 0)) <| normLastK K <|
        K.cutThm "eqSelfB" (fun Γ ↦ [lb (atPos 1 Γ)]) <| normLastK K <|
        linkK K "eqSym: the goal" (K.solve 3)) thm.ctx thm.hyps thm.concl
      | dbgTrace "eqSym: not proved" fun _ ↦ none
    pure (thm, d))

/-- That a list of constructors has at most one constructor of each label. -/
def uniqT (P : Prog) (cts : Term) : Term :=
  let ltT := (primT Kernel.Prim.lt).getD Term.star
  Internal.Logic.all P.o treeTy (Term.lam treeTy (truth P.o (apps ltT
    [pc P "Prelude.length" [filterL (v 0) (sh 1 cts)], leafT (numeral 2)])))

/-- A number whose successor is below two is zero: its bits split, a successor's successor not
below two. In the context of the number. -/
def succBelowTwo (P : Prog) (S : Defs) : Step :=
  ("succBelowTwo", fun ix E ↦ do
    let K := writerKit P S ix E
    let ltT ← primT Kernel.Prim.lt
    let eqT ← primT Kernel.Prim.eq
    let thm : Internal.Thm := ⟨0, [bitsTy],
      [truth K.P.o (apps ltT [leafT (call D.succ [] [v 0]), leafT (numeral 2)])],
      truth K.P.o (apps eqT [leafT (v 0), leafT bnilT])⟩
    let leaf (_ : Option (List Bool)) : Deducer := fun Γ Φ ψ ↦
      (K.solve 3 Γ Φ ψ).orElse fun _ ↦ K.hypFalse 0 Γ Φ ψ
    let some d := dBits K.L K.G K.E (ix "listCases") (ix "bitCases") leaf 4 [] (v 0) thm.ctx
        thm.hyps thm.concl
      | dbgTrace "succBelowTwo: not proved" fun _ ↦ none
    pure (thm, d))

/-- A number whose successor is below two is itself: its bits split. In the context of the number.
-/
def belowTwoDown (P : Prog) (S : Defs) : Step :=
  ("belowTwoDown", fun ix E ↦ do
    let K := writerKit P S ix E
    let ltT ← primT Kernel.Prim.lt
    let lt2 (t : Term) : Term := truth K.P.o (apps ltT [leafT t, leafT (numeral 2)])
    let thm : Internal.Thm := ⟨0, [bitsTy], [lt2 (call D.succ [] [v 0])], lt2 (v 0)⟩
    let leaf (_ : Option (List Bool)) : Deducer := fun Γ Φ ψ ↦
      (K.solve 3 Γ Φ ψ).orElse fun _ ↦ K.hypFalse 0 Γ Φ ψ
    let some d := dBits K.L K.G K.E (ix "listCases") (ix "bitCases") leaf 4 [] (v 0) thm.ctx
        thm.hyps thm.concl
      | dbgTrace "belowTwoDown: not proved" fun _ ↦ none
    pure (thm, d))

/-- Of a list of constructors with at most one of each label, the rest: at a label, the head's
decided; another, the selection is the rest's; its own, the selection's number is its successor's
below two ({name}`belowTwoDown`). In the context of the rest and the head. -/
def uniqTail (P : Prog) (S : Defs) : Step :=
  ("uniqTail", fun ix E ↦ do
    let K := fieldsKit P S ix E
    let P := K.P
    let L := K.L
    let Γ := [list treeTy, treeTy]
    let thm : Internal.Thm := ⟨0, Γ, [uniqT P (consT treeTy (v 1) (v 0))], uniqT P (v 0)⟩
    let main : Deducer := dAllI L fun Γ Φ ψ ↦
      let lAt := atPos (Γ.length - 1)
      let lenAt (Γ : List Tree) : Term := call D.lab [] [pc P "Prelude.length"
        [filterL (lAt Γ) (atPos 1 Γ)]]
      dAllE L K.G K.E 0 (lAt Γ) (normLastK K fun Γ Φ ψ ↦
        let hU := Φ.length - 1
        decideIn K (fun Γ ↦ eqL (child0 (atPos 0 Γ)) (lAt Γ))
          (linkK K "uniqTail: another label" (K.byHyp hU))
          (linkK K "uniqTail: the head's label" (applyThm K "belowTwoDown" (fun Γ ↦ [lenAt Γ])
            [K.byHyp hU] fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ)) Γ Φ ψ) Γ Φ ψ
    let some d := main thm.ctx thm.hyps thm.concl
      | dbgTrace "uniqTail: not proved" fun _ ↦ none
    pure (thm, d))

/-- Of a list of constructors with at most one of each label, where the head has a label, no
constructor of the rest passes its test at that label: its passing gives a constructor of the rest
of that label ({lit}`ctorsLabel`), so the selection's number at it is not zero ({lit}`labelFilter`),
while its successor is below two ({name}`succBelowTwo`). In the context of the markers, the label,
the rest, the head and the memberships. -/
def uniqHead (P : Prog) (S : Defs) : Step :=
  ("uniqHead", fun ix E ↦ do
    let K := fieldsKit P S ix E
    let P := K.P
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    let Γ := [list Ls, treeTy, Ls, treeTy, Ls]
    -- the memberships v0, the head v1, the rest v2, the label v3, the markers v4
    let thm : Internal.Thm := ⟨0, Γ,
      [uniqT P (consT treeTy (v 1) (v 2)), truth o (eqL (child0 (v 1)) (v 3))],
      notT o (truth o (anyT P (pc P "Typing.ctorOk" [v 6, v 1, v 5, v 2]) (v 2)))⟩
    let (msAt, lAt, restAt, hdAt, qsAt) := (atPos 0, atPos 1, atPos 2, atPos 3, atPos 4)
    let lenAt (Γ : List Tree) : Term := call D.lab [] [pc P "Prelude.length"
      [filterL (lAt Γ) (restAt Γ)]]
    let main : Deducer := dImpI L fun Γ Φ ψ ↦
      let hAny := Φ.length - 1
      dAllE L K.G K.E 0 (lAt Γ) (normLastK K fun Γ Φ ψ ↦
        let hU := Φ.length - 1
        applyThm K "succBelowTwo" (fun Γ ↦ [lenAt Γ]) [linkK K "uniqHead: below two" (K.byHyp hU)]
          (fun Γ Φ ψ ↦
            let hZ := Φ.length - 1
            K.cutThm "ctorsLabel" (fun Γ ↦ [restAt Γ]) (K.allEΓ msAt (K.allEΓ lAt (K.allEΓ qsAt
              (K.impE (linkK K "uniqHead: passing" (K.byHyp hAny)) fun Γ Φ ψ ↦
                let hL := Φ.length - 1
                K.cutThm "labelFilter" (fun Γ ↦ [restAt Γ]) (K.allEΓ lAt
                  (K.impE (K.byHyp hL) (K.impE (linkK K "uniqHead: zero" (K.byHyp hZ))
                    fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ))) Γ Φ ψ)))) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
    let some d := decideIn K (fun Γ ↦ eqL (child0 (hdAt Γ)) (lAt Γ)) (K.hypFalse 1) main thm.ctx
        thm.hyps thm.concl
      | dbgTrace "uniqHead: not proved" fun _ ↦ none
    pure (thm, d))

/-- The writer's test of a marker's constructors, by the prelude's right fold: at each constructor,
the conditional of the label's equality with its position, its test and the rest's, where both are
given, from the numeral zero. -/
def dataFold (P : Prog) (cl cts : Term) : Term :=
  let t := pc P "Recognize.ctorTest" [sh 2 cl, v 1]
  let r := v 0
  let getT (x : Term) : Term := pc P "Prelude.get" [x]
  let (s3, s4) := ("Recognize.s3", "Recognize.s4")
  let eqE := pc P s3 [pc P "Recognize.rEq" [], pc P "Recognize.vL" [],
    pc P "Recognize.num" [child0 (v 1)]]
  foldrT treeTy treeTy (Term.lam treeTy (Term.lam treeTy (condT treeTy
    (call D.lab [] [pc P "Reader.both" [t, r]])
    (pc P "Prelude.some" [pc P s4 [pc P "Recognize.rIf" [], eqE, getT t, getT r]])
    (pc P "Prelude.none" []))))
    (pc P "Prelude.some" [pc P "Recognize.zero" []]) cts

/-- The context of the writer's test of a marker's constructors: the constructors, the label, the
children, the function of a child's bits, the markers and the closure. -/
def dataVars : List Tree :=
  [list treeTy, treeTy, list treeTy, exp treeTy treeTy, list treeTy, list treeTy]

/-- The statement of the writer's test of a marker's constructors, in the context of
{name}`dataVars`, at the constructors {lit}`cts`: of constructors with at most one of each label,
where the writer gives it, it denotes a bit which, at children holding their bits, is true exactly
where a constructor passes its test at the label and the children's memberships. -/
def dataφ (P : Prog) (S : Defs) (cts : Term) : Term :=
  let o := P.o
  let imp := Internal.Logic.imp o
  let at_ := denAt dataVars
  let (cl, ms, R, cs, l) := (at_ 6, at_ 7, at_ 8, at_ 9, at_ 10)
  let fold := dataFold P cl cts
  let qs := membershipsT P ms cs
  let spec := anyT P (pc P "Typing.ctorOk" [sh 3 ms, v 1, sh 3 l, sh 3 qs]) (sh 1 cts)
  let bitsAll : Term := S.allL (Term.lam treeTy (bitsOkT P (sh 2 ms) (sh 2 cl)
    (Term.app (sh 2 R) (v 0)) (pc P "Typing.memberships" [sh 2 ms, v 0]))) (sh 1 cs)
  imp (uniqT P cts) (imp (truth o (pc P "Prelude.isSome" [fold]))
    (Internal.Logic.ex o treeTy (Term.lam treeTy (Internal.Logic.conj o
      (denT P S (sh 1 (at_ 0)) (sh 1 (at_ 3)) (sh 1 (at_ 2)) (sh 1 (at_ 1)) (sh 1 (at_ 4))
        (sh 1 (at_ 5)) (sh 1 (pc P "Prelude.get" [fold])) (quoteV P (v 0)))
      (imp bitsAll (iffT o (truth o (v 0)) (truth o spec)))))))

/-- The hypotheses of the writer's test of a marker's constructors: the variables of the node, of
the children's bits and of the label denote their values, and {name}`writerHyps`. -/
def dataHyps (P : Prog) (S : Defs) : List Term :=
  let at_ := denAt dataVars
  let (ms, R, cs, l) := (at_ 7, at_ 8, at_ 9, at_ 10)
  [denIn P S dataVars (pc P "Recognize.vN" []) (quoteV P (node0 (mapFnT R cs))),
    denIn P S dataVars (pc P "Recognize.vR" []) (treeList P (quotesT P (mapFnT R cs))),
    denIn P S dataVars (pc P "Recognize.vL" []) (quoteV P l)] ++
    writerHyps P ms (at_ 1) (at_ 2) (at_ 4)

/-- The writer's test of a marker's constructors ({name}`dataφ`): by induction on the constructors.
None: the numeral zero, no constructor passing. A construction: the constructor's test
({name}`ctorDen`) and the rest's, their conditional by the label's equality with its position; at
children holding their bits, the equality decided: true, the constructor's test, no other passing
({name}`uniqHead`); false, the rest's, the constructor's label failing ({name}`eqSym`). -/
def dataDen (P : Prog) (S : Defs) : Step :=
  ("dataDen", fun ix E ↦ do
    let K₀ := fieldsKit P S ix E
    let K : Kit := { K₀ with
      P := { K₀.P with folded := (K₀.P.folded.filter (· != "Reader.both")) ++
        ["Recognize.ctorTest"] } }
    let P := K.P
    let L := K.L
    let base := 3
    let Γ₀ := denCtx dataVars
    let φ := dataφ P S (v 0)
    let hyps := dataHyps P S
    let some lowered := Internal.lowerHyps P.G 0 Γ₀.tail hyps
      | dbgTrace "dataDen: the hypotheses" fun _ ↦ none
    let (clAt, msAt, RAt, csAt, lAt) := (atPos 6, atPos 7, atPos 8, atPos 9, atPos 10)
    let hA (a : String) : Deducer := K.byHyp (atomHyp base a)
    let hAbs (a : String) : List Deducer :=
      [K.byHyp (primHyp base a), K.byHyp (primHyp base a + 1), hA a]
    let atomT (a : String) : Term := pc P s!"Recognize.{a}" []
    let lastFalse : Deducer := fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ
    let lastHyp : Deducer := fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ
    let mp (h : ℕ) (prem k : Deducer) : Deducer := dImpE L h prem k
    -- no constructors
    let d₀ ← (dImpI L <| dImpI L <|
        applyThm K "denDigit/zero" denFixed [hA "zero"] fun Γ Φ ψ ↦
          dExI L K.G K.E (leafT (numeral 0)) (dConjI L
            (linkK K "dataDen: the empty test" (denAs K (fun _ ↦ quoteV P (leafT (numeral 0)))
              (fun Γ ↦ pc P "Prelude.get" [dataFold P (clAt Γ) (nilT treeTy)])
              (fun _ ↦ atomT "zero")))
            (linkK K "dataDen: the empty truth" (dImpI L (iffAuto K)))) Γ Φ ψ) Γ₀.tail lowered
      (Term.subst φ fun i ↦ if i = 0 then nilT treeTy else v (i - 1))
    -- a construction: positions, head 11, rest 12
    let (hdAt, tlAt) := (atPos 11, atPos 12)
    let ih := hyps.length
    let eqT ← primT Kernel.Prim.eq
    let writerAll (hb : ℕ) : List Deducer :=
      [dHyp, dHyp] ++ (writerPrims.flatMap fun a ↦
        [K.byHyp (primHyp hb a), K.byHyp (primHyp hb a + 1)]) ++
      writerAtoms.map fun a ↦ K.byHyp (atomHyp hb a)
    let posAt (Γ : List Tree) : Term := child0 (hdAt Γ)
    let numE (Γ : List Tree) : Term := pc P "Recognize.num" [posAt Γ]
    let eqE (Γ : List Tree) : Term := pc P "Recognize.s3" [atomT "rEq", atomT "vL", numE Γ]
    let eqV (Γ : List Tree) : Term := apps eqT [lAt Γ, posAt Γ]
    let ctorT (Γ : List Tree) : Term := pc P "Recognize.ctorTest" [clAt Γ, hdAt Γ]
    let getT (t : Term) : Term := pc P "Prelude.get" [t]
    let restF (Γ : List Tree) : Term := dataFold P (clAt Γ) (tlAt Γ)
    let qsAt (Γ : List Tree) : Term := membershipsT P (msAt Γ) (csAt Γ)
    -- the truth at children holding their bits, the equivalences' parts split
    let truth2 (cIff rIff : ℕ) : Deducer := fun Γ Φ ψ ↦
      dConjE L cIff (fun Γ Φ ψ ↦
        let (cTo, toC) := (Φ.length - 2, Φ.length - 1)
        dConjE L rIff (fun Γ Φ ψ ↦
          let (rTo, toR) := (Φ.length - 2, Φ.length - 1)
          -- the equality decided, then the other way about
          decideIn K eqV
            (decideIn K (fun Γ ↦ apps eqT [posAt Γ, lAt Γ])
              (linkK K "dataDen: another constructor's label" <| K.norm <| dConjI L
                (dImpI L fun Γ Φ ψ ↦ mp rTo (K.byHyp (Φ.length - 1)) lastHyp Γ Φ ψ)
                (dImpI L fun Γ Φ ψ ↦ mp toR (K.byHyp (Φ.length - 1)) lastHyp Γ Φ ψ))
              (linkK K "dataDen: the labels' symmetry" fun Γ Φ ψ ↦
                applyThm K "eqSym" (fun Γ ↦ [lAt Γ, posAt Γ]) [K.solve 3] lastFalse Γ Φ ψ))
            (decideIn K (fun Γ ↦ apps eqT [posAt Γ, lAt Γ])
              (linkK K "dataDen: the labels' symmetry, the other way" fun Γ Φ ψ ↦
                applyThm K "eqSym" (fun Γ ↦ [posAt Γ, lAt Γ]) [K.solve 3] lastFalse Γ Φ ψ)
              (linkK K "dataDen: the constructor's label" fun Γ Φ ψ ↦
                let walkA (Γ : List Tree) : Term :=
                  let (fts, flag, rty) := ctorParts (hdAt Γ)
                  walkT P (msAt Γ) flag rty fts (qsAt Γ)
                applyThm K "uniqHead" (fun Γ ↦ [qsAt Γ, hdAt Γ, tlAt Γ, lAt Γ, msAt Γ])
                  [dHyp, linkK K "dataDen: the head's label" (K.solve 3)] (fun Γ Φ ψ ↦
                  let noRest := Φ.length - 1
                  decideIn K walkA
                    (K.norm <| dConjI L
                      (dImpI L fun Γ Φ ψ ↦ mp cTo (K.byHyp (Φ.length - 1)) lastFalse Γ Φ ψ)
                      (dImpI L fun Γ Φ ψ ↦
                        mp noRest (K.byHyp (Φ.length - 1)) lastFalse Γ Φ ψ))
                    (K.norm <| dConjI L (dImpI L (K.solve 3))
                      (dImpI L (mp toC (K.solve 3) lastHyp))) Γ Φ ψ) Γ Φ ψ)) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
    let finish (wc wr gc gr : ℕ) : Deducer :=
      let (wcAt, wrAt) := (atPos wc, atPos wr)
      let valueAt (Γ : List Tree) : Term :=
        condT treeTy (call D.lab [] [eqV Γ]) (wcAt Γ) (wrAt Γ)
      let formAt (Γ : List Tree) : Term :=
        pc P "Recognize.s4" [atomT "rIf", eqE Γ, getT (ctorT Γ), getT (restF Γ)]
      applyThm K "denIf" (fun Γ ↦ [wrAt Γ, wcAt Γ, eqV Γ, getT (restF Γ), getT (ctorT Γ), eqE Γ] ++
          denFixed Γ) [hA "rIf", dHyp, dHyp, dHyp] fun Γ Φ ψ ↦
        dExI L K.G K.E (valueAt Γ) (dConjI L
          (linkK K "dataDen: the conditional" (denAs K (fun Γ ↦ quoteV P (valueAt Γ))
            (fun Γ ↦ getT (dataFold P (clAt Γ) (consT treeTy (hdAt Γ) (tlAt Γ)))) formAt))
          (linkK K "dataDen: the truth" <| dImpI L fun Γ Φ ψ ↦
            let hb := Φ.length - 1
            mp gc (K.byHyp hb) (fun Γ Φ ψ ↦
              let cIff := Φ.length - 1
              mp gr (K.byHyp hb) (fun Γ Φ ψ ↦ truth2 cIff (Φ.length - 1) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ))
          Γ Φ ψ
    let withEq (k : Deducer) : Deducer := fun Γ Φ ψ ↦
      dAllE L K.G K.E (base + 1) (posAt Γ) (normLastK K <| K.conjE fun Γ₁ Φ₁ ψ₁ ↦
        let h₁ := Φ₁.length - 2
        K.conjE (fun Γ₂ Φ₂ ψ₂ ↦
          applyThm K "denNum" (fun Γ ↦ posAt Γ :: denFixed Γ) [K.byHyp h₁, K.byNorm,
            K.byHyp (Φ₂.length - 1)] (
          applyThm K "denPrim2/eq" (fun Γ ↦ [posAt Γ, lAt Γ, numE Γ, atomT "vL"] ++ denFixed Γ)
            (hAbs "rEq" ++ [dHyp, dHyp]) k) Γ₂ Φ₂ ψ₂) Γ₁ Φ₁ ψ₁) Γ Φ ψ
    let cons : Deducer := dImpI L <| dImpI L fun Γ₁ Φ₁ ψ₁ ↦
      let hP := Φ₁.length - 1
      decideIn K (fun Γ ↦ pc P "Prelude.isSome" [ctorT Γ])
        (linkK K "dataDen: no constructor's test" (K.hypFalse hP))
        (decideIn K (fun Γ ↦ pc P "Prelude.isSome" [restF Γ])
          (linkK K "dataDen: no rest's test" (K.hypFalse hP))
          (linkK K "dataDen: both tests" <|
          applyThm K "ctorDen" (fun Γ ↦ [csAt Γ, RAt Γ, hdAt Γ, msAt Γ, clAt Γ] ++ denFixed Γ)
            ([K.solve 3, dHyp, dHyp] ++ writerAll base) <|
          K.exE <| K.conjE fun Γ Φ ψ ↦
            let (wc, gc) := (Γ.length - 1, Φ.length - 1)
            mp ih (applyThm K "uniqTail" (fun Γ ↦ [tlAt Γ, hdAt Γ]) [dHyp] dHyp)
              (K.impE (K.solve 3) <| K.exE <| K.conjE fun Γ Φ ψ ↦
                let (wr, gr) := (Γ.length - 1, Φ.length - 1)
                withEq (finish wc wr gc gr) Γ Φ ψ) Γ Φ ψ)) Γ₁ Φ₁ ψ₁
    let d₁ ← linkK K "dataDen: construction" cons (list treeTy :: treeTy :: Γ₀.tail)
      (lowered.map Internal.weaken2 ++ [Internal.weakenElem φ]) (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, Γ₀, hyps, φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- Convergences of a function's values at each element of a list to the quotations of a function
of the element combined: its values collected converge to the node of the quotations of the map. By
induction on the list, the head's and the rest's thresholds shifted to their sum. In the context of
the list, under the functions. -/
def valuesConv (P : Prog) (S : Defs) : Step :=
  ("valuesConv", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let L := K.L
    let o := P.o
    let all := Internal.Logic.all o
    let imp := Internal.Logic.imp o
    let FTy := exp nat (exp treeTy treeTy)
    let RTy := exp treeTy treeTy
    -- under the functions: R v0, F v1, the list v2
    let hyp : Term := S.allL (Term.lam treeTy
      (S.conv (Term.lam nat (apps (v 3) [v 0, v 1]))
        (Term.lam treeTy (Term.eq (v 0) (pc P "Eval.valQuote" [Term.app (v 2) (v 1)]))))) (v 2)
    let vals (R xs : Term) : Term := node0 (quotesT P (mapFnT R xs))
    let concl : Term := S.conv
      (Term.lam nat (pc P "Eval.allSomeT" [pc P "Eval.mapT" [Term.app (v 2) (v 0), v 3]]))
      (Term.lam treeTy (Term.eq (v 0) (vals (v 1) (v 3))))
    let φ := all FTy (Term.lam FTy (all RTy (Term.lam RTy (imp hyp concl))))
    let d₀ ← dAllI L (dAllI L (dImpI L (K.conv (fun _ ↦ zeroN) (fun _ ↦ node0 (nilT treeTy))
      (linkK K "valuesConv: empty stable" K.byNorm)
      (linkK K "valuesConv: empty value" (K.solve 2))))) [] []
      (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
    -- a construction: the head's and, by the induction hypothesis, the rest's
    let cons : Deducer := dAllI L (dAllI L (dImpI L fun Γ₁ Φ₁ ψ₁ ↦
      let F (Γ : List Tree) : Term := atPos 2 Γ
      let R (Γ : List Tree) : Term := atPos 3 Γ
      K.normLast (K.conjE fun Γ₂ Φ₂ ψ₂ ↦
        let (hh, hr) := (Φ₂.length - 2, Φ₂.length - 1)
        dRwHyp (evalRw K.G K.E [.delta (S.q + 2)] .head) hh (K.exE <| K.exE <| K.conjE
          fun Γ₃ Φ₃ ψ₃ ↦
          let (n₁, s₁) := (Γ₃.length - 2, Φ₃.length - 2)
          normLastK K (fun Γ₄ Φ₄ ψ₄ ↦
            dAllE L K.G K.E 0 (F Γ₄) (K.allEΓ R (K.impE (K.byHyp hr) (K.unfoldConv <| K.exE <|
              K.exE <| K.conjE fun Γ Φ ψ ↦
              let (n₂, s₂) := (Γ.length - 2, Φ.length - 2)
              normLastK K (shiftK K s₁ false (atPos n₂) fun Γ Φ ψ ↦
                let a₁ := Φ.length - 1
                shiftK K s₂ true (atPos n₁) (fun Γ Φ ψ ↦
                  let a₂ := Φ.length - 1
                  let value (Γ : List Tree) : Term := node0 (quotesT P (mapFnT (R Γ)
                    (consT treeTy (atPos 0 Γ) (atPos 1 Γ))))
                  K.conv (fun Γ ↦ S.add (atPos n₁ Γ) (atPos n₂ Γ)) value
                    (linkK K "valuesConv: stable" <| K.instN a₁ (fun _ ↦ v 0) <|
                      K.instN a₂ (fun _ ↦ v 0) K.byNorm)
                    (linkK K "valuesConv: the value" (K.solve 2)) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ))) Γ₄ Φ₄ ψ₄)
          Γ₃ Φ₃ ψ₃) Γ₂ Φ₂ ψ₂) Γ₁ Φ₁ ψ₁))
    let d₁ ← linkK K "valuesConv: construction" cons [list treeTy, treeTy]
      [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, [list treeTy], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The hypothesis of the fold of a function: at each label and children, the function applied to
the label's quotation and that to the list value of the quotations of a function of the children,
converges to the quotation of that function at the node. Under the label v1 and the children v0:
the function R, the step g, the type A and the relation's context D, of indices given. -/
def foldStepT (P : Prog) (S : Defs) (R g A Dv : Term) : Term :=
  let o := P.o
  let Ls := list treeTy
  -- beneath the label and the children, and beneath the level
  let ap : Term := Term.snd (S.levelN (Term.fst (sh 3 Dv)) (v 0))
  let F := Term.lam nat (pc P "Eval.bindO" [apps ap [sh 3 g, pc P "Eval.valQuote" [leafT (v 2)]],
    Term.lam treeTy (apps (sh 1 ap) [v 0, pc P "Eval.ofList" [sh 4 A,
      quotesT P (mapFnT (sh 4 R) (v 2))]])])
  let value := pc P "Eval.valQuote" [Term.app (sh 3 R) (nodeT (Term.pair (v 2) (v 1)))]
  Internal.Logic.all o bitsTy (Term.lam bitsTy (Internal.Logic.all o Ls (Term.lam Ls
    (S.conv F (Term.lam treeTy (Term.eq (v 0) value))))))

/-- The statement of the fold of a function, at the tree of index 4 under the quantifiers: under the
hypothesis of its steps ({name}`foldStepT`), the fold converges to the quotation of the function at
the tree. -/
def foldExactφ (P : Prog) (S : Defs) : Term :=
  let o := P.o
  let Fn := exp treeTy treeTy
  -- under the quantifiers: R v0, g v1, A v2, D v3, the tree v4
  let F := Term.lam nat (pc P "Eval.foldVal" [Term.snd (S.levelN (Term.fst (v 4)) (v 0)), v 3, v 2,
    v 5])
  let concl := S.conv F (Term.lam treeTy (Term.eq (v 0) (pc P "Eval.valQuote"
    [Term.app (v 1) (v 5)])))
  Internal.Logic.all o Defs3.ctxTy (Term.lam Defs3.ctxTy (Internal.Logic.all o treeTy
    (Term.lam treeTy (Internal.Logic.all o treeTy (Term.lam treeTy (Internal.Logic.all o Fn
      (Term.lam Fn (Internal.Logic.imp o (foldStepT P S (v 0) (v 1) (v 2) (v 3)) concl))))))))

/-- The fold of a function ({name}`foldExactφ`): by induction on trees, the children's values
converging together ({name}`valuesConv`), the step's hypothesis at the node's label and children,
both thresholds shifted to their sum. -/
def foldExact (P : Prog) (S : Defs) : Step :=
  ("foldExact", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, ["foldConvFus"].filter fun nm ↦ 0 < ix nm ∧ ix nm < E.size⟩
    let L := K.L
    let φ := foldExactφ P S
    -- the label 0, the children 1, the relation's context 2, the type 3, the step 4, the function 5
    let (lAt, csAt, DAt, AAt, gAt, RAt) :=
      (atPos 0, atPos 1, atPos 2, atPos 3, atPos 4, atPos 5)
    let body (hAll hs : ℕ) : Deducer :=
      -- the children's convergences at the step, and the function of the fuel and the child
      let Q (Γ : List Tree) : Term := Term.lam treeTy (S.conv (Term.lam nat (pc P "Eval.foldVal"
        [Term.snd (S.levelN (Term.fst (sh 2 (DAt Γ))) (v 0)), sh 2 (AAt Γ), sh 2 (gAt Γ), v 1]))
        (Term.lam treeTy (Term.eq (v 0) (pc P "Eval.valQuote" [Term.app (sh 2 (RAt Γ)) (v 1)]))))
      let FF (Γ : List Tree) : Term := Term.lam nat (Term.lam treeTy (pc P "Eval.foldVal"
        [Term.snd (S.levelN (Term.fst (sh 2 (DAt Γ))) (v 1)), sh 2 (AAt Γ), sh 2 (gAt Γ), v 0]))
      let mono : Deducer := dAllI L (dImpI L (K.normLast fun Γ Φ ψ ↦
        allEs K (Φ.length - 1) [DAt, AAt, gAt, RAt]
          (K.impE (K.byHyp hs) (fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ)) Γ Φ ψ))
      let fin (nC sC : ℕ) : Deducer := fun Γ Φ ψ ↦
        dAllE L K.G K.E hs (lAt Γ) (K.allEΓ csAt (K.unfoldConv <| K.exE <| K.exE <| K.conjE
          fun Γ Φ ψ ↦
          let (n₁, s₁) := (Γ.length - 2, Φ.length - 2)
          normLastK K (shiftK K sC false (atPos n₁) fun Γ Φ ψ ↦
            let a := Φ.length - 1
            shiftK K s₁ true (atPos nC) (fun Γ Φ ψ ↦
              let b := Φ.length - 1
              K.conv (fun Γ ↦ S.add (atPos nC Γ) (atPos n₁ Γ))
                (fun Γ ↦ pc P "Eval.valQuote"
                  [Term.app (RAt Γ) (nodeT (Term.pair (lAt Γ) (csAt Γ)))])
                (linkK K "foldExact: stable" <| K.instN a (fun _ ↦ v 0) <|
                  K.instN b (fun _ ↦ v 0) (linkK K "foldExact: the fold" K.byNorm))
                (linkK K "foldExact: the value" (K.solve 3)) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ)) Γ Φ ψ
      K.cutThm "allMono" (fun Γ ↦ [csAt Γ]) (K.allEΓ (fun _ ↦ Term.lam treeTy φ) (K.allEΓ Q
        (K.impE (K.byHyp hAll) (K.impE mono (fun Γ Φ ψ ↦
          let hQ := Φ.length - 1
          K.cutThm "valuesConv" (fun Γ ↦ [csAt Γ]) (K.allEΓ FF (K.allEΓ RAt (K.impE (K.byHyp hQ)
            (K.convE fun Γ Φ ψ ↦
              normLastK K (fin (Γ.length - 2) (Φ.length - 2)) Γ Φ ψ)))) Γ Φ ψ)))))
    let node : Deducer := fun Γ₀ Φ₀ ψ₀ ↦
      K.cutThm "foldExactAll" (fun Γ ↦ [v (Γ.length - 2)]) (K.impE dHyp (fun Γ Φ ψ ↦
        let hAll := Φ.length - 1
        allIs L 4 (dImpI L fun Γ₁ Φ₁ ψ₁ ↦ body hAll (Φ₁.length - 1) Γ₁ Φ₁ ψ₁) Γ Φ ψ)) Γ₀ Φ₀ ψ₀
    let d ← node [list treeTy, bitsTy] [Internal.roseHyp 0 1 φ]
      (Internal.roseNodeAt 2 treeTy bitsTy φ)
    pure (⟨0, [treeTy], [], φ⟩, nd (.roseIndHyp 2 0 1) [d]))

/-- The writer's marker of a datatype is that of its index among the markers' names, where it has
one: by induction on the markers; at a construction, the name the head's or not, the equality's
symmetry relating the writer's test to the index's. In the context of the markers, under the name.
-/
def markerOfAt (P : Prog) (S : Defs) : Step :=
  ("markerOfAt", fun ix E ↦ do
    let K₀ := writerKit P S ix E
    let K : Kit := { K₀ with
      P := { K₀.P with folded := K₀.P.folded.filter (· != "Typing.markerNames") }
      more := K₀.more ++ (["indexOfCons", "indexOfNil"].filter
        fun nm ↦ 0 < ix nm ∧ ix nm < E.size) }
    let P := K.P
    let L := K.L
    let o := P.o
    let equalT ← primT Kernel.Prim.equal
    let succRules : List Internal.NormRule :=
      [.thm (ix "rIterSucc") [list treeTy], .thm (ix "addOne") []]
    -- under the quantifier: the name v0, the markers v1
    let idx := markerIdx P (v 0) (v 1)
    let φ := Internal.Logic.all o treeTy (Term.lam treeTy (Internal.Logic.imp o
      (truth o (pc P "Prelude.isSome" [idx]))
      (Term.eq (pc P "Recognize.markerOf" [v 1, v 0]) (pc P "Prelude.some"
        [pc P "Typing/Txs.atOr" [pc P "Typing.tx0" [], v 1, pc P "Prelude.get" [idx]]]))))
    let lastFalse : Deducer := fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ
    let d₀ ← dAllI L (dImpI L (linkK K "markerOfAt: empty" lastFalse)) [] []
      (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
    let cons : Deducer := dAllI L <| dImpI L fun Γ₁ Φ₁ ψ₁ ↦
      let (hd, tl, key) := (atPos 0, atPos 1, atPos 2)
      let hI := Φ₁.length - 1
      let byNormS : Deducer := fun Γ Φ ψ ↦
        dEq (fun Γ Φ t u ↦ byMode .full K.G K.E 0 (K.rules Φ ++ succRules) Γ
          (rwHyps (K.rules Φ) Φ) t u) Γ Φ ψ
      let rest : Deducer := linkK K "markerOfAt: the rest" <|
        decideIn K (fun Γ ↦ pc P "Prelude.isSome" [markerIdx P (key Γ) (tl Γ)])
          (linkK K "markerOfAt: no index" (K.hypFalse hI))
          (fun Γ Φ ψ ↦ dAllE L K.G K.E 0 (key Γ) (K.impE (K.solve 3) <| normLastK K <|
            linkK K "markerOfAt: the rest's equation" byNormS) Γ Φ ψ)
      -- the writer's test and the index's, each by the other through the equality's soundness
      let head : Deducer := fun Γ Φ ψ ↦ byNormS Γ Φ ψ
      decideIn K (fun Γ ↦ apps equalT [key Γ, child0 (hd Γ)])
        (decideIn K (fun Γ ↦ apps equalT [child0 (hd Γ), key Γ]) rest
          (linkK K "markerOfAt: a test without the other" (K.cutThm "equalSymm"
            (fun Γ ↦ [key Γ, child0 (hd Γ)]) <| K.impE (K.solve 3) <|
            fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ)))
        (decideIn K (fun Γ ↦ apps equalT [child0 (hd Γ), key Γ])
          (linkK K "markerOfAt: the other without a test" (K.cutThm "equalSymm"
            (fun Γ ↦ [child0 (hd Γ), key Γ]) <| K.impE (K.solve 3) <|
            fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ))
          (linkK K "markerOfAt: the head" head)) Γ₁ Φ₁ ψ₁
    let d₁ ← linkK K "markerOfAt: construction" cons [list treeTy, treeTy]
      [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, [list treeTy], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- A tree passing the test of one of its datatype's marker's constructors at its label and its
children's memberships is a member: the converse of {lit}`memberCtors`, proved as it is. In the
context of the tree, the datatype and the markers. -/
def ctorsMember (P : Prog) (S : Defs) : Step :=
  ("ctorsMember", fun ix E ↦ do
    let P := chainProg P
    let K : Kit := ⟨P, S, E, ix, []⟩
    let o := P.o
    let Γ := [treeTy, treeTy, list treeTy]
    let (t, dt, ms) := (v 0, v 1, v 2)
    let member := truth o (pc P "Typing.memberOf" [ms, dt, t])
    let passes := truth o (anyT P (pc P "Typing.ctorOk" [sh 2 ms, v 1, labT (v 2),
      childMemberships P (sh 2 ms) (v 2)]) (specsOf P ms dt))
    let a : Internal.Thm := ⟨0, Γ, [passes], member⟩
    let unfold : List Internal.NormRule := [.delta (P.idx "Typing.memberships")]
    let some d := (K.treeNode t <| normLastK K fun Γ Φ ψ ↦
        let (pL, pK) := (Γ.length - 2, Γ.length - 1)
        let idx (Γ : List Tree) : Term := markerIdx P (atPos 1 Γ) (atPos 0 Γ)
        let g (Γ : List Tree) (Φ : List Term) : Term :=
          let mem := ((evalRw K.G K.E (K.rules Φ ++ unfold) .full Γ Φ
            (pc P "Typing.memberships" [atPos 0 Γ, atPos 2 Γ])).map Prod.fst).getD Term.star
          match findFoldr (atPos 0 Γ) mem with
          | some f => match foldrParts f with
            | some (_, step, _) => Term.lam treeTy
                (headT (Term.app (Term.app (sh 1 step) (v 0)) (nilT treeTy)))
            | none => dbgTrace "ctorsMember: no step" fun _ ↦ Term.star
          | none => dbgTrace "ctorsMember: no fold" fun _ ↦ Term.star
        decideIn K (fun Γ ↦ pc P "Prelude.isSome" [idx Γ])
          (linkK K "ctorsMember: no marker" fun Γ Φ ψ ↦
            dRwHyp (evalRw K.G K.E (K.rulesEx Φ 0 ++ unfold) .full) 0 (dFalse K.L dHyp) Γ Φ ψ)
          (K.cutThm "kidsMemberships" (fun Γ ↦ [atPos pK Γ, atPos 0 Γ, atPos pL Γ]) <|
            normLastK K <|
            K.cutThm "atIndexMap" (fun Γ ↦ [atPos 0 Γ]) <|
            (fun k Γ Φ ψ ↦ dAllE K.L K.G K.E (Φ.length - 1) (g Γ Φ) k Γ Φ ψ) <|
            K.allEΓ (atPos 1) <|
            K.impE (linkK K "ctorsMember: the index" (K.solve 3)) <| normLastK K <|
            linkK K "ctorsMember: the membership" fun Γ Φ ψ ↦
              dRwHyp (evalRw K.G K.E (K.rulesEx Φ 0 ++ unfold) .full) 0
                (dRwBy (evalRw K.G K.E (K.rules Φ ++ unfold) .full) dHyp) Γ Φ ψ) Γ Φ ψ)
        a.ctx a.hyps a.concl
      | dbgTrace "ctorsMember: not proved" fun _ ↦ none
    pure (a, d))

/-- The bit of a datatype at a tree: one where the test of a field of that datatype holds of the
tree's memberships, zero otherwise. The name, the tree and the markers given. -/
def bitT (P : Prog) (ms n t : Term) : Term :=
  condT treeTy (call D.lab [] [pc P "Typing.fieldOk" [ms, n, pc P "Typing.memberships" [ms, t]]])
    (leafT (numeral 1)) (leafT (numeral 0))

/-- The function the recognizer's fold computes: at a tree, the node over the bit of each datatype
of the closure {lit}`cl`. -/
def bitsFn (P : Prog) (ms cl : Term) : Term :=
  Term.lam treeTy (node0 (mapFnT (Term.lam treeTy (bitT P (sh 2 ms) (v 0) (v 1))) (sh 1 cl)))

/-- At the index of a name among a list of trees, the element of the map of a function there is the
function at the name, up to the name's equality: by induction on the list; at a construction, the
name the head or not. In the context of the list, under the function and the name. -/
def atIndexOf (P : Prog) (S : Defs) : Step :=
  ("atIndexOf", fun ix E ↦ do
    let K₀ := writerKit P S ix E
    let K : Kit := { K₀ with more := K₀.more ++ (["indexOfCons", "indexOfNil"].filter
      fun nm ↦ 0 < ix nm ∧ ix nm < E.size) }
    let P := K.P
    let L := K.L
    let o := P.o
    let F := exp treeTy treeTy
    let succRules : List Internal.NormRule :=
      [.thm (ix "rIterSucc") [list treeTy], .thm (ix "addOne") []]
    -- under the quantifiers: the name v0, the function v1, the list v2
    let idx := pc P "Reader.indexOf" [v 0, v 2]
    let φ := Internal.Logic.all o F (Term.lam F (Internal.Logic.all o treeTy (Term.lam treeTy
      (Internal.Logic.imp o (truth o (pc P "Prelude.isSome" [idx]))
        (Term.eq (pc P "Prelude.at" [mapFnT (v 1) (v 2), pc P "Prelude.get" [idx]])
          (Term.app (v 1) (v 0)))))))
    let lastFalse : Deducer := fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ
    let d₀ ← dAllI L (dAllI L (dImpI L (linkK K "atIndexOf: empty" lastFalse))) [] []
      (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
    let cons : Deducer := dAllI L <| dAllI L <| dImpI L fun Γ₁ Φ₁ ψ₁ ↦
      let (hd, tl, g, key) := (atPos 0, atPos 1, atPos 2, atPos 3)
      let byNormS : Deducer := fun Γ Φ ψ ↦
        dEq (fun Γ Φ t u ↦ byMode .full K.G K.E 0 (K.rules Φ ++ succRules) Γ
          (rwHyps (K.rules Φ) Φ) t u) Γ Φ ψ
      let rest : Deducer := linkK K "atIndexOf: the rest" <|
        decideIn K (fun Γ ↦ pc P "Prelude.isSome" [pc P "Reader.indexOf" [key Γ, tl Γ]])
          (linkK K "atIndexOf: no index" (K.hypFalse (Φ₁.length - 1)))
          (fun Γ Φ ψ ↦ dAllE L K.G K.E 0 (g Γ) (K.allEΓ key <| K.impE (K.solve 3) <|
            normLastK K <| linkK K "atIndexOf: the rest's equation" byNormS) Γ Φ ψ)
      let equalT := (primT Kernel.Prim.equal).getD Term.star
      decideIn K (fun Γ ↦ apps equalT [key Γ, hd Γ]) rest
        (linkK K "atIndexOf: the head" (dRwBy (fun Γ Φ t ↦
            evalRw K.G K.E (K.rules Φ ++ succRules) .full Γ Φ t) <|
          K.cutThm "equalSound" (fun Γ ↦ [key Γ]) <| K.allEΓ hd <|
          K.impE (K.solve 3) <| fun Γ Φ ψ ↦
            -- the goal's sides differ by the name only, which the equation rewrites
            dEq (fun Γ Φ t u ↦ byMode .full K.G K.E 0 [.hyp (Φ.length - 1)] Γ Φ t u) Γ Φ ψ))
        Γ₁ Φ₁ ψ₁
    let d₁ ← linkK K "atIndexOf: construction" cons [list treeTy, treeTy]
      [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, [list treeTy], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- A tree's bits ({name}`bitsFn`) hold of its memberships: the bit at a datatype's position is the
function at the datatype ({name}`atIndexOf`), one exactly where the field's test holds. In the
context of the tree, the closure and the markers. -/
def bitsFnOk (P : Prog) (S : Defs) : Step :=
  ("bitsFnOk", fun ix E ↦ do
    let K := fieldsKit P S ix E
    let P := K.P
    let L := K.L
    let Ls := list treeTy
    let Γ := [treeTy, Ls, Ls]
    let (tAt, clAt, msAt) := (atPos 2, atPos 1, atPos 0)
    let thm : Internal.Thm := ⟨0, Γ, [], bitsOkT P (v 2) (v 1)
      (Term.app (bitsFn P (v 2) (v 1)) (v 0)) (pc P "Typing.memberships" [v 2, v 0])⟩
    let fn (Γ : List Tree) : Term := Term.lam treeTy (bitT P (sh 1 (msAt Γ)) (v 0) (sh 1 (tAt Γ)))
    let main : Deducer := dAllI L <| dImpI L fun Γ Φ ψ ↦
      let nAt := atPos (Γ.length - 1)
      K.cutThm "atIndexOf" (fun Γ ↦ [clAt Γ]) (K.allEΓ fn (K.allEΓ nAt
        (K.impE (K.byHyp (Φ.length - 1)) <| normLastK K <| fun Γ Φ ψ ↦
          let okT (Γ : List Tree) : Term := pc P "Typing.fieldOk" [msAt Γ, nAt Γ,
            pc P "Typing.memberships" [msAt Γ, tAt Γ]]
          decideIn K okT (linkK K "bitsFnOk: false" (iffAuto K))
            (linkK K "bitsFnOk: true" (iffAuto K)) Γ Φ ψ))) Γ Φ ψ
    let some d := main thm.ctx thm.hyps thm.concl
      | dbgTrace "bitsFnOk: not proved" fun _ ↦ none
    pure (thm, d))

/-- Each of a list of trees holds its bits: by induction on the list, {name}`bitsFnOk` at the head.
In the context of the list, the closure and the markers. -/
def bitsFnAll (P : Prog) (S : Defs) : Step :=
  ("bitsFnAll", fun ix E ↦ do
    let K := fieldsKit P S ix E
    let P := K.P
    let L := K.L
    let Ls := list treeTy
    let Γ := [Ls, Ls, Ls]
    -- the list v0, the closure v1, the markers v2
    let φ := S.allL (Term.lam treeTy (bitsOkT P (sh 1 (v 2)) (sh 1 (v 1))
      (Term.app (bitsFn P (sh 1 (v 2)) (sh 1 (v 1))) (v 0))
      (pc P "Typing.memberships" [sh 1 (v 2), v 0]))) (v 0)
    let d₀ ← linkK K "bitsFnAll: empty" (K.solve 3) Γ.tail []
      (Term.subst φ fun i ↦ if i = 0 then nilT treeTy else v (i - 1))
    let cons : Deducer := K.norm <| dConjI L
      (linkK K "bitsFnAll: the head" (K.cutThm "bitsFnOk"
        (fun Γ ↦ [atPos 2 Γ, atPos 1 Γ, atPos 0 Γ]) fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ))
      (linkK K "bitsFnAll: the rest" (K.byHyp 0))
    let d₁ ← linkK K "bitsFnAll: construction" cons (Ls :: treeTy :: Γ.tail)
      [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, Γ, [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The membership of a tree in a datatype with a marker is the test of a field of that datatype at
the tree's memberships: both the element of the memberships at the datatype's index. In the context
of the tree, the name and the markers. -/
def memberField (P : Prog) (S : Defs) : Step :=
  ("memberField", fun ix E ↦ do
    let K := fieldsKit P S ix E
    let P := K.P
    let Γ := [treeTy, treeTy, list treeTy]
    let thm : Internal.Thm := ⟨0, Γ, [truth P.o (pc P "Prelude.isSome" [markerIdx P (v 1) (v 2)])],
      Term.eq (pc P "Typing.memberOf" [v 2, v 1, v 0])
        (pc P "Typing.fieldOk" [v 2, v 1, pc P "Typing.memberships" [v 2, v 0]])⟩
    let some d := decideIn K (fun Γ ↦ pc P "Prelude.isSome" [markerIdx P (atPos 1 Γ) (atPos 0 Γ)])
        (K.hypFalse 0)
        (linkK K "memberField: the sides" fun Γ Φ ψ ↦
          dEq (fun Γ Φ t u ↦ byMode .full K.G K.E 0 (K.rules Φ ++ [.delta (P.idx "Typing.fieldOk"),
            .delta (P.idx "Typing.memberOf")]) Γ (rwHyps (K.rules Φ) Φ) t u) Γ Φ ψ)
        thm.ctx thm.hyps thm.concl
      | dbgTrace "memberField: not proved" fun _ ↦ none
    pure (thm, d))

/-- The writer's marker of a datatype without an index among the markers' names is absent: by
induction on the markers; at a construction, the head's name the name's refuting the index's
absence. In the context of the markers, under the name. -/
def markerOfNone (P : Prog) (S : Defs) : Step :=
  ("markerOfNone", fun ix E ↦ do
    let K₀ := writerKit P S ix E
    let K : Kit := { K₀ with
      P := { K₀.P with folded := K₀.P.folded.filter (· != "Typing.markerNames") }
      more := K₀.more ++ (["indexOfCons", "indexOfNil"].filter
        fun nm ↦ 0 < ix nm ∧ ix nm < E.size) }
    let P := K.P
    let L := K.L
    let o := P.o
    let equalT ← primT Kernel.Prim.equal
    -- under the quantifier: the name v0, the markers v1
    let φ := Internal.Logic.all o treeTy (Term.lam treeTy (Internal.Logic.imp o
      (notTest o (pc P "Prelude.isSome" [markerIdx P (v 0) (v 1)]))
      (notTest o (pc P "Prelude.isSome" [pc P "Recognize.markerOf" [v 1, v 0]]))))
    let lastFalse : Deducer := fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ
    let d₀ ← dAllI L (dImpI L (dImpI L (linkK K "markerOfNone: empty" lastFalse))) [] []
      (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
    let cons : Deducer := dAllI L <| dImpI L <| dImpI L fun Γ₁ Φ₁ ψ₁ ↦
      let (hd, key) := (atPos 0, atPos 2)
      let (hN, hM) := (Φ₁.length - 2, Φ₁.length - 1)
      -- the name the head's: its index the first, against the hypothesis; otherwise the rest's
      let headArm : Deducer :=
        decideIn K (fun Γ ↦ apps equalT [key Γ, child0 (hd Γ)])
          (K.cutThm "equalSymm" (fun Γ ↦ [key Γ, child0 (hd Γ)]) (K.impE (K.solve 3) lastFalse))
          (dImpE L hN (linkK K "markerOfNone: the head's index" (K.solve 3)) lastFalse)
      let restArm : Deducer := fun Γ Φ ψ ↦
        dAllE L K.G K.E 0 (key Γ) (K.impE (dImpI L fun Γ Φ ψ ↦
            let hI := Φ.length - 1
            decideIn K (fun Γ ↦ pc P "Prelude.isSome" [markerIdx P (key Γ) (atPos 1 Γ)])
              (linkK K "markerOfNone: no index at the rest" (K.hypFalse hI))
              (dImpE L hN (linkK K "markerOfNone: the index at the rest" (K.solve 3)) lastFalse)
              Γ Φ ψ)
          (K.impE (linkK K "markerOfNone: the marker at the rest" (K.byHyp hM)) lastFalse)) Γ Φ ψ
      decideIn K (fun Γ ↦ apps equalT [child0 (hd Γ), key Γ])
        (decideIn K (fun Γ ↦ apps equalT [key Γ, child0 (hd Γ)])
          (linkK K "markerOfNone: the rest" restArm)
          (linkK K "markerOfNone: a test without the other" fun Γ Φ ψ ↦
            K.cutThm "equalSymm" (fun Γ ↦ [child0 (hd Γ), key Γ]) (K.impE (K.solve 3) lastFalse)
              Γ Φ ψ))
        (linkK K "markerOfNone: the head" headArm) Γ₁ Φ₁ ψ₁
    let d₁ ← linkK K "markerOfNone: construction" cons [list treeTy, treeTy]
      [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, [list treeTy], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- An expression denoting a value denotes what equals it: the denotation rewritten by the equation.
In the context of the values and the expression. -/
def denVal (P : Prog) (S : Defs) : Step :=
  ("denVal", fun ix E ↦ do
    let K := denKit P S ix E
    let vars := [treeTy, treeTy, treeTy]
    let at_ := denAt vars
    let (e, w₁, w₂) := (at_ 6, at_ 7, at_ 8)
    let thm : Internal.Thm := ⟨0, denCtx vars, [Term.eq w₁ w₂, denIn P S vars e w₂],
      denIn P S vars e w₁⟩
    let some d := dRwBy (evalRw K.G K.E [.hyp 0] .full) dHyp thm.ctx thm.hyps thm.concl
      | dbgTrace "denVal: not proved" fun _ ↦ none
    pure (thm, d))

/-- That each marker's constructors, read as the typing reads them, have at most one of each label.
-/
def uniqsT (P : Prog) (ms : Term) : Term :=
  Internal.Logic.all P.o treeTy (Term.lam treeTy (uniqT P (specsOf P (sh 1 ms) (v 0))))

/-- That each of the children holds its bits. -/
def bitsAllT (P : Prog) (S : Defs) (ms cl R cs : Term) : Term :=
  S.allL (Term.lam treeTy (bitsOkT P (sh 1 ms) (sh 1 cl) (Term.app (sh 1 R) (v 0))
    (pc P "Typing.memberships" [sh 1 ms, v 0]))) cs

/-- The writer's optional bit of a datatype: its test, under the conditional of one and zero. -/
def elemT (P : Prog) (cl ms n : Term) : Term :=
  let mn := pc P "Recognize.markerOf" [ms, n]
  let t := pc P "Recognize.dataTest" [cl, pc P "Prelude.get" [mn]]
  let (some', none') := (pc P "Prelude.some", pc P "Prelude.none" [])
  condT treeTy (call D.lab [] [pc P "Prelude.isSome" [mn]])
    (condT treeTy (call D.lab [] [pc P "Prelude.isSome" [t]])
      (some' [pc P "Recognize.s4" [pc P "Recognize.rIf" [], pc P "Prelude.get" [t],
        pc P "Recognize.one" [], pc P "Recognize.zero" []]])
      none')
    none'

/-- The context of the bits of a node: an element, the label, the children, the function of a
child's bits, the markers and the closure. -/
def elemVars (A : Tree) : List Tree :=
  [A, bitsTy, list treeTy, exp treeTy treeTy, list treeTy, list treeTy]

/-- The hypotheses of the bits of a node, in a context of {name}`elemVars`: the variables of the
node, of the children's bits and of the label denote their values, {name}`writerHyps`, the markers'
constructors {name}`uniqsT`, and the children hold their bits. -/
def elemHyps (P : Prog) (S : Defs) (A : Tree) : List Term :=
  let vars := elemVars A
  let at_ := denAt vars
  let (cl, ms, R, cs, lb) := (at_ 6, at_ 7, at_ 8, at_ 9, at_ 10)
  [denIn P S vars (pc P "Recognize.vN" []) (quoteV P (node0 (mapFnT R cs))),
    denIn P S vars (pc P "Recognize.vR" []) (treeList P (quotesT P (mapFnT R cs))),
    denIn P S vars (pc P "Recognize.vL" []) (quoteV P (leafT lb))] ++
    writerHyps P ms (at_ 1) (at_ 2) (at_ 4) ++
    [uniqsT P ms, bitsAllT P S ms cl R cs]

/-- The writer's bit of a datatype, where it gives one, denotes the bit of the node's membership
({name}`bitT`). The datatype's marker is that of its index ({name}`markerOfNone`,
{name}`markerOfAt`), so its constructors are those the typing reads, whose test ({name}`dataDen`)
holds exactly where the node is a member ({lit}`memberCtors`, {name}`ctorsMember`), the membership
being the field's test ({name}`memberField`). -/
def elemDen (P : Prog) (S : Defs) : Step :=
  ("elemDen", fun ix E ↦ do
    let K₀ := fieldsKit P S ix E
    let K : Kit := { K₀ with
      P := { K₀.P with folded := (K₀.P.folded.filter (· != "Reader.both")) ++
        ["Recognize.ctorTest"] } }
    let P := K.P
    let L := K.L
    let base := 3
    let vars := elemVars treeTy
    let at_ := denAt vars
    let hyps := elemHyps P S treeTy
    let thm : Internal.Thm := ⟨0, denCtx vars,
      hyps ++ [truth P.o (pc P "Prelude.isSome" [elemT P (at_ 6) (at_ 7) (at_ 11)])],
      denIn P S vars (pc P "Prelude.get" [elemT P (at_ 6) (at_ 7) (at_ 11)])
        (quoteV P (bitT P (at_ 7) (at_ 11) (nodeT (Term.pair (at_ 10) (at_ 9)))))⟩
    let (clAt, msAt, RAt, csAt, lAt, nAt) :=
      (atPos 6, atPos 7, atPos 8, atPos 9, atPos 10, atPos 11)
    let (hU, hB, hE) := (hyps.length - 2, hyps.length - 1, hyps.length)
    let tAt (Γ : List Tree) : Term := nodeT (Term.pair (lAt Γ) (csAt Γ))
    let lastFalse : Deducer := fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ
    let lastHyp : Deducer := fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ
    let mp (h : ℕ) (prem k : Deducer) : Deducer := dImpE L h prem k
    let mnAt (Γ : List Tree) : Term := pc P "Recognize.markerOf" [msAt Γ, nAt Γ]
    let idxAt (Γ : List Tree) : Term := markerIdx P (nAt Γ) (msAt Γ)
    let mAt (Γ : List Tree) : Term := pc P "Typing/Txs.atOr" [pc P "Typing.tx0" [], msAt Γ,
      pc P "Prelude.get" [idxAt Γ]]
    let ctsAt (Γ : List Tree) : Term := call D.tail [treeTy] [call D.children [] [mAt Γ]]
    let foldAt (Γ : List Tree) : Term := pc P "Prelude.get" [dataFold P (clAt Γ) (ctsAt Γ)]
    let okAt (Γ : List Tree) : Term := pc P "Typing.fieldOk" [msAt Γ, nAt Γ,
      pc P "Typing.memberships" [msAt Γ, tAt Γ]]
    let hA (a : String) : Deducer := K.byHyp (atomHyp base a)
    let atomT (a : String) : Term := pc P s!"Recognize.{a}" []
    let writerAll : List Deducer :=
      [dHyp, dHyp] ++ (writerPrims.flatMap fun a ↦
        [K.byHyp (primHyp base a), K.byHyp (primHyp base a + 1)]) ++
      writerAtoms.map fun a ↦ K.byHyp (atomHyp base a)
    let leaf (n : ℕ) : Term := leafT (numeral n)
    -- the value: the membership decided, the field's test deciding the bit
    let close (wI gI : ℕ) : Deducer := fun Γ Φ ψ ↦
      let wAt := atPos wI
      let bitAt (Γ : List Tree) : Term := quoteV P (bitT P (msAt Γ) (nAt Γ) (tAt Γ))
      let formAt (Γ : List Tree) : Term := pc P "Recognize.s4" [atomT "rIf", foldAt Γ,
        atomT "one", atomT "zero"]
      let valueAt (Γ : List Tree) : Term :=
        quoteV P (condT treeTy (call D.lab [] [wAt Γ]) (leaf 1) (leaf 0))
      applyThm K "memberField" (fun Γ ↦ [tAt Γ, nAt Γ, msAt Γ]) [K.solve 3]
        (normLastK K <| applyThm K "denDigit/one" denFixed [hA "one"] <|
          applyThm K "denDigit/zero" denFixed [hA "zero"] <|
          applyThm K "denIf"
            (fun Γ ↦ [leaf 0, leaf 1, wAt Γ, atomT "zero", atomT "one", foldAt Γ] ++ denFixed Γ)
            [hA "rIf", dHyp, dHyp, dHyp] <|
          applyThm K "denVal" (fun Γ ↦ [valueAt Γ, bitAt Γ, formAt Γ] ++ denFixed Γ)
            [linkK K "elemDen: the value" <|
              dConjE L gI fun Γ Φ ψ ↦
              let (wTo, toW) := (Φ.length - 2, Φ.length - 1)
              decideIn K wAt
                (decideIn K okAt (linkK K "elemDen: both false" K.byNorm)
                  (linkK K "elemDen: a member without the bit" <|
                    applyThm K "memberCtors" (fun Γ ↦ [tAt Γ, nAt Γ, msAt Γ])
                      [linkK K "elemDen: the membership" (K.solve 3)]
                      (mp toW (linkK K "elemDen: the test's constructor" lastHyp) lastFalse)))
                (decideIn K okAt
                  (linkK K "elemDen: the bit without membership" <|
                    mp wTo (K.solve 3) <|
                    applyThm K "ctorsMember" (fun Γ ↦ [tAt Γ, nAt Γ, msAt Γ])
                      [linkK K "elemDen: the passing constructor" lastHyp] lastFalse)
                  (linkK K "elemDen: both true" K.byNorm)) Γ Φ ψ, dHyp] <|
          denAs K bitAt
            (fun Γ ↦ pc P "Prelude.get" [elemT P (clAt Γ) (msAt Γ) (nAt Γ)]) formAt) Γ Φ ψ
    let main : Deducer :=
      decideIn K (fun Γ ↦ pc P "Prelude.isSome" [mnAt Γ])
        (linkK K "elemDen: no marker" (K.hypFalse hE))
        (decideIn K (fun Γ ↦ pc P "Prelude.isSome" [idxAt Γ])
          (linkK K "elemDen: no index" (K.cutThm "markerOfNone" (fun Γ ↦ [msAt Γ]) <|
            K.allEΓ nAt <| K.impE (dImpI L lastFalse) <|
            fun Γ Φ ψ ↦ mp (Φ.length - 1) (K.solve 3) lastFalse Γ Φ ψ))
          (K.cutThm "markerOfAt" (fun Γ ↦ [msAt Γ]) <| K.allEΓ nAt <|
            K.impE (K.solve 3) <| normLastK K <|
            decideIn K (fun Γ ↦ pc P "Prelude.isSome" [dataFold P (clAt Γ) (ctsAt Γ)])
              (linkK K "elemDen: no test" (K.hypFalse hE))
              (linkK K "elemDen: the test" <|
              applyThm K "dataDen"
                (fun Γ ↦ [ctsAt Γ, leafT (lAt Γ), csAt Γ, RAt Γ, msAt Γ, clAt Γ] ++ denFixed Γ)
                ([dHyp, dHyp, dHyp] ++ writerAll) <|
              K.impE (fun Γ Φ ψ ↦ dAllE L K.G K.E hU (nAt Γ)
                (linkK K "elemDen: the constructors' labels" fun Γ Φ ψ ↦
                  normLastK K lastHyp Γ Φ ψ) Γ Φ ψ) <|
              K.impE (K.solve 3) <| K.exE <| K.conjE fun Γ Φ ψ ↦
                let (wI, gI) := (Γ.length - 1, Φ.length - 1)
                mp gI (K.byHyp hB) (fun Γ Φ ψ ↦ close wI (Φ.length - 1) Γ Φ ψ) Γ Φ ψ)))
    let some d := main thm.ctx thm.hyps thm.concl
      | dbgTrace "elemDen: not proved" fun _ ↦ none
    pure (thm, d))

/-- The writer's optional bits of a list of datatypes, by the prelude's right fold. -/
def bitsFold (P : Prog) (cl ms ns : Term) : Term :=
  foldrT treeTy (list treeTy) (Term.lam treeTy (Term.lam (list treeTy)
    (consT treeTy (elemT P (sh 2 cl) (sh 2 ms) (v 1)) (v 0)))) (nilT treeTy) ns

/-- The writer's list of the children of a node, by the prelude's right fold. -/
def chainE (P : Prog) (x : Term) : Term :=
  foldrT treeTy treeTy (Term.lam treeTy (Term.lam treeTy
    (pc P "Recognize.s3" [pc P "Recognize.rCons" [], v 1, v 0])))
    (pc P "Recognize.s2" [pc P "Recognize.rNil" [], pc P "Recognize.rT" []])
    (call D.children [] [x])

/-- The bits of a tree at a list of datatypes. -/
def bitsAt (P : Prog) (ms t ns : Term) : Term :=
  mapFnT (Term.lam treeTy (bitT P (sh 1 ms) (v 0) (sh 1 t))) ns

/-- The writer's list of the bits of a node ({name}`bitsAt`), where it gives them all, denotes the
list value of their quotations: by induction on the datatypes. A construction: the head's bit
({name}`elemDen`) and the rest's, in the writer's construction of a list ({name}`denCons`). -/
def chainDen (P : Prog) (S : Defs) : Step :=
  ("chainDen", fun ix E ↦ do
    let K₀ := fieldsKit P S ix E
    let K : Kit := { K₀ with
      P := { K₀.P with folded := (K₀.P.folded.filter (· != "Reader.both")) ++
        ["Recognize.ctorTest", "Recognize.dataTest", "Recognize.markerOf"] } }
    let P := K.P
    let L := K.L
    let base := 3
    let vars := elemVars (list treeTy)
    let at_ := denAt vars
    let Γ₀ := denCtx vars
    let hyps := elemHyps P S (list treeTy)
    let all (cl ms ns : Term) : Term := pc P "Reader.allSome" [bitsFold P cl ms ns]
    let value (ms lb cs ns : Term) : Term :=
      treeList P (quotesT P (bitsAt P ms (nodeT (Term.pair lb cs)) ns))
    let φ := Internal.Logic.imp P.o
      (truth P.o (pc P "Prelude.isSome" [all (at_ 6) (at_ 7) (at_ 11)]))
      (denIn P S vars (chainE P (pc P "Prelude.get" [all (at_ 6) (at_ 7) (at_ 11)]))
        (value (at_ 7) (at_ 10) (at_ 9) (at_ 11)))
    let some lowered := Internal.lowerHyps P.G 0 Γ₀.tail hyps
      | dbgTrace "chainDen: the hypotheses" fun _ ↦ none
    let (clAt, msAt, RAt, csAt, lAt) := (atPos 6, atPos 7, atPos 8, atPos 9, atPos 10)
    let hA (a : String) : Deducer := K.byHyp (atomHyp base a)
    let atomT (a : String) : Term := pc P s!"Recognize.{a}" []
    let chainOf (Γ : List Tree) (ns : Term) : Term :=
      chainE P (pc P "Prelude.get" [all (clAt Γ) (msAt Γ) ns])
    let d₀ ← (dImpI L <| applyThm K "denNil" denFixed [hA "rNil", hA "rT"] <|
      let nilV (_ : List Tree) : Term := treeList P (nilT treeTy)
      let nilE (_ : List Tree) : Term := pc P "Recognize.s2" [atomT "rNil", atomT "rT"]
      applyThm K "denVal" (fun Γ ↦ [nilV Γ, value (msAt Γ) (lAt Γ) (csAt Γ) (nilT treeTy),
          nilE Γ] ++ denFixed Γ)
        [linkK K "chainDen: the empty value" K.byNorm, dHyp] <|
      linkK K "chainDen: the empty list" <| fun Γ Φ ψ ↦
        denAsWith K [.delta (P.idx "Reader.allSome")]
          (fun Γ ↦ value (msAt Γ) (lAt Γ) (csAt Γ) (nilT treeTy))
          (fun Γ ↦ chainOf Γ (nilT treeTy)) nilE Γ Φ ψ) Γ₀.tail lowered
      (Term.subst φ fun i ↦ if i = 0 then nilT treeTy else v (i - 1))
    let (hdAt, tlAt) := (atPos 11, atPos 12)
    let ih := hyps.length
    let elemAt (Γ : List Tree) : Term := elemT P (clAt Γ) (msAt Γ) (hdAt Γ)
    let restAt (Γ : List Tree) : Term := bitsFold P (clAt Γ) (msAt Γ) (tlAt Γ)
    let premises : List Deducer :=
      [dHyp, dHyp, dHyp, dHyp, dHyp] ++ (writerPrims.flatMap fun a ↦
        [K.byHyp (primHyp base a), K.byHyp (primHyp base a + 1)]) ++
      (writerAtoms.map fun a ↦ K.byHyp (atomHyp base a)) ++ [dHyp, dHyp]
    let bitAt (Γ : List Tree) : Term := quoteV P (bitT P (msAt Γ) (hdAt Γ)
      (nodeT (Term.pair (lAt Γ) (csAt Γ))))
    let xsAt (Γ : List Tree) : Term :=
      quotesT P (bitsAt P (msAt Γ) (nodeT (Term.pair (lAt Γ) (csAt Γ))) (tlAt Γ))
    let finish : Deducer :=
      let formAt (Γ : List Tree) : Term := pc P "Recognize.s3" [atomT "rCons",
        pc P "Prelude.get" [elemAt Γ], chainOf Γ (tlAt Γ)]
      let consV (Γ : List Tree) : Term := treeList P (consT treeTy (bitAt Γ) (xsAt Γ))
      let goalV (Γ : List Tree) : Term :=
        value (msAt Γ) (lAt Γ) (csAt Γ) (consT treeTy (hdAt Γ) (tlAt Γ))
      applyThm K "denCons" (fun Γ ↦ [xsAt Γ, bitAt Γ, chainOf Γ (tlAt Γ),
          pc P "Prelude.get" [elemAt Γ]] ++ denFixed Γ) [hA "rCons", dHyp, dHyp] <|
      applyThm K "denVal" (fun Γ ↦ [consV Γ, goalV Γ, formAt Γ] ++ denFixed Γ)
        [linkK K "chainDen: the value" K.byNorm, dHyp] <|
      linkK K "chainDen: the construction's form" <|
        denAs K goalV (fun Γ ↦ chainOf Γ (consT treeTy (hdAt Γ) (tlAt Γ))) formAt
    let cons : Deducer := dImpI L fun Γ₁ Φ₁ ψ₁ ↦
      let hP := Φ₁.length - 1
      applyThm K "allSomeHead" (fun Γ ↦ [restAt Γ, elemAt Γ]) [K.byHyp hP] (fun Γ Φ ψ ↦
        let hH := Φ.length - 1
        applyThm K "allSomeRest" (fun Γ ↦ [restAt Γ, elemAt Γ]) [K.byHyp hP] (fun Γ Φ ψ ↦
          let hR := Φ.length - 1
          applyThm K "allSomeKids" (fun Γ ↦ [restAt Γ, elemAt Γ]) [K.byHyp hP] (normLastK K <|
            dImpE L ih (K.byHyp hR) <|
            applyThm K "elemDen" (fun Γ ↦ [hdAt Γ, lAt Γ, csAt Γ, RAt Γ, msAt Γ, clAt Γ] ++
                denFixed Γ) (premises ++ [K.byHyp hH]) finish) Γ Φ ψ) Γ Φ ψ) Γ₁ Φ₁ ψ₁
    let d₁ ← linkK K "chainDen: construction" cons (list treeTy :: treeTy :: Γ₀.tail)
      (lowered.map Internal.weaken2 ++ [Internal.weakenElem φ]) (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, Γ₀, hyps, φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The writer's abstraction over one binder denotes the closure of its environment over the body's
term, from the binder's reading and the body's. -/
def denLam1 (P : Prog) : DenRule :=
  let Tt := treeTy
  let vars := [Tt, Tt, Tt, Tt, Tt]
  let at_ := denAt vars
  let (b, e, x, A, t) := (at_ 6, at_ 7, at_ 8, at_ 9, at_ 10)
  let rLam := pc P "Recognize.rLam" []
  let ps := consT treeTy (kNode 0 [x, A]) (nilT treeTy)
  { name := "denLam1", vars, plain := [rLam],
    more := [Term.eq (pc P "Reader.readBinders" [at_ 3, pc P "Reader.binders"
        [pc P "Reader.expandNums" [at_ 1, b]]]) (pc P "Prelude.some" [node0 ps]),
      Term.eq (pc P "Reader.resolve" [at_ 3, at_ 2, pc P "Reader.expandNums" [at_ 1, e],
        consT treeTy x (at_ 4)]) (pc P "Prelude.some" [t])],
    form := pc P "Recognize.s3" [rLam, b, e],
    value := pc P "Eval.valClo" [at_ 5, A, t], levels := 1 }

/-- The writer's fold, by an expression denoting a function, of an expression denoting a quotation,
denotes the quotation of the tree to which the fold of the function converges. The type's reading is
given. -/
def denFold (P : Prog) (S0 : Defs) : DenRule :=
  let Tt := treeTy
  let vars := [Tt, Tt, Tt, Tt, Tt, Tt, Tt]
  let at_ := denAt vars
  let (a, A, f, e, g, x, u) := (at_ 6, at_ 7, at_ 8, at_ 9, at_ 10, at_ 11, at_ 12)
  let rFold := pc P "Recognize.rFold" []
  let F := Term.lam nat (pc P "Eval.foldVal" [Term.snd (S0.levelN (Term.fst (sh 1 (at_ 0))) (v 0)),
    sh 1 A, sh 1 g, sh 1 x])
  { name := "denFold", vars, plain := [rFold],
    more := [Term.eq (pc P "Reader.readType" [at_ 3, pc P "Reader.expandNums" [at_ 1, a]])
      (pc P "Prelude.some" [A])],
    subs := [sub f g, sub e (quoteV P x)],
    convs := [(S0.conv F (Term.lam treeTy (Term.eq (v 0) (quoteV P (sh 1 u)))), 0)],
    form := pc P "Recognize.s4" [rFold, a, f, e],
    value := quoteV P u, levels := 2,
    rules := apNames "apFold" 2 }

/-- The development of the recognizers' decisions. -/
def recognizerDev (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  [lenMap P S, arityMap P S, allDrop P S, allTrees P S, ctorDen P S, eqSelfB P S, eqSym P S,
    succBelowTwo P S, belowTwoDown P S, uniqTail P S, uniqHead P S, dataDen P S, valuesConv P S,
    roseAllFor P S "foldExactAll" (foldExactφ P S), foldExact P S, markerOfAt P S, ctorsMember P S,
    atIndexOf P S, bitsFnOk P S, bitsFnAll P S, memberField P S, markerOfNone P S, denVal P S,
    elemDen P S, chainDen P S, denRule P S T (denLam1 P), denRule P S T (denFold P S)]

/-- The development of {name}`recognizerDev`, after the walk's, stored as the certificate
{lit}`datatype-recognizer`. -/
def recognizerCertificates (P : Prog) (S : Defs) (T : Defs3) (before : List Internal.Thm) :
    Except String (List Stored.Cert) := do
  let some names := walkAfter P S T | throw "the base is not stated"
  certifyAfter P (names ++ (walkDev P S T).map (·.1)) "datatype-recognizer" (recognizerDev P S T)
    before

/-- The writer's optional bits of a closure, as the recognizer's let. -/
def bitsAllE (P : Prog) (cl ms : Term) : Term := pc P "Reader.allSome" [bitsFold P cl ms cl]

/-- The writer's node of the children's bits. -/
def nodeRForm (P : Prog) : Term :=
  pc P "Recognize.s3" [pc P "Recognize.rNode" [], pc P "Recognize.zero" [], pc P "Recognize.vR" []]

/-- The writer's node of a node's bits. -/
def nodeChainForm (P : Prog) (cl ms : Term) : Term :=
  pc P "Recognize.s3" [pc P "Recognize.rNode" [], pc P "Recognize.zero" [],
    chainE P (pc P "Prelude.get" [bitsAllE P cl ms])]

/-- The body of the writer's step: the node of the children's bits, bound, around the node of the
node's bits. -/
def stepBodyForm (P : Prog) (cl ms : Term) : Term :=
  pc P "Recognize.sx" [consT treeTy (pc P "Recognize.rLet" [])
    (consT treeTy (pc P "Recognize.vN" []) (consT treeTy (pc P "Recognize.rT" [])
      (consT treeTy (nodeRForm P) (consT treeTy (nodeChainForm P cl ms) (nilT treeTy)))))]

/-- The scope of the body of the writer's step. -/
def stepScope (P : Prog) (scope : Term) : Term :=
  consT treeTy (atomNameT (pc P "Recognize.vR" []))
    (consT treeTy (atomNameT (pc P "Recognize.vL" [])) scope)

/-- The environment of the body of the writer's step, at a label and the children's bits. -/
def stepEnv (P : Prog) (lb R cs env : Term) : Term :=
  consT treeTy (treeList P (quotesT P (mapFnT R cs)))
    (consT treeTy (quoteV P (leafT lb)) env)

/-- The context of the writer's step's body: the label, the children, the function of a child's
bits, the markers and the closure. -/
def stepVars : List Tree :=
  [bitsTy, list treeTy, exp treeTy treeTy, list treeTy, list treeTy]

/-- The body of the writer's step, where the writer gives the bits, denotes the node of the bits of
the node, at children holding their bits. The node of the children's bits, by {name}`denNode`, is
the let's binding ({name}`denLet`), under which the variables of the node, the children's bits and
the label denote what {name}`chainDen` asks. -/
def stepBodyDen (P : Prog) (S : Defs) : Step :=
  ("stepBodyDen", fun ix E ↦ do
    let K₀ := fieldsKit P S ix E
    let K : Kit := { K₀ with
      P := { K₀.P with folded := (K₀.P.folded.filter (· != "Reader.both")) ++
        ["Recognize.ctorTest", "Recognize.dataTest", "Recognize.markerOf"] }
      more := K₀.more ++ (["indexOfCons", "indexOfNil"].filter
        fun nm ↦ 0 < ix nm ∧ ix nm < E.size) }
    let P := K.P
    let L := K.L
    let vars := stepVars
    let at_ := denAt vars
    let (cl, ms, R, cs, lb) := (at_ 6, at_ 7, at_ 8, at_ 9, at_ 10)
    let value (ms lb cs cl : Term) : Term :=
      quoteV P (node0 (bitsAt P ms (nodeT (Term.pair lb cs)) cl))
    let hyps : List Term := [truth P.o (pc P "Prelude.isSome" [bitsAllE P cl ms])] ++
      writerHyps P ms (at_ 1) (at_ 2) (at_ 4) ++ [uniqsT P ms, bitsAllT P S ms cl R cs]
    let thm : Internal.Thm := ⟨0, denCtx vars, hyps,
      denT P S (at_ 0) (at_ 3) (at_ 2) (at_ 1) (stepScope P (at_ 4)) (stepEnv P lb R cs (at_ 5))
        (stepBodyForm P cl ms) (value ms lb cs cl)⟩
    let base := 1
    let (clAt, msAt, RAt, csAt, lAt) := (atPos 6, atPos 7, atPos 8, atPos 9, atPos 10)
    let hA (a : String) : Deducer := K.byHyp (atomHyp base a)
    let atomT (a : String) : Term := pc P s!"Recognize.{a}" []
    let lastFalse : Deducer := fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ
    let mp (h : ℕ) (prem k : Deducer) : Deducer := dImpE L h prem k
    let scope₂ (Γ : List Tree) : Term := stepScope P (atPos 4 Γ)
    let env₂ (Γ : List Tree) : Term := stepEnv P (lAt Γ) (RAt Γ) (csAt Γ) (atPos 5 Γ)
    let scope₃ (Γ : List Tree) : Term := consT treeTy (atomNameT (atomT "vN")) (scope₂ Γ)
    let nodeV (Γ : List Tree) : Term := quoteV P (node0 (mapFnT (RAt Γ) (csAt Γ)))
    let env₃ (Γ : List Tree) : Term := consT treeTy (nodeV Γ) (env₂ Γ)
    let fixedAt (sc en : List Tree → Term) (Γ : List Tree) : List Term :=
      [en Γ, sc Γ, atPos 3 Γ, atPos 2 Γ, atPos 1 Γ, atPos 0 Γ]
    let fixed₂ := fixedAt scope₂ env₂
    let fixed₃ := fixedAt scope₃ env₃
    -- a primitive's name absent from a scope extended by the atoms
    let absentIn (a : String) : Deducer := dImpI L fun Γ Φ ψ ↦
      let hI := Φ.length - 1
      decideIn K (fun Γ ↦ pc P "Prelude.isSome" [pc P "Reader.indexOf"
          [atomNameT (atomT a), atPos 4 Γ]])
        (linkK K "stepBodyDen: absent, in the atoms" (K.hypFalse hI))
        (mp (primHyp base a) (K.solve 3) lastFalse) Γ Φ ψ
    let absentAll : List Deducer := writerPrims.flatMap fun a ↦
      [absentIn a, K.byHyp (primHyp base a + 1)]
    let varDen (nm a : String) (i : ℕ) (w : List Tree → Term) (fx : List Tree → List Term)
        (k : Deducer) : Deducer :=
      applyThm K s!"denVar/{nm}" (fun Γ ↦ [w Γ, leafT (numeral i)] ++ fx Γ)
        [hA a, linkK K s!"stepBodyDen: the index of {a}" K.byNorm,
          linkK K s!"stepBodyDen: the value of {a}" fun Γ Φ ψ ↦
            (K.byNorm Γ Φ ψ).orElse fun _ ↦
              K.cutThm "nthSuccRaw" (fun Γ ↦ [numeral 1, env₂ Γ, nodeV Γ]) (normLastK K K.byNorm)
                Γ Φ ψ] k
    let zero := leafT (numeral 0)
    let kids (Γ : List Tree) : Term := mapFnT (RAt Γ) (csAt Γ)
    let bits (Γ : List Tree) : Term :=
      bitsAt P (msAt Γ) (nodeT (Term.pair (lAt Γ) (csAt Γ))) (clAt Γ)
    let rsV (Γ : List Tree) : Term := treeList P (quotesT P (kids Γ))
    let lbV (Γ : List Tree) : Term := quoteV P (leafT (lAt Γ))
    let chainF (Γ : List Tree) : Term :=
      chainE P (pc P "Prelude.get" [bitsAllE P (clAt Γ) (msAt Γ)])
    let nodeOf (xs : Term) : Term := quoteV P (nodeT (Term.pair (call D.lab [] [zero]) xs))
    -- the premises of the chain, at the third scope and environment
    let chainPrems : List Deducer :=
      [dHyp, dHyp, dHyp, dHyp, dHyp] ++ absentAll ++
      (writerAtoms.map fun a ↦ K.byHyp (atomHyp base a)) ++ [dHyp, dHyp]
    let inner : Deducer :=
      applyThm K "denDigit/zero" fixed₃ [hA "zero"] <|
      varDen "l" "vL" 2 lbV fixed₃ <| varDen "r" "vR" 1 rsV fixed₃ <|
      varDen "n" "vN" 0 nodeV fixed₃ <|
      applyThm K "chainDen" (fun Γ ↦ [clAt Γ, lAt Γ, csAt Γ, RAt Γ, msAt Γ, clAt Γ] ++ fixed₃ Γ)
        chainPrems <|
      K.impE (K.byHyp 0) <|
      applyThm K "denNode" (fun Γ ↦ [bits Γ, zero, chainF Γ, atomT "zero"] ++ fixed₃ Γ)
        [absentIn "rNode", K.byHyp (primHyp base "rNode" + 1), hA "rNode", dHyp, dHyp] <|
      applyThm K "denVal" (fun Γ ↦ [nodeOf (bits Γ), value (msAt Γ) (lAt Γ) (csAt Γ) (clAt Γ),
          nodeChainForm P (clAt Γ) (msAt Γ)] ++ fixed₃ Γ)
        [linkK K "stepBodyDen: the node's value" K.byNorm, dHyp] <|
      fun Γ Φ ψ ↦ dHyp Γ Φ ψ
    let main : Deducer :=
      applyThm K "denDigit/zero" fixed₂ [hA "zero"] <|
      varDen "r" "vR" 0 rsV fixed₂ <|
      applyThm K "denNode" (fun Γ ↦ [kids Γ, zero, atomT "vR", atomT "zero"] ++ fixed₂ Γ)
        [absentIn "rNode", K.byHyp (primHyp base "rNode" + 1), hA "rNode", dHyp, dHyp] <|
      applyThm K "denVal" (fun Γ ↦ [nodeOf (kids Γ), nodeV Γ, nodeRForm P] ++ fixed₂ Γ)
        [linkK K "stepBodyDen: the children's value" K.byNorm, dHyp] <|
      fun Γ Φ ψ ↦ do
        let bodyDen := denT P S (atPos 0 Γ) (atPos 3 Γ) (atPos 2 Γ) (atPos 1 Γ) (scope₃ Γ) (env₃ Γ)
          (nodeChainForm P (clAt Γ) (msAt Γ)) (value (msAt Γ) (lAt Γ) (csAt Γ) (clAt Γ))
        let dB ← linkK K "stepBodyDen: the body" inner Γ Φ bodyDen
        dCut bodyDen dB
          (applyThm K "denLet/n" (fun Γ ↦ [value (msAt Γ) (lAt Γ) (csAt Γ) (clAt Γ), nodeV Γ,
              nodeChainForm P (clAt Γ) (msAt Γ), nodeRForm P] ++ fixed₂ Γ)
            [hA "rLet", hA "rT", hA "vN", dHyp, dHyp] dHyp) Γ Φ ψ
    let some d := main thm.ctx thm.hyps thm.concl
      | dbgTrace "stepBodyDen: not proved" fun _ ↦ none
    pure (thm, d))

/-- The writer's step of the recognizer's fold. -/
def stepForm (P : Prog) (cl ms : Term) : Term :=
  pc P "Recognize.s3" [pc P "Recognize.rLam" [], pc P "Recognize.bind2" [pc P "Recognize.vL" [],
    pc P "Recognize.rT" [], pc P "Recognize.vR" [], pc P "Recognize.tList" []],
    stepBodyForm P cl ms]

/-- The writer's step, where the writer gives the bits, denotes a function whose fold converges at
every tree to the quotation of the tree's bits ({name}`bitsFn`). The body's term from its denotation
at the empty label and children ({name}`stepBodyDen`), the same at every other by the reading's
equation; the fold by {name}`foldExact`, the children holding their bits by {name}`bitsFnAll`. In
the context of the markers and the closure. -/
def stepDen (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("stepDen", fun ix E ↦ do
    let Kd := denKit P S ix E
    let K₀ := fieldsKit P S ix E
    let K : Kit := { K₀ with
      P := { K₀.P with folded := (K₀.P.folded.filter (· != "Reader.both")) ++
        ["Recognize.ctorTest", "Recognize.dataTest", "Recognize.markerOf"] } }
    let P := K.P
    let L := K.L
    let o := P.o
    let vars := [list treeTy, list treeTy]
    let at_ := denAt vars
    let (cl, ms) := (at_ 6, at_ 7)
    let hyps : List Term := [truth o (pc P "Prelude.isSome" [bitsAllE P cl ms])] ++
      writerHyps P ms (at_ 1) (at_ 2) (at_ 4) ++ [uniqsT P ms]
    -- beneath the function v0
    let conclAt (g Dv cl ms : Term) : Term :=
      Internal.Logic.all o treeTy (Term.lam treeTy (S.conv
        (Term.lam nat (pc P "Eval.foldVal" [Term.snd (S.levelN (Term.fst (sh 2 Dv)) (v 0)), tyTreeT,
          sh 2 g, v 1]))
        (Term.lam treeTy (Term.eq (v 0)
          (quoteV P (Term.app (bitsFn P (sh 2 ms) (sh 2 cl)) (v 1)))))))
    let thm : Internal.Thm := ⟨0, denCtx vars, hyps,
      Internal.Logic.ex o treeTy (Term.lam treeTy (Internal.Logic.conj o
        (denT P S (sh 1 (at_ 0)) (sh 1 (at_ 3)) (sh 1 (at_ 2)) (sh 1 (at_ 1)) (sh 1 (at_ 4))
          (sh 1 (at_ 5)) (sh 1 (stepForm P cl ms)) (v 0))
        (conclAt (v 0) (sh 1 (at_ 0)) (sh 1 cl) (sh 1 ms))))⟩
    let base := 1
    let (clAt, msAt) := (atPos 6, atPos 7)
    let hA (a : String) : Deducer := K.byHyp (atomHyp base a)
    let atomT (a : String) : Term := pc P s!"Recognize.{a}" []
    let Rat (Γ : List Tree) : Term := bitsFn P (msAt Γ) (clAt Γ)
    let getT (t : Term) : Term := pc P "Prelude.get" [t]
    let bodyF (Γ : List Tree) : Term := stepBodyForm P (clAt Γ) (msAt Γ)
    -- the body's denotation at a label and children
    let writerAll : List Deducer :=
      [dHyp, dHyp] ++ (writerPrims.flatMap fun a ↦
        [K.byHyp (primHyp base a), K.byHyp (primHyp base a + 1)]) ++
      writerAtoms.map fun a ↦ K.byHyp (atomHyp base a)
    let bodyAt (l cs : List Tree → Term) (k : Deducer) : Deducer :=
      K.cutThm "bitsFnAll" (fun Γ ↦ [cs Γ, clAt Γ, msAt Γ]) <|
      linkK K "stepDen: bodyAt" fun Γ Φ ψ ↦
        let hB := Φ.length - 1
        applyThm K "stepBodyDen" (fun Γ ↦ [l Γ, cs Γ, Rat Γ, msAt Γ, clAt Γ] ++ denFixed Γ)
          ([K.byHyp 0] ++ writerAll ++ [dHyp, K.byHyp hB]) k Γ Φ ψ
    let hStep : Deducer :=
      dAllI L <| dAllI L fun Γ₁ Φ₁ ψ₁ ↦
      let (l, cs) := (atPos (Γ₁.length - 2), atPos (Γ₁.length - 1))
      bodyAt l cs (fun Γ Φ ψ ↦
        denE K (Φ.length - 1) (fun _ n _ st Γ Φ ψ ↦
          K.image (Φ.length - 1) getT (fun Γ Φ ψ ↦
            K.conv (fun Γ ↦ succs 2 (atPos n Γ))
              (fun Γ ↦ quoteV P (Term.app (Rat Γ) (nodeT (Term.pair (l Γ) (cs Γ)))))
              (linkK K "stepDen: the step stable" <| instNK K st (fun _ ↦ succs 1 (v 0)) K.byNorm)
              (linkK K "stepDen: the step's value" (K.solve 3)) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ) Γ₁ Φ₁ ψ₁
    let unfold := resolveRules P T ix E ++ [.delta (T.argIdx 3)]
    let byU (msg : String) : Deducer := fun Γ Φ ψ ↦
      (dEq (fun Γ Φ t u ↦ byMode .full Kd.G Kd.E 0 (Kd.rules Φ ++ unfold) Γ
        (rwHyps (Kd.rules Φ) Φ) t u) Γ Φ ψ).orElse fun _ ↦ do
        let (lhs, rhs) ← Internal.eqParts ψ
        let (l', _) ← evalRw Kd.G Kd.E (Kd.rules Φ ++ unfold) .full Γ Φ lhs
        let (r', _) ← evalRw Kd.G Kd.E (Kd.rules Φ ++ unfold) .full Γ Φ rhs
        dbgTrace s!"stepDen: {msg}: {(firstDiff l' r').map fun (a, b) ↦
          s!"{showT a}\n  vs {showT b}"}" fun _ ↦ none
    let isAbbrev (a : String) (Γ : List Tree) : Term := pc P "Prelude.isSome"
      [pc P "Reader.lookupAbbrev" [atomNameT (atomT a), atPos 1 Γ]]
    let decided (names : List String) (k : Deducer) : Deducer :=
      names.foldr (fun a k ↦ decideIn K (isAbbrev a) k
        (dImpE L (atomHyp base a) (K.solve 3) fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ)) k
    let bindF : Term := pc P "Recognize.bind2" [atomT "vL", atomT "rT", atomT "vR",
      pc P "Recognize.tList" []]
    let withTerm (t₀ : ℕ) : Deducer := fun Γ Φ ψ ↦
      let gAt (Γ : List Tree) : Term :=
        pc P "Eval.valClo" [atPos 5 Γ, tyTreeT, lamT kListT (atPos t₀ Γ)]
      dExI L K.G K.E (gAt Γ) (dConjI L
        (linkK K "stepDen: the abstraction" <| decided ["vL", "vR", "rT", "rList"] <|
          applyThm K "denLam2" (fun Γ ↦ [atPos t₀ Γ, kListT, atomNameT (atomT "vR"), tyTreeT,
              atomNameT (atomT "vL"), bodyF Γ, bindF] ++ denFixed Γ)
            [hA "rLam", byU "the binders", linkK K "stepDen: the body's reading" K.byNorm] dHyp)
        (linkK K "stepDen: the fold" <| dAllI L fun Γ₁ Φ₁ ψ₁ ↦
          let tAt := atPos (Γ₁.length - 1)
          let hT (Γ : List Tree) : Term :=
            foldStepT P S (Rat Γ) (gAt Γ) tyTreeT (atPos 0 Γ)
          K.cutThm "foldExact" (fun Γ ↦ [tAt Γ]) (K.allEΓ (atPos 0) (K.allEΓ (fun _ ↦ tyTreeT)
            (K.allEΓ gAt (K.allEΓ Rat (linkK K "stepDen: instantiated" fun Γ Φ ψ ↦ do
              let dH ← linkK K "stepDen: the steps" hStep Γ Φ (hT Γ)
              dCut (hT Γ) dH (dImpE L (Φ.length - 1) (K.byHyp Φ.length) (fun Γ Φ ψ ↦
                (dHyp Γ Φ ψ).orElse fun _ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ)) Γ Φ ψ))))) Γ₁ Φ₁ ψ₁))
        Γ Φ ψ
    let main : Deducer :=
      bodyAt (fun _ ↦ bnilT) (fun _ ↦ nilT treeTy) <| linkK K "stepDen: after the body" <|
        fun Γ Φ ψ ↦
        denE K (Φ.length - 1) (fun t₀ _ _ _ ↦ linkK K "stepDen: with the term" (withTerm t₀)) Γ Φ ψ
    let some d := main thm.ctx thm.hyps thm.concl
      | dbgTrace "stepDen: not proved" fun _ ↦ none
    pure (thm, d))

/-- The writer's fold of the recognizer. -/
def foldForm (P : Prog) (cl ms : Term) : Term :=
  pc P "Recognize.s4" [pc P "Recognize.rFold" [], pc P "Recognize.rT" [], stepForm P cl ms,
    pc P "Recognize.vT" []]

/-- The body of the writer's recognizer: the bit at the first position of the fold. -/
def recBodyForm (P : Prog) (cl ms : Term) : Term :=
  pc P "Recognize.s3" [pc P "Recognize.rChild" [], foldForm P cl ms,
    pc P "Recognize.num" [leafT (numeral 0)]]

/-- The writer's recognizer's abstraction. -/
def recForm (P : Prog) (cl ms : Term) : Term :=
  pc P "Recognize.s3" [pc P "Recognize.rLam" [], pc P "Recognize.bind1" [pc P "Recognize.vT" [],
    pc P "Recognize.rT" []], recBodyForm P cl ms]

/-- The writer's recognizer's abstraction, where the writer gives the bits, denotes a function which
at the quotation of every tree converges to the quotation of the bit at the first position of the
tree's bits. The body's term from its denotation at the empty tree, the same at every other by the
reading's equation; the body by the step's denotation ({name}`stepDen`) and the rules of the fold
and of the numeral's child. In the context of the markers and the closure. -/
def recDen (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("recDen", fun ix E ↦ do
    let Kd := denKit P S ix E
    let K₀ := fieldsKit P S ix E
    let K : Kit := { K₀ with
      P := { K₀.P with folded := (K₀.P.folded.filter (· != "Reader.both")) ++
        ["Recognize.ctorTest", "Recognize.dataTest", "Recognize.markerOf"] }
      more := K₀.more ++ (["indexOfCons", "indexOfNil"].filter
        fun nm ↦ 0 < ix nm ∧ ix nm < E.size) }
    let P := K.P
    let L := K.L
    let o := P.o
    let vars := [list treeTy, list treeTy]
    let at_ := denAt vars
    let (cl, ms) := (at_ 6, at_ 7)
    let childT := (primT Kernel.Prim.child).getD Term.star
    let hyps : List Term := [truth o (pc P "Prelude.isSome" [bitsAllE P cl ms])] ++
      writerHyps P ms (at_ 1) (at_ 2) (at_ 4) ++ [uniqsT P ms]
    let zero := leafT (numeral 0)
    -- beneath the function v0
    let conclAt (g Dv cl ms : Term) : Term :=
      Internal.Logic.all o treeTy (Term.lam treeTy (S.conv
        (Term.lam nat (apps (Term.snd (S.levelN (Term.fst (sh 2 Dv)) (v 0)))
          [sh 2 g, quoteV P (v 1)]))
        (Term.lam treeTy (Term.eq (v 0) (quoteV P (apps childT
          [Term.app (bitsFn P (sh 2 ms) (sh 2 cl)) (v 1), zero]))))))
    let thm : Internal.Thm := ⟨0, denCtx vars, hyps,
      Internal.Logic.ex o treeTy (Term.lam treeTy (Internal.Logic.conj o
        (denT P S (sh 1 (at_ 0)) (sh 1 (at_ 3)) (sh 1 (at_ 2)) (sh 1 (at_ 1)) (sh 1 (at_ 4))
          (sh 1 (at_ 5)) (sh 1 (recForm P cl ms)) (v 0))
        (conclAt (v 0) (sh 1 (at_ 0)) (sh 1 cl) (sh 1 ms))))⟩
    let base := 1
    let (clAt, msAt) := (atPos 6, atPos 7)
    let hA (a : String) : Deducer := K.byHyp (atomHyp base a)
    let atomT (a : String) : Term := pc P s!"Recognize.{a}" []
    let lastFalse : Deducer := fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ
    let lastHyp : Deducer := fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ
    let Rat (Γ : List Tree) : Term := bitsFn P (msAt Γ) (clAt Γ)
    let getT (t : Term) : Term := pc P "Prelude.get" [t]
    let bodyF (Γ : List Tree) : Term := recBodyForm P (clAt Γ) (msAt Γ)
    let unfold := resolveRules P T ix E ++ [.delta (T.argIdx 3)]
    let byU (msg : String) : Deducer := fun Γ Φ ψ ↦
      (dEq (fun Γ Φ t u ↦ byMode .full Kd.G Kd.E 0 (Kd.rules Φ ++ unfold) Γ
        (rwHyps (Kd.rules Φ) Φ) t u) Γ Φ ψ).orElse fun _ ↦ do
        let (lhs, rhs) ← Internal.eqParts ψ
        let (l', _) ← evalRw Kd.G Kd.E (Kd.rules Φ ++ unfold) .full Γ Φ lhs
        let (r', _) ← evalRw Kd.G Kd.E (Kd.rules Φ ++ unfold) .full Γ Φ rhs
        dbgTrace s!"recDen: {msg}: {(firstDiff l' r').map fun (a, b) ↦
          s!"{showT a}\n  vs {showT b}"}" fun _ ↦ none
    let isAbbrev (a : String) (Γ : List Tree) : Term := pc P "Prelude.isSome"
      [pc P "Reader.lookupAbbrev" [atomNameT (atomT a), atPos 1 Γ]]
    let decided (names : List String) (k : Deducer) : Deducer :=
      names.foldr (fun a k ↦ decideIn K (isAbbrev a) k
        (dImpE L (atomHyp base a) (K.solve 3) lastFalse)) k
    -- a primitive's name absent from the scope extended by the tree's variable
    let absentIn (a : String) : Deducer := dImpI L fun Γ Φ ψ ↦
      let hI := Φ.length - 1
      decideIn K (fun Γ ↦ pc P "Prelude.isSome" [pc P "Reader.indexOf"
          [atomNameT (atomT a), atPos 4 Γ]])
        (linkK K "recDen: absent, at the variable" (K.hypFalse hI))
        (dImpE L (primHyp base a) (K.solve 3) lastFalse) Γ Φ ψ
    -- the body's denotation at a tree
    let bodyAt (t : List Tree → Term) (k : Deducer) : Deducer :=
      let scope₁ (Γ : List Tree) : Term := consT treeTy (atomNameT (atomT "vT")) (atPos 4 Γ)
      let env₁ (Γ : List Tree) : Term := consT treeTy (quoteV P (t Γ)) (atPos 5 Γ)
      let fixed₁ (Γ : List Tree) : List Term :=
        [env₁ Γ, scope₁ Γ, atPos 3 Γ, atPos 2 Γ, atPos 1 Γ, atPos 0 Γ]
      let stepF (Γ : List Tree) : Term := stepForm P (clAt Γ) (msAt Γ)
      let foldF (Γ : List Tree) : Term := foldForm P (clAt Γ) (msAt Γ)
      let writerAll : List Deducer :=
        [dHyp, dHyp] ++ (writerPrims.flatMap fun a ↦
          [absentIn a, K.byHyp (primHyp base a + 1)]) ++
        writerAtoms.map fun a ↦ K.byHyp (atomHyp base a)
      let Rt (Γ : List Tree) : Term := Term.app (Rat Γ) (t Γ)
      applyThm K "denVar/t" (fun Γ ↦ [quoteV P (t Γ), zero] ++ fixed₁ Γ)
        [hA "vT", linkK K "recDen: the variable's index" K.byNorm,
          linkK K "recDen: the variable's value" K.byNorm] <|
      applyThm K "stepDen" (fun Γ ↦ [msAt Γ, clAt Γ] ++ fixed₁ Γ)
        ([K.byHyp 0] ++ writerAll ++ [dHyp]) <|
      K.exE <| K.conjE fun Γ Φ ψ ↦
        let gAt := atPos (Γ.length - 1)
        let hC := Φ.length - 1
        dAllE L K.G K.E hC (t Γ) (
        applyThm K "denFold" (fun Γ ↦ [Rt Γ, t Γ, gAt Γ, atomT "vT", stepF Γ, tyTreeT,
            atomT "rT"] ++ fixed₁ Γ)
          [hA "rFold", byU "the type", dHyp, dHyp,
            linkK K "recDen: the fold's convergence" fun Γ Φ ψ ↦
              (dHyp Γ Φ ψ).orElse fun _ ↦ lastHyp Γ Φ ψ] <|
        fun Γ Φ ψ ↦
        dAllE L K.G K.E (base + 1) zero (normLastK K <| K.conjE fun Γ₁ Φ₁ ψ₁ ↦
          let h₁ := Φ₁.length - 2
          K.conjE (fun Γ₂ Φ₂ ψ₂ ↦
            applyThm K "denNum" (fun Γ ↦ zero :: fixed₁ Γ) [K.byHyp h₁, K.byNorm,
              K.byHyp (Φ₂.length - 1)] (
            applyThm K "denPrim2/child" (fun Γ ↦ [zero, Rt Γ,
                pc P "Recognize.num" [zero], foldF Γ] ++ fixed₁ Γ)
              [absentIn "rChild", K.byHyp (primHyp base "rChild" + 1), hA "rChild", dHyp, dHyp]
              k) Γ₂ Φ₂ ψ₂) Γ₁ Φ₁ ψ₁) Γ Φ ψ) Γ Φ ψ
    let bindF : Term := pc P "Recognize.bind1" [atomT "vT", atomT "rT"]
    let withTerm (t₀ : ℕ) : Deducer := fun Γ Φ ψ ↦
      let cloAt (Γ : List Tree) : Term := pc P "Eval.valClo" [atPos 5 Γ, tyTreeT, atPos t₀ Γ]
      dExI L K.G K.E (cloAt Γ) (dConjI L
        (linkK K "recDen: the abstraction" <| decided ["vT"] <|
          applyThm K "denLam1" (fun Γ ↦ [atPos t₀ Γ, tyTreeT, atomNameT (atomT "vT"), bodyF Γ,
              bindF] ++ denFixed Γ)
            [hA "rLam", byU "the binder", linkK K "recDen: the body's reading" K.byNorm] dHyp)
        (linkK K "recDen: the applications" <| dAllI L fun Γ₁ Φ₁ ψ₁ ↦
          let tAt := atPos (Γ₁.length - 1)
          bodyAt tAt (fun Γ Φ ψ ↦
            denE K (Φ.length - 1) (fun _ n _ st Γ Φ ψ ↦
              K.image (Φ.length - 1) getT (fun Γ Φ ψ ↦
                K.conv (fun Γ ↦ succs 1 (atPos n Γ))
                  (fun Γ ↦ quoteV P (apps childT [Term.app (Rat Γ) (tAt Γ), zero]))
                  (linkK K "recDen: the application stable" <| instNK K st (fun _ ↦ v 0) K.byNorm)
                  (linkK K "recDen: the application's value" (K.solve 3)) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ)
            Γ₁ Φ₁ ψ₁)) Γ Φ ψ
    let main : Deducer :=
      decided ["rT"] <| bodyAt (fun _ ↦ zero) <| linkK K "recDen: after the body" <| fun Γ Φ ψ ↦
        denE K (Φ.length - 1) (fun t₀ _ _ _ ↦ linkK K "recDen: with the term" (withTerm t₀)) Γ Φ ψ
    let some d := main thm.ctx thm.hyps thm.concl
      | dbgTrace "recDen: not proved" fun _ ↦ none
    pure (thm, d))

/-- That a list of trees begins with a tree, in a context under which both are written. -/
def headsT (o : ℕ) (xs d : Term) : Term :=
  let Ls := list treeTy
  Internal.Logic.ex o Ls (Term.lam Ls (Term.eq (sh 1 xs) (consT treeTy (sh 1 d) (v 0))))

/-- The writer's addition of new datatypes, as the fold of {lit}`Recognize.addNew`. -/
def addFold (P : Prog) (cl ys : Term) : Term :=
  let Ls := list treeTy
  foldrT treeTy Ls (Term.lam treeTy (Term.lam Ls (condT Ls
    (call D.lab [] [pc P "Prelude.isSome" [pc P "Reader.indexOf" [v 1, v 0]]]) (v 0)
    (pc P "Prelude.append" [v 0, pc P "Prelude.single" [v 1]])))) cl ys

/-- The kit of the first datatype of a closure: the markers' lookups folded. -/
def headKit (P : Prog) (S : Defs) (ix : String → ℕ) (E : Array Internal.Entry) : Kit :=
  let K₀ := writerKit P S ix E
  { K₀ with P := { K₀.P with folded := K₀.P.folded ++ ["Recognize.markerOf", "Recognize.depsOf"] } }

/-- The addition of datatypes keeps a list's first: by induction on the datatypes, the first's
presence decided. In the context of the datatypes, the first and the list. -/
def addFoldHead (P : Prog) (S : Defs) : Step :=
  ("addFoldHead", fun ix E ↦ do
    let K := headKit P S ix E
    let P := K.P
    let L := K.L
    let Ls := list treeTy
    let Γ₀ := [Ls, treeTy, Ls]
    let hyp := headsT P.o (v 2) (v 1)
    let φ := headsT P.o (addFold P (v 2) (v 0)) (v 1)
    let some lowered := Internal.lowerHyps P.G 0 Γ₀.tail [hyp]
      | dbgTrace "addFoldHead: the hypothesis" fun _ ↦ none
    let d₀ ← linkK K "addFoldHead: empty" (K.byHyp 0) Γ₀.tail lowered
      (Term.subst φ fun i ↦ if i = 0 then nilT treeTy else v (i - 1))
    let (dAt, yAt) := (atPos 1, atPos 2)
    let cons : Deducer := K.exE <| normLastK K fun Γ Φ ψ ↦
      let rAt := atPos (Γ.length - 1)
      decideIn K (fun Γ ↦ pc P "Prelude.isSome" [pc P "Reader.indexOf"
          [yAt Γ, consT treeTy (dAt Γ) (rAt Γ)]])
        (fun Γ Φ ψ ↦ dExI L K.G K.E (pc P "Prelude.append" [rAt Γ, pc P "Prelude.single" [yAt Γ]])
          (linkK K "addFoldHead: new" K.byNorm) Γ Φ ψ)
        (fun Γ Φ ψ ↦ dExI L K.G K.E (rAt Γ) (linkK K "addFoldHead: present" K.byNorm) Γ Φ ψ) Γ Φ ψ
    let d₁ ← linkK K "addFoldHead: construction" cons (Ls :: treeTy :: Γ₀.tail)
      (lowered.map Internal.weaken2 ++ [Internal.weakenElem φ]) (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, Γ₀, [hyp], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The fold of a step of {lit}`Recognize.closure`, at a list of datatypes from a list. -/
def closeFold (P : Prog) (ms cl ns : Term) : Term :=
  let Ls := list treeTy
  let mn := pc P "Recognize.markerOf" [sh 2 ms, v 1]
  foldrT treeTy Ls (Term.lam treeTy (Term.lam Ls (condT Ls
    (call D.lab [] [pc P "Prelude.isSome" [mn]])
    (pc P "Recognize.addNew" [pc P "Recognize.depsOf" [sh 2 ms, pc P "Prelude.get" [mn]], v 0])
    (v 0)))) cl ns

/-- The fold of a step of the closure keeps a list's first: by induction on the datatypes, the
marker's presence decided, its dependencies by {name}`addFoldHead`. In the context of the datatypes,
the list, the first and the markers. -/
def closeFoldHead (P : Prog) (S : Defs) : Step :=
  ("closeFoldHead", fun ix E ↦ do
    let K := headKit P S ix E
    let P := K.P
    let Ls := list treeTy
    let Γ₀ := [Ls, Ls, treeTy, Ls]
    let hyp := headsT P.o (v 1) (v 2)
    let φ := headsT P.o (closeFold P (v 3) (v 1) (v 0)) (v 2)
    let some lowered := Internal.lowerHyps P.G 0 Γ₀.tail [hyp]
      | dbgTrace "closeFoldHead: the hypothesis" fun _ ↦ none
    let d₀ ← linkK K "closeFoldHead: empty" (K.byHyp 0) Γ₀.tail lowered
      (Term.subst φ fun i ↦ if i = 0 then nilT treeTy else v (i - 1))
    let (msAt, dAt, clAt, hAt, tAt) := (atPos 0, atPos 1, atPos 2, atPos 3, atPos 4)
    let mnAt (Γ : List Tree) : Term := pc P "Recognize.markerOf" [msAt Γ, hAt Γ]
    let cons : Deducer := fun Γ₁ Φ₁ ψ₁ ↦
      let ih := Φ₁.length - 1
      decideIn K (fun Γ ↦ pc P "Prelude.isSome" [mnAt Γ])
        (linkK K "closeFoldHead: no marker" (K.byHyp ih))
        (linkK K "closeFoldHead: a marker" <|
          applyThm K "addFoldHead" (fun Γ ↦ [pc P "Prelude.reverse" [pc P "Recognize.depsOf"
              [msAt Γ, pc P "Prelude.get" [mnAt Γ]]], dAt Γ, closeFold P (msAt Γ) (clAt Γ) (tAt Γ)])
            [K.byHyp ih] fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ) Γ₁ Φ₁ ψ₁
    let d₁ ← linkK K "closeFoldHead: construction" cons (Ls :: treeTy :: Γ₀.tail)
      (lowered.map Internal.weaken2 ++ [Internal.weakenElem φ]) (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, Γ₀, [hyp], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The iteration of the closure's step keeps a list's first: by induction on the number's bits,
the iteration of the rest's number applied to its own result, then the step once or twice as the
bit asks ({name}`closeFoldHead`). In the context of the number, the first and the markers, under the
list. -/
def iterHead (P : Prog) (S : Defs) : Step :=
  ("iterHead", fun ix E ↦ do
    let K := headKit P S ix E
    let P := K.P
    let L := K.L
    let Ls := list treeTy
    let Γ₀ := [bitsTy, treeTy, Ls]
    let f (ms : Term) : Term := Term.lam Ls (closeFold P (sh 1 ms) (v 0) (v 0))
    -- under the list v0: the number v1, the first v2, the markers v3
    let φ := Internal.Logic.all P.o Ls (Term.lam Ls (Internal.Logic.imp P.o
      (headsT P.o (v 0) (v 2))
      (headsT P.o (call D.iter [Ls] [v 1, f (v 3), v 0]) (v 2))))
    let lastHyp : Deducer := fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ
    let d₀ ← linkK K "iterHead: zero" (dAllI L (dImpI L lastHyp)) Γ₀.tail []
      (Term.subst φ (Internal.instVar (Term.arr 0 [bitTy] Term.star)))
    let (msAt, dAt, bAt, nAt) := (atPos 0, atPos 1, atPos 2, atPos 3)
    let cons : Deducer := dAllI L <| dImpI L fun Γ₁ Φ₁ ψ₁ ↦
      let hH := Φ₁.length - 1
      let xAt := atPos (Γ₁.length - 1)
      let once (Γ : List Tree) : Term := call D.iter [Ls] [nAt Γ, f (msAt Γ), xAt Γ]
      let twice (Γ : List Tree) : Term := call D.iter [Ls] [nAt Γ, f (msAt Γ), once Γ]
      dAllE L K.G K.E 0 (xAt Γ₁) (K.impE (K.byHyp hH) fun Γ Φ ψ ↦
        let h₁ := Φ.length - 1
        dAllE L K.G K.E 0 (once Γ) (K.impE (K.byHyp h₁) fun Γ Φ ψ ↦
          let h₂ := Φ.length - 1
          let thrice (Γ : List Tree) : Term := closeFold P (msAt Γ) (twice Γ) (twice Γ)
          let stepOn (x : List Tree → Term) (h : ℕ) (k : Deducer) : Deducer :=
            applyThm K "closeFoldHead" (fun Γ ↦ [x Γ, x Γ, dAt Γ, msAt Γ]) [K.byHyp h] k
          K.bitCase (bAt Γ)
            (linkK K "iterHead: a zero" (stepOn twice h₂ lastHyp))
            (linkK K "iterHead: a one" (stepOn twice h₂ fun Γ Φ ψ ↦
              stepOn thrice (Φ.length - 1) lastHyp Γ Φ ψ)) Γ Φ ψ)
          Γ Φ ψ) Γ₁ Φ₁ ψ₁
    let d₁ ← linkK K "iterHead: a bit" cons (list bitTy :: bitTy :: Γ₀.tail)
      [Internal.weakenElem φ] (Internal.listConsAt 1 bitTy φ)
    pure (⟨0, Γ₀, [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- A datatype's closure begins with the datatype: {name}`iterHead` at the singleton. In the context
of the datatype and the markers. -/
def closureHead (P : Prog) (S : Defs) : Step :=
  ("closureHead", fun ix E ↦ do
    let K := headKit P S ix E
    let P := K.P
    let L := K.L
    let Ls := list treeTy
    let thm : Internal.Thm := ⟨0, [treeTy, Ls], [],
      headsT P.o (pc P "Recognize.closure" [v 1, v 0]) (v 0)⟩
    let (msAt, dAt) := (atPos 0, atPos 1)
    let main : Deducer :=
      K.cutThm "iterHead" (fun Γ ↦ [call D.lab [] [pc P "Prelude.length" [msAt Γ]], dAt Γ, msAt Γ])
        (K.allEΓ (fun Γ ↦ pc P "Prelude.single" [dAt Γ]) (K.impE
          (fun Γ Φ ψ ↦ dExI L K.G K.E (nilT treeTy) (linkK K "closureHead: the singleton" K.byNorm)
            Γ Φ ψ)
          (linkK K "closureHead: the closure" fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ)))
    let some d := main thm.ctx thm.hyps thm.concl
      | dbgTrace "closureHead: not proved" fun _ ↦ none
    pure (thm, d))

/-- A marker's recognizer as the writer gives it: where it gives one, of markers with at most one
constructor of each label among which the marker's datatype is, a definition of the datatype's
recognizer name over an abstraction denoting a function which at the quotation of every tree
converges to the quotation of a bit, true exactly where the tree is a member. The abstraction by
{name}`recDen`; its bit at the first position, that of the datatype ({name}`closureHead`), is the
field's test, the membership ({name}`memberField`). In the context of the marker and the markers. -/
def recognizerDen (P : Prog) (S : Defs) : Step :=
  ("recognizerDen", fun ix E ↦ do
    let K₀ := fieldsKit P S ix E
    let K : Kit := { K₀ with
      P := { K₀.P with folded := (K₀.P.folded.filter (· != "Reader.both")) ++
        ["Recognize.ctorTest", "Recognize.dataTest", "Recognize.markerOf", "Recognize.closure"] } }
    let P := K.P
    let L := K.L
    let o := P.o
    let childT := (primT Kernel.Prim.child).getD Term.star
    let zero := leafT (numeral 0)
    let nameOf (m : Term) : Term := apps childT [m, zero]
    let vars := [treeTy, list treeTy]
    let at_ := denAt vars
    let (ms, m) := (at_ 6, at_ 7)
    let dd := nameOf m
    let cl := pc P "Recognize.closure" [ms, dd]
    let rec' := pc P "Recognize.recognizer" [ms, m]
    let hyps : List Term := [truth o (pc P "Prelude.isSome" [rec'])] ++
      writerHyps P ms (at_ 1) (at_ 2) (at_ 4) ++
      [uniqsT P ms, truth o (pc P "Prelude.isSome" [markerIdx P dd ms])]
    let hI := hyps.length - 1
    let defEq := Term.eq (pc P "Prelude.get" [rec']) (pc P "Recognize.s3" [pc P "Recognize.rDef" [],
      pc P "Datatype.memberName" [dd], recForm P cl ms])
    -- beneath the function v0, the tree v1 and the value v2
    let agrees : Term := Internal.Logic.ex o treeTy (Term.lam treeTy (Internal.Logic.conj o
      (Term.eq (v 1) (quoteV P (v 0)))
      (iffT o (truth o (v 0)) (truth o (pc P "Typing.memberOf" [sh 4 ms, sh 4 dd, v 2])))))
    let applied : Term := Internal.Logic.all o treeTy (Term.lam treeTy (S.conv
      (Term.lam nat (apps (Term.snd (S.levelN (Term.fst (sh 3 (at_ 0))) (v 0)))
        [v 2, quoteV P (v 1)]))
      (Term.lam treeTy agrees)))
    let thm : Internal.Thm := ⟨0, denCtx vars, hyps, Internal.Logic.conj o defEq
      (Internal.Logic.ex o treeTy (Term.lam treeTy (Internal.Logic.conj o
        (denT P S (sh 1 (at_ 0)) (sh 1 (at_ 3)) (sh 1 (at_ 2)) (sh 1 (at_ 1)) (sh 1 (at_ 4))
          (sh 1 (at_ 5)) (sh 1 (recForm P cl ms)) (v 0))
        applied)))⟩
    let base := 1
    let (msAt, mAt) := (atPos 6, atPos 7)
    let ddAt (Γ : List Tree) : Term := nameOf (mAt Γ)
    let clAt (Γ : List Tree) : Term := pc P "Recognize.closure" [msAt Γ, ddAt Γ]
    let writerAll : List Deducer :=
      [dHyp, dHyp] ++ (writerPrims.flatMap fun a ↦
        [K.byHyp (primHyp base a), K.byHyp (primHyp base a + 1)]) ++
      writerAtoms.map fun a ↦ K.byHyp (atomHyp base a)
    let Rat (Γ : List Tree) : Term := bitsFn P (msAt Γ) (clAt Γ)
    let main : Deducer := dConjI L (linkK K "recognizerDen: the definition" K.byNorm) <|
      applyThm K "recDen" (fun Γ ↦ [msAt Γ, clAt Γ] ++ denFixed Γ)
        ([linkK K "recognizerDen: the bits" (K.solve 3)] ++ writerAll ++ [dHyp]) <|
      K.exE <| K.conjE fun Γ Φ ψ ↦
        let cloAt := atPos (Γ.length - 1)
        let hC := Φ.length - 1
        K.cutThm "closureHead" (fun Γ ↦ [ddAt Γ, msAt Γ]) (K.exE <| normLastK K <|
            (fun Γ Φ ψ ↦ dExI L K.G K.E (cloAt Γ) (dConjI L dHyp
              (dAllI L fun Γ₁ Φ₁ ψ₁ ↦
                let tAt := atPos (Γ₁.length - 1)
                let bAt (Γ : List Tree) : Term := apps childT [Term.app (Rat Γ) (tAt Γ), zero]
                let okAt (Γ : List Tree) : Term := pc P "Typing.fieldOk" [msAt Γ, ddAt Γ,
                  pc P "Typing.memberships" [msAt Γ, tAt Γ]]
                dAllE L K.G K.E hC (tAt Γ₁) (K.unfoldConv <| K.exE <| K.exE <| K.conjE
                  fun Γ Φ ψ ↦
                  let (n, st) := (Γ.length - 2, Φ.length - 2)
                  normLastK K (
                    applyThm K "memberField" (fun Γ ↦ [tAt Γ, ddAt Γ, msAt Γ]) [K.byHyp hI] <|
                    normLastK K <|
                    K.conv (atPos n) (fun Γ ↦ quoteV P (bAt Γ))
                      (linkK K "recognizerDen: stable" <| instNK K st (fun _ ↦ v 0) K.byNorm)
                      (K.norm fun Γ Φ ψ ↦ dExI L K.G K.E (bAt Γ) (dConjI L
                        (linkK K "recognizerDen: the value" K.byNorm)
                        (decideIn K okAt
                          (linkK K "recognizerDen: not a member" (iffAuto K))
                          (linkK K "recognizerDen: a member" (iffAuto K)))) Γ Φ ψ)) Γ Φ ψ)
                  Γ₁ Φ₁ ψ₁)) Γ Φ ψ)) Γ Φ ψ
    let top : Deducer :=
      decideIn K (fun Γ ↦ pc P "Prelude.isSome" [bitsAllE P (clAt Γ) (msAt Γ)])
        (linkK K "recognizerDen: no bits" (K.hypFalse 0))
        (linkK K "recognizerDen: the recognizer" main)
    let some d := top thm.ctx thm.hyps thm.concl
      | dbgTrace "recognizerDen: not proved" fun _ ↦ none
    pure (thm, d))

/-- The development of the recognizers' folds: the step's body, its closure, the fold, the
recognizer. -/
def recognizerFoldDev (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  [stepBodyDen P S, stepDen P S T, recDen P S T, addFoldHead P S, closeFoldHead P S, iterHead P S,
    closureHead P S, recognizerDen P S]

/-- The development of {name}`recognizerFoldDev`, after the recognizers' decisions, stored as the
certificate {lit}`datatype-recognizer-fold`. -/
def recognizerFoldCertificates (P : Prog) (S : Defs) (T : Defs3) (before : List Internal.Thm) :
    Except String (List Stored.Cert) := do
  let some names := walkAfter P S T | throw "the base is not stated"
  certifyAfter P (names ++ (walkDev P S T).map (·.1) ++ (recognizerDev P S T).map (·.1))
    "datatype-recognizer-fold" (recognizerFoldDev P S T) before

end GebTests.Prototypes.FreeTopos.Datatypes

end
