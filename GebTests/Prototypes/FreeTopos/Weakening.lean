/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.TranslationProofs -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.TranslationProofs -- shake: keep
public import Geb.Prototypes.FreeTopos.Internal.Logic -- shake: keep
public meta import Geb.Prototypes.FreeTopos.Internal.Logic -- shake: keep

set_option doc.verso true in
/-!
# Weakening preserves types

The kernel's type checker written in Geb preserves types by weakening, proved in the internal
language about the translation of the programs, whose labels are bitstrings: for every
environment, contexts {lit}`c1` and {lit}`c2`, type {lit}`a` and term {lit}`t`, the type the
checker infers for {lit}`t` weakened past {lit}`a`, inserted below {lit}`c1`, in the context of
{lit}`c1`, {lit}`a` and {lit}`c2`, is the type it infers for {lit}`t` in the context of {lit}`c1`
and {lit}`c2`. The program is the prelude, the reader, the checker and the metalogic's checker,
whose weakening of kernel terms the statement cites, with the statement's two sides as
definitions, read and expanded by the stage-0 compiler's front end.

The statement is an equation between the two sides as functions of the environment, the contexts
and the inserted type, proved by induction on rose trees with the induction hypothesis
({name}`Geb.FreeTopos.Internal.byRoseIndHyp`). At a construction, the label is split into its
bits, which decides every test the traversal and the checker make on it. At a label whose case
depends on its children's types, the list of the children is split to their number, with the
induction hypothesis, which mentions it, reverted into an implication and introduced again in
each case, and then instantiated at each child, at the arguments and, for an abstraction's body,
at the first context extended by the abstraction's type. At a variable, the lookup in the
context at the index moved past the inserted type is the lookup at the index.

Both sides are compared in weak normal form, which leaves the steps of folds, and the bodies of
abstractions, unreduced, so that a fold at a child that is a variable does not unfold the
checker. The lemmas the comparison rewrites by make up the development: the unfolding of trees,
the connectives' rules, the conditionals moved through projections, applications and folds, the
folds' first components rebuilding their trees and lists, the lengths of the lists the folds
rebuild, and the labels' arithmetic, where the comparison and the iteration of bitstrings at
successors, and the lookup lemma, are proved by induction on bitstrings with case analysis of
their bits.

## Main definitions

* {lit}`prog?` — the translated program.
* {lit}`development` — the lemmas, each with its proof.
* {lit}`weakening` — the statement.
* {lit}`byLabels` — the proof at a construction.
* {lit}`byAuto` — the proof of an equation by instances of the hypotheses and case analysis of
  stuck variables.
* {lit}`revertCase` — the case analysis of a list variable that a hypothesis mentions.

## Tags

internal language, type checker, weakening, induction, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Weakening

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Translation
open GebTests.Prototypes.FreeTopos.TranslationProofs
open GebTests.Prototypes.FreeTopos.Translation (baseRules)
open Internal (Term NormRule Entry Deriv Decl Definition)
open scoped FinEnum

/-! The program. -/

/-- The two sides of the statement, as definitions of the program: the type of a term weakened
past a type inserted below a context's first part, and its type in the context without it; and
the two sides of the lookup at a variable, at its index moved past the inserted type and at its
index. -/
def statement : String := "
(def wkL (lam ((t T) (G Ts) (c1 Ts) (c2 Ts) (a T))
  (typeIn G (append c1 (cons a c2)) (wkAt (length c1) 1 t))))
(def wkR (lam ((t T) (G Ts) (c1 Ts) (c2 Ts) (a T)) (typeIn G (append c1 c2) t)))
(def nthL (lam ((c1 Ts) (c2 Ts) (a T) (t T))
  (nth (append c1 (cons a c2)) (if (lt (label t) (length c1)) (label t) (add (label t) 1)))))
(def nthR (lam ((c1 Ts) (c2 Ts) (a T) (t T)) (nth (append c1 c2) (label t))))"

/-- The program: the prelude, the reader, the type checker, the metalogic's checker, whose
weakening of kernel terms the statement cites, and the statement. -/
def programText : String :=
  Kernel.Stage0Tests.prelude ++ "\n" ++ Kernel.Stage0Tests.reader ++ "\n" ++
    Kernel.Stage0Tests.check ++ "\n" ++ Metalogic.Tests.equationsGeb ++ "\n" ++ statement

/-- A program's definitions with their names, read and expanded by the stage-0 compiler's
front end. -/
def bundled (bundlerText text : List Char) : Option (List (List Char × Tree)) := do
  let r ← Kernel.runMain bundlerText (Kernel.nameTree text)
  let b ← if r.label == 1 then r.children.head? else none
  Kernel.unbundle b

/-- The index of a program's definition among the translation's constants. -/
def defIndex (ds : List (List Char × Tree)) (name : List Char) : Option ℕ :=
  (ds.findIdx? fun d ↦ d.1 == name).map (lib.length + ·)

/-- The translated program: its constants, extended by the connectives' definitions, the index
of the connectives' first definition, and the index of each named definition of the program. -/
structure Prog where
  /-- The constants. -/
  G : Internal.Globals
  /-- The index of the connectives' first definition. -/
  o : ℕ
  /-- The index of a named definition. -/
  idx : String → ℕ

/-- The translated program of definitions, with the index of each named definition. -/
def prog? (ds : List (List Char × Tree)) (idx : String → ℕ) : Option Prog := do
  let (_, defs) ← program (ds.map Prod.snd)
  let o := lib.length + defs.length
  pure ⟨⟨prims, (lib ++ defs ++ Internal.Logic.defs o).map .language, sig.length⟩, o,
    idx⟩

/-! Proofs of equations. -/

/-- The application of a term to arguments, the first first. -/
def apps (f : Term) (xs : List Term) : Term := xs.foldl Term.app f

/-- The rules of the normalization: the language's equations and the unfolding of every
definition of the library and the program. -/
def baseNorm (P : Prog) : List NormRule := baseRules ++ [.unitVar, .deltaBelow P.o []]

/-- The weak normal form of a term in a context, in object variables, by rules, or the term. -/
def weakNF (P : Prog) (rs : List NormRule) (n : ℕ) (Γ : List Tree) (t : Term) : Term :=
  ((Internal.eval P.G #[] n rs 4096 .weak Γ [] t).map Prod.fst).getD t

/-- The proof of an equation by reducing both sides to one normal form, to a depth. -/
def byMode (m : Internal.Depth) (G : Internal.Globals) (E : Array Entry) (n : ℕ)
    (rs : List NormRule) : Internal.Prover := fun Γ Φ t u ↦ do
  let (v, d₁, _) ← Internal.eval G E n rs 4096 m Γ Φ t
  let (v', d₂, _) ← Internal.eval G E n rs 4096 m Γ Φ u
  if v = v' then some (RoseTree.node .join [d₁, d₂]) else none

/-- The proof of an equation by reducing both sides to one weak normal form. -/
def byWeak (G : Internal.Globals) (E : Array Entry) (n : ℕ) (rs : List NormRule) :
    Internal.Prover := byMode .weak G E n rs

/-- A theorem in object variables and a context whose sides are stated in weak normal form. -/
def weakThm (P : Prog) (n : ℕ) (Γ : List Tree) (t u : Term) : Internal.Thm :=
  ⟨n, Γ, [], Term.eq (weakNF P (baseNorm P) n Γ t) (weakNF P (baseNorm P) n Γ u)⟩

/-- The proof of an equation in a context of a list variable by induction on it in the form of
the uniqueness of its fold, with the step {lit}`s`, each premise by weak reduction. -/
def byListIndWeak (G : Internal.Globals) (E : Array Entry) (n : ℕ) (s : Term)
    (rs : List NormRule) : Internal.Prover := fun Γ Φ t u ↦ match Γ with
  | c :: Γ' => do
    let a ← Internal.listPart c
    let Φ' ← Internal.lowerHyps G n Γ' Φ
    let z := Internal.instVar (Term.arr 0 [a] Term.star)
    let p₀ ← byWeak G E n rs Γ' Φ' (Term.subst t z) (Term.subst u z)
    let p₁ ← byWeak G E n rs (c :: a :: Γ') (Φ'.map Internal.weaken2) (Internal.listConsAt 1 a t)
      (Term.subst s (Internal.atVar0 (Internal.weakenElem t)))
    let p₂ ← byWeak G E n rs (c :: a :: Γ') (Φ'.map Internal.weaken2) (Internal.listConsAt 1 a u)
      (Term.subst s (Internal.atVar0 (Internal.weakenElem u)))
    pure (RoseTree.node (.listInd 0 1 s) [p₀, p₁, p₂])
  | [] => none

/-- The proof of an equation in a context of a rose tree alone by induction on it in the form of
the uniqueness of its fold, with the step {lit}`s`, each premise by {lit}`p`. -/
def byRoseIndWith (G : Internal.Globals) (n : ℕ) (s : Term) (p : Internal.Prover) :
    Internal.Prover := fun Γ _ t u ↦ match Γ with
  | [r] => do
    let (a, _) ← Internal.roseParts r
    let C ← Internal.typeIn G n Γ t
    let p₁ ← p [list r, a] [] (Internal.roseNodeAt 2 r a t)
      (Term.subst s (Internal.atVar0 (Internal.roseMapAt 0 1 C t)))
    let p₂ ← p [list r, a] [] (Internal.roseNodeAt 2 r a u)
      (Term.subst s (Internal.atVar0 (Internal.roseMapAt 0 1 C u)))
    pure (RoseTree.node (.roseInd 2 0 1 s) [p₁, p₂])
  | _ => none

/-- The proof of an equation by case analysis of the list variable of index {lit}`i`: the sides
abstracted over it are equal functions, by extensionality and list induction on the new variable,
each case by its prover, and the equation follows by applying them to the variable. -/
def byListSplit (G : Internal.Globals) (n i : ℕ) (p₀ p₁ : Internal.Prover) : Internal.Prover :=
  fun Γ Φ t u ↦ do
    let c ← Γ[i]?
    let F := Internal.abstractVar i c t
    let H := Internal.abstractVar i c u
    let q ← Internal.byListIndWith G n 0 1 p₀ p₁ (c :: Γ) (Φ.map Internal.weaken1)
      (Term.app (Internal.weaken1 F) (v 0)) (Term.app (Internal.weaken1 H) (v 0))
    let χ := Term.eq (Term.app F (v i)) (Term.app H (v i))
    pure (RoseTree.node (.cut (Term.eq F H)) [RoseTree.node .funExt [q],
      RoseTree.node (.convFrom χ) [RoseTree.node .cong [RoseTree.node .beta [],
        RoseTree.node .beta []], RoseTree.node .join [RoseTree.node .cong
          [RoseTree.node (.rwHyp Φ.length false) [], RoseTree.node .refl []],
          RoseTree.node .refl []]]])

/-- The proof of an equation by case analysis of the variable of index {lit}`i`, of a
coproduct whose injections are the primitives of indices {lit}`kl` and {lit}`kr`, the first case
by {lit}`p₀` and the second by {lit}`p₁`, as {name}`Geb.FreeTopos.Internal.bySplit` proves it. -/
def bySplit2 (kl kr i : ℕ) (p₀ p₁ : Internal.Prover) : Internal.Prover := fun Γ Φ t u ↦ do
  let c ← Γ[i]?
  let (a, b) ← Internal.coprodParts c
  let F := Internal.abstractVar i c t
  let H := Internal.abstractVar i c u
  let inj (k : ℕ) (s : Term) : Term := Term.app (Internal.weaken1 s) (Term.arr k [a, b] (v 0))
  let q₀ ← p₀ (a :: Γ) (Φ.map Internal.weaken1) (inj kl F) (inj kl H)
  let q₁ ← p₁ (b :: Γ) (Φ.map Internal.weaken1) (inj kr F) (inj kr H)
  let χ := Term.eq (Term.app F (v i)) (Term.app H (v i))
  pure (RoseTree.node (.cut (Term.eq F H)) [RoseTree.node .funExt
    [RoseTree.node (.coprodInd kl kr) [q₀, q₁]], RoseTree.node (.convFrom χ)
      [RoseTree.node .cong [RoseTree.node .beta [], RoseTree.node .beta []],
        RoseTree.node .join [RoseTree.node .cong [RoseTree.node (.rwHyp Φ.length false) [],
          RoseTree.node .refl []], RoseTree.node .refl []]]])

/-- The proof of an equation by case analysis of its innermost variable, a list: empty, or an
element before a list, each case by {lit}`p`. -/
def byListCases (G : Internal.Globals) (n : ℕ) (p : Internal.Prover) : Internal.Prover :=
  Internal.byListIndWith G n 0 1 p p

/-- The proof of an equation by case analysis of its innermost variable, a bitstring: empty, or
a bit before a bitstring, the bit's two cases, each by {lit}`p`. -/
def bitsCases (G : Internal.Globals) (n : ℕ) (p : Internal.Prover) : Internal.Prover :=
  Internal.byListIndWith G n 0 1 p (Internal.bySplit 3 4 1 p)

/-- The proof of an equation with the hypotheses of the given indices, equations, cut in in weak
normal form and used as rewriting rules before those given to {lit}`k`. -/
def withWeakHyps (G : Internal.Globals) (E : Array Entry) (n : ℕ) (rs : List NormRule)
    (is : List ℕ) (k : List NormRule → Internal.Prover) (m : Internal.Depth := .weak) :
    Internal.Prover := fun Γ Φ t u ↦
  (is.foldr (fun i (acc : List Term → List NormRule → Option Deriv) Φ₁ extra ↦ do
      let (a, b) ← Internal.eqParts (← Φ₁[i]?)
      let (a', da, _) ← Internal.eval G E n rs 4096 m Γ Φ₁ a
      let (b', db, _) ← Internal.eval G E n rs 4096 m Γ Φ₁ b
      let ψ := Term.eq a' b'
      let rest ← acc (Φ₁ ++ [ψ]) (extra ++ [.hyp Φ₁.length])
      pure (RoseTree.node (.cut ψ) [RoseTree.node (.convFrom (Term.eq a b))
        [RoseTree.node .cong [da, db], RoseTree.node (.hyp i) []], rest]))
    (fun Φ₁ extra ↦ k extra Γ Φ₁ t u)) Φ []

/-- A derivation rewriting the function of an application to arguments by the hypothesis of
index {lit}`i`. -/
def rwFun (i : ℕ) : ℕ → Deriv :=
  Nat.rec (RoseTree.node (.rwHyp i false) []) fun _ d ↦
    RoseTree.node .cong [d, RoseTree.node .refl []]

/-- The proof of an equation with the instances of the hypothesis of index {lit}`h`, an
equation of functions, at the lists of arguments {lit}`αs`, each cut in and then in weak normal
form, as rewriting rules before those given to {lit}`k`. -/
def withInsts (G : Internal.Globals) (E : Array Entry) (n : ℕ) (rs : List NormRule) (h : ℕ)
    (αs : List (List Term)) (k : List NormRule → Internal.Prover) (m : Internal.Depth := .weak) :
    Internal.Prover :=
  fun Γ Φ t u ↦ do
    let (F, H) ← Internal.eqParts (← Φ[h]?)
    let insts := αs.map fun α ↦ Term.eq (apps F α) (apps H α)
    let rest ← withWeakHyps G E n rs ((List.range αs.length).map (Φ.length + ·)) k (m := m) Γ
      (Φ ++ insts) t u
    pure ((αs.zip insts).foldr (fun (α, q) r ↦ RoseTree.node (.cut q)
      [RoseTree.node .join [rwFun h α.length, RoseTree.node .refl []], r]) rest)

/-- The subterms of a term outside its binders and its folds' starts and steps, each with its
context's extension, none. -/
def openSubterms : Term → List Term := RoseTree.para fun l cs ↦
  RoseTree.node l (cs.map (·.1)) :: match l with
    | .lam _ => []
    | .natRec | .listRec => (cs.drop 2).flatMap (·.2)
    | .roseRec _ => (cs.drop 1).flatMap (·.2)
    | _ => cs.flatMap (·.2)

/-- The variable a weak normal form is stuck on: the datum of a fold, or the scrutinee of a case
analysis, the primitive of index five, that is a variable, the first in preorder. -/
def stuckVar (skip : ℕ → Bool) (t : Term) : Option ℕ :=
  let subs := openSubterms t
  -- a case analysis's scrutinee first, then a fold's datum
  (subs.findSome? fun u ↦ match u.label, u.children with
    | .app, [f, m] => match f.label, m.label with
      | .arr 5 _, .var i => if skip i then none else some i
      | _, _ => none
    | _, _ => none).orElse fun _ ↦ subs.findSome? fun u ↦ match u.label, u.children with
    | .natRec, [_, _, m] | .listRec, [_, _, m] | .roseRec _, [_, m] => match m.label with
      | .var i => if skip i then none else some i
      | _ => none
    | _, _ => none

/-- Whether a term mentions the variable of an index. -/
def mentions (t : Term) (i : ℕ) : Bool := Internal.uses t i > 0

/-- The arguments at which a matching of the body of an abstraction of {lit}`k` variables matches
the subterms of a term, its other variables those of the context. -/
def matchesWith (m : ℕ → Term → List (Option Term) → Option (List (Option Term))) (k : ℕ)
    (t : Term) : List (List Term) :=
  let width := k + 64
  let σ₀ : List (Option Term) := (List.range width).map fun j ↦
    if j < k then none else some (v (j - k))
  ((openSubterms t).filterMap fun u ↦ do
    let σ ← m 0 u σ₀
    let σ ← (σ.take k).mapM id
    pure σ.reverse).eraseDups

/-- The arguments at which the body of an abstraction of {lit}`k` variables matches the subterms
of a term, the body folded into its matching once rather than at each subterm. -/
def matchesOf (body : Term) (k : ℕ) (t : Term) : List (List Term) :=
  matchesWith (RoseTree.para Internal.matchStep body) k t

/-- The proof of an equation by weak reduction with the instances of the hypotheses that are
equations of abstractions of one variable, at the arguments at which the left side's body, in
weak normal form, matches the sides' weak normal forms, each cut in. -/
def byInstsOnce (m : Internal.Depth) (G : Internal.Globals) (E : Array Entry) (n : ℕ)
    (rs : List NormRule) (hs : ℕ) (next : List NormRule → Internal.Prover) : Internal.Prover :=
  fun Γ Φ t u ↦ do
  let (t', _, _) ← Internal.eval G E n rs 4096 m Γ Φ t
  let (u', _, _) ← Internal.eval G E n rs 4096 m Γ Φ u
  if t' = u' then byMode m G E n rs Γ Φ t u else
  let found := (List.range (min hs Φ.length)).filterMap fun h ↦ do
    let (F, _) ← Internal.eqParts (← Φ[h]?)
    match F.label, F.children with
    | .lam a, [b] =>
      let (bw, _, _) ← Internal.eval G E n rs 4096 m (a :: Γ) (Φ.map Internal.weaken1) b
      let αs := (matchesOf bw 1 t' ++ matchesOf bw 1 u').eraseDups
      if αs.isEmpty then none else some (h, αs)
    | _, _ => none
  let go := found.foldr (fun (h, αs) (k : List NormRule → Internal.Prover) extra ↦
      withInsts G E n rs h αs (fun ex ↦ k (extra ++ ex)) (m := m)) next
  if found.isEmpty then none else go [] Γ Φ t u

/-- The proof of an equation by {lit}`byInstsOnce` repeated, each round's instances rewriting
before the next looks for more, three rounds. -/
def byInsts (m : Internal.Depth) (G : Internal.Globals) (E : Array Entry) (n : ℕ)
    (rs : List NormRule) (hs : ℕ) : Internal.Prover :=
  let last (extra : List NormRule) : Internal.Prover := byMode m G E n (extra ++ rs)
  let round (next : List NormRule → Internal.Prover) (extra : List NormRule) : Internal.Prover :=
    fun Γ Φ t u ↦ (byMode m G E n (extra ++ rs) Γ Φ t u).orElse fun _ ↦
      byInstsOnce m G E n (extra ++ rs) hs (fun ex ↦ next (extra ++ ex)) Γ Φ t u
  round (round (round last)) []

/-- The proof of an equation by {lit}`byInsts` with the hypotheses it starts with, or else by
case analysis of a variable its normal forms are stuck on, a list or a coproduct, preferring the
scrutinee of a case analysis to the datum of a fold and a variable those hypotheses do not
mention, each case the same way, to a depth. -/
def byAuto (G : Internal.Globals) (E : Array Entry) (n : ℕ) (rs : List NormRule) (d : ℕ)
    (m : Internal.Depth := .weak) : Internal.Prover := fun Γ₀ Φ₀ t₀ u₀ ↦
  let hs := Φ₀.length
  (d.rec (byInsts m G E n rs hs) fun _ rec Γ Φ t u ↦
  (byInsts m G E n rs hs Γ Φ t u).orElse fun _ ↦ do
    let (t', _, _) ← Internal.eval G E n rs 4096 m Γ Φ t
    let (u', _, _) ← Internal.eval G E n rs 4096 m Γ Φ u
    let skip (i : ℕ) : Bool := (Φ.take hs).any (mentions · i)
    let i ← ((stuckVar skip t').orElse fun _ ↦ stuckVar skip u').orElse fun _ ↦
      (stuckVar (fun _ ↦ false) t').orElse fun _ ↦ stuckVar (fun _ ↦ false) u'
    let c ← Γ[i]?
    match Internal.listPart c, Internal.coprodParts c with
    | some _, _ => byListSplit G n i rec rec Γ Φ t u
    | none, some _ => bySplit2 3 4 i rec rec Γ Φ t u
    | none, none => none : Internal.Prover) Γ₀ Φ₀ t₀ u₀

/-- A prover under four new variables of the statement's arguments, by extensionality. -/
def funExt4 (G : Internal.Globals) (p : Internal.Prover) : Internal.Prover :=
  (List.replicate 4 ()).foldr (fun _ q ↦ Internal.byFunExt G 0 q) p

/-- The proof of an equation of two applications to a bit before a bitstring, the last two
variables, by the proof, by {lit}`p`, of the equation at the successor of the bitstring's
predecessor, into which the theorem of index {lit}`j` rewrites it backwards. -/
def bySuccPred (E : Array Entry) (j : ℕ) (p : Internal.Prover) : Internal.Prover :=
  fun Γ Φ t u ↦ do
  let some (Entry.language b) := E[j]? | none
  let (l, _) ← Internal.eqParts b.concl
  let σ := [v 1, v 0]
  let back : Deriv := RoseTree.node (.thm j [] σ true) []
  let rw (s : Term) : Option (Term × Deriv) := match s.label, s.children with
    | .app, [f, _] => some (Term.app f (Internal.instTerm [] σ l),
        RoseTree.node .cong [RoseTree.node .refl [], back])
    | _, _ => none
  let (t', dt) ← rw t
  let (u', du) ← rw u
  let q ← p Γ Φ t' u'
  pure (RoseTree.node .conv [RoseTree.node .cong [dt, du], q])

/-! The development. -/

/-- A development's entry: its name, and its theorem with its proof from the index of each named
entry and the entries before it. -/
abbrev Step : Type := String × ((String → ℕ) → Array Entry → Option (Internal.Thm × Deriv))

/-- An entry of a theorem stated beforehand. -/
def step (name : String) (a : Internal.Thm) (p : (String → ℕ) → Array Entry → Option Deriv) :
    Step :=
  (name, fun ix E ↦ (p ix E).map (a, ·))

/-- A development's derivations, each computed with the entries before it, or the name of the
first theorem whose proof is not found. -/
def developNamed (xs : List Step) : Except String (List Decl) :=
  let ix (name : String) : ℕ := (xs.findIdx? (·.1 == name)).getD 0
  (xs.foldlM (fun (acc : Array Entry × List Decl) (x : Step) ↦ match x.2 ix acc.1 with
    | some (a, d) => Except.ok (acc.1.push (Entry.language a), acc.2 ++ [Decl.language a d])
    | none => Except.error x.1) (#[], [])).map Prod.snd

/-- The index of the connectives' first rule among the development's theorems, after the lemmas
on the unfolding of trees. -/
def logicBase : ℕ := 3

/-- The connectives' introduction and elimination rules, following the lemmas on the unfolding of
trees. -/
def logicThms (P : Prog) : List Step :=
  (Internal.Logic.theorems P.o logicBase).map fun (a, d) ↦ step "logic" a (fun _ _ ↦ some d)

/-- The lemmas on the unfolding of trees: the fold of a list by construction, the fusion of the
rebuilding with the unfolding, and Lambek's lemma. -/
def unfoldingThms (P : Prog) : List Step :=
  (["mapId", "mapFusion", "lambek"].zip (treeLemmas P.G)).map fun (name, a, p) ↦
    step name a fun _ ↦ p

/-- The fold of the first term of a translated definition's body that is a rose tree's fold: its
type and its step. -/
def firstRose : Term → Option (Tree × Term) := RoseTree.para fun l cs ↦ match l, cs with
  | .roseRec c, [(s, _), _] => some (c, s)
  | _, cs => cs.findSome? (·.2)

/-- The conditional lemmas: a projection, an application and the type checker's fold moved
through a conditional, and a conditional in the branch its own test rejects. -/
def condLemmas (P : Prog) : Option (List (String × Internal.Thm)) := do
  let (C, s₀) ← ((P.G.defs[P.idx "typeIn"]?).bind Definition.language?).bind
    fun d ↦ firstRose d.body
  let (F, a) ← Internal.expParts C
  let b := v 0
  pure [
    ("sndCond", weakThm P 2 [bitsTy, prod (x 0) (x 1), prod (x 0) (x 1)]
      (Term.snd (condT (prod (x 0) (x 1)) b (v 1) (v 2)))
      (condT (x 1) b (Term.snd (v 1)) (Term.snd (v 2)))),
    ("fstCond", weakThm P 2 [bitsTy, prod (x 0) (x 1), prod (x 0) (x 1)]
      (Term.fst (condT (prod (x 0) (x 1)) b (v 1) (v 2)))
      (condT (x 0) b (Term.fst (v 1)) (Term.fst (v 2)))),
    ("labCond", weakThm P 0 [bitsTy, treeTy, treeTy]
      (call D.lab [] [condT treeTy b (v 1) (v 2)])
      (condT bitsTy b (call D.lab [] [v 1]) (call D.lab [] [v 2]))),
    ("appCond", weakThm P 2 [bitsTy, exp (x 0) (x 1), exp (x 0) (x 1), x 0]
      (Term.app (condT (exp (x 0) (x 1)) b (v 1) (v 2)) (v 3))
      (condT (x 1) b (Term.app (v 1) (v 3)) (Term.app (v 2) (v 3)))),
    ("condCond", weakThm P 1 [bitsTy, x 0, x 0, x 0]
      (condT (x 0) b (v 1) (condT (x 0) b (v 2) (v 3))) (condT (x 0) b (v 1) (v 3))),
    ("foldCond", weakThm P 0 [bitsTy, treeTy, treeTy, F]
      (Term.app (Term.roseRec C s₀ (condT treeTy b (v 1) (v 2))) (v 3))
      (condT a b (Term.app (Term.roseRec C s₀ (v 1)) (v 3))
        (Term.app (Term.roseRec C s₀ (v 2)) (v 3))))]

/-- The first application of a rose tree's fold to an argument in a term: the fold's type, its
step and the argument. -/
def firstFoldApp : Term → Option (Tree × Term × Term) := RoseTree.para fun l cs ↦
  match l, cs with
  | .app, [(f, rf), (x, rx)] => match f.label, f.children with
    | .roseRec c, [s, _] => some (c, s, x)
    | _, _ => rf.orElse fun _ ↦ rx
  | _, cs => cs.findSome? (·.2)

/-- The kernel's label of a tree, translated. -/
def labelK : Term := (primT Kernel.Prim.label).getD Term.star

/-- The folds of the traversal of kernel terms and of the type checker, at a variable: each
fold's type and step, and the traversal's step function, closed, and the checker's, in the
environment of index one. -/
def folds (P : Prog) : Option ((Tree × Term × Term) × (Tree × Term × Term)) := do
  let w := weakNF P (baseNorm P) 0 [treeTy, treeTy]
    (apps (call (P.idx "wkAt") [] []) [v 1, quoteT (Kernel.leaf 1), v 0])
  let t := weakNF P (baseNorm P) 0 [treeTy, list treeTy]
    (apps (call (P.idx "typeIn") [] []) [v 1, nilT treeTy, v 0])
  pure (← firstFoldApp w, ← firstFoldApp t)

/-- The list of the children of a translated node. -/
def kidsOf (t : Term) : Option Term := match t.label, t.children with
  | .arr 2 _, [p] => match p.label, p.children with
    | .pair, [_, k] => some k
    | _, _ => none
  | _, _ => none

/-- The lemmas on the folds: the fold of a list by construction rebuilds it; the traversal's
fold of the list of the children's folds is the fold of the children by the first components of
their folds, and its fold rebuilds its tree; and the label of the tree the type checker's fold
rebuilds is the tree's, first as functions of the environment. -/
def foldLemmas (P : Prog) : Option (List Step) := do
  let ((CT, sT, fW), (CR, sR, fG)) ← folds P
  let rs := baseNorm P
  let node2 := Term.arr 2 [bitsTy] (Term.pair (v 1) (v 0))
  let kids := weakThm P 0 [list treeTy] (sides mapFusion).1 (v 0)
  let fstBody := Term.fst (Term.app (Term.roseRec CT sT (v 0)) fW)
  let fstT : Internal.Thm := weakThm P 0 [treeTy] fstBody (v 0)
  let kidsL ← kidsOf (weakNF P rs 0 [list treeTy, bitsTy]
    (Internal.roseNodeAt 2 treeTy bitsTy fstBody))
  let stepR := consT treeTy (Internal.weaken1 (Internal.weaken1 fstBody) |>.rename
    (fun i ↦ if i = 2 then 1 else i)) (v 0)
  let fusT := weakThm P 0 [list treeTy] kidsL
    (Term.listRec (nilT treeTy) stepR (v 0))
  let trT := weakThm P 0 [list treeTy] kidsL (v 0)
  let (FT, aT) ← Internal.expParts CT
  let (FR, aR) ← Internal.expParts CR
  let lenOf (t : Term) : Term := call D.length [treeTy] [t]
  let lenR := weakThm P 0 [list treeTy, list treeTy]
    (lenOf (apps (call (P.idx "rrTrees") [] [])
      [call D.mapApp [FR, aR] [Term.listRec (nilT CR) (consT CR (Term.roseRec CR sR (v 1)) (v 0))
        (v 0), fG]]))
    (lenOf (v 0))
  let lenT := weakThm P 0 [list treeTy, treeTy]
    (lenOf (apps (call (P.idx "trAll") [] [])
      [call D.mapApp [FT, aT] [Term.listRec (nilT CT) (consT CT (Term.roseRec CT sT (v 1)) (v 0))
        (v 0), fW], v 1]))
    (lenOf (v 0))
  let succ0 := call D.succ [] [v 0]
  let lblBody := Term.app labelK (Term.fst (Term.app (Term.roseRec CR sR (v 0)) fG))
  let lblAbs : Internal.Thm := ⟨0, [treeTy], [], Term.eq
    (Internal.abstractVar 1 (list treeTy) lblBody)
    (Term.lam (list treeTy) (Term.app labelK (v 1)))⟩
  let lbl := weakThm P 0 [treeTy, list treeTy] lblBody (Term.app labelK (v 0))
  pure [
    step "kids" kids (fun ix E ↦ byListIndWeak P.G E 0 (consT treeTy (v 1) (v 0))
      ([.thm (ix "lambek") []] ++ rs) kids.ctx [] (sides kids).1 (sides kids).2),
    step "fusT" fusT (fun _ E ↦ byListIndWeak P.G E 0 stepR rs fusT.ctx [] (sides fusT).1
      (sides fusT).2),
    step "fstT" fstT (fun ix E ↦ byRoseIndWith P.G 0 node2
      (byWeak P.G E 0 ([.thm (ix "fusT") [], .thm (ix "mapId") []] ++ rs)) fstT.ctx []
      (sides fstT).1 (sides fstT).2),
    step "trT" trT (fun ix E ↦ byListIndWeak P.G E 0 (consT treeTy (v 1) (v 0))
      ([.thm (ix "fstT") []] ++ rs) trT.ctx [] (sides trT).1 (sides trT).2),
    step "lenR" lenR (fun _ E ↦ byListIndWeak P.G E 0 succ0 rs lenR.ctx [] (sides lenR).1
      (sides lenR).2),
    step "lenT" lenT (fun _ E ↦ byListIndWeak P.G E 0 succ0 rs lenT.ctx [] (sides lenT).1
      (sides lenT).2),
    step "lblAbs" lblAbs (fun _ E ↦ byRoseIndWith P.G 0
      (Term.lam (list treeTy) (Term.app labelK (Term.arr 2 [bitsTy]
        (Term.pair (v 2) (nilT treeTy)))))
      (Internal.byFunExt P.G 0 (byWeak P.G E 0 rs)) lblAbs.ctx [] (sides lblAbs).1
        (sides lblAbs).2),
    step "lbl" lbl (fun ix E ↦ do
      let F := (sides lblAbs).1
      let H := (sides lblAbs).2
      let (_, dF, _) ← Internal.eval P.G E 0 rs 4096 .weak lbl.ctx [] (Term.app F (v 1))
      let (_, dH, _) ← Internal.eval P.G E 0 rs 4096 .weak lbl.ctx [] (Term.app H (v 1))
      pure (RoseTree.node (.convFrom (Term.eq (Term.app F (v 1)) (Term.app H (v 1))))
        [RoseTree.node .cong [dF, dH], RoseTree.node .join [RoseTree.node .cong
          [RoseTree.node (.thm (ix "lblAbs") [] [v 0] false) [], RoseTree.node .refl []],
          RoseTree.node .refl []]]))]

/-- The lemmas on labels: the addition of one is the successor, by case analysis of the bits,
and the label of the prelude's length of a list, a fold by addition, is the library's length,
by list induction. -/
def arithLemmas (P : Prog) : Option (List Step) := do
  let rs := baseNorm P
  -- the rests of a bitstring the folds of addition and of the successor rebuild
  let rest (t : Term) : Option Term := match t.label, t.children with
    | .arr 1 _, [p] => match p.label, p.children with
      | .pair, [_, r] => some r
      | _, _ => none
    | _, _ => none
  let rA ← rest (weakNF P rs 0 [bitsTy] (call D.add [] [consT bitTy bit0T (v 0), numeral 1]))
  let rS ← rest (weakNF P rs 0 [bitsTy] (call D.succ [] [consT bitTy bit0T (v 0)]))
  let rebA : Internal.Thm := ⟨0, [bitsTy], [], Term.eq rA (v 0)⟩
  let rA₂ ← rest (weakNF P rs 0 [bitsTy] (call D.add [] [consT bitTy bit0T (v 0), oneN]))
  let rebA₂ : Internal.Thm := ⟨0, [bitsTy], [], Term.eq rA₂ (v 0)⟩
  let rebS : Internal.Thm := ⟨0, [bitsTy], [], Term.eq rS (v 0)⟩
  let addOne := weakThm P 0 [bitsTy] (call D.add [] [v 0, numeral 1]) (call D.succ [] [v 0])
  let addOne₂ := weakThm P 0 [bitsTy] (call D.add [] [v 0, oneN]) (call D.succ [] [v 0])
  let lenK := weakThm P 0 [list treeTy]
    (call D.lab [] [apps (call (P.idx "length") [] []) [v 0]]) (call D.length [treeTy] [v 0])
  let rsA (ix : String → ℕ) : List NormRule :=
    [.thm (ix "rebA") [], .thm (ix "rebA₂") [], .thm (ix "rebS") []] ++ rs
  pure [
   step "rebA" rebA (fun _ E ↦ byListIndWeak P.G E 0 (consT bitTy (v 1) (v 0)) rs rebA.ctx []
      (sides rebA).1 (sides rebA).2),
   step "rebS" rebS (fun _ E ↦ byListIndWeak P.G E 0 (consT bitTy (v 1) (v 0)) rs rebS.ctx []
      (sides rebS).1 (sides rebS).2),
   step "rebA₂" rebA₂ (fun _ E ↦ byListIndWeak P.G E 0 (consT bitTy (v 1) (v 0)) rs rebA₂.ctx []
      (sides rebA₂).1 (sides rebA₂).2),
   step "addOne" addOne (fun ix E ↦ Internal.byListIndWith P.G 0 0 1 (byWeak P.G E 0 (rsA ix))
      (Internal.bySplit 3 4 1 (byWeak P.G E 0 (rsA ix))) addOne.ctx [] (sides addOne).1
      (sides addOne).2),
   step "addOne₂" addOne₂ (fun ix E ↦ Internal.byListIndWith P.G 0 0 1 (byWeak P.G E 0 (rsA ix))
      (Internal.bySplit 3 4 1 (byWeak P.G E 0 (rsA ix))) addOne₂.ctx [] (sides addOne₂).1
      (sides addOne₂).2),
   step "lenK" lenK (fun ix E ↦ byListIndWeak P.G E 0 (call D.succ [] [v 0])
      ([.thm (ix "addOne") []] ++ rs) lenK.ctx [] (sides lenK).1 (sides lenK).2)]

/-- The rewriting rules of the lemmas: each theorem of the development from its left side to its
right, at the object instances given. -/
def lemmaRules (ix : String → ℕ) : List NormRule :=
  [.thm (ix "trT") [], .thm (ix "fstT") [], .thm (ix "lbl") [], .thm (ix "kids") [],
    .thm (ix "lambek") [], .thm (ix "lenR") [], .thm (ix "lenT") [], .thm (ix "lenK") [],
    .thm (ix "addOne") [], .thm (ix "addOne₂") [], .thm (ix "rebA") [], .thm (ix "rebA₂") [],
    .thm (ix "rebS") [],
    .thm (ix "foldCond") [], .thm (ix "condCond") [treeTy],
    .thm (ix "sndCond") [treeTy, exp (list treeTy) treeTy],
    .thm (ix "fstCond") [treeTy, exp (list treeTy) treeTy], .thm (ix "labCond") [],
    .thm (ix "appCond") [list treeTy, treeTy], .thm (ix "nthP") []]

/-- The pointwise form of an earlier theorem that equates two abstractions over one variable of
the type {lit}`a`: in the theorem's context extended by that variable, the bodies' normal forms at
the given depth with the given rules, by applying both sides to the variable. -/
def pointwise (P : Prog) (rules : (String → ℕ) → List NormRule) (m : Internal.Depth)
    (name src : String) (a : Tree) : Step :=
  (name, fun ix E ↦ do
    let some (Entry.language b) := E[ix src]? | none
    let (F, H) ← Internal.eqParts b.concl
    let Γ := a :: b.ctx
    let F' := Term.app (Internal.weaken1 F) (v 0)
    let H' := Term.app (Internal.weaken1 H) (v 0)
    let (f, dF, _) ← Internal.eval P.G E b.arity (rules ix) 4096 m Γ [] F'
    let (h, dH, _) ← Internal.eval P.G E b.arity (rules ix) 4096 m Γ [] H'
    let σ := (List.range b.ctx.length).map fun j ↦ v (j + 1)
    pure (⟨b.arity, Γ, [], Term.eq f h⟩, RoseTree.node (.convFrom (Term.eq F' H'))
      [RoseTree.node .cong [dF, dH], RoseTree.node .join [RoseTree.node .cong
        [RoseTree.node (.thm (ix src) ((List.range b.arity).map x) σ false) [],
          RoseTree.node .refl []], RoseTree.node .refl []]]))

/-- The lemmas on bitstrings: comparisons with zero and of zero with a successor, the successor
moved out of a conditional, the predecessor's rebuilding of the rest, and the successor of the
predecessor of a bitstring that is not empty. -/
def numLemmas (P : Prog) : Option (List Step) := do
  let rs := baseNorm P
  let rest (t : Term) : Option Term := match t.label, t.children with
    | .arr 1 _, [p] => match p.label, p.children with
      | .pair, [_, r] => some r
      | _, _ => none
    | _, _ => none
  let rP ← rest (weakNF P rs 0 [bitsTy] (call D.pred [] [consT bitTy bit1T (v 0)]))
  let rebP : Internal.Thm := ⟨0, [bitsTy], [], Term.eq rP (v 0)⟩
  -- the tail's fold rebuilds its list
  let (zT, sT) ← (lib[D.tail]?).bind fun d ↦ firstFold d.body
  let rebT : Internal.Thm := ⟨1, [list (x 0)], [],
    Term.eq (Term.fst (Term.listRec zT sT (v 0))) (v 0)⟩
  -- the case analysis of lists, at any pair of cases, rebuilds its list
  let (zL, sL) ← (lib[D.lcase]?).bind fun d ↦ firstFold d.body
  let rebL : Internal.Thm := ⟨2, [list (x 0),
    prod (exp one (x 1)) (exp (x 0) (exp (list (x 0)) (x 1)))],
    [], Term.eq (Term.fst (Term.app (Term.listRec zL sL (v 0)) (v 1))) (v 0)⟩
  let rsN (ix : String → ℕ) : List NormRule :=
    [.thm (ix "rebA") [], .thm (ix "rebS") [], .thm (ix "rebP") [],
      .thm (ix "rebL") [bitTy, ordTy], .thm (ix "rebL") [bitTy, bitsTy]] ++ rs
  let ltZero := weakThm P 0 [bitsTy] (call D.ltB [] [v 0, bnilT]) bnilT
  let ltZeroSucc := weakThm P 0 [bitsTy] (call D.ltB [] [bnilT, call D.succ [] [v 0]]) trueT
  let condSucc := weakThm P 0 [bitsTy, bitsTy, bitsTy]
    (condT bitsTy (v 0) (call D.succ [] [v 1]) (call D.succ [] [v 2]))
    (call D.succ [] [condT bitsTy (v 0) (v 1) (v 2)])
  let succPred : Internal.Thm := ⟨0, [bitsTy], [], Term.eq
    (Term.lam bitTy (call D.succ [] [call D.pred [] [consT bitTy (v 0) (v 1)]]))
    (Term.lam bitTy (consT bitTy (v 0) (v 1)))⟩
  -- comparisons: a case analysis of a comparison of a case analysis, a successor on one side and
  -- on both
  let ordCase := weakThm P 1 [ordTy, ordTy, ordTy, ordTy, x 0, x 0, x 0]
    (ifOrd (x 0) (ifOrd ordTy (v 0) (v 1) (v 2) (v 3)) (v 4) (v 5) (v 6))
    (ifOrd (x 0) (v 0) (ifOrd (x 0) (v 1) (v 4) (v 5) (v 6)) (ifOrd (x 0) (v 2) (v 4) (v 5) (v 6))
      (ifOrd (x 0) (v 3) (v 4) (v 5) (v 6)))
  let sc (t : Term) : Term := call D.succ [] [t]
  let cmpX2 : Internal.Thm := ⟨0, [bitsTy], [], Term.eq
    (Term.lam bitsTy (ifOrd ordTy (cmpT (v 0) (sc (v 1))) ltO gtO gtO))
    (Term.lam bitsTy (ifOrd ordTy (cmpT (v 0) (v 1)) ltO ltO gtO))⟩
  let cmpX1 : Internal.Thm := ⟨0, [bitsTy], [], Term.eq
    (Term.lam bitsTy (ifOrd ordTy (cmpT (sc (v 0)) (v 1)) ltO ltO gtO))
    (Term.lam bitsTy (ifOrd ordTy (cmpT (v 0) (v 1)) ltO gtO gtO))⟩
  let cmpSucc : Internal.Thm := ⟨0, [bitsTy], [], Term.eq
    (Term.lam bitsTy (cmpT (sc (v 0)) (sc (v 1)))) (Term.lam bitsTy (cmpT (v 0) (v 1)))⟩
  -- iteration: one more application commutes with it, and at a successor it is once more
  let it (n f z : Term) : Term := call D.iter [x 0] [n, f, z]
  let iterComm : Internal.Thm := ⟨1, [bitsTy, exp (x 0) (x 0)], [], Term.eq
    (Term.lam (x 0) (it (v 1) (v 2) (Term.app (v 2) (v 0))))
    (Term.lam (x 0) (Term.app (v 2) (it (v 1) (v 2) (v 0))))⟩
  let iterSucc : Internal.Thm := ⟨1, [bitsTy, exp (x 0) (x 0)], [], Term.eq
    (Term.lam (x 0) (it (sc (v 1)) (v 2) (v 0)))
    (Term.lam (x 0) (it (v 1) (v 2) (Term.app (v 2) (v 0))))⟩
  let rsC (ix : String → ℕ) : List NormRule :=
    [.thm (ix "ordCase") [ordTy], .thm (ix "ordCase") [bitsTy]] ++ rsN ix
  -- induction on the second number, as functions of the first: at the empty list by the
  -- automatic prover; at a bit before a list by case analysis of the bit, then of the first
  -- number, then of its first bit, each case with the induction hypothesis's instances
  let byInd (names : List String) (a : Internal.Thm) (ix : String → ℕ) (E : Array Entry) :
      Option Deriv :=
    let rules := names.map (fun nm ↦ NormRule.thm (ix nm) []) ++ rsC ix
    let leaf := byAuto P.G E 0 rules 2 .open
    let bit (i : ℕ) (p : Internal.Prover) : Internal.Prover := bySplit2 3 4 i p p
    -- after extensionality: the first number, the rest and the bit of the second
    let cons : Internal.Prover := fun Γ Φ t u ↦ Internal.byFunExt P.G 0
      (bit 2 (byListSplit P.G 0 1 leaf (bit 1 leaf))) Γ Φ t u
    Internal.byListIndWith P.G 0 0 1 (Internal.byFunExt P.G 0 (byAuto P.G E 0 rules 8 .open))
      cons a.ctx [] (sides a).1 (sides a).2
  -- the lookup at a variable's index moved past an inserted type, by induction on the context's
  -- first part, as functions of the index
  let nthSide (name : String) : Term := Term.lam bitsTy
    (apps (call (P.idx name) [] []) [v 1, v 2, v 3, leafT (v 0)])
  let nthThm : Internal.Thm := ⟨0, [list treeTy, list treeTy, treeTy], [],
    Term.eq (nthSide "nthL") (nthSide "nthR")⟩
  let rsNth (ix : String → ℕ) : List NormRule :=
    [.thm (ix "ltZero") [], .thm (ix "ltZeroSucc") [], .thm (ix "addOne") [],
      .thm (ix "lenK") [], .thm (ix "cmpSuccP") [], .thm (ix "iterSuccP") [list treeTy],
      .thm (ix "condSucc") [], .thm (ix "kids") [], .thm (ix "lambek") [],
      .thm (ix "rebT") [treeTy], .thm (ix "labCond") []] ++ rsC ix
  -- induction on the innermost number, as functions of the next variable, each premise by the
  -- automatic prover
  let byIndAuto (names : List String) (a : Internal.Thm) (ix : String → ℕ) (E : Array Entry) :
      Option Deriv :=
    let rules := names.map (fun nm ↦ NormRule.thm (ix nm) ((List.range a.arity).map x)) ++ rsC ix
    Internal.byListIndWith P.G a.arity 0 1
      (Internal.byFunExt P.G a.arity (byAuto P.G E a.arity rules 4 .open))
      (Internal.byFunExt P.G a.arity (byAuto P.G E a.arity rules 4 .open)) a.ctx []
      (sides a).1 (sides a).2
  pure [
    step "rebT" rebT (fun _ E ↦ byListIndWeak P.G E 1 (consT (x 0) (v 1) (v 0)) rs rebT.ctx []
      (sides rebT).1 (sides rebT).2),
    step "rebL" rebL (fun _ E ↦ byListIndWeak P.G E 2 (consT (x 0) (v 1) (v 0)) rs rebL.ctx []
      (sides rebL).1 (sides rebL).2),
    step "rebP" rebP (fun _ E ↦ byListIndWeak P.G E 0 (consT bitTy (v 1) (v 0)) rs rebP.ctx []
      (sides rebP).1 (sides rebP).2),
    step "ltZero" ltZero (fun ix E ↦ bitsCases P.G 0 (byWeak P.G E 0 (rsN ix)) ltZero.ctx []
      (sides ltZero).1 (sides ltZero).2),
    step "ltZeroSucc" ltZeroSucc (fun ix E ↦ bitsCases P.G 0 (byWeak P.G E 0 (rsN ix))
      ltZeroSucc.ctx [] (sides ltZeroSucc).1 (sides ltZeroSucc).2),
    step "condSucc" condSucc (fun ix E ↦ Internal.byListIndWith P.G 0 0 1
      (byWeak P.G E 0 (rsN ix)) (byWeak P.G E 0 (rsN ix)) condSucc.ctx []
      (sides condSucc).1 (sides condSucc).2),
    step "succPred" succPred (fun ix E ↦ Internal.byListIndWith P.G 0 0 1
      (Internal.byFunExt P.G 0 (Internal.bySplit 3 4 0 (byWeak P.G E 0 (rsN ix))))
      (fun Γ Φ t u ↦ Internal.byFunExt P.G 0 (Internal.bySplit 3 4 0
        (withInsts P.G E 0 (rsN ix) (Φ.length - 1) [[v 3]] fun extra ↦
          byWeak P.G E 0 (extra ++ rsN ix))) Γ Φ t u)
      succPred.ctx [] (sides succPred).1 (sides succPred).2),
    step "ordCase" ordCase (fun ix E ↦ byAuto P.G E 1 (rsN ix) 3 .weak ordCase.ctx []
      (sides ordCase).1 (sides ordCase).2),
    step "cmpX2" cmpX2 (byInd [] cmpX2),
    step "cmpX1" cmpX1 (byInd [] cmpX1),
    pointwise P rsC .open "cmpX1p" "cmpX1" bitsTy,
    pointwise P rsC .open "cmpX2p" "cmpX2" bitsTy,
    step "cmpSucc" cmpSucc (byInd ["cmpX1p", "cmpX2p"] cmpSucc),
    pointwise P rsC .open "cmpSuccP" "cmpSucc" bitsTy,
    step "iterComm" iterComm (byIndAuto [] iterComm),
    pointwise P rsC .open "iterCommP" "iterComm" (x 0),
    step "iterSucc" iterSucc (byIndAuto ["iterCommP"] iterSucc),
    pointwise P rsC .open "iterSuccP" "iterSucc" (x 0),
    pointwise P rsC .open "succPredP" "succPred" bitTy,
    step "nth" nthThm (fun ix E ↦
      let rules := rsNth ix
      Internal.byListIndWith P.G 0 0 1
        (Internal.byFunExt P.G 0 (byAuto P.G E 0 rules 2 .open))
        (Internal.byFunExt P.G 0 (byListSplit P.G 0 0
          (byAuto P.G E 0 rules 1 .open)
          (bySuccPred E (ix "succPredP") (byInsts .open P.G E 0 rules 1))))
        nthThm.ctx [] (sides nthThm).1 (sides nthThm).2),
    pointwise P (fun ix ↦ lemmaRules ix ++ rs) .weak "nthP" "nth" bitsTy]

/-- The development: the lemmas on the unfolding of trees, the connectives' rules, and the
lemmas on conditionals, on the folds, on labels and on bitstrings. -/
def development (P : Prog) : Option (List Step) := do
  let cs ← condLemmas P
  let fs ← foldLemmas P
  let ar ← arithLemmas P
  let ns ← numLemmas P
  pure (unfoldingThms P ++ logicThms P ++
    cs.map (fun (name, a) ↦ step name a fun _ E ↦ byListCases P.G a.arity
      (byWeak P.G E a.arity (baseNorm P)) a.ctx a.hyps (sides a).1 (sides a).2) ++ fs ++ ar ++ ns)

/-! The theorem. -/

/-- The induction hypothesis at the children: for the hypothesis of index {lit}`h`, that the
two lists of formulas its sides fold from the list of children are equal, the formula at each
child among the first {lit}`k`, cut in, then its instance at each list of arguments of
{lit}`args` of that child, cut in, and {lit}`k'` proving the goal with the instances' indices. -/
def withChildHyps (G : Internal.Globals) (E : Array Entry) (n : ℕ) (rs : List NormRule)
    (h : ℕ) (kids : List ℕ) (args : ℕ → List (List Term)) (k' : List ℕ → Internal.Prover) :
    Internal.Prover := fun Γ Φ t u ↦ do
  let (L₀, R₀) ← Internal.eqParts (← Φ[h]?)
  let tt : Term := Term.eq Term.star Term.star
  let nthOf (X : Term) (p : ℕ) : Term :=
    call D.headD [omega] [tt, p.rec X fun _ Y ↦ call D.tail [omega] [Y]]
  (kids.foldr (fun p (acc : List Term → List ℕ → Option Deriv) Φ₁ insts ↦ do
      let A := nthOf L₀ p
      let B := nthOf R₀ p
      let (A', dA, _) ← Internal.eval G E n rs 4096 .weak Γ Φ₁ A
      let (B', dB, _) ← Internal.eval G E n rs 4096 .weak Γ Φ₁ B
      let (_, dAh, _) ← Internal.eval G E n [.hyp h] 4096 .weak Γ Φ₁ A
      let (F, H) ← Internal.eqParts A'
      let i₁ := Φ₁.length
      let i₂ := i₁ + 1
      let αs := args p
      let Φ₂ := Φ₁ ++ [Term.eq A' B', A'] ++ αs.map fun α ↦ Term.eq (apps F α) (apps H α)
      let rest ← acc Φ₂ (insts ++ (List.range αs.length).map (i₂ + 1 + ·))
      let instDs := αs.map fun α ↦ RoseTree.node .join [rwFun i₂ α.length, RoseTree.node .refl []]
      let body := (αs.zip instDs).foldr (fun (α, d) r ↦
        RoseTree.node (.cut (Term.eq (apps F α) (apps H α))) [d, r]) rest
      pure (RoseTree.node (.cut (Term.eq A' B')) [RoseTree.node (.convFrom (Term.eq A B))
        [RoseTree.node .cong [dA, dB], RoseTree.node .join [dAh, RoseTree.node .refl []]],
        RoseTree.node (.cut A') [RoseTree.node .conv [RoseTree.node (.rwHyp i₁ false) [],
          RoseTree.node .join [RoseTree.node .refl [], RoseTree.node .refl []]], body]]))
    (fun Φ₁ insts ↦ k' insts Γ Φ₁ t u)) Φ []

/-- The proof of an equation by case analysis of the list variable of index {lit}`i`, the
hypothesis of index {lit}`h`, which mentions it, reverted: the implication of the equation by the
hypothesis, abstracted over the variable, equals the constant truth, by extensionality and list
induction on the new variable, the hypothesis introduced again in each case and each case's
equation proved by its prover under it, the last hypothesis; the equation follows from the
implication at the variable and the hypothesis. The connectives are the definitions from the
index {lit}`o`, their rules the theorems from {lit}`logicBase`. -/
def revertCase (G : Internal.Globals) (n o i h : ℕ) (pNil pCons : Internal.Prover) :
    Internal.Prover := fun Γ Φ t u ↦ do
  let c ← Γ[i]?
  let a ← Internal.listPart c
  let ψ ← Φ[h]?
  let q := Term.eq t u
  let imp (p r : Term) : Term := Internal.Logic.imp o p r
  let tt := Internal.Logic.tt o
  let Fχ := Internal.abstractVar i c (imp ψ q)
  let sub (x : Term) : Term :=
    Term.subst (Internal.weaken1 x) fun j ↦ if j = i + 1 then v 0 else v j
  let ψ₁ := sub ψ
  let q₁ := sub q
  let Φ₁ := Φ.map Internal.weaken1 ++ [tt]
  let Φ' ← Internal.lowerHyps G n Γ Φ₁
  -- the empty list
  let z := Internal.instVar (Term.arr 0 [a] Term.star)
  let ψ₀ := Term.subst ψ₁ z
  let q₀ := Term.subst q₁ z
  let (t₀, u₀) ← Internal.eqParts q₀
  let d₀ ← pNil Γ (Φ' ++ [ψ₀]) t₀ u₀
  -- a construction
  let Φc := Φ'.map Internal.weaken2 ++ [Internal.weakenElem (imp ψ₁ q₁)]
  let ψc := Internal.listConsAt 1 a ψ₁
  let qc := Internal.listConsAt 1 a q₁
  let (tc, uc) ← Internal.eqParts qc
  let dc ← pCons (c :: a :: Γ) (Φc ++ [ψc]) tc uc
  let dχ₁ := RoseTree.node (.listIndHyp 0 1) [Internal.Logic.impI logicBase Φ'.length ψ₀ q₀ d₀,
    Internal.Logic.impI logicBase Φc.length ψc qc dc]
  let dFun := RoseTree.node .funExt [RoseTree.node .conv [RoseTree.node .cong
    [RoseTree.node .beta [], RoseTree.node .beta []],
    RoseTree.node .propExt [Internal.Logic.trueI, dχ₁]]]
  let dχ := RoseTree.node (.cut (Term.eq Fχ (Term.lam c tt))) [dFun,
    RoseTree.node (.convFrom (Term.app Fχ (v i))) [RoseTree.node .beta [],
      RoseTree.node .conv [RoseTree.node .trans [RoseTree.node .cong
        [RoseTree.node (.rwHyp Φ.length false) [], RoseTree.node .refl []],
        RoseTree.node .beta []], Internal.Logic.trueI]]]
  pure (RoseTree.node (.apply (logicBase + 4) [] [q, ψ]) [dχ, RoseTree.node (.hyp h) []])

/-- The number of children the kernel's term of a label has, where the type checker's case
depends on the children's types. -/
def arityOf (l : ℕ) : Option ℕ :=
  if l = Kernel.Label.var ∨ l = Kernel.Label.fst ∨ l = Kernel.Label.snd then some 1
  else if l = Kernel.Label.lam ∨ l = Kernel.Label.app ∨ l = Kernel.Label.pair ∨
    l = Kernel.Label.cons then some 2
  else if l = Kernel.Label.cond then some 3
  else none

/-- The proof at a label: by weak reduction of the statement's sides under their arguments, by
the language's rules and the definitions alone and, where that fails, with the lemmas as well; or,
for a label whose case depends on the children's types, by case analysis of the list of the
children to their number, each shorter list by weak reduction with the lemmas, the induction
hypothesis reverted and, at that number, instantiated at each child, at the arguments, and for an
abstraction's body at the first context extended by the abstraction's type, the instances
rewriting after the language's rules and before the lemmas. The lemmas' matchings are prepared
({name}`Geb.FreeTopos.Internal.prepareRules`). -/
def labelLeaf (P : Prog) (lemmas : List NormRule) (E : Array Entry) (bits : Option (List Bool)) :
    Internal.Prover := fun Γ Φ t u ↦ do
  let rs := baseNorm P ++ lemmas
  let plain := funExt4 P.G (byWeak P.G E 0 rs)
  let k? := bits.bind fun bs ↦ arityOf (Oitavem.rank bs)
  match k? with
  | none => (funExt4 P.G (byWeak P.G E 0 (baseNorm P)) Γ Φ t u).orElse fun _ ↦ plain Γ Φ t u
  | some k => do
    -- the children's list: the variable the induction hypothesis folds
    let (L, _) ← Internal.eqParts (← Φ[0]?)
    let i ← match (L.children[2]?).map (·.label) with
      | some (Internal.Label.var j) => some j
      | _ => none
    let some (_, (CR, sR, fG)) := folds P | none
    let rest : Internal.Prover := fun Γ Φ t u ↦ do
      let child (p : ℕ) : Term := v (4 + 2 * (k - 1 - p) + 1)
      let A := Term.fst (Term.app (Term.roseRec CR sR (child 0))
        (Term.rename fG fun j ↦ if j = 1 then 3 else j))
      funExt4 P.G (withChildHyps P.G E 0 rs (Φ.length - 1) (List.range k) (fun p ↦
          [[v 3, v 2, v 1, v 0]] ++ if p = 1 then [[v 3, consT treeTy A (v 2), v 1, v 0]] else [])
        (fun insts ↦ withWeakHyps P.G E 0 rs insts fun extra ↦
          byWeak P.G E 0 (baseNorm P ++ extra ++ lemmas)))
        Γ Φ t u
    let levels : ℕ → Internal.Prover := fun m ↦ m.rec rest fun _ next ↦
      fun Γ Φ t u ↦ revertCase P.G 0 P.o 0 (Φ.length - 1) plain next Γ Φ t u
    revertCase P.G 0 P.o i 0 plain (levels (k - 1)) Γ Φ t u

/-- The proof at a construction: case analysis of the label's bits, to five of them, each case
proved by {lit}`labelLeaf` with the bits of a label ending there, or none past the fourth,
which no kernel label has. -/
def byLabels (P : Prog) (ix : String → ℕ) (E : Array Entry) : Internal.Prover :=
  let lemmas := Internal.prepareRules E (lemmaRules ix)
  let go : ℕ → List Bool → ℕ → Internal.Prover := fun d ↦ d.rec
    (fun bs i ↦ byListSplit P.G 0 i (labelLeaf P lemmas E (some bs)) (labelLeaf P lemmas E none))
    fun _ rec bs i ↦ byListSplit P.G 0 i (labelLeaf P lemmas E (some bs))
      -- the bit, zero then one, the rest at index one after the case's variable
      (bySplit2 3 4 1 (rec (bs ++ [false]) 1) (rec (bs ++ [true]) 1))
  go 4 [] 1

/-- The statement: the type of a term weakened past a type inserted below a context's first part
is its type in the context without it, the two sides as functions of the environment, the
context's parts and the inserted type. -/
def weakening (P : Prog) : Internal.Thm :=
  ⟨0, [treeTy], [], Term.eq (Term.app (call (P.idx "wkL") [] []) (v 0))
    (Term.app (call (P.idx "wkR") [] []) (v 0))⟩

/-- The proof of the statement, found and checked with the development, for the program's
definitions with the index of each named one, and the measurement: the nodes of the development's
lemmas and of the statement's derivation, and the milliseconds its proof and its check take; an
error where either fails. -/
def checkWeakening (ds : List (List Char × Tree)) (idx : String → ℕ) : IO Unit := do
  let some P := prog? ds idx | throw (IO.userError "the program does not translate")
  let some dev := development P | throw (IO.userError "the development is not stated")
  let decls ← match developNamed dev with
    | .ok decls => pure decls
    | .error name => throw (IO.userError s!"the lemma {name} is not proved")
  let some (G, E) := Internal.checkDev P.G #[] decls
    | throw (IO.userError "the development does not check")
  let ix (name : String) : ℕ := (dev.findIdx? (·.1 == name)).getD 0
  let a := weakening P
  let t₀ ← IO.monoMsNow
  let some d := Internal.byRoseIndHyp 2 0 1 (byLabels P ix E) a.ctx [] (sides a).1 (sides a).2
    | throw (IO.userError "the statement is not proved")
  let t₁ ← IO.monoMsNow
  if !Internal.checkThms G [Decl.language a d] E then
    throw (IO.userError "the statement's derivation does not check")
  let t₂ ← IO.monoMsNow
  let lemmaNodes := (decls.filterMap fun | Decl.language _ d => some (derivSize d) | _ => none).sum
  IO.println "lemma_nodes,theorem_nodes,proof_milliseconds,check_milliseconds"
  IO.println s!"{lemmaNodes},{derivSize d},{t₁ - t₀},{t₂ - t₁}"

#eval do
  let some ds := bundled Metalogic.ProofTests.bundler.toList programText.toList
    | throw (IO.userError "the program does not read")
  checkWeakening ds fun name ↦ (defIndex ds name.toList).getD 0

end GebTests.Prototypes.FreeTopos.Weakening

end
