/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.LF.Topos.Proofs
public import Geb.Prototypes.LF.Topos.ProofsMod
public import Geb.Prototypes.LF.Topos.Theorems
public meta import Geb.Prototypes.LF.Topos.Proofs -- shake: keep
public meta import Geb.Prototypes.LF.Topos.ProofsMod -- shake: keep
public meta import Geb.Prototypes.LF.Topos.Theorems -- shake: keep

/-!
# Tests for the decoding of proofs

The proofs that the type inhabitation solver Canonical finds of three equations of addition in
pure LF decode to derivations of the internal language that its checker accepts: a computation
of the fold at zero, one at a successor, and an induction whose step substitutes equals. So do a
substitution of equals into a motive whose fold's step mentions the motive's variable, the
computations of the fold of a list, the proof by induction on lists that the right fold by
construction from the empty list is the identity, the computation of the fold of a rose tree at a
construction, and the proof by induction on rose trees that the fold by the constant step zero is
zero, for rose trees of natural-number labels and of lists of natural numbers alike. Proofs that
check only modulo the rewrite rules decode to certificates the checker with a step of conversion
accepts and the base checker does not: reflexivity at an equation that holds by computation, and
an induction whose step computes under its hypothesis, and the associativity of concatenation by
list induction, its step by the substitution of equals or by congruence; a false equation it
rejects. Congruence applies the successor to the computation of the fold at zero. Theorems of
the language, declared past the signature, decode at their applications to the language's
applications of their entries: one without hypotheses at a variable and at a compound term, and
one whose hypothesis is proved by reflexivity.

## Tags

prototype, logical framework, LF, proof, derivation
-/

@[expose] public section

namespace Geb.LF.Topos.Tests

open FreeTopos.Internal (Globals Thm zeroPrim succPrim nilPrim consPrim nodePrim lnodePrim
  inlPrim inrPrim casePrim)

/-- Zero, the successor, the empty list, the construction of a list, the constructions of rose
trees of natural-number labels and of labels of a type, the injections into a coproduct and its
case analysis, of indices {lit}`0` to {lit}`8`. -/
def pfGlobals : Globals :=
  ⟨[zeroPrim, succPrim, nilPrim, consPrim, nodePrim, lnodePrim, inlPrim, inrPrim, casePrim], [], 0⟩

/-- The indices of the primitive arrows of {name}`pfGlobals`. -/
def pfIdx : PrimIdx := ⟨0, 1, 2, 3, 4, 5, 6, 7, 8, []⟩

/-- The successor as an LF abstraction. -/
def succLam : Expr := Expr.lam (succ (v 0))

/-- Whether a proof, in an LF context of {lit}`n` variables of {lit}`tp` and term variables of the
types of {lit}`Γ`, decodes to a derivation that proves the decoding of an equation in the
internal context {lit}`Γ` in {lit}`n` object variables. -/
def provesIn (n : ℕ) (Γ : List PartialHorn.Tree) (M F : Expr) : Bool :=
  match decPf pfIdx M (Γ.map fun _ ↦ none) 0, dec pfIdx F Γ.length with
    | some D, some φ => Thm.checks pfGlobals #[] ⟨n, Γ, [], φ⟩ D
    | _, _ => false

/-- Whether a proof, in an LF context of term variables of the types of {lit}`Γ`, decodes to a
derivation that proves the decoding of an equation in the internal context {lit}`Γ`. -/
def proves (Γ : List PartialHorn.Tree) (M F : Expr) : Bool := provesIn 0 Γ M F

/-- Whether a proof modulo the rules, in an LF context of term variables of the types of
{lit}`Γ`, decodes to a certificate with steps of conversion that proves the decoding of an equation
in the internal context {lit}`Γ`. -/
def provesMod (Γ : List PartialHorn.Tree) (M F : Expr) : Bool :=
  match decPfMod pfIdx M (Γ.map fun _ ↦ none) 0, dec pfIdx F Γ.length with
    | some D, some φ => Thm.convChecks pfGlobals #[] ⟨0, Γ, [], φ⟩ D
    | _, _ => false

/-- Whether a proof, in an LF context of term variables of the natural numbers, decodes to a
derivation that proves the decoding of an equation in the internal context of as many natural
numbers. -/
def provesNat (k : ℕ) (M F : Expr) : Bool := proves (List.replicate k FreeTopos.nat) M F

-- `n + 0 = n` by the computation of the fold at zero.
#guard provesNat 1 (Expr.const 25 [nat, v 0, succLam])
  (eq nat (natRec nat (v 0) succLam zero) (v 0))

-- `m + succ n = succ (m + n)` by the computation of the fold at a successor.
#guard provesNat 2 (Expr.const 26 [nat, v 1, succLam, v 0])
  (eq nat (natRec nat (v 1) succLam (succ (v 0))) (succ (natRec nat (v 1) succLam (v 0))))

/-- The step of the induction for {lit}`0 + n = n`: the substitution of equals at the motive
{lit}`λ x. 0 + succ n = succ x`, from the hypothesis {lit}`0 + n = n` and the computation of the
fold at the successor. -/
def zeroAddStep : Expr :=
  Expr.lam (Expr.lam (Expr.const 19 [nat,
    Expr.lam (eq nat (natRec nat zero succLam (succ (v 2))) (succ (v 0))),
    natRec nat zero succLam (v 1), v 1, v 0, Expr.const 26 [nat, zero, succLam, v 1]]))

-- `0 + n = n` by induction.
#guard provesNat 1 (Expr.const 29 [Expr.lam (eq nat (natRec nat zero succLam (v 0)) (v 0)),
    Expr.const 25 [nat, zero, succLam], zeroAddStep, v 0])
  (eq nat (natRec nat zero succLam (v 0)) (v 0))

/-- {lit}`n + 0`, the fold whose computation at zero proves it equal to {lit}`n`. -/
def addZero : Expr := natRec nat (v 0) succLam zero

-- `natRec 0 (λ a. n) 1 = n`: the motive `λ x. natRec 0 (λ a. x) 1 = x`, whose fold's step
-- mentions its variable, holds at `n + 0` by the computation of the fold at a successor, and
-- `n + 0 = n` by its computation at zero.
#guard provesNat 1 (Expr.const 19 [nat,
    Expr.lam (eq nat (natRec nat zero (Expr.lam (v 1)) (succ zero)) (v 0)), addZero, v 0,
    Expr.const 25 [nat, v 0, succLam],
    Expr.const 26 [nat, zero, Expr.lam (addZero.rename Nat.succ), zero]])
  (eq nat (natRec nat zero (Expr.lam (v 1)) (succ zero)) (v 0))

/-- The construction of a list of natural numbers as a step of a fold:
{lit}`λ h r. cons nat (pair h r)`. -/
def consLam : Expr := Expr.lam (Expr.lam (cons nat (pair nat (list nat) (v 1) (v 0))))

/-- The right fold of a list of natural numbers by construction from the empty list. -/
def foldCons (x : Expr) : Expr := listRec nat (list nat) (nil nat) consLam x

-- `foldCons nil = nil` by the computation of the fold at the empty list.
#guard proves [] (Expr.const 34 [nat, list nat, nil nat, consLam])
  (eq (list nat) (foldCons (nil nat)) (nil nat))

-- `foldCons (cons h t) = cons h (foldCons t)` by the computation of the fold at a construction.
#guard proves [FreeTopos.list FreeTopos.nat, FreeTopos.nat]
  (Expr.const 35 [nat, list nat, nil nat, consLam, v 1, v 0])
  (eq (list nat) (foldCons (cons nat (pair nat (list nat) (v 1) (v 0))))
    (cons nat (pair nat (list nat) (v 1) (foldCons (v 0)))))

/-- The step of the induction for {lit}`foldCons l = l`: the substitution of equals at the motive
{lit}`λ y. foldCons (cons h t) = cons h y`, from the hypothesis {lit}`foldCons t = t` and the
computation of the fold at the construction. -/
def foldConsStep : Expr :=
  Expr.lam (Expr.lam (Expr.lam (Expr.const 19 [list nat,
    Expr.lam (eq (list nat) (foldCons (cons nat (pair nat (list nat) (v 3) (v 2))))
      (cons nat (pair nat (list nat) (v 3) (v 0)))),
    foldCons (v 1), v 1, v 0, Expr.const 35 [nat, list nat, nil nat, consLam, v 2, v 1]])))

-- `foldCons l = l` by induction on lists.
#guard proves [FreeTopos.list FreeTopos.nat]
  (Expr.const 36 [nat, Expr.lam (eq (list nat) (foldCons (v 0)) (v 0)),
    Expr.const 34 [nat, list nat, nil nat, consLam], foldConsStep, v 0])
  (eq (list nat) (foldCons (v 0)) (v 0))

/-- The label of the root as a step of the fold of a rose tree: {lit}`λ p. fst p`. -/
def labelLam : Expr := Expr.lam (fst nat (list nat) (v 0))

/-- The construction of a rose tree from the label {lit}`l` and the children {lit}`cs`, the
variables of indices {lit}`i` and {lit}`j`. -/
def nodeAt (i j : ℕ) : Expr := node (pair nat (list rose) (v i) (v j))

-- `roseRec labelLam (node (pair l cs)) = fst (pair l (map (roseRec labelLam) cs))` by the
-- computation of the fold at a construction.
#guard proves [FreeTopos.list FreeTopos.rose, FreeTopos.nat]
  (Expr.const 40 [nat, labelLam, v 1, v 0])
  (eq nat (roseRec nat labelLam (nodeAt 1 0))
    (fst nat (list nat) (pair nat (list nat) (v 1) (listRec rose (list nat) (nil nat)
      (Expr.lam (Expr.lam (cons nat (pair nat (list nat) (roseRec nat labelLam (v 1)) (v 0)))))
      (v 0)))))

/-- The constant step zero of the fold of a rose tree. -/
def zeroLam : Expr := Expr.lam zero

/-- The step of the induction for {lit}`roseRec zeroLam t = zero`: the computation of the fold at
the construction, under the label, the children and the hypothesis at the children. -/
def zeroFoldStep : Expr :=
  Expr.lam (Expr.lam (Expr.lam (Expr.const 40 [nat, zeroLam, v 2, v 1])))

-- `roseRec zeroLam t = zero` by induction on rose trees.
#guard proves [FreeTopos.rose]
  (Expr.const 41 [Expr.lam (eq nat (roseRec nat zeroLam (v 0)) zero), zeroFoldStep, v 0])
  (eq nat (roseRec nat zeroLam (v 0)) zero)

/-- The type of lists of natural numbers, the labels of the rose trees below. -/
def listNatLF : Expr := list nat

/-- The label of the root as a step of the fold of a rose tree of lists: {lit}`λ p. fst p`. -/
def lLabelLam : Expr := Expr.lam (fst listNatLF (list listNatLF) (v 0))

-- `lroseRec lLabelLam (lnode (pair l cs)) = fst (pair l (map (lroseRec lLabelLam) cs))` by the
-- computation of the fold of a rose tree of lists at a construction.
#guard proves [FreeTopos.list (FreeTopos.lrose (FreeTopos.list FreeTopos.nat)),
    FreeTopos.list FreeTopos.nat]
  (Expr.const 45 [listNatLF, listNatLF, lLabelLam, v 1, v 0])
  (eq listNatLF (lroseRec listNatLF listNatLF lLabelLam
      (lnode listNatLF (pair listNatLF (list (lrose listNatLF)) (v 1) (v 0))))
    (fst listNatLF (list listNatLF) (pair listNatLF (list listNatLF) (v 1)
      (listRec (lrose listNatLF) (list listNatLF) (nil listNatLF)
        (Expr.lam (Expr.lam (cons listNatLF (pair listNatLF (list listNatLF)
          (lroseRec listNatLF listNatLF lLabelLam (v 1)) (v 0))))) (v 0)))))

/-- The step of the induction for {lit}`lroseRec zeroLam t = zero` on rose trees of lists: the
computation of the fold at the construction, under the label, the children and the hypothesis at
the children. -/
def lZeroFoldStep : Expr :=
  Expr.lam (Expr.lam (Expr.lam (Expr.const 45 [listNatLF, nat, zeroLam, v 2, v 1])))

-- `lroseRec zeroLam t = zero` by induction on rose trees of lists.
#guard proves [FreeTopos.lrose (FreeTopos.list FreeTopos.nat)]
  (Expr.const 46 [listNatLF, Expr.lam (eq nat (lroseRec listNatLF nat zeroLam (v 0)) zero),
    lZeroFoldStep, v 0])
  (eq nat (lroseRec listNatLF nat zeroLam (v 0)) zero)

/-- The case analysis of a coproduct of two copies of the natural numbers into the natural numbers
by the functions {lit}`g` and {lit}`h`, applied to {lit}`c`. -/
def caseNat (g h c : Expr) : Expr :=
  app (coprod nat nat) nat (case nat nat nat (pair (exp nat nat) (exp nat nat) g h)) c

/-- The internal context of an element {lit}`u` of the natural numbers and two functions
{lit}`h` and {lit}`g` on them, the innermost first. -/
def caseCtx : List PartialHorn.Tree :=
  [FreeTopos.nat, FreeTopos.exp FreeTopos.nat FreeTopos.nat,
    FreeTopos.exp FreeTopos.nat FreeTopos.nat]

-- `case (g, h) (inl u) = g u` by the computation of the case analysis at a left injection.
#guard proves caseCtx (Expr.const 53 [nat, nat, nat, v 2, v 1, v 0])
  (eq nat (caseNat (v 2) (v 1) (inl nat nat (v 0))) (app nat nat (v 2) (v 0)))

-- `case (g, h) (inr u) = h u` by the computation of the case analysis at a right injection.
#guard proves caseCtx (Expr.const 54 [nat, nat, nat, v 2, v 1, v 0])
  (eq nat (caseNat (v 2) (v 1) (inr nat nat (v 0))) (app nat nat (v 1) (v 0)))

-- `case (g, h) (inl u) = h u` does not hold.
#guard !proves caseCtx (Expr.const 53 [nat, nat, nat, v 2, v 1, v 0])
  (eq nat (caseNat (v 2) (v 1) (inl nat nat (v 0))) (app nat nat (v 1) (v 0)))

-- `c = c` by case analysis on `c`, at either injection by reflexivity.
#guard proves [FreeTopos.coprod FreeTopos.nat FreeTopos.nat]
  (Expr.const 55 [nat, nat, Expr.lam (eq (coprod nat nat) (v 0) (v 0)),
    Expr.lam (Expr.const 18 [coprod nat nat, inl nat nat (v 0)]),
    Expr.lam (Expr.const 18 [coprod nat nat, inr nat nat (v 0)]), v 0])
  (eq (coprod nat nat) (v 0) (v 0))

-- `0 = 1` from a term of the initial object.
#guard proves [FreeTopos.zero] (Expr.const 56 [v 0, eq nat zero (succ zero)])
  (eq nat zero (succ zero))

-- `0 = 1` does not follow from a natural number.
#guard !proves [FreeTopos.nat] (Expr.const 56 [v 0, eq nat zero (succ zero)])
  (eq nat zero (succ zero))

/-- The function on the natural numbers constantly zero. -/
def zeroFn : Expr := lam nat nat zeroLam

-- `case (zeroFn, zeroFn) c = 0` by case analysis on `c` modulo the rules: at either injection
-- by reflexivity, the computations of the case analysis and of the abstraction left to the
-- conversion.
#guard provesMod [FreeTopos.coprod FreeTopos.nat FreeTopos.nat]
  (Expr.const 55 [nat, nat, Expr.lam (eq nat (caseNat zeroFn zeroFn (v 0)) zero),
    Expr.lam (Expr.const 18 [nat, zero]), Expr.lam (Expr.const 18 [nat, zero]), v 0])
  (eq nat (caseNat zeroFn zeroFn (v 0)) zero)

-- `t = t` for a term `t` of the type of an object variable, by reflexivity: the LF context's
-- variable of `tp`, outermost, is the object variable.
#guard provesIn 1 [PartialHorn.var 0] (Expr.const 18 [v 1, v 0]) (eq (v 1) (v 0) (v 0))

/-- The construction of a list as a step of a fold, at the type of the LF variable of index
{lit}`a` outside the step: {lit}`λ h r. cons A (pair h r)`. -/
def consLamAt (a : ℕ) : Expr :=
  Expr.lam (Expr.lam (cons (v (a + 2)) (pair (v (a + 2)) (list (v (a + 2))) (v 1) (v 0))))

-- `foldr cons nil nil = nil` at the list type of an object variable, by the computation of the
-- fold at the empty list.
#guard provesIn 1 [] (Expr.const 34 [v 0, list (v 0), nil (v 0), consLamAt 0])
  (eq (list (v 0)) (listRec (v 0) (list (v 0)) (nil (v 0)) (consLamAt 0) (nil (v 0))) (nil (v 0)))

-- The same in no object variables does not hold: the type mentions an object variable.
#guard !provesIn 0 [] (Expr.const 34 [v 0, list (v 0), nil (v 0), consLamAt 0])
  (eq (list (v 0)) (listRec (v 0) (list (v 0)) (nil (v 0)) (consLamAt 0) (nil (v 0))) (nil (v 0)))

-- `n + 0 = n` by reflexivity holds by computation: the conversion checker accepts it, and the base
-- checker, which does not compute, rejects it.
#guard provesMod [FreeTopos.nat] (Expr.const 18 [nat, v 0]) (eq nat addZero (v 0))
#guard !proves [FreeTopos.nat] (Expr.const 18 [nat, v 0]) (eq nat addZero (v 0))

-- `n + 0 = succ n` does not hold.
#guard !provesMod [FreeTopos.nat] (Expr.const 18 [nat, v 0]) (eq nat addZero (succ (v 0)))

/-- The step of the induction for {lit}`0 + n = n` modulo the rules: the substitution of equals
at the motive {lit}`λ y. succ (0 + n) = succ y`, from the hypothesis {lit}`0 + n = n` and
reflexivity, the computation of the fold at the successor left to the conversion. -/
def zeroAddStepMod : Expr :=
  Expr.lam (Expr.lam (Expr.const 19 [nat,
    Expr.lam (eq nat (succ (natRec nat zero succLam (v 2))) (succ (v 0))),
    natRec nat zero succLam (v 1), v 1, v 0,
    Expr.const 18 [nat, succ (natRec nat zero succLam (v 1))]]))

-- `0 + n = n` by induction modulo the rules.
#guard provesMod [FreeTopos.nat] (Expr.const 29 [Expr.lam (eq nat (natRec nat zero succLam (v 0))
    (v 0)), Expr.const 18 [nat, zero], zeroAddStepMod, v 0])
  (eq nat (natRec nat zero succLam (v 0)) (v 0))

/-- The concatenation of lists of natural numbers, the right fold of the first by construction
from the second. -/
def appendLF (xs ys : Expr) : Expr := listRec nat (list nat) ys consLam xs

/-- The step of the induction for the associativity of concatenation modulo the rules, in the
context of {lit}`xs`, {lit}`ys` and {lit}`zs`: the substitution of equals at the motive
{lit}`λ y. cons h ((t ++ ys) ++ zs) = cons h y`, from the hypothesis and reflexivity. -/
def appendAssocStep : Expr :=
  Expr.lam (Expr.lam (Expr.lam (Expr.const 19 [list nat,
    Expr.lam (eq (list nat)
      (cons nat (pair nat (list nat) (v 3) (appendLF (appendLF (v 2) (v 5)) (v 4))))
      (cons nat (pair nat (list nat) (v 3) (v 0)))),
    appendLF (appendLF (v 1) (v 4)) (v 3), appendLF (v 1) (appendLF (v 4) (v 3)), v 0,
    Expr.const 18 [list nat,
      cons nat (pair nat (list nat) (v 2) (appendLF (appendLF (v 1) (v 4)) (v 3)))]])))

-- `(xs ++ ys) ++ zs = xs ++ (ys ++ zs)` by induction on `xs` modulo the rules.
#guard provesMod [FreeTopos.list FreeTopos.nat, FreeTopos.list FreeTopos.nat,
    FreeTopos.list FreeTopos.nat]
  (Expr.const 36 [nat, Expr.lam (eq (list nat) (appendLF (appendLF (v 0) (v 2)) (v 1))
      (appendLF (v 0) (appendLF (v 2) (v 1)))),
    Expr.const 18 [list nat, appendLF (v 1) (v 0)], appendAssocStep, v 2])
  (eq (list nat) (appendLF (appendLF (v 2) (v 1)) (v 0)) (appendLF (v 2) (appendLF (v 1) (v 0))))

-- `succ (n + 0) = succ n` by congruence of the successor at the computation of the fold at zero.
#guard provesNat 1
  (Expr.const 47 [nat, nat, succLam, addZero, v 0, Expr.const 25 [nat, v 0, succLam]])
  (eq nat (succ addZero) (succ (v 0)))

/-- The step of the induction for the associativity of concatenation modulo the rules by
congruence: the construction with the element applied to the hypothesis. -/
def appendAssocCongStep : Expr :=
  Expr.lam (Expr.lam (Expr.lam (Expr.const 47 [list nat, list nat,
    Expr.lam (cons nat (pair nat (list nat) (v 3) (v 0))),
    appendLF (appendLF (v 1) (v 4)) (v 3), appendLF (v 1) (appendLF (v 4) (v 3)), v 0])))

-- `(xs ++ ys) ++ zs = xs ++ (ys ++ zs)` by induction on `xs` and congruence modulo the rules.
#guard provesMod [FreeTopos.list FreeTopos.nat, FreeTopos.list FreeTopos.nat,
    FreeTopos.list FreeTopos.nat]
  (Expr.const 36 [nat, Expr.lam (eq (list nat) (appendLF (appendLF (v 0) (v 2)) (v 1))
      (appendLF (v 0) (appendLF (v 2) (v 1)))),
    Expr.const 18 [list nat, appendLF (v 1) (v 0)], appendAssocCongStep, v 2])
  (eq (list nat) (appendLF (appendLF (v 2) (v 1)) (v 0)) (appendLF (v 2) (appendLF (v 1) (v 0))))

/-- The theorem that the right fold of a list of natural numbers by construction from the empty
list is the identity, in one variable of a list. -/
def foldConsThm : Thm :=
  ⟨0, [FreeTopos.list FreeTopos.nat], [],
    (dec pfIdx (eq (list nat) (foldCons (v 0)) (v 0)) 1).getD (FreeTopos.Internal.Term.var 0)⟩

/-- The symmetry of equality of natural numbers, in two variables, the first outermost, from the
equation of the first with the second. -/
def symmNatThm : Thm :=
  ⟨0, [FreeTopos.nat, FreeTopos.nat],
    [(dec pfIdx (eq nat (v 1) (v 0)) 2).getD (FreeTopos.Internal.Term.var 0)],
    (dec pfIdx (eq nat (v 0) (v 1)) 2).getD (FreeTopos.Internal.Term.var 0)⟩

/-- The entries of {name}`foldConsThm` and {name}`symmNatThm`. -/
def thmEntries : Array FreeTopos.Internal.Entry := #[.language foldConsThm, .language symmNatThm]

/-- The indices of the primitive arrows, with the theorems of {name}`thmEntries` as the
constants past the signature. -/
def thmIdx : PrimIdx := { pfIdx with thms := [(0, 1), (1, 2)] }

/-- The signature extended by the declarations of the theorems of {name}`thmEntries`. -/
def thmSig : Sig :=
  sig ++ [foldConsThm, symmNatThm].filterMap (thmTy pfGlobals thmIdx)

/-- Whether a proof, in an LF context of term variables of the types of {lit}`Γ`, decodes, with the
theorems of {name}`thmEntries`, to a derivation that proves the decoding of an equation in the
internal context {lit}`Γ`. -/
def provesThm (Γ : List PartialHorn.Tree) (M F : Expr) : Bool :=
  match decPf thmIdx M (Γ.map fun _ ↦ none) 0, dec thmIdx F Γ.length with
    | some D, some φ => Thm.checks pfGlobals thmEntries ⟨0, Γ, [], φ⟩ D
    | _, _ => false

-- The theorems are well formed and declared.
#guard foldConsThm.wellFormed pfGlobals && symmNatThm.wellFormed pfGlobals
#guard thmSig.length == sig.length + 2

-- `foldCons xs = xs` by the theorem, in LF and decoded.
#guard Checks thmSig [tm (list nat)] (Expr.const 57 [v 0])
  (pf (eq (list nat) (foldCons (v 0)) (v 0)))
#guard provesThm [FreeTopos.list FreeTopos.nat] (Expr.const 57 [v 0])
  (eq (list nat) (foldCons (v 0)) (v 0))

-- `foldCons (foldCons xs) = foldCons xs` by the theorem at a term other than a variable.
#guard provesThm [FreeTopos.list FreeTopos.nat] (Expr.const 57 [foldCons (v 0)])
  (eq (list nat) (foldCons (foldCons (v 0))) (foldCons (v 0)))

-- The theorem does not prove an equation other than its instance.
#guard !provesThm [FreeTopos.list FreeTopos.nat] (Expr.const 57 [v 0])
  (eq (list nat) (foldCons (v 0)) (nil nat))

-- `n = m` from `m = n` by the symmetry theorem, its hypothesis proved by a hypothesis.
#guard Checks thmSig [pf (eq nat (v 0) (v 1)), tm nat, tm nat] (Expr.const 58 [v 1, v 2, v 0])
  (pf (eq nat (v 2) (v 1)))

-- `n = n` by the symmetry theorem, its hypothesis proved by reflexivity.
#guard provesThm [FreeTopos.nat] (Expr.const 58 [v 0, v 0, Expr.const 18 [nat, v 0]])
  (eq nat (v 0) (v 0))

end Geb.LF.Topos.Tests

end
