/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.LF.Topos.Adequacy
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The decoding of the proofs of the representation of the internal language

The canonical LF terms of the families of proofs of {name}`Geb.LF.Topos.sig` decode to
derivations of the internal language ({name}`Geb.FreeTopos.Internal.check`). An LF context of
proofs declares variables of families of terms of the fragment's types and of families of proofs
of its formulas, in any order; the first are the variables of the internal context, the second
its hypotheses. The decoding of a proof carries an environment that gives, for each LF variable,
whether it is a term variable or the index of its hypothesis, and the number of hypotheses, which
grows where the derivation a rule decodes to adds one of its own by a cut.

Each rule of the signature decodes to the derivation of its conclusion from its premises'
decodings. Reflexivity, β, the computations of pairs and the η rules decode to joins of
rewritings; the computations of the fold, an application of the fold with parameters
({name}`Geb.FreeTopos.Internal.iterDefn`), to the unfolding of the definition, the computation of
the language's fold, β and the components of a pair; function and propositional extensionality to
the rules of the same names. The substitution of equals decodes to the rewriting of the motive by
the equation, cut as a hypothesis, along its variable ({lit}`congAlong`). The
induction on the natural numbers proves the motive at a term from the equality of the motive and
the function constantly true, proved by function extensionality and induction on the fresh
variable ({lit}`natIndD`). No derivation cuts through a formula that substitutes into a motive, so
that each formula the checker types is the decoding of a term or built from such by the language's
term formers.

## Main definitions

* {lit}`tmIdx` — the renaming of an LF context's term variables to the internal context's.
* {lit}`congAlong` — the rewriting by a derivation at a variable's occurrences in a term.
* {lit}`natIndD` — the derivation of the induction on the natural numbers at a term.
* {lit}`decPf` — the decoding of a proof.

## References

* {cite}`HarperLicata2007`, Section 3.4, for the adequacy of the representation of judgments.

## Tags

logical framework, LF, adequacy, proof, derivation, internal language
-/

set_option doc.verso true

@[expose] public section

namespace Geb.LF.Topos

open FreeTopos.Internal (Term Deriv instVar weaken1)

/-- The renaming of an LF context's term variables to the internal context's: an environment
lists, for each LF variable, the innermost first, nothing for a term variable and the index of
its hypothesis for a proof variable; a term variable is renamed to the number of term variables
inside it, and a proof variable, which no term mentions, to zero. -/
def tmIdx : List (Option ℕ) → ℕ → ℕ :=
  List.rec id fun o _ r ↦ match o with
    | none => liftR r
    | some _ => fun i ↦ match i with
      | 0 => 0
      | j + 1 => r j

/-- The decoding of an LF term in an LF context of proofs: its term variables renamed to the
internal context's, then decoded. -/
def termOf (kz ks ki : ℕ) (env : List (Option ℕ)) (e : Expr) : Option MTerm :=
  dec kz ks ki (e.rename (tmIdx env))

/-- The body of an abstraction of the internal language. -/
def lamBody (s : MTerm) : Option MTerm :=
  match s.label, s.children with
    | .lam _, [b] => some b
    | _, _ => none

/-- A derivation of a rule and its children. -/
abbrev nd (r : FreeTopos.Internal.Rule) (cs : List Deriv) : Deriv := RoseTree.node r cs

/-- The identity rewriting. -/
abbrev reflD : Deriv := nd .refl []

/-- The proof of an equation by two rewritings to one term. -/
abbrev joinD (d₁ d₂ : Deriv) : Deriv := nd .join [d₁, d₂]

/-- One rewriting after another. -/
abbrev transD (d₁ d₂ : Deriv) : Deriv := nd .trans [d₁, d₂]

/-- A rewriting by a rule at the root. -/
abbrev ruleD (r : FreeTopos.Internal.Rule) : Deriv := nd r []

/-- One step of the rewriting by a derivation at the occurrences of a variable in a term: the
derivation at the variable, the identity at another, and the congruence elsewhere, under a
binder at the variable's successor; the start and the step of a fold are left in place. -/
def congAlongStep (d : Deriv) (l : FreeTopos.Internal.Label) (cs : List (Term × (ℕ → Deriv)))
    (j : ℕ) : Deriv :=
  match l, cs with
    | .var i, _ => if i = j then d else reflD
    | .lam _, cs => nd .cong (cs.map fun c ↦ c.2 (j + 1))
    | .natRec, [_, _, (_, rm)] => nd .cong [reflD, reflD, rm j]
    | .listRec, [_, _, (_, rm)] => nd .cong [reflD, reflD, rm j]
    | .roseRec _, [_, (_, rm)] => nd .cong [reflD, rm j]
    | _, cs => nd .cong (cs.map fun c ↦ c.2 j)

/-- The rewriting by a derivation at the occurrences of the variable of index {lit}`j` in a
term. -/
def congAlong (d : Deriv) : Term → ℕ → Deriv := RoseTree.para (congAlongStep d)

/-- The formula true, the equality of the terminal object's element with itself. -/
def truth : Term := Term.eq Term.star Term.star

/-- The derivation of a motive {lit}`pb`, a formula in a variable of the natural numbers, at a
term {lit}`n`, by the induction whose base and step are {lit}`D₀` and {lit}`Ds`, under
{lit}`m` hypotheses: the motive as a function is cut as equal to the function constantly true, by
function extensionality and propositional extensionality, the converse direction by the
induction on the fresh variable; the motive at {lit}`n` is the β-reduct of the function's
application to {lit}`n`, which that equation rewrites to the true one's. -/
def natIndD (kz ks : ℕ) (pb n : Term) (m : ℕ) (D₀ Ds : Deriv) : Deriv :=
  let L := Term.lam FreeTopos.nat pb
  let R := Term.lam FreeTopos.nat truth
  nd (.cut (Term.eq L R))
    [nd .funExt [nd .conv [nd .cong [ruleD .beta, ruleD .beta],
        nd .propExt [joinD reflD reflD, nd (.natIndHyp kz ks) [D₀, Ds]]]],
      nd (.convFrom (Term.app L n))
        [ruleD .beta, nd .conv [nd .cong [ruleD (.rwHyp m false), reflD],
          nd .conv [ruleD .beta, joinD reflD reflD]]]]

/-- The derivation of the substitution of equals: the motive {lit}`pb` at {lit}`u` from the
proof {lit}`Dh` of {lit}`t = u` and the proof {lit}`Dp` of the motive at {lit}`t`, under
{lit}`m` hypotheses: the equation is cut as a hypothesis, and the goal rewritten by it along the
motive's variable to the motive at {lit}`t`. -/
def leibD (pb : Term) (t u : Term) (m : ℕ) (Dh Dp : Deriv) : Deriv :=
  nd (.cut (Term.eq t u)) [Dh, nd .conv [congAlong (ruleD (.rwHyp m true)) pb 0, Dp]]

/-- The rewriting of a fold with parameters of a successor to the step at the fold of the
predecessor: the unfolding of the definition, the computation of the fold, β, the second
component of the pair, and β. -/
def natSuccLhsD (ks : ℕ) : Deriv :=
  transD (ruleD .delta) (transD (nd .cong [ruleD (.natSucc ks), reflD])
    (transD (ruleD .beta) (transD (nd .cong [ruleD .sndPair, reflD]) (ruleD .beta))))

/-- The rewriting of a fold with parameters of zero to the start: the unfolding of the definition,
the computation of the fold, β and the first component of the pair. -/
def natZeroLhsD (kz : ℕ) : Deriv :=
  transD (ruleD .delta) (transD (nd .cong [ruleD (.natZero kz), reflD])
    (transD (ruleD .beta) (ruleD .fstPair)))

section Decoding

variable (kz ks ki : ℕ)

/-- One step of the decoding of a proof, at a node of a label, from its children's decodings,
each a function of an environment and the number of hypotheses. -/
def decPfStep (l : Label) (cs : List (Expr × (List (Option ℕ) → ℕ → Option Deriv)))
    (env : List (Option ℕ)) (m : ℕ) : Option Deriv :=
  match l, cs with
    | .app (.var i), [] => match env[i]? with
      | some (some h) => some (ruleD (.hyp h))
      | _ => none
    | .app (.const 18), [_, _] => some (joinD reflD reflD)
    | .app (.const 19), [_, (P, _), (t, _), (u, _), (_, dh), (_, dp)] => do
      let pb ← lamBody (← termOf kz ks ki env P)
      pure (leibD pb (← termOf kz ks ki env t) (← termOf kz ks ki env u) m (← dh env m)
        (← dp env (m + 1)))
    | .app (.const 20), [_, _, _, _] => some (joinD (ruleD .beta) reflD)
    | .app (.const 21), [_, _, _, _] => some (joinD (ruleD .fstPair) reflD)
    | .app (.const 22), [_, _, _, _] => some (joinD (ruleD .sndPair) reflD)
    | .app (.const 23), [_, _, _] => some (joinD (ruleD .pairEta) reflD)
    | .app (.const 24), [_] => some (joinD (ruleD .unitEta) reflD)
    | .app (.const 25), [_, _, _] => some (joinD (natZeroLhsD kz) reflD)
    | .app (.const 26), [_, _, (s, _), _] => do
      let sb ← lamBody (← termOf kz ks ki env s)
      pure (joinD (natSuccLhsD ks) (congAlong (ruleD .delta) sb 0))
    | .app (.const 27), [_, _, _, _, (_, dH)] => do
      pure (nd .funExt [← dH (none :: env) m])
    | .app (.const 28), [_, _, (_, d₁), (_, d₂)] => do
      pure (nd .propExt [← d₁ (some m :: env) (m + 1), ← d₂ (some m :: env) (m + 1)])
    | .app (.const 29), [(P, _), (_, d₀), (_, ds), (n, _)] => do
      let pb ← lamBody (← termOf kz ks ki env P)
      pure (natIndD kz ks pb (← termOf kz ks ki env n) m (← d₀ env (m + 1))
        (← ds (some (m + 1) :: none :: env) (m + 2)))
    | .lam, [(_, d)] => d env m
    | _, _ => none

/-- The decoding of a proof in an environment, under a number of hypotheses. -/
def decPf : Expr → List (Option ℕ) → ℕ → Option Deriv := RoseTree.para (decPfStep kz ks ki)

end Decoding

end Geb.LF.Topos

end
