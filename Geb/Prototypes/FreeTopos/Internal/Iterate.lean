/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Arrows
public import Geb.Prototypes.FreeTopos.Internal.Inversion
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The fold of the natural numbers with parameters

The iteration of a step from a start, both values, as a definition of the language
({lit}`iterDefn`): the function from a natural number and a pair of a start and a step, as a
term and a function, to the step's iterate at the start. Its body is the fold with parameters of
the natural numbers object of a cartesian closed category ({cite}`EscardoSimpson2025`,
Proposition 2.3), the fold into the exponential of the parameters evaluated at the parameter,
the parameter the pair: the fold, at the exponential of the type of the pair into the result
type, whose start is the first projection and whose step applies the pair's second component to
the value of the previous function at the pair, applied to the pair. Neither the start nor the
step of that fold mentions a variable around it, and the parameters enter through the argument.
Its application takes the start and the step as values compiled in the environment of the
application, as the case analysis of a coproduct takes its functions.

## Main definitions

* {lit}`iterDefn` — the fold of the natural numbers with parameters.

## Main statements

* {lit}`iterDefn_compile` — the definition compiles.
* {lit}`compile_iter`, {lit}`compile_iter_inv` — the compilation of an application of the
  definition, and its inversion.

## References

* {cite}`EscardoSimpson2025`, Proposition 2.3, for folds with parameters.

## Tags

internal language, natural numbers object, fold, parameters, definition
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal

open PartialHorn (Tree op)

/-- The type of the pair of a start and a step of the iteration into the object variable: the
product of the variable and its exponential into itself. -/
def iterPairTy : Tree := prod (x 0) (exp (x 0) (x 0))

/-- The fold of the natural numbers with parameters, in one object variable {lit}`C`: from a
natural number {lit}`n` and a pair of a start {lit}`z` of {lit}`C` and a step {lit}`s` from
{lit}`C` to itself, the term parameters, the last first, the iterate {lit}`sⁿ(z)`. Its body
applies to the pair the fold, at the exponential of the pair's type into {lit}`C`, from the first
projection by the function that applies the pair's second component to the previous function's
value at the pair. -/
def iterDefn : Defn where
  arity := 1
  params := [nat, iterPairTy]
  type := x 0
  body := Term.app
    (Term.natRec (Term.lam iterPairTy (Term.fst (Term.var 0)))
      (Term.lam iterPairTy (Term.app (Term.snd (Term.var 0)) (Term.app (Term.var 1) (Term.var 0))))
      (Term.var 0))
    (Term.var 1)

set_option maxHeartbeats 400000 in
-- the reduction computes the fold's parameters from the variables its start and step mention
/-- The fold with parameters compiles, whatever the constants. -/
theorem iterDefn_compile (G : Globals) : (iterDefn.compile G).isSome = true := rfl

variable {G : Globals} {n : ℕ}

/-- The compilation of an application of the fold with parameters at a type, to a natural number
and a pair of a start and a step: the definition's operation after the tuple of the two. -/
theorem compile_iter {ki : ℕ} (hi : G.defs[ki]? = some (.language iterDefn)) {c : Tree}
    (hc : IsTy G n c = true) {m p : Term} {X : Tree} {e : List (Tree × Tree)} {fm fp : Tree}
    (hm : compile G n m X e = some (fm, nat))
    (hp : compile G n p X e = some (fp, prod c (exp c c))) :
    compile G n (Term.defn ki [c] [m, p]) X e =
      some (comp (op (G.base + ki) [c]) (tuple X [fm, fp]), c) := by
  refine compile_defn_iff.mpr ⟨iterDefn, [(fm, nat), (fp, prod c (exp c c))], hi, ?_, rfl,
    by simp [hc], ?_, ?_⟩
  · simp [hm, hp]
  · simp [iterDefn, iterPairTy, subst_op, subst_x, nat, prod, exp]
  · simp [iterDefn, subst_x]

/-- The inversion of the compilation of an application of the fold with parameters at a type: its
arguments compile to a natural number and a pair of a start and a step, and it to the
definition's operation after their tuple, of the type. -/
theorem compile_iter_inv {ki : ℕ} (hi : G.defs[ki]? = some (.language iterDefn)) {c : Tree}
    {m p : Term} {X : Tree} {e : List (Tree × Tree)} {r : Tree × Tree}
    (h : compile G n (Term.defn ki [c] [m, p]) X e = some r) :
    ∃ fm fp, compile G n m X e = some (fm, nat) ∧
      compile G n p X e = some (fp, prod c (exp c c)) ∧ IsTy G n c = true ∧
      r = (comp (op (G.base + ki) [c]) (tuple X [fm, fp]), c) := by
  obtain ⟨d, rs, hd, hrs, -, hθ, htys, rfl⟩ := compile_defn_iff.mp h
  obtain rfl := Definition.language.inj (Option.some.inj (hd.symm.trans hi))
  simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at hrs
  obtain ⟨⟨fm, tm⟩, hcm, _, ⟨⟨fp, tp⟩, hcp, _, rfl, rfl⟩, rfl⟩ := hrs
  simp only [List.map_cons, List.map_nil, iterDefn, iterPairTy, nat, prod, exp, subst_op, subst_x,
    List.getElem?_cons_zero, Option.getD_some, List.cons.injEq, and_true] at htys
  obtain ⟨rfl, rfl⟩ := htys
  refine ⟨fm, fp, hcm, hcp, by simpa using hθ, ?_⟩
  simp [iterDefn, subst_x]

end Geb.FreeTopos.Internal

end
