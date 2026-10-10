/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebExperiments.LF.Bridge
public import Geb.Prototypes.LF.Topos

/-!
# Canonical on the internal language of a topos

Goals of the fragment of the internal language represented by `Geb.LF.Topos.sig`, each given to
Canonical in two regimes: pure LF, the computation rules derivation rules among the constants; and
modulo the rewrite rules `Geb.LF.Topos.rules`, the derivation rules they make redundant withheld.
Each regime is run with every constant offered and with only those relevant to the goal
(`GebExperiments.LF.relevant`), from the core of the types, terms, formulas and proofs.
Each term Canonical returns is translated back to canonical LF and checked by the checker of the
regime, `Geb.LF.Checks` or `Geb.LF.ChecksMod`, and then decoded to a certificate of the internal
language and checked: a term of pure LF to a derivation (`Geb.LF.Topos.decPf`), checked by the
base checker (`Geb.FreeTopos.Internal.Thm.checks`), and a term found modulo the rules to a
certificate with steps of conversion (`Geb.LF.Topos.decPfMod`), checked by the conversion checker
(`Geb.FreeTopos.Internal.Thm.convChecks`). The decoding applies to a goal whose parameters are
term variables and hypotheses, the language having no object variables; a hypothesis's formula is
weakened past the parameters after it. The program prints, for each goal and regime, whether a
term was found, the time taken, the term, and both checkers' verdicts.
Its first argument is the timeout in seconds of each search, and a second, if given, restricts
the goals to those whose names contain it.

## Tags

logical framework, LF, Canonical, Mitchell–Bénabou language, experiment
-/

@[expose] public section

namespace GebExperiments.LF

open Geb Geb.LF Geb.LF.Topos
open Expr (arrow pi)

/-- The names of the constants of `Geb.LF.Topos.sig`. -/
def toposNames : List String :=
  ["tp", "one", "prod", "exp", "omega", "nat", "tm", "star", "pair", "fst", "snd", "lam", "app",
    "zero", "succ", "natRec", "eq", "pf", "refl", "leib", "beta", "fstPair", "sndPair", "pairEta",
    "unitEta", "natZero", "natSucc", "funExt", "propExt", "natInd", "list", "nilAt", "cons",
    "listRec", "listNil", "listCons", "listInd", "rose", "node", "roseRec", "roseNode", "roseInd",
    "lrose", "lnode", "lroseRec", "lroseNode", "lroseInd", "cong", "coprod", "initial", "inl",
    "inr", "case", "caseInl", "caseInr", "coprodInd", "exfalso"]

/-- The constants the rewrite rules make redundant: `beta`, `fstPair`, `sndPair`, `natZero`,
`natSucc`, `listNil`, `listCons`, `roseNode`, `lroseNode`, `caseInl` and `caseInr`. -/
def redundantModRules : List ℕ := [20, 21, 22, 25, 26, 34, 35, 40, 45, 53, 54]

/-- The core of the constants relevant to every goal: the kind of types, the families of terms
and of proofs, equality, the subobject classifier and the terminal object with its element. -/
def coreConsts : List ℕ := [0, 1, 4, 6, 7, 16, 17]

/-- A goal: a name and a closed type to inhabit. -/
structure Goal where
  /-- The goal's name. -/
  name : String
  /-- The type to inhabit, in the empty context. -/
  type : Expr

/-- The addition of `n` to `m`, the fold of `n` from `m` by the successor. -/
def add (m n : Expr) : Expr := natRec nat m (Expr.lam (succ (v 0))) n

/-- The construction of a list of natural numbers as a step of a fold:
`λ h r. cons nat (pair h r)`. -/
def consLam : Expr := Expr.lam (Expr.lam (cons nat (pair nat (list nat) (v 1) (v 0))))

/-- The concatenation of the lists of natural numbers `xs` and `ys`, the right fold of `xs` by
construction from `ys`. -/
def append (xs ys : Expr) : Expr := listRec nat (list nat) ys consLam xs

/-- The type of the pairs of an element and a list of natural numbers. -/
def natCell : Expr := prod nat (list nat)

/-- The goals. -/
def goals : List Goal :=
  [ ⟨"symmetry", pi tp (pi (tm (v 0)) (pi (tm (v 1))
      (arrow (pf (eq (v 2) (v 1) (v 0))) (pf (eq (v 2) (v 0) (v 1))))))⟩,
    ⟨"transitivity", pi tp (pi (tm (v 0)) (pi (tm (v 1)) (pi (tm (v 2))
      (arrow (pf (eq (v 3) (v 2) (v 1)))
        (arrow (pf (eq (v 3) (v 1) (v 0))) (pf (eq (v 3) (v 2) (v 0))))))))⟩,
    ⟨"congruence of succ", pi (tm nat) (pi (tm nat)
      (arrow (pf (eq nat (v 1) (v 0))) (pf (eq nat (succ (v 1)) (succ (v 0))))))⟩,
    ⟨"fold at one", pi tp (pi (tm (v 0)) (pi (arrow (tm (v 1)) (tm (v 1)))
      (pf (eq (v 2) (natRec (v 2) (v 1) (Expr.lam (Expr.var 1 [v 0])) (succ zero))
        (Expr.var 0 [v 1])))))⟩,
    ⟨"n + 0 = n", pi (tm nat) (pf (eq nat (add (v 0) zero) (v 0)))⟩,
    ⟨"m + succ n = succ (m + n)", pi (tm nat) (pi (tm nat)
      (pf (eq nat (add (v 1) (succ (v 0))) (succ (add (v 1) (v 0))))))⟩,
    ⟨"0 + n = n", pi (tm nat) (pf (eq nat (add zero (v 0)) (v 0)))⟩,
    ⟨"succ m + n = succ (m + n)", pi (tm nat) (pi (tm nat)
      (pf (eq nat (add (succ (v 1)) (v 0)) (succ (add (v 1) (v 0))))))⟩,
    ⟨"η of the identity's application", pf (eq (exp nat nat)
      (lam nat nat (Expr.lam (v 0)))
      (lam nat nat (Expr.lam (app nat nat (lam nat nat (Expr.lam (v 0))) (v 0)))))⟩,
    ⟨"foldr cons nil xs = xs", pi (tm (list nat))
      (pf (eq (list nat) (listRec nat (list nat) (nil nat) consLam (v 0)) (v 0)))⟩,
    -- the uniqueness of the right fold, its hypothesis at a construction an equation of functions
    ⟨"uniqueness of the right fold", pi (tm nat) (pi (tm (exp nat (exp nat nat)))
      (pi (tm (exp (list nat) nat))
        (arrow (pf (eq nat (app (list nat) nat (v 0) (nil nat)) (v 2)))
          (arrow (pf (eq (exp natCell nat)
              (lam natCell nat (Expr.lam (app (list nat) nat (v 1) (cons nat (v 0)))))
              (lam natCell nat (Expr.lam (app nat nat
                (app nat (exp nat nat) (v 2) (fst nat (list nat) (v 0)))
                (app (list nat) nat (v 1) (snd nat (list nat) (v 0))))))))
            (pi (tm (list nat)) (pf (eq nat (app (list nat) nat (v 1) (v 0))
              (listRec nat nat (v 3)
                (Expr.lam (Expr.lam (app nat nat (app nat (exp nat nat) (v 4) (v 1)) (v 0))))
                (v 0)))))))))⟩,
    ⟨"associativity of appending", pi (tm (list nat)) (pi (tm (list nat)) (pi (tm (list nat))
      (pf (eq (list nat) (append (append (v 2) (v 1)) (v 0))
        (append (v 2) (append (v 1) (v 0)))))))⟩ ]

/-- The primitive arrows of the internal language that the signature's constants stand for. -/
def toposGlobals : FreeTopos.Internal.Globals :=
  ⟨[FreeTopos.Internal.zeroPrim, FreeTopos.Internal.succPrim, FreeTopos.Internal.nilPrim,
    FreeTopos.Internal.consPrim, FreeTopos.Internal.nodePrim, FreeTopos.Internal.lnodePrim,
    FreeTopos.Internal.inlPrim, FreeTopos.Internal.inrPrim, FreeTopos.Internal.casePrim], [], 0⟩

/-- The indices of the primitive arrows of `toposGlobals`. -/
def toposIdx : PrimIdx := ⟨0, 1, 2, 3, 4, 5, 6, 7, 8⟩

/-- One step of the parameters of a type and its body, the parameters the outermost first. -/
def telescopeStep (l : Label) (cs : List (Expr × (List Expr × Expr))) : List Expr × Expr :=
  match l, cs with
    | .pi, [(a, _), (_, (as, body))] => (a :: as, body)
    | l, cs => ([], RoseTree.node l (cs.map (·.1)))

/-- The parameters of a type, the outermost first, and its body. -/
def telescope : Expr → List Expr × Expr := RoseTree.para telescopeStep

/-- The body of an LF abstraction. -/
def lfBody (e : Expr) : Option Expr := match e.label, e.children with
  | .lam, [b] => some b
  | _, _ => none

/-- The theorem of the internal language that a goal states, with the environment of its
parameters: a parameter of `tm A` is a variable of the type `A` decodes to, and one of
`pf F` a hypothesis, `F` decoded after its weakening past the parameters after it. A goal
with a parameter of another type, or whose body is not a family of proofs, states none. -/
def internalThm (goal : Expr) : Option (List (Option ℕ) × FreeTopos.Internal.Thm) := do
  let (ps, body) := telescope goal
  let F ← match body.label, body.children with
    | .app (.const 17), [F] => some F
    | _, _ => none
  let n := ps.length
  let (env, Γ, Φ) ← ps.zipIdx.foldlM (init := (([] : List (Option ℕ)), ([] : List _),
      ([] : List (Expr × ℕ)))) fun (env, Γ, Φ) (p, j) ↦
    match p.label, p.children with
      | .app (.const 6), [A] => do pure (none :: env, (← decTy A) :: Γ, Φ)
      | .app (.const 17), [P] => some (some Φ.length :: env, Γ, (P, n - 1 - j) :: Φ)
      | _, _ => none
  let hyps ← Φ.reverse.mapM fun (P, i) ↦ termOf toposIdx env (Expr.rename P (· + (i + 1)))
  pure (env, ⟨0, Γ, hyps, ← termOf toposIdx env F⟩)

/-- The verdict of the internal language's checkers on a term found for a goal: the term's
abstractions over the goal's parameters removed, its body decoded in their environment and the
certificate checked against the goal's theorem, by the base checker for a term of pure LF and by
the conversion checker for one found modulo the rules. -/
def internalVerdict (modulo : Bool) (goal term : Expr) : String :=
  match internalThm goal with
    | none => "outside the internal fragment"
    | some (env, thm) =>
      let body := (List.range env.length).foldlM (fun e _ ↦ lfBody e) term
      let verdict := if modulo then
          (body >>= fun b ↦ decPfMod toposIdx b env thm.hyps.length).map
            (thm.convChecks toposGlobals #[])
        else (body >>= fun b ↦ decPf toposIdx b env thm.hyps.length).map
            (thm.checks toposGlobals #[])
      match verdict with
        | none => "undecodable"
        | some true => "internal checks"
        | some false => "internal DOES NOT CHECK"

/-- The bound on the steps of normalization modulo the rules. -/
def fuel : ℕ := 64

/-- Run one goal in one regime, printing the outcome. -/
def runGoal (timeout : UInt64) (g : Goal) (modulo select : Bool) : IO Unit := do
  let rs := if modulo then rules else []
  let rel := relevant sig 0 coreConsts g.type
  let usable := fun c ↦ !(modulo && redundantModRules.contains c) && (!select || rel c)
  let decl := problem g.name toposNames sig rs usable [] g.type
  let t₀ ← IO.monoMsNow
  let r ← Canonical.canonical decl timeout 1
  let t₁ ← IO.monoMsNow
  let regime := (if modulo then "modulo rules" else "pure LF") ++
    (if select then ", relevant constants" else "")
  match r.terms[0]? with
    | none => IO.println s!"{g.name} [{regime}]: not found in {t₁ - t₀} ms"
    | some t =>
      let verdict := match fromTerm toposNames [] t with
        | none => "untranslatable"
        | some e =>
          let ok := if modulo then ChecksMod rules fuel sig [] e g.type else Checks sig [] e g.type
          (if ok then "checks" else "DOES NOT CHECK") ++ ", " ++ internalVerdict modulo g.type e
      IO.println s!"{g.name} [{regime}]: found in {t₁ - t₀} ms, {verdict}: {
        {t with lets := #[]}}"
  (← IO.getStdout).flush

/-- Run every goal in both regimes. -/
def main (args : List String) : IO UInt32 := do
  if toposNames.length != sig.length then
    IO.eprintln s!"{toposNames.length} names for {sig.length} constants"
    return 1
  let timeout := (args.head? >>= String.toNat?).getD 10
  let chosen := match args with
    | [_, part] => goals.filter fun (g : Goal) ↦ (g.name.splitOn part).length > 1
    | _ => goals
  for g in chosen do
    for modulo in [false, true] do
      for select in [false, true] do
        runGoal timeout.toUInt64 g modulo select
  return 0

end GebExperiments.LF

/-- The program's entry point. -/
def main (args : List String) : IO UInt32 := GebExperiments.LF.main args

end
