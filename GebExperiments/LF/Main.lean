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
Each term Canonical returns is translated back to canonical LF and checked by the checker of the
regime, `Geb.LF.Checks` or `Geb.LF.ChecksMod`. The program prints, for each goal and regime,
whether a term was found, the time taken, the term, and the checker's verdict. Its argument is the
timeout in seconds of each search.

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
    "unitEta", "natZero", "natSucc", "funExt", "propExt", "natInd"]

/-- The constants the rewrite rules make redundant: `beta`, `fstPair`, `sndPair`, `natZero` and
`natSucc`. -/
def redundantModRules : List ℕ := [20, 21, 22, 25, 26]

/-- A goal: a name and a closed type to inhabit. -/
structure Goal where
  /-- The goal's name. -/
  name : String
  /-- The type to inhabit, in the empty context. -/
  type : Expr

/-- The addition of `n` to `m`, the fold of `n` from `m` by the successor. -/
def add (m n : Expr) : Expr := natRec nat m (Expr.lam (succ (v 0))) n

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
      (lam nat nat (Expr.lam (app nat nat (lam nat nat (Expr.lam (v 0))) (v 0)))))⟩ ]

/-- The bound on the steps of normalization modulo the rules. -/
def fuel : ℕ := 64

/-- Run one goal in one regime, printing the outcome. -/
def runGoal (timeout : UInt64) (g : Goal) (modulo : Bool) : IO Unit := do
  let rs := if modulo then rules else []
  let usable := fun c ↦ !(modulo && redundantModRules.contains c)
  let typ := problem toposNames sig rs usable [] g.type
  let t₀ ← IO.monoMsNow
  let r ← Canonical.canonical typ g.name timeout 1
  let t₁ ← IO.monoMsNow
  let regime := if modulo then "modulo rules" else "pure LF"
  match r.terms[0]? with
    | none => IO.println s!"{g.name} [{regime}]: not found in {t₁ - t₀} ms"
    | some t =>
      let verdict := match fromTerm toposNames [] t with
        | none => "untranslatable"
        | some e =>
          let ok := if modulo then ChecksMod rules fuel sig [] e g.type else Checks sig [] e g.type
          if ok then "checks" else "DOES NOT CHECK"
      IO.println s!"{g.name} [{regime}]: found in {t₁ - t₀} ms, {verdict}: {
        {t with lets := #[]}}"

/-- Run every goal in both regimes. -/
def main (args : List String) : IO UInt32 := do
  let timeout := (args.head? >>= String.toNat?).getD 10
  for g in goals do
    for modulo in [false, true] do
      runGoal timeout.toUInt64 g modulo
  return 0

end GebExperiments.LF

/-- The program's entry point. -/
def main (args : List String) : IO UInt32 := GebExperiments.LF.main args

end
