/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.GoedelT.MirrorLoad
public import GebTests.Prototypes.GoedelT.MirrorChecker

set_option doc.verso true in
/-!
# The checker of Gödel's T written in Geb decides as the checker in Lean

The checker of Gödel's T written in Geb, {lit}`bootstrap/goedel-t/equations.geb` with the
prelude, the reader and the kernel's checker, loaded by {name}`Geb.Kernel.load`, has as its last
global a function of the type
{name}`GebTests.Prototypes.GoedelT.MirrorLoad.checkCertTy`. At a
certificate, a program's definitions, theorems about the program, its global environment's types,
a context and hypotheses, that function gives the encoding of what {name}`Geb.GoedelT.check`
gives at the same inputs: the equation it concludes, or nothing where it concludes nothing. The
two checkers therefore accept the same certificates with the same conclusions, in both
directions, at every input.

Theorems are encoded by
{name}`GebTests.Prototypes.GoedelT.MirrorEquations.encThm`, equations by
{name}`GebTests.Prototypes.GoedelT.MirrorEquations.encEqn`, optional trees by
{name}`GebTests.Prototypes.GoedelT.MirrorTyping.enc`, and a global environment by the list of
its globals' types. The proof composes the kernel's evaluation of the loading
({lit}`GebTests.Prototypes.GoedelT.MirrorLoad`) with the agreement of the program's Lean mirror
with the Lean checker, proved definition by definition
({name}`GebTests.Prototypes.GoedelT.MirrorChecker.checkCert_eq`).

## Main statements

* {lit}`checker_eq` — the loaded checker written in Geb decides as the checker in Lean.

## Tags

Gödel's T, checker, agreement, soundness, completeness
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.GoedelT.Agreement

open Geb Geb.Kernel Geb.GoedelT GebTests.Prototypes.GoedelT.MirrorTyping
  GebTests.Prototypes.GoedelT.MirrorEquations GebTests.Prototypes.GoedelT.MirrorLoad
  GebTests.Prototypes.GoedelT.MirrorChecker

/-- The checker of Gödel's T written in Geb decides as the checker in Lean: its program loads to
globals whose last is a function of the checker's type that, at encoded inputs, gives the encoding
of the Lean checker's result. -/
theorem checker_eq : ∃ G' : List Glob, load checker = some G' ∧
    ∃ f : Ty.den checkCertTy, G'[178]? = some ⟨checkCertTy, f⟩ ∧
      ∀ (E : Env) (G : List Glob) (c : Tree) (Γ : Ctx) (H : List Eqn),
        f E.defs (E.thms.map encThm) (G.map (·.1)) c Γ (H.map encEqn) =
          enc ((check c E G Γ H).map encEqn) :=
  ⟨_, checker.load_eq, GebMirror.GoedelT.checkCert, checker_checkCert, checkCert_eq⟩

end GebTests.Prototypes.GoedelT.Agreement

end
