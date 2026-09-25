/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.Metalogic -- shake: keep
public meta import GebTests.Prototypes.Metalogic -- shake: keep

set_option doc.verso true in
/-!
# Proofs about Geb programs

Theorems about the prelude's lists, {lit}`bootstrap/proofs/prelude.geb`, proved by the derived
rules of {lit}`bootstrap/metalogic/prove.geb` and checked by the metalogic's checker written in
Geb: the prover, compiled by the stage-0 compiler, checks each theorem's certificate, and each
certificate is checked again by {name}`Geb.Metalogic.check`, citing the theorems before it, in
the global environment the program's definitions load. A false equation, and a true one whose
tactic does not prove it, are rejected.

## Main definitions

* {lit}`prover` — the program of the prover.
* {lit}`results`, {lit}`accepted` — a file's results, and whether the Geb checker accepts one.
* {lit}`recheck` — whether the Lean checker accepts every certificate of a file's results.

## Tags

bootstrap, metalogic, proof certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Metalogic.ProofTests

open Geb.Kernel

/-- The proof construction written in Geb. -/
def proveGeb : String := include_str "../../bootstrap/metalogic/prove.geb"

/-- The theorems about the prelude. -/
def preludeProofs : String := include_str "../../bootstrap/proofs/prelude.geb"

/-- The program of the prover: the prelude, the reader, the kernel's checker, the metalogic's
checker and the proof construction, applying the proof construction to a file of program forms
and theorems. -/
def prover : String :=
  Kernel.Stage0Tests.prelude ++ "\n" ++ Kernel.Stage0Tests.reader ++ "\n" ++
    Kernel.Stage0Tests.check ++ "\n" ++ Tests.equationsGeb ++
    "\n" ++ proveGeb ++ "\n(def main (lam ((file T)) (proveFile 256 file)))"

/-- An equation from its representation in Geb. -/
def eqnOf (t : Tree) : Eqn :=
  ⟨t.children.getD 0 (leaf 0), t.children.getD 1 (leaf 0), t.children.getD 2 (leaf 0)⟩

/-- A theorem from its representation in Geb. -/
def thmOf (t : Tree) : Thm :=
  ⟨(t.children.headD (leaf 0)).children, eqnOf (t.children.getD 1 (leaf 0))⟩

/-- The results of checking a file with a compiled prover: the program's definitions, and for
each theorem the node over its name, the theorem, the certificate and whether the Geb checker
accepts it. -/
def results (f : Tree → Option Tree) (fileText : List Char) : Option (List Tree × List Tree) := do
  let r ← f (nameTree fileText)
  let out ← r.children.head?
  let b ← out.children.head?
  some ((← b.children.head?).children, (← out.children[1]?).children)

/-- Whether the Geb checker accepts a result. -/
def accepted (x : Tree) : Bool := (x.children.getD 3 (leaf 0)).label == 1

/-- Whether the Lean checker accepts every certificate of a file's results, each checked with the
theorems before it, in the global environment the program's definitions load. -/
def recheck (D : List Tree) (rs : List Tree) : Bool :=
  let G := (load D).getD []
  (rs.foldl (fun (acc : Bool × List Thm) x ↦
    let th := thmOf (x.children.getD 1 (leaf 0))
    (acc.1 && check (x.children.getD 2 (leaf 0)) ⟨D, acc.2⟩ G th.ctx [] == some th.eqn,
      acc.2 ++ [th])) (true, [])).1

/-- Theorems the prover does not accept: a false equation, and a true one whose tactic, without
induction, does not prove it. -/
def rejected : String :=
  "(theorem wrong ((xs Ts)) (append xs xs) xs (simp (unfold append)))\n" ++
  "(theorem unproved ((xs Ts)) (append xs (nil T)) xs (simp (unfold append)))"

-- every theorem about the prelude checks, in Geb and again in Lean, and the prover rejects the
-- false equation and the unproved one
#guard (Tests.gebCheck? Kernel.Stage0Tests.compiler.toList prover.toList).any fun f ↦
  ((results f (Kernel.Stage0Tests.prelude ++ "\n" ++ preludeProofs).toList).any fun (D, rs) ↦
    !rs.isEmpty && rs.all accepted && recheck D rs) &&
  (results f (Kernel.Stage0Tests.prelude ++ "\n" ++ rejected).toList).any fun (_, rs) ↦
    rs.length == 2 && !rs.any accepted

end Geb.Metalogic.ProofTests

end
