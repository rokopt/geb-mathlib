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

Theorems about the prelude's lists, {lit}`bootstrap/proofs/prelude.geb`, about the labels, the
natural numbers object inside the trees, {lit}`bootstrap/proofs/nat.geb`, and about the kernel's
type checker written in Geb, {lit}`bootstrap/proofs/check.geb`, proved by the derived rules of
{lit}`bootstrap/metalogic/prove.geb` and checked by the metalogic's checker written in Geb. The
prover's program is read and expanded by the stage-0 compiler and loaded by the seed, without an
image, whose serializer's recursion is as deep as the image is long; it checks each theorem's
certificate, and each certificate is checked again by {name}`Geb.Metalogic.check`, citing the
theorems before it, in the global environment the program's definitions load. A false
equation, and a true one whose tactic does not prove it, are rejected.

## Main definitions

* {lit}`prover`, {lit}`bundler`, {lit}`proverFn?` — the program of the prover, the stage-0
  compiler's front end, and the prover bundled by it and loaded by the seed.
* {lit}`results`, {lit}`accepted` — a file's results, and whether the Geb checker accepts one.
* {lit}`recheck`, {lit}`allCheck` — whether the Lean checker accepts every certificate of a
  file's results, and whether every theorem of a file checks in both.

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

/-- The theorems about the labels, the natural numbers object inside the trees. -/
def natProofs : String := include_str "../../bootstrap/proofs/nat.geb"

/-- The theorems about the kernel's type checker. -/
def checkProofs : String := include_str "../../bootstrap/proofs/check.geb"

/-- The program of the prover: the prelude, the reader, the kernel's checker, the metalogic's
checker and the proof construction, applying the proof construction to a file of program forms
and theorems. -/
def prover : String :=
  Kernel.Stage0Tests.prelude ++ "\n" ++ Kernel.Stage0Tests.reader ++ "\n" ++
    Kernel.Stage0Tests.check ++ "\n" ++ Tests.equationsGeb ++
    "\n" ++ proveGeb ++ "\n(def main (lam ((file T)) (proveFile 256 file)))"

/-- The stage-0 compiler with an entry point giving a program's bundle: its text read and its
Surface 1 forms expanded, without the image written. -/
def bundler : String :=
  Kernel.Stage0Tests.compiler ++ "(def bundleMain (lam ((file T)) (let sx T (readSExps " ++
    "(children file)) (if (isSome sx) (let kx T (expandProgram (children (get sx))) " ++
    "(if (isSome kx) (readProgram (children (get kx))) none)) none))))"

/-- The prover, its program bundled by the stage-0 compiler's reader and expansion and loaded by
the seed, which checks each definition's type, as a function on trees. -/
def proverFn? (bundlerText proverText : List Char) : Option (Tree → Option Tree) := do
  let r ← runMain bundlerText (nameTree proverText)
  let b ← if r.label == 1 then r.children.head? else none
  let G ← load ((← unbundle b).map Prod.snd)
  let main ← G.getLast?
  some main.apply

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

/-- Whether every theorem of a file checks, in Geb and again in Lean. -/
def allCheck (f : Tree → Option Tree) (fileText : List Char) : Bool :=
  (results f fileText).any fun (D, rs) ↦ !rs.isEmpty && rs.all accepted && recheck D rs

-- every theorem about the prelude, the labels and the kernel's type checker checks, in Geb and
-- again in Lean, and the prover rejects the false equation and the unproved one
#guard (proverFn? bundler.toList prover.toList).any fun f ↦
  allCheck f (Kernel.Stage0Tests.prelude ++ "\n" ++ preludeProofs).toList &&
  allCheck f (Kernel.Stage0Tests.prelude ++ "\n" ++ natProofs).toList &&
  allCheck f (Kernel.Stage0Tests.prelude ++ "\n" ++ Kernel.Stage0Tests.reader ++ "\n" ++
    Kernel.Stage0Tests.check ++ "\n" ++ checkProofs).toList &&
  (results f (Kernel.Stage0Tests.prelude ++ "\n" ++ rejected).toList).any fun (_, rs) ↦
    rs.length == 2 && !rs.any accepted

end Geb.Metalogic.ProofTests

end
