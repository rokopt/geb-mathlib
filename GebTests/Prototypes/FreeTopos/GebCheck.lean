/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel
public import GebTests.Prototypes.FreeTopos
public import GebTests.Prototypes.FreeTopos.Agreement.Encode
public meta import GebTests.Prototypes.FreeTopos.Agreement.Encode -- shake: keep
public meta import GebTests.Prototypes.FreeTopos -- shake: keep
public meta import GebTests.Prototypes.Stage0 -- shake: keep

set_option doc.verso true in
/-!
# The metalogic's checker written in Geb, compared with Lean's

The metalogic's checker written in the datatype language, {lit}`bootstrap/free-topos/`, is read
by the stage-0 compiler's front end and loaded by the kernel, and its definitions are compared
with the Lean definitions they transcribe: the sorts, scope and substitution of partial Horn
terms, the checker of certificates at the certificates of
{lit}`GebTests.Prototypes.FreeTopos` and malformed variants of each, and the extension of the
theory by a definition. Inputs are encoded as the Geb program represents them, by the encodings
of {lit}`GebTests.Prototypes.FreeTopos.Agreement.Encode`.

## Main definitions

* {lit}`loaded` — the program's definitions, loaded, by name.
* {lit}`fn` — a definition of the program at a type.

## Tags

partial Horn logic, proof certificate, differential testing, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.GebCheck

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Sorts GebTests.Prototypes.FreeTopos
  GebTests.Prototypes.FreeTopos.Agreement.Encode
open scoped FinEnum

/-- The prelude. -/
def preludeGeb : String := include_str "../../../bootstrap/prelude.geb"

/-- The lists and optional values at any element type. -/
def seqGeb : String := include_str "../../../bootstrap/seq.geb"

/-- The base of the metalogic's checker. -/
def baseGeb : String := include_str "../../../bootstrap/free-topos/base.geb"

/-- Partial Horn logic. -/
def partialHornGeb : String := include_str "../../../bootstrap/free-topos/partial-horn.geb"

/-- The theory of an elementary topos with data objects. -/
def theoryGeb : String := include_str "../../../bootstrap/free-topos/theory.geb"

/-- The inference of typings. -/
def inferGeb : String := include_str "../../../bootstrap/free-topos/infer.geb"

/-- The program: the prelude, the lists and optional values and the metalogic's checker, each
followed by a newline. -/
def program : String :=
  String.join ([preludeGeb, seqGeb, baseGeb, partialHornGeb, theoryGeb, inferGeb].map (· ++ "\n"))

/-- A program's definitions, read by the front end whose text is {lit}`fe` and loaded, by name. -/
def loaded (fe text : List Char) : Option (List (List Char × Kernel.Glob)) := do
  let r ← Kernel.runMain fe (Kernel.nameTree text)
  let b ← if r.label == 1 then r.children.head? else none
  let ds ← Kernel.unbundle b
  let G ← Kernel.load (ds.map Prod.snd)
  some ((ds.map Prod.fst).zip G)

/-- A loaded program's definition of a name, where it has the type {lit}`A`. -/
def fn (P : List (List Char × Kernel.Glob)) (name : List Char) (A : Tree) :
    Option (Kernel.Ty.den A) := do
  let (_, g) ← P.find? (·.1 == name)
  if h : g.1 = A then some (cast (congrArg Kernel.Ty.den h) g.2) else none

/-- The type of trees. -/
abbrev tyT : Tree := Kernel.tT

/-- The type of lists of trees. -/
abbrev tyTs : Tree := Kernel.tList Kernel.tT

/-- The function type. -/
abbrev arrow (A B : Tree) : Tree := Kernel.tArrow A B

/-- The terms the comparisons of sorts, scope and substitution run on: the sides of every
equation of every axiom, and a node of label zero that is not a variable. -/
def terms : List Tree :=
  notVar :: axioms.flatMap fun a ↦ (a.concl :: a.hyps).flatMap fun q ↦ [q.lhs, q.rhs]

/-- The sorts, the scope and the substitution of the terms, in the context of every axiom, as the
program computes them and as Lean does. -/
def sortsAgree (P : List (List Char × Kernel.Glob)) : Option Bool := do
  let so : List Tree → List Tree → Tree → Tree ←
    fn P "PartialHorn.sortOf".toList (arrow tyTs (arrow tyTs (arrow tyT tyT)))
  let sc : Tree → Tree → Tree ← fn P "PartialHorn.scoped".toList (arrow tyT (arrow tyT tyT))
  let su : List Tree → Tree → Tree ← fn P "PartialHorn.phSubst".toList (arrow tyTs (arrow tyT tyT))
  pure <| axioms.all fun a ↦ terms.all fun t ↦
    so (sig.map encOpSig) (a.ctx.map Kernel.leaf) t ==
        encOpt ((sortOf sig a.ctx t).map Kernel.leaf) &&
      sc (Kernel.leaf a.ctx.length) t == Kernel.ofBool (Scoped a.ctx.length t) &&
      su [x 1, op 4 []] t == subst [x 1, op 4 []] t

/-- The certificates the checkers are compared on, each with its theory's extension, the
theorems it may cite, and the context and hypotheses it checks in: those of
{lit}`GebTests.Prototypes.FreeTopos`, and one of each rule not among them. -/
def certs : List (List Defn × List Seq × Tree × List ℕ × List Eqn) :=
  [([], [], Cert.refl 0, [arr], []),
   ([], [], RoseTree.node Rule.refl [RoseTree.node 0 [Cert.leaf 0]], [arr], []),
   ([], [], Cert.ax 0 [x 0] [Cert.refl 0] [], [arr], []),
   ([], [], compDfd, [arr, arr], [composable]),
   ([], [], Cert.ax 5 [x 0, x 1] [Cert.refl 0, Cert.refl 1] [compDfd], [arr, arr], [composable]),
   ([], [], Cert.ax 10 [comp (x 0) (x 1)] [compDfd] [], [arr, arr], [composable]),
   ([], [], leftId zeroN zDfd zCod, [], []),
   ([], [], natIdRec, [], []),
   ([], [], Cert.ax (idx beforeClassifier 7) [x 0] [Cert.refl 0] [Cert.hyp 0], [arr],
     [dfd (chi (x 0))]),
   ([swapDefn], [], Cert.ax axioms.length [x 0, x 1] [Cert.refl 0, Cert.refl 1] [Cert.hyp 0],
     [obj, obj], [dfd swapDefn.body]),
   ([], [], Cert.ax 2 [x 0] [Cert.refl 0] [], [arr], []),
   ([], [], Cert.hyp 3, [arr], []),
   ([], [], Cert.trans (Cert.refl 0) (Cert.refl 1), [arr, arr], []),
   ([], [], Cert.strict 0 (Cert.refl 0), [arr], []),
   ([], [], compDfd, [arr, arr], [⟨dom (x 0), cod (x 1)⟩]),
   -- congruence, cut, and an instance of a theorem
   ([], [], Cert.cong compDfd [Cert.refl 0, Cert.refl 1], [arr, arr], [composable]),
   ([], [], Cert.cut compDfd (Cert.hyp 0), [arr, arr], [composable]),
   ([], categoryAxioms.take 1, Cert.thm 0 [x 0] [Cert.refl 0] [], [arr], []),
   ([], categoryAxioms.take 1, Cert.thm 1 [x 0] [Cert.refl 0] [], [arr], [])]

/-- Malformed variants of a certificate: its root relabelled with every rule's label and one
beyond, and with its last child removed. -/
def mutants (c : Tree) : List Tree :=
  ((List.range 10).map fun l ↦ RoseTree.node l c.children) ++
    [RoseTree.node c.label c.children.dropLast]

/-- The checker at every certificate and its malformed variants, as the program computes it and as
Lean does. -/
def checkerAgrees (P : List (List Char × Kernel.Glob)) : Option Bool := do
  let pc : Tree → List Tree → Tree → List Tree → List Tree → Tree ←
    fn P "PartialHorn.pcheck".toList
      (arrow tyT (arrow tyTs (arrow tyT (arrow tyTs (arrow tyTs tyT)))))
  pure <| certs.all fun (ds, E, c, Γ, H) ↦ (c :: mutants c).all fun c ↦
    let T := theory.extendAll ds
    pc (encTheory T) (E.map encSeq) c (Γ.map Kernel.leaf) (H.map encEqn) ==
      encOpt ((check T E.toArray c Γ H).map encEqn)

/-- The extension of the theory by one definition and by two, as the program computes it and as
Lean does. -/
def extensionAgrees (P : List (List Char × Kernel.Glob)) : Option Bool := do
  let te : Tree → List Tree → Tree ←
    fn P "PartialHorn.thyExtendAll".toList (arrow tyT (arrow tyTs tyT))
  pure <| [[swapDefn], [swapDefn, swapDefn]].all fun ds ↦
    te (encTheory theory) (ds.map encDefn) == encTheory (theory.extendAll ds)

/-- The theory of an elementary topos with data objects, its signature and its axioms, as the
program encodes it and as Lean does. -/
def theoryAgrees (P : List (List Char × Kernel.Glob)) : Option Bool := do
  let th : Tree ← fn P "Theory.toposTheory".toList tyT
  pure (th == encTheory theory)

/-- The rule tables, and the environments of the theory and of its extension by a definition, as
the program computes them and as Lean does. -/
def envAgrees (P : List (List Char × Kernel.Glob)) : Option Bool := do
  let eo : List Tree → Tree ← fn P "Infer.envOfDefs".toList (arrow tyTs tyT)
  pure <| [[], [swapDefn]].all fun ds ↦ eo (ds.map encDefn) == encExtEnv (ExtEnv.ofDefs ds)

/-- The inference of the typing of the sides of every axiom's equations, in its context and under
its hypotheses, as the program computes it and as Lean does. -/
def inferenceAgrees (P : List (List Char × Kernel.Glob)) : Option Bool := do
  let eo : List Tree → Tree ← fn P "Infer.envOfDefs".toList (arrow tyTs tyT)
  let inf : Tree → List Tree → List Tree → Tree → (List Tree → Tree → Tree) × (Tree → Tree) ←
    fn P "Infer.infers".toList (arrow tyT (arrow tyTs (arrow tyTs (arrow tyT
      (Kernel.tProd (arrow tyTs (arrow tyT tyT)) (arrow tyT tyT))))))
  let E := ExtEnv.ofDefs []
  let e := eo []
  pure <| axioms.all fun a ↦ ((a.concl :: a.hyps).flatMap fun q ↦ [q.lhs, q.rhs]).all fun t ↦
    (inf e (a.ctx.map Kernel.leaf) (a.hyps.map encEqn) (Kernel.leaf inferFuel)).2 t ==
      encOpt (((infers E a.ctx a.hyps inferFuel).2 t).map encAnn)

#eval show IO Unit from do
  let some P := loaded Geb.Kernel.Stage0Tests.bundler.toList program.toList
    | throw (IO.userError "the program does not load")
  let comparisons : List (String × (List (List Char × Kernel.Glob) → Option Bool)) :=
    [("sortsAgree", sortsAgree), ("checkerAgrees", checkerAgrees),
     ("extensionAgrees", extensionAgrees), ("theoryAgrees", theoryAgrees),
     ("envAgrees", envAgrees), ("inferenceAgrees", inferenceAgrees)]
  for (name, agrees) in comparisons do
    unless (agrees P).getD false do
      throw (IO.userError s!"{name}: the program and Lean disagree")

end GebTests.Prototypes.FreeTopos.GebCheck

end
