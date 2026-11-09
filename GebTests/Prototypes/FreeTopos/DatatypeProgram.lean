/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.DatatypeCata
public meta import GebTests.Prototypes.FreeTopos.DatatypeCata -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The soundness of the datatype language at a whole program

The statement of the soundness of a whole program of the datatype language: where the forms module
elaboration gives the expansion expand, check with the program's markers first, have the recognizers
they refer to written, read and check in the kernel, each definition the typing gives a type
denotes a value related at that type, and the recognizer of each datatype among the definitions
decides membership in it. The relation's context is the program's: the terms the reader reads and
the markers of all its datatypes, with which the typing checks every form.

The development proceeds by the typing's runs over the forms: a run over a concatenation is the
run over its second part from where the first leaves off; the run over the markers, which the
typing checks first, appends them to the environment's; and a run from a rejection leaves it.

## Main definitions

* {lit}`programφ` — the soundness at a program's forms.
* {lit}`programCertificates` — the typing's runs, stored as the certificate
  {lit}`datatype-program`.

## References

* {cite}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, datatypes, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Datatypes

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Translation Geb.FreeTopos.Tactics
open GebTests.Prototypes.FreeTopos.Weakening
open scoped FinEnum

open Internal (Term)
open GebTests.Prototypes.FreeTopos.Normalization

/-- The names of the program's definitions {lit}`programφ` applies. -/
def programNames : List String :=
  ["Datatype.expandTyped", "Datatype.markersFirst", "Datatype.kernelForms", "Typing.checkAll",
    "Typing.env0", "Typing/OName.nothing", "Typing.envMs", "Recognize.insertRecognizers",
    "Reader.readProgram", "Check.checkProgram", "Reader.named", "Reader.kwDefnum",
    "Reader.nameOf", "implName", "Prelude.and", "Prelude.nth", "Prelude.get", "Prelude.isSome"]

/-- The soundness of the datatype language at a whole program, the forms of index 0 that module
elaboration gives the expansion: if no numeral abbreviation among the forms takes a name of the
implementation's, the forms expand to typed forms, the typing of those forms with their markers
first rejects none, the recognizers the erased forms refer to can be written, the reader reads the
forms they give, and the kernel's typing gives each term read a type, then the definitions with the
markers of the typing environment the typed forms leave are related to that environment's
definitions by the reader's names, and its recognizers decide membership. -/
def programφ (P : Prog) (T : Defs3) : Option Term := do
  let o := P.o
  let childT ← primT Kernel.Prim.child
  let arityT ← primT Kernel.Prim.arity
  let eqT ← primT Kernel.Prim.eq
  let isSomeT (t : Term) : Term := truth o (pc P "Prelude.isSome" [t])
  let get (t : Term) : Term := pc P "Prelude.get" [t]
  let kids (t : Term) : Term := call D.children [] [t]
  let ch (t : Term) (i : ℕ) : Term := apps childT [t, leafT (numeral i)]
  -- the forms v0, and inside the quantifier over positions the position v0 and the forms v1
  let f := get (pc P "Prelude.nth" [v 1, v 0])
  let implNum : Term := Internal.Logic.all o treeTy (Term.lam treeTy (Internal.Logic.imp o
    (isSomeT (pc P "Prelude.nth" [v 1, v 0]))
    (Internal.Logic.imp o (truth o (pc P "Prelude.and" [pc P "Reader.named"
        [ch f 0, pc P "Reader.kwDefnum" []], pc P "Prelude.and" [apps eqT [apps arityT [f],
          leafT (numeral 3)], pc P "implName" [pc P "Reader.nameOf" [ch f 1]]]]))
      (Internal.Logic.ff o))))
  let x := pc P "Datatype.expandTyped" [v 0]
  let ts := Term.snd x
  let nothing := pc P "Typing/OName.nothing" []
  let run := pc P "Typing.checkAll" [Term.pair (pc P "Typing.env0" []) nothing,
    pc P "Datatype.markersFirst" [ts]]
  let E := Term.fst run
  let r := pc P "Recognize.insertRecognizers" [pc P "Datatype.kernelForms" [ts]]
  let b := pc P "Reader.readProgram" [kids (get r)]
  let terms := kids (ch (get b) 0)
  let names := kids (ch (get b) 1)
  let R := Term.pair terms (pc P "Typing.envMs" [E])
  let hs : List Term := [implNum, truth o (Term.fst x), Term.eq (Term.snd run) nothing,
    isSomeT r, isSomeT b, isSomeT (pc P "Check.checkProgram" [terms])]
  pure (Internal.Logic.all o (list treeTy) (Term.lam (list treeTy)
    (hs.foldr (Internal.Logic.imp o)
      (Internal.Logic.conj o (T.globT R E names) (T.recsT R E names)))))

/-- The typing's run of a program's forms over the concatenation of two lists is its run over the
second from the state its run over the first leaves: by induction on the first list, at a
construction the induction hypothesis at the second list and at the state the run over the head
alone leaves, the step of the run. -/
def checkAllAppend (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("checkAllAppend", fun ix E ↦ do
    let P := { P with folded := P.folded ++ ["Typing.checkStep"] }
    let K : Kit := ⟨P, S, E, ix, []⟩
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    let CS := prod T.envTy treeTy
    let app (xs ys : Term) : Term := pc P "Datatype/Txs.append" [xs, ys]
    let run (s xs : Term) : Term := pc P "Typing.checkAll" [s, xs]
    -- under the quantifiers: the state v0, the second list v1, the first v2
    let φ := Internal.Logic.all o Ls (Term.lam Ls (Internal.Logic.all o CS (Term.lam CS
      (Term.eq (run (v 0) (app (v 2) (v 1))) (run (run (v 0) (v 2)) (v 1))))))
    let d₀ ← dAllI L (dAllI L K.byNorm) [] []
      (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
    -- a construction, its tail v0 and head v1, under the quantifiers the state v0, the second
    -- list v1, the tail v2 and the head v3: the induction hypothesis, the first hypothesis, at the
    -- second list and at the state the head's step leaves
    let cons : Deducer := dAllI L <| dAllI L <| dAllE L K.G K.E 0 (v 1) fun Γ Φ ψ ↦
      dAllE L K.G K.E (Φ.length - 1) (run (v 0) (consT treeTy (v 3) (nilT treeTy)))
        (normLastK K K.byNorm) Γ Φ ψ
    let some d₁ := cons [Ls, treeTy] [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
      | dbgTrace "checkAllAppend: construction" fun _ ↦ none
    pure (⟨0, [Ls], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The program with the typing's step kept folded, which the proofs about runs of forms unfold
only at a form whose label is known. -/
def runProg (P : Prog) : Prog := { P with folded := P.folded ++ ["Typing.checkStep"] }

/-- The typing's concatenation of lists of forms, at the two lists. -/
def txsApp (P : Prog) (xs ys : Term) : Term := pc P "Typing/Txs.append" [xs, ys]

/-- The concatenation of a list with the empty list is the list, stated in normal form: by
induction on it. -/
def appendNil (P : Prog) (S : Defs) : Step :=
  ("appendNil", fun ix E ↦ do
    let K : Kit := ⟨runProg P, S, E, ix, []⟩
    let Ls := list treeTy
    let some l := nfE K.G K.E (K.rules []) [Ls] (txsApp P (v 0) (nilT treeTy))
      | dbgTrace "appendNil: left" fun _ ↦ none
    let φ := Term.eq l (v 0)
    let d₀ ← K.byNorm [] [] (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
    let some d₁ := normLastK K K.byNorm [Ls, treeTy] [Internal.weakenElem φ]
        (Internal.listConsAt 1 treeTy φ)
      | dbgTrace "appendNil: construction" fun _ ↦ none
    pure (⟨0, [Ls], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The concatenation of a list and a singleton, concatenated with a further list, is the
concatenation of the list with the further list after the singleton's element: by induction on
the list, in the context of the list v0, the element v1 and the further list v2; stated in normal
form. -/
def appendSnoc (P : Prog) (S : Defs) : Step :=
  ("appendSnoc", fun ix E ↦ do
    let K : Kit := ⟨runProg P, S, E, ix, []⟩
    let Ls := list treeTy
    let nf (t : Term) : Option Term := nfE K.G K.E (K.rules []) [Ls, treeTy, Ls] t
    let some l := nf (txsApp P (txsApp P (v 0) (consT treeTy (v 1) (nilT treeTy))) (v 2))
      | dbgTrace "appendSnoc: left" fun _ ↦ none
    let some r := nf (txsApp P (v 0) (consT treeTy (v 1) (v 2)))
      | dbgTrace "appendSnoc: right" fun _ ↦ none
    let φ := Term.eq l r
    let d₀ ← K.byNorm [treeTy, Ls] []
      (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
    let some d₁ := normLastK K K.byNorm [Ls, treeTy, treeTy, Ls] [Internal.weakenElem φ]
        (Internal.listConsAt 1 treeTy φ)
      | dbgTrace "appendSnoc: construction" fun _ ↦ none
    pure (⟨0, [Ls, treeTy, Ls], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- A marker, the node of label 9 over the trees v0, checked from an environment v1 with no
rejection: the environment with the marker after its markers, with no rejection; stated in the
normal form of the runs' rules, the typing's step unfolded in its proof. -/
def checkStepMarker (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("checkStepMarker", fun ix E ↦ do
    let K : Kit := ⟨runProg P, S, E, ix, []⟩
    let Γ := [list treeTy, T.envTy]
    let nothing := pc P "Typing/OName.nothing" []
    let m := nodeT (Term.pair (numeral 9) (v 0))
    let lhs := pc P "Typing.checkStep" [Term.pair (v 1) nothing, m]
    let rhs := Term.pair (pc P "Typing.withMs" [v 1, txsApp P (pc P "Typing.envMs" [v 1])
      (consT treeTy m (nilT treeTy))]) nothing
    let nf (t : Term) : Option Term := nfE K.G K.E (K.rules []) Γ t
    let some l := nf lhs | dbgTrace "checkStepMarker: left" fun _ ↦ none
    let some r := nf rhs | dbgTrace "checkStepMarker: right" fun _ ↦ none
    let a : Internal.Thm := ⟨0, Γ, [], Term.eq l r⟩
    let rs := K.rules [] ++ [.delta (P.idx "Typing.checkStep")]
    let some d := byMode .full K.G K.E 0 rs Γ [] l r
      | dbgTrace "checkStepMarker: not proved" fun _ ↦ none
    pure (a, d))

/-- The partition of the forms of index 0, in the context {lit}`Γ`, by which
{lit}`Datatype.markersFirst` orders them: the pair of the markers and of the other forms, read
from its normal form, the concatenation kept folded. -/
def partitionT (K : Kit) (Γ : List Tree) : Option Term := do
  let K := { K with P := { K.P with folded := K.P.folded ++ ["Datatype/Txs.append"] } }
  let r ← nfE K.G K.E (K.rules []) Γ (pc K.P "Datatype.markersFirst" [v 0])
  match r.label, r.children with
  | .app, [f, _] => match f.label, f.children with
    | .app, [_, a] => match a.label, a.children with
      | .fst, [X] => some X
      | _, _ => none
    | _, _ => none
  | _, _ => none

/-- A goal closed by {lit}`close`, or else its bitstring {lit}`X`, a variable, split, to a depth:
empty, or a construction whose bit is split and whose rest is split in turn. -/
def splitBits (K : Kit) (X : List Tree → Term) (depth : ℕ) (close : Deducer) : Deducer :=
  (Nat.rec (motive := fun _ ↦ (List Tree → Term) → Deducer) (fun _ ↦ close)
    (fun _ rec X Γ Φ ψ ↦ (close Γ Φ ψ).orElse fun _ ↦
      K.listCase bitTy (X Γ) close (fun Γ Φ ψ ↦
        K.bitCase (v 1) (rec fun _ ↦ v 0) (rec fun _ ↦ v 0) Γ Φ ψ) Γ Φ ψ) depth) X

/-- The typing's run over the markers of a program's forms, from an environment with some markers
and no rejection, is the environment with the program's markers after those, with no rejection:
by induction on the forms; at a construction, the head a node, the induction hypothesis at the
environment and at its markers and at those with the head after them, the bits of the head's label
split until the goal closes, a marker's step its equation ({name}`checkStepMarker`). -/
def markersRun (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("markersRun", fun ix E ↦ do
    let K : Kit := ⟨runProg P, S, E, ix, ["appendNil", "appendSnoc", "checkStepMarker"]⟩
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    let some X₀ := partitionT K [Ls] | dbgTrace "markersRun: no partition" fun _ ↦ none
    let nothing := pc P "Typing/OName.nothing" []
    -- under the quantifiers: the markers v0, the environment v1, the forms v2
    let ms := Term.fst (Term.subst X₀ fun i ↦ v (i + 2))
    let φ := Internal.Logic.all o T.envTy (Term.lam T.envTy (Internal.Logic.all o Ls (Term.lam Ls
      (Term.eq (pc P "Typing.checkAll" [Term.pair (pc P "Typing.withMs" [v 1, v 0]) nothing, ms])
        (Term.pair (pc P "Typing.withMs" [v 1, txsApp P (v 0) ms]) nothing)))))
    let some d₀ := dAllI L (dAllI L (linkK K "markersRun: empty" K.byNorm)) [] []
        (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
      | dbgTrace "markersRun: empty list" fun _ ↦ none
    -- a construction, under the quantifiers the markers v0, the environment v1, the tail v2 and
    -- the head v3: the head a node, of the label and children v1 and v0, the others shifted by
    -- two; the induction hypothesis at the environment, then at the markers and at the markers
    -- with the head after them, each normalized; the bits of the head's label, v1, split
    let cons : Deducer := dAllI L <| dAllI L <| K.treeNode (v 3) <|
      dAllE L K.G K.E 0 (v 3) fun Γ Φ ψ ↦
        let h := Φ.length - 1
        dAllE L K.G K.E h (v 2) (normLastK K <| dAllE L K.G K.E h
            (txsApp P (v 2) (consT treeTy (v 5) (nilT treeTy))) (normLastK K <|
          splitBits K (fun Γ ↦ v (Γ.length - 5)) 6
            (fun Γ Φ ψ ↦ normHyps K ((List.range Φ.length).drop 1) (K.solve 3) Γ Φ ψ))) Γ Φ ψ
    let some d₁ := cons [Ls, treeTy] [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
      | dbgTrace "markersRun: construction" fun _ ↦ none
    pure (⟨0, [Ls], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The typing's run from a state with a rejection leaves the state: by induction on the forms; at
a construction, the head a node, the typing's step unfolded, the bits of the head's label split
until the step's case analysis returns the state, the induction hypothesis then closing. In the
context of the forms v0, under the environment and the rejected name. -/
def checkAllRejected (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("checkAllRejected", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    -- under the quantifiers: the name v0, the environment v1, the forms v2
    let st := Term.pair (v 1) (pc P "Typing/OName.just" [v 0])
    let φ := Internal.Logic.all o T.envTy (Term.lam T.envTy (Internal.Logic.all o treeTy
      (Term.lam treeTy (Term.eq (pc P "Typing.checkAll" [st, v 2]) st))))
    let some d₀ := dAllI L (dAllI L (linkK K "checkAllRejected: empty" K.byNorm)) [] []
        (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
      | dbgTrace "checkAllRejected: empty list" fun _ ↦ none
    -- a construction, under the quantifiers the name v0, the environment v1, the tail v2 and the
    -- head v3: the head a node, the others shifted by two; the induction hypothesis at the
    -- environment and the name, normalized; the bits of the head's label, v1, split
    let cons : Deducer := dAllI L <| dAllI L <| K.treeNode (v 3) <|
      dAllE L K.G K.E 0 (v 3) fun Γ Φ ψ ↦
        dAllE L K.G K.E (Φ.length - 1) (v 2) (normLastK K <|
          splitBits K (fun Γ ↦ v (Γ.length - 5)) 6
            (fun Γ Φ ψ ↦ normHyps K ((List.range Φ.length).drop 1) (K.solve 3) Γ Φ ψ)) Γ Φ ψ
    let some d₁ := cons [Ls, treeTy] [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
      | dbgTrace "checkAllRejected: construction" fun _ ↦ none
    pure (⟨0, [Ls], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let some (P, _, T) := extended3 | throwError "the program does not extend"
  let missing := programNames.filter fun n ↦ P.idx n == 0
  unless missing.isEmpty do throwError m!"no definitions named {missing}"
  let some φ := programφ P T | throwError "the statement does not build"
  logInfo m!"the statement is a formula: {Internal.typeIn P.G 0 [] φ == some omega}"

/-- The development of the typing's runs over a program's forms. -/
def programDev (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  [checkAllAppend P S T, appendNil P S, appendSnoc P S, checkStepMarker P S T, markersRun P S T,
    checkAllRejected P S T]

/-- The development of the typing's runs over a program's forms ({name}`programDev`), after the
base's declarations, stored as the certificate {lit}`datatype-program`. -/
def programCertificates (P : Prog) (S : Defs) (T : Defs3) (before : List Internal.Thm) :
    Except String (List Stored.Cert) := do
  let some dev := baseDev3 P S T | throw "the base is not stated"
  certifyAfter P (dev.map (·.1)) "datatype-program" (programDev P S T) before

end GebTests.Prototypes.FreeTopos.Datatypes

end
