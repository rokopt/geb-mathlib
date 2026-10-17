/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.DatatypeList -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.DatatypeList -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The datatype language's soundness at abstractions and applications

The cases of the soundness of the datatype language's stage-1 compiler
({lit}`GebTests.Prototypes.FreeTopos.DatatypeBase`) whose lists have any length: an abstraction
over a list of binders, and an application of a head to a list of arguments.

## Main definitions

* {lit}`appCertificates` — the development, after the base's, the atom's and the list's.

## References

* {cite}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, datatypes, soundness, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Datatypes

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Translation Geb.FreeTopos.Tactics
open GebTests.Prototypes.FreeTopos.Weakening
open scoped FinEnum

open Internal (Term)
open GebTests.Prototypes.FreeTopos.Normalization

/-- The kernel's abstraction compatible with the relation, its conclusion's relation itself rather
than its η-expansion, as the soundness states it ({name}`lamCompatThm`): {lit}`lamCompat`, the
η-expansion rewritten to the relation, the two equal by extensionality. -/
def lamCompatC (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("lamCompatC", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let a := lamCompatThm P S T true
    let arrowT (A B : Term) : Term := nodeT (Term.pair (numeral Kernel.Label.tyArrow)
      (consT treeTy A (consT treeTy B (nilT treeTy))))
    -- the η-expansion of the relation at the arrow type and the relation, in the context
    let eta := Term.eq (Term.lam treeTy (Term.app (T.relT (v 6) (arrowT (v 5) (v 4))) (v 0)))
      (T.relT (v 5) (arrowT (v 4) (v 3)))
    let some dEta := dEq (Internal.byFunExt P.G 0 (byMode .full P.G E 0 [.rule .beta])) a.ctx []
        eta
      | dbgTrace "lamCompatC: the η-expansion" fun _ ↦ none
    let some d := dImpI K.L (K.cutThm "lamCompat" (fun _ ↦ (List.range 6).map v) <|
        K.impE dHyp <| dCut eta dEta fun Γ Φ ψ ↦
          dRwHyp (evalRw K.G K.E [.hyp (Φ.length - 1)] .full) (Φ.length - 2) dHyp Γ Φ ψ)
        a.ctx a.hyps a.concl
      | dbgTrace "lamCompatC: not proved" fun _ ↦ none
    pure (a, d))

/-- The list of trees of the elements of a list of terms. -/
def listNode (ts : List Term) : Term :=
  nodeT (Term.pair (numeral 2) (ts.foldr (consT treeTy) (nilT treeTy)))

/-- The reader's form of a list, the first component of its fold's value, the children of index 0
and the fold's parameters after them: the first component of the value's normal form by the
vocabulary's rules, and its weak normal form with the fold's argument and the list's case of the
reader unfolded as well, normalized by the vocabulary's rules; the weak normal form leaves the
step's resolution, the second component, unevaluated. -/
def rawListR (P : Prog) (T : Defs3) : Step :=
  ("rawListR", fun ix E ↦ do
    let f ← (foldSpecs P T.envTy)[4]?
    let (_, d, _, _, _, _) ← foldDefn P f (T.argIdx 4)
    let tys := d.params.tail
    let Γ := list treeTy :: tys
    let ps := (List.range tys.length).reverse.map fun i ↦ v (i + 1)
    let rs := vRules3 P ix E.size
    let some l := (nfE P.G E rs Γ (T.foldAt 4 ps (nodeT (Term.pair (numeral 2) (v 0))))).map
        Term.fst
      | dbgTrace "rawListR: left" fun _ ↦ none
    let some (w, dw, _) := Internal.eval P.G E 0
        (rs ++ [.delta (T.argIdx 4), .delta (P.idx "Reader.resolveList")]) 4096 .weak Γ [] l
      | dbgTrace "rawListR: weak" fun _ ↦ none
    let some (r, dr, _) := Internal.eval P.G E 0 rs 4096 .full Γ [] w
      | dbgTrace "rawListR: right" fun _ ↦ none
    if l == r then none else
    pure (⟨0, Γ, [], Term.eq l r⟩, nd .join [nd .trans [dw, dr], nd .refl]))

/-- The form of an abstraction over a list of one binder, a name at an annotation, in a body, the
elements of a context of three trees, the outermost first: the name, the annotation and the body.
The list of binders is the list of one, not the binder itself, which, its name a list, the reader
and the typing read as a list of two binders. -/
def lamOneForm (P : Prog) : Term :=
  listNode [kwAtom P "Reader.kwLam", listNode [listNode [v 2, v 1]], v 0]

/-- The soundness at an abstraction over one binder at expanded forms, given that at the body. -/
def lamOneThm (P : Prog) (S : Defs) (T : Defs3) : Internal.Thm :=
  kwThm P S T "Reader.kwLam" 3 [false, false, true] true (lamOneForm P)

/-- The soundness at an abstraction over one binder at expanded forms: the elements' sources, the
binder an atom, its name none of the erasure's keywords, the annotation read by the typing and the
reader, the body's type in the context extended by the binder at the annotation, its resolution in
the scope extended by the binder's name, the annotation a kernel type and the body's kernel type in
the kernel's context extended by it, each decided, any absent refuting the statement's hypothesis.
The keywords are decided before the binder's abbreviation, since the erasure at the binder, on
which the abbreviation's decisions read, is known only once they are. The abstraction resolves to
the kernel's abstraction of the body over the annotation's kernel type, related at the arrow type
by {lit}`lamCompatC`, the body's soundness at the context and environment extended, related by
{lit}`envTCons`; the theorem's conclusion, its labels written as bitstrings, is the goal. -/
def lamOneCase (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("lamOneCase", fun ix E ↦ do
    let ihs := [false, false, true]
    let W₀ := kwKit P S T ix E 3 ihs "Reader.kwLam" true
    let W := { W₀ with K := { W₀.K with more := W₀.K.more ++ ["rawListR"] } }
    let B : BindKit := ⟨W, 0, 1, 2, "lam"⟩
    let K := W.K
    let a := lamOneThm P S T
    let (tyT, kT) := B.terms
    let kernelT := pc P "Check.typeIn" [v 9, v 8, pc P "Prelude.get" [kT]]
    let decisions : Deducer → Deducer := fun k ↦
      ((List.range 3).foldr (fun c k ↦ W.present s!"element {c + 1}'s expansion"
        (B.atEl c (W.expansion (v nQ))) 5 k) <|
      W.sources <|
      (B.binderAtom (pre := fun typed k ↦
        ["Typing.kwRep", "Typing.kwDecode", "Typing.kwDatum"].foldr (fun kw k ↦
          decideKnown K (fun Γ ↦ pc P "Typing.namedTx" [B.raw B.binder Γ, pc P kw []]) k
            (linkK K s!"lam: the binder named by {kw}" (K.hypFalse typed))) k)) fun typed ↦
      (fun k ↦ decideOpt K B.readTypeAt (K.hypFalse (typed + 1))
        (W.generalize (fun Γ ↦ pc K.P "Prelude.get" [B.readTypeAt Γ]) k) (minimal := true)) <|
      (fun k ↦ K.splitHyp (typed + 1) k 6) <|
      (fun k ↦ decideOpt K B.readTyAt (fun Γ Φ ψ ↦
          (K.hypFalse typed Γ Φ ψ).orElse fun _ ↦ W.hypFalseU typed Γ Φ ψ)
        (W.generalize (fun Γ ↦ pc K.P "Prelude.get" [B.readTyAt Γ]) k) (minimal := true)) <|
      (W.presentAt "the body's type" (B.bodyAt tyT) typed (W.hyp 6) · (tested := true)) <|
      (W.presentAt "the body's resolution" (B.bodyAt kT) (typed + 1) (W.hyp 7) ·
        (tested := true)) <|
      decideKnown K (fun Γ ↦ pc P "Check.isTy" [B.annK Γ])
        (linkK K "lam: the annotation not a kernel type" fun Γ Φ ψ ↦
          (K.hypFalse (W.hyp 8) Γ Φ ψ).orElse fun _ ↦ K.hypFalse (typed + 2) Γ Φ ψ) <|
      (W.presentAt "the body's kernel type" (B.bodyAt kernelT) (typed + 2) (W.hyp 8) ·
        (unfolding := false) (tested := true)) <| K.norm k)
    -- the abstraction's convergence, its labels written as the bitstrings the goal's are
    let bits := [D.bnil, D.b0, D.b1].map Internal.NormRule.delta
    let eval := B.lamConv "lamCompatC" fun Γ Φ ψ ↦
      dRwHyp (evalRw K.G K.E bits .full) (Φ.length - 1) dHyp Γ Φ ψ
    let some d := W.intro "Reader.kwLam" (decisions eval) a.ctx a.hyps a.concl
      | dbgTrace "lamOneCase: not proved" fun _ ↦ none
    pure (a, d))

/-- The development of the soundness at abstractions and applications. -/
def appDev3 (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  kwEqs P T "Reader.kwLam" 3 (lamOneForm P) true ++
    [lamCompatC P S T, rawListR P T, lamOneCase P S T]

/-- The development of the soundness at abstractions and applications, after the base's, the
atom's and the list's declarations, stored as the certificate {lit}`datatype-app`, each
declaration checked as it is stored. -/
def appCertificates (P : Prog) (S : Defs) (T : Defs3) (before : List Internal.Thm) :
    Except String (List (String × List Internal.Decl)) := do
  let some dev := baseDev3 P S T | throw "the base is not stated"
  let E : Array Internal.Entry := (before.map Internal.Entry.language).toArray
  let names := dev.map (·.1) ++ (atomDev3 P S T).map (·.1) ++ (listDev3 P S T).map (·.1)
  unless names.length = E.size do
    throw "the certificates before are not the base's, the atom's and the list's"
  -- each step's proof reported as it is found
  let app := (appDev3 P S T).map fun (nm, f) ↦
    (nm, fun ix E ↦ (f ix E).map fun r ↦ dbgTrace s!"{nm} proved" fun _ ↦ r)
  let (_, _, ds) ← developAfter names E app
  checkAfter P.G E (app.map (·.1)) ds
  pure [("datatype-app", ds)]

end GebTests.Prototypes.FreeTopos.Datatypes

end

