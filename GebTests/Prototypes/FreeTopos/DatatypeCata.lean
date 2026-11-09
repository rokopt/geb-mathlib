/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.DatatypeApp
public import GebTests.Prototypes.FreeTopos.DatatypeCaseSound
public meta import GebTests.Prototypes.FreeTopos.DatatypeCaseSound -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The datatype language's soundness at structural recursion

The soundness of the datatype language's stage-1 compiler at a structural recursion.

## Main definitions

* {lit}`cataCertificates` — the development, stored as the certificate {lit}`datatype-cata`.

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

/-- The context of the walk of a structural recursion's clause's fields: the case analysis's
({name}`walkCtx`), the fixed fields' entries v0 and the remaining children's v3, then the
datatype's atom v11, the result type v12, the result type's form v13 and the default result's
form v14. -/
def cataWalkCtx (T : Defs3) : List Tree :=
  walkCtx T ++ [treeTy, treeTy, treeTy, treeTy]

/-- The parts of a structural recursion's clause's walk ({name}`WalkParts`), read off the normal
forms of the typing's walk ({lit}`Typing.cataFields`), of the constructor's test
({lit}`Typing.ctorOk`), and of the erasure's bindings, those of the recursion's erasure
({lit}`Datatype.eraseCata`) at a single clause, whose body is untested. -/
def cataWalkParts (K : Kit) (T : Defs3) : Option WalkParts := do
  let P := K.P
  let Γ := cataWalkCtx T
  let nf (t : Term) : Option Term := (evalRw K.G K.E (K.rules []) .full Γ [] t).map Prod.fst
  let md := listNode' (consT treeTy (leafT bnilT) (consT treeTy (listNode' (v 0))
    (consT treeTy (listNode' (v 3)) (nilT treeTy))))
  let tyNF ← nf (pc P "Typing.cataFields" [v 5, v 11, v 12, v 4, md, v 2, nilT treeTy])
  let ty ← findFoldr (v 0) tyNF
  let fts ← nf (call D.children [] [apps ((primT Kernel.Prim.child).getD Term.star)
    [v 4, leafT (numeral 1)]])
  let okNF ← nf (pc P "Typing.ctorOk" [pc P "Typing.envMs" [v 5], v 4, leafT bnilT,
    nilT (list treeTy)])
  let ok ← findFoldr fts okNF
  let ls (ts : List Term) : Term := ts.foldr (consT treeTy) (nilT treeTy)
  let rs := ls [v 11, v 13, leafT bnilT, v 14, listNode' (ls [md]), v 1]
  let erNF ← (evalRw K.G K.E (K.rules [] ++ [.delta (P.idx "Datatype.eraseCata")]) .full Γ []
    (pc P "Datatype.eraseCata" [rs])).map Prod.fst
  let er ← findFoldr (v 0) erNF
  pure ⟨ty, ok, er⟩

/-- The program for the walk of a structural recursion's clause's fields: the case analysis's
({name}`walkProg`), whose lemmas state the erasure's other builders unfolded. -/
def cataWalkProg (P : Prog) : Prog := walkProg P

/-- The type of a suspended result of the result type R, a function of the unit. -/
def thunkTy (P : Prog) (R : Term) : Term := pc P "Typing.tyArrow" [pc P "Typing.tyUnit" [], R]

/-- The named context's entry of the suspended results split, at the product of a suspended
result and their list, at the result type R. -/
def splitEntry (P : Prog) (R : Term) : Term :=
  pc P "Typing.abbr" [pc P "Typing.boundName" [pc P "Typing.kwSplit" []],
    pc P "Typing.tyProd" [thunkTy P R, pc P "Typing.tyList" [thunkTy P R]]]

/-- The name of the suspended results split, as the reader reads it. -/
def splitName (P : Prog) : Term := atomNameT (pc P "Datatype.aQ" [])

/-- Characters neither of the name of the children remaining nor of the split's: the label of each
comparison empty, as a false test's case gives it. -/
def unnamedT (P : Prog) (c : Term) : Term :=
  let unset (t : Term) : Term := Term.eq (call D.lab [] [t]) (nilT bitTy)
  Internal.Logic.conj P.o (unset (namedFields P c))
    (unset (apps ((primT Kernel.Prim.equal).getD Term.star)
      [splitName P, nodeT (Term.pair (numeral 0) c)]))

/-- The variable of a structural recursion's field's entry, its first element. -/
def entryVar (P : Prog) (e : Term) : Term :=
  pc P "Datatype.nthTx" [pc P "Datatype.elems" [e], leafT bnilT]

/-- The flag of a structural recursion's field's entry, its second element. -/
def entryFlag (P : Prog) (e : Term) : Term :=
  pc P "Datatype.nthTx" [pc P "Datatype.elems" [e], leafT (numeral 1)]

/-- A flag is the atom of the numeral zero or of the numeral one, as the expansion writes it. -/
def flagOk (P : Prog) (f : Term) : Term :=
  let equalT := (primT Kernel.Prim.equal).getD Term.star
  truth P.o (pc P "Prelude.or" [apps equalT [f, pc P "Datatype.numAtom" [leafT bnilT]],
    apps equalT [f, pc P "Datatype.numAtom" [leafT (numeral 1)]]])

/-- The suspended results {lit}`rs` of the children {lit}`ts` related: at each index of a child
that is a member of the datatype {lit}`d` by the markers of the typing environment {lit}`E`, the
result present and related, in the relation's context {lit}`D`, at the type of a suspended result
of the result type {lit}`R`. -/
def relatedT (P : Prog) (T : Defs3) (E d D R ts rs : Term) : Term :=
  let o := P.o
  let get (t : Term) : Term := pc P "Prelude.get" [t]
  let ms := pc P "Typing.envMs" [sh 1 E]
  -- beneath the quantifier, the index's bitstring v0
  let at_ (xs : Term) : Term := pc P "Prelude.nth" [sh 1 xs, leafT (v 0)]
  let member := pc P "Prelude.and" [pc P "Prelude.isSome" [at_ ts],
    pc P "Typing.fieldOk" [ms, sh 1 d, pc P "Typing.memberships" [ms, get (at_ ts)]]]
  Internal.Logic.all o bitsTy (Term.lam bitsTy (Internal.Logic.imp o (truth o member)
    (Internal.Logic.conj o (truth o (pc P "Prelude.isSome" [at_ rs]))
      (Term.app (T.relT (sh 1 D) (thunkTy P (sh 1 R))) (get (at_ rs))))))

/-- The lengths of two lists of trees equal: neither less than the other by the kernel's
comparison. -/
def lenEqT (P : Prog) (xs ys : Term) : Term :=
  let (a, b) := (pc P "Prelude.length" [xs], pc P "Prelude.length" [ys])
  Internal.Logic.conj P.o (notTest P.o (ltL a b)) (notTest P.o (ltL b a))

/-- An entry's variable's characters fixed by the expansion of the numeral abbreviations
{lit}`nums`, as a predicate of an entry. -/
def fixedEntry (P : Prog) (nums : Term) : Term :=
  Term.lam treeTy (Term.app (sh 1 (fixedAtom P nums)) (entryVar P (v 0)))

/-- An entry's flag the atom of a numeral zero or one, as a predicate of an entry. -/
def flagEntry (P : Prog) : Term := Term.lam treeTy (flagOk P (entryFlag P (v 0)))

/-- The statement of the walk of a structural recursion's clause's fields, at the fixed fields'
entries v0 of {name}`cataWalkCtx`: the case analysis's ({name}`walkφ`), the entries' flags each
the atom of a numeral zero or one ({name}`flagOk`), the numeral abbreviations coherent with the
typing environment ({lit}`Defs3.numsT`), the definitions' names none a primitive's
({lit}`Defs3.namesT`), with the suspended results
of the children remaining beside them: their pair with a value of the first component at an index
of the environment where the scope of the named context has the split's name and the kernel's
context the pair's type, the name the named context binds at that type. Where
the results are as many as the children and related ({name}`relatedT`), the resolution converges
to a value related at the walk's type. -/
def cataWalkφ (P : Prog) (S : Defs) (T : Defs3) (w : WalkParts) : Term :=
  let o := P.o
  let all (A : Tree) (t : Term) : Term := Internal.Logic.all o A (Term.lam A t)
  let imp := Internal.Logic.imp o
  let isSomeT (t : Term) : Term := truth o (pc P "Prelude.isSome" [t])
  let get (t : Term) : Term := pc P "Prelude.get" [t]
  -- beneath the nine quantifiers: the field types v8, the children v7, their results v6, the
  -- pair's first component v5, the results' type v4, the pair's index's bitstring v3, and the
  -- environment, the named context and the kernel's context beneath the entries v2, v1 and v0;
  -- the walk's context's variables shifted by 9
  let q (i : ℕ) : Term := v (i + 9)
  let ms := pc P "Typing.envMs" [q 5]
  let cx := consT treeTy (fieldsEntry P) (v 1)
  let pairV := nodeT (Term.pair (numeral Kernel.Label.pair)
    (consT treeTy (v 5) (consT treeTy (pc P "Eval.ofList" [v 4, v 6]) (nilT treeTy))))
  let env := consT treeTy (pc P "Eval.ofList" [leafT (numeral Kernel.Label.tyTree),
    quotesT P (v 7)]) (v 2)
  let kc := consT treeTy (listTK P (q 7)) (v 0)
  let some (t : Term) : Term := pc P "Prelude.some" [t]
  let tyW := Term.app (Term.app (sh 9 w.ty) (v 8)) cx
  let mem := Term.lam treeTy (pc P "Typing.memberships" [sh 1 ms, v 0])
  let okW := Term.app (foldrAt (sh 9 w.ok) (v 8)) (mapListsT mem (v 7))
  let kw := pc P "Reader.resolve" [q 7, q 9, pc P "Reader.expandNums" [q 8, sh 9 w.er],
    scopeOf P (q 8) cx]
  let related := relatedT P T (q 5) (q 11) (q 10) (q 12) (v 7) (v 6)
  -- the split's name at the pair's index of the scope, the numeral of a bitstring, the
  -- environment's value there the pair and the kernel's context's type there the reading of the
  -- split's type at the expansion of the result type's form
  let atIdx := Term.eq (pc P "Reader.indexOf" [splitName P, scopeOf P (q 8) cx])
    (some (leafT (v 3)))
  let envAt := Term.eq (pc P "Prelude.nth" [env, leafT (v 3)]) (some pairV)
  let kcAt := Term.eq (pc P "Prelude.nth" [kc, leafT (v 3)])
    (some (get (pc P "Reader.readType" [q 7,
      pc P "Datatype.splitTy" [pc P "Reader.expandNums" [q 8, q 13]]])))
  let fixedE : Term := fixedEntry P (v 8)
  let flagE : Term := flagEntry P
  imp (Term.eq (Term.snd (v 10)) (pc P "Typing.envMs" [v 5])) <| imp (T.kwsT (v 8)) <|
    imp (S.allL fixedE (v 0)) <| imp (S.allL fixedE (v 3)) <|
    imp (S.allL flagE (v 0)) <| imp (S.allL flagE (v 3)) <|
    imp (bodyφ P S T 0 (v 1) (v 2)) <| imp (T.numsT (v 5) (v 8)) <| imp (T.namesT (v 9)) <|
    all (list treeTy) <| all (list treeTy) <| all (list treeTy) <| all treeTy <| all treeTy <|
    all bitsTy <| all (list treeTy) <| all (list treeTy) <| all (list treeTy) <|
    imp (isSomeT tyW) <| imp (truth o okW) <| imp (lenEqT P (v 7) (v 6)) <| imp related <|
    imp atIdx <| imp envAt <| imp kcAt <|
    imp (T.envT (q 10) cx env) <| imp (T.cxT (q 5) cx) <| imp (isSomeT kw) <|
    imp (isSomeT (pc P "Check.typeIn" [q 6, kc, get kw])) <|
    S.conv (Term.lam nat (S.evN (Term.fst (sh 1 (q 10))) (v 0) (sh 1 env) (sh 1 (get kw))))
      (T.relT (q 10) (get tyW))

/-- An equation whose left side is, as written, that of the equation among the hypotheses of index
{lit}`i`, rewritten there to the hypothesis's right side, the congruence's derivation built
directly, so that no normalization reduces inside the left side first; then {lit}`k`. -/
def rwHypRoot (i : ℕ) (k : Deducer) : Deducer := fun Γ Φ ψ ↦ do
  let (l, r) ← Internal.eqParts ψ
  let (l', R) ← Internal.eqParts (← Φ[i]?)
  if l != l' then none else
  let d : Internal.Deriv := RoseTree.node .cong
    [RoseTree.node (.rwHyp i false) [], RoseTree.node .refl []]
  dRwBy (fun _ _ _ ↦ some (Term.eq R r, d)) k Γ Φ ψ

/-- Hypotheses normalized in turn, each without itself, so that their left sides are in the
normal form in which they occur. -/
def normHyps (K : Kit) (hs : List ℕ) (k : Deducer) : Deducer :=
  hs.foldr (fun h k Γ Φ ψ ↦ dRwHyp (evalRw K.G K.E (K.rulesEx Φ h) .full) h k Γ Φ ψ) k

/-- The erasure's fragments of a structural recursion's clause, at the result type's form
{lit}`r`: the split of the suspended results at the first, the default's form {lit}`dr` at the
results' end; the forcing of the split's first; and the right fold forcing the split's rest. -/
def cataFrags (P : Prog) (r dr : Term) : Term × Term × Term :=
  let d (n : String) : Term := pc P s!"Datatype.{n}" []
  let f1 (n : String) (a : Term) : Term := pc P s!"Datatype.{n}" [a]
  let sx (k : ℕ) (as : List Term) : Term := pc P s!"Datatype.sx{k}" as
  let th := f1 "thTy" r
  let split := sx 6 [d "aLcase", th, f1 "splitTy" r, sx 2 [d "aSnd", d "aQ"],
    sx 3 [d "aPair", pc P "Datatype.sLam1" [d "aU", d "aUnit", dr], sx 2 [d "aNil", th]],
    pc P "Datatype.sLam2" [d "aH", th, d "aTl", f1 "sList" th, sx 3 [d "aPair", d "aH",
      d "aTl"]]]
  let force := sx 2 [sx 2 [d "aFst", d "aQ"], d "aUnitV"]
  let fold := sx 6 [d "aFoldr", th, f1 "sList" r,
    pc P "Datatype.sLam2" [d "aH", th, d "aA", f1 "sList" r,
      sx 3 [d "aCons", sx 2 [d "aH", d "aUnitV"], d "aA"]],
    sx 2 [d "aNil", r], sx 2 [d "aSnd", d "aQ"]]
  (split, force, fold)

/-- The atoms of the erasure's fragments of a structural recursion ({name}`cataFrags`), as the
reader looks them up among the abbreviations. -/
def cataAtoms (P : Prog) : List Term :=
  ["aLcase", "aSnd", "aQ", "aPair", "aU", "aUnit", "aNil", "aH", "aTl", "aFst", "aUnitV",
    "aFoldr", "aA", "aCons", "aLam", "aList", "aArrow", "aProd"].map fun a ↦
    atomNameT (pc P s!"Datatype.{a}" [])

/-- The atoms of the erasure's fragments of a structural recursion ({name}`cataAtoms`) the case
analysis's walk does not write, those it writes as the reader's keywords among them. -/
def cataExtraAtoms (P : Prog) : List Term :=
  (cataAtoms P).filter (· ∉ walkAtoms P ++
    ["aLcase", "aNil", "aLam", "aList"].map fun a ↦ atomNameT (pc P s!"Datatype.{a}" []))

/-- The names of the atoms of {name}`cataExtraAtoms` excluded from the abbreviated names
({lit}`atomExcluded`), each with its lemma's name. -/
def cataExcluded (P : Prog) : List (Term × String) :=
  (cataExtraAtoms P).zipIdx.map fun (n, i) ↦ (n, s!"cataAtomExcluded{i}")

set_option linter.unusedVariables false in
/-- The program of the proofs of a structural recursion's walk: the case analysis's, with the
reader's numeral unfolded, which computes a flag's value, and the kernel's typing folded. -/
def cataVarProg (P : Prog) : Prog :=
  { cataWalkProg P with
    folded := ((cataWalkProg P).folded.filter (· ≠ "Reader.numeral")) ++ ["Check.typeIn"] }

/-- A clause's variable ({lit}`Typing.clauseVar`) is an atom of some characters, the name of which
the typing admits as a binder's and which is not the implementation's, beginning with no {lit}`%`.
In the context of the variable and the environment. Proved by the node of the variable, its label's
bits refuting the test at any label but an atom's. -/
def clauseVarAtom (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("clauseVarAtom", fun ix E ↦ do
    let P := cataVarProg P
    let K : Kit := ⟨P, S, E, ix, walkRules ix E⟩
    let L := K.L
    let o := P.o
    let conj := Internal.Logic.conj o
    let name (c : Term) : Term := nodeT (Term.pair (numeral 0) c)
    let Γ := [treeTy, T.envTy]
    let a : Internal.Thm := ⟨0, Γ,
      [Internal.Logic.tt o, truth o (pc P "Typing.clauseVar" [v 1, v 0])],
      Internal.Logic.ex o (list treeTy) (Term.lam (list treeTy) (conj
        (Term.eq (v 1) (nodeT (Term.pair (numeral 1) (v 0)))) (conj
        (truth o (pc P "Typing.nameOk" [v 2, name (v 0)]))
        (Term.eq (call D.lab [] [pc P "implName" [name (v 0)]]) (nilT bitTy)))))⟩
    let atomBranch (pC : ℕ) : Deducer :=
      let cs := atPos pC
      decideIn K (fun Γ ↦ pc P "Typing.nameOk" [atPos 0 Γ, name (cs Γ)]) (K.hypFalse 1) <|
      decideIn K (fun Γ ↦ pc P "implName" [name (cs Γ)])
        (fun Γ Φ ψ ↦ dExI L K.G K.E (cs Γ) (dConjI L (K.solve 3) <| dConjI L (K.solve 3)
          (K.solve 3)) Γ Φ ψ)
        (K.hypFalse 1)
    let some d := (K.treeNode (v 0) fun Γ Φ ψ ↦
        let pC := Γ.length - 1
        dBits L K.G K.E (ix "listCases") (ix "bitCases") (fun bs ↦
          if bs.map Oitavem.rank == some 1 then
            linkK K "clauseVarAtom: an atom" (atomBranch pC)
          else linkK K s!"clauseVarAtom: the label {bs.map Oitavem.rank}" (anyClash K))
          3 [] (v 1) Γ Φ ψ) a.ctx a.hyps a.concl
      | dbgTrace "clauseVarAtom: not proved" fun _ ↦ none
    pure (a, d))

/-- Characters of which a given test holds are neither those of the name of the children remaining
nor those of the split's: each comparison's truth makes them that name's ({lit}`equalSound`, their
children), of which the test fails. In the context of the characters. -/
def unnamedAt (thm : String) (prem : Prog → Term → Term) (P : Prog) (S : Defs) : Step :=
  (thm, fun ix E ↦ do
    let P := cataVarProg P
    let K : Kit := ⟨P, S, E, ix, walkRules ix E⟩
    let L := K.L
    let childrenT ← primT Kernel.Prim.children
    let equalT ← primT Kernel.Prim.equal
    let a : Internal.Thm := ⟨0, [list treeTy], [Internal.Logic.tt P.o, prem P (v 0)],
      unnamedT P (v 0)⟩
    let atom (Γ : List Tree) : Term := nodeT (Term.pair (numeral 0) (atPos 0 Γ))
    let refuted (n : Term) : Deducer :=
      K.cutThm "equalSound" (fun _ ↦ [n]) <| K.allEΓ atom <|
      K.impE (linkK K s!"{thm}: the names equal" (K.solve 3)) fun Γ Φ ψ ↦
        K.image (Φ.length - 1) (fun t ↦ apps childrenT [t]) (fun Γ Φ ψ ↦ do
          let (chs, _) ← Internal.eqParts (← Φ[Φ.length - 1]?)
          let rev := Term.eq (atPos 0 Γ) chs
          let dR ← K.byNorm Γ Φ rev
          dCut rev dR (linkK K s!"{thm}: the test refuted" (K.orFalse 1 (eqClash K 1))) Γ Φ ψ) Γ Φ ψ
    let part (t : List Tree → Term) (n : Term) : Deducer :=
      decideIn K t (K.solve 3) (refuted n)
    let some d := dConjI L (part (fun Γ ↦ namedFields P (atPos 0 Γ)) (fieldsName P))
        (part (fun Γ ↦ apps equalT [splitName P, atom Γ]) (splitName P)) a.ctx a.hyps a.concl
      | dbgTrace s!"{thm}: not proved" fun _ ↦ none
    pure (a, d))

/-- The fragments' atoms not abbreviated, as {name}`plainAtoms` decides them, each exclusion by its
lemma among {lit}`table` matched as written, which normalizing the reserved names' lookup would not
reach. -/
def excludedAtoms (K : Kit) (T : Defs3) (table : List (Term × String)) (nums : List Tree → Term)
    (hKw : ℕ) (k : Deducer) : Deducer :=
  table.foldr (fun (n, nm) k ↦
    decideIn K (fun Γ ↦ pc K.P "Prelude.isSome" [pc K.P "Reader.lookupAbbrev" [n, nums Γ]]) k
      (linkK K s!"an atom abbreviated {showT n}" <|
        dRwHyp (evalRw K.G K.E [.delta (T.q + 5 + 2 * nFolds)] .head) hKw
          (K.allEΓ (fun _ ↦ n) (K.impE (K.solve 3) (K.impE
            (K.cutThm nm (fun _ ↦ []) fun Γ Φ ψ ↦ (dHyp Γ Φ ψ).orElse fun _ ↦
              K.byHyp (Φ.length - 1) Γ Φ ψ)
            (fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ)))))) k

/-- The walk of a structural recursion's clause's fields sound ({name}`cataWalkφ`), by induction
on the fixed fields' entries, as the case analysis's ({lit}`walk`). -/
def cataWalk (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("cataWalk", fun ix E ↦ do
    let P := cataVarProg P
    let w ← cataWalkParts ⟨P, S, E, ix, []⟩ T
    let K : Kit := ⟨P, S, E, ix, walkRules ix E⟩
    let L := K.L
    let φ := cataWalkφ P S T w
    let childT ← primT Kernel.Prim.child
    let equalT ← primT Kernel.Prim.equal
    -- the walk's steps unfolded, and the reader's numeral, which computes a flag's value
    let steps : List Internal.NormRule :=
      ["Typing.bindRest", "Typing.bindVar", "Reader.numeral"].map fun nm ↦ .delta (P.idx nm)
    let refute (msg : String) (h : ℕ) : Deducer := linkK K s!"cataWalk: {msg}" fun Γ Φ ψ ↦
      (K.hypFalse h Γ Φ ψ).orElse fun _ ↦
        dRwHyp (evalRw K.G K.E (K.rulesEx Φ h ++ steps) .full) h (dFalse L dHyp) Γ Φ ψ
    let byLast : Deducer := fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ
    -- an equation among the hypotheses, normalized, so that it rewrites the goal to a reflexive
    -- one
    let eqHyp (h : ℕ) : Deducer := normHyps K [h] (K.solve 3)
    -- a hypothesis, or, an equation's instance reflexive by its rewriting, by normalization
    let hypOr (h : ℕ) : Deducer := fun Γ Φ ψ ↦ (K.byHyp h Γ Φ ψ).orElse fun _ ↦
      (K.solve 3 Γ Φ ψ).orElse fun _ ↦ eqHyp h Γ Φ ψ
    -- a lemma's hypothesis as a hypothesis, or, a negation, its antecedent refuted
    let prem : Deducer := fun Γ Φ ψ ↦ (K.norm dHyp Γ Φ ψ).orElse fun _ ↦
      dImpI L (fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ) Γ Φ ψ
    let byStep (h : ℕ) : Deducer := fun Γ Φ ψ ↦
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ h ++ steps) .full) h
        (dRwBy (evalRw K.G K.E (K.rules Φ ++ steps) .full) dHyp) Γ Φ ψ
    -- the hypotheses after the introductions, each quantifier adding the truth of its variable:
    -- the markers, the keywords, the entries' characters, their flags, the body's soundness, the
    -- numeral abbreviations' coherence and the definitions' names, then the walk's typing, the
    -- constructor's test, the lengths' equation, the results' relation, the split's index, the
    -- environment's and the kernel's context's values there, the environment's relation, the
    -- context's names, the resolution and the kernel's typing
    let (hTy, hOk, hLen, hRel, hIdx, hEnvAt) := (18, 19, 20, 21, 22, 23)
    let (hEnv, hCx, hRes, hKer) := (25, 26, 27, 28)
    let (hFlagR, hNums, hNames) := (5, 7, 8)
    -- the closed builders' expansions, cut in after the atoms' decisions, each its equation in
    -- the normal form of the rules
    let negated₀ : Deducer := dImpI L fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ
    let closedEqs (k : Deducer) : Deducer :=
      ["aTNums", "aCNums", "listTNums", "headNums", "tailNums"].foldr (fun nm k ↦
        applyThm K nm (fun Γ ↦ [atPos 6 Γ]) ((walkAtoms P).map fun _ ↦ negated₀) <|
          normLastK K k) k
    -- an entry, of position pE, a list of a variable and its flag, its flag the atom of the
    -- numeral zero, the field's raw type then not the datatype's atom, or of one, the raw type
    -- then the datatype's, decided, the typing of index hT refuted otherwise, or the flags'
    -- hypothesis of index hF, its first conjunct the entry's; k given the flag and the
    -- variable's position
    let entryCases (hT hF : ℕ) (raw : List Tree → Term) (pE : ℕ) (k : Bool → ℕ → Deducer) :
        Deducer :=
      let isRec (Γ : List Tree) : Term := apps equalT [raw Γ, atPos 3 Γ]
      -- the typing's walk refuted, the flag's numeral computed
      let refuteN (msg : String) : Deducer := linkK K s!"cataWalk: {msg}" fun Γ Φ ψ ↦
        dRwHyp (evalRw K.G K.E (K.rulesEx Φ hT ++ steps ++
          [.delta (P.idx "Reader.numeral")]) .full) hT (dFalse L dHyp) Γ Φ ψ
      let a0 := pc P "Datatype.numAtom" [leafT bnilT]
      let a1 := pc P "Datatype.numAtom" [leafT (numeral 1)]
      let refuteFlag : Deducer := linkK K "cataWalk: the flag neither" fun Γ Φ ψ ↦
        dRwHyp (evalRw K.G K.E (K.rulesEx Φ hF) .full) hF
          (fun Γ Φ ψ ↦ dConjE L (Φ.length - 1)
            (fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 2) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
      -- the flag, of position pF
      let flagged (pX pF : ℕ) : Deducer :=
        let f := atPos pF
        let eqAt (a : Term) (k : Deducer) : Deducer :=
          linkK K "cataWalk: the flag's equation" <|
          K.cutThm "equalSound" (fun Γ ↦ [f Γ]) <| K.allEΓ (fun _ ↦ a) <|
            K.impE (linkK K "cataWalk: the flag equal" (K.solve 3)) <|
            linkK K "cataWalk: after the flag's equation" k
        decideIn K (fun Γ ↦ apps equalT [f Γ, a1])
          (decideIn K (fun Γ ↦ apps equalT [f Γ, a0]) refuteFlag
            (eqAt a0 <| decideIn K isRec (k false pX)
              (refuteN "the flag unset, the field's the datatype")))
          (eqAt a1 <| fun Γ Φ ψ ↦ do
            -- the field's test's label split to its bits, as the typing compares the test's
            -- value with the flag's: one passes, any other refutes the typing
            let (X, _) ← evalRw K.G K.E (K.rules Φ) .full Γ Φ (call D.lab [] [isRec Γ])
            dBits L K.G K.E (ix "listCases") (ix "bitCases") (fun bs ↦
              if bs.map Oitavem.rank == some 1 then k true pX
              else refuteN s!"the flag set, the field's test {bs.map Oitavem.rank}") 2 [] X
              Γ Φ ψ)
      fun Γ₃ Φ₃ ψ₃ ↦ K.treeNode (atPos pE Γ₃) (fun Γ Φ ψ ↦
        let pK := Γ.length - 1
        dBits L K.G K.E (ix "listCases") (ix "bitCases") (fun bs ↦
          if bs.map Oitavem.rank == some 2 then fun Γ Φ ψ ↦
            K.listCase treeTy (atPos pK Γ) (refute "an entry without a variable" hT)
              (fun Γ Φ ψ ↦
                let pX := Γ.length - 2
                K.listCase treeTy (atPos (Γ.length - 1) Γ)
                  (refute "an entry without a flag" hT)
                  (fun Γ Φ ψ ↦ flagged pX (Γ.length - 2) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
          else linkK K s!"cataWalk: the entry's label {bs.map Oitavem.rank}"
            (refute "the entry no list" hT))
          3 [] (v 1) Γ Φ ψ) Γ₃ Φ₃ ψ₃
    -- the atoms the erasure writes, its fragments' among them, not abbreviated
    let atoms := walkAtoms P
    -- the introductions after o hypotheses, the induction hypothesis's at a construction
    let introsAt (o : ℕ) (k : Deducer) : Deducer :=
      (List.range 9).foldr (fun _ k ↦ dImpI L k) <|
        (List.range 9).foldr (fun _ k ↦ dAllI L k) <| (List.range 11).foldr (fun _ k ↦ dImpI L k) <|
        plainAtoms K T atoms (atPos 6) (1 + o) <|
        excludedAtoms K T (cataExcluded P) (atPos 6) (1 + o) <|
          closedEqs k
    let intros := introsAt 0
    -- the walk's context's positions, after the four outermost: the default's form, the result
    -- type's form, the result type and the datatype's atom
    let wp (i : ℕ) : List Tree → Term := atPos (i + 4)
    let (drForm, rForm, Rty) := (atPos 0, atPos 1, atPos 2)
    let lastFalse : Deducer := fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ
    let KL : Kit := { K with more := K.more ++ lookupEqNames.filter fun nm ↦ 0 < ix nm }
    -- the unit value's name absent from the scope's tail {lit}`scope0` of the context
    -- {lit}`cx` and from the definitions' names, by the hypotheses of the numeral abbreviations'
    -- coherence, the names and the context's names of indices {lit}`hN`, {lit}`hNm`, {lit}`hC`
    let absentAt (hN hNm hC : ℕ) (scope0 cx : List Tree → Term) (a : String) : List Deducer :=
      let (nums, names, E') := (wp 2, wp 1, wp 5)
      -- a name the typing admits as no binder's and that is not the implementation's, the unit
      -- value's, without an index in the scope's tail: there, the full scope's index present,
      -- the context would give it a type ({lit}`lookupAgreeB`), so that the typing admits it as
      -- a binder's or it is the implementation's ({lit}`Defs3.cxT`)
      let unscoped (n : Term) : Deducer := dImpI L fun Γ Φ ψ ↦
        decideIn K (fun Γ ↦ pc P "Prelude.isSome" [pc P "Reader.indexOf" [n, scope0 Γ]])
          (K.hypFalse (Φ.length - 1))
          (linkK K "cataWalk: a primitive in scope" <|
          K.cutThm "lookupAgreeB" (fun Γ ↦ [cx Γ]) <| K.allEΓ nums <| K.allEΓ E' <|
          K.allEΓ (fun _ ↦ n) <| K.impE (K.byHyp hN) <|
          K.impE (linkK K "cataWalk: the primitive no numeral" <| dImpI L fun Γ Φ ψ ↦
            dRwHyp (evalRw K.G K.E (K.rulesEx Φ (Φ.length - 1) ++
              [.delta (P.idx "Reader.numeral")]) .full) (Φ.length - 1) (dFalse L dHyp) Γ Φ ψ) <|
          K.impE (linkK K "cataWalk: the primitive not abbreviated" (dImpI L lastFalse)) <|
          K.impE (linkK K "cataWalk: the primitive's index" (KL.solve 3)) <| K.conjE fun Γ Φ ψ ↦
          let found := Φ.length - 2
          dRwHyp (evalRw K.G K.E [.delta (T.q + 7 + 2 * nFolds)] .head) hC
            (K.allEΓ (fun _ ↦ n) (K.impE (linkK K "cataWalk: the primitive given a type"
              fun Γ Φ ψ ↦ (K.solve 3 Γ Φ ψ).orElse fun _ ↦ (K.byHyp found Γ Φ ψ).orElse fun _ ↦
                (KL.byHyp found Γ Φ ψ).orElse fun _ ↦ KL.solve 3 Γ Φ ψ)
              (linkK K "cataWalk: the primitive admitted" fun Γ Φ ψ ↦
                dRwHyp (evalRw K.G K.E (K.rulesEx Φ (Φ.length - 1) ++
                  [.delta (P.idx "Reader.indexOf")]) .full) (Φ.length - 1) (dFalse L dHyp)
                  Γ Φ ψ))) Γ Φ ψ) Γ Φ ψ
      -- the unit value's name without an index among the definitions' names
      -- ({lit}`Defs3.namesT`)
      let undefined (n : Term) : Deducer := dImpI L fun Γ Φ ψ ↦
        let iIn := Φ.length - 1
        dRwHyp (evalRw K.G K.E [.delta (T.q + 4 + 2 * nFolds)] .head) hNm
          (K.allEΓ (fun _ ↦ n) <| K.impE (K.byHyp iIn) <|
            K.impE (linkK K "cataWalk: the primitive a primitive" fun Γ Φ ψ ↦
              dRwBy (evalRw K.G K.E (K.rules Φ ++ [.delta (P.idx "Reader.indexOf")]) .full)
                (K.solve 3) Γ Φ ψ) lastFalse) Γ Φ ψ
      -- the absences as the index none ({name}`indexNone`)
      let absentEq (n : Term) (xs : List Tree → Term) (prf : Deducer) : Deducer :=
        K.cutThm "indexNone" (fun Γ ↦ [xs Γ]) <| K.allEΓ (fun _ ↦ n) <| K.impE prf
          fun Γ Φ ψ ↦ eqHyp (Φ.length - 1) Γ Φ ψ
      let absent (a : String) : List Deducer :=
        let n := atomNameT (pc P s!"Datatype.{a}" [])
        [linkK K s!"cataWalk: {a} unscoped" (absentEq n scope0 (unscoped n)),
          linkK K s!"cataWalk: {a} undefined" (absentEq n names (undefined n))]
      absent a
    -- a test already true left as it is, else decided
    let decided (t : List Tree → Term) (kF kT : Deducer) : Deducer := fun Γ Φ ψ ↦
      if (K.solve 3 Γ Φ (truth P.o (t Γ))).isSome then kT Γ Φ ψ else decideIn K t kF kT Γ Φ ψ
    -- a clause's variable x, refuted otherwise by the hypothesis h, an atom whose name is admitted
    -- and begins with no % ({name}`clauseVarAtom`): k given the position of its characters and
    -- the index of the last fact
    let varAtom (h : ℕ) (x : List Tree → Term) (msg : String) (k : ℕ → ℕ → Deducer) : Deducer :=
      decideIn K (fun Γ ↦ pc P "Typing.clauseVar" [wp 5 Γ, x Γ]) (refute msg h) <|
      applyThm K "clauseVarAtom" (fun Γ ↦ [x Γ, wp 5 Γ]) [K.solve 3, K.solve 3] <|
      K.exE <| K.conjE <| K.conjE fun Γ Φ ψ ↦
        let m := Φ.length
        let pC := Γ.length - 1
        normHyps K [m - 4] (decideIn K (fun Γ ↦ pc P "Typing.nameOk" [wp 5 Γ,
            nodeT (Term.pair (numeral 0) (atPos pC Γ))]) (K.hypFalse (m - 2))
          (normHyps K [m - 1] (k pC (m - 1)))) Γ Φ ψ
    -- whether or not abbreviated, the expansion of the binder x, an atom of the characters cs of
    -- the fact iI, an atom of some characters, its name the scope's and neither the children
    -- remaining's name nor the split's: abbreviated, the abbreviation that of a numeral's atom
    -- ({lit}`Defs3.numsT`). So that what follows is proved once, at those characters
    let expansion (o : ℕ) (x cs : List Tree → Term) (iI : ℕ) (k : (List Tree → Term) → Deducer) :
        Deducer := fun Γ Φ ψ ↦ do
      let atomAt (l : ℕ) (c : Term) : Term := nodeT (Term.pair (numeral l) c)
      let conj := Internal.Logic.conj P.o
      let claim : Term := Internal.Logic.ex P.o (list treeTy) (Term.lam (list treeTy) (conj
        (Term.eq (sh 1 (pc P "Reader.expandNums" [wp 2 Γ, x Γ])) (atomAt 1 (v 0))) (conj
        (Term.eq (pc P "expName" [sh 1 (wp 2 Γ), sh 1 (pc P "Typing.atomName" [x Γ])])
          (atomAt 0 (v 0)))
        (unnamedT P (v 0)))))
      let witness (w : List Tree → Term) (thm : String) (pr : Deducer) : Deducer := fun Γ Φ ψ ↦
        dExI L K.G K.E (w Γ) (dConjI L (K.solve 3) <| dConjI L (K.solve 3) <|
          applyThm K thm (fun Γ ↦ [w Γ]) [K.solve 3, pr] byLast) Γ Φ ψ
      let abbreviated : Deducer :=
        dRwHyp (evalRw K.G K.E [.delta (T.q + 3 + 2 * nFolds)] .head) (hNums + o)
          (K.allEΓ (fun Γ ↦ atomAt 0 (cs Γ)) <| K.conjE fun Γ Φ ψ ↦
            let (c1, c2) := (Φ.length - 2, Φ.length - 1)
            dImpE L c2 (K.solve 3) (fun Γ Φ ψ ↦
              dImpE L c1 byLast (K.exE <| K.conjE fun Γ Φ ψ ↦
                let m := Φ.length
                normHyps K [m - 2] (witness (atPos (Γ.length - 1)) "unnamedNum"
                  (K.byHyp (m - 1))) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ)
      let d ← linkK K "cataWalk: the binder's expansion" (decideIn K (fun Γ ↦
          pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev" [atomAt 0 (cs Γ), wp 2 Γ]])
        (witness cs "unnamedVar" (hypOr iI))
        (linkK K "cataWalk: the binder abbreviated" abbreviated)) Γ Φ claim
      dCut claim d (K.exE <| K.conjE <| K.conjE <| K.conjE fun Γ Φ ψ ↦
        let m := Φ.length
        normHyps K [m - 6, m - 4, m - 2, m - 1] (k (atPos (Γ.length - 1))) Γ Φ ψ) Γ Φ ψ
    -- the empty walk: after the walk's context's positions, the field types, the children, the
    -- results, the pair's first component, the results' type, the environment, the named context
    -- and the kernel's context
    let nilCase : Deducer := intros fun Γ₀ Φ₀ ψ₀ ↦
      let c := wp 6
      let (fts, ts) := (wp 10, wp 11)
      let rvs := wp 7
      let cx (Γ : List Tree) : Term := consT treeTy (fieldsEntry P) (wp 17 Γ)
      let env (Γ : List Tree) : Term := consT treeTy (pc P "Eval.ofList"
        [leafT (numeral Kernel.Label.tyTree), quotesT P (ts Γ)]) (wp 16 Γ)
      let kc (Γ : List Tree) : Term := consT treeTy (listTK P (wp 3 Γ)) (wp 18 Γ)
      let body : Deducer := linkK K "cataWalk: the body" <|
        dAllE L K.G K.E 6 (cx Γ₀) <| K.allEΓ env <| K.allEΓ kc <|
        K.impE (K.byHyp hEnv) <| K.impE (byStep hTy) <| K.impE (K.byHyp hRes) <|
        K.impE (K.byHyp hKer) <| K.impE (K.byHyp hCx) <| fun Γ Φ ψ ↦
          dRwBy (evalRw K.G K.E (K.rules Φ ++ steps) .full) byLast Γ Φ ψ
      let noRest : Deducer := fun Γ Φ ψ ↦ K.listCase treeTy (rvs Γ)
        (fun Γ Φ ψ ↦ K.listCase treeTy (ts Γ) body (refute "children remaining" hOk) Γ Φ ψ)
        (refute "a remaining variable" hTy) Γ Φ ψ
      let E' := wp 5
      let raw (Γ : List Tree) : Term := apps childT [c Γ, leafT (numeral 3)]
      let nums := wp 2
      let cx0 := wp 17
      let negated : Deducer := dImpI L fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ
      let aC := pc P "Datatype.aC" []
      let aT := pc P "Datatype.aT" []
      -- the scope of the walk's named context after the children remaining's entry
      let scope0 (Γ : List Tree) : Term := scopeOf P (nums Γ) (cx0 Γ)
      let (tys, names) := (wp 3, wp 1)
      let absent := absentAt hNums hNames hCx scope0 cx
      -- the expansion of the numeral abbreviations at a form
      let en (t : List Tree → Term) (Γ : List Tree) : Term := pc P "Reader.expandNums" [nums Γ, t Γ]
      let rF := en rForm
      let foldRaw (Γ : List Tree) : Term := (cataFrags P (rForm Γ) (drForm Γ)).2.2
      -- the remaining children's variable, of position pR, its results' list where flagged, the
      -- remaining children's otherwise
      let restVar (flag : Bool) (pR : ℕ) : Deducer :=
        let r := atPos pR
        let bodyEx (Γ : List Tree) : Term := pc P "Reader.expandNums" [nums Γ, wp 9 Γ]
        -- flagged, the binding's resolution: the expansions of the fold and of the annotation,
        -- the list type of the result type's form, the reader's case of bindings,
        -- the result type's reading decided, absent refuting the resolution, and the fold's
        -- resolution ({name}`foldRes`)
        let foldBinding (k : Deducer) : Deducer :=
          -- the annotation's expansion first, which occurs in the fold's, as the rules rewrite
          -- innermost first
          linkK K "cataWalk: the fold's expansion" <|
          applyThm K "listNums" (fun Γ ↦ [rForm Γ, drForm Γ, nums Γ])
            ((cataAtoms P).map fun _ ↦ negated) <| normLastK K <|
          applyThm K "foldNums" (fun Γ ↦ [rForm Γ, drForm Γ, nums Γ])
            ((cataAtoms P).map fun _ ↦ negated) <| normLastK K <|
          linkK K "cataWalk: the fold's binding" <|
          applyThm K "letRes" (fun Γ ↦ [bodyEx Γ, en foldRaw Γ,
            en (fun Γ ↦ pc P "Datatype.sList" [rForm Γ]) Γ, en r Γ,
            consT treeTy (fieldsName P) (scope0 Γ), tys Γ, names Γ]) [] <| normLastK K <|
          decideIn K (fun Γ ↦ pc P "Prelude.isSome" [pc P "Reader.readType" [tys Γ, rF Γ]])
            (refute "the result type unread" hRes) <|
          linkK K "cataWalk: the fold resolved" <|
          applyThm K "foldRes" (fun Γ ↦ [scope0 Γ, tys Γ, names Γ, wp 15 Γ, rF Γ])
            ([K.solve 3, linkK K "cataWalk: the split's index" (eqHyp hIdx)] ++
              absent "aUnitV" ++ [K.solve 3]) <|
          normLastK K k
        -- the binding at the binder's expansion, an atom of the characters csB
        let restFlow (csB : List Tree → Term) : Deducer :=
          let bodyRes (Γ : List Tree) : Term := pc P "Reader.resolve" [wp 3 Γ, wp 1 Γ,
            bodyEx Γ, consT treeTy (nodeT (Term.pair (numeral 0) (csB Γ)))
              (consT treeTy (fieldsName P) (scope0 Γ))]
          -- the walk's steps at the remaining variable: the binding of the remaining variables
          -- unfolded, the variable's at the top
          let unfoldRest : List Internal.NormRule := [.delta (P.idx "Typing.bindRest")]
          let presentTy : Deducer := fun Γ Φ ψ ↦
            let iTy := Φ.length - 1
            dRwHyp (evalRw K.G K.E (K.rulesEx Φ hRes) .full) hRes (fun Γ₀ Φ ψ ↦ do
              let (g, kc, x) ← apps3Of (P.idx "Check.typeIn") (← Φ[hKer]?)
              let (y, _) ← evalRw K.G K.E (K.rules Φ) .full Γ₀ Φ x
              let [f, e] ← nodeKidsT y | none
              let [B, rB] ← nodeKidsT f | none
              let [Pg, F] := ψ.children | none
              let [body] := F.children | none
              let [f₁, _] := body.children | none
              let [fs, env] := f₁.children | none
              let [lvl] := fs.children | none
              let [_, dR] := lvl.children | none
              let [R] := dR.children | none
              let lower (u : Term) : Term := Term.subst u fun j ↦ v (j - 1)
              let (R, env) := (lower R, lower env)
              let w (u : Term) (Γ : List Tree) : Term := sh (Γ.length - Γ₀.length) u
              -- the typing's binding's arguments, its type the variable's entry's
              let hN ← Φ[iTy]?
              let some [envB, xB, tyB, kB] := (appsOf K.G (P.idx "Typing.bindVar") hN).head?.map
                  spineArgs
                | dbgTrace "cataWalk: no binding of the remaining variable" fun _ ↦ none
              let entry (Γ : List Tree) : Term := pc P "Typing.abbr"
                [pc P "Typing.atomName" [r Γ], pc P "Prelude.get" [w tyB Γ]]
              let byLast : Deducer := fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ
              let yv (Γ : List Tree) : Term := atPos Γ₀.length Γ
              let qY (Γ : List Tree) : Term := treeList P (quotesT P (ts Γ))
              let isQ (q : List Tree → Term) (Γ : List Tree) : Term :=
                Term.lam treeTy (Term.eq (v 0) (sh 1 (q Γ)))
              let fieldA (Γ : List Tree) : Term :=
                pc P "Prelude.get" [pc P "Typing.fieldTy" [E' Γ, raw Γ]]
              -- flagged, the value's predicate: related at the list type of the result type
              let listR (Γ : List Tree) : Term := nodeT (Term.pair (numeral Kernel.Label.tyList)
                (consT treeTy (Rty Γ) (nilT treeTy)))
              let relQ (Γ : List Tree) : Term := T.relT (w R Γ) (listR Γ)
              -- the remaining children's test at the datatype's atom, the raw field type equal
              -- to it ({lit}`equalSound`)
              let atD (k : Deducer) : Deducer :=
                K.cutThm "equalSound" (fun Γ ↦ [raw Γ]) <| K.allEΓ (atPos 3) <|
                  K.impE (K.solve 3) <| normLastK K k
              -- the remaining results each related ({name}`resultsRel`)
              let resultsOk : Deducer := linkK K "cataWalk: the remaining results related" <|
                K.cutThm "resultsRel" (fun Γ ↦ [ts Γ]) <| K.allEΓ E' <| K.allEΓ (atPos 3) <|
                K.allEΓ (w R) <| K.allEΓ Rty <| K.allEΓ (wp 12) <|
                K.impE (K.byHyp hRel) <|
                K.impE (linkK K "cataWalk: the remaining children's tests" (atD (K.byHyp hOk))) <|
                K.impE (K.byHyp hLen) byLast
              -- the fold's convergence ({name}`foldConv`)
              let foldVal : Deducer := linkK K "cataWalk: the fold's value" <|
                applyThm K "foldConv" (fun Γ ↦ [wp 16 Γ, treeList P (quotesT P (ts Γ)), wp 15 Γ,
                    wp 13 Γ, wp 14 Γ, wp 12 Γ, Rty Γ, tys Γ, pc P "Datatype.thTy" [rF Γ],
                    pc P "Datatype.sList" [rF Γ], rF Γ, w R Γ])
                  [K.solve 3, linkK K "cataWalk: the split at its index" (eqHyp hEnvAt),
                    resultsOk] byLast
              -- the children's quotations related at the raw field type's list type
              let relY : Deducer := K.cutThm "relOfListT" (fun Γ ↦ [quotesT P (ts Γ)]) <|
                K.allEΓ (fun _ ↦ leafT (numeral Kernel.Label.tyTree)) <| K.allEΓ (w R) <|
                K.allEΓ fieldA <|
                K.impE (linkK K "cataWalk: the children's quotations related" <|
                  K.cutThm "quotesFieldRel" (fun Γ ↦ [ts Γ]) <| K.allEΓ raw <|
                  -- the markers the hypothesis of index 0 as written, which supplies no rule
                  K.allEΓ E' <| K.allEΓ (w R) <| K.impE dHyp <|
                  K.impE (linkK K "cataWalk: the raw type present" (K.solve 3)) <|
                  K.impE (linkK K "cataWalk: the remaining children's test" (K.byHyp hOk))
                    byLast)
                  byLast
              let envOk (iQ : ℕ) : Deducer := applyThm K "envTCons" (fun Γ ↦ [yv Γ, entry Γ,
                  w env Γ, cx Γ, w R Γ])
                [K.byHyp hEnv, linkK K "cataWalk: the remaining variable's value related"
                  (if flag then K.byHyp iQ else relY)] byLast
              let cxOk : Deducer :=
                decided (fun Γ ↦ pc P "Typing.nameOk" [E' Γ, pc P "Typing.atomName" [r Γ]])
                  (refute "the remaining variable's name not admitted" hTy) <|
                applyThm K "cxTCons" (fun Γ ↦ [pc P "Prelude.get" [w tyB Γ],
                    pc P "Typing.atomName" [r Γ], E' Γ, cx Γ])
                  [linkK K "cataWalk: the remaining variable's name admitted" (K.solve 3),
                    K.byHyp hCx] byLast
              -- the typing's binding rewritten by its equation ({lit}`bindVarEq`)
              let bound (k : Deducer) : Deducer :=
                decided (fun Γ ↦ pc P "Typing.clauseVar" [E' Γ, r Γ])
                  (refute "the remaining variable at its node" hTy) <|
                applyThm K "bindVarEq" (fun Γ ↦ [w kB Γ, w tyB Γ, w xB Γ, w envB Γ])
                  [K.solve 3, K.solve 3] <| normLastK K k
              let bodyAt (iTr : ℕ) : Deducer := fun Γ Φ ψ ↦
                let iQ := Φ.length - 1
                (dAllE L K.G K.E 6 (consT treeTy (entry Γ) (cx Γ)) <|
                K.allEΓ (fun Γ ↦ consT treeTy (yv Γ) (w env Γ)) <|
                K.allEΓ (fun Γ ↦ consT treeTy (w B Γ) (w kc Γ)) <|
                K.impE (linkK K "cataWalk: the extended environment" (envOk iQ)) <|
                K.impE (linkK K "cataWalk: the body's typing"
                  (bound fun Γ Φ ψ ↦ K.byHyp iTy Γ Φ ψ)) <|
                K.impE (linkK K "cataWalk: the body resolved" (K.solve 3)) <|
                K.impE (linkK K "cataWalk: the body's kernel typing" (K.byHyp iTr)) <|
                K.impE (linkK K "cataWalk: the extended context's names" cxOk) <|
                linkK K "cataWalk: the body's soundness" fun Γ Φ ψ ↦
                  let iC := Φ.length - 1
                  dRwBy (evalRw K.G K.E (K.rules Φ ++ unfoldRest) .full)
                    (bound fun Γ Φ ψ ↦ dRwHyp (evalRw K.G K.E (K.rulesEx Φ iC) .full) iC
                      (dRwBy (evalRw K.G K.E (K.rules Φ) .full) dHyp) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
              (applyThm K "letTyped" (fun _ ↦ [e, rB, B, kc, g]) [K.byHyp hKer] <| K.conjE <|
                fun Γ Φ ψ ↦
                let iTr := Φ.length - 2
                applyThm K "letConv" (fun Γ ↦ [w env Γ, w e Γ, w rB Γ, w B Γ,
                    if flag then relQ Γ else isQ qY Γ, w Pg Γ, w R Γ])
                  [if flag then foldVal else linkK K "cataWalk: the children's value" <|
                    K.cutThm "var0Conv" (fun Γ ↦ [wp 16 Γ, qY Γ, w R Γ])
                      byLast,
                    linkK K "cataWalk: the remaining variable's binding" <| dAllI L <| dImpI L <|
                      normLastK K (bodyAt iTr)] byLast Γ Φ ψ) Γ₀ Φ ψ) Γ Φ ψ
          let present : Deducer := fun Γ Φ ψ ↦
            dRwHyp (evalRw K.G K.E (K.rulesEx Φ hTy ++ unfoldRest) .full) hTy presentTy Γ Φ ψ
          -- the binding's expansion, then its resolution
          let resolution (k : Deducer) : Deducer := if flag then
              applyThm K "letNums" (fun Γ ↦ [wp 9 Γ, foldRaw Γ,
                pc P "Datatype.sList" [rForm Γ], r Γ, nums Γ]) [negated] <| normLastK K <|
              foldBinding k
            else
              applyThm K "letNums" (fun Γ ↦ [wp 9 Γ, aC, pc P "Datatype.sList" [aT], r Γ,
                nums Γ]) [negated] <| normLastK K <| linkK K "cataWalk: rest restVarRes" <|
              applyThm K "restVarRes" (fun Γ ↦ [bodyEx Γ, csB Γ, scope0 Γ,
                wp 3 Γ, wp 1 Γ]) [] <| normLastK K k
          linkK K "cataWalk: rest letNums" <| resolution <|
          decideOpt K bodyRes (linkK K "cataWalk: the body unresolved" fun Γ Φ ψ ↦
              dRwHyp (evalRw K.G K.E (K.rulesEx Φ hRes) .full) hRes
                (fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ) Γ Φ ψ)
            (linkK K "cataWalk: the body resolved" present)
        -- the binder an atom of the characters of position pC, its characters fixed by its being
        -- a source form's
        let atomCase (pC iI : ℕ) : Deducer :=
          let cs := atPos pC
          let charsFix (k : Deducer) : Deducer := linkK K "cataWalk: charsFix" fun Γ Φ ψ ↦
            dRwHyp (evalRw K.G K.E (K.rulesEx Φ 3) .full) 3 (linkK K "cataWalk: conjE" fun Γ Φ ψ ↦
              dConjE L (Φ.length - 1) (fun Γ Φ ψ ↦
                -- the head an atom, its characters fixed
                dImpE L (Φ.length - 2) (linkK K "cataWalk: the remaining variable an atom"
                  (K.solve 3)) (fun Γ Φ ψ ↦
                let fixedHead := Φ.length - 1
                (linkK K "cataWalk: charsFixedEq" <|
                  K.cutThm "charsFixedEq" (fun Γ ↦ [cs Γ, nums Γ]) <|
                  K.impE (linkK K "cataWalk: the head fixed" fun Γ Φ ψ ↦
                    K.byHyp fixedHead Γ Φ ψ) <| normLastK K k) Γ Φ ψ)
                Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
          charsFix (expansion 0 r cs iI restFlow)
        -- unflagged, the raw field type present, absent refuting the typing
        (if flag then id else decideIn K (fun Γ ↦ pc P "Prelude.isSome"
            [pc P "Typing.fieldTy" [E' Γ, raw Γ]]) (refute "the raw field type absent" hTy)) <|
        varAtom hTy r "the remaining variable no clause's" atomCase
      -- the remaining children's entry, of position pE: a list of the variable and its flag, an
      -- atom of a numeral's characters equal to the test that the raw field type is the
      -- datatype's, else the typing's walk absent
      let entryRest (pE : ℕ) : Deducer := entryCases hTy hFlagR raw pE fun flag pX ↦
        linkK K (if flag then "cataWalk: flagged" else "cataWalk: unflagged") (restVar flag pX)
      let rest : Deducer := linkK K "cataWalk: the remaining children's variable" fun Γ Φ ψ ↦
        K.listCase treeTy (rvs Γ) (refute "no remaining variable" hTy)
          (fun Γ Φ ψ ↦ K.listCase treeTy (atPos (Γ.length - 1) Γ) (entryRest (Γ.length - 2))
            (refute "a second remaining variable" hTy) Γ Φ ψ) Γ Φ ψ
      K.listCase treeTy (fts Γ₀)
        (decideIn K (fun Γ ↦ apps childT [c Γ, leafT (numeral 2)])
          (linkK K "cataWalk: no remaining children" noRest) rest)
        (refute "a field type remaining" hTy) Γ₀ Φ₀ ψ₀
    let r₀ : Option Internal.Deriv := linkK K "cataWalk: no fields" nilCase
      (cataWalkCtx T).tail [] (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
    -- the lengths' hypothesis of index h refuted, one comparison true by the comparisons of
    -- lengths at constructions
    let KN : Kit := { K with more := K.more ++ lenRules.filter fun nm ↦ 0 < ix nm ∧ ix nm < E.size }
    let lenFalse (h : ℕ) : Deducer := linkK K "cataWalk: the lengths unequal" <| dConjE L h
      fun Γ Φ ψ ↦
      let refuted (i : ℕ) : Deducer := dImpE L i (KN.solve 3) fun Γ Φ ψ ↦
        K.hypFalse (Φ.length - 1) Γ Φ ψ
      (refuted (Φ.length - 2) Γ Φ ψ).orElse fun _ ↦ refuted (Φ.length - 1) Γ Φ ψ
    -- a fixed field's entry and the rest: in the context after the quantifiers, the entry at
    -- position 14 and the rest of the entries at 15, then the quantified variables from 16; the
    -- induction hypothesis the first hypothesis
    let o := 1
    let (cTy, cOk, cLen, cRel) := (hTy + o, hOk + o, hLen + o, hRel + o)
    let cFlag := 4 + o
    let cq (i : ℕ) : List Tree → Term := atPos (i + 16)
    let (cIdx, cRes, cKer, cEnvAt) := (hIdx + o, hRes + o, hKer + o, hEnvAt + o)
    let (nums, tys, names, E') := (wp 2, wp 3, wp 1, wp 5)
    let cx0 := cq 7
    let cx (Γ : List Tree) : Term := consT treeTy (fieldsEntry P) (cx0 Γ)
    let scope0 (Γ : List Tree) : Term := scopeOf P (nums Γ) (cx0 Γ)
    let fSc (Γ : List Tree) : Term := consT treeTy (fieldsName P) (scope0 Γ)
    let uSc (Γ : List Tree) : Term :=
      consT treeTy (atomNameT (pc P "Datatype.aU" [])) (fSc Γ)
    let en (t : List Tree → Term) (Γ : List Tree) : Term := pc P "Reader.expandNums" [nums Γ, t Γ]
    let (rF, drF) := (en rForm, en drForm)
    let ms (Γ : List Tree) : Term := pc P "Typing.envMs" [E' Γ]
    let negated : Deducer := dImpI L lastFalse
    let aC := pc P "Datatype.aC" []
    let aT := pc P "Datatype.aT" []
    -- the walk's erasure at a list of the fixed fields' entries, in the current context
    let erAt (xs : List Tree → Term) (Γ : List Tree) : Term :=
      Term.subst w.er fun j ↦ if j = 0 then xs Γ else atPos (14 - j) Γ
    let erRest := erAt (atPos 15)
    let restEx := en erRest
    -- the resolution's hypothesis refuted, the reader's case of bindings unfolded
    let refuteRes (msg : String) : Deducer := linkK K s!"cataWalk: {msg}" fun Γ Φ ψ ↦
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ cRes ++ [.thm (ix "letRes") []]) .full) cRes
        (dFalse L dHyp) Γ Φ ψ
    -- the field of the entry's variable of position pX, flagged or not, the field type of
    -- position pF, the child of position pT and the result of position pR, each before the
    -- rest of its list
    let consField (flag : Bool) (pX pF pT pR : ℕ) : Deducer :=
      let (x, ft, t) := (atPos pX, atPos pF, atPos pT)
      -- the forms of the fragments, in the current context
      let frags (Γ : List Tree) : Term × Term × Term := cataFrags P (rForm Γ) (drForm Γ)
      let tailB (Γ : List Tree) : Term := pc P "Datatype.sLet" [aC, pc P "Datatype.sList" [aT],
        pc P "Datatype.sTailOf" [aC], erRest Γ]
      let inner (Γ : List Tree) : Term := if flag
        then pc P "Datatype.sLet" [x Γ, rForm Γ, (frags Γ).2.1, tailB Γ]
        else pc P "Datatype.sLet" [x Γ, aT, pc P "Datatype.sHeadOf" [aC], tailB Γ]
      -- the rest resolved, the binder an atom of the characters cs and the rest's characters
      -- fixed the hypothesis iR: the kernel's term in normal form, the bindings of the split, of
      -- the field's variable and of the children remaining around the rest's term, its typing
      -- split at the three ({lit}`letTyped`), and their convergence ({lit}`letConv`): the split
      -- by {name}`splitConv`, the variable forced ({name}`forceConv`) or the head
      -- ({name}`cataConvs`), the tail; then the induction hypothesis at the rests
      let present (iR iOk : ℕ) : Deducer := fun Γ Φ ψ ↦
        dRwHyp (evalRw K.G K.E (K.rulesEx Φ cRes) .full) cRes (fun Γ₀ Φ ψ ↦ do
          let (g, kc0, xK) ← apps3Of (P.idx "Check.typeIn") (← Φ[cKer]?)
          let (y, _) ← evalRw K.G K.E (K.rules Φ) .full Γ₀ Φ xK
          let [f1, eQ] ← nodeKidsT y | none
          let [Aq, b1] ← nodeKidsT f1 | none
          let [f2, eX] ← nodeKidsT b1 | none
          let [Ax, b2] ← nodeKidsT f2 | none
          let [f3, eT] ← nodeKidsT b2 | none
          let [Ac, rK] ← nodeKidsT f3 | none
          -- the goal's predicate, relation's context and environment, the latter two lowered
          -- past the level's binder
          let [Pg, F] := ψ.children | none
          let [body] := F.children | none
          let [f₁, _] := body.children | none
          let [fs, env] := f₁.children | none
          let [lvl] := fs.children | none
          let [_, dR] := lvl.children | none
          let [R] := dR.children | none
          let lower (u : Term) : Term := Term.subst u fun j ↦ v (j - 1)
          let (R, env) := (lower R, lower env)
          let w (u : Term) (Γ : List Tree) : Term := sh (Γ.length - Γ₀.length) u
          let (ftsR, tsR, r, rsR) := (atPos (pF + 1), atPos (pT + 1), atPos pR, atPos (pR + 1))
          -- the values the three bindings bind, the variables after this context
          let qv (Γ : List Tree) : Term := atPos Γ₀.length Γ
          let xv (Γ : List Tree) : Term := atPos (Γ₀.length + 1) Γ
          let quote (u : Term) : Term := pc P "Eval.valQuote" [u]
          let splitVal (Γ : List Tree) : Term := nodeT (Term.pair (numeral Kernel.Label.pair)
            (consT treeTy (r Γ) (consT treeTy (pc P "Eval.ofList" [cq 4 Γ, rsR Γ])
              (nilT treeTy))))
          let isQ (q : List Tree → Term) (Γ : List Tree) : Term :=
            Term.lam treeTy (Term.eq (v 0) (sh 1 (q Γ)))
          let qT (Γ : List Tree) : Term := treeList P (quotesT P (tsR Γ))
          let thF (Γ : List Tree) : Term := pc P "Datatype.thTy" [rF Γ]
          let lvT (Γ : List Tree) : Term := pc P "Eval.ofList"
            [leafT (numeral Kernel.Label.tyTree), quotesT P (cq 1 Γ)]
          -- the field's type: the result type, flagged, else the field type's
          let fieldA (Γ : List Tree) : Term := if flag then Rty Γ
            else pc P "Prelude.get" [pc P "Typing.fieldTy" [E' Γ, ft Γ]]
          let xEntry (Γ : List Tree) : Term :=
            pc P "Typing.abbr" [pc P "Typing.atomName" [x Γ], fieldA Γ]
          let qEntry (Γ : List Tree) : Term := splitEntry P (Rty Γ)
          -- the field type the datatype's atom, flagged ({lit}`equalSound`)
          let atD (k : Deducer) : Deducer :=
            K.cutThm "equalSound" (fun Γ ↦ [ft Γ]) <| K.allEΓ (atPos 3) <|
              K.impE (K.solve 3) <| normLastK K k
          -- the head result related at the index zero, the child a member: the field's test at
          -- the datatype's atom, by the field type's equation
          let relHead : Deducer := linkK K "cataWalk: the field's result related" <| atD <|
            normHyps K [iOk] <| fun Γ Φ ψ ↦ dAllE L K.G K.E cRel bnilT
              (K.impE (linkK K "cataWalk: the head a member" (K.solve 3)) <| K.conjE
                (linkK K "cataWalk: the head's result" fun Γ Φ ψ ↦
                  (byLast Γ Φ ψ).orElse fun _ ↦ normLastK K byLast Γ Φ ψ)) Γ Φ ψ
          -- the split's convergence ({name}`splitConv`)
          let splitV : Deducer := linkK K "cataWalk: the split's value" <|
            applyThm K "splitConv" (fun Γ ↦ [cq 6 Γ, lvT Γ, cq 5 Γ, cq 3 Γ, cq 4 Γ, r Γ, rsR Γ,
                tys Γ, names Γ, fSc Γ, thF Γ, pc P "Datatype.splitTy" [rF Γ],
                pc P "Datatype.sList" [thF Γ], drF Γ, w R Γ])
              [K.solve 3, eqHyp cEnvAt] byLast
          -- the variable's convergence: forced, related at the result type, else the head
          let qX (Γ : List Tree) : Term := if flag then T.relT (w R Γ) (Rty Γ)
            else isQ (fun Γ ↦ quote (t Γ)) Γ
          let xV : Deducer := linkK K "cataWalk: the variable's value" <| if flag then
              applyThm K "forceConv" (fun Γ ↦ [w env Γ, r Γ, pc P "Eval.ofList" [cq 4 Γ, rsR Γ],
                Rty Γ, w R Γ]) [K.solve 3, relHead] byLast
            else K.cutThm "headConvQ" (fun Γ ↦ [qv Γ, cq 6 Γ, quotesT P (tsR Γ), t Γ, w R Γ])
              byLast
          -- the tail's convergence
          let tV : Deducer := linkK K "cataWalk: the tail's value" <|
            K.cutThm "tailConvQ" (fun Γ ↦ [cq 6 Γ, quotesT P (tsR Γ), t Γ, qv Γ, xv Γ, w R Γ])
              byLast
          -- the induction hypothesis at the rests
          let ih (iTr : ℕ) : Deducer :=
            let env' (Γ : List Tree) : Term := consT treeTy (xv Γ) (consT treeTy (qv Γ) (w env Γ))
            let cx' (Γ : List Tree) : Term := consT treeTy (xEntry Γ) (consT treeTy (qEntry Γ)
              (cx Γ))
            let kc' (Γ : List Tree) : Term := consT treeTy (w Ax Γ) (consT treeTy (w Aq Γ)
              (w kc0 Γ))
            let KN2 : Kit :=
              { K with more := K.more ++ ["nthTwo3", "nthTwo4", "nthOne2", "nthOne3"] }
            let fieldsNm : Term := pc P "Typing.boundName" [pc P "Typing.kwFields" []]
            let implOk (Γ : List Tree) (n : Term) : Term :=
              pc P "Typing.nameOk" [E' Γ, n]
            let cxOk : Deducer := fun Γ Φ ψ ↦
              -- the entry's name admitted as a binder's or, not, the implementation's
              let impl : Deducer := fun Γ Φ ψ ↦ (K.solve 3 Γ Φ ψ).orElse fun _ ↦ KL.solve 3 Γ Φ ψ
              let consAt (ty n : List Tree → Term) (cxT : List Tree → Term) (prev : Deducer) :
                  Deducer :=
                applyThm K "cxTCons" (fun Γ ↦ [ty Γ, n Γ, E' Γ, cxT Γ])
                  [decided (fun Γ ↦ implOk Γ (n Γ)) impl (K.solve 3), prev] byLast
              (consAt (fun _ ↦ pc P "Typing.tyList" [pc P "Typing.tyT" []]) (fun _ ↦ fieldsNm)
                (fun Γ ↦ consT treeTy (xEntry Γ) (consT treeTy (qEntry Γ) (cx Γ)))
                (consAt fieldA (fun Γ ↦ pc P "Typing.atomName" [x Γ])
                  (fun Γ ↦ consT treeTy (qEntry Γ) (cx Γ))
                  (consAt (fun Γ ↦ pc P "Typing.tyProd" [thunkTy P (Rty Γ),
                      pc P "Typing.tyList" [thunkTy P (Rty Γ)]])
                    (fun _ ↦ pc P "Typing.boundName" [pc P "Typing.kwSplit" []]) cx
                    (hypOr (hCx + o))))) Γ Φ ψ
            -- an entry's name one the erasure binds, by the index's equations
            let implName (msg : String) : Deducer := linkK K s!"cataWalk: {msg} bound" fun Γ Φ ψ ↦
              (K.solve 3 Γ Φ ψ).orElse fun _ ↦ KL.solve 3 Γ Φ ψ
            let envOk : Deducer :=
              applyThm K "envTConsImpl" (fun Γ ↦ [qT Γ, fieldsEntry P, env' Γ, cx' Γ, w R Γ])
                [linkK K "cataWalk: the variable's entry related" <|
                  applyThm K "envTCons" (fun Γ ↦ [xv Γ, xEntry Γ, consT treeTy (qv Γ) (w env Γ),
                    consT treeTy (qEntry Γ) (cx Γ), w R Γ])
                  [linkK K "cataWalk: the split's entry related" <|
                    applyThm K "envTConsImpl" (fun Γ ↦ [qv Γ, qEntry Γ, w env Γ, cx Γ, w R Γ])
                    [hypOr (hEnv + o), implName "the split's name"] byLast,
                    linkK K "cataWalk: the variable related" (if flag then
                      fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ
                    else applyThm K "fieldRel" (fun Γ ↦ [t Γ, ft Γ, E' Γ, w R Γ])
                      [K.byNorm, K.solve 3, K.solve 3] byLast)] byLast,
                  implName "the children's name"] byLast
            -- the walk's typing at the rest, the field's binding by its equation
            -- ({lit}`bindVarEq`)
            let bound (h : Deducer → Deducer) : Deducer := fun Γ Φ ψ ↦ do
              let (hN, _) ← evalRw K.G K.E (K.rules Φ) .full Γ Φ (← Φ[cTy]?)
              let some [env'', x'', ty'', k''] := (appsOf K.G (P.idx "Typing.bindVar")
                  hN).head?.map spineArgs
                | dbgTrace "cataWalk: no binding of the field's variable" fun _ ↦ none
              applyThm K "bindVarEq" (fun _ ↦ [k'', ty'', x'', env''])
                [linkK K "cataWalk: the field's type present" (K.solve 3),
                  linkK K "cataWalk: a clause's variable" (K.solve 3)] (normLastK K (h byLast))
                Γ Φ ψ
            dImpE L 0 (linkK K "cataWalk: the markers" (hypOr (0 + o))) <|
            K.impE (linkK K "cataWalk: the keywords" (hypOr (1 + o))) <|
            K.impE (linkK K "cataWalk: the rest's characters" (hypOr iR)) <|
            K.impE (linkK K "cataWalk: the remaining variables' characters" (hypOr (3 + o))) <|
            K.impE (linkK K "cataWalk: the rest's flags" fun Γ Φ ψ ↦
              dRwHyp (evalRw K.G K.E (K.rulesEx Φ cFlag) .full) cFlag (K.conjE byLast) Γ Φ ψ) <|
            K.impE (linkK K "cataWalk: the remaining variables' flags" (hypOr (5 + o))) <|
            K.impE (linkK K "cataWalk: the body" (hypOr (6 + o))) <|
            K.impE (linkK K "cataWalk: the abbreviations" (hypOr (7 + o))) <|
            K.impE (linkK K "cataWalk: the names" (hypOr (8 + o))) <|
            K.allEΓ ftsR <| K.allEΓ tsR <| K.allEΓ rsR <| K.allEΓ r <| K.allEΓ (cq 4) <|
            K.allEΓ (fun _ ↦ numeral 2) <| K.allEΓ env' <| K.allEΓ cx' <| K.allEΓ kc' <|
            K.impE (linkK K "cataWalk: the rest's typing" (bound fun _ ↦ K.byHyp cTy)) <|
            K.impE (linkK K "cataWalk: the rest's test" (K.byHyp cOk)) <|
            K.impE (linkK K "cataWalk: the rests' lengths" (KN.byHyp cLen)) <|
            K.impE (linkK K "cataWalk: the rests related" <|
              applyThm K "relatedTail" (fun Γ ↦ [rsR Γ, r Γ, tsR Γ, t Γ, Rty Γ, w R Γ, atPos 3 Γ,
                E' Γ]) [K.solve 3, K.byHyp cRel] byLast) <|
            K.impE (linkK K "cataWalk: the split's index" (KL.solve 3)) <|
            K.impE (linkK K "cataWalk: the split's value" (KN2.solve 3)) <|
            K.impE (linkK K "cataWalk: the split's type" (KN2.solve 3)) <|
            K.impE (linkK K "cataWalk: the environment" envOk) <|
            K.impE (linkK K "cataWalk: the context's names" cxOk) <|
            K.impE (linkK K "cataWalk: the rest resolved" (K.solve 3)) <|
            K.impE (linkK K "cataWalk: the rest's kernel typing" (K.byHyp iTr)) <|
            linkK K "cataWalk: the rest's soundness" fun Γ Φ ψ ↦
              let iC := Φ.length - 1
              (fun Γ Φ ψ ↦ do
                let (gN, _) ← evalRw K.G K.E (K.rules Φ) .full Γ Φ ψ
                let some [env'', x'', ty'', k''] := (appsOf K.G (P.idx "Typing.bindVar")
                    gN).head?.map spineArgs
                  | dbgTrace "cataWalk: no binding in the goal" fun _ ↦ none
                (applyThm K "bindVarEq" (fun _ ↦ [k'', ty'', x'', env''])
                  [K.solve 3, K.solve 3] <| normLastK K fun Γ Φ ψ ↦
                  dRwHyp (evalRw K.G K.E (K.rulesEx Φ iC) .full) iC
                    (dRwBy (evalRw K.G K.E (K.rules Φ) .full) dHyp) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
          -- the three bindings' convergence, each value its predicate's
          let inner3 (iTr : ℕ) : Deducer :=
            applyThm K "letConv" (fun Γ ↦ [consT treeTy (xv Γ) (consT treeTy (qv Γ) (w env Γ)),
                w eT Γ, w rK Γ, w Ac Γ, isQ qT Γ, w Pg Γ, w R Γ])
              [tV, linkK K "cataWalk: the rest's binding" <| dAllI L <| dImpI L <| normLastK K <|
                ih iTr] byLast
          let inner2 (iTr : ℕ) : Deducer :=
            applyThm K "letConv" (fun Γ ↦ [consT treeTy (qv Γ) (w env Γ), w eX Γ, w b2 Γ,
                w Ax Γ, qX Γ, w Pg Γ, w R Γ])
              [xV, linkK K "cataWalk: the tail's binding" <| dAllI L <| dImpI L <| normLastK K <|
                inner3 iTr] byLast
          (applyThm K "letTyped" (fun _ ↦ [eQ, b1, Aq, kc0, g]) [K.byHyp cKer] <| K.conjE <|
            fun Γ Φ ψ ↦
            applyThm K "letTyped" (fun _ ↦ [eX, b2, Ax, consT treeTy Aq kc0, g])
              [K.byHyp (Φ.length - 2)] (K.conjE fun Γ Φ ψ ↦
              applyThm K "letTyped" (fun _ ↦ [eT, rK, Ac, consT treeTy Ax (consT treeTy Aq kc0),
                  g]) [K.byHyp (Φ.length - 2)] (K.conjE fun Γ Φ ψ ↦
                let iTr := Φ.length - 2
                applyThm K "letConv" (fun Γ ↦ [w env Γ, w eQ Γ, w b1 Γ, w Aq Γ, isQ splitVal Γ,
                    w Pg Γ, w R Γ])
                  [splitV, linkK K "cataWalk: the variable's binding" <| dAllI L <| dImpI L <|
                    normLastK K <| inner2 iTr] byLast Γ Φ ψ) Γ Φ ψ) Γ Φ ψ) Γ₀ Φ ψ) Γ Φ ψ
      -- the binding at the binder's expansion, an atom of the characters cs
      let binderFlow (cs : List Tree → Term) (iR iOk : ℕ) : Deducer :=
        let restRes (Γ : List Tree) : Term := pc P "Reader.resolve" [tys Γ, names Γ, restEx Γ,
          consT treeTy (fieldsName P) (consT treeTy (nodeT (Term.pair (numeral 0) (cs Γ)))
            (consT treeTy (splitName P) (fSc Γ)))]
        let nums3 (nm : String) (k : Deducer) : Deducer :=
          applyThm K nm (fun Γ ↦ [rForm Γ, drForm Γ, nums Γ])
            ((cataAtoms P).map fun _ ↦ negated) <| normLastK K k
        -- a resolution's hypothesis refuted, its normal form with the bindings' equations none
        let refuteNone (msg : String) : Deducer := linkK K s!"cataWalk: {msg}" fun Γ Φ ψ ↦
          dRwHyp (evalRw K.G K.E (K.rulesEx Φ cRes) .full) cRes
            (fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ) Γ Φ ψ
        linkK K "cataWalk: the field's binding" <|
        applyThm K "letNums" (fun Γ ↦ [inner Γ, (frags Γ).1,
          pc P "Datatype.splitTy" [rForm Γ], pc P "Datatype.aQ" [], nums Γ]) [negated] <|
          normLastK K <|
        nums3 "aQNums" <| nums3 "splitTyNums" <| nums3 "splitNums" <|
        (if flag then fun k ↦
            applyThm K "letNums" (fun Γ ↦ [tailB Γ, (frags Γ).2.1, rForm Γ, x Γ, nums Γ])
              [negated] <| normLastK K <| nums3 "forceNums" k
          else fun k ↦
            applyThm K "letNums" (fun Γ ↦ [tailB Γ, pc P "Datatype.sHeadOf" [aC], aT, x Γ,
              nums Γ]) [negated] <| normLastK K k) <|
        applyThm K "letNums" (fun Γ ↦ [erRest Γ, pc P "Datatype.sTailOf" [aC],
          pc P "Datatype.sList" [aT], aC, nums Γ]) [negated] <| normLastK K <|
        decideIn K (fun Γ ↦ pc P "Prelude.isSome" [pc P "Reader.readType" [tys Γ, rF Γ]])
          (refuteRes "the result type unread") <|
        linkK K "cataWalk: the field's resolution" <|
        applyThm K s!"cataStepRes{if flag then 1 else 0}" (fun Γ ↦ [restEx Γ, cs Γ, scope0 Γ,
            tys Γ, names Γ, cq 5 Γ, rF Γ, drF Γ])
          ([K.solve 3, linkK K "cataWalk: the field's split's index" (eqHyp cIdx)] ++
            absentAt (hNums + o) (hNames + o) (hCx + o) scope0 cx "aUnitV" ++
            [K.solve 3, prem, prem]) <| normLastK K <|
        -- the rest's resolution decided, and then the default's beneath the unit's binder, the
        -- resolution's conjunction none where either is absent
        decideOpt K restRes (refuteNone "the rest unresolved") <|
        decideOpt K (fun Γ ↦ pc P "Reader.resolve" [tys Γ, names Γ, drF Γ, uSc Γ])
          (refuteNone "the default unresolved")
          (linkK K "cataWalk: the field's rest resolved" (present iR iOk))
      -- the binder an atom of characters at position pC; its characters fixed by the entries'
      -- hypothesis, split at the head; then the binding at its expansion
      let atomCase (iOk pC iI : ℕ) : Deducer :=
        let cs := atPos pC
        -- the index of the rest's characters fixed given to k
        let charsFix (k : ℕ → Deducer) : Deducer := linkK K "cataWalk: the field's characters"
          fun Γ Φ ψ ↦ dRwHyp (evalRw K.G K.E (K.rulesEx Φ (2 + o)) .full) (2 + o)
            (fun Γ Φ ψ ↦ dConjE L (Φ.length - 1) (fun Γ Φ ψ ↦
              let iR := Φ.length - 1
              dImpE L (Φ.length - 2) (linkK K "cataWalk: the field's variable an atom"
                (K.solve 3)) (fun Γ Φ ψ ↦
              let fixedHead := Φ.length - 1
              (K.cutThm "charsFixedEq" (fun Γ ↦ [cs Γ, nums Γ]) <|
                K.impE (fun Γ Φ ψ ↦ K.byHyp fixedHead Γ Φ ψ) <| normLastK K (k iR)) Γ Φ ψ)
              Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
        charsFix fun iR ↦ expansion o x cs iI fun c ↦ binderFlow c iR iOk
      decideIn K (fun Γ ↦ pc P "Typing.fieldOk" [ms Γ, ft Γ,
          pc P "Typing.memberships" [ms Γ, t Γ]]) (refute "the field's test" cOk) <| fun Γ Φ ψ ↦
        let iOk := Φ.length - 1
        -- unflagged, the field type's reading present, absent refuting the typing
        ((if flag then id else decideIn K (fun Γ ↦ pc P "Prelude.isSome"
            [pc P "Typing.fieldTy" [E' Γ, ft Γ]]) (refute "the field's type absent" cTy)) <|
          varAtom cTy x "the field's variable" (atomCase iOk)) Γ Φ ψ
    let consBody : Deducer := fun Γ₀ Φ₀ ψ₀ ↦
      K.listCase treeTy (cq 0 Γ₀) (refute "no field type for the entry" cTy) (fun Γ₁ Φ₁ ψ₁ ↦
        let pF := Γ₁.length - 2
        entryCases cTy cFlag (atPos pF) 14 (fun flag pX ↦ fun Γ Φ ψ ↦
          K.listCase treeTy (cq 1 Γ) (refute "no child for the field" cOk) (fun Γ Φ ψ ↦
            let pT := Γ.length - 2
            K.listCase treeTy (cq 2 Γ) (lenFalse cLen) (fun Γ Φ ψ ↦
              consField flag pX pF pT (Γ.length - 2) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ) Γ₁ Φ₁ ψ₁) Γ₀ Φ₀ ψ₀
    let r₁ : Option Internal.Deriv := linkK K "cataWalk: a field" (introsAt o consBody)
      (list treeTy :: treeTy :: (cataWalkCtx T).tail) [Internal.weakenElem φ]
      (Internal.listConsAt 1 treeTy φ)
    let some d₀ := r₀
      | dbgTrace s!"cataWalk: the empty walk not proved; a field {r₁.isSome}" fun _ ↦ none
    let some d₁ := r₁ | dbgTrace "cataWalk: the empty walk proved, a field not" fun _ ↦ none
    pure (⟨0, cataWalkCtx T, [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The expansion of the numeral abbreviations at the erasure's fragments of a structural recursion
({name}`cataFrags`) and at the list type and the split's type of the result type's form, their atoms
not abbreviated: each at the expansions of the forms. In the context of the result type's form, the
default's form and the abbreviations. -/
def fragNums (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  let en (t : Term) : Term := pc P "Reader.expandNums" [v 2, t]
  let tests := (cataAtoms P).map fun a ↦
    pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev" [a, v 2]]
  let step3 : Prog → (String → ℕ) → Array Internal.Entry → List Internal.NormRule :=
    fun _ _ _ ↦ [.delta (T.argIdx 3)]
  let (split, force, fold) := cataFrags P (v 0) (v 1)
  let (split', _, fold') := cataFrags P (en (v 0)) (en (v 1))
  let Γ := [treeTy, treeTy, list treeTy]
  [builderEq "splitNums" P S Γ tests (en split) step3 (some split'),
    builderEq "forceNums" P S Γ tests (en force) step3 (some force),
    builderEq "foldNums" P S Γ tests (en fold) step3 (some fold'),
    builderEq "listNums" P S Γ tests (en (pc P "Datatype.sList" [v 0])) step3
      (some (pc P "Datatype.sList" [en (v 0)])),
    builderEq "splitTyNums" P S Γ tests (en (pc P "Datatype.splitTy" [v 0])) step3
      (some (pc P "Datatype.splitTy" [en (v 0)])),
    builderEq "aQNums" P S Γ tests (en (pc P "Datatype.aQ" [])) step3
      (some (pc P "Datatype.aQ" []))]

/-- An equation proved by normalization under equations: in a context, after a first hypothesis
of truth, each hypothesis an equation in the normal form of the walk's rules, the left side's
normal form under those rules equal to its normal form under them and the further rules, the
hypotheses rewriting the opaque parts. -/
def eqUnder (name : String) (P : Prog) (S : Defs) (Γ : List Tree) (hyps : List Term) (lhs : Term)
    (extra : Prog → (String → ℕ) → Array Internal.Entry → List Internal.NormRule)
    (tests : List Term := []) (posTests : List Term := []) : Step :=
  (name, fun ix E ↦ do
    let P := walkProg P
    let K : Kit := ⟨P, S, E, ix, walkMore ix E⟩
    let rs := extra P ix E
    -- a first hypothesis of truth, as the first supplies no rule
    let hyps ← hyps.mapM fun h ↦ (evalRw K.G K.E (K.rules []) .full Γ [] h).map Prod.fst
    let hyps := Internal.Logic.tt P.o :: hyps
    -- the tests' outcomes' equations, the failing tests' labels empty and the passing ones' one
    let labelEq (t X : Term) : Option Term := do
      let (L, _) ← evalRw K.G K.E (K.rules []) .full Γ [] (call D.lab [] [t])
      pure (Term.eq L X)
    let fails ← tests.mapM fun t ↦ labelEq t bnilT
    let passes ← posTests.mapM fun t ↦ labelEq t (numeral 1)
    let outcomes := fails ++ passes
    let (l, _) ← evalRw K.G K.E (K.rules []) .full Γ [] lhs
    let (r, _) ← evalRw K.G K.E (K.rules (hyps ++ outcomes) ++ rs) .full Γ (hyps ++ outcomes) lhs
    let a : Internal.Thm := ⟨0, Γ, hyps ++ tests.map (notTest P.o) ++
      posTests.map (truth P.o), Term.eq l r⟩
    let nT := hyps.length
    -- each failing test decided, true refuting its negation; each passing test decided, false
    -- refuting its truth
    let at_ (t : Term) (Δ : List Tree) : Term := sh (Δ.length - Γ.length) t
    let decisions : Deducer → Deducer := fun k ↦
      tests.zipIdx.foldr (fun (t, i) k ↦
        decideIn K (at_ t) k (linkK K s!"{name}: test {i} true" fun Γ Φ ψ ↦
          dImpE K.L (nT + i) (K.solve 3) (fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ) Γ Φ ψ))
        (posTests.zipIdx.foldr (fun (t, i) k ↦
          decideIn K (at_ t) (linkK K s!"{name}: passing test {i} false"
            (K.hypFalse (nT + tests.length + i))) k) k)
    let some d := decisions (linkK K s!"{name}: the sides" fun Γ Φ ψ ↦
        dEq (fun Γ Φ t u ↦ byMode .full K.G K.E 0 (K.rules Φ ++ rs) Γ
          (rwHyps (K.rules Φ) Φ) t u) Γ Φ ψ) a.ctx a.hyps a.concl
      | dbgTrace s!"{name}: not proved" fun _ ↦ none
    pure (a, d))

/-- The reader's resolution of the builders of the erasure's fragments of a structural recursion
({name}`cataFrags`), one builder at a time, its parts opaque, the resolutions of the parts that are
fragments given, and the readings of the types and the resolution of an abstraction's body, which
are the result type's and the default's, present: the keyword forms of the right fold and of the
case analysis of lists over two types and three terms, the abstractions over one and two of the
erasure's names, the forms of pairs and of the construction of lists, which the reader reads as
keywords, the empty list at a type, the rest of the split at the split's index in the scope, and the
forcing of the split's first in the scope headed by the split's name, the unit value's name, an atom
the reader resolves after the scope and the definitions, in neither. Each in the context of its
parts, the scope, the type abbreviations, the definitions' names, then the given resolutions. -/
def fragRes (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  let res : Prog → (String → ℕ) → Array Internal.Entry → List Internal.NormRule :=
    fun P ix E ↦ resolveRules P T ix E
  let some (t : Term) : Term := pc P "Prelude.some" [t]
  let isSome (t : Term) : Term := pc P "Prelude.isSome" [t]
  let none' : Term := pc P "Prelude.none" []
  let d (n : String) : Term := pc P s!"Datatype.{n}" []
  let nm (n : String) : Term := atomNameT (d n)
  let rT (tys t : Term) : Term := pc P "Reader.readType" [tys, t]
  let rs (tys names t sc : Term) : Term := pc P "Reader.resolve" [tys, names, t, sc]
  let sx (k : ℕ) (as : List Term) : Term := pc P s!"Datatype.sx{k}" as
  -- the primitive's name absent from the scope and the definitions' names
  let unnamed (n sc names : Term) : List Term :=
    [Term.eq (pc P "Reader.indexOf" [n, sc]) none',
      Term.eq (pc P "Reader.indexOf" [n, names]) none']
  let L := list treeTy
  -- a keyword form: the types v0, v1, the terms v2, v3, v4, the scope v5, the type
  -- abbreviations v6, the names v7, then the resolutions v8, v9, v10
  let kw6 (name kw : String) : Step :=
    eqUnder name P S ([treeTy, treeTy, treeTy, treeTy, treeTy, L, L, L] ++
        List.replicate 3 treeTy)
      ([2, 3, 4].map fun i ↦ Term.eq (rs (v 6) (v 7) (v i) (v 5)) (some (v (i + 6))))
      (rs (v 6) (v 7) (sx 6 [d kw, v 0, v 1, v 2, v 3, v 4]) (v 5)) res []
      [isSome (rT (v 6) (v 0)), isSome (rT (v 6) (v 1))]
  -- an abstraction over one name: the type v0, the body v1, the scope v2, the type abbreviations
  -- v3, the names v4
  let lam1 (name x : String) : Step :=
    eqUnder name P S [treeTy, treeTy, L, L, L] []
      (rs (v 3) (v 4) (pc P "Datatype.sLam1" [d x, v 0, v 1]) (v 2)) res []
      [isSome (rT (v 3) (v 0)), isSome (rs (v 3) (v 4) (v 1) (consT treeTy (nm x) (v 2)))]
  -- an abstraction over two names: the types v0, v1, the body v2, the scope v3, the type
  -- abbreviations v4, the names v5 and the body's resolution v6
  let lam2 (name x y : String) : Step :=
    eqUnder name P S [treeTy, treeTy, treeTy, L, L, L, treeTy]
      [Term.eq (rs (v 4) (v 5) (v 2) (consT treeTy (nm y) (consT treeTy (nm x) (v 3))))
        (some (v 6))]
      (rs (v 4) (v 5) (pc P "Datatype.sLam2" [d x, v 0, d y, v 1, v 2]) (v 3)) res []
      [isSome (rT (v 4) (v 0)), isSome (rT (v 4) (v 1))]
  -- a primitive of two arguments: the terms v0, v1, the scope v2, the type abbreviations v3, the
  -- names v4, the resolutions v5, v6
  let prim3 (name p : String) : Step :=
    eqUnder name P S [treeTy, treeTy, L, L, L, treeTy, treeTy]
      ([0, 1].map fun i ↦ Term.eq (rs (v 3) (v 4) (v i) (v 2)) (some (v (i + 5))))
      (rs (v 3) (v 4) (sx 3 [d p, v 0, v 1]) (v 2)) res
  -- the closed fragments: the scope's tail v0, the type abbreviations v1, the names v2, the
  -- split's index v3, in the scope headed by the children remaining's name
  let sc := consT treeTy (fieldsName P) (v 0)
  let closed (name : String) (t : Term) (ps : List String) : Step :=
    eqUnder name P S [L, L, L, bitsTy]
      (Term.eq (pc P "Reader.indexOf" [splitName P, sc]) (some (leafT (v 3))) ::
        ps.flatMap fun p ↦ unnamed (nm p) (v 0) (v 2))
      (rs (v 1) (v 2) t sc) res
  -- the empty list at a type: the type v0, the scope v1, the type abbreviations v2, the names v3
  let nilAt : Step :=
    eqUnder "nilRes" P S [treeTy, L, L, L] [] (rs (v 2) (v 3) (sx 2 [d "aNil", v 0]) (v 1)) res []
      [isSome (rT (v 2) (v 0))]
  -- the forcing of the head in the step of the right fold: the scope's tail v0, the type
  -- abbreviations v1, the names v2, in the scope of the step's names before the children
  -- remaining's
  let stepSc := consT treeTy (nm "aA") (consT treeTy (nm "aH")
    (consT treeTy (fieldsName P) (v 0)))
  let headForce : Step :=
    eqUnder "headForceRes" P S [L, L, L] (unnamed (nm "aUnitV") (v 0) (v 2))
      (rs (v 1) (v 2) (sx 2 [d "aH", d "aUnitV"]) stepSc) res
  -- the pair of the split's head and tail in the step of its case analysis: the scope's tail v0,
  -- the type abbreviations v1, the names v2
  let htSc := consT treeTy (nm "aTl") (consT treeTy (nm "aH") (consT treeTy (fieldsName P) (v 0)))
  let pairHT : Step :=
    eqUnder "pairHTRes" P S [L, L, L] []
      (rs (v 1) (v 2) (sx 3 [d "aPair", d "aH", d "aTl"]) htSc) res
  -- the rest of the fold's step, its innermost name, in the step's scope
  let aRes : Step := eqUnder "aARes" P S [L, L, L] [] (rs (v 1) (v 2) (d "aA") stepSc) res
  -- the forcing in the scope the split's binding opens, headed by the split's name: the scope's
  -- tail v0, the type abbreviations v1, the names v2
  let qSc := consT treeTy (splitName P) (v 0)
  [kw6 "foldrRes" "aFoldr", kw6 "lcaseRes" "aLcase", lam1 "lamURes" "aU", pairHT, aRes,
    lam2 "lamHARes" "aH" "aA", lam2 "lamHTRes" "aH" "aTl", prim3 "pairRes" "aPair",
    prim3 "consRes" "aCons", nilAt, headForce,
    closed "sndQRes" (sx 2 [d "aSnd", d "aQ"]) [],
    eqUnder "forceRes" P S [L, L, L]
      (unnamed (nm "aUnitV") (v 0) (v 2))
      (rs (v 1) (v 2) (sx 2 [sx 2 [d "aFst", d "aQ"], d "aUnitV"]) qSc) res]

/-- The absence of the default's resolution beneath the unit's binder carried through the split
of the suspended results ({name}`cataFrags`), one builder at a time, its parts opaque: the
abstraction over the unit, its body unresolved; the pair of an unresolved first and a term; and
the keyword form of the case analysis of lists whose term for the empty list is unresolved; each
resolution none. Each in the context of its parts, the scope, the type abbreviations and the
definitions' names. -/
def fragNone (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  let res : Prog → (String → ℕ) → Array Internal.Entry → List Internal.NormRule :=
    fun P ix E ↦ resolveRules P T ix E
  let d (n : String) : Term := pc P s!"Datatype.{n}" []
  let none' : Term := pc P "Prelude.none" []
  let rs (tys names t sc : Term) : Term := pc P "Reader.resolve" [tys, names, t, sc]
  let sx (k : ℕ) (as : List Term) : Term := pc P s!"Datatype.sx{k}" as
  let L := list treeTy
  -- the abstraction over the unit: the type v0, the body v1, the scope v2, the type
  -- abbreviations v3, the names v4
  [eqUnder "lamUNone" P S [treeTy, treeTy, L, L, L] []
      (rs (v 3) (v 4) (pc P "Datatype.sLam1" [d "aU", v 0, v 1]) (v 2)) res
      [pc P "Prelude.isSome" [rs (v 3) (v 4) (v 1) (consT treeTy (atomNameT (d "aU")) (v 2))]],
    -- the pair: the terms v0, v1, the scope v2, the type abbreviations v3, the names v4
    eqUnder "pairNone" P S [treeTy, treeTy, L, L, L] [Term.eq (rs (v 3) (v 4) (v 0) (v 2)) none']
      (rs (v 3) (v 4) (sx 3 [d "aPair", v 0, v 1]) (v 2)) res,
    -- the case analysis of lists: the types v0, v1, the terms v2, v3, v4, the scope v5, the
    -- type abbreviations v6, the names v7
    eqUnder "lcaseNone" P S [treeTy, treeTy, treeTy, treeTy, treeTy, L, L, L]
      [Term.eq (rs (v 6) (v 7) (v 3) (v 5)) none']
      (rs (v 6) (v 7) (sx 6 [d "aLcase", v 0, v 1, v 2, v 3, v 4]) (v 5)) res]

/-- The instance of the kernel's term a resolution lemma resolves to ({name}`boundTerm`) at
terms of its context, the innermost first. -/
def resK (E : Array Internal.Entry) (ix : String → ℕ) (name : String) (σ : List Term) :
    Option Term :=
  (boundTerm E ix name).map (Internal.instTerm [] σ)

/-- A hypothesis of a resolution lemma ({name}`fragRes`) at its instance: by normalization, with
the index's equations, as a hypothesis, a negation by its antecedent refuted, or, a reading's
presence, by the result type's reading
{lit}`reading` decided, absent refuting the hypothesis of index {lit}`h` of its presence. -/
def resPrem (K : Kit) (reading : List Tree → Term) (h : ℕ) : Deducer :=
  let KL : Kit := { K with more := K.more ++ lookupEqNames }
  fun Γ Φ ψ ↦ (K.solve 3 Γ Φ ψ).orElse fun _ ↦ (KL.solve 3 Γ Φ ψ).orElse fun _ ↦
    (K.norm dHyp Γ Φ ψ).orElse fun _ ↦
    (dImpI K.L (fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ) Γ Φ ψ).orElse fun _ ↦
    decideIn K (fun Γ ↦ pc K.P "Prelude.isSome" [reading Γ]) (K.hypFalse h) (K.solve 3) Γ Φ ψ

/-- A resolution lemma ({name}`fragRes`) at terms of the context, its hypotheses each by
{lit}`prem`, its equation cut in normalized. -/
def useRes (K : Kit) (owner : String) (prem : Deducer) (name : String) (σ : List Tree → List Term)
    (k : Deducer) : Deducer := fun Γ Φ ψ ↦ do
  let some (Internal.Entry.language th) := K.E[K.ix name]? | none
  linkK K s!"{owner}: {name}" (applyThm K name σ
    (th.hyps.map fun _ ↦ prem)
    (linkK K s!"{owner}: after {name}" (normLastK K k))) Γ Φ ψ

/-- The reader's resolution of the right fold forcing the split's rest ({name}`cataFrags`), in the
scope headed by the children remaining's name, where the split's name has an index there, the unit
value's name is no scope's and no definition's, and the result type's form has a reading: the
composition of the resolution lemmas ({name}`fragRes`), innermost first. In the context of the
scope's tail, the type abbreviations, the definitions' names, the split's index's bitstring and the
result type's form. -/
def foldRes (P : Prog) (S : Defs) : Step :=
  ("foldRes", fun ix E ↦ do
    let P := walkProg P
    let K : Kit := ⟨P, S, E, ix, walkMore ix E⟩
    let s := Term.star
    let L := list treeTy
    let Γ := [L, L, L, bitsTy, treeTy]
    let d (n : String) : Term := pc P s!"Datatype.{n}" []
    let sx (k : ℕ) (as : List Term) : Term := pc P s!"Datatype.sx{k}" as
    let none' : Term := pc P "Prelude.none" []
    let (sc0, tys, names, b, rF) := (atPos 4, atPos 3, atPos 2, atPos 1, atPos 0)
    let sc (Γ : List Tree) : Term := consT treeTy (fieldsName P) (sc0 Γ)
    let stepSc (Γ : List Tree) : Term := consT treeTy (atomNameT (d "aA"))
      (consT treeTy (atomNameT (d "aH")) (sc Γ))
    -- the fold's parts ({name}`cataFrags`)
    let thF (Γ : List Tree) : Term := pc P "Datatype.thTy" [rF Γ]
    let lrF (Γ : List Tree) : Term := pc P "Datatype.sList" [rF Γ]
    let hfF : Term := sx 2 [d "aH", d "aUnitV"]
    let consF : Term := sx 3 [d "aCons", hfF, d "aA"]
    let stepF (Γ : List Tree) : Term :=
      pc P "Datatype.sLam2" [d "aH", thF Γ, d "aA", lrF Γ, consF]
    let nilF (Γ : List Tree) : Term := sx 2 [d "aNil", rF Γ]
    let sndF : Term := sx 2 [d "aSnd", d "aQ"]
    let (_, _, foldF) := cataFrags P (rF Γ) s
    -- the kernel's terms
    let sndK ← resK E ix "sndQRes" [s, s, s, b Γ]
    let nilK ← resK E ix "nilRes" [rF Γ, s, tys Γ, s]
    let hfK ← resK E ix "headForceRes" []
    let var0K ← resK E ix "aARes" []
    let bodyK ← resK E ix "consRes" [s, s, s, s, s, hfK, var0K]
    let stepK ← resK E ix "lamHARes" [thF Γ, lrF Γ, s, s, tys Γ, s, bodyK]
    let foldK ← resK E ix "foldrRes" [thF Γ, lrF Γ, s, s, s, s, tys Γ, s, stepK, nilK, sndK]
    let unnamed (p : String) : List Term :=
      [Term.eq (pc P "Reader.indexOf" [atomNameT (d p), v 0]) none',
        Term.eq (pc P "Reader.indexOf" [atomNameT (d p), v 2]) none']
    -- the hypotheses in the normal form in which the lemmas' instances occur, after a first of
    -- truth, which supplies no rule
    let hyps ← ([Term.eq (pc P "Reader.indexOf" [splitName P, sc Γ])
        (pc P "Prelude.some" [leafT (v 3)])] ++ unnamed "aUnitV" ++
      [truth P.o (pc P "Prelude.isSome" [pc P "Reader.readType" [v 1, v 4]])]).mapM fun h ↦
        (evalRw K.G K.E (K.rules []) .full Γ [] h).map Prod.fst
    let hyps := Internal.Logic.tt P.o :: hyps
    let (l, _) ← evalRw K.G K.E (K.rules []) .full Γ []
      (pc P "Reader.resolve" [v 1, v 2, foldF, sc Γ])
    let a : Internal.Thm := ⟨0, Γ, hyps, Term.eq l (pc P "Prelude.some" [foldK])⟩
    let use := useRes K "foldRes"
      (resPrem K (fun Γ ↦ pc P "Reader.readType" [tys Γ, rF Γ]) 4)
    let w (t : Term) (Γ : List Tree) : Term := sh (Γ.length - 5) t
    let some dv := (use "sndQRes" (fun Γ ↦ [sc0 Γ, tys Γ, names Γ, b Γ]) <|
        use "nilRes" (fun Γ ↦ [rF Γ, sc Γ, tys Γ, names Γ]) <|
        use "headForceRes" (fun Γ ↦ [sc0 Γ, tys Γ, names Γ]) <|
        use "aARes" (fun Γ ↦ [sc0 Γ, tys Γ, names Γ]) <|
        use "consRes" (fun Γ ↦ [hfF, d "aA", stepSc Γ, tys Γ, names Γ, w hfK Γ, w var0K Γ]) <|
        use "lamHARes" (fun Γ ↦ [thF Γ, lrF Γ, consF, sc Γ, tys Γ, names Γ, w bodyK Γ]) <|
        use "foldrRes" (fun Γ ↦ [thF Γ, lrF Γ, stepF Γ, nilF Γ, sndF, sc Γ, tys Γ, names Γ,
          w stepK Γ, w nilK Γ, w sndK Γ]) <|
        linkK K "foldRes: the composition" (K.solve 3)) a.ctx a.hyps a.concl
      | dbgTrace "foldRes: not proved" fun _ ↦ none
    pure (a, dv))

/-- The kernel's term of the split of the suspended results ({name}`cataFrags`), composed of the
resolution lemmas' terms ({name}`fragRes`) at the type abbreviations {lit}`tys`, the definitions'
names {lit}`names`, the scope {lit}`sc` at the split, the forms of the types of a suspended result
{lit}`thF`, of the split {lit}`spF` and of the suspended results' list {lit}`lthF`, the default's
form {lit}`drF` and the split's index's bitstring {lit}`b`. -/
def splitK (P : Prog) (E : Array Internal.Entry) (ix : String → ℕ)
    (tys names sc thF spF lthF drF b : Term) : Option Term := do
  let s := Term.star
  let sndK ← resK E ix "sndQRes" [s, s, s, b]
  let lamUK ← resK E ix "lamURes" [pc P "Datatype.aUnit" [], drF, sc, tys, names]
  let nilK ← resK E ix "nilRes" [thF, s, tys, s]
  let pairK ← resK E ix "pairRes" [s, s, s, s, s, lamUK, nilK]
  let pairHT ← resK E ix "pairHTRes" []
  let lamHTK ← resK E ix "lamHTRes" [thF, lthF, s, s, tys, s, pairHT]
  resK E ix "lcaseRes" [thF, spF, s, s, s, s, tys, s, sndK, pairK, lamHTK]

/-- A name without an index among names ({lit}`Reader.indexOf`) has the index none: by induction
on the names; at a construction, the head equal to the name or not, then the rest's index present
or not. Equal, or the rest's index present, the construction's index is present, refuting the
hypothesis; otherwise the induction hypothesis at the rest gives its index none, and the
construction's by the index's equations. -/
def indexNone (P : Prog) (S : Defs) : Step :=
  ("indexNone", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, lookupEqNames⟩
    let L := K.L
    let o := P.o
    let equalT ← primT Kernel.Prim.equal
    let isSomeT (t : Term) : Term := truth o (pc P "Prelude.isSome" [t])
    let none' : Term := pc P "Prelude.none" []
    -- under the quantifier: the name v0, the names v1
    let φ := Internal.Logic.all o treeTy (Term.lam treeTy (Internal.Logic.imp o
      (notT o (isSomeT (pc P "Reader.indexOf" [v 0, v 1])))
      (Term.eq (pc P "Reader.indexOf" [v 0, v 1]) none')))
    let d₀ ← dAllI L (dImpI L (linkK K "indexNone: empty" (K.solve 3))) [] []
      (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
    -- context: the name, the rest, the head; hypotheses: the induction hypothesis, the
    -- quantifier's truth, the name's index absent
    let cons : Deducer := dAllI L (dImpI L fun Γ₁ Φ₁ ψ₁ ↦
      let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
      let hd := at_ 0
      let n := at_ 2
      let absent := Φ₁.length - 1
      -- the construction's index present, refuting its absence
      let present : Deducer := dImpE L absent (K.solve 3) fun Γ Φ ψ ↦
        K.hypFalse (Φ.length - 1) Γ Φ ψ
      -- the rest's index none: the induction hypothesis at the name
      let rest : Deducer := linkK K "indexNone: the rest" fun Γ Φ ψ ↦
        dAllE L K.G K.E 0 (n Γ) (K.impE (dImpI L fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ)
          (normLastK K (K.solve 3))) Γ Φ ψ
      decideIn K (fun Γ ↦ apps equalT [n Γ, hd Γ])
        (decideIn K (fun Γ ↦ pc P "Prelude.isSome" [pc P "Reader.indexOf" [n Γ, at_ 1 Γ]])
          rest present)
        present Γ₁ Φ₁ ψ₁)
    let d₁ ← cons [list treeTy, treeTy] [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, [list treeTy], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The reader's resolution of the split of the suspended results ({name}`cataFrags`), in the scope
headed by the children remaining's name, where the split's name has an index there and the result
type's form has a reading: where the default's form has a resolution in that scope extended by the
unit's binder, the composition of the resolution lemmas ({name}`fragRes`), innermost first, to the
term {name}`splitK` composes, else none ({name}`fragNone`). In the context of the scope's tail, the
type abbreviations, the definitions' names, the split's index's bitstring, the result type's form
and the default's form. -/
def splitRes (P : Prog) (S : Defs) : Step :=
  ("splitRes", fun ix E ↦ do
    let P := walkProg P
    let K : Kit := ⟨P, S, E, ix, walkMore ix E⟩
    let s := Term.star
    let L := list treeTy
    let Γ := [L, L, L, bitsTy, treeTy, treeTy]
    let d (n : String) : Term := pc P s!"Datatype.{n}" []
    let sx (k : ℕ) (as : List Term) : Term := pc P s!"Datatype.sx{k}" as
    let (sc0, tys, names, b, rF, drF) :=
      (atPos 5, atPos 4, atPos 3, atPos 2, atPos 1, atPos 0)
    let sc (Γ : List Tree) : Term := consT treeTy (fieldsName P) (sc0 Γ)
    let uSc (Γ : List Tree) : Term := consT treeTy (atomNameT (d "aU")) (sc Γ)
    -- the split's parts ({name}`cataFrags`)
    let thF (Γ : List Tree) : Term := pc P "Datatype.thTy" [rF Γ]
    let spF (Γ : List Tree) : Term := pc P "Datatype.splitTy" [rF Γ]
    let lthF (Γ : List Tree) : Term := pc P "Datatype.sList" [thF Γ]
    let lamUF (Γ : List Tree) : Term := pc P "Datatype.sLam1" [d "aU", d "aUnit", drF Γ]
    let nilF (Γ : List Tree) : Term := sx 2 [d "aNil", thF Γ]
    let pairF (Γ : List Tree) : Term := sx 3 [d "aPair", lamUF Γ, nilF Γ]
    let pairHTF : Term := sx 3 [d "aPair", d "aH", d "aTl"]
    let lamHTF (Γ : List Tree) : Term :=
      pc P "Datatype.sLam2" [d "aH", thF Γ, d "aTl", lthF Γ, pairHTF]
    let sndF : Term := sx 2 [d "aSnd", d "aQ"]
    let (splitF, _, _) := cataFrags P (rF Γ) (drF Γ)
    -- the kernel's terms, as {name}`splitK` composes them
    let sndK ← resK E ix "sndQRes" [s, s, s, b Γ]
    let lamUK ← resK E ix "lamURes" [d "aUnit", drF Γ, sc Γ, tys Γ, names Γ]
    let nilK ← resK E ix "nilRes" [thF Γ, s, tys Γ, s]
    let pairK ← resK E ix "pairRes" [s, s, s, s, s, lamUK, nilK]
    let pairHTK ← resK E ix "pairHTRes" []
    let lamHTK ← resK E ix "lamHTRes" [thF Γ, lthF Γ, s, s, tys Γ, s, pairHTK]
    let sk ← splitK P E ix (tys Γ) (names Γ) (sc Γ) (thF Γ) (spF Γ) (lthF Γ) (drF Γ) (b Γ)
    -- the hypotheses in the normal form in which the lemmas' instances occur, after a first of
    -- truth, which supplies no rule
    let hyps ← [Term.eq (pc P "Reader.indexOf" [splitName P, sc Γ])
        (pc P "Prelude.some" [leafT (b Γ)]),
      truth P.o (pc P "Prelude.isSome" [pc P "Reader.readType" [tys Γ, rF Γ]])
      ].mapM fun h ↦ (evalRw K.G K.E (K.rules []) .full Γ [] h).map Prod.fst
    let hyps := Internal.Logic.tt P.o :: hyps
    let (l, _) ← evalRw K.G K.E (K.rules []) .full Γ []
      (pc P "Reader.resolve" [tys Γ, names Γ, splitF, sc Γ])
    -- the default's resolution beneath the unit's binder, its presence the resolution's
    let rdr (Γ : List Tree) : Term := pc P "Reader.resolve" [tys Γ, names Γ, drF Γ, uSc Γ]
    let rhs := condT treeTy (call D.lab [] [pc P "Prelude.isSome" [rdr Γ]])
      (pc P "Prelude.some" [sk]) (pc P "Prelude.none" [])
    let a : Internal.Thm := ⟨0, Γ, hyps, Term.eq l rhs⟩
    let use := useRes K "splitRes"
      (resPrem K (fun Γ ↦ pc P "Reader.readType" [tys Γ, rF Γ]) 2)
    let w (t : Term) (Γ' : List Tree) : Term := sh (Γ'.length - Γ.length) t
    -- the default unresolved: the split unresolved ({name}`fragNone`), the goal rewritten by the
    -- lemmas' instances, the other parts' resolutions given, the case analysis's resolution then a
    -- test of the types' readings with both branches none, decided by the result type's, absent
    -- refuting its hypothesis
    let absent : Deducer := linkK K "splitRes: the default unresolved" <|
      use "sndQRes" (fun Γ ↦ [sc0 Γ, tys Γ, names Γ, b Γ]) <|
      use "pairHTRes" (fun Γ ↦ [sc0 Γ, tys Γ, names Γ]) <|
      use "lamHTRes" (fun Γ ↦ [thF Γ, lthF Γ, pairHTF, sc Γ, tys Γ, names Γ, w pairHTK Γ]) <|
      use "lamUNone" (fun Γ ↦ [d "aUnit", drF Γ, sc Γ, tys Γ, names Γ]) <|
      use "pairNone" (fun Γ ↦ [lamUF Γ, nilF Γ, sc Γ, tys Γ, names Γ]) <|
      use "lcaseNone" (fun Γ ↦ [thF Γ, spF Γ, sndF, pairF Γ, lamHTF Γ, sc Γ, tys Γ, names Γ]) <|
      -- the goal's left side the equation's as written, rewritten by it at the root
      -- ({name}`rwHypRoot`), before any normalization reduces inside it
      fun Γ Φ ψ ↦
        let sides : Deducer := K.norm <| decideIn K (fun Γ ↦
          pc P "Prelude.isSome" [pc P "Reader.readType" [tys Γ, rF Γ]]) (K.hypFalse 2) (K.solve 3)
        (rwHypRoot (Φ.length - 1) sides Γ Φ ψ).orElse fun _ ↦
          rwHypRoot (Φ.length - 2) sides Γ Φ ψ
    let some dv := decideIn K (fun Γ ↦ pc P "Prelude.isSome" [rdr Γ]) absent (
        use "sndQRes" (fun Γ ↦ [sc0 Γ, tys Γ, names Γ, b Γ]) <|
        use "lamURes" (fun Γ ↦ [d "aUnit", drF Γ, sc Γ, tys Γ, names Γ]) <|
        use "nilRes" (fun Γ ↦ [thF Γ, sc Γ, tys Γ, names Γ]) <|
        use "pairRes" (fun Γ ↦ [lamUF Γ, nilF Γ, sc Γ, tys Γ, names Γ, w lamUK Γ, w nilK Γ]) <|
        use "pairHTRes" (fun Γ ↦ [sc0 Γ, tys Γ, names Γ]) <|
        use "lamHTRes" (fun Γ ↦ [thF Γ, lthF Γ, pairHTF, sc Γ, tys Γ, names Γ, w pairHTK Γ]) <|
        use "lcaseRes" (fun Γ ↦ [thF Γ, spF Γ, sndF, pairF Γ, lamHTF Γ, sc Γ, tys Γ, names Γ,
          w sndK Γ, w pairK Γ, w lamHTK Γ]) <|
        linkK K "splitRes: the composition" (K.solve 3)) a.ctx a.hyps a.concl
      | dbgTrace "splitRes: not proved" fun _ ↦ none
    pure (a, dv))

/-- The reader's resolution of the head and of the tail of the children remaining beneath the
split's name ({name}`splitName`): the head in the scope of the split's name before the children
remaining's, the tail in that scope extended by a binder's name, an atom's, that is neither name;
the kernel's terms. In the context of the scope's tail, then, for the tail, the binder's
characters, the type abbreviations and the definitions' names. -/
def cataBindEqs (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  let res : Prog → (String → ℕ) → Array Internal.Entry → List Internal.NormRule :=
    fun P ix E ↦ resolveRules P T ix E
  let aC := pc P "Datatype.aC" []
  let L := list treeTy
  let qSc (sc : Term) : Term := consT treeTy (splitName P) (consT treeTy (fieldsName P) sc)
  let equalT := (primT Kernel.Prim.equal).getD Term.star
  [builderEq "headResQ" P S [L, L, L] []
      (pc P "Reader.resolve" [v 1, v 2, pc P "Datatype.sHeadOf" [aC], qSc (v 0)]) res,
    builderEq "tailResQ" P S [L, L, L, L]
      [namedFields P (v 1), apps equalT [splitName P, nodeT (Term.pair (numeral 0) (v 1))]]
      (pc P "Reader.resolve" [v 2, v 3, pc P "Datatype.sTailOf" [aC],
        consT treeTy (nodeT (Term.pair (numeral 0) (v 1))) (qSc (v 0))]) res]

/-- The element of index 2 of a list of trees of {lit}`depth` elements before a rest, at least
three: in the context of the rest and the third element, the normal form of the lookup, in which
the other elements no longer occur, is the third element present. Proved by the lookup's equation
at a successor as written ({lit}`nthSuccRaw`) at the index 1, then the lookup at that index of
the list's rest ({lit}`nthOne`). -/
def nthTwo (P : Prog) (S : Defs) (depth : ℕ) : Step :=
  (s!"nthTwo{depth}", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, [s!"nthOne{depth - 1}"]⟩
    let Γ := [list treeTy, treeTy]
    let filler := leafT bnilT
    -- the elements after the third, fillers, before the rest; the list's rest after its first
    let tail := (List.range (depth - 3)).foldr (fun _ t ↦ consT treeTy filler t) (v 0)
    let xs := consT treeTy filler (consT treeTy (v 1) tail)
    let (l, _) ← evalRw K.G K.E (K.rules []) .full Γ []
      (pc P "Prelude.nth" [consT treeTy filler xs, leafT (numeral 2)])
    let (r, _) ← evalRw K.G K.E (K.rules []) .full Γ [] (pc P "Prelude.some" [v 1])
    let a : Internal.Thm := ⟨0, Γ, [], Term.eq l r⟩
    let some d := K.cutThm "nthSuccRaw" (fun _ ↦ [numeral 1, xs, filler])
        (normLastK K K.byNorm) a.ctx a.hyps a.concl
      | dbgTrace s!"nthTwo{depth}: not proved" fun _ ↦ none
    pure (a, d))

/-- The kernel's terms of the head and of the tail of the children remaining beneath the split's
name ({name}`cataBindEqs`) converge, in an environment of the split's value, and for the tail a
binder's value before it, then the list value of a construction of a tree's quotation and a rest,
to the quotation and to the rest's list value. In the context of the environment's rest, the
list's rest, the tree, the split's value, for the tail the binder's value, and the relation's
context. Proved at the level 5, by normalization as {lit}`headConv`, the lookups beneath the
branches' binders by {lit}`nthOne` and {name}`nthTwo`. -/
def cataConvs (P : Prog) (S : Defs) : List Step :=
  let quote (t : Term) : Term := pc P "Eval.valQuote" [t]
  let conv (name lem : String) (Γ : List Tree) (env val : Term) : Step :=
    (name, fun ix E ↦ do
      let K : Kit := ⟨P, S, E, ix, evalMore ++ ["nthOne4", "nthTwo3"]⟩
      let k ← boundTerm E ix lem
      let n := Γ.length
      let a : Internal.Thm := ⟨0, Γ, [], S.conv (Term.lam nat (S.evN (Term.fst (v n)) (v 0)
        (sh 1 env) k)) (Term.lam treeTy (Term.eq (v 0) (sh 1 val)))⟩
      let lv : Term := (5 : ℕ).rec zeroN fun _ t ↦ succN t
      let some d := dConv K.L K.G K.E S lv val
          (linkK K s!"{name} stable" K.byNorm) (linkK K s!"{name} value" (K.norm K.byNorm))
          a.ctx a.hyps a.concl
        | dbgTrace s!"{name}: not proved" fun _ ↦ none
      pure (a, d))
  -- the children's list value: the tree v2's quotation before the rest v1
  let kids : Term := treeList P (consT treeTy (quote (v 2)) (v 1))
  [conv "headConvQ" "headResQ" [treeTy, list treeTy, list treeTy, treeTy, Defs3.ctxTy]
      (consT treeTy (v 0) (consT treeTy (treeList P (consT treeTy (quote (v 3)) (v 2))) (v 1)))
      (quote (v 3)),
    conv "tailConvQ" "tailResQ" [list treeTy, list treeTy, treeTy, treeTy, treeTy, Defs3.ctxTy]
      (consT treeTy (v 4) (consT treeTy (v 3) (consT treeTy kids (v 0)))) (treeList P (v 1))]

/-- The erasure's binding of a fixed field of a structural recursion ({lit}`Datatype.eraseCata`),
of the variable {lit}`x`, around a rest {lit}`rest`, at the result type's form {lit}`r` and the
default's form {lit}`dr`: the split of the suspended results ({name}`cataFrags`), then, flagged,
the variable bound to the forcing of the split's first, else to the head of the children
remaining, and the children remaining to their tail. -/
def entryStep (P : Prog) (flag : Bool) (x r dr rest : Term) : Term :=
  let d (n : String) : Term := pc P s!"Datatype.{n}" []
  let (split, force, _) := cataFrags P r dr
  let aC := d "aC"
  let tailB := pc P "Datatype.sLet" [aC, pc P "Datatype.sList" [d "aT"],
    pc P "Datatype.sTailOf" [aC], rest]
  pc P "Datatype.sLet" [d "aQ", pc P "Datatype.splitTy" [r], split,
    if flag then pc P "Datatype.sLet" [x, r, force, tailB]
    else pc P "Datatype.sLet" [x, d "aT", pc P "Datatype.sHeadOf" [aC], tailB]]

/-- The resolution of a structural recursion's fixed field's binding ({name}`entryStep`) of an
atom's name, in the scope headed by the children remaining's name, where the split's name has an
index there, the unit value's name no scope's and no definition's and the result type's form a
reading, and the binder is neither
the children remaining's name nor the split's: its normal form with the resolution lemmas'
equations ({name}`splitRes`, {lit}`forceRes`, {name}`cataBindEqs`) and the reader's case of
bindings ({lit}`letRes`), the rest's resolution, in the scope extended by the three bindings,
folded. In the context of the rest, the binder's characters, the scope's tail, the type
abbreviations, the definitions' names, the split's index's bitstring, the result type's form and
the default's form, its left side in the normal form of the walk's rules. Proved by deciding the
binder's comparisons, true refuting the hypotheses,
then the sides by normalization with the lemmas' instances cut in. -/
def cataStepRes (P : Prog) (S : Defs) (flag : Bool) : Step :=
  (s!"cataStepRes{if flag then 1 else 0}", fun ix E ↦ do
    let P := walkProg P
    let K : Kit := ⟨P, S, E, ix, walkMore ix E⟩
    let L := list treeTy
    let Γ := [treeTy, L, L, L, L, bitsTy, treeTy, treeTy]
    let d (n : String) : Term := pc P s!"Datatype.{n}" []
    let none' : Term := pc P "Prelude.none" []
    let equalT ← primT Kernel.Prim.equal
    -- the context's variables, as terms of a context extending it
    let at_ (i : ℕ) (Δ : List Tree) : Term := v (Δ.length - Γ.length + i)
    let (rest, cs, sc0, tys, names, b, rF, drF) :=
      (at_ 0, at_ 1, at_ 2, at_ 3, at_ 4, at_ 5, at_ 6, at_ 7)
    let x (Δ : List Tree) : Term := nodeT (Term.pair (numeral 1) (cs Δ))
    let fSc (Δ : List Tree) : Term := consT treeTy (fieldsName P) (sc0 Δ)
    let lhs := pc P "Reader.resolve" [tys Γ, names Γ,
      entryStep P flag (x Γ) (rF Γ) (drF Γ) (rest Γ), fSc Γ]
    -- the binder's comparisons with the two names
    let tests := [namedFields P (cs Γ),
      apps equalT [splitName P, nodeT (Term.pair (numeral 0) (cs Γ))]]
    let hyps ← ([Term.eq (pc P "Reader.indexOf" [splitName P, fSc Γ])
        (pc P "Prelude.some" [leafT (b Γ)]),
      Term.eq (pc P "Reader.indexOf" [atomNameT (d "aUnitV"), sc0 Γ]) none',
      Term.eq (pc P "Reader.indexOf" [atomNameT (d "aUnitV"), names Γ]) none',
      truth P.o (pc P "Prelude.isSome" [pc P "Reader.readType" [tys Γ, rF Γ]])]).mapM fun h ↦
        (evalRw K.G K.E (K.rules []) .full Γ [] h).map Prod.fst
    let negs ← (tests.map (notTest P.o)).mapM fun h ↦
      (evalRw K.G K.E (K.rules []) .full Γ [] h).map Prod.fst
    let hyps := Internal.Logic.tt P.o :: hyps ++ negs
    -- the lemmas' instances, by the hypotheses' rules and the tests' failures', in the order
    -- they are cut in
    let fails ← tests.mapM fun t ↦ do
      let (X, _) ← evalRw K.G K.E (K.rules []) .full Γ [] (call D.lab [] [t])
      pure (Term.eq X bnilT)
    let KL : Kit := { K with more := K.more ++ lookupEqNames }
    let instances : List (String × List Term) :=
      [("splitRes", [sc0 Γ, tys Γ, names Γ, b Γ, rF Γ, drF Γ])] ++
      (if flag then [("forceRes", [fSc Γ, tys Γ, names Γ])]
        else [("headResQ", [sc0 Γ, tys Γ, names Γ])]) ++
      [("tailResQ", [sc0 Γ, cs Γ, tys Γ, names Γ])]
    let Φ ← instances.foldlM (fun Φ (nm, σ) ↦ do
      let some (Internal.Entry.language th) := E[ix nm]? | none
      let (l, r) ← Internal.eqParts (Internal.instTerm [] σ th.concl)
      let (l', _) ← evalRw KL.G KL.E (KL.rules Φ) .full Γ Φ l
      let (r', _) ← evalRw KL.G KL.E (KL.rules Φ) .full Γ Φ r
      pure (Φ ++ [Term.eq l' r'])) (hyps ++ fails)
    let letRule : List Internal.NormRule := [.thm (ix "letRes") []]
    -- the left side in the normal form of the walk's rules, the resolution at a binding folded,
    -- as the walk meets it
    let Kw : Kit := { K with more := walkRules ix E }
    let (l, _) ← evalRw Kw.G Kw.E (Kw.rules []) .full Γ [] lhs
    let (r, _) ← evalRw K.G K.E (K.rules Φ ++ letRule) .full Γ Φ lhs
    let a : Internal.Thm := ⟨0, Γ, hyps, Term.eq l r⟩
    let nT := hyps.length - tests.length
    -- a hypothesis by normalization, as a hypothesis, or, a negation, its antecedent refuted
    let prem : Deducer := fun Γ Φ ψ ↦ (K.solve 3 Γ Φ ψ).orElse fun _ ↦
      (KL.solve 3 Γ Φ ψ).orElse fun _ ↦ (K.norm dHyp Γ Φ ψ).orElse fun _ ↦
      dImpI K.L (fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ) Γ Φ ψ
    let use (nm : String) (σ : List Term) (k : Deducer) : Deducer := fun Γ' Φ ψ ↦ do
      let some (Internal.Entry.language th) := E[ix nm]? | none
      linkK K s!"cataStepRes: {nm}" (applyThm K nm (fun Δ ↦ σ.map (sh (Δ.length - Γ.length)))
        (th.hyps.map fun _ ↦ prem)
        (linkK K s!"cataStepRes: {nm}'s equation" (normLastK KL k))) Γ' Φ ψ
    let sides : Deducer := linkK K "cataStepRes: the sides" fun Γ Φ ψ ↦
      dEq (fun Γ Φ t u ↦ byMode .full K.G K.E 0 (K.rules Φ ++ letRule) Γ
        (rwHyps (K.rules Φ) Φ) t u) Γ Φ ψ
    let chain : Deducer := instances.foldr (fun (nm, σ) k ↦ use nm σ k) sides
    let decisions : Deducer := tests.zipIdx.foldr (fun (t, i) k ↦
      decideIn K (fun Δ ↦ sh (Δ.length - Γ.length) t) k
        (linkK K s!"cataStepRes: test {i} true" fun Γ Φ ψ ↦
          dImpE K.L (nT + i) (K.solve 3) (fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ) Γ Φ ψ))
      chain
    let some dv := decisions a.ctx a.hyps a.concl
      | dbgTrace s!"cataStepRes: not proved" fun _ ↦ none
    pure (a, dv))

/-- The split of the suspended results converges, where the environment's value at its index is
the pair of a value
and the list value of a construction of a result and a rest, to the pair of the result and the
rest's list value. In the context of the environment's tail after the children remaining's value,
that value, the index's bitstring, the pair's first component, the results' type, the result, the
rest, the type abbreviations, the definitions' names, the scope at the split, the forms of the
types of a suspended result, of the split and of the suspended results' list, the default's form
and the relation's context. Proved by
normalization at a level, the lookup at the index by the hypothesis. -/
def splitConv (P : Prog) (S : Defs) : Step :=
  ("splitConv", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, evalMore⟩
    let Γ := [list treeTy, treeTy, bitsTy, treeTy, treeTy, treeTy, list treeTy, list treeTy,
      list treeTy, list treeTy, treeTy, treeTy, treeTy, treeTy, Defs3.ctxTy]
    let pairV (a b : Term) : Term := nodeT (Term.pair (numeral Kernel.Label.pair)
      (consT treeTy a (consT treeTy b (nilT treeTy))))
    let ofL (xs : Term) : Term := pc P "Eval.ofList" [v 4, xs]
    let env := consT treeTy (v 1) (v 0)
    let hyp := Term.eq (pc P "Prelude.nth" [env, leafT (v 2)])
      (pc P "Prelude.some" [pairV (v 3) (ofL (consT treeTy (v 5) (v 6)))])
    let sk ← splitK P E ix (v 7) (v 8) (v 9) (v 10) (v 11) (v 12) (v 13) (v 2)
    let val := pairV (v 5) (ofL (v 6))
    let a : Internal.Thm := ⟨0, Γ, [Internal.Logic.tt P.o, hyp],
      S.conv (Term.lam nat (S.evN (Term.fst (v 15)) (v 0) (sh 1 (consT treeTy (v 1) (v 0)))
        (sh 1 sk))) (Term.lam treeTy (Term.eq (v 0) (sh 1 val)))⟩
    let lv : Term := (8 : ℕ).rec zeroN fun _ t ↦ succN t
    -- the lookup's hypothesis normalized, in which form the evaluation's lookup occurs
    let ranged (k : Deducer) : Deducer := normHyps K [1] k
    let some d := dConv K.L K.G K.E S lv val
        (linkK K "splitConv stable" (ranged K.byNorm))
        (linkK K "splitConv value" (ranged (K.norm K.byNorm)))
        a.ctx a.hyps a.concl
      | dbgTrace "splitConv: not proved" fun _ ↦ none
    pure (a, d))

/-- The forcing of the split's first converges related at the result type: the split's value
the environment's first, the pair of a suspended result related at the type of a suspended result
and a rest. In the context of the environment's tail, the suspended result, the rest, the result
type and the relation's context. The forcing is the application of the split's first to the unit
value ({lit}`appCompat`): the first converges to the suspended result at once, and the unit value to
itself, related at the unit type by the relation's unfolding. -/
def forceConv (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("forceConv", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, evalMore⟩
    let Γ := [list treeTy, treeTy, treeTy, treeTy, Defs3.ctxTy]
    let pairV := nodeT (Term.pair (numeral Kernel.Label.pair)
      (consT treeTy (v 1) (consT treeTy (v 2) (nilT treeTy))))
    let env := consT treeTy pairV (v 0)
    let some fk := resK E ix "forceRes" [] | none
    let some [f, x] := nodeKidsT fk | none
    let unitTy := pc P "Typing.tyUnit" []
    let a : Internal.Thm := ⟨0, Γ, [Internal.Logic.tt P.o,
        Term.app (T.relT (v 4) (thunkTy P (v 3))) (v 1)],
      S.conv (Term.lam nat (S.evN (Term.fst (v 5)) (v 0) (sh 1 env) fk)) (T.relT (v 4) (v 3))⟩
    let lv1 : Term := succN (succN (succN zeroN))
    let some d := (K.cutThm "appCompat" (fun _ ↦ [env, x, f, v 3, unitTy, v 4]) <|
        K.impE (linkK K "forceConv: the first" fun Γ Φ ψ ↦
          dConv K.L K.G K.E S lv1 (v 1) (linkK K "forceConv: first stable" K.byNorm)
            (linkK K "forceConv: first related" (K.norm (K.byHyp 1))) Γ Φ ψ) <|
        K.impE (linkK K "forceConv: the unit" fun Γ Φ ψ ↦
          dConv K.L K.G K.E S lv1 (nodeT (Term.pair (numeral Kernel.Label.unit) (nilT treeTy)))
            (linkK K "forceConv: unit stable" K.byNorm)
            (linkK K "forceConv: unit related" fun Γ Φ ψ ↦
              dRwBy (evalRw K.G K.E (K.rules Φ ++ [.delta T.q]) .full) (K.solve 3) Γ Φ ψ)
            Γ Φ ψ) <|
        linkK K "forceConv: the application" fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ)
        a.ctx a.hyps a.concl
      | dbgTrace "forceConv: not proved" fun _ ↦ none
    pure (a, d))

/-- The kernel's construction of lists compatible with the relation: where a head converges to a
value related at a type and a tail to a value related at its list type, their construction
converges to a value related at the list type. In the context of the environment, the tail, the
head, the element type and the relation's context. The head's and the tail's convergences' parts;
the tail's value a list value ({lit}`relTList1`), its test decided; the thresholds shifted to
their sum, a level above which the construction evaluates to the node of the two values, a list
value whose elements are related. -/
def consCompat (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("consCompat", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, ["relTList1"]⟩
    let L := K.L
    let o := P.o
    let Γ := [list treeTy, treeTy, treeTy, treeTy, Defs3.ctxTy]
    let listTy (A : Term) : Term := nodeT (Term.pair (numeral Kernel.Label.tyList)
      (consT treeTy A (nilT treeTy)))
    let consK (h t : Term) : Term := nodeT (Term.pair (numeral Kernel.Label.cons)
      (consT treeTy h (consT treeTy t (nilT treeTy))))
    let cv (t ty : Term) : Term :=
      S.conv (Term.lam nat (S.evN (Term.fst (v 5)) (v 0) (v 1) (sh 1 t))) (T.relT (v 4) ty)
    let a : Internal.Thm := ⟨0, Γ, [],
      Internal.Logic.imp o (cv (v 2) (v 3)) <| Internal.Logic.imp o (cv (v 1) (listTy (v 3))) <|
        cv (consK (v 2) (v 1)) (listTy (v 3))⟩
    let d? : Deducer := dImpI L <| dImpI L <| fun Γ₀ Φ₀ ψ₀ ↦
      dRwHyp (evalRw K.G K.E [.delta (S.q + 2)] .head) 0 (K.exE <| K.exE <| K.conjE
        fun Γ₁ Φ₁ ψ₁ ↦
        let (nx, wx) := (Γ₁.length - 2, Γ₁.length - 1)
        let (sx, ex) := (Φ₁.length - 2, Φ₁.length - 1)
        dRwHyp (evalRw K.G K.E [.delta (S.q + 2)] .head) 1 (K.exE <| K.exE <| K.conjE
          fun Γ₂ Φ₂ ψ₂ ↦
          let (nxs, wxs) := (Γ₂.length - 2, Γ₂.length - 1)
          let (sxs, exs) := (Φ₂.length - 2, Φ₂.length - 1)
          let w (Γ : List Tree) : Term := consK (atPos wx Γ) (atPos wxs Γ)
          let X := evalTools K Φ₂ [sx, ex, sxs, exs] [.thm (ix "relTList1") []]
          let kept (Φ : List Term) : List ℕ :=
            ((List.range Φ.length).filter fun h ↦
              h ∈ [sx, ex, sxs, exs] ∨ Φ₂.length ≤ h).reverse
          let auto : ℕ → Deducer := fun d ↦ d.rec (fun _ _ _ ↦ none) fun _ rec ↦ X.norm
            fun Γ Φ ψ ↦
            if ψ == Internal.Logic.tt P.o then some Internal.Logic.trueI else
            match defnParts ψ with
            | some (i, _, _) =>
              if i = P.o + 1 then dConjI L rec rec Γ Φ ψ else
              (kept Φ).findSome? fun h ↦ X.byHyp h Γ Φ ψ
            | none => ((kept Φ).findSome? fun h ↦
                X.byHyp h Γ Φ ψ).orElse fun _ ↦ X.byNorm Γ Φ ψ
          let fin : Deducer := fun Γ Φ ψ ↦
            let x₁ := Φ.length - 2
            let xs₁ := Φ.length - 1
            X.norm (dConv L K.G K.E S (succN (S.add (atPos nx Γ) (atPos nxs Γ))) (w Γ)
              (linkK K "consCompat stable" <|
                X.inst x₁ (fun _ ↦ succN (v 0)) (X.inst xs₁ (fun _ ↦ succN (v 0)) X.byNorm))
              (linkK K "consCompat related" (auto 5))) Γ Φ ψ
          let shifted : Deducer := linkK K "consCompat: shifted" <|
            shiftK K sx false (atPos nxs) <| shiftK K sxs true (atPos nx) fin
          -- the tail's value a list value: its test decided, false refuting its truth
          let tailList : Deducer := K.conjE fun Γ Φ ψ ↦
            let lt := Φ.length - 2
            linkK K "consCompat: the tail's list" (decideIn K
              (fun Γ ↦ pc P "Prelude.isSome" [pc P "Eval.listOf" [atPos wxs Γ]])
              (K.hypFalse lt) shifted) Γ Φ ψ
          linkK K "consCompat: the tail's relation"
            (dRwHyp (evalRw K.G K.E (X.rs Φ₂) .full) exs tailList) Γ₂ Φ₂ ψ₂) Γ₁ Φ₁ ψ₁) Γ₀ Φ₀ ψ₀
    let some d := d? a.ctx a.hyps a.concl | dbgTrace "consCompat: not proved" fun _ ↦ none
    pure (a, d))

/-- A goal of convergence to a value of which the η-expansion of a relation holds, reduced to the
convergence related by the relation itself: the expansion's equation with the relation, by
extensionality, rewriting the goal. -/
def etaGoal (K : Kit) (k : Deducer) : Deducer := fun Γ Φ ψ ↦ do
  let [Pr, _] := ψ.children | none
  let [b] := Pr.children | none
  let [X, _] := b.children | none
  let eta := Term.eq Pr (Term.subst X fun j ↦ v (j - 1))
  let dEta ← dEq (Internal.byFunExt K.P.G 0 (byMode .full K.P.G K.E 0 [.rule .beta])) Γ [] eta
  dCut eta dEta (fun Γ Φ ψ ↦ dRwBy (evalRw K.G K.E [.hyp (Φ.length - 1)] .full) k Γ Φ ψ) Γ Φ ψ

/-- The right fold forcing the split's rest converges related at the list type of the result
type: the environment's value at the split's index the pair of a value and the list value of
suspended results, each related at the type of a suspended result. In the context of the
environment's tail after the children remaining's value, that value, the index's bitstring, the
pair's first component, the results' type, the results, the result type, the type abbreviations,
the forms of the types of a suspended result, of the results' list and of the result, and the
relation's context. The fold
is the application of the right fold's constant ({lit}`relFoldrT`) to its step, the empty list and
the split's rest ({lit}`appCompat`), each function's relation the η-expansion's; the step two
abstractions ({lit}`lamCompatC`) over the construction ({name}`consCompat`) of the forced head
({lit}`appCompat`) and the rest; the empty list related by {lit}`relTList1`, and the split's rest
by {lit}`relOfListT`. -/
def foldConv (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("foldConv", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, evalMore⟩
    let L := K.L
    let s := Term.star
    let Γ₀ := [list treeTy, treeTy, bitsTy, treeTy, treeTy, list treeTy, treeTy, list treeTy,
      treeTy, treeTy, treeTy, Defs3.ctxTy]
    let (env0, lv, b, dv, A, rs, R, tys, thF, lrF, rF, D) :=
      (atPos 11, atPos 10, atPos 9, atPos 8, atPos 7, atPos 6, atPos 5, atPos 4, atPos 3, atPos 2,
        atPos 1, atPos 0)
    -- the kernel's types of a suspended result and of the results' list, their forms' readings
    let readK (F : List Tree → Term) (Γ : List Tree) : Term :=
      pc P "Prelude.get" [pc P "Reader.readType" [tys Γ, F Γ]]
    let (thK, lrK) := (readK thF, readK lrF)
    let node (l : ℕ) (xs : List Term) : Term :=
      nodeT (Term.pair (numeral l) (xs.foldr (consT treeTy) (nilT treeTy)))
    let arrowT (A B : Term) : Term := node Kernel.Label.tyArrow [A, B]
    let listTy (A : Term) : Term := node Kernel.Label.tyList [A]
    let unitTy := pc P "Typing.tyUnit" []
    let th (Γ : List Tree) : Term := arrowT unitTy (R Γ)
    let listR (Γ : List Tree) : Term := listTy (R Γ)
    let listTh (Γ : List Tree) : Term := listTy (th Γ)
    let stepTy (Γ : List Tree) : Term := arrowT (th Γ) (arrowT (listR Γ) (listR Γ))
    let env (Γ : List Tree) : Term := consT treeTy (lv Γ) (env0 Γ)
    -- the kernel's terms, in the lemma's context
    let sndK ← resK E ix "sndQRes" [s, s, s, b Γ₀]
    let nilK ← resK E ix "nilRes" [rF Γ₀, s, tys Γ₀, s]
    let hfK ← resK E ix "headForceRes" []
    let var0K ← resK E ix "aARes" []
    let bodyK ← resK E ix "consRes" [s, s, s, s, s, hfK, var0K]
    let stepK ← resK E ix "lamHARes" [thF Γ₀, lrF Γ₀, s, s, tys Γ₀, s, bodyK]
    let foldK ← resK E ix "foldrRes" [thF Γ₀, lrF Γ₀, s, s, s, s, tys Γ₀, s, stepK, nilK, sndK]
    let [f2, _] ← nodeKidsT foldK | none
    let [f1, _] ← nodeKidsT f2 | none
    let [fc, _] ← nodeKidsT f1 | none
    let [_, innerK] ← nodeKidsT stepK | none
    let [var1K, unitK] ← nodeKidsT hfK | none
    let pairV := node Kernel.Label.pair [dv Γ₀, pc P "Eval.ofList" [A Γ₀, rs Γ₀]]
    let hyps := [Internal.Logic.tt P.o,
      Term.eq (pc P "Prelude.nth" [env Γ₀, leafT (b Γ₀)]) (pc P "Prelude.some" [pairV]),
      S.allL (T.relT (D Γ₀) (th Γ₀)) (rs Γ₀)]
    let concl := S.conv (Term.lam nat (S.evN (Term.fst (sh 1 (D Γ₀))) (v 0) (sh 1 (env Γ₀))
      (sh 1 foldK))) (T.relT (D Γ₀) (listR Γ₀))
    -- a term of the lemma's context in a context extending it
    let up (t : Term) (Γ : List Tree) : Term := sh (Γ.length - Γ₀.length) t
    let byLast : Deducer := fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ
    -- an application related, by the function's relation and the argument's
    let app (e x f cod dom : List Tree → Term) (pf px : Deducer) : Deducer :=
      K.cutThm "appCompat" (fun Γ ↦ [e Γ, x Γ, f Γ, cod Γ, dom Γ, D Γ]) <|
        K.impE (etaGoal K pf) <| K.impE px byLast
    let lv1 : Term := succN (succN (succN zeroN))
    -- a value converging at once, related by a deducer
    let atOnce (msg : String) (w : List Tree → Term) (rel : Deducer) : Deducer := fun Γ Φ ψ ↦
      dConv L K.G K.E S lv1 (w Γ) (linkK K s!"foldConv: {msg} stable" K.byNorm)
        (linkK K s!"foldConv: {msg} related" rel) Γ Φ ψ
    let unitRel : Deducer := atOnce "the unit" (fun _ ↦ node Kernel.Label.unit [])
      fun Γ Φ ψ ↦ dRwBy (evalRw K.G K.E (K.rules Φ ++ [.delta T.q]) .full) (K.solve 3) Γ Φ ψ
    -- the step's body, beneath the step's two values, the suspended result x and the rest y,
    -- related by the hypotheses hx and hy
    let body (x y : List Tree → Term) (hx hy : ℕ) : Deducer :=
      let env2 (Γ : List Tree) : Term := consT treeTy (y Γ) (consT treeTy (x Γ) (up (env Γ₀) Γ))
      K.cutThm "consCompat" (fun Γ ↦ [env2 Γ, up var0K Γ, up hfK Γ, R Γ, D Γ]) <|
        K.impE (linkK K "foldConv: the forced head" <|
          app env2 (up unitK) (up var1K) R (fun _ ↦ unitTy)
            (atOnce "the suspended result" x (K.norm (K.byHyp hx))) unitRel) <|
        K.impE (linkK K "foldConv: the rest" (atOnce "the rest" y (K.norm (K.byHyp hy))))
          byLast
    -- the step's two abstractions
    let stepRel : Deducer :=
      K.cutThm "lamCompatC" (fun Γ ↦ [env Γ, up innerK Γ, thK Γ, arrowT (listR Γ) (listR Γ),
          th Γ, D Γ]) <|
        K.impE (linkK K "foldConv: the outer abstraction" <| dAllI L <| dImpI L
          fun Γ₁ Φ₁ ψ₁ ↦
          let x := atPos (Γ₁.length - 1)
          let hx := Φ₁.length - 1
          (K.cutThm "lamCompatC" (fun Γ ↦ [consT treeTy (x Γ) (env Γ), up bodyK Γ, lrK Γ,
              listR Γ, listR Γ, D Γ]) <|
            K.impE (linkK K "foldConv: the inner abstraction" <| dAllI L <| dImpI L
              fun Γ₂ Φ₂ ψ₂ ↦
              linkK K "foldConv: the body" (body x (atPos (Γ₂.length - 1)) hx (Φ₂.length - 1))
                Γ₂ Φ₂ ψ₂) (linkK K "foldConv: the inner conclusion" byLast)) Γ₁ Φ₁ ψ₁)
          (linkK K "foldConv: the outer conclusion" byLast)
    -- the fold's constant, related by {lit}`relFoldrT` at the carried types
    let fcRel : Deducer := atOnce "the fold's constant" (up fc)
      (K.cutThm "relFoldrT" (fun Γ ↦ [listR Γ, th Γ, D Γ, lrK Γ, thK Γ]) (K.norm byLast))
    let nilRel : Deducer := atOnce "the empty list" (up nilK)
      fun Γ Φ ψ ↦ dRwBy (evalRw K.G K.E (K.rules Φ ++ [.thm (ix "relTList1") []]) .full)
        (K.solve 3) Γ Φ ψ
    let sndRel : Deducer := fun Γ Φ ψ ↦
      dConv L K.G K.E S (succN lv1) (pc P "Eval.ofList" [A Γ, rs Γ])
        (linkK K "foldConv: the split's rest stable" (normHyps K [1] K.byNorm))
        (linkK K "foldConv: the split's rest related" <|
          K.cutThm "relOfListT" (fun Γ ↦ [rs Γ]) <| K.allEΓ A <| K.allEΓ D <| K.allEΓ th <|
            K.impE (K.byHyp 2) (K.norm byLast)) Γ Φ ψ
    let main : Deducer :=
      app env (up sndK) (up f2) listR listTh
        (linkK K "foldConv: the fold at its step and start" <|
          app env (up nilK) (up f1) (fun Γ ↦ arrowT (listTh Γ) (listR Γ)) listR
            (linkK K "foldConv: the fold at its step" <|
              app env (up stepK) (up fc)
                (fun Γ ↦ arrowT (listR Γ) (arrowT (listTh Γ) (listR Γ))) stepTy
                (linkK K "foldConv: the fold's constant" fcRel)
                (linkK K "foldConv: the step" stepRel))
            (linkK K "foldConv: the empty list" nilRel))
        (linkK K "foldConv: the split's rest" sndRel)
    let some d := main Γ₀ hyps concl | dbgTrace "foldConv: not proved" fun _ ↦ none
    pure (⟨0, Γ₀, hyps, concl⟩, d))

/-- The suspended results' relation ({name}`relatedT`) at constructions of a child and a result
gives it at the rests: at an index, the constructions' at its successor ({lit}`nthSuccRaw`). In
the context of the rest of the results, the result, the rest of the children, the child, the
result type, the relation's context, the datatype and the typing environment. -/
def relatedTail (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("relatedTail", fun ix E ↦ do
    let K : Kit := ⟨walkProg P, S, E, ix, []⟩
    let L := K.L
    let Γ := [list treeTy, treeTy, list treeTy, treeTy, treeTy, Defs3.ctxTy, treeTy, T.envTy]
    let rel (ts rs : Term) : Term := relatedT P T (v 7) (v 6) (v 5) (v 4) ts rs
    let a : Internal.Thm := ⟨0, Γ, [Internal.Logic.tt P.o,
      rel (consT treeTy (v 3) (v 2)) (consT treeTy (v 1) (v 0))], rel (v 2) (v 0)⟩
    let (rs, r, ts, t) := (atPos 7, atPos 6, atPos 5, atPos 4)
    -- beneath the index, the last variable: the lookup at its successor in a construction
    let succAt (xs x : List Tree → Term) (k : Deducer) : Deducer :=
      K.cutThm "nthSuccRaw" (fun Γ ↦ [atPos (Γ.length - 1) Γ, xs Γ, x Γ]) (normLastK K k)
    let some d := (dAllI L <| dImpI L fun Γ Φ ψ ↦
        let iMem := Φ.length - 1
        (succAt ts t <| succAt rs r <|
          dAllE L K.G K.E 1 (call D.succ [] [atPos (Γ.length - 1) Γ]) <|
          K.impE (linkK K "relatedTail: the member" (K.byHyp iMem)) <|
          linkK K "relatedTail: the result" fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ) Γ Φ ψ)
        a.ctx a.hyps a.concl
      | dbgTrace "relatedTail: not proved" fun _ ↦ none
    pure (a, d))

/-- Where the children are as many as the suspended results, related ({name}`relatedT`), and each
child's memberships pass the test of a field of the datatype, every result is related at the type
of a suspended result: by induction on the children, at a construction the results a
construction, the head's test decided, false refuting the children's, the head result related at
the index zero and the rest by the induction hypothesis at the rests ({name}`relatedTail`). -/
def resultsRel (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("resultsRel", fun ix E ↦ do
    let K : Kit := ⟨walkProg P, S, E, ix, []⟩
    -- the comparisons of lengths at constructions, for the lengths' hypothesis alone
    let KL : Kit := { K with more := lenRules.filter fun nm ↦ 0 < ix nm ∧ ix nm < E.size }
    let L := K.L
    let o := P.o
    let all (A : Tree) (t : Term) : Term := Internal.Logic.all o A (Term.lam A t)
    let imp := Internal.Logic.imp o
    -- under the quantifiers: the results v0, the result type v1, the relation's context v2, the
    -- datatype v3, the typing environment v4, then the children v5
    let ms := pc P "Typing.envMs" [v 4]
    let mem := Term.lam treeTy (pc P "Typing.memberships" [sh 1 ms, v 0])
    let okT := Term.lam (list treeTy) (Term.lam treeTy (pc P "Prelude.and"
      [pc P "Typing.fieldOk" [sh 2 ms, v 5, v 1], v 0]))
    let oks := foldrT (list treeTy) treeTy okT (leafT (numeral 1)) (mapListsT mem (v 5))
    let φ := all T.envTy <| all treeTy <| all Defs3.ctxTy <| all treeTy <| all (list treeTy) <|
      imp (relatedT P T (v 4) (v 3) (v 2) (v 1) (v 5) (v 0)) <| imp (truth o oks) <|
      imp (lenEqT P (v 5) (v 0)) <| S.allL (T.relT (v 2) (thunkTy P (v 1))) (v 0)
    let intros (k : Deducer) : Deducer :=
      (List.range 5).foldr (fun _ k ↦ dAllI L k) <| dImpI L <| dImpI L <| dImpI L k
    let byLast : Deducer := fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ
    -- the lengths' hypothesis refuted, one comparison true
    let lenFalse (hLen : ℕ) : Deducer := dConjE L hLen fun Γ Φ ψ ↦
      let refuted (h : ℕ) : Deducer := dImpE L h (KL.solve 3) fun Γ Φ ψ ↦
        K.hypFalse (Φ.length - 1) Γ Φ ψ
      (refuted (Φ.length - 2) Γ Φ ψ).orElse fun _ ↦ refuted (Φ.length - 1) Γ Φ ψ
    -- the empty children: the results empty, else the lengths unequal
    let d₀ ← linkK K "resultsRel: none" (intros fun Γ Φ ψ ↦
        let hLen := Φ.length - 1
        K.listCase treeTy (atPos (Γ.length - 1) Γ) (K.solve 3)
          (linkK K "resultsRel: none, more results" (lenFalse hLen)) Γ Φ ψ) [] []
      (Term.subst φ (Internal.instVar (nilT treeTy)))
    -- a construction: context the rest, the head, then the quantified typing environment,
    -- datatype, relation's context, result type and results; hypotheses the induction hypothesis,
    -- the quantifiers' truths, the relation, the tests and the lengths
    let cons : Deducer := intros fun Γ₁ Φ₁ ψ₁ ↦
      let (t, tsR, Ev, dt, D, R, rs) :=
        (atPos 0, atPos 1, atPos 2, atPos 3, atPos 4, atPos 5, atPos 6)
      let (hRel, hOks, hLen) := (Φ₁.length - 3, Φ₁.length - 2, Φ₁.length - 1)
      let msT (Γ : List Tree) : Term := pc P "Typing.envMs" [Ev Γ]
      let headOk (Γ : List Tree) : Term := pc P "Typing.fieldOk" [msT Γ, dt Γ,
        pc P "Typing.memberships" [msT Γ, t Γ]]
      K.listCase treeTy (rs Γ₁) (linkK K "resultsRel: fewer results" (lenFalse hLen))
        (fun Γ₂ Φ₂ ψ₂ ↦
          let (r, rsR) := (atPos (Γ₂.length - 2), atPos (Γ₂.length - 1))
          -- the head result related at the index zero
          let head : Deducer := linkK K "resultsRel: the head" <|
            dAllE L K.G K.E hRel bnilT <|
            K.impE (linkK K "resultsRel: the head a member" (K.solve 3)) <| K.conjE byLast
          -- the rest by the induction hypothesis at the rests
          let tail : Deducer := linkK K "resultsRel: the rest" <|
            (fun Γ Φ ψ ↦ dAllE L K.G K.E 0 (Ev Γ) (K.allEΓ dt <| K.allEΓ D <| K.allEΓ R <|
              K.allEΓ rsR <|
            K.impE (linkK K "resultsRel: the rests related" <|
              applyThm K "relatedTail" (fun Γ ↦ [rsR Γ, r Γ, tsR Γ, t Γ, R Γ, D Γ, dt Γ, Ev Γ])
                [K.solve 3, K.byHyp hRel] byLast) <|
            K.impE (linkK K "resultsRel: the rest's tests" (K.byHyp hOks)) <|
            K.impE (linkK K "resultsRel: the rests' lengths" (KL.byHyp hLen)) byLast) Γ Φ ψ)
          decideIn K headOk (linkK K "resultsRel: the head's test false" (K.hypFalse hOks))
            (K.norm (dConjI L head tail)) Γ₂ Φ₂ ψ₂) Γ₁ Φ₁ ψ₁
    let some d₁ := linkK K "resultsRel: a construction" cons [list treeTy, treeTy]
        [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
      | dbgTrace "resultsRel: not proved" fun _ ↦ none
    pure (⟨0, [list treeTy], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The development of the soundness at a structural recursion. -/
def cataDev (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  (cataExcluded P).map (fun (n, nm) ↦ atomExcluded P S nm n) ++ fragNums P S T ++ fragRes P S T ++
    fragNone P S T ++ cataBindEqs P S T ++ [nthOne P S 4, nthTwo P S 3, nthTwo P S 4] ++
    cataConvs P S ++
    [indexNone P S, foldRes P S, splitRes P S, cataStepRes P S false, cataStepRes P S true,
      relatedTail P S T, resultsRel P S T, splitConv P S,
      forceConv P S T, consCompat P S T, lamCompatC P S T, foldConv P S T, clauseVarAtom P S T,
      unnamedAt "unnamedVar" (fun P c ↦ Term.eq (call D.lab []
        [pc P "implName" [nodeT (Term.pair (numeral 0) c)]]) (nilT bitTy)) P S,
      unnamedAt "unnamedNum"
        (fun P c ↦ truth P.o (pc P "Prelude.isSome" [pc P "Reader.numeral" [c]])) P S,
      cataWalk P S T]

/-- The soundness at a structural recursion, after the case analysis's development. -/
def cataCertificates (P : Prog) (S : Defs) (T : Defs3) (before : List Internal.Thm) :
    Except String (List Stored.Cert) := do
  let some names := caseNames P S T | throw "the base is not stated"
  certifyAfter P (names ++ (caseDev P S T).map (·.1) ++ (clausesDev P S T).map (·.1) ++
    (caseSoundDev P S T).map (·.1)) "datatype-cata" (cataDev P S T) before

end GebTests.Prototypes.FreeTopos.Datatypes
