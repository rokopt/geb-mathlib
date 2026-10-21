/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.DatatypeAssembly
public meta import GebTests.Prototypes.FreeTopos.DatatypeAssembly -- shake: keep
public import GebTests.Prototypes.FreeTopos.NormalizationRel
public meta import GebTests.Prototypes.FreeTopos.NormalizationRel -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The datatype language's soundness at the kernel's constants

The constants of the kernel but the primitives, the folds of trees, iteration, the right fold of
lists and case analysis of lists, related at their types in the datatype language
({lit}`GebTests.Prototypes.FreeTopos.DatatypeBase`): the lemmas of the normalization proof on the
evaluator's folds and constants ({name}`GebTests.Prototypes.FreeTopos.Normalization.constDev`,
{name}`GebTests.Prototypes.FreeTopos.Normalization.foldRelDev`) at the relation at the datatype
language's types ({lit}`relTSpec`). The types a constant carries are quantified apart from the types
it is related at: the evaluator reads a fold's type only into the empty list values it builds,
whose elements no type constrains, and the reader gives a constant the erasure of the type the
typing reads.

A list headed by a constant's keyword, its types and further elements after it, is then sound as the
application of the constant to the further elements ({lit}`constCore`): the keyword no numeral
abbreviation, as the reader reserves it, its index among the reserved names present by lemmas on the
index at a list with the list a variable ({lit}`indexOfMore`, {lit}`reservedK`); the stage
functions' equations at the form cut in; each type's readings, the typing's and the reader's,
present, generalized, the constant related at the typing's type of it; and the soundness at the
application of the constant to the further elements, by induction on them
({name}`GebTests.Prototypes.FreeTopos.Datatypes.spineK`). At source forms it follows from the
soundness at expanded forms ({lit}`constSrc`, by
{name}`GebTests.Prototypes.FreeTopos.Datatypes.srcSound`), fewer types than the keyword reads
refuted by the typing.

## Main definitions

* {lit}`relTSpec` — the relation at the datatype language's types, as the normalization proof's
  lemmas take a relation.
* {lit}`ConstForm`, {lit}`constForms` — the keywords of the constants, with their types.
* {lit}`indexOfMore`, {lit}`reservedK` — a keyword's index among the reserved names present.
* {lit}`constCore`, {lit}`constSrc` — the soundness at a list headed by such a keyword at
  expanded and at source forms.
* {lit}`foldsDev3` — the development.
* {lit}`foldsCertificates` — the development, stored as the certificate {lit}`datatype-folds`.

## References

* {cite}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, datatypes, soundness, fold, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Datatypes

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Translation Geb.FreeTopos.Tactics
open GebTests.Prototypes.FreeTopos.Weakening
open scoped FinEnum

open Internal (Term)
open GebTests.Prototypes.FreeTopos.Normalization

/-- A type of the datatype language of a label over types, as the typing writes it. -/
def tyNode (l : ℕ) (tys : List Term) : Term :=
  nodeT (Term.pair (numeral l) (tys.foldr (consT treeTy) (nilT treeTy)))

/-- The relation at the datatype language's types: its context the program's definitions and the
markers of its datatypes, the evaluator's definitions the context's first component, its types
the typing's, the constants' types the typing's, the types the constants carry quantified apart,
and its equations at a node of a type those of the trees, the arrows and the lists. -/
def relTSpec (P : Prog) (T : Defs3) : RelSpec where
  ctxTy := Defs3.ctxTy
  rel := T.relT
  defs := Term.fst
  tyTree := tyNode Kernel.Label.tyTree []
  tyArrow A B := tyNode Kernel.Label.tyArrow [A, B]
  tyList A := tyNode Kernel.Label.tyList [A]
  foldTy A := pc P "Typing.foldTyOf" [A]
  iterTy A := pc P "Typing.iterTyOf" [A]
  foldrTy A B := pc P "Typing.foldrTyOf" [A, B]
  lcaseTy A B := pc P "Typing.lcaseTyOf" [A, B]
  annotated := true
  more := ["relTTree", "relTArrow", "relTList1"]
  name := (· ++ "T")

/-- A keyword of the kernel's constants applied to types and to further elements: the keyword, the
number of types it reads, the constant's label, the typing's type of the constant at the types, and
the constant's relation at that type ({lit}`foldsDev3`). -/
structure ConstForm where
  /-- The keyword's definition. -/
  kw : String
  /-- The number of types the keyword reads. -/
  ntys : ℕ
  /-- The constant's label. -/
  label : ℕ
  /-- The typing's definition of the constant's type at the types. -/
  tyOf : String
  /-- The constant's relation at that type. -/
  rel : String

/-- The keywords of the kernel's constants but the primitives. -/
def constForms : List ConstForm :=
  [⟨"Reader.kwFold", 1, Kernel.Label.fold, "Typing.foldTyOf", "relFoldT"⟩,
    ⟨"Reader.kwPara", 1, Kernel.Label.para, "Typing.foldTyOf", "relParaT"⟩,
    ⟨"Reader.kwIter", 1, Kernel.Label.iter, "Typing.iterTyOf", "relIterT"⟩,
    ⟨"Reader.kwFoldr", 2, Kernel.Label.foldr, "Typing.foldrTyOf", "relFoldrT"⟩,
    ⟨"Reader.kwLcase", 2, Kernel.Label.lcase, "Typing.lcaseTyOf", "relLcaseT"⟩]

namespace ConstForm

variable (c : ConstForm)

/-- The context of a keyword's form after the soundness's quantifiers, the innermost first: the
second type where it reads two, the further elements, the first type; so that the further elements
and the first type are at the positions of those of an application ({name}`appCtx`). -/
def ctx : List Tree := List.replicate (c.ntys - 1) treeTy ++ [list treeTy, treeTy]

/-- The position of the further elements in the context, the first type's 0. -/
def tailPos : ℕ := 1

/-- The position of the type of index j in the context. -/
def tyPos (j : ℕ) : ℕ := if j = 0 then 0 else j + 1

/-- The keyword applied to its types and to the further elements, under the soundness's
quantifiers, the context's variables after them. -/
def form (P : Prog) : Term :=
  let n := c.ctx.length
  let at_ (p : ℕ) : Term := v (nQ + n - 1 - p)
  nodeT (Term.pair (numeral 2) (consT treeTy (kwAtom P c.kw)
    ((List.range c.ntys).foldr (fun j t ↦ consT treeTy (at_ (ConstForm.tyPos j)) t)
      (at_ ConstForm.tailPos))))

/-- That the keyword is no numeral abbreviation, under the soundness's quantifiers: the test of
its abbreviation's presence false, its label empty. -/
def notAbbrev (P : Prog) : Term :=
  Term.eq (call D.lab [] [pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev" [pc P c.kw [], v 3]]])
    bnilT

/-- The name of the stage functions' equation of index i at the keyword's form. -/
def eqName (i : ℕ) : String := s!"{c.kw}/const{i}"

/-- The name of the soundness at the keyword's form at expanded forms. -/
def coreName : String := s!"{c.kw}/core"

/-- The soundness at the keyword's form at expanded forms, in the context {name}`ctx`, given that
at each further element. -/
def coreThm (P : Prog) (S : Defs) (T : Defs3) : Internal.Thm :=
  let n := c.ctx.length
  ⟨0, c.ctx, [S.allL (Term.lam treeTy (expandedφ P S T)) (v (n - 1 - ConstForm.tailPos))],
    expansionφ P S T (pc P "Prelude.some" [c.form P])⟩

end ConstForm

/-- The first application of the definition of index k to two arguments among a term's subterms
outside its binders, its second argument mentioning the variable of index i. -/
def appOf2 (k i : ℕ) : Term → Option Term := RoseTree.para fun l cs ↦
  let t : Term := RoseTree.node l (cs.map Prod.fst)
  let found : Bool := match l, cs.map Prod.fst with
    | .app, [f, a] => (match f.label, f.children with
        | .app, [g, _] => (match g.label with
          | .defn j _ => j == k
          | _ => false)
        | _, _ => false) && Term.occurs a i
    | _, _ => false
  if found then some t else (cs.zipIdx.filterMap fun ((_, r), j) ↦
    if Internal.sameCtx l j then r else none).head?

/-- The program with the typing's and the reader's readings of a type kept folded as well, so that
the readings of a type that is a variable stay single terms, which the soundness at a keyword's
form decides present. -/
def readingsFolded (P : Prog) : Prog :=
  { P with folded := P.folded ++ ["Typing.readTy", "Reader.readType"] }

/-- The comparisons of the numerals one and two with a bitstring's second and third successors,
true, which the typing and the reader test a keyword's arity by: by case analysis of the
bitstring's bits, the comparison recursing on its second number. -/
def ltMore (P : Prog) : List Step :=
  let rs := foldedRules P
  let sc (t : Term) : Term := call D.succ [] [t]
  let lt (n : ℕ) : Internal.Thm :=
    nfThm P rs [bitsTy] (call D.ltB [] [numeral n, n.rec (sc (v 0)) fun _ t ↦ sc t]) trueT
  let byBit (a : Internal.Thm) (ix : String → ℕ) (E : Array Internal.Entry) :
      Option Internal.Deriv :=
    let p : Internal.Prover := fun Γ Φ t u ↦ byWeak P.G E 0 (rulesNth P ix) Γ Φ t u
    byBits P.G p 4 0 a.ctx [] (TranslationProofs.sides a).1 (TranslationProofs.sides a).2
  [1, 2].map fun n ↦ step s!"ltSucc{n}" (lt n) (byBit (lt n))

/-- The reader's index of a name among names present past a further name, and among names headed
by the name itself; in the context of the names, the further name and the name, the innermost
first, the further name's equality with the name decided, the name's with itself by its
reflexivity. -/
def indexOfMore (P : Prog) (S : Defs) : List Step :=
  let o := P.o
  let isSomeT (t : Term) : Term := truth o (pc P "Prelude.isSome" [t])
  let idx (x xs : Term) : Term := pc P "Reader.indexOf" [x, xs]
  let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
  [("indexOfSkip", fun ix E ↦ do
      let K : Kit := ⟨P, S, E, ix, lookupEqNames⟩
      let equalT ← primT Kernel.Prim.equal
      let Γ := [list treeTy, treeTy, treeTy]
      let φ := Internal.Logic.imp o (isSomeT (idx (v 2) (v 0)))
        (isSomeT (idx (v 2) (consT treeTy (v 1) (v 0))))
      -- the names' positions: the name 0, the further name 1, the names 2
      let d ← dImpI K.L (decideIn K (fun Γ ↦ apps equalT [at_ 0 Γ, at_ 1 Γ])
          (decideIn K (fun Γ ↦ pc P "Prelude.isSome" [idx (at_ 0 Γ) (at_ 2 Γ)]) (anyFalse K)
            (K.solve 3))
          (K.solve 3)) Γ [] φ
      pure (⟨0, Γ, [], φ⟩, d)),
    ("indexOfHere", fun ix E ↦ do
      let K : Kit := ⟨P, S, E, ix, lookupEqNames⟩
      let equalT ← primT Kernel.Prim.equal
      let Γ := [list treeTy, treeTy]
      let φ := isSomeT (idx (v 1) (consT treeTy (v 1) (v 0)))
      let d ← K.cutThm "equalRefl" (fun Γ ↦ [at_ 0 Γ])
          (decideIn K (fun Γ ↦ apps equalT [at_ 0 Γ, at_ 0 Γ]) (anyFalse K) (K.solve 3)) Γ [] φ
      pure (⟨0, Γ, [], φ⟩, d))]

/-- That a keyword is reserved, the reader's index of it among the reserved names present: along
the reserved names' normal form, past each other name by {lit}`indexOfSkip`, at the keyword by
{lit}`indexOfHere` ({name}`indexOfMore`); so that the index is not computed, which unfolds the
index among the rest once for its presence and once for its value at each name before the
keyword. -/
def reservedK (K : Kit) (kw : String) : Deducer := fun Γ Φ ψ ↦ do
  let x ← nfE K.G K.E (K.rules []) Γ (pc K.P kw [])
  let names ← nfE K.G K.E (K.rules []) Γ (pc K.P "Reader.reservedNames" [])
  let parts (t : Term) : Option (Term × Term) := do
    let .arr 1 _ := t.label | none
    let [q] := t.children | none
    let [h, tl] := q.children | none
    pure (h, tl)
  -- the names before the keyword, each with the names after it, and the names after the keyword
  let (before, after) := (List.range 256).foldl (fun (r : List (Term × Term) × Option Term) _ ↦
    match r with
    | (_, some _) => r
    | (acc, none) => match parts ((acc.getLast?.map Prod.snd).getD names) with
      | some (h, tl) => if h == x then (acc, some tl) else (acc ++ [(h, tl)], none)
      | none => r) ([], none)
  let rest ← after
  let last : Deducer := fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ
  before.foldr (fun (h, tl) k ↦ K.cutThm "indexOfSkip" (fun _ ↦ [tl, h, x]) (K.impE k last))
    (K.cutThm "indexOfHere" (fun _ ↦ [rest, x]) last) Γ Φ ψ

/-- The stage functions' equations at a keyword's form ({name}`ConstForm.form`), the test of
source forms, the type and the optional resolution, by {name}`appEq` in the soundness's context
followed by the form's, the keyword no numeral abbreviation ({name}`ConstForm.notAbbrev`), with the
comparisons of the arity ({name}`ltMore`). -/
def constEqs (P : Prog) (S : Defs) (T : Defs3) (c : ConstForm) : List Step :=
  (List.range 3).map fun i ↦
    appEq (readingsFolded P) S T (c.eqName i) i (c.form P) ((appCtx T).take nQ ++ c.ctx)
      (some [c.notAbbrev P]) ["ltSucc1", "ltSucc2"]

/-- The soundness at a keyword's form at expanded forms ({name}`ConstForm.coreThm`): the stage
functions' equations at the form cut in ({name}`constEqs`); each type a source form, the typing's
reading of it and the reader's present, generalized, and the constant over the reader's
generalized; then the soundness at its application to the further elements ({name}`spineK`), the
constant related at the typing's type by its relation, its value itself at the first level. -/
def constCore (P : Prog) (S : Defs) (T : Defs3) (c : ConstForm) : Step :=
  (c.coreName, fun ix E ↦ do
    let n := c.ctx.length
    let W₀ := kwKit (readingsFolded P) S T ix E n ((List.range n).map (· == ConstForm.tailPos)) ""
      true
    let K₀ := appKit (readingsFolded P) S ix E
    let W := { W₀ with K := { K₀ with more := K₀.more ++ ["ltSucc1", "ltSucc2"] } }
    let K := W.K
    let L := K.L
    let a := c.coreThm P S T
    let srcH := pc P "srcForm" [Term.lam treeTy (pc P "Reader.expandNums" [v 4, v 0]), v nQ]
    -- the stage functions' equations at the context's variables
    let eqs (k : Deducer) : Deducer := (List.range 3).foldr (fun i k ↦
      W.cutApply (c.eqName i) (fun Γ ↦ (List.range (nQ + n)).map fun j ↦ atPos (nQ + n - 1 - j) Γ)
        [linkK K s!"{c.coreName}: the keyword not abbreviated" K.byNorm] k) k
    -- a type's reading, the definition named, present: its application to the type's form, as
    -- the stage functions read it, generalized, so that its normal form is written once; its
    -- presence decided, absent refuting the statement's hypothesis of index i; the value present
    -- generalized
    let present (msg reading : String) (i p : ℕ) (k : Deducer) : Deducer := fun Γ Φ ψ ↦ do
      let x := Γ.length - 1 - p
      -- among the hypotheses as they are, the stage functions' equations in normal form; else
      -- in the hypothesis of index i normalized
      let some t := (Φ.findSome? (appOf2 (P.idx reading) x)).orElse fun _ ↦ do
          let (nf, _) ← evalRw K.G K.E (K.rulesEx Φ (W.hyp i)) .full Γ Φ (← Φ[W.hyp i]?)
          appOf2 (P.idx reading) x nf
        | dbgTrace s!"{c.coreName}: {msg}: no reading" fun _ ↦ none
      let opt (Γ' : List Tree) : Term := Term.rename t (· + (Γ'.length - Γ.length))
      (W.generalize opt fun Γ Φ ψ ↦
        let y := atPos (Γ.length - 1)
        decideOpt K y (linkK K s!"{c.coreName}: {msg} absent" (K.hypFalse (W.hyp i)))
          (W.generalize (fun Γ ↦ pc P "Prelude.get" [y Γ]) k) (minimal := true) Γ Φ ψ) Γ Φ ψ
    -- the types' variables, the typing's readings and the reader's, after their decisions
    let types (k : List (List Tree → Term) → List (List Tree → Term) → Deducer) : Deducer :=
      (List.range c.ntys).foldr (fun j (rec : List (List Tree → Term) → List (List Tree → Term) →
          Deducer) tys ks ↦
        let p := ConstForm.tyPos j
        decideIn K (fun Γ ↦ W.inΓ (atPos p) Γ srcH)
          (linkK K s!"{c.coreName}: type {j} not a source form" (W.hypFalseU (W.hyp 4))) <|
        present s!"type {j}'s typing" "Typing.readTy" 6 p fun Γ₁ Φ₁ ψ₁ ↦
          let ty := atPos (Γ₁.length - 1)
          (present s!"type {j}'s reading" "Reader.readType" 7 p
            fun Γ₂ Φ₂ ψ₂ ↦ rec (tys ++ [ty]) (ks ++ [atPos (Γ₂.length - 1)]) Γ₂ Φ₂ ψ₂)
            Γ₁ Φ₁ ψ₁)
        (fun tys ks ↦ k tys ks) [] []
    let constT (ks : List (List Tree → Term)) (Γ : List Tree) : Term :=
      tyNode c.label (ks.map (· Γ))
    let tyHead (tys : List (List Tree → Term)) (Γ : List Tree) : Term :=
      pc P "Prelude.some" [pc P c.tyOf (tys.map (· Γ))]
    -- the constant's convergence related at its type, its value itself at the first level, its
    -- relation by the constant's relation, cut in before the constant is generalized, so that
    -- the generalization rewrites it with the term; then k given its index
    let related (tys ks : List (List Tree → Term)) (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ do
      let R := W.qv 10 Γ
      let sh (t : Term) : Term := Term.rename t (· + 1)
      let φ := S.conv (Term.lam nat (S.evN (Term.fst (sh R)) (v 0) (sh (W.qv 9 Γ))
        (sh (constT ks Γ)))) (T.relT R (pc P c.tyOf (tys.map (· Γ))))
      let σ (Γ : List Tree) : List Term :=
        tys.reverse.map (· Γ) ++ [W.qv 10 Γ] ++ ks.reverse.map (· Γ)
      let dφ ← dConv L K.G K.E S (succN zeroN) (constT ks Γ)
        (linkK K s!"{c.coreName}: the constant's value" K.byNorm)
        (linkK K s!"{c.coreName}: the constant's relation" <|
          K.cutThm c.rel σ fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ) Γ Φ φ
      dCut φ dφ (k Φ.length) Γ Φ ψ
    -- the head's type and resolved term related, by the constant's convergence
    let goodHead (iRel : ℕ) : Deducer := dImpI L <| dImpI L <|
      linkK K s!"{c.coreName}: the head related" (K.byHyp iRel)
    -- the keyword's characters fixed by the expansion of numeral abbreviations: the test's
    -- equation with its value, computed with the steps unfolded, cut in
    let kwChars (k : Deducer) : Deducer := fun Γ Φ ψ ↦ do
      let fn := Term.lam treeTy (pc P "Reader.expandNums" [Term.rename (W.qv 7 Γ) (· + 1), v 0])
      let t := pc P "charsFixed" [fn, call D.children [] [pc P c.kw []]]
      let (l, _) ← evalRw K.G K.E (K.rules Φ) .full Γ Φ t
      let rs := K.rules Φ ++ (W.ks ++ [P.idx "charsFixed"]).map Internal.NormRule.delta
      let (r, d, _) ← Internal.eval K.G K.E 0 rs 4096 .full Γ Φ l
      dCut (Term.eq l r) (nd .join [d, nd .refl]) k Γ Φ ψ
    let decisions : Deducer :=
      eqs <| kwChars <| types fun tys ks ↦ related tys ks fun iRel ↦
        W.generalize (constT ks) <|
          linkK K s!"{c.coreName}: the spine" (spineK P S T W (tyHead tys) 0 (goodHead iRel))
    let some d := W.introWith c.kw (reservedK K c.kw) decisions a.ctx a.hyps a.concl
      | dbgTrace s!"{c.coreName}: not proved" fun _ ↦ none
    pure (a, d))

/-- The soundness at a list headed by a keyword of the kernel's constants ({name}`kwListThm`):
the further elements split by cases until the types are present, fewer refuted by the typing
({name}`refuteForm`); then, the soundness at every element split into the types' and the
rest's, by {name}`srcSound`, the types' expansions generalized, from the soundness at expanded
forms at the keyword's form ({name}`constCore`). -/
def constSrc (P : Prog) (S : Defs) (T : Defs3) (c : ConstForm) : Step :=
  (kwListName c.kw, fun ix E ↦ do
    let K := appKit P S ix E
    let a := kwListThm P S T c.kw
    -- the soundness at every element split, after the hypotheses: each type's, then the rest's
    let splitAll (k : Deducer) : Deducer := fun Γ Φ ψ ↦
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ 0) .full) 0 ((List.range c.ntys).foldr
        (fun _ k Γ Φ ψ ↦ (K.conjE k Γ Φ ψ).orElse fun _ ↦ k Γ Φ ψ) k) Γ Φ ψ
    -- the form of the types at the positions tys and the rest at the position tl
    let main (tys : List ℕ) (tl : ℕ) : Deducer := splitAll fun Γ Φ ψ ↦
      let n := Γ.length
      let W₀ := kwKit P S T ix E n (List.replicate Φ.length true)
      let W := { W₀ with K := K }
      let at_ (p : ℕ) : Term := v (nQ + n - 1 - p)
      let F := listOf (kwAtom P c.kw) (tys.foldr (fun p t ↦ consT treeTy (at_ p) t) (at_ tl))
      -- the core's context: the second type where there are two, the rest, the first type
      let σ (hPos : List ℕ) (rest : Term) (Γ : List Tree) : List Term :=
        (hPos.drop 1).reverse.map (atPos · Γ) ++ [rest, atPos (hPos.headD 0) Γ]
      let body := srcSound P S T W F tys (1 + c.ntys) tl (Φ.length - 1) c.coreName σ [] 0 0
      W.introWith c.kw (reservedK K c.kw) body Γ Φ ψ
    -- the types split off the further elements, at the position tl, one by one
    let some d := (List.range c.ntys).foldr (fun _ (rec : ℕ → List ℕ → Deducer) tl tys ↦
          fun Γ Φ ψ ↦ K.listCase treeTy (atPos tl Γ)
            (refuteForm P S T K s!"{kwListName c.kw}: {tys.length} types" tys [])
            (fun Γ' Φ' ψ' ↦ rec (Γ'.length - 1) (tys ++ [Γ'.length - 2]) Γ' Φ' ψ') Γ Φ ψ)
        (fun tl tys ↦ main tys tl) 0 [] a.ctx a.hyps a.concl
      | dbgTrace s!"{kwListName c.kw}: not proved" fun _ ↦ none
    pure (a, d))

/-- The development of the constants' relations at the datatype language's types: the
normalization proof's lemmas on the evaluator's folds and on the constants but the primitives, at
the relation {name}`relTSpec`. -/
def foldsDev3 (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  constDev P S (relTSpec P T) false ++ foldRelDev P S (relTSpec P T) ++ ltMore P ++
    indexOfMore P S ++
    constForms.flatMap fun c ↦ constEqs P S T c ++ [constCore P S T c, constSrc P S T c]

/-- The development of the constants' relations ({name}`foldsDev3`), after the base's, the atom's,
the list's, the stage functions' at applications, the applications', the list expansion's and the
soundness at applications', stored as the certificate {lit}`datatype-folds`. -/
def foldsCertificates (P : Prog) (S : Defs) (T : Defs3) (before : List Internal.Thm) :
    Except String (List (String × List Internal.Decl)) := do
  let some names := listNames P S T | throw "the base is not stated"
  certifyAfter P (names ++ (stagesDev3 P S T).map (·.1) ++ (applyDev3 P S T).map (·.1) ++
    (expansionDev3 P S T).map (·.1) ++ (assemblyDev3 P S T).map (·.1)) "datatype-folds"
    (foldsDev3 P S T) before

end GebTests.Prototypes.FreeTopos.Datatypes

end
