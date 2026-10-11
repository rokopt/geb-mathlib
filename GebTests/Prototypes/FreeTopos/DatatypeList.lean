/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.DatatypeBase -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.DatatypeBase -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The datatype language's soundness at a list

The case of a list in the soundness of the datatype language's stage-1 compiler
({lit}`GebTests.Prototypes.FreeTopos.DatatypeBase`), one keyword at a time: a keyword applied to
elements whose soundness holds, the stage functions at its node computed from their folds at the
elements. The stage functions' equations at each keyword are proved once, in a context of the
elements, the folds' parameters and the elements' folds' values alone, and the proofs at the
keyword use them as rules, deciding the optional values the stages compute one at a time, by the
labels of their trees, in the order the stages test them.

## Main definitions

* {lit}`kwEqs` — the stage functions' equations at a keyword.
* {lit}`kwThm` — the soundness at a keyword applied to elements.
* {lit}`letCase` — the soundness at a binding of a name.
* {lit}`listCertificates` — the development, after the base's and the atom's.

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

/-- Whether the deducers' derivations are checked as they are found, for diagnosis. -/
def checkSteps : Bool := false

/-- A deducer whose derivations, where {name}`checkSteps` holds, are checked against their
sequents, a failure reported with a message. -/
def verifyK (K : Kit) (msg : String) (k : Deducer) : Deducer := fun Γ Φ ψ ↦
  (k Γ Φ ψ).map fun d ↦
    if !checkSteps || Internal.Thm.checks K.G K.E ⟨0, Γ, Φ, ψ⟩ d then d else
      dbgTrace s!"{msg}: does not check" fun _ ↦ d

/-- The applications of the definition of index k, its parameters its node's children, to all the
arguments its curried value takes, among a term's subterms, each once. -/
def appsWith (G : Internal.Globals) (k : ℕ) (t : Term) : List Term :=
  let arrows : Tree → ℕ := fun A ↦ (List.range 16).foldl (fun (acc : Tree × ℕ) _ ↦
    match Internal.expParts acc.1 with
    | some (_, B) => (B, acc.2 + 1)
    | none => acc) (A, 0) |>.2
  let arity := match G.defs[k]? with
    | some (.language d) => arrows d.type
    | _ => 0
  -- at each subterm: the number of arguments of its spine headed by the definition, and the
  -- applications found
  (RoseTree.para (fun (l : Internal.Label) (cs : List (Term × (Option ℕ × List Term))) ↦
    let n : Option ℕ := match l, cs with
      | .defn k' _, _ => if k' = k then some 0 else none
      | .app, [(_, (hf, _)), _] => hf.map (· + 1)
      | _, _ => none
    let below := cs.flatMap (·.2.2)
    (n, if n = some arity then RoseTree.node l (cs.map Prod.fst) :: below else below)) t).2
    |>.eraseDups

/-- The applications of the definitions of indices {lit}`ks` in the normal forms of the hypotheses
of indices {lit}`hs`, each evaluated to its weak normal form by the rules, the hypotheses'
equations and the definitions unfolded, its equation cut in after the hypotheses; repeated while
the equations expose new applications, to a number of rounds. The weak normal form leaves an
abstraction's body, as a step's function of the parameters its application receives, to the
hypotheses' normal forms, where the parameters and the decisions about them meet. -/
def unfoldApps (K : Kit) (ks hs : List ℕ) (k : Deducer) (rounds : ℕ := 6) : Deducer :=
  rounds.rec (motive := fun _ ↦ List Term → Deducer) (fun _ ↦ k) (fun _ rec done Γ Φ ψ ↦ do
    let nfs := hs.filterMap (Φ[·]?) |>.filterMap fun t ↦
      (evalRw K.G K.E (K.rules Φ) .full Γ Φ t).map Prod.fst
    let apps := (ks.flatMap fun j ↦ nfs.flatMap (appsWith K.G j)).eraseDups.filter
      (!done.contains ·)
    if apps.isEmpty then k Γ Φ ψ else
    let rules := K.rules Φ ++ ks.map .delta
    let cuts := apps.filterMap fun a ↦
      (Internal.eval K.G K.E 0 rules 4096 .weak Γ Φ a).map fun (r, d, _) ↦
        let d' := nd .join [d, nd .refl]
        let _ := if !checkSteps || Internal.Thm.checks K.G K.E ⟨0, Γ, Φ, Term.eq a r⟩ d' then ()
          else
          dbgTrace s!"unfoldApps: a cut does not check: {showT a}" fun _ ↦ ()
        (Term.eq a r, d')
    cuts.foldr (fun (e, d) k ↦ dCut e d k) (K.norm (rec (done ++ apps))) Γ Φ ψ) []

/-- The induction hypothesis on rose trees at the element of position {lit}`p`, the hypothesis of
index {lit}`h` an equation of the lists of formulas at the elements: the formula at the element cut
in, normalized, after the hypotheses. -/
def ihAt (K : Kit) (h p : ℕ) (k : Deducer) : Deducer := fun Γ Φ ψ ↦ do
  let (L₀, R₀) ← Internal.eqParts (← Φ[h]?)
  let A := nthOf L₀ p
  let B := nthOf R₀ p
  let (A', dA, _) ← Internal.eval K.G K.E 0 (K.rules Φ) 4096 .full Γ Φ A
  let (B', dB, _) ← Internal.eval K.G K.E 0 (K.rules Φ) 4096 .full Γ Φ B
  let (_, dAh, _) ← Internal.eval K.G K.E 0 [.hyp h] 4096 .weak Γ Φ A
  let i₁ := Φ.length
  let q ← k Γ (Φ ++ [Term.eq A' B', A']) ψ
  pure (nd (.cut (Term.eq A' B')) [nd (.convFrom (Term.eq A B))
    [nd .cong [dA, dB], nd .join [dAh, nd .refl]],
    nd (.cut A') [nd .conv [nd (.rwHyp i₁ false), nd .join [nd .refl, nd .refl]], q]])

/-- The stability of the hypothesis of index {lit}`h` shifted to a later threshold, the sum of its
threshold and another on its right ({lit}`stabR`) or on its left ({lit}`stabL`), cut in after the
hypotheses. -/
def shiftK (K : Kit) (h : ℕ) (left : Bool) (j : List Tree → Term) (k : Deducer) : Deducer :=
  fun Γ Φ ψ ↦ do
    let (F, n, w) ← stabParts K.P.o K.S.q (← Φ[h]?)
    let name := if left then "stabL" else "stabR"
    let some (Internal.Entry.language a) := K.E[K.ix name]? | none
    let σ := [j Γ, n, w, F]
    dCut (Internal.instTerm [] σ a.concl) (nd (.apply (K.ix name) [] σ) [nd (.hyp h)]) k Γ Φ ψ

/-- A universal hypothesis's instance, normalized without it, the last hypothesis. -/
def instNK (K : Kit) (h : ℕ) (t : List Tree → Term) (k : Deducer) : Deducer := fun Γ Φ ψ ↦
  dAllE K.L K.G K.E h (t Γ) (fun Γ Φ ψ ↦
    dRwHyp (evalRw K.G K.E (K.rules Φ.dropLast) .full) (Φ.length - 1) k Γ Φ ψ) Γ Φ ψ

/-- The truth of a test decided as by {name}`decideIn`, unless the hypotheses' normal form of its
label's bitstring is already empty, by {lit}`kF`, or a construction, by {lit}`kT`: a case
analysis of a construction would add the equation of a constant with a construction of new
variables, which the rules would apply wherever the constant occurs. -/
def decideKnown (K : Kit) (t : List Tree → Term) (kF kT : Deducer) : Deducer := fun Γ Φ ψ ↦
  match evalRw K.G K.E (K.rules Φ) .full Γ Φ (call D.lab [] [t Γ]) with
  | some (X, _) => match X.label with
    | .arr 0 _ => kF Γ Φ ψ
    | .arr 1 _ => kT Γ Φ ψ
    | _ => K.listCase bitTy X kF kT Γ Φ ψ
  | none => dbgTrace s!"a test without a normal form: {showT (t Γ)}" fun _ ↦ none

/-- An optional value's presence decided by the bits of its tree's label: the label of a value
present, by {lit}`kT`, any other, by {lit}`kF`. The equations decided are those of the label and of
its bits, which every test of the label finds, where an equation of the test as a whole would
rewrite it before its label is reached; a label already constant is decided at once. -/
def decideOpt (K : Kit) (opt : List Tree → Term) (kF kT : Deducer) : Deducer := fun Γ Φ ψ ↦
  let nf (t : Term) : Option Term := (evalRw K.G K.E (K.rules Φ) .full Γ Φ t).map Prod.fst
  match nf (call D.lab [] [opt Γ]), nf (numeral 1) with
  | some X, some one =>
    if X == one then kT Γ Φ ψ
    else if (List.range Γ.length).all fun i ↦ !Term.occurs X i then kF Γ Φ ψ
    else dBits K.L K.G K.E (K.ix "listCases") (K.ix "bitCases")
      (fun bs ↦ if bs.map Oitavem.rank == some 1 then kT else kF) 2 [] X Γ Φ ψ
  | _, _ => dbgTrace s!"a value without a normal form: {showT (opt Γ)}" fun _ ↦ none

/-- The tests of the soundness's antecedents at a form, under its quantifiers: its expansion a
source form, and its expansion, its expansion's type, its resolution and the kernel's type of the
resolved term, each present. -/
def antecedentTests (P : Prog) (form : Term) : List Term :=
  let isSome (t : Term) : Term := pc P "Prelude.isSome" [t]
  let (ty, k) := datatypeTerms P form
  [pc P "srcForm" [Term.lam treeTy (pc P "Reader.expandNums" [v 4, v 0]),
      pc P "Prelude.get" [pc P "Datatype.expandExpr" [v 7, form]]],
    isSome (pc P "Datatype.expandExpr" [v 7, form]), isSome ty, isSome k,
    isSome (pc P "Check.typeIn" [v 9, v 8, pc P "Prelude.get" [k]])]

/-- The optional values the soundness's antecedents at a form test present, under its
quantifiers: its expansion, its expansion's type, its resolution and the kernel's type of the
resolved term. -/
def antecedentOpts (P : Prog) (form : Term) : List Term :=
  let (ty, k) := datatypeTerms P form
  [pc P "Datatype.expandExpr" [v 7, form], ty, k,
    pc P "Check.typeIn" [v 9, v 8, pc P "Prelude.get" [k]]]

/-- The indices of the soundness's hypotheses that are the antecedents' tests, in their order. -/
def antecedentHyps : List ℕ := [4, 5, 6, 7, 8]

/-- The term of the variable at a position from the outermost. -/
def atPos (p : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - p)

/-- The atom of a keyword, the definition of the name {lit}`kw`: the node of label 1 over the
characters of its name, in normal form. -/
def kwAtom (P : Prog) (kw : String) : Term :=
  let cs := call D.children [] [pc P kw []]
  nodeT (Term.pair (numeral 1) ((nfE P.G #[] (vBase P) [] cs).getD cs))

/-- The form of a keyword applied to the elements of a context of trees, the outermost first: the
node of label 2 over the keyword's atom and the elements. -/
def kwForm (P : Prog) (kw : String) (n : ℕ) : Term :=
  nodeT (Term.pair (numeral 2) (consT treeTy (kwAtom P kw)
    ((List.range n).foldr (fun i t ↦ consT treeTy (v (n - 1 - i)) t) (nilT treeTy))))

/-- The name of the equation of the fold of index k at a keyword applied to n elements. -/
def kwEqName (kw : String) (n k : ℕ) : String := s!"{kw}/{n}/fold{k}"

/-- The subterms of a term outside its binders that mention exactly one of the variables below n
and are neither a variable, a construction, a pair, a subterm of {lit}`form` nor a term containing
the definition of index {lit}`step`, each the largest such: at a stage function's step at a node,
the values of the elements' folds. -/
def elementValues (n : ℕ) (form : Term) (step : ℕ) : Term → List Term := RoseTree.para fun l cs ↦
  let t := RoseTree.node l (cs.map Prod.fst)
  let isVar := match l with
    | .var _ | .arr _ _ | .pair => true
    | _ => false
  let inForm := (RoseTree.para (fun l' (rs : List (Term × Bool)) ↦
    RoseTree.node l' (rs.map Prod.fst) == t || rs.any (·.2)) form)
  let hasStep := (RoseTree.para (fun l' (rs : List (Term × Bool)) ↦
    (match l' with
      | .defn k _ => k == step
      | _ => false) || rs.any (·.2)) t)
  if !isVar && !inForm && !hasStep && ((List.range n).filter (Term.occurs t)).length = 1 then [t]
  else (cs.zipIdx.flatMap fun ((_, r), i) ↦ if Internal.sameCtx l i then r else []).eraseDups

/-- A term with each occurrence outside its binders of the subterm of index m of a list replaced
by the variable of index {lit}`base` plus m. -/
def abstractTerms (ts : List Term) (base : ℕ) : Term → Term := RoseTree.para fun l cs ↦
  match ts.idxOf? (RoseTree.node l (cs.map Prod.fst)) with
  | some m => v (base + m)
  | none => RoseTree.node l (cs.zipIdx.map fun ((c, r), i) ↦ if Internal.sameCtx l i then r else c)

/-- The equations of the stage functions at a keyword applied to the elements of a context of n
trees, the fold's parameters after them, and the values of the elements' folds after those, those
the left side mentions: the term's normal form by the vocabulary's rules, the fold's step at the
node exposed, its elements' values abstracted to variables; and its weak normal form with the step
and the list's and the atom's cases of the typing and the reader unfolded as well, so that the
cases on the elements' values reduce as the proofs decide them. With the values abstracted the
equation applies whatever form the values have reached. The proofs at the keyword use them as
rules in place of unfolding the steps among their hypotheses. -/
def kwEqs (P : Prog) (T : Defs3) (kw : String) (n : ℕ) : List Step :=
  (foldSpecs P T.envTy).zipIdx.map fun (f, k) ↦ (kwEqName kw n k, fun ix E ↦ do
    let Γ₀ := List.replicate n treeTy ++ f.ctx.tail
    let form := kwForm P kw n
    let t := Term.subst (pc P f.name f.args) fun i ↦ if i = 0 then form else v (i - 1 + n)
    let rs := vRules3 P ix E.size
    let unfold := [T.argIdx k, P.idx "Typing.synList", P.idx "Reader.resolveList",
      P.idx "Typing.synAtom", P.idx "Reader.resolveAtom"]
    let some l₀ := nfE P.G E rs Γ₀ t | dbgTrace s!"{kwEqName kw n k}: left" fun _ ↦ none
    let vals := elementValues n form (T.argIdx k) l₀
    let some tys := vals.mapM (Internal.typeIn P.G 0 Γ₀)
      | dbgTrace s!"{kwEqName kw n k}: untyped values" fun _ ↦ none
    let Γ₁ := Γ₀ ++ tys
    let l₁ := abstractTerms vals Γ₀.length l₀
    -- the context the variables the left side mentions, as a rule's must be
    let used := (List.range Γ₁.length).filter (Term.occurs l₁)
    let Γ := used.map (Γ₁.getD · treeTy)
    let l := Term.rename l₁ fun i ↦ used.idxOf i
    let some (r, d, _) := Internal.eval P.G E 0 (rs ++ unfold.map .delta) 4096 .weak Γ [] l
      | dbgTrace s!"{kwEqName kw n k}: right" fun _ ↦ none
    -- an equation of a term with itself would rewrite it to itself without end
    if l == r then none else
    pure (⟨0, Γ, [], Term.eq l r⟩, nd .join [d, nd .refl]))

/-- The typing's form of a node of a label, the first component of its fold's value applied to
the unit's element, the children of index 0 and the typing environment of index 1, named:
the term's normal form by the vocabulary's rules, and its normal form with the fold's step and
the definitions {lit}`unfold` unfolded as well. At an atom and at a list it is the node. -/
def rawAt (P : Prog) (T : Defs3) (name : String) (label : ℕ) (unfold : List ℕ) : Step :=
  (name, fun ix E ↦ do
    let Γ := [list treeTy, T.envTy]
    let t := Term.fst (Term.app (Term.snd (T.foldAt 1 [v 1]
      (nodeT (Term.pair (numeral label) (v 0))))) Term.star)
    let rs := vRules3 P ix E.size
    let some l := nfE P.G E rs Γ t | dbgTrace s!"{name}: left" fun _ ↦ none
    let some (r, d, _) := Internal.eval P.G E 0 (rs ++ (T.argIdx 1 :: unfold).map .delta) 4096
        .full Γ [] l
      | dbgTrace s!"{name}: right" fun _ ↦ none
    if l == r then none else
    pure (⟨0, Γ, [], Term.eq l r⟩, nd .join [d, nd .refl]))

/-- The typing's form of an atom ({name}`rawAt`). -/
def rawAtom (P : Prog) (T : Defs3) : Step := rawAt P T "rawAtom" 1 [P.idx "Typing.synAtom"]

/-- The typing's form of a list ({name}`rawAt`). -/
def rawList (P : Prog) (T : Defs3) : Step := rawAt P T "rawList" 2 []

/-- The reader's form of an atom, the first component of its fold's value, the characters of
index 0 and the fold's parameters after them: the first component of the value's normal form by
the vocabulary's rules, and its normal form with the fold's argument and the atom's case of the
reader unfolded as well. -/
def rawAtomR (P : Prog) (T : Defs3) : Step :=
  ("rawAtomR", fun ix E ↦ do
    let f ← (foldSpecs P T.envTy)[4]?
    let (_, d, _, _, _, _) ← foldDefn P f (T.argIdx 4)
    let tys := d.params.tail
    let Γ := list treeTy :: tys
    let ps := (List.range tys.length).reverse.map fun i ↦ v (i + 1)
    let rs := vRules3 P ix E.size
    -- the fold's value at the node normalized first, as where its children are normalized before
    -- it, the first component's rebuilding no longer applying
    let some l := (nfE P.G E rs Γ (T.foldAt 4 ps atomT)).map Term.fst
      | dbgTrace "rawAtomR: left" fun _ ↦ none
    let some (r, d, _) := Internal.eval P.G E 0
        (rs ++ [.delta (T.argIdx 4), .delta (P.idx "Reader.resolveAtom")]) 4096 .full Γ [] l
      | dbgTrace "rawAtomR: right" fun _ ↦ none
    if l == r then none else
    pure (⟨0, Γ, [], Term.eq l r⟩, nd .join [d, nd .refl]))

/-- The source forms' test at a node, its children of index 0, its label of index 1 and the
fold's parameters after them: the fold's value at the node in normal form by the vocabulary's
rules, its step exposed, and its normal form with the step unfolded as well, which tests the label
against those of atoms and lists. -/
def srcNode (P : Prog) (T : Defs3) : Step :=
  ("srcNode", fun ix E ↦ do
    let f ← (foldSpecs P T.envTy)[5]?
    let (_, d, _, _, _, _) ← foldDefn P f (T.argIdx 5)
    let tys := d.params.tail
    let Γ := [list treeTy, bitsTy] ++ tys
    let ps := (List.range tys.length).reverse.map fun i ↦ v (i + 2)
    let rs := vRules3 P ix E.size
    let some l := nfE P.G E rs Γ (T.foldAt 5 ps (nodeT (Term.pair (v 1) (v 0))))
      | dbgTrace "srcNode: left" fun _ ↦ none
    let some (r, d, _) := Internal.eval P.G E 0 (rs ++ [.delta (T.argIdx 5)]) 4096 .full Γ [] l
      | dbgTrace "srcNode: right" fun _ ↦ none
    if l == r then none else
    pure (⟨0, Γ, [], Term.eq l r⟩, nd .join [d, nd .refl]))

/-- The soundness at a keyword applied to the elements of a context of n trees, given the
soundness at each element {lit}`ihs` marks. -/
def kwThm (P : Prog) (S : Defs) (T : Defs3) (kw : String) (n : ℕ)
    (ihs : List Bool := List.replicate n true) : Internal.Thm :=
  ⟨0, List.replicate n treeTy,
    ((List.range n).filter fun i ↦ ihs.getD i false).map fun i ↦
      Internal.instTerm [] [v (n - 1 - i)] (datatypeφ P S T),
    Internal.instTerm [] [kwForm P kw n] (datatypeφ P S T)⟩

/-- The tools of the soundness at a keyword applied to the elements of a context of n trees: the
kit, the statement's variables and hypotheses in the context, the stage functions' steps, and the
elements' antecedents decided and their soundness instantiated. -/
structure KwKit where
  /-- The kit. -/
  K : Kit
  /-- The statement's definitions. -/
  T : Defs3
  /-- The number of elements. -/
  n : ℕ
  /-- The definitions unfolded where their applications are exposed. -/
  ks : List ℕ
  /-- Which elements' soundness is among the hypotheses. -/
  ihs : List Bool

namespace KwKit

variable (W : KwKit)

/-- The number of the statement's hypotheses. -/
def nH : ℕ := (datatypeParts W.K.P W.K.S W.T (v nQ)).1.length

/-- The statement's hypothesis of index i, after the elements' soundness and the variables'
truths. -/
def hyp (i : ℕ) : ℕ := (W.ihs.filter id).length + nQ + i

/-- The index of the hypothesis of the soundness at the element of position c. -/
def ihIdx (c : ℕ) : ℕ := ((W.ihs.take c).filter id).length

/-- The statement's variable of position j, from 1 for the kernel's globals' types to 10 for the
relation's context. -/
def qv (j : ℕ) : List Tree → Term := atPos (W.n - 1 + j)

/-- A term under the statement's quantifiers in the context, its form's variable at a term, the
variables of the positions {lit}`over` gives at its terms. -/
def inΓWith (over : ℕ → Option (List Tree → Term)) (form : List Tree → Term) (Γ : List Tree)
    (t : Term) : Term :=
  Term.subst t fun i ↦ if i < nQ then ((over (nQ - i)).getD (W.qv (nQ - i))) Γ
    else if i = nQ then form Γ else v i

/-- A term under the statement's quantifiers in the context, its form's variable at a term. -/
def inΓ (form : List Tree → Term) (Γ : List Tree) (t : Term) : Term :=
  W.inΓWith (fun _ ↦ none) form Γ t

/-- A term generalized: a new variable equal to its normal form, the equation after the
hypotheses, which rewrites the term to the variable. -/
def generalize (t : List Tree → Term) (k : Deducer) : Deducer := fun Γ Φ ψ ↦ do
  let K := W.K
  let (t', _) ← evalRw K.G K.E (K.rules Φ) .full Γ Φ (t Γ)
  let φ := Internal.Logic.ex K.P.o treeTy (Term.lam treeTy (Term.eq (Term.rename t' (· + 1))
    (v 0)))
  let d ← verifyK K "generalization" (dExI K.L K.G K.E t' (fun Γ Φ ψ ↦
    dEq (fun Γ Φ t u ↦ byMode .full K.G K.E 0 [] Γ (rwHyps [] Φ) t u) Γ Φ ψ)) Γ Φ φ
  dCut φ d (K.exE k) Γ Φ ψ

/-- A hypothesis refuted with the stage functions' steps unfolded. -/
def hypFalseU (h : ℕ) : Deducer := fun Γ Φ ψ ↦
  let K := W.K
  dRwHyp (evalRw K.G K.E ((K.rules Φ ++ (W.ks ++ [K.P.idx "charsFixed"]).map
    Internal.NormRule.delta).filter
    fun r ↦ match r with
      | .hyp j => j ≠ h
      | _ => true) .full) h (dFalse K.L dHyp) Γ Φ ψ

/-- Each element's expansion a source form, its test decided, false refuting the statement's
hypothesis with the stage functions' steps unfolded. -/
def sources (k : Deducer) : Deducer :=
  let K := W.K
  (List.range W.n).foldr (fun c k Γ Φ ψ ↦
    decideIn K (fun Γ ↦ W.inΓ (atPos c) Γ ((antecedentTests K.P (v nQ)).headD Term.star))
      (verifyK K s!"element {c + 1} not a source form"
        (linkK K s!"element {c + 1} not a source form" (W.hypFalseU (W.hyp 4)))) k Γ Φ ψ) k

/-- An optional value decided present by {name}`decideOpt`, absent refuting the statement's
hypothesis of index i, with the stage functions' steps unfolded where {lit}`unfolding` holds,
lazily along the branch the decisions select; the value present generalized. -/
def present (msg : String) (opt : List Tree → Term) (i : ℕ) (k : Deducer)
    (unfolding : Bool := false) : Deducer :=
  let K := W.K
  decideOpt K opt
    (verifyK K s!"{msg} refuted" (linkK K s!"{msg} refuted"
      (if unfolding then W.hypFalseU (W.hyp i) else K.hypFalse (W.hyp i))))
    (W.generalize (fun Γ ↦ pc K.P "Prelude.get" [opt Γ]) k)

/-- An optional value decided present by {name}`decideOpt`, absent refuting the hypothesis of index
h or that of index h', by the rules, else with the stage functions' steps unfolded; the value
present generalized. -/
def presentAt (msg : String) (opt : List Tree → Term) (h h' : ℕ) (k : Deducer)
    (unfolding : Bool := true) : Deducer :=
  let K := W.K
  decideOpt K opt
    (linkK K s!"{msg} refuted" fun Γ Φ ψ ↦
      (K.hypFalse h Γ Φ ψ).orElse fun _ ↦ (K.hypFalse h' Γ Φ ψ).orElse fun _ ↦
      if unfolding then (W.hypFalseU h Γ Φ ψ).orElse fun _ ↦ W.hypFalseU h' Γ Φ ψ
        else none)
    (W.generalize (fun Γ ↦ pc K.P "Prelude.get" [opt Γ]) k)

/-- The steps the statement's hypotheses expose unfolded. -/
def unfold (k : Deducer) : Deducer := unfoldApps W.K W.ks ((List.range W.nH).map W.hyp) k

/-- Optional values decided present, stage by stage, by {lit}`present`; after the first stage,
the expansions, the elements' expansions decided source forms and the steps the statement's
hypotheses expose unfolded, so that the steps that consume them receive decided values; the goal
normalized after them. A value is given by its element's position, its term under the statement's
quantifiers, its form's variable that of index {name}`nQ`, and the hypothesis. -/
def decideWith (stages : List (List (ℕ × Term × ℕ))) (k : Deducer) : Deducer :=
  stages.zipIdx.foldr (fun (stage, j) k ↦
    stage.foldr (fun (c, o, i) k ↦
        W.present s!"element {c + 1}'s value for {i}" (fun Γ ↦ W.inΓ (atPos c) Γ o) i k (j = 0))
      (if j = 0 then W.sources (W.unfold k) else k))
    (W.K.norm k)

/-- The elements' antecedents decided, antecedent by antecedent, by {lit}`decideWith`: each
element's expansion, its type, its resolution and the kernel's type of the resolved term. -/
def decideAll (k : Deducer) : Deducer :=
  W.decideWith (((antecedentOpts W.K.P (v nQ)).zip antecedentHyps.tail).map fun (o, i) ↦
    ((List.range W.n).filter fun c ↦ W.ihs.getD c false).map fun c ↦ (c, o, i)) k

/-- The soundness at the element of position c, its hypothesis, at the statement's variables,
those of the positions {lit}`over` gives at its terms; its antecedents those of the statement or
decided, the relation of the environment to the named context by {lit}`envOk` where either is
given; its conclusion, a convergence, the last hypothesis for k. -/
def soundAt (c : ℕ) (over : ℕ → Option (List Tree → Term)) (envOk : Deducer) (k : Deducer) :
    Deducer :=
  let K := W.K
  let at_ (j : ℕ) : List Tree → Term := (over j).getD (W.qv j)
  verifyK K s!"element {c + 1}'s soundness" <| linkK K s!"element {c + 1}'s soundness"
    fun Γ Φ ψ ↦
    dAllE K.L K.G K.E (W.ihIdx c) (at_ 1 Γ) (
      ((List.range (nQ - 1)).foldr (fun j k ↦ K.allEΓ (at_ (j + 2)) k) <|
      (List.range W.nH).foldr (fun i k ↦
          K.impE (verifyK K s!"element {c + 1}'s antecedent {i}"
            (linkK K s!"element {c + 1}'s antecedent {i}"
            (if i ∈ antecedentHyps then K.solve 3
              else if i = 1 ∧ ((over 5).isSome ∨ (over 9).isSome) then envOk
              else K.byHyp (W.hyp i)))) k) k)) Γ Φ ψ

/-- The soundness at the element of position c, its hypothesis, at the statement's variables:
its convergence's threshold and value and their stability and relation given to k by their
positions. -/
def element (c : ℕ) (k : ℕ → ℕ → ℕ → ℕ → Deducer) : Deducer :=
  let K := W.K
  W.soundAt c (fun _ ↦ none) (fun _ _ _ ↦ none) <|
    K.unfoldConv <| K.exE <| K.exE <| K.conjE fun Γ Φ ψ ↦
      k (Γ.length - 2) (Γ.length - 1) (Φ.length - 2) (Φ.length - 1) Γ Φ ψ

/-- The instance of a theorem with hypotheses at terms of the context, each hypothesis proved by
its deducer, cut in after the hypotheses. -/
def cutApply (name : String) (σ : List Tree → List Term) (prems : List Deducer) (k : Deducer) :
    Deducer := fun Γ Φ ψ ↦ do
  let K := W.K
  let some (Internal.Entry.language b) := K.E[K.ix name]? | none
  let ds ← (b.hyps.zip prems).mapM fun (h, d) ↦ d Γ Φ (Internal.instTerm [] (σ Γ) h)
  dCut (Internal.instTerm [] (σ Γ) b.concl) (nd (.apply (K.ix name) [] (σ Γ)) ds) k Γ Φ ψ

/-- The hypotheses introduced; the keyword not abbreviated, by the coherence of the
abbreviations with the keywords; then k. -/
def intro (kw : String) (k : Deducer) : Deducer :=
  let K := W.K
  let P := K.P
  let KL : Kit := { K with more := K.more ++ lookupEqNames }
  let lastFalse : Deducer := fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ
  let notAbbrev : Deducer := verifyK K "keyword abbreviated" <|
    linkK K s!"keyword {kw} abbreviated" <|
    dRwHyp (evalRw K.G K.E [.delta (W.T.q + 5 + 2 * nFolds)] .head) (W.hyp 9)
      (K.allEΓ (fun _ ↦ pc P kw []) (K.impE (K.solve 3) (K.impE (KL.solve 3) lastFalse)))
  let body : Deducer :=
    decideIn K (fun Γ ↦ pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev"
        [pc P kw [], W.qv 7 Γ]]) k notAbbrev
  (List.range nQ).foldr (fun _ k ↦ dAllI K.L k)
    ((List.range W.nH).foldr (fun _ k ↦ dImpI K.L k) body)

end KwKit

/-- The kit of the soundness at a keyword applied to n elements, after the development's
theorems, the stage functions' equations at the keyword among its rules where they are proved. -/
def kwKit (P : Prog) (S : Defs) (T : Defs3) (ix : String → ℕ) (E : Array Internal.Entry)
    (n : ℕ) (ihs : List Bool := List.replicate n true) (kw : String := "") : KwKit :=
  let more := (vocab3 ++ ["charsMap", "handlerAtom3", "rawAtom", "rawList", "rawAtomR"] ++
      (List.range nFolds).map (kwEqName kw n)).filter fun nm ↦
    0 < ix nm ∧ ix nm < E.size
  ⟨⟨P, S, E, ix, more⟩, T, n, (List.range nFolds).map T.argIdx ++
    [P.idx "Typing.synList", P.idx "Reader.resolveList", P.idx "Typing.synAtom",
      P.idx "Reader.resolveAtom"], ihs⟩

/-- The tools of an evaluation's proof after the elements' soundness: the rules, the vocabulary's
and those of the equations among the hypotheses of the indices kept, after the base, or of
generalizations, a term equal to a variable, with further rules; normalization of the goal and
of a hypothesis, an equation by normalizing it whole, and a universal hypothesis's instance. -/
structure EvalTools where
  /-- The rules at the hypotheses. -/
  rs : List Term → List Internal.NormRule
  /-- The goal normalized. -/
  norm : Deducer → Deducer
  /-- An equation, or truth, by normalizing the goal. -/
  byNorm : Deducer
  /-- A hypothesis normalized, then the goal normalized and found among the hypotheses. -/
  byHyp : ℕ → Deducer
  /-- A universal hypothesis's instance at a term, normalized, after the hypotheses. -/
  inst : ℕ → (List Tree → Term) → Deducer → Deducer

/-- The tools of an evaluation's proof, the hypotheses those before the evaluation, the indices
of those kept and the further rules given. -/
def evalTools (K : Kit) (Φ₀ : List Term) (keep : List ℕ) (extra : List Internal.NormRule) :
    EvalTools :=
  let base := Φ₀.length
  let generalizes (j : ℕ) : Bool := match (Φ₀[j]?).bind Internal.eqParts with
    | some (_, r) => match r.label with
      | .var _ => true
      | _ => false
    | none => false
  let without (h : ℕ) (rules : List Internal.NormRule) : List Internal.NormRule :=
    rules.filter fun r ↦ match r with
      | .hyp j => j ≠ h
      | _ => true
  let rs (Φ : List Term) : List Internal.NormRule := extra ++ (K.rules Φ).filter fun r ↦
    match r with
    | .hyp j => j ∈ keep ∨ base ≤ j ∨ generalizes j
    | _ => true
  let norm (k : Deducer) : Deducer := fun Γ Φ ψ ↦ dRwBy (evalRw K.G K.E (rs Φ) .full) k Γ Φ ψ
  { rs, norm
    byNorm := norm fun _ _ ψ ↦
      if ψ == Internal.Logic.tt K.P.o then some Internal.Logic.trueI else
      match Internal.eqParts ψ with
      | some (a, b) => if a == b then some (nd .join [nd .refl, nd .refl]) else none
      | none => none
    byHyp := fun h Γ Φ ψ ↦
      dRwHyp (evalRw K.G K.E (without h (rs Φ)) .full) h (norm dHyp) Γ Φ ψ
    inst := fun h t k Γ Φ ψ ↦ dAllE K.L K.G K.E h (t Γ) (fun Γ Φ ψ ↦
      dRwHyp (evalRw K.G K.E (rs Φ.dropLast) .full) (Φ.length - 1) k Γ Φ ψ) Γ Φ ψ }

/-- The soundness at a pair: the elements' antecedents decided and their soundness instantiated;
their thresholds shifted to their sum, at which, a level above, the pair evaluates to the pair of
the elements' values, related at the product type by its equation ({lit}`relTProd`). The rules of
the evaluation are the vocabulary's and those of the elements' convergences, the generalizations'
and the equations after them. -/
def pairCase (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("pairCase", fun ix E ↦ do
    let W := kwKit P S T ix E 2 (kw := "Reader.kwPair")
    let K := W.K
    let L := K.L
    let a := kwThm P S T "Reader.kwPair" 2
    let eval (n₀ w₀ s₀ e₀ n₁ w₁ s₁ e₁ : ℕ) : Deducer := fun Γ₀ Φ₀ ψ₀ ↦
      let base := Φ₀.length
      let generalizes (j : ℕ) : Bool := match (Φ₀[j]?).bind Internal.eqParts with
        | some (_, r) => match r.label with
          | .var _ => true
          | _ => false
        | none => false
      let without (h : ℕ) (rules : List Internal.NormRule) : List Internal.NormRule :=
        rules.filter fun r ↦ match r with
          | .hyp j => j ≠ h
          | _ => true
      let rs (Φ : List Term) : List Internal.NormRule := (K.rules Φ).filter fun r ↦ match r with
        | .hyp j => j ∈ [s₀, e₀, s₁, e₁] ∨ base ≤ j ∨ generalizes j
        | _ => true
      let normE (k : Deducer) : Deducer := fun Γ Φ ψ ↦
        dRwBy (evalRw K.G K.E (rs Φ) .full) k Γ Φ ψ
      -- an equation by normalizing it whole: truth, or an equation of a term with itself
      let byNormE : Deducer := normE fun _ _ ψ ↦
        if ψ == Internal.Logic.tt P.o then some Internal.Logic.trueI else
        match Internal.eqParts ψ with
        | some (a, b) => if a == b then some (nd .join [nd .refl, nd .refl]) else none
        | none => none
      let instE (h : ℕ) (t : List Tree → Term) (k : Deducer) : Deducer := fun Γ Φ ψ ↦
        dAllE L K.G K.E h (t Γ) (fun Γ Φ ψ ↦
          dRwHyp (evalRw K.G K.E (rs Φ.dropLast) .full) (Φ.length - 1) k Γ Φ ψ) Γ Φ ψ
      -- the relation at the product type rewritten by its equation
      let rsP (Φ : List Term) : List Internal.NormRule := .thm (ix "relTProd") [] :: rs Φ
      let normP (k : Deducer) : Deducer := fun Γ Φ ψ ↦
        dRwBy (evalRw K.G K.E (rsP Φ) .full) k Γ Φ ψ
      let byHypP (h : ℕ) : Deducer := fun Γ Φ ψ ↦
        dRwHyp (evalRw K.G K.E (without h (rsP Φ)) .full) h (normP dHyp) Γ Φ ψ
      linkK K "pair evaluated" (shiftK K s₀ false (atPos n₁) <|
        shiftK K s₁ true (atPos n₀) fun Γ Φ ψ ↦
        let t₀ := Φ.length - 2
        let t₁ := Φ.length - 1
        normE (dConv L K.G K.E S (succN (S.add (atPos n₀ Γ) (atPos n₁ Γ)))
          (pc P "Eval.valPair" [atPos w₀ Γ, atPos w₁ Γ])
          (verifyK K "pair stable" <| linkK K "pair stable" (instE t₀ (fun _ ↦ succN (v 0)) <|
            instE t₁ (fun _ ↦ succN (v 0)) byNormE))
          (verifyK K "pair related" <| linkK K "pair related" (normP (dExI L K.G K.E (atPos w₀ Γ)
            (dExI L K.G K.E (atPos w₁ Γ)
              (dConjI L byNormE (dConjI L (byHypP e₀) (byHypP e₁)))))))) Γ Φ ψ) Γ₀ Φ₀ ψ₀
    let some d := W.intro "Reader.kwPair" (verifyK K "elements decided" <|
        W.decideAll <|
        W.element 0 fun n₀ w₀ s₀ e₀ ↦ W.element 1 fun n₁ w₁ s₁ e₁ ↦
          eval n₀ w₀ s₀ e₀ n₁ w₁ s₁ e₁) a.ctx a.hyps a.concl
      | dbgTrace "pairCase: not proved" fun _ ↦ none
    pure (a, d))

/-- The relation at a node of the label of products, over no children, one, or two and a rest:
a pair of values whose components are related at the first two children, a missing child's
relation false; each equation's sides in normal form by the vocabulary's rules with the relation
unfolded. -/
def relTProdNodes (P : Prog) (T : Defs3) : List Step :=
  let o := P.o
  -- context: the value, the children, the relation's context
  let eqn (name : String) (Γ : List Tree) (kids : Term) (r₀ r₁ : Term → Term) : Step :=
    (name, fun ix E ↦ do
      let lhs := Term.app (T.relT (v (Γ.length - 1))
        (nodeT (Term.pair (numeral Kernel.Label.tyProd) kids))) (v 0)
      let rhs := Internal.Logic.ex o treeTy (Term.lam treeTy (Internal.Logic.ex o treeTy
        (Term.lam treeTy (Internal.Logic.conj o
          (Term.eq (v 2) (pc P "Eval.valPair" [v 1, v 0]))
          (Internal.Logic.conj o (r₀ (v 1)) (r₁ (v 0)))))))
      let rs := vRules3 P ix E.size
      let some l := nfE P.G E rs Γ lhs | dbgTrace s!"{name}: left" fun _ ↦ none
      let some r := nfE P.G E rs Γ rhs | dbgTrace s!"{name}: right" fun _ ↦ none
      let some d := byMode .full P.G E 0 (rs ++ [.delta T.q]) Γ [] l r
        | dbgTrace s!"{name}: unequal {(firstDiff l r).map fun (a, b) ↦
            s!"{showT a}\n  vs {showT b}"}" fun _ ↦ none
      pure (⟨0, Γ, [], Term.eq l r⟩, d))
  let ff : Term → Term := fun _ ↦ Internal.Logic.ff o
  -- under the two binders, the context's variables raised by two
  let relAt (R c : ℕ) (x : Term) : Term := Term.app (T.relT (v (R + 2)) (v (c + 2))) x
  [eqn "relTProd0" [treeTy, Defs3.ctxTy] (nilT treeTy) ff ff,
    eqn "relTProd1" [treeTy, treeTy, Defs3.ctxTy] (consT treeTy (v 1) (nilT treeTy))
      (relAt 2 1) ff,
    eqn "relTProd2" [treeTy, list treeTy, treeTy, treeTy, Defs3.ctxTy]
      (consT treeTy (v 3) (consT treeTy (v 2) (v 1))) (relAt 4 3) (relAt 4 2)]

/-- The relation at a type of the label of products eliminated: a value related at it is a pair of
values related at its first two children, by the type's children decided, fewer than two
refuting the relation; the relation rewritten by its equations at such nodes. -/
def relTProdE (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("relTProdE", fun ix E ↦ do
    let o := P.o
    let K : Kit := ⟨P, S, E, ix, ["relTProd0", "relTProd1", "relTProd2"]⟩
    let L := K.L
    let childT ← primT Kernel.Prim.child
    -- context: the value, the type, the relation's context
    let Γ := [treeTy, treeTy, Defs3.ctxTy]
    let childAt (y : Term) (k : ℕ) : Term := apps childT [y, leafT (numeral k)]
    let a : Internal.Thm := ⟨0, Γ, [],
      Internal.Logic.imp o (Term.eq (call D.lab [] [v 1]) (numeral Kernel.Label.tyProd)) <|
      Internal.Logic.imp o (Term.app (T.relT (v 2) (v 1)) (v 0)) <|
      Internal.Logic.ex o treeTy (Term.lam treeTy (Internal.Logic.ex o treeTy (Term.lam treeTy
        (Internal.Logic.conj o (Term.eq (v 2) (pc P "Eval.valPair" [v 1, v 0]))
          (Internal.Logic.conj o (Term.app (T.relT (v 4) (childAt (v 3) 0)) (v 1))
            (Term.app (T.relT (v 4) (childAt (v 3) 1)) (v 0)))))))⟩
    -- the relation's hypothesis rewritten by the equations at the node, its parts
    let parts (k : Deducer) : Deducer := fun Γ Φ ψ ↦
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ 1) .full) 1 (fun Γ Φ ψ ↦
        (K.exE (K.exE (K.conjE (K.conjE k)))) Γ Φ ψ) Γ Φ ψ
    let anyHyp : Deducer := fun Γ Φ ψ ↦
      (List.range Φ.length).reverse.findSome? fun h ↦ K.byHyp h Γ Φ ψ
    let refuted : Deducer := linkK K "relTProdE refuted" (parts (anyFalse K))
    let two : Deducer := linkK K "relTProdE two" <| parts fun Γ Φ ψ ↦
      K.norm (dExI L K.G K.E (v 1) (dExI L K.G K.E (v 0)
        (dConjI L (linkK K "conjunct 1" (K.solve 3)) (dConjI L (linkK K "conjunct 2" anyHyp)
          (linkK K "conjunct 3" anyHyp))))) Γ Φ ψ
    let byChildren : Deducer := linkK K "relTProdE node" <|
      K.treeNode (v 1) <| (fun k Γ Φ ψ ↦ dRwHyp (evalRw K.G K.E (K.rulesEx Φ 0) .full) 0 k Γ Φ ψ)
        fun Γ Φ ψ ↦
      K.listCase treeTy (v 0) refuted (fun Γ Φ ψ ↦
        K.listCase treeTy (v 0) refuted (fun Γ Φ ψ ↦ two Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
    let some d := verifyK K "relTProdE" (linkK K "relTProdE" (dImpI L (dImpI L byChildren)))
        a.ctx a.hyps a.concl
      | none
    pure (a, d))

/-- The soundness at a projection of a pair, its first component's or its second's: the element's
antecedents decided and its soundness instantiated; its type's label decided, a product's, any
other refuting the typing; the element's value a pair of related values, by {lit}`relTProdE`,
whose component is the projection's value a level above the element's threshold. -/
def projCase (P : Prog) (S : Defs) (T : Defs3) (second : Bool) : Step :=
  (if second then "sndCase" else "fstCase", fun ix E ↦ do
    let kw := if second then "Reader.kwSnd" else "Reader.kwFst"
    let W := kwKit P S T ix E 1 (kw := kw)
    let K := W.K
    let L := K.L
    let a := kwThm P S T kw 1
    let tyT := (datatypeTerms P (v nQ)).1
    -- the element's type, in normal form: the variable its generalization introduced
    let tyOfElem (Γ : List Tree) (Φ : List Term) : Option Term :=
      (evalRw K.G K.E (K.rules Φ) .full Γ Φ
        (pc P "Prelude.get" [W.inΓ (atPos 0) Γ tyT])).map Prod.fst
    let eval (n w s e : ℕ) : Deducer := fun Γ₀ Φ₀ ψ₀ ↦
      match tyOfElem Γ₀ Φ₀ with
      | none => traceK K "projection: no type" Γ₀ Φ₀ ψ₀
      | some y =>
      -- the type's variable, by its position
      let yPos := match y.label with
        | .var i => Γ₀.length - 1 - i
        | _ => 0
      let main : Deducer := fun Γ₁ Φ₁ ψ₁ ↦
        let X := evalTools K Φ₁ [s, e] []
        K.cutThm "relTProdE" (fun Γ ↦ [atPos w Γ, atPos yPos Γ, W.qv 10 Γ]) (K.impE
          (linkK K "projection: the label" (K.solve 3))
          (K.impE (linkK K "projection: the relation" (K.byHyp e))
            (K.exE (K.exE (K.conjE (K.conjE fun Γ Φ ψ ↦
            -- context: the second component, the first
            let X' := evalTools K Φ [s, e, Φ.length - 4] []
            let _ := X
            X'.norm (dConv L K.G K.E S (succN (atPos n Γ)) (if second then v 0 else v 1)
              (verifyK K "projection stable" <| linkK K "projection stable" <|
                X'.inst s (fun _ ↦ succN (v 0)) X'.byNorm)
              (verifyK K "projection related" <| linkK K "projection related" <|
                fun Γ' Φ' ψ' ↦ (X'.byHyp (if second then Φ.length - 1 else Φ.length - 2)
                  Γ' Φ' ψ').orElse fun _ ↦
                  let h := if second then Φ.length - 1 else Φ.length - 2
                  let nf (t : Term) : Option Term :=
                    (evalRw K.G K.E (X'.rs Φ') .full Γ' Φ' t).map Prod.fst
                  dbgTrace s!"projection related: hypothesis {((Φ'[h]?).bind nf).map showT
                    }\n  goal {(nf ψ').map showT}\n  type {showT (atPos yPos Γ')}" fun _ ↦
                    none)) Γ Φ ψ)))))) Γ₁ Φ₁ ψ₁
      match (evalRw K.G K.E (K.rules Φ₀) .full Γ₀ Φ₀ (call D.lab [] [y])).map Prod.fst with
      | none => traceK K "projection: no label" Γ₀ Φ₀ ψ₀
      | some X =>
      dBits L K.G K.E (ix "listCases") (ix "bitCases") (fun bs ↦
        if bs.map Oitavem.rank == some Kernel.Label.tyProd then K.norm main
        else linkK K s!"the type's label {bs.map Oitavem.rank} refuted" (K.hypFalse (W.hyp 6)))
        3 [] X Γ₀ Φ₀ ψ₀
    let some d := W.intro kw (verifyK K "elements decided" <| W.decideAll <|
        W.element 0 fun n w s e ↦ eval n w s e) a.ctx a.hyps a.concl
      | dbgTrace s!"{kw}: not proved" fun _ ↦ none
    pure (a, d))

/-- The relation at the tree type: a value related at it is a tree's quotation; both sides in
normal form by the vocabulary's rules with the relation unfolded. -/
def relTTree (P : Prog) (T : Defs3) : Step :=
  ("relTTree", fun ix E ↦ do
    -- context: the value, the relation's context
    let Γ := [treeTy, Defs3.ctxTy]
    let lhs := Term.app (T.relT (v 1) (leafT bnilT)) (v 0)
    let rhs := Internal.Logic.ex P.o treeTy (Term.lam treeTy
      (Term.eq (v 1) (pc P "Eval.valQuote" [v 0])))
    let rs := vRules3 P ix E.size
    let some l := nfE P.G E rs Γ lhs | dbgTrace "relTTree: left" fun _ ↦ none
    let some r := nfE P.G E rs Γ rhs | dbgTrace "relTTree: right" fun _ ↦ none
    let some d := byMode .full P.G E 0 (rs ++ [.delta T.q]) Γ [] l r
      | dbgTrace s!"relTTree: unequal {(firstDiff l r).map fun (a, b) ↦
          s!"{showT a}\n  vs {showT b}"}" fun _ ↦ none
    pure (⟨0, Γ, [], Term.eq l r⟩, d))

/-- The soundness at a conditional: the elements' antecedents decided and their soundness
instantiated; the condition's type the tree type and the branches' types equal, by the equality's
soundness, else no type; the condition's value a quotation, by {lit}`relTTree`, its tree's label
empty or not selecting the second branch's value or the first's; the thresholds shifted to their
sum, at which, a level above, the conditional evaluates to the branch's value. -/
def ifCase (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("ifCase", fun ix E ↦ do
    let W := kwKit P S T ix E 3 (kw := "Reader.kwIf")
    let K := W.K
    let L := K.L
    let a := kwThm P S T "Reader.kwIf" 3
    let tyT := (datatypeTerms P (v nQ)).1
    let equalT ← primT Kernel.Prim.equal
    let typeOf (c : ℕ) (Γ : List Tree) (Φ : List Term) : Option Term :=
      (evalRw K.G K.E (K.rules Φ) .full Γ Φ
        (pc P "Prelude.get" [W.inΓ (atPos c) Γ tyT])).map Prod.fst
    let varPos (Γ : List Tree) (t : Term) : ℕ := match t.label with
      | .var i => Γ.length - 1 - i
      | _ => 0
    -- a type equal to another, by the equality's test decided: false refuting the typing; true
    -- the equation, by the equality's soundness, its index given to k
    let equalTy (x y : List Tree → Term) (k : ℕ → Deducer) : Deducer :=
      decideIn K (fun Γ ↦ apps equalT [x Γ, y Γ])
        (linkK K "if: the types refuted" (K.hypFalse (W.hyp 6)))
        (K.cutThm "equalSound" (fun Γ ↦ [x Γ]) <| K.allEΓ y <| K.impE (K.solve 3) <|
          normLastK K fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ)
    let eval (nc _wc sc ec na wa sa ea nb wb sb eb : ℕ) : Deducer := fun Γ₀ Φ₀ ψ₀ ↦
      match typeOf 0 Γ₀ Φ₀, typeOf 1 Γ₀ Φ₀, typeOf 2 Γ₀ Φ₀ with
      | some y₁, some y₂, some y₃ =>
        let at_ (y : Term) : List Tree → Term := atPos (varPos Γ₀ y)
        let main (e₁ e₂ : ℕ) : Deducer := fun Γ₁ Φ₁ ψ₁ ↦
          let X := evalTools K Φ₁ [sc, ec, sa, ea, sb, eb, e₁, e₂] [.thm (ix "relTTree") []]
          let shiftLast (left : Bool) (j : List Tree → Term) (k : Deducer) : Deducer :=
            fun Γ Φ ψ ↦ shiftK K (Φ.length - 1) left j k Γ Φ ψ
          let branch (second : Bool) : Deducer := linkK K s!"if: branch {second}" <|
            shiftK K sc false (atPos na) <| shiftLast false (atPos nb) <|
            shiftK K sa true (atPos nc) <| shiftLast false (atPos nb) <|
            shiftK K sb true (fun Γ ↦ S.add (atPos nc Γ) (atPos na Γ)) fun Γ Φ ψ ↦
              let c₂ := Φ.length - 4
              let a₂ := Φ.length - 2
              let b₁ := Φ.length - 1
              X.norm (dConv L K.G K.E S (succN (S.add (S.add (atPos nc Γ) (atPos na Γ))
                  (atPos nb Γ))) (atPos (if second then wb else wa) Γ)
                (verifyK K "if stable" <| linkK K "if stable" <|
                  X.inst c₂ (fun _ ↦ succN (v 0)) <| X.inst a₂ (fun _ ↦ succN (v 0)) <|
                    X.inst b₁ (fun _ ↦ succN (v 0)) X.byNorm)
                (verifyK K "if related" <| linkK K "if related" <|
                  X.byHyp (if second then eb else ea))) Γ Φ ψ
          -- the condition's value a quotation, its tree's label decided
          linkK K "if: the condition's value" (dRwHyp (evalRw K.G K.E (X.rs Φ₁) .full) ec
            (K.exE fun Γ Φ ψ ↦
              match evalRw K.G K.E (X.rs Φ) .full Γ Φ (call D.lab [] [v 0]) with
              | some (Y, _) => K.listCase bitTy Y (branch true) (branch false) Γ Φ ψ
              | none => traceK K "if: no label" Γ Φ ψ)) Γ₁ Φ₁ ψ₁
        (equalTy (at_ y₁) (fun _ ↦ leafT bnilT) fun e₁ ↦
          equalTy (at_ y₂) (at_ y₃) fun e₂ ↦ K.norm (main e₁ e₂)) Γ₀ Φ₀ ψ₀
      | _, _, _ => traceK K "if: no types" Γ₀ Φ₀ ψ₀
    let some d := W.intro "Reader.kwIf" (verifyK K "elements decided" <|
        W.decideAll <|
        W.element 0 fun nc wc sc ec ↦ W.element 1 fun na wa sa ea ↦
          W.element 2 fun nb wb sb eb ↦ eval nc wc sc ec na wa sa ea nb wb sb eb)
        a.ctx a.hyps a.concl
      | dbgTrace "ifCase: not proved" fun _ ↦ none
    pure (a, d))

/-- The relation at an arrow type, its domain's and codomain's relations kept folded: a value
related at the arrow type of the types of indices 2 and 1 is a function whose application to each
value related at the domain converges to a value related at the codomain; both sides in normal
form by the vocabulary's rules with the relation unfolded. -/
def relTArrow (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("relTArrow", fun ix E ↦ do
    let o := P.o
    -- context: the function, the codomain, the domain, the relation's context
    let Γ := [treeTy, treeTy, treeTy, Defs3.ctxTy]
    let arrowT := nodeT (Term.pair (numeral Kernel.Label.tyArrow)
      (consT treeTy (v 2) (consT treeTy (v 1) (nilT treeTy))))
    let lhs := Term.app (T.relT (v 3) arrowT) (v 0)
    -- under the argument: the argument v0, the function v1, the codomain v2, the domain v3
    let rhs := Internal.Logic.all o treeTy (Term.lam treeTy (Internal.Logic.imp o
      (Term.app (T.relT (v 4) (v 3)) (v 0))
      (S.conv (Term.lam nat (apps (Term.snd (S.levelN (Term.fst (v 5)) (v 0))) [v 2, v 1]))
        (Term.lam treeTy (Term.app (T.relT (v 5) (v 3)) (v 0))))))
    let rs := vRules3 P ix E.size
    let some l := nfE P.G E rs Γ lhs | dbgTrace "relTArrow: left" fun _ ↦ none
    let some r := nfE P.G E rs Γ rhs | dbgTrace "relTArrow: right" fun _ ↦ none
    let some d := byMode .full P.G E 0 (rs ++ [.delta T.q]) Γ [] l r
      | dbgTrace s!"relTArrow: unequal {(firstDiff l r).map fun (a, b) ↦
          s!"{showT a}\n  vs {showT b}"}" fun _ ↦ none
    pure (⟨0, Γ, [], Term.eq l r⟩, d))

/-- The kernel's abstraction of an annotation over a body. -/
def lamT (A b : Term) : Term :=
  nodeT (Term.pair (numeral Kernel.Label.lam) (consT treeTy A (consT treeTy b (nilT treeTy))))

/-- The kernel's application of a function to an argument. -/
def appT (f x : Term) : Term :=
  nodeT (Term.pair (numeral Kernel.Label.app) (consT treeTy f (consT treeTy x (nilT treeTy))))

/-- The abstraction compatible with the relation: an abstraction whose body, in the environment
extended by any value related at a type, converges to a value related at another, converges, at
the first level, to its closure, related at the arrow type by {lit}`relTArrow`; the closure's
application to a related value is the body's evaluation a level below. -/
def lamCompat (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("lamCompat", fun ix E ↦ do
    let o := P.o
    let K : Kit := ⟨P, S, E, ix, ["relTArrow"]⟩
    let L := K.L
    -- context: the environment, the body, the annotation, the codomain, the domain, the relation's
    -- context
    let Γ := [list treeTy, treeTy, treeTy, treeTy, treeTy, Defs3.ctxTy]
    let arrowT (A B : Term) : Term := nodeT (Term.pair (numeral Kernel.Label.tyArrow)
      (consT treeTy A (consT treeTy B (nilT treeTy))))
    -- the body's convergence related at the codomain as the soundness states it, the relation
    -- itself rather than its η-expansion
    let premise := Internal.Logic.all o treeTy (Term.lam treeTy (Internal.Logic.imp o
      (Term.app (T.relT (v 6) (v 5)) (v 0))
      (S.conv (Term.lam nat (S.evN (Term.fst (v 7)) (v 0) (consT treeTy (v 1) (v 2)) (v 3)))
        (T.relT (v 6) (v 4)))))
    let concl := S.conv (Term.lam nat (S.evN (Term.fst (v 6)) (v 0) (v 1) (lamT (v 3) (v 2))))
      (Term.lam treeTy (Term.app (T.relT (v 6) (arrowT (v 5) (v 4))) (v 0)))
    let a : Internal.Thm := ⟨0, Γ, [], Internal.Logic.imp o premise concl⟩
    let clo (Γ : List Tree) : Term := pc P "Eval.valClo"
      [v (Γ.length - 6), v (Γ.length - 4), v (Γ.length - 5)]
    let d? := dImpI L (fun Γ Φ ψ ↦ K.norm (dConv L K.G K.E S (succN zeroN) (clo Γ)
      (linkK K "lamCompat stable" K.byNorm)
      (linkK K "lamCompat related" <| K.norm <| dAllI L <| dImpI L fun Γ₁ Φ₁ ψ₁ ↦
        -- the premise at the argument, its convergence's parts
        dAllE L K.G K.E 0 (v 0) (K.impE (K.byHyp (Φ₁.length - 1)) <| K.unfoldConv <|
          K.exE <| K.exE <| K.conjE fun Γ Φ ψ ↦
            dConv L K.G K.E S (succN (v 1)) (v 0)
              (linkK K "lamCompat applied stable" <|
                instNK K (Φ.length - 2) (fun _ ↦ v 0) K.byNorm)
              (linkK K "lamCompat applied related" (K.byHyp (Φ.length - 1))) Γ Φ ψ)
          Γ₁ Φ₁ ψ₁)) Γ Φ ψ) a.ctx a.hyps a.concl
    let some d := d? | dbgTrace "lamCompat: not proved" fun _ ↦ none
    pure (a, d))

/-- The application compatible with the relation: a function converging to a value related at an
arrow type, applied to an argument converging to a value related at its domain, converges to a
value related at its codomain, the function value's application's: the three thresholds shifted
to their sum, a level above which the application evaluates to that value. -/
def appCompat (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("appCompat", fun ix E ↦ do
    let o := P.o
    let K : Kit := ⟨P, S, E, ix, ["relTArrow"]⟩
    let L := K.L
    -- context: the environment, the argument, the function, the codomain, the domain, the
    -- relation's context
    let Γ := [list treeTy, treeTy, treeTy, treeTy, treeTy, Defs3.ctxTy]
    let arrowT (A B : Term) : Term := nodeT (Term.pair (numeral Kernel.Label.tyArrow)
      (consT treeTy A (consT treeTy B (nilT treeTy))))
    -- a convergence related at a type, the type's variables one binder deep; the relation
    -- η-expanded, as the arrow's relation unfolds, or itself, as the soundness states it
    let convAt (t ty : Term) (expanded : Bool) : Term :=
      S.conv (Term.lam nat (S.evN (Term.fst (v 6)) (v 0) (v 1) t))
        (if expanded then Term.lam treeTy (Term.app (T.relT (v 6) ty) (v 0))
          else T.relT (v 5) (Term.rename ty (· - 1)))
    let a : Internal.Thm := ⟨0, Γ, [],
      Internal.Logic.imp o (convAt (v 3) (arrowT (v 5) (v 4)) true) <|
      Internal.Logic.imp o (convAt (v 2) (v 5) false) <| convAt (appT (v 3) (v 2)) (v 4) false⟩
    let shiftLast (left : Bool) (j : List Tree → Term) (k : Deducer) : Deducer :=
      fun Γ Φ ψ ↦ shiftK K (Φ.length - 1) left j k Γ Φ ψ
    let d? := dImpI L <| dImpI L <| fun Γ₀ Φ₀ ψ₀ ↦
      -- the function's convergence's parts, then the argument's
      dRwHyp (evalRw K.G K.E [.delta (S.q + 2)] .head) 0 (K.exE <| K.exE <| K.conjE
        fun Γ₁ Φ₁ ψ₁ ↦
        let sf := Φ₁.length - 2
        let rf := Φ₁.length - 1
        dRwHyp (evalRw K.G K.E [.delta (S.q + 2)] .head) 1 (K.exE <| K.exE <| K.conjE
          fun Γ₂ Φ₂ ψ₂ ↦
          let sx := Φ₂.length - 2
          let rx := Φ₂.length - 1
          -- the variables past Γ₂: the application's value and threshold
          let pos (k : ℕ) (Γ : List Tree) : Term := v (Γ.length - Γ₂.length + k)
          let nf := pos 3
          let nx := pos 1
          let wx := pos 0
          -- the function value's relation at the argument value
          dRwHyp (evalRw K.G K.E (K.rulesEx Φ₂ rf) .full) rf (fun Γ Φ ψ ↦
            dAllE L K.G K.E (Φ.length - 1) (wx Γ) (K.impE (K.byHyp rx) (K.unfoldConv
              (K.exE (K.exE (K.conjE fun Γ Φ ψ ↦
                let sa := Φ.length - 2
                let ra := Φ.length - 1
                let na (Γ : List Tree) : Term := v (Γ.length - Γ₂.length - 1)
                let wa (Γ : List Tree) : Term := v (Γ.length - Γ₂.length - 2)
                let sum (Γ : List Tree) : Term := S.add (S.add (nf Γ) (nx Γ)) (na Γ)
                shiftK K sf false nx (shiftK K (Φ.length) false na (shiftK K sx true nf
                  (shiftK K (Φ.length + 2) false na (shiftK K sa true
                    (fun Γ ↦ S.add (nf Γ) (nx Γ)) (fun Γ Φ ψ ↦
                    let f₂ := Φ.length - 4
                    let x₂ := Φ.length - 2
                    let a₁ := Φ.length - 1
                    dConv L K.G K.E S (succN (sum Γ)) (wa Γ)
                      (linkK K "appCompat stable" <|
                        instNK K f₂ (fun _ ↦ succN (v 0)) <| instNK K x₂ (fun _ ↦ succN (v 0)) <|
                          instNK K a₁ (fun _ ↦ v 0) K.byNorm)
                      (linkK K "appCompat related" (K.byHyp ra)) Γ Φ ψ))))) Γ Φ ψ))))) Γ Φ ψ)
            Γ₂ Φ₂ ψ₂) Γ₁ Φ₁ ψ₁) Γ₀ Φ₀ ψ₀
    let _ := shiftLast
    let some d := d? a.ctx a.hyps a.concl | dbgTrace "appCompat: not proved" fun _ ↦ none
    pure (a, d))

/-- The relation of an environment to a named context extended: an environment related to a
context and a value related at the type of an entry, the environment with the value related to the
context with the entry, by case analysis of the index's label, empty or a successor. -/
def envTCons (P : Prog) (T : Defs3) : Step :=
  ("envTCons", fun ix E ↦ do
    let L : Conn := ⟨P.o, logicBase⟩
    let G := P.G
    -- context: the value, the entry, the environment, the context, the relation's context
    let a : Internal.Thm := ⟨0, [treeTy, treeTy, list treeTy, list treeTy, Defs3.ctxTy],
      [T.envT (v 4) (v 3) (v 2), Term.app (T.relT (v 4) (tyOf (v 1))) (v 0)],
      T.envT (v 4) (consT treeTy (v 1) (v 3)) (consT treeTy (v 0) (v 2))⟩
    let rules (Φ : List Term) : List Internal.NormRule :=
      eqHyps Φ ++ [.thm (ix "nthConsSucc") []] ++ vRules P ix
    let norm : Deducer → Deducer := fun k Γ Φ ψ ↦ dRwBy (evalRw G E (rules Φ) .full) k Γ Φ ψ
    let byNorm : Deducer := fun Γ Φ ψ ↦ dEq (byMode .full G E 0 (rules Φ)) Γ Φ ψ
    let byHyp (h : ℕ) : Deducer := fun Γ Φ ψ ↦
      dRwHyp (evalRw G E (rules Φ.dropLast) .full) h (norm dHyp) Γ Φ ψ
    let unfold (k : ℕ) (h : ℕ) (kd : Deducer) : Deducer := fun Γ Φ ψ ↦
      dRwHyp (evalRw G E [.delta k] .head) h kd Γ Φ ψ
    let last (Φ : List Term) : ℕ := Φ.length - 1
    let exE (k : Deducer) : Deducer := fun Γ Φ ψ ↦ dExE L G E (last Φ) k Γ Φ ψ
    let conjE (k : Deducer) : Deducer := fun Γ Φ ψ ↦ dConjE L (last Φ) k Γ Φ ψ
    let allE (t : Term) (k : Deducer) : Deducer := fun Γ Φ ψ ↦ dAllE L G E (last Φ) t k Γ Φ ψ
    let impE (kp k : Deducer) : Deducer := fun Γ Φ ψ ↦ dImpE L (last Φ) kp k Γ Φ ψ
    let some (Internal.Entry.language bs) := E[ix "bitsSucc"]? | none
    let witness : Deducer := fun Γ Φ ψ ↦
      let r := Φ.length - 1
      dRwHyp (evalRw G E (rules (Φ.take (Φ.length - 2))) .full) (Φ.length - 2)
        (dExI L G E (v 0) (dConjI L byNorm (byHyp r))) Γ Φ ψ
    let succ : Deducer :=
      exE (unfold (T.q + 1) 0 (allE (leafT (v 0)) (impE (byHyp 3) (exE (conjE witness)))))
    let body : Deducer := dAllI L (dImpI L fun Γ Φ ψ ↦ do
      -- context: the index; hypotheses: the relations, truth and the lookup's truth
      let X ← nfE G E (vRules P ix) Γ (call D.lab [] [v 0])
      let cases := Internal.instTerm [] [X] bs.concl
      dCut cases (nd (.apply (ix "bitsSucc") [] [X]))
        (dDisjE L (last Φ + 1) (dExI L G E (v 1) (dConjI L byNorm (byHyp 1))) succ) Γ Φ ψ)
    let some d := dRwBy (evalRw G E [.delta (T.q + 1)] .head) body a.ctx a.hyps a.concl
      | dbgTrace "envTCons: not proved" fun _ ↦ none
    pure (a, d))

/-- The soundness at a binding of a name to a term of an annotated type in a body: the elements'
sources, expansions, the binder an atom, the annotation read by the typing and the reader, the
term's and the body's types, the body's in the context extended by the binder at the annotation,
their resolutions, the body's in the scope extended by the binder's name, and the kernel's types,
the body's in the kernel's context extended by the annotation, each decided, any absent refuting
the statement's hypothesis; the term's type and the annotation decided equal. The binding
resolves to the application of the abstraction of the body to the term, related by
{lit}`appCompat`: the abstraction by {lit}`lamCompat`, the body's soundness at the context and
environment extended, related by {lit}`envTCons`; the term by its soundness. -/
def letCase (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("letCase", fun ix E ↦ do
    let ihs := [false, false, true, true]
    let W := kwKit P S T ix E 4 ihs "Reader.kwLet"
    let K := W.K
    let L := K.L
    let a := kwThm P S T "Reader.kwLet" 4 ihs
    let equalT ← primT Kernel.Prim.equal
    -- terms under the statement's quantifiers, at an element, the variable of index nQ
    let x := pc P "Prelude.get" [pc P "Datatype.expandExpr" [v 7, v nQ]]
    let erased := pc P "Reader.expandNums" [v 3, pc P "Datatype.eraseExpr" [x]]
    let (tyT, kT) := datatypeTerms P (v nQ)
    let kernelT := pc P "Check.typeIn" [v 9, v 8, pc P "Prelude.get" [kT]]
    let get (t : Term) : Term := pc P "Prelude.get" [t]
    let at_ (c : ℕ) (t : Term) (Γ : List Tree) : Term := W.inΓ (atPos c) Γ t
    -- an element's form as the typing's fold rebuilds it, the first component of its value
    let raw (c : ℕ) (Γ : List Tree) : Term :=
      Term.fst (Term.app (Term.snd (T.foldAt 1 [W.qv 4 Γ] (at_ c x Γ))) Term.star)
    -- the annotation as the typing reads it and as the reader does
    let readTyAt (Γ : List Tree) : Term := pc P "Typing.readTy" [W.qv 4 Γ, raw 1 Γ]
    let annTy (Γ : List Tree) : Term := get (readTyAt Γ)
    let annK (Γ : List Tree) : Term := get (at_ 1 (pc P "Reader.readType" [v 4, erased]) Γ)
    -- the body's context: the binder's name with the annotation's type; the kernel's context
    -- extended by the annotation's kernel type; the environment by a value, the innermost
    let entry (Γ : List Tree) : Term :=
      pc P "Typing.abbr" [pc P "Typing.atomName" [raw 0 Γ], annTy Γ]
    let cxBody (Γ : List Tree) : Term := consT treeTy (entry Γ) (W.qv 5 Γ)
    let cBody (Γ : List Tree) : Term := consT treeTy (annK Γ) (W.qv 2 Γ)
    let overBody (j : ℕ) : Option (List Tree → Term) :=
      if j = 5 then some cxBody else if j = 2 then some cBody else none
    let bodyAt (t : Term) (Γ : List Tree) : Term := W.inΓWith overBody (atPos 3) Γ t
    -- terms in normal form, the generalized values' variables among them
    let nfIn (Γ : List Tree) (Φ : List Term) (t : Term) : Term :=
      ((evalRw K.G K.E (K.rules Φ) .full Γ Φ t).map Prod.fst).getD t
    let cutThmΦ (name : String) (σ : List Tree → List Term → List Term) (k : Deducer) :
        Deducer := fun Γ Φ ψ ↦ K.cutThm name (fun _ ↦ σ Γ Φ) k Γ Φ ψ
    -- the value of the body's evaluation: the abstraction related by lamCompat, its premise the
    -- body's soundness in the environment extended by any value related at the annotation's type
    let lamConv : Deducer := linkK K "let: the abstraction" <|
      cutThmΦ "lamCompat" (fun Γ Φ ↦ [W.qv 9 Γ, nfIn Γ Φ (get (bodyAt kT Γ)), nfIn Γ Φ (annK Γ),
          nfIn Γ Φ (get (bodyAt tyT Γ)), nfIn Γ Φ (annTy Γ), W.qv 10 Γ]) <|
        K.impE (dAllI L <| dImpI L fun Γ₁ Φ₁ ψ₁ ↦
          let w (Γ : List Tree) : Term := v (Γ.length - Γ₁.length)
          let rel := Φ₁.length - 1
          let envOk : Deducer := W.cutApply "envTCons" (fun Γ ↦ [w Γ,
              entry Γ, W.qv 9 Γ, W.qv 5 Γ, W.qv 10 Γ])
            [K.byHyp (W.hyp 1), K.byHyp rel] (fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ)
          W.soundAt 3 (fun j ↦ if j = 9 then some fun Γ ↦ consT treeTy (w Γ) (W.qv 9 Γ)
              else overBody j) envOk
            (fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ) Γ₁ Φ₁ ψ₁)
          (fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ)
    -- the application of the abstraction to the term, related by appCompat
    let eval : Deducer := linkK K "let: the application" <|
      cutThmΦ "appCompat" (fun Γ Φ ↦ [W.qv 9 Γ, nfIn Γ Φ (get (at_ 2 kT Γ)),
          lamT (nfIn Γ Φ (annK Γ)) (nfIn Γ Φ (get (bodyAt kT Γ))),
          nfIn Γ Φ (get (bodyAt tyT Γ)), nfIn Γ Φ (annTy Γ), W.qv 10 Γ]) <|
        K.impE lamConv <| K.impE (W.soundAt 2 (fun _ ↦ none) (fun _ _ _ ↦ none)
          (fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ)) <|
        fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ
    -- the term's type the annotation's, by the equality's soundness, else no type, refuting the
    -- typing's hypothesis normalized of index typed
    let sameTy (typed : ℕ) (k : Deducer) : Deducer := fun Γ₀ Φ₀ ψ₀ ↦
      let ty (Γ : List Tree) (Φ : List Term) : Term := nfIn Γ Φ (get (at_ 2 tyT Γ))
      let ann (Γ : List Tree) (Φ : List Term) : Term := nfIn Γ Φ (annTy Γ)
      let tyPos := match (ty Γ₀ Φ₀).label with
        | .var i => Γ₀.length - 1 - i
        | _ => 0
      let annPos := match (ann Γ₀ Φ₀).label with
        | .var i => Γ₀.length - 1 - i
        | _ => 0
      decideIn K (fun Γ ↦ apps equalT [atPos annPos Γ, atPos tyPos Γ])
        (linkK K "let: the types refuted" (fun Γ Φ ψ ↦
          (K.hypFalse typed Γ Φ ψ).orElse fun _ ↦ W.hypFalseU typed Γ Φ ψ))
        (K.cutThm "equalSound" (fun Γ ↦ [atPos tyPos Γ]) <| K.allEΓ (atPos annPos) <|
          K.impE (fun Γ Φ ψ ↦ (K.solve 3 Γ Φ ψ).orElse fun _ ↦
            K.cutThm "equalSymm" (fun Γ ↦ [atPos tyPos Γ, atPos annPos Γ])
              (K.impE (K.solve 3) (fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ)) Γ Φ ψ) <|
          normLastK K k) Γ₀ Φ₀ ψ₀
    -- the binder's expansion a source form; the typing's, the resolution's and the kernel's
    -- typing's hypotheses normalized, the first of index typed; then the binder's node decided:
    -- a label other than the atoms' refutes the typing's, or the source form's test, the steps at
    -- the node unfolded
    let binderAtom (k : ℕ → Deducer) : Deducer := fun Γ₀ Φ₀ ψ₀ ↦ do
      let x₀ := nfIn Γ₀ Φ₀ (at_ 0 x Γ₀)
      let p₀ := match x₀.label with
        | .var i => Γ₀.length - 1 - i
        | _ => 0
      -- the binder's expansion a source form
      let src := Φ₀.length
      let typed := Φ₀.length + 1
      let srcT (Γ : List Tree) : Term :=
        truth P.o (at_ 0 ((antecedentTests P (v nQ)).headD Term.star) Γ)
      -- the binder an atom: its characters fixed by the expansion of the numeral abbreviations,
      -- by its being a source form; whether its name is abbreviated decided, where the reader's
      -- name of the binder and the scope's agree
      let atom (cs : ℕ) : Deducer := fun Γ Φ ψ ↦
        let abbrevOf (Γ : List Tree) : Term :=
          pc P "Reader.lookupAbbrev" [nodeT (Term.pair (numeral 0) (atPos cs Γ)), W.qv 7 Γ]
        -- abbreviated, the abbreviation an atom, as the reader's binder must be, else the
        -- resolution refuted
        let isAtom : Deducer := decideOpt K (fun Γ ↦ nodeT (Term.pair
            (call D.lab [] [pc P "Prelude.get" [abbrevOf Γ]]) (nilT treeTy)))
          (linkK K "let: the abbreviation not an atom" fun Γ Φ ψ ↦
            (K.hypFalse (typed + 1) Γ Φ ψ).orElse fun _ ↦ K.hypFalse (W.hyp 7) Γ Φ ψ)
          (K.norm (k typed))
        let named : Deducer := decideKnown K (fun Γ ↦ pc P "Prelude.isSome" [abbrevOf Γ])
          (K.norm (k typed)) isAtom
        dRwHyp (evalRw K.G K.E (K.rulesEx Φ src) .full) src
          (K.cutThm "charsFixedEq" (fun Γ ↦ [atPos cs Γ, W.qv 7 Γ])
            (K.impE (fun Γ Φ ψ ↦ K.byHyp (Φ.length - 2) Γ Φ ψ) named)) Γ Φ ψ
      let srcD ← linkK K "let: the binder's source form" (K.solve 3) Γ₀ Φ₀ (srcT Γ₀)
      dCut (srcT Γ₀) srcD ([6, 7, 8].foldr (fun i k ↦ fun Γ Φ ψ ↦
        dRwHyp (evalRw K.G K.E (K.rulesEx Φ (W.hyp i)) .full) (W.hyp i) k Γ Φ ψ)
        (K.treeNode (atPos p₀ Γ₀) (fun Γ Φ ψ ↦
          let cs := Γ.length - 1
          dBits L K.G K.E (ix "listCases") (ix "bitCases") (fun bs ↦
            if bs.map Oitavem.rank == some 1 then linkK K "let: the binder's characters" (atom cs)
            else linkK K s!"let: the binder's label {bs.map Oitavem.rank} refuted"
              -- a label past the depth: the binder's expansion's being a source form refuted,
              -- which tests its label against those of atoms and lists alone, not its rest
              (fun Γ Φ ψ ↦ if bs.isNone then
                  dRwHyp (evalRw K.G K.E (K.rulesEx Φ src ++ [.thm (ix "srcNode") []]) .full) src
                    (dFalse K.L dHyp) Γ Φ ψ
                else (K.hypFalse typed Γ Φ ψ).orElse fun _ ↦ W.hypFalseU typed Γ Φ ψ))
            2 [] (v 1) Γ Φ ψ)))
        Γ₀ Φ₀ ψ₀
    let decisions : Deducer → Deducer := fun k ↦
      ((List.range 4).foldr (fun c k ↦ W.present s!"element {c + 1}'s expansion"
        (at_ c (pc P "Datatype.expandExpr" [v 7, v nQ])) 5 k) <|
      W.sources <|
      W.present "the annotation's type" readTyAt 6 <|
      W.present "the term's type" (at_ 2 tyT) 6 <|
      -- the binder an atom: its expansion a node of the label of atoms, else no type
      binderAtom fun typed ↦
      -- the reader's binder, its numeral abbreviation expanded: whether the binder's name is
      -- abbreviated, and the abbreviation an atom, decided by the tests the resolution's
      -- hypothesis is blocked on
      (fun k ↦ K.splitHyp (typed + 1) k 6) <|
      sameTy typed <|
      W.presentAt "the body's type" (bodyAt tyT) typed (W.hyp 6) <|
      W.presentAt "the annotation's kernel type" (at_ 1 (pc P "Reader.readType" [v 4, erased]))
        (typed + 1) (W.hyp 7) <|
      -- the body's resolution before the term's, as the reader tests them
      W.presentAt "the body's resolution" (bodyAt kT) (typed + 1) (W.hyp 7) <|
      W.presentAt "the term's resolution" (at_ 2 kT) (typed + 1) (W.hyp 7) <|
      -- the annotation's kernel type a type, as the kernel's abstraction requires, once the
      -- resolved term is known, else the kernel's typing refuted
      decideKnown K (fun Γ ↦ pc P "Check.isTy" [annK Γ])
        (linkK K "let: the annotation not a kernel type" fun Γ Φ ψ ↦
          (K.hypFalse (W.hyp 8) Γ Φ ψ).orElse fun _ ↦ K.hypFalse (typed + 2) Γ Φ ψ) <|
      -- the body's kernel type before the term's, as the kernel tests them
      (W.presentAt "the body's kernel type" (bodyAt kernelT) (typed + 2) (W.hyp 8) ·
        (unfolding := false)) <|
      (W.presentAt "the term's kernel type" (at_ 2 kernelT) (typed + 2) (W.hyp 8) ·
        (unfolding := false)) <| K.norm k)
    let some d := W.intro "Reader.kwLet" (decisions eval) a.ctx a.hyps a.concl
      | dbgTrace "letCase: not proved" fun _ ↦ none
    pure (a, d))

/-- The soundness at the empty list of a type or at a datum's quotation, whose element is a type's
or a datum's form, read by the typing and the reader: its source form and expansion decided, then
what the typing and the reader read from it, each present else refuting the statement's
hypothesis; the value, at the first level, the node of the empty list over the type the reader
reads, related at the list type by {lit}`relTList1`, or the datum's quotation, related at the tree
type by {lit}`relTTree`. -/
def readCase (P : Prog) (S : Defs) (T : Defs3) (isQuote : Bool) : Step :=
  (if isQuote then "quoteCase" else "nilCase", fun ix E ↦ do
    let kw := if isQuote then "Reader.kwQuote" else "Reader.kwNil"
    let W := kwKit P S T ix E 1 [false] kw
    let K := W.K
    let L := K.L
    let a := kwThm P S T kw 1 [false]
    let x := pc P "Prelude.get" [pc P "Datatype.expandExpr" [v 7, v nQ]]
    let read := pc P "Reader.expandNums" [v 3, pc P "Datatype.eraseExpr" [x]]
    -- the typing reads the element's form as its fold rebuilds it
    let readTy := pc P "Typing.readTy"
      [v 6, Term.fst (Term.app (Term.snd (T.foldAt 1 [v 6] x)) Term.star)]
    let readType := pc P "Reader.readType" [v 4, read]
    let readDatum := pc P "Reader.readDatum" [read]
    let expansion := (0, pc P "Datatype.expandExpr" [v 7, v nQ], 5)
    let stages := if isQuote then [[expansion], [(0, readDatum, 7)]]
      else [[expansion], [(0, readTy, 6)], [(0, readType, 7)]]
    -- the value read, in normal form: the variable its generalization introduced
    let readOf (t : Term) (Γ : List Tree) (Φ : List Term) : Option Term :=
      (evalRw K.G K.E (K.rules Φ) .full Γ Φ
        (pc P "Prelude.get" [W.inΓ (atPos 0) Γ t])).map Prod.fst
    let eval : Deducer := fun Γ Φ ψ ↦
      let X := evalTools K Φ [] [.thm (ix (if isQuote then "relTTree" else "relTList1")) []]
      match readOf (if isQuote then readDatum else readType) Γ Φ with
      | none => traceK K s!"{kw}: nothing read" Γ Φ ψ
      | some r =>
        let w := if isQuote then pc P "Eval.valQuote" [r]
          else nodeT (Term.pair (numeral Kernel.Label.nil) (consT treeTy r (nilT treeTy)))
        X.norm (dConv L K.G K.E S (succN zeroN) w
          (verifyK K s!"{kw} stable" <| linkK K s!"{kw} stable" X.byNorm)
          (verifyK K s!"{kw} related" <| linkK K s!"{kw} related" <| X.norm <|
            if isQuote then dExI L K.G K.E r X.byNorm else dConjI L X.byNorm X.byNorm)) Γ Φ ψ
    let some d := W.intro kw (verifyK K "read" <| W.decideWith stages eval)
        a.ctx a.hyps a.concl
      | dbgTrace s!"{kw}: not proved" fun _ ↦ none
    pure (a, d))

/-- The relation at a list type, its element type's relation kept folded: a value related at the
list type of the type of index 1 is a list value whose elements are related at it; both sides in
normal form by the vocabulary's rules with the relation unfolded. -/
def relTList1 (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("relTList1", fun ix E ↦ do
    -- context: the value, the element type, the relation's context
    let Γ := [treeTy, treeTy, Defs3.ctxTy]
    let listTy := nodeT (Term.pair (numeral Kernel.Label.tyList)
      (consT treeTy (v 1) (nilT treeTy)))
    let lhs := Term.app (T.relT (v 2) listTy) (v 0)
    let rhs := Internal.Logic.conj P.o
      (truth P.o (pc P "Prelude.isSome" [pc P "Eval.listOf" [v 0]]))
      (S.allL (Term.lam treeTy (Term.app (T.relT (v 3) (v 2)) (v 0)))
        (call D.children [] [pc P "Prelude.get" [pc P "Eval.listOf" [v 0]]]))
    let rs := vRules3 P ix E.size
    let some l := nfE P.G E rs Γ lhs | dbgTrace "relTList1: left" fun _ ↦ none
    let some r := nfE P.G E rs Γ rhs | dbgTrace "relTList1: right" fun _ ↦ none
    let some d := byMode .full P.G E 0 (rs ++ [.delta T.q]) Γ [] l r
      | dbgTrace s!"relTList1: unequal {(firstDiff l r).map fun (a, b) ↦
          s!"{showT a}\n  vs {showT b}"}" fun _ ↦ none
    pure (⟨0, Γ, [], Term.eq l r⟩, d))

/-- The soundness at a list's construction: the elements' antecedents decided and their soundness
instantiated; the tail's type the list type of the head's, by the equality's soundness, any other
refuting the typing; the tail's value a list value, by {lit}`relTList1`, its test decided; the
thresholds shifted to their sum, at which, a level above, the construction evaluates to the node
of the head's value and the tail's, a list value whose elements are related. -/
def consCase (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("consCase", fun ix E ↦ do
    let W := kwKit P S T ix E 2 (kw := "Reader.kwCons")
    let K := W.K
    let L := K.L
    let a := kwThm P S T "Reader.kwCons" 2
    let tyT := (datatypeTerms P (v nQ)).1
    let equalT ← primT Kernel.Prim.equal
    let typeOf (c : ℕ) (Γ : List Tree) (Φ : List Term) : Option Term :=
      (evalRw K.G K.E (K.rules Φ) .full Γ Φ
        (pc P "Prelude.get" [W.inΓ (atPos c) Γ tyT])).map Prod.fst
    let varPos (Γ : List Tree) (t : Term) : ℕ := match t.label with
      | .var i => Γ.length - 1 - i
      | _ => 0
    let eval (nx wx sx ex nxs wxs sxs exs : ℕ) : Deducer := fun Γ₀ Φ₀ ψ₀ ↦
      match typeOf 0 Γ₀ Φ₀, typeOf 1 Γ₀ Φ₀ with
      | some y₁, some y₂ =>
        let p₁ := varPos Γ₀ y₁
        let p₂ := varPos Γ₀ y₂
        let listTy (Γ : List Tree) : Term := nodeT (Term.pair (numeral Kernel.Label.tyList)
          (consT treeTy (atPos p₁ Γ) (nilT treeTy)))
        let w (Γ : List Tree) : Term := nodeT (Term.pair (numeral Kernel.Label.cons)
          (consT treeTy (atPos wx Γ) (consT treeTy (atPos wxs Γ) (nilT treeTy))))
        -- after the types' equation: the tail's relation a list value's, its test decided
        let main : Deducer := fun Γ₁ Φ₁ ψ₁ ↦
          let X := evalTools K Φ₁ [sx, ex, sxs, exs, Φ₁.length - 1] [.thm (ix "relTList1") []]
          -- the hypotheses kept and those after the base, the last first
          let kept (Φ : List Term) : List ℕ :=
            ((List.range Φ.length).filter fun h ↦
              h ∈ [sx, ex, sxs, exs, Φ₁.length - 1] ∨ Φ₁.length ≤ h).reverse
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
              (verifyK K "cons stable" <| linkK K "cons stable" <|
                X.inst x₁ (fun _ ↦ succN (v 0)) (X.inst xs₁ (fun _ ↦ succN (v 0)) X.byNorm))
              (verifyK K "cons related" <| linkK K "cons related" (auto 5))) Γ Φ ψ
          let shifted : Deducer := linkK K "cons: shifted" <|
            shiftK K sx false (atPos nxs) <| shiftK K sxs true (atPos nx) fin
          -- the tail's value a list value: its test decided, false refuting its truth
          let tailList : Deducer := K.conjE fun Γ Φ ψ ↦
            let lt := Φ.length - 2
            linkK K "cons: the tail's list" (decideIn K
              (fun Γ ↦ pc P "Prelude.isSome" [pc P "Eval.listOf" [atPos wxs Γ]])
              (K.hypFalse lt) shifted) Γ Φ ψ
          linkK K "cons: the tail's relation"
            (dRwHyp (evalRw K.G K.E (X.rs Φ₁) .full) exs tailList) Γ₁ Φ₁ ψ₁
        -- the types' test decided: the tail's type the list type of the head's, or no type
        decideIn K (fun Γ ↦ apps equalT [listTy Γ, atPos p₂ Γ])
          (linkK K "cons: the types refuted" (K.hypFalse (W.hyp 6)))
          (linkK K "cons: the types' equation" <|
            K.cutThm "equalSymm" (fun Γ ↦ [atPos p₂ Γ, listTy Γ]) <| K.impE (K.solve 3) <|
            K.cutThm "equalSound" (fun Γ ↦ [atPos p₂ Γ]) <| K.allEΓ listTy <|
            K.impE (fun Γ Φ ψ ↦ K.byHyp (Φ.length - 3) Γ Φ ψ) <| normLastK K <|
            K.norm (linkK K "cons: after the types" main)) Γ₀ Φ₀ ψ₀
      | _, _ => traceK K "cons: no types" Γ₀ Φ₀ ψ₀
    let some d := W.intro "Reader.kwCons" (verifyK K "elements decided" <|
        W.decideAll <|
        W.element 0 fun nx wx sx ex ↦ W.element 1 fun nxs wxs sxs exs ↦
          eval nx wx sx ex nxs wxs sxs exs) a.ctx a.hyps a.concl
      | dbgTrace "consCase: not proved" fun _ ↦ none
    pure (a, d))

/-- The relation at a product type, its components' relations kept folded: a value related at the
product of the types of indices 1 and 2 is a pair of values related at them; both sides in normal
form by the vocabulary's rules with the relation unfolded. -/
def relTProd (P : Prog) (T : Defs3) : Step :=
  ("relTProd", fun ix E ↦ do
    let o := P.o
    -- context: the value, the second type, the first, the relation's context
    let Γ := [treeTy, treeTy, treeTy, Defs3.ctxTy]
    let prodT := nodeT (Term.pair (numeral Kernel.Label.tyProd)
      (consT treeTy (v 2) (consT treeTy (v 1) (nilT treeTy))))
    let lhs := Term.app (T.relT (v 3) prodT) (v 0)
    let rhs := Internal.Logic.ex o treeTy (Term.lam treeTy (Internal.Logic.ex o treeTy
      (Term.lam treeTy (Internal.Logic.conj o
        (Term.eq (v 2) (pc P "Eval.valPair" [v 1, v 0]))
        (Internal.Logic.conj o (Term.app (T.relT (v 5) (v 4)) (v 1))
          (Term.app (T.relT (v 5) (v 3)) (v 0)))))))
    let rs := vRules3 P ix E.size
    let some l := nfE P.G E rs Γ lhs | dbgTrace "relTProd: left" fun _ ↦ none
    let some r := nfE P.G E rs Γ rhs | dbgTrace "relTProd: right" fun _ ↦ none
    let some d := byMode .full P.G E 0 (rs ++ [.delta T.q]) Γ [] l r
      | dbgTrace s!"relTProd: unequal {(firstDiff l r).map fun (a, b) ↦
          s!"{showT a}\n  vs {showT b}"}" fun _ ↦ none
    pure (⟨0, Γ, [], Term.eq l r⟩, d))

/-- The development of the soundness at a list. -/
def listDev3 (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  rawAtom P T :: rawList P T :: rawAtomR P T :: srcNode P T ::
  ([("Reader.kwLet", 4), ("Reader.kwQuote", 1), ("Reader.kwNil", 1), ("Reader.kwIf", 3),
      ("Reader.kwCons", 2), ("Reader.kwFst", 1), ("Reader.kwSnd", 1), ("Reader.kwPair", 2)].flatMap
    fun (kw, n) ↦ kwEqs P T kw n) ++
  [relTArrow P S T, lamCompat P S T, appCompat P S T, envTCons P T,
    relTTree P T, relTList1 P S T, readCase P S T true, readCase P S T false, ifCase P S T,
    consCase P S T, relTProd P T] ++
    relTProdNodes P T ++
    [relTProdE P S T, projCase P S T false, projCase P S T true, pairCase P S T, letCase P S T]

/-- The development of the soundness at a list, after the base's and the atom's declarations,
stored as the certificate {lit}`datatype-list`, each declaration checked as it is stored. -/
def listCertificates (P : Prog) (S : Defs) (T : Defs3) (before : List Internal.Decl) :
    Except String (List (String × List Internal.Decl)) := do
  let some dev := baseDev3 P S T | throw "the base is not stated"
  let E : Array Internal.Entry := (before.filterMap fun
    | .language a _ => some (Internal.Entry.language a)
    | _ => none).toArray
  let names := dev.map (·.1) ++ (atomDev3 P S T).map (·.1)
  unless names.length = E.size do throw "the certificates before are not the base's and the atom's"
  -- each step's proof reported as it is found
  let list := (listDev3 P S T).map fun (nm, f) ↦
    (nm, fun ix E ↦ (f ix E).map fun r ↦ dbgTrace s!"{nm} proved" fun _ ↦ r)
  let (_, _, ds) ← developAfter names E list
  checkAfter P.G E (list.map (·.1)) ds
  pure [("datatype-list", ds)]



end GebTests.Prototypes.FreeTopos.Datatypes

end
