/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Holes
public import Geb.Prototypes.FreeTopos.Internal.Logic

set_option doc.verso true in
/-!
# Conditional certificates for proof sketches

A hole's obligation is closed over its hypotheses by implication and over its context by
universal quantification. These conditions and the goal's hypotheses imply its conclusion in
the translated theorem. The translation constructs conversion certificates and checks them with
the existing checker, in the original environment.

## Main definitions

* {lit}`condition` — the closed formula of an obligation.
* {lit}`conditional` — the theorem of the conditions implying the goal.
* {lit}`certify` — checked translation to a conversion certificate.

## Main statements

* {lit}`convChecks_of_certify` — a returned certificate is accepted by the conversion checker.
* {lit}`valid_of_certify` — its conditional theorem is valid without assuming the holes valid.

## Implementation notes

This is a partial translation. It moves references to hypotheses past a prefix of conditions,
including references in normalizer and machine rules. It preserves closed premises of rose-tree
uniqueness, which resets their hypotheses, but cannot translate holes in those premises. An
embedded sequent certificate can also fail when the prefix changes the sequent it must prove.
Such failures return no certificate; the hole checker can still accept the original sketch.
The translation through closed lemmas in {lit}`Holes/Closed.lean` handles those rules and
universally closes the resulting theorem's term context as well.

## Tags

internal language, proof hole, conditional certificate, universal quantification
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal.ProofHoles

universe v

open PartialHorn (Tree)
open Sorts (obj)

open scoped FinEnum

/-- The formula of a sequent, its hypotheses discharged in order and its variables quantified
from innermost to outermost. The connectives are the definitions from index {lit}`o`. Object
variables remain parameters of the theorem. -/
def condition (o : ℕ) (a : Thm) : Term :=
  a.ctx.foldl (fun p A ↦ Logic.all o A (Term.lam A p)) (a.hyps.foldr (Logic.imp o) a.concl)

/-- A formula among the hypotheses, cited at its first occurrence. -/
def hypothesis (Φ : List Term) (p : Term) : Option ConvDeriv :=
  (Φ.findIdx? fun q ↦ decide (q = p)).map fun i ↦ RoseTree.node (.base (.hyp i)) []

/-- Eliminate one universal quantifier at a term, then reduce the
predicate's application. The logical theorems begin at index {lit}`j`. -/
def specializeAt (o j : ℕ) (t : Term) (p : Term × ConvDeriv) : Option (Term × ConvDeriv) :=
  match p.1.label, p.1.children with
  | .defn k [A], [P] =>
    if k = o + 3 then
      match P.label, P.children with
      | .lam _, [body] =>
        some (Term.subst body (instVar t),
          RoseTree.node (.base (.convFrom (Term.app P t)))
            [RoseTree.node (.base .beta) [],
              RoseTree.node (.base (.apply (j + 5) [A] [t, P])) [p.2]])
      | _, _ => none
    else none
  | _, _ => none

/-- Eliminate one universal quantifier at the variable of index {lit}`i`. -/
def specializeCondition (o j i : ℕ) (p : Term × ConvDeriv) : Option (Term × ConvDeriv) :=
  specializeAt o j (Term.var i) p

/-- Eliminate one implication using an antecedent among the local hypotheses. -/
def applyCondition (o j : ℕ) (Φ : List Term) (p : Term × ConvDeriv) (h : Term) :
    Option (Term × ConvDeriv) := do
  match p.1.label, p.1.children with
  | .defn k [], [q, h'] =>
    if k = o + 2 ∧ h' = h then
      let d ← hypothesis Φ h
      some (q, RoseTree.node (.base (.apply (j + 4) [] [q, h])) [p.2, d])
    else none
  | _, _ => none

/-- Prove an obligation from its universally closed condition and its local hypotheses.
Quantified variables are instantiated from outermost to innermost. -/
def dischargeCondition (o j : ℕ) (conditions : List Term) (a : Thm) : Option ConvDeriv := do
  let Φ := conditions ++ a.hyps
  let d ← hypothesis Φ (condition o a)
  let p ← (List.range a.ctx.length).reverse.foldlM
    (fun p i ↦ specializeCondition o j i p) (condition o a, d)
  let p ← a.hyps.foldlM (applyCondition o j Φ) p
  if p.1 = a.concl then some p.2 else none

/-- Move references to local hypotheses past a prefix of closed assumptions. -/
def shiftHypotheses (k : ℕ) : Rule → Rule
  | .hyp i => .hyp (k + i)
  | .rwHyp i flip => .rwHyp (k + i) flip
  | r => r

/-- Move hypothesis references in a normalizer's rules past the added assumptions. -/
def shiftNormHypotheses (k : ℕ) : NormRule → NormRule
  | .rule r => .rule (shiftHypotheses k r)
  | .hyp i => .hyp (k + i)
  | r => r

/-- Move hypothesis references, including those inside conversion steps, past the assumptions. -/
def shiftConvHypotheses (k : ℕ) : ConvRule → ConvRule
  | .base r => .base (shiftHypotheses k r)
  | .norm rs fuel => .norm (rs.map (shiftNormHypotheses k)) fuel
  | .eval rs fuel depth => .eval (rs.map (shiftNormHypotheses k)) fuel depth
  | .machine fuel m except kl kc rs =>
    .machine fuel m except kl kc (rs.map (shiftNormHypotheses k))
  | r => r

/-- Replace each hole by elimination of its condition, moving local hypothesis references past
the conditions. Rose-tree uniqueness resets the hypotheses of its premises, so its children are
translated without the prefix; a hole there cannot be discharged by a surrounding condition.
The result is a candidate, checked by {lit}`certify` before it can be returned. -/
def conditionalDeriv {α : Type} (o j : ℕ) (goals : α → Thm) :
    Sketch α → List Term → Option ConvDeriv :=
  PFunctor.FreeM.rec (fun h conditions ↦ dischargeCondition o j conditions (goals h))
    (fun r _ cs conditions ↦ match r.1 with
    | .norm .. | .eval .. | .lit .. | .machine .. =>
      some (RoseTree.node (shiftConvHypotheses conditions.length r.1) [])
    | _ => do
      let ps ← (List.ofFn cs).mapM fun c ↦ c (match r.1 with
        | .base (.roseInd ..) => []
        | _ => conditions)
      pure (RoseTree.node (shiftConvHypotheses conditions.length r.1) ps))

/-- The conditions of the holes, retaining occurrence order, followed by the goal's hypotheses. -/
def assumptions {α : Type} (o : ℕ) (goals : α → Thm) (a : Thm) (d : Sketch α) : List Term :=
  (holes d).map (fun h ↦ condition o (goals h)) ++ a.hyps

/-- The conditional conclusion, with the original free variables and object parameters. The
hole conditions and original hypotheses become explicit implications; it has no hypotheses. -/
def conditional {α : Type} (o : ℕ) (goals : α → Thm) (a : Thm) (d : Sketch α) : Thm :=
  { a with hyps := [], concl := (assumptions o goals a d).foldr (Logic.imp o) a.concl }

/-- Implication introduction for a conversion derivation. The consequent is proved under the
antecedent appended after the {lit}`n` existing hypotheses, as in {lit}`Logic.impI`. -/
def impIntro (j n : ℕ) (p q : Term) (d : ConvDeriv) : ConvDeriv :=
  let nd (r : Rule) (cs : List ConvDeriv := []) := RoseTree.node (.base r) cs
  nd .conv [nd .delta, nd .propExt [nd (.apply (j + 2) [] [q, p]) [nd (.hyp n)],
    nd (.apply (j + 1) [] [q, p]) [nd (.hyp n), d]]]

/-- Discharge the hypotheses, from last to first, into nested implications. -/
def imply (o j : ℕ) (Φ : List Term) (φ : Term) (d : ConvDeriv) : ConvDeriv :=
  (Φ.zipIdx.foldr (fun (p, i) (q, d) ↦ (Logic.imp o p q, impIntro j i p q d)) (φ, d)).2

/-- Translate an accepted sketch into an ordinary conversion certificate of its conditional
conclusion. The logical definitions start at {lit}`o`, their theorems at {lit}`j`. Both the
sketch and the resulting certificate must check in the original environment. No hole is added
to that environment. Translation can fail, including at an open rose-tree uniqueness premise
or an embedded sequent certificate whose hypotheses change. -/
def certify {α : Type} (G : Globals) (E : Array Entry) (R : List ℕ) (o j : ℕ)
    (goals : α → Thm) (a : Thm) (d : Sketch α) : Option ConvDeriv := do
  if !checks G E R goals a d then none else do
    let c ← conditionalDeriv o j goals d ((holes d).map fun h ↦ condition o (goals h))
    let c := imply o j (assumptions o goals a d) a.concl c
    if (conditional o goals a d).convChecks G E R c then some c else none

/-- A returned certificate proves exactly the conditional conclusion in the unchanged
environment, and its source sketch passed the hole checker. -/
theorem convChecks_of_certify {α : Type} {G : Globals} {E : Array Entry} {R : List ℕ}
    {o j : ℕ} {goals : α → Thm} {a : Thm} {d : Sketch α} {c : ConvDeriv}
    (h : certify G E R o j goals a d = some c) :
    checks G E R goals a d = true ∧ (conditional o goals a d).convChecks G E R c = true := by
  simp only [certify] at h
  split at h
  · cases h
  · rename_i hc
    simp only [Bool.not_eq_true] at hc
    obtain ⟨c', _, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · obtain rfl := Option.some.inj h
      exact ⟨by simpa using hc, by assumption⟩
    · cases h

/-- A returned certificate's conditional theorem is valid, without assuming that any hole is
valid. Only the original environment and the conversion checker's usual model assumptions are
required. -/
theorem valid_of_certify {α : Type} {defs : List PartialHorn.Defn}
    {M : PartialHorn.Model.{v} (ext defs).sig} (hM : PartialHorn.IsModel (ext defs) M)
    {G : Globals} (hG : G.WF)
    (hps : ∀ m ρ, ρ.map Sigma.fst = List.replicate m obj → PrimsHom M ρ G m)
    (hds : ∀ m ρ, ρ.map Sigma.fst = List.replicate m obj → DefsHom M ρ G m)
    (hδ : DefnsOk M G) {E : Array Entry}
    (hE : ∀ (j : ℕ) (e : Entry), E[j]? = some e → e.Valid M G) {R : List ℕ}
    (hR : ∀ j ∈ R, Literals.ready G E j = true)
    (hcert : ∀ cds, compileDefs G = some cds → G.base = sig.length → cds <+: defs)
    {o j : ℕ} {goals : α → Thm} {a : Thm} {d : Sketch α} {c : ConvDeriv}
    (h : certify G E R o j goals a d = some c) : (conditional o goals a d).Valid M G :=
  Thm.valid_of_convChecks hM hG hps hds hδ hcert hE hR (convChecks_of_certify h).2

end Geb.FreeTopos.Internal.ProofHoles

end
