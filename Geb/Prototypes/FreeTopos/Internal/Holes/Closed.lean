/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Holes.Conditional
public import Geb.Prototypes.FreeTopos.Internal.Holes.Sequent
public import Geb.Prototypes.FreeTopos.Internal.Holes.Rose

set_option doc.verso true in
/-!
# Closed conditional proofs

Each proof node is stated as a closed formula, with its own hypotheses discharged and its
variables universally quantified. These formulas are proved in premise order and combined by
cuts. The auxiliary assumptions at a node are consequently closed, including when induction
removes a variable from the context.

## Main definitions

* {lit}`Premise`, {lit}`Node` — the proof nodes and their rewriting or logical premises.
* {lit}`plan` — the nodes in premise order, with their original sequents.
* {lit}`conditional`, {lit}`certify` — the closed conditional theorem and its certificate.

## Main statements

* {lit}`convChecks_of_certify` — the source checks and the returned certificate replays.
* {lit}`valid_of_certify` — conditional validity without assuming any hole valid.

## Implementation notes

The logical definitions and theorem entries are supplied by their starting indices. Every
intermediate lemma and the final certificate are checked in the original environment. The
translation is a partial certificate producer: it returns nothing on malformed input, failed
construction or failed replay, including exhaustion of the normalizers' bounds. It does not
assert that every accepted sketch is translated successfully.

## Tags

internal language, proof hole, conditional certificate, induction
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal.ProofHoles.Closed

open PartialHorn (Tree)

universe u

open scoped FinEnum

/-- A node's premise: an existing rewriting, or a sequent to prove. -/
inductive Premise where
  /-- An existing rewriting derivation, with its local hypothesis references. -/
  | rewrite (d : ConvDeriv)
  /-- A logical premise, supplied by its closed conditional lemma. -/
  | proof (a : Thm)

/-- A proof node with its original sequent and premises. -/
structure Node where
  /-- The original sequent. -/
  sequent : Thm
  /-- The conversion rule; matching applications have their instances made explicit. -/
  rule : ConvRule
  /-- Rewritings and logical premises in rule order. -/
  premises : List Premise

/-- The sequents at a rule's logical premises, as in the conversion checker. Rewriting premises
retain their derivations. The source sketch is checked before this traversal is used. -/
def premises (G : Globals) (E : Array Entry) (R : List ℕ) (a : Thm)
    (r : ConvRule) (cs : List ConvDeriv) : Option (ConvRule × List Premise) := do
  let goal (Γ : List Tree) (Φ : List Term) (φ : Term) : Premise :=
    .proof { a with ctx := Γ, hyps := Φ, concl := φ }
  let at' (ps : List Premise) := some (r, ps)
  let Γ := a.ctx
  let Φ := a.hyps
  let φ := a.concl
  let n := a.arity
  match r, cs with
  | .base (.cut ψ), [_, _] => at' [goal Γ Φ ψ, goal Γ (Φ ++ [ψ]) φ]
  | .base .conv, [d, _] =>
    let φ' ← (convCheck G E R n d).1 Γ Φ φ
    at' [.rewrite d, goal Γ Φ φ']
  | .base (.convFrom ψ), [d, _] => at' [.rewrite d, goal Γ Φ ψ]
  | .base .propExt, [_, _] =>
    let (p, q) ← eqParts φ
    at' [goal Γ (Φ ++ [p]) q, goal Γ (Φ ++ [q]) p]
  | .base .funExt, [_] =>
    let (f, g) ← eqParts φ
    let (A, _) ← (typeIn G n Γ f).bind expParts
    at' [goal (A :: Γ) (Φ.map weaken1)
      (Term.eq (Term.app (weaken1 f) (Term.var 0)) (Term.app (weaken1 g) (Term.var 0)))]
  | .base (.apply j θ σ), _ =>
    let b ← (E[j]?).bind Entry.language?
    at' (b.hyps.map fun h ↦ goal Γ Φ (instTerm θ σ h))
  | .applyMatch j θ, _ =>
    let σ ← applyInst E j θ φ
    let b ← (E[j]?).bind Entry.language?
    pure (.base (.apply j θ σ), b.hyps.map fun h ↦ goal Γ Φ (instTerm θ σ h))
  | .base (.natInd kz ks s), [_, _, _] =>
    let (t, u) ← eqParts φ
    let _ :: Γ' := Γ | failure
    let Φ' ← lowerHyps G n Γ' Φ
    at' [goal Γ' Φ' (Term.eq (Term.subst t (instVar (Term.arr kz [] Term.star)))
        (Term.subst u (instVar (Term.arr kz [] Term.star)))),
      goal Γ Φ (Term.eq (natSuccAt ks t) (Term.subst s (atVar0 t))),
      goal Γ Φ (Term.eq (natSuccAt ks u) (Term.subst s (atVar0 u)))]
  | .base (.listInd kn kc s), [_, _, _] =>
    let (t, u) ← eqParts φ
    let c :: Γ' := Γ | failure
    let A ← listPart c
    let Φ' ← lowerHyps G n Γ' Φ
    at' [goal Γ' Φ' (Term.eq (Term.subst t (instVar (Term.arr kn [A] Term.star)))
        (Term.subst u (instVar (Term.arr kn [A] Term.star)))),
      goal (c :: A :: Γ') (Φ'.map weaken2)
        (Term.eq (listConsAt kc A t) (Term.subst s (atVar0 (weakenElem t)))),
      goal (c :: A :: Γ') (Φ'.map weaken2)
        (Term.eq (listConsAt kc A u) (Term.subst s (atVar0 (weakenElem u))))]
  | .base (.natIndHyp kz ks), [_, _] =>
    let _ :: Γ' := Γ | failure
    let Φ' ← lowerHyps G n Γ' Φ
    at' [goal Γ' Φ' (Term.subst φ (instVar (Term.arr kz [] Term.star))),
      goal Γ (Φ ++ [φ]) (natSuccAt ks φ)]
  | .base (.listIndHyp kn kc), [_, _] =>
    let c :: Γ' := Γ | failure
    let A ← listPart c
    let Φ' ← lowerHyps G n Γ' Φ
    at' [goal Γ' Φ' (Term.subst φ (instVar (Term.arr kn [A] Term.star))),
      goal (c :: A :: Γ') (Φ'.map weaken2 ++ [weakenElem φ]) (listConsAt kc A φ)]
  | .base (.coprodInd kl kr), [_, _] =>
    let c :: Γ' := Γ | failure
    let (A, B) ← coprodParts c
    at' [goal (A :: Γ') Φ (Term.subst φ (atVar0 (Term.arr kl [A, B] (Term.var 0)))),
      goal (B :: Γ') Φ (Term.subst φ (atVar0 (Term.arr kr [A, B] (Term.var 0))))]
  | .base (.quotInd kq θ), [_] =>
    let _ :: Γ' := Γ | failure
    let p ← G.prims[kq]?
    at' [goal (PartialHorn.subst θ p.dom :: Γ') Φ
      (Term.subst φ (atVar0 (Term.arr kq θ (Term.var 0))))]
  | .base (.roseInd kn kl kc s), [_, _] =>
    let (t, u) ← eqParts φ
    let [r] := Γ | failure
    let C ← typeIn G n Γ t
    let (A, _) ← roseParts r
    at' [goal [list r, A] [] (Term.eq (roseNodeAt kn r A t)
        (Term.subst s (atVar0 (roseMapAt kl kc C t)))),
      goal [list r, A] [] (Term.eq (roseNodeAt kn r A u)
        (Term.subst s (atVar0 (roseMapAt kl kc C u))))]
  | .base (.roseIndHyp kn kl kc), [_] =>
    let r :: Γ' := Γ | failure
    let (A, _) ← roseParts r
    let Φ' ← lowerHyps G n Γ' Φ
    at' [goal (list r :: A :: Γ') (Φ'.map weaken2 ++ [roseHyp kl kc φ])
      (roseNodeAt kn r A φ)]
  | _, _ => at' (cs.map Premise.rewrite)

/-- A subtree's unchanged derivation and its proof nodes at a sequent. The unchanged derivation
is used only for rewritings, where a hole cannot be an inspected premise. -/
abbrev Plan := ConvDeriv × (Thm → Option (List Node))

/-- Collect the logical children first, then the node with the sequents they prove. -/
def planStep (G : Globals) (E : Array Entry) (R : List ℕ) (r : ConvRule)
    (cs : List Plan) : Plan :=
  (RoseTree.node r (cs.map Prod.fst), fun a ↦ do
    let (r', ps) ← premises G E R a r (cs.map Prod.fst)
    guard (ps.length == cs.length)
    let ds ← (cs.zip ps).mapM fun (c, p) ↦ match p with
      | .rewrite _ => some []
      | .proof b => c.2 b
    pure (ds.flatten ++ [⟨a, r', ps⟩]))

/-- Collect a sketch's proof nodes, with holes supplied by their closed conditions. -/
def plan {α : Type} (G : Globals) (E : Array Entry) (R : List ℕ) : Sketch α → Plan :=
  PFunctor.FreeM.rec (fun _ ↦ (RoseTree.node (.base .join) [], fun _ ↦ some []))
    (fun r _ cs ↦ planStep G E R r.1 (List.ofFn cs))

/-- Universal introduction for a conversion derivation under the added hypothesis of truth. -/
def allIntro (d : ConvDeriv) : ConvDeriv :=
  let nd (r : Rule) (cs : List ConvDeriv := []) := RoseTree.node (.base r) cs
  nd .conv [nd .delta, nd .funExt [nd .conv [nd .cong [nd .beta, nd .beta],
    nd .propExt [RoseTree.map ConvRule.base Logic.trueI, d]]]]

/-- Discharge hypotheses after a fixed prefix of closed assumptions. -/
def implyFrom (o j k : ℕ) (Φ : List Term) (φ : Term) (d : ConvDeriv) : ConvDeriv :=
  (Φ.zipIdx.foldr (fun (p, i) (q, d) ↦ (Logic.imp o p q, impIntro j (k + i) p q d))
    (φ, d)).2

/-- Close a sequent's hypotheses and context. Universal introduction adds one truth hypothesis
per variable; the supplied body is under the closed assumptions, those truths, and the original
hypotheses, in that order. -/
def close (o j : ℕ) (C : List Term) (a : Thm) (d : ConvDeriv) : ConvDeriv :=
  a.ctx.foldl (fun d _ ↦ allIntro d)
    (implyFrom o j (C.length + a.ctx.length) a.hyps a.concl d)

/-- The closed assumptions available in the body after introducing a sequent's variables. -/
def bodyAssumptions (o : ℕ) (C : List Term) (a : Thm) : List Term :=
  C ++ List.replicate a.ctx.length (Logic.tt o)

/-- Prove a node's closed formula from those of its premises. Rose-tree uniqueness is handled
by a separate derived proof; embedded sequent certificates are transported to the hypotheses. -/
def regular (G : Globals) (E : Array Entry) (o j : ℕ) (C : List Term)
    (node : Node) : Option ConvDeriv := do
  let a := node.sequent
  let extra := bodyAssumptions o C a
  let c ← match node.rule with
    | .base (.certSeq c) => do
      let c ← Sequent.weaken G E a (extra ++ a.hyps) c
      pure (RoseTree.node (.base (.certSeq c)) [])
    | _ => do
      let ps ← node.premises.mapM fun p ↦ match p with
        | .rewrite d => some (RoseTree.map (shiftConvHypotheses extra.length) d)
        | .proof b => dischargeCondition o j extra b
      pure (RoseTree.node (shiftConvHypotheses extra.length node.rule) ps)
  pure (close o j C a c)

/-- Closed assumptions and the lemmas proved under them in order. -/
structure Ledger where
  /-- Initial hole conditions followed by the conclusions of the recorded lemmas. -/
  claims : List Term
  /-- Each new closed formula with its certificate under the preceding claims. -/
  proofs : List (Term × ConvDeriv) := []

/-- Record a closed lemma only after the ordinary conversion checker accepts its certificate. -/
def add (G : Globals) (E : Array Entry) (R : List ℕ) (o : ℕ) (a : Thm)
    (c : ConvDeriv) : StateT Ledger Option Unit := do
  let s ← get
  let p := condition o a
  let b : Thm := ⟨a.arity, [], s.claims, p⟩
  guard (b.convChecks G E R c)
  set { s with claims := s.claims ++ [p], proofs := s.proofs ++ [(p, c)] }

/-- Derive a uniqueness node from induction with its hypothesis. The two algebra equations
are available as closed lemmas even though the original uniqueness rule resets hypotheses. -/
def rose (G : Globals) (E : Array Entry) (R : List ℕ) (o j : ℕ) (node : Node)
    (kn kl kc : ℕ) : StateT Ledger Option Unit := do
  let a := node.sequent
  let (t, u) ← eqParts a.concl
  let [r] := a.ctx | failure
  let _ ← roseParts r
  let C ← typeIn G a.arity a.ctx t
  let [Premise.proof b, Premise.proof b'] := node.premises | failure
  let rb := Rose.rebuild a.arity kl kc
  let claims := (← get).claims
  if !claims.contains (condition o rb) then
    add G E R o rb (close o j claims rb (Rose.rebuildProof kl kc))
  let m := Rose.mapEquation o a.arity kl kc r C t u
  let claims := (← get).claims
  if !claims.contains (condition o m) then
    let c ← Rose.mapProof o j a.arity kl kc r C t u (bodyAssumptions o claims m)
    add G E R o m (close o j claims m c)
  let a₀ := { a with hyps := [] }
  let claims := (← get).claims
  let extra := bodyAssumptions o claims a₀
  let ih := roseHyp kl kc a.concl
  let k := extra.length
  let db ← dischargeCondition o j (extra ++ [ih]) b
  let db' ← dischargeCondition o j (extra ++ [ih, b.concl]) b'
  let dm ← Rose.specialize o j (extra ++ [ih, b.concl, b'.concl]) m (Term.var 0)
  let q := Term.eq (roseMapAt kl kc C t) (roseMapAt kl kc C u)
  let dq := Rose.impElim j ih q dm (Rose.nd (.hyp k))
  let c := Rose.nd (.roseIndHyp kn kl kc) [Rose.nd (.cut b.concl) [db,
    Rose.nd (.cut b'.concl) [db', Rose.nd (.cut q) [dq,
      Rose.nd .join [
        Rose.nd .trans [Rose.nd (.rwHyp (k + 1) false), Rose.norm [.hyp (k + 3)]],
        Rose.nd .trans [Rose.nd (.rwHyp (k + 2) false), Rose.norm [.hyp (k + 3)]]]]]]]
  add G E R o a₀ (close o j claims a₀ c)
  if a.hyps.isEmpty then return
  let claims := (← get).claims
  let c ← dischargeCondition o j (bodyAssumptions o claims a ++ a.hyps) a₀
  add G E R o a (close o j claims a c)

/-- Record a node's conditional lemma unless it is already an assumption. -/
def synthesize (G : Globals) (E : Array Entry) (R : List ℕ) (o j : ℕ)
    (node : Node) : StateT Ledger Option Unit := do
  let C := (← get).claims
  if C.contains (condition o node.sequent) then return
  if let .base (.roseInd kn kl kc _) := node.rule then
    return ← rose G E R o j node kn kl kc
  let c ← regular G E o j C node
  add G E R o node.sequent c

/-- The fully closed conditional theorem: the hole conditions imply the universally closed
original sequent. Object variables remain its external parameters. -/
def conditional {α : Type} (o : ℕ) (goals : α → Thm) (a : Thm) (d : Sketch α) : Thm :=
  ⟨a.arity, [], [], ((holes d).map fun h ↦ condition o (goals h)).foldr
    (Logic.imp o) (condition o a)⟩

/-- Combine the checked lemmas by cuts, then discharge the initial hole conditions. -/
def assemble (o j : ℕ) (H : List Term) (a : Thm) (s : Ledger) : Option ConvDeriv := do
  let c ← hypothesis s.claims (condition o a)
  let c := s.proofs.foldr (fun (p, d) c ↦ RoseTree.node (.base (.cut p)) [d, c]) c
  pure (imply o j H (condition o a) c)

/-- Construct the closed lemmas and combine them into a conditional derivation. -/
def candidate {α : Type} (G : Globals) (E : Array Entry) (R : List ℕ) (o j : ℕ)
    (goals : α → Thm) (a : Thm) (d : Sketch α) : Option ConvDeriv := do
  let nodes ← (plan G E R d).2 a
  let H := (holes d).map fun h ↦ condition o (goals h)
  let s ← nodes.foldlM (fun s node ↦ ((synthesize G E R o j node).run s).map Prod.snd)
    ⟨H, []⟩
  assemble o j H a s

/-- Translate a checked sketch through closed conditional lemmas, rechecking the assembled
certificate in the original environment. -/
def certify {α : Type} (G : Globals) (E : Array Entry) (R : List ℕ) (o j : ℕ)
    (goals : α → Thm) (a : Thm) (d : Sketch α) : Option ConvDeriv := do
  if !checks G E R goals a d then none else do
    let c ← candidate G E R o j goals a d
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
    {M : PartialHorn.Model.{u} (ext defs).sig} (hM : PartialHorn.IsModel (ext defs) M)
    {G : Globals} (hG : G.WF)
    (hps : ∀ m ρ, ρ.map Sigma.fst = List.replicate m Sorts.obj → PrimsHom M ρ G m)
    (hds : ∀ m ρ, ρ.map Sigma.fst = List.replicate m Sorts.obj → DefsHom M ρ G m)
    (hδ : DefnsOk M G) {E : Array Entry}
    (hE : ∀ (j : ℕ) (e : Entry), E[j]? = some e → e.Valid M G) {R : List ℕ}
    (hR : ∀ j ∈ R, Literals.ready G E j = true)
    (hcert : ∀ cds, compileDefs G = some cds → G.base = sig.length → cds <+: defs)
    {o j : ℕ} {goals : α → Thm} {a : Thm} {d : Sketch α} {c : ConvDeriv}
    (h : certify G E R o j goals a d = some c) : (conditional o goals a d).Valid M G :=
  Thm.valid_of_convChecks hM hG hps hds hδ hcert hE hR (convChecks_of_certify h).2

end Geb.FreeTopos.Internal.ProofHoles.Closed

end
