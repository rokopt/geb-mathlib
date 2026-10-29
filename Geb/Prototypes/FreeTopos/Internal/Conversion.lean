/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Proofs
public import Geb.Prototypes.FreeTopos.Internal.ProveChecked
public import Geb.Prototypes.FreeTopos.Internal.MachineSound
public import Geb.Prototypes.FreeTopos.Internal.Reduce
public import Geb.Prototypes.FreeTopos.Literals
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The checker with a step of conversion

A checker of the internal language beside {name}`Geb.FreeTopos.Internal.check`, whose
certificates add to the language's rules a step of conversion and an application of a theorem
whose instance the checker finds. A step of conversion is the rewriting of a term by one of the
prover's reductions under named rules ({name}`Geb.FreeTopos.Internal.NormRule`): the innermost
normalization ({name}`Geb.FreeTopos.Internal.normalize`), or the reduction to a depth, weak head
normal forms first ({name}`Geb.FreeTopos.Internal.eval`). The base checker does not compute that
rewriting; it checks each step of it in a derivation. The conversion checker computes its result
alone, by the reductions that build no derivation ({name}`Geb.FreeTopos.Internal.normalizeR`,
{name}`Geb.FreeTopos.Internal.evalR`), each the projection of the prover's
({name}`Geb.FreeTopos.Internal.normalizeR_eq`, {name}`Geb.FreeTopos.Internal.evalR_eq`): the
derivation the prover's reduction computes rewrites the term to that result, which the base
checker accepts at every input ({name}`Geb.FreeTopos.Internal.normalize_checked`,
{name}`Geb.FreeTopos.Internal.eval_checked`), so the step is the base checker's rewriting by that
derivation, which is neither built nor checked. The application of a theorem names the theorem and
its objects, and its instance is the matching of its conclusion against the formula proved, as
the prover matches a theorem's left side ({name}`Geb.FreeTopos.Internal.matchTerm`); the step is
then the base checker's application at that instance. At every other node the conversion
checker takes the base checker's step. Its soundness is therefore relative to the base checker's,
a stronger checker admitted beside a weaker one by the translation of its certificates
({cite}`Davis2009`): each step of conversion by the soundness of the base checker
({name}`Geb.FreeTopos.Internal.check_sound`) at the reduction's derivation, and each other node by
the soundness of the base checker's step ({name}`Geb.FreeTopos.Internal.checkStep_sound`). A step
of conversion carries the bound on the depth of its reduction.

A step of evaluation rewrites a term built of the library's arithmetic over numerals to the
numeral of its value, computed by the arithmetic of the natural numbers
({name}`Geb.FreeTopos.Literals.eval`), where the theorems from an index on are the definitions'
equations at the numerals' bits ({name}`Geb.FreeTopos.Literals.lemmas`). Its translation is the
rewriting by those equations, which reaches that numeral by a proof in Lean
({name}`Geb.FreeTopos.Literals.checked_of_eval`), so that it too is the base checker's rewriting by
a derivation the step does not construct.

A step of the machine rewrites a term to its normal form under constructors by the environment
machine ({name}`Geb.FreeTopos.Internal.machineReduce`), which is not the prover's reduction; the
term rewrites to it by a derivation the base checker accepts
({name}`Geb.FreeTopos.Internal.machineReduce_reaches`) where the term and the definitions' bodies
have their variables as leaves, as a term that compiles has, so that it too is the base checker's
rewriting by a derivation the step does not construct.

## Main definitions

* {lit}`ConvRule`, {lit}`ConvDeriv` — the rules of the conversion checker's certificates, and
  its certificates.
* {lit}`applyInst` — the instance of a theorem whose conclusion matches a formula.
* {lit}`convCheck`, {lit}`Thm.convChecks` — the conversion checker, and the test that a
  certificate proves a theorem.

## Main statements

* {lit}`convCheck_sound` — the conversion checker is sound.
* {lit}`Thm.valid_of_convChecks` — a theorem a certificate proves with valid earlier entries is
  valid.

## References

* {cite}`Davis2009`, Chapter 1, for checkers admitted by relative soundness.

## Tags

internal language, proof checker, conversion, normalization, relative soundness
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal

open PartialHorn (Tree)
open Sorts

universe v

/-- A rule of the conversion checker's certificates. -/
inductive ConvRule where
  /-- A rule of the language's derivations. -/
  | base (r : Rule)
  /-- The rewriting of a term to its normal form under the rules {lit}`rs`, by the prover's
  normalization within the depth {lit}`fuel`. -/
  | norm (rs : List NormRule) (fuel : ℕ)
  /-- The reduction of a term to the depth {lit}`depth` under the rules {lit}`rs`, by the
  prover's reduction within the depth of recursion {lit}`fuel`. -/
  | eval (rs : List NormRule) (fuel : ℕ) (depth : Depth)
  /-- The theorem of index {lit}`j` at the objects {lit}`θ`, at the instance that matches its
  conclusion against the formula, its hypotheses' instances proved. -/
  | applyMatch (j : ℕ) (θ : List Tree)
  /-- The evaluation of a term built of the library's arithmetic over numerals, by the arithmetic
  of the natural numbers, admitted by the definitions' equations at the numerals' bits among the
  theorems from the index {lit}`j` on. -/
  | lit (j : ℕ)
  /-- The reduction of a term by the environment machine within the depth of recursion
  {lit}`fuel`, unfolding every definition of an index below {lit}`m` but those of
  {lit}`except`, a rose-tree fold's list of its children's values built by the primitives of
  indices {lit}`kl` and {lit}`kc`. -/
  | machine (fuel m : ℕ) (except : List ℕ) (kl kc : ℕ)

/-- A certificate of the conversion checker. -/
abbrev ConvDeriv : Type := RoseTree ConvRule

/-- The rule of the language's derivations a rule of the certificates stands for at a
congruence's choice of contexts: itself for a rule of the language, and one other than the
identity for a step of conversion and for an application of a theorem. -/
def ConvRule.toRule : ConvRule → Rule
  | .base r => r
  | .norm _ _ | .eval _ _ _ | .lit _ | .machine _ _ _ _ _ => .trans
  | .applyMatch j θ => .apply j θ []

/-- The instance of the theorem of index {lit}`j` among the entries, at the objects {lit}`θ`,
whose conclusion matches a formula, where every variable of the theorem's context is matched. -/
def applyInst (E : Array Entry) (j : ℕ) (θ : List Tree) (φ : Term) : Option (List Term) := do
  let a ← (E[j]?).bind Entry.language?
  let σ ← matchTerm (if θ.isEmpty then a.concl else Term.osubst θ a.concl) 0 φ
    (List.replicate a.ctx.length none)
  σ.mapM id

/-- One step of the conversion checker, at a node of a rule from its children's results: the base
checker's step at a rule of the language, each child standing for a derivation of its rule; at a
step of conversion, the result of the reduction of the term under the named rules, which proves
no formula; and at an application of a theorem, the base checker's application at the instance
that matches the formula, which rewrites no term. -/
def convStep (G : Globals) (E : Array Entry) (n : ℕ) (l : ConvRule)
    (cs : List (ConvDeriv × Checks)) : Checks := match l with
  | .base r => checkStep G E n r (cs.map fun (d, c) ↦ (RoseTree.node d.label.toRule [], c))
  | .norm rs fuel => (fun Γ Φ t ↦ (normalizeR G E n rs fuel Γ Φ t).map (·.1), fun _ _ _ ↦ false)
  | .eval rs fuel depth =>
    (fun Γ Φ t ↦ (evalR G E n rs fuel depth Γ Φ t).map (·.1), fun _ _ _ ↦ false)
  | .lit j => (fun Γ _ t ↦ if Literals.ready G E n Γ j then (Literals.eval t).map Literals.Val.term
      else none, fun _ _ _ ↦ false)
  | .machine fuel m except kl kc =>
    (fun _ _ t ↦ machineReduce G (fun j ↦ decide (j < m) && !except.contains j) kl kc fuel t,
      fun _ _ _ ↦ false)
  | .applyMatch j θ => (fun _ _ _ ↦ none, fun Γ Φ φ ↦ match applyInst E j θ φ with
    | some σ => (checkStep G E n (.apply j θ σ)
        (cs.map fun (d, c) ↦ (RoseTree.node d.label.toRule [], c))).2 Γ Φ φ
    | none => false)

/-- The conversion checker: the rewriting a certificate performs on a term in a context under
hypotheses, and whether it proves a formula in a context under hypotheses. -/
def convCheck (G : Globals) (E : Array Entry) (n : ℕ) : ConvDeriv → Checks :=
  RoseTree.para (convStep G E n)

/-- The computation rule of the conversion checker. -/
theorem convCheck_node {G : Globals} {E : Array Entry} {n : ℕ} (l : ConvRule)
    (cs : List ConvDeriv) :
    convCheck G E n (RoseTree.node l cs) =
      convStep G E n l (cs.map fun c ↦ (c, convCheck G E n c)) :=
  RoseTree.para_node _ l cs

/-- Whether a certificate proves a theorem: its context's types are types, its hypotheses and
conclusion formulas, and the conversion checker proves the conclusion from the hypotheses. -/
def Thm.convChecks (G : Globals) (E : Array Entry) (a : Thm) (d : ConvDeriv) : Bool :=
  a.wellFormed G && (convCheck G E a.arity d).2 a.ctx a.hyps a.concl

/-- A certificate whose rule is the identity rule's rewrites a term only to itself. -/
theorem convCheck_isRefl {G : Globals} {E : Array Entry} {n : ℕ} {c : ConvDeriv}
    (hc : c.label.toRule.isRefl = true)
    {Γ : List Tree} {Φ : List Term} {t t' : Term} (h : (convCheck G E n c).1 Γ Φ t = some t') :
    t' = t := by
  obtain ⟨l, cs, rfl⟩ : ∃ l cs, c = RoseTree.node l cs :=
    ⟨_, _, (RoseTree.node_label_children c).symm⟩
  rcases l with r | ⟨rs, fuel⟩ | ⟨rs, fuel, depth⟩ | ⟨j, θ⟩ | j | ⟨fuel, m, except, kl, kc⟩
  · cases r <;> simp only [RoseTree.label_node, ConvRule.toRule, Rule.isRefl, reduceCtorEq] at hc
    rw [convCheck_node] at h
    rcases cs with _ | ⟨c', cs⟩
    · exact (Option.some_inj.mp h).symm
    · simp [convStep, checkStep] at h
  all_goals simp [RoseTree.label_node, ConvRule.toRule, Rule.isRefl] at hc

section Soundness

variable {defs : List PartialHorn.Defn} {M : PartialHorn.Model.{v} (ext defs).sig}
  (hM : PartialHorn.IsModel (ext defs) M) {G : Globals} (hG : G.WF) {ρ : List M.Val} {n : ℕ}
  (hρ : ρ.map Sigma.fst = List.replicate n obj) (hps : PrimsHom M ρ G n) (hds : DefsHom M ρ G n)
include hM hG hρ hps hds

/-- The conversion checker is sound: every rewriting a certificate performs is sound, and every
formula it proves holds, with sound unfoldings and valid earlier entries, when the model's
definitions are the compilations of the definitions of {name}`G` wherever a certificate is
checked. -/
theorem convCheck_sound (hδ : DefnsOk M G) {E : Array Entry}
    (hE : ∀ (j : ℕ) (e : Entry), E[j]? = some e → e.Valid M G)
    (hcert : ∀ cds, compileDefs G = some cds → G.base = sig.length → cds <+: defs) :
    ∀ d : ConvDeriv, ChecksSound M ρ G n (convCheck G E n d) :=
  RoseTree.ind fun l cs ih ↦ by
    rw [convCheck_node]
    -- the base checker's step is sound at children standing for their certificates' rules
    have hstep (r : Rule) : ChecksSound M ρ G n (checkStep G E n r
        ((cs.map fun c ↦ (c, convCheck G E n c)).map fun (d, c) ↦
          (RoseTree.node d.label.toRule [], c))) := by
      refine checkStep_sound hM hG hρ hps hds hδ hE hcert r _ (fun x hx ↦ ?_) fun x hx ↦ ?_
      all_goals
        obtain ⟨⟨d, dc⟩, hd, rfl⟩ := List.mem_map.mp hx
        obtain ⟨c, hc, h⟩ := List.mem_map.mp hd
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      · exact ih c hc
      · exact fun hr _ _ _ _ h ↦ convCheck_isRefl hr h
    rcases l with r | ⟨rs, fuel⟩ | ⟨rs, fuel, depth⟩ | ⟨j, θ⟩ | j | ⟨fuel, m, except, kl, kc⟩
    · exact hstep r
    · refine ⟨fun Γ Φ t t' h ↦ ?_, fun _ _ _ h ↦ nomatch h⟩
      simp only [convStep, normalizeR_eq, Option.map_map] at h
      obtain ⟨⟨_, d, _⟩, hn, rfl⟩ := Option.map_eq_some_iff.mp h
      exact (check_sound hM hG hρ hps hds hδ hE hcert d).1 _ _ _ _
        (normalize_checked rs fuel _ _ _ _ hn).check
    · refine ⟨fun Γ Φ t t' h ↦ ?_, fun _ _ _ h ↦ nomatch h⟩
      simp only [convStep, evalR_eq, Reduction.result, Option.map_map] at h
      obtain ⟨⟨_, d, _⟩, hn, rfl⟩ := Option.map_eq_some_iff.mp h
      exact (check_sound hM hG hρ hps hds hδ hE hcert d).1 _ _ _ _
        (eval_checked rs fuel depth _ _ _ _ hn).check
    · refine ⟨fun _ _ _ _ h ↦ (nomatch h), fun Γ Φ φ h ↦ ?_⟩
      simp only [convStep] at h
      split at h
      · exact (hstep (.apply j θ _)).2 Γ Φ φ h
      · cases h
    · refine ⟨fun Γ Φ t t' h ↦ ?_, fun _ _ _ h ↦ nomatch h⟩
      simp only [convStep] at h
      split at h
      · obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨d, hd⟩ := Literals.checked_of_eval (Φ := Φ) (by assumption) hv
        exact (check_sound hM hG hρ hps hds hδ hE hcert d.1).1 _ _ _ _ hd.check
      · cases h
    · refine ⟨fun Γ Φ t t' h X e he hΓ hH r hr ↦ ?_, fun _ _ _ h ↦ nomatch h⟩
      simp only [convStep] at h
      have hdefs : ∀ (j : ℕ) (d : Defn), G.defs[j]? = some (.language d) →
          Term.VarLeaves d.body = true := fun j d hd ↦
        let ⟨_, hF, _⟩ := hδ j d hd
        Term.varLeaves_of_compile _ _ _ _ hF
      obtain ⟨d, hd⟩ := machineReduce_reaches (E := E) (n := n) (Γ := Γ) (Φ := Φ) _ _ _ hdefs
        (Term.varLeaves_of_compile t X e r hr) h
      exact (check_sound hM hG hρ hps hds hδ hE hcert d.1).1 _ _ _ _ hd.check X e he hΓ hH r hr

end Soundness

section Theorems

variable {defs : List PartialHorn.Defn} {M : PartialHorn.Model.{v} (ext defs).sig}
  (hM : PartialHorn.IsModel (ext defs) M) {G : Globals} (hG : G.WF)
  (hps : ∀ (m : ℕ) (ρ : List M.Val), ρ.map Sigma.fst = List.replicate m obj → PrimsHom M ρ G m)
  (hds : ∀ (m : ℕ) (ρ : List M.Val), ρ.map Sigma.fst = List.replicate m obj → DefsHom M ρ G m)
  (hδ : DefnsOk M G)
  (hcert : ∀ cds, compileDefs G = some cds → G.base = sig.length → cds <+: defs)
include hM hG hps hds hδ hcert

/-- A theorem a certificate of the conversion checker proves with valid earlier entries is
valid. -/
theorem Thm.valid_of_convChecks {E : Array Entry}
    (hE : ∀ (j : ℕ) (e : Entry), E[j]? = some e → e.Valid M G) {a : Thm} {d : ConvDeriv}
    (h : a.convChecks G E d = true) : a.Valid M G := by
  simp only [Thm.convChecks, Bool.and_eq_true] at h
  obtain ⟨hwf, hd⟩ := h
  obtain ⟨hctx, hhyps, hconcl⟩ := Thm.wellFormed_iff.mp hwf
  exact ⟨hctx, hhyps, hconcl,
    fun ρ hρ ↦ ⟨hps _ ρ hρ, hds _ ρ hρ,
      (convCheck_sound hM hG hρ (hps _ ρ hρ) (hds _ ρ hρ) hδ hE hcert d).2 _ _ _ hd⟩⟩

end Theorems

end Geb.FreeTopos.Internal

end
