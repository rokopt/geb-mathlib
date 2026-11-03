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
equations at the numerals' bits ({name}`Geb.FreeTopos.Literals.lemmas`). The checker does not test
that condition ({name}`Geb.FreeTopos.Literals.ready`) at the step: it is given the indices at which
the condition was tested, which a development tests once and records
({lit}`Geb.FreeTopos.Internal.ConvDecl`), since the condition reads neither the step's term nor
its context, and holds with more constants and entries
({name}`Geb.FreeTopos.Literals.ready_mono`). Its translation is the
rewriting by those equations, which reaches that numeral by a proof in Lean
({name}`Geb.FreeTopos.Literals.checked_of_eval`), so that it too is the base checker's rewriting by
a derivation the step does not construct.

A step of the machine rewrites a term to its normal form under constructors and abstractions by
the environment machine ({name}`Geb.FreeTopos.Internal.machineReduce`), which is not the prover's
reduction, rewriting at the roots of the normal form by the prover's rules the step names, the
theorems and hypotheses among them ({name}`Geb.FreeTopos.Internal.rootRewriteK`); the term
rewrites to it by a derivation the base checker accepts
({name}`Geb.FreeTopos.Internal.machineReduce_reaches`) where the term and the definitions' bodies
have their variables as leaves, as a term that compiles has, each rewriting at a root by its rule
({name}`Geb.FreeTopos.Internal.rootRewrite_checked`), so that it too is the base checker's
rewriting by a derivation the step does not construct.

## Main definitions

* {lit}`ConvRule`, {lit}`ConvDeriv` — the rules of the conversion checker's certificates, and
  its certificates.
* {lit}`applyInst` — the instance of a theorem whose conclusion matches a formula.
* {lit}`convCheck`, {lit}`Thm.convChecks` — the conversion checker, and the test that a
  certificate proves a theorem.
* {lit}`convCheckFast` — the conversion checker with its rewriting under hypotheses weakened where
  they are read.

## Main statements

* {lit}`convCheck_sound` — the conversion checker is sound.
* {lit}`Thm.valid_of_convChecks` — a theorem a certificate proves with valid earlier entries is
  valid.
* {lit}`convCheck_eq_convCheckFast` — the conversion checker is {lit}`convCheckFast`, by which the
  compiler replaces it.

## Implementation notes

The conversion checker's step at a rule of the language is the base checker's
({name}`Geb.FreeTopos.Internal.checkStep`), whose congruence under a binder weakens every
hypothesis past the bound variables. {lit}`convCheckFast` takes there the step of the base checker
as compiled ({name}`Geb.FreeTopos.Internal.checkFast`), which rewrites under the hypotheses as they
were stated with the number of the variables and weakens a hypothesis where a rewriting reads it;
a step of the prover's reductions weakens the hypotheses it is given, which the reduction may
rewrite by, and the other steps read none. The two are proved equal, and the attribute
{lit}`csimp` replaces the conversion checker by it in compiled code, so that the proof of
soundness is about the conversion checker as it is defined.

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
  theorems from the index {lit}`j` on, an index the checker is given as one at which they were
  found. -/
  | lit (j : ℕ)
  /-- The reduction of a term by the environment machine within the depth of recursion
  {lit}`fuel`, unfolding every definition of an index below {lit}`m` but those of
  {lit}`except`, a rose-tree fold's list of its children's values built by the primitives of
  indices {lit}`kl` and {lit}`kc`, its normal form rewritten at its roots by the prover's rules
  {lit}`rs`. -/
  | machine (fuel m : ℕ) (except : List ℕ) (kl kc : ℕ) (rs : List NormRule)

/-- A certificate of the conversion checker. -/
abbrev ConvDeriv : Type := RoseTree ConvRule

/-- The rule of the language's derivations a rule of the certificates stands for at a
congruence's choice of contexts: itself for a rule of the language, and one other than the
identity for a step of conversion and for an application of a theorem. -/
def ConvRule.toRule : ConvRule → Rule
  | .base r => r
  | .norm _ _ | .eval _ _ _ | .lit _ | .machine _ _ _ _ _ _ => .trans
  | .applyMatch j θ => .apply j θ []

/-- The instance of the theorem of index {lit}`j` among the entries, at the objects {lit}`θ`,
whose conclusion matches a formula, where every variable of the theorem's context is matched. -/
def applyInst (E : Array Entry) (j : ℕ) (θ : List Tree) (φ : Term) : Option (List Term) := do
  let a ← (E[j]?).bind Entry.language?
  let σ ← matchTerm (if θ.isEmpty then a.concl else Term.osubst θ a.concl) 0 φ
    (List.replicate a.ctx.length none)
  σ.mapM id

/-- The rewriting at a root of the machine's normal form by an index of the prover's rules under
the hypotheses {lit}`Φ`, prepared in {lit}`hs`, weakened past the binders the normal form has
passed where a rule reads them. -/
def machineRw (G : Globals) (E : Array Entry) (n : ℕ)
    (idx : List (ℕ × List NormRule) × List NormRule) (hs : PreparedHyps) (Φ : List Term)
    (Γ : List Tree) (k : ℕ) (t : Term) : Option Term :=
  (rootRewriteK G E n idx hs Γ k Φ t).map Prod.fst

/-- The rewriting at a root of the machine's normal form is sound. -/
theorem machineRw_reaches (G : Globals) (E : Array Entry) (n : ℕ) (rs : List NormRule)
    (Φ : List Term) {Γ : List Tree} {k : ℕ} {t u : Term}
    (h : machineRw G E n (indexRules E (prepareRules E rs)) (prepareHyps Φ) Φ Γ k t = some u) :
    Literals.Reaches G E n Γ (Φ.map (weakenBy k)) t u := by
  obtain ⟨⟨u', d⟩, hd, rfl⟩ := Option.map_eq_some_iff.mp h
  rw [rootRewriteK_eq] at hd
  exact ⟨(d, true), rootRewrite_checked hd⟩

/-- The reduction of a term in a context under hypotheses by the machine, which rewrites its normal
form by the prover's rules {lit}`rs`, prepared once for the reduction; where there is no rule, the
reduction reads no hypothesis. -/
def machineReduceBy (G : Globals) (E : Array Entry) (n : ℕ) (unfold : ℕ → Bool) (kl kc : ℕ)
    (rs : List NormRule) (fuel : ℕ) (Γ : List Tree) (Φ : List Term) (t : Term) : Option Term :=
  if rs.isEmpty then machineReduce G unfold kl kc (fun _ _ _ ↦ none) fuel Γ t
  else machineReduce G unfold kl kc
    (machineRw G E n (indexRules E (prepareRules E rs)) (prepareHyps Φ) Φ) fuel Γ t

/-- One step of the conversion checker, at a node of a rule from its children's results: the base
checker's step at a rule of the language, each child standing for a derivation of its rule; at a
step of conversion, the result of the reduction of the term under the named rules, which proves
no formula; and at an application of a theorem, the base checker's application at the instance
that matches the formula, which rewrites no term. -/
def convStep (G : Globals) (E : Array Entry) (R : List ℕ) (n : ℕ) (l : ConvRule)
    (cs : List (ConvDeriv × Checks)) : Checks := match l with
  | .base r => checkStep G E n r (cs.map fun (d, c) ↦ (RoseTree.node d.label.toRule [], c))
  | .norm rs fuel => (fun Γ Φ t ↦ (normalizeR G E n rs fuel Γ Φ t).map (·.1), fun _ _ _ ↦ false)
  | .eval rs fuel depth =>
    (fun Γ Φ t ↦ (evalR G E n rs fuel depth Γ Φ t).map (·.1), fun _ _ _ ↦ false)
  | .lit j => (fun _ _ t ↦ if R.contains j then (Literals.eval t).map Literals.Val.term else none,
      fun _ _ _ ↦ false)
  | .machine fuel m except kl kc rs =>
    (fun Γ Φ t ↦ machineReduceBy G E n (fun j ↦ decide (j < m) && !except.contains j) kl kc rs
      fuel Γ Φ t, fun _ _ _ ↦ false)
  | .applyMatch j θ => (fun _ _ _ ↦ none, fun Γ Φ φ ↦ match applyInst E j θ φ with
    | some σ => (checkStep G E n (.apply j θ σ)
        (cs.map fun (d, c) ↦ (RoseTree.node d.label.toRule [], c))).2 Γ Φ φ
    | none => false)

/-- The conversion checker, given the indices {lit}`R` at which the evaluation at literals is
ready: the rewriting a certificate performs on a term in a context under hypotheses, and whether
it proves a formula in a context under hypotheses. -/
def convCheck (G : Globals) (E : Array Entry) (R : List ℕ) (n : ℕ) : ConvDeriv → Checks :=
  RoseTree.para (convStep G E R n)

/-- The computation rule of the conversion checker. -/
theorem convCheck_node {G : Globals} {E : Array Entry} {R : List ℕ} {n : ℕ} (l : ConvRule)
    (cs : List ConvDeriv) :
    convCheck G E R n (RoseTree.node l cs) =
      convStep G E R n l (cs.map fun c ↦ (c, convCheck G E R n c)) :=
  RoseTree.para_node _ l cs

/-- The hypotheses a step other than a rule of the language reads, weakened past a number of new
innermost variables: those of a reduction by the prover's rules, which may rewrite by a
hypothesis, and none for the others. -/
def ConvRule.hyps (l : ConvRule) (k : ℕ) (Φ : List Term) : List Term := match l with
  | .norm _ _ | .eval _ _ _ => Φ.map (weakenBy k)
  | .machine _ _ _ _ _ rs => if rs.isEmpty then [] else Φ.map (weakenBy k)
  | _ => []

/-- One step of the conversion checker with its rewriting under weakened hypotheses
({name}`Geb.FreeTopos.Internal.fastStep`), at a node of a rule from its children's results: the
base checker's at a rule of the language, each child standing for its rule, and
{lit}`convStep`'s at any other, the hypotheses weakened where the step reads them. -/
def convFastStep (G : Globals) (E : Array Entry) (R : List ℕ) (n : ℕ) (l : ConvRule)
    (cs : List (ConvDeriv × FastChecks)) : FastChecks := match l with
  | .base r => fastStep G E n r (cs.map fun c ↦ (RoseTree.node c.1.label.toRule [], c.2))
  | l =>
    let c := convStep G E R n l (cs.map fun c ↦ (c.1, c.2.checks))
    (fun Γ k Φ t ↦ c.1 Γ (l.hyps k Φ) t, c.2)

/-- The conversion checker, its rewriting under hypotheses weakened where they are read: equal to
{lit}`convCheck`, which the compiler replaces by it. -/
def convCheckFast (G : Globals) (E : Array Entry) (R : List ℕ) (n : ℕ) (d : ConvDeriv) : Checks :=
  (RoseTree.para (convFastStep G E R n) d).checks

/-- The conversion checker with its rewriting under weakened hypotheses rewrites uniformly, and
its results are the conversion checker's. -/
theorem para_convFastStep (G : Globals) (E : Array Entry) (R : List ℕ) (n : ℕ) : ∀ d : ConvDeriv,
    (RoseTree.para (convFastStep G E R n) d).1.Uniform ∧
      (RoseTree.para (convFastStep G E R n) d).checks = convCheck G E R n d :=
  RoseTree.ind fun l ds ih ↦ by
    rw [RoseTree.para_node, convCheck_node]
    have hcs : (ds.map fun d ↦ (d, RoseTree.para (convFastStep G E R n) d)).map
        (fun c ↦ (c.1, c.2.checks)) = ds.map fun d ↦ (d, convCheck G E R n d) := by
      rw [List.map_map]
      exact List.map_congr_left fun d hd ↦ by rw [Function.comp_apply, (ih d hd).2]
    rcases l with r | ⟨rs, fuel⟩ | ⟨rs, fuel, depth⟩ | ⟨j, θ⟩ | j | ⟨fuel, m, except, kl, kc, rs⟩
    · obtain ⟨hu, hc⟩ := fastStep_eq G E n r
        (ds.map fun d ↦ (RoseTree.node d.label.toRule [], RoseTree.para (convFastStep G E R n) d))
        fun c hc ↦ by
          obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
          exact (ih d hd).1
      simp only [convFastStep, convStep, List.map_map, Function.comp_def]
      refine ⟨hu, hc.trans (congrArg _ ?_)⟩
      rw [List.map_map]
      exact List.map_congr_left fun d hd ↦ by rw [Function.comp_apply, (ih d hd).2]
    all_goals
      refine ⟨fun Γ k Φ t ↦ ?_, ?_⟩
      · simp only [convFastStep, ConvRule.hyps, map_weakenBy_zero]
      · simp only [convFastStep]
        rw [hcs]
        simp only [FastChecks.checks, ConvRule.hyps, map_weakenBy_zero]
        -- the remaining steps' rewritings read no hypothesis, nor the machine's without rules
        all_goals first
          | rfl
          | refine Prod.ext (funext fun Γ ↦ funext fun Φ ↦ funext fun t ↦ ?_) rfl
            split
            · simp only [convStep, machineReduceBy, *, ite_true]
            · rfl

/-- The conversion checker is the conversion checker with its rewriting under hypotheses weakened
where they are read, by which the compiler replaces it. -/
@[csimp] theorem convCheck_eq_convCheckFast : @convCheck = @convCheckFast := by
  funext G E R n d
  exact (para_convFastStep G E R n d).2.symm

/-- Whether a certificate proves a theorem: its context's types are types, its hypotheses and
conclusion formulas, and the conversion checker, given the indices {lit}`R` at which the
evaluation at literals is ready, proves the conclusion from the hypotheses. -/
def Thm.convChecks (G : Globals) (E : Array Entry) (R : List ℕ) (a : Thm) (d : ConvDeriv) : Bool :=
  a.wellFormed G && (convCheck G E R a.arity d).2 a.ctx a.hyps a.concl

/-- A certificate whose rule is the identity rule's rewrites a term only to itself. -/
theorem convCheck_isRefl {G : Globals} {E : Array Entry} {R : List ℕ} {n : ℕ} {c : ConvDeriv}
    (hc : c.label.toRule.isRefl = true)
    {Γ : List Tree} {Φ : List Term} {t t' : Term} (h : (convCheck G E R n c).1 Γ Φ t = some t') :
    t' = t := by
  obtain ⟨l, cs, rfl⟩ : ∃ l cs, c = RoseTree.node l cs :=
    ⟨_, _, (RoseTree.node_label_children c).symm⟩
  rcases l with r | ⟨rs, fuel⟩ | ⟨rs, fuel, depth⟩ | ⟨j, θ⟩ | j | ⟨fuel, m, except, kl, kc, rs⟩
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
checked, and the evaluation at literals is ready at the indices recorded. -/
theorem convCheck_sound (hδ : DefnsOk M G) {E : Array Entry}
    (hE : ∀ (j : ℕ) (e : Entry), E[j]? = some e → e.Valid M G) {R : List ℕ}
    (hR : ∀ j ∈ R, Literals.ready G E j = true)
    (hcert : ∀ cds, compileDefs G = some cds → G.base = sig.length → cds <+: defs) :
    ∀ d : ConvDeriv, ChecksSound M ρ G n (convCheck G E R n d) :=
  RoseTree.ind fun l cs ih ↦ by
    rw [convCheck_node]
    -- the base checker's step is sound at children standing for their certificates' rules
    have hstep (r : Rule) : ChecksSound M ρ G n (checkStep G E n r
        ((cs.map fun c ↦ (c, convCheck G E R n c)).map fun (d, c) ↦
          (RoseTree.node d.label.toRule [], c))) := by
      refine checkStep_sound hM hG hρ hps hds hδ hE hcert r _ (fun x hx ↦ ?_) fun x hx ↦ ?_
      all_goals
        obtain ⟨⟨d, dc⟩, hd, rfl⟩ := List.mem_map.mp hx
        obtain ⟨c, hc, h⟩ := List.mem_map.mp hd
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      · exact ih c hc
      · exact fun hr _ _ _ _ h ↦ convCheck_isRefl hr h
    rcases l with r | ⟨rs, fuel⟩ | ⟨rs, fuel, depth⟩ | ⟨j, θ⟩ | j | ⟨fuel, m, except, kl, kc, rs⟩
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
        obtain ⟨d, hd⟩ := Literals.checked_of_eval (Φ := Φ) hG
          (hR j (List.contains_iff_mem.mp (by assumption))) hv
        exact (check_sound hM hG hρ hps hds hδ hE hcert d.1).1 _ _ _ _ hd.check
      · cases h
    · refine ⟨fun Γ Φ t t' h X e he hΓ hH r hr ↦ ?_, fun _ _ _ h ↦ nomatch h⟩
      simp only [convStep] at h
      have hdefs : ∀ (j : ℕ) (d : Defn), G.defs[j]? = some (.language d) →
          Term.VarLeaves d.body = true := fun j d hd ↦
        let ⟨_, hF, _⟩ := hδ j d hd
        Term.varLeaves_of_compile _ _ _ _ hF
      have hleaves := Term.varLeaves_of_compile t X e r hr
      obtain ⟨d, hd⟩ : Literals.Reaches G E n Γ Φ t t' := by
        simp only [machineReduceBy] at h
        split at h
        · exact machineReduce_reaches _ _ _ (fun _ _ _ _ h ↦ by cases h) hdefs hleaves h
        · exact machineReduce_reaches _ _ _ (fun _ _ _ _ h ↦ machineRw_reaches G E n _ Φ h) hdefs
            hleaves h
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
valid, where the evaluation at literals is ready at the indices recorded. -/
theorem Thm.valid_of_convChecks {E : Array Entry}
    (hE : ∀ (j : ℕ) (e : Entry), E[j]? = some e → e.Valid M G) {R : List ℕ}
    (hR : ∀ j ∈ R, Literals.ready G E j = true) {a : Thm} {d : ConvDeriv}
    (h : a.convChecks G E R d = true) : a.Valid M G := by
  simp only [Thm.convChecks, Bool.and_eq_true] at h
  obtain ⟨hwf, hd⟩ := h
  obtain ⟨hctx, hhyps, hconcl⟩ := Thm.wellFormed_iff.mp hwf
  exact ⟨hctx, hhyps, hconcl,
    fun ρ hρ ↦ ⟨hps _ ρ hρ, hds _ ρ hρ,
      (convCheck_sound hM hG hρ (hps _ ρ hρ) (hds _ ρ hρ) hδ hE hR hcert d).2 _ _ _ hd⟩⟩

end Theorems

end Geb.FreeTopos.Internal

end
