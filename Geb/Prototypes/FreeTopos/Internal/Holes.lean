/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Cslib.Foundations.Data.PFunctor.Free
public import Geb.Prototypes.FreeTopos.Internal.Conversion

set_option doc.verso true in
/-!
# Proof sketches over the conversion checker

A proof sketch is the free monad on the conversion rules with their finite lists of premises.
Its variables are holes, whose declarations give their full sequents. Substitution grafts
sketches into holes, including sketches with further holes, using the existing free monad.

## Main definitions

* {lit}`ProofHoles.signature`, {lit}`ProofHoles.Sketch` — rules with premises and holes.
* {lit}`ProofHoles.node` — a rule applied to a list of sketches.
* {lit}`ProofHoles.check` — check a sketch and report its outstanding sequents.
* {lit}`ProofHoles.fill` — check fillings, possibly open, and graft them into a sketch.
* {lit}`ProofHoles.finish` — return a conversion certificate for a completed proof.

## Main statements

* {lit}`ProofHoles.valid_of_checks` — validity conditional on the remaining sequents.
* {lit}`ProofHoles.convChecks_of_finish` — completed proofs check without hole assumptions.
* {lit}`ProofHoles.finish_ofDeriv` — accepted conversion certificates finish as themselves.
* {lit}`ProofHoles.holes_bind` — substitution replaces each hole by its filling's holes.

## Implementation notes

Hole identities have one declaration each, supplied by a function. A hole checks only in that
exact sequent; changing its context requires an explicit proof. Holes suspend formula proofs,
not rewritings. The checker records each occurrence, so repeated identities share a declaration
but retain their positions in premise order. No equality test on identities is required.

Filling is {name}`PFunctor.FreeM.bind`, with the free monad's identity and associativity laws.
The checked interface checks each filling in its declared sequent and rechecks the grafted
sketch. Open checking proves a conditional validity theorem in Lean; it does not emit a
conversion certificate for an implication encoding the obligations. Finishing requires no
remaining holes and returns a certificate of the original theorem.

## Tags

internal language, proof checker, hole, substitution, free monad
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal.ProofHoles

open PartialHorn (Tree)
open Sorts
open scoped FinEnum

universe v

/-- The polynomial of conversion rules with a finite list of premises. -/
def signature : PFunctor := ⟨ConvRule × ℕ, RoseTree.Sig ConvRule⟩

/-- A conversion derivation with holes labelled by {lit}`α`. -/
abbrev Sketch (α : Type) : Type := signature.FreeM α

/-- A conversion rule applied to the given premises. -/
def node {α : Type} (r : ConvRule) (ds : List (Sketch α)) : Sketch α :=
  .liftBind (r, ds.length) fun i ↦ ds[i.1]

/-- A hole proves only its declared sequent, when that sequent is well formed. It performs no
rewriting, including rewriting under a binder. -/
def holeChecks (G : Globals) (n : ℕ) (a : Thm) : Checks :=
  (fun _ _ _ ↦ none, fun Γ Φ φ ↦ a.wellFormed G &&
    decide (a.arity = n ∧ a.ctx = Γ ∧ a.hyps = Φ ∧ a.concl = φ))

/-- The algebra of the checker, keeping each child's root rule for the conversion checker's
test of identity rewritings under binders. -/
def step (G : Globals) (E : Array Entry) (R : List ℕ) (n : ℕ) :
    signature.Obj (ConvRule × Checks) → ConvRule × Checks :=
  fun ⟨(r, _), cs⟩ ↦ (r, convStep G E R n r
    (List.ofFn fun i ↦ (RoseTree.node (cs i).1 [], (cs i).2)))

/-- Interpret a sketch by the conversion checker, suspending proof leaves at their declared
sequents. A hole is marked by a nonidentity rule, since it is never an identity rewriting. -/
def run {α : Type} (G : Globals) (E : Array Entry) (R : List ℕ) (n : ℕ)
    (goals : α → Thm) : Sketch α → ConvRule × Checks :=
  PFunctor.FreeM.rec (fun h ↦ (.base .join, holeChecks G n (goals h)))
    (fun r _ cs ↦ step G E R n ⟨r, cs⟩)

/-- The holes of a sketch in premise order, retaining repeated occurrences of the same hole. -/
def holes {α : Type} : Sketch α → List α :=
  PFunctor.FreeM.rec List.singleton (fun _ _ cs ↦ (List.ofFn cs).flatten)

/-- The conversion rule marked as an identity is exactly the base identity rule. -/
theorem isRefl_iff (r : ConvRule) : r.toRule.isRefl = true ↔ r = .base .refl := by
  cases r
  case base r => cases r <;> simp [ConvRule.toRule, Rule.isRefl]
  all_goals simp [ConvRule.toRule, Rule.isRefl]

/-- A sketch marked as an identity rewriting rewrites only to its input. -/
theorem run_isRefl {α : Type} {G : Globals} {E : Array Entry} {R : List ℕ} {n : ℕ}
    {goals : α → Thm} {d : Sketch α}
    (hr : (run G E R n goals d).1.toRule.isRefl = true)
    {Γ : List PartialHorn.Tree} {Φ : List Term} {t t' : Term}
    (h : (run G E R n goals d).2.1 Γ Φ t = some t') : t' = t := by
  cases d with
  | pure a => cases hr
  | liftBind r cs =>
    have hr' : r.1 = .base .refl := (isRefl_iff r.1).mp hr
    rcases r with ⟨r, k⟩
    cases hr'
    cases k with
    | zero => exact (Option.some.inj h).symm
    | succ k =>
      change (convStep G E R n (.base .refl) (List.ofFn fun i ↦
        (RoseTree.node (run G E R n goals (cs i)).1 [],
          (run G E R n goals (cs i)).2))).1 Γ Φ t = some t' at h
      simp [List.ofFn_succ, convStep, checkStep] at h

/-- Suspending a hole is sound conditional on the validity of its declared sequent. -/
theorem holeChecks_sound {defs : List PartialHorn.Defn}
    {M : PartialHorn.Model.{v} (ext defs).sig} {ρ : List M.Val} {G : Globals} {n : ℕ}
    (hρ : ρ.map Sigma.fst = List.replicate n obj) {a : Thm} (ha : a.Valid M G) :
    ChecksSound M ρ G n (holeChecks G n a) := by
  refine ⟨fun _ _ _ _ h ↦ (nomatch h), fun Γ Φ φ h ↦ ?_⟩
  simp only [holeChecks, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨_, rfl, rfl, rfl, rfl⟩ := h
  exact (ha.2.2.2 ρ hρ).2.2

/-- A sketch's checks are sound conditional on the sequents of its remaining holes. The
conditions quantify over the holes' own contexts, including hypotheses introduced by rules. -/
theorem run_sound {α : Type} {defs : List PartialHorn.Defn}
    {M : PartialHorn.Model.{v} (ext defs).sig} (hM : PartialHorn.IsModel (ext defs) M)
    {G : Globals} (hG : G.WF) {ρ : List M.Val} {n : ℕ}
    (hρ : ρ.map Sigma.fst = List.replicate n obj) (hps : PrimsHom M ρ G n)
    (hds : DefsHom M ρ G n) (hδ : DefnsOk M G) {E : Array Entry}
    (hE : ∀ (j : ℕ) (e : Entry), E[j]? = some e → e.Valid M G) {R : List ℕ}
    (hR : ∀ j ∈ R, Literals.ready G E j = true)
    (hcert : ∀ cds, compileDefs G = some cds → G.base = sig.length → cds <+: defs)
    {goals : α → Thm} (d : Sketch α) (hh : ∀ h ∈ holes d, (goals h).Valid M G) :
    ChecksSound M ρ G n (run G E R n goals d).2 := by
  refine PFunctor.FreeM.rec
    (motive := fun d : Sketch α ↦ (∀ h ∈ holes d, (goals h).Valid M G) →
      ChecksSound M ρ G n (run G E R n goals d).2) ?_ ?_ d hh
  · exact fun h hv ↦ holeChecks_sound hρ (hv h List.mem_cons_self)
  · intro r cs ih hv
    change ChecksSound M ρ G n (convStep G E R n r.1 (List.ofFn fun i ↦
      (RoseTree.node (run G E R n goals (cs i)).1 [], (run G E R n goals (cs i)).2)))
    refine convStep_sound hM hG hρ hps hds hδ hE hR hcert _ _
      (fun c hc ↦ ?_) fun c hc ↦ ?_
    all_goals obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    · refine ih i fun h hh ↦ hv h ?_
      change h ∈ (List.ofFn fun i ↦ holes (cs i)).flatten
      exact List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, hh⟩
    · exact fun hr _ _ _ _ h ↦ run_isRefl hr h

/-- Check an open sketch against its conclusion. Success leaves the declared holes as
obligations; it does not admit the conclusion as a theorem. All declarations are checked,
including holes in premises that a rule does not inspect. -/
def checks {α : Type} (G : Globals) (E : Array Entry) (R : List ℕ) (goals : α → Thm)
    (a : Thm) (d : Sketch α) : Bool :=
  a.wellFormed G && (holes d).all (fun h ↦ (goals h).wellFormed G) &&
    (run G E R a.arity goals d).2.2 a.ctx a.hyps a.concl

/-- An accepted sketch is valid conditional on its remaining obligations. Each obligation is
a sequent in its own context, not an extra formula in the conclusion's context. -/
theorem valid_of_checks {α : Type} {defs : List PartialHorn.Defn}
    {M : PartialHorn.Model.{v} (ext defs).sig} (hM : PartialHorn.IsModel (ext defs) M)
    {G : Globals} (hG : G.WF)
    (hps : ∀ m ρ, ρ.map Sigma.fst = List.replicate m obj → PrimsHom M ρ G m)
    (hds : ∀ m ρ, ρ.map Sigma.fst = List.replicate m obj → DefsHom M ρ G m)
    (hδ : DefnsOk M G) {E : Array Entry}
    (hE : ∀ (j : ℕ) (e : Entry), E[j]? = some e → e.Valid M G) {R : List ℕ}
    (hR : ∀ j ∈ R, Literals.ready G E j = true)
    (hcert : ∀ cds, compileDefs G = some cds → G.base = sig.length → cds <+: defs)
    {goals : α → Thm} {a : Thm} {d : Sketch α} (h : checks G E R goals a d = true)
    (hh : ∀ h ∈ holes d, (goals h).Valid M G) : a.Valid M G := by
  simp only [checks, Bool.and_eq_true] at h
  obtain ⟨⟨hwf, _⟩, hd⟩ := h
  obtain ⟨hctx, hhyps, hconcl⟩ := Thm.wellFormed_iff.mp hwf
  exact ⟨hctx, hhyps, hconcl, fun ρ hρ ↦ ⟨hps _ ρ hρ, hds _ ρ hρ,
    (run_sound hM hG hρ (hps _ ρ hρ) (hds _ ρ hρ) hδ hE hR hcert d hh).2 _ _ _ hd⟩⟩

/-- Return the outstanding obligations of an accepted sketch, in occurrence order. Repeated
identities share their declaration; callers may group them for display. -/
def check {α : Type} (G : Globals) (E : Array Entry) (R : List ℕ) (goals : α → Thm)
    (a : Thm) (d : Sketch α) : Option (List (α × Thm)) :=
  if checks G E R goals a d then some ((holes d).map fun h ↦ (h, goals h)) else none

/-- Interpret the rule tree as a conversion derivation, supplying a derivation at each hole.
This operation alone does not check the supplied derivations. -/
def toDeriv {α : Type} (fill : α → ConvDeriv) : Sketch α → ConvDeriv :=
  PFunctor.FreeM.rec fill (fun r _ cs ↦ RoseTree.node r.1 (List.ofFn cs))

/-- The conversion step depends on each child's root rule and checks, not on its descendants. -/
theorem convStep_roots (G : Globals) (E : Array Entry) (R : List ℕ) (n : ℕ)
    (r : ConvRule) (cs : List (ConvDeriv × Checks)) :
    convStep G E R n r (cs.map fun c ↦ (RoseTree.node c.1.label [], c.2)) =
      convStep G E R n r cs := by
  cases r <;> simp only [convStep, List.map_map, Function.comp_def, RoseTree.label_node]

/-- A sketch with no holes has exactly the conversion checker's checks. The filling is
irrelevant, since there is no hole to interpret. -/
theorem run_eq_convCheck {α : Type} (G : Globals) (E : Array Entry) (R : List ℕ) (n : ℕ)
    (goals : α → Thm) (fill : α → ConvDeriv) (d : Sketch α) (hh : holes d = []) :
    run G E R n goals d = ((toDeriv fill d).label, convCheck G E R n (toDeriv fill d)) := by
  refine PFunctor.FreeM.rec (motive := fun d : Sketch α ↦ holes d = [] →
    run G E R n goals d = ((toDeriv fill d).label, convCheck G E R n (toDeriv fill d)))
    ?_ ?_ d hh
  · intro h hh
    cases hh
  · intro r cs ih hh
    rcases r with ⟨r, k⟩
    have hcs (i : Fin k) : holes (cs i) = [] := by
      exact (List.flatten_eq_nil_iff.mp hh) _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
    change (r, convStep G E R n r (List.ofFn fun i ↦
      (RoseTree.node (run G E R n goals (cs i)).1 [], (run G E R n goals (cs i)).2))) =
      ((RoseTree.node r (List.ofFn fun i ↦ toDeriv fill (cs i))).label,
        convCheck G E R n (RoseTree.node r (List.ofFn fun i ↦ toDeriv fill (cs i))))
    have hi := fun i ↦ ih i (hcs i)
    have hm := congrArg (fun f : Fin k → ConvRule × Checks ↦
      List.ofFn fun i ↦ (RoseTree.node (f i).1 [], (f i).2)) (funext hi)
    rw [hm]
    simp only [RoseTree.label_node, convCheck_node, List.map_ofFn]
    simpa only [List.map_ofFn, Function.comp_def] using congrArg (r, ·) (convStep_roots G E R n r
      (List.ofFn (n := k) fun i ↦
        (toDeriv fill (cs i), convCheck G E R n (toDeriv fill (cs i)))))

/-- Regard an ordinary conversion certificate as a sketch with no holes. -/
def ofDeriv {α : Type} : ConvDeriv → Sketch α := RoseTree.elim node

/-- A rule's holes are the holes of its premises in order. -/
@[simp] theorem holes_node {α : Type} (r : ConvRule) (ds : List (Sketch α)) :
    holes (node r ds) = (ds.map holes).flatten := by
  change (List.ofFn fun i : Fin ds.length ↦ holes ds[i.1]).flatten = _
  rw [List.ofFn_getElem_eq_map]

/-- Interpreting a rule preserves its premises. -/
@[simp] theorem toDeriv_node {α : Type} (fill : α → ConvDeriv) (r : ConvRule)
    (ds : List (Sketch α)) :
    toDeriv fill (node r ds) = RoseTree.node r (ds.map (toDeriv fill)) := by
  change RoseTree.node r (List.ofFn fun i : Fin ds.length ↦ toDeriv fill ds[i.1]) = _
  rw [List.ofFn_getElem_eq_map]

/-- Embedding a certificate introduces no obligations. -/
@[simp] theorem holes_ofDeriv {α : Type} (d : ConvDeriv) :
    holes (ofDeriv (α := α) d) = [] := by
  refine RoseTree.ind (P := fun d ↦ holes (ofDeriv (α := α) d) = [])
    (fun r cs ih ↦ ?_) d
  simp only [ofDeriv, RoseTree.elim_node, holes_node]
  apply List.flatten_eq_nil_iff.mpr
  intro hs hhs
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hhs
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hs
  exact ih c hc

/-- Interpreting an embedded certificate returns that certificate. -/
@[simp] theorem toDeriv_ofDeriv {α : Type} (fill : α → ConvDeriv) (d : ConvDeriv) :
    toDeriv fill (ofDeriv d) = d := by
  refine RoseTree.ind (P := fun d ↦ toDeriv fill (ofDeriv d) = d) (fun r cs ih ↦ ?_) d
  simp only [ofDeriv, RoseTree.elim_node, toDeriv_node, List.map_map]
  exact congrArg (RoseTree.node r) ((List.map_congr_left ih).trans cs.map_id)

/-- Checking a closed sketch agrees with checking its conversion certificate. -/
theorem checks_eq_convChecks {α : Type} (G : Globals) (E : Array Entry) (R : List ℕ)
    (goals : α → Thm) (fill : α → ConvDeriv) (a : Thm) (d : Sketch α) (hh : holes d = []) :
    checks G E R goals a d = a.convChecks G E R (toDeriv fill d) := by
  simp only [checks, hh, List.all_nil, Bool.and_true,
    run_eq_convCheck G E R a.arity goals fill d hh, Thm.convChecks]

/-- Return an ordinary certificate only for an accepted sketch with no remaining holes. The
default filling is never used in an accepted result. -/
def finish {α : Type} (G : Globals) (E : Array Entry) (R : List ℕ) (goals : α → Thm)
    (a : Thm) (d : Sketch α) : Option ConvDeriv :=
  if (holes d).isEmpty && checks G E R goals a d then
    some (toDeriv (fun _ ↦ RoseTree.node (.base .join) []) d)
  else none

/-- Every certificate returned by finishing proves the original theorem in the conversion
checker. In particular, its existing soundness theorem applies without any hole assumptions. -/
theorem convChecks_of_finish {α : Type} {G : Globals} {E : Array Entry} {R : List ℕ}
    {goals : α → Thm} {a : Thm} {d : Sketch α} {c : ConvDeriv}
    (h : finish G E R goals a d = some c) : holes d = [] ∧ a.convChecks G E R c = true := by
  unfold finish at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hc
    obtain ⟨hh, hd⟩ := hc
    cases Option.some.inj h
    exact ⟨hh, (checks_eq_convChecks G E R goals _ a d hh) ▸ hd⟩
  · cases h

/-- Every accepted ordinary certificate finishes as itself. -/
theorem finish_ofDeriv {α : Type} (G : Globals) (E : Array Entry) (R : List ℕ)
    (goals : α → Thm) (a : Thm) (d : ConvDeriv) (h : a.convChecks G E R d = true) :
    finish G E R goals a (ofDeriv d) = some d := by
  simp only [finish, holes_ofDeriv, List.isEmpty_nil, Bool.true_and]
  rw [checks_eq_convChecks G E R goals (fun _ ↦ d) a _ (holes_ofDeriv d), toDeriv_ofDeriv, h]
  simp only [↓reduceIte, toDeriv_ofDeriv]

/-- Check a sketch and its fillings against their declared sequents, then check their grafting.
A filling may introduce further holes, declared by {lit}`newGoals`. Unfilled holes can be
retained by mapping them to variables. Only identities occurring in the sketch are inspected. -/
def fill {α β : Type} (G : Globals) (E : Array Entry) (R : List ℕ) (goals : α → Thm)
    (a : Thm) (d : Sketch α) (newGoals : β → Thm) (σ : α → Sketch β) : Option (Sketch β) :=
  if checks G E R goals a d &&
      (holes d).all (fun h ↦ checks G E R newGoals (goals h) (σ h)) then
    let result := d.bind σ
    if checks G E R newGoals a result then some result else none
  else none

/-- Accepted filling is exactly free-monad substitution, checked against the original target
and the new obligations. Its conditional soundness is {name}`valid_of_checks`. -/
theorem checks_of_fill {α β : Type} {G : Globals} {E : Array Entry} {R : List ℕ}
    {goals : α → Thm} {a : Thm} {d : Sketch α} {newGoals : β → Thm}
    {σ : α → Sketch β} {result : Sketch β}
    (h : fill G E R goals a d newGoals σ = some result) :
    result = d.bind σ ∧ checks G E R newGoals a result = true := by
  unfold fill at h
  split at h
  · dsimp only at h
    split at h
    · exact ⟨(Option.some.inj h).symm, Option.some.inj h ▸ ‹_ = true›⟩
    · cases h
  · cases h

/-- The report gives exactly the declared sequents of an accepted sketch's holes. -/
theorem check_eq_some_iff {α : Type} {G : Globals} {E : Array Entry} {R : List ℕ}
    {goals : α → Thm} {a : Thm} {d : Sketch α} {obligations : List (α × Thm)} :
    check G E R goals a d = some obligations ↔
      checks G E R goals a d = true ∧ obligations = (holes d).map (fun h ↦ (h, goals h)) := by
  simp only [check]
  split
  · rename_i hc
    rw [hc]
    exact ⟨fun h ↦ ⟨rfl, (Option.some.inj h).symm⟩, fun h ↦ congrArg some h.2.symm⟩
  · rename_i hc
    exact ⟨fun h ↦ (nomatch h), fun h ↦ (hc h.1).elim⟩

/-- Grafting replaces each occurrence of a hole by the obligations of its filling. -/
theorem holes_bind {α β : Type} (d : Sketch α) (σ : α → Sketch β) :
    holes (d.bind σ) = (holes d).flatMap (fun h ↦ holes (σ h)) := by
  refine PFunctor.FreeM.rec (motive := fun d : Sketch α ↦
    holes (d.bind σ) = (holes d).flatMap (fun h ↦ holes (σ h))) ?_ ?_ d
  · intro h
    change holes (σ h) = [h].flatMap (fun h ↦ holes (σ h))
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  · intro r cs ih
    change (List.ofFn fun i ↦ holes ((cs i).bind σ)).flatten =
      (List.ofFn fun i ↦ holes (cs i)).flatten.flatMap (fun h ↦ holes (σ h))
    rw [congrArg (fun f ↦ List.ofFn f) (funext ih)]
    simp only [List.flatMap_def, List.map_flatten, List.map_ofFn, List.flatten_flatten,
      Function.comp_def]

end Geb.FreeTopos.Internal.ProofHoles

end
