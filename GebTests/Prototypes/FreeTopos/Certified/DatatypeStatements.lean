/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.RepresentNat
public import GebTests.Prototypes.FreeTopos.Certified.DatatypePasses
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The definitions of the soundness's conclusion represent Lean's

The conclusion of the datatype language's soundness is stated by definitions of the extended
program ({lit}`DatatypeAccepted.statementDefs`): addition of natural numbers, convergence of a
function of the fuel, the quantification over a list, the evaluator's functions at a level of
fuel, the relation at a type, and the two formulas of the conclusion. Each compiles to an arrow
that, with every definition unfolded, represents a function or a predicate of Lean
({name}`Geb.FreeTopos.Represents`), built the same way from the values of the globals the
kernel loads.

## Main definitions

* {lit}`EvalFns` — the values of the compilers' definitions the conclusion calls.
* {lit}`Conv` — convergence of a function of the fuel to a value a predicate holds of.
* {lit}`Level` — the evaluator's functions at a level of fuel, from the loaded levels.

## Main statements

* {lit}`exists_evalFns` — the loaded globals give the values the conclusion's definitions call.
* {lit}`represents_add` — addition's arrow represents addition.
* {lit}`represents_conv` — convergence's arrow represents convergence.
* {lit}`represents_allL` — the quantification over a list's arrow represents the quantification
  over its elements.
* {lit}`represents_level` — the arrow of the evaluator's functions at a level represents the
  fold of the loaded levels.

## References

* {citeKey}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, datatypes, natural numbers object, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified.DatatypeStatements

open Geb Geb.FreeTopos Geb.FreeTopos.Translation GebTests.Prototypes.FreeTopos.Datatypes
open GebTests.Prototypes.FreeTopos.Weakening (Prog)
open GebTests.Prototypes.FreeTopos.Normalization (Defs succN kSucc pc)
open GebTests.Prototypes.FreeTopos.Certified.DatatypeAccepted (addDefn convDefn allLDefn
  levelDefn envTy fnsK statementDefs statementGlobals statementGlobalsTyped)
open GebTests.Prototypes.FreeTopos.Certified.DatatypeTranslated
open GebTests.Prototypes.FreeTopos.Certified.DatatypePasses (Env)
open Internal (Term RepC repC_var repC_lam repC_app envRep_std₁ envRep_std₂ envRep_ext
  repC_natRec repC_listRec repC_succ objVal_nat objVal_one objVal_exp objVal_prod objVal_list
  objVal_omega repC_eq isTy_nat isTy_exp isTy_omega isTy_list)
open Kernel (tT tList tProd tArrow)
open Sorts

/-- The values of the kernel type of the evaluator's functions at a level: evaluation in an
environment, and application. -/
abbrev Fns : Type :=
  (List Kernel.Tree → Kernel.Tree → Kernel.Tree) × (Kernel.Tree → Kernel.Tree → Kernel.Tree)

/-- The values of the compilers' definitions the soundness's conclusion calls. -/
structure EvalFns where
  /-- The presence of a tree. -/
  just : Kernel.Tree → Kernel.Tree
  /-- The element of a list at an index, when there is one. -/
  nth : List Kernel.Tree → Kernel.Tree → Kernel.Tree
  /-- The value of an optional tree that is present. -/
  get : Kernel.Tree → Kernel.Tree
  /-- Whether an optional tree is present. -/
  isSome : Kernel.Tree → Kernel.Tree
  /-- The evaluator's functions at a level, from the definitions. -/
  level : List Kernel.Tree → Kernel.Tree → Fns
  /-- The evaluator's functions at the next level, from the definitions and a level's. -/
  next : List Kernel.Tree → Fns → Fns
  /-- The value that quotes a tree. -/
  valQuote : Kernel.Tree → Kernel.Tree
  /-- The unit value. -/
  valUnit : Kernel.Tree
  /-- The value that pairs two values. -/
  valPair : Kernel.Tree → Kernel.Tree → Kernel.Tree
  /-- The list of values a value is, when it is one. -/
  listOf : Kernel.Tree → Kernel.Tree
  /-- Whether a tree is a member of a datatype, by the markers. -/
  memberOf : List Kernel.Tree → Kernel.Tree → Kernel.Tree → Kernel.Tree
  /-- The type a name has among named types, when it has one. -/
  lookupName : Kernel.Tree → List Kernel.Tree → Kernel.Tree
  /-- The typing environment's definitions. -/
  envDefs : Env → List Kernel.Tree
  /-- Whether a name is among names. -/
  hasName : Kernel.Tree → List Kernel.Tree → Kernel.Tree
  /-- The typing environment's datatypes. -/
  envNoms : Env → List Kernel.Tree
  /-- The name of a datatype's recognizer. -/
  recognizerName : Kernel.Tree → Kernel.Tree
  /-- The index of a name among names, when it has one. -/
  indexOf : Kernel.Tree → List Kernel.Tree → Kernel.Tree
  /-- The typing environment's markers. -/
  envMs : Env → List Kernel.Tree

/-- The values are those of the globals the kernel loads for the definitions' names. -/
structure EvalFns.Loaded (f : EvalFns) (Gk : List Kernel.Glob) (idx : String → ℕ) : Prop where
  /-- The presence's. -/
  just : DatatypeTranslated.Loaded Gk idx "Prelude.some" (tArrow tT tT) f.just
  /-- The element's. -/
  nth : DatatypeTranslated.Loaded Gk idx "Prelude.nth" (tArrow (tList tT) (tArrow tT tT)) f.nth
  /-- The present value's. -/
  get : DatatypeTranslated.Loaded Gk idx "Prelude.get" (tArrow tT tT) f.get
  /-- The presence test's. -/
  isSome : DatatypeTranslated.Loaded Gk idx "Prelude.isSome" (tArrow tT tT) f.isSome
  /-- The level's. -/
  level : DatatypeTranslated.Loaded Gk idx "Eval.level" (tArrow (tList tT) (tArrow tT fnsK))
    f.level
  /-- The next level's. -/
  next : DatatypeTranslated.Loaded Gk idx "Eval.next" (tArrow (tList tT) (tArrow fnsK fnsK))
    f.next
  /-- The quotation's. -/
  valQuote : DatatypeTranslated.Loaded Gk idx "Eval.valQuote" (tArrow tT tT) f.valQuote
  /-- The unit value's. -/
  valUnit : DatatypeTranslated.Loaded Gk idx "Eval.valUnit" tT f.valUnit
  /-- The pair's. -/
  valPair : DatatypeTranslated.Loaded Gk idx "Eval.valPair" (tArrow tT (tArrow tT tT)) f.valPair
  /-- The list's. -/
  listOf : DatatypeTranslated.Loaded Gk idx "Eval.listOf" (tArrow tT tT) f.listOf
  /-- The membership's. -/
  memberOf : DatatypeTranslated.Loaded Gk idx "Typing.memberOf"
    (tArrow (tList tT) (tArrow tT (tArrow tT tT))) f.memberOf
  /-- The lookup's. -/
  lookupName : DatatypeTranslated.Loaded Gk idx "Typing.lookupName"
    (tArrow tT (tArrow (tList tT) tT)) f.lookupName
  /-- The environment's definitions'. -/
  envDefs : DatatypeTranslated.Loaded Gk idx "Typing.envDefs" (tArrow envTy (tList tT)) f.envDefs
  /-- The name test's. -/
  hasName : DatatypeTranslated.Loaded Gk idx "Typing.hasName" (tArrow tT (tArrow (tList tT) tT))
    f.hasName
  /-- The environment's datatypes'. -/
  envNoms : DatatypeTranslated.Loaded Gk idx "Typing.envNoms" (tArrow envTy (tList tT)) f.envNoms
  /-- The recognizer's name's. -/
  recognizerName : DatatypeTranslated.Loaded Gk idx "Typing.recognizerName" (tArrow tT tT)
    f.recognizerName
  /-- The index's. -/
  indexOf : DatatypeTranslated.Loaded Gk idx "Reader.indexOf" (tArrow tT (tArrow (tList tT) tT))
    f.indexOf
  /-- The environment's markers'. -/
  envMs : DatatypeTranslated.Loaded Gk idx "Typing.envMs" (tArrow envTy (tList tT)) f.envMs

/-- Convergence of a function of the fuel to a value a predicate holds of: from some fuel on,
the function's value is the presence of one value, of which the predicate holds. -/
def Conv (just : Kernel.Tree → Kernel.Tree) (F : ℕ → Kernel.Tree) (Pr : Kernel.Tree → Prop) :
    Prop :=
  ∃ n : ℕ, ∃ w : Kernel.Tree, (∀ m : ℕ, F (n + m) = just w) ∧ Pr w

/-- The evaluator's functions at a level of fuel, from the definitions: the fold of the next
level from the level zero. -/
def Level (f : EvalFns) (D : List Kernel.Tree) (k : ℕ) : Fns :=
  Nat.rec (motive := fun _ ↦ List Kernel.Tree → Fns) (fun D ↦ f.level D (Kernel.leaf 0))
    (fun _ r D ↦ f.next D (r D)) k D

/-- The fold that defines the quantification over a list is the quantification over its
elements. -/
theorem foldr_all {α : Type} (Pr : α → Prop) :
    ∀ xs : List α, List.foldr (fun y (r : (α → Prop) → Prop) Pr' ↦ Pr' y ∧ r Pr')
      (fun _ ↦ True) xs Pr = ∀ x ∈ xs, Pr x :=
  List.rec (propext ⟨fun _ _ hx ↦ (List.not_mem_nil hx).elim, fun _ ↦ trivial⟩) fun y _ ih ↦
    (congrArg (Pr y ∧ ·) ih).trans (propext List.forall_mem_cons.symm)

/-- The recursion on the second summand into functions of the first is addition. -/
theorem natRec_add (a b : ℕ) :
    Nat.rec (motive := fun _ ↦ ℕ → ℕ) (fun a ↦ a) (fun _ f a ↦ (f a).succ) b a = a + b :=
  Nat.rec
    (motive := fun b ↦
      Nat.rec (motive := fun _ ↦ ℕ → ℕ) (fun a ↦ a) (fun _ f a ↦ (f a).succ) b a = a + b)
    rfl (fun _ ih ↦ congrArg Nat.succ ih) b

variable {PST : Prog × Defs × Defs3}

/-- The loaded globals give the values of the compilers' definitions the conclusion calls, each
at the kernel type the evaluator checked ({name}`DatatypeAccepted.statementGlobalsTyped`). -/
theorem exists_evalFns (L : Translated PST) : ∃ f : EvalFns, f.Loaded L.Gk PST.1.idx := by
  have m : ∀ (i : ℕ) {name : String} {T : Kernel.Tree},
      statementGlobals[i]? = some (name, T) →
        ∃ f, DatatypeTranslated.Loaded L.Gk PST.1.idx name T f := by
    intro _ _ _ hm
    exact L.loaded statementGlobalsTyped (List.mem_of_getElem? hm)
  obtain ⟨f₀, h₀⟩ := m 0 rfl
  obtain ⟨f₁, h₁⟩ := m 1 rfl
  obtain ⟨f₂, h₂⟩ := m 2 rfl
  obtain ⟨f₃, h₃⟩ := m 3 rfl
  obtain ⟨f₄, h₄⟩ := m 4 rfl
  obtain ⟨f₅, h₅⟩ := m 5 rfl
  obtain ⟨f₆, h₆⟩ := m 6 rfl
  obtain ⟨f₇, h₇⟩ := m 7 rfl
  obtain ⟨f₈, h₈⟩ := m 8 rfl
  obtain ⟨f₉, h₉⟩ := m 9 rfl
  obtain ⟨f₁₀, h₁₀⟩ := m 10 rfl
  obtain ⟨f₁₁, h₁₁⟩ := m 11 rfl
  obtain ⟨f₁₂, h₁₂⟩ := m 12 rfl
  obtain ⟨f₁₃, h₁₃⟩ := m 13 rfl
  obtain ⟨f₁₄, h₁₄⟩ := m 14 rfl
  obtain ⟨f₁₅, h₁₅⟩ := m 15 rfl
  obtain ⟨f₁₆, h₁₆⟩ := m 16 rfl
  obtain ⟨f₁₇, h₁₇⟩ := m 17 rfl
  exact ⟨⟨f₀, f₁, f₂, f₃, f₄, f₅, f₆, f₇, f₈, f₉, f₁₀, f₁₁, f₁₂, f₁₃, f₁₄, f₁₅, f₁₆, f₁₇⟩,
    ⟨h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇⟩⟩

section Globals

variable (L : Translated PST) {X : PartialHorn.Tree}
  {e : List (PartialHorn.Tree × PartialHorn.Tree)} {S A : Type} {R : S → A → Prop}

/-- A reference to a named definition, in any environment, represents the value of its loaded
global. -/
theorem repC_pc₀ {name : String} {T : Kernel.Tree} {g : Kernel.Ty.den T}
    (hg : DatatypeTranslated.Loaded L.Gk PST.1.idx name T g) {a : PartialHorn.Tree}
    (ha : ty T = some a) (hX : ObjVal [] (unfoldTerm sig (L.cds₀ ++ L.ext) X) A)
    (R : S → A → Prop) :
    RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] (pc PST.1 name []) X e a R (KRel T) fun _ ↦ g := by
  obtain ⟨n, hn, hG⟩ := hg
  obtain ⟨a', ha', hr⟩ := repC_global (e := e) L.ctx L.rep hG hX R
  obtain rfl : a' = a := Option.some.inj (ha'.symm.trans ha)
  rw [← hn] at hr
  exact hr

/-- The application of a named definition represents the application of its loaded global's
value. -/
theorem repC_pc₁ {name : String} {B C : Kernel.Tree} {g : Kernel.Ty.den B → Kernel.Ty.den C}
    (hg : DatatypeTranslated.Loaded L.Gk PST.1.idx name (tArrow B C) g)
    {b c : PartialHorn.Tree} (hb : ty B = some b) (hc : ty C = some c)
    (hX : ObjVal [] (unfoldTerm sig (L.cds₀ ++ L.ext) X) A) {u : Term}
    {F : S → Kernel.Ty.den B}
    (hu : RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] u X e b R (KRel B) F) :
    RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] (pc PST.1 name [u]) X e c R (KRel C)
      fun s ↦ g (F s) :=
  repC_app (repC_pc₀ L hg (a := exp b c) (by simp [hb, hc]) hX R) hu (objVal_ty' hb)
    (objVal_ty' hc)

/-- The application of a named definition to two arguments represents that of its loaded
global's value. -/
theorem repC_pc₂ {name : String} {B C E : Kernel.Tree}
    {g : Kernel.Ty.den B → Kernel.Ty.den C → Kernel.Ty.den E}
    (hg : DatatypeTranslated.Loaded L.Gk PST.1.idx name (tArrow B (tArrow C E)) g)
    {b c d : PartialHorn.Tree} (hb : ty B = some b) (hc : ty C = some c) (hd : ty E = some d)
    (hX : ObjVal [] (unfoldTerm sig (L.cds₀ ++ L.ext) X) A) {u w : Term}
    {F : S → Kernel.Ty.den B} {F' : S → Kernel.Ty.den C}
    (hu : RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] u X e b R (KRel B) F)
    (hw : RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] w X e c R (KRel C) F') :
    RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] (pc PST.1 name [u, w]) X e d R (KRel E)
      fun s ↦ g (F s) (F' s) :=
  repC_app (repC_app (repC_pc₀ L hg (a := exp b (exp c d)) (by simp [hb, hc, hd]) hX R) hu
    (objVal_ty' hb) (objVal_ty' (T := tArrow C E) (by simp [hc, hd]))) hw (objVal_ty' hc)
    (objVal_ty' hd)

/-- The application of a named definition to three arguments represents that of its loaded
global's value. -/
theorem repC_pc₃ {name : String} {B C E H : Kernel.Tree}
    {g : Kernel.Ty.den B → Kernel.Ty.den C → Kernel.Ty.den E → Kernel.Ty.den H}
    (hg : DatatypeTranslated.Loaded L.Gk PST.1.idx name (tArrow B (tArrow C (tArrow E H))) g)
    {b c d k : PartialHorn.Tree} (hb : ty B = some b) (hc : ty C = some c) (hd : ty E = some d)
    (hk : ty H = some k) (hX : ObjVal [] (unfoldTerm sig (L.cds₀ ++ L.ext) X) A)
    {u w z : Term} {F : S → Kernel.Ty.den B} {F' : S → Kernel.Ty.den C}
    {F'' : S → Kernel.Ty.den E}
    (hu : RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] u X e b R (KRel B) F)
    (hw : RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] w X e c R (KRel C) F')
    (hz : RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] z X e d R (KRel E) F'') :
    RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] (pc PST.1 name [u, w, z]) X e k R (KRel H)
      fun s ↦ g (F s) (F' s) (F'' s) :=
  repC_app (repC_app (repC_app
    (repC_pc₀ L hg (a := exp b (exp c (exp d k))) (by simp [hb, hc, hd, hk]) hX R) hu
    (objVal_ty' hb) (objVal_ty' (T := tArrow C (tArrow E H)) (by simp [hc, hd, hk]))) hw
    (objVal_ty' hc) (objVal_ty' (T := tArrow E H) (by simp [hd, hk]))) hz (objVal_ty' hd)
    (objVal_ty' hk)

end Globals

variable (h : extended3 = some PST) (L : Translated PST)

include h

/-- The extended program's constants have the connectives' definitions and compile to
well-formed definitions. -/
theorem connectives : Internal.Connectives PST.1.G (L.cds₀ ++ L.ext) PST.1.o :=
  ⟨L.ctx.base, L.ctx.compiles, L.ctx.wf, DatatypeAccepted.hasLogic h⟩

/-- Addition's arrow represents the addition of a pair of natural numbers. -/
theorem represents_add {fk : PartialHorn.Tree}
    (hdk : (L.cds₀ ++ L.ext)[PST.2.1.q]? = some ⟨List.replicate 0 obj, arr, fk⟩) :
    Represents [] (unfoldTerm sig (L.cds₀ ++ L.ext) fk) (Rep.prod Rep.nat Rep.nat) Rep.nat
      fun p : ℕ × ℕ ↦ p.1 + p.2 := by
  have hk : PST.1.G.defs[PST.2.1.q]? = some (.language addDefn) :=
    DatatypeAccepted.defined h (List.mem_of_getElem? (i := 0) rfl)
  have hS : ({ PST.1.G with defs := PST.1.G.defs.take PST.2.1.q } : Internal.Globals).prims[kSucc]?
      = some Internal.succPrim :=
    (DatatypeAccepted.natPrims h).2
  have he := envRep_std₂ (ds := L.cds₀ ++ L.ext) (ρ := []) (p₁ := nat) (p₂ := nat) objVal_nat
    objVal_nat Rep.nat Rep.nat
  -- the start, the identity, and the step, the successor of the function's value
  have hv : RepC { PST.1.G with defs := PST.1.G.defs.take PST.2.1.q } 0 (L.cds₀ ++ L.ext) []
      (v 0) (prod one nat) (Internal.extEnv one nat []) nat (Rep.prod Rep.unit Rep.nat)
      Rep.nat Prod.snd :=
    repC_var (envRep_ext objVal_one objVal_nat .nil Rep.nat) rfl
  have hz : RepC { PST.1.G with defs := PST.1.G.defs.take PST.2.1.q } 0 (L.cds₀ ++ L.ext) []
      (Term.lam nat (v 0)) one [] (exp nat nat) Rep.unit (Rep.exp Rep.nat Rep.nat)
      fun _ a ↦ a :=
    repC_lam Internal.isTy_nat objVal_one objVal_nat hv
  have hes := envRep_ext (objVal_exp objVal_nat objVal_nat) objVal_nat
    (envRep_std₁ (ds := L.cds₀ ++ L.ext) (ρ := []) (objVal_exp objVal_nat objVal_nat)
      (Rep.exp Rep.nat Rep.nat)) Rep.nat
  have hb : RepC { PST.1.G with defs := PST.1.G.defs.take PST.2.1.q } 0 (L.cds₀ ++ L.ext) []
      (succN (Term.app (v 1) (v 0))) (prod (exp nat nat) nat)
      (Internal.extEnv (exp nat nat) nat (Internal.stdEnv [exp nat nat])) nat
      (Rep.prod (Rep.exp Rep.nat Rep.nat) Rep.nat) Rep.nat
      fun s : (ℕ → ℕ) × ℕ ↦ (s.1 s.2).succ :=
    repC_succ hS (repC_app (repC_var hes rfl) (repC_var hes rfl) objVal_nat objVal_nat)
  have hs : RepC { PST.1.G with defs := PST.1.G.defs.take PST.2.1.q } 0 (L.cds₀ ++ L.ext) []
      (Term.lam nat (succN (Term.app (v 1) (v 0)))) (exp nat nat)
      (Internal.stdEnv [exp nat nat]) (exp nat nat) (Rep.exp Rep.nat Rep.nat)
      (Rep.exp Rep.nat Rep.nat) fun f a ↦ (f a).succ :=
    repC_lam Internal.isTy_nat (objVal_exp objVal_nat objVal_nat) objVal_nat hb
  exact Internal.rep_def (τ' := []) L.ctx.compiles hk
    (repC_app (repC_natRec (repC_var he rfl) hz hs) (repC_var he rfl) objVal_nat objVal_nat)
    (fun p ↦ natRec_add p.1 p.2) hdk

/-- A sum of two natural numbers in a context represents the sum of what they represent. -/
theorem repC_add {X : PartialHorn.Tree} {e : List (PartialHorn.Tree × PartialHorn.Tree)}
    {S A : Type} {R : S → A → Prop} {m k : Term} {M K : S → ℕ}
    (hm : RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] m X e nat R Rep.nat M)
    (hk : RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] k X e nat R Rep.nat K) :
    RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] (PST.2.1.add m k) X e nat R Rep.nat
      fun s ↦ M s + K s := by
  have hd : PST.1.G.defs[PST.2.1.q]? = some (.language addDefn) :=
    DatatypeAccepted.defined h (List.mem_of_getElem? (i := 0) rfl)
  obtain ⟨fa, hda⟩ := Internal.compiled_language L.ctx.compiles hd
  exact Internal.repC_call₂ (θ := []) (τ' := []) (d := addDefn) L.ctx.base hd L.ctx.wf hda rfl
    rfl (fun _ hu ↦ nomatch hu) .nil (by simp [addDefn, nat, subst_op])
    (by simp [addDefn, nat, subst_op]) (represents_add h L hda) hm hk

/-- Convergence's arrow represents the convergence of a function of the fuel to a value a
predicate holds of ({name}`Conv`), by the loaded presence of a tree. -/
theorem represents_conv {f : EvalFns} (hf : f.Loaded L.Gk PST.1.idx) {fk : PartialHorn.Tree}
    (hdk : (L.cds₀ ++ L.ext)[PST.2.1.q + 2]? = some ⟨List.replicate 0 obj, arr, fk⟩) :
    Represents [] (unfoldTerm sig (L.cds₀ ++ L.ext) fk)
      (Rep.prod (Rep.exp Rep.nat (Rep.rose RN)) (Rep.exp (Rep.rose RN) Rep.prop)) Rep.prop
      fun p : (ℕ → Kernel.Tree) × (Kernel.Tree → Prop) ↦ Conv f.just p.1 p.2 := by
  have hC := connectives h L
  have hk : PST.1.G.defs[PST.2.1.q + 2]? = some (.language (convDefn PST.1 PST.2.1)) :=
    DatatypeAccepted.defined h (List.mem_of_getElem? (i := 1) rfl)
  -- the types' values, and their properties
  have hT : ObjVal [] (unfoldTerm sig (L.cds₀ ++ L.ext) treeTy) (MTy tT) := objVal_ty' rfl
  have hN := objVal_nat (ds := L.cds₀ ++ L.ext) (ρ := [])
  have hF := objVal_exp hN hT
  have hP := objVal_exp hT (objVal_omega (ds := L.cds₀ ++ L.ext) (ρ := []))
  have hsT := ty_spec (G := PST.1.G) (n := 0) (ρ := []) (ds := L.cds₀ ++ L.ext) tT rfl
  obtain ⟨htot, hsur, hl, hr⟩ := (order_props tT).1 rfl
  -- the contexts under the binders: the parameters, the fuel, the value, the further fuel
  have he₀ := envRep_std₂ hF hP (Rep.exp Rep.nat (Rep.rose RN)) (Rep.exp (Rep.rose RN) Rep.prop)
  have hX₀ : ObjVal [] (unfoldTerm sig (L.cds₀ ++ L.ext)
      (Internal.ctxObj [exp treeTy omega, exp nat treeTy])) (FunRel ℕ (MTy tT) ×
        FunRel (MTy tT) Prop) := by
    rw [Internal.ctxObj_cons_cons, Internal.ctxObj_single]
    exact objVal_prod hF hP
  have he₁ := envRep_ext hX₀ hN he₀ Rep.nat
  have hX₁ := objVal_prod hX₀ hN
  have he₂ := envRep_ext hX₁ hT he₁ (Rep.rose RN)
  have hX₂ := objVal_prod hX₁ hT
  have he₃ := envRep_ext hX₂ hN he₂ Rep.nat
  have hX₃ := objVal_prod hX₂ hN
  -- the function's value at the sum of the fuels is the presence of the value
  have heq := repC_eq
    (repC_app (repC_var (i := 4) he₃ rfl)
      (repC_add h L (repC_var (i := 2) he₃ rfl) (repC_var (i := 0) he₃ rfl)) hN hT)
    (repC_pc₁ L hf.just rfl rfl hX₃ (repC_var (i := 1) he₃ rfl)) hT hl hr
  have hall := hC.all (Rx := Rep.nat) (fun s ↦ ⟨s, rfl⟩) (fun a ↦ ⟨a, rfl⟩) isTy_nat rfl
    eval_nat (repC_lam isTy_nat hX₂ hN heq)
  have hcj := hC.conj hall
    (repC_app (repC_var (i := 2) he₂ rfl) (repC_var (i := 0) he₂ rfl) hT objVal_omega)
  have hex := hC.ex (Rx := Rep.rose RN) htot hsur hsT.1 hsT.2.1 (objVal_ty (T := tT) rfl)
    (repC_lam hsT.1 hX₁ hT hcj)
  have hexn := hC.ex (Rx := Rep.nat) (fun s ↦ ⟨s, rfl⟩) (fun a ↦ ⟨a, rfl⟩) isTy_nat rfl
    eval_nat (repC_lam isTy_nat hX₀ hN hex)
  exact Internal.rep_def_full (τ' := []) L.ctx.compiles hk hexn (fun _ ↦ rfl) hdk

/-- A convergence in a context represents the convergence of the function of the fuel to a
value of the predicate, as its parts represent them. -/
theorem repC_conv {f : EvalFns} (hf : f.Loaded L.Gk PST.1.idx) {X : PartialHorn.Tree}
    {e : List (PartialHorn.Tree × PartialHorn.Tree)} {S A : Type} {R : S → A → Prop}
    {t p : Term} {F : S → ℕ → Kernel.Tree} {Pr : S → Kernel.Tree → Prop}
    (ht : RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] t X e (exp nat treeTy) R
      (Rep.exp Rep.nat (Rep.rose RN)) F)
    (hp : RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] p X e (exp treeTy omega) R
      (Rep.exp (Rep.rose RN) Rep.prop) Pr) :
    RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] (PST.2.1.conv t p) X e omega R Rep.prop
      fun s ↦ Conv f.just (F s) (Pr s) := by
  have hd : PST.1.G.defs[PST.2.1.q + 2]? = some (.language (convDefn PST.1 PST.2.1)) :=
    DatatypeAccepted.defined h (List.mem_of_getElem? (i := 1) rfl)
  obtain ⟨fc, hdc⟩ := Internal.compiled_language L.ctx.compiles hd
  exact Internal.repC_call₂ (θ := []) (τ' := []) (d := convDefn PST.1 PST.2.1) L.ctx.base hd
    L.ctx.wf hdc rfl rfl (fun _ hu ↦ nomatch hu) .nil rfl rfl (represents_conv h L hf hdc) ht hp

/-- The quantification over a list's arrow represents the quantification of a predicate over
the elements of a list. -/
theorem represents_allL {fk : PartialHorn.Tree}
    (hdk : (L.cds₀ ++ L.ext)[PST.2.1.q + 3]? = some ⟨List.replicate 0 obj, arr, fk⟩) :
    Represents [] (unfoldTerm sig (L.cds₀ ++ L.ext) fk)
      (Rep.prod (Rep.exp (Rep.rose RN) Rep.prop) (Rep.list (Rep.rose RN))) Rep.prop
      fun p : (Kernel.Tree → Prop) × List Kernel.Tree ↦ ∀ x ∈ p.2, p.1 x := by
  have hC := connectives h L
  have hk : PST.1.G.defs[PST.2.1.q + 3]? = some (.language (allLDefn PST.1)) :=
    DatatypeAccepted.defined h (List.mem_of_getElem? (i := 2) rfl)
  have hT : ObjVal [] (unfoldTerm sig (L.cds₀ ++ L.ext) treeTy) (MTy tT) := objVal_ty' rfl
  have hP := objVal_exp hT (objVal_omega (ds := L.cds₀ ++ L.ext) (ρ := []))
  have hc := objVal_exp hP (objVal_omega (ds := L.cds₀ ++ L.ext) (ρ := []))
  have htT : ∀ G : Internal.Globals, Internal.IsTy G 0 treeTy = true := fun G ↦
    (ty_spec (G := G) (n := 0) (ρ := []) (ds := []) tT rfl).1
  have htP : ∀ G : Internal.Globals, Internal.IsTy G 0 (exp treeTy omega) = true := fun G ↦ by
    simp [isTy_exp, htT G, isTy_omega]
  have htc : ∀ G : Internal.Globals,
      Internal.IsTy G 0 (exp (exp treeTy omega) omega) = true := fun G ↦ by
    simp [isTy_exp, htT G, isTy_omega]
  -- the parameters: the predicate, then the list
  have c₀ := (RepCtx.single L.ctx hP (htP _) (Rep.exp (Rep.rose RN) Rep.prop)).extend L.ctx
    (objVal_list hT) (by simp [isTy_list, htT]) (Rep.list (Rep.rose RN))
  -- the start, in no variables, under its predicate
  have cz := (RepCtx.nil L.ctx).extend L.ctx hP (htP _) (Rep.exp (Rep.rose RN) Rep.prop)
  have hz := repC_lam (G := PST.1.G) (n := 0) (htP _) (RepCtx.nil L.ctx).val hP
    (hC.tt (e := Internal.extEnv one (exp treeTy omega) []) cz.val
      (Rep.prod Rep.unit (Rep.exp (Rep.rose RN) Rep.prop)))
  -- the step, in the element and the rest's value, under its predicate
  have cs := (RepCtx.single L.ctx hT (htT _) (Rep.rose RN)).extend L.ctx hc (htc _)
    (Rep.exp (Rep.exp (Rep.rose RN) Rep.prop) Rep.prop)
  have csP := cs.extend L.ctx hP (htP _) (Rep.exp (Rep.rose RN) Rep.prop)
  have hs := repC_lam (G := PST.1.G) (n := 0) (htP _) cs.val hP
    (hC.conj (repC_app (csP.var (i := 0) rfl) (csP.var (i := 2) rfl) hT objVal_omega)
      (repC_app (csP.var (i := 1) rfl) (csP.var (i := 0) rfl) hP objVal_omega))
  exact Internal.rep_def_full (τ' := []) L.ctx.compiles hk
    (repC_app (repC_listRec (c₀.var (i := 0) rfl) hz hs hT) (c₀.var (i := 1) rfl) hP
      objVal_omega) (fun p ↦ foldr_all p.1 p.2) hdk

/-- A quantification over a list in a context represents the quantification of the predicate
over the elements of the list, as its parts represent them. -/
theorem repC_allL {X : PartialHorn.Tree} {e : List (PartialHorn.Tree × PartialHorn.Tree)}
    {S A : Type} {R : S → A → Prop} {p t : Term} {Pr : S → Kernel.Tree → Prop}
    {Xs : S → List Kernel.Tree}
    (hp : RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] p X e (exp treeTy omega) R
      (Rep.exp (Rep.rose RN) Rep.prop) Pr)
    (ht : RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] t X e (list treeTy) R
      (Rep.list (Rep.rose RN)) Xs) :
    RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] (PST.2.1.allL p t) X e omega R Rep.prop
      fun s ↦ ∀ x ∈ Xs s, Pr s x := by
  have hd : PST.1.G.defs[PST.2.1.q + 3]? = some (.language (allLDefn PST.1)) :=
    DatatypeAccepted.defined h (List.mem_of_getElem? (i := 2) rfl)
  obtain ⟨fc, hdc⟩ := Internal.compiled_language L.ctx.compiles hd
  exact Internal.repC_call₂ (θ := []) (τ' := []) (d := allLDefn PST.1) L.ctx.base hd
    L.ctx.wf hdc rfl rfl (fun _ hu ↦ nomatch hu) .nil rfl rfl (represents_allL h L hdc) hp ht

/-- The arrow of the evaluator's functions at a level represents the fold of the loaded next
level from the loaded level zero ({name}`Level`). -/
theorem represents_level {f : EvalFns} (hf : f.Loaded L.Gk PST.1.idx) {fk : PartialHorn.Tree}
    (hdk : (L.cds₀ ++ L.ext)[PST.2.1.q + 4]? = some ⟨List.replicate 0 obj, arr, fk⟩) :
    Represents [] (unfoldTerm sig (L.cds₀ ++ L.ext) fk)
      (Rep.prod (Rep.list (Rep.rose RN)) Rep.nat) (KRel fnsK)
      fun p : List Kernel.Tree × ℕ ↦ Level f p.1 p.2 := by
  have hk : PST.1.G.defs[PST.2.1.q + 4]? = some (.language (levelDefn PST.1)) :=
    DatatypeAccepted.defined h (List.mem_of_getElem? (i := 3) rfl)
  have hT : ObjVal [] (unfoldTerm sig (L.cds₀ ++ L.ext) treeTy) (MTy tT) := objVal_ty' rfl
  have hL := objVal_list hT
  have hN := objVal_nat (ds := L.cds₀ ++ L.ext) (ρ := [])
  have hty : ty fnsK = some Normalization.fnsTy := rfl
  have hFn : ObjVal [] (unfoldTerm sig (L.cds₀ ++ L.ext) Normalization.fnsTy) (MTy fnsK) :=
    objVal_ty' hty
  have hc := objVal_exp hL hFn
  have htL : ∀ G : Internal.Globals, Internal.IsTy G 0 (list treeTy) = true := fun G ↦
    (ty_spec (G := G) (n := 0) (ρ := []) (ds := []) (tList tT) rfl).1
  have htF : ∀ G : Internal.Globals, Internal.IsTy G 0 Normalization.fnsTy = true := fun G ↦
    (ty_spec (G := G) (n := 0) (ρ := []) (ds := []) fnsK hty).1
  have htc : ∀ G : Internal.Globals,
      Internal.IsTy G 0 (exp (list treeTy) Normalization.fnsTy) = true := fun G ↦ by
    simp [isTy_exp, htL G, htF G]
  -- the parameters: the definitions, then the level
  have c₀ := (RepCtx.single L.ctx hL (htL _) (Rep.list (Rep.rose RN))).extend L.ctx hN isTy_nat
    Rep.nat
  -- the level zero, in no variables, under its definitions
  have cz := (RepCtx.nil L.ctx).extend L.ctx hL (htL _) (Rep.list (Rep.rose RN))
  have hz := repC_lam (G := PST.1.G) (n := 0) (htL _) (RepCtx.nil L.ctx).val hL
    (repC_pc₂ L hf.level rfl rfl hty cz.val (cz.var (i := 0) rfl)
      (cz.quote L.ctx (Kernel.leaf 0)))
  -- the next level, in the level's functions of the definitions, under its definitions
  have cs := RepCtx.single L.ctx hc (htc _) (Rep.exp (Rep.list (Rep.rose RN)) (KRel fnsK))
  have csL := cs.extend L.ctx hL (htL _) (Rep.list (Rep.rose RN))
  have hs := repC_lam (G := PST.1.G) (n := 0) (htL _) cs.val hL
    (repC_pc₂ L hf.next rfl hty hty csL.val (csL.var (i := 0) rfl)
      (repC_app (csL.var (i := 1) rfl) (csL.var (i := 0) rfl) hL hFn))
  exact Internal.rep_def_full (τ' := []) L.ctx.compiles hk
    (repC_app (repC_natRec (c₀.var (i := 0) rfl) hz hs) (c₀.var (i := 1) rfl) hL hFn)
    (fun _ ↦ rfl) hdk

/-- The evaluator's functions at a level in a context represent those the loaded levels give
({name}`Level`), at the definitions and the level its parts represent. -/
theorem repC_level {f : EvalFns} (hf : f.Loaded L.Gk PST.1.idx) {X : PartialHorn.Tree}
    {e : List (PartialHorn.Tree × PartialHorn.Tree)} {S A : Type} {R : S → A → Prop}
    {t k : Term} {D : S → List Kernel.Tree} {K : S → ℕ}
    (ht : RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] t X e (list treeTy) R (Rep.list (Rep.rose RN)) D)
    (hk : RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] k X e nat R Rep.nat K) :
    RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] (PST.2.1.levelN t k) X e Normalization.fnsTy R
      (KRel fnsK) fun s ↦ Level f (D s) (K s) := by
  have hd : PST.1.G.defs[PST.2.1.q + 4]? = some (.language (levelDefn PST.1)) :=
    DatatypeAccepted.defined h (List.mem_of_getElem? (i := 3) rfl)
  obtain ⟨fc, hdc⟩ := Internal.compiled_language L.ctx.compiles hd
  exact Internal.repC_call₂ (θ := []) (τ' := []) (d := levelDefn PST.1) L.ctx.base hd
    L.ctx.wf hdc rfl rfl (fun _ hu ↦ nomatch hu) .nil rfl rfl (represents_level h L hf hdc) ht hk

end GebTests.Prototypes.FreeTopos.Certified.DatatypeStatements

end
