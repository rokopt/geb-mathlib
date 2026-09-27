/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Development
public import Geb.Prototypes.FreeTopos.TranslationKernel
public import Geb.Prototypes.Kernel.Reader
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The translation of the computational core is sound

A kernel program's translation ({name}`Geb.FreeTopos.Translation.program`) represents, definition
by definition, the globals the kernel loads ({name}`Geb.Kernel.load`); and when the internal
language's checker proves the translation of a kernel theorem
({name}`Geb.FreeTopos.Translation.thm`) in a development over the translated program, the kernel's
denotations of the theorem's sides agree. The argument evaluates the theorem's compiled sides in
the topos of types and functional relations, a model of the theory: there they are one functional
relation, which represents both sides' denotations by the fundamental lemma ({lit}`repC_term`),
so the denotations agree wherever the representations determine them.

## Main definitions

* {lit}`LTot`, {lit}`RTot`, {lit}`LUni`, {lit}`RUni` — the totality and uniqueness of a
  representation, in each direction.
* {lit}`order`, {lit}`FirstOrder` — the kernel types of data and of first order.

## Main statements

* {lit}`rep_program` — the definitions of a translated program represent the globals the kernel
  loads from it.
* {lit}`ctxRep_std` — a theorem's context is represented at the product of its types.
* {lit}`ty_inj` — the translation of types is injective.
* {lit}`order_props` — the representations of types of first order are total and unique.
* {lit}`translation_sound` — the soundness of the translation.
* {lit}`thm_valid` — a kernel theorem of first order whose translation is proved is valid.

## Implementation notes

The soundness theorem concludes the agreement of the sides at the values of the context that
have representations, when the equation's type's representations each represent one value; both
hold of the types of first order, whose function types have domains of data. A value of a
function type whose domain contains a function type has a representation only by unique choice:
the representation of a kernel function of functions relates each functional relation to the
kernel function's value at the function it represents, and extracting that function from a
functional relation, whose value at each argument exists uniquely, needs unique choice, which
Lean's logic without {lit}`Classical.choice` does not provide. The internal language validates
unique choice; the restriction arises only in reading its results back as Lean functions.

## Tags

translation, kernel, soundness, logical relation, functional relation
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Translation

open PartialHorn (Tree)
open Internal (Term Defn Globals RepC objs compileDefs)
open Sorts
open scoped Internal
open scoped FinEnum

variable {ds : List PartialHorn.Defn} {defsF : List Defn}

/-- An element of a list is the element of each list it is an initial segment of. -/
theorem getElem?_of_prefix {α : Type} {l l' : List α} (h : l <+: l') {i : ℕ} {a : α}
    (ha : l[i]? = some a) : l'[i]? = some a := by
  obtain ⟨t, rfl⟩ := h
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp ha).1]
  exact ha

/-- The constants of a program's first definitions are those of the whole program's truncated
after the library and them. -/
theorem globals_take {defs₀ : List Defn} (hpre : defs₀ <+: defsF) :
    { globals defsF with defs := (globals defsF).defs.take (lib.length + defs₀.length) } =
      globals defs₀ := by
  obtain ⟨rest, rfl⟩ := hpre
  simp only [globals, ← List.map_take]
  rw [List.take_append, List.take_of_length_le (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.take_left' rfl]

/-- A representation of a program's globals extends to a definition after them that represents
a value of its type. -/
theorem globRep_snoc (hF : compileDefs (globals defsF) = some ds) {defs₀ : List Defn}
    {G₀ : List Kernel.Glob} (hG : GlobRep defs₀ ds G₀) (hlen : defs₀.length = G₀.length)
    {A : Kernel.Tree} {a : Tree} {u : Term} (hpre : defs₀ ++ [mkDefn 0 [] a u] <+: defsF)
    (ha : ty A = some a) {v : Kernel.Ty.den A}
    (hr : RepC (globals defs₀) 0 ds [] u one [] a Rep.unit (KRel A) fun _ ↦ v) :
    GlobRep (defs₀ ++ [mkDefn 0 [] a u]) ds (G₀ ++ [⟨A, v⟩]) := by
  intro n g hg
  rcases Nat.lt_or_ge n G₀.length with hn | hn
  · rw [List.getElem?_append_left hn] at hg
    obtain ⟨a', d, fk, ha', hk, har, hpar, hty, hdk, hr'⟩ := hG n g hg
    refine ⟨a', d, fk, ha', getElem?_of_prefix ?_ hk, har, hpar, hty, hdk, hr'⟩
    simp only [globals, ← List.append_assoc, List.map_append]
    exact List.prefix_append _ _
  · obtain rfl : n = G₀.length := by
      have := (List.getElem?_eq_some_iff.mp hg).1
      simp only [List.length_append, List.length_singleton] at this
      omega
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero,
      Option.some.injEq] at hg
    subst hg
    have hk : (globals (defs₀ ++ [mkDefn 0 [] a u])).defs[lib.length + G₀.length]? =
        some (.language (mkDefn 0 [] a u)) := by
      simp [globals, ← hlen]
    have hkF : (globals defsF).defs[lib.length + G₀.length]? =
        some (.language (mkDefn 0 [] a u)) :=
      getElem?_of_prefix (by
        obtain ⟨t, ht⟩ := hpre
        exact ⟨t.map Internal.Definition.language, by simp [globals, ← ht]⟩) hk
    obtain ⟨fk, hdk⟩ := Internal.compiled_language hF hkF
    have hb := hr
    rw [← globals_take ((List.prefix_append _ _).trans hpre), hlen] at hb
    exact ⟨a, _, fk, ha, hk, rfl, rfl, PartialHorn.subst_nil a, hdk,
      Internal.rep_def (τ' := []) hF hkF hb (fun _ ↦ rfl) hdk⟩

/-- The step of a program's translation: the translation of a definition in the types of the
globals before it, appended to theirs. -/
def programStep (acc : Option (List Tree × List Defn)) (t : Kernel.Tree) :
    Option (List Tree × List Defn) := do
  let (gt, defs) ← acc
  let (A, u) ← term gt [] t
  pure (gt ++ [A], defs ++ [mkDefn 0 [] (← ty A) u])

/-- The step of the kernel's loading of a program: a definition's global, in the globals before
it, appended to them. -/
def loadStep (acc : Option (List Kernel.Glob)) (t : Kernel.Tree) : Option (List Kernel.Glob) := do
  let G ← acc
  let m ← Kernel.infer G [] t
  some (G ++ [⟨m.1, m.2 ()⟩])

/-- A program's translation is the fold of its step. -/
theorem program_eq (D : List Kernel.Tree) : program D = D.foldl programStep (some ([], [])) := rfl

/-- The kernel's loading of a program is the fold of its step. -/
theorem load_eq (D : List Kernel.Tree) : Kernel.load D = D.foldl loadStep (some []) := rfl

/-- The translation of definitions after a failure fails. -/
theorem foldl_programStep_none : ∀ D : List Kernel.Tree, D.foldl programStep none = none :=
  List.rec rfl fun _ _ ih ↦ ih

/-- The translation of definitions extends the definitions before them. -/
theorem foldl_programStep_prefix : ∀ (D : List Kernel.Tree) (gt₀ : List Tree) (defs₀ : List Defn)
    (gt : List Tree) (defs : List Defn),
    D.foldl programStep (some (gt₀, defs₀)) = some (gt, defs) → defs₀ <+: defs :=
  List.rec (fun _ _ _ _ h ↦ by
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact List.prefix_refl _)
    fun t D ih gt₀ defs₀ gt defs h ↦ by
      rw [List.foldl_cons] at h
      cases hs : programStep (some (gt₀, defs₀)) t with
      | none => rw [hs, foldl_programStep_none] at h; exact nomatch h
      | some p =>
        rw [hs] at h
        have hp := ih p.1 p.2 gt defs h
        simp only [programStep, Option.bind_eq_bind, Option.bind_some,
          Option.bind_eq_some_iff] at hs
        obtain ⟨⟨A, u⟩, -, hs⟩ := hs
        simp only [Option.pure_def, Option.some.injEq] at hs
        obtain ⟨a, -, rfl⟩ := hs
        exact (List.prefix_append _ _).trans hp

/-- The definitions of a program's translation represent, definition by definition, the globals
the kernel loads from it, whose types are those the translation records. -/
theorem rep_program (hF : compileDefs (globals defsF) = some ds)
    (hwf : PartialHorn.DefnsWF sig ds) :
    ∀ (D : List Kernel.Tree) (gt₀ : List Tree) (defs₀ : List Defn) (G₀ : List Kernel.Glob),
      gt₀ = G₀.map (·.1) → defs₀.length = G₀.length → GlobRep defs₀ ds G₀ →
      ∀ gt defs, D.foldl programStep (some (gt₀, defs₀)) = some (gt, defs) → defs <+: defsF →
        ∃ G, D.foldl loadStep (some G₀) = some G ∧ gt = G.map (·.1) ∧ GlobRep defs ds G :=
  List.rec (fun _ _ G₀ hgt _ hG gt defs h _ ↦ by
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact ⟨G₀, rfl, hgt, hG⟩)
    fun t D ih gt₀ defs₀ G₀ hgt hlen hG gt defs h hpre ↦ by
      rw [List.foldl_cons] at h
      cases hs : programStep (some (gt₀, defs₀)) t with
      | none => rw [hs, foldl_programStep_none] at h; exact nomatch h
      | some p =>
        rw [hs] at h
        have hp := foldl_programStep_prefix D p.1 p.2 gt defs h
        simp only [programStep, Option.bind_eq_bind, Option.bind_some,
          Option.bind_eq_some_iff] at hs
        obtain ⟨⟨A, u⟩, ht, hs⟩ := hs
        simp only [Option.pure_def, Option.some.injEq] at hs
        obtain ⟨a, ha, rfl⟩ := hs
        subst hgt
        obtain ⟨d, a', hd, ha', hr⟩ :=
          repC_term hF hwf hG t [] (ctxRep_nil (ds := ds) (globals defs₀)) ht
        obtain rfl : a' = a := Option.some.inj (ha'.symm.trans ha)
        obtain ⟨G, hG', hgt', hGr⟩ := ih (G₀.map (·.1) ++ [A]) (defs₀ ++ [mkDefn 0 [] a' u])
          (G₀ ++ [⟨A, d ()⟩]) (by simp) (by simp [hlen])
          (globRep_snoc hF hG hlen (hp.trans hpre) ha' hr) gt defs h hpre
        refine ⟨G, ?_, hgt', hGr⟩
        rw [List.foldl_cons]
        convert hG' using 2
        simp [loadStep, hd]

/-! The contexts of theorems. -/

/-- A representation of which every value has a representation. -/
def LTot {S A : Type} (R : S → A → Prop) : Prop := ∀ x, ∃ a, R x a

/-- A representation of which every representation represents a value. -/
def RTot {S A : Type} (R : S → A → Prop) : Prop := ∀ a, ∃ x, R x a

/-- A representation that represents each value at most once. -/
def LUni {S A : Type} (R : S → A → Prop) : Prop := ∀ x a b, R x a → R x b → a = b

/-- A representation each of whose representations represents at most one value. -/
def RUni {S A : Type} (R : S → A → Prop) : Prop := ∀ x y a, R x a → R y a → x = y

/-- Every value of a kernel type is represented. -/
abbrev LTotal (T : Kernel.Tree) : Prop := LTot (KRel T)

/-- A representation represents one value of a kernel type. -/
abbrev RUnique (T : Kernel.Tree) : Prop := RUni (KRel T)

/-- A kernel context with a translation is represented at the product of its types'
translations, with the environment of its projections, by a representation that represents each
of its values whose types' values are all represented. -/
theorem ctxRep_std (G : Globals) : ∀ (Γ : Kernel.Ctx) (Γ' : List Tree), Γ.mapM ty = some Γ' →
    ∃ (S A : Type) (R : S → A → Prop) (proj : S → Γ.den),
      CtxRep G ds Γ (Internal.ctxObj Γ') (Internal.stdEnv Γ') R proj ∧
        ((∀ T ∈ Γ, LTotal T) → ∀ e, ∃ s a, proj s = e ∧ R s a) :=
  List.rec (fun Γ' h ↦ by
      obtain rfl := Option.some.inj h
      exact ⟨Unit, Unit, Rep.unit, fun _ ↦ (), ctxRep_nil G,
        fun _ e ↦ ⟨(), (), rfl, trivial⟩⟩)
    fun T Γ₀ ih Γ' h ↦ by
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨a, ha, Γ₀', hΓ₀, rfl⟩ := h
      rcases Γ₀ with _ | ⟨B, Γ₁⟩
      · obtain rfl := Option.some.inj hΓ₀
        refine ⟨Kernel.Ty.den T, MTy T, KRel T, fun x ↦ (x, ()), ⟨objVal_ty' ha, ?_⟩, ?_⟩
        · rintro (_ | i) p hp
          · obtain rfl := (Option.some.inj hp).symm
            exact ⟨a, ha, Internal.repC_var (Internal.envRep_idt (objVal_ty' ha) (KRel T)) rfl⟩
          · exact nomatch hp
        · intro hT e
          obtain ⟨b, hb⟩ := hT T List.mem_cons_self e.1
          exact ⟨e.1, b, rfl, hb⟩
      · obtain ⟨S, A, R, proj, hR, htot⟩ := ih Γ₀' hΓ₀
        simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
          Option.some.injEq] at hΓ₀
        obtain ⟨b, -, Γ₁', -, rfl⟩ := hΓ₀
        refine ⟨S × Kernel.Ty.den T, A × MTy T, Rep.prod R (KRel T), fun s ↦ (s.2, proj s.1),
          ctxRep_cons hR ha, fun hT e ↦ ?_⟩
        obtain ⟨s, c, hs, hc⟩ := htot (fun T' hT' ↦ hT T' (List.mem_cons_of_mem T hT')) e.2
        obtain ⟨d, hd⟩ := hT T List.mem_cons_self e.1
        exact ⟨(s, e.1), (c, d), Prod.ext rfl hs, hc, hd⟩

/-! The translation of types is injective. -/

/-- The kernel type an object of the internal language translates, read from its outermost
operations: the rose-tree object the base type, and the terminal object, products, exponentials
and list objects the others. -/
def unty : Tree → Option Kernel.Tree :=
  RoseTree.elim fun l rs ↦ match l, rs with
    | 41, [_] => some Kernel.tT
    | 5, [] => some Kernel.tUnit
    | 7, [x, y] => do pure (Kernel.tProd (← x) (← y))
    | 23, [x, y] => do pure (Kernel.tArrow (← x) (← y))
    | 34, [x] => do pure (Kernel.tList (← x))
    | _, _ => none

/-- The kernel type of a product object. -/
theorem unty_prod (x y : Tree) :
    unty (prod x y) = (do pure (Kernel.tProd (← unty x) (← unty y))) := rfl

/-- The kernel type of an exponential object. -/
theorem unty_exp (x y : Tree) :
    unty (exp x y) = (do pure (Kernel.tArrow (← unty x) (← unty y))) := rfl

/-- The kernel type of a list object. -/
theorem unty_list (x : Tree) : unty (list x) = (do pure (Kernel.tList (← unty x))) := rfl

/-- The kernel type a type's translation translates is the type. -/
theorem unty_ty : ∀ (T : Kernel.Tree) {a : Tree}, ty T = some a → unty a = some T :=
  RoseTree.ind fun l cs ih a h ↦ by
    rw [ty, RoseTree.elim_node] at h
    split at h
    · rename_i hcs
      obtain rfl := List.map_eq_nil_iff.mp hcs
      obtain rfl := Option.some.inj h
      rfl
    · rename_i hcs
      obtain rfl := List.map_eq_nil_iff.mp hcs
      obtain rfl := Option.some.inj h
      rfl
    · rename_i hcs
      rcases cs with _ | ⟨c₀, _ | ⟨c₁, _ | ⟨c₂, cs⟩⟩⟩ <;> simp only [List.map_cons, List.map_nil,
        List.cons.injEq, reduceCtorEq, and_false] at hcs
      obtain ⟨rfl, rfl, -⟩ := hcs
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨x, hx, y, hy, rfl⟩ := h
      rw [node_two, unty_prod, ih c₀ (by simp) hx, ih c₁ (by simp) hy]
      rfl
    · rename_i hcs
      rcases cs with _ | ⟨c₀, _ | ⟨c₁, _ | ⟨c₂, cs⟩⟩⟩ <;> simp only [List.map_cons, List.map_nil,
        List.cons.injEq, reduceCtorEq, and_false] at hcs
      obtain ⟨rfl, rfl, -⟩ := hcs
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨x, hx, y, hy, rfl⟩ := h
      rw [node_two, unty_exp, ih c₀ (by simp) hx, ih c₁ (by simp) hy]
      rfl
    · rename_i hcs
      rcases cs with _ | ⟨c₀, _ | ⟨c₁, cs⟩⟩ <;> simp only [List.map_cons, List.map_nil,
        List.cons.injEq, reduceCtorEq, and_false] at hcs
      obtain ⟨rfl, -⟩ := hcs
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨x, hx, rfl⟩ := h
      rw [unty_list, ih c₀ (by simp) hx]
      exact congrArg some (RoseTree.node_eq_mk (Kernel.Label.tyList) [c₀] rfl ![c₀]
        fun i ↦ match i with | ⟨0, _⟩ => rfl).symm
    · exact nomatch h

/-- Kernel types with the same translation are equal. -/
theorem ty_inj {T₁ T₂ : Kernel.Tree} {a : Tree} (h₁ : ty T₁ = some a) (h₂ : ty T₂ = some a) :
    T₁ = T₂ :=
  Option.some.inj ((unty_ty T₁ h₁).symm.trans (unty_ty T₂ h₂))

/-! The kernel types whose representations are total and unique. -/

/-- Whether a kernel type is a type of data, built from trees and the unit type by products and
lists, and whether it is first order: built from those by products, lists and function types
whose domains are types of data. -/
def order : Kernel.Tree → Bool × Bool :=
  RoseTree.elim fun l rs ↦ match l, rs with
    | Kernel.Label.tyTree, [] | Kernel.Label.tyUnit, [] => (true, true)
    | Kernel.Label.tyProd, [x, y] => (x.1 && y.1, x.2 && y.2)
    | Kernel.Label.tyList, [x] => x
    | Kernel.Label.tyArrow, [x, y] => (false, x.1 && y.2)
    | _, _ => (false, false)

/-- A kernel type of first order. -/
def FirstOrder (T : Kernel.Tree) : Prop := (order T).2 = true

/-- Lists of values represent lists elementwise at most once when their elements do. -/
theorem forall₂_left_unique {α β : Type} {R : α → β → Prop}
    (h : ∀ x a b, R x a → R x b → a = b) :
    ∀ (l : List α) (a b : List β), List.Forall₂ R l a → List.Forall₂ R l b → a = b :=
  List.rec (fun a b ha hb ↦ by
      rw [List.forall₂_nil_left_iff.mp ha, List.forall₂_nil_left_iff.mp hb])
    fun x l ih a b ha hb ↦ by
      obtain ⟨a₀, as, h₀, hs, rfl⟩ := List.forall₂_cons_left_iff.mp ha
      obtain ⟨b₀, bs, h₀', hs', rfl⟩ := List.forall₂_cons_left_iff.mp hb
      rw [h x a₀ b₀ h₀ h₀', ih as bs hs hs']

/-- Lists of values are represented elementwise by at most one list when their elements are. -/
theorem forall₂_right_unique {α β : Type} {R : α → β → Prop}
    (h : ∀ x y a, R x a → R y a → x = y) :
    ∀ (l m : List α) (a : List β), List.Forall₂ R l a → List.Forall₂ R m a → l = m :=
  List.rec (fun m a ha hb ↦ by
      rw [List.forall₂_nil_left_iff.mp ha] at hb
      exact (List.forall₂_nil_right_iff.mp hb).symm)
    fun x l ih m a ha hb ↦ by
      obtain ⟨a₀, as, h₀, hs, rfl⟩ := List.forall₂_cons_left_iff.mp ha
      obtain ⟨y, ys, h₀', hs', rfl⟩ := List.forall₂_cons_right_iff.mp hb
      rw [h x y a₀ h₀ h₀', ih ys as hs hs']

/-- Lists of values are all represented elementwise when their elements are. -/
theorem forall₂_left_total {α β : Type} {R : α → β → Prop} (h : ∀ x, ∃ a, R x a) :
    ∀ l : List α, ∃ a, List.Forall₂ R l a :=
  List.rec ⟨[], .nil⟩ fun x _ ih ↦
    let ⟨a, ha⟩ := h x
    let ⟨as, has⟩ := ih
    ⟨a :: as, .cons ha has⟩

/-- Lists all represent lists elementwise when their elements do. -/
theorem forall₂_right_total {α β : Type} {R : α → β → Prop} (h : ∀ a, ∃ x, R x a) :
    ∀ a : List β, ∃ l, List.Forall₂ R l a :=
  List.rec ⟨[], .nil⟩ fun a _ ih ↦
    let ⟨x, hx⟩ := h a
    let ⟨l, hl⟩ := ih
    ⟨x :: l, .cons hx hl⟩

section Props

variable {S S' A A' : Type} {R : S → A → Prop} {R' : S' → A' → Prop}

/-- The representation of pairs is total and unique as its components' are. -/
theorem prod_props (h : LTot R ∧ RTot R ∧ LUni R ∧ RUni R)
    (h' : LTot R' ∧ RTot R' ∧ LUni R' ∧ RUni R') :
    LTot (Rep.prod R R') ∧ RTot (Rep.prod R R') ∧ LUni (Rep.prod R R') ∧ RUni (Rep.prod R R') :=
  ⟨fun x ↦ let ⟨a, ha⟩ := h.1 x.1; let ⟨b, hb⟩ := h'.1 x.2; ⟨(a, b), ha, hb⟩,
    fun a ↦ let ⟨x, hx⟩ := h.2.1 a.1; let ⟨y, hy⟩ := h'.2.1 a.2; ⟨(x, y), hx, hy⟩,
    fun _ _ _ ha hb ↦ Prod.ext (h.2.2.1 _ _ _ ha.1 hb.1) (h'.2.2.1 _ _ _ ha.2 hb.2),
    fun _ _ _ ha hb ↦ Prod.ext (h.2.2.2 _ _ _ ha.1 hb.1) (h'.2.2.2 _ _ _ ha.2 hb.2)⟩

/-- The representation of pairs is total on values and unique as its components' are. -/
theorem prod_props' (h : LTot R ∧ LUni R ∧ RUni R) (h' : LTot R' ∧ LUni R' ∧ RUni R') :
    LTot (Rep.prod R R') ∧ LUni (Rep.prod R R') ∧ RUni (Rep.prod R R') :=
  ⟨fun x ↦ let ⟨a, ha⟩ := h.1 x.1; let ⟨b, hb⟩ := h'.1 x.2; ⟨(a, b), ha, hb⟩,
    fun _ _ _ ha hb ↦ Prod.ext (h.2.1 _ _ _ ha.1 hb.1) (h'.2.1 _ _ _ ha.2 hb.2),
    fun _ _ _ ha hb ↦ Prod.ext (h.2.2 _ _ _ ha.1 hb.1) (h'.2.2 _ _ _ ha.2 hb.2)⟩

/-- The representation of lists is total and unique as its elements' is. -/
theorem list_props (h : LTot R ∧ RTot R ∧ LUni R ∧ RUni R) :
    LTot (Rep.list R) ∧ RTot (Rep.list R) ∧ LUni (Rep.list R) ∧ RUni (Rep.list R) :=
  ⟨forall₂_left_total h.1, forall₂_right_total h.2.1, forall₂_left_unique h.2.2.1,
    forall₂_right_unique h.2.2.2⟩

/-- The representation of lists is total on values and unique as its elements' is. -/
theorem list_props' (h : LTot R ∧ LUni R ∧ RUni R) :
    LTot (Rep.list R) ∧ LUni (Rep.list R) ∧ RUni (Rep.list R) :=
  ⟨forall₂_left_total h.1, forall₂_left_unique h.2.1, forall₂_right_unique h.2.2⟩

/-- The representation of functions by functional relations is total on functions and unique,
when the domain's representation is total and unique and the codomain's total on values and
unique. -/
theorem exp_props (h : LTot R ∧ RTot R ∧ LUni R ∧ RUni R) (h' : LTot R' ∧ LUni R' ∧ RUni R') :
    LTot (Rep.exp R R') ∧ LUni (Rep.exp R R') ∧ RUni (Rep.exp R R') := by
  obtain ⟨hl, hrt, -, hru⟩ := h
  obtain ⟨hl', hlu', hru'⟩ := h'
  refine ⟨fun f ↦ ?_, fun f φ ψ hφ hψ ↦ ?_, fun f g φ hf hg ↦ ?_⟩
  · refine ⟨⟨{p | ∃ x, R x p.1 ∧ R' (f x) p.2}, fun a ↦ ?_⟩, fun s a hs b ⟨x, hx, hb⟩ ↦ ?_⟩
    · obtain ⟨x, hx⟩ := hrt a
      obtain ⟨b, hb⟩ := hl' (f x)
      exact ⟨b, ⟨x, hx, hb⟩, fun b' ⟨x', hx', hb'⟩ ↦
        hlu' _ _ _ (hru x' x a hx' hx ▸ hb') hb⟩
    · exact hru x s a hx hs ▸ hb
  · refine FunRel.ext_of_le fun a b hab ↦ ?_
    obtain ⟨x, hx⟩ := hrt a
    obtain ⟨b', hb', -⟩ := ψ.functional a
    rw [hlu' _ _ _ (hφ x a hx b hab) (hψ x a hx b' hb')]
    exact hb'
  · funext x
    obtain ⟨a, ha⟩ := hl x
    obtain ⟨b, hb, -⟩ := φ.functional a
    exact hru' _ _ b (hf x a ha b hb) (hg x a ha b hb)

/-- The representation of kernel trees is total and unique. -/
theorem rose_props :
    LTot (Rep.rose RN) ∧ RTot (Rep.rose RN) ∧ LUni (Rep.rose RN) ∧ RUni (Rep.rose RN) :=
  ⟨fun t ↦ ⟨t.map ofNum, (rose_rn_iff _ _).mpr rfl⟩,
    fun a ↦ ⟨a.map rankB, (rose_rn_iff _ _).mpr (by
      rw [RoseTree.map_map]
      conv_lhs => rw [← RoseTree.map_id a]
      exact congrArg (RoseTree.map · a) (funext fun w ↦ (ofNum_rankB w).symm))⟩,
    fun _ _ _ ha hb ↦ ((rose_rn_iff _ _).mp ha).trans ((rose_rn_iff _ _).mp hb).symm,
    fun _ _ _ ha hb ↦ map_ofNum_inj.mp (((rose_rn_iff _ _).mp ha).symm.trans
      ((rose_rn_iff _ _).mp hb))⟩

/-- The representation of a type of data is total and unique, and that of a type of first order
total on values and unique. -/
theorem order_props : ∀ T : Kernel.Tree,
    ((order T).1 = true → LTot (KRel T) ∧ RTot (KRel T) ∧ LUni (KRel T) ∧ RUni (KRel T)) ∧
      ((order T).2 = true → LTot (KRel T) ∧ LUni (KRel T) ∧ RUni (KRel T)) :=
  RoseTree.ind fun l cs ih ↦ by
    rw [order, RoseTree.elim_node]
    rcases cs with _ | ⟨c₀, _ | ⟨c₁, _ | ⟨c₂, cs⟩⟩⟩
    · rcases l with _ | _ | l
      · exact ⟨fun _ ↦ rose_props, fun _ ↦ ⟨rose_props.1, rose_props.2.2⟩⟩
      · have hu : LTot (KRel (RoseTree.node 1 [])) ∧ RTot (KRel (RoseTree.node 1 [])) ∧
            LUni (KRel (RoseTree.node 1 [])) ∧ RUni (KRel (RoseTree.node 1 [])) :=
          ⟨fun _ ↦ ⟨(), trivial⟩, fun _ ↦ ⟨(), trivial⟩, fun _ _ _ _ _ ↦ rfl,
            fun _ _ _ _ _ ↦ rfl⟩
        exact ⟨fun _ ↦ hu, fun _ ↦ ⟨hu.1, hu.2.2⟩⟩
      · simp
    · rcases l with _ | _ | _ | _ | _ | l
      · simp
      · simp
      · simp
      · simp
      · exact ⟨fun h ↦ list_props ((ih c₀ (by simp)).1 h),
          fun h ↦ list_props' ((ih c₀ (by simp)).2 h)⟩
      · simp
    · rcases l with _ | _ | _ | _ | _ | l
      · simp
      · simp
      · refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
        · obtain ⟨h₀, h₁⟩ := Bool.and_eq_true_iff.mp h
          exact prod_props ((ih c₀ (by simp)).1 h₀) ((ih c₁ (by simp)).1 h₁)
        · obtain ⟨h₀, h₁⟩ := Bool.and_eq_true_iff.mp h
          exact prod_props' ((ih c₀ (by simp)).2 h₀) ((ih c₁ (by simp)).2 h₁)
      · refine ⟨fun h ↦ (Bool.false_ne_true h).elim, fun h ↦ ?_⟩
        obtain ⟨h₀, h₁⟩ := Bool.and_eq_true_iff.mp h
        exact exp_props ((ih c₀ (by simp)).1 h₀) ((ih c₁ (by simp)).2 h₁)
      · simp
      · simp
    · simp

end Props

/-! Soundness. -/

/-- The translations of a context's types are types. -/
theorem all_isTy_of_mapM {G : Globals} {n : ℕ} :
    ∀ (Γ : Kernel.Ctx) (Γ' : List Tree), Γ.mapM ty = some Γ' → Γ'.all (Internal.IsTy G n) = true :=
  List.rec (fun Γ' h ↦ by rw [← Option.some.inj h]; rfl) fun T Γ ih Γ' h ↦ by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨a, ha, Γ₀', hΓ, rfl⟩ := h
    rw [List.all_cons, (ty_spec (ds := []) (ρ := []) T ha).1, ih Γ₀' hΓ, Bool.and_self]

/-- The soundness of the translation: when the internal language's checker proves the
translation of a kernel theorem, in a development over a kernel program's translation, the
kernel's denotations of the theorem's sides have one type and agree at every value of its context
whose types' values are all represented, when that type's representations each represent one
value. -/
theorem translation_sound {D : List Kernel.Tree} {gt : List Tree} {defs : List Defn}
    (hprog : program D = some (gt, defs)) (hF : compileDefs (globals defs) = some ds)
    (hok : (globals defs).ok (ExtEnv.ofDefs ds) = true) {a : Metalogic.Thm} {th : Internal.Thm}
    (hth : thm gt a = some th) {decls : List Internal.Decl} {Gf : Globals}
    {Ef : Array Internal.Entry} (hdev : Internal.checkDev (globals defs) #[] decls = some (Gf, Ef))
    {F : List PartialHorn.Defn} (hFf : compileDefs Gf = some F)
    (hwfF : PartialHorn.DefnsWF sig F) {j : ℕ} (hj : Ef[j]? = some (.language th)) :
    ∃ G, Kernel.load D = some G ∧ ∃ T dl dr, Kernel.infer G a.ctx a.eqn.lhs = some ⟨T, dl⟩ ∧
      Kernel.infer G a.ctx a.eqn.rhs = some ⟨T, dr⟩ ∧
        ((∀ T' ∈ a.ctx, LTotal T') → RUnique T → ∀ e, dl e = dr e) := by
  have hle := Internal.le_of_checkDev decls hdev
  obtain ⟨ext', rfl⟩ := Internal.compileDefs_prefix hle hF hFf
  have hwf := PartialHorn.defnsWF_of_append ext' ds sig hwfF
  obtain ⟨G, hload, hgt, hG⟩ := rep_program (defsF := defs) hF hwf D [] [] [] rfl rfl
    (fun _ _ h ↦ nomatch h) gt defs (program_eq D ▸ hprog) (List.prefix_refl _)
  refine ⟨G, load_eq D ▸ hload, ?_⟩
  simp only [thm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hth
  obtain ⟨Γ', hΓ', ⟨Tl, l⟩, hl, ⟨Tr, r⟩, hr, rfl⟩ := hth
  obtain ⟨S, A, R, proj, hR, htot⟩ := ctxRep_std (ds := ds) (globals defs) a.ctx Γ' hΓ'
  subst hgt
  obtain ⟨dl, al, hdl, hal, fl, hfl, hrl⟩ := repC_term hF hwf hG a.eqn.lhs a.ctx hR hl
  obtain ⟨dr, ar, hdr, har, fr, hfr, hrr⟩ := repC_term hF hwf hG a.eqn.rhs a.ctx hR hr
  obtain ⟨f, g, B, hf, hg, hvalid⟩ := Internal.valid_unfoldAll_of_checkDev (pre := [])
    (by simp [globals]) (by simpa using hok) hF hdev hFf (by simpa using hwfF) hj rfl rfl
  obtain ⟨rfl, rfl⟩ :=
    Prod.mk.inj (Option.some.inj ((Internal.compile_mono hle _ _ _ _ hfl).symm.trans hf))
  obtain ⟨rfl, rfl⟩ :=
    Prod.mk.inj (Option.some.inj ((Internal.compile_mono hle _ _ _ _ hfr).symm.trans hg))
  obtain rfl := ty_inj hal har
  have hΓty := all_isTy_of_mapM (G := globals defs) (n := 0) a.ctx Γ' hΓ'
  have hdefs := fun k d (hd : (globals defs).defs[k]? = some d) ↦
    Internal.getElem?_sig_compileDefs (pre := []) (by simp [globals]) hF hd
  have hops : ∀ {s : Term} {r : Tree × Tree},
      Internal.compile (globals defs) 0 s (Internal.ctxObj Γ') (Internal.stdEnv Γ') = some r →
        PartialHorn.OpsBelow (sig.extendAll ds).length r.1 = true := fun hs ↦ by
    have := (Internal.compile_sortOf (defs := [] ++ ds) (Globals.wf_of_ok hok)
      (fun k p hp ↦ Internal.sortOf_prims_of_ok (by simpa using hok) hp) hdefs _ _ _ _ hs
      (Internal.sortOf_ctxObj hdefs Γ' hΓty) (Internal.sortOf_stdEnv hdefs Γ' hΓty)).1
    have h := PartialHorn.opsBelow_of_sortOf _ this
    rw [List.nil_append, PartialHorn.Theory.extendAll_sig] at h
    exact h
  refine ⟨Tl, dl, dr, hdl, hdr, fun hctx hu e ↦ ?_⟩
  have hv := hvalid relTopos.model relTopos.isModel
  rw [unfoldAll_eq, List.nil_append] at hv
  obtain ⟨w, hw₁, hw₂⟩ := hv [] rfl (fun _ h ↦ nomatch h)
  simp only [unfoldTerm_append ext' ds sig _ (hops hfl),
    unfoldTerm_append ext' ds sig _ (hops hfr)] at hw₁ hw₂
  obtain ⟨φ, hφ, hrφ⟩ := hrl
  obtain ⟨ψ, hψ, hrψ⟩ := hrr
  unfold ArrVal at hφ hψ
  have hφψ := Part.some_injective ((hφ.symm.trans hw₁).trans (hw₂.symm.trans hψ))
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at hφψ
  obtain ⟨-, h₁⟩ := Sigma.mk.inj hφψ
  obtain rfl : φ = ψ := eq_of_heq (Sigma.mk.inj (eq_of_heq h₁)).2
  obtain ⟨s, x, rfl, hsx⟩ := htot hctx e
  obtain ⟨b, hb, -⟩ := φ.functional x
  exact hu _ _ b (hrφ s x hsx b hb) (hrψ s x hsx b hb)

/-- The soundness of the translation for theorems of first order: when the internal language's
checker proves the translation of a kernel theorem whose context's types and equation's type are
of first order and whose left side has the equation's type, the theorem is valid in the globals
the kernel loads from the program. -/
theorem thm_valid {D : List Kernel.Tree} {gt : List Tree} {defs : List Defn}
    (hprog : program D = some (gt, defs)) (hF : compileDefs (globals defs) = some ds)
    (hok : (globals defs).ok (ExtEnv.ofDefs ds) = true) {a : Metalogic.Thm} {th : Internal.Thm}
    (hth : thm gt a = some th) {decls : List Internal.Decl} {Gf : Globals}
    {Ef : Array Internal.Entry} (hdev : Internal.checkDev (globals defs) #[] decls = some (Gf, Ef))
    {F : List PartialHorn.Defn} (hFf : compileDefs Gf = some F)
    (hwfF : PartialHorn.DefnsWF sig F) {j : ℕ} (hj : Ef[j]? = some (.language th))
    {G : List Kernel.Glob} (hload : Kernel.load D = some G)
    (htyped : Metalogic.typeOf G a.ctx a.eqn.lhs = some a.eqn.ty)
    (hctx : ∀ T ∈ a.ctx, FirstOrder T) (hT : FirstOrder a.eqn.ty) : a.Valid G := by
  obtain ⟨G', hG', T, dl, dr, hdl, hdr, hagree⟩ :=
    translation_sound hprog hF hok hth hdev hFf hwfF hj
  obtain rfl := Option.some.inj (hG'.symm.trans hload)
  rw [Metalogic.typeOf, hdl] at htyped
  obtain rfl : T = a.eqn.ty := Option.some.inj htyped
  exact ⟨dl, dr, hdl, hdr, fun e _ ↦ hagree (fun T' hT' ↦ ((order_props T').2 (hctx T' hT')).1)
    ((order_props _).2 hT).2.2 e⟩

end Geb.FreeTopos.Translation

end
