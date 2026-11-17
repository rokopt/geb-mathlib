/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Certified.DatatypeFolds
public import GebTests.Prototypes.FreeTopos.Certified.DatatypeMirror
public import GebTests.Prototypes.CheckMirror

set_option doc.verso true in
/-!
# The passes succeed on the forms the expansion accepts

The soundness of a whole program of the datatype language's stage-1 compiler assumes that the
compiler's passes succeed on a program's forms ({lit}`DatatypePasses.PassFns.passes`): the
forms expand, their typing rejects none, the recognizers can be written, the reader reads the
result, and the kernel types the terms. The compiler computes those passes by the expansion of
a program ({lit}`Datatype.expandProgram`), which expands the forms, types them and erases
them, followed by the insertion of the recognizers, the reader and the kernel's typing of what
it reads, each applied to the result of the one before where that is present
({lit}`bootstrap/compile.geb`). Where each of those steps gives a result ({lit}`Accepts`), the
passes succeed: the expansion of a program gives a result only where the forms expand and their
typing's rejection is not labelled as a name, and the result is then the erased forms; and the
typing's rejection is the absent name wherever it is not labelled as a name, the typing's step
giving a state the absent name or a name and leaving a state that rejects as it is.

## Main definitions

* {lit}`Rej` — a state of the typing's run rejects no definition, or one by its name.
* {lit}`expanded` — the kernel forms the expansion of a program gives.
* {lit}`Accepts` — each step of the compiler from the expansion on gives a result.

## Main statements

* {lit}`rej_checkStep`, {lit}`rej_checkAll` — the typing's step and its run over a program's
  forms give states that reject no definition or one by its name.
* {lit}`expandProgram_just` — where the expansion of a program gives a result, the forms expand,
  their typing rejects none, and the result is the erased forms.
* {lit}`passes_of_accepts` — the passes succeed on the forms the compiler's steps accept.

## Tags

internal language, datatypes, kernel, mirror, compiler, test
-/

set_option doc.verso true

@[expose] public section

open GebMirror.DatatypeSoundness

namespace GebTests.Prototypes.FreeTopos.Certified.DatatypeEntry

open Geb Geb.Kernel
open GebTests.Prototypes.FreeTopos.Certified.DatatypePasses (Env PassFns)
open GebTests.Prototypes.FreeTopos.Certified.DatatypeFolds (foldr_run)
open GebTests.Prototypes.FreeTopos.Certified.DatatypeMirror (passFns)
open GebTests.Prototypes.CheckMirror (child_node children_node)

/-- A state of the typing's run rejects no definition, or rejects one by its name: its second
component is the absent name, or is labelled as a present one. -/
def Rej (s : Env × Tree) : Prop :=
  s.2 = «$547970696e672f4f4e616d652e6e6f7468696e67» ∨
    (Const.eq (Const.label s.2) (leaf 1)).label ≠ 0

/-- A conditional between two states that each reject no definition or one by its name is such
a state. -/
theorem Rej.ite {c : Prop} [Decidable c] {a b : Env × Tree} (ha : c → Rej a) (hb : ¬c → Rej b) :
    Rej (if c then a else b) := by
  split
  · exact ha ‹_›
  · exact hb ‹_›

/-- The typing's step on a form gives a state that rejects no definition or one by its name: a
state that rejects is left as it is, and any other is given the absent name or a name. -/
theorem rej_checkStep (s : Env × Tree) (f : Tree) : Rej («Typing.checkStep» s f) := by
  unfold «Typing.checkStep»
  refine Rej.ite (fun h ↦ Or.inr h) fun _ ↦ ?_
  repeat' refine Rej.ite (fun _ ↦ ?_) (fun _ ↦ ?_)
  all_goals first | exact Or.inl rfl | exact Or.inr Nat.one_ne_zero

/-- A run of the typing's step over forms, from a state that rejects no definition or one by
its name, ends in such a state. -/
theorem rej_foldl : ∀ (fs : List Tree) (s : Env × Tree), Rej s →
    Rej (fs.foldl «Typing.checkStep» s) :=
  List.rec (fun _ h ↦ h) fun f _ ih s _ ↦ ih _ (rej_checkStep s f)

/-- The typing's run over forms is the left fold of its step. -/
theorem checkRun_eq (s : Env × Tree) (fs : List Tree) :
    «Typing.checkRun» s fs = fs.foldl «Typing.checkStep» s :=
  foldr_run «Typing.checkStep» fs s

/-- The step of the typing of a program's forms: a template's instance is checked from the
state, which keeps its environment and takes the instance's rejection, unless the state
rejects; any other form takes the typing's step. -/
def allStep (s : Env × Tree) (f : Tree) : Env × Tree :=
  if (Const.eq (Const.label f) (leaf 15)).label ≠ 0 then
    if (Const.eq (Const.label s.2) (leaf 1)).label ≠ 0 then s
    else (s.1, («Typing.checkRun» s (Const.children f)).2)
  else «Typing.checkStep» s f

/-- The typing of a program's forms is the left fold of its step. -/
theorem checkAll_eq (s : Env × Tree) (fs : List Tree) :
    «Typing.checkAll» s fs = fs.foldl allStep s :=
  foldr_run allStep fs s

/-- The step of the typing of a program's forms, from a state that rejects no definition or
one by its name, gives such a state. -/
theorem rej_allStep {s : Env × Tree} (hs : Rej s) (f : Tree) : Rej (allStep s f) :=
  Rej.ite (fun _ ↦ Rej.ite (fun h ↦ Or.inr h) fun _ ↦ checkRun_eq s _ ▸ rej_foldl _ s hs)
    fun _ ↦ rej_checkStep s f

/-- The typing of a program's forms, from a state that rejects no definition or one by its
name, ends in such a state. -/
theorem rej_checkAll : ∀ (fs : List Tree) (s : Env × Tree), Rej s →
    Rej («Typing.checkAll» s fs) := fun fs s hs ↦
  checkAll_eq s fs ▸ (List.rec (motive := fun fs ↦ ∀ s, Rej s → Rej (fs.foldl allStep s))
    (fun _ h ↦ h) (fun f _ ih _ h ↦ ih _ (rej_allStep h f)) fs s hs)

/-- A tree is labelled as a present optional value. -/
abbrev IsJust (t : Tree) : Prop := (Const.eq (Const.label t) (leaf 1)).label ≠ 0

/-- The typing of a program's forms rejects none where its rejection is not labelled as a
name: the rejection is then the absent name. -/
theorem checkForms_nothing {fs : List Tree} (h : ¬IsJust («Typing.checkForms» fs)) :
    («Typing.checkAll» («Typing.env0», «$547970696e672f4f4e616d652e6e6f7468696e67») fs).2 =
      «$547970696e672f4f4e616d652e6e6f7468696e67» :=
  (rej_checkAll fs _ (Or.inl rfl)).resolve_right h

/-- The elements of the list of forms are the forms. -/
theorem elems_node (es : List Tree) : «Datatype.elems» (Const.node (leaf 2) es) = es :=
  (ite_eq_left
    (show (Const.eq (Const.label (Const.node (leaf 2) es)) (leaf 2)).label ≠ 0 from
      Nat.one_ne_zero)).trans (children_node 2 es)

/-- Where the expansion of checked forms gives a result, the forms expand, the typing's
rejection is not labelled as a name, and the result is the list of the erased forms. -/
theorem expandChecked_just {es : List Tree} (h : IsJust («Datatype.expandChecked» es)) :
    («Datatype.expandTyped» es).1.label ≠ 0 ∧
      ¬IsJust («Typing.checkForms» («Datatype.markersFirst» («Datatype.expandTyped» es).2)) ∧
      «Datatype.expandChecked» es = «$44617461747970652f4f54782e6a757374»
        («Typing.tList» («Datatype.kernelForms» («Datatype.expandTyped» es).2)) := by
  by_cases h₁ : («Datatype.expandTyped» es).1.label ≠ 0
  · by_cases h₂ :
        IsJust («Typing.checkForms» («Datatype.markersFirst» («Datatype.expandTyped» es).2))
    · have e : «Datatype.expandChecked» es = «$44617461747970652f4f54782e6e6f7468696e67» :=
        (ite_eq_left h₁).trans (ite_eq_left h₂)
      rw [e] at h
      exact absurd rfl h
    · exact ⟨h₁, h₂, (ite_eq_left h₁).trans (ite_eq_right h₂)⟩
  · have e : «Datatype.expandChecked» es = «$44617461747970652f4f54782e6e6f7468696e67» :=
      ite_eq_right h₁
    rw [e] at h
    exact absurd rfl h

/-- Where the expansion of a program gives a result, the expansion of its checked forms does,
and the result is the node of that one's elements. -/
theorem expandProgram_checked {es : List Tree} (h : IsJust («Datatype.expandProgram» es)) :
    IsJust («Datatype.expandChecked» es) ∧
      «Datatype.expandProgram» es = «Prelude.some» (Const.node (leaf 0) (Const.children
        (Const.lcase (Const.children («Datatype.expandChecked» es)) (leaf 0) fun x _ ↦ x))) := by
  by_cases h₀ : («Typing.Tx.member» (Const.node (leaf 2) es)).label ≠ 0
  · by_cases h₁ : IsJust («Datatype.expandChecked» («Datatype.elems» (Const.node (leaf 2) es)))
    · have e : «Datatype.expandProgram» es = «Prelude.some» (Const.node (leaf 0)
          (Const.children (Const.lcase (Const.children
            («Datatype.expandChecked» («Datatype.elems» (Const.node (leaf 2) es))))
            (leaf 0) fun x _ ↦ x))) :=
        (ite_eq_left h₀).trans (ite_eq_left h₁)
      rw [elems_node] at h₁ e
      exact ⟨h₁, e⟩
    · have e : «Datatype.expandProgram» es = «Prelude.none» :=
        (ite_eq_left h₀).trans (ite_eq_right h₁)
      rw [e] at h
      exact absurd rfl h
  · have e : «Datatype.expandProgram» es = «Prelude.none» := ite_eq_right h₀
    rw [e] at h
    exact absurd rfl h

/-- The kernel forms the expansion of a program gives: the children of its result. -/
def expanded (es : List Tree) : List Tree :=
  Const.children («Prelude.get» («Datatype.expandProgram» es))

/-- Where the expansion of a program gives a result, the forms expand, their typing rejects
none, and the result's kernel forms are the erased forms. -/
theorem expandProgram_just {es : List Tree} (h : IsJust («Datatype.expandProgram» es)) :
    («Datatype.expandTyped» es).1.label ≠ 0 ∧
      («Typing.checkAll» («Typing.env0», «$547970696e672f4f4e616d652e6e6f7468696e67»)
        («Datatype.markersFirst» («Datatype.expandTyped» es).2)).2 =
          «$547970696e672f4f4e616d652e6e6f7468696e67» ∧
      expanded es = «Datatype.kernelForms» («Datatype.expandTyped» es).2 := by
  obtain ⟨hc, e⟩ := expandProgram_checked h
  obtain ⟨h₁, h₂, ec⟩ := expandChecked_just hc
  refine ⟨h₁, checkForms_nothing h₂, ?_⟩
  rw [expanded, e, ec]
  change Const.children (Const.child (RoseTree.node 1 [RoseTree.node 0 (Const.children
    (Const.lcase (Const.children (RoseTree.node 1 [RoseTree.node 2 _])) (leaf 0) fun x _ ↦ x))])
    (leaf 0)) = _
  rw [children_node, child_node]
  exact (children_node 0 _).trans (children_node 2 _)

/-- Each step of the compiler from the expansion on gives a result at a program's forms: the
expansion of the program, the insertion of the recognizers in the kernel forms it gives, the
reader at the forms with their recognizers, and the kernel's typing of the terms the reader
reads. -/
structure Accepts (es : List Tree) : Prop where
  /-- The expansion of the program gives a result. -/
  expands : IsJust («Datatype.expandProgram» es)
  /-- The recognizers can be written. -/
  recognizes : IsJust («Recognize.insertRecognizers» (expanded es))
  /-- The reader reads the forms with their recognizers. -/
  reads : IsJust («Reader.readProgram»
    (Const.children («Prelude.get» («Recognize.insertRecognizers» (expanded es)))))
  /-- The kernel types the terms the reader reads. -/
  checks : IsJust («Check.checkProgram» (Const.children (Const.child («Prelude.get»
    («Reader.readProgram» (Const.children («Prelude.get»
      («Recognize.insertRecognizers» (expanded es)))))) (leaf 0))))

/-- The compiler's passes succeed on the forms each of its steps from the expansion on
accepts. -/
theorem passes_of_accepts {es : List Tree} (h : Accepts es) : ∀ p ∈ passFns.passes, p es := by
  obtain ⟨h₁, h₂, e⟩ := expandProgram_just h.expands
  have hr := h.recognizes
  have hd := h.reads
  have hk := h.checks
  rw [e] at hr hd hk
  exact List.forall_mem_cons.mpr ⟨h₁, List.forall_mem_cons.mpr ⟨h₂, List.forall_mem_cons.mpr
    ⟨hr, List.forall_mem_cons.mpr ⟨hd, List.forall_mem_cons.mpr
      ⟨hk, fun _ hm ↦ (List.not_mem_nil hm).elim⟩⟩⟩⟩⟩

end GebTests.Prototypes.FreeTopos.Certified.DatatypeEntry

end
