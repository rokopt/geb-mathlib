/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Certified.DatatypeTranslated
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The passes of the datatype language's compiler, as the kernel evaluates them

The soundness of a whole program of the datatype language's stage-1 compiler has, among its
hypotheses, that the compiler's passes succeed on the program's forms: the forms expand, their
typing rejects none, the recognizers can be written, the reader reads the result and the kernel
types its terms. Each is a formula of the internal language over references to the compilers'
definitions. The kernel loads those definitions as globals, and each formula represents
({name}`Geb.FreeTopos.Internal.RepC`) the proposition built the same way from the loaded
globals' values: that a tree the compilers compute has a label other than zero, or that two
trees they compute are equal. The representation is at the kernel's lists of trees, each
related to the list of trees of bitstrings of the same shape
({name}`Geb.FreeTopos.Translation.KRel`).

## Main definitions

* {lit}`PassFns` — the values of the compilers' definitions the passes call.
* {lit}`PassFns.passes` — the passes' successes at a program's forms, as those values compute
  them.
* {lit}`passHyps` — the formulas of the passes' successes.

## Main statements

* {lit}`exists_passFns` — the loaded globals give the values.
* {lit}`passes_rep` — the formulas represent the passes' successes.

## References

* {citeKey}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, datatypes, kernel, translation, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified.DatatypePasses

open Geb Geb.FreeTopos Geb.FreeTopos.Translation Geb.FreeTopos.Tactics
open GebTests.Prototypes.FreeTopos.Datatypes
open GebTests.Prototypes.FreeTopos.Weakening (Prog)
open GebTests.Prototypes.FreeTopos.Normalization (Defs pc truth)
open GebTests.Prototypes.FreeTopos.Certified.DatatypeAccepted (envTy passGlobals passGlobalsTyped)
open GebTests.Prototypes.FreeTopos.Certified.DatatypeTranslated
open Internal (Term RepC)
open Kernel (tT tList tProd tArrow)
open Sorts

/-- The values of the typing environment's kernel type. -/
abbrev Env : Type :=
  List Kernel.Tree × List Kernel.Tree × List Kernel.Tree × List Kernel.Tree × List Kernel.Tree ×
    List Kernel.Tree

/-- The values of the compilers' definitions the passes call. -/
structure PassFns where
  /-- The expansion of a program's forms with their datatypes: whether it succeeds, and the
  typed forms. -/
  expandTyped : List Kernel.Tree → Kernel.Tree × List Kernel.Tree
  /-- The absence of a rejected definition's name. -/
  nothing : Kernel.Tree
  /-- The typing of forms from an environment and a rejection. -/
  checkAll : Env × Kernel.Tree → List Kernel.Tree → Env × Kernel.Tree
  /-- The typing environment before any form. -/
  env0 : Env
  /-- The typed forms with their markers first. -/
  markersFirst : List Kernel.Tree → List Kernel.Tree
  /-- The kernel forms with the recognizers they refer to, when those can be written. -/
  insertRecognizers : List Kernel.Tree → Kernel.Tree
  /-- The erasure of typed forms to kernel forms. -/
  kernelForms : List Kernel.Tree → List Kernel.Tree
  /-- The reader's reading of a program's forms, when it reads them. -/
  readProgram : List Kernel.Tree → Kernel.Tree
  /-- The value of an optional tree that is present. -/
  get : Kernel.Tree → Kernel.Tree
  /-- Whether an optional tree is present. -/
  isSome : Kernel.Tree → Kernel.Tree
  /-- The kernel's typing of a program's terms, when it types them. -/
  checkProgram : List Kernel.Tree → Kernel.Tree

namespace PassFns

/-- The values are those of the globals the kernel loads for the definitions' names. -/
structure Loaded (f : PassFns) (Gk : List Kernel.Glob) (idx : String → ℕ) : Prop where
  /-- The expansion's. -/
  expandTyped : DatatypeTranslated.Loaded Gk idx "Datatype.expandTyped"
    (tArrow (tList tT) (tProd tT (tList tT))) f.expandTyped
  /-- The absent name's. -/
  nothing : DatatypeTranslated.Loaded Gk idx "Typing/OName.nothing" tT f.nothing
  /-- The typing's. -/
  checkAll : DatatypeTranslated.Loaded Gk idx "Typing.checkAll"
    (tArrow (tProd envTy tT) (tArrow (tList tT) (tProd envTy tT))) f.checkAll
  /-- The first environment's. -/
  env0 : DatatypeTranslated.Loaded Gk idx "Typing.env0" envTy f.env0
  /-- The markers' ordering's. -/
  markersFirst : DatatypeTranslated.Loaded Gk idx "Datatype.markersFirst"
    (tArrow (tList tT) (tList tT)) f.markersFirst
  /-- The recognizers' insertion's. -/
  insertRecognizers : DatatypeTranslated.Loaded Gk idx "Recognize.insertRecognizers"
    (tArrow (tList tT) tT) f.insertRecognizers
  /-- The erasure's. -/
  kernelForms : DatatypeTranslated.Loaded Gk idx "Datatype.kernelForms"
    (tArrow (tList tT) (tList tT)) f.kernelForms
  /-- The reader's. -/
  readProgram : DatatypeTranslated.Loaded Gk idx "Reader.readProgram" (tArrow (tList tT) tT)
    f.readProgram
  /-- The present value's. -/
  get : DatatypeTranslated.Loaded Gk idx "Prelude.get" (tArrow tT tT) f.get
  /-- The presence test's. -/
  isSome : DatatypeTranslated.Loaded Gk idx "Prelude.isSome" (tArrow tT tT) f.isSome
  /-- The kernel's typing's. -/
  checkProgram : DatatypeTranslated.Loaded Gk idx "Check.checkProgram" (tArrow (tList tT) tT)
    f.checkProgram

/-- The typing of a program's typed forms, their markers first, from the first environment and
no rejection: the environment it ends in, and the rejection. -/
def run (f : PassFns) (ks : List Kernel.Tree) : Env × Kernel.Tree :=
  f.checkAll (f.env0, f.nothing) (f.markersFirst (f.expandTyped ks).2)

/-- The kernel forms of a program's typed forms with their recognizers, when those can be
written. -/
def recognized (f : PassFns) (ks : List Kernel.Tree) : Kernel.Tree :=
  f.insertRecognizers (f.kernelForms (f.expandTyped ks).2)

/-- The reader's reading of the kernel forms with their recognizers, when it reads them. -/
def read (f : PassFns) (ks : List Kernel.Tree) : Kernel.Tree :=
  f.readProgram (f.get (f.recognized ks)).children

/-- The terms the reader reads. -/
def terms (f : PassFns) (ks : List Kernel.Tree) : List Kernel.Tree :=
  (Kernel.Const.child (f.get (f.read ks)) (Kernel.leaf 0)).children

/-- The passes' successes at a program's forms: the forms expand, their typing rejects none,
the recognizers can be written, the reader reads the result, and the kernel types the terms. -/
def passes (f : PassFns) : List (List Kernel.Tree → Prop) :=
  [fun ks ↦ (f.expandTyped ks).1.label ≠ 0, fun ks ↦ (f.run ks).2 = f.nothing,
    fun ks ↦ (f.isSome (f.recognized ks)).label ≠ 0, fun ks ↦ (f.isSome (f.read ks)).label ≠ 0,
    fun ks ↦ (f.isSome (f.checkProgram (f.terms ks))).label ≠ 0]

end PassFns

/-- The formulas of the passes' successes at a program's forms, the variable of the context:
those the soundness of a whole program has among its hypotheses. -/
def passHyps (P : Prog) : Option (List Term) := do
  let o := P.o
  let childT ← primT Kernel.Prim.child
  let isSomeT (t : Term) : Term := truth o (pc P "Prelude.isSome" [t])
  let get (t : Term) : Term := pc P "Prelude.get" [t]
  let kids (t : Term) : Term := call D.children [] [t]
  let ch (t : Term) (i : ℕ) : Term := apps childT [t, leafT (numeral i)]
  let x := pc P "Datatype.expandTyped" [v 0]
  let ts := Term.snd x
  let nothing := pc P "Typing/OName.nothing" []
  let run := pc P "Typing.checkAll" [Term.pair (pc P "Typing.env0" []) nothing,
    pc P "Datatype.markersFirst" [ts]]
  let r := pc P "Recognize.insertRecognizers" [pc P "Datatype.kernelForms" [ts]]
  let b := pc P "Reader.readProgram" [kids (get r)]
  let terms := kids (ch (get b) 0)
  pure [truth o (Term.fst x), Term.eq (Term.snd run) nothing, isSomeT r, isSomeT b,
    isSomeT (pc P "Check.checkProgram" [terms])]

variable {PST : Prog × Defs × Defs3}

/-- The loaded globals give the values of the compilers' definitions the passes call, each at
the kernel type the evaluator checked ({name}`DatatypeAccepted.passGlobalsTyped`). -/
theorem exists_passFns (L : Translated PST) : ∃ f : PassFns, f.Loaded L.Gk PST.1.idx := by
  have m : ∀ (i : ℕ) {name : String} {T : Kernel.Tree}, passGlobals[i]? = some (name, T) →
      ∃ f, DatatypeTranslated.Loaded L.Gk PST.1.idx name T f := by
    intro _ _ _ hm
    exact L.loaded passGlobalsTyped (List.mem_of_getElem? hm)
  obtain ⟨f₁, h₁⟩ := m 0 rfl
  obtain ⟨f₂, h₂⟩ := m 1 rfl
  obtain ⟨f₃, h₃⟩ := m 2 rfl
  obtain ⟨f₄, h₄⟩ := m 3 rfl
  obtain ⟨f₅, h₅⟩ := m 4 rfl
  obtain ⟨f₆, h₆⟩ := m 5 rfl
  obtain ⟨f₇, h₇⟩ := m 6 rfl
  obtain ⟨f₈, h₈⟩ := m 7 rfl
  obtain ⟨f₉, h₉⟩ := m 8 rfl
  obtain ⟨f₁₀, h₁₀⟩ := m 9 rfl
  obtain ⟨f₁₁, h₁₁⟩ := m 10 rfl
  exact ⟨⟨f₁, f₂, f₃, f₄, f₅, f₆, f₇, f₈, f₉, f₁₀, f₁₁⟩,
    ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁⟩⟩

section Readings

variable (L : Translated PST) {f : PassFns}

/-- The representation of a term in the context of a program's forms, over the extended
program's constants, as a function of the kernel's list of forms into a kernel type. -/
abbrev RepF (L : Translated PST) (u : Term) (T : Kernel.Tree)
    (F : List Kernel.Tree → Kernel.Ty.den T) : Prop :=
  RepK PST.1.G (L.cds₀ ++ L.ext) [list treeTy] (KRel (tList tT)) u T F

/-- A reference to a named definition represents the value of its loaded global. -/
theorem repF_pc₀ {name : String} {T : Kernel.Tree} {g : Kernel.Ty.den T}
    (hg : DatatypeTranslated.Loaded L.Gk PST.1.idx name T g) :
    RepF L (pc PST.1 name []) T fun _ ↦ g := by
  obtain ⟨n, hn, hG⟩ := hg
  have h := repK_global (R := KRel (tList tT)) L.ctx L.rep hG
  rw [← hn] at h
  exact h

/-- The application of a named definition represents the application of its loaded global's
value. -/
theorem repF_pc₁ {name : String} {B C : Kernel.Tree} {g : Kernel.Ty.den B → Kernel.Ty.den C}
    (hg : DatatypeTranslated.Loaded L.Gk PST.1.idx name (tArrow B C) g) {u : Term}
    {F : List Kernel.Tree → Kernel.Ty.den B} (hu : RepF L u B F) :
    RepF L (pc PST.1 name [u]) C fun ks ↦ g (F ks) :=
  repK_app (repF_pc₀ L hg) hu

/-- The application of a named definition to two arguments represents that of its loaded
global's value. -/
theorem repF_pc₂ {name : String} {B C E : Kernel.Tree}
    {g : Kernel.Ty.den B → Kernel.Ty.den C → Kernel.Ty.den E}
    (hg : DatatypeTranslated.Loaded L.Gk PST.1.idx name (tArrow B (tArrow C E)) g) {u w : Term}
    {F : List Kernel.Tree → Kernel.Ty.den B} {F' : List Kernel.Tree → Kernel.Ty.den C}
    (hu : RepF L u B F) (hw : RepF L w C F') :
    RepF L (pc PST.1 name [u, w]) E fun ks ↦ g (F ks) (F' ks) :=
  repK_app (repK_app (repF_pc₀ L hg) hu) hw

/-- The formulas of the passes' successes represent the passes' successes, as the loaded
globals' values compute them, at the kernel's lists of trees. -/
theorem passes_rep (h : extended3 = some PST) (hf : f.Loaded L.Gk PST.1.idx) {hs : List Term}
    (hp : passHyps PST.1 = some hs) :
    List.Forall₂ (fun (t : Term) (F : List Kernel.Tree → Prop) ↦
      RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] t (Internal.ctxObj [list treeTy])
        (Internal.stdEnv [list treeTy]) omega (KRel (tList tT)) Rep.prop F) hs f.passes := by
  have hlog := DatatypeAccepted.hasLogic h
  have hE := L.ctx
  obtain rfl : _ = hs := Option.some.inj hp
  -- the forms, their expansion and the typed forms
  have hv : RepF L (v 0) (tList tT) id := repK_var₀ rfl
  have hx := repF_pc₁ L hf.expandTyped hv
  have hts := repK_snd hx
  -- the typing
  have hno := repF_pc₀ L hf.nothing
  have hrun := repF_pc₂ L hf.checkAll (repK_pair (repF_pc₀ L hf.env0) hno)
    (repF_pc₁ L hf.markersFirst hts)
  -- the recognizers, the reading and the terms
  have hr := repF_pc₁ L hf.insertRecognizers (repF_pc₁ L hf.kernelForms hts)
  have hb := repF_pc₁ L hf.readProgram (repK_children hE (repF_pc₁ L hf.get hr))
  have hchild : RepF L _ (tArrow tT (tArrow tT tT)) fun _ ↦ Kernel.Const.child :=
    repK_prim hE (k := Kernel.Prim.child) (g := ⟨tArrow tT (tArrow tT tT), Kernel.Const.child⟩)
      rfl rfl
  have hterms := repK_children hE
    (repK_app (repK_app hchild (repF_pc₁ L hf.get hb)) (repK_quote hE (Kernel.leaf 0)))
  exact .cons (repC_test hE hlog (repK_fst hx))
    (.cons (repC_eqK (T := tT) rfl (repK_snd hrun) hno)
      (.cons (repC_test hE hlog (repF_pc₁ L hf.isSome hr))
        (.cons (repC_test hE hlog (repF_pc₁ L hf.isSome hb))
          (.cons (repC_test hE hlog (repF_pc₁ L hf.isSome (repF_pc₁ L hf.checkProgram hterms)))
            .nil))))

end Readings

end GebTests.Prototypes.FreeTopos.Certified.DatatypePasses

end
