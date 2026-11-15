/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.TranslationExtension
public import GebTests.Prototypes.FreeTopos.Certified.DatatypeAccepted

set_option doc.verso true in
/-!
# The constants of the datatype language's soundness extend the translated program's

The program the datatype language's soundness is stated in is the translation of the compilers'
kernel program extended by the connectives', the fundamental lemma's and the datatype language's
definitions. Its constants extend those of the translation alone
({name}`Geb.FreeTopos.Translation.globals`): the same primitive arrows before the natural
numbers', and the translated definitions before the others. The translated definitions
represent the globals the kernel loads from the compilers' program, so a reference to a named
definition of the program represents the value of a loaded global, at the kernel type the
translation records for it.

## Main definitions

* {lit}`Translated` — the compilers' program as bundled, translated and loaded, with what
  relates it to the extended program.
* {lit}`Loaded` — a named definition's loaded global has a kernel type and a value of it.

## Main statements

* {lit}`translated_le` — the translation's constants are among the extended program's.
* {lit}`translated` — the extended program has the translated and loaded program.
* {lit}`Translated.loaded` — a named definition of an evaluated kernel type is loaded at it.

## Tags

internal language, translation, datatypes, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified.DatatypeTranslated

open Geb Geb.FreeTopos Geb.FreeTopos.Translation GebTests.Prototypes.FreeTopos.Datatypes
open GebTests.Prototypes.FreeTopos.Weakening (Prog)
open GebTests.Prototypes.FreeTopos.Normalization (Defs)
open scoped FinEnum

/-- The constants of a translated program with the connectives extend the translation's, and
its names' indices are those given. -/
theorem prog_le {ds : List (List Char × PartialHorn.Tree)} {idx : String → ℕ} {P : Prog}
    (h : Weakening.prog? ds idx = some P) :
    ∃ gt defs, program (ds.map Prod.snd) = some (gt, defs) ∧ (globals defs).Le P.G ∧
      P.o = lib.length + defs.length ∧ P.idx = idx := by
  simp only [Weakening.prog?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨⟨gt, defs⟩, hp, rfl⟩ := h
  refine ⟨gt, defs, hp, ⟨List.prefix_refl _, rfl, ?_⟩, rfl, rfl⟩
  simp only [globals, List.map_append]
  exact (List.prefix_append _ _)

/-- The constants of the program extended for the fundamental lemma extend the program's, with
the same names' indices. -/
theorem extend_le {P P' : Prog} {S : Defs} (h : Normalization.extend P = some (P', S)) :
    P.G.Le P'.G ∧ P'.o = P.o ∧ P'.idx = P.idx := by
  simp only [Normalization.extend, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨_, -, _, -, _, -, _, -, rfl, -⟩ := h
  exact ⟨⟨List.prefix_append _ _, rfl, List.prefix_append _ _⟩, rfl, rfl⟩

/-- The constants of the program extended for the datatype language's soundness extend the
program's, with the same names' indices. -/
theorem extend3_le {P P' : Prog} {S : Defs} {T : Defs3} (h : extend3 P S = some (P', T)) :
    P.G.Le P'.G ∧ P'.o = P.o ∧ P'.idx = P.idx := by
  unfold extend3 at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, -, _, -, _, -, _, -, rfl, -⟩ := h
    exact ⟨⟨List.prefix_refl _, rfl, List.prefix_append _ _⟩, rfl, rfl⟩
  · exact nomatch h

/-- The constants of the program the datatype language's soundness is stated in extend those
of the translation of the bundled compilers' program, whose definitions come before the
connectives', and its names' indices are the bundled definitions'. -/
theorem translated_le {PST : Prog × Defs × Defs3} (h : extended3 = some PST) :
    ∃ ds gt defs, Weakening.bundled Geb.Kernel.Stage0Tests.bundler.toList programText.toList =
        some ds ∧ program (ds.map Prod.snd) = some (gt, defs) ∧ (globals defs).Le PST.1.G ∧
      PST.1.o = lib.length + defs.length ∧
      PST.1.idx = fun name ↦ (Weakening.defIndex ds name.toList).getD 0 := by
  simp only [extended3, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨ds, hds, ⟨P, S⟩, hPS, ⟨P3, T⟩, h3, rfl⟩ := h
  simp only [Normalization.extendedOf, Option.bind_eq_bind, Option.bind_eq_some_iff] at hPS
  obtain ⟨P0, hP0, hext⟩ := hPS
  obtain ⟨gt, defs, hp, hle0, ho0, hi0⟩ := prog_le hP0
  obtain ⟨hle1, ho1, hi1⟩ := extend_le hext
  obtain ⟨hle3, ho3, hi3⟩ := extend3_le h3
  exact ⟨ds, gt, defs, hds, hp, (hle0.trans hle1).trans hle3, by rw [ho3, ho1, ho0],
    by rw [hi3, hi1, hi0]⟩

/-- The compilers' program as bundled, translated and loaded by the kernel, with what relates it
to the program the datatype language's soundness is stated in: that program's constants extend
the translation's, its names' indices are the bundled definitions', and the translated
definitions represent the loaded globals, whose types are those the translation records. -/
structure Translated (PST : Prog × Defs × Defs3) where
  /-- The bundled definitions, each with its name. -/
  ds : List (List Char × PartialHorn.Tree)
  /-- The kernel types of the definitions. -/
  gt : List PartialHorn.Tree
  /-- The translated definitions. -/
  defs : List Internal.Defn
  /-- The definitions the translation's constants compile to. -/
  cds₀ : List PartialHorn.Defn
  /-- The further definitions the extended program's constants compile to. -/
  ext : List PartialHorn.Defn
  /-- The globals the kernel loads. -/
  Gk : List Kernel.Glob
  /-- The program bundles. -/
  bundled : Weakening.bundled Geb.Kernel.Stage0Tests.bundler.toList programText.toList = some ds
  /-- The program translates. -/
  program : program (ds.map Prod.snd) = some (gt, defs)
  /-- The connectives' definitions follow the translation's. -/
  o : PST.1.o = lib.length + defs.length
  /-- The names' indices are the bundled definitions'. -/
  idx : PST.1.idx = fun name ↦ (Weakening.defIndex ds name.toList).getD 0
  /-- The kernel loads the program. -/
  load : Kernel.load (ds.map Prod.snd) = some Gk
  /-- The loaded globals' types are those the translation records. -/
  types : gt = Gk.map (·.1)
  /-- The translated definitions represent the loaded globals. -/
  rep : GlobRep defs cds₀ Gk
  /-- The extended program's constants extend the translation's, in the context of a list of
  trees. -/
  ctx : ExtCtx defs cds₀ ext PST.1.G [list treeTy] (MTy (Kernel.tList Kernel.tT))

/-- The program the datatype language's soundness is stated in has the compilers' program as
bundled, translated and loaded: the translated definitions represent the globals the kernel
loads from it ({name}`Geb.FreeTopos.Translation.rep_program`), and are, compiled, the first of
the definitions the soundness's constants compile to. -/
theorem translated {PST : Prog × Defs × Defs3} (h : extended3 = some PST) :
    Nonempty (Translated PST) := by
  obtain ⟨ds, gt, defs, hds, hp, hle, ho, hidx⟩ := translated_le h
  have hacc : (globals defs).accepted = true := by
    have ha := DatatypeAccepted.translatedAccepted
    simp only [DatatypeAccepted.translatedGlobals, hds, hp, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def] at ha
    exact ha
  obtain ⟨cds₀, hc₀, -, hok₀, hwf₀⟩ := Internal.Globals.of_accepted hacc
  obtain ⟨cds, hc, -, -, hwf⟩ := Internal.Globals.of_accepted (DatatypeAccepted.accepted h)
  obtain ⟨ext, rfl⟩ := Internal.compileDefs_prefix hle hc₀ hc
  obtain ⟨Gk, hload, hgt, hG⟩ := rep_program (defsF := defs) hc₀ hwf₀ (ds.map Prod.snd) [] [] []
    rfl rfl (fun _ _ hn ↦ nomatch hn) gt defs (program_eq _ ▸ hp) (List.prefix_refl _)
  have hty : ty (Kernel.tList Kernel.tT) = some (list treeTy) := rfl
  exact ⟨ds, gt, defs, cds₀, ext, Gk, hds, hp, ho, hidx, load_eq _ ▸ hload, hgt, hG, hle,
    by simpa using hok₀, hc₀, hc, hwf,
    by simp [(ty_spec (G := globals defs) (n := 0) (ρ := []) (ds := cds₀) _ hty).1],
    objVal_ty' hty, objVal_ty' hty⟩

/-- A named definition's loaded global has a kernel type and a value of it: the name's index
is that of a translated definition, and the global the kernel loads for it is the value at the
type. -/
def Loaded (Gk : List Kernel.Glob) (idx : String → ℕ) (name : String) (T : Kernel.Tree)
    (f : Kernel.Ty.den T) : Prop :=
  ∃ n, idx name = lib.length + n ∧ Gk[n]? = some ⟨T, f⟩

/-- A named definition among those whose kernel types the evaluator checked
({name}`DatatypeAccepted.typedIn`) is loaded at its type. -/
theorem Translated.loaded {PST : Prog × Defs × Defs3} (L : Translated PST)
    {l : List (String × Kernel.Tree)}
    (hl : DatatypeAccepted.typedIn DatatypeAccepted.bundledTypes l = true) {name : String}
    {T : Kernel.Tree} (hm : (name, T) ∈ l) : ∃ f, Loaded L.Gk PST.1.idx name T f := by
  have hb : DatatypeAccepted.bundledTypes = some (L.ds, L.gt) := by
    simp only [DatatypeAccepted.bundledTypes, L.bundled, L.program, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def]
  rw [hb] at hl
  have hp := List.all_eq_true.mp hl (name, T) hm
  split at hp
  · next i hi =>
    have hgt : (L.Gk.map (·.1))[i]? = some T := by
      rw [← L.types]
      exact of_decide_eq_true hp
    rw [List.getElem?_map] at hgt
    obtain ⟨⟨T', f⟩, hg, rfl⟩ := Option.map_eq_some_iff.mp hgt
    exact ⟨f, i, by simp [L.idx, Weakening.defIndex, hi], hg⟩
  · exact nomatch hp

end GebTests.Prototypes.FreeTopos.Certified.DatatypeTranslated

end
