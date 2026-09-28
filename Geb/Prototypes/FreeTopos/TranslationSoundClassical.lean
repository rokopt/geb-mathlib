/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.TranslationSound
public import Geb.Prototypes.FreeTopos.UniqueChoiceClassical
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The translation of the computational core is sound, with choice

The soundness of the translation for every type
({name}`Geb.FreeTopos.Translation.thm_valid_of_uniqueChoice`) at the proof of unique choice from
{lit}`Classical.choice` ({name}`Geb.FreeTopos.uniqueChoice`). The module only combines the two, and
it is admitted to the axiom linter's allowlist ({lit}`GebMeta.classicalAllowedModules`) for that.

## Main statements

* {lit}`thm_valid_classical` — a kernel theorem whose translation the internal language's checker
  proves is valid.

## Tags

translation, kernel, soundness, unique choice
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Translation

open PartialHorn (Tree)
open Internal (Defn Globals compileDefs)

/-- The soundness of the translation, with {lit}`Classical.choice`: when the internal language's
checker proves the translation of a kernel theorem whose left side has the equation's type, in a
development over a kernel program's translation, the theorem is valid in the globals the kernel
loads from the program. -/
theorem thm_valid_classical {ds : List PartialHorn.Defn} {D : List Kernel.Tree} {gt : List Tree}
    {defs : List Defn} (hprog : program D = some (gt, defs))
    (hF : compileDefs (globals defs) = some ds)
    (hok : (globals defs).ok (ExtEnv.ofDefs ds) = true) {a : Metalogic.Thm} {th : Internal.Thm}
    (hth : thm gt a = some th) {decls : List Internal.Decl} {Gf : Globals}
    {Ef : Array Internal.Entry} (hdev : Internal.checkDev (globals defs) #[] decls = some (Gf, Ef))
    {F : List PartialHorn.Defn} (hFf : compileDefs Gf = some F)
    (hwfF : PartialHorn.DefnsWF sig F) {j : ℕ} (hj : Ef[j]? = some (.language th))
    {G : List Kernel.Glob} (hload : Kernel.load D = some G)
    (htyped : Metalogic.typeOf G a.ctx a.eqn.lhs = some a.eqn.ty) : a.Valid G :=
  thm_valid_of_uniqueChoice uniqueChoice hprog hF hok hth hdev hFf hwfF hj hload htyped

end Geb.FreeTopos.Translation

end
