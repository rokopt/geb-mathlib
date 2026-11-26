/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Lean.Meta.Tactic.Simp.RegisterCommand
meta import Lean.Meta.Tactic.Simp.Attr
public meta import Lean.Elab.Command -- shake: keep

set_option doc.verso true in
/-!
# The equations of the templates' instances in the mirror

The bootstrap compiler emits a definition with type parameters once at each list of arguments.
Its name spells the application to those types, and
{lit}`GebTests.Prototypes.FreeTopos.Agreement.Templates` states each such definition once as a Lean
function. The command {lit}`template_equations` declares, for each copy among the constants of a
namespace, its equation with that function, closed by reflexivity, as a simp lemma, also of the
set {lit}`template`, the set in which the agreement proofs collect the equations of definitions
with the forms the proofs reason about. The module holds elaboration code alone, and
{lit}`GebMeta.classicalAllowedModules` admits it as it admits the commands of
{lit}`GebTests.Prototypes.ProgramCommand`.

## Main definitions

* {lit}`template` — the simp set.
* {lit}`template_equations` — the equations of a namespace's instances with the templates'
  functions.

## Tags

template, module, agreement, mirror, command
-/

set_option doc.verso true

public section

namespace GebTests.Prototypes.FreeTopos.Agreement.TemplateEquations

/-- The simp set of the equations of the templates' instances with the functions of
{lit}`GebTests.Prototypes.FreeTopos.Agreement.Templates`. -/
register_simp_attr template

private meta def nameBytes : List Char → Option (List UInt8)
  | [] => some []
  | a :: b :: rest => do
    guard (a.isHexDigit && b.isHexDigit)
    let byte ← Lean.Syntax.decodeNatLitVal? (String.ofList ['0', 'x', a, b])
    return byte.toUInt8 :: (← nameBytes rest)
  | [_] => none

open Lean Elab Command Meta in
/-- Register each erased instance of a generic bootstrap function whose type matches its
representative in {lit}`Templates`. The emitted name encodes the application to its types. -/
elab "template_equations " ns:ident : command => do
  let ns := ns.getId
  let here := `GebTests.Prototypes.FreeTopos.Agreement.Templates
  let fns := ["single", "length", "append", "reverse", "tail", "drop", "atOr", "nothing", "just",
    "isJust", "fromMaybe", "nthOf", "allJust", "all", "any", "isEmpty", "take", "map", "l2", "l3",
    "l4", "l5", "l6", "res", "bad", "ok", "pure", "fail", "orElse", "bind"]
  let cands := (← getEnv).constants.fold (init := #[]) fun acc c _ ↦
    match c with
    | .str p s =>
      if p == ns && s.startsWith "$28" then
        let original := (nameBytes (s.toList.drop 1)).bind fun bs ↦
          String.fromUTF8? ⟨bs.toArray⟩
        original.elim acc fun name ↦ acc.push (c, name)
      else acc
    | _ => acc
  for (c, s) in cands.qsort (fun a b ↦ a.2 < b.2) do
    let head := ((s.drop 1).takeWhile (· != ' ')).toString
    let parts := head.splitOn "."
    unless ["Seq", "Option", "Lists", "Each", "Few", "Map", "Combinator.Comp"].contains
        (".".intercalate parts.dropLast) do continue
    let f := parts.getLast!
    unless fns.contains f do continue
    let t := here ++ Name.mkSimple f
    let same ← liftTermElabM do
      isDefEq (← getConstInfo c).type (← getConstInfo t).type
    unless same do continue
    elabCommand (← `(command|
      @[simp, template] theorem $(mkIdent (Name.mkSimple (s ++ "_template"))) :
          $(mkIdent c) = $(mkIdent t) := rfl))

end GebTests.Prototypes.FreeTopos.Agreement.TemplateEquations

end
