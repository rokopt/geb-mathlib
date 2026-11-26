/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

set_option doc.verso true in
/-!
# Names in emitted Lean mirrors

The Geb compiler writes each definition in a Lean namespace. For names such as
{lit}`(Lists.tail (Arrow T T))`, it encodes the bytes of the name in hexadecimal.
The loader looks up that identifier with {lit}`mirrorName`. Proofs referring to
the same definition can use its original Geb spelling with {lit}`gebMirror%`.
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Kernel.LoadCommand

open Lean

/-- A definition's mirror name, with the byte characters stored in its image encoded as by
{lit}`LeanBackend.leanName`: ASCII names stay readable, except Lean's special names; every other
name becomes a dollar followed by two hexadecimal digits per byte. -/
meta def mirrorName (ns : Name) (cs : List Char) : Name :=
  let s := String.ofList cs
  let safe (c : Char) := c.isDigit || ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z') ||
    c == '_' || c == '.' || c == '-'
  let digit (n : Nat) := Char.ofNat (if n < 10 then 48 + n else 87 + n)
  ns ++ .mkSimple (if !cs.isEmpty && s != "_" && s != "_root_" && cs.all safe then s
    else String.ofList ('$' :: cs.flatMap fun c ↦ [digit (c.toNat / 16), digit (c.toNat % 16)]))

/-- A definition in an open mirror namespace, named by its spelling in the Geb image. -/
macro:max "gebMirror% " s:str : term =>
  let bytes := s.getString.toUTF8.data.toList.map fun b ↦ Char.ofNat b.toNat
  pure (mkIdentFrom s (mirrorName .anonymous bytes))

end Geb.Kernel.LoadCommand

end
