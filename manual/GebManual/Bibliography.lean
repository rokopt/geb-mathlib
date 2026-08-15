/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import VersoManual
import Verso.Doc.Concrete.InlineString

/-! # Bibliography

The works the manual cites, as Verso bibliography entries.
`docs/references.bib` is the authoritative record; these are
rendering transcriptions keyed identically (the UpperCamelCase
names mirror the bib keys).
-/

open Verso.Genre.Manual

/-- Meertens, on paramorphisms. -/
public def Meertens1992 : Article := {
  title := inlines!"Paramorphisms",
  authors := #[inlines!"L. Meertens"],
  journal := inlines!"Formal Aspects of Computing",
  year := 1992,
  month := none,
  volume := inlines!"4",
  number := inlines!"5",
  pages := some (413, 424),
  url := some "https://doi.org/10.1007/BF01211391"
}
