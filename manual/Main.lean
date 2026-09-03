/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/

import GebManual

/-! # Generator entry point

Passes the root `Part` to `manualMain`. Outside the `GebManual`
module prefix, so `lake lint -- GebManual` does not reach it.
-/

open Verso.Genre.Manual

/-- Generate the Geb manual. -/
def main (args : List String) : IO UInt32 :=
  manualMain (%doc GebManual.Root)
    (options := args)
    (config := {
      sourceLink := some "/literate/",
      issueLink := some "https://github.com/rokopt/geb-mathlib/issues"
    })
