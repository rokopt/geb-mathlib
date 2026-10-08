/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import GebTests.Prototypes.FreeTopos.StoredWriter

/-!
# Certificate generator entry point

Write the certificates of the internal language's developments into a directory with
`lake exe geb-certify DIR`, as `scripts/certificates.sh` runs it. The generator is
`GebTests.Prototypes.FreeTopos.StoredWriter.generate`; the entry point is outside the library's
module prefix.

## Main definitions

* `main`: the certificates written into the directory the one argument names.
-/

/-- Write the certificates into the directory the one argument names. -/
public def main (args : List String) : IO UInt32 := do
  match args with
  | [dir] => GebTests.Prototypes.FreeTopos.StoredWriter.generate dir
  | _ =>
    IO.eprintln "usage: geb-certify DIR"
    pure 2
