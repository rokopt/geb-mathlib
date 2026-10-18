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
`lake exe geb-certify DIR`, as `scripts/certificates.sh` runs it, or those of the searches named
after the directory with `lake exe geb-certify DIR NAME...`, and print the searches' names with
`lake exe geb-certify --searches`. The generator is
`GebTests.Prototypes.FreeTopos.StoredWriter.generate`; the entry point is outside the library's
module prefix.

## Main definitions

* `main`: the certificates written into the directory the first argument names.
-/

/-- Write the certificates into the directory the first argument names, those of the searches the
other arguments name where there are any; or print the searches' names, one to a line. -/
public def main (args : List String) : IO UInt32 := do
  match args with
  | ["--searches"] =>
    for (name, _) in GebTests.Prototypes.FreeTopos.Certificates.searches do IO.println name
    pure 0
  | dir :: names => GebTests.Prototypes.FreeTopos.StoredWriter.generate dir names
  | _ =>
    IO.eprintln "usage: geb-certify DIR [NAME...] | geb-certify --searches"
    pure 2
