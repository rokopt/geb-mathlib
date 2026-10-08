/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Certified.Basic
public import GebTests.Prototypes.FreeTopos.Certified.Expansion
public import GebTests.Prototypes.FreeTopos.Certified.Normalization
public import GebTests.Prototypes.FreeTopos.Certified.Substitution
public import GebTests.Prototypes.FreeTopos.Certified.TreeCases
public import GebTests.Prototypes.FreeTopos.Certified.Weakening

set_option doc.verso true in
/-!
# The developments of the internal language, read from their certificates

Each development the internal language proves about the programs of the bootstrap, stored in a
certificate of {lit}`bootstrap/certificates/` that
{lit}`GebTests.Prototypes.FreeTopos.Certificates` writes, is read and checked in the program it is
about, and proves the statement it was found for.

## Tags

internal language, development, certificate, test
-/
