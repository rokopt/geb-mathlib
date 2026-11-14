/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Certified.Basic
public import GebTests.Prototypes.FreeTopos.Certified.Chain
public import GebTests.Prototypes.FreeTopos.Certified.Datatype
public import GebTests.Prototypes.FreeTopos.Certified.DatatypeAccepted
public import GebTests.Prototypes.FreeTopos.Certified.DatatypeCase
public import GebTests.Prototypes.FreeTopos.Certified.DatatypeCata
public import GebTests.Prototypes.FreeTopos.Certified.DatatypeClosed
public import GebTests.Prototypes.FreeTopos.Certified.DatatypeDatum
public import GebTests.Prototypes.FreeTopos.Certified.DatatypeForms
public import GebTests.Prototypes.FreeTopos.Certified.DatatypeGenerated
public import GebTests.Prototypes.FreeTopos.Certified.DatatypeList
public import GebTests.Prototypes.FreeTopos.Certified.DatatypeProgram
public import GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramData
public import GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramKinds
public import GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramReading
public import GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramSound
public import GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramTheory
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
