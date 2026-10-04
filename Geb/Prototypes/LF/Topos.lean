/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.LF.Topos.Rules
public import Geb.Prototypes.LF.Topos.Signature
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The internal language of a topos in LF

A fragment of the Mitchell–Bénabou language of the free elementary topos with a natural numbers
object ({cite}`MacLaneMoerdijk1992`, Section VI.5) as an LF signature, its types, terms and
derivations the canonical terms of LF types, and its computation rules as rewrite rules on the
signature's constants.
-/

set_option doc.verso true
