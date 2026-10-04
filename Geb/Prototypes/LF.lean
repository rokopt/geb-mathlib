/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.LF.HSubst
public import Geb.Prototypes.LF.Syntax
public import Geb.Prototypes.LF.Typing
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The logical framework LF

Canonical LF ({cite}`HarperLicata2007`, Section 2), the presentation of the logical framework LF
of {cite}`HarperHonsellPlotkin1993` whose expressions are its canonical forms: its syntax, in
which the β-normal forms are the only expressions and each application is a head with its spine;
the hereditary substitution, which keeps them canonical; and its judgments, decided by a fold
over the expression each classifies, among them the formation of a signature, the declaration of
the constants, with their kinds and types, that an object language is represented by. The
expressions are the input format of the type inhabitation solver of {cite}`NormanAvigad2025`
without its let definitions.
-/

set_option doc.verso true
