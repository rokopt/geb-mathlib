/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.LF.Metatheory.HSubstRename
public import Geb.Prototypes.LF.Metatheory.Rename
public import Geb.Prototypes.LF.Metatheory.Scope
public import Geb.Prototypes.LF.Metatheory.Weakening
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The metatheory of canonical LF

The metatheory of Canonical LF of {cite}`HarperLicata2007`, Section 2.3: the laws of renaming
and its commutation with hereditary substitution, the stability of the judgments under renaming,
weakening among them, and the scoping of judged expressions, by which the declarations of a
formed signature are closed.
-/

set_option doc.verso true
