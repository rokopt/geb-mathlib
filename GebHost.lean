/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module -- shake: keep-all, shake: keep-downstream

public import GebHost.Authoring
public import GebHost.Migration
public import GebHost.Navigation
public import GebHost.Editor
import GebMeta

set_option doc.verso true in
/-!
# The bootstrap's host services

Compiler diagnostics and the authoring driver, shared by the command-line tools and the manual.
The compiler, proof-source parser, prover and checker they run are written in Geb.
-/
