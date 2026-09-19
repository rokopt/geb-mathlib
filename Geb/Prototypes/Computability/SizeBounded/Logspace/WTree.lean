/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.Spell
public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.Events
public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.Positions
public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.Nodes
public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.Children
public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.Recognize
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Recognizing the W-trees of a coded signature

Index for the modules that recognize a word as the spelling of an admissible
W-tree of a finitary slice polynomial endofunctor whose shapes are coded by
bitstrings: the spelling of a W-tree as an Elias-length tree of labels and the
tree-level characterization of admissibility; the events of the streaming
scanner and the positions of labels in an encoding; the scan over the nodes
and the scan over one node's children, each the streaming scanner with a
fixed number of further counters; and the recognizer composed of them, with
its specification.
-/

set_option doc.verso true
