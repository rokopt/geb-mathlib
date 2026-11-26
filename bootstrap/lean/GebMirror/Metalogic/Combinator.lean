module

public import GebMirror.Metalogic.Tactics

/-! Generated from a Geb program by `bootstrap/stage1/lean.geb`. -/

@[expose] public section

open Geb.Kernel
open Geb.Kernel renaming Tree → T

namespace GebMirror.Metalogic

def «Combinator.cHyp» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (_root_.GebMirror.Metalogic.«Prelude.single»
        (_root_.Geb.Kernel.Const.node
          x0
          ([] : _root_.List _root_.Geb.Kernel.Tree)));
    x1

def «Combinator.cRefl» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (_root_.GebMirror.Metalogic.«Prelude.single»
        (_root_.Geb.Kernel.Const.node
          x0
          ([] : _root_.List _root_.Geb.Kernel.Tree)));
    x1

def «Combinator.cSymm» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 2)
      (_root_.GebMirror.Metalogic.«Prelude.single» x0);
    x1

def «Combinator.cTrans» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 3)
      (_root_.GebMirror.Metalogic.«Theory.l2» x0 x1);
    x2

def «Combinator.cCong» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 4)
      (x0 :: x1);
    x2

def «Combinator.cStrict» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 5)
      (_root_.GebMirror.Metalogic.«Theory.l2»
        (_root_.Geb.Kernel.Const.node
          x0
          ([] : _root_.List _root_.Geb.Kernel.Tree))
        x1);
    x2

def «Combinator.cAx» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 6)
      ((_root_.Geb.Kernel.Const.node
        x0
        ([] : _root_.List _root_.Geb.Kernel.Tree)) ::
        (_root_.GebMirror.Metalogic.«Prelude.append»
          x1
          (_root_.GebMirror.Metalogic.«Prelude.append» x2 x3)));
    x4

def «Combinator.cThm» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 8)
      ((_root_.Geb.Kernel.Const.node
        x0
        ([] : _root_.List _root_.Geb.Kernel.Tree)) ::
        (_root_.GebMirror.Metalogic.«Prelude.append»
          x1
          (_root_.GebMirror.Metalogic.«Prelude.append» x2 x3)));
    x4

def «Combinator.certs» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 0) x0

def «Combinator.certsOf» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                 let x2 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x1;
                                 let x3 : _root_.List _root_.Geb.Kernel.Tree := x2; x3);
    x1

def «Combinator.scope» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «Combinator.scCtx» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                 let x2 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x1;
                                 let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree)
                                   x2
                                   (_root_.Geb.Kernel.leaf 0)
                                   (fun (x3 : _root_.Geb.Kernel.Tree)
                                      (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x3);
                                 let x4 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                   x2
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x5);
                                 let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree)
                                   x4
                                   (_root_.Geb.Kernel.leaf 0)
                                   (fun (x5 : _root_.Geb.Kernel.Tree)
                                      (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x5);
                                 let _ : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                   x4
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x7);
                                 let x7 : _root_.Geb.Kernel.Tree := x3;
                                 let x8 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x7;
                                 let x9 : _root_.List _root_.Geb.Kernel.Tree := x8; x9);
    x1

def «Combinator.scHyps» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                 let x2 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x1;
                                 let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree)
                                   x2
                                   (_root_.Geb.Kernel.leaf 0)
                                   (fun (x3 : _root_.Geb.Kernel.Tree)
                                      (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x3);
                                 let x4 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                   x2
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x5);
                                 let x5 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree)
                                   x4
                                   (_root_.Geb.Kernel.leaf 0)
                                   (fun (x5 : _root_.Geb.Kernel.Tree)
                                      (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x5);
                                 let _ : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                   x4
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x7);
                                 let x7 : _root_.Geb.Kernel.Tree := x5;
                                 let x8 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x7;
                                 let x9 : _root_.List _root_.Geb.Kernel.Tree := x8; x9);
    x1

def «Combinator.scSeq» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«PartialHorn.mkSeq»
      (_root_.GebMirror.Metalogic.«Combinator.scCtx» x0)
      (_root_.GebMirror.Metalogic.«Combinator.scHyps» x0)
      x1;
    x2

def «$285365712e6c656e677468205061727469616c486f726e2e45716e29» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (_ : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.add x2 (_root_.Geb.Kernel.leaf 1))
      (_root_.Geb.Kernel.leaf 0)
      x0;
    x1

def «Combinator.scCite» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.length»
                                          (_root_.GebMirror.Metalogic.«Combinator.scCtx» x0);
                                        _root_.GebMirror.Metalogic.«Combinator.cThm»
                                          x1
                                          (_root_.GebMirror.Metalogic.«Base.mapT»
                                            _root_.GebMirror.Metalogic.«PartialHorn.phVar»
                                            (_root_.GebMirror.Metalogic.«Base.range» x2))
                                          (_root_.GebMirror.Metalogic.«Base.mapT»
                                            _root_.GebMirror.Metalogic.«Combinator.cRefl»
                                            (_root_.GebMirror.Metalogic.«Base.range» x2))
                                          (_root_.GebMirror.Metalogic.«Base.mapT»
                                            _root_.GebMirror.Metalogic.«Combinator.cHyp»
                                            (_root_.GebMirror.Metalogic.«Base.range»
                                              (_root_.GebMirror.Metalogic.«$285365712e6c656e677468205061727469616c486f726e2e45716e29»
                                                (_root_.GebMirror.Metalogic.«Combinator.scHyps» x0)))));
    x2

def «Combinator.pty» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree)
    (x6 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 ::
        (x1 ::
          (x2 ::
            (x3 ::
              (x4 :: (x5 :: (x6 :: ([] : _root_.List _root_.Geb.Kernel.Tree))))))))

def «Combinator.ptys» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 0) x0

def «Combinator.ptysOf» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                 let x2 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x1;
                                 let x3 : _root_.List _root_.Geb.Kernel.Tree := x2; x3);
    x1

def «Combinator.tyT» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                        let x2 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                          x1;
                                        let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x2
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x3 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x3);
                                        let x4 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x2
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x5);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x4
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x5 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x5);
                                        let x6 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x4
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x7);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x6
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x7 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x7);
                                        let x8 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x6
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x9);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x8
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x9 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x9);
                                        let x10 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x8
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x11 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x11);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x10
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x11 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x11);
                                        let x12 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x10
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x13 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x13);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x12
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x13 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x13);
                                        let x14 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x12
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x15 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x15);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x14
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x15 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x15);
                                        let _ : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x14
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x17 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x17);
                                        x3);
    x1

def «Combinator.tySort» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                        let x2 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                          x1;
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x2
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x3 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x3);
                                        let x4 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x2
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x5);
                                        let x5 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x4
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x5 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x5);
                                        let x6 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x4
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x7);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x6
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x7 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x7);
                                        let x8 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x6
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x9);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x8
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x9 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x9);
                                        let x10 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x8
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x11 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x11);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x10
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x11 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x11);
                                        let x12 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x10
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x13 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x13);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x12
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x13 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x13);
                                        let x14 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x12
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x15 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x15);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x14
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x15 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x15);
                                        let _ : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x14
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x17 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x17);
                                        x5);
    x1

def «Combinator.tyDfd» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                        let x2 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                          x1;
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x2
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x3 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x3);
                                        let x4 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x2
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x5);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x4
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x5 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x5);
                                        let x6 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x4
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x7);
                                        let x7 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x6
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x7 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x7);
                                        let x8 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x6
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x9);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x8
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x9 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x9);
                                        let x10 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x8
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x11 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x11);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x10
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x11 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x11);
                                        let x12 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x10
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x13 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x13);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x12
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x13 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x13);
                                        let x14 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x12
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x15 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x15);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x14
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x15 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x15);
                                        let _ : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x14
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x17 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x17);
                                        x7);
    x1

def «Combinator.tyLo» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                        let x2 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                          x1;
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x2
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x3 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x3);
                                        let x4 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x2
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x5);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x4
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x5 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x5);
                                        let x6 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x4
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x7);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x6
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x7 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x7);
                                        let x8 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x6
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x9);
                                        let x9 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x8
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x9 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x9);
                                        let x10 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x8
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x11 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x11);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x10
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x11 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x11);
                                        let x12 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x10
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x13 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x13);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x12
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x13 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x13);
                                        let x14 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x12
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x15 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x15);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x14
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x15 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x15);
                                        let _ : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x14
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x17 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x17);
                                        x9);
    x1

def «Combinator.tyLoC» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                        let x2 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                          x1;
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x2
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x3 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x3);
                                        let x4 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x2
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x5);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x4
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x5 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x5);
                                        let x6 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x4
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x7);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x6
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x7 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x7);
                                        let x8 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x6
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x9);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x8
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x9 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x9);
                                        let x10 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x8
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x11 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x11);
                                        let x11 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x10
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x11 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x11);
                                        let x12 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x10
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x13 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x13);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x12
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x13 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x13);
                                        let x14 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x12
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x15 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x15);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x14
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x15 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x15);
                                        let _ : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x14
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x17 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x17);
                                        x11);
    x1

def «Combinator.tyHi» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                        let x2 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                          x1;
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x2
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x3 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x3);
                                        let x4 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x2
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x5);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x4
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x5 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x5);
                                        let x6 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x4
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x7);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x6
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x7 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x7);
                                        let x8 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x6
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x9);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x8
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x9 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x9);
                                        let x10 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x8
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x11 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x11);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x10
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x11 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x11);
                                        let x12 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x10
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x13 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x13);
                                        let x13 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x12
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x13 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x13);
                                        let x14 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x12
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x15 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x15);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x14
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x15 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x15);
                                        let _ : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x14
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x17 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x17);
                                        x13);
    x1

def «Combinator.tyHiC» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                        let x2 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                          x1;
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x2
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x3 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x3);
                                        let x4 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x2
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x5);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x4
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x5 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x5);
                                        let x6 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x4
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x7);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x6
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x7 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x7);
                                        let x8 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x6
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x9);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x8
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x9 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x9);
                                        let x10 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x8
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x11 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x11);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x10
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x11 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x11);
                                        let x12 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x10
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x13 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x13);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x12
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x13 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x13);
                                        let x14 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x12
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x15 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x15);
                                        let x15 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x14
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x15 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x15);
                                        let _ : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x14
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x17 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x17);
                                        x15);
    x1

def «Combinator.pty0» :=
  _root_.GebMirror.Metalogic.«Combinator.pty»
    (_root_.Geb.Kernel.leaf 0)
    (_root_.Geb.Kernel.leaf 0)
    (_root_.Geb.Kernel.leaf 0)
    (_root_.Geb.Kernel.leaf 0)
    (_root_.Geb.Kernel.leaf 0)
    (_root_.Geb.Kernel.leaf 0)
    (_root_.Geb.Kernel.leaf 0)

def «Combinator.devEntry» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «Combinator.devSeq» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                        let x2 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                          x1;
                                        let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x2
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x3 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x3);
                                        let x4 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x2
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x5);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x4
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x5 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x5);
                                        let _ : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x4
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x7);
                                        x3);
    x1

def «Combinator.devs» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 0) x0

def «Combinator.memoEntry» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «Combinator.memos» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 0) x0

def «Combinator.pairs» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 0) x0

def «Combinator.pairsOf» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                 let x2 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x1;
                                 let x3 : _root_.List _root_.Geb.Kernel.Tree := x2; x3);
    x1

def «Combinator.nfEntry» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «Combinator.nfList» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 0) x0

def «Combinator.pst» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 ::
        (x1 ::
          (x2 ::
            (x3 :: (x4 :: (x5 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))))))

def «Combinator.stDev» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                 let x2 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x1;
                                 let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree)
                                   x2
                                   (_root_.Geb.Kernel.leaf 0)
                                   (fun (x3 : _root_.Geb.Kernel.Tree)
                                      (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x3);
                                 let x4 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                   x2
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x5);
                                 let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree)
                                   x4
                                   (_root_.Geb.Kernel.leaf 0)
                                   (fun (x5 : _root_.Geb.Kernel.Tree)
                                      (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x5);
                                 let x6 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                   x4
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x7);
                                 let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree)
                                   x6
                                   (_root_.Geb.Kernel.leaf 0)
                                   (fun (x7 : _root_.Geb.Kernel.Tree)
                                      (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x7);
                                 let x8 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                   x6
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x9);
                                 let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree)
                                   x8
                                   (_root_.Geb.Kernel.leaf 0)
                                   (fun (x9 : _root_.Geb.Kernel.Tree)
                                      (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x9);
                                 let x10 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                   x8
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x11 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x11);
                                 let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree)
                                   x10
                                   (_root_.Geb.Kernel.leaf 0)
                                   (fun (x11 : _root_.Geb.Kernel.Tree)
                                      (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x11);
                                 let x12 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                   x10
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x13 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x13);
                                 let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree)
                                   x12
                                   (_root_.Geb.Kernel.leaf 0)
                                   (fun (x13 : _root_.Geb.Kernel.Tree)
                                      (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x13);
                                 let _ : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                   x12
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x15 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x15);
                                 let x15 : _root_.Geb.Kernel.Tree := x3;
                                 let x16 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x15;
                                 let x17 : _root_.List _root_.Geb.Kernel.Tree := x16; x17);
    x1

def «Combinator.stMemo» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                 let x2 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x1;
                                 let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree)
                                   x2
                                   (_root_.Geb.Kernel.leaf 0)
                                   (fun (x3 : _root_.Geb.Kernel.Tree)
                                      (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x3);
                                 let x4 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                   x2
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x5);
                                 let x5 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree)
                                   x4
                                   (_root_.Geb.Kernel.leaf 0)
                                   (fun (x5 : _root_.Geb.Kernel.Tree)
                                      (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x5);
                                 let x6 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                   x4
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x7);
                                 let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree)
                                   x6
                                   (_root_.Geb.Kernel.leaf 0)
                                   (fun (x7 : _root_.Geb.Kernel.Tree)
                                      (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x7);
                                 let x8 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                   x6
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x9);
                                 let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree)
                                   x8
                                   (_root_.Geb.Kernel.leaf 0)
                                   (fun (x9 : _root_.Geb.Kernel.Tree)
                                      (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x9);
                                 let x10 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                   x8
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x11 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x11);
                                 let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree)
                                   x10
                                   (_root_.Geb.Kernel.leaf 0)
                                   (fun (x11 : _root_.Geb.Kernel.Tree)
                                      (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x11);
                                 let x12 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                   x10
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x13 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x13);
                                 let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree)
                                   x12
                                   (_root_.Geb.Kernel.leaf 0)
                                   (fun (x13 : _root_.Geb.Kernel.Tree)
                                      (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x13);
                                 let _ : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                   x12
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x15 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x15);
                                 let x15 : _root_.Geb.Kernel.Tree := x5;
                                 let x16 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x15;
                                 let x17 : _root_.List _root_.Geb.Kernel.Tree := x16; x17);
    x1

def «Combinator.stNfs» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                 let x2 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x1;
                                 let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree)
                                   x2
                                   (_root_.Geb.Kernel.leaf 0)
                                   (fun (x3 : _root_.Geb.Kernel.Tree)
                                      (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x3);
                                 let x4 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                   x2
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x5);
                                 let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree)
                                   x4
                                   (_root_.Geb.Kernel.leaf 0)
                                   (fun (x5 : _root_.Geb.Kernel.Tree)
                                      (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x5);
                                 let x6 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                   x4
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x7);
                                 let x7 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree)
                                   x6
                                   (_root_.Geb.Kernel.leaf 0)
                                   (fun (x7 : _root_.Geb.Kernel.Tree)
                                      (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x7);
                                 let x8 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                   x6
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x9);
                                 let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree)
                                   x8
                                   (_root_.Geb.Kernel.leaf 0)
                                   (fun (x9 : _root_.Geb.Kernel.Tree)
                                      (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x9);
                                 let x10 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                   x8
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x11 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x11);
                                 let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree)
                                   x10
                                   (_root_.Geb.Kernel.leaf 0)
                                   (fun (x11 : _root_.Geb.Kernel.Tree)
                                      (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x11);
                                 let x12 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                   x10
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x13 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x13);
                                 let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree)
                                   x12
                                   (_root_.Geb.Kernel.leaf 0)
                                   (fun (x13 : _root_.Geb.Kernel.Tree)
                                      (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x13);
                                 let _ : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                   x12
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x15 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x15);
                                 let x15 : _root_.Geb.Kernel.Tree := x7;
                                 let x16 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x15;
                                 let x17 : _root_.List _root_.Geb.Kernel.Tree := x16; x17);
    x1

def «Combinator.stDefs» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                 let x2 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x1;
                                 let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree)
                                   x2
                                   (_root_.Geb.Kernel.leaf 0)
                                   (fun (x3 : _root_.Geb.Kernel.Tree)
                                      (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x3);
                                 let x4 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                   x2
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x5);
                                 let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree)
                                   x4
                                   (_root_.Geb.Kernel.leaf 0)
                                   (fun (x5 : _root_.Geb.Kernel.Tree)
                                      (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x5);
                                 let x6 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                   x4
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x7);
                                 let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree)
                                   x6
                                   (_root_.Geb.Kernel.leaf 0)
                                   (fun (x7 : _root_.Geb.Kernel.Tree)
                                      (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x7);
                                 let x8 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                   x6
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x9);
                                 let x9 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree)
                                   x8
                                   (_root_.Geb.Kernel.leaf 0)
                                   (fun (x9 : _root_.Geb.Kernel.Tree)
                                      (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x9);
                                 let x10 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                   x8
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x11 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x11);
                                 let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree)
                                   x10
                                   (_root_.Geb.Kernel.leaf 0)
                                   (fun (x11 : _root_.Geb.Kernel.Tree)
                                      (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x11);
                                 let x12 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                   x10
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x13 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x13);
                                 let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree)
                                   x12
                                   (_root_.Geb.Kernel.leaf 0)
                                   (fun (x13 : _root_.Geb.Kernel.Tree)
                                      (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x13);
                                 let _ : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                   x12
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x15 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x15);
                                 let x15 : _root_.Geb.Kernel.Tree := x9;
                                 let x16 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x15;
                                 let x17 : _root_.List _root_.Geb.Kernel.Tree := x16; x17);
    x1

def «Combinator.stSig» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                 let x2 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x1;
                                 let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree)
                                   x2
                                   (_root_.Geb.Kernel.leaf 0)
                                   (fun (x3 : _root_.Geb.Kernel.Tree)
                                      (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x3);
                                 let x4 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                   x2
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x5);
                                 let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree)
                                   x4
                                   (_root_.Geb.Kernel.leaf 0)
                                   (fun (x5 : _root_.Geb.Kernel.Tree)
                                      (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x5);
                                 let x6 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                   x4
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x7);
                                 let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree)
                                   x6
                                   (_root_.Geb.Kernel.leaf 0)
                                   (fun (x7 : _root_.Geb.Kernel.Tree)
                                      (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x7);
                                 let x8 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                   x6
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x9);
                                 let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree)
                                   x8
                                   (_root_.Geb.Kernel.leaf 0)
                                   (fun (x9 : _root_.Geb.Kernel.Tree)
                                      (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x9);
                                 let x10 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                   x8
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x11 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x11);
                                 let x11 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree)
                                   x10
                                   (_root_.Geb.Kernel.leaf 0)
                                   (fun (x11 : _root_.Geb.Kernel.Tree)
                                      (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x11);
                                 let x12 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                   x10
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x13 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x13);
                                 let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree)
                                   x12
                                   (_root_.Geb.Kernel.leaf 0)
                                   (fun (x13 : _root_.Geb.Kernel.Tree)
                                      (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x13);
                                 let _ : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                   x12
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x15 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x15);
                                 let x15 : _root_.Geb.Kernel.Tree := x11;
                                 let x16 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x15;
                                 let x17 : _root_.List _root_.Geb.Kernel.Tree := x16; x17);
    x1

def «Combinator.stInfer» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                        let x2 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                          x1;
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x2
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x3 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x3);
                                        let x4 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x2
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x5);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x4
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x5 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x5);
                                        let x6 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x4
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x7);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x6
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x7 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x7);
                                        let x8 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x6
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x9);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x8
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x9 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x9);
                                        let x10 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x8
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x11 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x11);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x10
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x11 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x11);
                                        let x12 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x10
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x13 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x13);
                                        let x13 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x12
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x13 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x13);
                                        let _ : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x12
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x15 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x15);
                                        x13);
    x1

def «Combinator.withDev» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (let x2 : _root_.Geb.Kernel.Tree := x0;
                                        let x3 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                          x2;
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x3
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x4 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x4);
                                        let x5 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x3
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x6 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x6);
                                        let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x5
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x6 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x6);
                                        let x7 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x5
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x8);
                                        let x8 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x7
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x8 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x8);
                                        let x9 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x7
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x10 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x10);
                                        let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x9
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x10 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x10);
                                        let x11 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x9
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x12);
                                        let x12 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x11
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x12 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x12);
                                        let x13 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x11
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x14);
                                        let x14 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x13
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x14 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x14);
                                        let _ : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x13
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x16 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x16);
                                        _root_.GebMirror.Metalogic.«Combinator.pst»
                                          (_root_.GebMirror.Metalogic.«Combinator.devs» x1)
                                          x6
                                          x8
                                          x10
                                          x12
                                          x14);
    x2

def «Combinator.withMemo» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (let x2 : _root_.Geb.Kernel.Tree := x0;
                                        let x3 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                          x2;
                                        let x4 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x3
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x4 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x4);
                                        let x5 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x3
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x6 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x6);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x5
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x6 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x6);
                                        let x7 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x5
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x8);
                                        let x8 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x7
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x8 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x8);
                                        let x9 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x7
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x10 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x10);
                                        let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x9
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x10 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x10);
                                        let x11 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x9
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x12);
                                        let x12 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x11
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x12 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x12);
                                        let x13 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x11
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x14);
                                        let x14 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x13
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x14 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x14);
                                        let _ : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x13
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x16 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x16);
                                        _root_.GebMirror.Metalogic.«Combinator.pst»
                                          x4
                                          (_root_.GebMirror.Metalogic.«Combinator.memos» x1)
                                          x8
                                          x10
                                          x12
                                          x14);
    x2

def «Combinator.withNfs» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (let x2 : _root_.Geb.Kernel.Tree := x0;
                                        let x3 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                          x2;
                                        let x4 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x3
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x4 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x4);
                                        let x5 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x3
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x6 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x6);
                                        let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x5
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x6 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x6);
                                        let x7 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x5
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x8);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x7
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x8 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x8);
                                        let x9 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x7
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x10 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x10);
                                        let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x9
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x10 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x10);
                                        let x11 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x9
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x12);
                                        let x12 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x11
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x12 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x12);
                                        let x13 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x11
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x14);
                                        let x14 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x13
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x14 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x14);
                                        let _ : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x13
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x16 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x16);
                                        _root_.GebMirror.Metalogic.«Combinator.pst»
                                          x4
                                          x6
                                          (_root_.GebMirror.Metalogic.«Combinator.nfList» x1)
                                          x10
                                          x12
                                          x14);
    x2

def «$284f7074696f6e2e6e6f7468696e6720436f6d62696e61746f722e50547929» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$284f7074696f6e2e6a75737420436f6d62696e61746f722e50547929» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «Combinator.memoFind» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree) (x3 : _root_.Geb.Kernel.Tree) =>
        let x4 : _root_.Geb.Kernel.Tree := x2;
        let x5 : _root_.List
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x4;
        let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
          (α := _root_.Geb.Kernel.Tree)
          (β := _root_.Geb.Kernel.Tree)
          x5
          (_root_.Geb.Kernel.leaf 0)
          (fun (x6 : _root_.Geb.Kernel.Tree)
             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
            x6);
        let x7 : _root_.List
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
          (α := _root_.Geb.Kernel.Tree)
          (β := _root_.List _root_.Geb.Kernel.Tree)
          x5
          ([] : _root_.List _root_.Geb.Kernel.Tree)
          (fun (_ : _root_.Geb.Kernel.Tree)
             (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
            x8);
        let x8 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
          (α := _root_.Geb.Kernel.Tree)
          (β := _root_.Geb.Kernel.Tree)
          x7
          (_root_.Geb.Kernel.leaf 0)
          (fun (x8 : _root_.Geb.Kernel.Tree)
             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
            x8);
        let _ : _root_.List
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
          (α := _root_.Geb.Kernel.Tree)
          (β := _root_.List _root_.Geb.Kernel.Tree)
          x7
          ([] : _root_.List _root_.Geb.Kernel.Tree)
          (fun (_ : _root_.Geb.Kernel.Tree)
             (x10 : _root_.List _root_.Geb.Kernel.Tree) =>
            x10);
        if (_root_.Geb.Kernel.Const.equal x6 x1).label ≠ 0 then
          _root_.GebMirror.Metalogic.«$284f7074696f6e2e6a75737420436f6d62696e61746f722e50547929»
            x8
        else
          x3)
      _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e6720436f6d62696e61746f722e50547929»
      x0;
    x2

def «Combinator.nfFind» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree) (x3 : _root_.Geb.Kernel.Tree) =>
        let x4 : _root_.Geb.Kernel.Tree := x2;
        let x5 : _root_.List
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x4;
        let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
          (α := _root_.Geb.Kernel.Tree)
          (β := _root_.Geb.Kernel.Tree)
          x5
          (_root_.Geb.Kernel.leaf 0)
          (fun (x6 : _root_.Geb.Kernel.Tree)
             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
            x6);
        let x7 : _root_.List
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
          (α := _root_.Geb.Kernel.Tree)
          (β := _root_.List _root_.Geb.Kernel.Tree)
          x5
          ([] : _root_.List _root_.Geb.Kernel.Tree)
          (fun (_ : _root_.Geb.Kernel.Tree)
             (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
            x8);
        let x8 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
          (α := _root_.Geb.Kernel.Tree)
          (β := _root_.Geb.Kernel.Tree)
          x7
          (_root_.Geb.Kernel.leaf 0)
          (fun (x8 : _root_.Geb.Kernel.Tree)
             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
            x8);
        let _ : _root_.List
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
          (α := _root_.Geb.Kernel.Tree)
          (β := _root_.List _root_.Geb.Kernel.Tree)
          x7
          ([] : _root_.List _root_.Geb.Kernel.Tree)
          (fun (_ : _root_.Geb.Kernel.Tree)
             (x10 : _root_.List _root_.Geb.Kernel.Tree) =>
            x10);
        if (_root_.Geb.Kernel.Const.equal x6 x1).label ≠ 0 then
          _root_.GebMirror.Metalogic.«$284f7074696f6e2e6a757374204c616e67756167652e545061697229»
            x8
        else
          x3)
      _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e67204c616e67756167652e545061697229»
      x0;
    x2

def «Combinator.eqnCert» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «Combinator.ecEqn» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                        let x2 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                          x1;
                                        let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x2
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x3 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x3);
                                        let x4 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x2
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x5);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x4
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x5 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x5);
                                        let _ : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x4
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x7);
                                        x3);
    x1

def «Combinator.ecCert» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                        let x2 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                          x1;
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x2
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x3 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x3);
                                        let x4 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x2
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x5);
                                        let x5 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x4
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x5 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x5);
                                        let _ : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x4
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x7);
                                        x5);
    x1

def «Combinator.assoc» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 ::
        (x1 :: (x2 :: (x3 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))))

def «$28436f6d62696e61746f722e436f6d702e726573205429» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «$28436f6d62696e61746f722e436f6d702e626164205429» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$28436f6d62696e61746f722e436f6d702e6f6b205429» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «$28436f6d62696e61746f722e436f6d702e72657320436f6d62696e61746f722e50547929» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «$28436f6d62696e61746f722e436f6d702e62616420436f6d62696e61746f722e50547929» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$28436f6d62696e61746f722e436f6d702e6f6b20436f6d62696e61746f722e50547929» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «$28436f6d62696e61746f722e436f6d702e726573205061727469616c486f726e2e53657175656e7429» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «$28436f6d62696e61746f722e436f6d702e626164205061727469616c486f726e2e53657175656e7429» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$28436f6d62696e61746f722e436f6d702e6f6b205061727469616c486f726e2e53657175656e7429» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «$28436f6d62696e61746f722e436f6d702e726573204c616e67756167652e545061697229» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «$28436f6d62696e61746f722e436f6d702e626164204c616e67756167652e545061697229» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$28436f6d62696e61746f722e436f6d702e6f6b204c616e67756167652e545061697229» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «$28436f6d62696e61746f722e436f6d702e72657320436f6d62696e61746f722e45716e4365727429» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «$28436f6d62696e61746f722e436f6d702e62616420436f6d62696e61746f722e45716e4365727429» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$28436f6d62696e61746f722e436f6d702e6f6b20436f6d62696e61746f722e45716e4365727429» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «$28436f6d62696e61746f722e436f6d702e72657320436f6d62696e61746f722e436572747329» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «$28436f6d62696e61746f722e436f6d702e62616420436f6d62696e61746f722e436572747329» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$28436f6d62696e61746f722e436f6d702e6f6b20436f6d62696e61746f722e436572747329» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «$28436f6d62696e61746f722e436f6d702e72657320436f6d62696e61746f722e5054797329» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «$28436f6d62696e61746f722e436f6d702e62616420436f6d62696e61746f722e5054797329» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$28436f6d62696e61746f722e436f6d702e6f6b20436f6d62696e61746f722e5054797329» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «$28436f6d62696e61746f722e436f6d702e72657320436f6d62696e61746f722e506169727329» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «$28436f6d62696e61746f722e436f6d702e62616420436f6d62696e61746f722e506169727329» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$28436f6d62696e61746f722e436f6d702e6f6b20436f6d62696e61746f722e506169727329» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «$28436f6d62696e61746f722e436f6d702e7265732032393a284f7074696f6e2e4d6179626520436f6d62696e61746f722e5054792929» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «$28436f6d62696e61746f722e436f6d702e6261642032393a284f7074696f6e2e4d6179626520436f6d62696e61746f722e5054792929» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$28436f6d62696e61746f722e436f6d702e6f6b2032393a284f7074696f6e2e4d6179626520436f6d62696e61746f722e5054792929» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «$28436f6d62696e61746f722e436f6d702e7265732032393a284f7074696f6e2e4d61796265204c616e67756167652e54506169722929» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «$28436f6d62696e61746f722e436f6d702e6261642032393a284f7074696f6e2e4d61796265204c616e67756167652e54506169722929» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$28436f6d62696e61746f722e436f6d702e6f6b2032393a284f7074696f6e2e4d61796265204c616e67756167652e54506169722929» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «$28436f6d62696e61746f722e436f6d702e72657320436f6d62696e61746f722e4173736f6329» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «$28436f6d62696e61746f722e436f6d702e62616420436f6d62696e61746f722e4173736f6329» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$28436f6d62696e61746f722e436f6d702e6f6b20436f6d62696e61746f722e4173736f6329» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «$28436f6d62696e61746f722e436f6d702e72657320436f6d62696e61746f722e50537429» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «$28436f6d62696e61746f722e436f6d702e62616420436f6d62696e61746f722e50537429» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$28436f6d62696e61746f722e436f6d702e6f6b20436f6d62696e61746f722e50537429» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «Combinator.pmGet» :=
  fun (_ : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6f6b20436f6d62696e61746f722e50537429»
      (_root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e72657320436f6d62696e61746f722e50537429»
        x1
        x1);
    x2

def «Combinator.pmGuard» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (_ : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
      if (x0).label ≠ 0 then
        _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6f6b205429»
          (_root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e726573205429»
            (_root_.Geb.Kernel.leaf 0)
            x2)
      else
        _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e626164205429»);
    x1

def «$28436f6d62696e61746f722e436f6d702e62696e64205420436f6d62696e61746f722e436572747329» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x4)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x5 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x5
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x6 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x5
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x8);
                                          let x8 : _root_.Geb.Kernel.Tree := x6;
                                          let x9 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x8;
                                          let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x9
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x10 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x10);
                                          let x11 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x9
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let x12 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x11
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x12 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x11
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x14);
                                          x1 x10 x2 x12
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62616420436f6d62696e61746f722e436572747329»);
    x4

def «$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e436572747320436f6d62696e61746f722e436572747329» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x4)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x5 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x5
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x6 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x5
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x8);
                                          let x8 : _root_.Geb.Kernel.Tree := x6;
                                          let x9 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x8;
                                          let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x9
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x10 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x10);
                                          let x11 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x9
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let x12 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x11
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x12 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x11
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x14);
                                          x1 x10 x2 x12
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62616420436f6d62696e61746f722e436572747329»);
    x4

def «$28436f6d62696e61746f722e436f6d702e7075726520436f6d62696e61746f722e436572747329» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (_ : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6f6b20436f6d62696e61746f722e436572747329»
      (_root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e72657320436f6d62696e61746f722e436572747329»
        x0
        x2);
    x3

def «Combinator.mapMEqC» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.Geb.Kernel.Tree →
           _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64205420436f6d62696e61746f722e436572747329»
          (x0 x2)
          (fun (x4 : _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e436572747320436f6d62696e61746f722e436572747329»
              x3
              (fun (x5 : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e7075726520436f6d62696e61746f722e436572747329»
                  (_root_.GebMirror.Metalogic.«Combinator.certs»
                    (x4 :: (_root_.GebMirror.Metalogic.«Combinator.certsOf» x5))))))
      (_root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e7075726520436f6d62696e61746f722e436572747329»
        (_root_.GebMirror.Metalogic.«Combinator.certs»
          ([] : _root_.List _root_.Geb.Kernel.Tree)))
      x1;
    x2

def «Combinator.mapMPairC» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.Geb.Kernel.Tree →
           _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64205420436f6d62696e61746f722e436572747329»
          (x0 x2)
          (fun (x4 : _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e436572747320436f6d62696e61746f722e436572747329»
              x3
              (fun (x5 : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e7075726520436f6d62696e61746f722e436572747329»
                  (_root_.GebMirror.Metalogic.«Combinator.certs»
                    (x4 :: (_root_.GebMirror.Metalogic.«Combinator.certsOf» x5))))))
      (_root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e7075726520436f6d62696e61746f722e436572747329»
        (_root_.GebMirror.Metalogic.«Combinator.certs»
          ([] : _root_.List _root_.Geb.Kernel.Tree)))
      x1;
    x2

def «$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e50547920436f6d62696e61746f722e5054797329» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x4)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x5 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x5
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x6 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x5
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x8);
                                          let x8 : _root_.Geb.Kernel.Tree := x6;
                                          let x9 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x8;
                                          let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x9
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x10 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x10);
                                          let x11 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x9
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let x12 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x11
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x12 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x11
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x14);
                                          x1 x10 x2 x12
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62616420436f6d62696e61746f722e5054797329»);
    x4

def «$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e5054797320436f6d62696e61746f722e5054797329» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x4)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x5 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x5
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x6 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x5
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x8);
                                          let x8 : _root_.Geb.Kernel.Tree := x6;
                                          let x9 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x8;
                                          let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x9
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x10 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x10);
                                          let x11 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x9
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let x12 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x11
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x12 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x11
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x14);
                                          x1 x10 x2 x12
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62616420436f6d62696e61746f722e5054797329»);
    x4

def «$28436f6d62696e61746f722e436f6d702e7075726520436f6d62696e61746f722e5054797329» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (_ : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6f6b20436f6d62696e61746f722e5054797329»
      (_root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e72657320436f6d62696e61746f722e5054797329»
        x0
        x2);
    x3

def «Combinator.mapMTY» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.Geb.Kernel.Tree →
           _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e50547920436f6d62696e61746f722e5054797329»
          (x0 x2)
          (fun (x4 : _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e5054797320436f6d62696e61746f722e5054797329»
              x3
              (fun (x5 : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e7075726520436f6d62696e61746f722e5054797329»
                  (_root_.GebMirror.Metalogic.«Combinator.ptys»
                    (x4 :: (_root_.GebMirror.Metalogic.«Combinator.ptysOf» x5))))))
      (_root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e7075726520436f6d62696e61746f722e5054797329»
        (_root_.GebMirror.Metalogic.«Combinator.ptys»
          ([] : _root_.List _root_.Geb.Kernel.Tree)))
      x1;
    x2

def «Combinator.seqY» :=
  fun (x0 : _root_.List
      (_root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
    let x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree →
           _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
         (x2 : _root_.Geb.Kernel.Tree →
           _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e50547920436f6d62696e61746f722e5054797329»
          x1
          (fun (x3 : _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e5054797320436f6d62696e61746f722e5054797329»
              x2
              (fun (x4 : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e7075726520436f6d62696e61746f722e5054797329»
                  (_root_.GebMirror.Metalogic.«Combinator.ptys»
                    (x3 :: (_root_.GebMirror.Metalogic.«Combinator.ptysOf» x4))))))
      (_root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e7075726520436f6d62696e61746f722e5054797329»
        (_root_.GebMirror.Metalogic.«Combinator.ptys»
          ([] : _root_.List _root_.Geb.Kernel.Tree)))
      x0;
    x1

def «$28436f6d62696e61746f722e436f6d702e62696e64204c616e67756167652e545061697220436f6d62696e61746f722e506169727329» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x4)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x5 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x5
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x6 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x5
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x8);
                                          let x8 : _root_.Geb.Kernel.Tree := x6;
                                          let x9 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x8;
                                          let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x9
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x10 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x10);
                                          let x11 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x9
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let x12 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x11
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x12 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x11
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x14);
                                          x1 x10 x2 x12
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62616420436f6d62696e61746f722e506169727329»);
    x4

def «$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e506169727320436f6d62696e61746f722e506169727329» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x4)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x5 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x5
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x6 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x5
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x8);
                                          let x8 : _root_.Geb.Kernel.Tree := x6;
                                          let x9 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x8;
                                          let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x9
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x10 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x10);
                                          let x11 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x9
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let x12 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x11
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x12 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x11
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x14);
                                          x1 x10 x2 x12
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62616420436f6d62696e61746f722e506169727329»);
    x4

def «$28436f6d62696e61746f722e436f6d702e7075726520436f6d62696e61746f722e506169727329» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (_ : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6f6b20436f6d62696e61746f722e506169727329»
      (_root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e72657320436f6d62696e61746f722e506169727329»
        x0
        x2);
    x3

def «Combinator.seqP» :=
  fun (x0 : _root_.List
      (_root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
    let x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree →
           _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
         (x2 : _root_.Geb.Kernel.Tree →
           _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64204c616e67756167652e545061697220436f6d62696e61746f722e506169727329»
          x1
          (fun (x3 : _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e506169727320436f6d62696e61746f722e506169727329»
              x2
              (fun (x4 : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e7075726520436f6d62696e61746f722e506169727329»
                  (_root_.GebMirror.Metalogic.«Combinator.pairs»
                    (x3 :: (_root_.GebMirror.Metalogic.«Combinator.pairsOf» x4))))))
      (_root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e7075726520436f6d62696e61746f722e506169727329»
        (_root_.GebMirror.Metalogic.«Combinator.pairs»
          ([] : _root_.List _root_.Geb.Kernel.Tree)))
      x0;
    x1

def «Combinator.findIdx» :=
  fun (x0 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (_root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.Geb.Kernel.Tree × _root_.Geb.Kernel.Tree) =>
        (_root_.Geb.Kernel.Const.sub (x3).1 (_root_.Geb.Kernel.leaf 1),
          if (x0 x2).label ≠ 0 then
            _root_.GebMirror.Metalogic.«Prelude.some»
              (_root_.Geb.Kernel.Const.sub (x3).1 (_root_.Geb.Kernel.leaf 1))
          else
            (x3).2))
      (_root_.GebMirror.Metalogic.«$285365712e6c656e677468205061727469616c486f726e2e45716e29»
        x1,
        _root_.GebMirror.Metalogic.«Prelude.none»)
      x1).2;
    x2

def «Combinator.seq0» :=
  _root_.GebMirror.Metalogic.«PartialHorn.mkSeq»
    ([] : _root_.List _root_.Geb.Kernel.Tree)
    ([] : _root_.List _root_.Geb.Kernel.Tree)
    (_root_.GebMirror.Metalogic.«PartialHorn.eqn»
      (_root_.Geb.Kernel.leaf 0)
      (_root_.Geb.Kernel.leaf 0))

def «Combinator.pdefn0» :=
  _root_.GebMirror.Metalogic.«PartialHorn.pdefn»
    (_root_.GebMirror.Metalogic.«PartialHorn.sorts»
      ([] : _root_.List _root_.Geb.Kernel.Tree))
    (_root_.Geb.Kernel.leaf 0)
    (_root_.Geb.Kernel.leaf 0)

def «$28436f6d62696e61746f722e436f6d702e70757265205061727469616c486f726e2e53657175656e7429» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (_ : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6f6b205061727469616c486f726e2e53657175656e7429»
      (_root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e726573205061727469616c486f726e2e53657175656e7429»
        x0
        x2);
    x3

def «$285365712e7461696c205061727469616c486f726e2e53657175656e7429» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      x0
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      (fun (_ : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
        x2);
    x1

def «$285365712e64726f70205061727469616c486f726e2e53657175656e7429» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.iter
      (α := _root_.List _root_.Geb.Kernel.Tree)
      _root_.GebMirror.Metalogic.«$285365712e7461696c205061727469616c486f726e2e53657175656e7429»
      x1
      x0;
    x2

def «$285365712e61744f72205061727469616c486f726e2e53657175656e7429» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«$285365712e64726f70205061727469616c486f726e2e53657175656e7429»
        x2
        x1)
      x0
      (fun (x3 : _root_.Geb.Kernel.Tree)
         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        x3);
    x3

def «$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e505374205061727469616c486f726e2e53657175656e7429» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x4)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x5 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x5
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x6 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x5
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x8);
                                          let x8 : _root_.Geb.Kernel.Tree := x6;
                                          let x9 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x8;
                                          let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x9
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x10 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x10);
                                          let x11 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x9
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let x12 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x11
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x12 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x11
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x14);
                                          x1 x10 x2 x12
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e626164205061727469616c486f726e2e53657175656e7429»);
    x4

def «$28436f6d62696e61746f722e436f6d702e6661696c205061727469616c486f726e2e53657175656e7429» :=
  fun (_ : _root_.Geb.Kernel.Tree) (_ : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e626164205061727469616c486f726e2e53657175656e7429»;
    x2

def «Combinator.axiomAt» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (if (_root_.Geb.Kernel.Const.lt
      x0
      (_root_.GebMirror.Metalogic.«$285365712e6c656e677468205061727469616c486f726e2e53657175656e7429»
        _root_.GebMirror.Metalogic.«Theory.axioms»)).label ≠ 0 then
      _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265205061727469616c486f726e2e53657175656e7429»
        (_root_.GebMirror.Metalogic.«$285365712e61744f72205061727469616c486f726e2e53657175656e7429»
          _root_.GebMirror.Metalogic.«Combinator.seq0»
          _root_.GebMirror.Metalogic.«Theory.axioms»
          x0)
    else
      _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e505374205061727469616c486f726e2e53657175656e7429»
        _root_.GebMirror.Metalogic.«Combinator.pmGet»
        (fun (x1 : _root_.Geb.Kernel.Tree) =>
          let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.sub
            x0
            (_root_.GebMirror.Metalogic.«$285365712e6c656e677468205061727469616c486f726e2e53657175656e7429»
              _root_.GebMirror.Metalogic.«Theory.axioms»);
          let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e74684f66205061727469616c486f726e2e504465666e29»
            (_root_.GebMirror.Metalogic.«Combinator.stDefs» x1)
            (_root_.Geb.Kernel.Const.div x2 (_root_.Geb.Kernel.leaf 2));
          if (_root_.GebMirror.Metalogic.«$284f7074696f6e2e69734a757374205061727469616c486f726e2e504465666e29»
            x3).label ≠ 0 then
            let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e74684f66205061727469616c486f726e2e53657175656e7429»
              (_root_.GebMirror.Metalogic.«PartialHorn.pdAxioms»
                (_root_.Geb.Kernel.Const.add
                  (_root_.GebMirror.Metalogic.«$285365712e6c656e677468205061727469616c486f726e2e4f7053696729»
                    _root_.GebMirror.Metalogic.«Theory.sig»)
                  (_root_.Geb.Kernel.Const.div x2 (_root_.Geb.Kernel.leaf 2)))
                (_root_.GebMirror.Metalogic.«$284f7074696f6e2e66726f6d4d61796265205061727469616c486f726e2e504465666e29»
                  _root_.GebMirror.Metalogic.«Combinator.pdefn0»
                  x3))
              (_root_.Geb.Kernel.Const.mod x2 (_root_.Geb.Kernel.leaf 2));
            if (_root_.GebMirror.Metalogic.«$284f7074696f6e2e69734a757374205061727469616c486f726e2e53657175656e7429»
              x4).label ≠ 0 then
              _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265205061727469616c486f726e2e53657175656e7429»
                (_root_.GebMirror.Metalogic.«$284f7074696f6e2e66726f6d4d61796265205061727469616c486f726e2e53657175656e7429»
                  _root_.GebMirror.Metalogic.«Combinator.seq0»
                  x4)
            else
              _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6661696c205061727469616c486f726e2e53657175656e7429»
          else
            _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6661696c205061727469616c486f726e2e53657175656e7429»));
    x1

def «$285365712e6c656e67746820436f6d62696e61746f722e446576456e74727929» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (_ : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.add x2 (_root_.Geb.Kernel.leaf 1))
      (_root_.Geb.Kernel.leaf 0)
      x0;
    x1

def «$285365712e617070656e6420436f6d62696e61746f722e446576456e74727929» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        (x2 :: x3))
      x1
      x0;
    x2

def «$285365712e73696e676c6520436f6d62696e61746f722e446576456e74727929» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      ([] : _root_.List _root_.Geb.Kernel.Tree));
    x1

def «Combinator.addLemma» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6f6b205429»
        (_root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e726573205429»
          (_root_.GebMirror.Metalogic.«Combinator.scCite»
            x2
            (_root_.GebMirror.Metalogic.«$285365712e6c656e67746820436f6d62696e61746f722e446576456e74727929»
              (_root_.GebMirror.Metalogic.«Combinator.stDev» x3)))
          (_root_.GebMirror.Metalogic.«Combinator.withDev»
            x3
            (_root_.GebMirror.Metalogic.«$285365712e617070656e6420436f6d62696e61746f722e446576456e74727929»
              (_root_.GebMirror.Metalogic.«Combinator.stDev» x3)
              (_root_.GebMirror.Metalogic.«$285365712e73696e676c6520436f6d62696e61746f722e446576456e74727929»
                (_root_.GebMirror.Metalogic.«Combinator.devEntry»
                  (_root_.GebMirror.Metalogic.«Combinator.scSeq» x2 x0)
                  x1))))));
    x2

def «Combinator.lookup» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (_ : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
      _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6f6b2032393a284f7074696f6e2e4d6179626520436f6d62696e61746f722e5054792929»
        (_root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e7265732032393a284f7074696f6e2e4d6179626520436f6d62696e61746f722e5054792929»
          (_root_.GebMirror.Metalogic.«Combinator.memoFind»
            (_root_.GebMirror.Metalogic.«Combinator.stMemo» x2)
            x0)
          x2));
    x1

def «Combinator.memoize» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (_ : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
      _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6f6b205429»
        (_root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e726573205429»
          (_root_.Geb.Kernel.leaf 0)
          (_root_.GebMirror.Metalogic.«Combinator.withMemo»
            x2
            ((_root_.GebMirror.Metalogic.«Combinator.memoEntry»
              (_root_.GebMirror.Metalogic.«Combinator.tyT» x0)
              x0) ::
              (_root_.GebMirror.Metalogic.«Combinator.stMemo» x2)))));
    x1

def «$28436f6d62696e61746f722e436f6d702e62696e64205420436f6d62696e61746f722e50547929» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x4)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x5 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x5
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x6 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x5
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x8);
                                          let x8 : _root_.Geb.Kernel.Tree := x6;
                                          let x9 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x8;
                                          let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x9
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x10 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x10);
                                          let x11 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x9
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let x12 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x11
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x12 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x11
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x14);
                                          x1 x10 x2 x12
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62616420436f6d62696e61746f722e50547929»);
    x4

def «$28436f6d62696e61746f722e436f6d702e7075726520436f6d62696e61746f722e50547929» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (_ : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6f6b20436f6d62696e61746f722e50547929»
      (_root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e72657320436f6d62696e61746f722e50547929»
        x0
        x2);
    x3

def «Combinator.memoRet» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64205420436f6d62696e61746f722e50547929»
      (_root_.GebMirror.Metalogic.«Combinator.memoize» x0)
      (fun (_ : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e7075726520436f6d62696e61746f722e50547929»
          x0);
    x1

def «Combinator.dfdCert» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      if (_root_.GebMirror.Metalogic.«Combinator.stInfer» x3).label ≠ 0 then
        _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6f6b205429»
          (_root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e726573205429»
            (_root_.Geb.Kernel.Const.node
              (_root_.Geb.Kernel.leaf 9)
              (_root_.GebMirror.Metalogic.«Prelude.single» x0))
            x3)
      else
        _root_.GebMirror.Metalogic.«Combinator.addLemma»
          (_root_.GebMirror.Metalogic.«Theory.dfd» x0)
          x1
          x2
          x3);
    x2

def «Combinator.eqCert» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      if (_root_.GebMirror.Metalogic.«Combinator.stInfer» x3).label ≠ 0 then
        _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6f6b205429»
          (_root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e726573205429»
            (_root_.Geb.Kernel.Const.node
              (_root_.Geb.Kernel.leaf 10)
              (_root_.GebMirror.Metalogic.«Theory.l2»
                (_root_.GebMirror.Metalogic.«PartialHorn.eqLhs» x0)
                (_root_.GebMirror.Metalogic.«PartialHorn.eqRhs» x0)))
            x3)
      else
        _root_.GebMirror.Metalogic.«Combinator.addLemma» x0 x1 x2 x3);
    x2

def «Combinator.objEq» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (_ : _root_.Geb.Kernel.Tree) (x3 : _root_.Geb.Kernel.Tree) =>
      if (_root_.GebMirror.Metalogic.«Prelude.and»
        (_root_.Geb.Kernel.Const.eq
          (_root_.GebMirror.Metalogic.«Combinator.tySort» x0)
          (_root_.Geb.Kernel.leaf 0))
        (_root_.GebMirror.Metalogic.«Prelude.and»
          (_root_.Geb.Kernel.Const.eq
            (_root_.GebMirror.Metalogic.«Combinator.tySort» x1)
            (_root_.Geb.Kernel.leaf 0))
          (_root_.Geb.Kernel.Const.equal
            (_root_.GebMirror.Metalogic.«Combinator.tyLo» x0)
            (_root_.GebMirror.Metalogic.«Combinator.tyLo» x1)))).label ≠ 0 then
        _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6f6b205429»
          (_root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e726573205429»
            (if (_root_.GebMirror.Metalogic.«Combinator.stInfer» x3).label ≠ 0 then
              _root_.Geb.Kernel.Const.node
                (_root_.Geb.Kernel.leaf 10)
                (_root_.GebMirror.Metalogic.«Theory.l2»
                  (_root_.GebMirror.Metalogic.«Combinator.tyT» x0)
                  (_root_.GebMirror.Metalogic.«Combinator.tyT» x1))
            else
              _root_.GebMirror.Metalogic.«Combinator.cTrans»
                (_root_.GebMirror.Metalogic.«Combinator.tyLoC» x0)
                (_root_.GebMirror.Metalogic.«Combinator.cSymm»
                  (_root_.GebMirror.Metalogic.«Combinator.tyLoC» x1)))
            x3)
      else
        _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e626164205429»);
    x2

def «$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e505479205429» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x4)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x5 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x5
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x6 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x5
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x8);
                                          let x8 : _root_.Geb.Kernel.Tree := x6;
                                          let x9 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x8;
                                          let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x9
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x10 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x10);
                                          let x11 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x9
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let x12 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x11
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x12 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x11
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x14);
                                          x1 x10 x2 x12
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e626164205429»);
    x4

def «$28436f6d62696e61746f722e436f6d702e70757265205429» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (_ : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6f6b205429»
      (_root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e726573205429»
        x0
        x2);
    x3

def «Combinator.proveHyp» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e505479205429»
      (x0 x1 (_root_.GebMirror.Metalogic.«PartialHorn.eqLhs» x2))
      (fun (x3 : _root_.Geb.Kernel.Tree) =>
        if (_root_.Geb.Kernel.Const.equal
          (_root_.GebMirror.Metalogic.«PartialHorn.eqLhs» x2)
          (_root_.GebMirror.Metalogic.«PartialHorn.eqRhs» x2)).label ≠ 0 then
          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265205429»
            (_root_.GebMirror.Metalogic.«Combinator.tyDfd» x3)
        else
          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e505479205429»
            (x0 x1 (_root_.GebMirror.Metalogic.«PartialHorn.eqRhs» x2))
            (fun (x4 : _root_.Geb.Kernel.Tree) =>
              _root_.GebMirror.Metalogic.«Combinator.objEq» x3 x4));
    x3

def «$28436f6d62696e61746f722e436f6d702e62696e64205061727469616c486f726e2e53657175656e74204c616e67756167652e545061697229» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x4)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x5 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x5
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x6 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x5
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x8);
                                          let x8 : _root_.Geb.Kernel.Tree := x6;
                                          let x9 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x8;
                                          let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x9
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x10 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x10);
                                          let x11 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x9
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let x12 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x11
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x12 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x11
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x14);
                                          x1 x10 x2 x12
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e626164204c616e67756167652e545061697229»);
    x4

def «$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e4365727473204c616e67756167652e545061697229» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x4)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x5 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x5
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x6 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x5
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x8);
                                          let x8 : _root_.Geb.Kernel.Tree := x6;
                                          let x9 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x8;
                                          let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x9
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x10 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x10);
                                          let x11 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x9
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let x12 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x11
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x12 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x11
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x14);
                                          x1 x10 x2 x12
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e626164204c616e67756167652e545061697229»);
    x4

def «$285365712e6c656e67746820436f6d62696e61746f722e50547929» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (_ : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.add x2 (_root_.Geb.Kernel.leaf 1))
      (_root_.Geb.Kernel.leaf 0)
      x0;
    x1

def «$284d61702e6d617020436f6d62696e61746f722e505479205429» :=
  fun (x0 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        ((x0 x2) :: x3))
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      x1;
    x2

def «$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e505479204c616e67756167652e545061697229» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x4)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x5 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x5
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x6 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x5
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x8);
                                          let x8 : _root_.Geb.Kernel.Tree := x6;
                                          let x9 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x8;
                                          let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x9
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x10 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x10);
                                          let x11 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x9
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let x12 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x11
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x12 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x11
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x14);
                                          x1 x10 x2 x12
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e626164204c616e67756167652e545061697229»);
    x4

def «$28436f6d62696e61746f722e436f6d702e70757265204c616e67756167652e545061697229» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (_ : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6f6b204c616e67756167652e545061697229»
      (_root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e726573204c616e67756167652e545061697229»
        x0
        x2);
    x3

def «Combinator.pBound» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64205061727469616c486f726e2e53657175656e74204c616e67756167652e545061697229»
      (_root_.GebMirror.Metalogic.«Combinator.axiomAt» x3)
      (fun (x5 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e4365727473204c616e67756167652e545061697229»
          (_root_.GebMirror.Metalogic.«Combinator.mapMEqC»
            (fun (x6 : _root_.Geb.Kernel.Tree) =>
              if (_root_.Geb.Kernel.Const.equal
                x6
                (_root_.GebMirror.Metalogic.«Theory.dfd»
                  (_root_.GebMirror.Metalogic.«PartialHorn.opVars»
                    x2
                    (_root_.GebMirror.Metalogic.«$285365712e6c656e67746820436f6d62696e61746f722e50547929»
                      x1)))).label ≠ 0 then
                _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265205429» x4
              else
                _root_.GebMirror.Metalogic.«Combinator.proveHyp» x0 x1 x6)
            (_root_.GebMirror.Metalogic.«PartialHorn.seqHyps» x5))
          (fun (x6 : _root_.Geb.Kernel.Tree) =>
            let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.cAx»
              x3
              (_root_.GebMirror.Metalogic.«$284d61702e6d617020436f6d62696e61746f722e505479205429»
                _root_.GebMirror.Metalogic.«Combinator.tyT»
                x1)
              (_root_.GebMirror.Metalogic.«$284d61702e6d617020436f6d62696e61746f722e505479205429»
                _root_.GebMirror.Metalogic.«Combinator.tyDfd»
                x1)
              (_root_.GebMirror.Metalogic.«Combinator.certsOf» x6);
            _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e505479204c616e67756167652e545061697229»
              (x0
                x1
                (_root_.GebMirror.Metalogic.«PartialHorn.eqRhs»
                  (_root_.GebMirror.Metalogic.«PartialHorn.seqConcl» x5)))
              (fun (x8 : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265204c616e67756167652e545061697229»
                  (_root_.GebMirror.Metalogic.«Language.pr»
                    (_root_.GebMirror.Metalogic.«Combinator.tyLo» x8)
                    (_root_.GebMirror.Metalogic.«Combinator.cTrans»
                      x7
                      (_root_.GebMirror.Metalogic.«Combinator.tyLoC» x8))))));
    x5

def «$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e50537420436f6d62696e61746f722e50547929» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x4)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x5 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x5
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x6 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x5
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x8);
                                          let x8 : _root_.Geb.Kernel.Tree := x6;
                                          let x9 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x8;
                                          let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x9
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x10 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x10);
                                          let x11 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x9
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let x12 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x11
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x12 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x11
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x14);
                                          x1 x10 x2 x12
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62616420436f6d62696e61746f722e50547929»);
    x4

def «$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e50547920436f6d62696e61746f722e50547929» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x4)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x5 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x5
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x6 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x5
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x8);
                                          let x8 : _root_.Geb.Kernel.Tree := x6;
                                          let x9 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x8;
                                          let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x9
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x10 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x10);
                                          let x11 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x9
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let x12 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x11
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x12 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x11
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x14);
                                          x1 x10 x2 x12
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62616420436f6d62696e61746f722e50547929»);
    x4

def «$28436f6d62696e61746f722e436f6d702e6661696c20436f6d62696e61746f722e50547929» :=
  fun (_ : _root_.Geb.Kernel.Tree) (_ : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62616420436f6d62696e61746f722e50547929»;
    x2

def «Combinator.typeDefined» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e50537420436f6d62696e61746f722e50547929»
      _root_.GebMirror.Metalogic.«Combinator.pmGet»
      (fun (x4 : _root_.Geb.Kernel.Tree) =>
        let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e74684f66205061727469616c486f726e2e504465666e29»
          (_root_.GebMirror.Metalogic.«Combinator.stDefs» x4)
          x1;
        if (_root_.GebMirror.Metalogic.«$284f7074696f6e2e69734a757374205061727469616c486f726e2e504465666e29»
          x5).label ≠ 0 then
          let x6 : _root_.List
            _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$284d61702e6d617020436f6d62696e61746f722e505479205429»
            _root_.GebMirror.Metalogic.«Combinator.tyT»
            x3;
          let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«PartialHorn.phOp»
            (_root_.Geb.Kernel.Const.add
              (_root_.GebMirror.Metalogic.«$285365712e6c656e677468205061727469616c486f726e2e4f7053696729»
                _root_.GebMirror.Metalogic.«Theory.sig»)
              x1)
            x6;
          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e50547920436f6d62696e61746f722e50547929»
            (x0
              x3
              (_root_.GebMirror.Metalogic.«PartialHorn.pdBody»
                (_root_.GebMirror.Metalogic.«$284f7074696f6e2e66726f6d4d61796265205061727469616c486f726e2e504465666e29»
                  _root_.GebMirror.Metalogic.«Combinator.pdefn0»
                  x5)))
            (fun (x8 : _root_.Geb.Kernel.Tree) =>
              _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e50537420436f6d62696e61746f722e50547929»
                _root_.GebMirror.Metalogic.«Combinator.pmGet»
                (fun (x9 : _root_.Geb.Kernel.Tree) =>
                  if (_root_.GebMirror.Metalogic.«Combinator.stInfer» x9).label ≠ 0 then
                    let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.node
                      (_root_.Geb.Kernel.leaf 9)
                      (_root_.GebMirror.Metalogic.«Prelude.single» x7);
                    _root_.GebMirror.Metalogic.«Combinator.memoRet»
                      (if (_root_.Geb.Kernel.Const.eq
                        x2
                        (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                        _root_.GebMirror.Metalogic.«Combinator.pty»
                          x7
                          (_root_.Geb.Kernel.leaf 0)
                          x10
                          (_root_.GebMirror.Metalogic.«Combinator.tyLo» x8)
                          (_root_.Geb.Kernel.Const.node
                            (_root_.Geb.Kernel.leaf 10)
                            (_root_.GebMirror.Metalogic.«Theory.l2» x7 (_root_.GebMirror.Metalogic.«Combinator.tyLo» x8)))
                          (_root_.GebMirror.Metalogic.«Combinator.tyLo» x8)
                          (_root_.Geb.Kernel.Const.node
                            (_root_.Geb.Kernel.leaf 10)
                            (_root_.GebMirror.Metalogic.«Theory.l2» x7 (_root_.GebMirror.Metalogic.«Combinator.tyLo» x8)))
                      else
                        _root_.GebMirror.Metalogic.«Combinator.pty»
                          x7
                          (_root_.Geb.Kernel.leaf 1)
                          x10
                          (_root_.GebMirror.Metalogic.«Combinator.tyLo» x8)
                          (_root_.Geb.Kernel.Const.node
                            (_root_.Geb.Kernel.leaf 10)
                            (_root_.GebMirror.Metalogic.«Theory.l2»
                              (_root_.GebMirror.Metalogic.«Theory.dom» x7)
                              (_root_.GebMirror.Metalogic.«Combinator.tyLo» x8)))
                          (_root_.GebMirror.Metalogic.«Combinator.tyHi» x8)
                          (_root_.Geb.Kernel.Const.node
                            (_root_.Geb.Kernel.leaf 10)
                            (_root_.GebMirror.Metalogic.«Theory.l2»
                              (_root_.GebMirror.Metalogic.«Theory.cod» x7)
                              (_root_.GebMirror.Metalogic.«Combinator.tyHi» x8))))
                  else
                    _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64205420436f6d62696e61746f722e50547929»
                      (_root_.GebMirror.Metalogic.«Combinator.addLemma»
                        (_root_.GebMirror.Metalogic.«PartialHorn.eqn»
                          x7
                          (_root_.GebMirror.Metalogic.«Combinator.tyT» x8))
                        (_root_.GebMirror.Metalogic.«Combinator.cAx»
                          (_root_.GebMirror.Metalogic.«Infer.defAxIdx» x1)
                          x6
                          (_root_.GebMirror.Metalogic.«$284d61702e6d617020436f6d62696e61746f722e505479205429»
                            _root_.GebMirror.Metalogic.«Combinator.tyDfd»
                            x3)
                          (_root_.GebMirror.Metalogic.«Prelude.single»
                            (_root_.GebMirror.Metalogic.«Combinator.tyDfd» x8))))
                      (fun (x10 : _root_.Geb.Kernel.Tree) =>
                        _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64205420436f6d62696e61746f722e50547929»
                          (_root_.GebMirror.Metalogic.«Combinator.addLemma»
                            (_root_.GebMirror.Metalogic.«Theory.dfd» x7)
                            (_root_.GebMirror.Metalogic.«Combinator.cTrans»
                              x10
                              (_root_.GebMirror.Metalogic.«Combinator.cSymm» x10)))
                          (fun (x11 : _root_.Geb.Kernel.Tree) =>
                            if (_root_.Geb.Kernel.Const.eq
                              x2
                              (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                              _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64205420436f6d62696e61746f722e50547929»
                                (_root_.GebMirror.Metalogic.«Combinator.addLemma»
                                  (_root_.GebMirror.Metalogic.«PartialHorn.eqn»
                                    x7
                                    (_root_.GebMirror.Metalogic.«Combinator.tyLo» x8))
                                  (_root_.GebMirror.Metalogic.«Combinator.cTrans»
                                    x10
                                    (_root_.GebMirror.Metalogic.«Combinator.tyLoC» x8)))
                                (fun (x12 : _root_.Geb.Kernel.Tree) =>
                                  _root_.GebMirror.Metalogic.«Combinator.memoRet»
                                    (_root_.GebMirror.Metalogic.«Combinator.pty»
                                      x7
                                      (_root_.Geb.Kernel.leaf 0)
                                      x11
                                      (_root_.GebMirror.Metalogic.«Combinator.tyLo» x8)
                                      x12
                                      (_root_.GebMirror.Metalogic.«Combinator.tyLo» x8)
                                      x12))
                            else
                              _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64205420436f6d62696e61746f722e50547929»
                                (_root_.GebMirror.Metalogic.«Combinator.addLemma»
                                  (_root_.GebMirror.Metalogic.«PartialHorn.eqn»
                                    (_root_.GebMirror.Metalogic.«Theory.dom» x7)
                                    (_root_.GebMirror.Metalogic.«Combinator.tyLo» x8))
                                  (_root_.GebMirror.Metalogic.«Combinator.cTrans»
                                    (_root_.GebMirror.Metalogic.«Combinator.cCong»
                                      (_root_.GebMirror.Metalogic.«Combinator.cAx»
                                        (_root_.Geb.Kernel.leaf 0)
                                        (_root_.GebMirror.Metalogic.«Prelude.single» x7)
                                        (_root_.GebMirror.Metalogic.«Prelude.single» x11)
                                        ([] : _root_.List _root_.Geb.Kernel.Tree))
                                      (_root_.GebMirror.Metalogic.«Prelude.single» x10))
                                    (_root_.GebMirror.Metalogic.«Combinator.tyLoC» x8)))
                                (fun (x12 : _root_.Geb.Kernel.Tree) =>
                                  _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64205420436f6d62696e61746f722e50547929»
                                    (_root_.GebMirror.Metalogic.«Combinator.addLemma»
                                      (_root_.GebMirror.Metalogic.«PartialHorn.eqn»
                                        (_root_.GebMirror.Metalogic.«Theory.cod» x7)
                                        (_root_.GebMirror.Metalogic.«Combinator.tyHi» x8))
                                      (_root_.GebMirror.Metalogic.«Combinator.cTrans»
                                        (_root_.GebMirror.Metalogic.«Combinator.cCong»
                                          (_root_.GebMirror.Metalogic.«Combinator.cAx»
                                            (_root_.Geb.Kernel.leaf 1)
                                            (_root_.GebMirror.Metalogic.«Prelude.single» x7)
                                            (_root_.GebMirror.Metalogic.«Prelude.single» x11)
                                            ([] : _root_.List _root_.Geb.Kernel.Tree))
                                          (_root_.GebMirror.Metalogic.«Prelude.single» x10))
                                        (_root_.GebMirror.Metalogic.«Combinator.tyHiC» x8)))
                                    (fun (x13 : _root_.Geb.Kernel.Tree) =>
                                      _root_.GebMirror.Metalogic.«Combinator.memoRet»
                                        (_root_.GebMirror.Metalogic.«Combinator.pty»
                                          x7
                                          (_root_.Geb.Kernel.leaf 1)
                                          x11
                                          (_root_.GebMirror.Metalogic.«Combinator.tyLo» x8)
                                          x12
                                          (_root_.GebMirror.Metalogic.«Combinator.tyHi» x8)
                                          x13)))))))
        else
          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6661696c20436f6d62696e61746f722e50547929»);
    x4

def «$28436f6d62696e61746f722e436f6d702e62696e64205061727469616c486f726e2e53657175656e74205429» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x4)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x5 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x5
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x6 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x5
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x8);
                                          let x8 : _root_.Geb.Kernel.Tree := x6;
                                          let x9 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x8;
                                          let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x9
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x10 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x10);
                                          let x11 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x9
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let x12 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x11
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x12 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x11
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x14);
                                          x1 x10 x2 x12
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e626164205429»);
    x4

def «$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e4365727473205429» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x4)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x5 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x5
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x6 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x5
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x8);
                                          let x8 : _root_.Geb.Kernel.Tree := x6;
                                          let x9 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x8;
                                          let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x9
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x10 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x10);
                                          let x11 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x9
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let x12 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x11
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x12 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x11
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x14);
                                          x1 x10 x2 x12
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e626164205429»);
    x4

def «$28436f6d62696e61746f722e436f6d702e6661696c205429» :=
  fun (_ : _root_.Geb.Kernel.Tree) (_ : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e626164205429»;
    x2

def «Combinator.typeOpDfd» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (let x3 : _root_.List
                                     _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$284d61702e6d617020436f6d62696e61746f722e505479205429»
                                     _root_.GebMirror.Metalogic.«Combinator.tyT»
                                     x2;
                                   let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e74684f662032383a284f7074696f6e2e4d6179626520496e6665722e44666452756c652929»
                                     _root_.GebMirror.Metalogic.«Infer.dfdRules»
                                     x1;
                                   if (_root_.Geb.Kernel.Const.eq
                                     (_root_.Geb.Kernel.Const.label x4)
                                     (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                     let x5 : _root_.List
                                       _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                       x4;
                                     let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                       (α := _root_.Geb.Kernel.Tree)
                                       (β := _root_.Geb.Kernel.Tree)
                                       x5
                                       (_root_.Geb.Kernel.leaf 0)
                                       (fun (x6 : _root_.Geb.Kernel.Tree)
                                          (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                         x6);
                                     let _ : _root_.List
                                       _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                       (α := _root_.Geb.Kernel.Tree)
                                       (β := _root_.List _root_.Geb.Kernel.Tree)
                                       x5
                                       ([] : _root_.List _root_.Geb.Kernel.Tree)
                                       (fun (_ : _root_.Geb.Kernel.Tree)
                                          (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                         x8);
                                     let x8 : _root_.Geb.Kernel.Tree := x6;
                                     if (_root_.Geb.Kernel.Const.eq
                                       (_root_.Geb.Kernel.Const.label x8)
                                       (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                       let x9 : _root_.List
                                         _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                         x8;
                                       let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                         (α := _root_.Geb.Kernel.Tree)
                                         (β := _root_.Geb.Kernel.Tree)
                                         x9
                                         (_root_.Geb.Kernel.leaf 0)
                                         (fun (x10 : _root_.Geb.Kernel.Tree)
                                            (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                           x10);
                                       let _ : _root_.List
                                         _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                         (α := _root_.Geb.Kernel.Tree)
                                         (β := _root_.List _root_.Geb.Kernel.Tree)
                                         x9
                                         ([] : _root_.List _root_.Geb.Kernel.Tree)
                                         (fun (_ : _root_.Geb.Kernel.Tree)
                                            (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                                           x12);
                                       let x12 : _root_.Geb.Kernel.Tree := x10;
                                       if (_root_.Geb.Kernel.Const.eq
                                         (_root_.Geb.Kernel.Const.label x12)
                                         (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                                         let x13 : _root_.List
                                           _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                           x12;
                                         let x14 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                           (α := _root_.Geb.Kernel.Tree)
                                           (β := _root_.Geb.Kernel.Tree)
                                           x13
                                           (_root_.Geb.Kernel.leaf 0)
                                           (fun (x14 : _root_.Geb.Kernel.Tree)
                                              (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                             x14);
                                         let _ : _root_.List
                                           _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                           (α := _root_.Geb.Kernel.Tree)
                                           (β := _root_.List _root_.Geb.Kernel.Tree)
                                           x13
                                           ([] : _root_.List _root_.Geb.Kernel.Tree)
                                           (fun (_ : _root_.Geb.Kernel.Tree)
                                              (x16 : _root_.List _root_.Geb.Kernel.Tree) =>
                                             x16);
                                         _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64205061727469616c486f726e2e53657175656e74205429»
                                           (_root_.GebMirror.Metalogic.«Combinator.axiomAt» x14)
                                           (fun (x16 : _root_.Geb.Kernel.Tree) =>
                                             _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e4365727473205429»
                                               (_root_.GebMirror.Metalogic.«Combinator.mapMEqC»
                                                 (_root_.GebMirror.Metalogic.«Combinator.proveHyp» x0 x2)
                                                 (_root_.GebMirror.Metalogic.«PartialHorn.seqHyps» x16))
                                               (fun (x17 : _root_.Geb.Kernel.Tree) =>
                                                 _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265205429»
                                                   (_root_.GebMirror.Metalogic.«Combinator.cAx»
                                                     x14
                                                     x3
                                                     (_root_.GebMirror.Metalogic.«$284d61702e6d617020436f6d62696e61746f722e505479205429»
                                                       _root_.GebMirror.Metalogic.«Combinator.tyDfd»
                                                       x2)
                                                     (_root_.GebMirror.Metalogic.«Combinator.certsOf» x17))))
                                       else
                                         if (_root_.Geb.Kernel.Const.eq
                                           (_root_.Geb.Kernel.Const.label x12)
                                           (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                           let x13 : _root_.List
                                             _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                             x12;
                                           let x14 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                             (α := _root_.Geb.Kernel.Tree)
                                             (β := _root_.Geb.Kernel.Tree)
                                             x13
                                             (_root_.Geb.Kernel.leaf 0)
                                             (fun (x14 : _root_.Geb.Kernel.Tree)
                                                (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                               x14);
                                           let _ : _root_.List
                                             _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                             (α := _root_.Geb.Kernel.Tree)
                                             (β := _root_.List _root_.Geb.Kernel.Tree)
                                             x13
                                             ([] : _root_.List _root_.Geb.Kernel.Tree)
                                             (fun (_ : _root_.Geb.Kernel.Tree)
                                                (x16 : _root_.List _root_.Geb.Kernel.Tree) =>
                                               x16);
                                           _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265205429»
                                             (_root_.GebMirror.Metalogic.«Combinator.cStrict»
                                               (_root_.Geb.Kernel.leaf 0)
                                               (_root_.GebMirror.Metalogic.«Combinator.cAx»
                                                 x14
                                                 x3
                                                 (_root_.GebMirror.Metalogic.«$284d61702e6d617020436f6d62696e61746f722e505479205429»
                                                   _root_.GebMirror.Metalogic.«Combinator.tyDfd»
                                                   x2)
                                                 ([] : _root_.List _root_.Geb.Kernel.Tree)))
                                         else
                                           let x13 : _root_.List
                                             _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                             x12;
                                           let x14 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                             (α := _root_.Geb.Kernel.Tree)
                                             (β := _root_.Geb.Kernel.Tree)
                                             x13
                                             (_root_.Geb.Kernel.leaf 0)
                                             (fun (x14 : _root_.Geb.Kernel.Tree)
                                                (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                               x14);
                                           let _ : _root_.List
                                             _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                             (α := _root_.Geb.Kernel.Tree)
                                             (β := _root_.List _root_.Geb.Kernel.Tree)
                                             x13
                                             ([] : _root_.List _root_.Geb.Kernel.Tree)
                                             (fun (_ : _root_.Geb.Kernel.Tree)
                                                (x16 : _root_.List _root_.Geb.Kernel.Tree) =>
                                               x16);
                                           let x16 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.cAx»
                                             x14
                                             ([] : _root_.List _root_.Geb.Kernel.Tree)
                                             ([] : _root_.List _root_.Geb.Kernel.Tree)
                                             ([] : _root_.List _root_.Geb.Kernel.Tree);
                                           _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265205429»
                                             (_root_.GebMirror.Metalogic.«Combinator.cTrans»
                                               (_root_.GebMirror.Metalogic.«Combinator.cSymm» x16)
                                               x16)
                                     else
                                       let _ : _root_.List
                                         _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                         x8;
                                       _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6661696c205429»
                                   else
                                     let _ : _root_.List
                                       _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                       x4;
                                     _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6661696c205429»);
    x3

def «Combinator.typeOpObj» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«PartialHorn.phOp»
                                     x0
                                     (_root_.GebMirror.Metalogic.«$284d61702e6d617020436f6d62696e61746f722e505479205429»
                                       (fun (x4 : _root_.Geb.Kernel.Tree) =>
                                         if (_root_.Geb.Kernel.Const.eq
                                           (_root_.GebMirror.Metalogic.«Combinator.tySort» x4)
                                           (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                                           _root_.GebMirror.Metalogic.«Combinator.tyLo» x4
                                         else
                                           _root_.GebMirror.Metalogic.«Combinator.tyT» x4)
                                       x3);
                                   if (_root_.Geb.Kernel.Const.equal x4 x1).label ≠ 0 then
                                     _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e7075726520436f6d62696e61746f722e50547929»
                                       (_root_.GebMirror.Metalogic.«Combinator.pty»
                                         x1
                                         (_root_.Geb.Kernel.leaf 0)
                                         x2
                                         x1
                                         x2
                                         x1
                                         x2)
                                   else
                                     _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64205420436f6d62696e61746f722e50547929»
                                       (_root_.GebMirror.Metalogic.«Combinator.eqCert»
                                         (_root_.GebMirror.Metalogic.«PartialHorn.eqn» x1 x4)
                                         (_root_.GebMirror.Metalogic.«Combinator.cCong»
                                           x2
                                           (_root_.GebMirror.Metalogic.«$284d61702e6d617020436f6d62696e61746f722e505479205429»
                                             (fun (x5 : _root_.Geb.Kernel.Tree) =>
                                               if (_root_.Geb.Kernel.Const.eq
                                                 (_root_.GebMirror.Metalogic.«Combinator.tySort» x5)
                                                 (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                                                 _root_.GebMirror.Metalogic.«Combinator.tyLoC» x5
                                               else
                                                 _root_.GebMirror.Metalogic.«Combinator.tyDfd» x5)
                                             x3)))
                                       (fun (x5 : _root_.Geb.Kernel.Tree) =>
                                         _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e7075726520436f6d62696e61746f722e50547929»
                                           (_root_.GebMirror.Metalogic.«Combinator.pty»
                                             x1
                                             (_root_.Geb.Kernel.leaf 0)
                                             x2
                                             x4
                                             x5
                                             x4
                                             x5)));
    x4

def «$285365712e7461696c20436f6d62696e61746f722e50547929» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      x0
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      (fun (_ : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
        x2);
    x1

def «$285365712e64726f7020436f6d62696e61746f722e50547929» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.iter
      (α := _root_.List _root_.Geb.Kernel.Tree)
      _root_.GebMirror.Metalogic.«$285365712e7461696c20436f6d62696e61746f722e50547929»
      x1
      x0;
    x2

def «$285365712e61744f7220436f6d62696e61746f722e50547929» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«$285365712e64726f7020436f6d62696e61746f722e50547929»
        x2
        x1)
      x0
      (fun (x3 : _root_.Geb.Kernel.Tree)
         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        x3);
    x3

def «$28436f6d62696e61746f722e436f6d702e62696e64204c616e67756167652e545061697220436f6d62696e61746f722e50547929» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x4)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x5 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x5
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x6 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x5
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x8);
                                          let x8 : _root_.Geb.Kernel.Tree := x6;
                                          let x9 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x8;
                                          let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x9
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x10 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x10);
                                          let x11 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x9
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let x12 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x11
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x12 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x11
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x14);
                                          x1 x10 x2 x12
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62616420436f6d62696e61746f722e50547929»);
    x4

def «Combinator.typeOpTy» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x6 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (if (_root_.Geb.Kernel.Const.eq
      x2
      (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
      if (_root_.GebMirror.Metalogic.«Prelude.and»
        (_root_.Geb.Kernel.Const.eq x1 (_root_.Geb.Kernel.leaf 0))
        (_root_.Geb.Kernel.Const.eq
          (_root_.GebMirror.Metalogic.«$285365712e6c656e67746820436f6d62696e61746f722e50547929»
            x5)
          (_root_.Geb.Kernel.leaf 1))).label ≠ 0 then
        let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$285365712e61744f7220436f6d62696e61746f722e50547929»
          _root_.GebMirror.Metalogic.«Combinator.pty0»
          x5
          (_root_.Geb.Kernel.leaf 0);
        _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e7075726520436f6d62696e61746f722e50547929»
          (_root_.GebMirror.Metalogic.«Combinator.pty»
            x3
            (_root_.Geb.Kernel.leaf 0)
            x4
            (_root_.GebMirror.Metalogic.«Combinator.tyLo» x6)
            (_root_.GebMirror.Metalogic.«Combinator.tyLoC» x6)
            (_root_.GebMirror.Metalogic.«Combinator.tyLo» x6)
            (_root_.GebMirror.Metalogic.«Combinator.tyLoC» x6))
      else
        if (_root_.GebMirror.Metalogic.«Prelude.and»
          (_root_.Geb.Kernel.Const.eq x1 (_root_.Geb.Kernel.leaf 1))
          (_root_.Geb.Kernel.Const.eq
            (_root_.GebMirror.Metalogic.«$285365712e6c656e67746820436f6d62696e61746f722e50547929»
              x5)
            (_root_.Geb.Kernel.leaf 1))).label ≠ 0 then
          let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$285365712e61744f7220436f6d62696e61746f722e50547929»
            _root_.GebMirror.Metalogic.«Combinator.pty0»
            x5
            (_root_.Geb.Kernel.leaf 0);
          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e7075726520436f6d62696e61746f722e50547929»
            (_root_.GebMirror.Metalogic.«Combinator.pty»
              x3
              (_root_.Geb.Kernel.leaf 0)
              x4
              (_root_.GebMirror.Metalogic.«Combinator.tyHi» x6)
              (_root_.GebMirror.Metalogic.«Combinator.tyHiC» x6)
              (_root_.GebMirror.Metalogic.«Combinator.tyHi» x6)
              (_root_.GebMirror.Metalogic.«Combinator.tyHiC» x6))
        else
          _root_.GebMirror.Metalogic.«Combinator.typeOpObj» x1 x3 x4 x5
    else
      let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.nth»
        _root_.GebMirror.Metalogic.«Infer.domRules»
        x1;
      let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.nth»
        _root_.GebMirror.Metalogic.«Infer.codRules»
        x1;
      if (_root_.GebMirror.Metalogic.«Prelude.and»
        (_root_.GebMirror.Metalogic.«Prelude.and»
          (_root_.GebMirror.Metalogic.«Prelude.isSome» x6)
          (_root_.GebMirror.Metalogic.«Prelude.isSome» (_root_.GebMirror.Metalogic.«Prelude.get» x6)))
        (_root_.GebMirror.Metalogic.«Prelude.and»
          (_root_.GebMirror.Metalogic.«Prelude.isSome» x7)
          (_root_.GebMirror.Metalogic.«Prelude.isSome»
            (_root_.GebMirror.Metalogic.«Prelude.get» x7)))).label ≠ 0 then
        _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64204c616e67756167652e545061697220436f6d62696e61746f722e50547929»
          (_root_.GebMirror.Metalogic.«Combinator.pBound»
            x0
            x5
            x1
            (_root_.GebMirror.Metalogic.«Prelude.get» (_root_.GebMirror.Metalogic.«Prelude.get» x6))
            x4)
          (fun (x8 : _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64204c616e67756167652e545061697220436f6d62696e61746f722e50547929»
              (_root_.GebMirror.Metalogic.«Combinator.pBound»
                x0
                x5
                x1
                (_root_.GebMirror.Metalogic.«Prelude.get» (_root_.GebMirror.Metalogic.«Prelude.get» x7))
                x4)
              (fun (x9 : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64205420436f6d62696e61746f722e50547929»
                  (_root_.GebMirror.Metalogic.«Combinator.eqCert»
                    (_root_.GebMirror.Metalogic.«PartialHorn.eqn»
                      (_root_.GebMirror.Metalogic.«Theory.dom» x3)
                      (_root_.GebMirror.Metalogic.«Language.p1» x8))
                    (_root_.GebMirror.Metalogic.«Language.p2» x8))
                  (fun (x10 : _root_.Geb.Kernel.Tree) =>
                    _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64205420436f6d62696e61746f722e50547929»
                      (_root_.GebMirror.Metalogic.«Combinator.eqCert»
                        (_root_.GebMirror.Metalogic.«PartialHorn.eqn»
                          (_root_.GebMirror.Metalogic.«Theory.cod» x3)
                          (_root_.GebMirror.Metalogic.«Language.p1» x9))
                        (_root_.GebMirror.Metalogic.«Language.p2» x9))
                      (fun (x11 : _root_.Geb.Kernel.Tree) =>
                        _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e7075726520436f6d62696e61746f722e50547929»
                          (_root_.GebMirror.Metalogic.«Combinator.pty»
                            x3
                            (_root_.Geb.Kernel.leaf 1)
                            x4
                            (_root_.GebMirror.Metalogic.«Language.p1» x8)
                            x10
                            (_root_.GebMirror.Metalogic.«Language.p1» x9)
                            x11)))))
      else
        _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6661696c20436f6d62696e61746f722e50547929»);
    x6

def «Combinator.opSig0» :=
  _root_.GebMirror.Metalogic.«PartialHorn.opSig»
    (_root_.GebMirror.Metalogic.«PartialHorn.sorts»
      ([] : _root_.List _root_.Geb.Kernel.Tree))
    (_root_.Geb.Kernel.leaf 0)

def «$284f7074696f6e2e69734a757374205061727469616c486f726e2e4f7053696729» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x1)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x2 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x1;
                                          let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x2
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x3 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x3);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x2
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x5);
                                          _root_.Geb.Kernel.leaf 1
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x1;
                                          _root_.Geb.Kernel.leaf 0);
    x1

def «$284f7074696f6e2e66726f6d4d61796265205061727469616c486f726e2e4f7053696729» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (let x2 : _root_.Geb.Kernel.Tree := x1;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x2)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x3 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x2;
                                          let x4 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x3
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x4 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x4);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x3
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x6 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          x4
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x2;
                                          x0);
    x2

def «Combinator.typeOp» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e50537420436f6d62696e61746f722e50547929»
      _root_.GebMirror.Metalogic.«Combinator.pmGet»
      (fun (x3 : _root_.Geb.Kernel.Tree) =>
        let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e74684f66205061727469616c486f726e2e4f7053696729»
          (_root_.GebMirror.Metalogic.«Combinator.stSig» x3)
          x1;
        if (_root_.GebMirror.Metalogic.«$284f7074696f6e2e69734a757374205061727469616c486f726e2e4f7053696729»
          x4).label ≠ 0 then
          let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$284f7074696f6e2e66726f6d4d61796265205061727469616c486f726e2e4f7053696729»
            _root_.GebMirror.Metalogic.«Combinator.opSig0»
            x4;
          if (_root_.GebMirror.Metalogic.«Base.equalTs»
            (_root_.GebMirror.Metalogic.«$284d61702e6d617020436f6d62696e61746f722e505479205429»
              _root_.GebMirror.Metalogic.«Combinator.tySort»
              x2)
            (_root_.GebMirror.Metalogic.«PartialHorn.opArgs» x5)).label ≠ 0 then
            if (_root_.Geb.Kernel.Const.lt
              x1
              (_root_.GebMirror.Metalogic.«$285365712e6c656e677468205061727469616c486f726e2e4f7053696729»
                _root_.GebMirror.Metalogic.«Theory.sig»)).label ≠ 0 then
              let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«PartialHorn.phOp»
                x1
                (_root_.GebMirror.Metalogic.«$284d61702e6d617020436f6d62696e61746f722e505479205429»
                  _root_.GebMirror.Metalogic.«Combinator.tyT»
                  x2);
              _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64205420436f6d62696e61746f722e50547929»
                (_root_.GebMirror.Metalogic.«Combinator.typeOpDfd» x0 x1 x2)
                (fun (x7 : _root_.Geb.Kernel.Tree) =>
                  _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64205420436f6d62696e61746f722e50547929»
                    (_root_.GebMirror.Metalogic.«Combinator.dfdCert» x6 x7)
                    (fun (x8 : _root_.Geb.Kernel.Tree) =>
                      _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e50547920436f6d62696e61746f722e50547929»
                        (_root_.GebMirror.Metalogic.«Combinator.typeOpTy»
                          x0
                          x1
                          (_root_.GebMirror.Metalogic.«PartialHorn.opSort» x5)
                          x6
                          x8
                          x2)
                        _root_.GebMirror.Metalogic.«Combinator.memoRet»))
            else
              _root_.GebMirror.Metalogic.«Combinator.typeDefined»
                x0
                (_root_.Geb.Kernel.Const.sub
                  x1
                  (_root_.GebMirror.Metalogic.«$285365712e6c656e677468205061727469616c486f726e2e4f7053696729»
                    _root_.GebMirror.Metalogic.«Theory.sig»))
                (_root_.GebMirror.Metalogic.«PartialHorn.opSort» x5)
                x2
          else
            _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6661696c20436f6d62696e61746f722e50547929»
        else
          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6661696c20436f6d62696e61746f722e50547929»);
    x3

def «$28436f6d62696e61746f722e436f6d702e62696e642032393a284f7074696f6e2e4d6179626520436f6d62696e61746f722e5054792920436f6d62696e61746f722e50547929» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x4)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x5 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x5
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x6 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x5
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x8);
                                          let x8 : _root_.Geb.Kernel.Tree := x6;
                                          let x9 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x8;
                                          let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x9
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x10 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x10);
                                          let x11 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x9
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let x12 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x11
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x12 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x11
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x14);
                                          x1 x10 x2 x12
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62616420436f6d62696e61746f722e50547929»);
    x4

def «$284f7074696f6e2e69734a75737420436f6d62696e61746f722e50547929» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x1)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x2 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x1;
                                          let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x2
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x3 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x3);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x2
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x5);
                                          _root_.Geb.Kernel.leaf 1
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x1;
                                          _root_.Geb.Kernel.leaf 0);
    x1

def «$284f7074696f6e2e66726f6d4d6179626520436f6d62696e61746f722e50547929» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (let x2 : _root_.Geb.Kernel.Tree := x1;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x2)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x3 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x2;
                                          let x4 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x3
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x4 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x4);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x3
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x6 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          x4
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x2;
                                          x0);
    x2

def «$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e5054797320436f6d62696e61746f722e50547929» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x4)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x5 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x5
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x6 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x5
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x8);
                                          let x8 : _root_.Geb.Kernel.Tree := x6;
                                          let x9 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x8;
                                          let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x9
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x10 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x10);
                                          let x11 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x9
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let x12 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x11
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x12 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x11
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x14);
                                          x1 x10 x2 x12
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62616420436f6d62696e61746f722e50547929»);
    x4

def «Combinator.typeStep» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.List
      (_root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
    let x5 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (let x5 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.label
                                     x3;
                                   if (_root_.Geb.Kernel.Const.eq
                                     x5
                                     (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                                     if (_root_.Geb.Kernel.Const.eq
                                       (_root_.GebMirror.Metalogic.«Prelude.length»
                                         (_root_.Geb.Kernel.Const.children x3))
                                       (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                       x1
                                         (_root_.Geb.Kernel.Const.label
                                           (_root_.GebMirror.Metalogic.«Prelude.at»
                                             (_root_.Geb.Kernel.Const.children x3)
                                             (_root_.Geb.Kernel.leaf 0)))
                                     else
                                       _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6661696c20436f6d62696e61746f722e50547929»
                                   else
                                     _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e642032393a284f7074696f6e2e4d6179626520436f6d62696e61746f722e5054792920436f6d62696e61746f722e50547929»
                                       (_root_.GebMirror.Metalogic.«Combinator.lookup» (x2 x3))
                                       (fun (x6 : _root_.Geb.Kernel.Tree) =>
                                         if (_root_.GebMirror.Metalogic.«$284f7074696f6e2e69734a75737420436f6d62696e61746f722e50547929»
                                           x6).label ≠ 0 then
                                           _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e7075726520436f6d62696e61746f722e50547929»
                                             (_root_.GebMirror.Metalogic.«$284f7074696f6e2e66726f6d4d6179626520436f6d62696e61746f722e50547929»
                                               _root_.GebMirror.Metalogic.«Combinator.pty0»
                                               x6)
                                         else
                                           _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e5054797320436f6d62696e61746f722e50547929»
                                             (_root_.GebMirror.Metalogic.«Combinator.seqY» x4)
                                             (fun (x7 : _root_.Geb.Kernel.Tree) =>
                                               _root_.GebMirror.Metalogic.«Combinator.typeOp»
                                                 x0
                                                 (_root_.Geb.Kernel.Const.sub
                                                   x5
                                                   (_root_.Geb.Kernel.leaf 1))
                                                 (_root_.GebMirror.Metalogic.«Combinator.ptysOf» x7))));
    x5

def «Combinator.eqn0» :=
  _root_.GebMirror.Metalogic.«PartialHorn.eqn»
    (_root_.Geb.Kernel.leaf 0)
    (_root_.Geb.Kernel.leaf 0)

def «Combinator.varSide» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x5 : _root_.Geb.Kernel.Tree)
                                     (x6 : _root_.Geb.Kernel.Tree) =>
      let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«PartialHorn.phOp»
        x3
        (_root_.GebMirror.Metalogic.«Prelude.single»
          (_root_.GebMirror.Metalogic.«PartialHorn.phVar» x1));
      let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.findIdx»
        (fun (x8 : _root_.Geb.Kernel.Tree) =>
          _root_.Geb.Kernel.Const.equal
            (_root_.GebMirror.Metalogic.«PartialHorn.eqLhs» x8)
            x7)
        (_root_.GebMirror.Metalogic.«Combinator.scHyps» x5);
      if (_root_.GebMirror.Metalogic.«Prelude.isSome» x8).label ≠ 0 then
        let x9 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.get» x8;
        let x10 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e74684f66205061727469616c486f726e2e45716e29»
          (_root_.GebMirror.Metalogic.«Combinator.scHyps» x5)
          x9;
        if (_root_.GebMirror.Metalogic.«$284f7074696f6e2e69734a757374205061727469616c486f726e2e45716e29»
          x10).label ≠ 0 then
          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e505479204c616e67756167652e545061697229»
            (x0
              (_root_.GebMirror.Metalogic.«PartialHorn.eqRhs»
                (_root_.GebMirror.Metalogic.«$284f7074696f6e2e66726f6d4d61796265205061727469616c486f726e2e45716e29»
                  _root_.GebMirror.Metalogic.«Combinator.eqn0»
                  x10)))
            (fun (x11 : _root_.Geb.Kernel.Tree) =>
              _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265204c616e67756167652e545061697229»
                (_root_.GebMirror.Metalogic.«Language.pr»
                  (_root_.GebMirror.Metalogic.«Combinator.tyLo» x11)
                  (if (x2).label ≠ 0 then
                    _root_.Geb.Kernel.Const.node
                      (_root_.Geb.Kernel.leaf 10)
                      (_root_.GebMirror.Metalogic.«Theory.l2» x7 (_root_.GebMirror.Metalogic.«Combinator.tyLo» x11))
                  else
                    _root_.GebMirror.Metalogic.«Combinator.cTrans»
                      (_root_.GebMirror.Metalogic.«Combinator.cHyp» x9)
                      (_root_.GebMirror.Metalogic.«Combinator.tyLoC» x11))))
            x5
            x6
        else
          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e626164204c616e67756167652e545061697229»
      else
        _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6f6b204c616e67756167652e545061697229»
          (_root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e726573204c616e67756167652e545061697229»
            (_root_.GebMirror.Metalogic.«Language.pr»
              x7
              (_root_.GebMirror.Metalogic.«Combinator.cAx»
                x4
                (_root_.GebMirror.Metalogic.«Prelude.single»
                  (_root_.GebMirror.Metalogic.«PartialHorn.phVar» x1))
                (_root_.GebMirror.Metalogic.«Prelude.single»
                  (_root_.GebMirror.Metalogic.«Combinator.cRefl» x1))
                ([] : _root_.List _root_.Geb.Kernel.Tree)))
            x6));
    x5

def «Combinator.typeVar» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.nth»
        (_root_.GebMirror.Metalogic.«Combinator.scCtx» x2)
        x1;
      if (_root_.GebMirror.Metalogic.«Prelude.isSome» x4).label ≠ 0 then
        let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.get» x4;
        if (_root_.Geb.Kernel.Const.eq
          x5
          (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6f6b20436f6d62696e61746f722e50547929»
            (_root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e72657320436f6d62696e61746f722e50547929»
              (_root_.GebMirror.Metalogic.«Combinator.pty»
                (_root_.GebMirror.Metalogic.«PartialHorn.phVar» x1)
                (_root_.Geb.Kernel.leaf 0)
                (_root_.GebMirror.Metalogic.«Combinator.cRefl» x1)
                (_root_.GebMirror.Metalogic.«PartialHorn.phVar» x1)
                (_root_.GebMirror.Metalogic.«Combinator.cRefl» x1)
                (_root_.GebMirror.Metalogic.«PartialHorn.phVar» x1)
                (_root_.GebMirror.Metalogic.«Combinator.cRefl» x1))
              x3)
        else
          if (_root_.Geb.Kernel.Const.eq
            x5
            (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
            let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.stInfer»
              x3;
            _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64204c616e67756167652e545061697220436f6d62696e61746f722e50547929»
              (_root_.GebMirror.Metalogic.«Combinator.varSide»
                x0
                x1
                x6
                (_root_.Geb.Kernel.leaf 0)
                (_root_.Geb.Kernel.leaf 0))
              (fun (x7 : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64204c616e67756167652e545061697220436f6d62696e61746f722e50547929»
                  (_root_.GebMirror.Metalogic.«Combinator.varSide»
                    x0
                    x1
                    x6
                    (_root_.Geb.Kernel.leaf 1)
                    (_root_.Geb.Kernel.leaf 1))
                  (fun (x8 : _root_.Geb.Kernel.Tree) =>
                    _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e7075726520436f6d62696e61746f722e50547929»
                      (_root_.GebMirror.Metalogic.«Combinator.pty»
                        (_root_.GebMirror.Metalogic.«PartialHorn.phVar» x1)
                        (_root_.Geb.Kernel.leaf 1)
                        (_root_.GebMirror.Metalogic.«Combinator.cRefl» x1)
                        (_root_.GebMirror.Metalogic.«Language.p1» x7)
                        (_root_.GebMirror.Metalogic.«Language.p2» x7)
                        (_root_.GebMirror.Metalogic.«Language.p1» x8)
                        (_root_.GebMirror.Metalogic.«Language.p2» x8))))
              x2
              x3
          else
            _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62616420436f6d62696e61746f722e50547929»
      else
        _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62616420436f6d62696e61746f722e50547929»);
    x2

def «$284f7074696f6e2e6e74684f6620436f6d62696e61746f722e50547929» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (_root_.Geb.Kernel.Const.iter
        (α := _root_.List _root_.Geb.Kernel.Tree)
        (fun (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
          _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.List _root_.Geb.Kernel.Tree)
            x2
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (fun (_ : _root_.Geb.Kernel.Tree)
               (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
              x4))
        x0
        x1)
      _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e6720436f6d62696e61746f722e50547929»
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$284f7074696f6e2e6a75737420436f6d62696e61746f722e50547929»
          x2);
    x2

def «Combinator.typerStep» :=
  fun (x0 : (_root_.List _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) ×
      (_root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
    let x1 : (_root_.List _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) ×
      (_root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree) := (fun (x1 : _root_.List _root_.Geb.Kernel.Tree)
                                          (x2 : _root_.Geb.Kernel.Tree) =>
      _root_.Geb.Kernel.Const.para
        (α := _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
        (_root_.GebMirror.Metalogic.«Combinator.typeStep»
          (x0).1
          (fun (x3 : _root_.Geb.Kernel.Tree) =>
            let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e74684f6620436f6d62696e61746f722e50547929»
              x1
              x3;
            if (_root_.GebMirror.Metalogic.«$284f7074696f6e2e69734a75737420436f6d62696e61746f722e50547929»
              x4).label ≠ 0 then
              _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e7075726520436f6d62696e61746f722e50547929»
                (_root_.GebMirror.Metalogic.«$284f7074696f6e2e66726f6d4d6179626520436f6d62696e61746f722e50547929»
                  _root_.GebMirror.Metalogic.«Combinator.pty0»
                  x4)
            else
              _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6661696c20436f6d62696e61746f722e50547929»)
          (_root_.GebMirror.Metalogic.«PartialHorn.phSubst»
            (_root_.GebMirror.Metalogic.«$284d61702e6d617020436f6d62696e61746f722e505479205429»
              _root_.GebMirror.Metalogic.«Combinator.tyT»
              x1)))
        x2,
      fun (x1 : _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.para
          (α := _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
          (_root_.GebMirror.Metalogic.«Combinator.typeStep»
            (x0).1
            (_root_.GebMirror.Metalogic.«Combinator.typeVar» (x0).2)
            (fun (x2 : _root_.Geb.Kernel.Tree) => x2))
          x1);
    x1

def «Combinator.typerStep2» :=
  fun (x0 : (_root_.List _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) ×
      (_root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
    let x1 : (_root_.List _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) ×
      (_root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree) := _root_.GebMirror.Metalogic.«Combinator.typerStep»
      (_root_.GebMirror.Metalogic.«Combinator.typerStep» x0);
    x1

def «Combinator.typerStep4» :=
  fun (x0 : (_root_.List _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) ×
      (_root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
    let x1 : (_root_.List _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) ×
      (_root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree) := _root_.GebMirror.Metalogic.«Combinator.typerStep2»
      (_root_.GebMirror.Metalogic.«Combinator.typerStep2» x0);
    x1

def «Combinator.typers» :=
  _root_.GebMirror.Metalogic.«Combinator.typerStep4»
    (_root_.GebMirror.Metalogic.«Combinator.typerStep4»
      (fun (_ : _root_.List _root_.Geb.Kernel.Tree)
         (_ : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6661696c20436f6d62696e61746f722e50547929»,
        fun (_ : _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6661696c20436f6d62696e61746f722e50547929»))

def «Combinator.typeTerm» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (_root_.GebMirror.Metalogic.«Combinator.typers»).2
      x0;
    x1

def «Combinator.typePattern» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (_root_.GebMirror.Metalogic.«Combinator.typers»).1
      x0
      x1;
    x2

def «$284d61702e6d6170205061727469616c486f726e2e504465666e205061727469616c486f726e2e4f7053696729» :=
  fun (x0 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        ((x0 x2) :: x3))
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      x1;
    x2

def «Combinator.pmStart» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.pst»
      (_root_.GebMirror.Metalogic.«Combinator.devs» x0)
      (_root_.GebMirror.Metalogic.«Combinator.memos»
        ([] : _root_.List _root_.Geb.Kernel.Tree))
      (_root_.GebMirror.Metalogic.«Combinator.nfList»
        ([] : _root_.List _root_.Geb.Kernel.Tree))
      (_root_.GebMirror.Metalogic.«PartialHorn.pdefns» x1)
      (_root_.GebMirror.Metalogic.«PartialHorn.opSigs»
        (_root_.GebMirror.Metalogic.«$285365712e617070656e64205061727469616c486f726e2e4f7053696729»
          _root_.GebMirror.Metalogic.«Theory.sig»
          (_root_.GebMirror.Metalogic.«$284d61702e6d6170205061727469616c486f726e2e504465666e205061727469616c486f726e2e4f7053696729»
            (fun (x3 : _root_.Geb.Kernel.Tree) =>
              _root_.GebMirror.Metalogic.«PartialHorn.opSig»
                (_root_.GebMirror.Metalogic.«PartialHorn.sorts»
                  (_root_.GebMirror.Metalogic.«PartialHorn.pdCtx» x3))
                (_root_.GebMirror.Metalogic.«PartialHorn.pdSort» x3))
            x1)))
      x2;
    x3

def «Combinator.srcAx» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «Combinator.srcThm» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «Combinator.dev0» :=
  _root_.GebMirror.Metalogic.«Combinator.devEntry»
    _root_.GebMirror.Metalogic.«Combinator.seq0»
    (_root_.Geb.Kernel.leaf 0)

def «$284f7074696f6e2e6e6f7468696e6720436f6d62696e61746f722e446576456e74727929» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$284f7074696f6e2e6a75737420436f6d62696e61746f722e446576456e74727929» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «$284f7074696f6e2e6e74684f6620436f6d62696e61746f722e446576456e74727929» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (_root_.Geb.Kernel.Const.iter
        (α := _root_.List _root_.Geb.Kernel.Tree)
        (fun (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
          _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.List _root_.Geb.Kernel.Tree)
            x2
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (fun (_ : _root_.Geb.Kernel.Tree)
               (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
              x4))
        x0
        x1)
      _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e6720436f6d62696e61746f722e446576456e74727929»
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$284f7074696f6e2e6a75737420436f6d62696e61746f722e446576456e74727929»
          x2);
    x2

def «$284f7074696f6e2e69734a75737420436f6d62696e61746f722e446576456e74727929» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x1)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x2 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x1;
                                          let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x2
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x3 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x3);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x2
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x5);
                                          _root_.Geb.Kernel.leaf 1
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x1;
                                          _root_.Geb.Kernel.leaf 0);
    x1

def «$284f7074696f6e2e66726f6d4d6179626520436f6d62696e61746f722e446576456e74727929» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (let x2 : _root_.Geb.Kernel.Tree := x1;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x2)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x3 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x2;
                                          let x4 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x3
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x4 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x4);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x3
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x6 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          x4
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x2;
                                          x0);
    x2

def «Combinator.srcSeq» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                   if (_root_.Geb.Kernel.Const.eq
                                     (_root_.Geb.Kernel.Const.label x1)
                                     (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                                     let x2 : _root_.List
                                       _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                       x1;
                                     let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                       (α := _root_.Geb.Kernel.Tree)
                                       (β := _root_.Geb.Kernel.Tree)
                                       x2
                                       (_root_.Geb.Kernel.leaf 0)
                                       (fun (x3 : _root_.Geb.Kernel.Tree)
                                          (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                         x3);
                                     let _ : _root_.List
                                       _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                       (α := _root_.Geb.Kernel.Tree)
                                       (β := _root_.List _root_.Geb.Kernel.Tree)
                                       x2
                                       ([] : _root_.List _root_.Geb.Kernel.Tree)
                                       (fun (_ : _root_.Geb.Kernel.Tree)
                                          (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
                                         x5);
                                     _root_.GebMirror.Metalogic.«Combinator.axiomAt» x3
                                   else
                                     let x2 : _root_.List
                                       _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                       x1;
                                     let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                       (α := _root_.Geb.Kernel.Tree)
                                       (β := _root_.Geb.Kernel.Tree)
                                       x2
                                       (_root_.Geb.Kernel.leaf 0)
                                       (fun (x3 : _root_.Geb.Kernel.Tree)
                                          (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                         x3);
                                     let _ : _root_.List
                                       _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                       (α := _root_.Geb.Kernel.Tree)
                                       (β := _root_.List _root_.Geb.Kernel.Tree)
                                       x2
                                       ([] : _root_.List _root_.Geb.Kernel.Tree)
                                       (fun (_ : _root_.Geb.Kernel.Tree)
                                          (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
                                         x5);
                                     _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e505374205061727469616c486f726e2e53657175656e7429»
                                       _root_.GebMirror.Metalogic.«Combinator.pmGet»
                                       (fun (x5 : _root_.Geb.Kernel.Tree) =>
                                         let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e74684f6620436f6d62696e61746f722e446576456e74727929»
                                           (_root_.GebMirror.Metalogic.«Combinator.stDev» x5)
                                           x3;
                                         if (_root_.GebMirror.Metalogic.«$284f7074696f6e2e69734a75737420436f6d62696e61746f722e446576456e74727929»
                                           x6).label ≠ 0 then
                                           _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265205061727469616c486f726e2e53657175656e7429»
                                             (_root_.GebMirror.Metalogic.«Combinator.devSeq»
                                               (_root_.GebMirror.Metalogic.«$284f7074696f6e2e66726f6d4d6179626520436f6d62696e61746f722e446576456e74727929»
                                                 _root_.GebMirror.Metalogic.«Combinator.dev0»
                                                 x6))
                                         else
                                           _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6661696c205061727469616c486f726e2e53657175656e7429»));
    x1

def «Combinator.srcCert» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x4)
                                          (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                                          let x5 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x5
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x6 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x5
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x8);
                                          _root_.GebMirror.Metalogic.«Combinator.cAx» x6 x1 x2 x3
                                        else
                                          let x5 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x5
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x6 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x5
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x8);
                                          _root_.GebMirror.Metalogic.«Combinator.cThm» x6 x1 x2 x3);
    x4

def «Combinator.labels» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 0) x0

def «Combinator.rwRule» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: (x2 :: ([] : _root_.List _root_.Geb.Kernel.Tree))))

def «Combinator.rwSrc» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                        let x2 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                          x1;
                                        let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x2
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x3 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x3);
                                        let x4 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x2
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x5);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x4
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x5 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x5);
                                        let x6 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x4
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x7);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x6
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x7 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x7);
                                        let _ : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x6
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x9);
                                        x3);
    x1

def «Combinator.rwFlip» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                        let x2 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                          x1;
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x2
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x3 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x3);
                                        let x4 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x2
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x5);
                                        let x5 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x4
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x5 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x5);
                                        let x6 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x4
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x7);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x6
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x7 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x7);
                                        let _ : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x6
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x9);
                                        x5);
    x1

def «Combinator.rwAvoid» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                 let x2 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x1;
                                 let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree)
                                   x2
                                   (_root_.Geb.Kernel.leaf 0)
                                   (fun (x3 : _root_.Geb.Kernel.Tree)
                                      (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x3);
                                 let x4 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                   x2
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x5);
                                 let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree)
                                   x4
                                   (_root_.Geb.Kernel.leaf 0)
                                   (fun (x5 : _root_.Geb.Kernel.Tree)
                                      (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x5);
                                 let x6 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                   x4
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x7);
                                 let x7 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree)
                                   x6
                                   (_root_.Geb.Kernel.leaf 0)
                                   (fun (x7 : _root_.Geb.Kernel.Tree)
                                      (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x7);
                                 let _ : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                   x6
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x9);
                                 let x9 : _root_.Geb.Kernel.Tree := x7;
                                 let x10 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x9;
                                 let x11 : _root_.List _root_.Geb.Kernel.Tree := x10; x11);
    x1

def «Combinator.opts» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 0) x0

def «Combinator.matchSt» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «Combinator.msSigma» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                 let x2 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x1;
                                 let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree)
                                   x2
                                   (_root_.Geb.Kernel.leaf 0)
                                   (fun (x3 : _root_.Geb.Kernel.Tree)
                                      (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x3);
                                 let x4 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                   x2
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x5);
                                 let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree)
                                   x4
                                   (_root_.Geb.Kernel.leaf 0)
                                   (fun (x5 : _root_.Geb.Kernel.Tree)
                                      (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x5);
                                 let _ : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                   x4
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x7);
                                 let x7 : _root_.Geb.Kernel.Tree := x3;
                                 let x8 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x7;
                                 let x9 : _root_.List _root_.Geb.Kernel.Tree := x8; x9);
    x1

def «Combinator.msObjs» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                 let x2 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x1;
                                 let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree)
                                   x2
                                   (_root_.Geb.Kernel.leaf 0)
                                   (fun (x3 : _root_.Geb.Kernel.Tree)
                                      (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x3);
                                 let x4 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                   x2
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x5);
                                 let x5 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree)
                                   x4
                                   (_root_.Geb.Kernel.leaf 0)
                                   (fun (x5 : _root_.Geb.Kernel.Tree)
                                      (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x5);
                                 let _ : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                   x4
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x7);
                                 _root_.GebMirror.Metalogic.«Combinator.pairsOf» x5);
    x1

def «Combinator.msDefer» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.matchSt»
      (_root_.GebMirror.Metalogic.«Combinator.opts»
        (_root_.GebMirror.Metalogic.«Combinator.msSigma» x0))
      (_root_.GebMirror.Metalogic.«Combinator.pairs»
        ((_root_.GebMirror.Metalogic.«Language.pr» x1 x2) ::
          (_root_.GebMirror.Metalogic.«Combinator.msObjs» x0)));
    x3

def «$284f7074696f6e2e6e6f7468696e6720436f6d62696e61746f722e4d61746368537429» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$284f7074696f6e2e6a75737420436f6d62696e61746f722e4d61746368537429» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «Combinator.bindM» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (let x2 : _root_.Geb.Kernel.Tree := x0;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x2)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x3 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x2;
                                          let x4 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x3
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x4 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x4);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x3
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x6 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          x1 x4
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x2;
                                          _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e6720436f6d62696e61746f722e4d61746368537429»);
    x2

def «Combinator.matchKids» :=
  fun (x0 : _root_.List
      (_root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (fun (x3 : _root_.Geb.Kernel.Tree →
           _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
         (x4 : _root_.List _root_.Geb.Kernel.Tree →
           _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
         (x5 : _root_.List _root_.Geb.Kernel.Tree)
         (x6 : _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.lcase
          (α := _root_.Geb.Kernel.Tree)
          (β := _root_.Geb.Kernel.Tree)
          x5
          (_root_.GebMirror.Metalogic.«$284f7074696f6e2e6a75737420436f6d62696e61746f722e4d61746368537429»
            x6)
          (fun (x7 : _root_.Geb.Kernel.Tree)
             (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Metalogic.«Combinator.bindM»
              (x3 x7 x6)
              (fun (x9 : _root_.Geb.Kernel.Tree) => x4 x8 x9)))
      (fun (_ : _root_.List _root_.Geb.Kernel.Tree)
         (x4 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$284f7074696f6e2e6a75737420436f6d62696e61746f722e4d61746368537429»
          x4)
      x0
      x1
      x2;
    x3

def «Combinator.matchStepP» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List
      (_root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
    let x4 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x4 : _root_.Geb.Kernel.Tree)
                                     (x5 : _root_.Geb.Kernel.Tree) =>
      let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.label x2;
      if (_root_.Geb.Kernel.Const.eq
        x6
        (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
        if (_root_.Geb.Kernel.Const.eq
          (_root_.GebMirror.Metalogic.«Prelude.length»
            (_root_.Geb.Kernel.Const.children x2))
          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
          let x7 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.label
            (_root_.GebMirror.Metalogic.«Prelude.at»
              (_root_.Geb.Kernel.Const.children x2)
              (_root_.Geb.Kernel.leaf 0));
          let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.nth»
            (_root_.GebMirror.Metalogic.«Combinator.msSigma» x5)
            x7;
          if (_root_.GebMirror.Metalogic.«Prelude.isSome» x8).label ≠ 0 then
            if (_root_.GebMirror.Metalogic.«Prelude.isSome»
              (_root_.GebMirror.Metalogic.«Prelude.get» x8)).label ≠ 0 then
              if (_root_.Geb.Kernel.Const.equal
                (_root_.GebMirror.Metalogic.«Prelude.get» (_root_.GebMirror.Metalogic.«Prelude.get» x8))
                x4).label ≠ 0 then
                _root_.GebMirror.Metalogic.«$284f7074696f6e2e6a75737420436f6d62696e61746f722e4d61746368537429»
                  x5
              else
                if (_root_.Geb.Kernel.Const.equal
                  (_root_.GebMirror.Metalogic.«Prelude.nth» x1 x7)
                  (_root_.GebMirror.Metalogic.«Prelude.some»
                    (_root_.Geb.Kernel.leaf 0))).label ≠ 0 then
                  _root_.GebMirror.Metalogic.«$284f7074696f6e2e6a75737420436f6d62696e61746f722e4d61746368537429»
                    (_root_.GebMirror.Metalogic.«Combinator.msDefer» x5 x2 x4)
                else
                  _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e6720436f6d62696e61746f722e4d61746368537429»
            else
              _root_.GebMirror.Metalogic.«$284f7074696f6e2e6a75737420436f6d62696e61746f722e4d61746368537429»
                (_root_.GebMirror.Metalogic.«Combinator.matchSt»
                  (_root_.GebMirror.Metalogic.«Combinator.opts»
                    (_root_.GebMirror.Metalogic.«Prover.setAt»
                      (_root_.GebMirror.Metalogic.«Combinator.msSigma» x5)
                      x7
                      (_root_.GebMirror.Metalogic.«Prelude.some» x4)))
                  (_root_.GebMirror.Metalogic.«Combinator.pairs»
                    (_root_.GebMirror.Metalogic.«Combinator.msObjs» x5)))
          else
            _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e6720436f6d62696e61746f722e4d61746368537429»
        else
          _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e6720436f6d62696e61746f722e4d61746368537429»
      else
        if (_root_.Geb.Kernel.Const.equal
          (_root_.GebMirror.Metalogic.«PartialHorn.sortOf» x0 x1 x2)
          (_root_.GebMirror.Metalogic.«Prelude.some»
            (_root_.Geb.Kernel.leaf 0))).label ≠ 0 then
          _root_.GebMirror.Metalogic.«$284f7074696f6e2e6a75737420436f6d62696e61746f722e4d61746368537429»
            (_root_.GebMirror.Metalogic.«Combinator.msDefer» x5 x2 x4)
        else
          if (_root_.GebMirror.Metalogic.«Prelude.and»
            (_root_.Geb.Kernel.Const.eq (_root_.Geb.Kernel.Const.label x4) x6)
            (_root_.Geb.Kernel.Const.eq
              (_root_.GebMirror.Metalogic.«Prelude.length»
                (_root_.Geb.Kernel.Const.children x4))
              (_root_.GebMirror.Metalogic.«Prelude.length»
                (_root_.Geb.Kernel.Const.children x2)))).label ≠ 0 then
            _root_.GebMirror.Metalogic.«Combinator.matchKids»
              x3
              (_root_.Geb.Kernel.Const.children x4)
              x5
          else
            _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e6720436f6d62696e61746f722e4d61746368537429»);
    x4

def «Combinator.matchPat» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.para
      (α := _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«Combinator.matchStepP» x0 x1)
      x2
      x3
      x4;
    x5

def «Combinator.bridgeKids» :=
  fun (x0 : _root_.List
      (_root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree →
           _root_.Geb.Kernel.Tree →
             _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree →
           _root_.Geb.Kernel.Tree →
             _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
         (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.lcase
          (α := _root_.Geb.Kernel.Tree)
          (β := _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
          x4
          (_root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e7075726520436f6d62696e61746f722e436572747329»
            (_root_.GebMirror.Metalogic.«Combinator.certs»
              ([] : _root_.List _root_.Geb.Kernel.Tree)))
          (fun (x5 : _root_.Geb.Kernel.Tree)
             (x6 : _root_.List _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64205420436f6d62696e61746f722e436572747329»
              (x2 x5)
              (fun (x7 : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e436572747320436f6d62696e61746f722e436572747329»
                  (x3 x6)
                  (fun (x8 : _root_.Geb.Kernel.Tree) =>
                    _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e7075726520436f6d62696e61746f722e436572747329»
                      (_root_.GebMirror.Metalogic.«Combinator.certs»
                        (x7 :: (_root_.GebMirror.Metalogic.«Combinator.certsOf» x8)))))))
      (fun (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e7075726520436f6d62696e61746f722e436572747329»
          (_root_.GebMirror.Metalogic.«Combinator.certs»
            ([] : _root_.List _root_.Geb.Kernel.Tree)))
      x0
      x1;
    x2

def «Combinator.bridgeStep» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List
      (_root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
    let x3 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree := (fun (x3 : _root_.Geb.Kernel.Tree) =>
      _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e505479205429»
        (_root_.GebMirror.Metalogic.«Combinator.typeTerm» x3)
        (fun (x4 : _root_.Geb.Kernel.Tree) =>
          if (_root_.Geb.Kernel.Const.equal
            (_root_.GebMirror.Metalogic.«PartialHorn.phSubst»
              (_root_.GebMirror.Metalogic.«$284d61702e6d617020436f6d62696e61746f722e505479205429»
                _root_.GebMirror.Metalogic.«Combinator.tyT»
                x0)
              x1)
            x3).label ≠ 0 then
            _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265205429»
              (_root_.GebMirror.Metalogic.«Combinator.tyDfd» x4)
          else
            if (_root_.Geb.Kernel.Const.eq
              (_root_.GebMirror.Metalogic.«Combinator.tySort» x4)
              (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
              _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e505479205429»
                (_root_.GebMirror.Metalogic.«Combinator.typePattern» x0 x1)
                (fun (x5 : _root_.Geb.Kernel.Tree) =>
                  _root_.GebMirror.Metalogic.«Combinator.objEq» x4 x5)
            else
              if (_root_.GebMirror.Metalogic.«Prelude.or»
                (_root_.Geb.Kernel.Const.eq
                  (_root_.Geb.Kernel.Const.label x1)
                  (_root_.Geb.Kernel.leaf 0))
                (_root_.GebMirror.Metalogic.«Base.not»
                  (_root_.Geb.Kernel.Const.eq
                    (_root_.GebMirror.Metalogic.«Prelude.length»
                      (_root_.Geb.Kernel.Const.children x3))
                    (_root_.GebMirror.Metalogic.«Prelude.length»
                      (_root_.Geb.Kernel.Const.children x1))))).label ≠ 0 then
                _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6661696c205429»
              else
                _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e4365727473205429»
                  (_root_.GebMirror.Metalogic.«Combinator.bridgeKids»
                    x2
                    (_root_.Geb.Kernel.Const.children x3))
                  (fun (x5 : _root_.Geb.Kernel.Tree) =>
                    _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265205429»
                      (_root_.GebMirror.Metalogic.«Combinator.cCong»
                        (_root_.GebMirror.Metalogic.«Combinator.tyDfd» x4)
                        (_root_.GebMirror.Metalogic.«Combinator.certsOf» x5)))));
    x3

def «Combinator.bridge» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.para
      (α := _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«Combinator.bridgeStep» x0)
      x1
      x2;
    x3

def «Combinator.ms0» :=
  _root_.GebMirror.Metalogic.«Combinator.matchSt»
    (_root_.GebMirror.Metalogic.«Combinator.opts»
      ([] : _root_.List _root_.Geb.Kernel.Tree))
    (_root_.GebMirror.Metalogic.«Combinator.pairs»
      ([] : _root_.List _root_.Geb.Kernel.Tree))

def «$28436f6d62696e61746f722e436f6d702e62696e642054204c616e67756167652e545061697229» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x4)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x5 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x5
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x6 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x5
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x8);
                                          let x8 : _root_.Geb.Kernel.Tree := x6;
                                          let x9 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x8;
                                          let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x9
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x10 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x10);
                                          let x11 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x9
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let x12 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x11
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x12 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x11
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x14);
                                          x1 x10 x2 x12
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e626164204c616e67756167652e545061697229»);
    x4

def «$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e505374204c616e67756167652e545061697229» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x4)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x5 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x5
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x6 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x5
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x8);
                                          let x8 : _root_.Geb.Kernel.Tree := x6;
                                          let x9 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x8;
                                          let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x9
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x10 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x10);
                                          let x11 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x9
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let x12 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x11
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x12 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x11
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x14);
                                          x1 x10 x2 x12
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e626164204c616e67756167652e545061697229»);
    x4

def «$284f7074696f6e2e69734a75737420436f6d62696e61746f722e4d61746368537429» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x1)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x2 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x1;
                                          let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x2
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x3 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x3);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x2
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x5);
                                          _root_.Geb.Kernel.leaf 1
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x1;
                                          _root_.Geb.Kernel.leaf 0);
    x1

def «$284f7074696f6e2e66726f6d4d6179626520436f6d62696e61746f722e4d61746368537429» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (let x2 : _root_.Geb.Kernel.Tree := x1;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x2)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x3 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x2;
                                          let x4 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x3
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x4 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x4);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x3
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x6 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          x4
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x2;
                                          x0);
    x2

def «$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e50547973204c616e67756167652e545061697229» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x4)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x5 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x5
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x6 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x5
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x8);
                                          let x8 : _root_.Geb.Kernel.Tree := x6;
                                          let x9 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x8;
                                          let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x9
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x10 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x10);
                                          let x11 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x9
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let x12 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x11
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x12 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x11
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x14);
                                          x1 x10 x2 x12
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e626164204c616e67756167652e545061697229»);
    x4

def «$28436f6d62696e61746f722e436f6d702e6661696c204c616e67756167652e545061697229» :=
  fun (_ : _root_.Geb.Kernel.Tree) (_ : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e626164204c616e67756167652e545061697229»;
    x2

def «Combinator.applyRule» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e642054204c616e67756167652e545061697229»
      (_root_.GebMirror.Metalogic.«Combinator.pmGuard»
        (_root_.GebMirror.Metalogic.«Base.not»
          (_root_.GebMirror.Metalogic.«Base.anyT»
            (fun (x2 : _root_.Geb.Kernel.Tree) =>
              _root_.Geb.Kernel.Const.eq (_root_.Geb.Kernel.Const.label x1) x2)
            (_root_.GebMirror.Metalogic.«Combinator.rwAvoid» x0))))
      (fun (_ : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64205061727469616c486f726e2e53657175656e74204c616e67756167652e545061697229»
          (_root_.GebMirror.Metalogic.«Combinator.srcSeq»
            (_root_.GebMirror.Metalogic.«Combinator.rwSrc» x0))
          (fun (x3 : _root_.Geb.Kernel.Tree) =>
            let x4 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Combinator.rwFlip»
              x0).label ≠ 0 then
              _root_.GebMirror.Metalogic.«PartialHorn.eqRhs»
                (_root_.GebMirror.Metalogic.«PartialHorn.seqConcl» x3)
            else
              _root_.GebMirror.Metalogic.«PartialHorn.eqLhs»
                (_root_.GebMirror.Metalogic.«PartialHorn.seqConcl» x3));
            let x5 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Combinator.rwFlip»
              x0).label ≠ 0 then
              _root_.GebMirror.Metalogic.«PartialHorn.eqLhs»
                (_root_.GebMirror.Metalogic.«PartialHorn.seqConcl» x3)
            else
              _root_.GebMirror.Metalogic.«PartialHorn.eqRhs»
                (_root_.GebMirror.Metalogic.«PartialHorn.seqConcl» x3));
            _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e505374204c616e67756167652e545061697229»
              _root_.GebMirror.Metalogic.«Combinator.pmGet»
              (fun (x6 : _root_.Geb.Kernel.Tree) =>
                let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.matchPat»
                  (_root_.GebMirror.Metalogic.«Combinator.stSig» x6)
                  (_root_.GebMirror.Metalogic.«PartialHorn.seqCtx» x3)
                  x4
                  x1
                  (_root_.GebMirror.Metalogic.«Combinator.matchSt»
                    (_root_.GebMirror.Metalogic.«Combinator.opts»
                      (_root_.GebMirror.Metalogic.«Base.mapT»
                        (fun (_ : _root_.Geb.Kernel.Tree) => _root_.GebMirror.Metalogic.«Prelude.none»)
                        (_root_.GebMirror.Metalogic.«PartialHorn.seqCtx» x3)))
                    (_root_.GebMirror.Metalogic.«Combinator.pairs»
                      ([] : _root_.List _root_.Geb.Kernel.Tree)));
                if (_root_.GebMirror.Metalogic.«$284f7074696f6e2e69734a75737420436f6d62696e61746f722e4d61746368537429»
                  x7).label ≠ 0 then
                  let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$284f7074696f6e2e66726f6d4d6179626520436f6d62696e61746f722e4d61746368537429»
                    _root_.GebMirror.Metalogic.«Combinator.ms0»
                    x7;
                  let x9 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Base.allSomeT»
                    (_root_.GebMirror.Metalogic.«Combinator.msSigma» x8);
                  if (_root_.GebMirror.Metalogic.«Prelude.isSome» x9).label ≠ 0 then
                    let x10 : _root_.List
                      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                      (_root_.GebMirror.Metalogic.«Prelude.get» x9);
                    _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e50547973204c616e67756167652e545061697229»
                      (_root_.GebMirror.Metalogic.«Combinator.mapMTY»
                        _root_.GebMirror.Metalogic.«Combinator.typeTerm»
                        x10)
                      (fun (x11 : _root_.Geb.Kernel.Tree) =>
                        let x12 : _root_.List
                          _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.ptysOf» x11;
                        _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e4365727473204c616e67756167652e545061697229»
                          (_root_.GebMirror.Metalogic.«Combinator.mapMPairC»
                            (fun (x13 : _root_.Geb.Kernel.Tree) =>
                              _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e505479205429»
                                (_root_.GebMirror.Metalogic.«Combinator.typePattern»
                                  x12
                                  (_root_.GebMirror.Metalogic.«Language.p1» x13))
                                (fun (x14 : _root_.Geb.Kernel.Tree) =>
                                  _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e505479205429»
                                    (_root_.GebMirror.Metalogic.«Combinator.typeTerm»
                                      (_root_.GebMirror.Metalogic.«Language.p2» x13))
                                    (fun (x15 : _root_.Geb.Kernel.Tree) =>
                                      _root_.GebMirror.Metalogic.«Combinator.objEq» x14 x15)))
                            (_root_.GebMirror.Metalogic.«Combinator.msObjs» x8))
                          (fun (_ : _root_.Geb.Kernel.Tree) =>
                            _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e642054204c616e67756167652e545061697229»
                              (_root_.GebMirror.Metalogic.«Combinator.bridge» x12 x4 x1)
                              (fun (x14 : _root_.Geb.Kernel.Tree) =>
                                _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e4365727473204c616e67756167652e545061697229»
                                  (_root_.GebMirror.Metalogic.«Combinator.mapMEqC»
                                    (_root_.GebMirror.Metalogic.«Combinator.proveHyp»
                                      _root_.GebMirror.Metalogic.«Combinator.typePattern»
                                      x12)
                                    (_root_.GebMirror.Metalogic.«PartialHorn.seqHyps» x3))
                                  (fun (x15 : _root_.Geb.Kernel.Tree) =>
                                    let x16 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.srcCert»
                                      (_root_.GebMirror.Metalogic.«Combinator.rwSrc» x0)
                                      x10
                                      (_root_.GebMirror.Metalogic.«$284d61702e6d617020436f6d62696e61746f722e505479205429»
                                        _root_.GebMirror.Metalogic.«Combinator.tyDfd»
                                        x12)
                                      (_root_.GebMirror.Metalogic.«Combinator.certsOf» x15);
                                    _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265204c616e67756167652e545061697229»
                                      (_root_.GebMirror.Metalogic.«Language.pr»
                                        (_root_.GebMirror.Metalogic.«PartialHorn.phSubst» x10 x5)
                                        (_root_.GebMirror.Metalogic.«Combinator.cTrans»
                                          x14
                                          (if (_root_.GebMirror.Metalogic.«Combinator.rwFlip» x0).label ≠ 0 then
                                            _root_.GebMirror.Metalogic.«Combinator.cSymm» x16
                                          else
                                            x16)))))))
                  else
                    _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6661696c204c616e67756167652e545061697229»
                else
                  _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6661696c204c616e67756167652e545061697229»)));
    x2

def «$28436f6d62696e61746f722e436f6d702e6f72456c7365204c616e67756167652e545061697229» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
                                        let x5 : _root_.Geb.Kernel.Tree := x4;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x5)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x6 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x5;
                                          let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x6
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x7 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x7);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x6
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x9);
                                          x4
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x5;
                                          x1 x2 x3);
    x4

def «Combinator.firstRule» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.Geb.Kernel.Tree →
           _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6f72456c7365204c616e67756167652e545061697229»
          (_root_.GebMirror.Metalogic.«Combinator.applyRule» x2 x1)
          x3)
      _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6661696c204c616e67756167652e545061697229»
      x0;
    x2

def «$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e50547920436f6d62696e61746f722e4173736f6329» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x4)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x5 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x5
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x6 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x5
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x8);
                                          let x8 : _root_.Geb.Kernel.Tree := x6;
                                          let x9 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x8;
                                          let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x9
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x10 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x10);
                                          let x11 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x9
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let x12 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x11
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x12 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x11
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x14);
                                          x1 x10 x2 x12
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62616420436f6d62696e61746f722e4173736f6329»);
    x4

def «$28436f6d62696e61746f722e436f6d702e7075726520436f6d62696e61746f722e4173736f6329» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (_ : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6f6b20436f6d62696e61746f722e4173736f6329»
      (_root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e72657320436f6d62696e61746f722e4173736f6329»
        x0
        x2);
    x3

def «$28436f6d62696e61746f722e436f6d702e6661696c20436f6d62696e61746f722e4173736f6329» :=
  fun (_ : _root_.Geb.Kernel.Tree) (_ : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62616420436f6d62696e61746f722e4173736f6329»;
    x2

def «Combinator.assocLeft» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Prelude.and»
      (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x0)
        (_root_.Geb.Kernel.leaf 4))
      (_root_.Geb.Kernel.Const.eq
        (_root_.GebMirror.Metalogic.«Prelude.length»
          (_root_.Geb.Kernel.Const.children x0))
        (_root_.Geb.Kernel.leaf 2))).label ≠ 0 then
      let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.at»
        (_root_.Geb.Kernel.Const.children x0)
        (_root_.Geb.Kernel.leaf 0);
      let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.at»
        (_root_.Geb.Kernel.Const.children x0)
        (_root_.Geb.Kernel.leaf 1);
      if (_root_.GebMirror.Metalogic.«Prelude.and»
        (_root_.Geb.Kernel.Const.eq
          (_root_.Geb.Kernel.Const.label x2)
          (_root_.Geb.Kernel.leaf 4))
        (_root_.Geb.Kernel.Const.eq
          (_root_.GebMirror.Metalogic.«Prelude.length»
            (_root_.Geb.Kernel.Const.children x2))
          (_root_.Geb.Kernel.leaf 2))).label ≠ 0 then
        let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.at»
          (_root_.Geb.Kernel.Const.children x2)
          (_root_.Geb.Kernel.leaf 0);
        let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.at»
          (_root_.Geb.Kernel.Const.children x2)
          (_root_.Geb.Kernel.leaf 1);
        _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e50547920436f6d62696e61746f722e4173736f6329»
          (_root_.GebMirror.Metalogic.«Combinator.typeTerm» x0)
          (fun (x5 : _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e50547920436f6d62696e61746f722e4173736f6329»
              (_root_.GebMirror.Metalogic.«Combinator.typeTerm» x1)
              (fun (x6 : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e50547920436f6d62696e61746f722e4173736f6329»
                  (_root_.GebMirror.Metalogic.«Combinator.typeTerm» x3)
                  (fun (x7 : _root_.Geb.Kernel.Tree) =>
                    _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e50547920436f6d62696e61746f722e4173736f6329»
                      (_root_.GebMirror.Metalogic.«Combinator.typeTerm» x4)
                      (fun (x8 : _root_.Geb.Kernel.Tree) =>
                        _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e7075726520436f6d62696e61746f722e4173736f6329»
                          (_root_.GebMirror.Metalogic.«Combinator.assoc»
                            x1
                            x3
                            x4
                            (_root_.GebMirror.Metalogic.«Combinator.cAx»
                              (_root_.Geb.Kernel.leaf 7)
                              (_root_.GebMirror.Metalogic.«Theory.l3» x1 x3 x4)
                              (_root_.GebMirror.Metalogic.«Theory.l3»
                                (_root_.GebMirror.Metalogic.«Combinator.tyDfd» x6)
                                (_root_.GebMirror.Metalogic.«Combinator.tyDfd» x7)
                                (_root_.GebMirror.Metalogic.«Combinator.tyDfd» x8))
                              (_root_.GebMirror.Metalogic.«Prelude.single»
                                (_root_.GebMirror.Metalogic.«Combinator.tyDfd» x5))))))))
      else
        _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6661696c20436f6d62696e61746f722e4173736f6329»
    else
      _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6661696c20436f6d62696e61746f722e4173736f6329»);
    x1

def «$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e4173736f63204c616e67756167652e545061697229» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x4)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x5 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x5
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x6 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x5
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x8);
                                          let x8 : _root_.Geb.Kernel.Tree := x6;
                                          let x9 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x8;
                                          let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x9
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x10 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x10);
                                          let x11 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x9
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let x12 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x11
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x12 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x11
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x14);
                                          x1 x10 x2 x12
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e626164204c616e67756167652e545061697229»);
    x4

def «$28436f6d62696e61746f722e436f6d702e62696e64204c616e67756167652e5450616972204c616e67756167652e545061697229» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x4)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x5 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x5
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x6 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x5
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x8);
                                          let x8 : _root_.Geb.Kernel.Tree := x6;
                                          let x9 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x8;
                                          let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x9
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x10 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x10);
                                          let x11 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x9
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let x12 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x11
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x12 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x11
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x14);
                                          x1 x10 x2 x12
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e626164204c616e67756167652e545061697229»);
    x4

def «Combinator.rewriteRoot» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6f72456c7365204c616e67756167652e545061697229»
      (_root_.GebMirror.Metalogic.«Combinator.firstRule» x0 x1)
      (_root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e4173736f63204c616e67756167652e545061697229»
        (_root_.GebMirror.Metalogic.«Combinator.assocLeft» x1)
        (fun (x2 : _root_.Geb.Kernel.Tree) =>
          let x3 : _root_.Geb.Kernel.Tree := x2;
          let x4 : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x3;
          let x5 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.Geb.Kernel.Tree)
            x4
            (_root_.Geb.Kernel.leaf 0)
            (fun (x5 : _root_.Geb.Kernel.Tree)
               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
              x5);
          let x6 : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.List _root_.Geb.Kernel.Tree)
            x4
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (fun (_ : _root_.Geb.Kernel.Tree)
               (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
              x7);
          let x7 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.Geb.Kernel.Tree)
            x6
            (_root_.Geb.Kernel.leaf 0)
            (fun (x7 : _root_.Geb.Kernel.Tree)
               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
              x7);
          let x8 : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.List _root_.Geb.Kernel.Tree)
            x6
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (fun (_ : _root_.Geb.Kernel.Tree)
               (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
              x9);
          let x9 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.Geb.Kernel.Tree)
            x8
            (_root_.Geb.Kernel.leaf 0)
            (fun (x9 : _root_.Geb.Kernel.Tree)
               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
              x9);
          let x10 : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.List _root_.Geb.Kernel.Tree)
            x8
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (fun (_ : _root_.Geb.Kernel.Tree)
               (x11 : _root_.List _root_.Geb.Kernel.Tree) =>
              x11);
          let x11 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.Geb.Kernel.Tree)
            x10
            (_root_.Geb.Kernel.leaf 0)
            (fun (x11 : _root_.Geb.Kernel.Tree)
               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
              x11);
          let _ : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.List _root_.Geb.Kernel.Tree)
            x10
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (fun (_ : _root_.Geb.Kernel.Tree)
               (x13 : _root_.List _root_.Geb.Kernel.Tree) =>
              x13);
          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64204c616e67756167652e5450616972204c616e67756167652e545061697229»
            (_root_.GebMirror.Metalogic.«Combinator.firstRule»
              x0
              (_root_.GebMirror.Metalogic.«Theory.comp» x5 x7))
            (fun (x13 : _root_.Geb.Kernel.Tree) =>
              _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e505479204c616e67756167652e545061697229»
                (_root_.GebMirror.Metalogic.«Combinator.typeTerm»
                  (_root_.GebMirror.Metalogic.«Theory.comp»
                    (_root_.GebMirror.Metalogic.«Theory.comp» x5 x7)
                    x9))
                (fun (x14 : _root_.Geb.Kernel.Tree) =>
                  _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e505479204c616e67756167652e545061697229»
                    (_root_.GebMirror.Metalogic.«Combinator.typeTerm» x9)
                    (fun (x15 : _root_.Geb.Kernel.Tree) =>
                      _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265204c616e67756167652e545061697229»
                        (_root_.GebMirror.Metalogic.«Language.pr»
                          (_root_.GebMirror.Metalogic.«Theory.comp» (_root_.GebMirror.Metalogic.«Language.p1» x13) x9)
                          (_root_.GebMirror.Metalogic.«Combinator.cTrans»
                            x11
                            (_root_.GebMirror.Metalogic.«Combinator.cCong»
                              (_root_.GebMirror.Metalogic.«Combinator.tyDfd» x14)
                              (_root_.GebMirror.Metalogic.«Theory.l2»
                                (_root_.GebMirror.Metalogic.«Language.p2» x13)
                                (_root_.GebMirror.Metalogic.«Combinator.tyDfd» x15))))))))));
    x2

def «Combinator.lookupNf» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (_ : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
      _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6f6b2032393a284f7074696f6e2e4d61796265204c616e67756167652e54506169722929»
        (_root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e7265732032393a284f7074696f6e2e4d61796265204c616e67756167652e54506169722929»
          (_root_.GebMirror.Metalogic.«Combinator.nfFind»
            (_root_.GebMirror.Metalogic.«Combinator.stNfs» x2)
            x0)
          x2));
    x1

def «Combinator.memoizeNf» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e642054204c616e67756167652e545061697229»
      (if (_root_.Geb.Kernel.Const.equal x0 x1).label ≠ 0 then
        _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265205429» x2
      else
        _root_.GebMirror.Metalogic.«Combinator.addLemma»
          (_root_.GebMirror.Metalogic.«PartialHorn.eqn» x0 x1)
          x2)
      (fun (x3 : _root_.Geb.Kernel.Tree)
         (_ : _root_.Geb.Kernel.Tree)
         (x5 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6f6b204c616e67756167652e545061697229»
          (_root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e726573204c616e67756167652e545061697229»
            (_root_.GebMirror.Metalogic.«Language.pr» x1 x3)
            (_root_.GebMirror.Metalogic.«Combinator.withNfs»
              x5
              ((_root_.GebMirror.Metalogic.«Combinator.nfEntry»
                x0
                (_root_.GebMirror.Metalogic.«Language.pr» x1 x3)) ::
                (_root_.GebMirror.Metalogic.«Combinator.stNfs» x5)))));
    x3

def «Combinator.pr0» :=
  _root_.GebMirror.Metalogic.«Language.pr»
    (_root_.Geb.Kernel.leaf 0)
    (_root_.Geb.Kernel.leaf 0)

def «$28436f6d62696e61746f722e436f6d702e62696e642032393a284f7074696f6e2e4d61796265204c616e67756167652e545061697229204c616e67756167652e545061697229» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x4)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x5 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x5
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x6 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x5
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x8);
                                          let x8 : _root_.Geb.Kernel.Tree := x6;
                                          let x9 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x8;
                                          let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x9
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x10 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x10);
                                          let x11 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x9
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let x12 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x11
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x12 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x11
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x14);
                                          x1 x10 x2 x12
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e626164204c616e67756167652e545061697229»);
    x4

def «$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e5061697273204c616e67756167652e545061697229» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x4)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x5 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x5
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x6 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x5
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x8);
                                          let x8 : _root_.Geb.Kernel.Tree := x6;
                                          let x9 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x8;
                                          let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x9
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x10 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x10);
                                          let x11 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x9
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let x12 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x11
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x12 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x11
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x14);
                                          x1 x10 x2 x12
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e626164204c616e67756167652e545061697229»);
    x4

def «$28436f6d62696e61746f722e436f6d702e6f72456c73652032393a284f7074696f6e2e4d61796265204c616e67756167652e54506169722929» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
                                        let x5 : _root_.Geb.Kernel.Tree := x4;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x5)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x6 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x5;
                                          let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x6
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x7 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x7);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x6
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x9);
                                          x4
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x5;
                                          x1 x2 x3);
    x4

def «$28436f6d62696e61746f722e436f6d702e62696e64204c616e67756167652e54506169722032393a284f7074696f6e2e4d61796265204c616e67756167652e54506169722929» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x4)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x5 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x5
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x6 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x5
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x8);
                                          let x8 : _root_.Geb.Kernel.Tree := x6;
                                          let x9 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x8;
                                          let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x9
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x10 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x10);
                                          let x11 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x9
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let x12 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x11
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x12 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x11
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x14);
                                          x1 x10 x2 x12
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6261642032393a284f7074696f6e2e4d61796265204c616e67756167652e54506169722929»);
    x4

def «$28436f6d62696e61746f722e436f6d702e707572652032393a284f7074696f6e2e4d61796265204c616e67756167652e54506169722929» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (_ : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6f6b2032393a284f7074696f6e2e4d61796265204c616e67756167652e54506169722929»
      (_root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e7265732032393a284f7074696f6e2e4d61796265204c616e67756167652e54506169722929»
        x0
        x2);
    x3

def «Combinator.normStepP» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List
      (_root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
    let x4 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e642032393a284f7074696f6e2e4d61796265204c616e67756167652e545061697229204c616e67756167652e545061697229»
      (_root_.GebMirror.Metalogic.«Combinator.lookupNf» x2)
      (fun (x4 : _root_.Geb.Kernel.Tree) =>
        if (_root_.GebMirror.Metalogic.«$284f7074696f6e2e69734a757374204c616e67756167652e545061697229»
          x4).label ≠ 0 then
          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265204c616e67756167652e545061697229»
            (_root_.GebMirror.Metalogic.«$284f7074696f6e2e66726f6d4d61796265204c616e67756167652e545061697229»
              _root_.GebMirror.Metalogic.«Combinator.pr0»
              x4)
        else
          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e505479204c616e67756167652e545061697229»
            (_root_.GebMirror.Metalogic.«Combinator.typeTerm» x2)
            (fun (x5 : _root_.Geb.Kernel.Tree) =>
              if (_root_.Geb.Kernel.Const.eq
                (_root_.GebMirror.Metalogic.«Combinator.tySort» x5)
                (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265204c616e67756167652e545061697229»
                  (_root_.GebMirror.Metalogic.«Language.pr»
                    (_root_.GebMirror.Metalogic.«Combinator.tyLo» x5)
                    (_root_.GebMirror.Metalogic.«Combinator.tyLoC» x5))
              else
                if (_root_.Geb.Kernel.Const.eq
                  (_root_.Geb.Kernel.Const.label x2)
                  (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                  _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265204c616e67756167652e545061697229»
                    (_root_.GebMirror.Metalogic.«Language.pr»
                      x2
                      (_root_.GebMirror.Metalogic.«Combinator.tyDfd» x5))
                else
                  _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e5061697273204c616e67756167652e545061697229»
                    (_root_.GebMirror.Metalogic.«Combinator.seqP» x3)
                    (fun (x6 : _root_.Geb.Kernel.Tree) =>
                      let x7 : _root_.List
                        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.pairsOf» x6;
                      let x8 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.node
                        (_root_.Geb.Kernel.Const.label x2)
                        (_root_.GebMirror.Metalogic.«$284d61702e6d6170204c616e67756167652e5450616972205429»
                          _root_.GebMirror.Metalogic.«Language.p1»
                          x7);
                      let x9 : _root_.Geb.Kernel.Tree := (if (_root_.Geb.Kernel.Const.equal
                        x8
                        x2).label ≠ 0 then
                        _root_.GebMirror.Metalogic.«Combinator.tyDfd» x5
                      else
                        _root_.GebMirror.Metalogic.«Combinator.cCong»
                          (_root_.GebMirror.Metalogic.«Combinator.tyDfd» x5)
                          (_root_.GebMirror.Metalogic.«$284d61702e6d6170204c616e67756167652e5450616972205429»
                            _root_.GebMirror.Metalogic.«Language.p2»
                            x7));
                      _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e642032393a284f7074696f6e2e4d61796265204c616e67756167652e545061697229204c616e67756167652e545061697229»
                        (_root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6f72456c73652032393a284f7074696f6e2e4d61796265204c616e67756167652e54506169722929»
                          (_root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64204c616e67756167652e54506169722032393a284f7074696f6e2e4d61796265204c616e67756167652e54506169722929»
                            (_root_.GebMirror.Metalogic.«Combinator.rewriteRoot» x0 x8)
                            (fun (x10 : _root_.Geb.Kernel.Tree) =>
                              _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e707572652032393a284f7074696f6e2e4d61796265204c616e67756167652e54506169722929»
                                (_root_.GebMirror.Metalogic.«$284f7074696f6e2e6a757374204c616e67756167652e545061697229»
                                  x10)))
                          (_root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e707572652032393a284f7074696f6e2e4d61796265204c616e67756167652e54506169722929»
                            _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e67204c616e67756167652e545061697229»))
                        (fun (x10 : _root_.Geb.Kernel.Tree) =>
                          if (_root_.GebMirror.Metalogic.«$284f7074696f6e2e69734a757374204c616e67756167652e545061697229»
                            x10).label ≠ 0 then
                            let x11 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$284f7074696f6e2e66726f6d4d61796265204c616e67756167652e545061697229»
                              _root_.GebMirror.Metalogic.«Combinator.pr0»
                              x10;
                            _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64204c616e67756167652e5450616972204c616e67756167652e545061697229»
                              (x1 (_root_.GebMirror.Metalogic.«Language.p1» x11))
                              (fun (x12 : _root_.Geb.Kernel.Tree) =>
                                _root_.GebMirror.Metalogic.«Combinator.memoizeNf»
                                  x2
                                  (_root_.GebMirror.Metalogic.«Language.p1» x12)
                                  (_root_.GebMirror.Metalogic.«Combinator.cTrans»
                                    x9
                                    (_root_.GebMirror.Metalogic.«Combinator.cTrans»
                                      (_root_.GebMirror.Metalogic.«Language.p2» x11)
                                      (_root_.GebMirror.Metalogic.«Language.p2» x12))))
                          else
                            _root_.GebMirror.Metalogic.«Combinator.memoizeNf» x2 x8 x9))));
    x4

def «Combinator.normP» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree) =>
      _root_.Geb.Kernel.Const.para
        (α := _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
        (_root_.GebMirror.Metalogic.«Combinator.normStepP» x0 x1)
        x2);
    x2

def «Combinator.normP2» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.normP»
      x0
      (_root_.GebMirror.Metalogic.«Combinator.normP» x0 x1);
    x2

def «Combinator.normP4» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.normP2»
      x0
      (_root_.GebMirror.Metalogic.«Combinator.normP2» x0 x1);
    x2

def «Combinator.normP8» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.normP4»
      x0
      (_root_.GebMirror.Metalogic.«Combinator.normP4» x0 x1);
    x2

def «Combinator.normP16» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.normP8»
      x0
      (_root_.GebMirror.Metalogic.«Combinator.normP8» x0 x1);
    x2

def «Combinator.normP32» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.normP16»
      x0
      (_root_.GebMirror.Metalogic.«Combinator.normP16» x0 x1);
    x2

def «Combinator.normalizers» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.normP32»
      x0
      (_root_.GebMirror.Metalogic.«Combinator.normP32»
        x0
        (fun (_ : _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6661696c204c616e67756167652e545061697229»));
    x1

def «Combinator.pNormalize» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.normalizers»
      x0
      x1;
    x2

def «Combinator.beforeTerminal» :=
  _root_.GebMirror.Metalogic.«$285365712e6c656e677468205061727469616c486f726e2e53657175656e7429»
    _root_.GebMirror.Metalogic.«Theory.categoryAxioms»

def «Combinator.beforeProduct» :=
  _root_.Geb.Kernel.Const.add
    _root_.GebMirror.Metalogic.«Combinator.beforeTerminal»
    (_root_.GebMirror.Metalogic.«$285365712e6c656e677468205061727469616c486f726e2e53657175656e7429»
      _root_.GebMirror.Metalogic.«Theory.terminalAxioms»)

def «Combinator.beforeExponential» :=
  _root_.Geb.Kernel.Const.add
    _root_.GebMirror.Metalogic.«Combinator.beforeProduct»
    (_root_.Geb.Kernel.Const.add
      (_root_.GebMirror.Metalogic.«$285365712e6c656e677468205061727469616c486f726e2e53657175656e7429»
        _root_.GebMirror.Metalogic.«Theory.productAxioms»)
      (_root_.Geb.Kernel.Const.add
        (_root_.GebMirror.Metalogic.«$285365712e6c656e677468205061727469616c486f726e2e53657175656e7429»
          _root_.GebMirror.Metalogic.«Theory.equalizerAxioms»)
        (_root_.Geb.Kernel.Const.add
          (_root_.GebMirror.Metalogic.«$285365712e6c656e677468205061727469616c486f726e2e53657175656e7429»
            _root_.GebMirror.Metalogic.«Theory.initialAxioms»)
          (_root_.Geb.Kernel.Const.add
            (_root_.GebMirror.Metalogic.«$285365712e6c656e677468205061727469616c486f726e2e53657175656e7429»
              _root_.GebMirror.Metalogic.«Theory.coproductAxioms»)
            (_root_.GebMirror.Metalogic.«$285365712e6c656e677468205061727469616c486f726e2e53657175656e7429»
              _root_.GebMirror.Metalogic.«Theory.coequalizerAxioms»)))))

def «Combinator.beforeNat» :=
  _root_.Geb.Kernel.Const.add
    _root_.GebMirror.Metalogic.«Combinator.beforeExponential»
    (_root_.Geb.Kernel.Const.add
      (_root_.GebMirror.Metalogic.«$285365712e6c656e677468205061727469616c486f726e2e53657175656e7429»
        _root_.GebMirror.Metalogic.«Theory.exponentialAxioms»)
      (_root_.GebMirror.Metalogic.«$285365712e6c656e677468205061727469616c486f726e2e53657175656e7429»
        _root_.GebMirror.Metalogic.«Theory.classifierAxioms»))

def «Combinator.beforeList» :=
  _root_.Geb.Kernel.Const.add
    _root_.GebMirror.Metalogic.«Combinator.beforeNat»
    (_root_.GebMirror.Metalogic.«$285365712e6c656e677468205061727469616c486f726e2e53657175656e7429»
      _root_.GebMirror.Metalogic.«Theory.natAxioms»)

def «$28436f6d62696e61746f722e436f6d702e62696e64205061727469616c486f726e2e53657175656e7420436f6d62696e61746f722e45716e4365727429» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x4)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x5 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x5
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x6 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x5
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x8);
                                          let x8 : _root_.Geb.Kernel.Tree := x6;
                                          let x9 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x8;
                                          let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x9
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x10 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x10);
                                          let x11 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x9
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let x12 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x11
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x12 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x11
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x14);
                                          x1 x10 x2 x12
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62616420436f6d62696e61746f722e45716e4365727429»);
    x4

def «$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e5054797320436f6d62696e61746f722e45716e4365727429» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x4)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x5 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x5
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x6 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x5
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x8);
                                          let x8 : _root_.Geb.Kernel.Tree := x6;
                                          let x9 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x8;
                                          let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x9
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x10 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x10);
                                          let x11 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x9
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let x12 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x11
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x12 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x11
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x14);
                                          x1 x10 x2 x12
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62616420436f6d62696e61746f722e45716e4365727429»);
    x4

def «$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e436572747320436f6d62696e61746f722e45716e4365727429» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x4)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x5 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x5
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x6 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x5
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x8);
                                          let x8 : _root_.Geb.Kernel.Tree := x6;
                                          let x9 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x8;
                                          let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x9
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x10 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x10);
                                          let x11 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x9
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let x12 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x11
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x12 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x11
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x14);
                                          x1 x10 x2 x12
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62616420436f6d62696e61746f722e45716e4365727429»);
    x4

def «$28436f6d62696e61746f722e436f6d702e7075726520436f6d62696e61746f722e45716e4365727429» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (_ : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6f6b20436f6d62696e61746f722e45716e4365727429»
      (_root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e72657320436f6d62696e61746f722e45716e4365727429»
        x0
        x2);
    x3

def «Combinator.pInst» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64205061727469616c486f726e2e53657175656e7420436f6d62696e61746f722e45716e4365727429»
      (_root_.GebMirror.Metalogic.«Combinator.srcSeq» x0)
      (fun (x2 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e5054797320436f6d62696e61746f722e45716e4365727429»
          (_root_.GebMirror.Metalogic.«Combinator.mapMTY»
            _root_.GebMirror.Metalogic.«Combinator.typeTerm»
            x1)
          (fun (x3 : _root_.Geb.Kernel.Tree) =>
            let x4 : _root_.List
              _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.ptysOf» x3;
            _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e436572747320436f6d62696e61746f722e45716e4365727429»
              (_root_.GebMirror.Metalogic.«Combinator.mapMEqC»
                (_root_.GebMirror.Metalogic.«Combinator.proveHyp»
                  _root_.GebMirror.Metalogic.«Combinator.typePattern»
                  x4)
                (_root_.GebMirror.Metalogic.«PartialHorn.seqHyps» x2))
              (fun (x5 : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e7075726520436f6d62696e61746f722e45716e4365727429»
                  (_root_.GebMirror.Metalogic.«Combinator.eqnCert»
                    (_root_.GebMirror.Metalogic.«PartialHorn.eqSubst»
                      x1
                      (_root_.GebMirror.Metalogic.«PartialHorn.seqConcl» x2))
                    (_root_.GebMirror.Metalogic.«Combinator.srcCert»
                      x0
                      x1
                      (_root_.GebMirror.Metalogic.«$284d61702e6d617020436f6d62696e61746f722e505479205429»
                        _root_.GebMirror.Metalogic.«Combinator.tyDfd»
                        x4)
                      (_root_.GebMirror.Metalogic.«Combinator.certsOf» x5))))));
    x2

def «$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e45716e43657274204c616e67756167652e545061697229» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x4)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x5 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x5
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x6 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x5
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x8);
                                          let x8 : _root_.Geb.Kernel.Tree := x6;
                                          let x9 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x8;
                                          let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x9
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x10 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x10);
                                          let x11 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x9
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let x12 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x11
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x12 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x11
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x14);
                                          x1 x10 x2 x12
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e626164204c616e67756167652e545061697229»);
    x4

def «Combinator.etaExpand» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e505479204c616e67756167652e545061697229»
      (_root_.GebMirror.Metalogic.«Combinator.typeTerm» x0)
      (fun (x1 : _root_.Geb.Kernel.Tree) =>
        let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.tyHi»
          x1;
        if (_root_.GebMirror.Metalogic.«Prelude.and»
          (_root_.Geb.Kernel.Const.eq
            (_root_.Geb.Kernel.Const.label x2)
            (_root_.Geb.Kernel.leaf 7))
          (_root_.Geb.Kernel.Const.eq
            (_root_.GebMirror.Metalogic.«Prelude.length»
              (_root_.Geb.Kernel.Const.children x2))
            (_root_.Geb.Kernel.leaf 2))).label ≠ 0 then
          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e45716e43657274204c616e67756167652e545061697229»
            (_root_.GebMirror.Metalogic.«Combinator.pInst»
              (_root_.GebMirror.Metalogic.«Combinator.srcAx»
                (_root_.Geb.Kernel.Const.add
                  _root_.GebMirror.Metalogic.«Combinator.beforeProduct»
                  (_root_.Geb.Kernel.leaf 11)))
              (_root_.GebMirror.Metalogic.«Theory.l3»
                x0
                (_root_.GebMirror.Metalogic.«Prelude.at»
                  (_root_.Geb.Kernel.Const.children x2)
                  (_root_.Geb.Kernel.leaf 0))
                (_root_.GebMirror.Metalogic.«Prelude.at»
                  (_root_.Geb.Kernel.Const.children x2)
                  (_root_.Geb.Kernel.leaf 1))))
            (fun (x3 : _root_.Geb.Kernel.Tree) =>
              _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265204c616e67756167652e545061697229»
                (_root_.GebMirror.Metalogic.«Language.pr»
                  (_root_.GebMirror.Metalogic.«PartialHorn.eqLhs»
                    (_root_.GebMirror.Metalogic.«Combinator.ecEqn» x3))
                  (_root_.GebMirror.Metalogic.«Combinator.cSymm»
                    (_root_.GebMirror.Metalogic.«Combinator.ecCert» x3))))
        else
          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6661696c204c616e67756167652e545061697229»);
    x1

def «Combinator.rwAx» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.rwRule»
      (_root_.GebMirror.Metalogic.«Combinator.srcAx» x0)
      (_root_.Geb.Kernel.leaf 0)
      (_root_.GebMirror.Metalogic.«Combinator.labels»
        ([] : _root_.List _root_.Geb.Kernel.Tree));
    x1

def «Combinator.rwThm» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.rwRule»
      (_root_.GebMirror.Metalogic.«Combinator.srcThm» x0)
      (_root_.Geb.Kernel.leaf 0)
      (_root_.GebMirror.Metalogic.«Combinator.labels»
        ([] : _root_.List _root_.Geb.Kernel.Tree));
    x1

def «Combinator.deltaRule» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.rwAx»
      (_root_.GebMirror.Metalogic.«Infer.defAxIdx» x0);
    x1

def «$28436f6d62696e61746f722e436f6d702e62696e64204c616e67756167652e5450616972205429» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x4)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x5 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x5
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x6 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x5
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x8);
                                          let x8 : _root_.Geb.Kernel.Tree := x6;
                                          let x9 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x8;
                                          let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x9
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x10 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x10);
                                          let x11 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x9
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let x12 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x11
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x12 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x11
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x14);
                                          x1 x10 x2 x12
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e626164205429»);
    x4

def «$28436f6d62696e61746f722e436f6d702e62696e642054205429» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x4)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x5 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x5
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x6 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x5
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x8);
                                          let x8 : _root_.Geb.Kernel.Tree := x6;
                                          let x9 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x8;
                                          let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x9
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x10 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x10);
                                          let x11 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x9
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let x12 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x11
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x12 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x11
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x14);
                                          x1 x10 x2 x12
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e626164205429»);
    x4

def «Combinator.pByNorm» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64204c616e67756167652e5450616972205429»
      (_root_.GebMirror.Metalogic.«Combinator.pNormalize»
        x0
        (_root_.GebMirror.Metalogic.«PartialHorn.eqLhs» x1))
      (fun (x2 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64204c616e67756167652e5450616972205429»
          (_root_.GebMirror.Metalogic.«Combinator.pNormalize»
            x0
            (_root_.GebMirror.Metalogic.«PartialHorn.eqRhs» x1))
          (fun (x3 : _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e642054205429»
              (_root_.GebMirror.Metalogic.«Combinator.pmGuard»
                (_root_.Geb.Kernel.Const.equal
                  (_root_.GebMirror.Metalogic.«Language.p1» x2)
                  (_root_.GebMirror.Metalogic.«Language.p1» x3)))
              (fun (_ : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265205429»
                  (_root_.GebMirror.Metalogic.«Combinator.cTrans»
                    (_root_.GebMirror.Metalogic.«Language.p2» x2)
                    (_root_.GebMirror.Metalogic.«Combinator.cSymm»
                      (_root_.GebMirror.Metalogic.«Language.p2» x3))))));
    x2

def «Combinator.proved» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «Combinator.provedIdx» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                        let x2 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                          x1;
                                        let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x2
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x3 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x3);
                                        let x4 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x2
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x5);
                                        let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.Geb.Kernel.Tree)
                                          x4
                                          (_root_.Geb.Kernel.leaf 0)
                                          (fun (x5 : _root_.Geb.Kernel.Tree)
                                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x5);
                                        let _ : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x4
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x7);
                                        x3);
    x1

def «Combinator.provedDev» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                 let x2 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x1;
                                 let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree)
                                   x2
                                   (_root_.Geb.Kernel.leaf 0)
                                   (fun (x3 : _root_.Geb.Kernel.Tree)
                                      (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x3);
                                 let x4 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                   x2
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x5);
                                 let x5 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree)
                                   x4
                                   (_root_.Geb.Kernel.leaf 0)
                                   (fun (x5 : _root_.Geb.Kernel.Tree)
                                      (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x5);
                                 let _ : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                   x4
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x7);
                                 let x7 : _root_.Geb.Kernel.Tree := x5;
                                 let x8 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x7;
                                 let x9 : _root_.List _root_.Geb.Kernel.Tree := x8; x9);
    x1

def «$284f7074696f6e2e6e6f7468696e6720436f6d62696e61746f722e50726f76656429» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$284f7074696f6e2e6a75737420436f6d62696e61746f722e50726f76656429» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «Combinator.proveSeq» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree := (let x5 : _root_.Geb.Kernel.Tree := x1
                                          (_root_.GebMirror.Metalogic.«Combinator.scope»
                                            (_root_.GebMirror.Metalogic.«PartialHorn.sorts»
                                              (_root_.GebMirror.Metalogic.«PartialHorn.seqCtx» x0))
                                            (_root_.GebMirror.Metalogic.«PartialHorn.eqns»
                                              (_root_.GebMirror.Metalogic.«PartialHorn.seqHyps» x0)))
                                          (_root_.GebMirror.Metalogic.«Combinator.pmStart» x4 x2 x3);
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x5)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x6 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x5;
                                          let x7 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x6
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x7 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x7);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x6
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x9);
                                          let x9 : _root_.Geb.Kernel.Tree := x7;
                                          let x10 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x9;
                                          let x11 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x10
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x11 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x11);
                                          let x12 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x10
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x13 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x13);
                                          let x13 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x12
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x13 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x13);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x12
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x15 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x15);
                                          let x15 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.stDev»
                                            x13;
                                          _root_.GebMirror.Metalogic.«$284f7074696f6e2e6a75737420436f6d62696e61746f722e50726f76656429»
                                            (_root_.GebMirror.Metalogic.«Combinator.proved»
                                              (_root_.GebMirror.Metalogic.«$285365712e6c656e67746820436f6d62696e61746f722e446576456e74727929»
                                                x15)
                                              (_root_.GebMirror.Metalogic.«Combinator.devs»
                                                (_root_.GebMirror.Metalogic.«$285365712e617070656e6420436f6d62696e61746f722e446576456e74727929»
                                                  x15
                                                  (_root_.GebMirror.Metalogic.«$285365712e73696e676c6520436f6d62696e61746f722e446576456e74727929»
                                                    (_root_.GebMirror.Metalogic.«Combinator.devEntry»
                                                      x0
                                                      x11)))))
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x5;
                                          _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e6720436f6d62696e61746f722e50726f76656429»);
    x5

def «Combinator.normalizeThm» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree := (let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e74684f6620436f6d62696e61746f722e446576456e74727929»
                                          x4
                                          x1;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x5)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x6 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x5;
                                          let x7 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x6
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x7 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x7);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x6
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x9);
                                          let x9 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.devSeq»
                                            x7;
                                          let x10 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.scope»
                                            (_root_.GebMirror.Metalogic.«PartialHorn.sorts»
                                              (_root_.GebMirror.Metalogic.«PartialHorn.seqCtx» x9))
                                            (_root_.GebMirror.Metalogic.«PartialHorn.eqns»
                                              (_root_.GebMirror.Metalogic.«PartialHorn.seqHyps» x9));
                                          let x11 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.pNormalize»
                                            x0
                                            (_root_.GebMirror.Metalogic.«PartialHorn.eqLhs»
                                              (_root_.GebMirror.Metalogic.«PartialHorn.seqConcl» x9))
                                            x10
                                            (_root_.GebMirror.Metalogic.«Combinator.pmStart» x4 x2 x3);
                                          if (_root_.Geb.Kernel.Const.eq
                                            (_root_.Geb.Kernel.Const.label x11)
                                            (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                            let x12 : _root_.List
                                              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                              x11;
                                            let x13 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                              (α := _root_.Geb.Kernel.Tree)
                                              (β := _root_.Geb.Kernel.Tree)
                                              x12
                                              (_root_.Geb.Kernel.leaf 0)
                                              (fun (x13 : _root_.Geb.Kernel.Tree)
                                                 (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                                x13);
                                            let _ : _root_.List
                                              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                              (α := _root_.Geb.Kernel.Tree)
                                              (β := _root_.List _root_.Geb.Kernel.Tree)
                                              x12
                                              ([] : _root_.List _root_.Geb.Kernel.Tree)
                                              (fun (_ : _root_.Geb.Kernel.Tree)
                                                 (x15 : _root_.List _root_.Geb.Kernel.Tree) =>
                                                x15);
                                            let x15 : _root_.Geb.Kernel.Tree := x13;
                                            let x16 : _root_.List
                                              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                              x15;
                                            let x17 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                              (α := _root_.Geb.Kernel.Tree)
                                              (β := _root_.Geb.Kernel.Tree)
                                              x16
                                              (_root_.Geb.Kernel.leaf 0)
                                              (fun (x17 : _root_.Geb.Kernel.Tree)
                                                 (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                                x17);
                                            let x18 : _root_.List
                                              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                              (α := _root_.Geb.Kernel.Tree)
                                              (β := _root_.List _root_.Geb.Kernel.Tree)
                                              x16
                                              ([] : _root_.List _root_.Geb.Kernel.Tree)
                                              (fun (_ : _root_.Geb.Kernel.Tree)
                                                 (x19 : _root_.List _root_.Geb.Kernel.Tree) =>
                                                x19);
                                            let x19 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                              (α := _root_.Geb.Kernel.Tree)
                                              (β := _root_.Geb.Kernel.Tree)
                                              x18
                                              (_root_.Geb.Kernel.leaf 0)
                                              (fun (x19 : _root_.Geb.Kernel.Tree)
                                                 (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                                x19);
                                            let _ : _root_.List
                                              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                              (α := _root_.Geb.Kernel.Tree)
                                              (β := _root_.List _root_.Geb.Kernel.Tree)
                                              x18
                                              ([] : _root_.List _root_.Geb.Kernel.Tree)
                                              (fun (_ : _root_.Geb.Kernel.Tree)
                                                 (x21 : _root_.List _root_.Geb.Kernel.Tree) =>
                                                x21);
                                            let x21 : _root_.List
                                              _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.stDev»
                                              x19;
                                            _root_.GebMirror.Metalogic.«$284f7074696f6e2e6a75737420436f6d62696e61746f722e50726f76656429»
                                              (_root_.GebMirror.Metalogic.«Combinator.proved»
                                                (_root_.GebMirror.Metalogic.«$285365712e6c656e67746820436f6d62696e61746f722e446576456e74727929»
                                                  x21)
                                                (_root_.GebMirror.Metalogic.«Combinator.devs»
                                                  (_root_.GebMirror.Metalogic.«$285365712e617070656e6420436f6d62696e61746f722e446576456e74727929»
                                                    x21
                                                    (_root_.GebMirror.Metalogic.«$285365712e73696e676c6520436f6d62696e61746f722e446576456e74727929»
                                                      (_root_.GebMirror.Metalogic.«Combinator.devEntry»
                                                        (_root_.GebMirror.Metalogic.«Combinator.scSeq»
                                                          x10
                                                          (_root_.GebMirror.Metalogic.«PartialHorn.eqn»
                                                            (_root_.GebMirror.Metalogic.«Language.p1» x17)
                                                            (_root_.GebMirror.Metalogic.«PartialHorn.eqRhs»
                                                              (_root_.GebMirror.Metalogic.«PartialHorn.seqConcl»
                                                                x9))))
                                                        (_root_.GebMirror.Metalogic.«Combinator.cTrans»
                                                          (_root_.GebMirror.Metalogic.«Combinator.cSymm»
                                                            (_root_.GebMirror.Metalogic.«Language.p2» x17))
                                                          (_root_.GebMirror.Metalogic.«Combinator.scCite»
                                                            x10
                                                            x1)))))))
                                          else
                                            let _ : _root_.List
                                              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                              x11;
                                            _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e6720436f6d62696e61746f722e50726f76656429»
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x5;
                                          _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e6720436f6d62696e61746f722e50726f76656429»);
    x5

def «$28436f6d62696e61746f722e436f6d702e6f72456c7365205429» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
                                        let x5 : _root_.Geb.Kernel.Tree := x4;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x5)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x6 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x5;
                                          let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x6
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x7 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x7);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x6
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x9);
                                          x4
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x5;
                                          x1 x2 x3);
    x4

def «Combinator.instBy» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64205061727469616c486f726e2e53657175656e7420436f6d62696e61746f722e45716e4365727429»
      (_root_.GebMirror.Metalogic.«Combinator.srcSeq» x1)
      (fun (x3 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e5054797320436f6d62696e61746f722e45716e4365727429»
          (_root_.GebMirror.Metalogic.«Combinator.mapMTY»
            _root_.GebMirror.Metalogic.«Combinator.typeTerm»
            x2)
          (fun (x4 : _root_.Geb.Kernel.Tree) =>
            let x5 : _root_.List
              _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.ptysOf» x4;
            _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e436572747320436f6d62696e61746f722e45716e4365727429»
              (_root_.GebMirror.Metalogic.«Combinator.mapMEqC»
                (fun (x6 : _root_.Geb.Kernel.Tree) =>
                  _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6f72456c7365205429»
                    (_root_.GebMirror.Metalogic.«Combinator.proveHyp»
                      _root_.GebMirror.Metalogic.«Combinator.typePattern»
                      x5
                      x6)
                    (_root_.GebMirror.Metalogic.«Combinator.pByNorm»
                      x0
                      (_root_.GebMirror.Metalogic.«PartialHorn.eqSubst» x2 x6)))
                (_root_.GebMirror.Metalogic.«PartialHorn.seqHyps» x3))
              (fun (x6 : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e7075726520436f6d62696e61746f722e45716e4365727429»
                  (_root_.GebMirror.Metalogic.«Combinator.eqnCert»
                    (_root_.GebMirror.Metalogic.«PartialHorn.eqSubst»
                      x2
                      (_root_.GebMirror.Metalogic.«PartialHorn.seqConcl» x3))
                    (_root_.GebMirror.Metalogic.«Combinator.srcCert»
                      x1
                      x2
                      (_root_.GebMirror.Metalogic.«$284d61702e6d617020436f6d62696e61746f722e505479205429»
                        _root_.GebMirror.Metalogic.«Combinator.tyDfd»
                        x5)
                      (_root_.GebMirror.Metalogic.«Combinator.certsOf» x6))))));
    x3

def «Combinator.congStep» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List
      (_root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
    let x4 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree := (fun (x4 : _root_.Geb.Kernel.Tree) =>
      _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e505479205429»
        (_root_.GebMirror.Metalogic.«Combinator.typeTerm» x2)
        (fun (x5 : _root_.Geb.Kernel.Tree) =>
          if (_root_.Geb.Kernel.Const.equal x2 x4).label ≠ 0 then
            _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265205429»
              (_root_.GebMirror.Metalogic.«Combinator.tyDfd» x5)
          else
            if (_root_.GebMirror.Metalogic.«Prelude.and»
              (_root_.Geb.Kernel.Const.equal
                x2
                (_root_.GebMirror.Metalogic.«PartialHorn.eqLhs» x0))
              (_root_.Geb.Kernel.Const.equal
                x4
                (_root_.GebMirror.Metalogic.«PartialHorn.eqRhs» x0))).label ≠ 0 then
              _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265205429» x1
            else
              if (_root_.Geb.Kernel.Const.eq
                (_root_.GebMirror.Metalogic.«Combinator.tySort» x5)
                (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e505479205429»
                  (_root_.GebMirror.Metalogic.«Combinator.typeTerm» x4)
                  (fun (x6 : _root_.Geb.Kernel.Tree) =>
                    _root_.GebMirror.Metalogic.«Combinator.objEq» x5 x6)
              else
                if (_root_.GebMirror.Metalogic.«Prelude.or»
                  (_root_.Geb.Kernel.Const.eq
                    (_root_.Geb.Kernel.Const.label x2)
                    (_root_.Geb.Kernel.leaf 0))
                  (_root_.GebMirror.Metalogic.«Prelude.or»
                    (_root_.GebMirror.Metalogic.«Base.not»
                      (_root_.Geb.Kernel.Const.eq
                        (_root_.Geb.Kernel.Const.label x4)
                        (_root_.Geb.Kernel.Const.label x2)))
                    (_root_.GebMirror.Metalogic.«Base.not»
                      (_root_.Geb.Kernel.Const.eq
                        (_root_.GebMirror.Metalogic.«Prelude.length»
                          (_root_.Geb.Kernel.Const.children x4))
                        (_root_.GebMirror.Metalogic.«Prelude.length»
                          (_root_.Geb.Kernel.Const.children x2)))))).label ≠ 0 then
                  _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6661696c205429»
                else
                  _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e4365727473205429»
                    (_root_.GebMirror.Metalogic.«Combinator.bridgeKids»
                      x3
                      (_root_.Geb.Kernel.Const.children x4))
                    (fun (x6 : _root_.Geb.Kernel.Tree) =>
                      _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265205429»
                        (_root_.GebMirror.Metalogic.«Combinator.cCong»
                          (_root_.GebMirror.Metalogic.«Combinator.tyDfd» x5)
                          (_root_.GebMirror.Metalogic.«Combinator.certsOf» x6)))));
    x4

def «Combinator.congBy» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.para
      (α := _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«Combinator.congStep» x0 x1)
      x2
      x3;
    x4

def «$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e45716e43657274205429» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x4)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x5 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x5
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x6 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x5
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x8);
                                          let x8 : _root_.Geb.Kernel.Tree := x6;
                                          let x9 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x8;
                                          let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x9
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x10 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x10);
                                          let x11 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x9
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let x12 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x11
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x12 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x12);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x11
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x14 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x14);
                                          x1 x10 x2 x12
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e626164205429»);
    x4

def «Combinator.natRecUniq» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e45716e43657274205429»
      (_root_.GebMirror.Metalogic.«Combinator.instBy»
        x0
        (_root_.GebMirror.Metalogic.«Combinator.srcAx»
          (_root_.Geb.Kernel.Const.add
            _root_.GebMirror.Metalogic.«Combinator.beforeNat»
            (_root_.Geb.Kernel.leaf 12)))
        (_root_.GebMirror.Metalogic.«Theory.l3» x1 x2 x3))
      (fun (x4 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265205429»
          (_root_.GebMirror.Metalogic.«Combinator.ecCert» x4));
    x4

def «Combinator.listRecUniq» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e45716e43657274205429»
      (_root_.GebMirror.Metalogic.«Combinator.instBy»
        x0
        (_root_.GebMirror.Metalogic.«Combinator.srcAx»
          (_root_.Geb.Kernel.Const.add
            _root_.GebMirror.Metalogic.«Combinator.beforeList»
            (_root_.Geb.Kernel.leaf 13)))
        (_root_.GebMirror.Metalogic.«Theory.l4» x1 x2 x3 x4))
      (fun (x5 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265205429»
          (_root_.GebMirror.Metalogic.«Combinator.ecCert» x5));
    x5

def «Combinator.byNatInduction» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e642054205429»
      (_root_.GebMirror.Metalogic.«Combinator.natRecUniq»
        x0
        x1
        x2
        (_root_.GebMirror.Metalogic.«PartialHorn.eqLhs» x3))
      (fun (x4 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e642054205429»
          (_root_.GebMirror.Metalogic.«Combinator.natRecUniq»
            x0
            x1
            x2
            (_root_.GebMirror.Metalogic.«PartialHorn.eqRhs» x3))
          (fun (x5 : _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265205429»
              (_root_.GebMirror.Metalogic.«Combinator.cTrans»
                x4
                (_root_.GebMirror.Metalogic.«Combinator.cSymm» x5))));
    x4

def «Combinator.byListInduction» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e642054205429»
      (_root_.GebMirror.Metalogic.«Combinator.listRecUniq»
        x0
        x1
        x2
        x3
        (_root_.GebMirror.Metalogic.«PartialHorn.eqLhs» x4))
      (fun (x5 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e642054205429»
          (_root_.GebMirror.Metalogic.«Combinator.listRecUniq»
            x0
            x1
            x2
            x3
            (_root_.GebMirror.Metalogic.«PartialHorn.eqRhs» x4))
          (fun (x6 : _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265205429»
              (_root_.GebMirror.Metalogic.«Combinator.cTrans»
                x5
                (_root_.GebMirror.Metalogic.«Combinator.cSymm» x6))));
    x5

def «Combinator.byListParamInduction» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e505479205429»
      (_root_.GebMirror.Metalogic.«Combinator.typeTerm»
        (_root_.GebMirror.Metalogic.«PartialHorn.eqLhs» x4))
      (fun (x5 : _root_.Geb.Kernel.Tree) =>
        let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.tyLo»
          x5;
        if (_root_.GebMirror.Metalogic.«Prelude.and»
          (_root_.Geb.Kernel.Const.eq
            (_root_.Geb.Kernel.Const.label x6)
            (_root_.Geb.Kernel.leaf 7))
          (_root_.Geb.Kernel.Const.eq
            (_root_.GebMirror.Metalogic.«Prelude.length»
              (_root_.Geb.Kernel.Const.children x6))
            (_root_.Geb.Kernel.leaf 2))).label ≠ 0 then
          let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.at»
            (_root_.Geb.Kernel.Const.children x6)
            (_root_.Geb.Kernel.leaf 0);
          let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.at»
            (_root_.Geb.Kernel.Const.children x6)
            (_root_.Geb.Kernel.leaf 1);
          let x9 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.tyHi»
            x5;
          let x10 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Theory.exp» x8 x9;
          let x11 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Theory.prod»
            x1
            x10;
          let x12 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Theory.curry»
            _root_.GebMirror.Metalogic.«Theory.one»
            x8
            (_root_.GebMirror.Metalogic.«Theory.comp»
              x2
              (_root_.GebMirror.Metalogic.«Theory.cSnd» _root_.GebMirror.Metalogic.«Theory.one» x8));
          let x13 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Theory.curry»
            x11
            x8
            (_root_.GebMirror.Metalogic.«Theory.comp»
              x3
              (_root_.GebMirror.Metalogic.«Theory.cPair»
                (_root_.GebMirror.Metalogic.«Theory.cPair»
                  (_root_.GebMirror.Metalogic.«Theory.comp»
                    (_root_.GebMirror.Metalogic.«Theory.cFst» x1 x10)
                    (_root_.GebMirror.Metalogic.«Theory.cFst» x11 x8))
                  (_root_.GebMirror.Metalogic.«Theory.comp»
                    (_root_.GebMirror.Metalogic.«Theory.ev» x8 x9)
                    (_root_.GebMirror.Metalogic.«Theory.cPair»
                      (_root_.GebMirror.Metalogic.«Theory.comp»
                        (_root_.GebMirror.Metalogic.«Theory.cSnd» x1 x10)
                        (_root_.GebMirror.Metalogic.«Theory.cFst» x11 x8))
                      (_root_.GebMirror.Metalogic.«Theory.cSnd» x11 x8))))
                (_root_.GebMirror.Metalogic.«Theory.cSnd» x11 x8)));
          let x14 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Theory.curry»
            x7
            x8
            (_root_.GebMirror.Metalogic.«PartialHorn.eqLhs» x4);
          let x15 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Theory.curry»
            x7
            x8
            (_root_.GebMirror.Metalogic.«PartialHorn.eqRhs» x4);
          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e642054205429»
            (_root_.GebMirror.Metalogic.«Combinator.byListInduction»
              x0
              x1
              x12
              x13
              (_root_.GebMirror.Metalogic.«PartialHorn.eqn» x14 x15))
            (fun (x16 : _root_.Geb.Kernel.Tree) =>
              _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e45716e43657274205429»
                (_root_.GebMirror.Metalogic.«Combinator.pInst»
                  (_root_.GebMirror.Metalogic.«Combinator.srcAx»
                    (_root_.Geb.Kernel.Const.add
                      _root_.GebMirror.Metalogic.«Combinator.beforeExponential»
                      (_root_.Geb.Kernel.leaf 7)))
                  (_root_.GebMirror.Metalogic.«Theory.l3»
                    x7
                    x8
                    (_root_.GebMirror.Metalogic.«PartialHorn.eqLhs» x4)))
                (fun (x17 : _root_.Geb.Kernel.Tree) =>
                  _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e45716e43657274205429»
                    (_root_.GebMirror.Metalogic.«Combinator.pInst»
                      (_root_.GebMirror.Metalogic.«Combinator.srcAx»
                        (_root_.Geb.Kernel.Const.add
                          _root_.GebMirror.Metalogic.«Combinator.beforeExponential»
                          (_root_.Geb.Kernel.leaf 7)))
                      (_root_.GebMirror.Metalogic.«Theory.l3»
                        x7
                        x8
                        (_root_.GebMirror.Metalogic.«PartialHorn.eqRhs» x4)))
                    (fun (x18 : _root_.Geb.Kernel.Tree) =>
                      _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e642054205429»
                        (_root_.GebMirror.Metalogic.«Combinator.congBy»
                          (_root_.GebMirror.Metalogic.«PartialHorn.eqn» x14 x15)
                          x16
                          (_root_.GebMirror.Metalogic.«PartialHorn.eqLhs»
                            (_root_.GebMirror.Metalogic.«Combinator.ecEqn» x17))
                          (_root_.GebMirror.Metalogic.«PartialHorn.eqLhs»
                            (_root_.GebMirror.Metalogic.«Combinator.ecEqn» x18)))
                        (fun (x19 : _root_.Geb.Kernel.Tree) =>
                          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265205429»
                            (_root_.GebMirror.Metalogic.«Combinator.cTrans»
                              (_root_.GebMirror.Metalogic.«Combinator.cSymm»
                                (_root_.GebMirror.Metalogic.«Combinator.ecCert» x17))
                              (_root_.GebMirror.Metalogic.«Combinator.cTrans»
                                x19
                                (_root_.GebMirror.Metalogic.«Combinator.ecCert» x18)))))))
        else
          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e6661696c205429»);
    x5

def «$284665772e6c3220436f6d62696e61746f722e527752756c6529» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)));
    x2

def «Combinator.baseRules» :=
  ((_root_.GebMirror.Metalogic.«Combinator.rwRule»
    (_root_.GebMirror.Metalogic.«Combinator.srcAx» (_root_.Geb.Kernel.leaf 7))
    (_root_.Geb.Kernel.leaf 1)
    (_root_.GebMirror.Metalogic.«Combinator.labels»
      ([] : _root_.List _root_.Geb.Kernel.Tree))) ::
    ((_root_.GebMirror.Metalogic.«Combinator.rwAx» (_root_.Geb.Kernel.leaf 10)) ::
      ((_root_.GebMirror.Metalogic.«Combinator.rwAx» (_root_.Geb.Kernel.leaf 11)) ::
        ((_root_.GebMirror.Metalogic.«Combinator.rwAx»
          (_root_.Geb.Kernel.Const.add
            _root_.GebMirror.Metalogic.«Combinator.beforeProduct»
            (_root_.Geb.Kernel.leaf 9))) ::
          ((_root_.GebMirror.Metalogic.«Combinator.rwAx»
            (_root_.Geb.Kernel.Const.add
              _root_.GebMirror.Metalogic.«Combinator.beforeProduct»
              (_root_.Geb.Kernel.leaf 10))) ::
            ((_root_.GebMirror.Metalogic.«Combinator.rwAx»
              (_root_.Geb.Kernel.Const.add
                _root_.GebMirror.Metalogic.«Combinator.beforeProduct»
                (_root_.Geb.Kernel.leaf 11))) ::
              ((_root_.GebMirror.Metalogic.«Combinator.rwRule»
                (_root_.GebMirror.Metalogic.«Combinator.srcAx»
                  (_root_.Geb.Kernel.Const.add
                    _root_.GebMirror.Metalogic.«Combinator.beforeTerminal»
                    (_root_.Geb.Kernel.leaf 3)))
                (_root_.Geb.Kernel.leaf 0)
                (_root_.GebMirror.Metalogic.«Combinator.labels»
                  (_root_.GebMirror.Metalogic.«Theory.l2»
                    (_root_.Geb.Kernel.leaf 3)
                    (_root_.Geb.Kernel.leaf 6)))) ::
                ((_root_.GebMirror.Metalogic.«Combinator.rwAx»
                  (_root_.Geb.Kernel.Const.add
                    _root_.GebMirror.Metalogic.«Combinator.beforeNat»
                    (_root_.Geb.Kernel.leaf 10))) ::
                  ((_root_.GebMirror.Metalogic.«Combinator.rwAx»
                    (_root_.Geb.Kernel.Const.add
                      _root_.GebMirror.Metalogic.«Combinator.beforeNat»
                      (_root_.Geb.Kernel.leaf 11))) ::
                    (_root_.GebMirror.Metalogic.«$284665772e6c3220436f6d62696e61746f722e527752756c6529»
                      (_root_.GebMirror.Metalogic.«Combinator.rwAx»
                        (_root_.Geb.Kernel.Const.add
                          _root_.GebMirror.Metalogic.«Combinator.beforeList»
                          (_root_.Geb.Kernel.leaf 11)))
                      (_root_.GebMirror.Metalogic.«Combinator.rwAx»
                        (_root_.Geb.Kernel.Const.add
                          _root_.GebMirror.Metalogic.«Combinator.beforeList»
                          (_root_.Geb.Kernel.leaf 12)))))))))))))

def «Combinator.compPairSeq» :=
  _root_.GebMirror.Metalogic.«PartialHorn.mkSeq»
    (_root_.GebMirror.Metalogic.«Theory.l3»
      (_root_.Geb.Kernel.leaf 1)
      (_root_.Geb.Kernel.leaf 1)
      (_root_.Geb.Kernel.leaf 1))
    (_root_.GebMirror.Metalogic.«$284665772e6c32205061727469616c486f726e2e45716e29»
      (_root_.GebMirror.Metalogic.«PartialHorn.eqn»
        (_root_.GebMirror.Metalogic.«Theory.dom»
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 1)))
        (_root_.GebMirror.Metalogic.«Theory.dom»
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 0))))
      (_root_.GebMirror.Metalogic.«PartialHorn.eqn»
        (_root_.GebMirror.Metalogic.«Theory.cod»
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 2)))
        (_root_.GebMirror.Metalogic.«Theory.dom»
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 0)))))
    (_root_.GebMirror.Metalogic.«PartialHorn.eqn»
      (_root_.GebMirror.Metalogic.«Theory.comp»
        (_root_.GebMirror.Metalogic.«Theory.cPair»
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 0))
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 1)))
        (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 2)))
      (_root_.GebMirror.Metalogic.«Theory.cPair»
        (_root_.GebMirror.Metalogic.«Theory.comp»
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 0))
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 2)))
        (_root_.GebMirror.Metalogic.«Theory.comp»
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 1))
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 2)))))

def «Combinator.pairFstSndSeq» :=
  _root_.GebMirror.Metalogic.«PartialHorn.mkSeq»
    (_root_.GebMirror.Metalogic.«Theory.l2»
      (_root_.Geb.Kernel.leaf 0)
      (_root_.Geb.Kernel.leaf 0))
    ([] : _root_.List _root_.Geb.Kernel.Tree)
    (_root_.GebMirror.Metalogic.«PartialHorn.eqn»
      (_root_.GebMirror.Metalogic.«Theory.cPair»
        (_root_.GebMirror.Metalogic.«Theory.cFst»
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 0))
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 1)))
        (_root_.GebMirror.Metalogic.«Theory.cSnd»
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 0))
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 1))))
      (_root_.GebMirror.Metalogic.«Theory.idt»
        (_root_.GebMirror.Metalogic.«Theory.prod»
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 0))
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 1)))))

def «Combinator.evCurrySeq» :=
  _root_.GebMirror.Metalogic.«PartialHorn.mkSeq»
    (_root_.GebMirror.Metalogic.«Theory.l5»
      (_root_.Geb.Kernel.leaf 0)
      (_root_.Geb.Kernel.leaf 0)
      (_root_.Geb.Kernel.leaf 1)
      (_root_.Geb.Kernel.leaf 1)
      (_root_.Geb.Kernel.leaf 1))
    (_root_.GebMirror.Metalogic.«$284665772e6c34205061727469616c486f726e2e45716e29»
      (_root_.GebMirror.Metalogic.«PartialHorn.eqn»
        (_root_.GebMirror.Metalogic.«Theory.dom»
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 2)))
        (_root_.GebMirror.Metalogic.«Theory.prod»
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 0))
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 1))))
      (_root_.GebMirror.Metalogic.«PartialHorn.eqn»
        (_root_.GebMirror.Metalogic.«Theory.cod»
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 3)))
        (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 0)))
      (_root_.GebMirror.Metalogic.«PartialHorn.eqn»
        (_root_.GebMirror.Metalogic.«Theory.cod»
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 4)))
        (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 1)))
      (_root_.GebMirror.Metalogic.«PartialHorn.eqn»
        (_root_.GebMirror.Metalogic.«Theory.dom»
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 4)))
        (_root_.GebMirror.Metalogic.«Theory.dom»
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 3)))))
    (_root_.GebMirror.Metalogic.«PartialHorn.eqn»
      (_root_.GebMirror.Metalogic.«Theory.comp»
        (_root_.GebMirror.Metalogic.«Theory.ev»
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 1))
          (_root_.GebMirror.Metalogic.«Theory.cod»
            (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 2))))
        (_root_.GebMirror.Metalogic.«Theory.cPair»
          (_root_.GebMirror.Metalogic.«Theory.comp»
            (_root_.GebMirror.Metalogic.«Theory.curry»
              (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 0))
              (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 1))
              (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 2)))
            (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 3)))
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 4))))
      (_root_.GebMirror.Metalogic.«Theory.comp»
        (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 2))
        (_root_.GebMirror.Metalogic.«Theory.cPair»
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 3))
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 4)))))

def «Combinator.evCurry0Seq» :=
  _root_.GebMirror.Metalogic.«PartialHorn.mkSeq»
    (_root_.GebMirror.Metalogic.«Theory.l4»
      (_root_.Geb.Kernel.leaf 0)
      (_root_.Geb.Kernel.leaf 0)
      (_root_.Geb.Kernel.leaf 1)
      (_root_.Geb.Kernel.leaf 1))
    (_root_.GebMirror.Metalogic.«$284665772e6c33205061727469616c486f726e2e45716e29»
      (_root_.GebMirror.Metalogic.«PartialHorn.eqn»
        (_root_.GebMirror.Metalogic.«Theory.dom»
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 2)))
        (_root_.GebMirror.Metalogic.«Theory.prod»
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 0))
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 1))))
      (_root_.GebMirror.Metalogic.«PartialHorn.eqn»
        (_root_.GebMirror.Metalogic.«Theory.cod»
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 3)))
        (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 1)))
      (_root_.GebMirror.Metalogic.«PartialHorn.eqn»
        (_root_.GebMirror.Metalogic.«Theory.dom»
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 3)))
        (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 0))))
    (_root_.GebMirror.Metalogic.«PartialHorn.eqn»
      (_root_.GebMirror.Metalogic.«Theory.comp»
        (_root_.GebMirror.Metalogic.«Theory.ev»
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 1))
          (_root_.GebMirror.Metalogic.«Theory.cod»
            (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 2))))
        (_root_.GebMirror.Metalogic.«Theory.cPair»
          (_root_.GebMirror.Metalogic.«Theory.curry»
            (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 0))
            (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 1))
            (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 2)))
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 3))))
      (_root_.GebMirror.Metalogic.«Theory.comp»
        (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 2))
        (_root_.GebMirror.Metalogic.«Theory.cPair»
          (_root_.GebMirror.Metalogic.«Theory.idt»
            (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 0)))
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 3)))))

def «Combinator.curryNatSeq» :=
  _root_.GebMirror.Metalogic.«PartialHorn.mkSeq»
    (_root_.GebMirror.Metalogic.«Theory.l4»
      (_root_.Geb.Kernel.leaf 0)
      (_root_.Geb.Kernel.leaf 0)
      (_root_.Geb.Kernel.leaf 1)
      (_root_.Geb.Kernel.leaf 1))
    (_root_.GebMirror.Metalogic.«$284665772e6c32205061727469616c486f726e2e45716e29»
      (_root_.GebMirror.Metalogic.«PartialHorn.eqn»
        (_root_.GebMirror.Metalogic.«Theory.dom»
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 2)))
        (_root_.GebMirror.Metalogic.«Theory.prod»
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 0))
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 1))))
      (_root_.GebMirror.Metalogic.«PartialHorn.eqn»
        (_root_.GebMirror.Metalogic.«Theory.cod»
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 3)))
        (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 0))))
    (_root_.GebMirror.Metalogic.«PartialHorn.eqn»
      (_root_.GebMirror.Metalogic.«Theory.comp»
        (_root_.GebMirror.Metalogic.«Theory.curry»
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 0))
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 1))
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 2)))
        (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 3)))
      (_root_.GebMirror.Metalogic.«Theory.curry»
        (_root_.GebMirror.Metalogic.«Theory.dom»
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 3)))
        (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 1))
        (_root_.GebMirror.Metalogic.«Theory.comp»
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 2))
          (_root_.GebMirror.Metalogic.«Theory.prodMapLeft»
            (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 3))
            (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 1))))))

def «Combinator.bangOneSeq» :=
  _root_.GebMirror.Metalogic.«PartialHorn.mkSeq»
    ([] : _root_.List _root_.Geb.Kernel.Tree)
    ([] : _root_.List _root_.Geb.Kernel.Tree)
    (_root_.GebMirror.Metalogic.«PartialHorn.eqn»
      (_root_.GebMirror.Metalogic.«Theory.bang» _root_.GebMirror.Metalogic.«Theory.one»)
      (_root_.GebMirror.Metalogic.«Theory.idt» _root_.GebMirror.Metalogic.«Theory.one»))

def «Combinator.seqLhs» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«PartialHorn.eqLhs»
      (_root_.GebMirror.Metalogic.«PartialHorn.seqConcl» x0);
    x1

def «Combinator.seqRhs» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«PartialHorn.eqRhs»
      (_root_.GebMirror.Metalogic.«PartialHorn.seqConcl» x0);
    x1

def «Combinator.compPairProof» :=
  _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64204c616e67756167652e5450616972205429»
    (_root_.GebMirror.Metalogic.«Combinator.etaExpand»
      (_root_.GebMirror.Metalogic.«Combinator.seqLhs»
        _root_.GebMirror.Metalogic.«Combinator.compPairSeq»))
    (fun (x0 : _root_.Geb.Kernel.Tree) =>
      _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64204c616e67756167652e5450616972205429»
        (_root_.GebMirror.Metalogic.«Combinator.pNormalize»
          _root_.GebMirror.Metalogic.«Combinator.baseRules»
          (_root_.GebMirror.Metalogic.«Language.p1» x0))
        (fun (x1 : _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e642054205429»
            (_root_.GebMirror.Metalogic.«Combinator.pmGuard»
              (_root_.Geb.Kernel.Const.equal
                (_root_.GebMirror.Metalogic.«Language.p1» x1)
                (_root_.GebMirror.Metalogic.«Combinator.seqRhs»
                  _root_.GebMirror.Metalogic.«Combinator.compPairSeq»)))
            (fun (_ : _root_.Geb.Kernel.Tree) =>
              _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265205429»
                (_root_.GebMirror.Metalogic.«Combinator.cTrans»
                  (_root_.GebMirror.Metalogic.«Language.p2» x0)
                  (_root_.GebMirror.Metalogic.«Language.p2» x1)))))

def «Combinator.pairFstSndProof» :=
  let x0 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Theory.prod»
    (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 0))
    (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 1));
  _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e45716e43657274205429»
    (_root_.GebMirror.Metalogic.«Combinator.pInst»
      (_root_.GebMirror.Metalogic.«Combinator.srcAx»
        (_root_.Geb.Kernel.Const.add
          _root_.GebMirror.Metalogic.«Combinator.beforeProduct»
          (_root_.Geb.Kernel.leaf 11)))
      (_root_.GebMirror.Metalogic.«Theory.l3»
        (_root_.GebMirror.Metalogic.«Theory.idt» x0)
        (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 0))
        (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 1))))
    (fun (x1 : _root_.Geb.Kernel.Tree) =>
      _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64204c616e67756167652e5450616972205429»
        (_root_.GebMirror.Metalogic.«Combinator.pNormalize»
          _root_.GebMirror.Metalogic.«Combinator.baseRules»
          (_root_.GebMirror.Metalogic.«PartialHorn.eqLhs»
            (_root_.GebMirror.Metalogic.«Combinator.ecEqn» x1)))
        (fun (x2 : _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e642054205429»
            (_root_.GebMirror.Metalogic.«Combinator.pmGuard»
              (_root_.Geb.Kernel.Const.equal
                (_root_.GebMirror.Metalogic.«Language.p1» x2)
                (_root_.GebMirror.Metalogic.«Combinator.seqLhs»
                  _root_.GebMirror.Metalogic.«Combinator.pairFstSndSeq»)))
            (fun (_ : _root_.Geb.Kernel.Tree) =>
              _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265205429»
                (_root_.GebMirror.Metalogic.«Combinator.cTrans»
                  (_root_.GebMirror.Metalogic.«Combinator.cSymm» (_root_.GebMirror.Metalogic.«Language.p2» x2))
                  (_root_.GebMirror.Metalogic.«Combinator.ecCert» x1)))))

def «$285365712e617070656e6420436f6d62696e61746f722e527752756c6529» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        (x2 :: x3))
      x1
      x0;
    x2

def «$285365712e73696e676c6520436f6d62696e61746f722e527752756c6529» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      ([] : _root_.List _root_.Geb.Kernel.Tree));
    x1

def «Combinator.evCurryProof» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (let x1 : _root_.List
                                     _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$285365712e617070656e6420436f6d62696e61746f722e527752756c6529»
                                     _root_.GebMirror.Metalogic.«Combinator.baseRules»
                                     (_root_.GebMirror.Metalogic.«$285365712e73696e676c6520436f6d62696e61746f722e527752756c6529»
                                       (_root_.GebMirror.Metalogic.«Combinator.rwThm» x0));
                                   _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e45716e43657274205429»
                                     (_root_.GebMirror.Metalogic.«Combinator.pInst»
                                       (_root_.GebMirror.Metalogic.«Combinator.srcAx»
                                         (_root_.Geb.Kernel.Const.add
                                           _root_.GebMirror.Metalogic.«Combinator.beforeExponential»
                                           (_root_.Geb.Kernel.leaf 7)))
                                       (_root_.GebMirror.Metalogic.«Theory.l3»
                                         (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 0))
                                         (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 1))
                                         (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 2))))
                                     (fun (x2 : _root_.Geb.Kernel.Tree) =>
                                       let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Theory.cPair»
                                         (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 3))
                                         (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 4));
                                       let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Theory.comp»
                                         (_root_.GebMirror.Metalogic.«PartialHorn.eqLhs»
                                           (_root_.GebMirror.Metalogic.«Combinator.ecEqn» x2))
                                         x3;
                                       _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64204c616e67756167652e5450616972205429»
                                         (_root_.GebMirror.Metalogic.«Combinator.pNormalize» x1 x4)
                                         (fun (x5 : _root_.Geb.Kernel.Tree) =>
                                           _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64204c616e67756167652e5450616972205429»
                                             (_root_.GebMirror.Metalogic.«Combinator.pNormalize»
                                               x1
                                               (_root_.GebMirror.Metalogic.«Combinator.seqLhs»
                                                 _root_.GebMirror.Metalogic.«Combinator.evCurrySeq»))
                                             (fun (x6 : _root_.Geb.Kernel.Tree) =>
                                               _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e642054205429»
                                                 (_root_.GebMirror.Metalogic.«Combinator.pmGuard»
                                                   (_root_.Geb.Kernel.Const.equal
                                                     (_root_.GebMirror.Metalogic.«Language.p1» x5)
                                                     (_root_.GebMirror.Metalogic.«Language.p1» x6)))
                                                 (fun (_ : _root_.Geb.Kernel.Tree) =>
                                                   _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e505479205429»
                                                     (_root_.GebMirror.Metalogic.«Combinator.typeTerm» x4)
                                                     (fun (x8 : _root_.Geb.Kernel.Tree) =>
                                                       _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e505479205429»
                                                         (_root_.GebMirror.Metalogic.«Combinator.typeTerm» x3)
                                                         (fun (x9 : _root_.Geb.Kernel.Tree) =>
                                                           _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265205429»
                                                             (_root_.GebMirror.Metalogic.«Combinator.cTrans»
                                                               (_root_.GebMirror.Metalogic.«Combinator.cTrans»
                                                                 (_root_.GebMirror.Metalogic.«Language.p2» x6)
                                                                 (_root_.GebMirror.Metalogic.«Combinator.cSymm»
                                                                   (_root_.GebMirror.Metalogic.«Language.p2»
                                                                     x5)))
                                                               (_root_.GebMirror.Metalogic.«Combinator.cCong»
                                                                 (_root_.GebMirror.Metalogic.«Combinator.tyDfd»
                                                                   x8)
                                                                 (_root_.GebMirror.Metalogic.«Theory.l2»
                                                                   (_root_.GebMirror.Metalogic.«Combinator.ecCert»
                                                                     x2)
                                                                   (_root_.GebMirror.Metalogic.«Combinator.tyDfd»
                                                                     x9)))))))))));
    x1

def «Combinator.evCurry0Proof» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e45716e43657274205429»
      (_root_.GebMirror.Metalogic.«Combinator.pInst»
        (_root_.GebMirror.Metalogic.«Combinator.srcThm» x0)
        (_root_.GebMirror.Metalogic.«Theory.l5»
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 0))
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 1))
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 2))
          (_root_.GebMirror.Metalogic.«Theory.idt»
            (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 0)))
          (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 3))))
      (fun (x1 : _root_.Geb.Kernel.Tree) =>
        let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.ecEqn»
          x1;
        _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64204c616e67756167652e5450616972205429»
          (_root_.GebMirror.Metalogic.«Combinator.pNormalize»
            _root_.GebMirror.Metalogic.«Combinator.baseRules»
            (_root_.GebMirror.Metalogic.«PartialHorn.eqLhs» x2))
          (fun (x3 : _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e642054205429»
              (_root_.GebMirror.Metalogic.«Combinator.pmGuard»
                (_root_.GebMirror.Metalogic.«Prelude.and»
                  (_root_.Geb.Kernel.Const.equal
                    (_root_.GebMirror.Metalogic.«Language.p1» x3)
                    (_root_.GebMirror.Metalogic.«Combinator.seqLhs»
                      _root_.GebMirror.Metalogic.«Combinator.evCurry0Seq»))
                  (_root_.Geb.Kernel.Const.equal
                    (_root_.GebMirror.Metalogic.«PartialHorn.eqRhs» x2)
                    (_root_.GebMirror.Metalogic.«Combinator.seqRhs»
                      _root_.GebMirror.Metalogic.«Combinator.evCurry0Seq»))))
              (fun (_ : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265205429»
                  (_root_.GebMirror.Metalogic.«Combinator.cTrans»
                    (_root_.GebMirror.Metalogic.«Combinator.cSymm» (_root_.GebMirror.Metalogic.«Language.p2» x3))
                    (_root_.GebMirror.Metalogic.«Combinator.ecCert» x1)))));
    x1

def «Combinator.curryNatProof» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (let x2 : _root_.List
                                     _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$285365712e617070656e6420436f6d62696e61746f722e527752756c6529»
                                     _root_.GebMirror.Metalogic.«Combinator.baseRules»
                                     (_root_.GebMirror.Metalogic.«$284665772e6c3220436f6d62696e61746f722e527752756c6529»
                                       (_root_.GebMirror.Metalogic.«Combinator.rwThm» x0)
                                       (_root_.GebMirror.Metalogic.«Combinator.rwThm» x1));
                                   let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.seqLhs»
                                     _root_.GebMirror.Metalogic.«Combinator.curryNatSeq»;
                                   _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e45716e43657274205429»
                                     (_root_.GebMirror.Metalogic.«Combinator.pInst»
                                       (_root_.GebMirror.Metalogic.«Combinator.srcAx»
                                         (_root_.Geb.Kernel.Const.add
                                           _root_.GebMirror.Metalogic.«Combinator.beforeExponential»
                                           (_root_.Geb.Kernel.leaf 8)))
                                       (_root_.GebMirror.Metalogic.«Theory.l4»
                                         (_root_.GebMirror.Metalogic.«Theory.dom»
                                           (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 3)))
                                         (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 1))
                                         (_root_.GebMirror.Metalogic.«Theory.cod»
                                           (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 2)))
                                         x3))
                                     (fun (x4 : _root_.Geb.Kernel.Tree) =>
                                       _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64204c616e67756167652e5450616972205429»
                                         (_root_.GebMirror.Metalogic.«Combinator.pNormalize»
                                           x2
                                           (_root_.GebMirror.Metalogic.«PartialHorn.eqLhs»
                                             (_root_.GebMirror.Metalogic.«Combinator.ecEqn» x4)))
                                         (fun (x5 : _root_.Geb.Kernel.Tree) =>
                                           _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64204c616e67756167652e5450616972205429»
                                             (_root_.GebMirror.Metalogic.«Combinator.pNormalize»
                                               x2
                                               (_root_.GebMirror.Metalogic.«Combinator.seqRhs»
                                                 _root_.GebMirror.Metalogic.«Combinator.curryNatSeq»))
                                             (fun (x6 : _root_.Geb.Kernel.Tree) =>
                                               _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e642054205429»
                                                 (_root_.GebMirror.Metalogic.«Combinator.pmGuard»
                                                   (_root_.Geb.Kernel.Const.equal
                                                     (_root_.GebMirror.Metalogic.«Language.p1» x5)
                                                     (_root_.GebMirror.Metalogic.«Language.p1» x6)))
                                                 (fun (_ : _root_.Geb.Kernel.Tree) =>
                                                   _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265205429»
                                                     (_root_.GebMirror.Metalogic.«Combinator.cTrans»
                                                       (_root_.GebMirror.Metalogic.«Combinator.cSymm»
                                                         (_root_.GebMirror.Metalogic.«Combinator.ecCert» x4))
                                                       (_root_.GebMirror.Metalogic.«Combinator.cTrans»
                                                         (_root_.GebMirror.Metalogic.«Language.p2» x5)
                                                         (_root_.GebMirror.Metalogic.«Combinator.cSymm»
                                                           (_root_.GebMirror.Metalogic.«Language.p2»
                                                             x6)))))))));
    x2

def «Combinator.bangOneProof» :=
  _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e6420436f6d62696e61746f722e45716e43657274205429»
    (_root_.GebMirror.Metalogic.«Combinator.pInst»
      (_root_.GebMirror.Metalogic.«Combinator.srcAx»
        (_root_.Geb.Kernel.Const.add
          _root_.GebMirror.Metalogic.«Combinator.beforeTerminal»
          (_root_.Geb.Kernel.leaf 3)))
      (_root_.GebMirror.Metalogic.«Prelude.single»
        (_root_.GebMirror.Metalogic.«Theory.idt» _root_.GebMirror.Metalogic.«Theory.one»)))
    (fun (x0 : _root_.Geb.Kernel.Tree) =>
      _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e64204c616e67756167652e5450616972205429»
        (_root_.GebMirror.Metalogic.«Combinator.pNormalize»
          _root_.GebMirror.Metalogic.«Combinator.baseRules»
          (_root_.GebMirror.Metalogic.«PartialHorn.eqRhs»
            (_root_.GebMirror.Metalogic.«Combinator.ecEqn» x0)))
        (fun (x1 : _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e62696e642054205429»
            (_root_.GebMirror.Metalogic.«Combinator.pmGuard»
              (_root_.Geb.Kernel.Const.equal
                (_root_.GebMirror.Metalogic.«Language.p1» x1)
                (_root_.GebMirror.Metalogic.«Theory.bang» _root_.GebMirror.Metalogic.«Theory.one»)))
            (fun (_ : _root_.Geb.Kernel.Tree) =>
              _root_.GebMirror.Metalogic.«$28436f6d62696e61746f722e436f6d702e70757265205429»
                (_root_.GebMirror.Metalogic.«Combinator.cSymm»
                  (_root_.GebMirror.Metalogic.«Combinator.cTrans»
                    (_root_.GebMirror.Metalogic.«Combinator.ecCert» x0)
                    (_root_.GebMirror.Metalogic.«Language.p2» x1))))))

def «Combinator.indices» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 0) x0

def «Combinator.library» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «$284f7074696f6e2e6e6f7468696e6720436f6d62696e61746f722e4c69627261727929» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$284f7074696f6e2e6a75737420436f6d62696e61746f722e4c69627261727929» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «Combinator.bindPr» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (let x2 : _root_.Geb.Kernel.Tree := x0;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x2)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x3 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x2;
                                          let x4 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.Geb.Kernel.Tree)
                                            x3
                                            (_root_.Geb.Kernel.leaf 0)
                                            (fun (x4 : _root_.Geb.Kernel.Tree)
                                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x4);
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x3
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x6 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x6);
                                          x1 x4
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x2;
                                          _root_.GebMirror.Metalogic.«$284f7074696f6e2e6e6f7468696e6720436f6d62696e61746f722e4c69627261727929»);
    x2

def «Combinator.libraryWith» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.bindPr»
      (_root_.GebMirror.Metalogic.«Combinator.proveSeq»
        _root_.GebMirror.Metalogic.«Combinator.compPairSeq»
        _root_.GebMirror.Metalogic.«Combinator.compPairProof»
        ([] : _root_.List _root_.Geb.Kernel.Tree)
        x0
        ([] : _root_.List _root_.Geb.Kernel.Tree))
      (fun (x1 : _root_.Geb.Kernel.Tree) =>
        let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.provedIdx»
          x1;
        _root_.GebMirror.Metalogic.«Combinator.bindPr»
          (_root_.GebMirror.Metalogic.«Combinator.proveSeq»
            _root_.GebMirror.Metalogic.«Combinator.pairFstSndSeq»
            _root_.GebMirror.Metalogic.«Combinator.pairFstSndProof»
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            x0
            (_root_.GebMirror.Metalogic.«Combinator.provedDev» x1))
          (fun (x3 : _root_.Geb.Kernel.Tree) =>
            let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.provedIdx»
              x3;
            _root_.GebMirror.Metalogic.«Combinator.bindPr»
              (_root_.GebMirror.Metalogic.«Combinator.proveSeq»
                _root_.GebMirror.Metalogic.«Combinator.evCurrySeq»
                (_root_.GebMirror.Metalogic.«Combinator.evCurryProof» x2)
                ([] : _root_.List _root_.Geb.Kernel.Tree)
                x0
                (_root_.GebMirror.Metalogic.«Combinator.provedDev» x3))
              (fun (x5 : _root_.Geb.Kernel.Tree) =>
                let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.provedIdx»
                  x5;
                _root_.GebMirror.Metalogic.«Combinator.bindPr»
                  (_root_.GebMirror.Metalogic.«Combinator.proveSeq»
                    _root_.GebMirror.Metalogic.«Combinator.evCurry0Seq»
                    (_root_.GebMirror.Metalogic.«Combinator.evCurry0Proof» x6)
                    ([] : _root_.List _root_.Geb.Kernel.Tree)
                    x0
                    (_root_.GebMirror.Metalogic.«Combinator.provedDev» x5))
                  (fun (x7 : _root_.Geb.Kernel.Tree) =>
                    let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.provedIdx»
                      x7;
                    _root_.GebMirror.Metalogic.«Combinator.bindPr»
                      (_root_.GebMirror.Metalogic.«Combinator.proveSeq»
                        _root_.GebMirror.Metalogic.«Combinator.curryNatSeq»
                        (_root_.GebMirror.Metalogic.«Combinator.curryNatProof» x2 x6)
                        ([] : _root_.List _root_.Geb.Kernel.Tree)
                        x0
                        (_root_.GebMirror.Metalogic.«Combinator.provedDev» x7))
                      (fun (x9 : _root_.Geb.Kernel.Tree) =>
                        let x10 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.provedIdx»
                          x9;
                        _root_.GebMirror.Metalogic.«Combinator.bindPr»
                          (_root_.GebMirror.Metalogic.«Combinator.proveSeq»
                            _root_.GebMirror.Metalogic.«Combinator.bangOneSeq»
                            _root_.GebMirror.Metalogic.«Combinator.bangOneProof»
                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                            x0
                            (_root_.GebMirror.Metalogic.«Combinator.provedDev» x9))
                          (fun (x11 : _root_.Geb.Kernel.Tree) =>
                            _root_.GebMirror.Metalogic.«$284f7074696f6e2e6a75737420436f6d62696e61746f722e4c69627261727929»
                              (_root_.GebMirror.Metalogic.«Combinator.library»
                                (_root_.GebMirror.Metalogic.«Combinator.indices»
                                  (_root_.GebMirror.Metalogic.«Theory.l6»
                                    x2
                                    x4
                                    x6
                                    x8
                                    x10
                                    (_root_.GebMirror.Metalogic.«Combinator.provedIdx» x11)))
                                (_root_.GebMirror.Metalogic.«Combinator.devs»
                                  (_root_.GebMirror.Metalogic.«Combinator.provedDev» x11)))))))));
    x1

def «$284665772e6c3320436f6d62696e61746f722e527752756c6529» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      (_root_.GebMirror.Metalogic.«$284665772e6c3220436f6d62696e61746f722e527752756c6529»
        x1
        x2));
    x3

def «$284665772e6c3420436f6d62696e61746f722e527752756c6529» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      (_root_.GebMirror.Metalogic.«$284665772e6c3320436f6d62696e61746f722e527752756c6529»
        x1
        x2
        x3));
    x4

def «$284665772e6c3520436f6d62696e61746f722e527752756c6529» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      (_root_.GebMirror.Metalogic.«$284665772e6c3420436f6d62696e61746f722e527752756c6529»
        x1
        x2
        x3
        x4));
    x5

def «Combinator.libRules» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (let x1 : _root_.List
                                   _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                                              let x2 : _root_.List
                                                                _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                                x1;
                                                              let x3 : _root_.List
                                                                _root_.Geb.Kernel.Tree := x2;
                                                              x3);
                                 _root_.GebMirror.Metalogic.«$285365712e617070656e6420436f6d62696e61746f722e527752756c6529»
                                   _root_.GebMirror.Metalogic.«Combinator.baseRules»
                                   (_root_.GebMirror.Metalogic.«$284665772e6c3520436f6d62696e61746f722e527752756c6529»
                                     (_root_.GebMirror.Metalogic.«Combinator.rwThm»
                                       (_root_.GebMirror.Metalogic.«Prelude.at» x1 (_root_.Geb.Kernel.leaf 0)))
                                     (_root_.GebMirror.Metalogic.«Combinator.rwThm»
                                       (_root_.GebMirror.Metalogic.«Prelude.at» x1 (_root_.Geb.Kernel.leaf 1)))
                                     (_root_.GebMirror.Metalogic.«Combinator.rwThm»
                                       (_root_.GebMirror.Metalogic.«Prelude.at» x1 (_root_.Geb.Kernel.leaf 4)))
                                     (_root_.GebMirror.Metalogic.«Combinator.rwThm»
                                       (_root_.GebMirror.Metalogic.«Prelude.at» x1 (_root_.Geb.Kernel.leaf 3)))
                                     (_root_.GebMirror.Metalogic.«Combinator.rwThm»
                                       (_root_.GebMirror.Metalogic.«Prelude.at»
                                         x1
                                         (_root_.Geb.Kernel.leaf 5)))));
    x1

end GebMirror.Metalogic

end
