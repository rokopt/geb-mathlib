module

public import GebMirror.Metalogic.Affine
public import Geb.Prototypes.FreeTopos.Internal.Accelerate

/-! Generated from a Geb program by `bootstrap/stage1/lean.geb`. -/

@[expose] public section

open Geb.Kernel
open Geb.Kernel renaming Tree → T

namespace GebMirror.Metalogic

def «Literals.litBits» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «Literals.litOrd» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «Literals.litPair» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 2)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «$4c69746572616c732f4f4c69742e6e6f7468696e67» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$4c69746572616c732f4f4c69742e6a757374» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «$4c69746572616c732f4f4c69742e69734a757374» :=
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

def «$4c69746572616c732f4f4c69742e66726f6d4d61796265» :=
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

def «$4c69746572616c732f4f4c69742e6e74684f66» :=
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
      _root_.GebMirror.Metalogic.«$4c69746572616c732f4f4c69742e6e6f7468696e67»
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$4c69746572616c732f4f4c69742e6a757374» x2);
    x2

def «$4c69746572616c732f4f4c69742e616c6c4a757374» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree ×
      _root_.List
        _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree) =>
        let x3 : _root_.Geb.Kernel.Tree := x1;
        if (_root_.Geb.Kernel.Const.eq
          (_root_.Geb.Kernel.Const.label x3)
          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
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
          let _ : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.List _root_.Geb.Kernel.Tree)
            x4
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (fun (_ : _root_.Geb.Kernel.Tree)
               (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
              x7);
          ((x2).1, (x5 :: (x2).2))
        else
          let _ : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x3;
          (_root_.Geb.Kernel.leaf 0, (x2).2))
      (_root_.Geb.Kernel.leaf 1, ([] : _root_.List _root_.Geb.Kernel.Tree))
      x0;
    x1

def «$4c69746572616c732f4f4c6974732e7461696c» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      x0
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      (fun (_ : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
        x2)

def «$4c69746572616c732f4c6974732e73696e676c65» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      ([] : _root_.List _root_.Geb.Kernel.Tree));
    x1

def «$4c69746572616c732f4c6974732e6c656e677468» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (_ : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.add x2 (_root_.Geb.Kernel.leaf 1))
      (_root_.Geb.Kernel.leaf 0)
      x0;
    x1

def «$4c69746572616c732f4c6974732e617070656e64» :=
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

def «$4c69746572616c732f4c6974732e72657665727365» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree →
           _root_.List _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        x2 (x1 :: x3))
      (fun (x1 : _root_.List _root_.Geb.Kernel.Tree) => x1)
      x0
      ([] : _root_.List _root_.Geb.Kernel.Tree);
    x1

def «$4c69746572616c732f4c6974732e7461696c» :=
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

def «$4c69746572616c732f4c6974732e64726f70» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.iter
      (α := _root_.List _root_.Geb.Kernel.Tree)
      _root_.GebMirror.Metalogic.«$4c69746572616c732f4c6974732e7461696c»
      x1
      x0;
    x2

def «$4c69746572616c732f4c6974732e61744f72» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«$4c69746572616c732f4c6974732e64726f70» x2 x1)
      x0
      (fun (x3 : _root_.Geb.Kernel.Tree)
         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        x3);
    x3

def «$4c69746572616c732f456163684c69742e616c6c» :=
  fun (x0 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree) (x3 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Prelude.and» (x0 x2) x3)
      (_root_.Geb.Kernel.leaf 1)
      x1;
    x2

def «$4c69746572616c732f456163684c69742e616e79» :=
  fun (x0 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree) (x3 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Prelude.or» (x0 x2) x3)
      (_root_.Geb.Kernel.leaf 0)
      x1;
    x2

def «$4c69746572616c732f456163684c69742e6973456d707479» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.eq
      (_root_.Geb.Kernel.Const.foldr
        (α := _root_.Geb.Kernel.Tree)
        (β := _root_.Geb.Kernel.Tree)
        (fun (_ : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
          _root_.Geb.Kernel.Const.add x2 (_root_.Geb.Kernel.leaf 1))
        (_root_.Geb.Kernel.leaf 0)
        x0)
      (_root_.Geb.Kernel.leaf 0);
    x1

def «$4c69746572616c732f456163684c69742e74616b65» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := (let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x3 : _root_.Geb.Kernel.Tree) =>
                                     _root_.Geb.Kernel.Const.add x3 (_root_.Geb.Kernel.leaf 1))
                                   (_root_.Geb.Kernel.leaf 0)
                                   x1;
                                 (_root_.Geb.Kernel.Const.foldr
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree ×
                                     _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (x3 : _root_.Geb.Kernel.Tree)
                                      (x4 : _root_.Geb.Kernel.Tree ×
                                        _root_.List _root_.Geb.Kernel.Tree) =>
                                     (_root_.Geb.Kernel.Const.add (x4).1 (_root_.Geb.Kernel.leaf 1),
                                       if (_root_.Geb.Kernel.Const.lt
                                         (_root_.Geb.Kernel.Const.sub
                                           (_root_.Geb.Kernel.Const.sub x2 (x4).1)
                                           (_root_.Geb.Kernel.leaf 1))
                                         x0).label ≠ 0 then
                                         (x3 :: (x4).2)
                                       else
                                         (x4).2))
                                   (_root_.Geb.Kernel.leaf 0,
                                     ([] : _root_.List _root_.Geb.Kernel.Tree))
                                   x1).2);
    x2

def «Literals.pairTy» :=
  _root_.GebMirror.Metalogic.«Theory.prod»
    _root_.GebMirror.Metalogic.«Translation.bitsTy»
    _root_.GebMirror.Metalogic.«Translation.bitsTy»

def «Literals.b1c» :=
  _root_.GebMirror.Metalogic.«Prelude.single» _root_.GebMirror.Metalogic.«Translation.bitsTy»

def «Literals.b2c» :=
  _root_.GebMirror.Metalogic.«Theory.l2»
    _root_.GebMirror.Metalogic.«Translation.bitsTy»
    _root_.GebMirror.Metalogic.«Translation.bitsTy»

def «Literals.b3c» :=
  _root_.GebMirror.Metalogic.«Theory.l3»
    _root_.GebMirror.Metalogic.«Translation.bitsTy»
    _root_.GebMirror.Metalogic.«Translation.bitsTy»
    _root_.GebMirror.Metalogic.«Translation.bitsTy»

def «Literals.symRow» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (_root_.GebMirror.Metalogic.«Theory.l4»
        x0
        (_root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 0) x1)
        (_root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 0) x2)
        x3);
    x4

def «Literals.syms» :=
  _root_.GebMirror.Metalogic.«Prelude.append»
    (_root_.GebMirror.Metalogic.«Theory.l6»
      (_root_.GebMirror.Metalogic.«Literals.symRow»
        (_root_.Geb.Kernel.leaf 0)
        ([] : _root_.List _root_.Geb.Kernel.Tree)
        ([] : _root_.List _root_.Geb.Kernel.Tree)
        _root_.GebMirror.Metalogic.«Translation.bitsTy»)
      (_root_.GebMirror.Metalogic.«Literals.symRow»
        (_root_.Geb.Kernel.leaf 1)
        ([] : _root_.List _root_.Geb.Kernel.Tree)
        _root_.GebMirror.Metalogic.«Literals.b1c»
        _root_.GebMirror.Metalogic.«Translation.bitsTy»)
      (_root_.GebMirror.Metalogic.«Literals.symRow»
        (_root_.Geb.Kernel.leaf 2)
        ([] : _root_.List _root_.Geb.Kernel.Tree)
        _root_.GebMirror.Metalogic.«Literals.b1c»
        _root_.GebMirror.Metalogic.«Translation.bitsTy»)
      (_root_.GebMirror.Metalogic.«Literals.symRow»
        (_root_.Geb.Kernel.leaf 10)
        (_root_.GebMirror.Metalogic.«Prelude.single» _root_.GebMirror.Metalogic.«Translation.bitTy»)
        _root_.GebMirror.Metalogic.«Literals.b1c»
        _root_.GebMirror.Metalogic.«Translation.bitsTy»)
      (_root_.GebMirror.Metalogic.«Literals.symRow»
        (_root_.Geb.Kernel.leaf 11)
        ([] : _root_.List _root_.Geb.Kernel.Tree)
        _root_.GebMirror.Metalogic.«Literals.b1c»
        _root_.GebMirror.Metalogic.«Translation.bitsTy»)
      (_root_.GebMirror.Metalogic.«Literals.symRow»
        (_root_.Geb.Kernel.leaf 14)
        ([] : _root_.List _root_.Geb.Kernel.Tree)
        _root_.GebMirror.Metalogic.«Literals.b1c»
        _root_.GebMirror.Metalogic.«Translation.bitsTy»))
    (_root_.GebMirror.Metalogic.«Prelude.append»
      (_root_.GebMirror.Metalogic.«Theory.l6»
        (_root_.GebMirror.Metalogic.«Literals.symRow»
          (_root_.Geb.Kernel.leaf 13)
          ([] : _root_.List _root_.Geb.Kernel.Tree)
          _root_.GebMirror.Metalogic.«Literals.b1c»
          _root_.GebMirror.Metalogic.«Translation.bitsTy»)
        (_root_.GebMirror.Metalogic.«Literals.symRow»
          (_root_.Geb.Kernel.leaf 6)
          _root_.GebMirror.Metalogic.«Literals.b1c»
          _root_.GebMirror.Metalogic.«Literals.b3c»
          _root_.GebMirror.Metalogic.«Translation.bitsTy»)
        (_root_.GebMirror.Metalogic.«Literals.symRow»
          (_root_.Geb.Kernel.leaf 6)
          (_root_.GebMirror.Metalogic.«Prelude.single» _root_.GebMirror.Metalogic.«Translation.ordTy»)
          (_root_.GebMirror.Metalogic.«Theory.l3»
            _root_.GebMirror.Metalogic.«Translation.ordTy»
            _root_.GebMirror.Metalogic.«Translation.ordTy»
            _root_.GebMirror.Metalogic.«Translation.bitsTy»)
          _root_.GebMirror.Metalogic.«Translation.ordTy»)
        (_root_.GebMirror.Metalogic.«Literals.symRow»
          (_root_.Geb.Kernel.leaf 15)
          ([] : _root_.List _root_.Geb.Kernel.Tree)
          _root_.GebMirror.Metalogic.«Literals.b2c»
          _root_.GebMirror.Metalogic.«Translation.bitsTy»)
        (_root_.GebMirror.Metalogic.«Literals.symRow»
          (_root_.Geb.Kernel.leaf 21)
          ([] : _root_.List _root_.Geb.Kernel.Tree)
          _root_.GebMirror.Metalogic.«Literals.b2c»
          _root_.GebMirror.Metalogic.«Translation.bitsTy»)
        (_root_.GebMirror.Metalogic.«Literals.symRow»
          (_root_.Geb.Kernel.leaf 18)
          ([] : _root_.List _root_.Geb.Kernel.Tree)
          _root_.GebMirror.Metalogic.«Literals.b2c»
          _root_.GebMirror.Metalogic.«Translation.bitsTy»))
      (_root_.GebMirror.Metalogic.«Theory.l6»
        (_root_.GebMirror.Metalogic.«Literals.symRow»
          (_root_.Geb.Kernel.leaf 16)
          ([] : _root_.List _root_.Geb.Kernel.Tree)
          _root_.GebMirror.Metalogic.«Literals.b2c»
          _root_.GebMirror.Metalogic.«Translation.ordTy»)
        (_root_.GebMirror.Metalogic.«Literals.symRow»
          (_root_.Geb.Kernel.leaf 17)
          ([] : _root_.List _root_.Geb.Kernel.Tree)
          _root_.GebMirror.Metalogic.«Literals.b2c»
          _root_.GebMirror.Metalogic.«Translation.bitsTy»)
        (_root_.GebMirror.Metalogic.«Literals.symRow»
          (_root_.Geb.Kernel.leaf 19)
          ([] : _root_.List _root_.Geb.Kernel.Tree)
          _root_.GebMirror.Metalogic.«Literals.b2c»
          _root_.GebMirror.Metalogic.«Translation.bitsTy»)
        (_root_.GebMirror.Metalogic.«Literals.symRow»
          (_root_.Geb.Kernel.leaf 20)
          ([] : _root_.List _root_.Geb.Kernel.Tree)
          _root_.GebMirror.Metalogic.«Literals.b2c»
          _root_.GebMirror.Metalogic.«Translation.bitsTy»)
        (_root_.GebMirror.Metalogic.«Literals.symRow»
          (_root_.Geb.Kernel.leaf 22)
          ([] : _root_.List _root_.Geb.Kernel.Tree)
          _root_.GebMirror.Metalogic.«Literals.b2c»
          _root_.GebMirror.Metalogic.«Literals.pairTy»)
        (_root_.GebMirror.Metalogic.«Literals.symRow»
          (_root_.Geb.Kernel.leaf 23)
          ([] : _root_.List _root_.Geb.Kernel.Tree)
          _root_.GebMirror.Metalogic.«Literals.b1c»
          _root_.GebMirror.Metalogic.«Translation.bitsTy»)))

def «Literals.symOf» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (if (_root_.Geb.Kernel.Const.eq
      (_root_.Geb.Kernel.Const.label x0)
      (_root_.Geb.Kernel.leaf 11)).label ≠ 0 then
      let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mD»
        x0
        (_root_.Geb.Kernel.leaf 0);
      let x2 : _root_.List
        _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
        (_root_.GebMirror.Metalogic.«Language.mD» x0 (_root_.Geb.Kernel.leaf 1));
      _root_.Geb.Kernel.Const.foldr
        (α := _root_.Geb.Kernel.Tree)
        (β := _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
        (fun (x3 : _root_.Geb.Kernel.Tree)
           (x4 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
           (x5 : _root_.Geb.Kernel.Tree) =>
          if (_root_.GebMirror.Metalogic.«Prelude.and»
            (_root_.Geb.Kernel.Const.eq
              (_root_.Geb.Kernel.Const.child x3 (_root_.Geb.Kernel.leaf 0))
              x1)
            (_root_.GebMirror.Metalogic.«Base.equalTs»
              (_root_.Geb.Kernel.Const.children
                (_root_.Geb.Kernel.Const.child x3 (_root_.Geb.Kernel.leaf 1)))
              x2)).label ≠ 0 then
            _root_.GebMirror.Metalogic.«Prelude.some» x5
          else
            x4 (_root_.Geb.Kernel.Const.add x5 (_root_.Geb.Kernel.leaf 1)))
        (fun (_ : _root_.Geb.Kernel.Tree) => _root_.GebMirror.Metalogic.«Prelude.none»)
        _root_.GebMirror.Metalogic.«Literals.syms»
        (_root_.Geb.Kernel.leaf 0)
    else
      _root_.GebMirror.Metalogic.«Prelude.none»);
    x1

def «Literals.bits1» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      x0
      _root_.GebMirror.Metalogic.«Prelude.none»
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
        if (_root_.GebMirror.Metalogic.«$4c69746572616c732f456163684c69742e6973456d707479»
          x2).label ≠ 0 then
          let x3 : _root_.Geb.Kernel.Tree := x1;
          if (_root_.Geb.Kernel.Const.eq
            (_root_.Geb.Kernel.Const.label x3)
            (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
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
            let _ : _root_.List
              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
              (α := _root_.Geb.Kernel.Tree)
              (β := _root_.List _root_.Geb.Kernel.Tree)
              x4
              ([] : _root_.List _root_.Geb.Kernel.Tree)
              (fun (_ : _root_.Geb.Kernel.Tree)
                 (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
                x7);
            _root_.GebMirror.Metalogic.«Prelude.some» x5
          else
            _root_.GebMirror.Metalogic.«Prelude.none»
        else
          _root_.GebMirror.Metalogic.«Prelude.none»);
    x1

def «Literals.bits2» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      x0
      _root_.GebMirror.Metalogic.«$4c616e67756167652f4f54506169722e6e6f7468696e67»
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
        let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Literals.bits1» x2;
        if (_root_.GebMirror.Metalogic.«Prelude.isSome» x3).label ≠ 0 then
          let x4 : _root_.Geb.Kernel.Tree := x1;
          if (_root_.Geb.Kernel.Const.eq
            (_root_.Geb.Kernel.Const.label x4)
            (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
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
            let _ : _root_.List
              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
              (α := _root_.Geb.Kernel.Tree)
              (β := _root_.List _root_.Geb.Kernel.Tree)
              x5
              ([] : _root_.List _root_.Geb.Kernel.Tree)
              (fun (_ : _root_.Geb.Kernel.Tree)
                 (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                x8);
            _root_.GebMirror.Metalogic.«$4c616e67756167652f4f54506169722e6a757374»
              (_root_.GebMirror.Metalogic.«Language.pr» x6 (_root_.GebMirror.Metalogic.«Prelude.get» x3))
          else
            _root_.GebMirror.Metalogic.«$4c616e67756167652f4f54506169722e6e6f7468696e67»
        else
          _root_.GebMirror.Metalogic.«$4c616e67756167652f4f54506169722e6e6f7468696e67»);
    x1

def «Literals.truth» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (if (x0).label ≠ 0 then
      _root_.Geb.Kernel.leaf 1
    else
      _root_.Geb.Kernel.leaf 0);
    x1

def «Literals.hostCond» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      x1
      _root_.GebMirror.Metalogic.«$4c69746572616c732f4f4c69742e6e6f7468696e67»
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.lcase
          (α := _root_.Geb.Kernel.Tree)
          (β := _root_.Geb.Kernel.Tree)
          x3
          _root_.GebMirror.Metalogic.«$4c69746572616c732f4f4c69742e6e6f7468696e67»
          (fun (x4 : _root_.Geb.Kernel.Tree)
             (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
            _root_.Geb.Kernel.Const.lcase
              (α := _root_.Geb.Kernel.Tree)
              (β := _root_.Geb.Kernel.Tree)
              x5
              _root_.GebMirror.Metalogic.«$4c69746572616c732f4f4c69742e6e6f7468696e67»
              (fun (x6 : _root_.Geb.Kernel.Tree)
                 (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
                if (_root_.GebMirror.Metalogic.«$4c69746572616c732f456163684c69742e6973456d707479»
                  x7).label ≠ 0 then
                  let x8 : _root_.Geb.Kernel.Tree := x2;
                  if (_root_.Geb.Kernel.Const.eq
                    (_root_.Geb.Kernel.Const.label x8)
                    (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                    let x9 : _root_.List
                      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x8;
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
                    let x12 : _root_.Geb.Kernel.Tree := x4;
                    if (_root_.Geb.Kernel.Const.eq
                      (_root_.Geb.Kernel.Const.label x12)
                      (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                      let x13 : _root_.List
                        _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x12;
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
                      let x16 : _root_.Geb.Kernel.Tree := x6;
                      if (_root_.Geb.Kernel.Const.eq
                        (_root_.Geb.Kernel.Const.label x16)
                        (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                        let x17 : _root_.List
                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x16;
                        let x18 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                          (α := _root_.Geb.Kernel.Tree)
                          (β := _root_.Geb.Kernel.Tree)
                          x17
                          (_root_.Geb.Kernel.leaf 0)
                          (fun (x18 : _root_.Geb.Kernel.Tree)
                             (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                            x18);
                        let _ : _root_.List
                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                          (α := _root_.Geb.Kernel.Tree)
                          (β := _root_.List _root_.Geb.Kernel.Tree)
                          x17
                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                          (fun (_ : _root_.Geb.Kernel.Tree)
                             (x20 : _root_.List _root_.Geb.Kernel.Tree) =>
                            x20);
                        if (_root_.Geb.Kernel.Const.eq
                          x0
                          (_root_.Geb.Kernel.leaf 7)).label ≠ 0 then
                          _root_.GebMirror.Metalogic.«$4c69746572616c732f4f4c69742e6a757374»
                            (_root_.GebMirror.Metalogic.«Literals.litBits»
                              (if (_root_.Geb.Kernel.Const.eq
                                x10
                                (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                                x18
                              else
                                x14))
                        else
                          _root_.GebMirror.Metalogic.«$4c69746572616c732f4f4c69742e6e6f7468696e67»
                      else
                        _root_.GebMirror.Metalogic.«$4c69746572616c732f4f4c69742e6e6f7468696e67»
                    else
                      if (_root_.Geb.Kernel.Const.eq
                        (_root_.Geb.Kernel.Const.label x12)
                        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                        let x13 : _root_.List
                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x12;
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
                        let x16 : _root_.Geb.Kernel.Tree := x6;
                        if (_root_.Geb.Kernel.Const.eq
                          (_root_.Geb.Kernel.Const.label x16)
                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                          let x17 : _root_.List
                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x16;
                          let x18 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                            (α := _root_.Geb.Kernel.Tree)
                            (β := _root_.Geb.Kernel.Tree)
                            x17
                            (_root_.Geb.Kernel.leaf 0)
                            (fun (x18 : _root_.Geb.Kernel.Tree)
                               (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                              x18);
                          let _ : _root_.List
                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                            (α := _root_.Geb.Kernel.Tree)
                            (β := _root_.List _root_.Geb.Kernel.Tree)
                            x17
                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                            (fun (_ : _root_.Geb.Kernel.Tree)
                               (x20 : _root_.List _root_.Geb.Kernel.Tree) =>
                              x20);
                          if (_root_.Geb.Kernel.Const.eq
                            x0
                            (_root_.Geb.Kernel.leaf 8)).label ≠ 0 then
                            _root_.GebMirror.Metalogic.«$4c69746572616c732f4f4c69742e6a757374»
                              (_root_.GebMirror.Metalogic.«Literals.litOrd»
                                (if (_root_.Geb.Kernel.Const.eq
                                  x10
                                  (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                                  x18
                                else
                                  x14))
                          else
                            _root_.GebMirror.Metalogic.«$4c69746572616c732f4f4c69742e6e6f7468696e67»
                        else
                          _root_.GebMirror.Metalogic.«$4c69746572616c732f4f4c69742e6e6f7468696e67»
                      else
                        _root_.GebMirror.Metalogic.«$4c69746572616c732f4f4c69742e6e6f7468696e67»
                  else
                    _root_.GebMirror.Metalogic.«$4c69746572616c732f4f4c69742e6e6f7468696e67»
                else
                  _root_.GebMirror.Metalogic.«$4c69746572616c732f4f4c69742e6e6f7468696e67»)));
    x2

def «Literals.host» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (if (_root_.Geb.Kernel.Const.eq
      x0
      (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
      if (_root_.GebMirror.Metalogic.«$4c69746572616c732f456163684c69742e6973456d707479»
        x1).label ≠ 0 then
        _root_.GebMirror.Metalogic.«$4c69746572616c732f4f4c69742e6a757374»
          (_root_.GebMirror.Metalogic.«Literals.litBits» (_root_.Geb.Kernel.leaf 0))
      else
        _root_.GebMirror.Metalogic.«$4c69746572616c732f4f4c69742e6e6f7468696e67»
    else
      if (_root_.GebMirror.Metalogic.«Prelude.or»
        (_root_.Geb.Kernel.Const.eq x0 (_root_.Geb.Kernel.leaf 7))
        (_root_.Geb.Kernel.Const.eq
          x0
          (_root_.Geb.Kernel.leaf 8))).label ≠ 0 then
        _root_.GebMirror.Metalogic.«Literals.hostCond» x0 x1
      else
        if (_root_.GebMirror.Metalogic.«Prelude.or»
          (_root_.Geb.Kernel.Const.lt x0 (_root_.Geb.Kernel.leaf 7))
          (_root_.Geb.Kernel.Const.eq
            x0
            (_root_.Geb.Kernel.leaf 17))).label ≠ 0 then
          let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Literals.bits1» x1;
          if (_root_.GebMirror.Metalogic.«Prelude.isSome» x2).label ≠ 0 then
            let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.get» x2;
            _root_.GebMirror.Metalogic.«$4c69746572616c732f4f4c69742e6a757374»
              (_root_.GebMirror.Metalogic.«Literals.litBits»
                (if (_root_.Geb.Kernel.Const.eq
                  x0
                  (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                  _root_.Geb.Kernel.Const.add
                    (_root_.Geb.Kernel.Const.mul (_root_.Geb.Kernel.leaf 2) x3)
                    (_root_.Geb.Kernel.leaf 1)
                else
                  if (_root_.Geb.Kernel.Const.eq
                    x0
                    (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
                    _root_.Geb.Kernel.Const.add
                      (_root_.Geb.Kernel.Const.mul (_root_.Geb.Kernel.leaf 2) x3)
                      (_root_.Geb.Kernel.leaf 2)
                  else
                    if (_root_.Geb.Kernel.Const.eq
                      x0
                      (_root_.Geb.Kernel.leaf 3)).label ≠ 0 then
                      _root_.GebMirror.Metalogic.«Literals.truth»
                        (_root_.Geb.Kernel.Const.eq x3 (_root_.Geb.Kernel.leaf 0))
                    else
                      if (_root_.Geb.Kernel.Const.eq
                        x0
                        (_root_.Geb.Kernel.leaf 4)).label ≠ 0 then
                        _root_.Geb.Kernel.Const.add x3 (_root_.Geb.Kernel.leaf 1)
                      else
                        if (_root_.Geb.Kernel.Const.eq
                          x0
                          (_root_.Geb.Kernel.leaf 5)).label ≠ 0 then
                          _root_.Geb.Kernel.Const.mul (_root_.Geb.Kernel.leaf 2) x3
                        else
                          if (_root_.Geb.Kernel.Const.eq
                            x0
                            (_root_.Geb.Kernel.leaf 6)).label ≠ 0 then
                            _root_.Geb.Kernel.Const.sub x3 (_root_.Geb.Kernel.leaf 1)
                          else
                            _root_.Geb.Kernel.Const.log2 x3))
          else
            _root_.GebMirror.Metalogic.«$4c69746572616c732f4f4c69742e6e6f7468696e67»
        else
          let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Literals.bits2» x1;
          if (_root_.Geb.Kernel.Const.eq
            (_root_.Geb.Kernel.Const.label x2)
            (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
            let x3 : _root_.List
              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x2;
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
            let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.p1» x4;
            let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.p2» x4;
            if (_root_.Geb.Kernel.Const.eq
              x0
              (_root_.Geb.Kernel.leaf 9)).label ≠ 0 then
              _root_.GebMirror.Metalogic.«$4c69746572616c732f4f4c69742e6a757374»
                (_root_.GebMirror.Metalogic.«Literals.litBits»
                  (_root_.Geb.Kernel.Const.add x6 x7))
            else
              if (_root_.Geb.Kernel.Const.eq
                x0
                (_root_.Geb.Kernel.leaf 10)).label ≠ 0 then
                _root_.GebMirror.Metalogic.«$4c69746572616c732f4f4c69742e6a757374»
                  (_root_.GebMirror.Metalogic.«Literals.litBits»
                    (_root_.Geb.Kernel.Const.mul x6 x7))
              else
                if (_root_.Geb.Kernel.Const.eq
                  x0
                  (_root_.Geb.Kernel.leaf 11)).label ≠ 0 then
                  _root_.GebMirror.Metalogic.«$4c69746572616c732f4f4c69742e6a757374»
                    (_root_.GebMirror.Metalogic.«Literals.litBits»
                      (_root_.GebMirror.Metalogic.«Literals.truth» (_root_.Geb.Kernel.Const.eq x6 x7)))
                else
                  if (_root_.Geb.Kernel.Const.eq
                    x0
                    (_root_.Geb.Kernel.leaf 12)).label ≠ 0 then
                    _root_.GebMirror.Metalogic.«$4c69746572616c732f4f4c69742e6a757374»
                      (_root_.GebMirror.Metalogic.«Literals.litOrd»
                        (if (_root_.Geb.Kernel.Const.lt x6 x7).label ≠ 0 then
                          _root_.Geb.Kernel.leaf 0
                        else
                          if (_root_.Geb.Kernel.Const.eq x6 x7).label ≠ 0 then
                            _root_.Geb.Kernel.leaf 1
                          else
                            _root_.Geb.Kernel.leaf 2))
                  else
                    if (_root_.Geb.Kernel.Const.eq
                      x0
                      (_root_.Geb.Kernel.leaf 13)).label ≠ 0 then
                      _root_.GebMirror.Metalogic.«$4c69746572616c732f4f4c69742e6a757374»
                        (_root_.GebMirror.Metalogic.«Literals.litBits»
                          (_root_.GebMirror.Metalogic.«Literals.truth» (_root_.Geb.Kernel.Const.lt x6 x7)))
                    else
                      if (_root_.Geb.Kernel.Const.eq
                        x0
                        (_root_.Geb.Kernel.leaf 14)).label ≠ 0 then
                        if (_root_.Geb.Kernel.Const.lt x6 x7).label ≠ 0 then
                          _root_.GebMirror.Metalogic.«$4c69746572616c732f4f4c69742e6e6f7468696e67»
                        else
                          _root_.GebMirror.Metalogic.«$4c69746572616c732f4f4c69742e6a757374»
                            (_root_.GebMirror.Metalogic.«Literals.litBits»
                              (_root_.Geb.Kernel.Const.sub x6 x7))
                      else
                        if (_root_.Geb.Kernel.Const.eq
                          x0
                          (_root_.Geb.Kernel.leaf 15)).label ≠ 0 then
                          _root_.GebMirror.Metalogic.«$4c69746572616c732f4f4c69742e6a757374»
                            (_root_.GebMirror.Metalogic.«Literals.litBits»
                              (_root_.Geb.Kernel.Const.sub x6 x7))
                        else
                          if (_root_.Geb.Kernel.Const.eq
                            x0
                            (_root_.Geb.Kernel.leaf 16)).label ≠ 0 then
                            _root_.GebMirror.Metalogic.«$4c69746572616c732f4f4c69742e6a757374»
                              (_root_.GebMirror.Metalogic.«Literals.litPair»
                                (_root_.Geb.Kernel.Const.div x6 x7)
                                (_root_.Geb.Kernel.Const.mod x6 x7))
                          else
                            _root_.GebMirror.Metalogic.«$4c69746572616c732f4f4c69742e6e6f7468696e67»
          else
            let _ : _root_.List
              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x2;
            _root_.GebMirror.Metalogic.«$4c69746572616c732f4f4c69742e6e6f7468696e67»);
    x2

def «Literals.pairStep» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (if (_root_.Geb.Kernel.Const.eq
      x0
      (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
      let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Literals.bits2» x1;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x2)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
        let x3 : _root_.List
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x2;
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
        _root_.GebMirror.Metalogic.«$4c69746572616c732f4f4c69742e6a757374»
          (_root_.GebMirror.Metalogic.«Literals.litPair»
            (_root_.GebMirror.Metalogic.«Language.p1» x4)
            (_root_.GebMirror.Metalogic.«Language.p2» x4))
      else
        let _ : _root_.List
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x2;
        _root_.GebMirror.Metalogic.«$4c69746572616c732f4f4c69742e6e6f7468696e67»
    else
      _root_.Geb.Kernel.Const.lcase
        (α := _root_.Geb.Kernel.Tree)
        (β := _root_.Geb.Kernel.Tree)
        x1
        _root_.GebMirror.Metalogic.«$4c69746572616c732f4f4c69742e6e6f7468696e67»
        (fun (x2 : _root_.Geb.Kernel.Tree)
           (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
          if (_root_.GebMirror.Metalogic.«$4c69746572616c732f456163684c69742e6973456d707479»
            x3).label ≠ 0 then
            let x4 : _root_.Geb.Kernel.Tree := x2;
            if (_root_.Geb.Kernel.Const.eq
              (_root_.Geb.Kernel.Const.label x4)
              (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
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
              if (_root_.Geb.Kernel.Const.eq
                x0
                (_root_.Geb.Kernel.leaf 3)).label ≠ 0 then
                _root_.GebMirror.Metalogic.«$4c69746572616c732f4f4c69742e6a757374»
                  (_root_.GebMirror.Metalogic.«Literals.litBits» x6)
              else
                if (_root_.Geb.Kernel.Const.eq
                  x0
                  (_root_.Geb.Kernel.leaf 4)).label ≠ 0 then
                  _root_.GebMirror.Metalogic.«$4c69746572616c732f4f4c69742e6a757374»
                    (_root_.GebMirror.Metalogic.«Literals.litBits» x8)
                else
                  _root_.GebMirror.Metalogic.«$4c69746572616c732f4f4c69742e6e6f7468696e67»
            else
              _root_.GebMirror.Metalogic.«$4c69746572616c732f4f4c69742e6e6f7468696e67»
          else
            _root_.GebMirror.Metalogic.«$4c69746572616c732f4f4c69742e6e6f7468696e67»));
    x2

def «Literals.evalStep» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (if (_root_.Geb.Kernel.Const.equal
      x0
      _root_.GebMirror.Metalogic.«Translation.ltO»).label ≠ 0 then
      _root_.GebMirror.Metalogic.«$4c69746572616c732f4f4c69742e6a757374»
        (_root_.GebMirror.Metalogic.«Literals.litOrd» (_root_.Geb.Kernel.leaf 0))
    else
      if (_root_.Geb.Kernel.Const.equal
        x0
        _root_.GebMirror.Metalogic.«Translation.eqO»).label ≠ 0 then
        _root_.GebMirror.Metalogic.«$4c69746572616c732f4f4c69742e6a757374»
          (_root_.GebMirror.Metalogic.«Literals.litOrd» (_root_.Geb.Kernel.leaf 1))
      else
        if (_root_.Geb.Kernel.Const.equal
          x0
          _root_.GebMirror.Metalogic.«Translation.gtO»).label ≠ 0 then
          _root_.GebMirror.Metalogic.«$4c69746572616c732f4f4c69742e6a757374»
            (_root_.GebMirror.Metalogic.«Literals.litOrd» (_root_.Geb.Kernel.leaf 2))
        else
          let x2 : _root_.Geb.Kernel.Tree ×
            _root_.List
              _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$4c69746572616c732f4f4c69742e616c6c4a757374»
            (_root_.GebMirror.Metalogic.«$4c69746572616c732f4f4c6974732e7461696c» x1);
          if ((x2).1).label ≠ 0 then
            let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Literals.symOf» x0;
            if (_root_.GebMirror.Metalogic.«Prelude.isSome» x3).label ≠ 0 then
              _root_.GebMirror.Metalogic.«Literals.host»
                (_root_.GebMirror.Metalogic.«Prelude.get» x3)
                (_root_.GebMirror.Metalogic.«$4c69746572616c732f4c6974732e72657665727365» (x2).2)
            else
              _root_.GebMirror.Metalogic.«Literals.pairStep»
                (_root_.Geb.Kernel.Const.label x0)
                (x2).2
          else
            _root_.GebMirror.Metalogic.«$4c69746572616c732f4f4c69742e6e6f7468696e67»);
    x2

def «Literals.valueOf» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.para
      (α := _root_.Geb.Kernel.Tree)
      _root_.GebMirror.Metalogic.«Literals.evalStep»
      x0;
    x1

def «Literals.litTerm» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
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
                                          _root_.GebMirror.Metalogic.«Translation.trNumeral» x3
                                        else
                                          if (_root_.Geb.Kernel.Const.eq
                                            (_root_.Geb.Kernel.Const.label x1)
                                            (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
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
                                            if (_root_.Geb.Kernel.Const.eq
                                              x3
                                              (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                                              _root_.GebMirror.Metalogic.«Translation.ltO»
                                            else
                                              if (_root_.Geb.Kernel.Const.eq
                                                x3
                                                (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                                _root_.GebMirror.Metalogic.«Translation.eqO»
                                              else
                                                _root_.GebMirror.Metalogic.«Translation.gtO»
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
                                            _root_.GebMirror.Metalogic.«Language.mPair»
                                              (_root_.GebMirror.Metalogic.«Translation.trNumeral» x3)
                                              (_root_.GebMirror.Metalogic.«Translation.trNumeral» x5));
    x1

def «Literals.litEval» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Literals.valueOf»
                                          x0;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x1)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
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
                                          _root_.GebMirror.Metalogic.«Prelude.some»
                                            (_root_.GebMirror.Metalogic.«Literals.litTerm» x3)
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x1;
                                          _root_.GebMirror.Metalogic.«Prelude.none»);
    x1

def «$4c69746572616c732f54686d462e6c32» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)));
    x2

def «$4c69746572616c732f54686d462e6c33» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      (_root_.GebMirror.Metalogic.«$4c69746572616c732f54686d462e6c32» x1 x2));
    x3

def «$4c69746572616c732f54686d462e6c34» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      (_root_.GebMirror.Metalogic.«$4c69746572616c732f54686d462e6c33» x1 x2 x3));
    x4

def «$4c69746572616c732f54686d462e6c35» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      (_root_.GebMirror.Metalogic.«$4c69746572616c732f54686d462e6c34» x1 x2 x3 x4));
    x5

def «$4c69746572616c732f54686d462e6c36» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree) =>
    let x6 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      (_root_.GebMirror.Metalogic.«$4c69746572616c732f54686d462e6c35» x1 x2 x3 x4 x5));
    x6

def «$4c69746572616c732f54686d732e73696e676c65» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      ([] : _root_.List _root_.Geb.Kernel.Tree));
    x1

def «$4c69746572616c732f54686d732e6c656e677468» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (_ : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.add x2 (_root_.Geb.Kernel.leaf 1))
      (_root_.Geb.Kernel.leaf 0)
      x0;
    x1

def «$4c69746572616c732f54686d732e617070656e64» :=
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

def «$4c69746572616c732f54686d732e72657665727365» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree →
           _root_.List _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        x2 (x1 :: x3))
      (fun (x1 : _root_.List _root_.Geb.Kernel.Tree) => x1)
      x0
      ([] : _root_.List _root_.Geb.Kernel.Tree);
    x1

def «$4c69746572616c732f54686d732e7461696c» :=
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

def «$4c69746572616c732f54686d732e64726f70» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.iter
      (α := _root_.List _root_.Geb.Kernel.Tree)
      _root_.GebMirror.Metalogic.«$4c69746572616c732f54686d732e7461696c»
      x1
      x0;
    x2

def «$4c69746572616c732f54686d732e61744f72» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«$4c69746572616c732f54686d732e64726f70» x2 x1)
      x0
      (fun (x3 : _root_.Geb.Kernel.Tree)
         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        x3);
    x3

def «Literals.lemEqn» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Derivation.mkThm»
      (_root_.Geb.Kernel.leaf 0)
      (_root_.GebMirror.Metalogic.«Language.objs» x0)
      (_root_.GebMirror.Metalogic.«Derivation.terms»
        ([] : _root_.List _root_.Geb.Kernel.Tree))
      (_root_.GebMirror.Metalogic.«Language.mEq» x1 x2);
    x3

def «Literals.vy» :=
  _root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)

def «Literals.vx» :=
  _root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1)

def «Literals.vz» :=
  _root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 2)

def «Literals.isNilT» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Translation.call»
      (_root_.Geb.Kernel.leaf 10)
      (_root_.GebMirror.Metalogic.«Prelude.single» _root_.GebMirror.Metalogic.«Translation.bitTy»)
      (_root_.GebMirror.Metalogic.«Prelude.single» x0);
    x1

def «Literals.un» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Translation.call»
      x0
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«Prelude.single» x1);
    x2

def «Literals.bin» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Translation.call»
      x0
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«Theory.l2» x1 x2);
    x3

def «Literals.condB» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Translation.call»
      (_root_.Geb.Kernel.leaf 6)
      (_root_.GebMirror.Metalogic.«Prelude.single» _root_.GebMirror.Metalogic.«Translation.bitsTy»)
      (_root_.GebMirror.Metalogic.«Theory.l3» x0 x1 x2);
    x3

def «Literals.condO» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Translation.call»
      (_root_.Geb.Kernel.leaf 6)
      (_root_.GebMirror.Metalogic.«Prelude.single» _root_.GebMirror.Metalogic.«Translation.ordTy»)
      (_root_.GebMirror.Metalogic.«Theory.l3» x0 x1 x2);
    x3

def «Literals.selIn» :=
  _root_.GebMirror.Metalogic.«Translation.ifOrd»
    _root_.GebMirror.Metalogic.«Literals.pairTy»
    (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 3))
    _root_.GebMirror.Metalogic.«Literals.vz»
    _root_.GebMirror.Metalogic.«Literals.vx»
    _root_.GebMirror.Metalogic.«Literals.vy»

def «Literals.selSel» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Translation.ifOrd»
      _root_.GebMirror.Metalogic.«Literals.pairTy»
      x0
      (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 5))
      (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 4))
      _root_.GebMirror.Metalogic.«Literals.selIn»;
    x1

def «Literals.divStep» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.subst»
      (_root_.GebMirror.Metalogic.«Literals.selSel»
        (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 6)))
      (_root_.GebMirror.Metalogic.«Language.substList»
        ((_root_.GebMirror.Metalogic.«Language.mPair»
          (_root_.GebMirror.Metalogic.«Translation.b1T» x0)
          _root_.GebMirror.Metalogic.«Translation.bnilT») ::
          (_root_.GebMirror.Metalogic.«Theory.l6»
            (_root_.GebMirror.Metalogic.«Language.mPair»
              (_root_.GebMirror.Metalogic.«Translation.b1T» x0)
              _root_.GebMirror.Metalogic.«Translation.bnilT»)
            (_root_.GebMirror.Metalogic.«Language.mPair»
              (_root_.GebMirror.Metalogic.«Translation.b0T» x0)
              (_root_.GebMirror.Metalogic.«Literals.bin» (_root_.Geb.Kernel.leaf 19) x1 x2))
            (_root_.GebMirror.Metalogic.«Literals.bin»
              (_root_.Geb.Kernel.leaf 16)
              x1
              (_root_.GebMirror.Metalogic.«Literals.un» (_root_.Geb.Kernel.leaf 14) x2))
            (_root_.GebMirror.Metalogic.«Language.mPair»
              (_root_.GebMirror.Metalogic.«Translation.b0T» x0)
              _root_.GebMirror.Metalogic.«Translation.bnilT»)
            (_root_.GebMirror.Metalogic.«Language.mPair»
              (_root_.GebMirror.Metalogic.«Literals.un» (_root_.Geb.Kernel.leaf 14) x0)
              x1)
            (_root_.GebMirror.Metalogic.«Literals.bin» (_root_.Geb.Kernel.leaf 16) x1 x2))));
    x3

def «Literals.bitT» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (if (x0).label ≠ 0 then
      _root_.GebMirror.Metalogic.«Translation.b1T» x1
    else
      _root_.GebMirror.Metalogic.«Translation.b0T» x1);
    x2

def «Literals.divRhs» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Literals.bin»
                                          (_root_.Geb.Kernel.leaf 22)
                                          _root_.GebMirror.Metalogic.«Literals.vx»
                                          (_root_.GebMirror.Metalogic.«Literals.bitT»
                                            x1
                                            _root_.GebMirror.Metalogic.«Literals.vy»);
                                        _root_.GebMirror.Metalogic.«Literals.divStep»
                                          (_root_.GebMirror.Metalogic.«Language.mFst» x2)
                                          (_root_.GebMirror.Metalogic.«Literals.bitT»
                                            x0
                                            (_root_.GebMirror.Metalogic.«Language.mSnd» x2))
                                          (_root_.GebMirror.Metalogic.«Literals.bitT»
                                            x1
                                            _root_.GebMirror.Metalogic.«Literals.vy»));
    x2

def «Literals.lenOneT» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mListRec»
      (_root_.GebMirror.Metalogic.«Language.mPair»
        _root_.GebMirror.Metalogic.«Translation.bnilT»
        _root_.GebMirror.Metalogic.«Translation.bnilT»)
      (_root_.GebMirror.Metalogic.«Language.app»
        (_root_.GebMirror.Metalogic.«Language.mLam»
          _root_.GebMirror.Metalogic.«Literals.pairTy»
          (_root_.GebMirror.Metalogic.«Language.mPair»
            (_root_.GebMirror.Metalogic.«Literals.un»
              (_root_.Geb.Kernel.leaf 11)
              (_root_.GebMirror.Metalogic.«Language.mFst» _root_.GebMirror.Metalogic.«Literals.vy»))
            (_root_.GebMirror.Metalogic.«Translation.ifBit»
              _root_.GebMirror.Metalogic.«Translation.bitsTy»
              _root_.GebMirror.Metalogic.«Literals.vz»
              (_root_.GebMirror.Metalogic.«Language.mSnd» _root_.GebMirror.Metalogic.«Literals.vy»)
              _root_.GebMirror.Metalogic.«Translation.trueT»)))
        _root_.GebMirror.Metalogic.«Literals.vy»)
      x0;
    x1

def «Literals.lemSucc» :=
  _root_.GebMirror.Metalogic.«$4c69746572616c732f54686d462e6c36»
    (_root_.GebMirror.Metalogic.«Literals.lemEqn»
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«Literals.isNilT» _root_.GebMirror.Metalogic.«Translation.bnilT»)
      _root_.GebMirror.Metalogic.«Translation.trueT»)
    (_root_.GebMirror.Metalogic.«Literals.lemEqn»
      _root_.GebMirror.Metalogic.«Literals.b1c»
      (_root_.GebMirror.Metalogic.«Literals.isNilT»
        (_root_.GebMirror.Metalogic.«Translation.b0T» _root_.GebMirror.Metalogic.«Literals.vy»))
      _root_.GebMirror.Metalogic.«Translation.bnilT»)
    (_root_.GebMirror.Metalogic.«Literals.lemEqn»
      _root_.GebMirror.Metalogic.«Literals.b1c»
      (_root_.GebMirror.Metalogic.«Literals.isNilT»
        (_root_.GebMirror.Metalogic.«Translation.b1T» _root_.GebMirror.Metalogic.«Literals.vy»))
      _root_.GebMirror.Metalogic.«Translation.bnilT»)
    (_root_.GebMirror.Metalogic.«Literals.lemEqn»
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«Literals.un»
        (_root_.Geb.Kernel.leaf 11)
        _root_.GebMirror.Metalogic.«Translation.bnilT»)
      (_root_.GebMirror.Metalogic.«Translation.b0T» _root_.GebMirror.Metalogic.«Translation.bnilT»))
    (_root_.GebMirror.Metalogic.«Literals.lemEqn»
      _root_.GebMirror.Metalogic.«Literals.b1c»
      (_root_.GebMirror.Metalogic.«Literals.un»
        (_root_.Geb.Kernel.leaf 11)
        (_root_.GebMirror.Metalogic.«Translation.b0T» _root_.GebMirror.Metalogic.«Literals.vy»))
      (_root_.GebMirror.Metalogic.«Translation.b1T» _root_.GebMirror.Metalogic.«Literals.vy»))
    (_root_.GebMirror.Metalogic.«Literals.lemEqn»
      _root_.GebMirror.Metalogic.«Literals.b1c»
      (_root_.GebMirror.Metalogic.«Literals.un»
        (_root_.Geb.Kernel.leaf 11)
        (_root_.GebMirror.Metalogic.«Translation.b1T» _root_.GebMirror.Metalogic.«Literals.vy»))
      (_root_.GebMirror.Metalogic.«Translation.b0T»
        (_root_.GebMirror.Metalogic.«Literals.un»
          (_root_.Geb.Kernel.leaf 11)
          _root_.GebMirror.Metalogic.«Literals.vy»)))

def «Literals.lemPred» :=
  _root_.GebMirror.Metalogic.«$4c69746572616c732f54686d462e6c36»
    (_root_.GebMirror.Metalogic.«Literals.lemEqn»
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«Literals.un»
        (_root_.Geb.Kernel.leaf 14)
        _root_.GebMirror.Metalogic.«Translation.bnilT»)
      _root_.GebMirror.Metalogic.«Translation.bnilT»)
    (_root_.GebMirror.Metalogic.«Literals.lemEqn»
      _root_.GebMirror.Metalogic.«Literals.b1c»
      (_root_.GebMirror.Metalogic.«Literals.un»
        (_root_.Geb.Kernel.leaf 14)
        (_root_.GebMirror.Metalogic.«Translation.b0T» _root_.GebMirror.Metalogic.«Literals.vy»))
      (_root_.GebMirror.Metalogic.«Translation.b1T»
        (_root_.GebMirror.Metalogic.«Literals.un»
          (_root_.Geb.Kernel.leaf 14)
          _root_.GebMirror.Metalogic.«Literals.vy»)))
    (_root_.GebMirror.Metalogic.«Literals.lemEqn»
      _root_.GebMirror.Metalogic.«Literals.b1c»
      (_root_.GebMirror.Metalogic.«Literals.un»
        (_root_.Geb.Kernel.leaf 14)
        (_root_.GebMirror.Metalogic.«Translation.b1T» _root_.GebMirror.Metalogic.«Literals.vy»))
      (_root_.GebMirror.Metalogic.«Translation.b1T»
        (_root_.GebMirror.Metalogic.«Translation.b0T» _root_.GebMirror.Metalogic.«Literals.vy»)))
    (_root_.GebMirror.Metalogic.«Literals.lemEqn»
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«Literals.un»
        (_root_.Geb.Kernel.leaf 13)
        _root_.GebMirror.Metalogic.«Translation.bnilT»)
      _root_.GebMirror.Metalogic.«Translation.bnilT»)
    (_root_.GebMirror.Metalogic.«Literals.lemEqn»
      _root_.GebMirror.Metalogic.«Literals.b1c»
      (_root_.GebMirror.Metalogic.«Literals.un»
        (_root_.Geb.Kernel.leaf 13)
        (_root_.GebMirror.Metalogic.«Translation.b0T» _root_.GebMirror.Metalogic.«Literals.vy»))
      (_root_.GebMirror.Metalogic.«Literals.condB»
        _root_.GebMirror.Metalogic.«Literals.vy»
        (_root_.GebMirror.Metalogic.«Translation.b1T»
          (_root_.GebMirror.Metalogic.«Literals.un»
            (_root_.Geb.Kernel.leaf 13)
            _root_.GebMirror.Metalogic.«Literals.vy»))
        _root_.GebMirror.Metalogic.«Translation.bnilT»))
    (_root_.GebMirror.Metalogic.«Literals.lemEqn»
      _root_.GebMirror.Metalogic.«Literals.b1c»
      (_root_.GebMirror.Metalogic.«Literals.un»
        (_root_.Geb.Kernel.leaf 13)
        (_root_.GebMirror.Metalogic.«Translation.b1T» _root_.GebMirror.Metalogic.«Literals.vy»))
      (_root_.GebMirror.Metalogic.«Translation.b0T» _root_.GebMirror.Metalogic.«Literals.vy»))

def «Literals.lemCond» :=
  _root_.GebMirror.Metalogic.«$4c69746572616c732f54686d462e6c36»
    (_root_.GebMirror.Metalogic.«Literals.lemEqn»
      _root_.GebMirror.Metalogic.«Literals.b2c»
      (_root_.GebMirror.Metalogic.«Literals.condB»
        _root_.GebMirror.Metalogic.«Translation.bnilT»
        _root_.GebMirror.Metalogic.«Literals.vx»
        _root_.GebMirror.Metalogic.«Literals.vy»)
      _root_.GebMirror.Metalogic.«Literals.vy»)
    (_root_.GebMirror.Metalogic.«Literals.lemEqn»
      _root_.GebMirror.Metalogic.«Literals.b3c»
      (_root_.GebMirror.Metalogic.«Literals.condB»
        (_root_.GebMirror.Metalogic.«Translation.b0T» _root_.GebMirror.Metalogic.«Literals.vz»)
        _root_.GebMirror.Metalogic.«Literals.vx»
        _root_.GebMirror.Metalogic.«Literals.vy»)
      _root_.GebMirror.Metalogic.«Literals.vx»)
    (_root_.GebMirror.Metalogic.«Literals.lemEqn»
      _root_.GebMirror.Metalogic.«Literals.b3c»
      (_root_.GebMirror.Metalogic.«Literals.condB»
        (_root_.GebMirror.Metalogic.«Translation.b1T» _root_.GebMirror.Metalogic.«Literals.vz»)
        _root_.GebMirror.Metalogic.«Literals.vx»
        _root_.GebMirror.Metalogic.«Literals.vy»)
      _root_.GebMirror.Metalogic.«Literals.vx»)
    (_root_.GebMirror.Metalogic.«Literals.lemEqn»
      (_root_.GebMirror.Metalogic.«Theory.l2»
        _root_.GebMirror.Metalogic.«Translation.ordTy»
        _root_.GebMirror.Metalogic.«Translation.ordTy»)
      (_root_.GebMirror.Metalogic.«Literals.condO»
        _root_.GebMirror.Metalogic.«Translation.bnilT»
        _root_.GebMirror.Metalogic.«Literals.vx»
        _root_.GebMirror.Metalogic.«Literals.vy»)
      _root_.GebMirror.Metalogic.«Literals.vy»)
    (_root_.GebMirror.Metalogic.«Literals.lemEqn»
      (_root_.GebMirror.Metalogic.«Theory.l3»
        _root_.GebMirror.Metalogic.«Translation.ordTy»
        _root_.GebMirror.Metalogic.«Translation.ordTy»
        _root_.GebMirror.Metalogic.«Translation.bitsTy»)
      (_root_.GebMirror.Metalogic.«Literals.condO»
        (_root_.GebMirror.Metalogic.«Translation.b0T» _root_.GebMirror.Metalogic.«Literals.vz»)
        _root_.GebMirror.Metalogic.«Literals.vx»
        _root_.GebMirror.Metalogic.«Literals.vy»)
      _root_.GebMirror.Metalogic.«Literals.vx»)
    (_root_.GebMirror.Metalogic.«Literals.lemEqn»
      (_root_.GebMirror.Metalogic.«Theory.l3»
        _root_.GebMirror.Metalogic.«Translation.ordTy»
        _root_.GebMirror.Metalogic.«Translation.ordTy»
        _root_.GebMirror.Metalogic.«Translation.bitsTy»)
      (_root_.GebMirror.Metalogic.«Literals.condO»
        (_root_.GebMirror.Metalogic.«Translation.b1T» _root_.GebMirror.Metalogic.«Literals.vz»)
        _root_.GebMirror.Metalogic.«Literals.vx»
        _root_.GebMirror.Metalogic.«Literals.vy»)
      _root_.GebMirror.Metalogic.«Literals.vx»)

def «Literals.lemAdd» :=
  _root_.GebMirror.Metalogic.«$4c69746572616c732f54686d732e617070656e64»
    (_root_.GebMirror.Metalogic.«$4c69746572616c732f54686d462e6c34»
      (_root_.GebMirror.Metalogic.«Literals.lemEqn»
        _root_.GebMirror.Metalogic.«Literals.b1c»
        (_root_.GebMirror.Metalogic.«Literals.bin»
          (_root_.Geb.Kernel.leaf 15)
          _root_.GebMirror.Metalogic.«Literals.vy»
          _root_.GebMirror.Metalogic.«Translation.bnilT»)
        _root_.GebMirror.Metalogic.«Literals.vy»)
      (_root_.GebMirror.Metalogic.«Literals.lemEqn»
        _root_.GebMirror.Metalogic.«Literals.b1c»
        (_root_.GebMirror.Metalogic.«Literals.bin»
          (_root_.Geb.Kernel.leaf 15)
          _root_.GebMirror.Metalogic.«Translation.bnilT»
          (_root_.GebMirror.Metalogic.«Translation.b0T» _root_.GebMirror.Metalogic.«Literals.vy»))
        (_root_.GebMirror.Metalogic.«Translation.b0T» _root_.GebMirror.Metalogic.«Literals.vy»))
      (_root_.GebMirror.Metalogic.«Literals.lemEqn»
        _root_.GebMirror.Metalogic.«Literals.b1c»
        (_root_.GebMirror.Metalogic.«Literals.bin»
          (_root_.Geb.Kernel.leaf 15)
          _root_.GebMirror.Metalogic.«Translation.bnilT»
          (_root_.GebMirror.Metalogic.«Translation.b1T» _root_.GebMirror.Metalogic.«Literals.vy»))
        (_root_.GebMirror.Metalogic.«Translation.b1T» _root_.GebMirror.Metalogic.«Literals.vy»))
      (_root_.GebMirror.Metalogic.«Literals.lemEqn»
        _root_.GebMirror.Metalogic.«Literals.b2c»
        (_root_.GebMirror.Metalogic.«Literals.bin»
          (_root_.Geb.Kernel.leaf 15)
          (_root_.GebMirror.Metalogic.«Translation.b0T» _root_.GebMirror.Metalogic.«Literals.vx»)
          (_root_.GebMirror.Metalogic.«Translation.b0T» _root_.GebMirror.Metalogic.«Literals.vy»))
        (_root_.GebMirror.Metalogic.«Translation.b1T»
          (_root_.GebMirror.Metalogic.«Literals.bin»
            (_root_.Geb.Kernel.leaf 15)
            _root_.GebMirror.Metalogic.«Literals.vx»
            _root_.GebMirror.Metalogic.«Literals.vy»))))
    (_root_.GebMirror.Metalogic.«$4c69746572616c732f54686d462e6c36»
      (_root_.GebMirror.Metalogic.«Literals.lemEqn»
        _root_.GebMirror.Metalogic.«Literals.b2c»
        (_root_.GebMirror.Metalogic.«Literals.bin»
          (_root_.Geb.Kernel.leaf 15)
          (_root_.GebMirror.Metalogic.«Translation.b0T» _root_.GebMirror.Metalogic.«Literals.vx»)
          (_root_.GebMirror.Metalogic.«Translation.b1T» _root_.GebMirror.Metalogic.«Literals.vy»))
        (_root_.GebMirror.Metalogic.«Translation.b0T»
          (_root_.GebMirror.Metalogic.«Literals.un»
            (_root_.Geb.Kernel.leaf 11)
            (_root_.GebMirror.Metalogic.«Literals.bin»
              (_root_.Geb.Kernel.leaf 15)
              _root_.GebMirror.Metalogic.«Literals.vx»
              _root_.GebMirror.Metalogic.«Literals.vy»))))
      (_root_.GebMirror.Metalogic.«Literals.lemEqn»
        _root_.GebMirror.Metalogic.«Literals.b2c»
        (_root_.GebMirror.Metalogic.«Literals.bin»
          (_root_.Geb.Kernel.leaf 15)
          (_root_.GebMirror.Metalogic.«Translation.b1T» _root_.GebMirror.Metalogic.«Literals.vx»)
          (_root_.GebMirror.Metalogic.«Translation.b0T» _root_.GebMirror.Metalogic.«Literals.vy»))
        (_root_.GebMirror.Metalogic.«Translation.b0T»
          (_root_.GebMirror.Metalogic.«Literals.un»
            (_root_.Geb.Kernel.leaf 11)
            (_root_.GebMirror.Metalogic.«Literals.bin»
              (_root_.Geb.Kernel.leaf 15)
              _root_.GebMirror.Metalogic.«Literals.vx»
              _root_.GebMirror.Metalogic.«Literals.vy»))))
      (_root_.GebMirror.Metalogic.«Literals.lemEqn»
        _root_.GebMirror.Metalogic.«Literals.b2c»
        (_root_.GebMirror.Metalogic.«Literals.bin»
          (_root_.Geb.Kernel.leaf 15)
          (_root_.GebMirror.Metalogic.«Translation.b1T» _root_.GebMirror.Metalogic.«Literals.vx»)
          (_root_.GebMirror.Metalogic.«Translation.b1T» _root_.GebMirror.Metalogic.«Literals.vy»))
        (_root_.GebMirror.Metalogic.«Translation.b1T»
          (_root_.GebMirror.Metalogic.«Literals.un»
            (_root_.Geb.Kernel.leaf 11)
            (_root_.GebMirror.Metalogic.«Literals.bin»
              (_root_.Geb.Kernel.leaf 15)
              _root_.GebMirror.Metalogic.«Literals.vx»
              _root_.GebMirror.Metalogic.«Literals.vy»))))
      (_root_.GebMirror.Metalogic.«Literals.lemEqn»
        _root_.GebMirror.Metalogic.«Literals.b1c»
        (_root_.GebMirror.Metalogic.«Literals.bin»
          (_root_.Geb.Kernel.leaf 21)
          _root_.GebMirror.Metalogic.«Literals.vy»
          _root_.GebMirror.Metalogic.«Translation.bnilT»)
        _root_.GebMirror.Metalogic.«Translation.bnilT»)
      (_root_.GebMirror.Metalogic.«Literals.lemEqn»
        _root_.GebMirror.Metalogic.«Literals.b2c»
        (_root_.GebMirror.Metalogic.«Literals.bin»
          (_root_.Geb.Kernel.leaf 21)
          _root_.GebMirror.Metalogic.«Literals.vx»
          (_root_.GebMirror.Metalogic.«Translation.b0T» _root_.GebMirror.Metalogic.«Literals.vy»))
        (_root_.GebMirror.Metalogic.«Literals.bin»
          (_root_.Geb.Kernel.leaf 15)
          (_root_.GebMirror.Metalogic.«Literals.un»
            (_root_.Geb.Kernel.leaf 14)
            (_root_.GebMirror.Metalogic.«Literals.bin»
              (_root_.Geb.Kernel.leaf 21)
              _root_.GebMirror.Metalogic.«Literals.vx»
              _root_.GebMirror.Metalogic.«Literals.vy»))
          _root_.GebMirror.Metalogic.«Literals.vx»))
      (_root_.GebMirror.Metalogic.«Literals.lemEqn»
        _root_.GebMirror.Metalogic.«Literals.b2c»
        (_root_.GebMirror.Metalogic.«Literals.bin»
          (_root_.Geb.Kernel.leaf 21)
          _root_.GebMirror.Metalogic.«Literals.vx»
          (_root_.GebMirror.Metalogic.«Translation.b1T» _root_.GebMirror.Metalogic.«Literals.vy»))
        (_root_.GebMirror.Metalogic.«Literals.bin»
          (_root_.Geb.Kernel.leaf 15)
          (_root_.GebMirror.Metalogic.«Literals.un»
            (_root_.Geb.Kernel.leaf 14)
            (_root_.GebMirror.Metalogic.«Literals.bin»
              (_root_.Geb.Kernel.leaf 21)
              _root_.GebMirror.Metalogic.«Literals.vx»
              _root_.GebMirror.Metalogic.«Literals.vy»))
          (_root_.GebMirror.Metalogic.«Literals.un»
            (_root_.Geb.Kernel.leaf 14)
            _root_.GebMirror.Metalogic.«Literals.vx»))))

def «Literals.lemEq» :=
  ((_root_.GebMirror.Metalogic.«Literals.lemEqn»
    _root_.GebMirror.Metalogic.«Literals.b1c»
    (_root_.GebMirror.Metalogic.«Literals.bin»
      (_root_.Geb.Kernel.leaf 18)
      _root_.GebMirror.Metalogic.«Literals.vy»
      _root_.GebMirror.Metalogic.«Translation.bnilT»)
    (_root_.GebMirror.Metalogic.«Literals.isNilT» _root_.GebMirror.Metalogic.«Literals.vy»)) ::
    (_root_.GebMirror.Metalogic.«$4c69746572616c732f54686d462e6c36»
      (_root_.GebMirror.Metalogic.«Literals.lemEqn»
        _root_.GebMirror.Metalogic.«Literals.b1c»
        (_root_.GebMirror.Metalogic.«Literals.bin»
          (_root_.Geb.Kernel.leaf 18)
          _root_.GebMirror.Metalogic.«Translation.bnilT»
          (_root_.GebMirror.Metalogic.«Translation.b0T» _root_.GebMirror.Metalogic.«Literals.vy»))
        _root_.GebMirror.Metalogic.«Translation.bnilT»)
      (_root_.GebMirror.Metalogic.«Literals.lemEqn»
        _root_.GebMirror.Metalogic.«Literals.b1c»
        (_root_.GebMirror.Metalogic.«Literals.bin»
          (_root_.Geb.Kernel.leaf 18)
          _root_.GebMirror.Metalogic.«Translation.bnilT»
          (_root_.GebMirror.Metalogic.«Translation.b1T» _root_.GebMirror.Metalogic.«Literals.vy»))
        _root_.GebMirror.Metalogic.«Translation.bnilT»)
      (_root_.GebMirror.Metalogic.«Literals.lemEqn»
        _root_.GebMirror.Metalogic.«Literals.b2c»
        (_root_.GebMirror.Metalogic.«Literals.bin»
          (_root_.Geb.Kernel.leaf 18)
          (_root_.GebMirror.Metalogic.«Translation.b0T» _root_.GebMirror.Metalogic.«Literals.vx»)
          (_root_.GebMirror.Metalogic.«Translation.b0T» _root_.GebMirror.Metalogic.«Literals.vy»))
        (_root_.GebMirror.Metalogic.«Literals.bin»
          (_root_.Geb.Kernel.leaf 18)
          _root_.GebMirror.Metalogic.«Literals.vx»
          _root_.GebMirror.Metalogic.«Literals.vy»))
      (_root_.GebMirror.Metalogic.«Literals.lemEqn»
        _root_.GebMirror.Metalogic.«Literals.b2c»
        (_root_.GebMirror.Metalogic.«Literals.bin»
          (_root_.Geb.Kernel.leaf 18)
          (_root_.GebMirror.Metalogic.«Translation.b0T» _root_.GebMirror.Metalogic.«Literals.vx»)
          (_root_.GebMirror.Metalogic.«Translation.b1T» _root_.GebMirror.Metalogic.«Literals.vy»))
        _root_.GebMirror.Metalogic.«Translation.bnilT»)
      (_root_.GebMirror.Metalogic.«Literals.lemEqn»
        _root_.GebMirror.Metalogic.«Literals.b2c»
        (_root_.GebMirror.Metalogic.«Literals.bin»
          (_root_.Geb.Kernel.leaf 18)
          (_root_.GebMirror.Metalogic.«Translation.b1T» _root_.GebMirror.Metalogic.«Literals.vx»)
          (_root_.GebMirror.Metalogic.«Translation.b0T» _root_.GebMirror.Metalogic.«Literals.vy»))
        _root_.GebMirror.Metalogic.«Translation.bnilT»)
      (_root_.GebMirror.Metalogic.«Literals.lemEqn»
        _root_.GebMirror.Metalogic.«Literals.b2c»
        (_root_.GebMirror.Metalogic.«Literals.bin»
          (_root_.Geb.Kernel.leaf 18)
          (_root_.GebMirror.Metalogic.«Translation.b1T» _root_.GebMirror.Metalogic.«Literals.vx»)
          (_root_.GebMirror.Metalogic.«Translation.b1T» _root_.GebMirror.Metalogic.«Literals.vy»))
        (_root_.GebMirror.Metalogic.«Literals.bin»
          (_root_.Geb.Kernel.leaf 18)
          _root_.GebMirror.Metalogic.«Literals.vx»
          _root_.GebMirror.Metalogic.«Literals.vy»))))

def «Literals.o3c» :=
  _root_.GebMirror.Metalogic.«Theory.l3»
    _root_.GebMirror.Metalogic.«Translation.ordTy»
    _root_.GebMirror.Metalogic.«Translation.ordTy»
    _root_.GebMirror.Metalogic.«Translation.ordTy»

def «Literals.lemCmp» :=
  _root_.GebMirror.Metalogic.«$4c69746572616c732f54686d732e617070656e64»
    ((_root_.GebMirror.Metalogic.«Literals.lemEqn»
      _root_.GebMirror.Metalogic.«Literals.b1c»
      (_root_.GebMirror.Metalogic.«Literals.bin»
        (_root_.Geb.Kernel.leaf 16)
        _root_.GebMirror.Metalogic.«Literals.vy»
        _root_.GebMirror.Metalogic.«Translation.bnilT»)
      (_root_.GebMirror.Metalogic.«Literals.condO»
        _root_.GebMirror.Metalogic.«Literals.vy»
        _root_.GebMirror.Metalogic.«Translation.gtO»
        _root_.GebMirror.Metalogic.«Translation.eqO»)) ::
      (_root_.GebMirror.Metalogic.«$4c69746572616c732f54686d462e6c36»
        (_root_.GebMirror.Metalogic.«Literals.lemEqn»
          _root_.GebMirror.Metalogic.«Literals.b1c»
          (_root_.GebMirror.Metalogic.«Literals.bin»
            (_root_.Geb.Kernel.leaf 16)
            _root_.GebMirror.Metalogic.«Translation.bnilT»
            (_root_.GebMirror.Metalogic.«Translation.b0T» _root_.GebMirror.Metalogic.«Literals.vy»))
          _root_.GebMirror.Metalogic.«Translation.ltO»)
        (_root_.GebMirror.Metalogic.«Literals.lemEqn»
          _root_.GebMirror.Metalogic.«Literals.b1c»
          (_root_.GebMirror.Metalogic.«Literals.bin»
            (_root_.Geb.Kernel.leaf 16)
            _root_.GebMirror.Metalogic.«Translation.bnilT»
            (_root_.GebMirror.Metalogic.«Translation.b1T» _root_.GebMirror.Metalogic.«Literals.vy»))
          _root_.GebMirror.Metalogic.«Translation.ltO»)
        (_root_.GebMirror.Metalogic.«Literals.lemEqn»
          _root_.GebMirror.Metalogic.«Literals.b2c»
          (_root_.GebMirror.Metalogic.«Literals.bin»
            (_root_.Geb.Kernel.leaf 16)
            (_root_.GebMirror.Metalogic.«Translation.b0T» _root_.GebMirror.Metalogic.«Literals.vx»)
            (_root_.GebMirror.Metalogic.«Translation.b0T» _root_.GebMirror.Metalogic.«Literals.vy»))
          (_root_.GebMirror.Metalogic.«Translation.ifOrd»
            _root_.GebMirror.Metalogic.«Translation.ordTy»
            (_root_.GebMirror.Metalogic.«Literals.bin»
              (_root_.Geb.Kernel.leaf 16)
              _root_.GebMirror.Metalogic.«Literals.vx»
              _root_.GebMirror.Metalogic.«Literals.vy»)
            _root_.GebMirror.Metalogic.«Translation.ltO»
            _root_.GebMirror.Metalogic.«Translation.eqO»
            _root_.GebMirror.Metalogic.«Translation.gtO»))
        (_root_.GebMirror.Metalogic.«Literals.lemEqn»
          _root_.GebMirror.Metalogic.«Literals.b2c»
          (_root_.GebMirror.Metalogic.«Literals.bin»
            (_root_.Geb.Kernel.leaf 16)
            (_root_.GebMirror.Metalogic.«Translation.b0T» _root_.GebMirror.Metalogic.«Literals.vx»)
            (_root_.GebMirror.Metalogic.«Translation.b1T» _root_.GebMirror.Metalogic.«Literals.vy»))
          (_root_.GebMirror.Metalogic.«Translation.ifOrd»
            _root_.GebMirror.Metalogic.«Translation.ordTy»
            (_root_.GebMirror.Metalogic.«Literals.bin»
              (_root_.Geb.Kernel.leaf 16)
              _root_.GebMirror.Metalogic.«Literals.vx»
              _root_.GebMirror.Metalogic.«Literals.vy»)
            _root_.GebMirror.Metalogic.«Translation.ltO»
            _root_.GebMirror.Metalogic.«Translation.ltO»
            _root_.GebMirror.Metalogic.«Translation.gtO»))
        (_root_.GebMirror.Metalogic.«Literals.lemEqn»
          _root_.GebMirror.Metalogic.«Literals.b2c»
          (_root_.GebMirror.Metalogic.«Literals.bin»
            (_root_.Geb.Kernel.leaf 16)
            (_root_.GebMirror.Metalogic.«Translation.b1T» _root_.GebMirror.Metalogic.«Literals.vx»)
            (_root_.GebMirror.Metalogic.«Translation.b0T» _root_.GebMirror.Metalogic.«Literals.vy»))
          (_root_.GebMirror.Metalogic.«Translation.ifOrd»
            _root_.GebMirror.Metalogic.«Translation.ordTy»
            (_root_.GebMirror.Metalogic.«Literals.bin»
              (_root_.Geb.Kernel.leaf 16)
              _root_.GebMirror.Metalogic.«Literals.vx»
              _root_.GebMirror.Metalogic.«Literals.vy»)
            _root_.GebMirror.Metalogic.«Translation.ltO»
            _root_.GebMirror.Metalogic.«Translation.gtO»
            _root_.GebMirror.Metalogic.«Translation.gtO»))
        (_root_.GebMirror.Metalogic.«Literals.lemEqn»
          _root_.GebMirror.Metalogic.«Literals.b2c»
          (_root_.GebMirror.Metalogic.«Literals.bin»
            (_root_.Geb.Kernel.leaf 16)
            (_root_.GebMirror.Metalogic.«Translation.b1T» _root_.GebMirror.Metalogic.«Literals.vx»)
            (_root_.GebMirror.Metalogic.«Translation.b1T» _root_.GebMirror.Metalogic.«Literals.vy»))
          (_root_.GebMirror.Metalogic.«Translation.ifOrd»
            _root_.GebMirror.Metalogic.«Translation.ordTy»
            (_root_.GebMirror.Metalogic.«Literals.bin»
              (_root_.Geb.Kernel.leaf 16)
              _root_.GebMirror.Metalogic.«Literals.vx»
              _root_.GebMirror.Metalogic.«Literals.vy»)
            _root_.GebMirror.Metalogic.«Translation.ltO»
            _root_.GebMirror.Metalogic.«Translation.eqO»
            _root_.GebMirror.Metalogic.«Translation.gtO»))))
    ((_root_.GebMirror.Metalogic.«Literals.lemEqn»
      _root_.GebMirror.Metalogic.«Literals.o3c»
      (_root_.GebMirror.Metalogic.«Translation.ifOrd»
        _root_.GebMirror.Metalogic.«Translation.ordTy»
        _root_.GebMirror.Metalogic.«Translation.ltO»
        _root_.GebMirror.Metalogic.«Literals.vz»
        _root_.GebMirror.Metalogic.«Literals.vx»
        _root_.GebMirror.Metalogic.«Literals.vy»)
      _root_.GebMirror.Metalogic.«Literals.vz») ::
      (_root_.GebMirror.Metalogic.«$4c69746572616c732f54686d462e6c36»
        (_root_.GebMirror.Metalogic.«Literals.lemEqn»
          _root_.GebMirror.Metalogic.«Literals.o3c»
          (_root_.GebMirror.Metalogic.«Translation.ifOrd»
            _root_.GebMirror.Metalogic.«Translation.ordTy»
            _root_.GebMirror.Metalogic.«Translation.eqO»
            _root_.GebMirror.Metalogic.«Literals.vz»
            _root_.GebMirror.Metalogic.«Literals.vx»
            _root_.GebMirror.Metalogic.«Literals.vy»)
          _root_.GebMirror.Metalogic.«Literals.vx»)
        (_root_.GebMirror.Metalogic.«Literals.lemEqn»
          _root_.GebMirror.Metalogic.«Literals.o3c»
          (_root_.GebMirror.Metalogic.«Translation.ifOrd»
            _root_.GebMirror.Metalogic.«Translation.ordTy»
            _root_.GebMirror.Metalogic.«Translation.gtO»
            _root_.GebMirror.Metalogic.«Literals.vz»
            _root_.GebMirror.Metalogic.«Literals.vx»
            _root_.GebMirror.Metalogic.«Literals.vy»)
          _root_.GebMirror.Metalogic.«Literals.vy»)
        (_root_.GebMirror.Metalogic.«Literals.lemEqn»
          _root_.GebMirror.Metalogic.«Literals.b3c»
          (_root_.GebMirror.Metalogic.«Translation.ifOrd»
            _root_.GebMirror.Metalogic.«Translation.bitsTy»
            _root_.GebMirror.Metalogic.«Translation.ltO»
            _root_.GebMirror.Metalogic.«Literals.vz»
            _root_.GebMirror.Metalogic.«Literals.vx»
            _root_.GebMirror.Metalogic.«Literals.vy»)
          _root_.GebMirror.Metalogic.«Literals.vz»)
        (_root_.GebMirror.Metalogic.«Literals.lemEqn»
          _root_.GebMirror.Metalogic.«Literals.b3c»
          (_root_.GebMirror.Metalogic.«Translation.ifOrd»
            _root_.GebMirror.Metalogic.«Translation.bitsTy»
            _root_.GebMirror.Metalogic.«Translation.eqO»
            _root_.GebMirror.Metalogic.«Literals.vz»
            _root_.GebMirror.Metalogic.«Literals.vx»
            _root_.GebMirror.Metalogic.«Literals.vy»)
          _root_.GebMirror.Metalogic.«Literals.vx»)
        (_root_.GebMirror.Metalogic.«Literals.lemEqn»
          _root_.GebMirror.Metalogic.«Literals.b3c»
          (_root_.GebMirror.Metalogic.«Translation.ifOrd»
            _root_.GebMirror.Metalogic.«Translation.bitsTy»
            _root_.GebMirror.Metalogic.«Translation.gtO»
            _root_.GebMirror.Metalogic.«Literals.vz»
            _root_.GebMirror.Metalogic.«Literals.vx»
            _root_.GebMirror.Metalogic.«Literals.vy»)
          _root_.GebMirror.Metalogic.«Literals.vy»)
        (_root_.GebMirror.Metalogic.«Literals.lemEqn»
          _root_.GebMirror.Metalogic.«Literals.b2c»
          (_root_.GebMirror.Metalogic.«Literals.bin»
            (_root_.Geb.Kernel.leaf 17)
            _root_.GebMirror.Metalogic.«Literals.vx»
            _root_.GebMirror.Metalogic.«Literals.vy»)
          (_root_.GebMirror.Metalogic.«Translation.ifOrd»
            _root_.GebMirror.Metalogic.«Translation.bitsTy»
            (_root_.GebMirror.Metalogic.«Literals.bin»
              (_root_.Geb.Kernel.leaf 16)
              _root_.GebMirror.Metalogic.«Literals.vx»
              _root_.GebMirror.Metalogic.«Literals.vy»)
            _root_.GebMirror.Metalogic.«Translation.trueT»
            _root_.GebMirror.Metalogic.«Translation.bnilT»
            _root_.GebMirror.Metalogic.«Translation.bnilT»))))

def «Literals.lemSub» :=
  _root_.GebMirror.Metalogic.«$4c69746572616c732f54686d732e617070656e64»
    (_root_.GebMirror.Metalogic.«$4c69746572616c732f54686d462e6c34»
      (_root_.GebMirror.Metalogic.«Literals.lemEqn»
        _root_.GebMirror.Metalogic.«Literals.b1c»
        (_root_.GebMirror.Metalogic.«Literals.bin»
          (_root_.Geb.Kernel.leaf 19)
          _root_.GebMirror.Metalogic.«Literals.vy»
          _root_.GebMirror.Metalogic.«Translation.bnilT»)
        _root_.GebMirror.Metalogic.«Literals.vy»)
      (_root_.GebMirror.Metalogic.«Literals.lemEqn»
        _root_.GebMirror.Metalogic.«Literals.b1c»
        (_root_.GebMirror.Metalogic.«Literals.bin»
          (_root_.Geb.Kernel.leaf 19)
          _root_.GebMirror.Metalogic.«Translation.bnilT»
          (_root_.GebMirror.Metalogic.«Translation.b0T» _root_.GebMirror.Metalogic.«Literals.vy»))
        _root_.GebMirror.Metalogic.«Translation.bnilT»)
      (_root_.GebMirror.Metalogic.«Literals.lemEqn»
        _root_.GebMirror.Metalogic.«Literals.b1c»
        (_root_.GebMirror.Metalogic.«Literals.bin»
          (_root_.Geb.Kernel.leaf 19)
          _root_.GebMirror.Metalogic.«Translation.bnilT»
          (_root_.GebMirror.Metalogic.«Translation.b1T» _root_.GebMirror.Metalogic.«Literals.vy»))
        _root_.GebMirror.Metalogic.«Translation.bnilT»)
      (_root_.GebMirror.Metalogic.«Literals.lemEqn»
        _root_.GebMirror.Metalogic.«Literals.b2c»
        (_root_.GebMirror.Metalogic.«Literals.bin»
          (_root_.Geb.Kernel.leaf 19)
          (_root_.GebMirror.Metalogic.«Translation.b0T» _root_.GebMirror.Metalogic.«Literals.vx»)
          (_root_.GebMirror.Metalogic.«Translation.b0T» _root_.GebMirror.Metalogic.«Literals.vy»))
        (_root_.GebMirror.Metalogic.«Literals.un»
          (_root_.Geb.Kernel.leaf 14)
          (_root_.GebMirror.Metalogic.«Literals.bin»
            (_root_.Geb.Kernel.leaf 19)
            _root_.GebMirror.Metalogic.«Literals.vx»
            _root_.GebMirror.Metalogic.«Literals.vy»))))
    (_root_.GebMirror.Metalogic.«$4c69746572616c732f54686d462e6c34»
      (_root_.GebMirror.Metalogic.«Literals.lemEqn»
        _root_.GebMirror.Metalogic.«Literals.b2c»
        (_root_.GebMirror.Metalogic.«Literals.bin»
          (_root_.Geb.Kernel.leaf 19)
          (_root_.GebMirror.Metalogic.«Translation.b0T» _root_.GebMirror.Metalogic.«Literals.vx»)
          (_root_.GebMirror.Metalogic.«Translation.b1T» _root_.GebMirror.Metalogic.«Literals.vy»))
        (_root_.GebMirror.Metalogic.«Translation.b0T»
          (_root_.GebMirror.Metalogic.«Literals.un»
            (_root_.Geb.Kernel.leaf 13)
            (_root_.GebMirror.Metalogic.«Literals.bin»
              (_root_.Geb.Kernel.leaf 19)
              _root_.GebMirror.Metalogic.«Literals.vx»
              _root_.GebMirror.Metalogic.«Literals.vy»))))
      (_root_.GebMirror.Metalogic.«Literals.lemEqn»
        _root_.GebMirror.Metalogic.«Literals.b2c»
        (_root_.GebMirror.Metalogic.«Literals.bin»
          (_root_.Geb.Kernel.leaf 19)
          (_root_.GebMirror.Metalogic.«Translation.b1T» _root_.GebMirror.Metalogic.«Literals.vx»)
          (_root_.GebMirror.Metalogic.«Translation.b0T» _root_.GebMirror.Metalogic.«Literals.vy»))
        (_root_.GebMirror.Metalogic.«Translation.b0T»
          (_root_.GebMirror.Metalogic.«Literals.bin»
            (_root_.Geb.Kernel.leaf 19)
            _root_.GebMirror.Metalogic.«Literals.vx»
            _root_.GebMirror.Metalogic.«Literals.vy»)))
      (_root_.GebMirror.Metalogic.«Literals.lemEqn»
        _root_.GebMirror.Metalogic.«Literals.b2c»
        (_root_.GebMirror.Metalogic.«Literals.bin»
          (_root_.Geb.Kernel.leaf 19)
          (_root_.GebMirror.Metalogic.«Translation.b1T» _root_.GebMirror.Metalogic.«Literals.vx»)
          (_root_.GebMirror.Metalogic.«Translation.b1T» _root_.GebMirror.Metalogic.«Literals.vy»))
        (_root_.GebMirror.Metalogic.«Literals.un»
          (_root_.Geb.Kernel.leaf 14)
          (_root_.GebMirror.Metalogic.«Literals.bin»
            (_root_.Geb.Kernel.leaf 19)
            _root_.GebMirror.Metalogic.«Literals.vx»
            _root_.GebMirror.Metalogic.«Literals.vy»)))
      (_root_.GebMirror.Metalogic.«Literals.lemEqn»
        _root_.GebMirror.Metalogic.«Literals.b2c»
        (_root_.GebMirror.Metalogic.«Literals.bin»
          (_root_.Geb.Kernel.leaf 20)
          _root_.GebMirror.Metalogic.«Literals.vx»
          _root_.GebMirror.Metalogic.«Literals.vy»)
        (_root_.GebMirror.Metalogic.«Literals.condB»
          (_root_.GebMirror.Metalogic.«Literals.bin»
            (_root_.Geb.Kernel.leaf 17)
            _root_.GebMirror.Metalogic.«Literals.vx»
            _root_.GebMirror.Metalogic.«Literals.vy»)
          _root_.GebMirror.Metalogic.«Translation.bnilT»
          (_root_.GebMirror.Metalogic.«Literals.bin»
            (_root_.Geb.Kernel.leaf 19)
            _root_.GebMirror.Metalogic.«Literals.vx»
            _root_.GebMirror.Metalogic.«Literals.vy»))))

def «Literals.lemDiv» :=
  ((_root_.GebMirror.Metalogic.«Literals.lemEqn»
    _root_.GebMirror.Metalogic.«Literals.b1c»
    (_root_.GebMirror.Metalogic.«Literals.bin»
      (_root_.Geb.Kernel.leaf 22)
      _root_.GebMirror.Metalogic.«Literals.vy»
      _root_.GebMirror.Metalogic.«Translation.bnilT»)
    (_root_.GebMirror.Metalogic.«Language.mPair»
      _root_.GebMirror.Metalogic.«Translation.bnilT»
      _root_.GebMirror.Metalogic.«Literals.vy»)) ::
    (_root_.GebMirror.Metalogic.«$4c69746572616c732f54686d462e6c36»
      (_root_.GebMirror.Metalogic.«Literals.lemEqn»
        _root_.GebMirror.Metalogic.«Literals.b1c»
        (_root_.GebMirror.Metalogic.«Literals.bin»
          (_root_.Geb.Kernel.leaf 22)
          _root_.GebMirror.Metalogic.«Translation.bnilT»
          (_root_.GebMirror.Metalogic.«Translation.b0T» _root_.GebMirror.Metalogic.«Literals.vy»))
        (_root_.GebMirror.Metalogic.«Language.mPair»
          _root_.GebMirror.Metalogic.«Translation.bnilT»
          _root_.GebMirror.Metalogic.«Translation.bnilT»))
      (_root_.GebMirror.Metalogic.«Literals.lemEqn»
        _root_.GebMirror.Metalogic.«Literals.b1c»
        (_root_.GebMirror.Metalogic.«Literals.bin»
          (_root_.Geb.Kernel.leaf 22)
          _root_.GebMirror.Metalogic.«Translation.bnilT»
          (_root_.GebMirror.Metalogic.«Translation.b1T» _root_.GebMirror.Metalogic.«Literals.vy»))
        (_root_.GebMirror.Metalogic.«Language.mPair»
          _root_.GebMirror.Metalogic.«Translation.bnilT»
          _root_.GebMirror.Metalogic.«Translation.bnilT»))
      (_root_.GebMirror.Metalogic.«Literals.lemEqn»
        _root_.GebMirror.Metalogic.«Literals.b2c»
        (_root_.GebMirror.Metalogic.«Literals.bin»
          (_root_.Geb.Kernel.leaf 22)
          (_root_.GebMirror.Metalogic.«Translation.b0T» _root_.GebMirror.Metalogic.«Literals.vx»)
          (_root_.GebMirror.Metalogic.«Translation.b0T» _root_.GebMirror.Metalogic.«Literals.vy»))
        (_root_.GebMirror.Metalogic.«Literals.divRhs»
          (_root_.Geb.Kernel.leaf 0)
          (_root_.Geb.Kernel.leaf 0)))
      (_root_.GebMirror.Metalogic.«Literals.lemEqn»
        _root_.GebMirror.Metalogic.«Literals.b2c»
        (_root_.GebMirror.Metalogic.«Literals.bin»
          (_root_.Geb.Kernel.leaf 22)
          (_root_.GebMirror.Metalogic.«Translation.b0T» _root_.GebMirror.Metalogic.«Literals.vx»)
          (_root_.GebMirror.Metalogic.«Translation.b1T» _root_.GebMirror.Metalogic.«Literals.vy»))
        (_root_.GebMirror.Metalogic.«Literals.divRhs»
          (_root_.Geb.Kernel.leaf 0)
          (_root_.Geb.Kernel.leaf 1)))
      (_root_.GebMirror.Metalogic.«Literals.lemEqn»
        _root_.GebMirror.Metalogic.«Literals.b2c»
        (_root_.GebMirror.Metalogic.«Literals.bin»
          (_root_.Geb.Kernel.leaf 22)
          (_root_.GebMirror.Metalogic.«Translation.b1T» _root_.GebMirror.Metalogic.«Literals.vx»)
          (_root_.GebMirror.Metalogic.«Translation.b0T» _root_.GebMirror.Metalogic.«Literals.vy»))
        (_root_.GebMirror.Metalogic.«Literals.divRhs»
          (_root_.Geb.Kernel.leaf 1)
          (_root_.Geb.Kernel.leaf 0)))
      (_root_.GebMirror.Metalogic.«Literals.lemEqn»
        _root_.GebMirror.Metalogic.«Literals.b2c»
        (_root_.GebMirror.Metalogic.«Literals.bin»
          (_root_.Geb.Kernel.leaf 22)
          (_root_.GebMirror.Metalogic.«Translation.b1T» _root_.GebMirror.Metalogic.«Literals.vx»)
          (_root_.GebMirror.Metalogic.«Translation.b1T» _root_.GebMirror.Metalogic.«Literals.vy»))
        (_root_.GebMirror.Metalogic.«Literals.divRhs»
          (_root_.Geb.Kernel.leaf 1)
          (_root_.Geb.Kernel.leaf 1)))))

def «Literals.p3c» :=
  _root_.GebMirror.Metalogic.«Theory.l3»
    _root_.GebMirror.Metalogic.«Literals.pairTy»
    _root_.GebMirror.Metalogic.«Literals.pairTy»
    _root_.GebMirror.Metalogic.«Literals.pairTy»

def «Literals.p6c» :=
  _root_.GebMirror.Metalogic.«Theory.l6»
    _root_.GebMirror.Metalogic.«Literals.pairTy»
    _root_.GebMirror.Metalogic.«Literals.pairTy»
    _root_.GebMirror.Metalogic.«Literals.pairTy»
    _root_.GebMirror.Metalogic.«Translation.ordTy»
    _root_.GebMirror.Metalogic.«Literals.pairTy»
    _root_.GebMirror.Metalogic.«Literals.pairTy»

def «Literals.lemSel» :=
  _root_.GebMirror.Metalogic.«$4c69746572616c732f54686d462e6c36»
    (_root_.GebMirror.Metalogic.«Literals.lemEqn»
      _root_.GebMirror.Metalogic.«Literals.p3c»
      (_root_.GebMirror.Metalogic.«Translation.ifOrd»
        _root_.GebMirror.Metalogic.«Literals.pairTy»
        _root_.GebMirror.Metalogic.«Translation.ltO»
        _root_.GebMirror.Metalogic.«Literals.vz»
        _root_.GebMirror.Metalogic.«Literals.vx»
        _root_.GebMirror.Metalogic.«Literals.vy»)
      _root_.GebMirror.Metalogic.«Literals.vz»)
    (_root_.GebMirror.Metalogic.«Literals.lemEqn»
      _root_.GebMirror.Metalogic.«Literals.p3c»
      (_root_.GebMirror.Metalogic.«Translation.ifOrd»
        _root_.GebMirror.Metalogic.«Literals.pairTy»
        _root_.GebMirror.Metalogic.«Translation.eqO»
        _root_.GebMirror.Metalogic.«Literals.vz»
        _root_.GebMirror.Metalogic.«Literals.vx»
        _root_.GebMirror.Metalogic.«Literals.vy»)
      _root_.GebMirror.Metalogic.«Literals.vx»)
    (_root_.GebMirror.Metalogic.«Literals.lemEqn»
      _root_.GebMirror.Metalogic.«Literals.p3c»
      (_root_.GebMirror.Metalogic.«Translation.ifOrd»
        _root_.GebMirror.Metalogic.«Literals.pairTy»
        _root_.GebMirror.Metalogic.«Translation.gtO»
        _root_.GebMirror.Metalogic.«Literals.vz»
        _root_.GebMirror.Metalogic.«Literals.vx»
        _root_.GebMirror.Metalogic.«Literals.vy»)
      _root_.GebMirror.Metalogic.«Literals.vy»)
    (_root_.GebMirror.Metalogic.«Literals.lemEqn»
      _root_.GebMirror.Metalogic.«Literals.p6c»
      (_root_.GebMirror.Metalogic.«Literals.selSel» _root_.GebMirror.Metalogic.«Translation.ltO»)
      (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 5)))
    (_root_.GebMirror.Metalogic.«Literals.lemEqn»
      _root_.GebMirror.Metalogic.«Literals.p6c»
      (_root_.GebMirror.Metalogic.«Literals.selSel» _root_.GebMirror.Metalogic.«Translation.eqO»)
      (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 4)))
    (_root_.GebMirror.Metalogic.«Literals.lemEqn»
      _root_.GebMirror.Metalogic.«Literals.p6c»
      (_root_.GebMirror.Metalogic.«Literals.selSel» _root_.GebMirror.Metalogic.«Translation.gtO»)
      _root_.GebMirror.Metalogic.«Literals.selIn»)

def «Literals.lemLog» :=
  _root_.GebMirror.Metalogic.«$4c69746572616c732f54686d462e6c34»
    (_root_.GebMirror.Metalogic.«Literals.lemEqn»
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«Literals.lenOneT» _root_.GebMirror.Metalogic.«Translation.bnilT»)
      (_root_.GebMirror.Metalogic.«Language.mPair»
        _root_.GebMirror.Metalogic.«Translation.bnilT»
        _root_.GebMirror.Metalogic.«Translation.bnilT»))
    (_root_.GebMirror.Metalogic.«Literals.lemEqn»
      _root_.GebMirror.Metalogic.«Literals.b1c»
      (_root_.GebMirror.Metalogic.«Literals.lenOneT»
        (_root_.GebMirror.Metalogic.«Translation.b0T» _root_.GebMirror.Metalogic.«Literals.vy»))
      (_root_.GebMirror.Metalogic.«Language.mPair»
        (_root_.GebMirror.Metalogic.«Literals.un»
          (_root_.Geb.Kernel.leaf 11)
          (_root_.GebMirror.Metalogic.«Language.mFst»
            (_root_.GebMirror.Metalogic.«Literals.lenOneT» _root_.GebMirror.Metalogic.«Literals.vy»)))
        (_root_.GebMirror.Metalogic.«Language.mSnd»
          (_root_.GebMirror.Metalogic.«Literals.lenOneT» _root_.GebMirror.Metalogic.«Literals.vy»))))
    (_root_.GebMirror.Metalogic.«Literals.lemEqn»
      _root_.GebMirror.Metalogic.«Literals.b1c»
      (_root_.GebMirror.Metalogic.«Literals.lenOneT»
        (_root_.GebMirror.Metalogic.«Translation.b1T» _root_.GebMirror.Metalogic.«Literals.vy»))
      (_root_.GebMirror.Metalogic.«Language.mPair»
        (_root_.GebMirror.Metalogic.«Literals.un»
          (_root_.Geb.Kernel.leaf 11)
          (_root_.GebMirror.Metalogic.«Language.mFst»
            (_root_.GebMirror.Metalogic.«Literals.lenOneT» _root_.GebMirror.Metalogic.«Literals.vy»)))
        _root_.GebMirror.Metalogic.«Translation.trueT»))
    (_root_.GebMirror.Metalogic.«Literals.lemEqn»
      _root_.GebMirror.Metalogic.«Literals.b1c»
      (_root_.GebMirror.Metalogic.«Literals.un»
        (_root_.Geb.Kernel.leaf 23)
        _root_.GebMirror.Metalogic.«Literals.vy»)
      (_root_.GebMirror.Metalogic.«Literals.condB»
        (_root_.GebMirror.Metalogic.«Language.mSnd»
          (_root_.GebMirror.Metalogic.«Literals.lenOneT» _root_.GebMirror.Metalogic.«Literals.vy»))
        (_root_.GebMirror.Metalogic.«Language.mFst»
          (_root_.GebMirror.Metalogic.«Literals.lenOneT» _root_.GebMirror.Metalogic.«Literals.vy»))
        (_root_.GebMirror.Metalogic.«Literals.un»
          (_root_.Geb.Kernel.leaf 13)
          (_root_.GebMirror.Metalogic.«Language.mFst»
            (_root_.GebMirror.Metalogic.«Literals.lenOneT» _root_.GebMirror.Metalogic.«Literals.vy»)))))

def «Literals.lemmas» :=
  _root_.GebMirror.Metalogic.«$4c69746572616c732f54686d732e617070656e64»
    _root_.GebMirror.Metalogic.«Literals.lemSucc»
    (_root_.GebMirror.Metalogic.«$4c69746572616c732f54686d732e617070656e64»
      _root_.GebMirror.Metalogic.«Literals.lemPred»
      (_root_.GebMirror.Metalogic.«$4c69746572616c732f54686d732e617070656e64»
        _root_.GebMirror.Metalogic.«Literals.lemCond»
        (_root_.GebMirror.Metalogic.«$4c69746572616c732f54686d732e617070656e64»
          _root_.GebMirror.Metalogic.«Literals.lemAdd»
          (_root_.GebMirror.Metalogic.«$4c69746572616c732f54686d732e617070656e64»
            _root_.GebMirror.Metalogic.«Literals.lemEq»
            (_root_.GebMirror.Metalogic.«$4c69746572616c732f54686d732e617070656e64»
              _root_.GebMirror.Metalogic.«Literals.lemCmp»
              (_root_.GebMirror.Metalogic.«$4c69746572616c732f54686d732e617070656e64»
                _root_.GebMirror.Metalogic.«Literals.lemSub»
                (_root_.GebMirror.Metalogic.«$4c69746572616c732f54686d732e617070656e64»
                  _root_.GebMirror.Metalogic.«Literals.lemDiv»
                  (_root_.GebMirror.Metalogic.«$4c69746572616c732f54686d732e617070656e64»
                    _root_.GebMirror.Metalogic.«Literals.lemSel»
                    _root_.GebMirror.Metalogic.«Literals.lemLog»))))))))

def «Literals.lemmasIn» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
         (x4 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Prelude.and»
          (let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Derivation.thmAt»
             x0
             (_root_.Geb.Kernel.Const.add x1 x4);
           if (_root_.Geb.Kernel.Const.eq
             (_root_.Geb.Kernel.Const.label x5)
             (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
             let x6 : _root_.List
               _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x5;
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
             _root_.Geb.Kernel.Const.equal x7 x2
           else
             let _ : _root_.List
               _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x5;
             _root_.Geb.Kernel.leaf 0)
          (x3 (_root_.Geb.Kernel.Const.add x4 (_root_.Geb.Kernel.leaf 1))))
      (fun (_ : _root_.Geb.Kernel.Tree) => _root_.Geb.Kernel.leaf 1)
      _root_.GebMirror.Metalogic.«Literals.lemmas»
      (_root_.Geb.Kernel.leaf 0);
    x2

def «Literals.sigOk» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree) =>
    let x6 : _root_.Geb.Kernel.Tree := (let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.bindDL»
                                          (_root_.GebMirror.Metalogic.«$4c616e67756167652f4f446566696e6974696f6e2e6e74684f66»
                                            (_root_.GebMirror.Metalogic.«Language.gDefs» x0)
                                            x2)
                                          _root_.GebMirror.Metalogic.«Language.defLanguage»;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x6)
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          let x7 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x6;
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
                                          _root_.GebMirror.Metalogic.«Prelude.and»
                                            (_root_.GebMirror.Metalogic.«Prelude.and»
                                              (_root_.GebMirror.Metalogic.«Prelude.and»
                                                (_root_.Geb.Kernel.Const.eq
                                                  (_root_.GebMirror.Metalogic.«Language.ldArity» x8)
                                                  (_root_.GebMirror.Metalogic.«Prelude.length» x3))
                                                (_root_.GebMirror.Metalogic.«Base.allT»
                                                  (_root_.GebMirror.Metalogic.«Language.isTy» x0 x1)
                                                  x3))
                                              (_root_.GebMirror.Metalogic.«Base.equalTs»
                                                (_root_.GebMirror.Metalogic.«Base.mapT»
                                                  (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                                    _root_.GebMirror.Metalogic.«PartialHorn.phSubst» x3 x10)
                                                  (_root_.GebMirror.Metalogic.«Language.ldParams» x8))
                                                x4))
                                            (_root_.Geb.Kernel.Const.equal
                                              (_root_.GebMirror.Metalogic.«PartialHorn.phSubst»
                                                x3
                                                (_root_.GebMirror.Metalogic.«Language.ldType» x8))
                                              x5)
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x6;
                                          _root_.Geb.Kernel.leaf 0);
    x6

def «Literals.sigs» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Base.allT»
      (fun (x2 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Literals.sigOk»
          x0
          x1
          (_root_.Geb.Kernel.Const.child x2 (_root_.Geb.Kernel.leaf 0))
          (_root_.Geb.Kernel.Const.children
            (_root_.Geb.Kernel.Const.child x2 (_root_.Geb.Kernel.leaf 1)))
          (_root_.Geb.Kernel.Const.children
            (_root_.Geb.Kernel.Const.child x2 (_root_.Geb.Kernel.leaf 2)))
          (_root_.Geb.Kernel.Const.child x2 (_root_.Geb.Kernel.leaf 3)))
      _root_.GebMirror.Metalogic.«Literals.syms»;
    x2

def «Literals.ready» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.and»
      (_root_.GebMirror.Metalogic.«Prelude.and»
        (_root_.GebMirror.Metalogic.«Literals.lemmasIn» x1 x2)
        (_root_.GebMirror.Metalogic.«Literals.sigs» x0 (_root_.Geb.Kernel.leaf 0)))
      (_root_.GebMirror.Metalogic.«Prelude.and»
        (_root_.Geb.Kernel.Const.equal
          (_root_.GebMirror.Metalogic.«Derivation.typeIn»
            x0
            (_root_.Geb.Kernel.leaf 0)
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            _root_.GebMirror.Metalogic.«Translation.ltO»)
          (_root_.GebMirror.Metalogic.«Prelude.some» _root_.GebMirror.Metalogic.«Translation.ordTy»))
        (_root_.GebMirror.Metalogic.«Prelude.and»
          (_root_.Geb.Kernel.Const.equal
            (_root_.GebMirror.Metalogic.«Derivation.typeIn»
              x0
              (_root_.Geb.Kernel.leaf 0)
              ([] : _root_.List _root_.Geb.Kernel.Tree)
              _root_.GebMirror.Metalogic.«Translation.eqO»)
            (_root_.GebMirror.Metalogic.«Prelude.some» _root_.GebMirror.Metalogic.«Translation.ordTy»))
          (_root_.Geb.Kernel.Const.equal
            (_root_.GebMirror.Metalogic.«Derivation.typeIn»
              x0
              (_root_.Geb.Kernel.leaf 0)
              ([] : _root_.List _root_.Geb.Kernel.Tree)
              _root_.GebMirror.Metalogic.«Translation.gtO»)
            (_root_.GebMirror.Metalogic.«Prelude.some» _root_.GebMirror.Metalogic.«Translation.ordTy»))));
    x3

def «Machine.failV» :=
  _root_.GebMirror.Metalogic.«Language.mNode»
    (_root_.Geb.Kernel.leaf 16)
    ([] : _root_.List _root_.Geb.Kernel.Tree)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «Machine.delayed» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mNode»
      (_root_.Geb.Kernel.leaf 15)
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«Theory.l2»
        (_root_.GebMirror.Metalogic.«Base.getD» x0 _root_.GebMirror.Metalogic.«Machine.failV»)
        x1);
    x2

def «Machine.freeVar» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (if (_root_.Geb.Kernel.Const.lt
      x1
      x0).label ≠ 0 then
      _root_.GebMirror.Metalogic.«Language.mNode»
        (_root_.Geb.Kernel.leaf 0)
        (_root_.GebMirror.Metalogic.«Prelude.single»
          (_root_.Geb.Kernel.Const.sub
            (_root_.Geb.Kernel.Const.sub x0 (_root_.Geb.Kernel.leaf 1))
            x1))
        ([] : _root_.List _root_.Geb.Kernel.Tree)
    else
      _root_.GebMirror.Metalogic.«Language.mNode»
        (_root_.Geb.Kernel.leaf 1)
        (_root_.GebMirror.Metalogic.«Prelude.single» (_root_.Geb.Kernel.Const.sub x1 x0))
        ([] : _root_.List _root_.Geb.Kernel.Tree));
    x2

def «Machine.level» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mNode»
      (_root_.Geb.Kernel.leaf 0)
      (_root_.GebMirror.Metalogic.«Prelude.single» x0)
      ([] : _root_.List _root_.Geb.Kernel.Tree);
    x1

def «Machine.envSubst» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := (if (_root_.Geb.Kernel.Const.lt
      x2
      (_root_.GebMirror.Metalogic.«Prelude.length» x0)).label ≠ 0 then
      _root_.GebMirror.Metalogic.«Prelude.at» x0 x2
    else
      _root_.GebMirror.Metalogic.«Language.var»
        (_root_.Geb.Kernel.Const.add
          (_root_.Geb.Kernel.Const.sub x2 (_root_.GebMirror.Metalogic.«Prelude.length» x0))
          x1));
    x3

def «Machine.readStep» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := (let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.label
                                          x1;
                                        if (_root_.Geb.Kernel.Const.eq
                                          x3
                                          (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                                          _root_.GebMirror.Metalogic.«Language.var»
                                            (_root_.Geb.Kernel.Const.sub
                                              (_root_.Geb.Kernel.Const.sub
                                                x0
                                                (_root_.Geb.Kernel.leaf 1))
                                              (_root_.GebMirror.Metalogic.«Language.mD»
                                                x1
                                                (_root_.Geb.Kernel.leaf 0)))
                                        else
                                          if (_root_.Geb.Kernel.Const.eq
                                            x3
                                            (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                            _root_.GebMirror.Metalogic.«Language.var»
                                              (_root_.Geb.Kernel.Const.add
                                                x0
                                                (_root_.GebMirror.Metalogic.«Language.mD»
                                                  x1
                                                  (_root_.Geb.Kernel.leaf 0)))
                                          else
                                            if (_root_.Geb.Kernel.Const.eq
                                              x3
                                              (_root_.Geb.Kernel.leaf 3)).label ≠ 0 then
                                              _root_.GebMirror.Metalogic.«Language.mNode»
                                                (_root_.Geb.Kernel.leaf 2)
                                                ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                x2
                                            else
                                              if (_root_.Geb.Kernel.Const.eq
                                                x3
                                                (_root_.Geb.Kernel.leaf 4)).label ≠ 0 then
                                                _root_.GebMirror.Metalogic.«Language.mLam»
                                                  (_root_.GebMirror.Metalogic.«Language.mD»
                                                    x1
                                                    (_root_.Geb.Kernel.leaf 0))
                                                  (_root_.GebMirror.Metalogic.«Language.subst»
                                                    (_root_.GebMirror.Metalogic.«Language.mD»
                                                      x1
                                                      (_root_.Geb.Kernel.leaf 1))
                                                    (fun (x4 : _root_.Geb.Kernel.Tree) =>
                                                      _root_.GebMirror.Metalogic.«Language.liftS»
                                                        (_root_.GebMirror.Metalogic.«Machine.envSubst»
                                                          x2
                                                          (_root_.Geb.Kernel.Const.sub
                                                            x0
                                                            (_root_.GebMirror.Metalogic.«Language.mD»
                                                              x1
                                                              (_root_.Geb.Kernel.leaf 2))))
                                                        x4))
                                              else
                                                if (_root_.Geb.Kernel.Const.eq
                                                  x3
                                                  (_root_.Geb.Kernel.leaf 5)).label ≠ 0 then
                                                  _root_.GebMirror.Metalogic.«Language.mNode»
                                                    (_root_.Geb.Kernel.leaf 7)
                                                    (_root_.Geb.Kernel.Const.children
                                                      (_root_.Geb.Kernel.Const.child
                                                        x1
                                                        (_root_.Geb.Kernel.leaf 0)))
                                                    x2
                                                else
                                                  if (_root_.Geb.Kernel.Const.eq
                                                    x3
                                                    (_root_.Geb.Kernel.leaf 6)).label ≠ 0 then
                                                    _root_.GebMirror.Metalogic.«Language.mNode»
                                                      (_root_.Geb.Kernel.leaf 6)
                                                      ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                      x2
                                                  else
                                                    if (_root_.Geb.Kernel.Const.eq
                                                      x3
                                                      (_root_.Geb.Kernel.leaf 7)).label ≠ 0 then
                                                      _root_.GebMirror.Metalogic.«Language.mNode»
                                                        (_root_.Geb.Kernel.leaf 3)
                                                        ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                        x2
                                                    else
                                                      if (_root_.Geb.Kernel.Const.eq
                                                        x3
                                                        (_root_.Geb.Kernel.leaf 8)).label ≠ 0 then
                                                        _root_.GebMirror.Metalogic.«Language.mNode»
                                                          (_root_.Geb.Kernel.leaf 4)
                                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                          x2
                                                      else
                                                        if (_root_.Geb.Kernel.Const.eq
                                                          x3
                                                          (_root_.Geb.Kernel.leaf 9)).label ≠ 0 then
                                                          if (_root_.Geb.Kernel.Const.lt
                                                            (_root_.GebMirror.Metalogic.«Prelude.length» x2)
                                                            (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
                                                            _root_.GebMirror.Metalogic.«Language.mNode»
                                                              (_root_.Geb.Kernel.leaf 8)
                                                              ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                              x2
                                                          else
                                                            _root_.GebMirror.Metalogic.«Language.mNatRec»
                                                              (_root_.GebMirror.Metalogic.«Prelude.at»
                                                                x2
                                                                (_root_.Geb.Kernel.leaf 0))
                                                              (_root_.GebMirror.Metalogic.«Language.subst»
                                                                (_root_.GebMirror.Metalogic.«Language.mD»
                                                                  x1
                                                                  (_root_.Geb.Kernel.leaf 0))
                                                                (fun (x4 : _root_.Geb.Kernel.Tree) =>
                                                                  _root_.GebMirror.Metalogic.«Language.liftS»
                                                                    (_root_.GebMirror.Metalogic.«Machine.envSubst»
                                                                      (_root_.GebMirror.Metalogic.«Prelude.drop»
                                                                        (_root_.Geb.Kernel.leaf 2)
                                                                        x2)
                                                                      (_root_.Geb.Kernel.Const.sub
                                                                        x0
                                                                        (_root_.GebMirror.Metalogic.«Language.mD»
                                                                          x1
                                                                          (_root_.Geb.Kernel.leaf 1))))
                                                                    x4))
                                                              (_root_.GebMirror.Metalogic.«Prelude.at»
                                                                x2
                                                                (_root_.Geb.Kernel.leaf 1))
                                                        else
                                                          if (_root_.Geb.Kernel.Const.eq
                                                            x3
                                                            (_root_.Geb.Kernel.leaf 10)).label ≠ 0 then
                                                            if (_root_.Geb.Kernel.Const.lt
                                                              (_root_.GebMirror.Metalogic.«Prelude.length» x2)
                                                              (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
                                                              _root_.GebMirror.Metalogic.«Language.mNode»
                                                                (_root_.Geb.Kernel.leaf 9)
                                                                ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                                x2
                                                            else
                                                              _root_.GebMirror.Metalogic.«Language.mListRec»
                                                                (_root_.GebMirror.Metalogic.«Prelude.at»
                                                                  x2
                                                                  (_root_.Geb.Kernel.leaf 0))
                                                                (_root_.GebMirror.Metalogic.«Language.subst»
                                                                  (_root_.GebMirror.Metalogic.«Language.mD»
                                                                    x1
                                                                    (_root_.Geb.Kernel.leaf 0))
                                                                  (fun (x4 : _root_.Geb.Kernel.Tree) =>
                                                                    _root_.GebMirror.Metalogic.«Language.liftS»
                                                                      (fun (x5 : _root_.Geb.Kernel.Tree) =>
                                                                        _root_.GebMirror.Metalogic.«Language.liftS»
                                                                          (_root_.GebMirror.Metalogic.«Machine.envSubst»
                                                                            (_root_.GebMirror.Metalogic.«Prelude.drop»
                                                                              (_root_.Geb.Kernel.leaf 2)
                                                                              x2)
                                                                            (_root_.Geb.Kernel.Const.sub
                                                                              x0
                                                                              (_root_.GebMirror.Metalogic.«Language.mD»
                                                                                x1
                                                                                (_root_.Geb.Kernel.leaf 1))))
                                                                          x5)
                                                                      x4))
                                                                (_root_.GebMirror.Metalogic.«Prelude.at»
                                                                  x2
                                                                  (_root_.Geb.Kernel.leaf 1))
                                                          else
                                                            if (_root_.Geb.Kernel.Const.eq
                                                              x3
                                                              (_root_.Geb.Kernel.leaf 11)).label ≠ 0 then
                                                              if (_root_.GebMirror.Metalogic.«Base.isEmpty»
                                                                x2).label ≠ 0 then
                                                                _root_.GebMirror.Metalogic.«Language.mNode»
                                                                  (_root_.Geb.Kernel.leaf 10)
                                                                  (_root_.GebMirror.Metalogic.«Prelude.single»
                                                                    (_root_.GebMirror.Metalogic.«Language.mD»
                                                                      x1
                                                                      (_root_.Geb.Kernel.leaf 0)))
                                                                  x2
                                                              else
                                                                _root_.GebMirror.Metalogic.«Language.mRoseRec»
                                                                  (_root_.GebMirror.Metalogic.«Language.mD»
                                                                    x1
                                                                    (_root_.Geb.Kernel.leaf 0))
                                                                  (_root_.GebMirror.Metalogic.«Language.subst»
                                                                    (_root_.GebMirror.Metalogic.«Language.mD»
                                                                      x1
                                                                      (_root_.Geb.Kernel.leaf 1))
                                                                    (fun (x4 : _root_.Geb.Kernel.Tree) =>
                                                                      _root_.GebMirror.Metalogic.«Language.liftS»
                                                                        (_root_.GebMirror.Metalogic.«Machine.envSubst»
                                                                          (_root_.GebMirror.Metalogic.«Prelude.tail»
                                                                            x2)
                                                                          (_root_.Geb.Kernel.Const.sub
                                                                            x0
                                                                            (_root_.GebMirror.Metalogic.«Language.mD»
                                                                              x1
                                                                              (_root_.Geb.Kernel.leaf 2))))
                                                                        x4))
                                                                  (_root_.GebMirror.Metalogic.«Prelude.at»
                                                                    x2
                                                                    (_root_.Geb.Kernel.leaf 0))
                                                            else
                                                              if (_root_.Geb.Kernel.Const.eq
                                                                x3
                                                                (_root_.Geb.Kernel.leaf 12)).label ≠ 0 then
                                                                _root_.GebMirror.Metalogic.«Language.mNode»
                                                                  (_root_.Geb.Kernel.leaf 11)
                                                                  (_root_.Geb.Kernel.Const.children
                                                                    (_root_.Geb.Kernel.Const.child
                                                                      x1
                                                                      (_root_.Geb.Kernel.leaf 0)))
                                                                  x2
                                                              else
                                                                if (_root_.Geb.Kernel.Const.eq
                                                                  x3
                                                                  (_root_.Geb.Kernel.leaf 13)).label ≠ 0 then
                                                                  _root_.GebMirror.Metalogic.«Language.mNode»
                                                                    (_root_.Geb.Kernel.leaf 12)
                                                                    ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                                    x2
                                                                else
                                                                  if (_root_.Geb.Kernel.Const.eq
                                                                    x3
                                                                    (_root_.Geb.Kernel.leaf 14)).label ≠ 0 then
                                                                    _root_.GebMirror.Metalogic.«Language.subst»
                                                                      (_root_.GebMirror.Metalogic.«Language.mD»
                                                                        x1
                                                                        (_root_.Geb.Kernel.leaf 0))
                                                                      (fun (x4 : _root_.Geb.Kernel.Tree) =>
                                                                        _root_.GebMirror.Metalogic.«Machine.envSubst»
                                                                          x2
                                                                          (_root_.Geb.Kernel.Const.sub
                                                                            x0
                                                                            (_root_.GebMirror.Metalogic.«Language.mD»
                                                                              x1
                                                                              (_root_.Geb.Kernel.leaf 1)))
                                                                          x4)
                                                                  else
                                                                    if (_root_.GebMirror.Metalogic.«Prelude.and»
                                                                      (_root_.Geb.Kernel.Const.eq
                                                                        x3
                                                                        (_root_.Geb.Kernel.leaf 15))
                                                                      (_root_.Geb.Kernel.Const.eq
                                                                        (_root_.GebMirror.Metalogic.«Prelude.length»
                                                                          x2)
                                                                        (_root_.Geb.Kernel.leaf 2))).label ≠ 0 then
                                                                      _root_.GebMirror.Metalogic.«Prelude.at»
                                                                        x2
                                                                        (_root_.Geb.Kernel.leaf 1)
                                                                    else
                                                                      _root_.GebMirror.Metalogic.«Language.mStar»);
    x3

def «Machine.readBack» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.para
      (α := _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Machine.readStep»
          x0
          x2
          (_root_.GebMirror.Metalogic.«Prelude.tail» x3))
      x1;
    x2

def «Machine.varLeaves» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.para
      (α := _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Prelude.and»
          (if (_root_.Geb.Kernel.Const.eq
            (_root_.Geb.Kernel.Const.label x1)
            (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
            _root_.GebMirror.Metalogic.«Base.isEmpty» (_root_.GebMirror.Metalogic.«Prelude.tail» x2)
          else
            _root_.Geb.Kernel.leaf 1)
          (_root_.GebMirror.Metalogic.«Base.allT»
            (fun (x3 : _root_.Geb.Kernel.Tree) => x3)
            (_root_.GebMirror.Metalogic.«Prelude.tail» x2)))
      x0;
    x1

def «Machine.marked» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.some»
      (_root_.Geb.Kernel.Const.node
        (_root_.Geb.Kernel.leaf 0)
        (_root_.GebMirror.Metalogic.«Theory.l2» x0 x1));
    x2

def «Machine.nfTerm» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.child
      x0
      (_root_.Geb.Kernel.leaf 0);
    x1

def «Machine.nfMark» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.child
      x0
      (_root_.Geb.Kernel.leaf 1);
    x1

def «Machine.jobE» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mNode»
      (_root_.Geb.Kernel.leaf 0)
      (_root_.GebMirror.Metalogic.«Theory.l2» x0 x2)
      x1;
    x3

def «Machine.jobW» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mNode»
      (_root_.Geb.Kernel.leaf 1)
      (_root_.GebMirror.Metalogic.«Prelude.single» x0)
      ([] : _root_.List _root_.Geb.Kernel.Tree);
    x1

def «Machine.jobN» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mNode»
      (_root_.Geb.Kernel.leaf 2)
      (_root_.GebMirror.Metalogic.«Theory.l2» x1 x2)
      x0;
    x3

def «Machine.msDone» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mNode»
      (_root_.Geb.Kernel.leaf 0)
      (_root_.GebMirror.Metalogic.«Prelude.single» x0)
      ([] : _root_.List _root_.Geb.Kernel.Tree);
    x1

def «Machine.msTail» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mNode»
      (_root_.Geb.Kernel.leaf 1)
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«Prelude.single» x0);
    x1

def «Machine.msWhnf» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mNode»
      (_root_.Geb.Kernel.leaf 2)
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«Prelude.single» x0);
    x1

def «Machine.bindS» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Prelude.isSome»
      x0).label ≠ 0 then
      x1 (_root_.GebMirror.Metalogic.«Prelude.get» x0)
    else
      _root_.GebMirror.Metalogic.«Machine.msDone» _root_.GebMirror.Metalogic.«Prelude.none»);
    x2

def «Machine.eHasStrict» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.label
                                          x0;
                                        let x2 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mArgs»
                                          x0;
                                        _root_.GebMirror.Metalogic.«Prelude.or»
                                          (_root_.GebMirror.Metalogic.«Prelude.and»
                                            (_root_.GebMirror.Metalogic.«Prelude.or»
                                              (_root_.Geb.Kernel.Const.eq
                                                x1
                                                (_root_.Geb.Kernel.leaf 3))
                                              (_root_.Geb.Kernel.Const.eq
                                                x1
                                                (_root_.Geb.Kernel.leaf 4)))
                                            (_root_.Geb.Kernel.Const.eq
                                              (_root_.GebMirror.Metalogic.«Prelude.length» x2)
                                              (_root_.Geb.Kernel.leaf 1)))
                                          (_root_.GebMirror.Metalogic.«Prelude.or»
                                            (_root_.GebMirror.Metalogic.«Language.mIs»
                                              (_root_.Geb.Kernel.leaf 6)
                                              (_root_.Geb.Kernel.leaf 2)
                                              x0)
                                            (_root_.GebMirror.Metalogic.«Prelude.or»
                                              (_root_.GebMirror.Metalogic.«Prelude.and»
                                                (_root_.GebMirror.Metalogic.«Prelude.or»
                                                  (_root_.Geb.Kernel.Const.eq
                                                    x1
                                                    (_root_.Geb.Kernel.leaf 8))
                                                  (_root_.Geb.Kernel.Const.eq
                                                    x1
                                                    (_root_.Geb.Kernel.leaf 9)))
                                                (_root_.Geb.Kernel.Const.eq
                                                  (_root_.GebMirror.Metalogic.«Prelude.length» x2)
                                                  (_root_.Geb.Kernel.leaf 3)))
                                              (_root_.GebMirror.Metalogic.«Language.mIs»
                                                (_root_.Geb.Kernel.leaf 10)
                                                (_root_.Geb.Kernel.leaf 2)
                                                x0))));
    x1

def «Machine.eKids» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.label
                                   x0;
                                 let x2 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mArgs» x0;
                                 if (_root_.GebMirror.Metalogic.«Prelude.and»
                                   (_root_.GebMirror.Metalogic.«Prelude.or»
                                     (_root_.Geb.Kernel.Const.eq x1 (_root_.Geb.Kernel.leaf 8))
                                     (_root_.Geb.Kernel.Const.eq x1 (_root_.Geb.Kernel.leaf 9)))
                                   (_root_.Geb.Kernel.Const.eq
                                     (_root_.GebMirror.Metalogic.«Prelude.length» x2)
                                     (_root_.Geb.Kernel.leaf 3))).label ≠ 0 then
                                   _root_.GebMirror.Metalogic.«Theory.l2»
                                     (_root_.GebMirror.Metalogic.«Prelude.at» x2 (_root_.Geb.Kernel.leaf 2))
                                     (_root_.GebMirror.Metalogic.«Prelude.at» x2 (_root_.Geb.Kernel.leaf 0))
                                 else
                                   if (_root_.GebMirror.Metalogic.«Language.mIs»
                                     (_root_.Geb.Kernel.leaf 10)
                                     (_root_.Geb.Kernel.leaf 2)
                                     x0).label ≠ 0 then
                                     _root_.GebMirror.Metalogic.«Prelude.single»
                                       (_root_.GebMirror.Metalogic.«Prelude.at» x2 (_root_.Geb.Kernel.leaf 1))
                                   else
                                     x2);
    x1

def «Machine.eDelayed» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Machine.eHasStrict»
      x0).label ≠ 0 then
      _root_.GebMirror.Metalogic.«Prelude.tail» (_root_.GebMirror.Metalogic.«Machine.eKids» x0)
    else
      _root_.GebMirror.Metalogic.«Machine.eKids» x0);
    x1

def «Machine.eStart» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mD»
                                          x0
                                          (_root_.Geb.Kernel.leaf 0);
                                        let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mD»
                                          x0
                                          (_root_.Geb.Kernel.leaf 1);
                                        let x3 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mArgs»
                                          x0;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x1)
                                          (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                                          let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mD»
                                            x1
                                            (_root_.Geb.Kernel.leaf 0);
                                          _root_.GebMirror.Metalogic.«Machine.msDone»
                                            (_root_.GebMirror.Metalogic.«Prelude.some»
                                              (if (_root_.Geb.Kernel.Const.lt
                                                x4
                                                (_root_.GebMirror.Metalogic.«Prelude.length» x3)).label ≠ 0 then
                                                _root_.GebMirror.Metalogic.«Prelude.at» x3 x4
                                              else
                                                _root_.GebMirror.Metalogic.«Machine.freeVar»
                                                  x2
                                                  (_root_.Geb.Kernel.Const.sub
                                                    x4
                                                    (_root_.GebMirror.Metalogic.«Prelude.length» x3))))
                                        else
                                          if (_root_.GebMirror.Metalogic.«Language.mIs»
                                            (_root_.Geb.Kernel.leaf 1)
                                            (_root_.Geb.Kernel.leaf 0)
                                            x1).label ≠ 0 then
                                            _root_.GebMirror.Metalogic.«Machine.msDone»
                                              (_root_.GebMirror.Metalogic.«Prelude.some»
                                                (_root_.GebMirror.Metalogic.«Language.mNode»
                                                  (_root_.Geb.Kernel.leaf 2)
                                                  ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                  ([] : _root_.List _root_.Geb.Kernel.Tree)))
                                          else
                                            if (_root_.GebMirror.Metalogic.«Language.mIs»
                                              (_root_.Geb.Kernel.leaf 5)
                                              (_root_.Geb.Kernel.leaf 1)
                                              x1).label ≠ 0 then
                                              _root_.GebMirror.Metalogic.«Machine.msDone»
                                                (_root_.GebMirror.Metalogic.«Prelude.some»
                                                  (_root_.GebMirror.Metalogic.«Language.mNode»
                                                    (_root_.Geb.Kernel.leaf 4)
                                                    (_root_.GebMirror.Metalogic.«Theory.l3»
                                                      (_root_.GebMirror.Metalogic.«Language.mD»
                                                        x1
                                                        (_root_.Geb.Kernel.leaf 0))
                                                      (_root_.GebMirror.Metalogic.«Language.mArg»
                                                        x1
                                                        (_root_.Geb.Kernel.leaf 0))
                                                      x2)
                                                    x3))
                                            else
                                              _root_.GebMirror.Metalogic.«Language.mNode»
                                                (_root_.Geb.Kernel.leaf 3)
                                                (_root_.GebMirror.Metalogic.«Prelude.single» x0)
                                                (_root_.GebMirror.Metalogic.«Base.mapT»
                                                  (fun (x4 : _root_.Geb.Kernel.Tree) =>
                                                    _root_.GebMirror.Metalogic.«Machine.jobE» x4 x3 x2)
                                                  (_root_.GebMirror.Metalogic.«Machine.eKids» x1)));
    x1

def «Machine.eArgs» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Machine.eHasStrict»
                                          (_root_.GebMirror.Metalogic.«Language.mD»
                                            x0
                                            (_root_.Geb.Kernel.leaf 0));
                                        _root_.GebMirror.Metalogic.«Language.mNode»
                                          (_root_.Geb.Kernel.leaf 4)
                                          (_root_.GebMirror.Metalogic.«Theory.l2»
                                            x0
                                            (if (x2).label ≠ 0 then
                                              _root_.GebMirror.Metalogic.«Prelude.at»
                                                x1
                                                (_root_.Geb.Kernel.leaf 0)
                                            else
                                              _root_.GebMirror.Metalogic.«Prelude.none»))
                                          (_root_.GebMirror.Metalogic.«Base.mapT»
                                            _root_.GebMirror.Metalogic.«Machine.jobW»
                                            (if (x2).label ≠ 0 then
                                              _root_.GebMirror.Metalogic.«Prelude.tail» x1
                                            else
                                              x1)));
    x2

def «Machine.eDelays» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := (let x2 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Machine.eDelayed»
                                   (_root_.GebMirror.Metalogic.«Language.mD» x0 (_root_.Geb.Kernel.leaf 0));
                                 _root_.GebMirror.Metalogic.«Base.mapT»
                                   (fun (x3 : _root_.Geb.Kernel.Tree) =>
                                     _root_.GebMirror.Metalogic.«Machine.delayed»
                                       (_root_.GebMirror.Metalogic.«Prelude.at» x1 x3)
                                       (_root_.GebMirror.Metalogic.«Language.mNode»
                                         (_root_.Geb.Kernel.leaf 14)
                                         (_root_.GebMirror.Metalogic.«Theory.l2»
                                           (_root_.GebMirror.Metalogic.«Prelude.at» x2 x3)
                                           (_root_.GebMirror.Metalogic.«Language.mD»
                                             x0
                                             (_root_.Geb.Kernel.leaf 1)))
                                         (_root_.GebMirror.Metalogic.«Language.mArgs» x0)))
                                   (_root_.GebMirror.Metalogic.«Base.range»
                                     (_root_.GebMirror.Metalogic.«Prelude.length» x2)));
    x2

def «Machine.evalDefn» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree := (let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mD»
                                          x3
                                          (_root_.Geb.Kernel.leaf 0);
                                        let x6 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                          (_root_.GebMirror.Metalogic.«Language.mD»
                                            x3
                                            (_root_.Geb.Kernel.leaf 1));
                                        let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Machine.msDone»
                                          (_root_.GebMirror.Metalogic.«Prelude.some»
                                            (_root_.GebMirror.Metalogic.«Language.mNode»
                                              (_root_.Geb.Kernel.leaf 12)
                                              (_root_.Geb.Kernel.Const.children
                                                (_root_.Geb.Kernel.Const.child
                                                  x3
                                                  (_root_.Geb.Kernel.leaf 0)))
                                              x2));
                                        let x8 : _root_.Geb.Kernel.Tree := (if (x1
                                          x5).label ≠ 0 then
                                          _root_.GebMirror.Metalogic.«Language.bindDL»
                                            (_root_.GebMirror.Metalogic.«$4c616e67756167652f4f446566696e6974696f6e2e6e74684f66»
                                              (_root_.GebMirror.Metalogic.«Language.gDefs» x0)
                                              x5)
                                            _root_.GebMirror.Metalogic.«Language.defLanguage»
                                        else
                                          _root_.GebMirror.Metalogic.«$4c616e67756167652f4f4c4465666e2e6e6f7468696e67»);
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
                                          if (_root_.Geb.Kernel.Const.eq
                                            (_root_.GebMirror.Metalogic.«Prelude.length» x2)
                                            (_root_.GebMirror.Metalogic.«Prelude.length»
                                              (_root_.GebMirror.Metalogic.«Language.ldParams»
                                                x10))).label ≠ 0 then
                                            _root_.GebMirror.Metalogic.«Machine.msTail»
                                              (_root_.GebMirror.Metalogic.«Machine.jobE»
                                                (if (_root_.GebMirror.Metalogic.«Base.isEmpty»
                                                  x6).label ≠ 0 then
                                                  _root_.GebMirror.Metalogic.«Language.ldBody» x10
                                                else
                                                  _root_.GebMirror.Metalogic.«Language.osubst»
                                                    x6
                                                    (_root_.GebMirror.Metalogic.«Language.ldBody» x10))
                                                x2
                                                x4)
                                          else
                                            x7
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x8;
                                          x7);
    x5

def «Machine.eFinal» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree := (let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mD»
                                          x2
                                          (_root_.Geb.Kernel.leaf 0);
                                        let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mD»
                                          x2
                                          (_root_.Geb.Kernel.leaf 1);
                                        let x7 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mArgs»
                                          x2;
                                        let x8 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.label
                                          x5;
                                        let x9 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mArgs»
                                          x5;
                                        if (_root_.GebMirror.Metalogic.«Prelude.and»
                                          (_root_.GebMirror.Metalogic.«Prelude.or»
                                            (_root_.Geb.Kernel.Const.eq
                                              x8
                                              (_root_.Geb.Kernel.leaf 3))
                                            (_root_.Geb.Kernel.Const.eq
                                              x8
                                              (_root_.Geb.Kernel.leaf 4)))
                                          (_root_.Geb.Kernel.Const.eq
                                            (_root_.GebMirror.Metalogic.«Prelude.length» x9)
                                            (_root_.Geb.Kernel.leaf 1))).label ≠ 0 then
                                          _root_.GebMirror.Metalogic.«Machine.msTail»
                                            (_root_.GebMirror.Metalogic.«Machine.jobW»
                                              (_root_.GebMirror.Metalogic.«Base.mapO»
                                                (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                                  _root_.GebMirror.Metalogic.«Language.mNode»
                                                    (if (_root_.Geb.Kernel.Const.eq
                                                      x8
                                                      (_root_.Geb.Kernel.leaf 3)).label ≠ 0 then
                                                      _root_.Geb.Kernel.leaf 7
                                                    else
                                                      _root_.Geb.Kernel.leaf 8)
                                                    ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                    (_root_.GebMirror.Metalogic.«Prelude.single» x10))
                                                x3))
                                        else
                                          if (_root_.GebMirror.Metalogic.«Language.mIs»
                                            (_root_.Geb.Kernel.leaf 6)
                                            (_root_.Geb.Kernel.leaf 2)
                                            x5).label ≠ 0 then
                                            _root_.GebMirror.Metalogic.«Machine.msTail»
                                              (_root_.GebMirror.Metalogic.«Machine.jobW»
                                                (_root_.GebMirror.Metalogic.«Base.mapO»
                                                  (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                                    _root_.GebMirror.Metalogic.«Language.mNode»
                                                      (_root_.Geb.Kernel.leaf 6)
                                                      ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                      (_root_.GebMirror.Metalogic.«Theory.l2»
                                                        x10
                                                        (_root_.GebMirror.Metalogic.«Prelude.at»
                                                          x4
                                                          (_root_.Geb.Kernel.leaf 0))))
                                                  x3))
                                          else
                                            if (_root_.GebMirror.Metalogic.«Prelude.and»
                                              (_root_.GebMirror.Metalogic.«Prelude.or»
                                                (_root_.Geb.Kernel.Const.eq
                                                  x8
                                                  (_root_.Geb.Kernel.leaf 8))
                                                (_root_.Geb.Kernel.Const.eq
                                                  x8
                                                  (_root_.Geb.Kernel.leaf 9)))
                                              (_root_.Geb.Kernel.Const.eq
                                                (_root_.GebMirror.Metalogic.«Prelude.length» x9)
                                                (_root_.Geb.Kernel.leaf 3))).label ≠ 0 then
                                              _root_.GebMirror.Metalogic.«Machine.msTail»
                                                (_root_.GebMirror.Metalogic.«Machine.jobW»
                                                  (_root_.GebMirror.Metalogic.«Base.mapO»
                                                    (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                                      _root_.GebMirror.Metalogic.«Language.mNode»
                                                        (if (_root_.Geb.Kernel.Const.eq
                                                          x8
                                                          (_root_.Geb.Kernel.leaf 8)).label ≠ 0 then
                                                          _root_.Geb.Kernel.leaf 9
                                                        else
                                                          _root_.Geb.Kernel.leaf 10)
                                                        (_root_.GebMirror.Metalogic.«Theory.l2»
                                                          (_root_.GebMirror.Metalogic.«Language.mArg»
                                                            x5
                                                            (_root_.Geb.Kernel.leaf 1))
                                                          x6)
                                                        ((_root_.GebMirror.Metalogic.«Prelude.at»
                                                          x4
                                                          (_root_.Geb.Kernel.leaf 0)) ::
                                                          (x10 :: x7)))
                                                    x3))
                                            else
                                              if (_root_.GebMirror.Metalogic.«Language.mIs»
                                                (_root_.Geb.Kernel.leaf 10)
                                                (_root_.Geb.Kernel.leaf 2)
                                                x5).label ≠ 0 then
                                                _root_.GebMirror.Metalogic.«Machine.msTail»
                                                  (_root_.GebMirror.Metalogic.«Machine.jobW»
                                                    (_root_.GebMirror.Metalogic.«Base.mapO»
                                                      (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                                        _root_.GebMirror.Metalogic.«Language.mNode»
                                                          (_root_.Geb.Kernel.leaf 11)
                                                          (_root_.GebMirror.Metalogic.«Theory.l3»
                                                            (_root_.GebMirror.Metalogic.«Language.mD»
                                                              x5
                                                              (_root_.Geb.Kernel.leaf 0))
                                                            (_root_.GebMirror.Metalogic.«Language.mArg»
                                                              x5
                                                              (_root_.Geb.Kernel.leaf 0))
                                                            x6)
                                                          (x10 :: x7))
                                                      x3))
                                              else
                                                if (_root_.Geb.Kernel.Const.eq
                                                  x8
                                                  (_root_.Geb.Kernel.leaf 11)).label ≠ 0 then
                                                  _root_.GebMirror.Metalogic.«Machine.evalDefn» x0 x1 x4 x5 x6
                                                else
                                                  if (_root_.Geb.Kernel.Const.eq
                                                    x8
                                                    (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
                                                    _root_.GebMirror.Metalogic.«Machine.msDone»
                                                      (_root_.GebMirror.Metalogic.«Prelude.some»
                                                        (_root_.GebMirror.Metalogic.«Language.mNode»
                                                          (_root_.Geb.Kernel.leaf 3)
                                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                          x4))
                                                  else
                                                    if (_root_.Geb.Kernel.Const.eq
                                                      x8
                                                      (_root_.Geb.Kernel.leaf 3)).label ≠ 0 then
                                                      _root_.GebMirror.Metalogic.«Machine.msDone»
                                                        (_root_.GebMirror.Metalogic.«Prelude.some»
                                                          (_root_.GebMirror.Metalogic.«Language.mNode»
                                                            (_root_.Geb.Kernel.leaf 7)
                                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                            x4))
                                                    else
                                                      if (_root_.Geb.Kernel.Const.eq
                                                        x8
                                                        (_root_.Geb.Kernel.leaf 4)).label ≠ 0 then
                                                        _root_.GebMirror.Metalogic.«Machine.msDone»
                                                          (_root_.GebMirror.Metalogic.«Prelude.some»
                                                            (_root_.GebMirror.Metalogic.«Language.mNode»
                                                              (_root_.Geb.Kernel.leaf 8)
                                                              ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                              x4))
                                                      else
                                                        if (_root_.Geb.Kernel.Const.eq
                                                          x8
                                                          (_root_.Geb.Kernel.leaf 6)).label ≠ 0 then
                                                          _root_.GebMirror.Metalogic.«Machine.msDone»
                                                            (_root_.GebMirror.Metalogic.«Prelude.some»
                                                              (_root_.GebMirror.Metalogic.«Language.mNode»
                                                                (_root_.Geb.Kernel.leaf 6)
                                                                ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                                x4))
                                                        else
                                                          if (_root_.Geb.Kernel.Const.eq
                                                            x8
                                                            (_root_.Geb.Kernel.leaf 7)).label ≠ 0 then
                                                            _root_.GebMirror.Metalogic.«Machine.msDone»
                                                              (_root_.GebMirror.Metalogic.«Prelude.some»
                                                                (_root_.GebMirror.Metalogic.«Language.mNode»
                                                                  (_root_.Geb.Kernel.leaf 5)
                                                                  (_root_.Geb.Kernel.Const.children
                                                                    (_root_.Geb.Kernel.Const.child
                                                                      x5
                                                                      (_root_.Geb.Kernel.leaf 0)))
                                                                  x4))
                                                          else
                                                            if (_root_.Geb.Kernel.Const.eq
                                                              x8
                                                              (_root_.Geb.Kernel.leaf 12)).label ≠ 0 then
                                                              _root_.GebMirror.Metalogic.«Machine.msDone»
                                                                (_root_.GebMirror.Metalogic.«Prelude.some»
                                                                  (_root_.GebMirror.Metalogic.«Language.mNode»
                                                                    (_root_.Geb.Kernel.leaf 13)
                                                                    ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                                    x4))
                                                            else
                                                              _root_.GebMirror.Metalogic.«Machine.msDone»
                                                                _root_.GebMirror.Metalogic.«Prelude.none»);
    x5

def «Machine.wStart» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.label
                                          x0;
                                        let x2 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mArgs»
                                          x0;
                                        if (_root_.GebMirror.Metalogic.«Language.mIs»
                                          (_root_.Geb.Kernel.leaf 15)
                                          (_root_.Geb.Kernel.leaf 2)
                                          x0).label ≠ 0 then
                                          let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mArg»
                                            x0
                                            (_root_.Geb.Kernel.leaf 0);
                                          _root_.GebMirror.Metalogic.«Machine.msDone»
                                            (if (_root_.Geb.Kernel.Const.eq
                                              (_root_.Geb.Kernel.Const.label x3)
                                              (_root_.Geb.Kernel.leaf 16)).label ≠ 0 then
                                              _root_.GebMirror.Metalogic.«Prelude.none»
                                            else
                                              _root_.GebMirror.Metalogic.«Prelude.some» x3)
                                        else
                                          if (_root_.GebMirror.Metalogic.«Prelude.or»
                                            (_root_.GebMirror.Metalogic.«Prelude.and»
                                              (_root_.GebMirror.Metalogic.«Prelude.or»
                                                (_root_.Geb.Kernel.Const.eq
                                                  x1
                                                  (_root_.Geb.Kernel.leaf 7))
                                                (_root_.Geb.Kernel.Const.eq
                                                  x1
                                                  (_root_.Geb.Kernel.leaf 8)))
                                              (_root_.Geb.Kernel.Const.eq
                                                (_root_.GebMirror.Metalogic.«Prelude.length» x2)
                                                (_root_.Geb.Kernel.leaf 1)))
                                            (_root_.GebMirror.Metalogic.«Prelude.or»
                                              (_root_.GebMirror.Metalogic.«Language.mIs»
                                                (_root_.Geb.Kernel.leaf 6)
                                                (_root_.Geb.Kernel.leaf 2)
                                                x0)
                                              (_root_.GebMirror.Metalogic.«Prelude.and»
                                                (_root_.Geb.Kernel.Const.eq
                                                  x1
                                                  (_root_.Geb.Kernel.leaf 11))
                                                (_root_.GebMirror.Metalogic.«Base.not»
                                                  (_root_.GebMirror.Metalogic.«Base.isEmpty»
                                                    x2))))).label ≠ 0 then
                                            _root_.GebMirror.Metalogic.«Language.mNode»
                                              (_root_.Geb.Kernel.leaf 5)
                                              (_root_.GebMirror.Metalogic.«Prelude.single» x0)
                                              (_root_.GebMirror.Metalogic.«Prelude.single»
                                                (_root_.GebMirror.Metalogic.«Machine.jobW»
                                                  (_root_.GebMirror.Metalogic.«Prelude.some»
                                                    (_root_.GebMirror.Metalogic.«Prelude.at»
                                                      x2
                                                      (_root_.Geb.Kernel.leaf 0)))))
                                          else
                                            if (_root_.GebMirror.Metalogic.«Prelude.and»
                                              (_root_.GebMirror.Metalogic.«Prelude.or»
                                                (_root_.Geb.Kernel.Const.eq
                                                  x1
                                                  (_root_.Geb.Kernel.leaf 9))
                                                (_root_.Geb.Kernel.Const.eq
                                                  x1
                                                  (_root_.Geb.Kernel.leaf 10)))
                                              (_root_.GebMirror.Metalogic.«Base.not»
                                                (_root_.Geb.Kernel.Const.lt
                                                  (_root_.GebMirror.Metalogic.«Prelude.length» x2)
                                                  (_root_.Geb.Kernel.leaf 2)))).label ≠ 0 then
                                              _root_.GebMirror.Metalogic.«Language.mNode»
                                                (_root_.Geb.Kernel.leaf 5)
                                                (_root_.GebMirror.Metalogic.«Prelude.single» x0)
                                                (_root_.GebMirror.Metalogic.«Prelude.single»
                                                  (_root_.GebMirror.Metalogic.«Machine.jobW»
                                                    (_root_.GebMirror.Metalogic.«Prelude.some»
                                                      (_root_.GebMirror.Metalogic.«Prelude.at»
                                                        x2
                                                        (_root_.Geb.Kernel.leaf 1)))))
                                            else
                                              _root_.GebMirror.Metalogic.«Machine.msDone»
                                                (_root_.GebMirror.Metalogic.«Prelude.some» x0));
    x1

def «Machine.wProj» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Language.mIs»
      (_root_.Geb.Kernel.leaf 3)
      (_root_.Geb.Kernel.leaf 2)
      x1).label ≠ 0 then
      _root_.GebMirror.Metalogic.«Machine.msTail»
        (_root_.GebMirror.Metalogic.«Machine.jobW»
          (_root_.GebMirror.Metalogic.«Prelude.some»
            (_root_.GebMirror.Metalogic.«Language.mArg»
              x1
              (if (_root_.Geb.Kernel.Const.eq
                (_root_.Geb.Kernel.Const.label x0)
                (_root_.Geb.Kernel.leaf 7)).label ≠ 0 then
                _root_.Geb.Kernel.leaf 0
              else
                _root_.Geb.Kernel.leaf 1))))
    else
      _root_.GebMirror.Metalogic.«Machine.msDone»
        (_root_.GebMirror.Metalogic.«Prelude.some»
          (_root_.GebMirror.Metalogic.«Language.mNode»
            (_root_.Geb.Kernel.Const.label x0)
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (_root_.GebMirror.Metalogic.«Prelude.single» x1))));
    x2

def «Machine.wApp» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := (let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mArg»
                                          x1
                                          (_root_.Geb.Kernel.leaf 1);
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x2)
                                          (_root_.Geb.Kernel.leaf 4)).label ≠ 0 then
                                          _root_.GebMirror.Metalogic.«Machine.msWhnf»
                                            (_root_.GebMirror.Metalogic.«Machine.jobE»
                                              (_root_.GebMirror.Metalogic.«Language.mD»
                                                x2
                                                (_root_.Geb.Kernel.leaf 1))
                                              (x3 :: (_root_.GebMirror.Metalogic.«Language.mArgs» x2))
                                              (_root_.GebMirror.Metalogic.«Language.mD»
                                                x2
                                                (_root_.Geb.Kernel.leaf 2)))
                                        else
                                          if (_root_.GebMirror.Metalogic.«Prelude.and»
                                            (_root_.GebMirror.Metalogic.«Language.mIs»
                                              (_root_.Geb.Kernel.leaf 5)
                                              (_root_.Geb.Kernel.leaf 1)
                                              x2)
                                            (_root_.GebMirror.Metalogic.«Derivation.primIs»
                                              x0
                                              (_root_.GebMirror.Metalogic.«Language.mD»
                                                x2
                                                (_root_.Geb.Kernel.leaf 0))
                                              _root_.GebMirror.Metalogic.«Derivation.casePrim»)).label ≠ 0 then
                                            _root_.GebMirror.Metalogic.«Language.mNode»
                                              (_root_.Geb.Kernel.leaf 6)
                                              (_root_.GebMirror.Metalogic.«Prelude.single» x2)
                                              (_root_.GebMirror.Metalogic.«Prelude.single»
                                                (_root_.GebMirror.Metalogic.«Machine.jobW»
                                                  (_root_.GebMirror.Metalogic.«Prelude.some» x3)))
                                          else
                                            _root_.GebMirror.Metalogic.«Machine.msDone»
                                              (_root_.GebMirror.Metalogic.«Prelude.some»
                                                (_root_.GebMirror.Metalogic.«Language.mNode»
                                                  (_root_.Geb.Kernel.leaf 6)
                                                  ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                  (_root_.GebMirror.Metalogic.«Theory.l2» x2 x3))));
    x3

def «Machine.wCase» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Prelude.and»
      (_root_.GebMirror.Metalogic.«Language.mIs»
        (_root_.Geb.Kernel.leaf 5)
        (_root_.Geb.Kernel.leaf 1)
        x2)
      (_root_.GebMirror.Metalogic.«Prelude.or»
        (_root_.GebMirror.Metalogic.«Derivation.primIs»
          x0
          (_root_.GebMirror.Metalogic.«Language.mD» x2 (_root_.Geb.Kernel.leaf 0))
          _root_.GebMirror.Metalogic.«Derivation.inlPrim»)
        (_root_.GebMirror.Metalogic.«Derivation.primIs»
          x0
          (_root_.GebMirror.Metalogic.«Language.mD» x2 (_root_.Geb.Kernel.leaf 0))
          _root_.GebMirror.Metalogic.«Derivation.inrPrim»))).label ≠ 0 then
      _root_.GebMirror.Metalogic.«Language.mNode»
        (_root_.Geb.Kernel.leaf 7)
        (_root_.GebMirror.Metalogic.«Theory.l2» x1 x2)
        (_root_.GebMirror.Metalogic.«Prelude.single»
          (_root_.GebMirror.Metalogic.«Machine.jobW»
            (_root_.GebMirror.Metalogic.«Prelude.some»
              (_root_.GebMirror.Metalogic.«Language.mArg» x1 (_root_.Geb.Kernel.leaf 0)))))
    else
      _root_.GebMirror.Metalogic.«Machine.msDone»
        (_root_.GebMirror.Metalogic.«Prelude.some»
          (_root_.GebMirror.Metalogic.«Language.mNode»
            (_root_.Geb.Kernel.leaf 6)
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (_root_.GebMirror.Metalogic.«Theory.l2» x1 x2))));
    x3

def «Machine.wCase2» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Language.mIs»
      (_root_.Geb.Kernel.leaf 3)
      (_root_.Geb.Kernel.leaf 2)
      x3).label ≠ 0 then
      _root_.GebMirror.Metalogic.«Machine.msTail»
        (_root_.GebMirror.Metalogic.«Machine.jobW»
          (_root_.GebMirror.Metalogic.«Prelude.some»
            (_root_.GebMirror.Metalogic.«Language.mNode»
              (_root_.Geb.Kernel.leaf 6)
              ([] : _root_.List _root_.Geb.Kernel.Tree)
              (_root_.GebMirror.Metalogic.«Theory.l2»
                (_root_.GebMirror.Metalogic.«Language.mArg»
                  x3
                  (if (_root_.GebMirror.Metalogic.«Derivation.primIs»
                    x0
                    (_root_.GebMirror.Metalogic.«Language.mD» x2 (_root_.Geb.Kernel.leaf 0))
                    _root_.GebMirror.Metalogic.«Derivation.inlPrim»).label ≠ 0 then
                    _root_.Geb.Kernel.leaf 0
                  else
                    _root_.Geb.Kernel.leaf 1))
                (_root_.GebMirror.Metalogic.«Language.mArg» x2 (_root_.Geb.Kernel.leaf 0))))))
    else
      _root_.GebMirror.Metalogic.«Machine.msDone»
        (_root_.GebMirror.Metalogic.«Prelude.some»
          (_root_.GebMirror.Metalogic.«Language.mNode»
            (_root_.Geb.Kernel.leaf 6)
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (_root_.GebMirror.Metalogic.«Theory.l2» x1 x2))));
    x4

def «Machine.foldStuck» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Machine.msDone»
      (_root_.GebMirror.Metalogic.«Prelude.some»
        (_root_.GebMirror.Metalogic.«Language.mNode»
          (_root_.Geb.Kernel.Const.label x0)
          (_root_.Geb.Kernel.Const.children
            (_root_.Geb.Kernel.Const.child x0 (_root_.Geb.Kernel.leaf 0)))
          ((_root_.GebMirror.Metalogic.«Language.mArg» x0 (_root_.Geb.Kernel.leaf 0)) ::
            (x1 ::
              (_root_.GebMirror.Metalogic.«Prelude.drop»
                (_root_.Geb.Kernel.leaf 2)
                (_root_.GebMirror.Metalogic.«Language.mArgs» x0))))));
    x2

def «Machine.roseStuck» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Machine.msDone»
      (_root_.GebMirror.Metalogic.«Prelude.some»
        (_root_.GebMirror.Metalogic.«Language.mNode»
          (_root_.Geb.Kernel.leaf 11)
          (_root_.Geb.Kernel.Const.children
            (_root_.Geb.Kernel.Const.child x0 (_root_.Geb.Kernel.leaf 0)))
          (x1 ::
            (_root_.GebMirror.Metalogic.«Prelude.tail»
              (_root_.GebMirror.Metalogic.«Language.mArgs» x0)))));
    x2

def «Machine.wRecOf» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mNode»
      (_root_.Geb.Kernel.leaf 11)
      (_root_.GebMirror.Metalogic.«Theory.l5»
        x0
        x1
        x2
        x3
        (_root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 0) x4))
      (_root_.GebMirror.Metalogic.«Prelude.single»
        (_root_.GebMirror.Metalogic.«Machine.jobW» (_root_.GebMirror.Metalogic.«Prelude.some» x2)));
    x5

def «Machine.wRec» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Machine.delayed»
                                          x1
                                          (_root_.GebMirror.Metalogic.«Prelude.at»
                                            x0
                                            (_root_.Geb.Kernel.leaf 2));
                                        let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.at»
                                          x0
                                          (_root_.Geb.Kernel.leaf 3);
                                        _root_.GebMirror.Metalogic.«Machine.msWhnf»
                                          (_root_.GebMirror.Metalogic.«Machine.jobE»
                                            (_root_.GebMirror.Metalogic.«Prelude.at»
                                              x0
                                              (_root_.Geb.Kernel.leaf 0))
                                            ((if (_root_.GebMirror.Metalogic.«Prelude.isSome» x3).label ≠ 0 then
                                              _root_.GebMirror.Metalogic.«Language.mNode»
                                                (_root_.Geb.Kernel.leaf 3)
                                                ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                (_root_.GebMirror.Metalogic.«Theory.l2»
                                                  (_root_.GebMirror.Metalogic.«Prelude.get» x3)
                                                  x2)
                                            else
                                              x2) ::
                                              (_root_.Geb.Kernel.Const.children
                                                (_root_.GebMirror.Metalogic.«Prelude.at»
                                                  x0
                                                  (_root_.Geb.Kernel.leaf 4))))
                                            (_root_.GebMirror.Metalogic.«Prelude.at»
                                              x0
                                              (_root_.Geb.Kernel.leaf 1))));
    x2

def «Machine.wBase» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Language.mIs»
      (_root_.Geb.Kernel.leaf 2)
      (_root_.Geb.Kernel.leaf 0)
      x2).label ≠ 0 then
      _root_.GebMirror.Metalogic.«Machine.msTail»
        (_root_.GebMirror.Metalogic.«Machine.jobW»
          (_root_.GebMirror.Metalogic.«Prelude.some»
            (_root_.GebMirror.Metalogic.«Language.mArg» x0 (_root_.Geb.Kernel.leaf 0))))
    else
      _root_.GebMirror.Metalogic.«Machine.foldStuck» x0 x1);
    x3

def «Machine.wNat» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Prelude.and»
      (_root_.GebMirror.Metalogic.«Language.mIs»
        (_root_.Geb.Kernel.leaf 5)
        (_root_.Geb.Kernel.leaf 1)
        x2)
      (_root_.GebMirror.Metalogic.«Base.isEmpty»
        (_root_.Geb.Kernel.Const.children
          (_root_.GebMirror.Metalogic.«Language.mD»
            x2
            (_root_.Geb.Kernel.leaf 1))))).label ≠ 0 then
      let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mArg»
        x2
        (_root_.Geb.Kernel.leaf 0);
      if (_root_.GebMirror.Metalogic.«Derivation.primIs»
        x0
        (_root_.GebMirror.Metalogic.«Language.mD» x2 (_root_.Geb.Kernel.leaf 0))
        _root_.GebMirror.Metalogic.«Derivation.zeroPrim»).label ≠ 0 then
        _root_.GebMirror.Metalogic.«Language.mNode»
          (_root_.Geb.Kernel.leaf 8)
          (_root_.GebMirror.Metalogic.«Theory.l2» x1 x2)
          (_root_.GebMirror.Metalogic.«Prelude.single»
            (_root_.GebMirror.Metalogic.«Machine.jobW» (_root_.GebMirror.Metalogic.«Prelude.some» x3)))
      else
        if (_root_.GebMirror.Metalogic.«Derivation.primIs»
          x0
          (_root_.GebMirror.Metalogic.«Language.mD» x2 (_root_.Geb.Kernel.leaf 0))
          _root_.GebMirror.Metalogic.«Derivation.succPrim»).label ≠ 0 then
          _root_.GebMirror.Metalogic.«Machine.wRecOf»
            (_root_.GebMirror.Metalogic.«Language.mD» x1 (_root_.Geb.Kernel.leaf 0))
            (_root_.GebMirror.Metalogic.«Language.mD» x1 (_root_.Geb.Kernel.leaf 1))
            (_root_.GebMirror.Metalogic.«Language.mNode»
              (_root_.Geb.Kernel.leaf 9)
              (_root_.Geb.Kernel.Const.children
                (_root_.Geb.Kernel.Const.child x1 (_root_.Geb.Kernel.leaf 0)))
              ((_root_.GebMirror.Metalogic.«Language.mArg» x1 (_root_.Geb.Kernel.leaf 0)) ::
                (x3 ::
                  (_root_.GebMirror.Metalogic.«Prelude.drop»
                    (_root_.Geb.Kernel.leaf 2)
                    (_root_.GebMirror.Metalogic.«Language.mArgs» x1)))))
            _root_.GebMirror.Metalogic.«Prelude.none»
            (_root_.GebMirror.Metalogic.«Prelude.drop»
              (_root_.Geb.Kernel.leaf 2)
              (_root_.GebMirror.Metalogic.«Language.mArgs» x1))
        else
          _root_.GebMirror.Metalogic.«Machine.foldStuck» x1 x2
    else
      _root_.GebMirror.Metalogic.«Machine.foldStuck» x1 x2);
    x3

def «Machine.wList» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Prelude.and»
      (_root_.GebMirror.Metalogic.«Language.mIs»
        (_root_.Geb.Kernel.leaf 5)
        (_root_.Geb.Kernel.leaf 1)
        x2)
      (_root_.Geb.Kernel.Const.eq
        (_root_.GebMirror.Metalogic.«Prelude.length»
          (_root_.Geb.Kernel.Const.children
            (_root_.GebMirror.Metalogic.«Language.mD» x2 (_root_.Geb.Kernel.leaf 1))))
        (_root_.Geb.Kernel.leaf 1))).label ≠ 0 then
      let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mArg»
        x2
        (_root_.Geb.Kernel.leaf 0);
      if (_root_.GebMirror.Metalogic.«Derivation.primIs»
        x0
        (_root_.GebMirror.Metalogic.«Language.mD» x2 (_root_.Geb.Kernel.leaf 0))
        _root_.GebMirror.Metalogic.«Derivation.nilPrim»).label ≠ 0 then
        _root_.GebMirror.Metalogic.«Language.mNode»
          (_root_.Geb.Kernel.leaf 8)
          (_root_.GebMirror.Metalogic.«Theory.l2» x1 x2)
          (_root_.GebMirror.Metalogic.«Prelude.single»
            (_root_.GebMirror.Metalogic.«Machine.jobW» (_root_.GebMirror.Metalogic.«Prelude.some» x3)))
      else
        if (_root_.GebMirror.Metalogic.«Derivation.primIs»
          x0
          (_root_.GebMirror.Metalogic.«Language.mD» x2 (_root_.Geb.Kernel.leaf 0))
          _root_.GebMirror.Metalogic.«Derivation.consPrim»).label ≠ 0 then
          _root_.GebMirror.Metalogic.«Language.mNode»
            (_root_.Geb.Kernel.leaf 9)
            (_root_.GebMirror.Metalogic.«Theory.l2» x1 x2)
            (_root_.GebMirror.Metalogic.«Prelude.single»
              (_root_.GebMirror.Metalogic.«Machine.jobW» (_root_.GebMirror.Metalogic.«Prelude.some» x3)))
        else
          _root_.GebMirror.Metalogic.«Machine.foldStuck» x1 x2
    else
      _root_.GebMirror.Metalogic.«Machine.foldStuck» x1 x2);
    x3

def «Machine.wCons» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Language.mIs»
      (_root_.Geb.Kernel.leaf 3)
      (_root_.Geb.Kernel.leaf 2)
      x2).label ≠ 0 then
      let x3 : _root_.List
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.drop»
        (_root_.Geb.Kernel.leaf 2)
        (_root_.GebMirror.Metalogic.«Language.mArgs» x0);
      _root_.GebMirror.Metalogic.«Machine.wRecOf»
        (_root_.GebMirror.Metalogic.«Language.mD» x0 (_root_.Geb.Kernel.leaf 0))
        (_root_.GebMirror.Metalogic.«Language.mD» x0 (_root_.Geb.Kernel.leaf 1))
        (_root_.GebMirror.Metalogic.«Language.mNode»
          (_root_.Geb.Kernel.leaf 10)
          (_root_.Geb.Kernel.Const.children
            (_root_.Geb.Kernel.Const.child x0 (_root_.Geb.Kernel.leaf 0)))
          ((_root_.GebMirror.Metalogic.«Language.mArg» x0 (_root_.Geb.Kernel.leaf 0)) ::
            ((_root_.GebMirror.Metalogic.«Language.mArg» x2 (_root_.Geb.Kernel.leaf 1)) ::
              x3)))
        _root_.GebMirror.Metalogic.«Prelude.none»
        ((_root_.GebMirror.Metalogic.«Language.mArg» x2 (_root_.Geb.Kernel.leaf 0)) :: x3)
    else
      _root_.GebMirror.Metalogic.«Machine.foldStuck» x0 x1);
    x3

def «Machine.wRose» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Prelude.and»
      (_root_.GebMirror.Metalogic.«Language.mIs»
        (_root_.Geb.Kernel.leaf 5)
        (_root_.Geb.Kernel.leaf 1)
        x4)
      (_root_.GebMirror.Metalogic.«Prelude.and»
        (_root_.GebMirror.Metalogic.«Prelude.or»
          (_root_.GebMirror.Metalogic.«Derivation.primIs»
            x0
            (_root_.GebMirror.Metalogic.«Language.mD» x4 (_root_.Geb.Kernel.leaf 0))
            _root_.GebMirror.Metalogic.«Derivation.nodePrim»)
          (_root_.GebMirror.Metalogic.«Derivation.primIs»
            x0
            (_root_.GebMirror.Metalogic.«Language.mD» x4 (_root_.Geb.Kernel.leaf 0))
            _root_.GebMirror.Metalogic.«Derivation.lnodePrim»))
        (_root_.GebMirror.Metalogic.«Prelude.and»
          (_root_.GebMirror.Metalogic.«Derivation.primIs»
            x0
            x1
            _root_.GebMirror.Metalogic.«Derivation.nilPrim»)
          (_root_.GebMirror.Metalogic.«Derivation.primIs»
            x0
            x2
            _root_.GebMirror.Metalogic.«Derivation.consPrim»)))).label ≠ 0 then
      _root_.GebMirror.Metalogic.«Language.mNode»
        (_root_.Geb.Kernel.leaf 10)
        (_root_.GebMirror.Metalogic.«Theory.l2» x3 x4)
        (_root_.GebMirror.Metalogic.«Prelude.single»
          (_root_.GebMirror.Metalogic.«Machine.jobW»
            (_root_.GebMirror.Metalogic.«Prelude.some»
              (_root_.GebMirror.Metalogic.«Language.mArg» x4 (_root_.Geb.Kernel.leaf 0)))))
    else
      _root_.GebMirror.Metalogic.«Machine.roseStuck» x3 x4);
    x5

def «Machine.wRose2» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Language.mIs»
      (_root_.Geb.Kernel.leaf 3)
      (_root_.Geb.Kernel.leaf 2)
      x4).label ≠ 0 then
      let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mD»
        x2
        (_root_.Geb.Kernel.leaf 0);
      let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mD»
        x2
        (_root_.Geb.Kernel.leaf 1);
      let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mD»
        x2
        (_root_.Geb.Kernel.leaf 2);
      let x8 : _root_.List
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.tail»
        (_root_.GebMirror.Metalogic.«Language.mArgs» x2);
      _root_.GebMirror.Metalogic.«Machine.wRecOf»
        x6
        x7
        (_root_.GebMirror.Metalogic.«Language.mNode»
          (_root_.Geb.Kernel.leaf 10)
          (_root_.GebMirror.Metalogic.«Theory.l2»
            (_root_.GebMirror.Metalogic.«Language.mArr»
              x1
              (_root_.GebMirror.Metalogic.«Prelude.single» x5)
              (_root_.GebMirror.Metalogic.«Language.mPair»
                (_root_.GebMirror.Metalogic.«Language.mRoseRec»
                  x5
                  (_root_.GebMirror.Metalogic.«Derivation.weakenStep2» x6)
                  (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 1)))
                (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))))
            x7)
          ((_root_.GebMirror.Metalogic.«Language.mNode»
            (_root_.Geb.Kernel.leaf 5)
            (_root_.GebMirror.Metalogic.«Theory.l2»
              x0
              (_root_.Geb.Kernel.Const.node
                (_root_.Geb.Kernel.leaf 0)
                (_root_.GebMirror.Metalogic.«Prelude.single» x5)))
            (_root_.GebMirror.Metalogic.«Prelude.single»
              (_root_.GebMirror.Metalogic.«Language.mNode»
                (_root_.Geb.Kernel.leaf 2)
                ([] : _root_.List _root_.Geb.Kernel.Tree)
                ([] : _root_.List _root_.Geb.Kernel.Tree)))) ::
            ((_root_.GebMirror.Metalogic.«Language.mArg» x4 (_root_.Geb.Kernel.leaf 1)) ::
              x8)))
        (_root_.GebMirror.Metalogic.«Prelude.some»
          (_root_.GebMirror.Metalogic.«Language.mArg» x4 (_root_.Geb.Kernel.leaf 0)))
        x8
    else
      _root_.GebMirror.Metalogic.«Machine.roseStuck» x2 x3);
    x5

def «Machine.wHead» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree := (let x5 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.label
                                          x3;
                                        if (_root_.GebMirror.Metalogic.«Prelude.or»
                                          (_root_.Geb.Kernel.Const.eq x5 (_root_.Geb.Kernel.leaf 7))
                                          (_root_.Geb.Kernel.Const.eq
                                            x5
                                            (_root_.Geb.Kernel.leaf 8))).label ≠ 0 then
                                          _root_.GebMirror.Metalogic.«Machine.wProj» x3 x4
                                        else
                                          if (_root_.Geb.Kernel.Const.eq
                                            x5
                                            (_root_.Geb.Kernel.leaf 6)).label ≠ 0 then
                                            _root_.GebMirror.Metalogic.«Machine.wApp» x0 x3 x4
                                          else
                                            if (_root_.Geb.Kernel.Const.eq
                                              x5
                                              (_root_.Geb.Kernel.leaf 9)).label ≠ 0 then
                                              _root_.GebMirror.Metalogic.«Machine.wNat» x0 x3 x4
                                            else
                                              if (_root_.Geb.Kernel.Const.eq
                                                x5
                                                (_root_.Geb.Kernel.leaf 10)).label ≠ 0 then
                                                _root_.GebMirror.Metalogic.«Machine.wList» x0 x3 x4
                                              else
                                                _root_.GebMirror.Metalogic.«Machine.wRose» x0 x1 x2 x3 x4);
    x5

def «Machine.nRenorm» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mNode»
      (_root_.Geb.Kernel.leaf 17)
      (_root_.GebMirror.Metalogic.«Theory.l2»
        (_root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 0) x0)
        x1)
      (_root_.GebMirror.Metalogic.«Prelude.single»
        (_root_.GebMirror.Metalogic.«Machine.jobE»
          x2
          ([] : _root_.List _root_.Geb.Kernel.Tree)
          x1));
    x3

def «Machine.nPost» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree) =>
    let x6 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Prelude.and»
      x5
      (_root_.GebMirror.Metalogic.«Prelude.and»
        (_root_.Geb.Kernel.Const.lt
          (_root_.Geb.Kernel.leaf 5)
          (_root_.Geb.Kernel.Const.label x3))
        (_root_.Geb.Kernel.Const.lt
          (_root_.Geb.Kernel.Const.label x3)
          (_root_.Geb.Kernel.leaf 12)))).label ≠ 0 then
      _root_.GebMirror.Metalogic.«Machine.nRenorm» x1 x2 x4
    else
      let x6 : _root_.Geb.Kernel.Tree := x0 x1 x2 x4;
      if (_root_.GebMirror.Metalogic.«Prelude.and»
        (_root_.GebMirror.Metalogic.«Prelude.isSome» x6)
        (_root_.GebMirror.Metalogic.«Machine.varLeaves»
          (_root_.GebMirror.Metalogic.«Prelude.get» x6))).label ≠ 0 then
        _root_.GebMirror.Metalogic.«Machine.nRenorm»
          x1
          x2
          (_root_.GebMirror.Metalogic.«Prelude.get» x6)
      else
        _root_.GebMirror.Metalogic.«Machine.msDone»
          (_root_.GebMirror.Metalogic.«Machine.marked» x4 x5));
    x6

def «Machine.nNode» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.label
                                          x3;
                                        let x5 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mArgs»
                                          x3;
                                        let x6 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Theory.l3»
                                          (_root_.Geb.Kernel.Const.node
                                            (_root_.Geb.Kernel.leaf 0)
                                            x1)
                                          x2
                                          x3;
                                        if (_root_.GebMirror.Metalogic.«Prelude.and»
                                          (_root_.GebMirror.Metalogic.«Prelude.or»
                                            (_root_.Geb.Kernel.Const.eq
                                              x4
                                              (_root_.Geb.Kernel.leaf 9))
                                            (_root_.Geb.Kernel.Const.eq
                                              x4
                                              (_root_.Geb.Kernel.leaf 10)))
                                          (_root_.GebMirror.Metalogic.«Base.not»
                                            (_root_.Geb.Kernel.Const.lt
                                              (_root_.GebMirror.Metalogic.«Prelude.length» x5)
                                              (_root_.Geb.Kernel.leaf 2)))).label ≠ 0 then
                                          _root_.GebMirror.Metalogic.«Language.mNode»
                                            (_root_.Geb.Kernel.leaf 13)
                                            x6
                                            (_root_.GebMirror.Metalogic.«Theory.l2»
                                              (_root_.GebMirror.Metalogic.«Machine.jobN»
                                                x1
                                                x2
                                                (_root_.GebMirror.Metalogic.«Prelude.some»
                                                  (_root_.GebMirror.Metalogic.«Prelude.at»
                                                    x5
                                                    (_root_.Geb.Kernel.leaf 0))))
                                              (_root_.GebMirror.Metalogic.«Machine.jobN»
                                                x1
                                                x2
                                                (_root_.GebMirror.Metalogic.«Prelude.some»
                                                  (_root_.GebMirror.Metalogic.«Prelude.at»
                                                    x5
                                                    (_root_.Geb.Kernel.leaf 1)))))
                                        else
                                          if (_root_.GebMirror.Metalogic.«Prelude.and»
                                            (_root_.Geb.Kernel.Const.eq
                                              x4
                                              (_root_.Geb.Kernel.leaf 11))
                                            (_root_.GebMirror.Metalogic.«Base.not»
                                              (_root_.GebMirror.Metalogic.«Base.isEmpty» x5))).label ≠ 0 then
                                            _root_.GebMirror.Metalogic.«Language.mNode»
                                              (_root_.Geb.Kernel.leaf 13)
                                              x6
                                              (_root_.GebMirror.Metalogic.«Prelude.single»
                                                (_root_.GebMirror.Metalogic.«Machine.jobN»
                                                  x1
                                                  x2
                                                  (_root_.GebMirror.Metalogic.«Prelude.some»
                                                    (_root_.GebMirror.Metalogic.«Prelude.at»
                                                      x5
                                                      (_root_.Geb.Kernel.leaf 0)))))
                                          else
                                            if (_root_.Geb.Kernel.Const.eq
                                              x4
                                              (_root_.Geb.Kernel.leaf 4)).label ≠ 0 then
                                              _root_.GebMirror.Metalogic.«Language.mNode»
                                                (_root_.Geb.Kernel.leaf 14)
                                                (_root_.GebMirror.Metalogic.«Theory.l6»
                                                  (_root_.Geb.Kernel.Const.node
                                                    (_root_.Geb.Kernel.leaf 0)
                                                    x1)
                                                  x2
                                                  x3
                                                  (_root_.Geb.Kernel.Const.node
                                                    (_root_.Geb.Kernel.leaf 0)
                                                    ((_root_.GebMirror.Metalogic.«Language.mD»
                                                      x3
                                                      (_root_.Geb.Kernel.leaf 0)) ::
                                                      x1))
                                                  (_root_.Geb.Kernel.Const.add
                                                    x2
                                                    (_root_.Geb.Kernel.leaf 1))
                                                  (_root_.Geb.Kernel.Const.node
                                                    (_root_.Geb.Kernel.leaf 0)
                                                    ([] : _root_.List _root_.Geb.Kernel.Tree)))
                                                (_root_.GebMirror.Metalogic.«Prelude.single»
                                                  (_root_.GebMirror.Metalogic.«Machine.jobE»
                                                    (_root_.GebMirror.Metalogic.«Language.mD»
                                                      x3
                                                      (_root_.Geb.Kernel.leaf 1))
                                                    ((_root_.GebMirror.Metalogic.«Machine.level» x2) :: x5)
                                                    (_root_.GebMirror.Metalogic.«Language.mD»
                                                      x3
                                                      (_root_.Geb.Kernel.leaf 2))))
                                            else
                                              if (_root_.GebMirror.Metalogic.«Prelude.or»
                                                (_root_.Geb.Kernel.Const.lt
                                                  x4
                                                  (_root_.Geb.Kernel.leaf 4))
                                                (_root_.GebMirror.Metalogic.«Prelude.or»
                                                  (_root_.GebMirror.Metalogic.«Prelude.and»
                                                    (_root_.Geb.Kernel.Const.lt
                                                      (_root_.Geb.Kernel.leaf 4)
                                                      x4)
                                                    (_root_.Geb.Kernel.Const.lt
                                                      x4
                                                      (_root_.Geb.Kernel.leaf 9)))
                                                  (_root_.GebMirror.Metalogic.«Prelude.or»
                                                    (_root_.Geb.Kernel.Const.eq
                                                      x4
                                                      (_root_.Geb.Kernel.leaf 12))
                                                    (_root_.Geb.Kernel.Const.eq
                                                      x4
                                                      (_root_.Geb.Kernel.leaf 13))))).label ≠ 0 then
                                                _root_.GebMirror.Metalogic.«Language.mNode»
                                                  (_root_.Geb.Kernel.leaf 16)
                                                  x6
                                                  (_root_.GebMirror.Metalogic.«Base.mapT»
                                                    (fun (x7 : _root_.Geb.Kernel.Tree) =>
                                                      _root_.GebMirror.Metalogic.«Machine.jobN»
                                                        x1
                                                        x2
                                                        (_root_.GebMirror.Metalogic.«Prelude.some» x7))
                                                    x5)
                                              else
                                                if (_root_.Geb.Kernel.Const.eq
                                                  x4
                                                  (_root_.Geb.Kernel.leaf 16)).label ≠ 0 then
                                                  _root_.GebMirror.Metalogic.«Machine.msDone»
                                                    _root_.GebMirror.Metalogic.«Prelude.none»
                                                else
                                                  _root_.GebMirror.Metalogic.«Machine.nPost»
                                                    x0
                                                    x1
                                                    x2
                                                    x3
                                                    (_root_.GebMirror.Metalogic.«Machine.readBack» x2 x3)
                                                    (_root_.Geb.Kernel.leaf 0));
    x4

def «Machine.nFold» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x6 : _root_.Geb.Kernel.Tree := (let x6 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mArgs»
                                          x4;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x4)
                                          (_root_.Geb.Kernel.leaf 11)).label ≠ 0 then
                                          _root_.GebMirror.Metalogic.«Machine.bindS»
                                            (_root_.GebMirror.Metalogic.«Prelude.at»
                                              x5
                                              (_root_.Geb.Kernel.leaf 0))
                                            (fun (x7 : _root_.Geb.Kernel.Tree) =>
                                              _root_.GebMirror.Metalogic.«Machine.bindS»
                                                (_root_.GebMirror.Metalogic.«Base.bindO»
                                                  (_root_.GebMirror.Metalogic.«Derivation.typeIn»
                                                    x0
                                                    x1
                                                    x2
                                                    (_root_.GebMirror.Metalogic.«Machine.nfTerm» x7))
                                                  _root_.GebMirror.Metalogic.«Language.roseLabel»)
                                                (fun (x8 : _root_.Geb.Kernel.Tree) =>
                                                  _root_.GebMirror.Metalogic.«Language.mNode»
                                                    (_root_.Geb.Kernel.leaf 14)
                                                    (_root_.GebMirror.Metalogic.«Theory.l6»
                                                      (_root_.Geb.Kernel.Const.node
                                                        (_root_.Geb.Kernel.leaf 0)
                                                        x2)
                                                      x3
                                                      x4
                                                      (_root_.Geb.Kernel.Const.node
                                                        (_root_.Geb.Kernel.leaf 0)
                                                        ((_root_.GebMirror.Metalogic.«Theory.prod»
                                                          x8
                                                          (_root_.GebMirror.Metalogic.«Theory.list»
                                                            (_root_.GebMirror.Metalogic.«Language.mD»
                                                              x4
                                                              (_root_.Geb.Kernel.leaf 0)))) ::
                                                          x2))
                                                      (_root_.Geb.Kernel.Const.add
                                                        x3
                                                        (_root_.Geb.Kernel.leaf 1))
                                                      (_root_.Geb.Kernel.Const.node
                                                        (_root_.Geb.Kernel.leaf 0)
                                                        (_root_.GebMirror.Metalogic.«Theory.l2»
                                                          (_root_.GebMirror.Metalogic.«Machine.nfTerm» x7)
                                                          (_root_.GebMirror.Metalogic.«Machine.nfMark» x7))))
                                                    (_root_.GebMirror.Metalogic.«Prelude.single»
                                                      (_root_.GebMirror.Metalogic.«Machine.jobE»
                                                        (_root_.GebMirror.Metalogic.«Language.mD»
                                                          x4
                                                          (_root_.Geb.Kernel.leaf 1))
                                                        ((_root_.GebMirror.Metalogic.«Machine.level» x3) ::
                                                          (_root_.GebMirror.Metalogic.«Prelude.tail» x6))
                                                        (_root_.GebMirror.Metalogic.«Language.mD»
                                                          x4
                                                          (_root_.Geb.Kernel.leaf 2))))))
                                        else
                                          _root_.GebMirror.Metalogic.«Machine.bindS»
                                            (_root_.GebMirror.Metalogic.«Prelude.at»
                                              x5
                                              (_root_.Geb.Kernel.leaf 0))
                                            (fun (x7 : _root_.Geb.Kernel.Tree) =>
                                              _root_.GebMirror.Metalogic.«Machine.bindS»
                                                (_root_.GebMirror.Metalogic.«Prelude.at»
                                                  x5
                                                  (_root_.Geb.Kernel.leaf 1))
                                                (fun (x8 : _root_.Geb.Kernel.Tree) =>
                                                  _root_.GebMirror.Metalogic.«Machine.bindS»
                                                    (_root_.GebMirror.Metalogic.«Derivation.typeIn»
                                                      x0
                                                      x1
                                                      x2
                                                      (_root_.GebMirror.Metalogic.«Machine.nfTerm» x7))
                                                    (fun (x9 : _root_.Geb.Kernel.Tree) =>
                                                      let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.node
                                                        (_root_.Geb.Kernel.leaf 0)
                                                        (_root_.GebMirror.Metalogic.«Theory.l3»
                                                          (_root_.GebMirror.Metalogic.«Machine.nfTerm» x7)
                                                          (_root_.GebMirror.Metalogic.«Machine.nfTerm» x8)
                                                          (_root_.GebMirror.Metalogic.«Prelude.or»
                                                            (_root_.GebMirror.Metalogic.«Machine.nfMark» x7)
                                                            (_root_.GebMirror.Metalogic.«Machine.nfMark» x8)));
                                                      if (_root_.Geb.Kernel.Const.eq
                                                        (_root_.Geb.Kernel.Const.label x4)
                                                        (_root_.Geb.Kernel.leaf 9)).label ≠ 0 then
                                                        _root_.GebMirror.Metalogic.«Language.mNode»
                                                          (_root_.Geb.Kernel.leaf 14)
                                                          (_root_.GebMirror.Metalogic.«Theory.l6»
                                                            (_root_.Geb.Kernel.Const.node
                                                              (_root_.Geb.Kernel.leaf 0)
                                                              x2)
                                                            x3
                                                            x4
                                                            (_root_.Geb.Kernel.Const.node
                                                              (_root_.Geb.Kernel.leaf 0)
                                                              (x9 :: x2))
                                                            (_root_.Geb.Kernel.Const.add
                                                              x3
                                                              (_root_.Geb.Kernel.leaf 1))
                                                            x10)
                                                          (_root_.GebMirror.Metalogic.«Prelude.single»
                                                            (_root_.GebMirror.Metalogic.«Machine.jobE»
                                                              (_root_.GebMirror.Metalogic.«Language.mD»
                                                                x4
                                                                (_root_.Geb.Kernel.leaf 0))
                                                              ((_root_.GebMirror.Metalogic.«Machine.level»
                                                                x3) ::
                                                                (_root_.GebMirror.Metalogic.«Prelude.drop»
                                                                  (_root_.Geb.Kernel.leaf 2)
                                                                  x6))
                                                              (_root_.GebMirror.Metalogic.«Language.mD»
                                                                x4
                                                                (_root_.Geb.Kernel.leaf 1))))
                                                      else
                                                        _root_.GebMirror.Metalogic.«Machine.bindS»
                                                          (_root_.GebMirror.Metalogic.«Base.bindO»
                                                            (_root_.GebMirror.Metalogic.«Derivation.typeIn»
                                                              x0
                                                              x1
                                                              x2
                                                              (_root_.GebMirror.Metalogic.«Machine.nfTerm» x8))
                                                            _root_.GebMirror.Metalogic.«Language.listPart»)
                                                          (fun (x11 : _root_.Geb.Kernel.Tree) =>
                                                            _root_.GebMirror.Metalogic.«Language.mNode»
                                                              (_root_.Geb.Kernel.leaf 14)
                                                              (_root_.GebMirror.Metalogic.«Theory.l6»
                                                                (_root_.Geb.Kernel.Const.node
                                                                  (_root_.Geb.Kernel.leaf 0)
                                                                  x2)
                                                                x3
                                                                x4
                                                                (_root_.Geb.Kernel.Const.node
                                                                  (_root_.Geb.Kernel.leaf 0)
                                                                  (x9 :: (x11 :: x2)))
                                                                (_root_.Geb.Kernel.Const.add
                                                                  x3
                                                                  (_root_.Geb.Kernel.leaf 2))
                                                                x10)
                                                              (_root_.GebMirror.Metalogic.«Prelude.single»
                                                                (_root_.GebMirror.Metalogic.«Machine.jobE»
                                                                  (_root_.GebMirror.Metalogic.«Language.mD»
                                                                    x4
                                                                    (_root_.Geb.Kernel.leaf 0))
                                                                  ((_root_.GebMirror.Metalogic.«Machine.level»
                                                                    (_root_.Geb.Kernel.Const.add
                                                                      x3
                                                                      (_root_.Geb.Kernel.leaf 1))) ::
                                                                    ((_root_.GebMirror.Metalogic.«Machine.level»
                                                                      x3) ::
                                                                      (_root_.GebMirror.Metalogic.«Prelude.drop»
                                                                        (_root_.Geb.Kernel.leaf 2)
                                                                        x6)))
                                                                  (_root_.GebMirror.Metalogic.«Language.mD»
                                                                    x4
                                                                    (_root_.Geb.Kernel.leaf 1)))))))));
    x6

def «Machine.nBody» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mNode»
      (_root_.Geb.Kernel.leaf 15)
      (_root_.GebMirror.Metalogic.«Theory.l4»
        (_root_.GebMirror.Metalogic.«Prelude.at» x0 (_root_.Geb.Kernel.leaf 0))
        (_root_.GebMirror.Metalogic.«Prelude.at» x0 (_root_.Geb.Kernel.leaf 1))
        (_root_.GebMirror.Metalogic.«Prelude.at» x0 (_root_.Geb.Kernel.leaf 2))
        (_root_.GebMirror.Metalogic.«Prelude.at» x0 (_root_.Geb.Kernel.leaf 5)))
      (_root_.GebMirror.Metalogic.«Prelude.single»
        (_root_.GebMirror.Metalogic.«Machine.jobN»
          (_root_.Geb.Kernel.Const.children
            (_root_.GebMirror.Metalogic.«Prelude.at» x0 (_root_.Geb.Kernel.leaf 3)))
          (_root_.GebMirror.Metalogic.«Prelude.at» x0 (_root_.Geb.Kernel.leaf 4))
          x1));
    x2

def «Machine.nBuildT» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := (let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.label
                                          x0;
                                        if (_root_.Geb.Kernel.Const.eq
                                          x3
                                          (_root_.Geb.Kernel.leaf 9)).label ≠ 0 then
                                          _root_.GebMirror.Metalogic.«Language.mNatRec»
                                            (_root_.GebMirror.Metalogic.«Prelude.at»
                                              x1
                                              (_root_.Geb.Kernel.leaf 0))
                                            (_root_.GebMirror.Metalogic.«Machine.nfTerm» x2)
                                            (_root_.GebMirror.Metalogic.«Prelude.at»
                                              x1
                                              (_root_.Geb.Kernel.leaf 1))
                                        else
                                          if (_root_.Geb.Kernel.Const.eq
                                            x3
                                            (_root_.Geb.Kernel.leaf 10)).label ≠ 0 then
                                            _root_.GebMirror.Metalogic.«Language.mListRec»
                                              (_root_.GebMirror.Metalogic.«Prelude.at»
                                                x1
                                                (_root_.Geb.Kernel.leaf 0))
                                              (_root_.GebMirror.Metalogic.«Machine.nfTerm» x2)
                                              (_root_.GebMirror.Metalogic.«Prelude.at»
                                                x1
                                                (_root_.Geb.Kernel.leaf 1))
                                          else
                                            if (_root_.Geb.Kernel.Const.eq
                                              x3
                                              (_root_.Geb.Kernel.leaf 11)).label ≠ 0 then
                                              _root_.GebMirror.Metalogic.«Language.mRoseRec»
                                                (_root_.GebMirror.Metalogic.«Language.mD»
                                                  x0
                                                  (_root_.Geb.Kernel.leaf 0))
                                                (_root_.GebMirror.Metalogic.«Machine.nfTerm» x2)
                                                (_root_.GebMirror.Metalogic.«Prelude.at»
                                                  x1
                                                  (_root_.Geb.Kernel.leaf 0))
                                            else
                                              _root_.GebMirror.Metalogic.«Language.mLam»
                                                (_root_.GebMirror.Metalogic.«Language.mD»
                                                  x0
                                                  (_root_.Geb.Kernel.leaf 0))
                                                (_root_.GebMirror.Metalogic.«Machine.nfTerm» x2));
    x3

def «Machine.nBuildB» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := (let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.label
                                          x0;
                                        if (_root_.GebMirror.Metalogic.«Prelude.or»
                                          (_root_.Geb.Kernel.Const.eq x3 (_root_.Geb.Kernel.leaf 9))
                                          (_root_.Geb.Kernel.Const.eq
                                            x3
                                            (_root_.Geb.Kernel.leaf 10))).label ≠ 0 then
                                          _root_.GebMirror.Metalogic.«Prelude.at» x1 (_root_.Geb.Kernel.leaf 2)
                                        else
                                          if (_root_.Geb.Kernel.Const.eq
                                            x3
                                            (_root_.Geb.Kernel.leaf 11)).label ≠ 0 then
                                            _root_.GebMirror.Metalogic.«Prelude.at»
                                              x1
                                              (_root_.Geb.Kernel.leaf 1)
                                          else
                                            _root_.GebMirror.Metalogic.«Machine.nfMark» x2);
    x3

def «Machine.nDone» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := (let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.at»
                                          x1
                                          (_root_.Geb.Kernel.leaf 2);
                                        let x4 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                          (_root_.GebMirror.Metalogic.«Prelude.at»
                                            x1
                                            (_root_.Geb.Kernel.leaf 3));
                                        _root_.GebMirror.Metalogic.«Machine.nPost»
                                          x0
                                          (_root_.Geb.Kernel.Const.children
                                            (_root_.GebMirror.Metalogic.«Prelude.at»
                                              x1
                                              (_root_.Geb.Kernel.leaf 0)))
                                          (_root_.GebMirror.Metalogic.«Prelude.at»
                                            x1
                                            (_root_.Geb.Kernel.leaf 1))
                                          x3
                                          (_root_.GebMirror.Metalogic.«Machine.nBuildT» x3 x4 x2)
                                          (_root_.GebMirror.Metalogic.«Machine.nBuildB» x3 x4 x2));
    x3

def «Machine.nKids» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Base.allT»
      _root_.GebMirror.Metalogic.«Prelude.isSome»
      x4).label ≠ 0 then
      _root_.GebMirror.Metalogic.«Machine.nPost»
        x0
        x1
        x2
        x3
        (_root_.GebMirror.Metalogic.«Machine.readStep»
          x2
          x3
          (_root_.GebMirror.Metalogic.«Base.mapT»
            (fun (x5 : _root_.Geb.Kernel.Tree) =>
              _root_.GebMirror.Metalogic.«Machine.nfTerm» (_root_.GebMirror.Metalogic.«Prelude.get» x5))
            x4))
        (_root_.GebMirror.Metalogic.«Base.anyT»
          (fun (x5 : _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Metalogic.«Machine.nfMark» (_root_.GebMirror.Metalogic.«Prelude.get» x5))
          x4)
    else
      _root_.GebMirror.Metalogic.«Machine.msDone» _root_.GebMirror.Metalogic.«Prelude.none»);
    x5

def «Machine.msStart» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.label
                                          x0;
                                        if (_root_.Geb.Kernel.Const.eq
                                          x1
                                          (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                                          _root_.GebMirror.Metalogic.«Machine.eStart» x0
                                        else
                                          if (_root_.Geb.Kernel.Const.eq
                                            x1
                                            (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                            _root_.GebMirror.Metalogic.«Machine.bindS»
                                              (_root_.GebMirror.Metalogic.«Language.mD»
                                                x0
                                                (_root_.Geb.Kernel.leaf 0))
                                              _root_.GebMirror.Metalogic.«Machine.wStart»
                                          else
                                            _root_.GebMirror.Metalogic.«Language.mNode»
                                              (_root_.Geb.Kernel.leaf 12)
                                              (_root_.GebMirror.Metalogic.«Theory.l2»
                                                (_root_.Geb.Kernel.Const.node
                                                  (_root_.Geb.Kernel.leaf 0)
                                                  (_root_.GebMirror.Metalogic.«Language.mArgs» x0))
                                                (_root_.GebMirror.Metalogic.«Language.mD»
                                                  x0
                                                  (_root_.Geb.Kernel.leaf 0)))
                                              (_root_.GebMirror.Metalogic.«Prelude.single»
                                                (_root_.GebMirror.Metalogic.«Machine.jobW»
                                                  (_root_.GebMirror.Metalogic.«Language.mD»
                                                    x0
                                                    (_root_.Geb.Kernel.leaf 1)))));
    x1

def «Machine.msResult» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (if (_root_.Geb.Kernel.Const.eq
      (_root_.Geb.Kernel.Const.label x0)
      (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
      _root_.GebMirror.Metalogic.«Language.mD» x0 (_root_.Geb.Kernel.leaf 0)
    else
      _root_.GebMirror.Metalogic.«Prelude.none»);
    x1

def «Machine.msAdv» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x6 : _root_.Geb.Kernel.Tree)
    (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x8 : _root_.Geb.Kernel.Tree := (let x8 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.label
                                          x6;
                                        let x9 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.at»
                                          x7
                                          (_root_.Geb.Kernel.leaf 0);
                                        if (_root_.Geb.Kernel.Const.eq
                                          x8
                                          (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                                          x6
                                        else
                                          if (_root_.Geb.Kernel.Const.eq
                                            x8
                                            (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                            _root_.GebMirror.Metalogic.«Machine.msDone» x9
                                          else
                                            if (_root_.Geb.Kernel.Const.eq
                                              x8
                                              (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
                                              _root_.GebMirror.Metalogic.«Machine.msTail»
                                                (_root_.GebMirror.Metalogic.«Machine.jobW» x9)
                                            else
                                              if (_root_.Geb.Kernel.Const.eq
                                                x8
                                                (_root_.Geb.Kernel.leaf 3)).label ≠ 0 then
                                                _root_.GebMirror.Metalogic.«Machine.eArgs»
                                                  (_root_.GebMirror.Metalogic.«Language.mD»
                                                    x6
                                                    (_root_.Geb.Kernel.leaf 0))
                                                  x7
                                              else
                                                if (_root_.Geb.Kernel.Const.eq
                                                  x8
                                                  (_root_.Geb.Kernel.leaf 4)).label ≠ 0 then
                                                  _root_.GebMirror.Metalogic.«Machine.eFinal»
                                                    x0
                                                    x2
                                                    (_root_.GebMirror.Metalogic.«Language.mD»
                                                      x6
                                                      (_root_.Geb.Kernel.leaf 0))
                                                    (_root_.GebMirror.Metalogic.«Language.mD»
                                                      x6
                                                      (_root_.Geb.Kernel.leaf 1))
                                                    (_root_.GebMirror.Metalogic.«Machine.eDelays»
                                                      (_root_.GebMirror.Metalogic.«Language.mD»
                                                        x6
                                                        (_root_.Geb.Kernel.leaf 0))
                                                      x7)
                                                else
                                                  if (_root_.Geb.Kernel.Const.eq
                                                    x8
                                                    (_root_.Geb.Kernel.leaf 5)).label ≠ 0 then
                                                    _root_.GebMirror.Metalogic.«Machine.bindS»
                                                      x9
                                                      (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                                        _root_.GebMirror.Metalogic.«Machine.wHead»
                                                          x0
                                                          x3
                                                          x4
                                                          (_root_.GebMirror.Metalogic.«Language.mD»
                                                            x6
                                                            (_root_.Geb.Kernel.leaf 0))
                                                          x10)
                                                  else
                                                    if (_root_.Geb.Kernel.Const.eq
                                                      x8
                                                      (_root_.Geb.Kernel.leaf 6)).label ≠ 0 then
                                                      _root_.GebMirror.Metalogic.«Machine.bindS»
                                                        x9
                                                        (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                                          _root_.GebMirror.Metalogic.«Machine.wCase»
                                                            x0
                                                            (_root_.GebMirror.Metalogic.«Language.mD»
                                                              x6
                                                              (_root_.Geb.Kernel.leaf 0))
                                                            x10)
                                                    else
                                                      if (_root_.Geb.Kernel.Const.eq
                                                        x8
                                                        (_root_.Geb.Kernel.leaf 7)).label ≠ 0 then
                                                        _root_.GebMirror.Metalogic.«Machine.bindS»
                                                          x9
                                                          (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                                            _root_.GebMirror.Metalogic.«Machine.wCase2»
                                                              x0
                                                              (_root_.GebMirror.Metalogic.«Language.mD»
                                                                x6
                                                                (_root_.Geb.Kernel.leaf 0))
                                                              (_root_.GebMirror.Metalogic.«Language.mD»
                                                                x6
                                                                (_root_.Geb.Kernel.leaf 1))
                                                              x10)
                                                      else
                                                        if (_root_.Geb.Kernel.Const.eq
                                                          x8
                                                          (_root_.Geb.Kernel.leaf 8)).label ≠ 0 then
                                                          _root_.GebMirror.Metalogic.«Machine.bindS»
                                                            x9
                                                            (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                                              _root_.GebMirror.Metalogic.«Machine.wBase»
                                                                (_root_.GebMirror.Metalogic.«Language.mD»
                                                                  x6
                                                                  (_root_.Geb.Kernel.leaf 0))
                                                                (_root_.GebMirror.Metalogic.«Language.mD»
                                                                  x6
                                                                  (_root_.Geb.Kernel.leaf 1))
                                                                x10)
                                                        else
                                                          if (_root_.Geb.Kernel.Const.eq
                                                            x8
                                                            (_root_.Geb.Kernel.leaf 9)).label ≠ 0 then
                                                            _root_.GebMirror.Metalogic.«Machine.bindS»
                                                              x9
                                                              (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                                                _root_.GebMirror.Metalogic.«Machine.wCons»
                                                                  (_root_.GebMirror.Metalogic.«Language.mD»
                                                                    x6
                                                                    (_root_.Geb.Kernel.leaf 0))
                                                                  (_root_.GebMirror.Metalogic.«Language.mD»
                                                                    x6
                                                                    (_root_.Geb.Kernel.leaf 1))
                                                                  x10)
                                                          else
                                                            if (_root_.Geb.Kernel.Const.eq
                                                              x8
                                                              (_root_.Geb.Kernel.leaf 10)).label ≠ 0 then
                                                              _root_.GebMirror.Metalogic.«Machine.bindS»
                                                                x9
                                                                (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                                                  _root_.GebMirror.Metalogic.«Machine.wRose2»
                                                                    x3
                                                                    x4
                                                                    (_root_.GebMirror.Metalogic.«Language.mD»
                                                                      x6
                                                                      (_root_.Geb.Kernel.leaf 0))
                                                                    (_root_.GebMirror.Metalogic.«Language.mD»
                                                                      x6
                                                                      (_root_.Geb.Kernel.leaf 1))
                                                                    x10)
                                                            else
                                                              if (_root_.Geb.Kernel.Const.eq
                                                                x8
                                                                (_root_.Geb.Kernel.leaf 11)).label ≠ 0 then
                                                                _root_.GebMirror.Metalogic.«Machine.wRec»
                                                                  (_root_.Geb.Kernel.Const.children
                                                                    (_root_.Geb.Kernel.Const.child
                                                                      x6
                                                                      (_root_.Geb.Kernel.leaf 0)))
                                                                  x9
                                                              else
                                                                if (_root_.Geb.Kernel.Const.eq
                                                                  x8
                                                                  (_root_.Geb.Kernel.leaf 12)).label ≠ 0 then
                                                                  _root_.GebMirror.Metalogic.«Machine.bindS»
                                                                    x9
                                                                    (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                                                      _root_.GebMirror.Metalogic.«Machine.nNode»
                                                                        x5
                                                                        (_root_.Geb.Kernel.Const.children
                                                                          (_root_.GebMirror.Metalogic.«Language.mD»
                                                                            x6
                                                                            (_root_.Geb.Kernel.leaf 0)))
                                                                        (_root_.GebMirror.Metalogic.«Language.mD»
                                                                          x6
                                                                          (_root_.Geb.Kernel.leaf 1))
                                                                        x10)
                                                                else
                                                                  if (_root_.Geb.Kernel.Const.eq
                                                                    x8
                                                                    (_root_.Geb.Kernel.leaf 13)).label ≠ 0 then
                                                                    _root_.GebMirror.Metalogic.«Machine.nFold»
                                                                      x0
                                                                      x1
                                                                      (_root_.Geb.Kernel.Const.children
                                                                        (_root_.GebMirror.Metalogic.«Language.mD»
                                                                          x6
                                                                          (_root_.Geb.Kernel.leaf 0)))
                                                                      (_root_.GebMirror.Metalogic.«Language.mD»
                                                                        x6
                                                                        (_root_.Geb.Kernel.leaf 1))
                                                                      (_root_.GebMirror.Metalogic.«Language.mD»
                                                                        x6
                                                                        (_root_.Geb.Kernel.leaf 2))
                                                                      x7
                                                                  else
                                                                    if (_root_.Geb.Kernel.Const.eq
                                                                      x8
                                                                      (_root_.Geb.Kernel.leaf 14)).label ≠ 0 then
                                                                      _root_.GebMirror.Metalogic.«Machine.nBody»
                                                                        (_root_.Geb.Kernel.Const.children
                                                                          (_root_.Geb.Kernel.Const.child
                                                                            x6
                                                                            (_root_.Geb.Kernel.leaf 0)))
                                                                        x9
                                                                    else
                                                                      if (_root_.Geb.Kernel.Const.eq
                                                                        x8
                                                                        (_root_.Geb.Kernel.leaf 15)).label ≠ 0 then
                                                                        _root_.GebMirror.Metalogic.«Machine.bindS»
                                                                          x9
                                                                          (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                                                            _root_.GebMirror.Metalogic.«Machine.nDone»
                                                                              x5
                                                                              (_root_.Geb.Kernel.Const.children
                                                                                (_root_.Geb.Kernel.Const.child
                                                                                  x6
                                                                                  (_root_.Geb.Kernel.leaf 0)))
                                                                              x10)
                                                                      else
                                                                        if (_root_.Geb.Kernel.Const.eq
                                                                          x8
                                                                          (_root_.Geb.Kernel.leaf 16)).label ≠ 0 then
                                                                          _root_.GebMirror.Metalogic.«Machine.nKids»
                                                                            x5
                                                                            (_root_.Geb.Kernel.Const.children
                                                                              (_root_.GebMirror.Metalogic.«Language.mD»
                                                                                x6
                                                                                (_root_.Geb.Kernel.leaf 0)))
                                                                            (_root_.GebMirror.Metalogic.«Language.mD»
                                                                              x6
                                                                              (_root_.Geb.Kernel.leaf 1))
                                                                            (_root_.GebMirror.Metalogic.«Language.mD»
                                                                              x6
                                                                              (_root_.Geb.Kernel.leaf 2))
                                                                            x7
                                                                        else
                                                                          if (_root_.Geb.Kernel.Const.eq
                                                                            x8
                                                                            (_root_.Geb.Kernel.leaf 17)).label ≠ 0 then
                                                                            _root_.GebMirror.Metalogic.«Language.mNode»
                                                                              (_root_.Geb.Kernel.leaf 18)
                                                                              ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                                              (_root_.GebMirror.Metalogic.«Prelude.single»
                                                                                (_root_.GebMirror.Metalogic.«Machine.jobN»
                                                                                  (_root_.Geb.Kernel.Const.children
                                                                                    (_root_.GebMirror.Metalogic.«Language.mD»
                                                                                      x6
                                                                                      (_root_.Geb.Kernel.leaf 0)))
                                                                                  (_root_.GebMirror.Metalogic.«Language.mD»
                                                                                    x6
                                                                                    (_root_.Geb.Kernel.leaf 1))
                                                                                  x9))
                                                                          else
                                                                            _root_.GebMirror.Metalogic.«Machine.msDone»
                                                                              (_root_.GebMirror.Metalogic.«Base.bindO»
                                                                                x9
                                                                                (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                                                                  _root_.GebMirror.Metalogic.«Machine.marked»
                                                                                    (_root_.GebMirror.Metalogic.«Machine.nfTerm»
                                                                                      x10)
                                                                                    (_root_.Geb.Kernel.leaf 1))));
    x8

def «Machine.splitRs» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List _root_.Geb.Kernel.Tree ×
      _root_.List
        _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree ×
          _root_.List _root_.Geb.Kernel.Tree)
      (fun (_ : _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree →
           _root_.List _root_.Geb.Kernel.Tree ×
             _root_.List _root_.Geb.Kernel.Tree)
         (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.lcase
          (α := _root_.Geb.Kernel.Tree)
          (β := _root_.List _root_.Geb.Kernel.Tree ×
            _root_.List _root_.Geb.Kernel.Tree)
          x4
          (([] : _root_.List _root_.Geb.Kernel.Tree),
            ([] : _root_.List _root_.Geb.Kernel.Tree))
          (fun (x5 : _root_.Geb.Kernel.Tree)
             (x6 : _root_.List _root_.Geb.Kernel.Tree) =>
            let x7 : _root_.List _root_.Geb.Kernel.Tree ×
              _root_.List _root_.Geb.Kernel.Tree := x3 x6;
            ((x5 :: (x7).1), (x7).2)))
      (fun (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
        (([] : _root_.List _root_.Geb.Kernel.Tree), x2))
      x0
      x1;
    x2

def «Machine.msRound» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x6 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree)
    (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x8 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree)
      (fun (x8 : _root_.Geb.Kernel.Tree)
         (x9 : _root_.List _root_.Geb.Kernel.Tree →
           _root_.List _root_.Geb.Kernel.Tree)
         (x10 : _root_.List _root_.Geb.Kernel.Tree) =>
        let x11 : _root_.List _root_.Geb.Kernel.Tree ×
          _root_.List
            _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Machine.splitRs»
          (_root_.GebMirror.Metalogic.«Language.mArgs» x8)
          x10;
        ((_root_.GebMirror.Metalogic.«Machine.msAdv» x0 x1 x2 x3 x4 x5 x8 (x11).1) ::
          (x9 (x11).2)))
      (fun (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        ([] : _root_.List _root_.Geb.Kernel.Tree))
      x7
      (x6
        (_root_.Geb.Kernel.Const.foldr
          (α := _root_.Geb.Kernel.Tree)
          (β := _root_.List _root_.Geb.Kernel.Tree)
          (fun (x8 : _root_.Geb.Kernel.Tree)
             (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Metalogic.«Prelude.append»
              (_root_.GebMirror.Metalogic.«Language.mArgs» x8)
              x9)
          ([] : _root_.List _root_.Geb.Kernel.Tree)
          x7));
    x8

def «Machine.machStepB» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x6 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree) =>
    let x7 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List
        _root_.Geb.Kernel.Tree := (fun (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
      _root_.Geb.Kernel.Const.lcase
        (α := _root_.Geb.Kernel.Tree)
        (β := _root_.List _root_.Geb.Kernel.Tree)
        x7
        ([] : _root_.List _root_.Geb.Kernel.Tree)
        (fun (_ : _root_.Geb.Kernel.Tree)
           (_ : _root_.List _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.Metalogic.«Base.mapT»
            _root_.GebMirror.Metalogic.«Machine.msResult»
            (_root_.GebMirror.Metalogic.«Machine.msRound»
              x0
              x1
              x2
              x3
              x4
              x5
              x6
              (_root_.GebMirror.Metalogic.«Machine.msRound»
                x0
                x1
                x2
                x3
                x4
                x5
                x6
                (_root_.GebMirror.Metalogic.«Machine.msRound»
                  x0
                  x1
                  x2
                  x3
                  x4
                  x5
                  x6
                  (_root_.GebMirror.Metalogic.«Machine.msRound»
                    x0
                    x1
                    x2
                    x3
                    x4
                    x5
                    x6
                    (_root_.GebMirror.Metalogic.«Machine.msRound»
                      x0
                      x1
                      x2
                      x3
                      x4
                      x5
                      x6
                      (_root_.GebMirror.Metalogic.«Machine.msRound»
                        x0
                        x1
                        x2
                        x3
                        x4
                        x5
                        x6
                        (_root_.GebMirror.Metalogic.«Base.mapT»
                          _root_.GebMirror.Metalogic.«Machine.msStart»
                          x7)))))))));
    x7

def «Machine.machB» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x6 : _root_.Geb.Kernel.Tree) =>
    let x7 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List
        _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.iter
      (α := _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«Machine.machStepB» x0 x1 x2 x3 x4 x5)
      (fun (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Base.mapT»
          (fun (_ : _root_.Geb.Kernel.Tree) => _root_.GebMirror.Metalogic.«Prelude.none»)
          x7)
      x6;
    x7

def «Machine.machineReduce» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x6 : _root_.Geb.Kernel.Tree)
    (x7 : _root_.List _root_.Geb.Kernel.Tree)
    (x8 : _root_.Geb.Kernel.Tree) =>
    let x9 : _root_.Geb.Kernel.Tree := (let x9 : _root_.List _root_.Geb.Kernel.Tree →
                                          _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Machine.machB»
                                          x0
                                          x1
                                          x2
                                          x3
                                          x4
                                          x5
                                          x6;
                                        _root_.GebMirror.Metalogic.«Base.bindO»
                                          (_root_.GebMirror.Metalogic.«Prelude.at»
                                            (x9
                                              (_root_.GebMirror.Metalogic.«Prelude.single»
                                                (_root_.GebMirror.Metalogic.«Machine.jobN»
                                                  x7
                                                  (_root_.Geb.Kernel.leaf 0)
                                                  (_root_.GebMirror.Metalogic.«Prelude.at»
                                                    (x9
                                                      (_root_.GebMirror.Metalogic.«Prelude.single»
                                                        (_root_.GebMirror.Metalogic.«Machine.jobE»
                                                          x8
                                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                          (_root_.Geb.Kernel.leaf 0))))
                                                    (_root_.Geb.Kernel.leaf 0)))))
                                            (_root_.Geb.Kernel.leaf 0))
                                          (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                            _root_.GebMirror.Metalogic.«Prelude.some»
                                              (_root_.GebMirror.Metalogic.«Machine.nfTerm» x10)));
    x9

def «$436f6e76657273696f6e2f52756c6541742e6d6170» :=
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

def «$436f6e76657273696f6e2f4561636852756c652e616c6c» :=
  fun (x0 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree) (x3 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Prelude.and» (x0 x2) x3)
      (_root_.Geb.Kernel.leaf 1)
      x1;
    x2

def «$436f6e76657273696f6e2f4561636852756c652e616e79» :=
  fun (x0 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree) (x3 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Prelude.or» (x0 x2) x3)
      (_root_.Geb.Kernel.leaf 0)
      x1;
    x2

def «$436f6e76657273696f6e2f4561636852756c652e6973456d707479» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.eq
      (_root_.Geb.Kernel.Const.foldr
        (α := _root_.Geb.Kernel.Tree)
        (β := _root_.Geb.Kernel.Tree)
        (fun (_ : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
          _root_.Geb.Kernel.Const.add x2 (_root_.Geb.Kernel.leaf 1))
        (_root_.Geb.Kernel.leaf 0)
        x0)
      (_root_.Geb.Kernel.leaf 0);
    x1

def «$436f6e76657273696f6e2f4561636852756c652e74616b65» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := (let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x3 : _root_.Geb.Kernel.Tree) =>
                                     _root_.Geb.Kernel.Const.add x3 (_root_.Geb.Kernel.leaf 1))
                                   (_root_.Geb.Kernel.leaf 0)
                                   x1;
                                 (_root_.Geb.Kernel.Const.foldr
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree ×
                                     _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (x3 : _root_.Geb.Kernel.Tree)
                                      (x4 : _root_.Geb.Kernel.Tree ×
                                        _root_.List _root_.Geb.Kernel.Tree) =>
                                     (_root_.Geb.Kernel.Const.add (x4).1 (_root_.Geb.Kernel.leaf 1),
                                       if (_root_.Geb.Kernel.Const.lt
                                         (_root_.Geb.Kernel.Const.sub
                                           (_root_.Geb.Kernel.Const.sub x2 (x4).1)
                                           (_root_.Geb.Kernel.leaf 1))
                                         x0).label ≠ 0 then
                                         (x3 :: (x4).2)
                                       else
                                         (x4).2))
                                   (_root_.Geb.Kernel.leaf 0,
                                     ([] : _root_.List _root_.Geb.Kernel.Tree))
                                   x1).2);
    x2

def «Conversion.ckNone» :=
  fun (_ : _root_.Geb.Kernel.Tree)
    (_ : _root_.List _root_.Geb.Kernel.Tree)
    (_ : _root_.Geb.Kernel.Tree)
    (_ : _root_.List _root_.Geb.Kernel.Tree)
    (_ : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.leaf 0

def «Conversion.toRule» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.label
                                          x0;
                                        if (_root_.Geb.Kernel.Const.lt
                                          x1
                                          (_root_.Geb.Kernel.leaf 37)).label ≠ 0 then
                                          _root_.Geb.Kernel.Const.node
                                            x1
                                            (_root_.GebMirror.Metalogic.«Prelude.single»
                                              (_root_.Geb.Kernel.Const.child
                                                x0
                                                (_root_.Geb.Kernel.leaf 0)))
                                        else
                                          if (_root_.Geb.Kernel.Const.eq
                                            x1
                                            (_root_.Geb.Kernel.leaf 39)).label ≠ 0 then
                                            _root_.Geb.Kernel.Const.node
                                              (_root_.Geb.Kernel.leaf 27)
                                              (_root_.GebMirror.Metalogic.«Prelude.single»
                                                (_root_.Geb.Kernel.Const.node
                                                  (_root_.Geb.Kernel.leaf 0)
                                                  (_root_.GebMirror.Metalogic.«Theory.l3»
                                                    (_root_.GebMirror.Metalogic.«Language.mD»
                                                      x0
                                                      (_root_.Geb.Kernel.leaf 0))
                                                    (_root_.GebMirror.Metalogic.«Language.mD»
                                                      x0
                                                      (_root_.Geb.Kernel.leaf 1))
                                                    (_root_.Geb.Kernel.Const.node
                                                      (_root_.Geb.Kernel.leaf 0)
                                                      ([] : _root_.List _root_.Geb.Kernel.Tree)))))
                                          else
                                            _root_.Geb.Kernel.Const.node
                                              (_root_.Geb.Kernel.leaf 1)
                                              (_root_.GebMirror.Metalogic.«Prelude.single»
                                                (_root_.Geb.Kernel.Const.node
                                                  (_root_.Geb.Kernel.leaf 0)
                                                  ([] : _root_.List _root_.Geb.Kernel.Tree))));
    x1

def «Conversion.baseNode» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.node
      x0
      (x1 ::
        (_root_.GebMirror.Metalogic.«Base.mapT»
          _root_.GebMirror.Metalogic.«Conversion.toRule»
          (_root_.GebMirror.Metalogic.«Prelude.tail»
            (_root_.Geb.Kernel.Const.children x2))));
    x3

def «Conversion.ruleOf» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.label
                                          x0;
                                        let x2 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                          x0;
                                        if (_root_.Geb.Kernel.Const.eq
                                          x1
                                          (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                                          _root_.GebMirror.Metalogic.«Prover.nrRule»
                                            (_root_.GebMirror.Metalogic.«Prelude.at»
                                              x2
                                              (_root_.Geb.Kernel.leaf 0))
                                            (_root_.GebMirror.Metalogic.«Derivation.terms»
                                              (_root_.Geb.Kernel.Const.children
                                                (_root_.GebMirror.Metalogic.«Prelude.at»
                                                  x2
                                                  (_root_.Geb.Kernel.leaf 1))))
                                        else
                                          if (_root_.Geb.Kernel.Const.eq
                                            x1
                                            (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                            _root_.GebMirror.Metalogic.«Prover.nrDelta»
                                              (_root_.GebMirror.Metalogic.«Prelude.at»
                                                x2
                                                (_root_.Geb.Kernel.leaf 0))
                                          else
                                            if (_root_.Geb.Kernel.Const.eq
                                              x1
                                              (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
                                              _root_.GebMirror.Metalogic.«Prover.nrBelow»
                                                (_root_.GebMirror.Metalogic.«Prelude.at»
                                                  x2
                                                  (_root_.Geb.Kernel.leaf 0))
                                                (_root_.GebMirror.Metalogic.«Derivation.terms»
                                                  (_root_.Geb.Kernel.Const.children
                                                    (_root_.GebMirror.Metalogic.«Prelude.at»
                                                      x2
                                                      (_root_.Geb.Kernel.leaf 1))))
                                            else
                                              if (_root_.Geb.Kernel.Const.eq
                                                x1
                                                (_root_.Geb.Kernel.leaf 4)).label ≠ 0 then
                                                _root_.GebMirror.Metalogic.«Prover.nrThm»
                                                  (_root_.GebMirror.Metalogic.«Prelude.at»
                                                    x2
                                                    (_root_.Geb.Kernel.leaf 0))
                                                  (_root_.GebMirror.Metalogic.«Language.objs»
                                                    (_root_.Geb.Kernel.Const.children
                                                      (_root_.GebMirror.Metalogic.«Prelude.at»
                                                        x2
                                                        (_root_.Geb.Kernel.leaf 1))))
                                              else
                                                if (_root_.Geb.Kernel.Const.eq
                                                  x1
                                                  (_root_.Geb.Kernel.leaf 5)).label ≠ 0 then
                                                  _root_.GebMirror.Metalogic.«Prover.nrThmAt»
                                                    (_root_.GebMirror.Metalogic.«Prelude.at»
                                                      x2
                                                      (_root_.Geb.Kernel.leaf 0))
                                                    (_root_.GebMirror.Metalogic.«Language.objs»
                                                      (_root_.Geb.Kernel.Const.children
                                                        (_root_.GebMirror.Metalogic.«Prelude.at»
                                                          x2
                                                          (_root_.Geb.Kernel.leaf 1))))
                                                    (_root_.GebMirror.Metalogic.«Prelude.at»
                                                      x2
                                                      (_root_.Geb.Kernel.leaf 2))
                                                    (_root_.GebMirror.Metalogic.«Prelude.at»
                                                      x2
                                                      (_root_.Geb.Kernel.leaf 3))
                                                else
                                                  if (_root_.Geb.Kernel.Const.eq
                                                    x1
                                                    (_root_.Geb.Kernel.leaf 6)).label ≠ 0 then
                                                    _root_.GebMirror.Metalogic.«Prover.nrHyp»
                                                      (_root_.GebMirror.Metalogic.«Prelude.at»
                                                        x2
                                                        (_root_.Geb.Kernel.leaf 0))
                                                  else
                                                    _root_.GebMirror.Metalogic.«Prover.nrUnit»);
    x1

def «Conversion.rulesOf» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$436f6e76657273696f6e2f52756c6541742e6d6170»
      _root_.GebMirror.Metalogic.«Conversion.ruleOf»
      x0;
    x1

def «Conversion.stepNorm» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.List _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree →
              _root_.Geb.Kernel.Tree := (let x4 : _root_.List _root_.Geb.Kernel.Tree →
                                           _root_.List _root_.Geb.Kernel.Tree →
                                             _root_.Geb.Kernel.Tree →
                                               _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.normalize»
                                           x0
                                           x1
                                           x2
                                           (_root_.GebMirror.Metalogic.«Conversion.rulesOf»
                                             (_root_.Geb.Kernel.Const.children
                                               (_root_.GebMirror.Metalogic.«Prelude.at»
                                                 x3
                                                 (_root_.Geb.Kernel.leaf 0))))
                                           (_root_.GebMirror.Metalogic.«Prelude.at»
                                             x3
                                             (_root_.Geb.Kernel.leaf 1));
                                         fun (x5 : _root_.Geb.Kernel.Tree)
                                           (x6 : _root_.List _root_.Geb.Kernel.Tree)
                                           (x7 : _root_.Geb.Kernel.Tree)
                                           (x8 : _root_.List _root_.Geb.Kernel.Tree)
                                           (x9 : _root_.Geb.Kernel.Tree) =>
                                           if (x5).label ≠ 0 then
                                             _root_.Geb.Kernel.leaf 0
                                           else
                                             _root_.GebMirror.Metalogic.«Prover.bindNT»
                                               (x4
                                                 x6
                                                 (_root_.GebMirror.Metalogic.«Base.mapT»
                                                   (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                                     _root_.GebMirror.Metalogic.«Derivation.weakenBy» x7 x10)
                                                   x8)
                                                 x9)
                                               (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                                 _root_.GebMirror.Metalogic.«Prelude.some»
                                                   (_root_.GebMirror.Metalogic.«Prover.nfTerm» x10)));
    x4

def «Conversion.stepEval» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.List _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree →
              _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree →
                                           _root_.List _root_.Geb.Kernel.Tree →
                                             _root_.List _root_.Geb.Kernel.Tree →
                                               _root_.Geb.Kernel.Tree →
                                                 _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.eval»
                                           x0
                                           x1
                                           x2
                                           (_root_.GebMirror.Metalogic.«Conversion.rulesOf»
                                             (_root_.Geb.Kernel.Const.children
                                               (_root_.GebMirror.Metalogic.«Prelude.at»
                                                 x3
                                                 (_root_.Geb.Kernel.leaf 0))))
                                           (_root_.GebMirror.Metalogic.«Prelude.at»
                                             x3
                                             (_root_.Geb.Kernel.leaf 1));
                                         fun (x5 : _root_.Geb.Kernel.Tree)
                                           (x6 : _root_.List _root_.Geb.Kernel.Tree)
                                           (x7 : _root_.Geb.Kernel.Tree)
                                           (x8 : _root_.List _root_.Geb.Kernel.Tree)
                                           (x9 : _root_.Geb.Kernel.Tree) =>
                                           if (x5).label ≠ 0 then
                                             _root_.Geb.Kernel.leaf 0
                                           else
                                             _root_.GebMirror.Metalogic.«Prover.bindNT»
                                               (x4
                                                 (_root_.GebMirror.Metalogic.«Prelude.at»
                                                   x3
                                                   (_root_.Geb.Kernel.leaf 2))
                                                 x6
                                                 (_root_.GebMirror.Metalogic.«Base.mapT»
                                                   (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                                     _root_.GebMirror.Metalogic.«Derivation.weakenBy» x7 x10)
                                                   x8)
                                                 x9)
                                               (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                                 _root_.GebMirror.Metalogic.«Prelude.some»
                                                   (_root_.GebMirror.Metalogic.«Prover.nfTerm» x10)));
    x4

def «Conversion.applyInst» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Derivation.thmAt»
                                          x0
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
                                          let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.matchTerm»
                                            (if (_root_.GebMirror.Metalogic.«Base.isEmpty» x2).label ≠ 0 then
                                              _root_.GebMirror.Metalogic.«Derivation.thConcl» x6
                                            else
                                              _root_.GebMirror.Metalogic.«Language.osubst»
                                                x2
                                                (_root_.GebMirror.Metalogic.«Derivation.thConcl» x6))
                                            (_root_.Geb.Kernel.leaf 0)
                                            x3
                                            (_root_.GebMirror.Metalogic.«Prelude.replicate»
                                              (_root_.GebMirror.Metalogic.«Prelude.length»
                                                (_root_.GebMirror.Metalogic.«Derivation.thCtx» x6))
                                              _root_.GebMirror.Metalogic.«Prelude.none»);
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
                                            _root_.GebMirror.Metalogic.«Base.allSomeT»
                                              (_root_.GebMirror.Metalogic.«Prover.assigned» x10)
                                          else
                                            let _ : _root_.List
                                              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                              x8;
                                            _root_.GebMirror.Metalogic.«Prelude.none»
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«Prelude.none»);
    x4

def «Conversion.stepApply» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.List
      (_root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.List _root_.Geb.Kernel.Tree →
              _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
    let x6 : _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.List _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree →
              _root_.Geb.Kernel.Tree := (fun (x6 : _root_.Geb.Kernel.Tree)
                                           (x7 : _root_.List _root_.Geb.Kernel.Tree)
                                           (_ : _root_.Geb.Kernel.Tree)
                                           (x9 : _root_.List _root_.Geb.Kernel.Tree)
                                           (x10 : _root_.Geb.Kernel.Tree) =>
      if (x6).label ≠ 0 then
        let x11 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Conversion.applyInst»
          x1
          (_root_.GebMirror.Metalogic.«Prelude.at» x3 (_root_.Geb.Kernel.leaf 0))
          (_root_.Geb.Kernel.Const.children
            (_root_.GebMirror.Metalogic.«Prelude.at» x3 (_root_.Geb.Kernel.leaf 1)))
          x10;
        if (_root_.GebMirror.Metalogic.«Prelude.isSome» x11).label ≠ 0 then
          _root_.GebMirror.Metalogic.«Derivation.checkStep»
            x0
            x1
            x2
            (_root_.GebMirror.Metalogic.«Conversion.baseNode»
              (_root_.Geb.Kernel.leaf 27)
              (_root_.Geb.Kernel.Const.node
                (_root_.Geb.Kernel.leaf 0)
                (_root_.GebMirror.Metalogic.«Theory.l3»
                  (_root_.GebMirror.Metalogic.«Prelude.at» x3 (_root_.Geb.Kernel.leaf 0))
                  (_root_.GebMirror.Metalogic.«Prelude.at» x3 (_root_.Geb.Kernel.leaf 1))
                  (_root_.GebMirror.Metalogic.«Prelude.get» x11)))
              x4)
            x5
            (_root_.Geb.Kernel.leaf 1)
            x7
            (_root_.Geb.Kernel.leaf 0)
            x9
            x10
        else
          _root_.Geb.Kernel.leaf 0
      else
        _root_.GebMirror.Metalogic.«Prelude.none»);
    x6

def «Conversion.stepLit» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.List _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree →
              _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                           (_ : _root_.List _root_.Geb.Kernel.Tree)
                                           (_ : _root_.Geb.Kernel.Tree)
                                           (_ : _root_.List _root_.Geb.Kernel.Tree)
                                           (x6 : _root_.Geb.Kernel.Tree) =>
      if (x2).label ≠ 0 then
        _root_.Geb.Kernel.leaf 0
      else
        if (_root_.GebMirror.Metalogic.«Base.anyT»
          (fun (x7 : _root_.Geb.Kernel.Tree) =>
            _root_.Geb.Kernel.Const.eq
              x7
              (_root_.GebMirror.Metalogic.«Prelude.at» x1 (_root_.Geb.Kernel.leaf 0)))
          x0).label ≠ 0 then
          _root_.GebMirror.Metalogic.«Literals.litEval» x6
        else
          _root_.GebMirror.Metalogic.«Prelude.none»);
    x2

def «Conversion.machineReduceBy» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree)
    (x6 : _root_.List _root_.Geb.Kernel.Tree)
    (x7 : _root_.Geb.Kernel.Tree)
    (x8 : _root_.List _root_.Geb.Kernel.Tree)
    (x9 : _root_.List _root_.Geb.Kernel.Tree)
    (x10 : _root_.Geb.Kernel.Tree) =>
    let x11 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«$436f6e76657273696f6e2f4561636852756c652e6973456d707479»
      x6).label ≠ 0 then
      _root_.GebMirror.Metalogic.«Machine.machineReduce»
        x0
        x2
        x3
        x4
        x5
        (fun (_ : _root_.List _root_.Geb.Kernel.Tree)
           (_ : _root_.Geb.Kernel.Tree)
           (_ : _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.Metalogic.«Prelude.none»)
        x7
        x8
        x10
    else
      let x11 : _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.List _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree →
              _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.rootRewriteK»
        x0
        x1
        x2
        (_root_.GebMirror.Metalogic.«Prover.indexRules»
          x1
          (_root_.GebMirror.Metalogic.«Prover.prepareRules» x1 x6))
        (_root_.GebMirror.Metalogic.«Prover.prepareHyps» x9);
      _root_.GebMirror.Metalogic.«Machine.machineReduce»
        x0
        x2
        x3
        x4
        x5
        (fun (x12 : _root_.List _root_.Geb.Kernel.Tree)
           (x13 : _root_.Geb.Kernel.Tree)
           (x14 : _root_.Geb.Kernel.Tree) =>
          let x15 : _root_.Geb.Kernel.Tree := x11 x12 x13 x9 x14;
          if (_root_.Geb.Kernel.Const.eq
            (_root_.Geb.Kernel.Const.label x15)
            (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
            let x16 : _root_.List
              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x15;
            let x17 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
              (α := _root_.Geb.Kernel.Tree)
              (β := _root_.Geb.Kernel.Tree)
              x16
              (_root_.Geb.Kernel.leaf 0)
              (fun (x17 : _root_.Geb.Kernel.Tree)
                 (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                x17);
            let _ : _root_.List
              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
              (α := _root_.Geb.Kernel.Tree)
              (β := _root_.List _root_.Geb.Kernel.Tree)
              x16
              ([] : _root_.List _root_.Geb.Kernel.Tree)
              (fun (_ : _root_.Geb.Kernel.Tree)
                 (x19 : _root_.List _root_.Geb.Kernel.Tree) =>
                x19);
            _root_.GebMirror.Metalogic.«Prelude.some» (_root_.GebMirror.Metalogic.«Language.p1» x17)
          else
            let _ : _root_.List
              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x15;
            _root_.GebMirror.Metalogic.«Prelude.none»)
        x7
        x8
        x10);
    x11

def «Conversion.machineRun$geb» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree)
    (x5 : _root_.List _root_.Geb.Kernel.Tree)
    (x6 : _root_.Geb.Kernel.Tree) =>
    let x7 : _root_.Geb.Kernel.Tree := (let x7 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                          (_root_.GebMirror.Metalogic.«Prelude.at»
                                            x3
                                            (_root_.Geb.Kernel.leaf 2));
                                        _root_.GebMirror.Metalogic.«Conversion.machineReduceBy»
                                          x0
                                          x1
                                          x2
                                          (fun (x8 : _root_.Geb.Kernel.Tree) =>
                                            _root_.GebMirror.Metalogic.«Prelude.and»
                                              (_root_.Geb.Kernel.Const.lt
                                                x8
                                                (_root_.GebMirror.Metalogic.«Prelude.at»
                                                  x3
                                                  (_root_.Geb.Kernel.leaf 1)))
                                              (_root_.GebMirror.Metalogic.«Base.not»
                                                (_root_.GebMirror.Metalogic.«Base.anyT»
                                                  (fun (x9 : _root_.Geb.Kernel.Tree) =>
                                                    _root_.Geb.Kernel.Const.eq x9 x8)
                                                  x7)))
                                          (_root_.GebMirror.Metalogic.«Prelude.at»
                                            x3
                                            (_root_.Geb.Kernel.leaf 3))
                                          (_root_.GebMirror.Metalogic.«Prelude.at»
                                            x3
                                            (_root_.Geb.Kernel.leaf 4))
                                          (_root_.GebMirror.Metalogic.«Conversion.rulesOf»
                                            (_root_.Geb.Kernel.Const.children
                                              (_root_.GebMirror.Metalogic.«Prelude.at»
                                                x3
                                                (_root_.Geb.Kernel.leaf 5))))
                                          (_root_.GebMirror.Metalogic.«Prelude.at»
                                            x3
                                            (_root_.Geb.Kernel.leaf 0))
                                          x4
                                          x5
                                          x6);
    x7

def «Conversion.machineRun$accel» : type_of% «Conversion.machineRun$geb» :=
  _root_.Geb.FreeTopos.Internal.Accelerate.machineRun «Conversion.machineRun$geb»

@[implemented_by «Conversion.machineRun$accel»]
def «Conversion.machineRun» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree)
    (x5 : _root_.List _root_.Geb.Kernel.Tree)
    (x6 : _root_.Geb.Kernel.Tree) =>
    let x7 : _root_.Geb.Kernel.Tree := (let x7 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                          (_root_.GebMirror.Metalogic.«Prelude.at»
                                            x3
                                            (_root_.Geb.Kernel.leaf 2));
                                        _root_.GebMirror.Metalogic.«Conversion.machineReduceBy»
                                          x0
                                          x1
                                          x2
                                          (fun (x8 : _root_.Geb.Kernel.Tree) =>
                                            _root_.GebMirror.Metalogic.«Prelude.and»
                                              (_root_.Geb.Kernel.Const.lt
                                                x8
                                                (_root_.GebMirror.Metalogic.«Prelude.at»
                                                  x3
                                                  (_root_.Geb.Kernel.leaf 1)))
                                              (_root_.GebMirror.Metalogic.«Base.not»
                                                (_root_.GebMirror.Metalogic.«Base.anyT»
                                                  (fun (x9 : _root_.Geb.Kernel.Tree) =>
                                                    _root_.Geb.Kernel.Const.eq x9 x8)
                                                  x7)))
                                          (_root_.GebMirror.Metalogic.«Prelude.at»
                                            x3
                                            (_root_.Geb.Kernel.leaf 3))
                                          (_root_.GebMirror.Metalogic.«Prelude.at»
                                            x3
                                            (_root_.Geb.Kernel.leaf 4))
                                          (_root_.GebMirror.Metalogic.«Conversion.rulesOf»
                                            (_root_.Geb.Kernel.Const.children
                                              (_root_.GebMirror.Metalogic.«Prelude.at»
                                                x3
                                                (_root_.Geb.Kernel.leaf 5))))
                                          (_root_.GebMirror.Metalogic.«Prelude.at»
                                            x3
                                            (_root_.Geb.Kernel.leaf 0))
                                          x4
                                          x5
                                          x6);
    x7

def «Conversion.stepMachine» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.List _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree →
              _root_.Geb.Kernel.Tree := (fun (x4 : _root_.Geb.Kernel.Tree)
                                           (x5 : _root_.List _root_.Geb.Kernel.Tree)
                                           (x6 : _root_.Geb.Kernel.Tree)
                                           (x7 : _root_.List _root_.Geb.Kernel.Tree)
                                           (x8 : _root_.Geb.Kernel.Tree) =>
      if (x4).label ≠ 0 then
        _root_.Geb.Kernel.leaf 0
      else
        _root_.GebMirror.Metalogic.«Conversion.machineRun»
          x0
          x1
          x2
          x3
          x5
          (if (_root_.GebMirror.Metalogic.«Base.isEmpty»
            (_root_.Geb.Kernel.Const.children
              (_root_.GebMirror.Metalogic.«Prelude.at»
                x3
                (_root_.Geb.Kernel.leaf 5)))).label ≠ 0 then
            ([] : _root_.List _root_.Geb.Kernel.Tree)
          else
            _root_.GebMirror.Metalogic.«Base.mapT»
              (fun (x9 : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.Metalogic.«Derivation.weakenBy» x6 x9)
              x7)
          x8);
    x4

def «Conversion.convStep» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.List
      (_root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.List _root_.Geb.Kernel.Tree →
              _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
    let x6 : _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.List _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree →
              _root_.Geb.Kernel.Tree := (let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.label
                                           x4;
                                         let x7 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.child
                                           x4
                                           (_root_.Geb.Kernel.leaf 0);
                                         let x8 : _root_.List
                                           _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                           x7;
                                         if (_root_.Geb.Kernel.Const.lt
                                           x6
                                           (_root_.Geb.Kernel.leaf 37)).label ≠ 0 then
                                           _root_.GebMirror.Metalogic.«Derivation.checkStep»
                                             x0
                                             x1
                                             x3
                                             (_root_.GebMirror.Metalogic.«Conversion.baseNode» x6 x7 x4)
                                             x5
                                         else
                                           if (_root_.Geb.Kernel.Const.eq
                                             x6
                                             (_root_.Geb.Kernel.leaf 37)).label ≠ 0 then
                                             _root_.GebMirror.Metalogic.«Conversion.stepNorm» x0 x1 x3 x8
                                           else
                                             if (_root_.Geb.Kernel.Const.eq
                                               x6
                                               (_root_.Geb.Kernel.leaf 38)).label ≠ 0 then
                                               _root_.GebMirror.Metalogic.«Conversion.stepEval» x0 x1 x3 x8
                                             else
                                               if (_root_.Geb.Kernel.Const.eq
                                                 x6
                                                 (_root_.Geb.Kernel.leaf 39)).label ≠ 0 then
                                                 _root_.GebMirror.Metalogic.«Conversion.stepApply»
                                                   x0
                                                   x1
                                                   x3
                                                   x8
                                                   x4
                                                   x5
                                               else
                                                 if (_root_.Geb.Kernel.Const.eq
                                                   x6
                                                   (_root_.Geb.Kernel.leaf 40)).label ≠ 0 then
                                                   _root_.GebMirror.Metalogic.«Conversion.stepLit» x2 x8
                                                 else
                                                   if (_root_.Geb.Kernel.Const.eq
                                                     x6
                                                     (_root_.Geb.Kernel.leaf 41)).label ≠ 0 then
                                                     _root_.GebMirror.Metalogic.«Conversion.stepMachine»
                                                       x0
                                                       x1
                                                       x3
                                                       x8
                                                   else
                                                     _root_.GebMirror.Metalogic.«Conversion.ckNone»);
    x6

def «Conversion.convCheck» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.List _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree →
              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.para
      (α := _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.List _root_.Geb.Kernel.Tree →
              _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«Conversion.convStep» x0 x1 x2 x3)
      x4;
    x5

def «Conversion.thmConvChecks» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree := (let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Derivation.thArity»
                                          x3;
                                        let x6 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Derivation.thCtx»
                                          x3;
                                        if (_root_.GebMirror.Metalogic.«Prelude.and»
                                          (_root_.GebMirror.Metalogic.«Base.allT»
                                            (_root_.GebMirror.Metalogic.«Language.isTy» x0 x5)
                                            x6)
                                          (_root_.GebMirror.Metalogic.«Prelude.and»
                                            (_root_.GebMirror.Metalogic.«Base.allT»
                                              (_root_.GebMirror.Metalogic.«Derivation.isFormula» x0 x5 x6)
                                              (_root_.GebMirror.Metalogic.«Derivation.thHyps» x3))
                                            (_root_.GebMirror.Metalogic.«Derivation.isFormula»
                                              x0
                                              x5
                                              x6
                                              (_root_.GebMirror.Metalogic.«Derivation.thConcl»
                                                x3)))).label ≠ 0 then
                                          _root_.GebMirror.Metalogic.«Conversion.convCheck»
                                            x0
                                            x1
                                            x2
                                            x5
                                            x4
                                            (_root_.Geb.Kernel.leaf 1)
                                            x6
                                            (_root_.Geb.Kernel.leaf 0)
                                            (_root_.GebMirror.Metalogic.«Derivation.thHyps» x3)
                                            (_root_.GebMirror.Metalogic.«Derivation.thConcl» x3)
                                        else
                                          _root_.Geb.Kernel.leaf 0);
    x5

def «Conversion.indices» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 0) x0

def «Conversion.convState» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: (x2 :: ([] : _root_.List _root_.Geb.Kernel.Tree))))

def «$436f6e76657273696f6e2f4f436f6e7653746174652e6e6f7468696e67» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$436f6e76657273696f6e2f4f436f6e7653746174652e6a757374» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «$436f6e76657273696f6e2f4f436f6e7653746174652e69734a757374» :=
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

def «$436f6e76657273696f6e2f4f436f6e7653746174652e66726f6d4d61796265» :=
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

def «$436f6e76657273696f6e2f4f436f6e7653746174652e6e74684f66» :=
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
      _root_.GebMirror.Metalogic.«$436f6e76657273696f6e2f4f436f6e7653746174652e6e6f7468696e67»
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$436f6e76657273696f6e2f4f436f6e7653746174652e6a757374»
          x2);
    x2

def «$436f6e76657273696f6e2f4f436f6e7653746174652e616c6c4a757374» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree ×
      _root_.List
        _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree) =>
        let x3 : _root_.Geb.Kernel.Tree := x1;
        if (_root_.Geb.Kernel.Const.eq
          (_root_.Geb.Kernel.Const.label x3)
          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
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
          let _ : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
            (α := _root_.Geb.Kernel.Tree)
            (β := _root_.List _root_.Geb.Kernel.Tree)
            x4
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (fun (_ : _root_.Geb.Kernel.Tree)
               (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
              x7);
          ((x2).1, (x5 :: (x2).2))
        else
          let _ : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x3;
          (_root_.Geb.Kernel.leaf 0, (x2).2))
      (_root_.Geb.Kernel.leaf 1, ([] : _root_.List _root_.Geb.Kernel.Tree))
      x0;
    x1

def «Conversion.csConsts» :=
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

def «Conversion.csEntries» :=
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
                                 let _ : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                   x6
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x9);
                                 let x9 : _root_.Geb.Kernel.Tree := x5;
                                 let x10 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x9;
                                 let x11 : _root_.List _root_.Geb.Kernel.Tree := x10; x11);
    x1

def «Conversion.csIndices» :=
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

def «Conversion.cdBase» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «Conversion.cdConv» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «Conversion.cdReady» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 2)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «Conversion.convDeclStep» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := x3;
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
                                          let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Derivation.declStep»
                                            x0
                                            x1
                                            x6;
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
                                            let x15 : _root_.List
                                              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                              (α := _root_.Geb.Kernel.Tree)
                                              (β := _root_.List _root_.Geb.Kernel.Tree)
                                              x13
                                              ([] : _root_.List _root_.Geb.Kernel.Tree)
                                              (fun (_ : _root_.Geb.Kernel.Tree)
                                                 (x16 : _root_.List _root_.Geb.Kernel.Tree) =>
                                                x16);
                                            let x16 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                              (α := _root_.Geb.Kernel.Tree)
                                              (β := _root_.Geb.Kernel.Tree)
                                              x15
                                              (_root_.Geb.Kernel.leaf 0)
                                              (fun (x16 : _root_.Geb.Kernel.Tree)
                                                 (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                                x16);
                                            let _ : _root_.List
                                              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                              (α := _root_.Geb.Kernel.Tree)
                                              (β := _root_.List _root_.Geb.Kernel.Tree)
                                              x15
                                              ([] : _root_.List _root_.Geb.Kernel.Tree)
                                              (fun (_ : _root_.Geb.Kernel.Tree)
                                                 (x18 : _root_.List _root_.Geb.Kernel.Tree) =>
                                                x18);
                                            _root_.GebMirror.Metalogic.«$436f6e76657273696f6e2f4f436f6e7653746174652e6a757374»
                                              (_root_.GebMirror.Metalogic.«Conversion.convState»
                                                x14
                                                x16
                                                (_root_.GebMirror.Metalogic.«Conversion.indices» x2))
                                          else
                                            let _ : _root_.List
                                              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                              x8;
                                            _root_.GebMirror.Metalogic.«$436f6e76657273696f6e2f4f436f6e7653746174652e6e6f7468696e67»
                                        else
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
                                            if (_root_.GebMirror.Metalogic.«Conversion.thmConvChecks»
                                              x0
                                              x1
                                              x2
                                              x6
                                              x8).label ≠ 0 then
                                              _root_.GebMirror.Metalogic.«$436f6e76657273696f6e2f4f436f6e7653746174652e6a757374»
                                                (_root_.GebMirror.Metalogic.«Conversion.convState»
                                                  x0
                                                  (_root_.GebMirror.Metalogic.«Derivation.entries»
                                                    (_root_.GebMirror.Metalogic.«Derivation.push»
                                                      x1
                                                      (_root_.GebMirror.Metalogic.«Derivation.entLang» x6)))
                                                  (_root_.GebMirror.Metalogic.«Conversion.indices» x2))
                                            else
                                              _root_.GebMirror.Metalogic.«$436f6e76657273696f6e2f4f436f6e7653746174652e6e6f7468696e67»
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
                                            if (_root_.GebMirror.Metalogic.«Literals.ready»
                                              x0
                                              x1
                                              x6).label ≠ 0 then
                                              _root_.GebMirror.Metalogic.«$436f6e76657273696f6e2f4f436f6e7653746174652e6a757374»
                                                (_root_.GebMirror.Metalogic.«Conversion.convState»
                                                  x0
                                                  (_root_.GebMirror.Metalogic.«Derivation.entries» x1)
                                                  (_root_.GebMirror.Metalogic.«Conversion.indices» (x6 :: x2)))
                                            else
                                              _root_.GebMirror.Metalogic.«$436f6e76657273696f6e2f4f436f6e7653746174652e6e6f7468696e67»);
    x4

def «$436f6e76657273696f6e2f436f6e764465636c732e73696e676c65» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      ([] : _root_.List _root_.Geb.Kernel.Tree));
    x1

def «$436f6e76657273696f6e2f436f6e764465636c732e6c656e677468» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (_ : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.add x2 (_root_.Geb.Kernel.leaf 1))
      (_root_.Geb.Kernel.leaf 0)
      x0;
    x1

def «$436f6e76657273696f6e2f436f6e764465636c732e617070656e64» :=
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

def «$436f6e76657273696f6e2f436f6e764465636c732e72657665727365» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree →
           _root_.List _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        x2 (x1 :: x3))
      (fun (x1 : _root_.List _root_.Geb.Kernel.Tree) => x1)
      x0
      ([] : _root_.List _root_.Geb.Kernel.Tree);
    x1

def «$436f6e76657273696f6e2f436f6e764465636c732e7461696c» :=
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

def «$436f6e76657273696f6e2f436f6e764465636c732e64726f70» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.iter
      (α := _root_.List _root_.Geb.Kernel.Tree)
      _root_.GebMirror.Metalogic.«$436f6e76657273696f6e2f436f6e764465636c732e7461696c»
      x1
      x0;
    x2

def «$436f6e76657273696f6e2f436f6e764465636c732e61744f72» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«$436f6e76657273696f6e2f436f6e764465636c732e64726f70»
        x2
        x1)
      x0
      (fun (x3 : _root_.Geb.Kernel.Tree)
         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        x3);
    x3

def «Conversion.checkConvDev» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (x3 : _root_.Geb.Kernel.Tree) (x4 : _root_.Geb.Kernel.Tree) =>
        let x5 : _root_.Geb.Kernel.Tree := x4;
        if (_root_.Geb.Kernel.Const.eq
          (_root_.Geb.Kernel.Const.label x5)
          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
          let x6 : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x5;
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
          _root_.GebMirror.Metalogic.«Conversion.convDeclStep»
            (_root_.GebMirror.Metalogic.«Conversion.csConsts» x7)
            (_root_.GebMirror.Metalogic.«Conversion.csEntries» x7)
            (_root_.GebMirror.Metalogic.«Conversion.csIndices» x7)
            x3
        else
          let _ : _root_.List
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x5;
          _root_.GebMirror.Metalogic.«$436f6e76657273696f6e2f4f436f6e7653746174652e6e6f7468696e67»)
      (_root_.GebMirror.Metalogic.«$436f6e76657273696f6e2f4f436f6e7653746174652e6a757374»
        (_root_.GebMirror.Metalogic.«Conversion.convState»
          x0
          (_root_.GebMirror.Metalogic.«Derivation.entries» x1)
          (_root_.GebMirror.Metalogic.«Conversion.indices»
            ([] : _root_.List _root_.Geb.Kernel.Tree))))
      (_root_.GebMirror.Metalogic.«$436f6e76657273696f6e2f436f6e764465636c732e72657665727365»
        x2);
    x3

end GebMirror.Metalogic

end
