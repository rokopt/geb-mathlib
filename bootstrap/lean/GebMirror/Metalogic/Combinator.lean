module

public import GebMirror.Metalogic.Tactics

/-! Generated from a Geb program by `bootstrap/stage1/lean.geb`. -/

@[expose] public section

open Geb.Kernel
open Geb.Kernel renaming Tree → T

namespace GebMirror.Metalogic

def «$436f6d62696e61746f722f536571732e73696e676c65» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      ([] : _root_.List _root_.Geb.Kernel.Tree));
    x1

def «$436f6d62696e61746f722f536571732e6c656e677468» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (_ : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.add x2 (_root_.Geb.Kernel.leaf 1))
      (_root_.Geb.Kernel.leaf 0)
      x0;
    x1

def «$436f6d62696e61746f722f536571732e617070656e64» :=
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

def «$436f6d62696e61746f722f536571732e72657665727365» :=
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

def «$436f6d62696e61746f722f536571732e7461696c» :=
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

def «$436f6d62696e61746f722f536571732e64726f70» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.iter
      (α := _root_.List _root_.Geb.Kernel.Tree)
      _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f536571732e7461696c»
      x1
      x0;
    x2

def «$436f6d62696e61746f722f536571732e61744f72» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f536571732e64726f70» x2 x1)
      x0
      (fun (x3 : _root_.Geb.Kernel.Tree)
         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        x3);
    x3

def «$436f6d62696e61746f722f4f70536967732e73696e676c65» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      ([] : _root_.List _root_.Geb.Kernel.Tree));
    x1

def «$436f6d62696e61746f722f4f70536967732e6c656e677468» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (_ : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.add x2 (_root_.Geb.Kernel.leaf 1))
      (_root_.Geb.Kernel.leaf 0)
      x0;
    x1

def «$436f6d62696e61746f722f4f70536967732e617070656e64» :=
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

def «$436f6d62696e61746f722f4f70536967732e72657665727365» :=
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

def «$436f6d62696e61746f722f4f70536967732e7461696c» :=
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

def «$436f6d62696e61746f722f4f70536967732e64726f70» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.iter
      (α := _root_.List _root_.Geb.Kernel.Tree)
      _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f70536967732e7461696c»
      x1
      x0;
    x2

def «$436f6d62696e61746f722f4f70536967732e61744f72» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f70536967732e64726f70» x2 x1)
      x0
      (fun (x3 : _root_.Geb.Kernel.Tree)
         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        x3);
    x3

def «$436f6d62696e61746f722f45716e732e73696e676c65» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      ([] : _root_.List _root_.Geb.Kernel.Tree));
    x1

def «$436f6d62696e61746f722f45716e732e6c656e677468» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (_ : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.add x2 (_root_.Geb.Kernel.leaf 1))
      (_root_.Geb.Kernel.leaf 0)
      x0;
    x1

def «$436f6d62696e61746f722f45716e732e617070656e64» :=
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

def «$436f6d62696e61746f722f45716e732e72657665727365» :=
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

def «$436f6d62696e61746f722f45716e732e7461696c» :=
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

def «$436f6d62696e61746f722f45716e732e64726f70» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.iter
      (α := _root_.List _root_.Geb.Kernel.Tree)
      _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f45716e732e7461696c»
      x1
      x0;
    x2

def «$436f6d62696e61746f722f45716e732e61744f72» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f45716e732e64726f70» x2 x1)
      x0
      (fun (x3 : _root_.Geb.Kernel.Tree)
         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        x3);
    x3

def «$436f6d62696e61746f722f45716e4c2e6c32» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)));
    x2

def «$436f6d62696e61746f722f45716e4c2e6c33» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f45716e4c2e6c32» x1 x2));
    x3

def «$436f6d62696e61746f722f45716e4c2e6c34» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f45716e4c2e6c33» x1 x2 x3));
    x4

def «$436f6d62696e61746f722f45716e4c2e6c35» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f45716e4c2e6c34» x1 x2 x3 x4));
    x5

def «$436f6d62696e61746f722f45716e4c2e6c36» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree) =>
    let x6 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f45716e4c2e6c35»
        x1
        x2
        x3
        x4
        x5));
    x6

def «$436f6d62696e61746f722f4f4f4466642e6e6f7468696e67» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$436f6d62696e61746f722f4f4f4466642e6a757374» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «$436f6d62696e61746f722f4f4f4466642e69734a757374» :=
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

def «$436f6d62696e61746f722f4f4f4466642e66726f6d4d61796265» :=
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

def «$436f6d62696e61746f722f4f4f4466642e6e74684f66» :=
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
      _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f4f4466642e6e6f7468696e67»
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f4f4466642e6a757374» x2);
    x2

def «$436f6d62696e61746f722f4f4f4466642e616c6c4a757374» :=
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

def «$436f6d62696e61746f722f50616972542e6d6170» :=
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
                                              (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f45716e732e6c656e677468»
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

def «$436f6d62696e61746f722f4f5054792e6e6f7468696e67» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$436f6d62696e61746f722f4f5054792e6a757374» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «$436f6d62696e61746f722f4f5054792e69734a757374» :=
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

def «$436f6d62696e61746f722f4f5054792e66726f6d4d61796265» :=
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

def «$436f6d62696e61746f722f4f5054792e6e74684f66» :=
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
      _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f5054792e6e6f7468696e67»
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f5054792e6a757374» x2);
    x2

def «$436f6d62696e61746f722f4f5054792e616c6c4a757374» :=
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

def «$436f6d62696e61746f722f54794c2e73696e676c65» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      ([] : _root_.List _root_.Geb.Kernel.Tree));
    x1

def «$436f6d62696e61746f722f54794c2e6c656e677468» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (_ : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.add x2 (_root_.Geb.Kernel.leaf 1))
      (_root_.Geb.Kernel.leaf 0)
      x0;
    x1

def «$436f6d62696e61746f722f54794c2e617070656e64» :=
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

def «$436f6d62696e61746f722f54794c2e72657665727365» :=
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

def «$436f6d62696e61746f722f54794c2e7461696c» :=
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

def «$436f6d62696e61746f722f54794c2e64726f70» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.iter
      (α := _root_.List _root_.Geb.Kernel.Tree)
      _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f54794c2e7461696c»
      x1
      x0;
    x2

def «$436f6d62696e61746f722f54794c2e61744f72» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f54794c2e64726f70» x2 x1)
      x0
      (fun (x3 : _root_.Geb.Kernel.Tree)
         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        x3);
    x3

def «$436f6d62696e61746f722f59542e6d6170» :=
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

def «$436f6d62696e61746f722f4465764c2e73696e676c65» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      ([] : _root_.List _root_.Geb.Kernel.Tree));
    x1

def «$436f6d62696e61746f722f4465764c2e6c656e677468» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (_ : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.add x2 (_root_.Geb.Kernel.leaf 1))
      (_root_.Geb.Kernel.leaf 0)
      x0;
    x1

def «$436f6d62696e61746f722f4465764c2e617070656e64» :=
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

def «$436f6d62696e61746f722f4465764c2e72657665727365» :=
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

def «$436f6d62696e61746f722f4465764c2e7461696c» :=
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

def «$436f6d62696e61746f722f4465764c2e64726f70» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.iter
      (α := _root_.List _root_.Geb.Kernel.Tree)
      _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4465764c2e7461696c»
      x1
      x0;
    x2

def «$436f6d62696e61746f722f4465764c2e61744f72» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4465764c2e64726f70» x2 x1)
      x0
      (fun (x3 : _root_.Geb.Kernel.Tree)
         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        x3);
    x3

def «$436f6d62696e61746f722f4f4465762e6e6f7468696e67» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$436f6d62696e61746f722f4f4465762e6a757374» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «$436f6d62696e61746f722f4f4465762e69734a757374» :=
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

def «$436f6d62696e61746f722f4f4465762e66726f6d4d61796265» :=
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

def «$436f6d62696e61746f722f4f4465762e6e74684f66» :=
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
      _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f4465762e6e6f7468696e67»
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f4465762e6a757374» x2);
    x2

def «$436f6d62696e61746f722f4f4465762e616c6c4a757374» :=
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
          _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f5054792e6a757374» x8
        else
          x3)
      _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f5054792e6e6f7468696e67»
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
          _root_.GebMirror.Metalogic.«$4c616e67756167652f4f54506169722e6a757374» x8
        else
          x3)
      _root_.GebMirror.Metalogic.«$4c616e67756167652f4f54506169722e6e6f7468696e67»
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

def «$436f6d62696e61746f722f43542e726573» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «$436f6d62696e61746f722f43542e626164» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$436f6d62696e61746f722f43542e6f6b» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «$436f6d62696e61746f722f43542e70757265» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (_ : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
      _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e6f6b»
        (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e726573» x0 x2));
    x1

def «$436f6d62696e61746f722f43542e6661696c» :=
  fun (_ : _root_.Geb.Kernel.Tree) (_ : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e626164»;
    x2

def «$436f6d62696e61746f722f43542e6f72456c7365» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      let x5 : _root_.Geb.Kernel.Tree := x4;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x5)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
        let x6 : _root_.List
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x5;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x5;
        x1 x2 x3);
    x2

def «$436f6d62696e61746f722f43592e726573» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «$436f6d62696e61746f722f43592e626164» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$436f6d62696e61746f722f43592e6f6b» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «$436f6d62696e61746f722f43592e70757265» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (_ : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
      _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43592e6f6b»
        (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43592e726573» x0 x2));
    x1

def «$436f6d62696e61746f722f43592e6661696c» :=
  fun (_ : _root_.Geb.Kernel.Tree) (_ : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43592e626164»;
    x2

def «$436f6d62696e61746f722f43592e6f72456c7365» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      let x5 : _root_.Geb.Kernel.Tree := x4;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x5)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
        let x6 : _root_.List
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x5;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x5;
        x1 x2 x3);
    x2

def «$436f6d62696e61746f722f43512e726573» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «$436f6d62696e61746f722f43512e626164» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$436f6d62696e61746f722f43512e6f6b» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «$436f6d62696e61746f722f43512e70757265» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (_ : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
      _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43512e6f6b»
        (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43512e726573» x0 x2));
    x1

def «$436f6d62696e61746f722f43512e6661696c» :=
  fun (_ : _root_.Geb.Kernel.Tree) (_ : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43512e626164»;
    x2

def «$436f6d62696e61746f722f43512e6f72456c7365» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      let x5 : _root_.Geb.Kernel.Tree := x4;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x5)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
        let x6 : _root_.List
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x5;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x5;
        x1 x2 x3);
    x2

def «$436f6d62696e61746f722f43532e726573» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «$436f6d62696e61746f722f43532e626164» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$436f6d62696e61746f722f43532e6f6b» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «$436f6d62696e61746f722f43532e70757265» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (_ : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
      _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43532e6f6b»
        (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43532e726573» x0 x2));
    x1

def «$436f6d62696e61746f722f43532e6661696c» :=
  fun (_ : _root_.Geb.Kernel.Tree) (_ : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43532e626164»;
    x2

def «$436f6d62696e61746f722f43532e6f72456c7365» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      let x5 : _root_.Geb.Kernel.Tree := x4;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x5)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
        let x6 : _root_.List
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x5;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x5;
        x1 x2 x3);
    x2

def «$436f6d62696e61746f722f43502e726573» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «$436f6d62696e61746f722f43502e626164» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$436f6d62696e61746f722f43502e6f6b» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «$436f6d62696e61746f722f43502e70757265» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (_ : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
      _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43502e6f6b»
        (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43502e726573» x0 x2));
    x1

def «$436f6d62696e61746f722f43502e6661696c» :=
  fun (_ : _root_.Geb.Kernel.Tree) (_ : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43502e626164»;
    x2

def «$436f6d62696e61746f722f43502e6f72456c7365» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      let x5 : _root_.Geb.Kernel.Tree := x4;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x5)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
        let x6 : _root_.List
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x5;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x5;
        x1 x2 x3);
    x2

def «$436f6d62696e61746f722f43452e726573» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «$436f6d62696e61746f722f43452e626164» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$436f6d62696e61746f722f43452e6f6b» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «$436f6d62696e61746f722f43452e70757265» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (_ : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
      _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43452e6f6b»
        (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43452e726573» x0 x2));
    x1

def «$436f6d62696e61746f722f43452e6661696c» :=
  fun (_ : _root_.Geb.Kernel.Tree) (_ : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43452e626164»;
    x2

def «$436f6d62696e61746f722f43452e6f72456c7365» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      let x5 : _root_.Geb.Kernel.Tree := x4;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x5)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
        let x6 : _root_.List
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x5;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x5;
        x1 x2 x3);
    x2

def «$436f6d62696e61746f722f43432e726573» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «$436f6d62696e61746f722f43432e626164» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$436f6d62696e61746f722f43432e6f6b» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «$436f6d62696e61746f722f43432e70757265» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (_ : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
      _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43432e6f6b»
        (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43432e726573» x0 x2));
    x1

def «$436f6d62696e61746f722f43432e6661696c» :=
  fun (_ : _root_.Geb.Kernel.Tree) (_ : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43432e626164»;
    x2

def «$436f6d62696e61746f722f43432e6f72456c7365» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      let x5 : _root_.Geb.Kernel.Tree := x4;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x5)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
        let x6 : _root_.List
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x5;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x5;
        x1 x2 x3);
    x2

def «$436f6d62696e61746f722f4359732e726573» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «$436f6d62696e61746f722f4359732e626164» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$436f6d62696e61746f722f4359732e6f6b» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «$436f6d62696e61746f722f4359732e70757265» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (_ : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
      _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4359732e6f6b»
        (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4359732e726573» x0 x2));
    x1

def «$436f6d62696e61746f722f4359732e6661696c» :=
  fun (_ : _root_.Geb.Kernel.Tree) (_ : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4359732e626164»;
    x2

def «$436f6d62696e61746f722f4359732e6f72456c7365» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      let x5 : _root_.Geb.Kernel.Tree := x4;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x5)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
        let x6 : _root_.List
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x5;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x5;
        x1 x2 x3);
    x2

def «$436f6d62696e61746f722f4350732e726573» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «$436f6d62696e61746f722f4350732e626164» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$436f6d62696e61746f722f4350732e6f6b» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «$436f6d62696e61746f722f4350732e70757265» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (_ : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
      _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4350732e6f6b»
        (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4350732e726573» x0 x2));
    x1

def «$436f6d62696e61746f722f4350732e6661696c» :=
  fun (_ : _root_.Geb.Kernel.Tree) (_ : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4350732e626164»;
    x2

def «$436f6d62696e61746f722f4350732e6f72456c7365» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      let x5 : _root_.Geb.Kernel.Tree := x4;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x5)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
        let x6 : _root_.List
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x5;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x5;
        x1 x2 x3);
    x2

def «$436f6d62696e61746f722f434f592e726573» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «$436f6d62696e61746f722f434f592e626164» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$436f6d62696e61746f722f434f592e6f6b» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «$436f6d62696e61746f722f434f592e70757265» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (_ : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
      _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f434f592e6f6b»
        (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f434f592e726573» x0 x2));
    x1

def «$436f6d62696e61746f722f434f592e6661696c» :=
  fun (_ : _root_.Geb.Kernel.Tree) (_ : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f434f592e626164»;
    x2

def «$436f6d62696e61746f722f434f592e6f72456c7365» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      let x5 : _root_.Geb.Kernel.Tree := x4;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x5)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
        let x6 : _root_.List
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x5;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x5;
        x1 x2 x3);
    x2

def «$436f6d62696e61746f722f434f502e726573» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «$436f6d62696e61746f722f434f502e626164» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$436f6d62696e61746f722f434f502e6f6b» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «$436f6d62696e61746f722f434f502e70757265» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (_ : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
      _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f434f502e6f6b»
        (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f434f502e726573» x0 x2));
    x1

def «$436f6d62696e61746f722f434f502e6661696c» :=
  fun (_ : _root_.Geb.Kernel.Tree) (_ : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f434f502e626164»;
    x2

def «$436f6d62696e61746f722f434f502e6f72456c7365» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      let x5 : _root_.Geb.Kernel.Tree := x4;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x5)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
        let x6 : _root_.List
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x5;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x5;
        x1 x2 x3);
    x2

def «$436f6d62696e61746f722f43412e726573» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «$436f6d62696e61746f722f43412e626164» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$436f6d62696e61746f722f43412e6f6b» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «$436f6d62696e61746f722f43412e70757265» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (_ : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
      _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43412e6f6b»
        (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43412e726573» x0 x2));
    x1

def «$436f6d62696e61746f722f43412e6661696c» :=
  fun (_ : _root_.Geb.Kernel.Tree) (_ : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43412e626164»;
    x2

def «$436f6d62696e61746f722f43412e6f72456c7365» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      let x5 : _root_.Geb.Kernel.Tree := x4;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x5)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
        let x6 : _root_.List
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x5;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x5;
        x1 x2 x3);
    x2

def «Combinator.bindTToT» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x4)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
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
        let x8 : _root_.Geb.Kernel.Tree := x6;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x4;
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e626164»);
    x2

def «Combinator.bindTToY» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x4)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
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
        let x8 : _root_.Geb.Kernel.Tree := x6;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x4;
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43592e626164»);
    x2

def «Combinator.bindTToP» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x4)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
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
        let x8 : _root_.Geb.Kernel.Tree := x6;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x4;
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43502e626164»);
    x2

def «Combinator.bindTToC» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x4)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
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
        let x8 : _root_.Geb.Kernel.Tree := x6;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x4;
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43432e626164»);
    x2

def «Combinator.bindYToT» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x4)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
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
        let x8 : _root_.Geb.Kernel.Tree := x6;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x4;
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e626164»);
    x2

def «Combinator.bindYToY» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x4)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
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
        let x8 : _root_.Geb.Kernel.Tree := x6;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x4;
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43592e626164»);
    x2

def «Combinator.bindYToP» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x4)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
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
        let x8 : _root_.Geb.Kernel.Tree := x6;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x4;
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43502e626164»);
    x2

def «Combinator.bindYToYs» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x4)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
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
        let x8 : _root_.Geb.Kernel.Tree := x6;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x4;
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4359732e626164»);
    x2

def «Combinator.bindYToA» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x4)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
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
        let x8 : _root_.Geb.Kernel.Tree := x6;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x4;
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43412e626164»);
    x2

def «Combinator.bindQToT» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x4)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
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
        let x8 : _root_.Geb.Kernel.Tree := x6;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x4;
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e626164»);
    x2

def «Combinator.bindQToP» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x4)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
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
        let x8 : _root_.Geb.Kernel.Tree := x6;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x4;
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43502e626164»);
    x2

def «Combinator.bindQToE» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x4)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
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
        let x8 : _root_.Geb.Kernel.Tree := x6;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x4;
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43452e626164»);
    x2

def «Combinator.bindSToY» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x4)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
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
        let x8 : _root_.Geb.Kernel.Tree := x6;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x4;
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43592e626164»);
    x2

def «Combinator.bindSToQ» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x4)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
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
        let x8 : _root_.Geb.Kernel.Tree := x6;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x4;
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43512e626164»);
    x2

def «Combinator.bindSToP» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x4)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
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
        let x8 : _root_.Geb.Kernel.Tree := x6;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x4;
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43502e626164»);
    x2

def «Combinator.bindPToT» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x4)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
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
        let x8 : _root_.Geb.Kernel.Tree := x6;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x4;
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e626164»);
    x2

def «Combinator.bindPToY» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x4)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
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
        let x8 : _root_.Geb.Kernel.Tree := x6;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x4;
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43592e626164»);
    x2

def «Combinator.bindPToP» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x4)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
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
        let x8 : _root_.Geb.Kernel.Tree := x6;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x4;
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43502e626164»);
    x2

def «Combinator.bindPToPs» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x4)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
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
        let x8 : _root_.Geb.Kernel.Tree := x6;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x4;
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4350732e626164»);
    x2

def «Combinator.bindPToOP» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x4)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
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
        let x8 : _root_.Geb.Kernel.Tree := x6;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x4;
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f434f502e626164»);
    x2

def «Combinator.bindEToT» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x4)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
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
        let x8 : _root_.Geb.Kernel.Tree := x6;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x4;
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e626164»);
    x2

def «Combinator.bindEToP» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x4)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
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
        let x8 : _root_.Geb.Kernel.Tree := x6;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x4;
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43502e626164»);
    x2

def «Combinator.bindCToT» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x4)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
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
        let x8 : _root_.Geb.Kernel.Tree := x6;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x4;
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e626164»);
    x2

def «Combinator.bindCToP» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x4)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
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
        let x8 : _root_.Geb.Kernel.Tree := x6;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x4;
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43502e626164»);
    x2

def «Combinator.bindCToE» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x4)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
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
        let x8 : _root_.Geb.Kernel.Tree := x6;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x4;
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43452e626164»);
    x2

def «Combinator.bindCToC» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x4)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
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
        let x8 : _root_.Geb.Kernel.Tree := x6;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x4;
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43432e626164»);
    x2

def «Combinator.bindYsToY» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x4)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
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
        let x8 : _root_.Geb.Kernel.Tree := x6;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x4;
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43592e626164»);
    x2

def «Combinator.bindYsToP» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x4)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
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
        let x8 : _root_.Geb.Kernel.Tree := x6;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x4;
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43502e626164»);
    x2

def «Combinator.bindYsToE» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x4)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
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
        let x8 : _root_.Geb.Kernel.Tree := x6;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x4;
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43452e626164»);
    x2

def «Combinator.bindYsToYs» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x4)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
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
        let x8 : _root_.Geb.Kernel.Tree := x6;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x4;
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4359732e626164»);
    x2

def «Combinator.bindPsToP» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x4)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
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
        let x8 : _root_.Geb.Kernel.Tree := x6;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x4;
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43502e626164»);
    x2

def «Combinator.bindPsToPs» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x4)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
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
        let x8 : _root_.Geb.Kernel.Tree := x6;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x4;
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4350732e626164»);
    x2

def «Combinator.bindOYToY» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x4)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
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
        let x8 : _root_.Geb.Kernel.Tree := x6;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x4;
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43592e626164»);
    x2

def «Combinator.bindOPToP» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x4)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
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
        let x8 : _root_.Geb.Kernel.Tree := x6;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x4;
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43502e626164»);
    x2

def «Combinator.bindAToP» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      let x4 : _root_.Geb.Kernel.Tree := x0 x2 x3;
      if (_root_.Geb.Kernel.Const.eq
        (_root_.Geb.Kernel.Const.label x4)
        (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
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
        let x8 : _root_.Geb.Kernel.Tree := x6;
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
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x4;
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43502e626164»);
    x2

def «Combinator.pmGet» :=
  fun (_ : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43532e6f6b»
      (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43532e726573» x1 x1);
    x2

def «Combinator.pmGuard» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (_ : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
      if (x0).label ≠ 0 then
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e6f6b»
          (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e726573»
            (_root_.Geb.Kernel.leaf 0)
            x2)
      else
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e626164»);
    x1

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
        _root_.GebMirror.Metalogic.«Combinator.bindTToC»
          (x0 x2)
          (fun (x4 : _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Metalogic.«Combinator.bindCToC»
              x3
              (fun (x5 : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43432e70757265»
                  (_root_.GebMirror.Metalogic.«Combinator.certs»
                    (x4 :: (_root_.GebMirror.Metalogic.«Combinator.certsOf» x5))))))
      (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43432e70757265»
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
        _root_.GebMirror.Metalogic.«Combinator.bindTToC»
          (x0 x2)
          (fun (x4 : _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Metalogic.«Combinator.bindCToC»
              x3
              (fun (x5 : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43432e70757265»
                  (_root_.GebMirror.Metalogic.«Combinator.certs»
                    (x4 :: (_root_.GebMirror.Metalogic.«Combinator.certsOf» x5))))))
      (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43432e70757265»
        (_root_.GebMirror.Metalogic.«Combinator.certs»
          ([] : _root_.List _root_.Geb.Kernel.Tree)))
      x1;
    x2

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
        _root_.GebMirror.Metalogic.«Combinator.bindYToYs»
          (x0 x2)
          (fun (x4 : _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Metalogic.«Combinator.bindYsToYs»
              x3
              (fun (x5 : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4359732e70757265»
                  (_root_.GebMirror.Metalogic.«Combinator.ptys»
                    (x4 :: (_root_.GebMirror.Metalogic.«Combinator.ptysOf» x5))))))
      (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4359732e70757265»
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
        _root_.GebMirror.Metalogic.«Combinator.bindYToYs»
          x1
          (fun (x3 : _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Metalogic.«Combinator.bindYsToYs»
              x2
              (fun (x4 : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4359732e70757265»
                  (_root_.GebMirror.Metalogic.«Combinator.ptys»
                    (x3 :: (_root_.GebMirror.Metalogic.«Combinator.ptysOf» x4))))))
      (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4359732e70757265»
        (_root_.GebMirror.Metalogic.«Combinator.ptys»
          ([] : _root_.List _root_.Geb.Kernel.Tree)))
      x0;
    x1

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
        _root_.GebMirror.Metalogic.«Combinator.bindPToPs»
          x1
          (fun (x3 : _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Metalogic.«Combinator.bindPsToPs»
              x2
              (fun (x4 : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4350732e70757265»
                  (_root_.GebMirror.Metalogic.«Combinator.pairs»
                    (x3 :: (_root_.GebMirror.Metalogic.«Combinator.pairsOf» x4))))))
      (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4350732e70757265»
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
      (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f45716e732e6c656e677468» x1,
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

def «Combinator.axiomAt» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (if (_root_.Geb.Kernel.Const.lt
      x0
      (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f536571732e6c656e677468»
        _root_.GebMirror.Metalogic.«Theory.axioms»)).label ≠ 0 then
      _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43512e70757265»
        (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f536571732e61744f72»
          _root_.GebMirror.Metalogic.«Combinator.seq0»
          _root_.GebMirror.Metalogic.«Theory.axioms»
          x0)
    else
      _root_.GebMirror.Metalogic.«Combinator.bindSToQ»
        _root_.GebMirror.Metalogic.«Combinator.pmGet»
        (fun (x1 : _root_.Geb.Kernel.Tree) =>
          let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.sub
            x0
            (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f536571732e6c656e677468»
              _root_.GebMirror.Metalogic.«Theory.axioms»);
          let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$5061727469616c486f726e2f4f504465666e2e6e74684f66»
            (_root_.GebMirror.Metalogic.«Combinator.stDefs» x1)
            (_root_.Geb.Kernel.Const.div x2 (_root_.Geb.Kernel.leaf 2));
          if (_root_.GebMirror.Metalogic.«$5061727469616c486f726e2f4f504465666e2e69734a757374»
            x3).label ≠ 0 then
            let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$5061727469616c486f726e2f4f53657175656e742e6e74684f66»
              (_root_.GebMirror.Metalogic.«PartialHorn.pdAxioms»
                (_root_.Geb.Kernel.Const.add
                  (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f70536967732e6c656e677468»
                    _root_.GebMirror.Metalogic.«Theory.sig»)
                  (_root_.Geb.Kernel.Const.div x2 (_root_.Geb.Kernel.leaf 2)))
                (_root_.GebMirror.Metalogic.«$5061727469616c486f726e2f4f504465666e2e66726f6d4d61796265»
                  _root_.GebMirror.Metalogic.«Combinator.pdefn0»
                  x3))
              (_root_.Geb.Kernel.Const.mod x2 (_root_.Geb.Kernel.leaf 2));
            if (_root_.GebMirror.Metalogic.«$5061727469616c486f726e2f4f53657175656e742e69734a757374»
              x4).label ≠ 0 then
              _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43512e70757265»
                (_root_.GebMirror.Metalogic.«$5061727469616c486f726e2f4f53657175656e742e66726f6d4d61796265»
                  _root_.GebMirror.Metalogic.«Combinator.seq0»
                  x4)
            else
              _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43512e6661696c»
          else
            _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43512e6661696c»));
    x1

def «Combinator.addLemma» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e6f6b»
        (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e726573»
          (_root_.GebMirror.Metalogic.«Combinator.scCite»
            x2
            (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4465764c2e6c656e677468»
              (_root_.GebMirror.Metalogic.«Combinator.stDev» x3)))
          (_root_.GebMirror.Metalogic.«Combinator.withDev»
            x3
            (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4465764c2e617070656e64»
              (_root_.GebMirror.Metalogic.«Combinator.stDev» x3)
              (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4465764c2e73696e676c65»
                (_root_.GebMirror.Metalogic.«Combinator.devEntry»
                  (_root_.GebMirror.Metalogic.«Combinator.scSeq» x2 x0)
                  x1))))));
    x2

def «Combinator.lookup» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (_ : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
      _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f434f592e6f6b»
        (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f434f592e726573»
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
      _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e6f6b»
        (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e726573»
          (_root_.Geb.Kernel.leaf 0)
          (_root_.GebMirror.Metalogic.«Combinator.withMemo»
            x2
            ((_root_.GebMirror.Metalogic.«Combinator.memoEntry»
              (_root_.GebMirror.Metalogic.«Combinator.tyT» x0)
              x0) ::
              (_root_.GebMirror.Metalogic.«Combinator.stMemo» x2)))));
    x1

def «Combinator.memoRet» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.bindTToY»
      (_root_.GebMirror.Metalogic.«Combinator.memoize» x0)
      (fun (_ : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43592e70757265» x0);
    x1

def «Combinator.dfdCert» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (fun (x2 : _root_.Geb.Kernel.Tree)
                                     (x3 : _root_.Geb.Kernel.Tree) =>
      if (_root_.GebMirror.Metalogic.«Combinator.stInfer» x3).label ≠ 0 then
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e6f6b»
          (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e726573»
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
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e6f6b»
          (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e726573»
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
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e6f6b»
          (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e726573»
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
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e626164»);
    x2

def «Combinator.proveHyp» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.bindYToT»
      (x0 x1 (_root_.GebMirror.Metalogic.«PartialHorn.eqLhs» x2))
      (fun (x3 : _root_.Geb.Kernel.Tree) =>
        if (_root_.Geb.Kernel.Const.equal
          (_root_.GebMirror.Metalogic.«PartialHorn.eqLhs» x2)
          (_root_.GebMirror.Metalogic.«PartialHorn.eqRhs» x2)).label ≠ 0 then
          _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e70757265»
            (_root_.GebMirror.Metalogic.«Combinator.tyDfd» x3)
        else
          _root_.GebMirror.Metalogic.«Combinator.bindYToT»
            (x0 x1 (_root_.GebMirror.Metalogic.«PartialHorn.eqRhs» x2))
            (fun (x4 : _root_.Geb.Kernel.Tree) =>
              _root_.GebMirror.Metalogic.«Combinator.objEq» x3 x4));
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
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.bindQToP»
      (_root_.GebMirror.Metalogic.«Combinator.axiomAt» x3)
      (fun (x5 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Combinator.bindCToP»
          (_root_.GebMirror.Metalogic.«Combinator.mapMEqC»
            (fun (x6 : _root_.Geb.Kernel.Tree) =>
              if (_root_.Geb.Kernel.Const.equal
                x6
                (_root_.GebMirror.Metalogic.«Theory.dfd»
                  (_root_.GebMirror.Metalogic.«PartialHorn.opVars»
                    x2
                    (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f54794c2e6c656e677468»
                      x1)))).label ≠ 0 then
                _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e70757265» x4
              else
                _root_.GebMirror.Metalogic.«Combinator.proveHyp» x0 x1 x6)
            (_root_.GebMirror.Metalogic.«PartialHorn.seqHyps» x5))
          (fun (x6 : _root_.Geb.Kernel.Tree) =>
            let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.cAx»
              x3
              (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f59542e6d6170»
                _root_.GebMirror.Metalogic.«Combinator.tyT»
                x1)
              (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f59542e6d6170»
                _root_.GebMirror.Metalogic.«Combinator.tyDfd»
                x1)
              (_root_.GebMirror.Metalogic.«Combinator.certsOf» x6);
            _root_.GebMirror.Metalogic.«Combinator.bindYToP»
              (x0
                x1
                (_root_.GebMirror.Metalogic.«PartialHorn.eqRhs»
                  (_root_.GebMirror.Metalogic.«PartialHorn.seqConcl» x5)))
              (fun (x8 : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43502e70757265»
                  (_root_.GebMirror.Metalogic.«Language.pr»
                    (_root_.GebMirror.Metalogic.«Combinator.tyLo» x8)
                    (_root_.GebMirror.Metalogic.«Combinator.cTrans»
                      x7
                      (_root_.GebMirror.Metalogic.«Combinator.tyLoC» x8))))));
    x5

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
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.bindSToY»
      _root_.GebMirror.Metalogic.«Combinator.pmGet»
      (fun (x4 : _root_.Geb.Kernel.Tree) =>
        let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$5061727469616c486f726e2f4f504465666e2e6e74684f66»
          (_root_.GebMirror.Metalogic.«Combinator.stDefs» x4)
          x1;
        if (_root_.GebMirror.Metalogic.«$5061727469616c486f726e2f4f504465666e2e69734a757374»
          x5).label ≠ 0 then
          let x6 : _root_.List
            _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f59542e6d6170»
            _root_.GebMirror.Metalogic.«Combinator.tyT»
            x3;
          let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«PartialHorn.phOp»
            (_root_.Geb.Kernel.Const.add
              (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f70536967732e6c656e677468»
                _root_.GebMirror.Metalogic.«Theory.sig»)
              x1)
            x6;
          _root_.GebMirror.Metalogic.«Combinator.bindYToY»
            (x0
              x3
              (_root_.GebMirror.Metalogic.«PartialHorn.pdBody»
                (_root_.GebMirror.Metalogic.«$5061727469616c486f726e2f4f504465666e2e66726f6d4d61796265»
                  _root_.GebMirror.Metalogic.«Combinator.pdefn0»
                  x5)))
            (fun (x8 : _root_.Geb.Kernel.Tree) =>
              _root_.GebMirror.Metalogic.«Combinator.bindSToY»
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
                    _root_.GebMirror.Metalogic.«Combinator.bindTToY»
                      (_root_.GebMirror.Metalogic.«Combinator.addLemma»
                        (_root_.GebMirror.Metalogic.«PartialHorn.eqn»
                          x7
                          (_root_.GebMirror.Metalogic.«Combinator.tyT» x8))
                        (_root_.GebMirror.Metalogic.«Combinator.cAx»
                          (_root_.GebMirror.Metalogic.«Infer.defAxIdx» x1)
                          x6
                          (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f59542e6d6170»
                            _root_.GebMirror.Metalogic.«Combinator.tyDfd»
                            x3)
                          (_root_.GebMirror.Metalogic.«Prelude.single»
                            (_root_.GebMirror.Metalogic.«Combinator.tyDfd» x8))))
                      (fun (x10 : _root_.Geb.Kernel.Tree) =>
                        _root_.GebMirror.Metalogic.«Combinator.bindTToY»
                          (_root_.GebMirror.Metalogic.«Combinator.addLemma»
                            (_root_.GebMirror.Metalogic.«Theory.dfd» x7)
                            (_root_.GebMirror.Metalogic.«Combinator.cTrans»
                              x10
                              (_root_.GebMirror.Metalogic.«Combinator.cSymm» x10)))
                          (fun (x11 : _root_.Geb.Kernel.Tree) =>
                            if (_root_.Geb.Kernel.Const.eq
                              x2
                              (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                              _root_.GebMirror.Metalogic.«Combinator.bindTToY»
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
                              _root_.GebMirror.Metalogic.«Combinator.bindTToY»
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
                                  _root_.GebMirror.Metalogic.«Combinator.bindTToY»
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
          _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43592e6661696c»);
    x4

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
                                     _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f59542e6d6170»
                                     _root_.GebMirror.Metalogic.«Combinator.tyT»
                                     x2;
                                   let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f4f4466642e6e74684f66»
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
                                         _root_.GebMirror.Metalogic.«Combinator.bindQToT»
                                           (_root_.GebMirror.Metalogic.«Combinator.axiomAt» x14)
                                           (fun (x16 : _root_.Geb.Kernel.Tree) =>
                                             _root_.GebMirror.Metalogic.«Combinator.bindCToT»
                                               (_root_.GebMirror.Metalogic.«Combinator.mapMEqC»
                                                 (_root_.GebMirror.Metalogic.«Combinator.proveHyp» x0 x2)
                                                 (_root_.GebMirror.Metalogic.«PartialHorn.seqHyps» x16))
                                               (fun (x17 : _root_.Geb.Kernel.Tree) =>
                                                 _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e70757265»
                                                   (_root_.GebMirror.Metalogic.«Combinator.cAx»
                                                     x14
                                                     x3
                                                     (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f59542e6d6170»
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
                                           _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e70757265»
                                             (_root_.GebMirror.Metalogic.«Combinator.cStrict»
                                               (_root_.Geb.Kernel.leaf 0)
                                               (_root_.GebMirror.Metalogic.«Combinator.cAx»
                                                 x14
                                                 x3
                                                 (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f59542e6d6170»
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
                                           _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e70757265»
                                             (_root_.GebMirror.Metalogic.«Combinator.cTrans»
                                               (_root_.GebMirror.Metalogic.«Combinator.cSymm» x16)
                                               x16)
                                     else
                                       let _ : _root_.List
                                         _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                         x8;
                                       _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e6661696c»
                                   else
                                     let _ : _root_.List
                                       _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                       x4;
                                     _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e6661696c»);
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
                                     (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f59542e6d6170»
                                       (fun (x4 : _root_.Geb.Kernel.Tree) =>
                                         if (_root_.Geb.Kernel.Const.eq
                                           (_root_.GebMirror.Metalogic.«Combinator.tySort» x4)
                                           (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                                           _root_.GebMirror.Metalogic.«Combinator.tyLo» x4
                                         else
                                           _root_.GebMirror.Metalogic.«Combinator.tyT» x4)
                                       x3);
                                   if (_root_.Geb.Kernel.Const.equal x4 x1).label ≠ 0 then
                                     _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43592e70757265»
                                       (_root_.GebMirror.Metalogic.«Combinator.pty»
                                         x1
                                         (_root_.Geb.Kernel.leaf 0)
                                         x2
                                         x1
                                         x2
                                         x1
                                         x2)
                                   else
                                     _root_.GebMirror.Metalogic.«Combinator.bindTToY»
                                       (_root_.GebMirror.Metalogic.«Combinator.eqCert»
                                         (_root_.GebMirror.Metalogic.«PartialHorn.eqn» x1 x4)
                                         (_root_.GebMirror.Metalogic.«Combinator.cCong»
                                           x2
                                           (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f59542e6d6170»
                                             (fun (x5 : _root_.Geb.Kernel.Tree) =>
                                               if (_root_.Geb.Kernel.Const.eq
                                                 (_root_.GebMirror.Metalogic.«Combinator.tySort» x5)
                                                 (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                                                 _root_.GebMirror.Metalogic.«Combinator.tyLoC» x5
                                               else
                                                 _root_.GebMirror.Metalogic.«Combinator.tyDfd» x5)
                                             x3)))
                                       (fun (x5 : _root_.Geb.Kernel.Tree) =>
                                         _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43592e70757265»
                                           (_root_.GebMirror.Metalogic.«Combinator.pty»
                                             x1
                                             (_root_.Geb.Kernel.leaf 0)
                                             x2
                                             x4
                                             x5
                                             x4
                                             x5)));
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
          (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f54794c2e6c656e677468» x5)
          (_root_.Geb.Kernel.leaf 1))).label ≠ 0 then
        let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f54794c2e61744f72»
          _root_.GebMirror.Metalogic.«Combinator.pty0»
          x5
          (_root_.Geb.Kernel.leaf 0);
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43592e70757265»
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
            (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f54794c2e6c656e677468» x5)
            (_root_.Geb.Kernel.leaf 1))).label ≠ 0 then
          let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f54794c2e61744f72»
            _root_.GebMirror.Metalogic.«Combinator.pty0»
            x5
            (_root_.Geb.Kernel.leaf 0);
          _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43592e70757265»
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
        _root_.GebMirror.Metalogic.«Combinator.bindPToY»
          (_root_.GebMirror.Metalogic.«Combinator.pBound»
            x0
            x5
            x1
            (_root_.GebMirror.Metalogic.«Prelude.get» (_root_.GebMirror.Metalogic.«Prelude.get» x6))
            x4)
          (fun (x8 : _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Metalogic.«Combinator.bindPToY»
              (_root_.GebMirror.Metalogic.«Combinator.pBound»
                x0
                x5
                x1
                (_root_.GebMirror.Metalogic.«Prelude.get» (_root_.GebMirror.Metalogic.«Prelude.get» x7))
                x4)
              (fun (x9 : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.Metalogic.«Combinator.bindTToY»
                  (_root_.GebMirror.Metalogic.«Combinator.eqCert»
                    (_root_.GebMirror.Metalogic.«PartialHorn.eqn»
                      (_root_.GebMirror.Metalogic.«Theory.dom» x3)
                      (_root_.GebMirror.Metalogic.«Language.p1» x8))
                    (_root_.GebMirror.Metalogic.«Language.p2» x8))
                  (fun (x10 : _root_.Geb.Kernel.Tree) =>
                    _root_.GebMirror.Metalogic.«Combinator.bindTToY»
                      (_root_.GebMirror.Metalogic.«Combinator.eqCert»
                        (_root_.GebMirror.Metalogic.«PartialHorn.eqn»
                          (_root_.GebMirror.Metalogic.«Theory.cod» x3)
                          (_root_.GebMirror.Metalogic.«Language.p1» x9))
                        (_root_.GebMirror.Metalogic.«Language.p2» x9))
                      (fun (x11 : _root_.Geb.Kernel.Tree) =>
                        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43592e70757265»
                          (_root_.GebMirror.Metalogic.«Combinator.pty»
                            x3
                            (_root_.Geb.Kernel.leaf 1)
                            x4
                            (_root_.GebMirror.Metalogic.«Language.p1» x8)
                            x10
                            (_root_.GebMirror.Metalogic.«Language.p1» x9)
                            x11)))))
      else
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43592e6661696c»);
    x6

def «Combinator.opSig0» :=
  _root_.GebMirror.Metalogic.«PartialHorn.opSig»
    (_root_.GebMirror.Metalogic.«PartialHorn.sorts»
      ([] : _root_.List _root_.Geb.Kernel.Tree))
    (_root_.Geb.Kernel.leaf 0)

def «Combinator.typeOp» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.bindSToY»
      _root_.GebMirror.Metalogic.«Combinator.pmGet»
      (fun (x3 : _root_.Geb.Kernel.Tree) =>
        let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$5061727469616c486f726e2f4f4f705369672e6e74684f66»
          (_root_.GebMirror.Metalogic.«Combinator.stSig» x3)
          x1;
        if (_root_.GebMirror.Metalogic.«$5061727469616c486f726e2f4f4f705369672e69734a757374»
          x4).label ≠ 0 then
          let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$5061727469616c486f726e2f4f4f705369672e66726f6d4d61796265»
            _root_.GebMirror.Metalogic.«Combinator.opSig0»
            x4;
          if (_root_.GebMirror.Metalogic.«Base.equalTs»
            (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f59542e6d6170»
              _root_.GebMirror.Metalogic.«Combinator.tySort»
              x2)
            (_root_.GebMirror.Metalogic.«PartialHorn.opArgs» x5)).label ≠ 0 then
            if (_root_.Geb.Kernel.Const.lt
              x1
              (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f70536967732e6c656e677468»
                _root_.GebMirror.Metalogic.«Theory.sig»)).label ≠ 0 then
              let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«PartialHorn.phOp»
                x1
                (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f59542e6d6170»
                  _root_.GebMirror.Metalogic.«Combinator.tyT»
                  x2);
              _root_.GebMirror.Metalogic.«Combinator.bindTToY»
                (_root_.GebMirror.Metalogic.«Combinator.typeOpDfd» x0 x1 x2)
                (fun (x7 : _root_.Geb.Kernel.Tree) =>
                  _root_.GebMirror.Metalogic.«Combinator.bindTToY»
                    (_root_.GebMirror.Metalogic.«Combinator.dfdCert» x6 x7)
                    (fun (x8 : _root_.Geb.Kernel.Tree) =>
                      _root_.GebMirror.Metalogic.«Combinator.bindYToY»
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
                  (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f70536967732e6c656e677468»
                    _root_.GebMirror.Metalogic.«Theory.sig»))
                (_root_.GebMirror.Metalogic.«PartialHorn.opSort» x5)
                x2
          else
            _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43592e6661696c»
        else
          _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43592e6661696c»);
    x3

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
                                       _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43592e6661696c»
                                   else
                                     _root_.GebMirror.Metalogic.«Combinator.bindOYToY»
                                       (_root_.GebMirror.Metalogic.«Combinator.lookup» (x2 x3))
                                       (fun (x6 : _root_.Geb.Kernel.Tree) =>
                                         if (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f5054792e69734a757374»
                                           x6).label ≠ 0 then
                                           _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43592e70757265»
                                             (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f5054792e66726f6d4d61796265»
                                               _root_.GebMirror.Metalogic.«Combinator.pty0»
                                               x6)
                                         else
                                           _root_.GebMirror.Metalogic.«Combinator.bindYsToY»
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
        let x10 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$5061727469616c486f726e2f4f45716e2e6e74684f66»
          (_root_.GebMirror.Metalogic.«Combinator.scHyps» x5)
          x9;
        if (_root_.GebMirror.Metalogic.«$5061727469616c486f726e2f4f45716e2e69734a757374»
          x10).label ≠ 0 then
          _root_.GebMirror.Metalogic.«Combinator.bindYToP»
            (x0
              (_root_.GebMirror.Metalogic.«PartialHorn.eqRhs»
                (_root_.GebMirror.Metalogic.«$5061727469616c486f726e2f4f45716e2e66726f6d4d61796265»
                  _root_.GebMirror.Metalogic.«Combinator.eqn0»
                  x10)))
            (fun (x11 : _root_.Geb.Kernel.Tree) =>
              _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43502e70757265»
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
          _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43502e626164»
      else
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43502e6f6b»
          (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43502e726573»
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
          _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43592e6f6b»
            (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43592e726573»
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
            _root_.GebMirror.Metalogic.«Combinator.bindPToY»
              (_root_.GebMirror.Metalogic.«Combinator.varSide»
                x0
                x1
                x6
                (_root_.Geb.Kernel.leaf 0)
                (_root_.Geb.Kernel.leaf 0))
              (fun (x7 : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.Metalogic.«Combinator.bindPToY»
                  (_root_.GebMirror.Metalogic.«Combinator.varSide»
                    x0
                    x1
                    x6
                    (_root_.Geb.Kernel.leaf 1)
                    (_root_.Geb.Kernel.leaf 1))
                  (fun (x8 : _root_.Geb.Kernel.Tree) =>
                    _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43592e70757265»
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
            _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43592e626164»
      else
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43592e626164»);
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
            let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f5054792e6e74684f66»
              x1
              x3;
            if (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f5054792e69734a757374»
              x4).label ≠ 0 then
              _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43592e70757265»
                (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f5054792e66726f6d4d61796265»
                  _root_.GebMirror.Metalogic.«Combinator.pty0»
                  x4)
            else
              _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43592e6661696c»)
          (_root_.GebMirror.Metalogic.«PartialHorn.phSubst»
            (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f59542e6d6170»
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
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43592e6661696c»,
        fun (_ : _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43592e6661696c»))

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

def «$436f6d62696e61746f722f4465665369672e6d6170» :=
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
        (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f70536967732e617070656e64»
          _root_.GebMirror.Metalogic.«Theory.sig»
          (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4465665369672e6d6170»
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
                                     _root_.GebMirror.Metalogic.«Combinator.bindSToQ»
                                       _root_.GebMirror.Metalogic.«Combinator.pmGet»
                                       (fun (x5 : _root_.Geb.Kernel.Tree) =>
                                         let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f4465762e6e74684f66»
                                           (_root_.GebMirror.Metalogic.«Combinator.stDev» x5)
                                           x3;
                                         if (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f4465762e69734a757374»
                                           x6).label ≠ 0 then
                                           _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43512e70757265»
                                             (_root_.GebMirror.Metalogic.«Combinator.devSeq»
                                               (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f4465762e66726f6d4d61796265»
                                                 _root_.GebMirror.Metalogic.«Combinator.dev0»
                                                 x6))
                                         else
                                           _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43512e6661696c»));
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

def «$436f6d62696e61746f722f527752756c65732e73696e676c65» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      ([] : _root_.List _root_.Geb.Kernel.Tree));
    x1

def «$436f6d62696e61746f722f527752756c65732e6c656e677468» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (_ : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.add x2 (_root_.Geb.Kernel.leaf 1))
      (_root_.Geb.Kernel.leaf 0)
      x0;
    x1

def «$436f6d62696e61746f722f527752756c65732e617070656e64» :=
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

def «$436f6d62696e61746f722f527752756c65732e72657665727365» :=
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

def «$436f6d62696e61746f722f527752756c65732e7461696c» :=
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

def «$436f6d62696e61746f722f527752756c65732e64726f70» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.iter
      (α := _root_.List _root_.Geb.Kernel.Tree)
      _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f527752756c65732e7461696c»
      x1
      x0;
    x2

def «$436f6d62696e61746f722f527752756c65732e61744f72» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f527752756c65732e64726f70»
        x2
        x1)
      x0
      (fun (x3 : _root_.Geb.Kernel.Tree)
         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        x3);
    x3

def «$436f6d62696e61746f722f52774c2e6c32» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)));
    x2

def «$436f6d62696e61746f722f52774c2e6c33» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f52774c2e6c32» x1 x2));
    x3

def «$436f6d62696e61746f722f52774c2e6c34» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f52774c2e6c33» x1 x2 x3));
    x4

def «$436f6d62696e61746f722f52774c2e6c35» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f52774c2e6c34» x1 x2 x3 x4));
    x5

def «$436f6d62696e61746f722f52774c2e6c36» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree) =>
    let x6 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f52774c2e6c35»
        x1
        x2
        x3
        x4
        x5));
    x6

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

def «$436f6d62696e61746f722f4f4d617463682e6e6f7468696e67» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$436f6d62696e61746f722f4f4d617463682e6a757374» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «$436f6d62696e61746f722f4f4d617463682e69734a757374» :=
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

def «$436f6d62696e61746f722f4f4d617463682e66726f6d4d61796265» :=
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

def «$436f6d62696e61746f722f4f4d617463682e6e74684f66» :=
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
      _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f4d617463682e6e6f7468696e67»
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f4d617463682e6a757374» x2);
    x2

def «$436f6d62696e61746f722f4f4d617463682e616c6c4a757374» :=
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
                                          _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f4d617463682e6e6f7468696e67»);
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
          (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f4d617463682e6a757374» x6)
          (fun (x7 : _root_.Geb.Kernel.Tree)
             (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Metalogic.«Combinator.bindM»
              (x3 x7 x6)
              (fun (x9 : _root_.Geb.Kernel.Tree) => x4 x8 x9)))
      (fun (_ : _root_.List _root_.Geb.Kernel.Tree)
         (x4 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f4d617463682e6a757374» x4)
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
                _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f4d617463682e6a757374» x5
              else
                if (_root_.Geb.Kernel.Const.equal
                  (_root_.GebMirror.Metalogic.«Prelude.nth» x1 x7)
                  (_root_.GebMirror.Metalogic.«Prelude.some»
                    (_root_.Geb.Kernel.leaf 0))).label ≠ 0 then
                  _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f4d617463682e6a757374»
                    (_root_.GebMirror.Metalogic.«Combinator.msDefer» x5 x2 x4)
                else
                  _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f4d617463682e6e6f7468696e67»
            else
              _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f4d617463682e6a757374»
                (_root_.GebMirror.Metalogic.«Combinator.matchSt»
                  (_root_.GebMirror.Metalogic.«Combinator.opts»
                    (_root_.GebMirror.Metalogic.«Prover.setAt»
                      (_root_.GebMirror.Metalogic.«Combinator.msSigma» x5)
                      x7
                      (_root_.GebMirror.Metalogic.«Prelude.some» x4)))
                  (_root_.GebMirror.Metalogic.«Combinator.pairs»
                    (_root_.GebMirror.Metalogic.«Combinator.msObjs» x5)))
          else
            _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f4d617463682e6e6f7468696e67»
        else
          _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f4d617463682e6e6f7468696e67»
      else
        if (_root_.Geb.Kernel.Const.equal
          (_root_.GebMirror.Metalogic.«PartialHorn.sortOf» x0 x1 x2)
          (_root_.GebMirror.Metalogic.«Prelude.some»
            (_root_.Geb.Kernel.leaf 0))).label ≠ 0 then
          _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f4d617463682e6a757374»
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
            _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f4d617463682e6e6f7468696e67»);
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
          (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43432e70757265»
            (_root_.GebMirror.Metalogic.«Combinator.certs»
              ([] : _root_.List _root_.Geb.Kernel.Tree)))
          (fun (x5 : _root_.Geb.Kernel.Tree)
             (x6 : _root_.List _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Metalogic.«Combinator.bindTToC»
              (x2 x5)
              (fun (x7 : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.Metalogic.«Combinator.bindCToC»
                  (x3 x6)
                  (fun (x8 : _root_.Geb.Kernel.Tree) =>
                    _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43432e70757265»
                      (_root_.GebMirror.Metalogic.«Combinator.certs»
                        (x7 :: (_root_.GebMirror.Metalogic.«Combinator.certsOf» x8)))))))
      (fun (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43432e70757265»
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
      _root_.GebMirror.Metalogic.«Combinator.bindYToT»
        (_root_.GebMirror.Metalogic.«Combinator.typeTerm» x3)
        (fun (x4 : _root_.Geb.Kernel.Tree) =>
          if (_root_.Geb.Kernel.Const.equal
            (_root_.GebMirror.Metalogic.«PartialHorn.phSubst»
              (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f59542e6d6170»
                _root_.GebMirror.Metalogic.«Combinator.tyT»
                x0)
              x1)
            x3).label ≠ 0 then
            _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e70757265»
              (_root_.GebMirror.Metalogic.«Combinator.tyDfd» x4)
          else
            if (_root_.Geb.Kernel.Const.eq
              (_root_.GebMirror.Metalogic.«Combinator.tySort» x4)
              (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
              _root_.GebMirror.Metalogic.«Combinator.bindYToT»
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
                _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e6661696c»
              else
                _root_.GebMirror.Metalogic.«Combinator.bindCToT»
                  (_root_.GebMirror.Metalogic.«Combinator.bridgeKids»
                    x2
                    (_root_.Geb.Kernel.Const.children x3))
                  (fun (x5 : _root_.Geb.Kernel.Tree) =>
                    _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e70757265»
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

def «Combinator.applyRule» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.bindTToP»
      (_root_.GebMirror.Metalogic.«Combinator.pmGuard»
        (_root_.GebMirror.Metalogic.«Base.not»
          (_root_.GebMirror.Metalogic.«Base.anyT»
            (fun (x2 : _root_.Geb.Kernel.Tree) =>
              _root_.Geb.Kernel.Const.eq (_root_.Geb.Kernel.Const.label x1) x2)
            (_root_.GebMirror.Metalogic.«Combinator.rwAvoid» x0))))
      (fun (_ : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Combinator.bindQToP»
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
            _root_.GebMirror.Metalogic.«Combinator.bindSToP»
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
                if (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f4d617463682e69734a757374»
                  x7).label ≠ 0 then
                  let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f4d617463682e66726f6d4d61796265»
                    _root_.GebMirror.Metalogic.«Combinator.ms0»
                    x7;
                  let x9 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Base.allSomeT»
                    (_root_.GebMirror.Metalogic.«Combinator.msSigma» x8);
                  if (_root_.GebMirror.Metalogic.«Prelude.isSome» x9).label ≠ 0 then
                    let x10 : _root_.List
                      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                      (_root_.GebMirror.Metalogic.«Prelude.get» x9);
                    _root_.GebMirror.Metalogic.«Combinator.bindYsToP»
                      (_root_.GebMirror.Metalogic.«Combinator.mapMTY»
                        _root_.GebMirror.Metalogic.«Combinator.typeTerm»
                        x10)
                      (fun (x11 : _root_.Geb.Kernel.Tree) =>
                        let x12 : _root_.List
                          _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.ptysOf» x11;
                        _root_.GebMirror.Metalogic.«Combinator.bindCToP»
                          (_root_.GebMirror.Metalogic.«Combinator.mapMPairC»
                            (fun (x13 : _root_.Geb.Kernel.Tree) =>
                              _root_.GebMirror.Metalogic.«Combinator.bindYToT»
                                (_root_.GebMirror.Metalogic.«Combinator.typePattern»
                                  x12
                                  (_root_.GebMirror.Metalogic.«Language.p1» x13))
                                (fun (x14 : _root_.Geb.Kernel.Tree) =>
                                  _root_.GebMirror.Metalogic.«Combinator.bindYToT»
                                    (_root_.GebMirror.Metalogic.«Combinator.typeTerm»
                                      (_root_.GebMirror.Metalogic.«Language.p2» x13))
                                    (fun (x15 : _root_.Geb.Kernel.Tree) =>
                                      _root_.GebMirror.Metalogic.«Combinator.objEq» x14 x15)))
                            (_root_.GebMirror.Metalogic.«Combinator.msObjs» x8))
                          (fun (_ : _root_.Geb.Kernel.Tree) =>
                            _root_.GebMirror.Metalogic.«Combinator.bindTToP»
                              (_root_.GebMirror.Metalogic.«Combinator.bridge» x12 x4 x1)
                              (fun (x14 : _root_.Geb.Kernel.Tree) =>
                                _root_.GebMirror.Metalogic.«Combinator.bindCToP»
                                  (_root_.GebMirror.Metalogic.«Combinator.mapMEqC»
                                    (_root_.GebMirror.Metalogic.«Combinator.proveHyp»
                                      _root_.GebMirror.Metalogic.«Combinator.typePattern»
                                      x12)
                                    (_root_.GebMirror.Metalogic.«PartialHorn.seqHyps» x3))
                                  (fun (x15 : _root_.Geb.Kernel.Tree) =>
                                    let x16 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.srcCert»
                                      (_root_.GebMirror.Metalogic.«Combinator.rwSrc» x0)
                                      x10
                                      (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f59542e6d6170»
                                        _root_.GebMirror.Metalogic.«Combinator.tyDfd»
                                        x12)
                                      (_root_.GebMirror.Metalogic.«Combinator.certsOf» x15);
                                    _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43502e70757265»
                                      (_root_.GebMirror.Metalogic.«Language.pr»
                                        (_root_.GebMirror.Metalogic.«PartialHorn.phSubst» x10 x5)
                                        (_root_.GebMirror.Metalogic.«Combinator.cTrans»
                                          x14
                                          (if (_root_.GebMirror.Metalogic.«Combinator.rwFlip» x0).label ≠ 0 then
                                            _root_.GebMirror.Metalogic.«Combinator.cSymm» x16
                                          else
                                            x16)))))))
                  else
                    _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43502e6661696c»
                else
                  _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43502e6661696c»)));
    x2

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
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43502e6f72456c7365»
          (_root_.GebMirror.Metalogic.«Combinator.applyRule» x2 x1)
          x3)
      _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43502e6661696c»
      x0;
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
        _root_.GebMirror.Metalogic.«Combinator.bindYToA»
          (_root_.GebMirror.Metalogic.«Combinator.typeTerm» x0)
          (fun (x5 : _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Metalogic.«Combinator.bindYToA»
              (_root_.GebMirror.Metalogic.«Combinator.typeTerm» x1)
              (fun (x6 : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.Metalogic.«Combinator.bindYToA»
                  (_root_.GebMirror.Metalogic.«Combinator.typeTerm» x3)
                  (fun (x7 : _root_.Geb.Kernel.Tree) =>
                    _root_.GebMirror.Metalogic.«Combinator.bindYToA»
                      (_root_.GebMirror.Metalogic.«Combinator.typeTerm» x4)
                      (fun (x8 : _root_.Geb.Kernel.Tree) =>
                        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43412e70757265»
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
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43412e6661696c»
    else
      _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43412e6661696c»);
    x1

def «Combinator.rewriteRoot» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43502e6f72456c7365»
      (_root_.GebMirror.Metalogic.«Combinator.firstRule» x0 x1)
      (_root_.GebMirror.Metalogic.«Combinator.bindAToP»
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
          _root_.GebMirror.Metalogic.«Combinator.bindPToP»
            (_root_.GebMirror.Metalogic.«Combinator.firstRule»
              x0
              (_root_.GebMirror.Metalogic.«Theory.comp» x5 x7))
            (fun (x13 : _root_.Geb.Kernel.Tree) =>
              _root_.GebMirror.Metalogic.«Combinator.bindYToP»
                (_root_.GebMirror.Metalogic.«Combinator.typeTerm»
                  (_root_.GebMirror.Metalogic.«Theory.comp»
                    (_root_.GebMirror.Metalogic.«Theory.comp» x5 x7)
                    x9))
                (fun (x14 : _root_.Geb.Kernel.Tree) =>
                  _root_.GebMirror.Metalogic.«Combinator.bindYToP»
                    (_root_.GebMirror.Metalogic.«Combinator.typeTerm» x9)
                    (fun (x15 : _root_.Geb.Kernel.Tree) =>
                      _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43502e70757265»
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
      _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f434f502e6f6b»
        (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f434f502e726573»
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
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.bindTToP»
      (if (_root_.Geb.Kernel.Const.equal x0 x1).label ≠ 0 then
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e70757265» x2
      else
        _root_.GebMirror.Metalogic.«Combinator.addLemma»
          (_root_.GebMirror.Metalogic.«PartialHorn.eqn» x0 x1)
          x2)
      (fun (x3 : _root_.Geb.Kernel.Tree)
         (_ : _root_.Geb.Kernel.Tree)
         (x5 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43502e6f6b»
          (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43502e726573»
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
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.bindOPToP»
      (_root_.GebMirror.Metalogic.«Combinator.lookupNf» x2)
      (fun (x4 : _root_.Geb.Kernel.Tree) =>
        if (_root_.GebMirror.Metalogic.«$4c616e67756167652f4f54506169722e69734a757374»
          x4).label ≠ 0 then
          _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43502e70757265»
            (_root_.GebMirror.Metalogic.«$4c616e67756167652f4f54506169722e66726f6d4d61796265»
              _root_.GebMirror.Metalogic.«Combinator.pr0»
              x4)
        else
          _root_.GebMirror.Metalogic.«Combinator.bindYToP»
            (_root_.GebMirror.Metalogic.«Combinator.typeTerm» x2)
            (fun (x5 : _root_.Geb.Kernel.Tree) =>
              if (_root_.Geb.Kernel.Const.eq
                (_root_.GebMirror.Metalogic.«Combinator.tySort» x5)
                (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43502e70757265»
                  (_root_.GebMirror.Metalogic.«Language.pr»
                    (_root_.GebMirror.Metalogic.«Combinator.tyLo» x5)
                    (_root_.GebMirror.Metalogic.«Combinator.tyLoC» x5))
              else
                if (_root_.Geb.Kernel.Const.eq
                  (_root_.Geb.Kernel.Const.label x2)
                  (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                  _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43502e70757265»
                    (_root_.GebMirror.Metalogic.«Language.pr»
                      x2
                      (_root_.GebMirror.Metalogic.«Combinator.tyDfd» x5))
                else
                  _root_.GebMirror.Metalogic.«Combinator.bindPsToP»
                    (_root_.GebMirror.Metalogic.«Combinator.seqP» x3)
                    (fun (x6 : _root_.Geb.Kernel.Tree) =>
                      let x7 : _root_.List
                        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.pairsOf» x6;
                      let x8 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.node
                        (_root_.Geb.Kernel.Const.label x2)
                        (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f50616972542e6d6170»
                          _root_.GebMirror.Metalogic.«Language.p1»
                          x7);
                      let x9 : _root_.Geb.Kernel.Tree := (if (_root_.Geb.Kernel.Const.equal
                        x8
                        x2).label ≠ 0 then
                        _root_.GebMirror.Metalogic.«Combinator.tyDfd» x5
                      else
                        _root_.GebMirror.Metalogic.«Combinator.cCong»
                          (_root_.GebMirror.Metalogic.«Combinator.tyDfd» x5)
                          (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f50616972542e6d6170»
                            _root_.GebMirror.Metalogic.«Language.p2»
                            x7));
                      _root_.GebMirror.Metalogic.«Combinator.bindOPToP»
                        (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f434f502e6f72456c7365»
                          (_root_.GebMirror.Metalogic.«Combinator.bindPToOP»
                            (_root_.GebMirror.Metalogic.«Combinator.rewriteRoot» x0 x8)
                            (fun (x10 : _root_.Geb.Kernel.Tree) =>
                              _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f434f502e70757265»
                                (_root_.GebMirror.Metalogic.«$4c616e67756167652f4f54506169722e6a757374» x10)))
                          (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f434f502e70757265»
                            _root_.GebMirror.Metalogic.«$4c616e67756167652f4f54506169722e6e6f7468696e67»))
                        (fun (x10 : _root_.Geb.Kernel.Tree) =>
                          if (_root_.GebMirror.Metalogic.«$4c616e67756167652f4f54506169722e69734a757374»
                            x10).label ≠ 0 then
                            let x11 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$4c616e67756167652f4f54506169722e66726f6d4d61796265»
                              _root_.GebMirror.Metalogic.«Combinator.pr0»
                              x10;
                            _root_.GebMirror.Metalogic.«Combinator.bindPToP»
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
          _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43502e6661696c»));
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
  _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f536571732e6c656e677468»
    _root_.GebMirror.Metalogic.«Theory.categoryAxioms»

def «Combinator.beforeProduct» :=
  _root_.Geb.Kernel.Const.add
    _root_.GebMirror.Metalogic.«Combinator.beforeTerminal»
    (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f536571732e6c656e677468»
      _root_.GebMirror.Metalogic.«Theory.terminalAxioms»)

def «Combinator.beforeExponential» :=
  _root_.Geb.Kernel.Const.add
    _root_.GebMirror.Metalogic.«Combinator.beforeProduct»
    (_root_.Geb.Kernel.Const.add
      (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f536571732e6c656e677468»
        _root_.GebMirror.Metalogic.«Theory.productAxioms»)
      (_root_.Geb.Kernel.Const.add
        (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f536571732e6c656e677468»
          _root_.GebMirror.Metalogic.«Theory.equalizerAxioms»)
        (_root_.Geb.Kernel.Const.add
          (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f536571732e6c656e677468»
            _root_.GebMirror.Metalogic.«Theory.initialAxioms»)
          (_root_.Geb.Kernel.Const.add
            (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f536571732e6c656e677468»
              _root_.GebMirror.Metalogic.«Theory.coproductAxioms»)
            (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f536571732e6c656e677468»
              _root_.GebMirror.Metalogic.«Theory.coequalizerAxioms»)))))

def «Combinator.beforeNat» :=
  _root_.Geb.Kernel.Const.add
    _root_.GebMirror.Metalogic.«Combinator.beforeExponential»
    (_root_.Geb.Kernel.Const.add
      (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f536571732e6c656e677468»
        _root_.GebMirror.Metalogic.«Theory.exponentialAxioms»)
      (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f536571732e6c656e677468»
        _root_.GebMirror.Metalogic.«Theory.classifierAxioms»))

def «Combinator.beforeList» :=
  _root_.Geb.Kernel.Const.add
    _root_.GebMirror.Metalogic.«Combinator.beforeNat»
    (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f536571732e6c656e677468»
      _root_.GebMirror.Metalogic.«Theory.natAxioms»)

def «Combinator.pInst» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.bindQToE»
      (_root_.GebMirror.Metalogic.«Combinator.srcSeq» x0)
      (fun (x2 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Combinator.bindYsToE»
          (_root_.GebMirror.Metalogic.«Combinator.mapMTY»
            _root_.GebMirror.Metalogic.«Combinator.typeTerm»
            x1)
          (fun (x3 : _root_.Geb.Kernel.Tree) =>
            let x4 : _root_.List
              _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.ptysOf» x3;
            _root_.GebMirror.Metalogic.«Combinator.bindCToE»
              (_root_.GebMirror.Metalogic.«Combinator.mapMEqC»
                (_root_.GebMirror.Metalogic.«Combinator.proveHyp»
                  _root_.GebMirror.Metalogic.«Combinator.typePattern»
                  x4)
                (_root_.GebMirror.Metalogic.«PartialHorn.seqHyps» x2))
              (fun (x5 : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43452e70757265»
                  (_root_.GebMirror.Metalogic.«Combinator.eqnCert»
                    (_root_.GebMirror.Metalogic.«PartialHorn.eqSubst»
                      x1
                      (_root_.GebMirror.Metalogic.«PartialHorn.seqConcl» x2))
                    (_root_.GebMirror.Metalogic.«Combinator.srcCert»
                      x0
                      x1
                      (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f59542e6d6170»
                        _root_.GebMirror.Metalogic.«Combinator.tyDfd»
                        x4)
                      (_root_.GebMirror.Metalogic.«Combinator.certsOf» x5))))));
    x2

def «Combinator.etaExpand» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.bindYToP»
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
          _root_.GebMirror.Metalogic.«Combinator.bindEToP»
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
              _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43502e70757265»
                (_root_.GebMirror.Metalogic.«Language.pr»
                  (_root_.GebMirror.Metalogic.«PartialHorn.eqLhs»
                    (_root_.GebMirror.Metalogic.«Combinator.ecEqn» x3))
                  (_root_.GebMirror.Metalogic.«Combinator.cSymm»
                    (_root_.GebMirror.Metalogic.«Combinator.ecCert» x3))))
        else
          _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43502e6661696c»);
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

def «Combinator.pByNorm» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.bindPToT»
      (_root_.GebMirror.Metalogic.«Combinator.pNormalize»
        x0
        (_root_.GebMirror.Metalogic.«PartialHorn.eqLhs» x1))
      (fun (x2 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Combinator.bindPToT»
          (_root_.GebMirror.Metalogic.«Combinator.pNormalize»
            x0
            (_root_.GebMirror.Metalogic.«PartialHorn.eqRhs» x1))
          (fun (x3 : _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Metalogic.«Combinator.bindTToT»
              (_root_.GebMirror.Metalogic.«Combinator.pmGuard»
                (_root_.Geb.Kernel.Const.equal
                  (_root_.GebMirror.Metalogic.«Language.p1» x2)
                  (_root_.GebMirror.Metalogic.«Language.p1» x3)))
              (fun (_ : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e70757265»
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

def «$436f6d62696e61746f722f4f50726f7665642e6e6f7468696e67» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$436f6d62696e61746f722f4f50726f7665642e6a757374» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «$436f6d62696e61746f722f4f50726f7665642e69734a757374» :=
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

def «$436f6d62696e61746f722f4f50726f7665642e66726f6d4d61796265» :=
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

def «$436f6d62696e61746f722f4f50726f7665642e6e74684f66» :=
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
      _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f50726f7665642e6e6f7468696e67»
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f50726f7665642e6a757374» x2);
    x2

def «$436f6d62696e61746f722f4f50726f7665642e616c6c4a757374» :=
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
                                          _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f50726f7665642e6a757374»
                                            (_root_.GebMirror.Metalogic.«Combinator.proved»
                                              (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4465764c2e6c656e677468»
                                                x15)
                                              (_root_.GebMirror.Metalogic.«Combinator.devs»
                                                (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4465764c2e617070656e64»
                                                  x15
                                                  (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4465764c2e73696e676c65»
                                                    (_root_.GebMirror.Metalogic.«Combinator.devEntry»
                                                      x0
                                                      x11)))))
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x5;
                                          _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f50726f7665642e6e6f7468696e67»);
    x5

def «Combinator.normalizeThm» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree := (let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f4465762e6e74684f66»
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
                                            _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f50726f7665642e6a757374»
                                              (_root_.GebMirror.Metalogic.«Combinator.proved»
                                                (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4465764c2e6c656e677468»
                                                  x21)
                                                (_root_.GebMirror.Metalogic.«Combinator.devs»
                                                  (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4465764c2e617070656e64»
                                                    x21
                                                    (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4465764c2e73696e676c65»
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
                                            _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f50726f7665642e6e6f7468696e67»
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x5;
                                          _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f50726f7665642e6e6f7468696e67»);
    x5

def «Combinator.instBy» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.bindQToE»
      (_root_.GebMirror.Metalogic.«Combinator.srcSeq» x1)
      (fun (x3 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Combinator.bindYsToE»
          (_root_.GebMirror.Metalogic.«Combinator.mapMTY»
            _root_.GebMirror.Metalogic.«Combinator.typeTerm»
            x2)
          (fun (x4 : _root_.Geb.Kernel.Tree) =>
            let x5 : _root_.List
              _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.ptysOf» x4;
            _root_.GebMirror.Metalogic.«Combinator.bindCToE»
              (_root_.GebMirror.Metalogic.«Combinator.mapMEqC»
                (fun (x6 : _root_.Geb.Kernel.Tree) =>
                  _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e6f72456c7365»
                    (_root_.GebMirror.Metalogic.«Combinator.proveHyp»
                      _root_.GebMirror.Metalogic.«Combinator.typePattern»
                      x5
                      x6)
                    (_root_.GebMirror.Metalogic.«Combinator.pByNorm»
                      x0
                      (_root_.GebMirror.Metalogic.«PartialHorn.eqSubst» x2 x6)))
                (_root_.GebMirror.Metalogic.«PartialHorn.seqHyps» x3))
              (fun (x6 : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43452e70757265»
                  (_root_.GebMirror.Metalogic.«Combinator.eqnCert»
                    (_root_.GebMirror.Metalogic.«PartialHorn.eqSubst»
                      x2
                      (_root_.GebMirror.Metalogic.«PartialHorn.seqConcl» x3))
                    (_root_.GebMirror.Metalogic.«Combinator.srcCert»
                      x1
                      x2
                      (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f59542e6d6170»
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
      _root_.GebMirror.Metalogic.«Combinator.bindYToT»
        (_root_.GebMirror.Metalogic.«Combinator.typeTerm» x2)
        (fun (x5 : _root_.Geb.Kernel.Tree) =>
          if (_root_.Geb.Kernel.Const.equal x2 x4).label ≠ 0 then
            _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e70757265»
              (_root_.GebMirror.Metalogic.«Combinator.tyDfd» x5)
          else
            if (_root_.GebMirror.Metalogic.«Prelude.and»
              (_root_.Geb.Kernel.Const.equal
                x2
                (_root_.GebMirror.Metalogic.«PartialHorn.eqLhs» x0))
              (_root_.Geb.Kernel.Const.equal
                x4
                (_root_.GebMirror.Metalogic.«PartialHorn.eqRhs» x0))).label ≠ 0 then
              _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e70757265» x1
            else
              if (_root_.Geb.Kernel.Const.eq
                (_root_.GebMirror.Metalogic.«Combinator.tySort» x5)
                (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                _root_.GebMirror.Metalogic.«Combinator.bindYToT»
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
                  _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e6661696c»
                else
                  _root_.GebMirror.Metalogic.«Combinator.bindCToT»
                    (_root_.GebMirror.Metalogic.«Combinator.bridgeKids»
                      x3
                      (_root_.Geb.Kernel.Const.children x4))
                    (fun (x6 : _root_.Geb.Kernel.Tree) =>
                      _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e70757265»
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

def «Combinator.natRecUniq» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.bindEToT»
      (_root_.GebMirror.Metalogic.«Combinator.instBy»
        x0
        (_root_.GebMirror.Metalogic.«Combinator.srcAx»
          (_root_.Geb.Kernel.Const.add
            _root_.GebMirror.Metalogic.«Combinator.beforeNat»
            (_root_.Geb.Kernel.leaf 12)))
        (_root_.GebMirror.Metalogic.«Theory.l3» x1 x2 x3))
      (fun (x4 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e70757265»
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
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.bindEToT»
      (_root_.GebMirror.Metalogic.«Combinator.instBy»
        x0
        (_root_.GebMirror.Metalogic.«Combinator.srcAx»
          (_root_.Geb.Kernel.Const.add
            _root_.GebMirror.Metalogic.«Combinator.beforeList»
            (_root_.Geb.Kernel.leaf 13)))
        (_root_.GebMirror.Metalogic.«Theory.l4» x1 x2 x3 x4))
      (fun (x5 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e70757265»
          (_root_.GebMirror.Metalogic.«Combinator.ecCert» x5));
    x5

def «Combinator.byNatInduction» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.bindTToT»
      (_root_.GebMirror.Metalogic.«Combinator.natRecUniq»
        x0
        x1
        x2
        (_root_.GebMirror.Metalogic.«PartialHorn.eqLhs» x3))
      (fun (x4 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Combinator.bindTToT»
          (_root_.GebMirror.Metalogic.«Combinator.natRecUniq»
            x0
            x1
            x2
            (_root_.GebMirror.Metalogic.«PartialHorn.eqRhs» x3))
          (fun (x5 : _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e70757265»
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
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.bindTToT»
      (_root_.GebMirror.Metalogic.«Combinator.listRecUniq»
        x0
        x1
        x2
        x3
        (_root_.GebMirror.Metalogic.«PartialHorn.eqLhs» x4))
      (fun (x5 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Combinator.bindTToT»
          (_root_.GebMirror.Metalogic.«Combinator.listRecUniq»
            x0
            x1
            x2
            x3
            (_root_.GebMirror.Metalogic.«PartialHorn.eqRhs» x4))
          (fun (x6 : _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e70757265»
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
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.bindYToT»
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
          _root_.GebMirror.Metalogic.«Combinator.bindTToT»
            (_root_.GebMirror.Metalogic.«Combinator.byListInduction»
              x0
              x1
              x12
              x13
              (_root_.GebMirror.Metalogic.«PartialHorn.eqn» x14 x15))
            (fun (x16 : _root_.Geb.Kernel.Tree) =>
              _root_.GebMirror.Metalogic.«Combinator.bindEToT»
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
                  _root_.GebMirror.Metalogic.«Combinator.bindEToT»
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
                      _root_.GebMirror.Metalogic.«Combinator.bindTToT»
                        (_root_.GebMirror.Metalogic.«Combinator.congBy»
                          (_root_.GebMirror.Metalogic.«PartialHorn.eqn» x14 x15)
                          x16
                          (_root_.GebMirror.Metalogic.«PartialHorn.eqLhs»
                            (_root_.GebMirror.Metalogic.«Combinator.ecEqn» x17))
                          (_root_.GebMirror.Metalogic.«PartialHorn.eqLhs»
                            (_root_.GebMirror.Metalogic.«Combinator.ecEqn» x18)))
                        (fun (x19 : _root_.Geb.Kernel.Tree) =>
                          _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e70757265»
                            (_root_.GebMirror.Metalogic.«Combinator.cTrans»
                              (_root_.GebMirror.Metalogic.«Combinator.cSymm»
                                (_root_.GebMirror.Metalogic.«Combinator.ecCert» x17))
                              (_root_.GebMirror.Metalogic.«Combinator.cTrans»
                                x19
                                (_root_.GebMirror.Metalogic.«Combinator.ecCert» x18)))))))
        else
          _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e6661696c»);
    x5

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
                    (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f52774c2e6c32»
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
    (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f45716e4c2e6c32»
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
    (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f45716e4c2e6c34»
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
    (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f45716e4c2e6c33»
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
    (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f45716e4c2e6c32»
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
  _root_.GebMirror.Metalogic.«Combinator.bindPToT»
    (_root_.GebMirror.Metalogic.«Combinator.etaExpand»
      (_root_.GebMirror.Metalogic.«Combinator.seqLhs»
        _root_.GebMirror.Metalogic.«Combinator.compPairSeq»))
    (fun (x0 : _root_.Geb.Kernel.Tree) =>
      _root_.GebMirror.Metalogic.«Combinator.bindPToT»
        (_root_.GebMirror.Metalogic.«Combinator.pNormalize»
          _root_.GebMirror.Metalogic.«Combinator.baseRules»
          (_root_.GebMirror.Metalogic.«Language.p1» x0))
        (fun (x1 : _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.Metalogic.«Combinator.bindTToT»
            (_root_.GebMirror.Metalogic.«Combinator.pmGuard»
              (_root_.Geb.Kernel.Const.equal
                (_root_.GebMirror.Metalogic.«Language.p1» x1)
                (_root_.GebMirror.Metalogic.«Combinator.seqRhs»
                  _root_.GebMirror.Metalogic.«Combinator.compPairSeq»)))
            (fun (_ : _root_.Geb.Kernel.Tree) =>
              _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e70757265»
                (_root_.GebMirror.Metalogic.«Combinator.cTrans»
                  (_root_.GebMirror.Metalogic.«Language.p2» x0)
                  (_root_.GebMirror.Metalogic.«Language.p2» x1)))))

def «Combinator.pairFstSndProof» :=
  let x0 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Theory.prod»
    (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 0))
    (_root_.GebMirror.Metalogic.«Theory.x» (_root_.Geb.Kernel.leaf 1));
  _root_.GebMirror.Metalogic.«Combinator.bindEToT»
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
      _root_.GebMirror.Metalogic.«Combinator.bindPToT»
        (_root_.GebMirror.Metalogic.«Combinator.pNormalize»
          _root_.GebMirror.Metalogic.«Combinator.baseRules»
          (_root_.GebMirror.Metalogic.«PartialHorn.eqLhs»
            (_root_.GebMirror.Metalogic.«Combinator.ecEqn» x1)))
        (fun (x2 : _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.Metalogic.«Combinator.bindTToT»
            (_root_.GebMirror.Metalogic.«Combinator.pmGuard»
              (_root_.Geb.Kernel.Const.equal
                (_root_.GebMirror.Metalogic.«Language.p1» x2)
                (_root_.GebMirror.Metalogic.«Combinator.seqLhs»
                  _root_.GebMirror.Metalogic.«Combinator.pairFstSndSeq»)))
            (fun (_ : _root_.Geb.Kernel.Tree) =>
              _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e70757265»
                (_root_.GebMirror.Metalogic.«Combinator.cTrans»
                  (_root_.GebMirror.Metalogic.«Combinator.cSymm» (_root_.GebMirror.Metalogic.«Language.p2» x2))
                  (_root_.GebMirror.Metalogic.«Combinator.ecCert» x1)))))

def «Combinator.evCurryProof» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (let x1 : _root_.List
                                     _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f527752756c65732e617070656e64»
                                     _root_.GebMirror.Metalogic.«Combinator.baseRules»
                                     (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f527752756c65732e73696e676c65»
                                       (_root_.GebMirror.Metalogic.«Combinator.rwThm» x0));
                                   _root_.GebMirror.Metalogic.«Combinator.bindEToT»
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
                                       _root_.GebMirror.Metalogic.«Combinator.bindPToT»
                                         (_root_.GebMirror.Metalogic.«Combinator.pNormalize» x1 x4)
                                         (fun (x5 : _root_.Geb.Kernel.Tree) =>
                                           _root_.GebMirror.Metalogic.«Combinator.bindPToT»
                                             (_root_.GebMirror.Metalogic.«Combinator.pNormalize»
                                               x1
                                               (_root_.GebMirror.Metalogic.«Combinator.seqLhs»
                                                 _root_.GebMirror.Metalogic.«Combinator.evCurrySeq»))
                                             (fun (x6 : _root_.Geb.Kernel.Tree) =>
                                               _root_.GebMirror.Metalogic.«Combinator.bindTToT»
                                                 (_root_.GebMirror.Metalogic.«Combinator.pmGuard»
                                                   (_root_.Geb.Kernel.Const.equal
                                                     (_root_.GebMirror.Metalogic.«Language.p1» x5)
                                                     (_root_.GebMirror.Metalogic.«Language.p1» x6)))
                                                 (fun (_ : _root_.Geb.Kernel.Tree) =>
                                                   _root_.GebMirror.Metalogic.«Combinator.bindYToT»
                                                     (_root_.GebMirror.Metalogic.«Combinator.typeTerm» x4)
                                                     (fun (x8 : _root_.Geb.Kernel.Tree) =>
                                                       _root_.GebMirror.Metalogic.«Combinator.bindYToT»
                                                         (_root_.GebMirror.Metalogic.«Combinator.typeTerm» x3)
                                                         (fun (x9 : _root_.Geb.Kernel.Tree) =>
                                                           _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e70757265»
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
        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.bindEToT»
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
        _root_.GebMirror.Metalogic.«Combinator.bindPToT»
          (_root_.GebMirror.Metalogic.«Combinator.pNormalize»
            _root_.GebMirror.Metalogic.«Combinator.baseRules»
            (_root_.GebMirror.Metalogic.«PartialHorn.eqLhs» x2))
          (fun (x3 : _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Metalogic.«Combinator.bindTToT»
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
                _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e70757265»
                  (_root_.GebMirror.Metalogic.«Combinator.cTrans»
                    (_root_.GebMirror.Metalogic.«Combinator.cSymm» (_root_.GebMirror.Metalogic.«Language.p2» x3))
                    (_root_.GebMirror.Metalogic.«Combinator.ecCert» x1)))));
    x1

def «Combinator.curryNatProof» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (let x2 : _root_.List
                                     _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f527752756c65732e617070656e64»
                                     _root_.GebMirror.Metalogic.«Combinator.baseRules»
                                     (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f52774c2e6c32»
                                       (_root_.GebMirror.Metalogic.«Combinator.rwThm» x0)
                                       (_root_.GebMirror.Metalogic.«Combinator.rwThm» x1));
                                   let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Combinator.seqLhs»
                                     _root_.GebMirror.Metalogic.«Combinator.curryNatSeq»;
                                   _root_.GebMirror.Metalogic.«Combinator.bindEToT»
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
                                       _root_.GebMirror.Metalogic.«Combinator.bindPToT»
                                         (_root_.GebMirror.Metalogic.«Combinator.pNormalize»
                                           x2
                                           (_root_.GebMirror.Metalogic.«PartialHorn.eqLhs»
                                             (_root_.GebMirror.Metalogic.«Combinator.ecEqn» x4)))
                                         (fun (x5 : _root_.Geb.Kernel.Tree) =>
                                           _root_.GebMirror.Metalogic.«Combinator.bindPToT»
                                             (_root_.GebMirror.Metalogic.«Combinator.pNormalize»
                                               x2
                                               (_root_.GebMirror.Metalogic.«Combinator.seqRhs»
                                                 _root_.GebMirror.Metalogic.«Combinator.curryNatSeq»))
                                             (fun (x6 : _root_.Geb.Kernel.Tree) =>
                                               _root_.GebMirror.Metalogic.«Combinator.bindTToT»
                                                 (_root_.GebMirror.Metalogic.«Combinator.pmGuard»
                                                   (_root_.Geb.Kernel.Const.equal
                                                     (_root_.GebMirror.Metalogic.«Language.p1» x5)
                                                     (_root_.GebMirror.Metalogic.«Language.p1» x6)))
                                                 (fun (_ : _root_.Geb.Kernel.Tree) =>
                                                   _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e70757265»
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
  _root_.GebMirror.Metalogic.«Combinator.bindEToT»
    (_root_.GebMirror.Metalogic.«Combinator.pInst»
      (_root_.GebMirror.Metalogic.«Combinator.srcAx»
        (_root_.Geb.Kernel.Const.add
          _root_.GebMirror.Metalogic.«Combinator.beforeTerminal»
          (_root_.Geb.Kernel.leaf 3)))
      (_root_.GebMirror.Metalogic.«Prelude.single»
        (_root_.GebMirror.Metalogic.«Theory.idt» _root_.GebMirror.Metalogic.«Theory.one»)))
    (fun (x0 : _root_.Geb.Kernel.Tree) =>
      _root_.GebMirror.Metalogic.«Combinator.bindPToT»
        (_root_.GebMirror.Metalogic.«Combinator.pNormalize»
          _root_.GebMirror.Metalogic.«Combinator.baseRules»
          (_root_.GebMirror.Metalogic.«PartialHorn.eqRhs»
            (_root_.GebMirror.Metalogic.«Combinator.ecEqn» x0)))
        (fun (x1 : _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.Metalogic.«Combinator.bindTToT»
            (_root_.GebMirror.Metalogic.«Combinator.pmGuard»
              (_root_.Geb.Kernel.Const.equal
                (_root_.GebMirror.Metalogic.«Language.p1» x1)
                (_root_.GebMirror.Metalogic.«Theory.bang» _root_.GebMirror.Metalogic.«Theory.one»)))
            (fun (_ : _root_.Geb.Kernel.Tree) =>
              _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f43542e70757265»
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

def «$436f6d62696e61746f722f4f4c6962726172792e6e6f7468696e67» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$436f6d62696e61746f722f4f4c6962726172792e6a757374» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «$436f6d62696e61746f722f4f4c6962726172792e69734a757374» :=
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

def «$436f6d62696e61746f722f4f4c6962726172792e66726f6d4d61796265» :=
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

def «$436f6d62696e61746f722f4f4c6962726172792e6e74684f66» :=
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
      _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f4c6962726172792e6e6f7468696e67»
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f4c6962726172792e6a757374»
          x2);
    x2

def «$436f6d62696e61746f722f4f4c6962726172792e616c6c4a757374» :=
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
                                          _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f4c6962726172792e6e6f7468696e67»);
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
                            _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f4f4c6962726172792e6a757374»
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
                                 _root_.GebMirror.Metalogic.«$436f6d62696e61746f722f527752756c65732e617070656e64»
                                   _root_.GebMirror.Metalogic.«Combinator.baseRules»
                                   (_root_.GebMirror.Metalogic.«$436f6d62696e61746f722f52774c2e6c35»
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
