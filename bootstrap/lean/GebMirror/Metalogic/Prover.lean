module

public import GebMirror.Metalogic.Translation

/-! Generated from a Geb program by `bootstrap/stage1/lean.geb`. -/

@[expose] public section

open Geb.Kernel
open Geb.Kernel renaming Tree → T

namespace GebMirror.Metalogic

def «Prover.dNode» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mNode»
      x0
      x1
      x2;
    x3

def «Prover.mark» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «Prover.mDeriv» :=
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

def «Prover.mFlag» :=
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

def «$50726f7665722f456163684d61726b65642e616c6c» :=
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

def «$50726f7665722f456163684d61726b65642e616e79» :=
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

def «$50726f7665722f456163684d61726b65642e6973456d707479» :=
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

def «$50726f7665722f456163684d61726b65642e74616b65» :=
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

def «$50726f7665722f4d61726b65644f75742e6d6170» :=
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

def «$50726f7665722f4d61726b6564462e6c32» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)));
    x2

def «$50726f7665722f4d61726b6564462e6c33» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      (_root_.GebMirror.Metalogic.«$50726f7665722f4d61726b6564462e6c32» x1 x2));
    x3

def «$50726f7665722f4d61726b6564462e6c34» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      (_root_.GebMirror.Metalogic.«$50726f7665722f4d61726b6564462e6c33» x1 x2 x3));
    x4

def «$50726f7665722f4d61726b6564462e6c35» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      (_root_.GebMirror.Metalogic.«$50726f7665722f4d61726b6564462e6c34» x1 x2 x3 x4));
    x5

def «$50726f7665722f4d61726b6564462e6c36» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree) =>
    let x6 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      (_root_.GebMirror.Metalogic.«$50726f7665722f4d61726b6564462e6c35»
        x1
        x2
        x3
        x4
        x5));
    x6

def «$50726f7665722f4d61726b656441742e6d6170» :=
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

def «Prover.dRefl» :=
  _root_.GebMirror.Metalogic.«Prover.mark»
    (_root_.GebMirror.Metalogic.«Prover.dNode»
      (_root_.Geb.Kernel.leaf 0)
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      ([] : _root_.List _root_.Geb.Kernel.Tree))
    (_root_.Geb.Kernel.leaf 0)

def «Prover.dTrans» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Prover.mFlag»
      x0).label ≠ 0 then
      if (_root_.GebMirror.Metalogic.«Prover.mFlag» x1).label ≠ 0 then
        _root_.GebMirror.Metalogic.«Prover.mark»
          (_root_.GebMirror.Metalogic.«Prover.dNode»
            (_root_.Geb.Kernel.leaf 1)
            ([] : _root_.List _root_.Geb.Kernel.Tree)
            (_root_.GebMirror.Metalogic.«Theory.l2»
              (_root_.GebMirror.Metalogic.«Prover.mDeriv» x0)
              (_root_.GebMirror.Metalogic.«Prover.mDeriv» x1)))
          (_root_.Geb.Kernel.leaf 1)
      else
        x0
    else
      x1);
    x2

def «Prover.dCong» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«$50726f7665722f456163684d61726b65642e616e79»
      _root_.GebMirror.Metalogic.«Prover.mFlag»
      x0).label ≠ 0 then
      _root_.GebMirror.Metalogic.«Prover.mark»
        (_root_.GebMirror.Metalogic.«Prover.dNode»
          (_root_.Geb.Kernel.leaf 2)
          ([] : _root_.List _root_.Geb.Kernel.Tree)
          (_root_.GebMirror.Metalogic.«$50726f7665722f4d61726b65644f75742e6d6170»
            _root_.GebMirror.Metalogic.«Prover.mDeriv»
            x0))
        (_root_.Geb.Kernel.leaf 1)
    else
      _root_.GebMirror.Metalogic.«Prover.dRefl»);
    x1

def «Prover.sameShape» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.label
                                          x0;
                                        if (_root_.Geb.Kernel.Const.eq
                                          x2
                                          (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                                          _root_.Geb.Kernel.leaf 1
                                        else
                                          if (_root_.Geb.Kernel.Const.eq
                                            (_root_.Geb.Kernel.Const.label x1)
                                            x2).label ≠ 0 then
                                            if (_root_.GebMirror.Metalogic.«Prelude.or»
                                              (_root_.Geb.Kernel.Const.eq
                                                x2
                                                (_root_.Geb.Kernel.leaf 7))
                                              (_root_.Geb.Kernel.Const.eq
                                                x2
                                                (_root_.Geb.Kernel.leaf 11))).label ≠ 0 then
                                              _root_.Geb.Kernel.Const.eq
                                                (_root_.GebMirror.Metalogic.«Language.mD»
                                                  x0
                                                  (_root_.Geb.Kernel.leaf 0))
                                                (_root_.GebMirror.Metalogic.«Language.mD»
                                                  x1
                                                  (_root_.Geb.Kernel.leaf 0))
                                            else
                                              _root_.Geb.Kernel.leaf 1
                                          else
                                            _root_.Geb.Kernel.leaf 0);
    x2

def «Prover.setAt» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Base.mapT»
      (fun (x3 : _root_.Geb.Kernel.Tree) =>
        if (_root_.Geb.Kernel.Const.eq x3 x1).label ≠ 0 then
          x2
        else
          _root_.GebMirror.Metalogic.«Prelude.at» x0 x3)
      (_root_.GebMirror.Metalogic.«Base.range» (_root_.GebMirror.Metalogic.«Prelude.length» x0));
    x3

def «Prover.assign» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 0) x0

def «$50726f7665722f4f41737369676e2e6e6f7468696e67» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$50726f7665722f4f41737369676e2e6a757374» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «$50726f7665722f4f41737369676e2e69734a757374» :=
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

def «$50726f7665722f4f41737369676e2e66726f6d4d61796265» :=
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

def «$50726f7665722f4f41737369676e2e6e74684f66» :=
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
      _root_.GebMirror.Metalogic.«$50726f7665722f4f41737369676e2e6e6f7468696e67»
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$50726f7665722f4f41737369676e2e6a757374» x2);
    x2

def «$50726f7665722f4f41737369676e2e616c6c4a757374» :=
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

def «Prover.assigned» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                 let x2 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x1;
                                 let x3 : _root_.List _root_.Geb.Kernel.Tree := x2; x3);
    x1

def «Prover.bindAA» :=
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
                                          _root_.GebMirror.Metalogic.«$50726f7665722f4f41737369676e2e6e6f7468696e67»);
    x2

def «$50726f7665722f4d74732e7461696c» :=
  fun (x0 : _root_.List
      (_root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
    _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (β := _root_.List
        (_root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      x0
      ([] : _root_.List (_root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      (fun (_ : _root_.Geb.Kernel.Tree →
           _root_.Geb.Kernel.Tree →
             _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
         (x2 : _root_.List
           (_root_.Geb.Kernel.Tree →
             _root_.Geb.Kernel.Tree →
               _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
        x2)

def «Prover.matchVar» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (if (_root_.Geb.Kernel.Const.lt
      x0
      x1).label ≠ 0 then
      if (_root_.Geb.Kernel.Const.equal
        x2
        (_root_.GebMirror.Metalogic.«Language.var» x0)).label ≠ 0 then
        _root_.GebMirror.Metalogic.«$50726f7665722f4f41737369676e2e6a757374»
          (_root_.GebMirror.Metalogic.«Prover.assign» x3)
      else
        _root_.GebMirror.Metalogic.«$50726f7665722f4f41737369676e2e6e6f7468696e67»
    else
      let x4 : _root_.Geb.Kernel.Tree := (if (_root_.Geb.Kernel.Const.eq
        x1
        (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
        x2
      else
        _root_.GebMirror.Metalogic.«Language.rename»
          x2
          (fun (x4 : _root_.Geb.Kernel.Tree) =>
            _root_.Geb.Kernel.Const.sub x4 x1));
      if (_root_.GebMirror.Metalogic.«Prelude.or»
        (_root_.Geb.Kernel.Const.eq x1 (_root_.Geb.Kernel.leaf 0))
        (_root_.Geb.Kernel.Const.equal
          (_root_.GebMirror.Metalogic.«Language.rename»
            x4
            (fun (x5 : _root_.Geb.Kernel.Tree) =>
              _root_.Geb.Kernel.Const.add x5 x1))
          x2)).label ≠ 0 then
        let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.nth»
          x3
          (_root_.Geb.Kernel.Const.sub x0 x1);
        if (_root_.GebMirror.Metalogic.«Prelude.isSome» x5).label ≠ 0 then
          if (_root_.GebMirror.Metalogic.«Prelude.isSome»
            (_root_.GebMirror.Metalogic.«Prelude.get» x5)).label ≠ 0 then
            if (_root_.Geb.Kernel.Const.equal
              (_root_.GebMirror.Metalogic.«Prelude.get» (_root_.GebMirror.Metalogic.«Prelude.get» x5))
              x4).label ≠ 0 then
              _root_.GebMirror.Metalogic.«$50726f7665722f4f41737369676e2e6a757374»
                (_root_.GebMirror.Metalogic.«Prover.assign» x3)
            else
              _root_.GebMirror.Metalogic.«$50726f7665722f4f41737369676e2e6e6f7468696e67»
          else
            _root_.GebMirror.Metalogic.«$50726f7665722f4f41737369676e2e6a757374»
              (_root_.GebMirror.Metalogic.«Prover.assign»
                (_root_.GebMirror.Metalogic.«Prover.setAt»
                  x3
                  (_root_.Geb.Kernel.Const.sub x0 x1)
                  (_root_.GebMirror.Metalogic.«Prelude.some» x4)))
        else
          if (_root_.Geb.Kernel.Const.equal
            x4
            (_root_.GebMirror.Metalogic.«Language.var»
              (_root_.Geb.Kernel.Const.sub x0 x1))).label ≠ 0 then
            _root_.GebMirror.Metalogic.«$50726f7665722f4f41737369676e2e6a757374»
              (_root_.GebMirror.Metalogic.«Prover.assign» x3)
          else
            _root_.GebMirror.Metalogic.«$50726f7665722f4f41737369676e2e6e6f7468696e67»
      else
        _root_.GebMirror.Metalogic.«$50726f7665722f4f41737369676e2e6e6f7468696e67»);
    x4

def «Prover.matchAll» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List
      (_root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
    let x4 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.List _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (fun (x4 : _root_.Geb.Kernel.Tree →
           _root_.Geb.Kernel.Tree →
             _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
         (x5 : _root_.Geb.Kernel.Tree →
           _root_.Geb.Kernel.Tree →
             _root_.List _root_.Geb.Kernel.Tree →
               _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
         (x6 : _root_.Geb.Kernel.Tree)
         (x7 : _root_.Geb.Kernel.Tree)
         (x8 : _root_.List _root_.Geb.Kernel.Tree)
         (x9 : _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.lcase
          (α := _root_.Geb.Kernel.Tree)
          (β := _root_.Geb.Kernel.Tree)
          x8
          x9
          (fun (x10 : _root_.Geb.Kernel.Tree)
             (x11 : _root_.List _root_.Geb.Kernel.Tree) =>
            x5
              x6
              (_root_.Geb.Kernel.Const.add x7 (_root_.Geb.Kernel.leaf 1))
              x11
              (if (_root_.GebMirror.Metalogic.«Prelude.and»
                (_root_.GebMirror.Metalogic.«Prelude.and»
                  (_root_.Geb.Kernel.Const.eq x1 (_root_.Geb.Kernel.leaf 10))
                  (_root_.Geb.Kernel.Const.eq x2 (_root_.Geb.Kernel.leaf 2)))
                (_root_.Geb.Kernel.Const.eq
                  x7
                  (_root_.Geb.Kernel.leaf 0))).label ≠ 0 then
                if (_root_.Geb.Kernel.Const.equal
                  (_root_.GebMirror.Metalogic.«Language.mArg» x0 (_root_.Geb.Kernel.leaf 0))
                  x10).label ≠ 0 then
                  x9
                else
                  _root_.GebMirror.Metalogic.«$50726f7665722f4f41737369676e2e6e6f7468696e67»
              else
                _root_.GebMirror.Metalogic.«Prover.bindAA»
                  x9
                  (fun (x12 : _root_.Geb.Kernel.Tree) =>
                    x4
                      (_root_.Geb.Kernel.Const.add
                        x6
                        (_root_.GebMirror.Metalogic.«Language.childBound» x1 x2 x7))
                      x10
                      (_root_.GebMirror.Metalogic.«Prover.assigned» x12)))))
      (fun (_ : _root_.Geb.Kernel.Tree)
         (_ : _root_.Geb.Kernel.Tree)
         (_ : _root_.List _root_.Geb.Kernel.Tree)
         (x7 : _root_.Geb.Kernel.Tree) =>
        x7)
      (_root_.GebMirror.Metalogic.«$50726f7665722f4d74732e7461696c» x3);
    x4

def «Prover.matchStep» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List
      (_root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree := (let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.label
                                       x0;
                                     let x3 : _root_.Geb.Kernel.Tree →
                                       _root_.Geb.Kernel.Tree →
                                         _root_.List _root_.Geb.Kernel.Tree →
                                           _root_.Geb.Kernel.Tree →
                                             _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.matchAll»
                                       x0
                                       x2
                                       (_root_.GebMirror.Metalogic.«Prelude.length»
                                         (_root_.GebMirror.Metalogic.«Language.mArgs» x0))
                                       x1;
                                     fun (x4 : _root_.Geb.Kernel.Tree)
                                       (x5 : _root_.Geb.Kernel.Tree)
                                       (x6 : _root_.List _root_.Geb.Kernel.Tree) =>
                                       if (_root_.Geb.Kernel.Const.eq
                                         x2
                                         (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                                         _root_.GebMirror.Metalogic.«Prover.matchVar»
                                           (_root_.GebMirror.Metalogic.«Language.mD»
                                             x0
                                             (_root_.Geb.Kernel.leaf 0))
                                           x4
                                           x5
                                           x6
                                       else
                                         let x7 : _root_.List
                                           _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mArgs»
                                           x5;
                                         if (_root_.GebMirror.Metalogic.«Prelude.and»
                                           (_root_.GebMirror.Metalogic.«Prelude.and»
                                             (_root_.Geb.Kernel.Const.eq
                                               x2
                                               (_root_.Geb.Kernel.Const.label x5))
                                             (_root_.Geb.Kernel.Const.equal
                                               (_root_.Geb.Kernel.Const.child
                                                 x0
                                                 (_root_.Geb.Kernel.leaf 0))
                                               (_root_.Geb.Kernel.Const.child
                                                 x5
                                                 (_root_.Geb.Kernel.leaf 0))))
                                           (_root_.Geb.Kernel.Const.eq
                                             (_root_.GebMirror.Metalogic.«Prelude.length»
                                               (_root_.GebMirror.Metalogic.«Language.mArgs» x0))
                                             (_root_.GebMirror.Metalogic.«Prelude.length» x7))).label ≠ 0 then
                                           x3
                                             x4
                                             (_root_.Geb.Kernel.leaf 0)
                                             x7
                                             (_root_.GebMirror.Metalogic.«$50726f7665722f4f41737369676e2e6a757374»
                                               (_root_.GebMirror.Metalogic.«Prover.assign» x6))
                                         else
                                           _root_.GebMirror.Metalogic.«$50726f7665722f4f41737369676e2e6e6f7468696e67»);
    x2

def «Prover.matchTerm» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.para
      (α := _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      _root_.GebMirror.Metalogic.«Prover.matchStep»
      x0;
    x1

def «Prover.nrRule» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «Prover.nrDelta» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «Prover.nrBelow» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 2)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «Prover.nrUnit» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 3)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «Prover.nrThm» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 4)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «Prover.nrThmAt» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 5)
      (x0 ::
        (x1 :: (x2 :: (x3 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))))

def «Prover.nrHyp» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 6)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «Prover.bindP» :=
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
                                          _root_.GebMirror.Metalogic.«Prelude.none»);
    x2

def «Prover.bindAP» :=
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
                                          _root_.GebMirror.Metalogic.«$4c616e67756167652f4f54506169722e6e6f7468696e67»);
    x2

def «Prover.bindHP» :=
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
                                          _root_.GebMirror.Metalogic.«$4c616e67756167652f4f54506169722e6e6f7468696e67»);
    x2

def «Prover.mapTP» :=
  fun (x0 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Prelude.isSome»
      x1).label ≠ 0 then
      _root_.GebMirror.Metalogic.«$4c616e67756167652f4f54506169722e6a757374»
        (x0 (_root_.GebMirror.Metalogic.«Prelude.get» x1))
    else
      _root_.GebMirror.Metalogic.«$4c616e67756167652f4f54506169722e6e6f7468696e67»);
    x2

def «Prover.termsOf» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                 let x2 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x1;
                                 let x3 : _root_.List _root_.Geb.Kernel.Tree := x2; x3);
    x1

def «Prover.objsOf» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                 let x2 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x1;
                                 let x3 : _root_.List _root_.Geb.Kernel.Tree := x2; x3);
    x1

def «Prover.thmRewrite» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree)
    (x6 : _root_.List _root_.Geb.Kernel.Tree)
    (x7 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x8 : _root_.Geb.Kernel.Tree)
    (x9 : _root_.Geb.Kernel.Tree) =>
    let x10 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.bindAP»
      (x7
        (_root_.Geb.Kernel.leaf 0)
        x9
        (_root_.GebMirror.Metalogic.«Prelude.replicate» x8 _root_.GebMirror.Metalogic.«Prelude.none»))
      (fun (x10 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Language.bindTP»
          (_root_.GebMirror.Metalogic.«Base.allSomeT»
            (_root_.GebMirror.Metalogic.«Prover.assigned» x10))
          (fun (x11 : _root_.Geb.Kernel.Tree) =>
            let x12 : _root_.List
              _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Theory.l4»
              x5
              (_root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 0) x6)
              x11
              (_root_.Geb.Kernel.leaf 0);
            _root_.GebMirror.Metalogic.«Prover.mapTP»
              (fun (x13 : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.Metalogic.«Language.pr»
                  x13
                  (_root_.GebMirror.Metalogic.«Prover.dNode»
                    (_root_.Geb.Kernel.leaf 16)
                    x12
                    ([] : _root_.List _root_.Geb.Kernel.Tree)))
              (_root_.GebMirror.Metalogic.«Derivation.rootStep»
                x0
                x1
                x2
                x3
                x4
                (_root_.Geb.Kernel.leaf 16)
                x12
                x9)));
    x10

def «Prover.tryRule» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree)
    (x6 : _root_.Geb.Kernel.Tree) =>
    let x7 : _root_.Geb.Kernel.Tree := (let x7 : _root_.Geb.Kernel.Tree := x5;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x7)
                                          (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                                          let x8 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x7;
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
                                          let x13 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.termsOf»
                                            x11;
                                          _root_.GebMirror.Metalogic.«Prover.mapTP»
                                            (fun (x14 : _root_.Geb.Kernel.Tree) =>
                                              _root_.GebMirror.Metalogic.«Language.pr»
                                                x14
                                                (_root_.GebMirror.Metalogic.«Prover.dNode»
                                                  x9
                                                  x13
                                                  ([] : _root_.List _root_.Geb.Kernel.Tree)))
                                            (_root_.GebMirror.Metalogic.«Derivation.rootStep»
                                              x0
                                              x1
                                              x2
                                              x3
                                              x4
                                              x9
                                              x13
                                              x6)
                                        else
                                          if (_root_.Geb.Kernel.Const.eq
                                            (_root_.Geb.Kernel.Const.label x7)
                                            (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                            let x8 : _root_.List
                                              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                              x7;
                                            let x9 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                              (α := _root_.Geb.Kernel.Tree)
                                              (β := _root_.Geb.Kernel.Tree)
                                              x8
                                              (_root_.Geb.Kernel.leaf 0)
                                              (fun (x9 : _root_.Geb.Kernel.Tree)
                                                 (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                                x9);
                                            let _ : _root_.List
                                              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                              (α := _root_.Geb.Kernel.Tree)
                                              (β := _root_.List _root_.Geb.Kernel.Tree)
                                              x8
                                              ([] : _root_.List _root_.Geb.Kernel.Tree)
                                              (fun (_ : _root_.Geb.Kernel.Tree)
                                                 (x11 : _root_.List _root_.Geb.Kernel.Tree) =>
                                                x11);
                                            if (_root_.GebMirror.Metalogic.«Prelude.and»
                                              (_root_.Geb.Kernel.Const.eq
                                                (_root_.Geb.Kernel.Const.label x6)
                                                (_root_.Geb.Kernel.leaf 11))
                                              (_root_.Geb.Kernel.Const.eq
                                                (_root_.GebMirror.Metalogic.«Language.mD»
                                                  x6
                                                  (_root_.Geb.Kernel.leaf 0))
                                                x9)).label ≠ 0 then
                                              _root_.GebMirror.Metalogic.«Prover.mapTP»
                                                (fun (x11 : _root_.Geb.Kernel.Tree) =>
                                                  _root_.GebMirror.Metalogic.«Language.pr»
                                                    x11
                                                    (_root_.GebMirror.Metalogic.«Prover.dNode»
                                                      (_root_.Geb.Kernel.leaf 8)
                                                      ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                      ([] : _root_.List _root_.Geb.Kernel.Tree)))
                                                (_root_.GebMirror.Metalogic.«Derivation.rootStep»
                                                  x0
                                                  x1
                                                  x2
                                                  x3
                                                  x4
                                                  (_root_.Geb.Kernel.leaf 8)
                                                  ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                  x6)
                                            else
                                              _root_.GebMirror.Metalogic.«$4c616e67756167652f4f54506169722e6e6f7468696e67»
                                          else
                                            if (_root_.Geb.Kernel.Const.eq
                                              (_root_.Geb.Kernel.Const.label x7)
                                              (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
                                              let x8 : _root_.List
                                                _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                x7;
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
                                              if (_root_.GebMirror.Metalogic.«Prelude.and»
                                                (_root_.Geb.Kernel.Const.eq
                                                  (_root_.Geb.Kernel.Const.label x6)
                                                  (_root_.Geb.Kernel.leaf 11))
                                                (_root_.GebMirror.Metalogic.«Prelude.and»
                                                  (_root_.Geb.Kernel.Const.lt
                                                    (_root_.GebMirror.Metalogic.«Language.mD»
                                                      x6
                                                      (_root_.Geb.Kernel.leaf 0))
                                                    x9)
                                                  (_root_.GebMirror.Metalogic.«Base.not»
                                                    (_root_.GebMirror.Metalogic.«Base.anyT»
                                                      (fun (x13 : _root_.Geb.Kernel.Tree) =>
                                                        _root_.Geb.Kernel.Const.eq
                                                          x13
                                                          (_root_.GebMirror.Metalogic.«Language.mD»
                                                            x6
                                                            (_root_.Geb.Kernel.leaf 0)))
                                                      (_root_.GebMirror.Metalogic.«Prover.termsOf»
                                                        x11))))).label ≠ 0 then
                                                _root_.GebMirror.Metalogic.«Prover.mapTP»
                                                  (fun (x13 : _root_.Geb.Kernel.Tree) =>
                                                    _root_.GebMirror.Metalogic.«Language.pr»
                                                      x13
                                                      (_root_.GebMirror.Metalogic.«Prover.dNode»
                                                        (_root_.Geb.Kernel.leaf 8)
                                                        ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                        ([] : _root_.List _root_.Geb.Kernel.Tree)))
                                                  (_root_.GebMirror.Metalogic.«Derivation.rootStep»
                                                    x0
                                                    x1
                                                    x2
                                                    x3
                                                    x4
                                                    (_root_.Geb.Kernel.leaf 8)
                                                    ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                    x6)
                                              else
                                                _root_.GebMirror.Metalogic.«$4c616e67756167652f4f54506169722e6e6f7468696e67»
                                            else
                                              if (_root_.Geb.Kernel.Const.eq
                                                (_root_.Geb.Kernel.Const.label x7)
                                                (_root_.Geb.Kernel.leaf 3)).label ≠ 0 then
                                                let _ : _root_.List
                                                  _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                  x7;
                                                if (_root_.GebMirror.Metalogic.«Prelude.and»
                                                  (_root_.Geb.Kernel.Const.eq
                                                    (_root_.Geb.Kernel.Const.label x6)
                                                    (_root_.Geb.Kernel.leaf 0))
                                                  (_root_.Geb.Kernel.Const.equal
                                                    (_root_.GebMirror.Metalogic.«Prelude.nth»
                                                      x3
                                                      (_root_.GebMirror.Metalogic.«Language.mD»
                                                        x6
                                                        (_root_.Geb.Kernel.leaf 0)))
                                                    (_root_.GebMirror.Metalogic.«Prelude.some»
                                                      _root_.GebMirror.Metalogic.«Theory.one»))).label ≠ 0 then
                                                  _root_.GebMirror.Metalogic.«Prover.mapTP»
                                                    (fun (x9 : _root_.Geb.Kernel.Tree) =>
                                                      _root_.GebMirror.Metalogic.«Language.pr»
                                                        x9
                                                        (_root_.GebMirror.Metalogic.«Prover.dNode»
                                                          (_root_.Geb.Kernel.leaf 7)
                                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                          ([] : _root_.List _root_.Geb.Kernel.Tree)))
                                                    (_root_.GebMirror.Metalogic.«Derivation.rootStep»
                                                      x0
                                                      x1
                                                      x2
                                                      x3
                                                      x4
                                                      (_root_.Geb.Kernel.leaf 7)
                                                      ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                      x6)
                                                else
                                                  _root_.GebMirror.Metalogic.«$4c616e67756167652f4f54506169722e6e6f7468696e67»
                                              else
                                                if (_root_.Geb.Kernel.Const.eq
                                                  (_root_.Geb.Kernel.Const.label x7)
                                                  (_root_.Geb.Kernel.leaf 4)).label ≠ 0 then
                                                  let x8 : _root_.List
                                                    _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                    x7;
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
                                                  let x13 : _root_.List
                                                    _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.objsOf»
                                                    x11;
                                                  _root_.GebMirror.Metalogic.«Prover.bindHP»
                                                    (_root_.GebMirror.Metalogic.«Derivation.thmAt» x1 x9)
                                                    (fun (x14 : _root_.Geb.Kernel.Tree) =>
                                                      _root_.GebMirror.Metalogic.«Language.bindPP»
                                                        (_root_.GebMirror.Metalogic.«Derivation.eqParts»
                                                          (_root_.GebMirror.Metalogic.«Derivation.thConcl» x14))
                                                        (fun (x15 : _root_.Geb.Kernel.Tree) =>
                                                          if (_root_.GebMirror.Metalogic.«Prover.sameShape»
                                                            (_root_.GebMirror.Metalogic.«Language.p1» x15)
                                                            x6).label ≠ 0 then
                                                            _root_.GebMirror.Metalogic.«Prover.thmRewrite»
                                                              x0
                                                              x1
                                                              x2
                                                              x3
                                                              x4
                                                              x9
                                                              x13
                                                              (_root_.GebMirror.Metalogic.«Prover.matchTerm»
                                                                (if (_root_.GebMirror.Metalogic.«Base.isEmpty»
                                                                  x13).label ≠ 0 then
                                                                  _root_.GebMirror.Metalogic.«Language.p1» x15
                                                                else
                                                                  _root_.GebMirror.Metalogic.«Language.osubst»
                                                                    x13
                                                                    (_root_.GebMirror.Metalogic.«Language.p1»
                                                                      x15)))
                                                              (_root_.GebMirror.Metalogic.«Prelude.length»
                                                                (_root_.GebMirror.Metalogic.«Derivation.thCtx»
                                                                  x14))
                                                              x6
                                                          else
                                                            _root_.GebMirror.Metalogic.«$4c616e67756167652f4f54506169722e6e6f7468696e67»))
                                                else
                                                  if (_root_.Geb.Kernel.Const.eq
                                                    (_root_.Geb.Kernel.Const.label x7)
                                                    (_root_.Geb.Kernel.leaf 5)).label ≠ 0 then
                                                    let x8 : _root_.List
                                                      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                      x7;
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
                                                         (x11 : _root_.List
                                                           _root_.Geb.Kernel.Tree) =>
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
                                                         (x13 : _root_.List
                                                           _root_.Geb.Kernel.Tree) =>
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
                                                         (x15 : _root_.List
                                                           _root_.Geb.Kernel.Tree) =>
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
                                                         (x17 : _root_.List
                                                           _root_.Geb.Kernel.Tree) =>
                                                        x17);
                                                    if (_root_.GebMirror.Metalogic.«Prover.sameShape»
                                                      x13
                                                      x6).label ≠ 0 then
                                                      _root_.GebMirror.Metalogic.«Prover.thmRewrite»
                                                        x0
                                                        x1
                                                        x2
                                                        x3
                                                        x4
                                                        x9
                                                        (_root_.GebMirror.Metalogic.«Prover.objsOf» x11)
                                                        (_root_.GebMirror.Metalogic.«Prover.matchTerm» x13)
                                                        x15
                                                        x6
                                                    else
                                                      _root_.GebMirror.Metalogic.«$4c616e67756167652f4f54506169722e6e6f7468696e67»
                                                  else
                                                    let x8 : _root_.List
                                                      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                      x7;
                                                    let x9 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                      (α := _root_.Geb.Kernel.Tree)
                                                      (β := _root_.Geb.Kernel.Tree)
                                                      x8
                                                      (_root_.Geb.Kernel.leaf 0)
                                                      (fun (x9 : _root_.Geb.Kernel.Tree)
                                                         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
                                                        x9);
                                                    let _ : _root_.List
                                                      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                      (α := _root_.Geb.Kernel.Tree)
                                                      (β := _root_.List _root_.Geb.Kernel.Tree)
                                                      x8
                                                      ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                      (fun (_ : _root_.Geb.Kernel.Tree)
                                                         (x11 : _root_.List
                                                           _root_.Geb.Kernel.Tree) =>
                                                        x11);
                                                    let x11 : _root_.List
                                                      _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Theory.l2»
                                                      x9
                                                      (_root_.Geb.Kernel.leaf 0);
                                                    _root_.GebMirror.Metalogic.«Prover.mapTP»
                                                      (fun (x12 : _root_.Geb.Kernel.Tree) =>
                                                        _root_.GebMirror.Metalogic.«Language.pr»
                                                          x12
                                                          (_root_.GebMirror.Metalogic.«Prover.dNode»
                                                            (_root_.Geb.Kernel.leaf 17)
                                                            x11
                                                            ([] : _root_.List _root_.Geb.Kernel.Tree)))
                                                      (_root_.GebMirror.Metalogic.«Derivation.rootStep»
                                                        x0
                                                        x1
                                                        x2
                                                        x3
                                                        x4
                                                        (_root_.Geb.Kernel.leaf 17)
                                                        x11
                                                        x6));
    x7

def «Prover.rootRewrite» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree)
    (x5 : _root_.List _root_.Geb.Kernel.Tree)
    (x6 : _root_.Geb.Kernel.Tree) =>
    let x7 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (fun (x7 : _root_.Geb.Kernel.Tree)
         (x8 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
         (x9 : _root_.Geb.Kernel.Tree) =>
        let x10 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.tryRule»
          x0
          x1
          x2
          x4
          x5
          x7
          x9;
        if (_root_.GebMirror.Metalogic.«$4c616e67756167652f4f54506169722e69734a757374»
          x10).label ≠ 0 then
          x10
        else
          x8 x9)
      (fun (_ : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$4c616e67756167652f4f54506169722e6e6f7468696e67»)
      x3
      x6;
    x7

def «Prover.pr0» :=
  _root_.GebMirror.Metalogic.«Language.pr»
    (_root_.Geb.Kernel.leaf 0)
    (_root_.Geb.Kernel.leaf 0)

def «Prover.thm0» :=
  _root_.GebMirror.Metalogic.«Derivation.mkThm»
    (_root_.Geb.Kernel.leaf 0)
    (_root_.GebMirror.Metalogic.«Language.objs»
      ([] : _root_.List _root_.Geb.Kernel.Tree))
    (_root_.GebMirror.Metalogic.«Derivation.terms»
      ([] : _root_.List _root_.Geb.Kernel.Tree))
    (_root_.Geb.Kernel.leaf 0)

def «Prover.prepareRule» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (let x2 : _root_.Geb.Kernel.Tree := x1;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x2)
                                          (_root_.Geb.Kernel.leaf 4)).label ≠ 0 then
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
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x5
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x8);
                                          let x8 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.objsOf»
                                            x6;
                                          let x9 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Derivation.thmAt»
                                            x0
                                            x4;
                                          let x10 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.bindHP»
                                            x9
                                            (fun (x10 : _root_.Geb.Kernel.Tree) =>
                                              _root_.GebMirror.Metalogic.«Derivation.eqParts»
                                                (_root_.GebMirror.Metalogic.«Derivation.thConcl» x10));
                                          if (_root_.GebMirror.Metalogic.«$4c616e67756167652f4f54506169722e69734a757374»
                                            x10).label ≠ 0 then
                                            let x11 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Base.isEmpty»
                                              x8).label ≠ 0 then
                                              _root_.GebMirror.Metalogic.«Language.p1»
                                                (_root_.GebMirror.Metalogic.«$4c616e67756167652f4f54506169722e66726f6d4d61796265»
                                                  _root_.GebMirror.Metalogic.«Prover.pr0»
                                                  x10)
                                            else
                                              _root_.GebMirror.Metalogic.«Language.osubst»
                                                x8
                                                (_root_.GebMirror.Metalogic.«Language.p1»
                                                  (_root_.GebMirror.Metalogic.«$4c616e67756167652f4f54506169722e66726f6d4d61796265»
                                                    _root_.GebMirror.Metalogic.«Prover.pr0»
                                                    x10)));
                                            _root_.GebMirror.Metalogic.«Prover.nrThmAt»
                                              x4
                                              x6
                                              x11
                                              (_root_.GebMirror.Metalogic.«Prelude.length»
                                                (_root_.GebMirror.Metalogic.«Derivation.thCtx»
                                                  (_root_.GebMirror.Metalogic.«$44657269766174696f6e2f4f54686d2e66726f6d4d61796265»
                                                    _root_.GebMirror.Metalogic.«Prover.thm0»
                                                    x9)))
                                          else
                                            x1
                                        else
                                          x1);
    x2

def «Prover.prepareRules» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        ((_root_.GebMirror.Metalogic.«Prover.prepareRule» x0 x2) :: x3))
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      x1;
    x2

def «Prover.nfr» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «Prover.nfTerm» :=
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

def «Prover.nfMarked» :=
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

def «$50726f7665722f4f4e46522e6e6f7468696e67» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$50726f7665722f4f4e46522e6a757374» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «$50726f7665722f4f4e46522e69734a757374» :=
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

def «$50726f7665722f4f4e46522e66726f6d4d61796265» :=
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

def «$50726f7665722f4f4e46522e6e74684f66» :=
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
      _root_.GebMirror.Metalogic.«$50726f7665722f4f4e46522e6e6f7468696e67»
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$50726f7665722f4f4e46522e6a757374» x2);
    x2

def «$50726f7665722f4f4e46522e616c6c4a757374» :=
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

def «$50726f7665722f456163684e46522e616c6c» :=
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

def «$50726f7665722f456163684e46522e616e79» :=
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

def «$50726f7665722f456163684e46522e6973456d707479» :=
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

def «$50726f7665722f456163684e46522e74616b65» :=
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

def «$50726f7665722f4e46525465726d2e6d6170» :=
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

def «$50726f7665722f4e46524d61726b65642e6d6170» :=
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

def «Prover.nfrs» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 0) x0

def «$50726f7665722f4f4e46524c6973742e6e6f7468696e67» :=
  _root_.Geb.Kernel.Const.node
    (_root_.Geb.Kernel.leaf 0)
    ([] : _root_.List _root_.Geb.Kernel.Tree)

def «$50726f7665722f4f4e46524c6973742e6a757374» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «$50726f7665722f4f4e46524c6973742e69734a757374» :=
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

def «$50726f7665722f4f4e46524c6973742e66726f6d4d61796265» :=
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

def «$50726f7665722f4f4e46524c6973742e6e74684f66» :=
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
      _root_.GebMirror.Metalogic.«$50726f7665722f4f4e46524c6973742e6e6f7468696e67»
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$50726f7665722f4f4e46524c6973742e6a757374» x2);
    x2

def «$50726f7665722f4f4e46524c6973742e616c6c4a757374» :=
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

def «Prover.nfrsOf» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                 let x2 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x1;
                                 let x3 : _root_.List _root_.Geb.Kernel.Tree := x2; x3);
    x1

def «Prover.bindNT» :=
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
                                          _root_.GebMirror.Metalogic.«Prelude.none»);
    x2

def «Prover.bindNN» :=
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
                                          _root_.GebMirror.Metalogic.«$50726f7665722f4f4e46522e6e6f7468696e67»);
    x2

def «Prover.mapNN» :=
  fun (x0 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
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
                                          _root_.GebMirror.Metalogic.«$50726f7665722f4f4e46522e6a757374» (x0 x4)
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x2;
                                          _root_.GebMirror.Metalogic.«$50726f7665722f4f4e46522e6e6f7468696e67»);
    x2

def «Prover.bindTN» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Prelude.isSome»
      x0).label ≠ 0 then
      x1 (_root_.GebMirror.Metalogic.«Prelude.get» x0)
    else
      _root_.GebMirror.Metalogic.«$50726f7665722f4f4e46522e6e6f7468696e67»);
    x2

def «Prover.bindSN» :=
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
                                          _root_.GebMirror.Metalogic.«$50726f7665722f4f4e46522e6e6f7468696e67»);
    x2

def «Prover.allSomeN» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree ×
                                          _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$50726f7665722f4f4e46522e616c6c4a757374»
                                          x0;
                                        if ((x1).1).label ≠ 0 then
                                          _root_.GebMirror.Metalogic.«$50726f7665722f4f4e46524c6973742e6a757374»
                                            (_root_.GebMirror.Metalogic.«Prover.nfrs» (x1).2)
                                        else
                                          _root_.GebMirror.Metalogic.«$50726f7665722f4f4e46524c6973742e6e6f7468696e67»);
    x1

def «Prover.bindLN» :=
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
                                          _root_.GebMirror.Metalogic.«$50726f7665722f4f4e46522e6e6f7468696e67»);
    x2

def «Prover.bindHT» :=
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
                                          _root_.GebMirror.Metalogic.«Prelude.none»);
    x2

def «Prover.rebuild» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.Const.label x0)
      ((_root_.Geb.Kernel.Const.child x0 (_root_.Geb.Kernel.leaf 0)) ::
        (_root_.GebMirror.Metalogic.«$50726f7665722f4e46525465726d2e6d6170»
          _root_.GebMirror.Metalogic.«Prover.nfTerm»
          x1));
    x2

def «Prover.marked» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$50726f7665722f456163684e46522e616e79»
      (fun (x1 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Prover.mFlag» (_root_.GebMirror.Metalogic.«Prover.nfMarked» x1))
      x0;
    x1

def «Prover.scopeTerm» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «$50726f7665722f53636f70655465726d732e73696e676c65» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      ([] : _root_.List _root_.Geb.Kernel.Tree));
    x1

def «$50726f7665722f53636f70655465726d732e6c656e677468» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (_ : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.add x2 (_root_.Geb.Kernel.leaf 1))
      (_root_.Geb.Kernel.leaf 0)
      x0;
    x1

def «$50726f7665722f53636f70655465726d732e617070656e64» :=
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

def «$50726f7665722f53636f70655465726d732e72657665727365» :=
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

def «$50726f7665722f53636f70655465726d732e7461696c» :=
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

def «$50726f7665722f53636f70655465726d732e64726f70» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.iter
      (α := _root_.List _root_.Geb.Kernel.Tree)
      _root_.GebMirror.Metalogic.«$50726f7665722f53636f70655465726d732e7461696c»
      x1
      x0;
    x2

def «$50726f7665722f53636f70655465726d732e61744f72» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«$50726f7665722f53636f70655465726d732e64726f70» x2 x1)
      x0
      (fun (x3 : _root_.Geb.Kernel.Tree)
         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        x3);
    x3

def «Prover.scopeOf» :=
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

def «Prover.termOf» :=
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

def «Prover.zipTs» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree →
           _root_.List _root_.Geb.Kernel.Tree)
         (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.lcase
          (α := _root_.Geb.Kernel.Tree)
          (β := _root_.List _root_.Geb.Kernel.Tree)
          x4
          ([] : _root_.List _root_.Geb.Kernel.Tree)
          (fun (x5 : _root_.Geb.Kernel.Tree)
             (x6 : _root_.List _root_.Geb.Kernel.Tree) =>
            ((_root_.GebMirror.Metalogic.«Prover.scopeTerm» x2 x5) :: (x3 x6))))
      (fun (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        ([] : _root_.List _root_.Geb.Kernel.Tree))
      x0
      x1;
    x2

def «Prover.job» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 ::
        (x1 ::
          (x2 :: (x3 :: (x4 :: ([] : _root_.List _root_.Geb.Kernel.Tree))))))

def «Prover.jobs» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 0) x0

def «Prover.jobsOf» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                 let x2 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x1;
                                 let x3 : _root_.List _root_.Geb.Kernel.Tree := x2; x3);
    x1

def «$50726f7665722f4a6f624c2e73696e676c65» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (x0 ::
      ([] : _root_.List _root_.Geb.Kernel.Tree));
    x1

def «$50726f7665722f4a6f624c2e6c656e677468» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (_ : _root_.Geb.Kernel.Tree) (x2 : _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.add x2 (_root_.Geb.Kernel.leaf 1))
      (_root_.Geb.Kernel.leaf 0)
      x0;
    x1

def «$50726f7665722f4a6f624c2e617070656e64» :=
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

def «$50726f7665722f4a6f624c2e72657665727365» :=
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

def «$50726f7665722f4a6f624c2e7461696c» :=
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

def «$50726f7665722f4a6f624c2e64726f70» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.iter
      (α := _root_.List _root_.Geb.Kernel.Tree)
      _root_.GebMirror.Metalogic.«$50726f7665722f4a6f624c2e7461696c»
      x1
      x0;
    x2

def «$50726f7665722f4a6f624c2e61744f72» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«$50726f7665722f4a6f624c2e64726f70» x2 x1)
      x0
      (fun (x3 : _root_.Geb.Kernel.Tree)
         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        x3);
    x3

def «$50726f7665722f4a6f6241742e6d6170» :=
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

def «Prover.jobDp» :=
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
                                        let _ : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x10
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x13 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x13);
                                        x3);
    x1

def «Prover.jobCtx» :=
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
                                 let _ : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                   x10
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x13 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x13);
                                 let x13 : _root_.Geb.Kernel.Tree := x5;
                                 let x14 : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x13;
                                 let x15 : _root_.List _root_.Geb.Kernel.Tree := x14; x15);
    x1

def «Prover.jobNum» :=
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
                                        let _ : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x10
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x13 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x13);
                                        x7);
    x1

def «Prover.jobHyps» :=
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
                                 let _ : _root_.List
                                   _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                   (α := _root_.Geb.Kernel.Tree)
                                   (β := _root_.List _root_.Geb.Kernel.Tree)
                                   x10
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                   (fun (_ : _root_.Geb.Kernel.Tree)
                                      (x13 : _root_.List _root_.Geb.Kernel.Tree) =>
                                     x13);
                                 _root_.GebMirror.Metalogic.«Prover.termsOf» x9);
    x1

def «Prover.jobTerm» :=
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
                                        let _ : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                          (α := _root_.Geb.Kernel.Tree)
                                          (β := _root_.List _root_.Geb.Kernel.Tree)
                                          x10
                                          ([] : _root_.List _root_.Geb.Kernel.Tree)
                                          (fun (_ : _root_.Geb.Kernel.Tree)
                                             (x13 : _root_.List _root_.Geb.Kernel.Tree) =>
                                            x13);
                                        x11);
    x1

def «Prover.jobAt» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := (let x3 : _root_.Geb.Kernel.Tree := x0;
                                        let x4 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                          x3;
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
                                        _root_.GebMirror.Metalogic.«Prover.job» x1 x7 x9 x11 x2);
    x3

def «Prover.firstR» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      x0
      _root_.GebMirror.Metalogic.«$50726f7665722f4f4e46522e6e6f7468696e67»
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        x1);
    x1

def «Prover.splitRs» :=
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

def «$50726f7665722f4e6f726d4a6f622e6d6170» :=
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

def «Prover.nsDone» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «Prover.nsKids» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 :: (x1 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))

def «Prover.nsTail» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 2)
      (x0 :: (x1 :: (x2 :: ([] : _root_.List _root_.Geb.Kernel.Tree))))

def «$50726f7665722f4e7341742e6d6170» :=
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

def «$50726f7665722f4e734f75742e6d6170» :=
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

def «Prover.nsResult» :=
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
                                          x3
                                        else
                                          _root_.GebMirror.Metalogic.«$50726f7665722f4f4e46522e6e6f7468696e67»);
    x1

def «Prover.nsNeed» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                 if (_root_.Geb.Kernel.Const.eq
                                   (_root_.Geb.Kernel.Const.label x1)
                                   (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
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
                                   let _ : _root_.List
                                     _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                     (α := _root_.Geb.Kernel.Tree)
                                     (β := _root_.List _root_.Geb.Kernel.Tree)
                                     x2
                                     ([] : _root_.List _root_.Geb.Kernel.Tree)
                                     (fun (_ : _root_.Geb.Kernel.Tree)
                                        (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
                                       x5);
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
                                 else
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
                                     _root_.GebMirror.Metalogic.«Prover.jobsOf» x5
                                   else
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
                                     let _ : _root_.List
                                       _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                       (α := _root_.Geb.Kernel.Tree)
                                       (β := _root_.List _root_.Geb.Kernel.Tree)
                                       x6
                                       ([] : _root_.List _root_.Geb.Kernel.Tree)
                                       (fun (_ : _root_.Geb.Kernel.Tree)
                                          (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
                                         x9);
                                     _root_.GebMirror.Metalogic.«$50726f7665722f4a6f624c2e73696e676c65» x7);
    x1

def «Prover.nsStart» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := (let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.jobTerm»
                                          x2;
                                        let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Derivation.childCtxs»
                                          x0
                                          x1
                                          x3
                                          (_root_.GebMirror.Metalogic.«Prover.jobCtx» x2)
                                          (_root_.GebMirror.Metalogic.«Prover.jobHyps» x2);
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
                                          _root_.GebMirror.Metalogic.«Prover.nsKids»
                                            x2
                                            (_root_.GebMirror.Metalogic.«Prover.jobs»
                                              (_root_.GebMirror.Metalogic.«$50726f7665722f4e6f726d4a6f622e6d6170»
                                                (fun (x8 : _root_.Geb.Kernel.Tree) =>
                                                  let x9 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.scopeOf»
                                                    x8;
                                                  _root_.GebMirror.Metalogic.«Prover.job»
                                                    (_root_.Geb.Kernel.leaf 0)
                                                    (_root_.GebMirror.Metalogic.«Language.objs»
                                                      (_root_.GebMirror.Metalogic.«Derivation.scopeCtx» x9))
                                                    (_root_.Geb.Kernel.leaf 0)
                                                    (_root_.GebMirror.Metalogic.«Derivation.terms»
                                                      (_root_.GebMirror.Metalogic.«Derivation.scopeHyps» x9))
                                                    (_root_.GebMirror.Metalogic.«Prover.termOf» x8))
                                                (_root_.GebMirror.Metalogic.«Prover.zipTs»
                                                  (_root_.GebMirror.Metalogic.«Derivation.scopesOf» x6)
                                                  (_root_.GebMirror.Metalogic.«Language.mArgs» x3))))
                                        else
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                            x4;
                                          _root_.GebMirror.Metalogic.«Prover.nsDone»
                                            _root_.GebMirror.Metalogic.«$50726f7665722f4f4e46522e6e6f7468696e67»);
    x3

def «Prover.nsAdv» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x6 : _root_.Geb.Kernel.Tree := (let x6 : _root_.Geb.Kernel.Tree := x4;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x6)
                                          (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
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
                                          _root_.GebMirror.Metalogic.«Prover.nsDone» x8
                                        else
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
                                            let x9 : _root_.List
                                              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                              (α := _root_.Geb.Kernel.Tree)
                                              (β := _root_.List _root_.Geb.Kernel.Tree)
                                              x7
                                              ([] : _root_.List _root_.Geb.Kernel.Tree)
                                              (fun (_ : _root_.Geb.Kernel.Tree)
                                                 (x10 : _root_.List _root_.Geb.Kernel.Tree) =>
                                                x10);
                                            let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
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
                                            let x12 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.allSomeN»
                                              x5;
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
                                              let x16 : _root_.List
                                                _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.nfrsOf»
                                                x14;
                                              let x17 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.rebuild»
                                                (_root_.GebMirror.Metalogic.«Prover.jobTerm» x8)
                                                x16;
                                              let x18 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Prover.marked»
                                                x16).label ≠ 0 then
                                                _root_.GebMirror.Metalogic.«Prover.mark»
                                                  (_root_.GebMirror.Metalogic.«Prover.dNode»
                                                    (_root_.Geb.Kernel.leaf 2)
                                                    ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                    (_root_.GebMirror.Metalogic.«$50726f7665722f4e46525465726d2e6d6170»
                                                      (fun (x18 : _root_.Geb.Kernel.Tree) =>
                                                        _root_.GebMirror.Metalogic.«Prover.mDeriv»
                                                          (_root_.GebMirror.Metalogic.«Prover.nfMarked» x18))
                                                      x16))
                                                  (_root_.Geb.Kernel.leaf 1)
                                              else
                                                _root_.GebMirror.Metalogic.«Prover.dRefl»);
                                              let x19 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.rootRewrite»
                                                x0
                                                x1
                                                x2
                                                x3
                                                (_root_.GebMirror.Metalogic.«Prover.jobCtx» x8)
                                                (_root_.GebMirror.Metalogic.«Prover.jobHyps» x8)
                                                x17;
                                              if (_root_.GebMirror.Metalogic.«$4c616e67756167652f4f54506169722e69734a757374»
                                                x19).label ≠ 0 then
                                                let x20 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$4c616e67756167652f4f54506169722e66726f6d4d61796265»
                                                  _root_.GebMirror.Metalogic.«Prover.pr0»
                                                  x19;
                                                _root_.GebMirror.Metalogic.«Prover.nsTail»
                                                  x18
                                                  (_root_.GebMirror.Metalogic.«Prover.mark»
                                                    (_root_.GebMirror.Metalogic.«Language.p2» x20)
                                                    (_root_.Geb.Kernel.leaf 1))
                                                  (_root_.GebMirror.Metalogic.«Prover.jobAt»
                                                    x8
                                                    (_root_.Geb.Kernel.leaf 0)
                                                    (_root_.GebMirror.Metalogic.«Language.p1» x20))
                                              else
                                                _root_.GebMirror.Metalogic.«Prover.nsDone»
                                                  (_root_.GebMirror.Metalogic.«$50726f7665722f4f4e46522e6a757374»
                                                    (_root_.GebMirror.Metalogic.«Prover.nfr» x17 x18))
                                            else
                                              let _ : _root_.List
                                                _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                x12;
                                              _root_.GebMirror.Metalogic.«Prover.nsDone»
                                                _root_.GebMirror.Metalogic.«$50726f7665722f4f4e46522e6e6f7468696e67»
                                          else
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
                                            let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
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
                                            let x14 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.firstR»
                                              x5;
                                            if (_root_.Geb.Kernel.Const.eq
                                              (_root_.Geb.Kernel.Const.label x14)
                                              (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                              let x15 : _root_.List
                                                _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                x14;
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
                                              _root_.GebMirror.Metalogic.«Prover.nsDone»
                                                (_root_.GebMirror.Metalogic.«$50726f7665722f4f4e46522e6a757374»
                                                  (_root_.GebMirror.Metalogic.«Prover.nfr»
                                                    (_root_.GebMirror.Metalogic.«Prover.nfTerm» x16)
                                                    (_root_.GebMirror.Metalogic.«Prover.dTrans»
                                                      x8
                                                      (_root_.GebMirror.Metalogic.«Prover.dTrans»
                                                        x10
                                                        (_root_.GebMirror.Metalogic.«Prover.nfMarked» x16)))))
                                            else
                                              let _ : _root_.List
                                                _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                x14;
                                              _root_.GebMirror.Metalogic.«Prover.nsDone»
                                                _root_.GebMirror.Metalogic.«$50726f7665722f4f4e46522e6e6f7468696e67»);
    x6

def «Prover.nsRound» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree)
    (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x6 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree)
      (fun (x6 : _root_.Geb.Kernel.Tree)
         (x7 : _root_.List _root_.Geb.Kernel.Tree →
           _root_.List _root_.Geb.Kernel.Tree)
         (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
        let x9 : _root_.List _root_.Geb.Kernel.Tree ×
          _root_.List
            _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.splitRs»
          (_root_.GebMirror.Metalogic.«Prover.nsNeed» x6)
          x8;
        ((_root_.GebMirror.Metalogic.«Prover.nsAdv» x0 x1 x2 x3 x6 (x9).1) ::
          (x7 (x9).2)))
      (fun (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        ([] : _root_.List _root_.Geb.Kernel.Tree))
      x5
      (x4
        (_root_.Geb.Kernel.Const.foldr
          (α := _root_.Geb.Kernel.Tree)
          (β := _root_.List _root_.Geb.Kernel.Tree)
          (fun (x6 : _root_.Geb.Kernel.Tree)
             (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Metalogic.«$50726f7665722f4a6f624c2e617070656e64»
              (_root_.GebMirror.Metalogic.«Prover.nsNeed» x6)
              x7)
          ([] : _root_.List _root_.Geb.Kernel.Tree)
          x5));
    x6

def «Prover.normStepB» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List
        _root_.Geb.Kernel.Tree := (fun (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
      _root_.Geb.Kernel.Const.lcase
        (α := _root_.Geb.Kernel.Tree)
        (β := _root_.List _root_.Geb.Kernel.Tree)
        x5
        ([] : _root_.List _root_.Geb.Kernel.Tree)
        (fun (_ : _root_.Geb.Kernel.Tree)
           (_ : _root_.List _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.Metalogic.«$50726f7665722f4e734f75742e6d6170»
            _root_.GebMirror.Metalogic.«Prover.nsResult»
            (_root_.GebMirror.Metalogic.«Prover.nsRound»
              x0
              x1
              x2
              x3
              x4
              (_root_.GebMirror.Metalogic.«Prover.nsRound»
                x0
                x1
                x2
                x3
                x4
                (_root_.GebMirror.Metalogic.«$50726f7665722f4e7341742e6d6170»
                  (fun (x8 : _root_.Geb.Kernel.Tree) =>
                    _root_.GebMirror.Metalogic.«Prover.nsStart» x0 x2 x8)
                  x5)))));
    x5

def «Prover.normB» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List
        _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.iter
      (α := _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«Prover.normStepB» x0 x1 x2 x3)
      (fun (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$50726f7665722f4e734f75742e6d6170»
          _root_.GebMirror.Metalogic.«Prover.nsResult»
          (_root_.GebMirror.Metalogic.«$50726f7665722f4e7341742e6d6170»
            (fun (x6 : _root_.Geb.Kernel.Tree) =>
              _root_.GebMirror.Metalogic.«Prover.nsDone»
                (_root_.GebMirror.Metalogic.«$50726f7665722f4f4e46522e6a757374»
                  (_root_.GebMirror.Metalogic.«Prover.nfr»
                    (_root_.GebMirror.Metalogic.«Prover.jobTerm» x6)
                    _root_.GebMirror.Metalogic.«Prover.dRefl»)))
            x5))
      x4;
    x5

def «Prover.normalize» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree := (fun (x5 : _root_.List _root_.Geb.Kernel.Tree)
                                       (x6 : _root_.List _root_.Geb.Kernel.Tree)
                                       (x7 : _root_.Geb.Kernel.Tree) =>
      _root_.GebMirror.Metalogic.«Prover.firstR»
        (_root_.GebMirror.Metalogic.«Prover.normB»
          x0
          x1
          x2
          x3
          x4
          (_root_.GebMirror.Metalogic.«$50726f7665722f4a6f624c2e73696e676c65»
            (_root_.GebMirror.Metalogic.«Prover.job»
              (_root_.Geb.Kernel.leaf 0)
              (_root_.GebMirror.Metalogic.«Language.objs» x5)
              (_root_.Geb.Kernel.leaf 0)
              (_root_.GebMirror.Metalogic.«Derivation.terms» x6)
              x7))));
    x5

def «Prover.joinBy» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.bindNT»
      (x0 x1 x2 x3)
      (fun (x5 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Prover.bindNT»
          (x0 x1 x2 x4)
          (fun (x6 : _root_.Geb.Kernel.Tree) =>
            if (_root_.Geb.Kernel.Const.equal
              (_root_.GebMirror.Metalogic.«Prover.nfTerm» x5)
              (_root_.GebMirror.Metalogic.«Prover.nfTerm» x6)).label ≠ 0 then
              _root_.GebMirror.Metalogic.«Prelude.some»
                (_root_.GebMirror.Metalogic.«Prover.dNode»
                  (_root_.Geb.Kernel.leaf 18)
                  ([] : _root_.List _root_.Geb.Kernel.Tree)
                  (_root_.GebMirror.Metalogic.«Theory.l2»
                    (_root_.GebMirror.Metalogic.«Prover.mDeriv» (_root_.GebMirror.Metalogic.«Prover.nfMarked» x5))
                    (_root_.GebMirror.Metalogic.«Prover.mDeriv»
                      (_root_.GebMirror.Metalogic.«Prover.nfMarked» x6))))
            else
              _root_.GebMirror.Metalogic.«Prelude.none»));
    x5

def «Prover.byNorm» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.List _root_.Geb.Kernel.Tree)
    (x6 : _root_.List _root_.Geb.Kernel.Tree)
    (x7 : _root_.Geb.Kernel.Tree)
    (x8 : _root_.Geb.Kernel.Tree) =>
    let x9 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.joinBy»
      (_root_.GebMirror.Metalogic.«Prover.normalize» x0 x1 x2 x3 x4)
      x5
      x6
      x7
      x8;
    x9

def «Prover.instAt» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.subst»
      x2
      (_root_.GebMirror.Metalogic.«Derivation.instVar»
        (_root_.GebMirror.Metalogic.«Language.mArr»
          x0
          x1
          _root_.GebMirror.Metalogic.«Language.mStar»));
    x3

def «Prover.byNatInd» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree)
    (x6 : _root_.List _root_.Geb.Kernel.Tree)
    (x7 : _root_.Geb.Kernel.Tree)
    (x8 : _root_.List _root_.Geb.Kernel.Tree)
    (x9 : _root_.List _root_.Geb.Kernel.Tree)
    (x10 : _root_.Geb.Kernel.Tree)
    (x11 : _root_.Geb.Kernel.Tree) =>
    let x12 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      x8
      _root_.GebMirror.Metalogic.«Prelude.none»
      (fun (_ : _root_.Geb.Kernel.Tree)
         (x13 : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Prover.bindHT»
          (_root_.GebMirror.Metalogic.«Derivation.lowerHyps» x0 x2 x13 x9)
          (fun (x14 : _root_.Geb.Kernel.Tree) =>
            let x15 : _root_.List
              _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.termsOf» x14;
            _root_.GebMirror.Metalogic.«Base.bindO»
              (_root_.GebMirror.Metalogic.«Prover.byNorm»
                x0
                x1
                x2
                x6
                x7
                x13
                x15
                (_root_.GebMirror.Metalogic.«Prover.instAt»
                  x3
                  ([] : _root_.List _root_.Geb.Kernel.Tree)
                  x10)
                (_root_.GebMirror.Metalogic.«Prover.instAt»
                  x3
                  ([] : _root_.List _root_.Geb.Kernel.Tree)
                  x11))
              (fun (x16 : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.Metalogic.«Base.bindO»
                  (_root_.GebMirror.Metalogic.«Prover.byNorm»
                    x0
                    x1
                    x2
                    x6
                    x7
                    x8
                    x9
                    (_root_.GebMirror.Metalogic.«Derivation.natSuccAt» x4 x10)
                    (_root_.GebMirror.Metalogic.«Language.subst»
                      x5
                      (_root_.GebMirror.Metalogic.«Derivation.atVar0» x10)))
                  (fun (x17 : _root_.Geb.Kernel.Tree) =>
                    _root_.GebMirror.Metalogic.«Base.mapO»
                      (fun (x18 : _root_.Geb.Kernel.Tree) =>
                        _root_.GebMirror.Metalogic.«Prover.dNode»
                          (_root_.Geb.Kernel.leaf 19)
                          (_root_.GebMirror.Metalogic.«Theory.l3» x3 x4 x5)
                          (_root_.GebMirror.Metalogic.«Theory.l3» x16 x17 x18))
                      (_root_.GebMirror.Metalogic.«Prover.byNorm»
                        x0
                        x1
                        x2
                        x6
                        x7
                        x8
                        x9
                        (_root_.GebMirror.Metalogic.«Derivation.natSuccAt» x4 x11)
                        (_root_.GebMirror.Metalogic.«Language.subst»
                          x5
                          (_root_.GebMirror.Metalogic.«Derivation.atVar0» x11)))))));
    x12

def «Prover.byListInd» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree)
    (x6 : _root_.List _root_.Geb.Kernel.Tree)
    (x7 : _root_.Geb.Kernel.Tree)
    (x8 : _root_.List _root_.Geb.Kernel.Tree)
    (x9 : _root_.List _root_.Geb.Kernel.Tree)
    (x10 : _root_.Geb.Kernel.Tree)
    (x11 : _root_.Geb.Kernel.Tree) =>
    let x12 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      x8
      _root_.GebMirror.Metalogic.«Prelude.none»
      (fun (x12 : _root_.Geb.Kernel.Tree)
         (x13 : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Base.bindO»
          (_root_.GebMirror.Metalogic.«Language.listPart» x12)
          (fun (x14 : _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Metalogic.«Prover.bindHT»
              (_root_.GebMirror.Metalogic.«Derivation.lowerHyps» x0 x2 x13 x9)
              (fun (x15 : _root_.Geb.Kernel.Tree) =>
                let x16 : _root_.List
                  _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.termsOf» x15;
                let x17 : _root_.List _root_.Geb.Kernel.Tree := (x12 :: (x14 :: x13));
                let x18 : _root_.List
                  _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Base.mapT»
                  _root_.GebMirror.Metalogic.«Derivation.weaken2»
                  x16;
                _root_.GebMirror.Metalogic.«Base.bindO»
                  (_root_.GebMirror.Metalogic.«Prover.byNorm»
                    x0
                    x1
                    x2
                    x6
                    x7
                    x13
                    x16
                    (_root_.GebMirror.Metalogic.«Prover.instAt»
                      x3
                      (_root_.GebMirror.Metalogic.«Prelude.single» x14)
                      x10)
                    (_root_.GebMirror.Metalogic.«Prover.instAt»
                      x3
                      (_root_.GebMirror.Metalogic.«Prelude.single» x14)
                      x11))
                  (fun (x19 : _root_.Geb.Kernel.Tree) =>
                    _root_.GebMirror.Metalogic.«Base.bindO»
                      (_root_.GebMirror.Metalogic.«Prover.byNorm»
                        x0
                        x1
                        x2
                        x6
                        x7
                        x17
                        x18
                        (_root_.GebMirror.Metalogic.«Derivation.listConsAt» x4 x14 x10)
                        (_root_.GebMirror.Metalogic.«Language.subst»
                          x5
                          (_root_.GebMirror.Metalogic.«Derivation.atVar0»
                            (_root_.GebMirror.Metalogic.«Derivation.weakenElem» x10))))
                      (fun (x20 : _root_.Geb.Kernel.Tree) =>
                        _root_.GebMirror.Metalogic.«Base.mapO»
                          (fun (x21 : _root_.Geb.Kernel.Tree) =>
                            _root_.GebMirror.Metalogic.«Prover.dNode»
                              (_root_.Geb.Kernel.leaf 20)
                              (_root_.GebMirror.Metalogic.«Theory.l3» x3 x4 x5)
                              (_root_.GebMirror.Metalogic.«Theory.l3» x19 x20 x21))
                          (_root_.GebMirror.Metalogic.«Prover.byNorm»
                            x0
                            x1
                            x2
                            x6
                            x7
                            x17
                            x18
                            (_root_.GebMirror.Metalogic.«Derivation.listConsAt» x4 x14 x11)
                            (_root_.GebMirror.Metalogic.«Language.subst»
                              x5
                              (_root_.GebMirror.Metalogic.«Derivation.atVar0»
                                (_root_.GebMirror.Metalogic.«Derivation.weakenElem» x11)))))))));
    x12

def «Prover.withHyp» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        (x2 :: x3))
      ((_root_.GebMirror.Metalogic.«Prover.nrHyp» x1) ::
        ([] : _root_.List _root_.Geb.Kernel.Tree))
      x0;
    x2

def «Prover.byNatIndHyp» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.List _root_.Geb.Kernel.Tree)
    (x6 : _root_.Geb.Kernel.Tree)
    (x7 : _root_.List _root_.Geb.Kernel.Tree)
    (x8 : _root_.List _root_.Geb.Kernel.Tree)
    (x9 : _root_.Geb.Kernel.Tree)
    (x10 : _root_.Geb.Kernel.Tree) =>
    let x11 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      x7
      _root_.GebMirror.Metalogic.«Prelude.none»
      (fun (_ : _root_.Geb.Kernel.Tree)
         (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Prover.bindHT»
          (_root_.GebMirror.Metalogic.«Derivation.lowerHyps» x0 x2 x12 x8)
          (fun (x13 : _root_.Geb.Kernel.Tree) =>
            let x14 : _root_.List
              _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.termsOf» x13;
            _root_.GebMirror.Metalogic.«Base.bindO»
              (_root_.GebMirror.Metalogic.«Prover.byNorm»
                x0
                x1
                x2
                x5
                x6
                x12
                x14
                (_root_.GebMirror.Metalogic.«Prover.instAt»
                  x3
                  ([] : _root_.List _root_.Geb.Kernel.Tree)
                  x9)
                (_root_.GebMirror.Metalogic.«Prover.instAt»
                  x3
                  ([] : _root_.List _root_.Geb.Kernel.Tree)
                  x10))
              (fun (x15 : _root_.Geb.Kernel.Tree) =>
                let x16 : _root_.List
                  _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.append»
                  x8
                  (_root_.GebMirror.Metalogic.«Prelude.single»
                    (_root_.GebMirror.Metalogic.«Language.mEq» x9 x10));
                _root_.GebMirror.Metalogic.«Prover.bindNT»
                  (_root_.GebMirror.Metalogic.«Prover.normalize»
                    x0
                    x1
                    x2
                    x5
                    x6
                    x7
                    x16
                    (_root_.GebMirror.Metalogic.«Language.mEq» x9 x10))
                  (fun (x17 : _root_.Geb.Kernel.Tree) =>
                    let x18 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.nfTerm»
                      x17;
                    _root_.GebMirror.Metalogic.«Base.bindO»
                      (_root_.GebMirror.Metalogic.«Prover.byNorm»
                        x0
                        x1
                        x2
                        (_root_.GebMirror.Metalogic.«Prover.withHyp»
                          x5
                          (_root_.GebMirror.Metalogic.«Prelude.length» x16))
                        x6
                        x7
                        (_root_.GebMirror.Metalogic.«Prelude.append»
                          x16
                          (_root_.GebMirror.Metalogic.«Prelude.single» x18))
                        (_root_.GebMirror.Metalogic.«Derivation.natSuccAt» x4 x9)
                        (_root_.GebMirror.Metalogic.«Derivation.natSuccAt» x4 x10))
                      (fun (x19 : _root_.Geb.Kernel.Tree) =>
                        let x20 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.dNode»
                          (_root_.Geb.Kernel.leaf 24)
                          (_root_.GebMirror.Metalogic.«Prelude.single»
                            (_root_.GebMirror.Metalogic.«Language.mEq» x9 x10))
                          (_root_.GebMirror.Metalogic.«Theory.l2»
                            (_root_.GebMirror.Metalogic.«Prover.mDeriv»
                              (_root_.GebMirror.Metalogic.«Prover.nfMarked» x17))
                            (_root_.GebMirror.Metalogic.«Prover.dNode»
                              (_root_.Geb.Kernel.leaf 21)
                              (_root_.GebMirror.Metalogic.«Prelude.single» (_root_.GebMirror.Metalogic.«Prelude.length» x8))
                              ([] : _root_.List _root_.Geb.Kernel.Tree)));
                        _root_.GebMirror.Metalogic.«Prelude.some»
                          (_root_.GebMirror.Metalogic.«Prover.dNode»
                            (_root_.Geb.Kernel.leaf 28)
                            (_root_.GebMirror.Metalogic.«Theory.l2» x3 x4)
                            (_root_.GebMirror.Metalogic.«Theory.l2»
                              x15
                              (_root_.GebMirror.Metalogic.«Prover.dNode»
                                (_root_.Geb.Kernel.leaf 22)
                                (_root_.GebMirror.Metalogic.«Prelude.single» x18)
                                (_root_.GebMirror.Metalogic.«Theory.l2» x20 x19)))))))));
    x11

def «Prover.byListIndHyp» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.List _root_.Geb.Kernel.Tree)
    (x6 : _root_.Geb.Kernel.Tree)
    (x7 : _root_.List _root_.Geb.Kernel.Tree)
    (x8 : _root_.List _root_.Geb.Kernel.Tree)
    (x9 : _root_.Geb.Kernel.Tree)
    (x10 : _root_.Geb.Kernel.Tree) =>
    let x11 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      x7
      _root_.GebMirror.Metalogic.«Prelude.none»
      (fun (x11 : _root_.Geb.Kernel.Tree)
         (x12 : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Base.bindO»
          (_root_.GebMirror.Metalogic.«Language.listPart» x11)
          (fun (x13 : _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Metalogic.«Prover.bindHT»
              (_root_.GebMirror.Metalogic.«Derivation.lowerHyps» x0 x2 x12 x8)
              (fun (x14 : _root_.Geb.Kernel.Tree) =>
                let x15 : _root_.List
                  _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.termsOf» x14;
                _root_.GebMirror.Metalogic.«Base.bindO»
                  (_root_.GebMirror.Metalogic.«Prover.byNorm»
                    x0
                    x1
                    x2
                    x5
                    x6
                    x12
                    x15
                    (_root_.GebMirror.Metalogic.«Prover.instAt»
                      x3
                      (_root_.GebMirror.Metalogic.«Prelude.single» x13)
                      x9)
                    (_root_.GebMirror.Metalogic.«Prover.instAt»
                      x3
                      (_root_.GebMirror.Metalogic.«Prelude.single» x13)
                      x10))
                  (fun (x16 : _root_.Geb.Kernel.Tree) =>
                    let x17 : _root_.List _root_.Geb.Kernel.Tree := (x11 :: (x13 :: x12));
                    let x18 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Derivation.weakenElem»
                      (_root_.GebMirror.Metalogic.«Language.mEq» x9 x10);
                    let x19 : _root_.List
                      _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.append»
                      (_root_.GebMirror.Metalogic.«Base.mapT» _root_.GebMirror.Metalogic.«Derivation.weaken2» x15)
                      (_root_.GebMirror.Metalogic.«Prelude.single» x18);
                    _root_.GebMirror.Metalogic.«Prover.bindNT»
                      (_root_.GebMirror.Metalogic.«Prover.normalize» x0 x1 x2 x5 x6 x17 x19 x18)
                      (fun (x20 : _root_.Geb.Kernel.Tree) =>
                        let x21 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.nfTerm»
                          x20;
                        _root_.GebMirror.Metalogic.«Base.bindO»
                          (_root_.GebMirror.Metalogic.«Prover.byNorm»
                            x0
                            x1
                            x2
                            (_root_.GebMirror.Metalogic.«Prover.withHyp»
                              x5
                              (_root_.GebMirror.Metalogic.«Prelude.length» x19))
                            x6
                            x17
                            (_root_.GebMirror.Metalogic.«Prelude.append»
                              x19
                              (_root_.GebMirror.Metalogic.«Prelude.single» x21))
                            (_root_.GebMirror.Metalogic.«Derivation.listConsAt» x4 x13 x9)
                            (_root_.GebMirror.Metalogic.«Derivation.listConsAt» x4 x13 x10))
                          (fun (x22 : _root_.Geb.Kernel.Tree) =>
                            let x23 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.dNode»
                              (_root_.Geb.Kernel.leaf 24)
                              (_root_.GebMirror.Metalogic.«Prelude.single» x18)
                              (_root_.GebMirror.Metalogic.«Theory.l2»
                                (_root_.GebMirror.Metalogic.«Prover.mDeriv»
                                  (_root_.GebMirror.Metalogic.«Prover.nfMarked» x20))
                                (_root_.GebMirror.Metalogic.«Prover.dNode»
                                  (_root_.Geb.Kernel.leaf 21)
                                  (_root_.GebMirror.Metalogic.«Prelude.single»
                                    (_root_.GebMirror.Metalogic.«Prelude.length» x15))
                                  ([] : _root_.List _root_.Geb.Kernel.Tree)));
                            _root_.GebMirror.Metalogic.«Prelude.some»
                              (_root_.GebMirror.Metalogic.«Prover.dNode»
                                (_root_.Geb.Kernel.leaf 29)
                                (_root_.GebMirror.Metalogic.«Theory.l2» x3 x4)
                                (_root_.GebMirror.Metalogic.«Theory.l2»
                                  x16
                                  (_root_.GebMirror.Metalogic.«Prover.dNode»
                                    (_root_.Geb.Kernel.leaf 22)
                                    (_root_.GebMirror.Metalogic.«Prelude.single» x21)
                                    (_root_.GebMirror.Metalogic.«Theory.l2» x23 x22))))))))));
    x11

def «Prover.headChild» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Prelude.or»
      (_root_.GebMirror.Metalogic.«Language.mIs»
        (_root_.Geb.Kernel.leaf 3)
        (_root_.Geb.Kernel.leaf 1)
        x0)
      (_root_.GebMirror.Metalogic.«Language.mIs»
        (_root_.Geb.Kernel.leaf 4)
        (_root_.Geb.Kernel.leaf 1)
        x0)).label ≠ 0 then
      _root_.GebMirror.Metalogic.«Prelude.some» (_root_.Geb.Kernel.leaf 0)
    else
      if (_root_.GebMirror.Metalogic.«Prelude.or»
        (_root_.GebMirror.Metalogic.«Language.mIs»
          (_root_.Geb.Kernel.leaf 8)
          (_root_.Geb.Kernel.leaf 3)
          x0)
        (_root_.GebMirror.Metalogic.«Language.mIs»
          (_root_.Geb.Kernel.leaf 9)
          (_root_.Geb.Kernel.leaf 3)
          x0)).label ≠ 0 then
        _root_.GebMirror.Metalogic.«Prelude.some» (_root_.Geb.Kernel.leaf 2)
      else
        if (_root_.GebMirror.Metalogic.«Language.mIs»
          (_root_.Geb.Kernel.leaf 10)
          (_root_.Geb.Kernel.leaf 2)
          x0).label ≠ 0 then
          _root_.GebMirror.Metalogic.«Prelude.some» (_root_.Geb.Kernel.leaf 1)
        else
          _root_.GebMirror.Metalogic.«Prelude.none»);
    x1

def «Prover.keepsFold» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Prelude.or»
      (_root_.Geb.Kernel.Const.eq x0 (_root_.Geb.Kernel.leaf 8))
      (_root_.Geb.Kernel.Const.eq
        x0
        (_root_.Geb.Kernel.leaf 9))).label ≠ 0 then
      _root_.Geb.Kernel.Const.lt x1 (_root_.Geb.Kernel.leaf 2)
    else
      if (_root_.Geb.Kernel.Const.eq
        x0
        (_root_.Geb.Kernel.leaf 10)).label ≠ 0 then
        _root_.Geb.Kernel.Const.eq x1 (_root_.Geb.Kernel.leaf 0)
      else
        _root_.Geb.Kernel.leaf 0);
    x2

def «Prover.keepsWeak» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (if (_root_.Geb.Kernel.Const.eq
      x0
      (_root_.Geb.Kernel.leaf 5)).label ≠ 0 then
      _root_.Geb.Kernel.leaf 1
    else
      _root_.GebMirror.Metalogic.«Prover.keepsFold» x0 x1);
    x2

def «$50726f7665722f5546732e7461696c» :=
  fun (x0 : _root_.List
      (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
    _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (β := _root_.List (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      x0
      ([] : _root_.List (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      (fun (_ : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
         (x2 : _root_.List
           (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
        x2)

def «Prover.usesStep» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List
      (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree := (let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.label
                                   x0;
                                 let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.length»
                                   (_root_.GebMirror.Metalogic.«Language.mArgs» x0);
                                 let x4 : _root_.Geb.Kernel.Tree →
                                   _root_.Geb.Kernel.Tree →
                                     _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
                                   (α := _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
                                   (β := _root_.Geb.Kernel.Tree →
                                     _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
                                   (fun (x4 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
                                      (x5 : _root_.Geb.Kernel.Tree →
                                        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
                                      (x6 : _root_.Geb.Kernel.Tree)
                                      (x7 : _root_.Geb.Kernel.Tree) =>
                                     let x8 : _root_.Geb.Kernel.Tree := (if (_root_.Geb.Kernel.Const.eq
                                       x2
                                       (_root_.Geb.Kernel.leaf 5)).label ≠ 0 then
                                       _root_.Geb.Kernel.leaf 1
                                     else
                                       _root_.GebMirror.Metalogic.«Language.childBound» x2 x3 x7);
                                     _root_.Geb.Kernel.Const.add
                                       (_root_.Geb.Kernel.Const.mul
                                         (if (_root_.Geb.Kernel.Const.eq
                                           x8
                                           (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                                           _root_.Geb.Kernel.leaf 1
                                         else
                                           _root_.Geb.Kernel.leaf 2)
                                         (x4 (_root_.Geb.Kernel.Const.add x6 x8)))
                                       (x5
                                         x6
                                         (_root_.Geb.Kernel.Const.add
                                           x7
                                           (_root_.Geb.Kernel.leaf 1))))
                                   (fun (_ : _root_.Geb.Kernel.Tree) (_ : _root_.Geb.Kernel.Tree) =>
                                     _root_.Geb.Kernel.leaf 0)
                                   (_root_.GebMirror.Metalogic.«$50726f7665722f5546732e7461696c» x1);
                                 fun (x5 : _root_.Geb.Kernel.Tree) =>
                                   if (_root_.Geb.Kernel.Const.eq
                                     x2
                                     (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                                     if (_root_.Geb.Kernel.Const.eq
                                       (_root_.GebMirror.Metalogic.«Language.mD» x0 (_root_.Geb.Kernel.leaf 0))
                                       x5).label ≠ 0 then
                                       _root_.Geb.Kernel.leaf 1
                                     else
                                       _root_.Geb.Kernel.leaf 0
                                   else
                                     x4 x5 (_root_.Geb.Kernel.leaf 0));
    x2

def «Prover.uses» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.para
      (α := _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      _root_.GebMirror.Metalogic.«Prover.usesStep»
      x0
      x1;
    x2

def «Prover.rootKey» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.label
                                          x0;
                                        if (_root_.Geb.Kernel.Const.eq
                                          x1
                                          (_root_.Geb.Kernel.leaf 7)).label ≠ 0 then
                                          _root_.Geb.Kernel.Const.add
                                            (_root_.Geb.Kernel.leaf 11)
                                            (_root_.Geb.Kernel.Const.mul
                                              (_root_.Geb.Kernel.leaf 2)
                                              (_root_.GebMirror.Metalogic.«Language.mD»
                                                x0
                                                (_root_.Geb.Kernel.leaf 0)))
                                        else
                                          if (_root_.Geb.Kernel.Const.eq
                                            x1
                                            (_root_.Geb.Kernel.leaf 11)).label ≠ 0 then
                                            _root_.Geb.Kernel.Const.add
                                              (_root_.Geb.Kernel.leaf 12)
                                              (_root_.Geb.Kernel.Const.mul
                                                (_root_.Geb.Kernel.leaf 2)
                                                (_root_.GebMirror.Metalogic.«Language.mD»
                                                  x0
                                                  (_root_.Geb.Kernel.leaf 0)))
                                          else
                                            if (_root_.Geb.Kernel.Const.eq
                                              x1
                                              (_root_.Geb.Kernel.leaf 8)).label ≠ 0 then
                                              _root_.Geb.Kernel.leaf 7
                                            else
                                              if (_root_.Geb.Kernel.Const.eq
                                                x1
                                                (_root_.Geb.Kernel.leaf 9)).label ≠ 0 then
                                                _root_.Geb.Kernel.leaf 8
                                              else
                                                if (_root_.Geb.Kernel.Const.eq
                                                  x1
                                                  (_root_.Geb.Kernel.leaf 10)).label ≠ 0 then
                                                  _root_.Geb.Kernel.leaf 9
                                                else
                                                  if (_root_.Geb.Kernel.Const.eq
                                                    x1
                                                    (_root_.Geb.Kernel.leaf 12)).label ≠ 0 then
                                                    _root_.Geb.Kernel.leaf 10
                                                  else
                                                    x1);
    x1

def «Prover.patternKey» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (if (_root_.Geb.Kernel.Const.eq
      (_root_.Geb.Kernel.Const.label x0)
      (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
      _root_.GebMirror.Metalogic.«Prelude.none»
    else
      _root_.GebMirror.Metalogic.«Prelude.some» (_root_.GebMirror.Metalogic.«Prover.rootKey» x0));
    x1

def «Prover.ruleKey» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Prelude.or»
      (_root_.Geb.Kernel.Const.eq x0 (_root_.Geb.Kernel.leaf 3))
      (_root_.GebMirror.Metalogic.«Prelude.or»
        (_root_.Geb.Kernel.Const.eq x0 (_root_.Geb.Kernel.leaf 14))
        (_root_.Geb.Kernel.Const.eq
          x0
          (_root_.Geb.Kernel.leaf 15)))).label ≠ 0 then
      _root_.GebMirror.Metalogic.«Prelude.some» (_root_.Geb.Kernel.leaf 6)
    else
      if (_root_.Geb.Kernel.Const.eq
        x0
        (_root_.Geb.Kernel.leaf 4)).label ≠ 0 then
        _root_.GebMirror.Metalogic.«Prelude.some» (_root_.Geb.Kernel.leaf 3)
      else
        if (_root_.Geb.Kernel.Const.eq
          x0
          (_root_.Geb.Kernel.leaf 5)).label ≠ 0 then
          _root_.GebMirror.Metalogic.«Prelude.some» (_root_.Geb.Kernel.leaf 4)
        else
          if (_root_.Geb.Kernel.Const.eq
            x0
            (_root_.Geb.Kernel.leaf 6)).label ≠ 0 then
            _root_.GebMirror.Metalogic.«Prelude.some» (_root_.Geb.Kernel.leaf 2)
          else
            if (_root_.GebMirror.Metalogic.«Prelude.or»
              (_root_.Geb.Kernel.Const.eq x0 (_root_.Geb.Kernel.leaf 9))
              (_root_.Geb.Kernel.Const.eq
                x0
                (_root_.Geb.Kernel.leaf 10))).label ≠ 0 then
              _root_.GebMirror.Metalogic.«Prelude.some» (_root_.Geb.Kernel.leaf 7)
            else
              if (_root_.GebMirror.Metalogic.«Prelude.or»
                (_root_.Geb.Kernel.Const.eq x0 (_root_.Geb.Kernel.leaf 11))
                (_root_.Geb.Kernel.Const.eq
                  x0
                  (_root_.Geb.Kernel.leaf 12))).label ≠ 0 then
                _root_.GebMirror.Metalogic.«Prelude.some» (_root_.Geb.Kernel.leaf 8)
              else
                if (_root_.Geb.Kernel.Const.eq
                  x0
                  (_root_.Geb.Kernel.leaf 13)).label ≠ 0 then
                  _root_.GebMirror.Metalogic.«Prelude.some» (_root_.Geb.Kernel.leaf 9)
                else
                  _root_.GebMirror.Metalogic.«Prelude.none»);
    x1

def «Prover.nrKey» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (let x2 : _root_.Geb.Kernel.Tree := x1;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x2)
                                          (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
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
                                          let _ : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            x5
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (_ : _root_.Geb.Kernel.Tree)
                                               (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              x8);
                                          _root_.GebMirror.Metalogic.«Prover.ruleKey» x4
                                        else
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
                                            _root_.GebMirror.Metalogic.«Prelude.some»
                                              (_root_.Geb.Kernel.Const.add
                                                (_root_.Geb.Kernel.leaf 12)
                                                (_root_.Geb.Kernel.Const.mul
                                                  (_root_.Geb.Kernel.leaf 2)
                                                  x4))
                                          else
                                            if (_root_.Geb.Kernel.Const.eq
                                              (_root_.Geb.Kernel.Const.label x2)
                                              (_root_.Geb.Kernel.leaf 3)).label ≠ 0 then
                                              let _ : _root_.List
                                                _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                x2;
                                              _root_.GebMirror.Metalogic.«Prelude.some»
                                                (_root_.Geb.Kernel.leaf 0)
                                            else
                                              if (_root_.Geb.Kernel.Const.eq
                                                (_root_.Geb.Kernel.Const.label x2)
                                                (_root_.Geb.Kernel.leaf 4)).label ≠ 0 then
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
                                                let _ : _root_.List
                                                  _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                  (α := _root_.Geb.Kernel.Tree)
                                                  (β := _root_.List _root_.Geb.Kernel.Tree)
                                                  x5
                                                  ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                  (fun (_ : _root_.Geb.Kernel.Tree)
                                                     (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                                                    x8);
                                                let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Derivation.thmAt»
                                                  x0
                                                  x4;
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
                                                  let x12 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Derivation.eqParts»
                                                    (_root_.GebMirror.Metalogic.«Derivation.thConcl» x10);
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
                                                         (x16 : _root_.List
                                                           _root_.Geb.Kernel.Tree) =>
                                                        x16);
                                                    _root_.GebMirror.Metalogic.«Prover.patternKey»
                                                      (_root_.GebMirror.Metalogic.«Language.p1» x14)
                                                  else
                                                    let _ : _root_.List
                                                      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                      x12;
                                                    _root_.GebMirror.Metalogic.«Prelude.none»
                                                else
                                                  let _ : _root_.List
                                                    _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                    x8;
                                                  _root_.GebMirror.Metalogic.«Prelude.none»
                                              else
                                                if (_root_.Geb.Kernel.Const.eq
                                                  (_root_.Geb.Kernel.Const.label x2)
                                                  (_root_.Geb.Kernel.leaf 5)).label ≠ 0 then
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
                                                  let _ : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
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
                                                  _root_.GebMirror.Metalogic.«Prover.patternKey» x8
                                                else
                                                  _root_.GebMirror.Metalogic.«Prelude.none»);
    x2

def «Prover.keyFits» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Prelude.isSome»
      x1).label ≠ 0 then
      _root_.Geb.Kernel.Const.eq (_root_.GebMirror.Metalogic.«Prelude.get» x1) x0
    else
      _root_.Geb.Kernel.leaf 1);
    x2

def «Prover.bucketOf» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x3 : _root_.Geb.Kernel.Tree)
         (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
        if (_root_.GebMirror.Metalogic.«Prover.keyFits»
          x2
          (_root_.GebMirror.Metalogic.«Prover.nrKey» x0 x3)).label ≠ 0 then
          (x3 :: x4)
        else
          x4)
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      x1;
    x3

def «Prover.ruleKeys» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.nrKey»
          x0
          x2;
        if (_root_.GebMirror.Metalogic.«Prelude.and»
          (_root_.GebMirror.Metalogic.«Prelude.isSome» x4)
          (_root_.GebMirror.Metalogic.«Base.not»
            (_root_.GebMirror.Metalogic.«Base.anyT»
              (fun (x5 : _root_.Geb.Kernel.Tree) =>
                _root_.Geb.Kernel.Const.eq x5 (_root_.GebMirror.Metalogic.«Prelude.get» x4))
              x3))).label ≠ 0 then
          ((_root_.GebMirror.Metalogic.«Prelude.get» x4) :: x3)
        else
          x3)
      ([] : _root_.List _root_.Geb.Kernel.Tree)
      x1;
    x2

def «Prover.indexRules» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      (_root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree) ×
      _root_.List
        _root_.Geb.Kernel.Tree := (_root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List
        (_root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree))
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.List
           (_root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree)) =>
        ((x2, _root_.GebMirror.Metalogic.«Prover.bucketOf» x0 x1 x2) :: x3))
      ([] : _root_.List (_root_.Geb.Kernel.Tree ×
        _root_.List _root_.Geb.Kernel.Tree))
      (_root_.GebMirror.Metalogic.«Prover.ruleKeys» x0 x1),
      _root_.Geb.Kernel.Const.foldr
        (α := _root_.Geb.Kernel.Tree)
        (β := _root_.List _root_.Geb.Kernel.Tree)
        (fun (x2 : _root_.Geb.Kernel.Tree)
           (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
          if (_root_.GebMirror.Metalogic.«Prelude.isSome»
            (_root_.GebMirror.Metalogic.«Prover.nrKey» x0 x2)).label ≠ 0 then
            x3
          else
            (x2 :: x3))
        ([] : _root_.List _root_.Geb.Kernel.Tree)
        x1);
    x2

def «Prover.ruleBucket» :=
  fun (x0 : _root_.List
      (_root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree) ×
      _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
        if (_root_.Geb.Kernel.Const.eq (x2).1 x1).label ≠ 0 then
          (x2).2
        else
          x3)
      (x0).2
      (x0).1;
    x2

def «$50726f7665722f5254732e7461696c» :=
  fun (x0 : _root_.List
      ((_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
    _root_.Geb.Kernel.Const.lcase
      (α := (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (β := _root_.List
        ((_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      x0
      ([] : _root_.List ((_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      (fun (_ : (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
           _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
         (x2 : _root_.List
           ((_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
             _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
        x2)

def «Prover.childRen» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Prelude.and»
      (_root_.Geb.Kernel.Const.eq x0 (_root_.Geb.Kernel.leaf 5))
      (_root_.Geb.Kernel.Const.eq
        x1
        (_root_.Geb.Kernel.leaf 1))).label ≠ 0 then
      fun (x4 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Language.liftR» x2 x4
    else
      if (_root_.GebMirror.Metalogic.«Prelude.and»
        (_root_.Geb.Kernel.Const.eq x0 (_root_.Geb.Kernel.leaf 8))
        (_root_.Geb.Kernel.Const.eq
          x1
          (_root_.Geb.Kernel.leaf 3))).label ≠ 0 then
        if (_root_.Geb.Kernel.Const.eq
          x3
          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
          fun (x4 : _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Metalogic.«Language.liftR» x2 x4
        else
          x2
      else
        if (_root_.GebMirror.Metalogic.«Prelude.and»
          (_root_.Geb.Kernel.Const.eq x0 (_root_.Geb.Kernel.leaf 9))
          (_root_.Geb.Kernel.Const.eq
            x1
            (_root_.Geb.Kernel.leaf 3))).label ≠ 0 then
          if (_root_.Geb.Kernel.Const.eq
            x3
            (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
            fun (x4 : _root_.Geb.Kernel.Tree) =>
              _root_.GebMirror.Metalogic.«Language.liftR»
                (fun (x5 : _root_.Geb.Kernel.Tree) =>
                  _root_.GebMirror.Metalogic.«Language.liftR» x2 x5)
                x4
          else
            x2
        else
          if (_root_.GebMirror.Metalogic.«Prelude.and»
            (_root_.Geb.Kernel.Const.eq x0 (_root_.Geb.Kernel.leaf 10))
            (_root_.Geb.Kernel.Const.eq
              x1
              (_root_.Geb.Kernel.leaf 2))).label ≠ 0 then
            if (_root_.Geb.Kernel.Const.eq
              x3
              (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
              fun (x4 : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.Metalogic.«Language.liftR» x2 x4
            else
              x2
          else
            x2);
    x4

def «Prover.holdAll» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List
      ((_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
    let x3 : (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
      _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (β := (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
        _root_.Geb.Kernel.Tree →
          _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (fun (x3 : (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
           _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
         (x4 : (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
           _root_.Geb.Kernel.Tree →
             _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
         (x5 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
         (x6 : _root_.Geb.Kernel.Tree)
         (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.lcase
          (α := _root_.Geb.Kernel.Tree)
          (β := _root_.Geb.Kernel.Tree)
          x7
          (_root_.Geb.Kernel.leaf 0)
          (fun (x8 : _root_.Geb.Kernel.Tree)
             (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Metalogic.«Prelude.and»
              (x3 (_root_.GebMirror.Metalogic.«Prover.childRen» x0 x1 x5 x6) x8)
              (x4
                x5
                (_root_.Geb.Kernel.Const.add x6 (_root_.Geb.Kernel.leaf 1))
                x9)))
      (fun (_ : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
         (_ : _root_.Geb.Kernel.Tree)
         (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Base.isEmpty» x5)
      x2;
    x3

def «Prover.isRenameStep» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List
      ((_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
    let x2 : (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (let x2 : (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
                                     _root_.Geb.Kernel.Tree →
                                       _root_.List _root_.Geb.Kernel.Tree →
                                         _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.holdAll»
                                     (_root_.Geb.Kernel.Const.label x0)
                                     (_root_.GebMirror.Metalogic.«Prelude.length»
                                       (_root_.GebMirror.Metalogic.«Language.mArgs» x0))
                                     (_root_.GebMirror.Metalogic.«$50726f7665722f5254732e7461696c» x1);
                                   fun (x3 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
                                     (x4 : _root_.Geb.Kernel.Tree) =>
                                     if (_root_.Geb.Kernel.Const.eq
                                       (_root_.Geb.Kernel.Const.label x0)
                                       (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                                       _root_.GebMirror.Metalogic.«Prelude.and»
                                         (_root_.Geb.Kernel.Const.eq
                                           (_root_.Geb.Kernel.Const.label x4)
                                           (_root_.Geb.Kernel.leaf 0))
                                         (_root_.GebMirror.Metalogic.«Prelude.and»
                                           (_root_.Geb.Kernel.Const.eq
                                             (_root_.GebMirror.Metalogic.«Language.mD»
                                               x4
                                               (_root_.Geb.Kernel.leaf 0))
                                             (x3
                                               (_root_.GebMirror.Metalogic.«Language.mD»
                                                 x0
                                                 (_root_.Geb.Kernel.leaf 0))))
                                           (_root_.GebMirror.Metalogic.«Base.isEmpty»
                                             (_root_.GebMirror.Metalogic.«Language.mArgs» x4)))
                                     else
                                       _root_.GebMirror.Metalogic.«Prelude.and»
                                         (_root_.Geb.Kernel.Const.eq
                                           (_root_.Geb.Kernel.Const.label x4)
                                           (_root_.Geb.Kernel.Const.label x0))
                                         (_root_.GebMirror.Metalogic.«Prelude.and»
                                           (_root_.Geb.Kernel.Const.equal
                                             (_root_.Geb.Kernel.Const.child
                                               x4
                                               (_root_.Geb.Kernel.leaf 0))
                                             (_root_.Geb.Kernel.Const.child
                                               x0
                                               (_root_.Geb.Kernel.leaf 0)))
                                           (x2
                                             x3
                                             (_root_.Geb.Kernel.leaf 0)
                                             (_root_.GebMirror.Metalogic.«Language.mArgs» x4))));
    x2

def «Prover.isRename» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.para
      (α := (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      _root_.GebMirror.Metalogic.«Prover.isRenameStep»
      x0;
    x1

def «$50726f7665722f5048732e7461696c» :=
  fun (x0 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.Geb.Kernel.Tree ×
          (_root_.Geb.Kernel.Tree ×
            ((_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
              _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))))) =>
    _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree ×
        (_root_.Geb.Kernel.Tree ×
          (_root_.Geb.Kernel.Tree ×
            ((_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
              _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))))
      (β := _root_.List
        (_root_.Geb.Kernel.Tree ×
          (_root_.Geb.Kernel.Tree ×
            (_root_.Geb.Kernel.Tree ×
              ((_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
                _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))))
      x0
      ([] : _root_.List (_root_.Geb.Kernel.Tree ×
        (_root_.Geb.Kernel.Tree ×
          (_root_.Geb.Kernel.Tree ×
            ((_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
              _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))))
      (fun (_ : _root_.Geb.Kernel.Tree ×
           (_root_.Geb.Kernel.Tree ×
             (_root_.Geb.Kernel.Tree ×
               ((_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
                 _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))))
         (x2 : _root_.List
           (_root_.Geb.Kernel.Tree ×
             (_root_.Geb.Kernel.Tree ×
               (_root_.Geb.Kernel.Tree ×
                 ((_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
                   _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))))) =>
        x2)

def «Prover.ph0» :=
  (_root_.Geb.Kernel.leaf 0,
    (_root_.Geb.Kernel.leaf 0,
      (_root_.Geb.Kernel.leaf 0,
        fun (_ : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
          (_ : _root_.Geb.Kernel.Tree) =>
          _root_.Geb.Kernel.leaf 0)))

def «Prover.prepareHyps» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.Geb.Kernel.Tree ×
          (_root_.Geb.Kernel.Tree ×
            ((_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
              _root_.Geb.Kernel.Tree →
                _root_.Geb.Kernel.Tree)))) := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List
        (_root_.Geb.Kernel.Tree ×
          (_root_.Geb.Kernel.Tree ×
            (_root_.Geb.Kernel.Tree ×
              ((_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
                _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))))
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List
           (_root_.Geb.Kernel.Tree ×
             (_root_.Geb.Kernel.Tree ×
               (_root_.Geb.Kernel.Tree ×
                 ((_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
                   _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))))) =>
        ((let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Derivation.eqParts»
            x1;
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
            (_root_.Geb.Kernel.leaf 1,
              (_root_.GebMirror.Metalogic.«Language.p1» x5,
                (_root_.GebMirror.Metalogic.«Language.p2» x5,
                  _root_.GebMirror.Metalogic.«Prover.isRename» (_root_.GebMirror.Metalogic.«Language.p1» x5))))
          else
            let _ : _root_.List
              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x3;
            _root_.GebMirror.Metalogic.«Prover.ph0») ::
          x2))
      ([] : _root_.List (_root_.Geb.Kernel.Tree ×
        (_root_.Geb.Kernel.Tree ×
          (_root_.Geb.Kernel.Tree ×
            ((_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
              _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))))
      x0;
    x1

def «Prover.phAt» :=
  fun (x0 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.Geb.Kernel.Tree ×
          (_root_.Geb.Kernel.Tree ×
            ((_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
              _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))))
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree ×
      (_root_.Geb.Kernel.Tree ×
        (_root_.Geb.Kernel.Tree ×
          ((_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
            _root_.Geb.Kernel.Tree →
              _root_.Geb.Kernel.Tree))) := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree ×
        (_root_.Geb.Kernel.Tree ×
          (_root_.Geb.Kernel.Tree ×
            ((_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
              _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))))
      (β := _root_.Geb.Kernel.Tree ×
        (_root_.Geb.Kernel.Tree ×
          (_root_.Geb.Kernel.Tree ×
            ((_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
              _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))))
      (_root_.Geb.Kernel.Const.iter
        (α := _root_.List
          (_root_.Geb.Kernel.Tree ×
            (_root_.Geb.Kernel.Tree ×
              (_root_.Geb.Kernel.Tree ×
                ((_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
                  _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))))
        _root_.GebMirror.Metalogic.«$50726f7665722f5048732e7461696c»
        x0
        x1)
      _root_.GebMirror.Metalogic.«Prover.ph0»
      (fun (x2 : _root_.Geb.Kernel.Tree ×
           (_root_.Geb.Kernel.Tree ×
             (_root_.Geb.Kernel.Tree ×
               ((_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
                 _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))))
         (_ : _root_.List
           (_root_.Geb.Kernel.Tree ×
             (_root_.Geb.Kernel.Tree ×
               (_root_.Geb.Kernel.Tree ×
                 ((_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
                   _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))))) =>
        x2);
    x2

def «Prover.tryRuleK» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.List _root_.Geb.Kernel.Tree)
    (x6 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.Geb.Kernel.Tree ×
          (_root_.Geb.Kernel.Tree ×
            ((_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
              _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)))))
    (x7 : _root_.Geb.Kernel.Tree)
    (x8 : _root_.Geb.Kernel.Tree) =>
    let x9 : _root_.Geb.Kernel.Tree := (let x9 : _root_.Geb.Kernel.Tree := x7;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x9)
                                          (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
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
                                            _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.termsOf»
                                            x13;
                                          _root_.GebMirror.Metalogic.«Prover.mapTP»
                                            (fun (x16 : _root_.Geb.Kernel.Tree) =>
                                              _root_.GebMirror.Metalogic.«Language.pr»
                                                x16
                                                (_root_.GebMirror.Metalogic.«Prover.dNode»
                                                  x11
                                                  x15
                                                  ([] : _root_.List _root_.Geb.Kernel.Tree)))
                                            (_root_.GebMirror.Metalogic.«Derivation.rootStepK»
                                              x0
                                              x1
                                              x2
                                              x3
                                              x4
                                              x5
                                              x11
                                              x15
                                              x8)
                                        else
                                          if (_root_.Geb.Kernel.Const.eq
                                            (_root_.Geb.Kernel.Const.label x9)
                                            (_root_.Geb.Kernel.leaf 6)).label ≠ 0 then
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
                                            let _ : _root_.List
                                              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                              (α := _root_.Geb.Kernel.Tree)
                                              (β := _root_.List _root_.Geb.Kernel.Tree)
                                              x10
                                              ([] : _root_.List _root_.Geb.Kernel.Tree)
                                              (fun (_ : _root_.Geb.Kernel.Tree)
                                                 (x13 : _root_.List _root_.Geb.Kernel.Tree) =>
                                                x13);
                                            let x13 : _root_.Geb.Kernel.Tree ×
                                              (_root_.Geb.Kernel.Tree ×
                                                (_root_.Geb.Kernel.Tree ×
                                                  ((_root_.Geb.Kernel.Tree →
                                                    _root_.Geb.Kernel.Tree) →
                                                    _root_.Geb.Kernel.Tree →
                                                      _root_.Geb.Kernel.Tree))) := _root_.GebMirror.Metalogic.«Prover.phAt»
                                              x6
                                              x11;
                                            if (_root_.GebMirror.Metalogic.«Prelude.and»
                                              (x13).1
                                              (if (_root_.Geb.Kernel.Const.eq
                                                x4
                                                (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                                                _root_.Geb.Kernel.Const.equal x8 ((x13).2).1
                                              else
                                                (((x13).2).2).2
                                                  (fun (x14 : _root_.Geb.Kernel.Tree) =>
                                                    _root_.Geb.Kernel.Const.add x14 x4)
                                                  x8)).label ≠ 0 then
                                              _root_.GebMirror.Metalogic.«$4c616e67756167652f4f54506169722e6a757374»
                                                (_root_.GebMirror.Metalogic.«Language.pr»
                                                  (_root_.GebMirror.Metalogic.«Derivation.weakenBy»
                                                    x4
                                                    (((x13).2).2).1)
                                                  (_root_.GebMirror.Metalogic.«Prover.dNode»
                                                    (_root_.Geb.Kernel.leaf 17)
                                                    (_root_.GebMirror.Metalogic.«Theory.l2»
                                                      x11
                                                      (_root_.Geb.Kernel.leaf 0))
                                                    ([] : _root_.List _root_.Geb.Kernel.Tree)))
                                            else
                                              _root_.GebMirror.Metalogic.«$4c616e67756167652f4f54506169722e6e6f7468696e67»
                                          else
                                            _root_.GebMirror.Metalogic.«Prover.tryRule»
                                              x0
                                              x1
                                              x2
                                              x3
                                              ([] : _root_.List _root_.Geb.Kernel.Tree)
                                              x7
                                              x8);
    x9

def «Prover.rootRewriteK» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List
      (_root_.Geb.Kernel.Tree × _root_.List _root_.Geb.Kernel.Tree) ×
      _root_.List _root_.Geb.Kernel.Tree)
    (x4 : _root_.List
      (_root_.Geb.Kernel.Tree ×
        (_root_.Geb.Kernel.Tree ×
          (_root_.Geb.Kernel.Tree ×
            ((_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) →
              _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))))) =>
    let x5 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree := (fun (x5 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x6 : _root_.Geb.Kernel.Tree)
                                         (x7 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x8 : _root_.Geb.Kernel.Tree) =>
      _root_.Geb.Kernel.Const.foldr
        (α := _root_.Geb.Kernel.Tree)
        (β := _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
        (fun (x9 : _root_.Geb.Kernel.Tree)
           (x10 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
           (x11 : _root_.Geb.Kernel.Tree) =>
          let x12 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.tryRuleK»
            x0
            x1
            x2
            x5
            x6
            x7
            x4
            x9
            x11;
          if (_root_.GebMirror.Metalogic.«$4c616e67756167652f4f54506169722e69734a757374»
            x12).label ≠ 0 then
            x12
          else
            x10 x11)
        (fun (_ : _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.Metalogic.«$4c616e67756167652f4f54506169722e6e6f7468696e67»)
        (_root_.GebMirror.Metalogic.«Prover.ruleBucket»
          x3
          (_root_.GebMirror.Metalogic.«Prover.rootKey» x8))
        x8);
    x5

def «Prover.jobRw» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := x0
      (_root_.GebMirror.Metalogic.«Prover.jobCtx» x1)
      (_root_.GebMirror.Metalogic.«Prover.jobNum» x1)
      (_root_.GebMirror.Metalogic.«Prover.jobHyps» x1)
      x2;
    x3

def «Prover.stDone» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «Prover.stTail» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 1)
      (x0 ::
        (x1 ::
          (x2 :: (x3 :: (x4 :: ([] : _root_.List _root_.Geb.Kernel.Tree))))))

def «Prover.stFun» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 2)
      (x0 :: ([] : _root_.List _root_.Geb.Kernel.Tree))

def «Prover.stArg» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 3)
      (x0 :: (x1 :: (x2 :: ([] : _root_.List _root_.Geb.Kernel.Tree))))

def «Prover.stChild» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 4)
      (x0 :: (x1 :: (x2 :: ([] : _root_.List _root_.Geb.Kernel.Tree))))

def «Prover.stKids» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 5)
      (x0 ::
        (x1 :: (x2 :: (x3 :: ([] : _root_.List _root_.Geb.Kernel.Tree)))))

def «$50726f7665722f537441742e6d6170» :=
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

def «$50726f7665722f53744f75742e6d6170» :=
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

def «Prover.stResult» :=
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
                                          x3
                                        else
                                          _root_.GebMirror.Metalogic.«$50726f7665722f4f4e46522e6e6f7468696e67»);
    x1

def «Prover.stNeed» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := (let x1 : _root_.Geb.Kernel.Tree := x0;
                                 if (_root_.Geb.Kernel.Const.eq
                                   (_root_.Geb.Kernel.Const.label x1)
                                   (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
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
                                   let _ : _root_.List
                                     _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                     (α := _root_.Geb.Kernel.Tree)
                                     (β := _root_.List _root_.Geb.Kernel.Tree)
                                     x2
                                     ([] : _root_.List _root_.Geb.Kernel.Tree)
                                     (fun (_ : _root_.Geb.Kernel.Tree)
                                        (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
                                       x5);
                                   ([] : _root_.List _root_.Geb.Kernel.Tree)
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
                                     let _ : _root_.List
                                       _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                       (α := _root_.Geb.Kernel.Tree)
                                       (β := _root_.List _root_.Geb.Kernel.Tree)
                                       x10
                                       ([] : _root_.List _root_.Geb.Kernel.Tree)
                                       (fun (_ : _root_.Geb.Kernel.Tree)
                                          (x13 : _root_.List _root_.Geb.Kernel.Tree) =>
                                         x13);
                                     _root_.GebMirror.Metalogic.«$50726f7665722f4a6f624c2e73696e676c65» x3
                                   else
                                     if (_root_.Geb.Kernel.Const.eq
                                       (_root_.Geb.Kernel.Const.label x1)
                                       (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
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
                                       _root_.GebMirror.Metalogic.«$50726f7665722f4a6f624c2e73696e676c65»
                                         (_root_.GebMirror.Metalogic.«Prover.jobAt»
                                           x3
                                           (_root_.Geb.Kernel.leaf 0)
                                           (_root_.GebMirror.Metalogic.«Language.mArg»
                                             (_root_.GebMirror.Metalogic.«Prover.jobTerm» x3)
                                             (_root_.Geb.Kernel.leaf 0)))
                                     else
                                       if (_root_.Geb.Kernel.Const.eq
                                         (_root_.Geb.Kernel.Const.label x1)
                                         (_root_.Geb.Kernel.leaf 3)).label ≠ 0 then
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
                                         let _ : _root_.List
                                           _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                           (α := _root_.Geb.Kernel.Tree)
                                           (β := _root_.List _root_.Geb.Kernel.Tree)
                                           x6
                                           ([] : _root_.List _root_.Geb.Kernel.Tree)
                                           (fun (_ : _root_.Geb.Kernel.Tree)
                                              (x9 : _root_.List _root_.Geb.Kernel.Tree) =>
                                             x9);
                                         _root_.GebMirror.Metalogic.«$50726f7665722f4a6f624c2e73696e676c65» x7
                                       else
                                         if (_root_.Geb.Kernel.Const.eq
                                           (_root_.Geb.Kernel.Const.label x1)
                                           (_root_.Geb.Kernel.leaf 4)).label ≠ 0 then
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
                                           _root_.GebMirror.Metalogic.«$50726f7665722f4a6f624c2e73696e676c65»
                                             (_root_.GebMirror.Metalogic.«Prover.jobAt»
                                               x3
                                               (_root_.Geb.Kernel.leaf 0)
                                               x7)
                                         else
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
                                           let _ : _root_.List
                                             _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                             (α := _root_.Geb.Kernel.Tree)
                                             (β := _root_.List _root_.Geb.Kernel.Tree)
                                             x8
                                             ([] : _root_.List _root_.Geb.Kernel.Tree)
                                             (fun (_ : _root_.Geb.Kernel.Tree)
                                                (x11 : _root_.List _root_.Geb.Kernel.Tree) =>
                                               x11);
                                           _root_.GebMirror.Metalogic.«Prover.jobsOf» x9);
    x1

def «Prover.stDeep» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree := (let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.nfTerm»
                                          x4;
                                        let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.label
                                          x5;
                                        let x7 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mArgs»
                                          x5;
                                        if (_root_.Geb.Kernel.Const.eq
                                          x2
                                          (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                          _root_.GebMirror.Metalogic.«Prover.stKids»
                                            (_root_.GebMirror.Metalogic.«Prover.jobAt»
                                              x3
                                              (_root_.Geb.Kernel.leaf 1)
                                              x5)
                                            x5
                                            (_root_.GebMirror.Metalogic.«Prover.nfMarked» x4)
                                            (_root_.GebMirror.Metalogic.«Prover.jobs»
                                              (_root_.GebMirror.Metalogic.«$50726f7665722f4a6f6241742e6d6170»
                                                (fun (x8 : _root_.Geb.Kernel.Tree) =>
                                                  _root_.GebMirror.Metalogic.«Prover.jobAt»
                                                    x3
                                                    (if (_root_.GebMirror.Metalogic.«Prover.keepsWeak»
                                                      x6
                                                      x8).label ≠ 0 then
                                                      _root_.Geb.Kernel.leaf 4
                                                    else
                                                      _root_.Geb.Kernel.leaf 1)
                                                    (_root_.GebMirror.Metalogic.«Prelude.at» x7 x8))
                                                (_root_.GebMirror.Metalogic.«Base.range»
                                                  (_root_.GebMirror.Metalogic.«Prelude.length» x7))))
                                        else
                                          let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Derivation.childBinders»
                                            x0
                                            x1
                                            x5
                                            (_root_.GebMirror.Metalogic.«Prover.jobCtx» x3);
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
                                            let x12 : _root_.List
                                              _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Derivation.bindersOf»
                                              x10;
                                            let x13 : _root_.Geb.Kernel.Tree := (if (_root_.Geb.Kernel.Const.lt
                                              (_root_.GebMirror.Metalogic.«$44657269766174696f6e2f42696e6465724c2e6c656e677468»
                                                x12)
                                              (_root_.GebMirror.Metalogic.«Prelude.length» x7)).label ≠ 0 then
                                              _root_.GebMirror.Metalogic.«$44657269766174696f6e2f42696e6465724c2e6c656e677468»
                                                x12
                                            else
                                              _root_.GebMirror.Metalogic.«Prelude.length» x7);
                                            _root_.GebMirror.Metalogic.«Prover.stKids»
                                              (_root_.GebMirror.Metalogic.«Prover.jobAt» x3 x2 x5)
                                              x5
                                              (_root_.GebMirror.Metalogic.«Prover.nfMarked» x4)
                                              (_root_.GebMirror.Metalogic.«Prover.jobs»
                                                (_root_.GebMirror.Metalogic.«$50726f7665722f4a6f6241742e6d6170»
                                                  (fun (x14 : _root_.Geb.Kernel.Tree) =>
                                                    let x15 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$44657269766174696f6e2f42696e6465724c2e61744f72»
                                                      _root_.GebMirror.Metalogic.«Derivation.binder0»
                                                      x12
                                                      x14;
                                                    let x16 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.at»
                                                      x7
                                                      x14;
                                                    if (_root_.GebMirror.Metalogic.«Prelude.and»
                                                      (_root_.Geb.Kernel.Const.eq
                                                        x2
                                                        (_root_.Geb.Kernel.leaf 2))
                                                      (_root_.GebMirror.Metalogic.«Prover.keepsFold»
                                                        x6
                                                        x14)).label ≠ 0 then
                                                      _root_.GebMirror.Metalogic.«Prover.jobAt»
                                                        x3
                                                        (_root_.Geb.Kernel.leaf 4)
                                                        x16
                                                    else
                                                      _root_.GebMirror.Metalogic.«Prover.job»
                                                        x2
                                                        (_root_.GebMirror.Metalogic.«Language.objs»
                                                          (_root_.GebMirror.Metalogic.«Derivation.binderCtx»
                                                            x15))
                                                        (_root_.Geb.Kernel.Const.add
                                                          (_root_.GebMirror.Metalogic.«Prover.jobNum» x3)
                                                          (_root_.GebMirror.Metalogic.«Derivation.binderNum»
                                                            x15))
                                                        (_root_.GebMirror.Metalogic.«Derivation.terms»
                                                          (_root_.GebMirror.Metalogic.«Prover.jobHyps» x3))
                                                        x16)
                                                  (_root_.GebMirror.Metalogic.«Base.range» x13)))
                                          else
                                            let _ : _root_.List
                                              _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                              x8;
                                            _root_.GebMirror.Metalogic.«Prover.stDone»
                                              _root_.GebMirror.Metalogic.«$50726f7665722f4f4e46522e6e6f7468696e67»);
    x5

def «Prover.stAfter» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree := (if (_root_.Geb.Kernel.Const.eq
      x2
      (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
      _root_.GebMirror.Metalogic.«Prover.stDone»
        (_root_.GebMirror.Metalogic.«$50726f7665722f4f4e46522e6a757374» x4)
    else
      _root_.GebMirror.Metalogic.«Prover.stDeep» x0 x1 x2 x3 x4);
    x5

def «Prover.stRoot» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree)
    (x6 : _root_.Geb.Kernel.Tree)
    (x7 : _root_.Geb.Kernel.Tree) =>
    let x8 : _root_.Geb.Kernel.Tree := (let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.jobRw»
                                          x2
                                          x5
                                          x6;
                                        if (_root_.GebMirror.Metalogic.«$4c616e67756167652f4f54506169722e69734a757374»
                                          x8).label ≠ 0 then
                                          let x9 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$4c616e67756167652f4f54506169722e66726f6d4d61796265»
                                            _root_.GebMirror.Metalogic.«Prover.pr0»
                                            x8;
                                          _root_.GebMirror.Metalogic.«Prover.stTail»
                                            (_root_.GebMirror.Metalogic.«Prover.jobAt»
                                              x5
                                              x3
                                              (_root_.GebMirror.Metalogic.«Language.p1» x9))
                                            _root_.GebMirror.Metalogic.«Prover.dRefl»
                                            x7
                                            (_root_.GebMirror.Metalogic.«Prover.mark»
                                              (_root_.GebMirror.Metalogic.«Language.p2» x9)
                                              (_root_.Geb.Kernel.leaf 1))
                                            x4
                                        else
                                          _root_.GebMirror.Metalogic.«Prover.stAfter»
                                            x0
                                            x1
                                            x4
                                            x5
                                            (_root_.GebMirror.Metalogic.«Prover.nfr» x6 x7));
    x8

def «Prover.stStart» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.jobDp»
                                          x3;
                                        let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.jobTerm»
                                          x3;
                                        if (_root_.Geb.Kernel.Const.eq
                                          x4
                                          (_root_.Geb.Kernel.leaf 4)).label ≠ 0 then
                                          _root_.GebMirror.Metalogic.«Prover.stDone»
                                            (_root_.GebMirror.Metalogic.«$50726f7665722f4f4e46522e6a757374»
                                              (_root_.GebMirror.Metalogic.«Prover.nfr»
                                                x5
                                                _root_.GebMirror.Metalogic.«Prover.dRefl»))
                                        else
                                          if (_root_.GebMirror.Metalogic.«Language.mIs»
                                            (_root_.Geb.Kernel.leaf 6)
                                            (_root_.Geb.Kernel.leaf 2)
                                            x5).label ≠ 0 then
                                            _root_.GebMirror.Metalogic.«Prover.stFun» x3
                                          else
                                            let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.jobRw»
                                              x2
                                              x3
                                              x5;
                                            if (_root_.GebMirror.Metalogic.«$4c616e67756167652f4f54506169722e69734a757374»
                                              x6).label ≠ 0 then
                                              let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$4c616e67756167652f4f54506169722e66726f6d4d61796265»
                                                _root_.GebMirror.Metalogic.«Prover.pr0»
                                                x6;
                                              _root_.GebMirror.Metalogic.«Prover.stTail»
                                                (_root_.GebMirror.Metalogic.«Prover.jobAt»
                                                  x3
                                                  (_root_.Geb.Kernel.leaf 0)
                                                  (_root_.GebMirror.Metalogic.«Language.p1» x7))
                                                _root_.GebMirror.Metalogic.«Prover.dRefl»
                                                _root_.GebMirror.Metalogic.«Prover.dRefl»
                                                (_root_.GebMirror.Metalogic.«Prover.mark»
                                                  (_root_.GebMirror.Metalogic.«Language.p2» x7)
                                                  (_root_.Geb.Kernel.leaf 1))
                                                x4
                                            else
                                              let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.headChild»
                                                x5;
                                              if (_root_.GebMirror.Metalogic.«Prelude.isSome» x7).label ≠ 0 then
                                                let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.nth»
                                                  (_root_.GebMirror.Metalogic.«Language.mArgs» x5)
                                                  (_root_.GebMirror.Metalogic.«Prelude.get» x7);
                                                if (_root_.GebMirror.Metalogic.«Prelude.isSome»
                                                  x8).label ≠ 0 then
                                                  _root_.GebMirror.Metalogic.«Prover.stChild»
                                                    x3
                                                    (_root_.GebMirror.Metalogic.«Prelude.get» x7)
                                                    (_root_.GebMirror.Metalogic.«Prelude.get» x8)
                                                else
                                                  _root_.GebMirror.Metalogic.«Prover.stDone»
                                                    _root_.GebMirror.Metalogic.«$50726f7665722f4f4e46522e6e6f7468696e67»
                                              else
                                                _root_.GebMirror.Metalogic.«Prover.stAfter»
                                                  x0
                                                  x1
                                                  x4
                                                  x3
                                                  (_root_.GebMirror.Metalogic.«Prover.nfr»
                                                    x5
                                                    _root_.GebMirror.Metalogic.«Prover.dRefl»));
    x4

def «Prover.stAdv» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree := (let x5 : _root_.Geb.Kernel.Tree := x3;
                                        if (_root_.Geb.Kernel.Const.eq
                                          (_root_.Geb.Kernel.Const.label x5)
                                          (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
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
                                          _root_.GebMirror.Metalogic.«Prover.stDone» x7
                                        else
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
                                            let x17 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.firstR»
                                              x4;
                                            if (_root_.Geb.Kernel.Const.eq
                                              (_root_.Geb.Kernel.Const.label x17)
                                              (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                              let x18 : _root_.List
                                                _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                x17;
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
                                              _root_.GebMirror.Metalogic.«Prover.stAfter»
                                                x0
                                                x1
                                                x15
                                                x7
                                                (_root_.GebMirror.Metalogic.«Prover.nfr»
                                                  (_root_.GebMirror.Metalogic.«Prover.nfTerm» x19)
                                                  (_root_.GebMirror.Metalogic.«Prover.dTrans»
                                                    x9
                                                    (_root_.GebMirror.Metalogic.«Prover.dTrans»
                                                      x11
                                                      (_root_.GebMirror.Metalogic.«Prover.dTrans»
                                                        x13
                                                        (_root_.GebMirror.Metalogic.«Prover.nfMarked» x19)))))
                                            else
                                              let _ : _root_.List
                                                _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                x17;
                                              _root_.GebMirror.Metalogic.«Prover.stDone»
                                                _root_.GebMirror.Metalogic.«$50726f7665722f4f4e46522e6e6f7468696e67»
                                          else
                                            if (_root_.Geb.Kernel.Const.eq
                                              (_root_.Geb.Kernel.Const.label x5)
                                              (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
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
                                              let x9 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.firstR»
                                                x4;
                                              if (_root_.Geb.Kernel.Const.eq
                                                (_root_.Geb.Kernel.Const.label x9)
                                                (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
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
                                                let _ : _root_.List
                                                  _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                  (α := _root_.Geb.Kernel.Tree)
                                                  (β := _root_.List _root_.Geb.Kernel.Tree)
                                                  x10
                                                  ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                  (fun (_ : _root_.Geb.Kernel.Tree)
                                                     (x13 : _root_.List _root_.Geb.Kernel.Tree) =>
                                                    x13);
                                                let x13 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.nfTerm»
                                                  x11;
                                                let x14 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mArg»
                                                  (_root_.GebMirror.Metalogic.«Prover.jobTerm» x7)
                                                  (_root_.Geb.Kernel.leaf 1);
                                                _root_.GebMirror.Metalogic.«Prover.stArg»
                                                  x7
                                                  x11
                                                  (if (_root_.GebMirror.Metalogic.«Language.mIs»
                                                    (_root_.Geb.Kernel.leaf 5)
                                                    (_root_.Geb.Kernel.leaf 1)
                                                    x13).label ≠ 0 then
                                                    _root_.GebMirror.Metalogic.«Prover.jobAt»
                                                      x7
                                                      (if (_root_.Geb.Kernel.Const.lt
                                                        (_root_.GebMirror.Metalogic.«Prover.uses»
                                                          (_root_.GebMirror.Metalogic.«Language.mArg»
                                                            x13
                                                            (_root_.Geb.Kernel.leaf 0))
                                                          (_root_.Geb.Kernel.leaf 0))
                                                        (_root_.Geb.Kernel.leaf 2)).label ≠ 0 then
                                                        _root_.Geb.Kernel.leaf 4
                                                      else
                                                        _root_.Geb.Kernel.leaf 1)
                                                      x14
                                                  else
                                                    _root_.GebMirror.Metalogic.«Prover.jobAt»
                                                      x7
                                                      (_root_.Geb.Kernel.leaf 0)
                                                      x14)
                                              else
                                                let _ : _root_.List
                                                  _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                  x9;
                                                _root_.GebMirror.Metalogic.«Prover.stDone»
                                                  _root_.GebMirror.Metalogic.«$50726f7665722f4f4e46522e6e6f7468696e67»
                                            else
                                              if (_root_.Geb.Kernel.Const.eq
                                                (_root_.Geb.Kernel.Const.label x5)
                                                (_root_.Geb.Kernel.leaf 3)).label ≠ 0 then
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
                                                let _ : _root_.List
                                                  _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                  (α := _root_.Geb.Kernel.Tree)
                                                  (β := _root_.List _root_.Geb.Kernel.Tree)
                                                  x10
                                                  ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                  (fun (_ : _root_.Geb.Kernel.Tree)
                                                     (x13 : _root_.List _root_.Geb.Kernel.Tree) =>
                                                    x13);
                                                let x13 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.firstR»
                                                  x4;
                                                if (_root_.Geb.Kernel.Const.eq
                                                  (_root_.Geb.Kernel.Const.label x13)
                                                  (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                                  let x14 : _root_.List
                                                    _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                    x13;
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
                                                  _root_.GebMirror.Metalogic.«Prover.stRoot»
                                                    x0
                                                    x1
                                                    x2
                                                    (_root_.Geb.Kernel.leaf 0)
                                                    (_root_.GebMirror.Metalogic.«Prover.jobDp» x7)
                                                    x7
                                                    (_root_.GebMirror.Metalogic.«Language.app»
                                                      (_root_.GebMirror.Metalogic.«Prover.nfTerm» x9)
                                                      (_root_.GebMirror.Metalogic.«Prover.nfTerm» x15))
                                                    (_root_.GebMirror.Metalogic.«Prover.dCong»
                                                      (_root_.GebMirror.Metalogic.«$50726f7665722f4d61726b6564462e6c32»
                                                        (_root_.GebMirror.Metalogic.«Prover.nfMarked» x9)
                                                        (_root_.GebMirror.Metalogic.«Prover.nfMarked» x15)))
                                                else
                                                  let _ : _root_.List
                                                    _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                    x13;
                                                  _root_.GebMirror.Metalogic.«Prover.stDone»
                                                    _root_.GebMirror.Metalogic.«$50726f7665722f4f4e46522e6e6f7468696e67»
                                              else
                                                if (_root_.Geb.Kernel.Const.eq
                                                  (_root_.Geb.Kernel.Const.label x5)
                                                  (_root_.Geb.Kernel.leaf 4)).label ≠ 0 then
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
                                                  let _ : _root_.List
                                                    _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                    (α := _root_.Geb.Kernel.Tree)
                                                    (β := _root_.List _root_.Geb.Kernel.Tree)
                                                    x10
                                                    ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                    (fun (_ : _root_.Geb.Kernel.Tree)
                                                       (x13 : _root_.List _root_.Geb.Kernel.Tree) =>
                                                      x13);
                                                  let x13 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.firstR»
                                                    x4;
                                                  if (_root_.Geb.Kernel.Const.eq
                                                    (_root_.Geb.Kernel.Const.label x13)
                                                    (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                                    let x14 : _root_.List
                                                      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                      x13;
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
                                                         (x17 : _root_.List
                                                           _root_.Geb.Kernel.Tree) =>
                                                        x17);
                                                    let x17 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.jobTerm»
                                                      x7;
                                                    if (_root_.GebMirror.Metalogic.«Prover.mFlag»
                                                      (_root_.GebMirror.Metalogic.«Prover.nfMarked»
                                                        x15)).label ≠ 0 then
                                                      let x18 : _root_.List
                                                        _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mArgs»
                                                        x17;
                                                      _root_.GebMirror.Metalogic.«Prover.stRoot»
                                                        x0
                                                        x1
                                                        x2
                                                        (_root_.Geb.Kernel.leaf 0)
                                                        (_root_.GebMirror.Metalogic.«Prover.jobDp» x7)
                                                        x7
                                                        (_root_.Geb.Kernel.Const.node
                                                          (_root_.Geb.Kernel.Const.label x17)
                                                          ((_root_.Geb.Kernel.Const.child
                                                            x17
                                                            (_root_.Geb.Kernel.leaf 0)) ::
                                                            (_root_.GebMirror.Metalogic.«Prover.setAt»
                                                              x18
                                                              x9
                                                              (_root_.GebMirror.Metalogic.«Prover.nfTerm»
                                                                x15))))
                                                        (_root_.GebMirror.Metalogic.«Prover.dCong»
                                                          (_root_.GebMirror.Metalogic.«$50726f7665722f4d61726b656441742e6d6170»
                                                            (fun (x19 : _root_.Geb.Kernel.Tree) =>
                                                              if (_root_.Geb.Kernel.Const.eq
                                                                x19
                                                                x9).label ≠ 0 then
                                                                _root_.GebMirror.Metalogic.«Prover.nfMarked» x15
                                                              else
                                                                _root_.GebMirror.Metalogic.«Prover.dRefl»)
                                                            (_root_.GebMirror.Metalogic.«Base.range»
                                                              (_root_.GebMirror.Metalogic.«Prelude.length»
                                                                x18))))
                                                    else
                                                      _root_.GebMirror.Metalogic.«Prover.stAfter»
                                                        x0
                                                        x1
                                                        (_root_.GebMirror.Metalogic.«Prover.jobDp» x7)
                                                        x7
                                                        (_root_.GebMirror.Metalogic.«Prover.nfr»
                                                          x17
                                                          _root_.GebMirror.Metalogic.«Prover.dRefl»)
                                                  else
                                                    let _ : _root_.List
                                                      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                      x13;
                                                    _root_.GebMirror.Metalogic.«Prover.stDone»
                                                      _root_.GebMirror.Metalogic.«$50726f7665722f4f4e46522e6e6f7468696e67»
                                                else
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
                                                  let x15 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.allSomeN»
                                                    x4;
                                                  if (_root_.Geb.Kernel.Const.eq
                                                    (_root_.Geb.Kernel.Const.label x15)
                                                    (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
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
                                                    let _ : _root_.List
                                                      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
                                                      (α := _root_.Geb.Kernel.Tree)
                                                      (β := _root_.List _root_.Geb.Kernel.Tree)
                                                      x16
                                                      ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                      (fun (_ : _root_.Geb.Kernel.Tree)
                                                         (x19 : _root_.List
                                                           _root_.Geb.Kernel.Tree) =>
                                                        x19);
                                                    let x19 : _root_.List
                                                      _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.nfrsOf»
                                                      x17;
                                                    let x20 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.rebuild»
                                                      x9
                                                      x19;
                                                    if (_root_.Geb.Kernel.Const.eq
                                                      (_root_.GebMirror.Metalogic.«Prover.jobDp» x7)
                                                      (_root_.Geb.Kernel.leaf 3)).label ≠ 0 then
                                                      let x21 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.dCong»
                                                        (_root_.GebMirror.Metalogic.«$50726f7665722f4e46524d61726b65642e6d6170»
                                                          _root_.GebMirror.Metalogic.«Prover.nfMarked»
                                                          x19);
                                                      let x22 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.jobRw»
                                                        x2
                                                        x7
                                                        x20;
                                                      if (_root_.GebMirror.Metalogic.«$4c616e67756167652f4f54506169722e69734a757374»
                                                        x22).label ≠ 0 then
                                                        let x23 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«$4c616e67756167652f4f54506169722e66726f6d4d61796265»
                                                          _root_.GebMirror.Metalogic.«Prover.pr0»
                                                          x22;
                                                        _root_.GebMirror.Metalogic.«Prover.stTail»
                                                          (_root_.GebMirror.Metalogic.«Prover.jobAt»
                                                            x7
                                                            (_root_.Geb.Kernel.leaf 3)
                                                            (_root_.GebMirror.Metalogic.«Language.p1» x23))
                                                          x11
                                                          x21
                                                          (_root_.GebMirror.Metalogic.«Prover.mark»
                                                            (_root_.GebMirror.Metalogic.«Language.p2» x23)
                                                            (_root_.Geb.Kernel.leaf 1))
                                                          (_root_.Geb.Kernel.leaf 0)
                                                      else
                                                        _root_.GebMirror.Metalogic.«Prover.stDone»
                                                          (_root_.GebMirror.Metalogic.«$50726f7665722f4f4e46522e6a757374»
                                                            (_root_.GebMirror.Metalogic.«Prover.nfr»
                                                              x20
                                                              (_root_.GebMirror.Metalogic.«Prover.dTrans»
                                                                x11
                                                                x21)))
                                                    else
                                                      let x21 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.dTrans»
                                                        x11
                                                        (_root_.GebMirror.Metalogic.«Prover.dCong»
                                                          (_root_.GebMirror.Metalogic.«$50726f7665722f4e46524d61726b65642e6d6170»
                                                            _root_.GebMirror.Metalogic.«Prover.nfMarked»
                                                            x19));
                                                      if (_root_.GebMirror.Metalogic.«Prover.marked»
                                                        x19).label ≠ 0 then
                                                        _root_.GebMirror.Metalogic.«Prover.stRoot»
                                                          x0
                                                          x1
                                                          x2
                                                          (_root_.GebMirror.Metalogic.«Prover.jobDp» x7)
                                                          (_root_.Geb.Kernel.leaf 0)
                                                          x7
                                                          x20
                                                          x21
                                                      else
                                                        _root_.GebMirror.Metalogic.«Prover.stDone»
                                                          (_root_.GebMirror.Metalogic.«$50726f7665722f4f4e46522e6a757374»
                                                            (_root_.GebMirror.Metalogic.«Prover.nfr» x20 x21))
                                                  else
                                                    let _ : _root_.List
                                                      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                                      x15;
                                                    _root_.GebMirror.Metalogic.«Prover.stDone»
                                                      _root_.GebMirror.Metalogic.«$50726f7665722f4f4e46522e6e6f7468696e67»);
    x5

def «Prover.stRound» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree)
      (fun (x5 : _root_.Geb.Kernel.Tree)
         (x6 : _root_.List _root_.Geb.Kernel.Tree →
           _root_.List _root_.Geb.Kernel.Tree)
         (x7 : _root_.List _root_.Geb.Kernel.Tree) =>
        let x8 : _root_.List _root_.Geb.Kernel.Tree ×
          _root_.List
            _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.splitRs»
          (_root_.GebMirror.Metalogic.«Prover.stNeed» x5)
          x7;
        ((_root_.GebMirror.Metalogic.«Prover.stAdv» x0 x1 x2 x5 (x8).1) :: (x6 (x8).2)))
      (fun (_ : _root_.List _root_.Geb.Kernel.Tree) =>
        ([] : _root_.List _root_.Geb.Kernel.Tree))
      x4
      (x3
        (_root_.Geb.Kernel.Const.foldr
          (α := _root_.Geb.Kernel.Tree)
          (β := _root_.List _root_.Geb.Kernel.Tree)
          (fun (x5 : _root_.Geb.Kernel.Tree)
             (x6 : _root_.List _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Metalogic.«$50726f7665722f4a6f624c2e617070656e64»
              (_root_.GebMirror.Metalogic.«Prover.stNeed» x5)
              x6)
          ([] : _root_.List _root_.Geb.Kernel.Tree)
          x4));
    x5

def «Prover.evalStepB» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List
        _root_.Geb.Kernel.Tree := (fun (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
      _root_.Geb.Kernel.Const.lcase
        (α := _root_.Geb.Kernel.Tree)
        (β := _root_.List _root_.Geb.Kernel.Tree)
        x4
        ([] : _root_.List _root_.Geb.Kernel.Tree)
        (fun (_ : _root_.Geb.Kernel.Tree)
           (_ : _root_.List _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.Metalogic.«$50726f7665722f53744f75742e6d6170»
            _root_.GebMirror.Metalogic.«Prover.stResult»
            (_root_.GebMirror.Metalogic.«Prover.stRound»
              x0
              x1
              x2
              x3
              (_root_.GebMirror.Metalogic.«Prover.stRound»
                x0
                x1
                x2
                x3
                (_root_.GebMirror.Metalogic.«Prover.stRound»
                  x0
                  x1
                  x2
                  x3
                  (_root_.GebMirror.Metalogic.«Prover.stRound»
                    x0
                    x1
                    x2
                    x3
                    (_root_.GebMirror.Metalogic.«Prover.stRound»
                      x0
                      x1
                      x2
                      x3
                      (_root_.GebMirror.Metalogic.«$50726f7665722f537441742e6d6170»
                        (fun (x7 : _root_.Geb.Kernel.Tree) =>
                          _root_.GebMirror.Metalogic.«Prover.stStart» x0 x1 x2 x7)
                        x4))))))));
    x4

def «Prover.evalB» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List
        _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.iter
      (α := _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«Prover.evalStepB» x0 x1 x2)
      (fun (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«$50726f7665722f53744f75742e6d6170»
          _root_.GebMirror.Metalogic.«Prover.stResult»
          (_root_.GebMirror.Metalogic.«$50726f7665722f537441742e6d6170»
            (fun (x5 : _root_.Geb.Kernel.Tree) =>
              _root_.GebMirror.Metalogic.«Prover.stDone»
                (_root_.GebMirror.Metalogic.«$50726f7665722f4f4e46522e6a757374»
                  (_root_.GebMirror.Metalogic.«Prover.nfr»
                    (_root_.GebMirror.Metalogic.«Prover.jobTerm» x5)
                    _root_.GebMirror.Metalogic.«Prover.dRefl»)))
            x4))
      x3;
    x4

def «Prover.evalK» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
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
      _root_.GebMirror.Metalogic.«Prover.firstR»
        (_root_.GebMirror.Metalogic.«Prover.evalB»
          x0
          x1
          x2
          x3
          (_root_.GebMirror.Metalogic.«$50726f7665722f4a6f624c2e73696e676c65»
            (_root_.GebMirror.Metalogic.«Prover.job»
              x4
              (_root_.GebMirror.Metalogic.«Language.objs» x5)
              x6
              (_root_.GebMirror.Metalogic.«Derivation.terms» x7)
              x8))));
    x4

def «Prover.eval» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree := (let x5 : _root_.List
                                         (_root_.Geb.Kernel.Tree ×
                                           _root_.List _root_.Geb.Kernel.Tree) ×
                                         _root_.List
                                           _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.indexRules»
                                         x1
                                         x3;
                                       fun (x6 : _root_.Geb.Kernel.Tree)
                                         (x7 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x8 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x9 : _root_.Geb.Kernel.Tree) =>
                                         _root_.GebMirror.Metalogic.«Prover.evalK»
                                           x0
                                           x2
                                           (_root_.GebMirror.Metalogic.«Prover.rootRewriteK»
                                             x0
                                             x1
                                             x2
                                             x5
                                             (_root_.GebMirror.Metalogic.«Prover.prepareHyps» x8))
                                           x4
                                           x6
                                           x7
                                           (_root_.Geb.Kernel.leaf 0)
                                           x8
                                           x9);
    x5

def «Prover.whnf» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.eval»
      x0
      x1
      x2
      x3
      x4
      (_root_.Geb.Kernel.leaf 0);
    x5

def «Prover.normalizeW» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.eval»
      x0
      x1
      x2
      x3
      x4
      (_root_.Geb.Kernel.leaf 3);
    x5

def «Prover.byNormW» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.List _root_.Geb.Kernel.Tree)
    (x6 : _root_.List _root_.Geb.Kernel.Tree)
    (x7 : _root_.Geb.Kernel.Tree)
    (x8 : _root_.Geb.Kernel.Tree) =>
    let x9 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.joinBy»
      (_root_.GebMirror.Metalogic.«Prover.normalizeW» x0 x1 x2 x3 x4)
      x5
      x6
      x7
      x8;
    x9

def «Prover.abstractVar» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mLam»
      x1
      (_root_.GebMirror.Metalogic.«Language.subst»
        (_root_.GebMirror.Metalogic.«Derivation.weaken1» x2)
        (fun (x3 : _root_.Geb.Kernel.Tree) =>
          if (_root_.Geb.Kernel.Const.eq
            x3
            (_root_.Geb.Kernel.Const.add
              x0
              (_root_.Geb.Kernel.leaf 1))).label ≠ 0 then
            _root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)
          else
            _root_.GebMirror.Metalogic.«Language.var» x3));
    x3

def «Prover.byFunExt» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree := (fun (x3 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x4 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x5 : _root_.Geb.Kernel.Tree)
                                         (x6 : _root_.Geb.Kernel.Tree) =>
      _root_.GebMirror.Metalogic.«Derivation.bindPT»
        (_root_.GebMirror.Metalogic.«Language.bindTP»
          (_root_.GebMirror.Metalogic.«Derivation.typeIn» x0 x1 x3 x5)
          _root_.GebMirror.Metalogic.«Language.expParts»)
        (fun (x7 : _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.Metalogic.«Base.mapO»
            (fun (x8 : _root_.Geb.Kernel.Tree) =>
              _root_.GebMirror.Metalogic.«Prover.dNode»
                (_root_.Geb.Kernel.leaf 26)
                ([] : _root_.List _root_.Geb.Kernel.Tree)
                (_root_.GebMirror.Metalogic.«Prelude.single» x8))
            (x2
              ((_root_.GebMirror.Metalogic.«Language.p1» x7) :: x3)
              (_root_.GebMirror.Metalogic.«Base.mapT» _root_.GebMirror.Metalogic.«Derivation.weaken1» x4)
              (_root_.GebMirror.Metalogic.«Language.app»
                (_root_.GebMirror.Metalogic.«Derivation.weaken1» x5)
                (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0)))
              (_root_.GebMirror.Metalogic.«Language.app»
                (_root_.GebMirror.Metalogic.«Derivation.weaken1» x6)
                (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))))));
    x3

def «Prover.bySplit» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree := (fun (x4 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x5 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x6 : _root_.Geb.Kernel.Tree)
                                         (x7 : _root_.Geb.Kernel.Tree) =>
      _root_.GebMirror.Metalogic.«Base.bindO»
        (_root_.GebMirror.Metalogic.«Prelude.nth» x4 x2)
        (fun (x8 : _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.Metalogic.«Prover.bindP»
            (_root_.GebMirror.Metalogic.«Language.coprodParts» x8)
            (fun (x9 : _root_.Geb.Kernel.Tree) =>
              let x10 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.p1» x9;
              let x11 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.p2» x9;
              let x12 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.abstractVar»
                x2
                x8
                x6;
              let x13 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.abstractVar»
                x2
                x8
                x7;
              let x14 : _root_.Geb.Kernel.Tree →
                _root_.Geb.Kernel.Tree →
                  _root_.Geb.Kernel.Tree := (fun (x14 : _root_.Geb.Kernel.Tree)
                                               (x15 : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.Metalogic.«Language.app»
                  (_root_.GebMirror.Metalogic.«Derivation.weaken1» x15)
                  (_root_.GebMirror.Metalogic.«Language.mArr»
                    x14
                    (_root_.GebMirror.Metalogic.«Theory.l2» x10 x11)
                    (_root_.GebMirror.Metalogic.«Language.var» (_root_.Geb.Kernel.leaf 0))));
              _root_.GebMirror.Metalogic.«Base.bindO»
                (x3
                  (x10 :: x4)
                  (_root_.GebMirror.Metalogic.«Base.mapT» _root_.GebMirror.Metalogic.«Derivation.weaken1» x5)
                  (x14 x0 x12)
                  (x14 x0 x13))
                (fun (x15 : _root_.Geb.Kernel.Tree) =>
                  _root_.GebMirror.Metalogic.«Base.bindO»
                    (x3
                      (x11 :: x4)
                      (_root_.GebMirror.Metalogic.«Base.mapT» _root_.GebMirror.Metalogic.«Derivation.weaken1» x5)
                      (x14 x1 x12)
                      (x14 x1 x13))
                    (fun (x16 : _root_.Geb.Kernel.Tree) =>
                      let x17 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.dNode»
                        (_root_.Geb.Kernel.leaf 26)
                        ([] : _root_.List _root_.Geb.Kernel.Tree)
                        (_root_.GebMirror.Metalogic.«Prelude.single»
                          (_root_.GebMirror.Metalogic.«Prover.dNode»
                            (_root_.Geb.Kernel.leaf 34)
                            (_root_.GebMirror.Metalogic.«Theory.l2» x0 x1)
                            (_root_.GebMirror.Metalogic.«Theory.l2» x15 x16)));
                      let x18 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.dNode»
                        (_root_.Geb.Kernel.leaf 2)
                        ([] : _root_.List _root_.Geb.Kernel.Tree)
                        (_root_.GebMirror.Metalogic.«Theory.l2»
                          (_root_.GebMirror.Metalogic.«Prover.dNode»
                            (_root_.Geb.Kernel.leaf 3)
                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                            ([] : _root_.List _root_.Geb.Kernel.Tree))
                          (_root_.GebMirror.Metalogic.«Prover.dNode»
                            (_root_.Geb.Kernel.leaf 3)
                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                            ([] : _root_.List _root_.Geb.Kernel.Tree)));
                      let x19 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.dNode»
                        (_root_.Geb.Kernel.leaf 18)
                        ([] : _root_.List _root_.Geb.Kernel.Tree)
                        (_root_.GebMirror.Metalogic.«Theory.l2»
                          (_root_.GebMirror.Metalogic.«Prover.dNode»
                            (_root_.Geb.Kernel.leaf 2)
                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                            (_root_.GebMirror.Metalogic.«Theory.l2»
                              (_root_.GebMirror.Metalogic.«Prover.dNode»
                                (_root_.Geb.Kernel.leaf 17)
                                (_root_.GebMirror.Metalogic.«Theory.l2»
                                  (_root_.GebMirror.Metalogic.«Prelude.length» x5)
                                  (_root_.Geb.Kernel.leaf 0))
                                ([] : _root_.List _root_.Geb.Kernel.Tree))
                              (_root_.GebMirror.Metalogic.«Prover.dNode»
                                (_root_.Geb.Kernel.leaf 0)
                                ([] : _root_.List _root_.Geb.Kernel.Tree)
                                ([] : _root_.List _root_.Geb.Kernel.Tree))))
                          (_root_.GebMirror.Metalogic.«Prover.dNode»
                            (_root_.Geb.Kernel.leaf 0)
                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                            ([] : _root_.List _root_.Geb.Kernel.Tree)));
                      let x20 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Language.mEq»
                        (_root_.GebMirror.Metalogic.«Language.app» x12 (_root_.GebMirror.Metalogic.«Language.var» x2))
                        (_root_.GebMirror.Metalogic.«Language.app»
                          x13
                          (_root_.GebMirror.Metalogic.«Language.var» x2));
                      _root_.GebMirror.Metalogic.«Prelude.some»
                        (_root_.GebMirror.Metalogic.«Prover.dNode»
                          (_root_.Geb.Kernel.leaf 22)
                          (_root_.GebMirror.Metalogic.«Prelude.single»
                            (_root_.GebMirror.Metalogic.«Language.mEq» x12 x13))
                          (_root_.GebMirror.Metalogic.«Theory.l2»
                            x17
                            (_root_.GebMirror.Metalogic.«Prover.dNode»
                              (_root_.Geb.Kernel.leaf 24)
                              (_root_.GebMirror.Metalogic.«Prelude.single» x20)
                              (_root_.GebMirror.Metalogic.«Theory.l2» x18 x19)))))))));
    x4

def «Prover.byListIndWith» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x5 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x6 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree := (fun (x6 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x7 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x8 : _root_.Geb.Kernel.Tree)
                                         (x9 : _root_.Geb.Kernel.Tree) =>
      _root_.Geb.Kernel.Const.lcase
        (α := _root_.Geb.Kernel.Tree)
        (β := _root_.Geb.Kernel.Tree)
        x6
        _root_.GebMirror.Metalogic.«Prelude.none»
        (fun (x10 : _root_.Geb.Kernel.Tree)
           (x11 : _root_.List _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.Metalogic.«Base.bindO»
            (_root_.GebMirror.Metalogic.«Language.listPart» x10)
            (fun (x12 : _root_.Geb.Kernel.Tree) =>
              _root_.GebMirror.Metalogic.«Prover.bindHT»
                (_root_.GebMirror.Metalogic.«Derivation.lowerHyps» x0 x1 x11 x7)
                (fun (x13 : _root_.Geb.Kernel.Tree) =>
                  let x14 : _root_.List
                    _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prover.termsOf» x13;
                  _root_.GebMirror.Metalogic.«Base.bindO»
                    (x4
                      x11
                      x14
                      (_root_.GebMirror.Metalogic.«Prover.instAt»
                        x2
                        (_root_.GebMirror.Metalogic.«Prelude.single» x12)
                        x8)
                      (_root_.GebMirror.Metalogic.«Prover.instAt»
                        x2
                        (_root_.GebMirror.Metalogic.«Prelude.single» x12)
                        x9))
                    (fun (x15 : _root_.Geb.Kernel.Tree) =>
                      _root_.GebMirror.Metalogic.«Base.mapO»
                        (fun (x16 : _root_.Geb.Kernel.Tree) =>
                          _root_.GebMirror.Metalogic.«Prover.dNode»
                            (_root_.Geb.Kernel.leaf 29)
                            (_root_.GebMirror.Metalogic.«Theory.l2» x2 x3)
                            (_root_.GebMirror.Metalogic.«Theory.l2» x15 x16))
                        (x5
                          (x10 :: (x12 :: x11))
                          (_root_.GebMirror.Metalogic.«Prelude.append»
                            (_root_.GebMirror.Metalogic.«Base.mapT» _root_.GebMirror.Metalogic.«Derivation.weaken2» x14)
                            (_root_.GebMirror.Metalogic.«Prelude.single»
                              (_root_.GebMirror.Metalogic.«Derivation.weakenElem»
                                (_root_.GebMirror.Metalogic.«Language.mEq» x8 x9))))
                          (_root_.GebMirror.Metalogic.«Derivation.listConsAt» x3 x12 x8)
                          (_root_.GebMirror.Metalogic.«Derivation.listConsAt» x3 x12 x9)))))));
    x6

def «Prover.byRoseInd» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree)
    (x6 : _root_.Geb.Kernel.Tree)
    (x7 : _root_.List _root_.Geb.Kernel.Tree)
    (x8 : _root_.Geb.Kernel.Tree)
    (x9 : _root_.List _root_.Geb.Kernel.Tree)
    (x10 : _root_.Geb.Kernel.Tree)
    (x11 : _root_.Geb.Kernel.Tree) =>
    let x12 : _root_.Geb.Kernel.Tree := (if (_root_.Geb.Kernel.Const.eq
      (_root_.GebMirror.Metalogic.«Prelude.length» x9)
      (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
      let x12 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.at»
        x9
        (_root_.Geb.Kernel.leaf 0);
      _root_.GebMirror.Metalogic.«Base.bindO»
        (_root_.GebMirror.Metalogic.«Language.roseLabel» x12)
        (fun (x13 : _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.Metalogic.«Base.bindO»
            (_root_.GebMirror.Metalogic.«Derivation.typeIn» x0 x2 x9 x10)
            (fun (x14 : _root_.Geb.Kernel.Tree) =>
              let x15 : _root_.List
                _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Theory.l2»
                (_root_.GebMirror.Metalogic.«Theory.list» x12)
                x13;
              _root_.GebMirror.Metalogic.«Base.bindO»
                (_root_.GebMirror.Metalogic.«Prover.byNorm»
                  x0
                  x1
                  x2
                  x7
                  x8
                  x15
                  ([] : _root_.List _root_.Geb.Kernel.Tree)
                  (_root_.GebMirror.Metalogic.«Derivation.roseNodeAt» x3 x12 x13 x10)
                  (_root_.GebMirror.Metalogic.«Language.subst»
                    x6
                    (_root_.GebMirror.Metalogic.«Derivation.atVar0»
                      (_root_.GebMirror.Metalogic.«Derivation.roseMapAt» x4 x5 x14 x10))))
                (fun (x16 : _root_.Geb.Kernel.Tree) =>
                  _root_.GebMirror.Metalogic.«Base.mapO»
                    (fun (x17 : _root_.Geb.Kernel.Tree) =>
                      _root_.GebMirror.Metalogic.«Prover.dNode»
                        (_root_.Geb.Kernel.leaf 32)
                        (_root_.GebMirror.Metalogic.«Theory.l4» x3 x4 x5 x6)
                        (_root_.GebMirror.Metalogic.«Theory.l2» x16 x17))
                    (_root_.GebMirror.Metalogic.«Prover.byNorm»
                      x0
                      x1
                      x2
                      x7
                      x8
                      x15
                      ([] : _root_.List _root_.Geb.Kernel.Tree)
                      (_root_.GebMirror.Metalogic.«Derivation.roseNodeAt» x3 x12 x13 x11)
                      (_root_.GebMirror.Metalogic.«Language.subst»
                        x6
                        (_root_.GebMirror.Metalogic.«Derivation.atVar0»
                          (_root_.GebMirror.Metalogic.«Derivation.roseMapAt» x4 x5 x14 x11)))))))
    else
      _root_.GebMirror.Metalogic.«Prelude.none»);
    x12

def «Prover.byRoseIndHyp» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.List _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree := (fun (x4 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x5 : _root_.List _root_.Geb.Kernel.Tree)
                                         (x6 : _root_.Geb.Kernel.Tree)
                                         (x7 : _root_.Geb.Kernel.Tree) =>
      if (_root_.GebMirror.Metalogic.«Prelude.and»
        (_root_.GebMirror.Metalogic.«Base.not» (_root_.GebMirror.Metalogic.«Base.isEmpty» x4))
        (_root_.GebMirror.Metalogic.«Base.isEmpty» x5)).label ≠ 0 then
        let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.at»
          x4
          (_root_.Geb.Kernel.leaf 0);
        _root_.GebMirror.Metalogic.«Base.bindO»
          (_root_.GebMirror.Metalogic.«Language.roseLabel» x8)
          (fun (x9 : _root_.Geb.Kernel.Tree) =>
            _root_.GebMirror.Metalogic.«Base.mapO»
              (fun (x10 : _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.Metalogic.«Prover.dNode»
                  (_root_.Geb.Kernel.leaf 33)
                  (_root_.GebMirror.Metalogic.«Theory.l3» x0 x1 x2)
                  (_root_.GebMirror.Metalogic.«Prelude.single» x10))
              (x3
                ((_root_.GebMirror.Metalogic.«Theory.list» x8) ::
                  (x9 :: (_root_.GebMirror.Metalogic.«Prelude.tail» x4)))
                (_root_.GebMirror.Metalogic.«Prelude.single»
                  (_root_.GebMirror.Metalogic.«Derivation.roseHyp»
                    x1
                    x2
                    (_root_.GebMirror.Metalogic.«Language.mEq» x6 x7)))
                (_root_.GebMirror.Metalogic.«Derivation.roseNodeAt» x0 x8 x9 x6)
                (_root_.GebMirror.Metalogic.«Derivation.roseNodeAt» x0 x8 x9 x7)))
      else
        _root_.GebMirror.Metalogic.«Prelude.none»);
    x4

end GebMirror.Metalogic

end
