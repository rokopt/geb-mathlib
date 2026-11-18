module

public import GebMirror.Metalogic.Printer

/-! Generated from a Geb program by `bootstrap/stage1/lean.geb`. -/

@[expose] public section

open Geb.Kernel
open Geb.Kernel renaming Tree → T

namespace GebMirror.Metalogic

def «$416666696e652f4346732e7461696c» :=
  fun (x0 : _root_.List
      (_root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
    _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (β := _root_.List
        (_root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      x0
      ([] : _root_.List (_root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree))
      (fun (_ : _root_.Geb.Kernel.Tree →
           _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
         (x2 : _root_.List
           (_root_.Geb.Kernel.Tree →
             _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
        x2)

def «Affine.isData» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.fold
      (α := _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Prelude.and»
          (_root_.GebMirror.Metalogic.«Base.not»
            (_root_.Geb.Kernel.Const.eq x1 (_root_.Geb.Kernel.leaf 3)))
          (_root_.GebMirror.Metalogic.«Base.allT»
            (fun (x3 : _root_.Geb.Kernel.Tree) => x3)
            x2))
      x0;
    x1

def «Affine.dBang» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.label
      (_root_.Geb.Kernel.Const.child x0 (_root_.Geb.Kernel.leaf 0));
    x1

def «Affine.dKids» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.tail»
      (_root_.Geb.Kernel.Const.children x0);
    x1

def «Affine.dMk» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.node
      x0
      (x1 :: x2);
    x3

def «Affine.dTy» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.fold
      (α := _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.node x1 (_root_.GebMirror.Metalogic.«Prelude.tail» x2))
      x0;
    x1

def «Affine.dData» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Affine.isData»
      (_root_.GebMirror.Metalogic.«Affine.dTy» x0);
    x1

def «Affine.dZero» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.fold
      (α := _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.Geb.Kernel.Const.node x1 ((_root_.Geb.Kernel.leaf 0) :: x2))
      x0;
    x1

def «Affine.dArrow» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Affine.dMk»
      (_root_.Geb.Kernel.leaf 3)
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (_root_.GebMirror.Metalogic.«Prelude.single» x1));
    x2

def «Affine.dList» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Affine.dMk»
      (_root_.Geb.Kernel.leaf 4)
      (_root_.Geb.Kernel.leaf 0)
      (_root_.GebMirror.Metalogic.«Prelude.single» x0);
    x1

def «Affine.withBang» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Affine.dData»
      x0).label ≠ 0 then
      x0
    else
      _root_.GebMirror.Metalogic.«Affine.dMk»
        (_root_.Geb.Kernel.Const.label x0)
        x1
        (_root_.GebMirror.Metalogic.«Affine.dKids» x0));
    x2

def «Affine.dShift» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Affine.withBang»
      x0
      (_root_.Geb.Kernel.Const.add (_root_.GebMirror.Metalogic.«Affine.dBang» x0) x1);
    x2

def «Affine.dUnbox» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Affine.withBang»
      x0
      (_root_.Geb.Kernel.Const.sub
        (_root_.GebMirror.Metalogic.«Affine.dBang» x0)
        (_root_.Geb.Kernel.leaf 1));
    x1

def «Affine.decorate» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.fold
      (α := _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.List
           (_root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
        let x4 : _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
          (α := _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
          (β := _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
          (fun (x4 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
             (x5 : _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
             (x6 : _root_.List _root_.Geb.Kernel.Tree) =>
            _root_.Geb.Kernel.Const.lcase
              (α := _root_.Geb.Kernel.Tree)
              (β := _root_.Geb.Kernel.Tree)
              x6
              _root_.GebMirror.Metalogic.«Prelude.none»
              (fun (x7 : _root_.Geb.Kernel.Tree)
                 (x8 : _root_.List _root_.Geb.Kernel.Tree) =>
                _root_.GebMirror.Metalogic.«Base.bindO»
                  (x4 x7)
                  (fun (x9 : _root_.Geb.Kernel.Tree) =>
                    _root_.GebMirror.Metalogic.«Base.mapO»
                      (fun (x10 : _root_.Geb.Kernel.Tree) =>
                        _root_.Geb.Kernel.Const.node
                          (_root_.Geb.Kernel.leaf 0)
                          (x9 :: (_root_.Geb.Kernel.Const.children x10)))
                      (x5 x8))))
          (fun (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
            if (_root_.GebMirror.Metalogic.«Base.isEmpty» x4).label ≠ 0 then
              _root_.GebMirror.Metalogic.«Prelude.some»
                (_root_.Geb.Kernel.Const.node
                  (_root_.Geb.Kernel.leaf 0)
                  ([] : _root_.List _root_.Geb.Kernel.Tree))
            else
              _root_.GebMirror.Metalogic.«Prelude.none»)
          x3;
        fun (x5 : _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.Metalogic.«Base.mapO»
            (fun (x6 : _root_.Geb.Kernel.Tree) =>
              let x7 : _root_.List
                _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x6;
              _root_.GebMirror.Metalogic.«Affine.dMk»
                x2
                (if (_root_.GebMirror.Metalogic.«Prelude.and»
                  (_root_.GebMirror.Metalogic.«Base.not»
                    (_root_.Geb.Kernel.Const.eq x2 (_root_.Geb.Kernel.leaf 3)))
                  (_root_.GebMirror.Metalogic.«Base.allT»
                    _root_.GebMirror.Metalogic.«Affine.dData»
                    x7)).label ≠ 0 then
                  _root_.Geb.Kernel.leaf 0
                else
                  _root_.Geb.Kernel.Const.label x5)
                x7)
            (x4 (_root_.Geb.Kernel.Const.children x5)))
      x0
      x1;
    x2

def «Affine.isPrefix» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.equal
      x0
      (_root_.Geb.Kernel.Const.node
        (_root_.Geb.Kernel.leaf 0)
        (_root_.GebMirror.Metalogic.«Base.take»
          (_root_.GebMirror.Metalogic.«Prelude.length»
            (_root_.Geb.Kernel.Const.children x0))
          (_root_.Geb.Kernel.Const.children x1)));
    x2

def «Affine.snocPath» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (_root_.GebMirror.Metalogic.«Prelude.append»
        (_root_.Geb.Kernel.Const.children x0)
        (_root_.GebMirror.Metalogic.«Prelude.single» x1));
    x2

def «Affine.countPath» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree) (x3 : _root_.Geb.Kernel.Tree) =>
        if (_root_.Geb.Kernel.Const.equal x2 x0).label ≠ 0 then
          _root_.Geb.Kernel.Const.add x3 (_root_.Geb.Kernel.leaf 1)
        else
          x3)
      (_root_.Geb.Kernel.leaf 0)
      x1;
    x2

def «Affine.belowPath» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Base.anyT»
      (fun (x2 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Prelude.and»
          (_root_.Geb.Kernel.Const.lt
            (_root_.GebMirror.Metalogic.«Prelude.length»
              (_root_.Geb.Kernel.Const.children x0))
            (_root_.GebMirror.Metalogic.«Prelude.length»
              (_root_.Geb.Kernel.Const.children x2)))
          (_root_.GebMirror.Metalogic.«Affine.isPrefix» x0 x2))
      x1;
    x2

def «Affine.ctStep» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List
      (_root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
    let x3 : _root_.Geb.Kernel.Tree →
      _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree := (let x3 : _root_.Geb.Kernel.Tree →
                                     _root_.Geb.Kernel.Tree →
                                       _root_.Geb.Kernel.Tree →
                                         _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
                                     (α := _root_.Geb.Kernel.Tree →
                                       _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
                                     (β := _root_.Geb.Kernel.Tree →
                                       _root_.Geb.Kernel.Tree →
                                         _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
                                     (fun (x3 : _root_.Geb.Kernel.Tree →
                                          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
                                        (x4 : _root_.Geb.Kernel.Tree →
                                          _root_.Geb.Kernel.Tree →
                                            _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
                                        (x5 : _root_.Geb.Kernel.Tree)
                                        (x6 : _root_.Geb.Kernel.Tree)
                                        (x7 : _root_.Geb.Kernel.Tree) =>
                                       let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Affine.snocPath»
                                         x5
                                         x7;
                                       _root_.GebMirror.Metalogic.«Prelude.and»
                                         (if (_root_.GebMirror.Metalogic.«Base.anyT»
                                           (fun (x9 : _root_.Geb.Kernel.Tree) =>
                                             _root_.GebMirror.Metalogic.«Affine.isPrefix» x8 x9)
                                           x0).label ≠ 0 then
                                           x3 x8 x6
                                         else
                                           _root_.Geb.Kernel.leaf 1)
                                         (x4
                                           x5
                                           x6
                                           (_root_.Geb.Kernel.Const.add
                                             x7
                                             (_root_.Geb.Kernel.leaf 1))))
                                     (fun (_ : _root_.Geb.Kernel.Tree)
                                        (_ : _root_.Geb.Kernel.Tree)
                                        (_ : _root_.Geb.Kernel.Tree) =>
                                       _root_.Geb.Kernel.leaf 1)
                                     (_root_.GebMirror.Metalogic.«$416666696e652f4346732e7461696c» x2);
                                   fun (x4 : _root_.Geb.Kernel.Tree)
                                     (x5 : _root_.Geb.Kernel.Tree) =>
                                     let x6 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.add
                                       (_root_.GebMirror.Metalogic.«Affine.dBang» x1)
                                       x5;
                                     let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Affine.countPath»
                                       x4
                                       x0;
                                     if (_root_.GebMirror.Metalogic.«Affine.dData» x1).label ≠ 0 then
                                       _root_.Geb.Kernel.leaf 1
                                     else
                                       if (_root_.GebMirror.Metalogic.«Prelude.or»
                                         (_root_.Geb.Kernel.Const.lt (_root_.Geb.Kernel.leaf 1) x7)
                                         (_root_.GebMirror.Metalogic.«Prelude.and»
                                           (_root_.Geb.Kernel.Const.lt
                                             (_root_.Geb.Kernel.leaf 0)
                                             x7)
                                           (_root_.GebMirror.Metalogic.«Affine.belowPath»
                                             x4
                                             x0))).label ≠ 0 then
                                         _root_.Geb.Kernel.Const.lt (_root_.Geb.Kernel.leaf 0) x6
                                       else
                                         _root_.GebMirror.Metalogic.«Prelude.or»
                                           (_root_.Geb.Kernel.Const.lt
                                             (_root_.Geb.Kernel.leaf 0)
                                             x7)
                                           (x3 x4 x6 (_root_.Geb.Kernel.leaf 0)));
    x3

def «Affine.contracts» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.para
      (α := _root_.Geb.Kernel.Tree →
        _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (_root_.GebMirror.Metalogic.«Affine.ctStep» x0)
      x1
      (_root_.Geb.Kernel.Const.node
        (_root_.Geb.Kernel.leaf 0)
        ([] : _root_.List _root_.Geb.Kernel.Tree))
      (_root_.Geb.Kernel.leaf 0);
    x2

def «Affine.dPlace» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
         (x4 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Base.bindO»
          (_root_.GebMirror.Metalogic.«Prelude.nth» (_root_.GebMirror.Metalogic.«Affine.dKids» x4) x2)
          (fun (x5 : _root_.Geb.Kernel.Tree) =>
            x3
              (if (_root_.GebMirror.Metalogic.«Affine.dData» x4).label ≠ 0 then
                x5
              else
                _root_.GebMirror.Metalogic.«Affine.dShift»
                  x5
                  (_root_.GebMirror.Metalogic.«Affine.dBang» x4))))
      _root_.GebMirror.Metalogic.«Prelude.some»
      x1
      x0;
    x2

def «Affine.plMk» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.node
      (_root_.Geb.Kernel.leaf 0)
      (x0 :: (_root_.GebMirror.Metalogic.«Prelude.single» x1));
    x2

def «Affine.plVar» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.child
      x0
      (_root_.Geb.Kernel.leaf 0);
    x1

def «Affine.plPath» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.child
      x0
      (_root_.Geb.Kernel.leaf 1);
    x1

def «Affine.termPlace» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.para
      (α := _root_.Geb.Kernel.Tree)
      (fun (x1 : _root_.Geb.Kernel.Tree)
         (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
        let x3 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.label x1;
        let x4 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.eq
          (_root_.GebMirror.Metalogic.«Prelude.length» x2)
          (_root_.Geb.Kernel.leaf 1);
        if (_root_.Geb.Kernel.Const.eq
          x3
          (_root_.Geb.Kernel.leaf 8)).label ≠ 0 then
          if (x4).label ≠ 0 then
            _root_.GebMirror.Metalogic.«Prelude.some»
              (_root_.GebMirror.Metalogic.«Affine.plMk»
                (_root_.Geb.Kernel.Const.label
                  (_root_.GebMirror.Metalogic.«Prelude.at»
                    (_root_.Geb.Kernel.Const.children x1)
                    (_root_.Geb.Kernel.leaf 0)))
                (_root_.Geb.Kernel.Const.node
                  (_root_.Geb.Kernel.leaf 0)
                  ([] : _root_.List _root_.Geb.Kernel.Tree)))
          else
            _root_.GebMirror.Metalogic.«Prelude.none»
        else
          if (_root_.Geb.Kernel.Const.eq
            x3
            (_root_.Geb.Kernel.leaf 13)).label ≠ 0 then
            if (x4).label ≠ 0 then
              _root_.GebMirror.Metalogic.«Base.mapO»
                (fun (x5 : _root_.Geb.Kernel.Tree) =>
                  _root_.GebMirror.Metalogic.«Affine.plMk»
                    (_root_.GebMirror.Metalogic.«Affine.plVar» x5)
                    (_root_.GebMirror.Metalogic.«Affine.snocPath»
                      (_root_.GebMirror.Metalogic.«Affine.plPath» x5)
                      (_root_.Geb.Kernel.leaf 0)))
                (_root_.GebMirror.Metalogic.«Prelude.at» x2 (_root_.Geb.Kernel.leaf 0))
            else
              _root_.GebMirror.Metalogic.«Prelude.none»
          else
            if (_root_.Geb.Kernel.Const.eq
              x3
              (_root_.Geb.Kernel.leaf 14)).label ≠ 0 then
              if (x4).label ≠ 0 then
                _root_.GebMirror.Metalogic.«Base.mapO»
                  (fun (x5 : _root_.Geb.Kernel.Tree) =>
                    _root_.GebMirror.Metalogic.«Affine.plMk»
                      (_root_.GebMirror.Metalogic.«Affine.plVar» x5)
                      (_root_.GebMirror.Metalogic.«Affine.snocPath»
                        (_root_.GebMirror.Metalogic.«Affine.plPath» x5)
                        (_root_.Geb.Kernel.leaf 1)))
                  (_root_.GebMirror.Metalogic.«Prelude.at» x2 (_root_.Geb.Kernel.leaf 0))
              else
                _root_.GebMirror.Metalogic.«Prelude.none»
            else
              _root_.GebMirror.Metalogic.«Prelude.none»)
      x0;
    x1

def «Affine.eraseT» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree → _root_.List _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.Geb.Kernel.Tree → _root_.List _root_.Geb.Kernel.Tree)
         (x4 : _root_.Geb.Kernel.Tree) =>
        if (_root_.GebMirror.Metalogic.«Prelude.and»
          (_root_.GebMirror.Metalogic.«Base.not» x4)
          (_root_.Geb.Kernel.Const.equal x2 x0)).label ≠ 0 then
          x3 (_root_.Geb.Kernel.leaf 1)
        else
          (x2 :: (x3 x4)))
      (fun (_ : _root_.Geb.Kernel.Tree) =>
        ([] : _root_.List _root_.Geb.Kernel.Tree))
      x1
      (_root_.Geb.Kernel.leaf 0);
    x2

def «Affine.diffT» :=
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
        x3 (_root_.GebMirror.Metalogic.«Affine.eraseT» x2 x4))
      (fun (x2 : _root_.List _root_.Geb.Kernel.Tree) => x2)
      x1
      x0;
    x2

def «Affine.usageMax» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.append»
      x0
      (_root_.GebMirror.Metalogic.«Affine.diffT» x1 x0);
    x2

def «Affine.res» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.some»
      (_root_.Geb.Kernel.Const.node
        (_root_.Geb.Kernel.leaf 0)
        (x0 ::
          (_root_.GebMirror.Metalogic.«Prelude.single»
            (_root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 0) x1))));
    x2

def «Affine.rD» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.child
      x0
      (_root_.Geb.Kernel.leaf 0);
    x1

def «Affine.rU» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.List
      _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
      (_root_.Geb.Kernel.Const.child x0 (_root_.Geb.Kernel.leaf 1));
    x1

def «Affine.ctxAt» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.nth» x0 x1;
    x2

def «Affine.occurrence» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Base.bindO»
      (_root_.GebMirror.Metalogic.«Affine.ctxAt» x0 (_root_.GebMirror.Metalogic.«Affine.plVar» x2))
      (fun (x3 : _root_.Geb.Kernel.Tree) =>
        let x4 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.child
          x3
          (_root_.Geb.Kernel.leaf 1);
        _root_.GebMirror.Metalogic.«Base.bindO»
          (_root_.GebMirror.Metalogic.«Affine.dPlace»
            (_root_.Geb.Kernel.Const.child x3 (_root_.Geb.Kernel.leaf 0))
            (_root_.Geb.Kernel.Const.children
              (_root_.GebMirror.Metalogic.«Affine.plPath» x2)))
          (fun (x5 : _root_.Geb.Kernel.Tree) =>
            if (_root_.Geb.Kernel.Const.lt x1 x4).label ≠ 0 then
              _root_.GebMirror.Metalogic.«Prelude.none»
            else
              if (_root_.GebMirror.Metalogic.«Affine.dData» x5).label ≠ 0 then
                _root_.GebMirror.Metalogic.«Affine.res» x5 (_root_.GebMirror.Metalogic.«Prelude.single» x2)
              else
                if (_root_.Geb.Kernel.Const.lt
                  (_root_.GebMirror.Metalogic.«Affine.dBang» x5)
                  (_root_.Geb.Kernel.Const.sub x1 x4)).label ≠ 0 then
                  _root_.GebMirror.Metalogic.«Prelude.none»
                else
                  _root_.GebMirror.Metalogic.«Affine.res»
                    (_root_.GebMirror.Metalogic.«Affine.withBang»
                      x5
                      (_root_.Geb.Kernel.Const.sub
                        (_root_.GebMirror.Metalogic.«Affine.dBang» x5)
                        (_root_.Geb.Kernel.Const.sub x1 x4)))
                    (_root_.GebMirror.Metalogic.«Prelude.single» x2)));
    x3

def «Affine.enter» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (if (_root_.GebMirror.Metalogic.«Base.allT»
      (fun (x4 : _root_.Geb.Kernel.Tree) =>
        let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Affine.ctxAt»
          x0
          (_root_.GebMirror.Metalogic.«Affine.plVar» x4);
        if (_root_.GebMirror.Metalogic.«Prelude.isSome» x5).label ≠ 0 then
          _root_.GebMirror.Metalogic.«Base.not»
            (_root_.Geb.Kernel.Const.lt
              x2
              (_root_.Geb.Kernel.Const.child
                (_root_.GebMirror.Metalogic.«Prelude.get» x5)
                (_root_.Geb.Kernel.leaf 1)))
        else
          _root_.Geb.Kernel.leaf 0)
      (_root_.GebMirror.Metalogic.«Affine.rU» x3)).label ≠ 0 then
      let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Affine.rD» x3;
      if (_root_.GebMirror.Metalogic.«Affine.dData» x4).label ≠ 0 then
        _root_.GebMirror.Metalogic.«Prelude.some» x3
      else
        if (_root_.Geb.Kernel.Const.lt
          (_root_.Geb.Kernel.Const.add (_root_.GebMirror.Metalogic.«Affine.dBang» x4) x2)
          x1).label ≠ 0 then
          _root_.GebMirror.Metalogic.«Prelude.none»
        else
          _root_.GebMirror.Metalogic.«Affine.res»
            (_root_.GebMirror.Metalogic.«Affine.withBang»
              x4
              (_root_.Geb.Kernel.Const.sub
                (_root_.Geb.Kernel.Const.add (_root_.GebMirror.Metalogic.«Affine.dBang» x4) x2)
                x1))
            (_root_.GebMirror.Metalogic.«Affine.rU» x3)
    else
      _root_.GebMirror.Metalogic.«Prelude.none»);
    x4

def «Affine.subOf» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Base.bindO»
      x2
      (fun (x4 : _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Affine.enter»
          x0
          x1
          (_root_.Geb.Kernel.Const.label x3)
          x4);
    x4

def «Affine.iterD» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Affine.dArrow»
      (_root_.GebMirror.Metalogic.«Affine.dMk»
        (_root_.Geb.Kernel.leaf 3)
        (_root_.Geb.Kernel.leaf 1)
        (x0 :: (_root_.GebMirror.Metalogic.«Prelude.single» x0)))
      (_root_.GebMirror.Metalogic.«Affine.dArrow»
        (_root_.GebMirror.Metalogic.«Affine.dShift» x0 (_root_.Geb.Kernel.leaf 1))
        (_root_.GebMirror.Metalogic.«Affine.dArrow»
          (_root_.GebMirror.Metalogic.«Affine.dZero» (_root_.Geb.Kernel.leaf 0))
          (_root_.GebMirror.Metalogic.«Affine.dShift» x0 (_root_.Geb.Kernel.leaf 1))));
    x1

def «Affine.foldD» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Affine.dArrow»
      (_root_.GebMirror.Metalogic.«Affine.dMk»
        (_root_.Geb.Kernel.leaf 3)
        (_root_.Geb.Kernel.leaf 1)
        ((_root_.GebMirror.Metalogic.«Affine.dZero» (_root_.Geb.Kernel.leaf 0)) ::
          (_root_.GebMirror.Metalogic.«Prelude.single»
            (_root_.GebMirror.Metalogic.«Affine.dArrow»
              (_root_.GebMirror.Metalogic.«Affine.dList» x0)
              x0))))
      (_root_.GebMirror.Metalogic.«Affine.dArrow»
        (_root_.GebMirror.Metalogic.«Affine.dZero» (_root_.Geb.Kernel.leaf 0))
        (_root_.GebMirror.Metalogic.«Affine.dShift» x0 (_root_.Geb.Kernel.leaf 1)));
    x1

def «Affine.foldrD» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Affine.dArrow»
      (_root_.GebMirror.Metalogic.«Affine.dMk»
        (_root_.Geb.Kernel.leaf 3)
        (_root_.Geb.Kernel.leaf 1)
        ((_root_.GebMirror.Metalogic.«Affine.dUnbox» x0) ::
          (_root_.GebMirror.Metalogic.«Prelude.single»
            (_root_.GebMirror.Metalogic.«Affine.dArrow» x1 x1))))
      (_root_.GebMirror.Metalogic.«Affine.dArrow»
        (_root_.GebMirror.Metalogic.«Affine.dShift» x1 (_root_.Geb.Kernel.leaf 1))
        (_root_.GebMirror.Metalogic.«Affine.dArrow»
          (_root_.GebMirror.Metalogic.«Affine.dList» x0)
          (_root_.GebMirror.Metalogic.«Affine.dShift» x1 (_root_.Geb.Kernel.leaf 1))));
    x2

def «Affine.lcaseD» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Affine.dArrow»
      (_root_.GebMirror.Metalogic.«Affine.dList» x0)
      (_root_.GebMirror.Metalogic.«Affine.dArrow»
        x1
        (_root_.GebMirror.Metalogic.«Affine.dArrow»
          (_root_.GebMirror.Metalogic.«Affine.dArrow»
            x0
            (_root_.GebMirror.Metalogic.«Affine.dArrow»
              (_root_.GebMirror.Metalogic.«Affine.dList» x0)
              x1))
          x1));
    x2

def «Affine.noBang» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.or»
      (_root_.GebMirror.Metalogic.«Affine.dData» x0)
      (_root_.Geb.Kernel.Const.eq
        (_root_.GebMirror.Metalogic.«Affine.dBang» x0)
        (_root_.Geb.Kernel.leaf 0));
    x1

def «Affine.lcaseSat» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree := (let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Affine.rD»
                                          x2;
                                        let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Affine.rD»
                                          x3;
                                        let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Affine.rD»
                                          x4;
                                        let x8 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Affine.dKids»
                                          x7;
                                        if (_root_.GebMirror.Metalogic.«Prelude.and»
                                          (_root_.Geb.Kernel.Const.equal
                                            (_root_.GebMirror.Metalogic.«Affine.dTy» x5)
                                            (_root_.GebMirror.Metalogic.«Check.tyList» x0))
                                          (_root_.GebMirror.Metalogic.«Prelude.and»
                                            (_root_.Geb.Kernel.Const.equal
                                              (_root_.GebMirror.Metalogic.«Affine.dTy» x6)
                                              x1)
                                            (_root_.GebMirror.Metalogic.«Prelude.and»
                                              (_root_.Geb.Kernel.Const.equal
                                                (_root_.GebMirror.Metalogic.«Affine.dTy» x7)
                                                (_root_.GebMirror.Metalogic.«Check.tyArrow»
                                                  x0
                                                  (_root_.GebMirror.Metalogic.«Check.tyArrow»
                                                    (_root_.GebMirror.Metalogic.«Check.tyList» x0)
                                                    x1)))
                                              (_root_.GebMirror.Metalogic.«Prelude.and»
                                                (_root_.GebMirror.Metalogic.«Affine.noBang» x5)
                                                (_root_.Geb.Kernel.Const.eq
                                                  (_root_.GebMirror.Metalogic.«Prelude.length» x8)
                                                  (_root_.Geb.Kernel.leaf 2)))))).label ≠ 0 then
                                          let x9 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.at»
                                            x8
                                            (_root_.Geb.Kernel.leaf 1);
                                          let x10 : _root_.List
                                            _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Affine.dKids»
                                            x9;
                                          if (_root_.GebMirror.Metalogic.«Prelude.and»
                                            (_root_.Geb.Kernel.Const.eq
                                              (_root_.GebMirror.Metalogic.«Prelude.length» x10)
                                              (_root_.Geb.Kernel.leaf 2))
                                            (_root_.GebMirror.Metalogic.«Prelude.and»
                                              (_root_.Geb.Kernel.Const.eq
                                                (_root_.GebMirror.Metalogic.«Affine.dBang» x7)
                                                (_root_.Geb.Kernel.leaf 0))
                                              (_root_.GebMirror.Metalogic.«Prelude.and»
                                                (_root_.Geb.Kernel.Const.eq
                                                  (_root_.GebMirror.Metalogic.«Affine.dBang» x9)
                                                  (_root_.Geb.Kernel.leaf 0))
                                                (_root_.GebMirror.Metalogic.«Prelude.and»
                                                  (_root_.Geb.Kernel.Const.equal
                                                    (_root_.GebMirror.Metalogic.«Prelude.some»
                                                      (_root_.GebMirror.Metalogic.«Prelude.at»
                                                        x8
                                                        (_root_.Geb.Kernel.leaf 0)))
                                                    (_root_.GebMirror.Metalogic.«Prelude.nth»
                                                      (_root_.GebMirror.Metalogic.«Affine.dKids» x5)
                                                      (_root_.Geb.Kernel.leaf 0)))
                                                  (_root_.GebMirror.Metalogic.«Prelude.and»
                                                    (_root_.Geb.Kernel.Const.equal
                                                      (_root_.GebMirror.Metalogic.«Prelude.at»
                                                        x10
                                                        (_root_.Geb.Kernel.leaf 0))
                                                      x5)
                                                    (_root_.Geb.Kernel.Const.equal
                                                      (_root_.GebMirror.Metalogic.«Prelude.at»
                                                        x10
                                                        (_root_.Geb.Kernel.leaf 1))
                                                      x6)))))).label ≠ 0 then
                                            _root_.GebMirror.Metalogic.«Affine.res»
                                              x6
                                              (_root_.GebMirror.Metalogic.«Prelude.append»
                                                (_root_.GebMirror.Metalogic.«Affine.rU» x2)
                                                (_root_.GebMirror.Metalogic.«Affine.usageMax»
                                                  (_root_.GebMirror.Metalogic.«Affine.rU» x3)
                                                  (_root_.GebMirror.Metalogic.«Affine.rU» x4)))
                                          else
                                            _root_.GebMirror.Metalogic.«Prelude.none»
                                        else
                                          _root_.GebMirror.Metalogic.«Prelude.none»);
    x5

def «Affine.project» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Affine.rD»
                                          x1;
                                        if (_root_.GebMirror.Metalogic.«Prelude.and»
                                          (_root_.Geb.Kernel.Const.eq
                                            (_root_.Geb.Kernel.Const.label x2)
                                            (_root_.Geb.Kernel.leaf 2))
                                          (_root_.GebMirror.Metalogic.«Affine.noBang» x2)).label ≠ 0 then
                                          _root_.GebMirror.Metalogic.«Base.mapO»
                                            (fun (x3 : _root_.Geb.Kernel.Tree) =>
                                              _root_.Geb.Kernel.Const.node
                                                (_root_.Geb.Kernel.leaf 0)
                                                (x3 ::
                                                  (_root_.GebMirror.Metalogic.«Prelude.single»
                                                    (_root_.Geb.Kernel.Const.child
                                                      x1
                                                      (_root_.Geb.Kernel.leaf 1)))))
                                            (_root_.GebMirror.Metalogic.«Prelude.nth»
                                              (_root_.GebMirror.Metalogic.«Affine.dKids» x2)
                                              x0)
                                        else
                                          _root_.GebMirror.Metalogic.«Prelude.none»);
    x2

def «Affine.abstraction» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (let x2 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Affine.rU» x1;
                                        if (_root_.GebMirror.Metalogic.«Affine.contracts»
                                          (_root_.Geb.Kernel.Const.foldr
                                            (α := _root_.Geb.Kernel.Tree)
                                            (β := _root_.List _root_.Geb.Kernel.Tree)
                                            (fun (x3 : _root_.Geb.Kernel.Tree)
                                               (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
                                              if (_root_.Geb.Kernel.Const.eq
                                                (_root_.GebMirror.Metalogic.«Affine.plVar» x3)
                                                (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                                                ((_root_.GebMirror.Metalogic.«Affine.plPath» x3) :: x4)
                                              else
                                                x4)
                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                            x2)
                                          x0).label ≠ 0 then
                                          _root_.GebMirror.Metalogic.«Affine.res»
                                            (_root_.GebMirror.Metalogic.«Affine.dArrow»
                                              x0
                                              (_root_.GebMirror.Metalogic.«Affine.rD» x1))
                                            (_root_.Geb.Kernel.Const.foldr
                                              (α := _root_.Geb.Kernel.Tree)
                                              (β := _root_.List _root_.Geb.Kernel.Tree)
                                              (fun (x3 : _root_.Geb.Kernel.Tree)
                                                 (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
                                                if (_root_.Geb.Kernel.Const.eq
                                                  (_root_.GebMirror.Metalogic.«Affine.plVar» x3)
                                                  (_root_.Geb.Kernel.leaf 0)).label ≠ 0 then
                                                  x4
                                                else
                                                  ((_root_.GebMirror.Metalogic.«Affine.plMk»
                                                    (_root_.Geb.Kernel.Const.sub
                                                      (_root_.GebMirror.Metalogic.«Affine.plVar» x3)
                                                      (_root_.Geb.Kernel.leaf 1))
                                                    (_root_.GebMirror.Metalogic.«Affine.plPath» x3)) ::
                                                    x4))
                                              ([] : _root_.List _root_.Geb.Kernel.Tree)
                                              x2)
                                        else
                                          _root_.GebMirror.Metalogic.«Prelude.none»);
    x2

def «Affine.isSpine2» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.and»
      (_root_.GebMirror.Metalogic.«Prelude.and»
        (_root_.Geb.Kernel.Const.eq
          (_root_.Geb.Kernel.Const.label x0)
          (_root_.Geb.Kernel.leaf 10))
        (_root_.Geb.Kernel.Const.eq
          (_root_.GebMirror.Metalogic.«Prelude.length»
            (_root_.Geb.Kernel.Const.children x0))
          (_root_.Geb.Kernel.leaf 2)))
      (let x1 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.at»
         (_root_.Geb.Kernel.Const.children x0)
         (_root_.Geb.Kernel.leaf 0);
       _root_.GebMirror.Metalogic.«Prelude.and»
         (_root_.GebMirror.Metalogic.«Prelude.and»
           (_root_.Geb.Kernel.Const.eq
             (_root_.Geb.Kernel.Const.label x1)
             (_root_.Geb.Kernel.leaf 10))
           (_root_.Geb.Kernel.Const.eq
             (_root_.GebMirror.Metalogic.«Prelude.length»
               (_root_.Geb.Kernel.Const.children x1))
             (_root_.Geb.Kernel.leaf 2)))
         (let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.at»
            (_root_.Geb.Kernel.Const.children x1)
            (_root_.Geb.Kernel.leaf 0);
          _root_.GebMirror.Metalogic.«Prelude.and»
            (_root_.Geb.Kernel.Const.eq
              (_root_.Geb.Kernel.Const.label x2)
              (_root_.Geb.Kernel.leaf 24))
            (_root_.Geb.Kernel.Const.eq
              (_root_.GebMirror.Metalogic.«Prelude.length»
                (_root_.Geb.Kernel.Const.children x2))
              (_root_.Geb.Kernel.leaf 2))));
    x1

def «Affine.spineTy» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.at»
      (_root_.Geb.Kernel.Const.children
        (_root_.GebMirror.Metalogic.«Prelude.at»
          (_root_.Geb.Kernel.Const.children
            (_root_.GebMirror.Metalogic.«Prelude.at»
              (_root_.Geb.Kernel.Const.children x0)
              (_root_.Geb.Kernel.leaf 0)))
          (_root_.Geb.Kernel.leaf 0)))
      x1;
    x2

def «Affine.one» :=
  fun (x0 : _root_.Geb.Kernel.Tree) (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := (if (x0).label ≠ 0 then
      x1
    else
      _root_.GebMirror.Metalogic.«Prelude.none»);
    x2

def «Affine.subAt» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Affine.subOf»
      x2
      x3
      (x0 (_root_.Geb.Kernel.leaf 0) x1 x2 x4)
      x4;
    x5

def «Affine.semVar» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Affine.one»
      (_root_.GebMirror.Metalogic.«Prelude.and»
        (_root_.Geb.Kernel.Const.eq
          (_root_.GebMirror.Metalogic.«Prelude.length» x2)
          (_root_.Geb.Kernel.leaf 1))
        (_root_.GebMirror.Metalogic.«Base.isEmpty» x3))
      (_root_.GebMirror.Metalogic.«Affine.occurrence»
        x0
        x1
        (_root_.GebMirror.Metalogic.«Affine.plMk»
          (_root_.Geb.Kernel.Const.label
            (_root_.GebMirror.Metalogic.«Prelude.at» x2 (_root_.Geb.Kernel.leaf 0)))
          (_root_.Geb.Kernel.Const.node
            (_root_.Geb.Kernel.leaf 0)
            ([] : _root_.List _root_.Geb.Kernel.Tree))));
    x4

def «Affine.semProj» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.List _root_.Geb.Kernel.Tree)
    (x6 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Affine.one»
      (_root_.Geb.Kernel.Const.eq
        (_root_.GebMirror.Metalogic.«Prelude.length» x5)
        (_root_.Geb.Kernel.leaf 1))
      (let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Affine.termPlace»
         (_root_.GebMirror.Metalogic.«Prelude.at» x5 (_root_.Geb.Kernel.leaf 0));
       if (_root_.GebMirror.Metalogic.«Prelude.isSome» x7).label ≠ 0 then
         _root_.GebMirror.Metalogic.«Affine.one»
           (_root_.GebMirror.Metalogic.«Base.isEmpty» x6)
           (_root_.GebMirror.Metalogic.«Affine.occurrence»
             x3
             x4
             (_root_.GebMirror.Metalogic.«Affine.plMk»
               (_root_.GebMirror.Metalogic.«Affine.plVar» (_root_.GebMirror.Metalogic.«Prelude.get» x7))
               (_root_.GebMirror.Metalogic.«Affine.snocPath»
                 (_root_.GebMirror.Metalogic.«Affine.plPath» (_root_.GebMirror.Metalogic.«Prelude.get» x7))
                 x0)))
       else
         _root_.GebMirror.Metalogic.«Affine.one»
           (_root_.Geb.Kernel.Const.eq
             (_root_.GebMirror.Metalogic.«Prelude.length» x6)
             (_root_.Geb.Kernel.leaf 1))
           (_root_.GebMirror.Metalogic.«Base.bindO»
             (_root_.GebMirror.Metalogic.«Affine.subAt»
               x1
               x2
               x3
               x4
               (_root_.GebMirror.Metalogic.«Prelude.at» x6 (_root_.Geb.Kernel.leaf 0)))
             (fun (x8 : _root_.Geb.Kernel.Tree) =>
               _root_.GebMirror.Metalogic.«Affine.project» x0 x8)));
    x7

def «Affine.semLam» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree)
    (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Affine.one»
      (_root_.GebMirror.Metalogic.«Prelude.and»
        (_root_.Geb.Kernel.Const.eq
          (_root_.GebMirror.Metalogic.«Prelude.length» x4)
          (_root_.Geb.Kernel.leaf 2))
        (_root_.GebMirror.Metalogic.«Prelude.and»
          (_root_.Geb.Kernel.Const.eq
            (_root_.GebMirror.Metalogic.«Prelude.length» x5)
            (_root_.Geb.Kernel.leaf 2))
          (_root_.GebMirror.Metalogic.«Check.isTy»
            (_root_.GebMirror.Metalogic.«Prelude.at» x4 (_root_.Geb.Kernel.leaf 0)))))
      (_root_.GebMirror.Metalogic.«Base.bindO»
        (_root_.GebMirror.Metalogic.«Affine.decorate»
          (_root_.GebMirror.Metalogic.«Prelude.at» x4 (_root_.Geb.Kernel.leaf 0))
          (_root_.GebMirror.Metalogic.«Prelude.at» x5 (_root_.Geb.Kernel.leaf 0)))
        (fun (x6 : _root_.Geb.Kernel.Tree) =>
          let x7 : _root_.List
            _root_.Geb.Kernel.Tree := ((_root_.Geb.Kernel.Const.node
            (_root_.Geb.Kernel.leaf 0)
            (x6 :: (_root_.GebMirror.Metalogic.«Prelude.single» x3))) ::
            x2);
          _root_.GebMirror.Metalogic.«Base.bindO»
            (_root_.GebMirror.Metalogic.«Affine.subAt»
              x0
              x1
              x7
              x3
              (_root_.GebMirror.Metalogic.«Prelude.at» x5 (_root_.Geb.Kernel.leaf 1)))
            (fun (x8 : _root_.Geb.Kernel.Tree) =>
              _root_.GebMirror.Metalogic.«Affine.abstraction» x6 x8)));
    x6

def «Affine.semSpine» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x5 : _root_.Geb.Kernel.Tree := (let x5 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.length»
                                          x4;
                                        let x6 : _root_.Geb.Kernel.Tree := x0
                                          (_root_.Geb.Kernel.leaf 1)
                                          x2
                                          x3
                                          (_root_.Geb.Kernel.Const.node
                                            (_root_.Geb.Kernel.leaf 0)
                                            (_root_.GebMirror.Metalogic.«Base.take»
                                              (_root_.Geb.Kernel.Const.sub
                                                x5
                                                (_root_.Geb.Kernel.leaf 1))
                                              x4));
                                        _root_.Geb.Kernel.Const.node
                                          (_root_.Geb.Kernel.leaf 0)
                                          (_root_.GebMirror.Metalogic.«Prelude.append»
                                            (_root_.Geb.Kernel.Const.children x6)
                                            (_root_.GebMirror.Metalogic.«Prelude.single»
                                              (x1
                                                (_root_.Geb.Kernel.leaf 0)
                                                x2
                                                x3
                                                (_root_.GebMirror.Metalogic.«Prelude.at»
                                                  x4
                                                  (_root_.Geb.Kernel.Const.sub
                                                    x5
                                                    (_root_.Geb.Kernel.leaf 1)))))));
    x5

def «Affine.semSat» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree)
    (x6 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Affine.one»
      (_root_.Geb.Kernel.Const.eq
        (_root_.GebMirror.Metalogic.«Prelude.length» x6)
        (_root_.Geb.Kernel.leaf 3))
      (let x7 : _root_.List
         _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
         (x1
           (_root_.Geb.Kernel.leaf 1)
           x3
           x4
           (_root_.Geb.Kernel.Const.node
             (_root_.Geb.Kernel.leaf 0)
             ((_root_.GebMirror.Metalogic.«Prelude.at» x6 (_root_.Geb.Kernel.leaf 0)) ::
               (_root_.GebMirror.Metalogic.«Prelude.single»
                 (_root_.GebMirror.Metalogic.«Prelude.at» x6 (_root_.Geb.Kernel.leaf 1))))));
       _root_.GebMirror.Metalogic.«Base.bindO»
         (_root_.GebMirror.Metalogic.«Affine.subOf»
           x4
           x5
           (_root_.GebMirror.Metalogic.«Prelude.at» x7 (_root_.Geb.Kernel.leaf 0))
           (_root_.GebMirror.Metalogic.«Prelude.at» x6 (_root_.Geb.Kernel.leaf 0)))
         (fun (x8 : _root_.Geb.Kernel.Tree) =>
           _root_.GebMirror.Metalogic.«Base.bindO»
             (_root_.GebMirror.Metalogic.«Affine.subOf»
               x4
               x5
               (_root_.GebMirror.Metalogic.«Prelude.at» x7 (_root_.Geb.Kernel.leaf 1))
               (_root_.GebMirror.Metalogic.«Prelude.at» x6 (_root_.Geb.Kernel.leaf 1)))
             (fun (x9 : _root_.Geb.Kernel.Tree) =>
               _root_.GebMirror.Metalogic.«Base.bindO»
                 (_root_.GebMirror.Metalogic.«Affine.subAt»
                   x2
                   x3
                   x4
                   x5
                   (_root_.GebMirror.Metalogic.«Prelude.at» x6 (_root_.Geb.Kernel.leaf 2)))
                 (fun (x10 : _root_.Geb.Kernel.Tree) =>
                   _root_.GebMirror.Metalogic.«Affine.lcaseSat»
                     (_root_.GebMirror.Metalogic.«Affine.spineTy» x0 (_root_.Geb.Kernel.leaf 0))
                     (_root_.GebMirror.Metalogic.«Affine.spineTy» x0 (_root_.Geb.Kernel.leaf 1))
                     x8
                     x9
                     x10))));
    x7

def «Affine.semApp» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Affine.one»
      (_root_.Geb.Kernel.Const.eq
        (_root_.GebMirror.Metalogic.«Prelude.length» x5)
        (_root_.Geb.Kernel.leaf 2))
      (_root_.GebMirror.Metalogic.«Base.bindO»
        (_root_.GebMirror.Metalogic.«Affine.subAt»
          x0
          x2
          x3
          x4
          (_root_.GebMirror.Metalogic.«Prelude.at» x5 (_root_.Geb.Kernel.leaf 0)))
        (fun (x6 : _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.Metalogic.«Base.bindO»
            (_root_.GebMirror.Metalogic.«Affine.subAt»
              x1
              x2
              x3
              x4
              (_root_.GebMirror.Metalogic.«Prelude.at» x5 (_root_.Geb.Kernel.leaf 1)))
            (fun (x7 : _root_.Geb.Kernel.Tree) =>
              let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Affine.rD» x6;
              let x9 : _root_.List
                _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Affine.dKids» x8;
              _root_.GebMirror.Metalogic.«Affine.one»
                (_root_.GebMirror.Metalogic.«Prelude.and»
                  (_root_.Geb.Kernel.Const.eq
                    (_root_.GebMirror.Metalogic.«Prelude.length» x9)
                    (_root_.Geb.Kernel.leaf 2))
                  (_root_.GebMirror.Metalogic.«Prelude.and»
                    (_root_.Geb.Kernel.Const.eq
                      (_root_.Geb.Kernel.Const.label x8)
                      (_root_.Geb.Kernel.leaf 3))
                    (_root_.GebMirror.Metalogic.«Prelude.and»
                      (_root_.Geb.Kernel.Const.eq
                        (_root_.GebMirror.Metalogic.«Affine.dBang» x8)
                        (_root_.Geb.Kernel.leaf 0))
                      (_root_.Geb.Kernel.Const.equal
                        (_root_.GebMirror.Metalogic.«Prelude.at» x9 (_root_.Geb.Kernel.leaf 0))
                        (_root_.GebMirror.Metalogic.«Affine.rD» x7)))))
                (_root_.GebMirror.Metalogic.«Affine.res»
                  (_root_.GebMirror.Metalogic.«Prelude.at» x9 (_root_.Geb.Kernel.leaf 1))
                  (_root_.GebMirror.Metalogic.«Prelude.append»
                    (_root_.GebMirror.Metalogic.«Affine.rU» x6)
                    (_root_.GebMirror.Metalogic.«Affine.rU» x7))))));
    x6

def «Affine.semPair» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Affine.one»
      (_root_.Geb.Kernel.Const.eq
        (_root_.GebMirror.Metalogic.«Prelude.length» x5)
        (_root_.Geb.Kernel.leaf 2))
      (_root_.GebMirror.Metalogic.«Base.bindO»
        (_root_.GebMirror.Metalogic.«Affine.subAt»
          x0
          x2
          x3
          x4
          (_root_.GebMirror.Metalogic.«Prelude.at» x5 (_root_.Geb.Kernel.leaf 0)))
        (fun (x6 : _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.Metalogic.«Base.bindO»
            (_root_.GebMirror.Metalogic.«Affine.subAt»
              x1
              x2
              x3
              x4
              (_root_.GebMirror.Metalogic.«Prelude.at» x5 (_root_.Geb.Kernel.leaf 1)))
            (fun (x7 : _root_.Geb.Kernel.Tree) =>
              _root_.GebMirror.Metalogic.«Affine.res»
                (_root_.GebMirror.Metalogic.«Affine.dMk»
                  (_root_.Geb.Kernel.leaf 2)
                  (_root_.Geb.Kernel.leaf 0)
                  ((_root_.GebMirror.Metalogic.«Affine.rD» x6) ::
                    (_root_.GebMirror.Metalogic.«Prelude.single» (_root_.GebMirror.Metalogic.«Affine.rD» x7))))
                (_root_.GebMirror.Metalogic.«Prelude.append»
                  (_root_.GebMirror.Metalogic.«Affine.rU» x6)
                  (_root_.GebMirror.Metalogic.«Affine.rU» x7)))));
    x6

def «Affine.semCond» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree)
    (x4 : _root_.List _root_.Geb.Kernel.Tree)
    (x5 : _root_.Geb.Kernel.Tree)
    (x6 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x7 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Affine.one»
      (_root_.Geb.Kernel.Const.eq
        (_root_.GebMirror.Metalogic.«Prelude.length» x6)
        (_root_.Geb.Kernel.leaf 3))
      (_root_.GebMirror.Metalogic.«Base.bindO»
        (_root_.GebMirror.Metalogic.«Affine.subAt»
          x0
          x3
          x4
          x5
          (_root_.GebMirror.Metalogic.«Prelude.at» x6 (_root_.Geb.Kernel.leaf 0)))
        (fun (x7 : _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.Metalogic.«Base.bindO»
            (_root_.GebMirror.Metalogic.«Affine.subAt»
              x1
              x3
              x4
              x5
              (_root_.GebMirror.Metalogic.«Prelude.at» x6 (_root_.Geb.Kernel.leaf 1)))
            (fun (x8 : _root_.Geb.Kernel.Tree) =>
              _root_.GebMirror.Metalogic.«Base.bindO»
                (_root_.GebMirror.Metalogic.«Affine.subAt»
                  x2
                  x3
                  x4
                  x5
                  (_root_.GebMirror.Metalogic.«Prelude.at» x6 (_root_.Geb.Kernel.leaf 2)))
                (fun (x9 : _root_.Geb.Kernel.Tree) =>
                  _root_.GebMirror.Metalogic.«Affine.one»
                    (_root_.GebMirror.Metalogic.«Prelude.and»
                      (_root_.Geb.Kernel.Const.equal
                        (_root_.GebMirror.Metalogic.«Affine.dTy» (_root_.GebMirror.Metalogic.«Affine.rD» x7))
                        (_root_.Geb.Kernel.leaf 0))
                      (_root_.Geb.Kernel.Const.equal
                        (_root_.GebMirror.Metalogic.«Affine.rD» x8)
                        (_root_.GebMirror.Metalogic.«Affine.rD» x9)))
                    (_root_.GebMirror.Metalogic.«Affine.res»
                      (_root_.GebMirror.Metalogic.«Affine.rD» x8)
                      (_root_.GebMirror.Metalogic.«Prelude.append»
                        (_root_.GebMirror.Metalogic.«Affine.rU» x7)
                        (_root_.GebMirror.Metalogic.«Affine.usageMax»
                          (_root_.GebMirror.Metalogic.«Affine.rU» x8)
                          (_root_.GebMirror.Metalogic.«Affine.rU» x9))))))));
    x7

def «Affine.semCons» :=
  fun (x0 : _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x6 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Affine.one»
      (_root_.Geb.Kernel.Const.eq
        (_root_.GebMirror.Metalogic.«Prelude.length» x5)
        (_root_.Geb.Kernel.leaf 2))
      (_root_.GebMirror.Metalogic.«Base.bindO»
        (_root_.GebMirror.Metalogic.«Affine.subAt»
          x0
          x2
          x3
          x4
          (_root_.GebMirror.Metalogic.«Prelude.at» x5 (_root_.Geb.Kernel.leaf 0)))
        (fun (x6 : _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.Metalogic.«Base.bindO»
            (_root_.GebMirror.Metalogic.«Affine.subAt»
              x1
              x2
              x3
              x4
              (_root_.GebMirror.Metalogic.«Prelude.at» x5 (_root_.Geb.Kernel.leaf 1)))
            (fun (x7 : _root_.Geb.Kernel.Tree) =>
              let x8 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Affine.rD» x7;
              _root_.GebMirror.Metalogic.«Affine.one»
                (_root_.GebMirror.Metalogic.«Prelude.and»
                  (_root_.Geb.Kernel.Const.equal
                    (_root_.GebMirror.Metalogic.«Affine.dTy» x8)
                    (_root_.GebMirror.Metalogic.«Check.tyList»
                      (_root_.GebMirror.Metalogic.«Affine.dTy» (_root_.GebMirror.Metalogic.«Affine.rD» x6))))
                  (_root_.GebMirror.Metalogic.«Prelude.or»
                    (_root_.GebMirror.Metalogic.«Affine.dData» x8)
                    (_root_.GebMirror.Metalogic.«Prelude.and»
                      (_root_.Geb.Kernel.Const.eq
                        (_root_.GebMirror.Metalogic.«Affine.dBang» x8)
                        (_root_.Geb.Kernel.leaf 0))
                      (_root_.Geb.Kernel.Const.equal
                        (_root_.Geb.Kernel.Const.node
                          (_root_.Geb.Kernel.leaf 0)
                          (_root_.GebMirror.Metalogic.«Affine.dKids» x8))
                        (_root_.Geb.Kernel.Const.node
                          (_root_.Geb.Kernel.leaf 0)
                          (_root_.GebMirror.Metalogic.«Prelude.single» (_root_.GebMirror.Metalogic.«Affine.rD» x6)))))))
                (_root_.GebMirror.Metalogic.«Affine.res»
                  (_root_.GebMirror.Metalogic.«Affine.dList» (_root_.GebMirror.Metalogic.«Affine.rD» x6))
                  (_root_.GebMirror.Metalogic.«Prelude.append»
                    (_root_.GebMirror.Metalogic.«Affine.rU» x6)
                    (_root_.GebMirror.Metalogic.«Affine.rU» x7))))));
    x6

def «Affine.semOne» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Affine.one»
      (_root_.GebMirror.Metalogic.«Prelude.and»
        (_root_.Geb.Kernel.Const.eq
          (_root_.GebMirror.Metalogic.«Prelude.length» x1)
          (_root_.Geb.Kernel.leaf 1))
        (_root_.GebMirror.Metalogic.«Prelude.and»
          (_root_.Geb.Kernel.Const.eq
            (_root_.GebMirror.Metalogic.«Prelude.length» x2)
            (_root_.Geb.Kernel.leaf 1))
          (_root_.GebMirror.Metalogic.«Check.isTy»
            (_root_.GebMirror.Metalogic.«Prelude.at» x1 (_root_.Geb.Kernel.leaf 0)))))
      (_root_.GebMirror.Metalogic.«Base.bindO»
        (_root_.GebMirror.Metalogic.«Affine.decorate»
          (_root_.GebMirror.Metalogic.«Prelude.at» x1 (_root_.Geb.Kernel.leaf 0))
          (_root_.GebMirror.Metalogic.«Prelude.at» x2 (_root_.Geb.Kernel.leaf 0)))
        (fun (x3 : _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.Metalogic.«Affine.res»
            (if (_root_.Geb.Kernel.Const.eq
              x0
              (_root_.Geb.Kernel.leaf 19)).label ≠ 0 then
              _root_.GebMirror.Metalogic.«Affine.dList» x3
            else
              if (_root_.Geb.Kernel.Const.eq
                x0
                (_root_.Geb.Kernel.leaf 18)).label ≠ 0 then
                _root_.GebMirror.Metalogic.«Affine.iterD» x3
              else
                _root_.GebMirror.Metalogic.«Affine.foldD» x3)
            ([] : _root_.List _root_.Geb.Kernel.Tree)));
    x3

def «Affine.semTwo» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Affine.one»
      (_root_.GebMirror.Metalogic.«Prelude.and»
        (_root_.Geb.Kernel.Const.eq
          (_root_.GebMirror.Metalogic.«Prelude.length» x1)
          (_root_.Geb.Kernel.leaf 2))
        (_root_.GebMirror.Metalogic.«Prelude.and»
          (_root_.Geb.Kernel.Const.eq
            (_root_.GebMirror.Metalogic.«Prelude.length» x2)
            (_root_.Geb.Kernel.leaf 2))
          (_root_.GebMirror.Metalogic.«Prelude.and»
            (_root_.GebMirror.Metalogic.«Check.isTy»
              (_root_.GebMirror.Metalogic.«Prelude.at» x1 (_root_.Geb.Kernel.leaf 0)))
            (_root_.GebMirror.Metalogic.«Check.isTy»
              (_root_.GebMirror.Metalogic.«Prelude.at» x1 (_root_.Geb.Kernel.leaf 1))))))
      (_root_.GebMirror.Metalogic.«Base.bindO»
        (_root_.GebMirror.Metalogic.«Affine.decorate»
          (_root_.GebMirror.Metalogic.«Prelude.at» x1 (_root_.Geb.Kernel.leaf 0))
          (_root_.GebMirror.Metalogic.«Prelude.at» x2 (_root_.Geb.Kernel.leaf 0)))
        (fun (x3 : _root_.Geb.Kernel.Tree) =>
          _root_.GebMirror.Metalogic.«Base.bindO»
            (_root_.GebMirror.Metalogic.«Affine.decorate»
              (_root_.GebMirror.Metalogic.«Prelude.at» x1 (_root_.Geb.Kernel.leaf 1))
              (_root_.GebMirror.Metalogic.«Prelude.at» x2 (_root_.Geb.Kernel.leaf 1)))
            (fun (x4 : _root_.Geb.Kernel.Tree) =>
              if (_root_.Geb.Kernel.Const.eq
                x0
                (_root_.Geb.Kernel.leaf 24)).label ≠ 0 then
                _root_.GebMirror.Metalogic.«Affine.res»
                  (_root_.GebMirror.Metalogic.«Affine.lcaseD» x3 x4)
                  ([] : _root_.List _root_.Geb.Kernel.Tree)
              else
                _root_.GebMirror.Metalogic.«Affine.one»
                  (_root_.GebMirror.Metalogic.«Prelude.or»
                    (_root_.GebMirror.Metalogic.«Affine.dData» x3)
                    (_root_.Geb.Kernel.Const.lt
                      (_root_.Geb.Kernel.leaf 0)
                      (_root_.GebMirror.Metalogic.«Affine.dBang» x3)))
                  (_root_.GebMirror.Metalogic.«Affine.res»
                    (_root_.GebMirror.Metalogic.«Affine.foldrD» x3 x4)
                    ([] : _root_.List _root_.Geb.Kernel.Tree)))));
    x3

def «Affine.semPrim» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Affine.one»
      (_root_.GebMirror.Metalogic.«Prelude.and»
        (_root_.Geb.Kernel.Const.eq
          (_root_.GebMirror.Metalogic.«Prelude.length» x0)
          (_root_.Geb.Kernel.leaf 1))
        (_root_.GebMirror.Metalogic.«Base.isEmpty» x1))
      (_root_.GebMirror.Metalogic.«Base.mapO»
        (fun (x2 : _root_.Geb.Kernel.Tree) =>
          _root_.Geb.Kernel.Const.node
            (_root_.Geb.Kernel.leaf 0)
            ((_root_.GebMirror.Metalogic.«Affine.dZero» x2) ::
              (_root_.GebMirror.Metalogic.«Prelude.single»
                (_root_.Geb.Kernel.Const.node
                  (_root_.Geb.Kernel.leaf 0)
                  ([] : _root_.List _root_.Geb.Kernel.Tree)))))
        (_root_.GebMirror.Metalogic.«Prelude.nth»
          _root_.GebMirror.Metalogic.«Check.primTypes»
          (_root_.Geb.Kernel.Const.label
            (_root_.GebMirror.Metalogic.«Prelude.at» x0 (_root_.Geb.Kernel.leaf 0)))));
    x2

def «Affine.semRef» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Affine.one»
      (_root_.GebMirror.Metalogic.«Prelude.and»
        (_root_.Geb.Kernel.Const.eq
          (_root_.GebMirror.Metalogic.«Prelude.length» x1)
          (_root_.Geb.Kernel.leaf 1))
        (_root_.Geb.Kernel.Const.eq
          (_root_.GebMirror.Metalogic.«Prelude.length» x2)
          (_root_.Geb.Kernel.leaf 2)))
      (let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.at»
         x2
         (_root_.Geb.Kernel.leaf 0);
       let x4 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Prelude.at»
         x2
         (_root_.Geb.Kernel.leaf 1);
       _root_.GebMirror.Metalogic.«Base.bindO»
         (_root_.GebMirror.Metalogic.«Prelude.nth» x0 (_root_.Geb.Kernel.Const.label x3))
         (fun (x5 : _root_.Geb.Kernel.Tree) =>
           _root_.GebMirror.Metalogic.«Affine.one»
             (_root_.GebMirror.Metalogic.«Prelude.and»
               (_root_.Geb.Kernel.Const.eq
                 (_root_.Geb.Kernel.Const.child x5 (_root_.Geb.Kernel.leaf 0))
                 (_root_.Geb.Kernel.Const.label
                   (_root_.GebMirror.Metalogic.«Prelude.at» x1 (_root_.Geb.Kernel.leaf 0))))
               (_root_.GebMirror.Metalogic.«Prelude.and»
                 (_root_.GebMirror.Metalogic.«Base.isEmpty» (_root_.Geb.Kernel.Const.children x3))
                 (_root_.GebMirror.Metalogic.«Base.isEmpty»
                   (_root_.Geb.Kernel.Const.children x4))))
             (_root_.GebMirror.Metalogic.«Affine.res»
               (_root_.GebMirror.Metalogic.«Affine.dShift»
                 (_root_.Geb.Kernel.Const.child x5 (_root_.Geb.Kernel.leaf 1))
                 (_root_.Geb.Kernel.Const.label x4))
               ([] : _root_.List _root_.Geb.Kernel.Tree))));
    x3

def «Affine.semLeaf» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.List _root_.Geb.Kernel.Tree)
    (x3 : _root_.List _root_.Geb.Kernel.Tree) =>
    let x4 : _root_.Geb.Kernel.Tree := (if (_root_.Geb.Kernel.Const.eq
      x0
      (_root_.Geb.Kernel.leaf 11)).label ≠ 0 then
      _root_.GebMirror.Metalogic.«Affine.one»
        (_root_.GebMirror.Metalogic.«Prelude.and»
          (_root_.GebMirror.Metalogic.«Base.isEmpty» x2)
          (_root_.GebMirror.Metalogic.«Base.isEmpty» x3))
        (_root_.GebMirror.Metalogic.«Affine.res»
          (_root_.GebMirror.Metalogic.«Affine.dZero» (_root_.Geb.Kernel.leaf 1))
          ([] : _root_.List _root_.Geb.Kernel.Tree))
    else
      if (_root_.Geb.Kernel.Const.eq
        x0
        (_root_.Geb.Kernel.leaf 15)).label ≠ 0 then
        _root_.GebMirror.Metalogic.«Affine.one»
          (_root_.GebMirror.Metalogic.«Prelude.and»
            (_root_.Geb.Kernel.Const.eq
              (_root_.GebMirror.Metalogic.«Prelude.length» x2)
              (_root_.Geb.Kernel.leaf 1))
            (_root_.GebMirror.Metalogic.«Base.isEmpty» x3))
          (_root_.GebMirror.Metalogic.«Affine.res»
            (_root_.GebMirror.Metalogic.«Affine.dZero» (_root_.Geb.Kernel.leaf 0))
            ([] : _root_.List _root_.Geb.Kernel.Tree))
      else
        if (_root_.Geb.Kernel.Const.eq
          x0
          (_root_.Geb.Kernel.leaf 22)).label ≠ 0 then
          _root_.GebMirror.Metalogic.«Affine.semPrim» x2 x3
        else
          if (_root_.Geb.Kernel.Const.eq
            x0
            (_root_.Geb.Kernel.leaf 23)).label ≠ 0 then
            _root_.GebMirror.Metalogic.«Affine.semRef» x1 x2 x3
          else
            if (_root_.GebMirror.Metalogic.«Prelude.or»
              (_root_.Geb.Kernel.Const.eq x0 (_root_.Geb.Kernel.leaf 21))
              (_root_.Geb.Kernel.Const.eq
                x0
                (_root_.Geb.Kernel.leaf 24))).label ≠ 0 then
              _root_.GebMirror.Metalogic.«Affine.semTwo» x0 x2 x3
            else
              if (_root_.GebMirror.Metalogic.«Prelude.or»
                (_root_.Geb.Kernel.Const.eq x0 (_root_.Geb.Kernel.leaf 19))
                (_root_.GebMirror.Metalogic.«Prelude.or»
                  (_root_.Geb.Kernel.Const.eq x0 (_root_.Geb.Kernel.leaf 18))
                  (_root_.GebMirror.Metalogic.«Prelude.or»
                    (_root_.Geb.Kernel.Const.eq x0 (_root_.Geb.Kernel.leaf 17))
                    (_root_.Geb.Kernel.Const.eq
                      x0
                      (_root_.Geb.Kernel.leaf 25))))).label ≠ 0 then
                _root_.GebMirror.Metalogic.«Affine.semOne» x0 x2 x3
              else
                _root_.GebMirror.Metalogic.«Prelude.none»);
    x4

def «Affine.semStep» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x3 : _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
    (x4 : _root_.Geb.Kernel.Tree)
    (x5 : _root_.List _root_.Geb.Kernel.Tree)
    (x6 : _root_.List _root_.Geb.Kernel.Tree)
    (x7 : _root_.Geb.Kernel.Tree) =>
    let x8 : _root_.Geb.Kernel.Tree := (let x8 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.label
                                          x0;
                                        let x9 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                          x0;
                                        let x10 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.label
                                          x7;
                                        let x11 : _root_.List
                                          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children
                                          x7;
                                        if (_root_.Geb.Kernel.Const.lt
                                          x8
                                          (_root_.Geb.Kernel.leaf 9)).label ≠ 0 then
                                          if (_root_.Geb.Kernel.Const.eq
                                            x8
                                            (_root_.Geb.Kernel.leaf 8)).label ≠ 0 then
                                            _root_.GebMirror.Metalogic.«Affine.semVar» x6 x10 x9 x11
                                          else
                                            _root_.GebMirror.Metalogic.«Prelude.none»
                                        else
                                          if (_root_.Geb.Kernel.Const.eq
                                            x8
                                            (_root_.Geb.Kernel.leaf 9)).label ≠ 0 then
                                            _root_.GebMirror.Metalogic.«Affine.semLam» x2 x5 x6 x10 x9 x11
                                          else
                                            if (_root_.Geb.Kernel.Const.eq
                                              x8
                                              (_root_.Geb.Kernel.leaf 10)).label ≠ 0 then
                                              _root_.GebMirror.Metalogic.«Affine.one»
                                                (_root_.Geb.Kernel.Const.eq
                                                  (_root_.GebMirror.Metalogic.«Prelude.length» x9)
                                                  (_root_.Geb.Kernel.leaf 2))
                                                (if (_root_.Geb.Kernel.Const.eq
                                                  x4
                                                  (_root_.Geb.Kernel.leaf 1)).label ≠ 0 then
                                                  _root_.GebMirror.Metalogic.«Affine.semSpine» x1 x2 x5 x6 x11
                                                else
                                                  if (_root_.GebMirror.Metalogic.«Affine.isSpine2»
                                                    (_root_.GebMirror.Metalogic.«Prelude.at»
                                                      x9
                                                      (_root_.Geb.Kernel.leaf 0))).label ≠ 0 then
                                                    _root_.GebMirror.Metalogic.«Affine.semSat»
                                                      (_root_.GebMirror.Metalogic.«Prelude.at»
                                                        x9
                                                        (_root_.Geb.Kernel.leaf 0))
                                                      x1
                                                      x2
                                                      x5
                                                      x6
                                                      x10
                                                      x11
                                                  else
                                                    _root_.GebMirror.Metalogic.«Affine.semApp»
                                                      x1
                                                      x2
                                                      x5
                                                      x6
                                                      x10
                                                      x11)
                                            else
                                              if (_root_.Geb.Kernel.Const.eq
                                                x8
                                                (_root_.Geb.Kernel.leaf 12)).label ≠ 0 then
                                                _root_.GebMirror.Metalogic.«Affine.one»
                                                  (_root_.Geb.Kernel.Const.eq
                                                    (_root_.GebMirror.Metalogic.«Prelude.length» x9)
                                                    (_root_.Geb.Kernel.leaf 2))
                                                  (_root_.GebMirror.Metalogic.«Affine.semPair»
                                                    x1
                                                    x2
                                                    x5
                                                    x6
                                                    x10
                                                    x11)
                                              else
                                                if (_root_.Geb.Kernel.Const.eq
                                                  x8
                                                  (_root_.Geb.Kernel.leaf 13)).label ≠ 0 then
                                                  _root_.GebMirror.Metalogic.«Affine.semProj»
                                                    (_root_.Geb.Kernel.leaf 0)
                                                    x1
                                                    x5
                                                    x6
                                                    x10
                                                    x9
                                                    x11
                                                else
                                                  if (_root_.Geb.Kernel.Const.eq
                                                    x8
                                                    (_root_.Geb.Kernel.leaf 14)).label ≠ 0 then
                                                    _root_.GebMirror.Metalogic.«Affine.semProj»
                                                      (_root_.Geb.Kernel.leaf 1)
                                                      x1
                                                      x5
                                                      x6
                                                      x10
                                                      x9
                                                      x11
                                                  else
                                                    if (_root_.Geb.Kernel.Const.eq
                                                      x8
                                                      (_root_.Geb.Kernel.leaf 16)).label ≠ 0 then
                                                      _root_.GebMirror.Metalogic.«Affine.one»
                                                        (_root_.Geb.Kernel.Const.eq
                                                          (_root_.GebMirror.Metalogic.«Prelude.length» x9)
                                                          (_root_.Geb.Kernel.leaf 3))
                                                        (_root_.GebMirror.Metalogic.«Affine.semCond»
                                                          x1
                                                          x2
                                                          x3
                                                          x5
                                                          x6
                                                          x10
                                                          x11)
                                                    else
                                                      if (_root_.Geb.Kernel.Const.eq
                                                        x8
                                                        (_root_.Geb.Kernel.leaf 20)).label ≠ 0 then
                                                        _root_.GebMirror.Metalogic.«Affine.one»
                                                          (_root_.Geb.Kernel.Const.eq
                                                            (_root_.GebMirror.Metalogic.«Prelude.length» x9)
                                                            (_root_.Geb.Kernel.leaf 2))
                                                          (_root_.GebMirror.Metalogic.«Affine.semCons»
                                                            x1
                                                            x2
                                                            x5
                                                            x6
                                                            x10
                                                            x11)
                                                      else
                                                        if (_root_.GebMirror.Metalogic.«Prelude.and»
                                                          (_root_.Geb.Kernel.Const.eq
                                                            x4
                                                            (_root_.Geb.Kernel.leaf 1))
                                                          (_root_.GebMirror.Metalogic.«Prelude.or»
                                                            (_root_.Geb.Kernel.Const.eq
                                                              x8
                                                              (_root_.Geb.Kernel.leaf 21))
                                                            (_root_.Geb.Kernel.Const.eq
                                                              x8
                                                              (_root_.Geb.Kernel.leaf 24)))).label ≠ 0 then
                                                          _root_.Geb.Kernel.Const.node
                                                            (_root_.Geb.Kernel.leaf 0)
                                                            ([] : _root_.List _root_.Geb.Kernel.Tree)
                                                        else
                                                          _root_.GebMirror.Metalogic.«Affine.semLeaf»
                                                            x8
                                                            x5
                                                            x9
                                                            x11);
    x8

def «Affine.sem0» :=
  fun (_ : _root_.Geb.Kernel.Tree)
    (_ : _root_.List _root_.Geb.Kernel.Tree)
    (_ : _root_.List _root_.Geb.Kernel.Tree)
    (_ : _root_.Geb.Kernel.Tree) =>
    _root_.GebMirror.Metalogic.«Prelude.none»

def «Affine.semThree» :=
  fun (x0 : _root_.Geb.Kernel.Tree)
    (x1 : _root_.List
      (_root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.List _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
    let x2 : _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.lcase
      (α := _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.List _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (β := _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.List _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      x1
      (_root_.GebMirror.Metalogic.«Affine.semStep»
        x0
        _root_.GebMirror.Metalogic.«Affine.sem0»
        _root_.GebMirror.Metalogic.«Affine.sem0»
        _root_.GebMirror.Metalogic.«Affine.sem0»)
      (fun (x2 : _root_.Geb.Kernel.Tree →
           _root_.List _root_.Geb.Kernel.Tree →
             _root_.List _root_.Geb.Kernel.Tree →
               _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
         (x3 : _root_.List
           (_root_.Geb.Kernel.Tree →
             _root_.List _root_.Geb.Kernel.Tree →
               _root_.List _root_.Geb.Kernel.Tree →
                 _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
        _root_.Geb.Kernel.Const.lcase
          (α := _root_.Geb.Kernel.Tree →
            _root_.List _root_.Geb.Kernel.Tree →
              _root_.List _root_.Geb.Kernel.Tree →
                _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
          (β := _root_.Geb.Kernel.Tree →
            _root_.List _root_.Geb.Kernel.Tree →
              _root_.List _root_.Geb.Kernel.Tree →
                _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
          x3
          (_root_.GebMirror.Metalogic.«Affine.semStep»
            x0
            x2
            _root_.GebMirror.Metalogic.«Affine.sem0»
            _root_.GebMirror.Metalogic.«Affine.sem0»)
          (fun (x4 : _root_.Geb.Kernel.Tree →
               _root_.List _root_.Geb.Kernel.Tree →
                 _root_.List _root_.Geb.Kernel.Tree →
                   _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
             (x5 : _root_.List
               (_root_.Geb.Kernel.Tree →
                 _root_.List _root_.Geb.Kernel.Tree →
                   _root_.List _root_.Geb.Kernel.Tree →
                     _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
            _root_.Geb.Kernel.Const.lcase
              (α := _root_.Geb.Kernel.Tree →
                _root_.List _root_.Geb.Kernel.Tree →
                  _root_.List _root_.Geb.Kernel.Tree →
                    _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
              (β := _root_.Geb.Kernel.Tree →
                _root_.List _root_.Geb.Kernel.Tree →
                  _root_.List _root_.Geb.Kernel.Tree →
                    _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
              x5
              (_root_.GebMirror.Metalogic.«Affine.semStep»
                x0
                x2
                x4
                _root_.GebMirror.Metalogic.«Affine.sem0»)
              (fun (x6 : _root_.Geb.Kernel.Tree →
                   _root_.List _root_.Geb.Kernel.Tree →
                     _root_.List _root_.Geb.Kernel.Tree →
                       _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
                 (_ : _root_.List
                   (_root_.Geb.Kernel.Tree →
                     _root_.List _root_.Geb.Kernel.Tree →
                       _root_.List _root_.Geb.Kernel.Tree →
                         _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)) =>
                _root_.GebMirror.Metalogic.«Affine.semStep» x0 x2 x4 x6)));
    x2

def «Affine.sem» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    let x1 : _root_.Geb.Kernel.Tree →
      _root_.List _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.para
      (α := _root_.Geb.Kernel.Tree →
        _root_.List _root_.Geb.Kernel.Tree →
          _root_.List _root_.Geb.Kernel.Tree →
            _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      _root_.GebMirror.Metalogic.«Affine.semThree»
      x0;
    x1

def «Affine.instanceOf» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.List _root_.Geb.Kernel.Tree)
    (x2 : _root_.Geb.Kernel.Tree) =>
    let x3 : _root_.Geb.Kernel.Tree := _root_.GebMirror.Metalogic.«Base.bindO»
      (_root_.GebMirror.Metalogic.«Prelude.nth» x0 (_root_.Geb.Kernel.Const.label x2))
      (fun (x3 : _root_.Geb.Kernel.Tree) =>
        let x4 : _root_.List
          _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.children x2;
        if (_root_.GebMirror.Metalogic.«Prelude.and»
          (_root_.Geb.Kernel.Const.eq
            (_root_.GebMirror.Metalogic.«Prelude.length» x4)
            (_root_.Geb.Kernel.leaf 1))
          (_root_.Geb.Kernel.Const.eq
            (_root_.Geb.Kernel.Const.label
              (_root_.GebMirror.Metalogic.«Prelude.at» x4 (_root_.Geb.Kernel.leaf 0)))
            (_root_.Geb.Kernel.leaf 0))).label ≠ 0 then
          _root_.GebMirror.Metalogic.«Base.mapO»
            (fun (x5 : _root_.Geb.Kernel.Tree) =>
              _root_.Geb.Kernel.Const.node
                (_root_.Geb.Kernel.leaf 0)
                (_root_.GebMirror.Metalogic.«Prelude.append»
                  x1
                  (_root_.GebMirror.Metalogic.«Prelude.single»
                    (_root_.Geb.Kernel.Const.node
                      (_root_.Geb.Kernel.leaf 0)
                      ((_root_.Geb.Kernel.Const.label x2) ::
                        (_root_.GebMirror.Metalogic.«Prelude.single»
                          (_root_.Geb.Kernel.Const.child x5 (_root_.Geb.Kernel.leaf 0))))))))
            (_root_.GebMirror.Metalogic.«Affine.sem»
              x3
              (_root_.Geb.Kernel.leaf 0)
              x1
              ([] : _root_.List _root_.Geb.Kernel.Tree)
              (_root_.GebMirror.Metalogic.«Prelude.at» x4 (_root_.Geb.Kernel.leaf 0)))
        else
          _root_.GebMirror.Metalogic.«Prelude.none»);
    x3

def «Affine.check» :=
  fun (x0 : _root_.List _root_.Geb.Kernel.Tree)
    (x1 : _root_.Geb.Kernel.Tree) =>
    let x2 : _root_.Geb.Kernel.Tree := _root_.Geb.Kernel.Const.foldr
      (α := _root_.Geb.Kernel.Tree)
      (β := _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
      (fun (x2 : _root_.Geb.Kernel.Tree)
         (x3 : _root_.List _root_.Geb.Kernel.Tree → _root_.Geb.Kernel.Tree)
         (x4 : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Base.bindO»
          (_root_.GebMirror.Metalogic.«Affine.instanceOf» x0 x4 x2)
          (fun (x5 : _root_.Geb.Kernel.Tree) =>
            x3 (_root_.Geb.Kernel.Const.children x5)))
      (fun (x2 : _root_.List _root_.Geb.Kernel.Tree) =>
        _root_.GebMirror.Metalogic.«Prelude.some»
          (_root_.Geb.Kernel.Const.node (_root_.Geb.Kernel.leaf 0) x2))
      (_root_.Geb.Kernel.Const.children x1)
      ([] : _root_.List _root_.Geb.Kernel.Tree);
    x2

end GebMirror.Metalogic

end
