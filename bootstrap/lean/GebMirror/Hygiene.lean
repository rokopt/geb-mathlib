module

public import Geb.Prototypes.Kernel.Reader

/-! Generated from a Geb program by `bootstrap/stage1/lean.geb`. -/

@[expose] public section

open Geb.Kernel
open Geb.Kernel renaming Tree → T

namespace GebMirror.Hygiene

def «leaf» := _root_.Geb.Kernel.leaf 1

def «mk» := _root_.Geb.Kernel.leaf 2

def «Const» := _root_.Geb.Kernel.leaf 3

def «x0» := _root_.Geb.Kernel.leaf 4

def «$61c2bb62» := _root_.Geb.Kernel.leaf 5

def «$243631633262623632» := _root_.Geb.Kernel.leaf 6

def «$6c696e650a627265616b» := _root_.Geb.Kernel.leaf 7

def «$5f726f6f745f» := _root_.Geb.Kernel.leaf 8

def «$5f» := _root_.Geb.Kernel.leaf 9

def «Prefix._root_.GebBoot.name» := _root_.Geb.Kernel.leaf 10

def «main» :=
  fun (x0 : _root_.Geb.Kernel.Tree) =>
    _root_.Geb.Kernel.Const.node
      x0
      (_root_.GebMirror.Hygiene.«leaf» ::
        (_root_.GebMirror.Hygiene.«mk» ::
          (_root_.GebMirror.Hygiene.«Const» ::
            (_root_.GebMirror.Hygiene.«x0» ::
              (_root_.GebMirror.Hygiene.«$61c2bb62» ::
                (_root_.GebMirror.Hygiene.«$243631633262623632» ::
                  (_root_.GebMirror.Hygiene.«$6c696e650a627265616b» ::
                    (_root_.GebMirror.Hygiene.«$5f726f6f745f» ::
                      (_root_.GebMirror.Hygiene.«$5f» ::
                        (_root_.GebMirror.Hygiene.«Prefix._root_.GebBoot.name» ::
                          ([] : _root_.List _root_.Geb.Kernel.Tree)))))))))))

end GebMirror.Hygiene

end
