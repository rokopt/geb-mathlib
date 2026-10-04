module

public import GebMirror.Metalogic.Combinator

/-! Generated from a Geb program by `bootstrap/stage1/lean.geb`. -/

@[expose] public section

open Geb.Kernel
open Geb.Kernel renaming Tree → T

namespace GebMirror.Metalogic

def «Datatype.sx1» :=
  fun (x0 : T) => Const.node (leaf 2) («Prelude.single» x0)

def «Datatype.sx2» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 2) (x0 :: («Prelude.single» x1))

def «Datatype.sx3» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    Const.node (leaf 2) (x0 :: (x1 :: («Prelude.single» x2)))

def «Datatype.sx4» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    Const.node (leaf 2) (x0 :: (x1 :: (x2 :: («Prelude.single» x3))))

def «Datatype.sx5» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    Const.node
      (leaf 2)
      (x0 :: (x1 :: (x2 :: (x3 :: («Prelude.single» x4)))))

def «Datatype.sx6» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) (x5 : T) =>
    Const.node
      (leaf 2)
      (x0 :: (x1 :: (x2 :: (x3 :: (x4 :: («Prelude.single» x5))))))

def «Datatype.aLet» := mk 1 [leaf 108, leaf 101, leaf 116]

def «Datatype.aIf» := mk 1 [leaf 105, leaf 102]

def «Datatype.aLam» := mk 1 [leaf 108, leaf 97, leaf 109]

def «Datatype.aPair» := mk 1 [leaf 112, leaf 97, leaf 105, leaf 114]

def «Datatype.aFst» := mk 1 [leaf 102, leaf 115, leaf 116]

def «Datatype.aSnd» := mk 1 [leaf 115, leaf 110, leaf 100]

def «Datatype.aCons» := mk 1 [leaf 99, leaf 111, leaf 110, leaf 115]

def «Datatype.aNil» := mk 1 [leaf 110, leaf 105, leaf 108]

def «Datatype.aIter» := mk 1 [leaf 105, leaf 116, leaf 101, leaf 114]

def «Datatype.aLcase» :=
  mk 1 [leaf 108, leaf 99, leaf 97, leaf 115, leaf 101]

def «Datatype.aFoldr» :=
  mk 1 [leaf 102, leaf 111, leaf 108, leaf 100, leaf 114]

def «Datatype.aFold» := mk 1 [leaf 102, leaf 111, leaf 108, leaf 100]

def «Datatype.aPara» := mk 1 [leaf 112, leaf 97, leaf 114, leaf 97]

def «Datatype.aDef» := mk 1 [leaf 100, leaf 101, leaf 102]

def «Datatype.aDeftype» :=
  mk 1 [leaf 100,
    leaf 101,
    leaf 102,
    leaf 116,
    leaf 121,
    leaf 112,
    leaf 101]

def «Datatype.aUnitV» := mk 1 [leaf 117, leaf 110, leaf 105, leaf 116]

def «Datatype.aLabel» :=
  mk 1 [leaf 108, leaf 97, leaf 98, leaf 101, leaf 108]

def «Datatype.aChild» :=
  mk 1 [leaf 99, leaf 104, leaf 105, leaf 108, leaf 100]

def «Datatype.aChildren» :=
  mk 1 [leaf 99,
    leaf 104,
    leaf 105,
    leaf 108,
    leaf 100,
    leaf 114,
    leaf 101,
    leaf 110]

def «Datatype.aNode» := mk 1 [leaf 110, leaf 111, leaf 100, leaf 101]

def «Datatype.aEq» := mk 1 [leaf 101, leaf 113]

def «Datatype.aT» := mk 1 [leaf 84]

def «Datatype.aUnit» := mk 1 [leaf 85, leaf 110, leaf 105, leaf 116]

def «Datatype.aProd» := mk 1 [leaf 80, leaf 114, leaf 111, leaf 100]

def «Datatype.aArrow» :=
  mk 1 [leaf 65, leaf 114, leaf 114, leaf 111, leaf 119]

def «Datatype.aList» := mk 1 [leaf 76, leaf 105, leaf 115, leaf 116]

def «Datatype.aZero» := mk 1 [leaf 48]

def «Datatype.aS» := mk 1 [leaf 37, leaf 115]

def «Datatype.aL» := mk 1 [leaf 37, leaf 108]

def «Datatype.aRs» := mk 1 [leaf 37, leaf 114, leaf 115]

def «Datatype.aO» := mk 1 [leaf 37, leaf 111]

def «Datatype.aP» := mk 1 [leaf 37, leaf 112]

def «Datatype.aA» := mk 1 [leaf 37, leaf 97]

def «Datatype.aH» := mk 1 [leaf 37, leaf 104]

def «Datatype.aTl» := mk 1 [leaf 37, leaf 116]

def «Datatype.aX» := mk 1 [leaf 37, leaf 120]

def «Datatype.aU» := mk 1 [leaf 37, leaf 117]

def «Datatype.aR» := mk 1 [leaf 37, leaf 114]

def «Datatype.aD» := mk 1 [leaf 37, leaf 100]

def «Datatype.aRest» :=
  mk 1 [leaf 37, leaf 114, leaf 101, leaf 115, leaf 116]

def «Datatype.aK» := mk 1 [leaf 37, leaf 107]

def «Datatype.kwData» := mk 0 [leaf 100, leaf 97, leaf 116, leaf 97]

def «Datatype.kwCase» := mk 0 [leaf 99, leaf 97, leaf 115, leaf 101]

def «Datatype.kwCata» := mk 0 [leaf 99, leaf 97, leaf 116, leaf 97]

def «Datatype.kwDefn» := mk 0 [leaf 100, leaf 101, leaf 102, leaf 110]

def «Datatype.kwElse» := mk 0 [leaf 101, leaf 108, leaf 115, leaf 101]

def «Datatype.kwAmp» := mk 0 [leaf 38]

def «Datatype.decimalChars» :=
  fun (x0 : T) =>
    if (Const.eq x0 (leaf 0)).label ≠ 0 then
      «Prelude.single» (leaf 48)
    else
      let x1 : T := (Const.iter
        (α := T × T)
        (fun (x1 : T × T) =>
          if (Const.eq (x1).2 (leaf 0)).label ≠ 0 then
            x1
          else
            (Const.add (x1).1 (leaf 1), Const.div (x1).2 (leaf 10)))
        (leaf 0, x0)
        (Const.add (Const.log2 x0) (leaf 1))).1;
      Const.foldr
        (α := T)
        (β := List T)
        (fun (x2 : T) (x3 : List T) => ((Const.add x2 (leaf 48)) :: x3))
        ([] : List T)
        («Prelude.digitsMsb» (leaf 10) x0 x1)

def «Datatype.numAtom» :=
  fun (x0 : T) => Const.node (leaf 1) («Datatype.decimalChars» x0)

def «Datatype.fieldAtom» :=
  fun (x0 : T) =>
    Const.node
      (leaf 1)
      ((leaf 37) :: ((leaf 102) :: («Datatype.decimalChars» x0)))

def «Datatype.sList» :=
  fun (x0 : T) => «Datatype.sx2» «Datatype.aList» x0

def «Datatype.sProd» :=
  fun (x0 : T) (x1 : T) => «Datatype.sx3» «Datatype.aProd» x0 x1

def «Datatype.sArrow» :=
  fun (x0 : T) (x1 : T) => «Datatype.sx3» «Datatype.aArrow» x0 x1

def «Datatype.sLet» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    «Datatype.sx5» «Datatype.aLet» x0 x1 x2 x3

def «Datatype.sIf» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    «Datatype.sx4» «Datatype.aIf» x0 x1 x2

def «Datatype.sLam1» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    «Datatype.sx3»
      «Datatype.aLam»
      («Datatype.sx1» («Datatype.sx2» x0 x1))
      x2

def «Datatype.sLam2» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    «Datatype.sx3»
      «Datatype.aLam»
      («Datatype.sx2» («Datatype.sx2» x0 x1) («Datatype.sx2» x2 x3))
      x4

def «Datatype.sTail» :=
  fun (x0 : T) =>
    «Datatype.sLam1»
      «Datatype.aX»
      («Datatype.sList» x0)
      («Datatype.sx6»
        «Datatype.aLcase»
        x0
        («Datatype.sList» x0)
        «Datatype.aX»
        («Datatype.sx2» «Datatype.aNil» x0)
        («Datatype.sLam2»
          «Datatype.aH»
          x0
          «Datatype.aTl»
          («Datatype.sList» x0)
          «Datatype.aTl»))

def «Datatype.sDrop» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    «Datatype.sx5»
      «Datatype.aIter»
      («Datatype.sList» x0)
      («Datatype.sTail» x0)
      x1
      («Datatype.numAtom» x2)

def «Datatype.dropLast» :=
  fun (x0 : List T) =>
    «Prelude.reverse» («Prelude.tail» («Prelude.reverse» x0))

def «Datatype.zipTs» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : T := «Prelude.length» x1;
    (Const.foldr
      (α := T)
      (β := T × List T)
      (fun (x3 : T) (x4 : T × List T) =>
        (Const.add (x4).1 (leaf 1),
          ((«Reader.node2»
            (leaf 0)
            x3
            («Prelude.at» x1 (Const.sub (Const.sub x2 (leaf 1)) (x4).1))) ::
            (x4).2)))
      (leaf 0, ([] : List T))
      x0).2

def «Datatype.allTrue» :=
  fun (x0 : List T) =>
    Const.foldr
      (α := T)
      (β := T)
      (fun (x1 : T) (x2 : T) => «Prelude.and» x1 x2)
      (leaf 1)
      x0

def «Datatype.findCtor» :=
  fun (x0 : T) (x1 : List T) =>
    Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) =>
        if («Prelude.and»
          (Const.eq (Const.label x2) (leaf 5))
          (Const.equal (Const.child x2 (leaf 0)) x0)).label ≠ 0 then
          «Prelude.some» x2
        else
          x3)
      «Prelude.none»
      x1

def «Datatype.isData» :=
  fun (x0 : T) (x1 : List T) =>
    Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) =>
        if («Prelude.and»
          (Const.eq (Const.label x2) (leaf 6))
          (Const.equal (Const.child x2 (leaf 0)) x0)).label ≠ 0 then
          leaf 1
        else
          x3)
      (leaf 0)
      x1

def «Datatype.findAlias» :=
  fun (x0 : T) (x1 : List T) =>
    Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) =>
        if («Prelude.and»
          (Const.eq (Const.label x2) (leaf 7))
          (Const.equal (Const.child x2 (leaf 0)) x0)).label ≠ 0 then
          «Prelude.some» (Const.child x2 (leaf 1))
        else
          x3)
      «Prelude.none»
      x1

def «Datatype.ctorsOf» :=
  fun (x0 : T) (x1 : List T) =>
    Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) =>
        if («Prelude.and»
          (Const.eq (Const.label x2) (leaf 5))
          (Const.equal (Const.child x2 (leaf 2)) x0)).label ≠ 0 then
          (x2 :: x3)
        else
          x3)
      ([] : List T)
      x1

def «Datatype.expandAliases» :=
  fun (x0 : List T) (x1 : T) =>
    Const.fold
      (α := T)
      (fun (x2 : T) (x3 : List T) =>
        let x4 : T := Const.node x2 x3;
        if («Reader.isAtom» x4).label ≠ 0 then
          let x5 : T := «Datatype.findAlias» («Reader.nameOf» x4) x0;
          if («Prelude.isSome» x5).label ≠ 0 then «Prelude.get» x5 else x4
        else
          x4)
      x1

def «Datatype.defaultOf» :=
  fun (x0 : T) =>
    (Const.fold
      (α := T × T)
      (fun (x1 : T) (x2 : List (T × T)) =>
        let x3 : T := Const.node x1 («Reader.rtTrees» x2);
        let x4 : List T := «Reader.rtValues» x2;
        (x3,
          if («Reader.isAtom» x3).label ≠ 0 then
            if (Const.equal («Reader.nameOf» x3) «Reader.kwUnit»).label ≠ 0 then
              «Datatype.aUnitV»
            else
              «Datatype.aZero»
          else
            let x5 : T := «Prelude.at» (Const.children x3) (leaf 0);
            if («Reader.named» x5 «Reader.kwProd»).label ≠ 0 then
              «Datatype.sx3»
                «Datatype.aPair»
                («Prelude.at» x4 (leaf 1))
                («Prelude.at» x4 (leaf 2))
            else
              if («Reader.named» x5 «Reader.kwArrow»).label ≠ 0 then
                «Datatype.sLam1»
                  «Datatype.aD»
                  («Prelude.at» (Const.children x3) (leaf 1))
                  («Prelude.at» x4 (leaf 2))
              else
                if («Reader.named» x5 «Reader.kwList»).label ≠ 0 then
                  «Datatype.sx2»
                    «Datatype.aNil»
                    («Prelude.at» (Const.children x3) (leaf 1))
                else
                  «Datatype.aZero»))
      x0).2

def «Datatype.bindWith» :=
  fun (x0 : T → T → T → T → T)
    (x1 : T → T → T → T → T)
    (x2 : T)
    (x3 : List T)
    (x4 : T) =>
    let x5 : List T := Const.children (Const.child x2 (leaf 3));
    let x6 : T := «Prelude.length» x5;
    let x7 : T := «Prelude.length» x3;
    if («Prelude.and»
      (Const.eq x7 (Const.add x6 (Const.child x2 (leaf 4))))
      («Datatype.allTrue»
        (Const.foldr
          (α := T)
          (β := List T)
          (fun (x8 : T) (x9 : List T) => ((«Reader.isAtom» x8) :: x9))
          ([] : List T)
          x3))).label ≠ 0 then
      «Prelude.some»
        (Const.foldr
          (α := T)
          (β := T × T)
          (fun (x8 : T) (x9 : T × T) =>
            let x10 : T := Const.sub (Const.sub x7 (leaf 1)) (x9).1;
            (Const.add (x9).1 (leaf 1),
              if (Const.lt x10 x6).label ≠ 0 then
                x0 x10 («Prelude.at» x5 x10) x8 (x9).2
              else
                x1 x6 (Const.child x2 (leaf 5)) x8 (x9).2))
          (leaf 0, x4)
          x3).2
    else
      «Prelude.none»

def «Datatype.clauseCtor» :=
  fun (x0 : List T) (x1 : T) =>
    if («Reader.isList» x1).label ≠ 0 then
      let x2 : T := Const.child x1 (leaf 0);
      if («Reader.isList» x2).label ≠ 0 then
        «Datatype.findCtor» («Reader.nameOf» (Const.child x2 (leaf 0))) x0
      else
        «Prelude.none»
    else
      «Prelude.none»

def «Datatype.testChain» :=
  fun (x0 : T) (x1 : List T) (x2 : T) (x3 : T → List T → T → T) =>
    let x4 : T ×
      (T ×
        T) := Const.foldr
      (α := T)
      (β := T × (T × T))
      (fun (x4 : T) (x5 : T × (T × T)) =>
        let x6 : T := Const.child x4 (leaf 0);
        let x7 : T := Const.child x4 (leaf 1);
        let x8 : T := x3
          x7
          («Prelude.tail» (Const.children (Const.child x6 (leaf 0))))
          (Const.child (Const.child x4 (leaf 2)) (leaf 1));
        if («Prelude.and» (x5).1 («Prelude.isSome» x8)).label ≠ 0 then
          (leaf 1,
            (leaf 1,
              if (((x5).2).1).label ≠ 0 then
                «Datatype.sIf»
                  («Datatype.sx3»
                    «Datatype.aEq»
                    («Datatype.sx2» «Datatype.aLabel» x0)
                    («Datatype.numAtom» (Const.child x7 (leaf 1))))
                  («Prelude.get» x8)
                  ((x5).2).2
              else
                «Prelude.get» x8))
        else
          (leaf 0, (leaf 0, leaf 0)))
      (if («Prelude.isSome» x2).label ≠ 0 then
        (leaf 1, (leaf 1, «Prelude.get» x2))
      else
        (leaf 1, (leaf 0, leaf 0)))
      x1;
    if («Prelude.and» (x4).1 ((x4).2).1).label ≠ 0 then
      «Prelude.some» ((x4).2).2
    else
      «Prelude.none»

def «Datatype.clauseChain» :=
  fun (x0 : List T)
    (x1 : T)
    (x2 : List T)
    (x3 : T)
    (x4 : T)
    (x5 : T → List T → T → T) =>
    if («Prelude.and»
      («Prelude.isSome» x3)
      («Reader.nonEmpty» x2)).label ≠ 0 then
      let x6 : List T := Const.children («Prelude.get» x3);
      let x7 : T := «Prelude.length» x2;
      let x8 : T := «Prelude.at» x2 (Const.sub x7 (leaf 1));
      let x9 : T := «Prelude.and»
        («Reader.isList» x8)
        («Prelude.and»
          (Const.eq (Const.arity x8) (leaf 2))
          («Reader.named» (Const.child x8 (leaf 0)) «Datatype.kwElse»));
      let x10 : List
        T := (if (x9).label ≠ 0 then «Datatype.dropLast» x2 else x2);
      let x11 : List
        T := (if (x9).label ≠ 0 then «Datatype.dropLast» x6 else x6);
      let x12 : T := (if (x9).label ≠ 0 then
        «Prelude.some»
          (Const.child («Prelude.at» x6 (Const.sub x7 (leaf 1))) (leaf 1))
      else
        «Prelude.none»);
      let x13 : List
        T := Const.foldr
        (α := T)
        (β := List T)
        (fun (x13 : T) (x14 : List T) =>
          ((«Datatype.clauseCtor» x0 x13) :: x14))
        ([] : List T)
        x10;
      let x14 : T := (if («Prelude.isSome» x1).label ≠ 0 then
        «Prelude.get» x1
      else
        if («Reader.nonEmpty» x13).label ≠ 0 then
          if («Prelude.isSome» («Prelude.at» x13 (leaf 0))).label ≠ 0 then
            Const.child («Prelude.get» («Prelude.at» x13 (leaf 0))) (leaf 2)
          else
            leaf 0
        else
          leaf 0);
      let x15 : T := «Datatype.allTrue»
        (Const.foldr
          (α := T)
          (β := List T)
          (fun (x15 : T) (x16 : List T) =>
            ((«Prelude.and»
              (Const.eq (Const.arity x15) (leaf 2))
              (let x17 : T := «Datatype.clauseCtor» x0 x15;
               «Prelude.and»
                 («Prelude.isSome» x17)
                 (Const.equal (Const.child («Prelude.get» x17) (leaf 2)) x14))) ::
              x16))
          ([] : List T)
          x10);
      let x16 : List
        T := Const.foldr
        (α := T)
        (β := List T)
        (fun (x16 : T) (x17 : List T) =>
          ((Const.child («Prelude.get» x16) (leaf 0)) :: x17))
        ([] : List T)
        x13;
      let x17 : T := «Prelude.or»
        x9
        («Datatype.allTrue»
          (Const.foldr
            (α := T)
            (β := List T)
            (fun (x17 : T) (x18 : List T) =>
              ((«Prelude.isSome»
                («Reader.indexOf» (Const.child x17 (leaf 0)) x16)) ::
                x18))
            ([] : List T)
            («Datatype.ctorsOf» x14 x0)));
      if («Prelude.and» x15 x17).label ≠ 0 then
        let x18 : T := «Prelude.length» x10;
        «Datatype.testChain»
          x4
          (Const.foldr
            (α := T)
            (β := T × List T)
            (fun (x19 : T) (x20 : T × List T) =>
              let x21 : T := Const.sub (Const.sub x18 (leaf 1)) (x20).1;
              (Const.add (x20).1 (leaf 1),
                ((Const.node
                  (leaf 0)
                  (x19 ::
                    ((«Prelude.get» («Prelude.at» x13 x21)) ::
                      («Prelude.single» («Prelude.at» x11 x21))))) ::
                  (x20).2)))
            (leaf 0, ([] : List T))
            x10).2
          x12
          x5
      else
        «Prelude.none»
    else
      «Prelude.none»

def «Datatype.caseField» :=
  fun (x0 : T) (_ : T) (x2 : T) (x3 : T) =>
    «Datatype.sLet»
      x2
      «Datatype.aT»
      («Datatype.sx3»
        «Datatype.aChild»
        «Datatype.aS»
        («Datatype.numAtom» x0))
      x3

def «Datatype.caseRest» :=
  fun (x0 : T) (_ : T) (x2 : T) (x3 : T) =>
    «Datatype.sLet»
      x2
      («Datatype.sList» «Datatype.aT»)
      («Datatype.sDrop»
        «Datatype.aT»
        («Datatype.sx2» «Datatype.aChildren» «Datatype.aS»)
        x0)
      x3

def «Datatype.expandCase» :=
  fun (x0 : List T) (x1 : T) (x2 : List (T × (List T → T))) =>
    let x3 : T := «Reader.rrAt» x2 (leaf 1) x0;
    let x4 : T := «Datatype.clauseChain»
      x0
      «Prelude.none»
      («Prelude.drop» (leaf 2) (Const.children x1))
      («Reader.argsOf» x2 (leaf 2) x0)
      «Datatype.aS»
      («Datatype.bindWith» «Datatype.caseField» «Datatype.caseRest»);
    if («Reader.both» x3 x4).label ≠ 0 then
      «Prelude.some»
        («Datatype.sLet»
          «Datatype.aS»
          «Datatype.aT»
          («Prelude.get» x3)
          («Prelude.get» x4))
    else
      «Prelude.none»

def «Datatype.thTy» :=
  fun (x0 : T) => «Datatype.sArrow» «Datatype.aUnit» x0

def «Datatype.splitTy» :=
  fun (x0 : T) =>
    «Datatype.sProd»
      («Datatype.thTy» x0)
      («Datatype.sList» («Datatype.thTy» x0))

def «Datatype.qAtom» :=
  fun (x0 : T) =>
    Const.node
      (leaf 1)
      ((leaf 37) :: ((leaf 113) :: («Datatype.decimalChars» x0)))

def «Datatype.resultsAt» :=
  fun (x0 : T) =>
    if (Const.eq x0 (leaf 0)).label ≠ 0 then
      «Datatype.aK»
    else
      «Datatype.sx2»
        «Datatype.aSnd»
        («Datatype.qAtom» (Const.sub x0 (leaf 1)))

def «Datatype.cataField» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) (x5 : T) (x6 : T) =>
    «Datatype.sLet»
      («Datatype.qAtom» x3)
      («Datatype.splitTy» x1)
      («Datatype.sx6»
        «Datatype.aLcase»
        («Datatype.thTy» x1)
        («Datatype.splitTy» x1)
        («Datatype.resultsAt» x3)
        («Datatype.sx3»
          «Datatype.aPair»
          («Datatype.sLam1» «Datatype.aU» «Datatype.aUnit» x2)
          («Datatype.sx2» «Datatype.aNil» («Datatype.thTy» x1)))
        («Datatype.sLam2»
          «Datatype.aH»
          («Datatype.thTy» x1)
          «Datatype.aTl»
          («Datatype.sList» («Datatype.thTy» x1))
          («Datatype.sx3» «Datatype.aPair» «Datatype.aH» «Datatype.aTl»)))
      (if («Reader.named» x4 x0).label ≠ 0 then
        «Datatype.sLet»
          x5
          x1
          («Datatype.sx2»
            («Datatype.sx2» «Datatype.aFst» («Datatype.qAtom» x3))
            «Datatype.aUnitV»)
          x6
      else
        «Datatype.sLet»
          x5
          «Datatype.aT»
          («Datatype.sx3»
            «Datatype.aChild»
            «Datatype.aO»
            («Datatype.numAtom» x3))
          x6)

def «Datatype.cataRest» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) (x5 : T) =>
    if («Reader.named» x3 x0).label ≠ 0 then
      «Datatype.sLet»
        x4
        («Datatype.sList» x1)
        («Datatype.sx6»
          «Datatype.aFoldr»
          («Datatype.thTy» x1)
          («Datatype.sList» x1)
          («Datatype.sLam2»
            «Datatype.aH»
            («Datatype.thTy» x1)
            «Datatype.aA»
            («Datatype.sList» x1)
            («Datatype.sx3»
              «Datatype.aCons»
              («Datatype.sx2» «Datatype.aH» «Datatype.aUnitV»)
              «Datatype.aA»))
          («Datatype.sx2» «Datatype.aNil» x1)
          («Datatype.resultsAt» x2))
        x5
    else
      «Datatype.sLet»
        x4
        («Datatype.sList» «Datatype.aT»)
        («Datatype.sDrop»
          «Datatype.aT»
          («Datatype.sx2» «Datatype.aChildren» «Datatype.aO»)
          x2)
        x5

def «Datatype.expandCata» :=
  fun (x0 : List T) (x1 : T) (x2 : List (T × (List T → T))) =>
    let x3 : List T := Const.children x1;
    let x4 : T := «Reader.nameOf» («Prelude.at» x3 (leaf 1));
    let x5 : T := «Prelude.at» x3 (leaf 2);
    let x6 : T := «Datatype.defaultOf» («Datatype.expandAliases» x0 x5);
    let x7 : T := «Reader.rrAt» x2 (leaf 3) x0;
    let x8 : T := (if («Prelude.and»
      («Reader.isAtom» («Prelude.at» x3 (leaf 1)))
      («Datatype.isData» x4 x0)).label ≠ 0 then
      «Datatype.clauseChain»
        x0
        («Prelude.some» x4)
        («Prelude.drop» (leaf 4) x3)
        («Reader.argsOf» x2 (leaf 4) x0)
        «Datatype.aO»
        («Datatype.bindWith»
          («Datatype.cataField» x4 x5 x6)
          («Datatype.cataRest» x4 x5))
    else
      «Prelude.none»);
    if («Reader.both» x7 x8).label ≠ 0 then
      «Prelude.some»
        («Datatype.sx2»
          («Datatype.sx4»
            «Datatype.aPara»
            («Datatype.thTy» x5)
            («Datatype.sLam2»
              «Datatype.aO»
              «Datatype.aT»
              «Datatype.aK»
              («Datatype.sList» («Datatype.thTy» x5))
              («Datatype.sLam1» «Datatype.aU» «Datatype.aUnit» («Prelude.get» x8)))
            («Prelude.get» x7))
          «Datatype.aUnitV»)
    else
      «Prelude.none»

def «Datatype.expandExpr» :=
  fun (x0 : List T) (x1 : T) =>
    (Const.fold
      (α := T × (List T → T))
      (fun (x2 : T) (x3 : List (T × (List T → T))) =>
        let x4 : T := Const.node x2 («Reader.rrTrees» x3);
        (x4,
          fun (x5 : List T) =>
            if («Reader.isList» x4).label ≠ 0 then
              let x6 : T := «Prelude.at» (Const.children x4) (leaf 0);
              let x7 : T := Const.arity x4;
              if («Prelude.and»
                («Reader.named» x6 «Datatype.kwCase»)
                (Const.lt (leaf 2) x7)).label ≠ 0 then
                «Datatype.expandCase» x5 x4 x3
              else
                if («Prelude.and»
                  («Reader.named» x6 «Datatype.kwCata»)
                  (Const.lt (leaf 4) x7)).label ≠ 0 then
                  «Datatype.expandCata» x5 x4 x3
                else
                  let x8 : T := «Reader.allSome» («Reader.rrApply» x3 x5);
                  if («Prelude.isSome» x8).label ≠ 0 then
                    «Prelude.some»
                      (Const.node (leaf 2) (Const.children («Prelude.get» x8)))
                  else
                    «Prelude.none»
            else
              «Prelude.some» x4))
      x1).2
      x0

def «Datatype.ctorDecl» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : List T := Const.children x2;
    let x4 : List T := «Prelude.tail» x3;
    let x5 : T := «Prelude.length» x4;
    let x6 : T := «Prelude.and»
      (Const.lt (leaf 1) x5)
      («Reader.named»
        («Prelude.at» x4 (Const.sub x5 (leaf 2)))
        «Datatype.kwAmp»);
    let x7 : List
      T := (if (x6).label ≠ 0 then
      «Datatype.dropLast» («Datatype.dropLast» x4)
    else
      x4);
    let x8 : T := «Prelude.length» x7;
    let x9 : List
      T := (Const.foldr
      (α := T)
      (β := T × List T)
      (fun (_ : T) (x10 : T × List T) =>
        (Const.add (x10).1 (leaf 1),
          ((«Datatype.sx2»
            («Datatype.fieldAtom» (Const.sub (Const.sub x8 (leaf 1)) (x10).1))
            «Datatype.aT») ::
            (x10).2)))
      (leaf 0, ([] : List T))
      x7).2;
    let x10 : T := (if (x6).label ≠ 0 then
      «Datatype.aRest»
    else
      «Datatype.sx2» «Datatype.aNil» «Datatype.aT»);
    let x11 : T := (Const.foldr
      (α := T)
      (β := T × T)
      (fun (_ : T) (x12 : T × T) =>
        (Const.add (x12).1 (leaf 1),
          «Datatype.sx3»
            «Datatype.aCons»
            («Datatype.fieldAtom» (Const.sub (Const.sub x8 (leaf 1)) (x12).1))
            (x12).2))
      (leaf 0, x10)
      x7).2;
    let x12 : List
      T := (if (x6).label ≠ 0 then
      «Prelude.append»
        x9
        («Prelude.single»
          («Datatype.sx2» «Datatype.aRest» («Datatype.sList» «Datatype.aT»)))
    else
      x9);
    let x13 : T := «Datatype.sx3»
      «Datatype.aNode»
      («Datatype.numAtom» x1)
      x11;
    if («Prelude.and»
      («Reader.isList» x2)
      («Reader.isAtom» («Prelude.at» x3 (leaf 0)))).label ≠ 0 then
      «Prelude.some»
        («Reader.node2»
          (leaf 0)
          (Const.node
            (leaf 5)
            ((«Reader.nameOf» («Prelude.at» x3 (leaf 0))) ::
              (x1 ::
                (x0 ::
                  ((Const.node (leaf 0) x7) ::
                    (x6 ::
                      («Prelude.single»
                        (if (x6).label ≠ 0 then
                          «Prelude.at» x4 (Const.sub x5 (leaf 1))
                        else
                          leaf 0))))))))
          («Datatype.sx3»
            «Datatype.aDef»
            («Prelude.at» x3 (leaf 0))
            (if («Reader.nonEmpty» x12).label ≠ 0 then
              «Datatype.sx3» «Datatype.aLam» (Const.node (leaf 2) x12) x13
            else
              x13)))
    else
      «Prelude.none»

def «Datatype.dataDecl» :=
  fun (x0 : T) =>
    let x1 : List T := Const.children x0;
    let x2 : T := «Reader.nameOf» («Prelude.at» x1 (leaf 1));
    let x3 : List T := «Prelude.drop» (leaf 2) x1;
    let x4 : T := «Prelude.length» x3;
    let x5 : T := «Reader.allSome»
      (Const.foldr
        (α := T)
        (β := T × List T)
        (fun (x5 : T) (x6 : T × List T) =>
          (Const.add (x6).1 (leaf 1),
            ((«Datatype.ctorDecl»
              x2
              (Const.sub (Const.sub x4 (leaf 1)) (x6).1)
              x5) ::
              (x6).2)))
        (leaf 0, ([] : List T))
        x3).2;
    if («Prelude.and»
      («Reader.isAtom» («Prelude.at» x1 (leaf 1)))
      («Prelude.isSome» x5)).label ≠ 0 then
      let x6 : List T := Const.children («Prelude.get» x5);
      «Prelude.some»
        («Reader.node2»
          (leaf 0)
          (Const.node
            (leaf 0)
            ((Const.node (leaf 6) («Prelude.single» x2)) ::
              (Const.foldr
                (α := T)
                (β := List T)
                (fun (x7 : T) (x8 : List T) => ((Const.child x7 (leaf 0)) :: x8))
                ([] : List T)
                x6)))
          (Const.node
            (leaf 0)
            ((«Datatype.sx3»
              «Datatype.aDeftype»
              («Prelude.at» x1 (leaf 1))
              «Datatype.aT») ::
              (Const.foldr
                (α := T)
                (β := List T)
                (fun (x7 : T) (x8 : List T) => ((Const.child x7 (leaf 1)) :: x8))
                ([] : List T)
                x6))))
    else
      «Prelude.none»

def «Datatype.xpFail» := (leaf 0, (([] : List T), ([] : List T)))

def «Datatype.xpStep» :=
  fun (x0 : T × (List T × List T)) (x1 : T) =>
    if («Prelude.and» (x0).1 («Reader.isList» x1)).label ≠ 0 then
      let x2 : List T := ((x0).2).1;
      let x3 : List T := ((x0).2).2;
      let x4 : List T := Const.children x1;
      let x5 : T := «Prelude.at» x4 (leaf 0);
      let x6 : T := Const.arity x1;
      if («Reader.named» x5 «Datatype.kwData»).label ≠ 0 then
        let x7 : T := «Datatype.dataDecl» x1;
        if («Prelude.isSome» x7).label ≠ 0 then
          (leaf 1,
            («Prelude.append»
              x2
              (Const.children (Const.child («Prelude.get» x7) (leaf 0))),
              «Prelude.append»
                («Prelude.reverse»
                  (Const.children (Const.child («Prelude.get» x7) (leaf 1))))
                x3))
        else
          «Datatype.xpFail»
      else
        if («Prelude.and»
          («Reader.named» x5 «Datatype.kwDefn»)
          (Const.eq x6 (leaf 5))).label ≠ 0 then
          let x7 : T := «Datatype.expandExpr» x2 («Prelude.at» x4 (leaf 4));
          if («Prelude.isSome» x7).label ≠ 0 then
            let x8 : T := «Datatype.sLet»
              «Datatype.aR»
              («Prelude.at» x4 (leaf 3))
              («Prelude.get» x7)
              «Datatype.aR»;
            (leaf 1,
              (x2,
                ((«Datatype.sx3»
                  «Datatype.aDef»
                  («Prelude.at» x4 (leaf 1))
                  (if (Const.eq
                    (Const.arity («Prelude.at» x4 (leaf 2)))
                    (leaf 0)).label ≠ 0 then
                    x8
                  else
                    «Datatype.sx3» «Datatype.aLam» («Prelude.at» x4 (leaf 2)) x8)) ::
                  x3)))
          else
            «Datatype.xpFail»
        else
          if («Prelude.and»
            («Reader.named» x5 «Reader.kwDef»)
            (Const.eq x6 (leaf 3))).label ≠ 0 then
            let x7 : T := «Datatype.expandExpr» x2 («Prelude.at» x4 (leaf 2));
            if («Prelude.isSome» x7).label ≠ 0 then
              (leaf 1,
                (x2,
                  ((«Datatype.sx3»
                    «Datatype.aDef»
                    («Prelude.at» x4 (leaf 1))
                    («Prelude.get» x7)) ::
                    x3)))
            else
              «Datatype.xpFail»
          else
            if («Prelude.and»
              («Reader.named» x5 «Reader.kwDeftype»)
              (Const.eq x6 (leaf 3))).label ≠ 0 then
              (leaf 1,
                («Prelude.append»
                  x2
                  («Prelude.single»
                    («Reader.node2»
                      (leaf 7)
                      («Reader.nameOf» («Prelude.at» x4 (leaf 1)))
                      («Datatype.expandAliases» x2 («Prelude.at» x4 (leaf 2))))),
                  (x1 :: x3)))
            else
              if («Prelude.and»
                («Reader.named» x5 «Reader.kwDefnum»)
                (Const.eq x6 (leaf 3))).label ≠ 0 then
                (leaf 1, (x2, (x1 :: x3)))
              else
                «Datatype.xpFail»
    else
      «Datatype.xpFail»

def «Datatype.expandProgram» :=
  fun (x0 : List T) =>
    let x1 : T ×
      (List T ×
        List
          T) := Const.foldr
      (α := T)
      (β := (T × (List T × List T)) → T × (List T × List T))
      (fun (x1 : T)
         (x2 : (T × (List T × List T)) → T × (List T × List T))
         (x3 : T × (List T × List T)) =>
        x2 («Datatype.xpStep» x3 x1))
      (fun (x1 : T × (List T × List T)) => x1)
      x0
      (leaf 1, (([] : List T), ([] : List T)));
    if ((x1).1).label ≠ 0 then
      «Prelude.some» (Const.node (leaf 0) («Prelude.reverse» ((x1).2).2))
    else
      «Prelude.none»

def «Printer.atomOf» :=
  fun (x0 : T) => Const.node (leaf 1) (Const.children x0)

def «Printer.listOf» := fun (x0 : List T) => Const.node (leaf 2) x0

def «Printer.numAtom» :=
  fun (x0 : T) => Const.node (leaf 1) («Datatype.decimalChars» x0)

def «Printer.binderAtom» :=
  fun (x0 : T) =>
    Const.node (leaf 1) ((leaf 95) :: («Datatype.decimalChars» x0))

def «Printer.nameAt» :=
  fun (x0 : List T) (x1 : T) => «Printer.atomOf» («Prelude.at» x0 x1)

def «Printer.printType» :=
  fun (x0 : T) =>
    Const.fold
      (α := T)
      (fun (x1 : T) (x2 : List T) =>
        if (Const.eq x1 (leaf 0)).label ≠ 0 then
          «Printer.atomOf» «Reader.kwT»
        else
          if (Const.eq x1 (leaf 1)).label ≠ 0 then
            «Printer.atomOf» «Reader.kwUnit»
          else
            if (Const.eq x1 (leaf 2)).label ≠ 0 then
              «Printer.listOf» ((«Printer.atomOf» «Reader.kwProd») :: x2)
            else
              if (Const.eq x1 (leaf 3)).label ≠ 0 then
                «Printer.listOf» ((«Printer.atomOf» «Reader.kwArrow») :: x2)
              else
                «Printer.listOf» ((«Printer.atomOf» «Reader.kwList») :: x2))
      x0

def «Printer.printTypes» :=
  fun (x0 : List T) =>
    Const.foldr
      (α := T)
      (β := List T)
      (fun (x1 : T) (x2 : List T) => ((«Printer.printType» x1) :: x2))
      ([] : List T)
      x0

def «Printer.printDatum» :=
  fun (x0 : T) =>
    Const.fold
      (α := T)
      (fun (x1 : T) (x2 : List T) =>
        if («Reader.nonEmpty» x2).label ≠ 0 then
          «Printer.listOf» ((«Printer.numAtom» x1) :: x2)
        else
          «Printer.numAtom» x1)
      x0

def «Printer.prTrees» :=
  fun (x0 : List (T × (T → T))) =>
    Const.foldr
      (α := T × (T → T))
      (β := List T)
      (fun (x1 : T × (T → T)) (x2 : List T) => ((x1).1 :: x2))
      ([] : List T)
      x0

def «Printer.prAt» :=
  fun (x0 : List (T × (T → T))) (x1 : T) =>
    Const.foldr
      (α := T × (T → T))
      (β := List T)
      (fun (x2 : T × (T → T)) (x3 : List T) => (((x2).2 x1) :: x3))
      ([] : List T)
      x0

def «Printer.kwList1» :=
  fun (x0 : T) (x1 : List T) =>
    «Printer.listOf» ((«Printer.atomOf» x0) :: x1)

def «Printer.printStep» :=
  fun (x0 : List T) (x1 : T) (x2 : List (T × (T → T))) (x3 : T) =>
    let x4 : List T := «Printer.prTrees» x2;
    let x5 : List T := «Printer.prAt» x2 x3;
    let x6 : T := Const.label («Prelude.at» x4 (leaf 0));
    if (Const.eq x1 (leaf 8)).label ≠ 0 then
      «Printer.binderAtom» (Const.sub (Const.sub x3 (leaf 1)) x6)
    else
      if (Const.eq x1 (leaf 9)).label ≠ 0 then
        «Printer.kwList1»
          «Reader.kwLam»
          ((«Printer.listOf»
            ((«Printer.binderAtom» x3) ::
              («Prelude.single»
                («Printer.printType» («Prelude.at» x4 (leaf 0)))))) ::
            («Prelude.single»
              («Prelude.at» («Printer.prAt» x2 (Const.add x3 (leaf 1))) (leaf 1))))
      else
        if (Const.eq x1 (leaf 10)).label ≠ 0 then
          «Printer.listOf» x5
        else
          if (Const.eq x1 (leaf 11)).label ≠ 0 then
            «Printer.atomOf» «Reader.kwUnitValue»
          else
            if (Const.eq x1 (leaf 12)).label ≠ 0 then
              «Printer.kwList1» «Reader.kwPair» x5
            else
              if (Const.eq x1 (leaf 13)).label ≠ 0 then
                «Printer.kwList1» «Reader.kwFst» x5
              else
                if (Const.eq x1 (leaf 14)).label ≠ 0 then
                  «Printer.kwList1» «Reader.kwSnd» x5
                else
                  if (Const.eq x1 (leaf 16)).label ≠ 0 then
                    «Printer.kwList1» «Reader.kwIf» x5
                  else
                    if (Const.eq x1 (leaf 20)).label ≠ 0 then
                      «Printer.kwList1» «Reader.kwCons» x5
                    else
                      if (Const.eq x1 (leaf 15)).label ≠ 0 then
                        let x7 : T := «Prelude.at» x4 (leaf 0);
                        if («Reader.nonEmpty» (Const.children x7)).label ≠ 0 then
                          «Printer.kwList1»
                            «Reader.kwQuote»
                            («Prelude.single» («Printer.printDatum» x7))
                        else
                          «Printer.numAtom» (Const.label x7)
                      else
                        if (Const.eq x1 (leaf 19)).label ≠ 0 then
                          «Printer.kwList1» «Reader.kwNil» («Printer.printTypes» x4)
                        else
                          if (Const.eq x1 (leaf 17)).label ≠ 0 then
                            «Printer.kwList1» «Reader.kwFold» («Printer.printTypes» x4)
                          else
                            if (Const.eq x1 (leaf 25)).label ≠ 0 then
                              «Printer.kwList1» «Reader.kwPara» («Printer.printTypes» x4)
                            else
                              if (Const.eq x1 (leaf 18)).label ≠ 0 then
                                «Printer.kwList1» «Reader.kwIter» («Printer.printTypes» x4)
                              else
                                if (Const.eq x1 (leaf 21)).label ≠ 0 then
                                  «Printer.kwList1» «Reader.kwFoldr» («Printer.printTypes» x4)
                                else
                                  if (Const.eq x1 (leaf 24)).label ≠ 0 then
                                    «Printer.kwList1» «Reader.kwLcase» («Printer.printTypes» x4)
                                  else
                                    if (Const.eq x1 (leaf 22)).label ≠ 0 then
                                      «Printer.nameAt» «Reader.primNames» x6
                                    else
                                      «Printer.nameAt» x0 x6

def «Printer.printTerm» :=
  fun (x0 : List T) (x1 : T) (x2 : T) =>
    let x3 : T := (Const.fold
      (α := T × (T → T))
      (fun (x3 : T) (x4 : List (T × (T → T))) =>
        (Const.node x3 («Printer.prTrees» x4),
          fun (x5 : T) => «Printer.printStep» x0 x3 x4 x5))
      x1).2
      x2;
    x3

def «Printer.readBack» :=
  fun (x0 : List T) (x1 : T) (x2 : List T) =>
    let x3 : T := «Reader.resolve» ([] : List T) x0 x1 x2; x3

def «Printer.printProgram» :=
  fun (x0 : T) =>
    let x1 : List T := Const.children (Const.child x0 (leaf 1));
    Const.node
      (leaf 0)
      (Const.foldr
        (α := T)
        (β := List T → List T)
        (fun (x2 : T) (x3 : List T → List T) (x4 : List T) =>
          let x5 : T := «Prelude.at» x1 («Prelude.length» x4);
          ((«Printer.kwList1»
            «Reader.kwDef»
            ((«Printer.atomOf» x5) ::
              («Prelude.single» («Printer.printTerm» x4 x2 (leaf 0))))) ::
            (x3 («Prelude.append» x4 («Prelude.single» x5)))))
        (fun (_ : List T) => ([] : List T))
        (Const.children (Const.child x0 (leaf 0)))
        ([] : List T))

end GebMirror.Metalogic

end
