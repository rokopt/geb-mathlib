module

public import Geb.Prototypes.Kernel.Reader

/-! Generated from a Geb program by `bootstrap/stage1/lean.geb`. -/

@[expose] public section

open Geb.Kernel
open Geb.Kernel renaming Tree → T

namespace GebBoot

def «append» :=
  fun (x0 : List T) (x1 : List T) =>
    Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0

def «length» :=
  fun (x0 : List T) =>
    Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0

def «reverse» :=
  fun (x0 : List T) =>
    Const.foldr
      (α := T)
      (β := List T → List T)
      (fun (x1 : T) (x2 : List T → List T) (x3 : List T) => x2 (x1 :: x3))
      (fun (x1 : List T) => x1)
      x0
      ([] : List T)

def «replicate» :=
  fun (x0 : T) (x1 : T) =>
    Const.iter
      (α := List T)
      (fun (x2 : List T) => (x1 :: x2))
      ([] : List T)
      x0

def «single» := fun (x0 : T) => (x0 :: ([] : List T))

def «digitsMsb» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    (Const.iter
      (α := T × List T)
      (fun (x3 : T × List T) =>
        (Const.div (x3).1 x0, ((Const.mod (x3).1 x0) :: (x3).2)))
      (x1, ([] : List T))
      x2).2

def «digitsLsb» :=
  fun (x0 : T) (x1 : T) (x2 : T) => «reverse» («digitsMsb» x0 x1 x2)

def «deltaBits» :=
  fun (x0 : T) =>
    let x1 : T := Const.add x0 (leaf 1);
    let x2 : T := Const.add (Const.log2 x1) (leaf 1);
    let x3 : T := Const.log2 x2;
    «append»
      («replicate» x3 (leaf 0))
      ((leaf 1) ::
        («append»
          («digitsMsb» (leaf 2) x2 x3)
          («digitsMsb» (leaf 2) x1 (Const.sub x2 (leaf 1)))))

def «nodeBits» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := Const.add x1 (leaf 1);
    «append»
      («replicate» x0 (leaf 1))
      ((leaf 0) ::
        («append»
          («deltaBits» (Const.log2 x2))
          («digitsLsb» (leaf 2) x2 (Const.log2 x2))))

def «treeBits» :=
  fun (x0 : T) =>
    Const.fold
      (α := List T → List T)
      (fun (x1 : T) (x2 : List (List T → List T)) (x3 : List T) =>
        «append»
          («nodeBits»
            (Const.foldr
              (α := List T → List T)
              (β := T)
              (fun (_ : List T → List T) (x5 : T) => Const.add x5 (leaf 1))
              (leaf 0)
              x2)
            x1)
          (Const.foldr
            (α := List T → List T)
            (β := List T)
            (fun (x4 : List T → List T) (x5 : List T) => x4 x5)
            x3
            x2))
      x0
      ([] : List T)

def «packBits» :=
  fun (x0 : List T) =>
    let x1 : T ×
      (T ×
        List
          T) := Const.foldr
      (α := T)
      (β := (T × (T × List T)) → T × (T × List T))
      (fun (x1 : T)
         (x2 : (T × (T × List T)) → T × (T × List T))
         (x3 : T × (T × List T)) =>
        let x4 : T := Const.add (x3).1 (Const.mul x1 ((x3).2).1);
        x2
          (if (Const.eq ((x3).2).1 (leaf 128)).label ≠ 0 then
            (leaf 0, (leaf 1, (x4 :: ((x3).2).2)))
          else
            (x4, (Const.mul (leaf 2) ((x3).2).1, ((x3).2).2))))
      (fun (x1 : T × (T × List T)) => x1)
      x0
      (leaf 0, (leaf 1, ([] : List T)));
    «reverse»
      (if (Const.eq ((x1).2).1 (leaf 1)).label ≠ 0 then
        ((x1).2).2
      else
        ((x1).1 :: ((x1).2).2))

def «image» :=
  fun (x0 : T) =>
    let x1 : List T := «treeBits» x0;
    Const.node
      (leaf 0)
      («append»
        ((leaf 71) ::
          ((leaf 69) ::
            ((leaf 66) :: ((leaf 75) :: ((leaf 1) :: ([] : List T))))))
        («append»
          («digitsLsb» (leaf 256) («length» x1) (leaf 8))
          («packBits» x1)))

def «some» := fun (x0 : T) => Const.node (leaf 1) («single» x0)

def «none» := leaf 0

def «isSome» := fun (x0 : T) => Const.eq (Const.label x0) (leaf 1)

def «get» := fun (x0 : T) => Const.child x0 (leaf 0)

def «both» :=
  fun (x0 : T) (x1 : T) =>
    if («isSome» x0).label ≠ 0 then «isSome» x1 else leaf 0

def «at» :=
  fun (x0 : List T) (x1 : T) => Const.child (Const.node (leaf 0) x0) x1

def «nonEmpty» :=
  fun (x0 : List T) =>
    Const.lcase
      (α := T)
      (β := T)
      x0
      (leaf 0)
      (fun (_ : T) (_ : List T) => leaf 1)

def «tail» :=
  fun (x0 : List T) =>
    Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2)

def «drop» :=
  fun (x0 : T) (x1 : List T) => Const.iter (α := List T) «tail» x1 x0

def «allSome» :=
  fun (x0 : List T) =>
    let x1 : T ×
      List
        T := Const.foldr
      (α := T)
      (β := T × List T)
      (fun (x1 : T) (x2 : T × List T) =>
        («both» x1 (x2).1, ((«get» x1) :: (x2).2)))
      (leaf 1, ([] : List T))
      x0;
    if ((x1).1).label ≠ 0 then
      «some» (Const.node (leaf 0) (x1).2)
    else
      «none»

def «flush» :=
  fun (x0 : List T × (List T × T)) =>
    if («nonEmpty» ((x0).2).1).label ≠ 0 then
      (((Const.node (leaf 3) («reverse» ((x0).2).1)) :: (x0).1),
        (([] : List T), ((x0).2).2))
    else
      x0

def «isSpace» :=
  fun (x0 : T) =>
    if (Const.eq x0 (leaf 32)).label ≠ 0 then
      leaf 1
    else
      if (Const.eq x0 (leaf 9)).label ≠ 0 then
        leaf 1
      else
        if (Const.eq x0 (leaf 13)).label ≠ 0 then
          leaf 1
        else
          Const.eq x0 (leaf 10)

def «tokStep» :=
  fun (x0 : List T × (List T × T)) (x1 : T) =>
    if (((x0).2).2).label ≠ 0 then
      ((x0).1,
        (((x0).2).1,
          if (Const.eq x1 (leaf 10)).label ≠ 0 then leaf 0 else leaf 1))
    else
      if (Const.eq x1 (leaf 59)).label ≠ 0 then
        let x2 : List T × (List T × T) := «flush» x0;
        ((x2).1, (((x2).2).1, leaf 1))
      else
        if (Const.eq x1 (leaf 40)).label ≠ 0 then
          let x2 : List T × (List T × T) := «flush» x0;
          (((leaf 1) :: (x2).1), (x2).2)
        else
          if (Const.eq x1 (leaf 41)).label ≠ 0 then
            let x2 : List T × (List T × T) := «flush» x0;
            (((leaf 2) :: (x2).1), (x2).2)
          else
            if («isSpace» x1).label ≠ 0 then
              «flush» x0
            else
              ((x0).1, ((x1 :: ((x0).2).1), leaf 0))

def «tokenize» :=
  fun (x0 : List T) =>
    «reverse»
      («flush»
        (Const.foldr
          (α := T)
          (β := (List T × (List T × T)) → List T × (List T × T))
          (fun (x1 : T)
             (x2 : (List T × (List T × T)) → List T × (List T × T))
             (x3 : List T × (List T × T)) =>
            x2 («tokStep» x3 x1))
          (fun (x1 : List T × (List T × T)) => x1)
          x0
          (([] : List T), (([] : List T), leaf 0)))).1

def «fail» := (leaf 0, ([] : List (List T)))

def «parseStep» :=
  fun (x0 : T × List (List T)) (x1 : T) =>
    if ((x0).1).label ≠ 0 then
      Const.lcase
        (α := List T)
        (β := T × List (List T))
        (x0).2
        «fail»
        (fun (x2 : List T) (x3 : List (List T)) =>
          if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
            (leaf 1, (([] : List T) :: (x2 :: x3)))
          else
            if (Const.eq (Const.label x1) (leaf 3)).label ≠ 0 then
              (leaf 1, (((Const.node (leaf 1) (Const.children x1)) :: x2) :: x3))
            else
              Const.lcase
                (α := List T)
                (β := T × List (List T))
                x3
                «fail»
                (fun (x4 : List T) (x5 : List (List T)) =>
                  (leaf 1, (((Const.node (leaf 2) («reverse» x2)) :: x4) :: x5))))
    else
      x0

def «readSExps» :=
  fun (x0 : List T) =>
    let x1 : T ×
      List
        (List
          T) := Const.foldr
      (α := T)
      (β := (T × List (List T)) → T × List (List T))
      (fun (x1 : T)
         (x2 : (T × List (List T)) → T × List (List T))
         (x3 : T × List (List T)) =>
        x2 («parseStep» x3 x1))
      (fun (x1 : T × List (List T)) => x1)
      («tokenize» x0)
      (leaf 1, (([] : List T) :: ([] : List (List T))));
    if ((x1).1).label ≠ 0 then
      Const.lcase
        (α := List T)
        (β := T)
        (x1).2
        «none»
        (fun (x2 : List T) (x3 : List (List T)) =>
          Const.lcase
            (α := List T)
            (β := T)
            x3
            («some» (Const.node (leaf 0) («reverse» x2)))
            (fun (_ : List T) (_ : List (List T)) => «none»))
    else
      «none»

def «isAtom» := fun (x0 : T) => Const.eq (Const.label x0) (leaf 1)

def «isList» := fun (x0 : T) => Const.eq (Const.label x0) (leaf 2)

def «nameOf» :=
  fun (x0 : T) => Const.node (leaf 0) (Const.children x0)

def «named» :=
  fun (x0 : T) (x1 : T) =>
    if («isAtom» x0).label ≠ 0 then
      Const.equal («nameOf» x0) x1
    else
      leaf 0

def «kwT» := mk 0 [leaf 84]

def «kwUnit» := mk 0 [leaf 85, leaf 110, leaf 105, leaf 116]

def «kwProd» := mk 0 [leaf 80, leaf 114, leaf 111, leaf 100]

def «kwArrow» :=
  mk 0 [leaf 65, leaf 114, leaf 114, leaf 111, leaf 119]

def «kwList» := mk 0 [leaf 76, leaf 105, leaf 115, leaf 116]

def «kwLam» := mk 0 [leaf 108, leaf 97, leaf 109]

def «kwLet» := mk 0 [leaf 108, leaf 101, leaf 116]

def «kwPair» := mk 0 [leaf 112, leaf 97, leaf 105, leaf 114]

def «kwFst» := mk 0 [leaf 102, leaf 115, leaf 116]

def «kwSnd» := mk 0 [leaf 115, leaf 110, leaf 100]

def «kwIf» := mk 0 [leaf 105, leaf 102]

def «kwQuote» :=
  mk 0 [leaf 113, leaf 117, leaf 111, leaf 116, leaf 101]

def «kwCons» := mk 0 [leaf 99, leaf 111, leaf 110, leaf 115]

def «kwNil» := mk 0 [leaf 110, leaf 105, leaf 108]

def «kwFold» := mk 0 [leaf 102, leaf 111, leaf 108, leaf 100]

def «kwIter» := mk 0 [leaf 105, leaf 116, leaf 101, leaf 114]

def «kwFoldr» :=
  mk 0 [leaf 102, leaf 111, leaf 108, leaf 100, leaf 114]

def «kwLcase» := mk 0 [leaf 108, leaf 99, leaf 97, leaf 115, leaf 101]

def «kwUnitValue» := mk 0 [leaf 117, leaf 110, leaf 105, leaf 116]

def «kwDef» := mk 0 [leaf 100, leaf 101, leaf 102]

def «kwDeftype» :=
  mk 0 [leaf 100,
    leaf 101,
    leaf 102,
    leaf 116,
    leaf 121,
    leaf 112,
    leaf 101]

def «kwDefnum» :=
  mk 0 [leaf 100, leaf 101, leaf 102, leaf 110, leaf 117, leaf 109]

def «primNames» :=
  Const.children
    (mk 0 [mk 0 [leaf 108, leaf 97, leaf 98, leaf 101, leaf 108],
      mk 0 [leaf 97, leaf 114, leaf 105, leaf 116, leaf 121],
      mk 0 [leaf 99, leaf 104, leaf 105, leaf 108, leaf 100],
      mk 0 [leaf 110, leaf 111, leaf 100, leaf 101],
      mk 0 [leaf 99,
        leaf 104,
        leaf 105,
        leaf 108,
        leaf 100,
        leaf 114,
        leaf 101,
        leaf 110],
      mk 0 [leaf 97, leaf 100, leaf 100],
      mk 0 [leaf 115, leaf 117, leaf 98],
      mk 0 [leaf 109, leaf 117, leaf 108],
      mk 0 [leaf 100, leaf 105, leaf 118],
      mk 0 [leaf 109, leaf 111, leaf 100],
      mk 0 [leaf 101, leaf 113],
      mk 0 [leaf 108, leaf 116],
      mk 0 [leaf 101, leaf 113, leaf 117, leaf 97, leaf 108],
      mk 0 [leaf 108, leaf 111, leaf 103, leaf 50]])

def «indexOf» :=
  fun (x0 : T) (x1 : List T) =>
    Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) =>
        if (Const.equal x0 x2).label ≠ 0 then
          «some» (leaf 0)
        else
          if («isSome» x3).label ≠ 0 then
            «some» (Const.add («get» x3) (leaf 1))
          else
            «none»)
      «none»
      x1

def «lookupAbbrev» :=
  fun (x0 : T) (x1 : List T) =>
    Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) =>
        if (Const.equal x0 (Const.child x2 (leaf 0))).label ≠ 0 then
          «some» (Const.child x2 (leaf 1))
        else
          x3)
      «none»
      x1

def «numeral» :=
  fun (x0 : List T) =>
    let x1 : T ×
      (T ×
        T) := Const.foldr
      (α := T)
      (β := T × (T × T))
      (fun (x1 : T) (x2 : T × (T × T)) =>
        if (Const.lt x1 (leaf 48)).label ≠ 0 then
          (leaf 0, (x2).2)
        else
          if (Const.lt (leaf 57) x1).label ≠ 0 then
            (leaf 0, (x2).2)
          else
            ((x2).1,
              (Const.add ((x2).2).1 (Const.mul (Const.sub x1 (leaf 48)) ((x2).2).2),
                Const.mul (leaf 10) ((x2).2).2)))
      (leaf 1, (leaf 0, leaf 1))
      x0;
    if («nonEmpty» x0).label ≠ 0 then
      if ((x1).1).label ≠ 0 then «some» ((x1).2).1 else «none»
    else
      «none»

def «expandNums» :=
  fun (x0 : List T) (x1 : T) =>
    Const.fold
      (α := T)
      (fun (x2 : T) (x3 : List T) =>
        let x4 : T := Const.node x2 x3;
        if («isAtom» x4).label ≠ 0 then
          let x5 : T := «lookupAbbrev» («nameOf» x4) x0;
          if («isSome» x5).label ≠ 0 then «get» x5 else x4
        else
          x4)
      x1

def «numOf» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := «expandNums» x0 x1;
    if («isAtom» x2).label ≠ 0 then
      if («isSome» («numeral» (Const.children x2))).label ≠ 0 then
        «some» x2
      else
        «none»
    else
      «none»

def «rtTrees» :=
  fun (x0 : List (T × T)) =>
    Const.foldr
      (α := T × T)
      (β := List T)
      (fun (x1 : T × T) (x2 : List T) => ((x1).1 :: x2))
      ([] : List T)
      x0

def «rtValues» :=
  fun (x0 : List (T × T)) =>
    Const.foldr
      (α := T × T)
      (β := List T)
      (fun (x1 : T × T) (x2 : List T) => ((x1).2 :: x2))
      ([] : List T)
      x0

def «node2» :=
  fun (x0 : T) (x1 : T) (x2 : T) => Const.node x0 (x1 :: («single» x2))

def «some2» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    if («both» x1 x2).label ≠ 0 then
      «some» («node2» x0 («get» x1) («get» x2))
    else
      «none»

def «readType» :=
  fun (x0 : List T) (x1 : T) =>
    (Const.fold
      (α := T × T)
      (fun (x2 : T) (x3 : List (T × T)) =>
        let x4 : T := Const.node x2 («rtTrees» x3);
        let x5 : List T := «rtValues» x3;
        (x4,
          if («isAtom» x4).label ≠ 0 then
            let x6 : T := «nameOf» x4;
            if (Const.equal x6 «kwT»).label ≠ 0 then
              «some» (leaf 0)
            else
              if (Const.equal x6 «kwUnit»).label ≠ 0 then
                «some» (leaf 1)
              else
                «lookupAbbrev» x6 x0
          else
            if («isList» x4).label ≠ 0 then
              let x6 : T := «at» (Const.children x4) (leaf 0);
              let x7 : T := Const.arity x4;
              if («named» x6 «kwProd»).label ≠ 0 then
                if (Const.eq x7 (leaf 3)).label ≠ 0 then
                  «some2» (leaf 2) («at» x5 (leaf 1)) («at» x5 (leaf 2))
                else
                  «none»
              else
                if («named» x6 «kwArrow»).label ≠ 0 then
                  if (Const.eq x7 (leaf 3)).label ≠ 0 then
                    «some2» (leaf 3) («at» x5 (leaf 1)) («at» x5 (leaf 2))
                  else
                    «none»
                else
                  if («named» x6 «kwList»).label ≠ 0 then
                    if (Const.eq x7 (leaf 2)).label ≠ 0 then
                      if («isSome» («at» x5 (leaf 1))).label ≠ 0 then
                        «some» (Const.node (leaf 4) («single» («get» («at» x5 (leaf 1)))))
                      else
                        «none»
                    else
                      «none»
                  else
                    «none»
            else
              «none»))
      x1).2

def «readDatum» :=
  fun (x0 : T) =>
    (Const.fold
      (α := T × T)
      (fun (x1 : T) (x2 : List (T × T)) =>
        let x3 : T := Const.node x1 («rtTrees» x2);
        (x3,
          if («isAtom» x3).label ≠ 0 then
            let x4 : T := «numeral» (Const.children x3);
            if («isSome» x4).label ≠ 0 then
              «some» (Const.node («get» x4) ([] : List T))
            else
              «none»
          else
            if («isList» x3).label ≠ 0 then
              Const.lcase
                (α := T)
                (β := T)
                (Const.children x3)
                «none»
                (fun (x4 : T) (_ : List T) =>
                  let x6 : T := (if («isAtom» x4).label ≠ 0 then
                    «numeral» (Const.children x4)
                  else
                    «none»);
                  let x7 : T := «allSome» («tail» («rtValues» x2));
                  if («both» x6 x7).label ≠ 0 then
                    «some» (Const.node («get» x6) (Const.children («get» x7)))
                  else
                    «none»)
            else
              «none»))
      x0).2

def «rrTrees» :=
  fun (x0 : List (T × (List T → T))) =>
    Const.foldr
      (α := T × (List T → T))
      (β := List T)
      (fun (x1 : T × (List T → T)) (x2 : List T) => ((x1).1 :: x2))
      ([] : List T)
      x0

def «rrApply» :=
  fun (x0 : List (T × (List T → T))) (x1 : List T) =>
    Const.foldr
      (α := T × (List T → T))
      (β := List T)
      (fun (x2 : T × (List T → T)) (x3 : List T) => (((x2).2 x1) :: x3))
      ([] : List T)
      x0

def «rrTail» :=
  fun (x0 : List (T × (List T → T))) =>
    Const.lcase
      (α := T × (List T → T))
      (β := List (T × (List T → T)))
      x0
      ([] : List (T × (List T → T)))
      (fun (_ : T × (List T → T)) (x2 : List (T × (List T → T))) => x2)

def «rrAt» :=
  fun (x0 : List (T × (List T → T))) (x1 : T) (x2 : List T) =>
    Const.lcase
      (α := T × (List T → T))
      (β := List T → T)
      (Const.iter (α := List (T × (List T → T))) «rrTail» x0 x1)
      (fun (_ : List T) => «none»)
      (fun (x3 : T × (List T → T)) (_ : List (T × (List T → T))) => (x3).2)
      x2

def «app» := fun (x0 : T) (x1 : T) => «node2» (leaf 10) x0 x1

def «apps» :=
  fun (x0 : T) (x1 : List T) =>
    Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) => «app» x3 x2)
      x0
      («reverse» x1)

def «some1» :=
  fun (x0 : T) (x1 : T) =>
    if («isSome» x1).label ≠ 0 then
      «some» (Const.node x0 («single» («get» x1)))
    else
      «none»

def «argsOf» :=
  fun (x0 : List (T × (List T → T))) (x1 : T) (x2 : List T) =>
    «allSome»
      («rrApply»
        (Const.iter (α := List (T × (List T → T))) «rrTail» x0 x1)
        x2)

def «mkArgs» :=
  fun (x0 : T) (x1 : T) =>
    if («isSome» x1).label ≠ 0 then
      «some» (Const.node x0 (Const.children («get» x1)))
    else
      «none»

def «appsOpt» :=
  fun (x0 : T) (x1 : T) =>
    if («both» x0 x1).label ≠ 0 then
      «some» («apps» («get» x0) (Const.children («get» x1)))
    else
      «none»

def «binders» :=
  fun (x0 : T) =>
    if («isList» x0).label ≠ 0 then
      if (Const.eq (Const.arity x0) (leaf 2)).label ≠ 0 then
        if («isAtom» (Const.child x0 (leaf 0))).label ≠ 0 then
          «single» x0
        else
          Const.children x0
      else
        Const.children x0
    else
      ([] : List T)

def «readBinders» :=
  fun (x0 : List T) (x1 : List T) =>
    «allSome»
      (Const.foldr
        (α := T)
        (β := List T)
        (fun (x2 : T) (x3 : List T) =>
          ((if («isList» x2).label ≠ 0 then
            if (Const.eq (Const.arity x2) (leaf 2)).label ≠ 0 then
              if («isAtom» (Const.child x2 (leaf 0))).label ≠ 0 then
                let x4 : T := «readType» x0 (Const.child x2 (leaf 1));
                if («isSome» x4).label ≠ 0 then
                  «some»
                    («node2» (leaf 0) («nameOf» (Const.child x2 (leaf 0))) («get» x4))
                else
                  «none»
              else
                «none»
            else
              «none»
          else
            «none») ::
            x3))
        ([] : List T)
        x1)

def «resolveAtom» :=
  fun (x0 : List T) (x1 : T) (x2 : List T) =>
    let x3 : T := «numeral» (Const.children x1);
    if («isSome» x3).label ≠ 0 then
      «some» (Const.node (leaf 15) («single» («get» x3)))
    else
      let x4 : T := «nameOf» x1;
      let x5 : T := «indexOf» x4 x2;
      if («isSome» x5).label ≠ 0 then
        «some» (Const.node (leaf 8) («single» («get» x5)))
      else
        let x6 : T := «indexOf» x4 x0;
        if («isSome» x6).label ≠ 0 then
          «some» (Const.node (leaf 23) («single» («get» x6)))
        else
          let x7 : T := «indexOf» x4 «primNames»;
          if («isSome» x7).label ≠ 0 then
            «some» (Const.node (leaf 22) («single» («get» x7)))
          else
            if (Const.equal x4 «kwUnitValue»).label ≠ 0 then
              «some» (Const.node (leaf 11) ([] : List T))
            else
              «none»

def «resolveList» :=
  fun (x0 : List T)
    (x1 : T)
    (x2 : List (T × (List T → T)))
    (x3 : List T) =>
    let x4 : List T := Const.children x1;
    let x5 : T := Const.arity x1;
    let x6 : T := «at» x4 (leaf 0);
    if (Const.eq x5 (leaf 0)).label ≠ 0 then
      «none»
    else
      if (if («named» x6 «kwLam»).label ≠ 0 then
        Const.eq x5 (leaf 3)
      else
        leaf 0).label ≠ 0 then
        let x7 : T := «readBinders» x0 («binders» («at» x4 (leaf 1)));
        if («isSome» x7).label ≠ 0 then
          let x8 : List T := Const.children («get» x7);
          if («nonEmpty» x8).label ≠ 0 then
            let x9 : T := «rrAt»
              x2
              (leaf 2)
              («append»
                («reverse»
                  (Const.foldr
                    (α := T)
                    (β := List T)
                    (fun (x9 : T) (x10 : List T) => ((Const.child x9 (leaf 0)) :: x10))
                    ([] : List T)
                    x8))
                x3);
            if («isSome» x9).label ≠ 0 then
              «some»
                (Const.foldr
                  (α := T)
                  (β := T)
                  (fun (x10 : T) (x11 : T) =>
                    «node2» (leaf 9) (Const.child x10 (leaf 1)) x11)
                  («get» x9)
                  x8)
            else
              «none»
          else
            «none»
        else
          «none»
      else
        if (if («named» x6 «kwLet»).label ≠ 0 then
          Const.eq x5 (leaf 5)
        else
          leaf 0).label ≠ 0 then
          let x7 : T := «at» x4 (leaf 1);
          if («isAtom» x7).label ≠ 0 then
            let x8 : T := «readType» x0 («at» x4 (leaf 2));
            let x9 : T := «rrAt» x2 (leaf 4) ((«nameOf» x7) :: x3);
            let x10 : T := «rrAt» x2 (leaf 3) x3;
            if («both» x8 («both» x9 x10)).label ≠ 0 then
              «some» («app» («node2» (leaf 9) («get» x8) («get» x9)) («get» x10))
            else
              «none»
          else
            «none»
        else
          if («named» x6 «kwPair»).label ≠ 0 then
            «mkArgs» (leaf 12) («argsOf» x2 (leaf 1) x3)
          else
            if («named» x6 «kwFst»).label ≠ 0 then
              «mkArgs» (leaf 13) («argsOf» x2 (leaf 1) x3)
            else
              if («named» x6 «kwSnd»).label ≠ 0 then
                «mkArgs» (leaf 14) («argsOf» x2 (leaf 1) x3)
              else
                if («named» x6 «kwIf»).label ≠ 0 then
                  «mkArgs» (leaf 16) («argsOf» x2 (leaf 1) x3)
                else
                  if («named» x6 «kwCons»).label ≠ 0 then
                    «mkArgs» (leaf 20) («argsOf» x2 (leaf 1) x3)
                  else
                    if (if («named» x6 «kwQuote»).label ≠ 0 then
                      Const.eq x5 (leaf 2)
                    else
                      leaf 0).label ≠ 0 then
                      «some1» (leaf 15) («readDatum» («at» x4 (leaf 1)))
                    else
                      if (if («named» x6 «kwNil»).label ≠ 0 then
                        Const.eq x5 (leaf 2)
                      else
                        leaf 0).label ≠ 0 then
                        «some1» (leaf 19) («readType» x0 («at» x4 (leaf 1)))
                      else
                        if (if («named» x6 «kwFold»).label ≠ 0 then
                          Const.lt (leaf 1) x5
                        else
                          leaf 0).label ≠ 0 then
                          let x7 : T := «readType» x0 («at» x4 (leaf 1));
                          if («isSome» x7).label ≠ 0 then
                            «appsOpt»
                              («some» (Const.node (leaf 17) («single» («get» x7))))
                              («argsOf» x2 (leaf 2) x3)
                          else
                            «none»
                        else
                          if (if («named» x6 «kwIter»).label ≠ 0 then
                            Const.lt (leaf 1) x5
                          else
                            leaf 0).label ≠ 0 then
                            let x7 : T := «readType» x0 («at» x4 (leaf 1));
                            if («isSome» x7).label ≠ 0 then
                              «appsOpt»
                                («some» (Const.node (leaf 18) («single» («get» x7))))
                                («argsOf» x2 (leaf 2) x3)
                            else
                              «none»
                          else
                            if (if («named» x6 «kwFoldr»).label ≠ 0 then
                              Const.lt (leaf 2) x5
                            else
                              leaf 0).label ≠ 0 then
                              let x7 : T := «some2»
                                (leaf 21)
                                («readType» x0 («at» x4 (leaf 1)))
                                («readType» x0 («at» x4 (leaf 2)));
                              if («isSome» x7).label ≠ 0 then
                                «appsOpt» x7 («argsOf» x2 (leaf 3) x3)
                              else
                                «none»
                            else
                              if (if («named» x6 «kwLcase»).label ≠ 0 then
                                Const.lt (leaf 2) x5
                              else
                                leaf 0).label ≠ 0 then
                                let x7 : T := «some2»
                                  (leaf 24)
                                  («readType» x0 («at» x4 (leaf 1)))
                                  («readType» x0 («at» x4 (leaf 2)));
                                if («isSome» x7).label ≠ 0 then
                                  «appsOpt» x7 («argsOf» x2 (leaf 3) x3)
                                else
                                  «none»
                              else
                                «appsOpt» («rrAt» x2 (leaf 0) x3) («argsOf» x2 (leaf 1) x3)

def «resolve» :=
  fun (x0 : List T) (x1 : List T) (x2 : T) (x3 : List T) =>
    (Const.fold
      (α := T × (List T → T))
      (fun (x4 : T) (x5 : List (T × (List T → T))) =>
        let x6 : T := Const.node x4 («rrTrees» x5);
        (x6,
          fun (x7 : List T) =>
            if («isAtom» x6).label ≠ 0 then
              «resolveAtom» x1 x6 x7
            else
              if («isList» x6).label ≠ 0 then
                «resolveList» x0 x6 x5 x7
              else
                «none»))
      x2).2
      x3

def «progStep» :=
  fun (x0 : T × (List T × (List T × (List T × List T)))) (x1 : T) =>
    let x2 : List T := ((x0).2).1;
    let x3 : List T := (((x0).2).2).1;
    let x4 : List T := ((((x0).2).2).2).1;
    let x5 : List T := ((((x0).2).2).2).2;
    if (if ((x0).1).label ≠ 0 then
      if («isList» x1).label ≠ 0 then
        if (Const.eq (Const.arity x1) (leaf 3)).label ≠ 0 then
          «isAtom» (Const.child x1 (leaf 1))
        else
          leaf 0
      else
        leaf 0
    else
      leaf 0).label ≠ 0 then
      let x6 : T := «nameOf» (Const.child x1 (leaf 1));
      if («named» (Const.child x1 (leaf 0)) «kwDef»).label ≠ 0 then
        let x7 : T := «resolve»
          x2
          x4
          («expandNums» x3 (Const.child x1 (leaf 2)))
          ([] : List T);
        if («isSome» x7).label ≠ 0 then
          (leaf 1,
            (x2,
              (x3, («append» x4 («single» x6), «append» x5 («single» («get» x7))))))
        else
          (leaf 0, (x0).2)
      else
        if («named» (Const.child x1 (leaf 0)) «kwDeftype»).label ≠ 0 then
          let x7 : T := «readType» x2 (Const.child x1 (leaf 2));
          if («isSome» x7).label ≠ 0 then
            (leaf 1, (((«node2» (leaf 0) x6 («get» x7)) :: x2), ((x0).2).2))
          else
            (leaf 0, (x0).2)
        else
          if («named» (Const.child x1 (leaf 0)) «kwDefnum»).label ≠ 0 then
            let x7 : T := «numOf» x3 (Const.child x1 (leaf 2));
            if («isSome» x7).label ≠ 0 then
              (leaf 1,
                (x2, (((«node2» (leaf 0) x6 («get» x7)) :: x3), (((x0).2).2).2)))
            else
              (leaf 0, (x0).2)
          else
            (leaf 0, (x0).2)
    else
      (leaf 0, (x0).2)

def «readProgram» :=
  fun (x0 : List T) =>
    let x1 : T ×
      (List T ×
        (List T ×
          (List T ×
            List
              T))) := Const.foldr
      (α := T)
      (β := (T × (List T × (List T × (List T × List T)))) →
        T × (List T × (List T × (List T × List T))))
      (fun (x1 : T)
         (x2 : (T × (List T × (List T × (List T × List T)))) →
           T × (List T × (List T × (List T × List T))))
         (x3 : T × (List T × (List T × (List T × List T)))) =>
        x2 («progStep» x3 x1))
      (fun (x1 : T × (List T × (List T × (List T × List T)))) => x1)
      x0
      (leaf 1,
        (([] : List T), (([] : List T), (([] : List T), ([] : List T)))));
    if ((x1).1).label ≠ 0 then
      «some»
        («node2»
          (leaf 100)
          (Const.node (leaf 101) ((((x1).2).2).2).2)
          (Const.node (leaf 102) ((((x1).2).2).2).1))
    else
      «none»

def «and» :=
  fun (x0 : T) (x1 : T) => if (x0).label ≠ 0 then x1 else leaf 0

def «or» :=
  fun (x0 : T) (x1 : T) => if (x0).label ≠ 0 then leaf 1 else x1

def «tyArrow» := fun (x0 : T) (x1 : T) => «node2» (leaf 3) x0 x1

def «tyList» := fun (x0 : T) => Const.node (leaf 4) («single» x0)

def «isTy» :=
  fun (x0 : T) =>
    Const.fold
      (α := T)
      (fun (x1 : T) (x2 : List T) =>
        let x3 : T := «length» x2;
        if (Const.eq x3 (leaf 0)).label ≠ 0 then
          if (Const.eq x1 (leaf 0)).label ≠ 0 then
            leaf 1
          else
            Const.eq x1 (leaf 1)
        else
          if (Const.eq x3 (leaf 1)).label ≠ 0 then
            «and» (Const.eq x1 (leaf 4)) («at» x2 (leaf 0))
          else
            if (Const.eq x3 (leaf 2)).label ≠ 0 then
              «and»
                (if (Const.eq x1 (leaf 2)).label ≠ 0 then
                  leaf 1
                else
                  Const.eq x1 (leaf 3))
                («and» («at» x2 (leaf 0)) («at» x2 (leaf 1)))
            else
              leaf 0)
      x0

def «isProd» :=
  fun (x0 : T) =>
    «and»
      (Const.eq (Const.label x0) (leaf 2))
      (Const.eq (Const.arity x0) (leaf 2))

def «isArrow» :=
  fun (x0 : T) =>
    «and»
      (Const.eq (Const.label x0) (leaf 3))
      (Const.eq (Const.arity x0) (leaf 2))

def «isListTy» :=
  fun (x0 : T) =>
    «and»
      (Const.eq (Const.label x0) (leaf 4))
      (Const.eq (Const.arity x0) (leaf 1))

def «foldTy» :=
  fun (x0 : T) =>
    «tyArrow»
      («tyArrow» (leaf 0) («tyArrow» («tyList» x0) x0))
      («tyArrow» (leaf 0) x0)

def «iterTy» :=
  fun (x0 : T) =>
    «tyArrow» («tyArrow» x0 x0) («tyArrow» x0 («tyArrow» (leaf 0) x0))

def «foldrTy» :=
  fun (x0 : T) (x1 : T) =>
    «tyArrow»
      («tyArrow» x0 («tyArrow» x1 x1))
      («tyArrow» x1 («tyArrow» («tyList» x0) x1))

def «lcaseTy» :=
  fun (x0 : T) (x1 : T) =>
    «tyArrow»
      («tyList» x0)
      («tyArrow»
        x1
        («tyArrow» («tyArrow» x0 («tyArrow» («tyList» x0) x1)) x1))

def «primTypes» :=
  let x0 : T := «tyArrow» (leaf 0) (leaf 0);
  let x1 : T := «tyArrow» (leaf 0) x0;
  «append»
    (x0 ::
      (x0 ::
        (x1 ::
          ((«tyArrow» (leaf 0) («tyArrow» («tyList» (leaf 0)) (leaf 0))) ::
            ((«tyArrow» (leaf 0) («tyList» (leaf 0))) :: ([] : List T))))))
    («append» («replicate» (leaf 8) x1) («single» x0))

def «nth» :=
  fun (x0 : List T) (x1 : T) =>
    if (Const.lt x1 («length» x0)).label ≠ 0 then
      «some» («at» x0 x1)
    else
      «none»

def «checkNode» :=
  fun (x0 : List T)
    (x1 : T)
    (x2 : List (T × (List T → T)))
    (x3 : List T) =>
    let x4 : T := Const.label x1;
    let x5 : List T := Const.children x1;
    let x6 : T := Const.arity x1;
    if (Const.eq x4 (leaf 8)).label ≠ 0 then
      if (Const.eq x6 (leaf 1)).label ≠ 0 then
        «nth» x3 (Const.label («at» x5 (leaf 0)))
      else
        «none»
    else
      if (Const.eq x4 (leaf 9)).label ≠ 0 then
        if (Const.eq x6 (leaf 2)).label ≠ 0 then
          let x7 : T := «at» x5 (leaf 0);
          if («isTy» x7).label ≠ 0 then
            let x8 : T := «rrAt» x2 (leaf 1) (x7 :: x3);
            if («isSome» x8).label ≠ 0 then
              «some» («tyArrow» x7 («get» x8))
            else
              «none»
          else
            «none»
        else
          «none»
      else
        if (Const.eq x4 (leaf 10)).label ≠ 0 then
          if (Const.eq x6 (leaf 2)).label ≠ 0 then
            let x7 : T := «rrAt» x2 (leaf 0) x3;
            let x8 : T := «rrAt» x2 (leaf 1) x3;
            if («both» x7 x8).label ≠ 0 then
              if («isArrow» («get» x7)).label ≠ 0 then
                if (Const.equal
                  («get» x8)
                  (Const.child («get» x7) (leaf 0))).label ≠ 0 then
                  «some» (Const.child («get» x7) (leaf 1))
                else
                  «none»
              else
                «none»
            else
              «none»
          else
            «none»
        else
          if (Const.eq x4 (leaf 11)).label ≠ 0 then
            if (Const.eq x6 (leaf 0)).label ≠ 0 then «some» (leaf 1) else «none»
          else
            if (Const.eq x4 (leaf 12)).label ≠ 0 then
              if (Const.eq x6 (leaf 2)).label ≠ 0 then
                «some2» (leaf 2) («rrAt» x2 (leaf 0) x3) («rrAt» x2 (leaf 1) x3)
              else
                «none»
            else
              if (Const.eq x4 (leaf 13)).label ≠ 0 then
                if (Const.eq x6 (leaf 1)).label ≠ 0 then
                  let x7 : T := «rrAt» x2 (leaf 0) x3;
                  if («isSome» x7).label ≠ 0 then
                    if («isProd» («get» x7)).label ≠ 0 then
                      «some» (Const.child («get» x7) (leaf 0))
                    else
                      «none»
                  else
                    «none»
                else
                  «none»
              else
                if (Const.eq x4 (leaf 14)).label ≠ 0 then
                  if (Const.eq x6 (leaf 1)).label ≠ 0 then
                    let x7 : T := «rrAt» x2 (leaf 0) x3;
                    if («isSome» x7).label ≠ 0 then
                      if («isProd» («get» x7)).label ≠ 0 then
                        «some» (Const.child («get» x7) (leaf 1))
                      else
                        «none»
                    else
                      «none»
                  else
                    «none»
                else
                  if (Const.eq x4 (leaf 15)).label ≠ 0 then
                    if (Const.eq x6 (leaf 1)).label ≠ 0 then «some» (leaf 0) else «none»
                  else
                    if (Const.eq x4 (leaf 16)).label ≠ 0 then
                      if (Const.eq x6 (leaf 3)).label ≠ 0 then
                        let x7 : T := «rrAt» x2 (leaf 0) x3;
                        let x8 : T := «rrAt» x2 (leaf 1) x3;
                        let x9 : T := «rrAt» x2 (leaf 2) x3;
                        if («both» x7 («both» x8 x9)).label ≠ 0 then
                          if (Const.equal («get» x7) (leaf 0)).label ≠ 0 then
                            if (Const.equal («get» x9) («get» x8)).label ≠ 0 then x8 else «none»
                          else
                            «none»
                        else
                          «none»
                      else
                        «none»
                    else
                      if (Const.eq x4 (leaf 17)).label ≠ 0 then
                        if (Const.eq x6 (leaf 1)).label ≠ 0 then
                          if («isTy» («at» x5 (leaf 0))).label ≠ 0 then
                            «some» («foldTy» («at» x5 (leaf 0)))
                          else
                            «none»
                        else
                          «none»
                      else
                        if (Const.eq x4 (leaf 18)).label ≠ 0 then
                          if (Const.eq x6 (leaf 1)).label ≠ 0 then
                            if («isTy» («at» x5 (leaf 0))).label ≠ 0 then
                              «some» («iterTy» («at» x5 (leaf 0)))
                            else
                              «none»
                          else
                            «none»
                        else
                          if (Const.eq x4 (leaf 19)).label ≠ 0 then
                            if (Const.eq x6 (leaf 1)).label ≠ 0 then
                              if («isTy» («at» x5 (leaf 0))).label ≠ 0 then
                                «some» («tyList» («at» x5 (leaf 0)))
                              else
                                «none»
                            else
                              «none»
                          else
                            if (Const.eq x4 (leaf 20)).label ≠ 0 then
                              if (Const.eq x6 (leaf 2)).label ≠ 0 then
                                let x7 : T := «rrAt» x2 (leaf 0) x3;
                                let x8 : T := «rrAt» x2 (leaf 1) x3;
                                if («both» x7 x8).label ≠ 0 then
                                  if («isListTy» («get» x8)).label ≠ 0 then
                                    if (Const.equal
                                      («get» x7)
                                      (Const.child («get» x8) (leaf 0))).label ≠ 0 then
                                      «some» («tyList» («get» x7))
                                    else
                                      «none»
                                  else
                                    «none»
                                else
                                  «none»
                              else
                                «none»
                            else
                              if (Const.eq x4 (leaf 21)).label ≠ 0 then
                                if (Const.eq x6 (leaf 2)).label ≠ 0 then
                                  if («and»
                                    («isTy» («at» x5 (leaf 0)))
                                    («isTy» («at» x5 (leaf 1)))).label ≠ 0 then
                                    «some» («foldrTy» («at» x5 (leaf 0)) («at» x5 (leaf 1)))
                                  else
                                    «none»
                                else
                                  «none»
                              else
                                if (Const.eq x4 (leaf 22)).label ≠ 0 then
                                  if (Const.eq x6 (leaf 1)).label ≠ 0 then
                                    «nth» «primTypes» (Const.label («at» x5 (leaf 0)))
                                  else
                                    «none»
                                else
                                  if (Const.eq x4 (leaf 23)).label ≠ 0 then
                                    if (Const.eq x6 (leaf 1)).label ≠ 0 then
                                      «nth» x0 (Const.label («at» x5 (leaf 0)))
                                    else
                                      «none»
                                  else
                                    if (Const.eq x4 (leaf 24)).label ≠ 0 then
                                      if (Const.eq x6 (leaf 2)).label ≠ 0 then
                                        if («and»
                                          («isTy» («at» x5 (leaf 0)))
                                          («isTy» («at» x5 (leaf 1)))).label ≠ 0 then
                                          «some» («lcaseTy» («at» x5 (leaf 0)) («at» x5 (leaf 1)))
                                        else
                                          «none»
                                      else
                                        «none»
                                    else
                                      «none»

def «typeIn» :=
  fun (x0 : List T) (x1 : List T) (x2 : T) =>
    (Const.fold
      (α := T × (List T → T))
      (fun (x3 : T) (x4 : List (T × (List T → T))) =>
        let x5 : T := Const.node x3 («rrTrees» x4);
        (x5, fun (x6 : List T) => «checkNode» x0 x5 x4 x6))
      x2).2
      x1

def «typeOf» :=
  fun (x0 : List T) (x1 : T) => «typeIn» x0 ([] : List T) x1

def «checkProgram» :=
  fun (x0 : List T) =>
    let x1 : T ×
      List
        T := Const.foldr
      (α := T)
      (β := (T × List T) → T × List T)
      (fun (x1 : T) (x2 : (T × List T) → T × List T) (x3 : T × List T) =>
        x2
          (if ((x3).1).label ≠ 0 then
            let x4 : T := «typeOf» (x3).2 x1;
            if («isSome» x4).label ≠ 0 then
              (leaf 1, «append» (x3).2 («single» («get» x4)))
            else
              (leaf 0, (x3).2)
          else
            x3))
      (fun (x1 : T × List T) => x1)
      x0
      (leaf 1, ([] : List T));
    if ((x1).1).label ≠ 0 then
      «some» (Const.node (leaf 0) (x1).2)
    else
      «none»

def «nothing» := Const.node (leaf 0) ([] : List T)

def «just» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «sx0» := Const.node (leaf 0) ([] : List T)

def «atom» := fun (x0 : List T) => Const.node (leaf 1) x0

def «lst» := fun (x0 : List T) => Const.node (leaf 2) x0

def «sx1» := fun (x0 : T) => let x1 : T := «lst» («single» x0); x1

def «sx2» :=
  fun (x0 : T) (x1 : T) => let x2 : T := «lst» (x0 :: («single» x1)); x2

def «sx3» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «lst» (x0 :: (x1 :: («single» x2))); x3

def «sx4» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : T := «lst» (x0 :: (x1 :: (x2 :: («single» x3)))); x4

def «sx5» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : T := «lst» (x0 :: (x1 :: (x2 :: (x3 :: («single» x4))))); x5

def «sx6» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) (x5 : T) =>
    let x6 : T := «lst»
      (x0 :: (x1 :: (x2 :: (x3 :: (x4 :: («single» x5))))));
    x6

def «aLet» := mk 1 [leaf 108, leaf 101, leaf 116]

def «aIf» := mk 1 [leaf 105, leaf 102]

def «aLam» := mk 1 [leaf 108, leaf 97, leaf 109]

def «aPair» := mk 1 [leaf 112, leaf 97, leaf 105, leaf 114]

def «aFst» := mk 1 [leaf 102, leaf 115, leaf 116]

def «aSnd» := mk 1 [leaf 115, leaf 110, leaf 100]

def «aCons» := mk 1 [leaf 99, leaf 111, leaf 110, leaf 115]

def «aNil» := mk 1 [leaf 110, leaf 105, leaf 108]

def «aIter» := mk 1 [leaf 105, leaf 116, leaf 101, leaf 114]

def «aLcase» := mk 1 [leaf 108, leaf 99, leaf 97, leaf 115, leaf 101]

def «aFoldr» :=
  mk 1 [leaf 102, leaf 111, leaf 108, leaf 100, leaf 114]

def «aFold» := mk 1 [leaf 102, leaf 111, leaf 108, leaf 100]

def «aDef» := mk 1 [leaf 100, leaf 101, leaf 102]

def «aDeftype» :=
  mk 1 [leaf 100,
    leaf 101,
    leaf 102,
    leaf 116,
    leaf 121,
    leaf 112,
    leaf 101]

def «aUnitV» := mk 1 [leaf 117, leaf 110, leaf 105, leaf 116]

def «aLabel» := mk 1 [leaf 108, leaf 97, leaf 98, leaf 101, leaf 108]

def «aChild» := mk 1 [leaf 99, leaf 104, leaf 105, leaf 108, leaf 100]

def «aChildren» :=
  mk 1 [leaf 99,
    leaf 104,
    leaf 105,
    leaf 108,
    leaf 100,
    leaf 114,
    leaf 101,
    leaf 110]

def «aNode» := mk 1 [leaf 110, leaf 111, leaf 100, leaf 101]

def «aEq» := mk 1 [leaf 101, leaf 113]

def «aT» := mk 1 [leaf 84]

def «aUnit» := mk 1 [leaf 85, leaf 110, leaf 105, leaf 116]

def «aProd» := mk 1 [leaf 80, leaf 114, leaf 111, leaf 100]

def «aArrow» := mk 1 [leaf 65, leaf 114, leaf 114, leaf 111, leaf 119]

def «aList» := mk 1 [leaf 76, leaf 105, leaf 115, leaf 116]

def «aZero» := mk 1 [leaf 48]

def «aS» := mk 1 [leaf 37, leaf 115]

def «aL» := mk 1 [leaf 37, leaf 108]

def «aRs» := mk 1 [leaf 37, leaf 114, leaf 115]

def «aO» := mk 1 [leaf 37, leaf 111]

def «aP» := mk 1 [leaf 37, leaf 112]

def «aA» := mk 1 [leaf 37, leaf 97]

def «aH» := mk 1 [leaf 37, leaf 104]

def «aTl» := mk 1 [leaf 37, leaf 116]

def «aX» := mk 1 [leaf 37, leaf 120]

def «aU» := mk 1 [leaf 37, leaf 117]

def «aR» := mk 1 [leaf 37, leaf 114]

def «aD» := mk 1 [leaf 37, leaf 100]

def «aRest» := mk 1 [leaf 37, leaf 114, leaf 101, leaf 115, leaf 116]

def «kwData» := mk 0 [leaf 100, leaf 97, leaf 116, leaf 97]

def «kwCase» := mk 0 [leaf 99, leaf 97, leaf 115, leaf 101]

def «kwCata» := mk 0 [leaf 99, leaf 97, leaf 116, leaf 97]

def «kwDefn» := mk 0 [leaf 100, leaf 101, leaf 102, leaf 110]

def «kwElse» := mk 0 [leaf 101, leaf 108, leaf 115, leaf 101]

def «kwAmp» := mk 0 [leaf 38]

def «decimalChars» :=
  fun (x0 : T) =>
    let x1 : List
      T := (if (Const.eq x0 (leaf 0)).label ≠ 0 then
      «single» (leaf 48)
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
        («digitsMsb» (leaf 10) x0 x1));
    x1

def «numAtom» :=
  fun (x0 : T) => let x1 : T := «atom» («decimalChars» x0); x1

def «fieldAtom» :=
  fun (x0 : T) =>
    let x1 : T := «atom»
      ((leaf 37) :: ((leaf 102) :: («decimalChars» x0)));
    x1

def «sList» := fun (x0 : T) => let x1 : T := «sx2» «aList» x0; x1

def «sProd» :=
  fun (x0 : T) (x1 : T) => let x2 : T := «sx3» «aProd» x0 x1; x2

def «sArrow» :=
  fun (x0 : T) (x1 : T) => let x2 : T := «sx3» «aArrow» x0 x1; x2

def «sLet» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : T := «sx5» «aLet» x0 x1 x2 x3; x4

def «sIf» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «sx4» «aIf» x0 x1 x2; x3

def «sLam1» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «sx3» «aLam» («sx1» («sx2» x0 x1)) x2; x3

def «sLam2» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : T := «sx3» «aLam» («sx2» («sx2» x0 x1) («sx2» x2 x3)) x4; x5

def «sTail» :=
  fun (x0 : T) =>
    let x1 : T := «sLam1»
      «aX»
      («sList» x0)
      («sx6»
        «aLcase»
        x0
        («sList» x0)
        «aX»
        («sx2» «aNil» x0)
        («sLam2» «aH» x0 «aTl» («sList» x0) «aTl»));
    x1

def «sDrop» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «sx5»
      «aIter»
      («sList» x0)
      («sTail» x0)
      x1
      («numAtom» x2);
    x3

def «dropLast» :=
  fun (x0 : List T) =>
    let x1 : List T := «reverse» («tail» («reverse» x0)); x1

def «allTrue» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x1 : T) (x2 : T) => «and» x1 x2)
      (leaf 1)
      x0;
    x1

def «ctorD» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) (x5 : T) =>
    Const.node
      (leaf 0)
      (x0 :: (x1 :: (x2 :: (x3 :: (x4 :: (x5 :: ([] : List T)))))))

def «dataD» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «aliasD» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 2) (x0 :: (x1 :: ([] : List T)))

def «findCtor» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) =>
        let x4 : T := x2;
        if (Const.eq (Const.label x4) (leaf 0)).label ≠ 0 then
          let x5 : T := Const.child x4 (leaf 0);
          let _ : T := Const.child x4 (leaf 1);
          let _ : T := Const.child x4 (leaf 2);
          let _ : T := Const.child x4 (leaf 3);
          let _ : T := Const.child x4 (leaf 4);
          let _ : T := Const.child x4 (leaf 5);
          if (Const.equal x5 x0).label ≠ 0 then «just» x2 else x3
        else
          x3)
      «nothing»
      x1;
    x2

def «isData» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) =>
        let x4 : T := x2;
        if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
          let x5 : T := Const.child x4 (leaf 0);
          if (Const.equal x5 x0).label ≠ 0 then leaf 1 else x3
        else
          x3)
      (leaf 0)
      x1;
    x2

def «findAlias» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) =>
        let x4 : T := x2;
        if (Const.eq (Const.label x4) (leaf 2)).label ≠ 0 then
          let x5 : T := Const.child x4 (leaf 0);
          let x6 : T := Const.child x4 (leaf 1);
          if (Const.equal x5 x0).label ≠ 0 then «just» x6 else x3
        else
          x3)
      «nothing»
      x1;
    x2

def «ctorsOf» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) =>
        let x4 : T := x2;
        if (Const.eq (Const.label x4) (leaf 0)).label ≠ 0 then
          let _ : T := Const.child x4 (leaf 0);
          let _ : T := Const.child x4 (leaf 1);
          let x7 : T := Const.child x4 (leaf 2);
          let _ : T := Const.child x4 (leaf 3);
          let _ : T := Const.child x4 (leaf 4);
          let _ : T := Const.child x4 (leaf 5);
          if (Const.equal x7 x0).label ≠ 0 then (x2 :: x3) else x3
        else
          x3)
      ([] : List T)
      x1;
    x2

def «expandAliases» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := (Const.fold
      (α := T × (Unit → T))
      (fun (x2 : T) (x3 : List (T × (Unit → T))) =>
        let x4 : T := Const.node
          x2
          (Const.foldr
            (α := T × (Unit → T))
            (β := List T)
            (fun (x4 : T × (Unit → T)) (x5 : List T) => ((x4).1 :: x5))
            ([] : List T)
            x3);
        (x4,
          fun (_ : Unit) =>
            if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
              let x6 : List
                T := Const.iter
                (α := List T)
                (fun (x6 : List T) =>
                  Const.lcase
                    (α := T)
                    (β := List T)
                    x6
                    ([] : List T)
                    (fun (_ : T) (x8 : List T) => x8))
                (Const.children x4)
                (leaf 0);
              let x7 : T := «findAlias» (Const.node (leaf 0) x6) x0;
              if (Const.eq (Const.label x7) (leaf 1)).label ≠ 0 then
                let x8 : T := Const.child x7 (leaf 0); x8
              else
                «atom» x6
            else
              if (Const.eq (Const.label x4) (leaf 2)).label ≠ 0 then
                let x6 : List
                  T := Const.foldr
                  (α := T × (Unit → T))
                  (β := List T)
                  (fun (x6 : T × (Unit → T)) (x7 : List T) => (((x6).2 ()) :: x7))
                  ([] : List T)
                  (Const.iter
                    (α := List (T × (Unit → T)))
                    (fun (x6 : List (T × (Unit → T))) =>
                      Const.lcase
                        (α := T × (Unit → T))
                        (β := List (T × (Unit → T)))
                        x6
                        ([] : List (T × (Unit → T)))
                        (fun (_ : T × (Unit → T)) (x8 : List (T × (Unit → T))) => x8))
                    x3
                    (leaf 0));
                «lst» x6
              else
                «sx0»))
      x1).2
      ();
    x2

def «defaultOf» :=
  fun (x0 : T) =>
    let x1 : T := ((Const.fold
      (α := T × (Unit → T × T))
      (fun (x1 : T) (x2 : List (T × (Unit → T × T))) =>
        let x3 : T := Const.node
          x1
          (Const.foldr
            (α := T × (Unit → T × T))
            (β := List T)
            (fun (x3 : T × (Unit → T × T)) (x4 : List T) => ((x3).1 :: x4))
            ([] : List T)
            x2);
        (x3,
          fun (_ : Unit) =>
            if (Const.eq (Const.label x3) (leaf 1)).label ≠ 0 then
              let x5 : List
                T := Const.iter
                (α := List T)
                (fun (x5 : List T) =>
                  Const.lcase
                    (α := T)
                    (β := List T)
                    x5
                    ([] : List T)
                    (fun (_ : T) (x7 : List T) => x7))
                (Const.children x3)
                (leaf 0);
              («atom» x5,
                if (Const.equal (Const.node (leaf 0) x5) «kwUnit»).label ≠ 0 then
                  «aUnitV»
                else
                  «aZero»)
            else
              if (Const.eq (Const.label x3) (leaf 2)).label ≠ 0 then
                let x5 : List
                  (T ×
                    T) := Const.foldr
                  (α := T × (Unit → T × T))
                  (β := List (T × T))
                  (fun (x5 : T × (Unit → T × T)) (x6 : List (T × T)) =>
                    (((x5).2 ()) :: x6))
                  ([] : List (T × T))
                  (Const.iter
                    (α := List (T × (Unit → T × T)))
                    (fun (x5 : List (T × (Unit → T × T))) =>
                      Const.lcase
                        (α := T × (Unit → T × T))
                        (β := List (T × (Unit → T × T)))
                        x5
                        ([] : List (T × (Unit → T × T)))
                        (fun (_ : T × (Unit → T × T)) (x7 : List (T × (Unit → T × T))) => x7))
                    x2
                    (leaf 0));
                let x6 : T := «lst» («rtTrees» x5);
                let x7 : List T := «rtValues» x5;
                let x8 : T := «at» (Const.children x6) (leaf 0);
                (x6,
                  if («named» x8 «kwProd»).label ≠ 0 then
                    «sx3» «aPair» («at» x7 (leaf 1)) («at» x7 (leaf 2))
                  else
                    if («named» x8 «kwArrow»).label ≠ 0 then
                      «sLam1» «aD» («at» (Const.children x6) (leaf 1)) («at» x7 (leaf 2))
                    else
                      if («named» x8 «kwList»).label ≠ 0 then
                        «sx2» «aNil» («at» (Const.children x6) (leaf 1))
                      else
                        «aZero»)
              else
                («sx0», «aZero»)))
      x0).2
      ()).2;
    x1

def «bindWith» :=
  fun (x0 : T → T → T → T → T)
    (x1 : T → T → T → T → T)
    (x2 : T)
    (x3 : List T)
    (x4 : T) =>
    let x5 : T := (let x5 : T := x2;
                   if (Const.eq (Const.label x5) (leaf 0)).label ≠ 0 then
                     let _ : T := Const.child x5 (leaf 0);
                     let _ : T := Const.child x5 (leaf 1);
                     let _ : T := Const.child x5 (leaf 2);
                     let x9 : T := Const.child x5 (leaf 3);
                     let x10 : T := Const.child x5 (leaf 4);
                     let x11 : T := Const.child x5 (leaf 5);
                     let x12 : List T := Const.children x9;
                     let x13 : T := «length» x12;
                     let x14 : T := «length» x3;
                     if («and»
                       (Const.eq x14 (Const.add x13 x10))
                       («allTrue»
                         (Const.foldr
                           (α := T)
                           (β := List T)
                           (fun (x15 : T) (x16 : List T) => ((«isAtom» x15) :: x16))
                           ([] : List T)
                           x3))).label ≠ 0 then
                       «just»
                         (Const.foldr
                           (α := T)
                           (β := T × T)
                           (fun (x15 : T) (x16 : T × T) =>
                             let x17 : T := Const.sub (Const.sub x14 (leaf 1)) (x16).1;
                             (Const.add (x16).1 (leaf 1),
                               if (Const.lt x17 x13).label ≠ 0 then
                                 x0 x17 («at» x12 x17) x15 (x16).2
                               else
                                 x1 x13 x11 x15 (x16).2))
                           (leaf 0, x4)
                           x3).2
                     else
                       «nothing»
                   else
                     «nothing»);
    x5

def «clauseCtor» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := (let x2 : T := x1;
                   if (Const.eq (Const.label x2) (leaf 2)).label ≠ 0 then
                     let x3 : List
                       T := Const.iter
                       (α := List T)
                       (fun (x3 : List T) =>
                         Const.lcase
                           (α := T)
                           (β := List T)
                           x3
                           ([] : List T)
                           (fun (_ : T) (x5 : List T) => x5))
                       (Const.children x2)
                       (leaf 0);
                     let x4 : T := «at» x3 (leaf 0);
                     if (Const.eq (Const.label x4) (leaf 2)).label ≠ 0 then
                       let x5 : List
                         T := Const.iter
                         (α := List T)
                         (fun (x5 : List T) =>
                           Const.lcase
                             (α := T)
                             (β := List T)
                             x5
                             ([] : List T)
                             (fun (_ : T) (x7 : List T) => x7))
                         (Const.children x4)
                         (leaf 0);
                       «findCtor» («nameOf» («at» x5 (leaf 0))) x0
                     else
                       «nothing»
                   else
                     «nothing»);
    x2

def «testChain» :=
  fun (x0 : T) (x1 : List T) (x2 : T) (x3 : T → List T → T → T) =>
    let x4 : T := (let x4 : T ×
                     (T ×
                       T) := Const.foldr
                     (α := T)
                     (β := T × (T × T))
                     (fun (x4 : T) (x5 : T × (T × T)) =>
                       let x6 : T := Const.child x4 (leaf 1);
                       let x7 : T := x3
                         x6
                         («tail»
                           (Const.children (Const.child (Const.child x4 (leaf 0)) (leaf 0))))
                         (Const.child (Const.child x4 (leaf 2)) (leaf 1));
                       if (Const.eq (Const.label x7) (leaf 1)).label ≠ 0 then
                         let x8 : T := Const.child x7 (leaf 0);
                         if ((x5).1).label ≠ 0 then
                           (leaf 1,
                             (leaf 1,
                               if (((x5).2).1).label ≠ 0 then
                                 «sIf»
                                   («sx3»
                                     «aEq»
                                     («sx2» «aLabel» x0)
                                     («numAtom» (Const.child x6 (leaf 1))))
                                   x8
                                   ((x5).2).2
                               else
                                 x8))
                         else
                           (leaf 0, (leaf 0, leaf 0))
                       else
                         (leaf 0, (leaf 0, leaf 0)))
                     (let x4 : T := x2;
                      if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
                        let x5 : T := Const.child x4 (leaf 0); (leaf 1, (leaf 1, x5))
                      else
                        (leaf 1, (leaf 0, leaf 0)))
                     x1;
                   if («and» (x4).1 ((x4).2).1).label ≠ 0 then
                     «just» ((x4).2).2
                   else
                     «nothing»);
    x4

def «clauseChain» :=
  fun (x0 : List T)
    (x1 : T)
    (x2 : List T)
    (x3 : T)
    (x4 : T)
    (x5 : T → List T → T → T) =>
    let x6 : T := (let x6 : T := x3;
                   if (Const.eq (Const.label x6) (leaf 1)).label ≠ 0 then
                     let x7 : T := Const.child x6 (leaf 0);
                     if («nonEmpty» x2).label ≠ 0 then
                       let x8 : List T := Const.children x7;
                       let x9 : T := «length» x2;
                       let x10 : T := «at» x2 (Const.sub x9 (leaf 1));
                       let x11 : T := «and»
                         («isList» x10)
                         («and»
                           (Const.eq (Const.arity x10) (leaf 2))
                           («named» (Const.child x10 (leaf 0)) «kwElse»));
                       let x12 : List T := (if (x11).label ≠ 0 then «dropLast» x2 else x2);
                       let x13 : List T := (if (x11).label ≠ 0 then «dropLast» x8 else x8);
                       let x14 : T := (if (x11).label ≠ 0 then
                         «just» (Const.child («at» x8 (Const.sub x9 (leaf 1))) (leaf 1))
                       else
                         «nothing»);
                       let x15 : List
                         T := Const.foldr
                         (α := T)
                         (β := List T)
                         (fun (x15 : T) (x16 : List T) => ((«clauseCtor» x0 x15) :: x16))
                         ([] : List T)
                         x12;
                       let x16 : T := (let x16 : T := x1;
                                       if (Const.eq (Const.label x16) (leaf 1)).label ≠ 0 then
                                         let x17 : T := Const.child x16 (leaf 0); x17
                                       else
                                         if («nonEmpty» x15).label ≠ 0 then
                                           let x17 : T := «at» x15 (leaf 0);
                                           if (Const.eq (Const.label x17) (leaf 1)).label ≠ 0 then
                                             let x18 : T := Const.child x17 (leaf 0);
                                             Const.child x18 (leaf 2)
                                           else
                                             leaf 0
                                         else
                                           leaf 0);
                       let x17 : T := «allTrue»
                         (Const.foldr
                           (α := T)
                           (β := List T)
                           (fun (x17 : T) (x18 : List T) =>
                             ((«and»
                               (Const.eq (Const.arity x17) (leaf 2))
                               (let x19 : T := «clauseCtor» x0 x17;
                                if (Const.eq (Const.label x19) (leaf 1)).label ≠ 0 then
                                  let x20 : T := Const.child x19 (leaf 0);
                                  Const.equal (Const.child x20 (leaf 2)) x16
                                else
                                  leaf 0)) ::
                               x18))
                           ([] : List T)
                           x12);
                       let x18 : List
                         T := Const.foldr
                         (α := T)
                         (β := List T)
                         (fun (x18 : T) (x19 : List T) =>
                           ((Const.child («get» x18) (leaf 0)) :: x19))
                         ([] : List T)
                         x15;
                       let x19 : T := «or»
                         x11
                         («allTrue»
                           (Const.foldr
                             (α := T)
                             (β := List T)
                             (fun (x19 : T) (x20 : List T) =>
                               ((«isSome» («indexOf» (Const.child x19 (leaf 0)) x18)) :: x20))
                             ([] : List T)
                             («ctorsOf» x16 x0)));
                       if («and» x17 x19).label ≠ 0 then
                         let x20 : T := «length» x12;
                         «testChain»
                           x4
                           (Const.foldr
                             (α := T)
                             (β := T × List T)
                             (fun (x21 : T) (x22 : T × List T) =>
                               let x23 : T := Const.sub (Const.sub x20 (leaf 1)) (x22).1;
                               (Const.add (x22).1 (leaf 1),
                                 ((Const.node
                                   (leaf 0)
                                   (x21 ::
                                     ((«get» («at» x15 x23)) :: («single» («at» x13 x23))))) ::
                                   (x22).2)))
                             (leaf 0, ([] : List T))
                             x12).2
                           x14
                           x5
                       else
                         «nothing»
                     else
                       «nothing»
                   else
                     «nothing»);
    x6

def «caseField» :=
  fun (x0 : T) (_ : T) (x2 : T) (x3 : T) =>
    let x4 : T := «sLet» x2 «aT» («sx3» «aChild» «aS» («numAtom» x0)) x3;
    x4

def «caseRest» :=
  fun (x0 : T) (_ : T) (x2 : T) (x3 : T) =>
    let x4 : T := «sLet»
      x2
      («sList» «aT»)
      («sDrop» «aT» («sx2» «aChildren» «aS») x0)
      x3;
    x4

def «expandCase» :=
  fun (x0 : List T) (x1 : T) (x2 : List (T × (List T → T))) =>
    let x3 : T := (let x3 : T := «rrAt» x2 (leaf 1) x0;
                   let x4 : T := «clauseChain»
                     x0
                     «nothing»
                     («drop» (leaf 2) (Const.children x1))
                     («argsOf» x2 (leaf 2) x0)
                     «aS»
                     («bindWith» «caseField» «caseRest»);
                   let x5 : T := x3;
                   if (Const.eq (Const.label x5) (leaf 1)).label ≠ 0 then
                     let x6 : T := Const.child x5 (leaf 0);
                     let x7 : T := x4;
                     if (Const.eq (Const.label x7) (leaf 1)).label ≠ 0 then
                       let x8 : T := Const.child x7 (leaf 0); «just» («sLet» «aS» «aT» x6 x8)
                     else
                       «nothing»
                   else
                     «nothing»);
    x3

def «pTy» :=
  fun (x0 : T) => let x1 : T := «sProd» «aT» («sArrow» «aUnit» x0); x1

def «forced» :=
  fun (x0 : T) => let x1 : T := «sx2» («sx2» «aSnd» x0) «aUnitV»; x1

def «nthP» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «sx6»
      «aLcase»
      («pTy» x0)
      («pTy» x0)
      («sDrop» («pTy» x0) «aRs» x2)
      («sx3» «aPair» «aZero» («sLam1» «aU» «aUnit» x1))
      («sLam2» «aH» («pTy» x0) «aTl» («sList» («pTy» x0)) «aH»);
    x3

def «cataField» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) (x5 : T) (x6 : T) =>
    let x7 : T := (if («named» x4 x0).label ≠ 0 then
      «sLet» x5 x1 («forced» («nthP» x1 x2 x3)) x6
    else
      «sLet» x5 «aT» («sx3» «aChild» «aO» («numAtom» x3)) x6);
    x7

def «cataRest» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) (x5 : T) =>
    let x6 : T := (if («named» x3 x0).label ≠ 0 then
      «sLet»
        x4
        («sList» x1)
        («sx6»
          «aFoldr»
          («pTy» x1)
          («sList» x1)
          («sLam2»
            «aP»
            («pTy» x1)
            «aA»
            («sList» x1)
            («sx3» «aCons» («forced» «aP») «aA»))
          («sx2» «aNil» x1)
          («sDrop» («pTy» x1) «aRs» x2))
        x5
    else
      «sLet»
        x4
        («sList» «aT»)
        («sDrop» «aT» («sx2» «aChildren» «aO») x2)
        x5);
    x6

def «cataStep» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «sLam2»
      «aL»
      «aT»
      «aRs»
      («sList» («pTy» x0))
      («sLet»
        «aO»
        «aT»
        («sx3»
          «aNode»
          «aL»
          («sx6»
            «aFoldr»
            («pTy» x0)
            («sList» «aT»)
            («sLam2»
              «aP»
              («pTy» x0)
              «aA»
              («sList» «aT»)
              («sx3» «aCons» («sx2» «aFst» «aP») «aA»))
            («sx2» «aNil» «aT»)
            «aRs»))
        («sx3» «aPair» «aO» («sLam1» «aU» «aUnit» x1)));
    x2

def «expandCata» :=
  fun (x0 : List T) (x1 : T) (x2 : List (T × (List T → T))) =>
    let x3 : T := (let x3 : List T := Const.children x1;
                   let x4 : T := «nameOf» («at» x3 (leaf 1));
                   let x5 : T := «at» x3 (leaf 2);
                   let x6 : T := (if («and»
                     («isAtom» («at» x3 (leaf 1)))
                     («isData» x4 x0)).label ≠ 0 then
                     «clauseChain»
                       x0
                       («just» x4)
                       («drop» (leaf 4) x3)
                       («argsOf» x2 (leaf 4) x0)
                       «aO»
                       («bindWith»
                         («cataField» x4 x5 («defaultOf» («expandAliases» x0 x5)))
                         («cataRest» x4 x5))
                   else
                     «nothing»);
                   let x7 : T := «rrAt» x2 (leaf 3) x0;
                   if (Const.eq (Const.label x7) (leaf 1)).label ≠ 0 then
                     let x8 : T := Const.child x7 (leaf 0);
                     let x9 : T := x6;
                     if (Const.eq (Const.label x9) (leaf 1)).label ≠ 0 then
                       let x10 : T := Const.child x9 (leaf 0);
                       «just» («forced» («sx4» «aFold» («pTy» x5) («cataStep» x5 x10) x8))
                     else
                       «nothing»
                   else
                     «nothing»);
    x3

def «expandExpr» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := ((Const.fold
      (α := T × (Unit → T × (List T → T)))
      (fun (x2 : T) (x3 : List (T × (Unit → T × (List T → T)))) =>
        let x4 : T := Const.node
          x2
          (Const.foldr
            (α := T × (Unit → T × (List T → T)))
            (β := List T)
            (fun (x4 : T × (Unit → T × (List T → T))) (x5 : List T) =>
              ((x4).1 :: x5))
            ([] : List T)
            x3);
        (x4,
          fun (_ : Unit) =>
            if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
              let x6 : List
                T := Const.iter
                (α := List T)
                (fun (x6 : List T) =>
                  Const.lcase
                    (α := T)
                    (β := List T)
                    x6
                    ([] : List T)
                    (fun (_ : T) (x8 : List T) => x8))
                (Const.children x4)
                (leaf 0);
              («atom» x6, fun (_ : List T) => «just» («atom» x6))
            else
              if (Const.eq (Const.label x4) (leaf 2)).label ≠ 0 then
                let x6 : List
                  (T ×
                    (List T →
                      T)) := Const.foldr
                  (α := T × (Unit → T × (List T → T)))
                  (β := List (T × (List T → T)))
                  (fun (x6 : T × (Unit → T × (List T → T)))
                     (x7 : List (T × (List T → T))) =>
                    (((x6).2 ()) :: x7))
                  ([] : List (T × (List T → T)))
                  (Const.iter
                    (α := List (T × (Unit → T × (List T → T))))
                    (fun (x6 : List (T × (Unit → T × (List T → T)))) =>
                      Const.lcase
                        (α := T × (Unit → T × (List T → T)))
                        (β := List (T × (Unit → T × (List T → T))))
                        x6
                        ([] : List (T × (Unit → T × (List T → T))))
                        (fun (_ : T × (Unit → T × (List T → T)))
                           (x8 : List (T × (Unit → T × (List T → T)))) =>
                          x8))
                    x3
                    (leaf 0));
                let x7 : T := «lst» («rrTrees» x6);
                (x7,
                  fun (x8 : List T) =>
                    let x9 : T := «at» (Const.children x7) (leaf 0);
                    let x10 : T := Const.arity x7;
                    if («and»
                      («named» x9 «kwCase»)
                      (Const.lt (leaf 2) x10)).label ≠ 0 then
                      «expandCase» x8 x7 x6
                    else
                      if («and»
                        («named» x9 «kwCata»)
                        (Const.lt (leaf 4) x10)).label ≠ 0 then
                        «expandCata» x8 x7 x6
                      else
                        let x11 : T := «allSome» («rrApply» x6 x8);
                        if (Const.eq (Const.label x11) (leaf 1)).label ≠ 0 then
                          let x12 : T := Const.child x11 (leaf 0);
                          «just» («lst» (Const.children x12))
                        else
                          «nothing»)
              else
                («sx0», fun (_ : List T) => «just» «sx0»)))
      x1).2
      ()).2
      x0;
    x2

def «ctorDecl» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := (let x3 : T := x2;
                   if (Const.eq (Const.label x3) (leaf 2)).label ≠ 0 then
                     let x4 : List
                       T := Const.iter
                       (α := List T)
                       (fun (x4 : List T) =>
                         Const.lcase
                           (α := T)
                           (β := List T)
                           x4
                           ([] : List T)
                           (fun (_ : T) (x6 : List T) => x6))
                       (Const.children x3)
                       (leaf 0);
                     let x5 : List T := «tail» x4;
                     let x6 : T := «length» x5;
                     let x7 : T := «and»
                       (Const.lt (leaf 1) x6)
                       («named» («at» x5 (Const.sub x6 (leaf 2))) «kwAmp»);
                     let x8 : List
                       T := (if (x7).label ≠ 0 then «dropLast» («dropLast» x5) else x5);
                     let x9 : T := «length» x8;
                     let x10 : List
                       T := (Const.foldr
                       (α := T)
                       (β := T × List T)
                       (fun (_ : T) (x11 : T × List T) =>
                         (Const.add (x11).1 (leaf 1),
                           ((«sx2»
                             («fieldAtom» (Const.sub (Const.sub x9 (leaf 1)) (x11).1))
                             «aT») ::
                             (x11).2)))
                       (leaf 0, ([] : List T))
                       x8).2;
                     let x11 : T := (Const.foldr
                       (α := T)
                       (β := T × T)
                       (fun (_ : T) (x12 : T × T) =>
                         (Const.add (x12).1 (leaf 1),
                           «sx3»
                             «aCons»
                             («fieldAtom» (Const.sub (Const.sub x9 (leaf 1)) (x12).1))
                             (x12).2))
                       (leaf 0, if (x7).label ≠ 0 then «aRest» else «sx2» «aNil» «aT»)
                       x8).2;
                     let x12 : List
                       T := (if (x7).label ≠ 0 then
                       «append» x10 («single» («sx2» «aRest» («sList» «aT»)))
                     else
                       x10);
                     let x13 : T := «sx3» «aNode» («numAtom» x1) x11;
                     if («isAtom» («at» x4 (leaf 0))).label ≠ 0 then
                       «just»
                         («node2»
                           (leaf 0)
                           («ctorD»
                             («nameOf» («at» x4 (leaf 0)))
                             x1
                             x0
                             (Const.node (leaf 0) x8)
                             x7
                             (if (x7).label ≠ 0 then «at» x5 (Const.sub x6 (leaf 1)) else leaf 0))
                           («sx3»
                             «aDef»
                             («at» x4 (leaf 0))
                             (if («nonEmpty» x12).label ≠ 0 then
                               «sx3» «aLam» («lst» x12) x13
                             else
                               x13)))
                     else
                       «nothing»
                   else
                     «nothing»);
    x3

def «dataDecl» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : List T := Const.children x0;
                   let x2 : T := «nameOf» («at» x1 (leaf 1));
                   let x3 : List T := «drop» (leaf 2) x1;
                   let x4 : T := «length» x3;
                   let x5 : T := «allSome»
                     (Const.foldr
                       (α := T)
                       (β := T × List T)
                       (fun (x5 : T) (x6 : T × List T) =>
                         (Const.add (x6).1 (leaf 1),
                           ((«ctorDecl» x2 (Const.sub (Const.sub x4 (leaf 1)) (x6).1) x5) ::
                             (x6).2)))
                       (leaf 0, ([] : List T))
                       x3).2;
                   if (Const.eq (Const.label x5) (leaf 1)).label ≠ 0 then
                     let x6 : T := Const.child x5 (leaf 0);
                     if («isAtom» («at» x1 (leaf 1))).label ≠ 0 then
                       let x7 : List T := Const.children x6;
                       «just»
                         («node2»
                           (leaf 0)
                           (Const.node
                             (leaf 0)
                             ((«dataD» x2) ::
                               (Const.foldr
                                 (α := T)
                                 (β := List T)
                                 (fun (x8 : T) (x9 : List T) => ((Const.child x8 (leaf 0)) :: x9))
                                 ([] : List T)
                                 x7)))
                           (Const.node
                             (leaf 0)
                             ((«sx3» «aDeftype» («at» x1 (leaf 1)) «aT») ::
                               (Const.foldr
                                 (α := T)
                                 (β := List T)
                                 (fun (x8 : T) (x9 : List T) => ((Const.child x8 (leaf 1)) :: x9))
                                 ([] : List T)
                                 x7))))
                     else
                       «nothing»
                   else
                     «nothing»);
    x1

def «xpFail» := (leaf 0, (([] : List T), ([] : List T)))

def «xpStep» :=
  fun (x0 : T × (List T × List T)) (x1 : T) =>
    let x2 : T ×
      (List T ×
        List
          T) := (if («and» (x0).1 («isList» x1)).label ≠ 0 then
      let x2 : List T := ((x0).2).1;
      let x3 : List T := ((x0).2).2;
      let x4 : List T := Const.children x1;
      let x5 : T := «at» x4 (leaf 0);
      let x6 : T := Const.arity x1;
      if («named» x5 «kwData»).label ≠ 0 then
        let x7 : T := «dataDecl» x1;
        if (Const.eq (Const.label x7) (leaf 1)).label ≠ 0 then
          let x8 : T := Const.child x7 (leaf 0);
          (leaf 1,
            («append» x2 (Const.children (Const.child x8 (leaf 0))),
              «append» («reverse» (Const.children (Const.child x8 (leaf 1)))) x3))
        else
          «xpFail»
      else
        if («and» («named» x5 «kwDefn») (Const.eq x6 (leaf 5))).label ≠ 0 then
          let x7 : T := «expandExpr» x2 («at» x4 (leaf 4));
          if (Const.eq (Const.label x7) (leaf 1)).label ≠ 0 then
            let x8 : T := Const.child x7 (leaf 0);
            let x9 : T := «sLet» «aR» («at» x4 (leaf 3)) x8 «aR»;
            (leaf 1,
              (x2,
                ((«sx3»
                  «aDef»
                  («at» x4 (leaf 1))
                  (if (Const.eq
                    (Const.arity («at» x4 (leaf 2)))
                    (leaf 0)).label ≠ 0 then
                    x9
                  else
                    «sx3» «aLam» («at» x4 (leaf 2)) x9)) ::
                  x3)))
          else
            «xpFail»
        else
          if («and» («named» x5 «kwDef») (Const.eq x6 (leaf 3))).label ≠ 0 then
            let x7 : T := «expandExpr» x2 («at» x4 (leaf 2));
            if (Const.eq (Const.label x7) (leaf 1)).label ≠ 0 then
              let x8 : T := Const.child x7 (leaf 0);
              (leaf 1, (x2, ((«sx3» «aDef» («at» x4 (leaf 1)) x8) :: x3)))
            else
              «xpFail»
          else
            if («and»
              («named» x5 «kwDeftype»)
              (Const.eq x6 (leaf 3))).label ≠ 0 then
              (leaf 1,
                («append»
                  x2
                  («single»
                    («aliasD»
                      («nameOf» («at» x4 (leaf 1)))
                      («expandAliases» x2 («at» x4 (leaf 2))))),
                  (x1 :: x3)))
            else
              if («and»
                («named» x5 «kwDefnum»)
                (Const.eq x6 (leaf 3))).label ≠ 0 then
                (leaf 1, (x2, (x1 :: x3)))
              else
                «xpFail»
    else
      «xpFail»);
    x2

def «expandProgram» :=
  fun (x0 : List T) =>
    let x1 : T := (let x1 : T ×
                     (List T ×
                       List
                         T) := Const.foldr
                     (α := T)
                     (β := (T × (List T × List T)) → T × (List T × List T))
                     (fun (x1 : T)
                        (x2 : (T × (List T × List T)) → T × (List T × List T))
                        (x3 : T × (List T × List T)) =>
                       x2 («xpStep» x3 x1))
                     (fun (x1 : T × (List T × List T)) => x1)
                     x0
                     (leaf 1, (([] : List T), ([] : List T)));
                   if ((x1).1).label ≠ 0 then
                     «just» (Const.node (leaf 0) («reverse» ((x1).2).2))
                   else
                     «nothing»);
    x1

def «compileWith» :=
  fun (x0 : T → T) (x1 : T) =>
    let x2 : T := «readSExps» (Const.children x1);
    let x3 : T := (if («isSome» x2).label ≠ 0 then
      «expandProgram» (Const.children («get» x2))
    else
      «none»);
    let x4 : T := (if («isSome» x3).label ≠ 0 then
      «readProgram» (Const.children («get» x3))
    else
      «none»);
    if («isSome» x4).label ≠ 0 then
      if («isSome»
        («checkProgram»
          (Const.children (Const.child («get» x4) (leaf 0))))).label ≠ 0 then
        x0 («get» x4)
      else
        Const.node (leaf 0) ([] : List T)
    else
      Const.node (leaf 0) ([] : List T)

def «compile» := fun (x0 : T) => «compileWith» «image» x0

def «main» := fun (x0 : T) => «compile» x0

def «txt» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: ([] : List T)))

def «cat» := fun (x0 : List T) => Const.node (leaf 1) x0

def «nest» :=
  fun (x0 : T) => Const.node (leaf 2) (x0 :: ([] : List T))

def «line» := Const.node (leaf 3) ([] : List T)

def «grp» := fun (x0 : T) => Const.node (leaf 4) (x0 :: ([] : List T))

def «align» :=
  fun (x0 : T) => Const.node (leaf 5) (x0 :: ([] : List T))

def «cols» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x1 : T) (x2 : T) =>
        if («and»
          (Const.lt (leaf 127) x1)
          (Const.lt x1 (leaf 192))).label ≠ 0 then
          x2
        else
          Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «text» :=
  fun (x0 : List T) =>
    let x1 : T := «txt» («cols» x0) (Const.node (leaf 0) x0); x1

def «cat2» :=
  fun (x0 : T) (x1 : T) => let x2 : T := «cat» (x0 :: («single» x1)); x2

def «cat3» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «cat» (x0 :: (x1 :: («single» x2))); x3

def «cat5» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : T := «cat» (x0 :: (x1 :: (x2 :: (x3 :: («single» x4))))); x5

def «indented» :=
  fun (x0 : T) => let x1 : T := «nest» («cat2» «line» x0); x1

def «joinWith» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := «cat»
      (Const.lcase
        (α := T)
        (β := List T)
        x1
        ([] : List T)
        (fun (x2 : T) (x3 : List T) =>
          (x2 ::
            (Const.foldr
              (α := T)
              (β := List T)
              (fun (x4 : T) (x5 : List T) => (x0 :: (x4 :: x5)))
              ([] : List T)
              x3))));
    x2

def «tLp» := «text» (Const.children (mk 0 [leaf 40]))

def «tRp» := «text» (Const.children (mk 0 [leaf 41]))

def «tComma» := «text» (Const.children (mk 0 [leaf 44]))

def «tColon» :=
  «text» (Const.children (mk 0 [leaf 32, leaf 58, leaf 32]))

def «tUnder» := «text» (Const.children (mk 0 [leaf 95]))

def «tFun» :=
  «text» (Const.children (mk 0 [leaf 102, leaf 117, leaf 110, leaf 32]))

def «tDoubleArrow» :=
  «text» (Const.children (mk 0 [leaf 32, leaf 61, leaf 62]))

def «tT» := «text» (Const.children (mk 0 [leaf 84]))

def «tUnitTy» :=
  «text» (Const.children (mk 0 [leaf 85, leaf 110, leaf 105, leaf 116]))

def «tTimes» :=
  «text» (Const.children (mk 0 [leaf 32, leaf 195, leaf 151]))

def «tTo» :=
  «text» (Const.children (mk 0 [leaf 32, leaf 226, leaf 134, leaf 146]))

def «tList» :=
  «text» (Const.children (mk 0 [leaf 76, leaf 105, leaf 115, leaf 116]))

def «tLet» :=
  «text» (Const.children (mk 0 [leaf 108, leaf 101, leaf 116, leaf 32]))

def «tSemi» := «text» (Const.children (mk 0 [leaf 59]))

def «tUnitV» := «text» (Const.children (mk 0 [leaf 40, leaf 41]))

def «tDot1» :=
  «text» (Const.children (mk 0 [leaf 41, leaf 46, leaf 49]))

def «tDot2» :=
  «text» (Const.children (mk 0 [leaf 41, leaf 46, leaf 50]))

def «tIf» :=
  «text» (Const.children (mk 0 [leaf 105, leaf 102, leaf 32, leaf 40]))

def «tThen» :=
  «text»
    (Const.children
      (mk 0 [leaf 41,
        leaf 46,
        leaf 108,
        leaf 97,
        leaf 98,
        leaf 101,
        leaf 108,
        leaf 32,
        leaf 226,
        leaf 137,
        leaf 160,
        leaf 32,
        leaf 48,
        leaf 32,
        leaf 116,
        leaf 104,
        leaf 101,
        leaf 110]))

def «tElse» :=
  «text»
    (Const.children (mk 0 [leaf 101, leaf 108, leaf 115, leaf 101]))

def «tFold» :=
  «text»
    (Const.children
      (mk 0 [leaf 67,
        leaf 111,
        leaf 110,
        leaf 115,
        leaf 116,
        leaf 46,
        leaf 102,
        leaf 111,
        leaf 108,
        leaf 100]))

def «tIter» :=
  «text»
    (Const.children
      (mk 0 [leaf 67,
        leaf 111,
        leaf 110,
        leaf 115,
        leaf 116,
        leaf 46,
        leaf 105,
        leaf 116,
        leaf 101,
        leaf 114]))

def «tFoldr» :=
  «text»
    (Const.children
      (mk 0 [leaf 67,
        leaf 111,
        leaf 110,
        leaf 115,
        leaf 116,
        leaf 46,
        leaf 102,
        leaf 111,
        leaf 108,
        leaf 100,
        leaf 114]))

def «tLcase» :=
  «text»
    (Const.children
      (mk 0 [leaf 67,
        leaf 111,
        leaf 110,
        leaf 115,
        leaf 116,
        leaf 46,
        leaf 108,
        leaf 99,
        leaf 97,
        leaf 115,
        leaf 101]))

def «tConstDot» :=
  «text»
    (Const.children
      (mk 0 [leaf 67, leaf 111, leaf 110, leaf 115, leaf 116, leaf 46]))

def «tAlpha» := «text» (Const.children (mk 0 [leaf 206, leaf 177]))

def «tBeta» := «text» (Const.children (mk 0 [leaf 206, leaf 178]))

def «tColonEq» :=
  «text» (Const.children (mk 0 [leaf 32, leaf 58, leaf 61, leaf 32]))

def «tNilLp» :=
  «text»
    (Const.children
      (mk 0 [leaf 40,
        leaf 91,
        leaf 93,
        leaf 32,
        leaf 58,
        leaf 32,
        leaf 76,
        leaf 105,
        leaf 115,
        leaf 116,
        leaf 32]))

def «tConsOp» :=
  «text» (Const.children (mk 0 [leaf 32, leaf 58, leaf 58]))

def «tLeaf» :=
  «text»
    (Const.children
      (mk 0 [leaf 108, leaf 101, leaf 97, leaf 102, leaf 32]))

def «tMk» :=
  «text» (Const.children (mk 0 [leaf 109, leaf 107, leaf 32]))

def «tSpLb» := «text» (Const.children (mk 0 [leaf 32, leaf 91]))

def «tRb» := «text» (Const.children (mk 0 [leaf 93]))

def «tLg» := «text» (Const.children (mk 0 [leaf 194, leaf 171]))

def «tRg» := «text» (Const.children (mk 0 [leaf 194, leaf 187]))

def «tDef» :=
  «text»
    (Const.children
      (mk 0 [leaf 100, leaf 101, leaf 102, leaf 32, leaf 194, leaf 171]))

def «tAssign» :=
  «text»
    (Const.children
      (mk 0 [leaf 194, leaf 187, leaf 32, leaf 58, leaf 61]))

def «tHeader» :=
  «text»
    (Const.children
      (mk 0 [leaf 109,
        leaf 111,
        leaf 100,
        leaf 117,
        leaf 108,
        leaf 101,
        leaf 10,
        leaf 10,
        leaf 112,
        leaf 117,
        leaf 98,
        leaf 108,
        leaf 105,
        leaf 99,
        leaf 32,
        leaf 105,
        leaf 109,
        leaf 112,
        leaf 111,
        leaf 114,
        leaf 116,
        leaf 32,
        leaf 71,
        leaf 101,
        leaf 98,
        leaf 46,
        leaf 80,
        leaf 114,
        leaf 111,
        leaf 116,
        leaf 111,
        leaf 116,
        leaf 121,
        leaf 112,
        leaf 101,
        leaf 115,
        leaf 46,
        leaf 75,
        leaf 101,
        leaf 114,
        leaf 110,
        leaf 101,
        leaf 108,
        leaf 46,
        leaf 82,
        leaf 101,
        leaf 97,
        leaf 100,
        leaf 101,
        leaf 114,
        leaf 10,
        leaf 10,
        leaf 47,
        leaf 45,
        leaf 33,
        leaf 32,
        leaf 71,
        leaf 101,
        leaf 110,
        leaf 101,
        leaf 114,
        leaf 97,
        leaf 116,
        leaf 101,
        leaf 100,
        leaf 32,
        leaf 102,
        leaf 114,
        leaf 111,
        leaf 109,
        leaf 32,
        leaf 97,
        leaf 32,
        leaf 71,
        leaf 101,
        leaf 98,
        leaf 32,
        leaf 112,
        leaf 114,
        leaf 111,
        leaf 103,
        leaf 114,
        leaf 97,
        leaf 109,
        leaf 32,
        leaf 98,
        leaf 121,
        leaf 32,
        leaf 96,
        leaf 98,
        leaf 111,
        leaf 111,
        leaf 116,
        leaf 115,
        leaf 116,
        leaf 114,
        leaf 97,
        leaf 112,
        leaf 47,
        leaf 115,
        leaf 116,
        leaf 97,
        leaf 103,
        leaf 101,
        leaf 49,
        leaf 47,
        leaf 108,
        leaf 101,
        leaf 97,
        leaf 110,
        leaf 46,
        leaf 103,
        leaf 101,
        leaf 98,
        leaf 96,
        leaf 46,
        leaf 32,
        leaf 45,
        leaf 47,
        leaf 10,
        leaf 10,
        leaf 64,
        leaf 91,
        leaf 101,
        leaf 120,
        leaf 112,
        leaf 111,
        leaf 115,
        leaf 101,
        leaf 93,
        leaf 32,
        leaf 112,
        leaf 117,
        leaf 98,
        leaf 108,
        leaf 105,
        leaf 99,
        leaf 32,
        leaf 115,
        leaf 101,
        leaf 99,
        leaf 116,
        leaf 105,
        leaf 111,
        leaf 110,
        leaf 10,
        leaf 10,
        leaf 111,
        leaf 112,
        leaf 101,
        leaf 110,
        leaf 32,
        leaf 71,
        leaf 101,
        leaf 98,
        leaf 46,
        leaf 75,
        leaf 101,
        leaf 114,
        leaf 110,
        leaf 101,
        leaf 108,
        leaf 10,
        leaf 111,
        leaf 112,
        leaf 101,
        leaf 110,
        leaf 32,
        leaf 71,
        leaf 101,
        leaf 98,
        leaf 46,
        leaf 75,
        leaf 101,
        leaf 114,
        leaf 110,
        leaf 101,
        leaf 108,
        leaf 32,
        leaf 114,
        leaf 101,
        leaf 110,
        leaf 97,
        leaf 109,
        leaf 105,
        leaf 110,
        leaf 103,
        leaf 32,
        leaf 84,
        leaf 114,
        leaf 101,
        leaf 101,
        leaf 32,
        leaf 226,
        leaf 134,
        leaf 146,
        leaf 32,
        leaf 84,
        leaf 10,
        leaf 10,
        leaf 110,
        leaf 97,
        leaf 109,
        leaf 101,
        leaf 115,
        leaf 112,
        leaf 97,
        leaf 99,
        leaf 101,
        leaf 32,
        leaf 71,
        leaf 101,
        leaf 98,
        leaf 66,
        leaf 111,
        leaf 111,
        leaf 116]))

def «tFooter» :=
  «text»
    (Const.children
      (mk 0 [leaf 10,
        leaf 10,
        leaf 101,
        leaf 110,
        leaf 100,
        leaf 32,
        leaf 71,
        leaf 101,
        leaf 98,
        leaf 66,
        leaf 111,
        leaf 111,
        leaf 116,
        leaf 10,
        leaf 10,
        leaf 101,
        leaf 110,
        leaf 100,
        leaf 10]))

def «wOf» :=
  fun (x0 : (T × (T × T)) × (T → T → T → (T × List T) → T × List T)) =>
    let x1 : T := ((x0).1).1; x1

def «hbOf» :=
  fun (x0 : (T × (T × T)) × (T → T → T → (T × List T) → T × List T)) =>
    let x1 : T := (((x0).1).2).1; x1

def «ldOf» :=
  fun (x0 : (T × (T × T)) × (T → T → T → (T × List T) → T × List T)) =>
    let x1 : T := (((x0).1).2).2; x1

def «ms» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T × (T × T) := (x0, (x1, x2)); x3

def «revOnto» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T → List T)
      (fun (x2 : T) (x3 : List T → List T) (x4 : List T) => x3 (x2 :: x4))
      (fun (x2 : List T) => x2)
      x0
      x1;
    x2

def «catWP» :=
  fun (x0 : (T × (T × T)) × (T → T → T → (T × List T) → T × List T))
    (x1 : (T × (T × T)) × (T → T → T → (T × List T) → T × List T)) =>
    let x2 : (T × (T × T)) ×
      (T →
        T →
          T →
            (T × List T) →
              T ×
                List
                  T) := («ms»
      (Const.add («wOf» x0) («wOf» x1))
      («or» («hbOf» x0) («hbOf» x1))
      (if («hbOf» x0).label ≠ 0 then
        «ldOf» x0
      else
        Const.add («wOf» x0) («ldOf» x1)),
      fun (x2 : T) (x3 : T) (x4 : T) (x5 : T × List T) =>
        (x1).2
          x2
          x3
          x4
          ((x0).2
            x2
            x3
            (Const.add («ldOf» x1) (if («hbOf» x1).label ≠ 0 then leaf 0 else x4))
            x5));
    x2

def «layout» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : (T × (T × T)) ×
                     (T →
                       T →
                         T →
                           (T × List T) →
                             T ×
                               List
                                 T) := (Const.fold
                     (α := T ×
                       (Unit → (T × (T × T)) × (T → T → T → (T × List T) → T × List T)))
                     (fun (x1 : T)
                        (x2 : List
                          (T ×
                            (Unit → (T × (T × T)) × (T → T → T → (T × List T) → T × List T)))) =>
                       let x3 : T := Const.node
                         x1
                         (Const.foldr
                           (α := T ×
                             (Unit → (T × (T × T)) × (T → T → T → (T × List T) → T × List T)))
                           (β := List T)
                           (fun (x3 : T ×
                                (Unit → (T × (T × T)) × (T → T → T → (T × List T) → T × List T)))
                              (x4 : List T) =>
                             ((x3).1 :: x4))
                           ([] : List T)
                           x2);
                       (x3,
                         fun (_ : Unit) =>
                           if (Const.eq (Const.label x3) (leaf 0)).label ≠ 0 then
                             let x5 : T := Const.child x3 (leaf 0);
                             let x6 : T := Const.child x3 (leaf 1);
                             («ms» x5 (leaf 0) x5,
                               fun (_ : T) (_ : T) (_ : T) (x10 : T × List T) =>
                                 (Const.add (x10).1 x5, «revOnto» (Const.children x6) (x10).2))
                           else
                             if (Const.eq (Const.label x3) (leaf 1)).label ≠ 0 then
                               let x5 : List
                                 ((T × (T × T)) ×
                                   (T →
                                     T →
                                       T →
                                         (T × List T) →
                                           T ×
                                             List
                                               T)) := Const.foldr
                                 (α := T ×
                                   (Unit → (T × (T × T)) × (T → T → T → (T × List T) → T × List T)))
                                 (β := List
                                   ((T × (T × T)) × (T → T → T → (T × List T) → T × List T)))
                                 (fun (x5 : T ×
                                      (Unit →
                                        (T × (T × T)) × (T → T → T → (T × List T) → T × List T)))
                                    (x6 : List
                                      ((T × (T × T)) × (T → T → T → (T × List T) → T × List T))) =>
                                   (((x5).2 ()) :: x6))
                                 ([] : List ((T × (T × T)) ×
                                   (T → T → T → (T × List T) → T × List T)))
                                 (Const.iter
                                   (α := List
                                     (T ×
                                       (Unit →
                                         (T × (T × T)) × (T → T → T → (T × List T) → T × List T))))
                                   (fun (x5 : List
                                        (T ×
                                          (Unit →
                                            (T × (T × T)) ×
                                              (T → T → T → (T × List T) → T × List T)))) =>
                                     Const.lcase
                                       (α := T ×
                                         (Unit →
                                           (T × (T × T)) × (T → T → T → (T × List T) → T × List T)))
                                       (β := List
                                         (T ×
                                           (Unit →
                                             (T × (T × T)) ×
                                               (T → T → T → (T × List T) → T × List T))))
                                       x5
                                       ([] : List (T ×
                                         (Unit →
                                           (T × (T × T)) ×
                                             (T → T → T → (T × List T) → T × List T))))
                                       (fun (_ : T ×
                                            (Unit →
                                              (T × (T × T)) ×
                                                (T → T → T → (T × List T) → T × List T)))
                                          (x7 : List
                                            (T ×
                                              (Unit →
                                                (T × (T × T)) ×
                                                  (T → T → T → (T × List T) → T × List T)))) =>
                                         x7))
                                   x2
                                   (leaf 0));
                               Const.foldr
                                 (α := (T × (T × T)) × (T → T → T → (T × List T) → T × List T))
                                 (β := (T × (T × T)) × (T → T → T → (T × List T) → T × List T))
                                 «catWP»
                                 («ms» (leaf 0) (leaf 0) (leaf 0),
                                   fun (_ : T) (_ : T) (_ : T) (x9 : T × List T) => x9)
                                 x5
                             else
                               if (Const.eq (Const.label x3) (leaf 2)).label ≠ 0 then
                                 let x5 : (T × (T × T)) ×
                                   (T →
                                     T →
                                       T →
                                         (T × List T) →
                                           T ×
                                             List
                                               T) := (Const.lcase
                                   (α := T ×
                                     (Unit →
                                       (T × (T × T)) × (T → T → T → (T × List T) → T × List T)))
                                   (β := T ×
                                     (Unit →
                                       (T × (T × T)) × (T → T → T → (T × List T) → T × List T)))
                                   (Const.iter
                                     (α := List
                                       (T ×
                                         (Unit →
                                           (T × (T × T)) ×
                                             (T → T → T → (T × List T) → T × List T))))
                                     (fun (x5 : List
                                          (T ×
                                            (Unit →
                                              (T × (T × T)) ×
                                                (T → T → T → (T × List T) → T × List T)))) =>
                                       Const.lcase
                                         (α := T ×
                                           (Unit →
                                             (T × (T × T)) ×
                                               (T → T → T → (T × List T) → T × List T)))
                                         (β := List
                                           (T ×
                                             (Unit →
                                               (T × (T × T)) ×
                                                 (T → T → T → (T × List T) → T × List T))))
                                         x5
                                         ([] : List (T ×
                                           (Unit →
                                             (T × (T × T)) ×
                                               (T → T → T → (T × List T) → T × List T))))
                                         (fun (_ : T ×
                                              (Unit →
                                                (T × (T × T)) ×
                                                  (T → T → T → (T × List T) → T × List T)))
                                            (x7 : List
                                              (T ×
                                                (Unit →
                                                  (T × (T × T)) ×
                                                    (T → T → T → (T × List T) → T × List T)))) =>
                                           x7))
                                     x2
                                     (leaf 0))
                                   (leaf 0,
                                     fun (_ : Unit) =>
                                       ((leaf 0, (leaf 0, leaf 0)),
                                         fun (_ : T) (_ : T) (_ : T) (_ : T × List T) =>
                                           (leaf 0, ([] : List T))))
                                   (fun (x5 : T ×
                                        (Unit →
                                          (T × (T × T)) × (T → T → T → (T × List T) → T × List T)))
                                      (_ : List
                                        (T ×
                                          (Unit →
                                            (T × (T × T)) ×
                                              (T → T → T → (T × List T) → T × List T)))) =>
                                     x5)).2
                                   ();
                                 ((x5).1,
                                   fun (x6 : T) (x7 : T) (x8 : T) (x9 : T × List T) =>
                                     (x5).2 (Const.add x6 (leaf 2)) x7 x8 x9)
                               else
                                 if (Const.eq (Const.label x3) (leaf 3)).label ≠ 0 then
                                   («ms» (leaf 1) (leaf 1) (leaf 0),
                                     fun (x5 : T) (x6 : T) (_ : T) (x8 : T × List T) =>
                                       if (x6).label ≠ 0 then
                                         (Const.add (x8).1 (leaf 1), ((leaf 32) :: (x8).2))
                                       else
                                         (x5,
                                           «revOnto»
                                             («replicate» x5 (leaf 32))
                                             ((leaf 10) :: (x8).2)))
                                 else
                                   if (Const.eq (Const.label x3) (leaf 4)).label ≠ 0 then
                                     let x5 : (T × (T × T)) ×
                                       (T →
                                         T →
                                           T →
                                             (T × List T) →
                                               T ×
                                                 List
                                                   T) := (Const.lcase
                                       (α := T ×
                                         (Unit →
                                           (T × (T × T)) × (T → T → T → (T × List T) → T × List T)))
                                       (β := T ×
                                         (Unit →
                                           (T × (T × T)) × (T → T → T → (T × List T) → T × List T)))
                                       (Const.iter
                                         (α := List
                                           (T ×
                                             (Unit →
                                               (T × (T × T)) ×
                                                 (T → T → T → (T × List T) → T × List T))))
                                         (fun (x5 : List
                                              (T ×
                                                (Unit →
                                                  (T × (T × T)) ×
                                                    (T → T → T → (T × List T) → T × List T)))) =>
                                           Const.lcase
                                             (α := T ×
                                               (Unit →
                                                 (T × (T × T)) ×
                                                   (T → T → T → (T × List T) → T × List T)))
                                             (β := List
                                               (T ×
                                                 (Unit →
                                                   (T × (T × T)) ×
                                                     (T → T → T → (T × List T) → T × List T))))
                                             x5
                                             ([] : List (T ×
                                               (Unit →
                                                 (T × (T × T)) ×
                                                   (T → T → T → (T × List T) → T × List T))))
                                             (fun (_ : T ×
                                                  (Unit →
                                                    (T × (T × T)) ×
                                                      (T → T → T → (T × List T) → T × List T)))
                                                (x7 : List
                                                  (T ×
                                                    (Unit →
                                                      (T × (T × T)) ×
                                                        (T →
                                                          T → T → (T × List T) → T × List T)))) =>
                                               x7))
                                         x2
                                         (leaf 0))
                                       (leaf 0,
                                         fun (_ : Unit) =>
                                           ((leaf 0, (leaf 0, leaf 0)),
                                             fun (_ : T) (_ : T) (_ : T) (_ : T × List T) =>
                                               (leaf 0, ([] : List T))))
                                       (fun (x5 : T ×
                                            (Unit →
                                              (T × (T × T)) ×
                                                (T → T → T → (T × List T) → T × List T)))
                                          (_ : List
                                            (T ×
                                              (Unit →
                                                (T × (T × T)) ×
                                                  (T → T → T → (T × List T) → T × List T)))) =>
                                         x5)).2
                                       ();
                                     («ms» («wOf» x5) (leaf 0) («wOf» x5),
                                       fun (x6 : T) (x7 : T) (x8 : T) (x9 : T × List T) =>
                                         (x5).2
                                           x6
                                           («or»
                                             x7
                                             («and»
                                               (Const.lt
                                                 (Const.add (x9).1 (Const.add («wOf» x5) x8))
                                                 (leaf 101))
                                               (Const.lt
                                                 (Const.add
                                                   (Const.sub (x9).1 x6)
                                                   (Const.add («wOf» x5) x8))
                                                 (leaf 71))))
                                           x8
                                           x9)
                                   else
                                     let x5 : (T × (T × T)) ×
                                       (T →
                                         T →
                                           T →
                                             (T × List T) →
                                               T ×
                                                 List
                                                   T) := (Const.lcase
                                       (α := T ×
                                         (Unit →
                                           (T × (T × T)) × (T → T → T → (T × List T) → T × List T)))
                                       (β := T ×
                                         (Unit →
                                           (T × (T × T)) × (T → T → T → (T × List T) → T × List T)))
                                       (Const.iter
                                         (α := List
                                           (T ×
                                             (Unit →
                                               (T × (T × T)) ×
                                                 (T → T → T → (T × List T) → T × List T))))
                                         (fun (x5 : List
                                              (T ×
                                                (Unit →
                                                  (T × (T × T)) ×
                                                    (T → T → T → (T × List T) → T × List T)))) =>
                                           Const.lcase
                                             (α := T ×
                                               (Unit →
                                                 (T × (T × T)) ×
                                                   (T → T → T → (T × List T) → T × List T)))
                                             (β := List
                                               (T ×
                                                 (Unit →
                                                   (T × (T × T)) ×
                                                     (T → T → T → (T × List T) → T × List T))))
                                             x5
                                             ([] : List (T ×
                                               (Unit →
                                                 (T × (T × T)) ×
                                                   (T → T → T → (T × List T) → T × List T))))
                                             (fun (_ : T ×
                                                  (Unit →
                                                    (T × (T × T)) ×
                                                      (T → T → T → (T × List T) → T × List T)))
                                                (x7 : List
                                                  (T ×
                                                    (Unit →
                                                      (T × (T × T)) ×
                                                        (T →
                                                          T → T → (T × List T) → T × List T)))) =>
                                               x7))
                                         x2
                                         (leaf 0))
                                       (leaf 0,
                                         fun (_ : Unit) =>
                                           ((leaf 0, (leaf 0, leaf 0)),
                                             fun (_ : T) (_ : T) (_ : T) (_ : T × List T) =>
                                               (leaf 0, ([] : List T))))
                                       (fun (x5 : T ×
                                            (Unit →
                                              (T × (T × T)) ×
                                                (T → T → T → (T × List T) → T × List T)))
                                          (_ : List
                                            (T ×
                                              (Unit →
                                                (T × (T × T)) ×
                                                  (T → T → T → (T × List T) → T × List T)))) =>
                                         x5)).2
                                       ();
                                     ((x5).1,
                                       fun (_ : T) (x7 : T) (x8 : T) (x9 : T × List T) =>
                                         (x5).2 (x9).1 x7 x8 x9)))
                     x0).2
                     ();
                   Const.node
                     (leaf 0)
                     («reverse»
                       ((x1).2 (leaf 0) (leaf 0) (leaf 0) (leaf 0, ([] : List T))).2));
    x1

def «atomic» :=
  fun (x0 : T) => Const.node (leaf 0) (x0 :: ([] : List T))

def «compound» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «fn» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 2) (x0 :: (x1 :: ([] : List T)))

def «ap» :=
  fun (x0 : T) (x1 : List T) => Const.node (leaf 3) (x0 :: x1)

def «binderDocs» :=
  fun (x0 : T) =>
    let x1 : T := «joinWith»
      «line»
      (Const.foldr
        (α := T)
        (β := List T)
        (fun (x1 : T) (x2 : List T) =>
          ((«cat5»
            «tLp»
            (Const.child x1 (leaf 0))
            «tColon»
            (Const.child x1 (leaf 1))
            «tRp») ::
            x2))
        ([] : List T)
        (Const.children x0));
    x1

def «shDoc» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 0)).label ≠ 0 then
                     let x2 : T := Const.child x1 (leaf 0); x2
                   else
                     if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
                       let x2 : T := Const.child x1 (leaf 0); x2
                     else
                       if (Const.eq (Const.label x1) (leaf 2)).label ≠ 0 then
                         let x2 : T := Const.child x1 (leaf 0);
                         let x3 : T := Const.child x1 (leaf 1);
                         «grp»
                           («cat2»
                             («align»
                               («grp» («cat3» «tFun» («nest» («binderDocs» x2)) «tDoubleArrow»)))
                             («indented» x3))
                       else
                         let x2 : T := Const.child x1 (leaf 0);
                         let x3 : List
                           T := Const.iter
                           (α := List T)
                           (fun (x3 : List T) =>
                             Const.lcase
                               (α := T)
                               (β := List T)
                               x3
                               ([] : List T)
                               (fun (_ : T) (x5 : List T) => x5))
                           (Const.children x1)
                           (leaf 1);
                         «grp»
                           («cat2»
                             x2
                             («nest»
                               («cat»
                                 (Const.foldr
                                   (α := T)
                                   (β := List T)
                                   (fun (x4 : T) (x5 : List T) => («line» :: (x4 :: x5)))
                                   ([] : List T)
                                   x3)))));
    x1

def «argDoc» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 0)).label ≠ 0 then
                     let x2 : T := Const.child x1 (leaf 0); x2
                   else
                     «cat3» «tLp» («shDoc» x0) «tRp»);
    x1

def «valDoc» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 0)).label ≠ 0 then
                     let x2 : T := Const.child x1 (leaf 0); x2
                   else
                     if (Const.eq (Const.label x1) (leaf 3)).label ≠ 0 then
                       let _ : T := Const.child x1 (leaf 0);
                       let _ : List
                         T := Const.iter
                         (α := List T)
                         (fun (x3 : List T) =>
                           Const.lcase
                             (α := T)
                             (β := List T)
                             x3
                             ([] : List T)
                             (fun (_ : T) (x5 : List T) => x5))
                         (Const.children x1)
                         (leaf 1);
                       «shDoc» x0
                     else
                       «cat3» «tLp» («shDoc» x0) «tRp»);
    x1

def «opDoc» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
                     let x2 : T := Const.child x1 (leaf 0); «cat3» «tLp» x2 «tRp»
                   else
                     «shDoc» x0);
    x1

def «ktT» := Const.node (leaf 0) ([] : List T)

def «ktUnit» := Const.node (leaf 1) ([] : List T)

def «ktProd» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 2) (x0 :: (x1 :: ([] : List T)))

def «ktArrow» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 3) (x0 :: (x1 :: ([] : List T)))

def «ktList» :=
  fun (x0 : T) => Const.node (leaf 4) (x0 :: ([] : List T))

def «kt5» := Const.node (leaf 5) ([] : List T)

def «kt6» := Const.node (leaf 6) ([] : List T)

def «kt7» := Const.node (leaf 7) ([] : List T)

def «kVar» :=
  fun (x0 : T) => Const.node (leaf 8) (x0 :: ([] : List T))

def «kLam» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 9) (x0 :: (x1 :: ([] : List T)))

def «kApp» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 10) (x0 :: (x1 :: ([] : List T)))

def «kUnit» := Const.node (leaf 11) ([] : List T)

def «kPair» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 12) (x0 :: (x1 :: ([] : List T)))

def «kFst» :=
  fun (x0 : T) => Const.node (leaf 13) (x0 :: ([] : List T))

def «kSnd» :=
  fun (x0 : T) => Const.node (leaf 14) (x0 :: ([] : List T))

def «kQuote» :=
  fun (x0 : T) => Const.node (leaf 15) (x0 :: ([] : List T))

def «kIf» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    Const.node (leaf 16) (x0 :: (x1 :: (x2 :: ([] : List T))))

def «kFold» :=
  fun (x0 : T) => Const.node (leaf 17) (x0 :: ([] : List T))

def «kIter» :=
  fun (x0 : T) => Const.node (leaf 18) (x0 :: ([] : List T))

def «kNil» :=
  fun (x0 : T) => Const.node (leaf 19) (x0 :: ([] : List T))

def «kCons» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 20) (x0 :: (x1 :: ([] : List T)))

def «kFoldr» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 21) (x0 :: (x1 :: ([] : List T)))

def «kPrim» :=
  fun (x0 : T) => Const.node (leaf 22) (x0 :: ([] : List T))

def «kRef» :=
  fun (x0 : T) => Const.node (leaf 23) (x0 :: ([] : List T))

def «kLcase» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 24) (x0 :: (x1 :: ([] : List T)))

def «orList» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T → List T)
      (fun (x2 : T) (x3 : List T → List T) (x4 : List T) =>
        Const.lcase
          (α := T)
          (β := List T)
          x4
          (x2 :: (x3 ([] : List T)))
          (fun (x5 : T) (x6 : List T) => ((«or» x2 x5) :: (x3 x6))))
      (fun (x2 : List T) => x2)
      x0
      x1;
    x2

def «closedSh» :=
  fun (x0 : T) =>
    let x1 : List T × (T → T) := (([] : List T), fun (_ : T) => x0); x1

def «closed» :=
  fun (x0 : T) =>
    let x1 : List T × (T → T) := «closedSh» («atomic» x0); x1

def «tyDoc» :=
  fun (x0 : List T × (T → T)) =>
    let x1 : T := «shDoc» ((x0).2 (leaf 0)); x1

def «varDoc» :=
  fun (x0 : T) =>
    let x1 : T := «text» ((leaf 120) :: («decimalChars» x0)); x1

def «namedArg» :=
  fun (x0 : T) (x1 : List T × (T → T)) =>
    let x2 : T := «cat5» «tLp» x0 «tColonEq» («tyDoc» x1) «tRp»; x2

def «quoteDoc» :=
  fun (x0 : T) =>
    let x1 : T := Const.fold
      (α := T)
      (fun (x1 : T) (x2 : List T) =>
        if («nonEmpty» x2).label ≠ 0 then
          «grp»
            («cat»
              («tMk» ::
                ((«text» («decimalChars» x1)) ::
                  («tSpLb» ::
                    ((«nest» («joinWith» («cat2» «tComma» «line») x2)) ::
                      («single» «tRb»))))))
        else
          «cat2» «tLeaf» («text» («decimalChars» x1)))
      x0;
    x1

def «letDoc» :=
  fun (x0 : List T) (x1 : T) (x2 : T) =>
    let x3 : T := (let x3 : T := «at» x0 (leaf 0);
                   let x4 : List T := «tail» x0;
                   «align»
                     («grp»
                       («cat»
                         («tLet» ::
                           ((Const.child x3 (leaf 0)) ::
                             («tColon» ::
                               ((Const.child x3 (leaf 1)) ::
                                 («tColonEq» ::
                                   ((«valDoc» x2) ::
                                     («tSemi» ::
                                       («line» ::
                                         («single»
                                           (if («nonEmpty» x4).label ≠ 0 then
                                             «shDoc» («fn» (Const.node (leaf 0) x4) x1)
                                           else
                                             x1)))))))))))));
    x3

def «emTerm» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : List T ×
      (T →
        T) := (Const.fold
      (α := T × (Unit → List T × (T → T)))
      (fun (x2 : T) (x3 : List (T × (Unit → List T × (T → T)))) =>
        let x4 : T := Const.node
          x2
          (Const.foldr
            (α := T × (Unit → List T × (T → T)))
            (β := List T)
            (fun (x4 : T × (Unit → List T × (T → T))) (x5 : List T) =>
              ((x4).1 :: x5))
            ([] : List T)
            x3);
        (x4,
          fun (_ : Unit) =>
            if (Const.eq (Const.label x4) (leaf 0)).label ≠ 0 then
              «closed» «tT»
            else
              if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
                «closed» «tUnitTy»
              else
                if (Const.eq (Const.label x4) (leaf 2)).label ≠ 0 then
                  let x6 : List T ×
                    (T →
                      T) := (Const.lcase
                    (α := T × (Unit → List T × (T → T)))
                    (β := T × (Unit → List T × (T → T)))
                    (Const.iter
                      (α := List (T × (Unit → List T × (T → T))))
                      (fun (x6 : List (T × (Unit → List T × (T → T)))) =>
                        Const.lcase
                          (α := T × (Unit → List T × (T → T)))
                          (β := List (T × (Unit → List T × (T → T))))
                          x6
                          ([] : List (T × (Unit → List T × (T → T))))
                          (fun (_ : T × (Unit → List T × (T → T)))
                             (x8 : List (T × (Unit → List T × (T → T)))) =>
                            x8))
                      x3
                      (leaf 0))
                    (leaf 0, fun (_ : Unit) => (([] : List T), fun (_ : T) => leaf 0))
                    (fun (x6 : T × (Unit → List T × (T → T)))
                       (_ : List (T × (Unit → List T × (T → T)))) =>
                      x6)).2
                    ();
                  let x7 : List T ×
                    (T →
                      T) := (Const.lcase
                    (α := T × (Unit → List T × (T → T)))
                    (β := T × (Unit → List T × (T → T)))
                    (Const.iter
                      (α := List (T × (Unit → List T × (T → T))))
                      (fun (x7 : List (T × (Unit → List T × (T → T)))) =>
                        Const.lcase
                          (α := T × (Unit → List T × (T → T)))
                          (β := List (T × (Unit → List T × (T → T))))
                          x7
                          ([] : List (T × (Unit → List T × (T → T))))
                          (fun (_ : T × (Unit → List T × (T → T)))
                             (x9 : List (T × (Unit → List T × (T → T)))) =>
                            x9))
                      x3
                      (leaf 1))
                    (leaf 0, fun (_ : Unit) => (([] : List T), fun (_ : T) => leaf 0))
                    (fun (x7 : T × (Unit → List T × (T → T)))
                       (_ : List (T × (Unit → List T × (T → T)))) =>
                      x7)).2
                    ();
                  «closedSh»
                    («compound»
                      («grp»
                        («cat3»
                          («opDoc» ((x6).2 (leaf 0)))
                          «tTimes»
                          («indented» («opDoc» ((x7).2 (leaf 0)))))))
                else
                  if (Const.eq (Const.label x4) (leaf 3)).label ≠ 0 then
                    let x6 : List T ×
                      (T →
                        T) := (Const.lcase
                      (α := T × (Unit → List T × (T → T)))
                      (β := T × (Unit → List T × (T → T)))
                      (Const.iter
                        (α := List (T × (Unit → List T × (T → T))))
                        (fun (x6 : List (T × (Unit → List T × (T → T)))) =>
                          Const.lcase
                            (α := T × (Unit → List T × (T → T)))
                            (β := List (T × (Unit → List T × (T → T))))
                            x6
                            ([] : List (T × (Unit → List T × (T → T))))
                            (fun (_ : T × (Unit → List T × (T → T)))
                               (x8 : List (T × (Unit → List T × (T → T)))) =>
                              x8))
                        x3
                        (leaf 0))
                      (leaf 0, fun (_ : Unit) => (([] : List T), fun (_ : T) => leaf 0))
                      (fun (x6 : T × (Unit → List T × (T → T)))
                         (_ : List (T × (Unit → List T × (T → T)))) =>
                        x6)).2
                      ();
                    let x7 : List T ×
                      (T →
                        T) := (Const.lcase
                      (α := T × (Unit → List T × (T → T)))
                      (β := T × (Unit → List T × (T → T)))
                      (Const.iter
                        (α := List (T × (Unit → List T × (T → T))))
                        (fun (x7 : List (T × (Unit → List T × (T → T)))) =>
                          Const.lcase
                            (α := T × (Unit → List T × (T → T)))
                            (β := List (T × (Unit → List T × (T → T))))
                            x7
                            ([] : List (T × (Unit → List T × (T → T))))
                            (fun (_ : T × (Unit → List T × (T → T)))
                               (x9 : List (T × (Unit → List T × (T → T)))) =>
                              x9))
                        x3
                        (leaf 1))
                      (leaf 0, fun (_ : Unit) => (([] : List T), fun (_ : T) => leaf 0))
                      (fun (x7 : T × (Unit → List T × (T → T)))
                         (_ : List (T × (Unit → List T × (T → T)))) =>
                        x7)).2
                      ();
                    «closedSh»
                      («compound»
                        («grp»
                          («cat3» («opDoc» ((x6).2 (leaf 0))) «tTo» («indented» («tyDoc» x7)))))
                  else
                    if (Const.eq (Const.label x4) (leaf 4)).label ≠ 0 then
                      let x6 : List T ×
                        (T →
                          T) := (Const.lcase
                        (α := T × (Unit → List T × (T → T)))
                        (β := T × (Unit → List T × (T → T)))
                        (Const.iter
                          (α := List (T × (Unit → List T × (T → T))))
                          (fun (x6 : List (T × (Unit → List T × (T → T)))) =>
                            Const.lcase
                              (α := T × (Unit → List T × (T → T)))
                              (β := List (T × (Unit → List T × (T → T))))
                              x6
                              ([] : List (T × (Unit → List T × (T → T))))
                              (fun (_ : T × (Unit → List T × (T → T)))
                                 (x8 : List (T × (Unit → List T × (T → T)))) =>
                                x8))
                          x3
                          (leaf 0))
                        (leaf 0, fun (_ : Unit) => (([] : List T), fun (_ : T) => leaf 0))
                        (fun (x6 : T × (Unit → List T × (T → T)))
                           (_ : List (T × (Unit → List T × (T → T)))) =>
                          x6)).2
                        ();
                      «closedSh» («ap» «tList» («single» («argDoc» ((x6).2 (leaf 0)))))
                    else
                      if (Const.eq (Const.label x4) (leaf 8)).label ≠ 0 then
                        let x6 : T := Const.child x4 (leaf 0);
                        («append» («replicate» (Const.label x6) (leaf 0)) («single» (leaf 1)),
                          fun (x7 : T) =>
                            «atomic»
                              («varDoc» (Const.sub (Const.sub x7 (leaf 1)) (Const.label x6))))
                      else
                        if (Const.eq (Const.label x4) (leaf 9)).label ≠ 0 then
                          let x6 : List T ×
                            (T →
                              T) := (Const.lcase
                            (α := T × (Unit → List T × (T → T)))
                            (β := T × (Unit → List T × (T → T)))
                            (Const.iter
                              (α := List (T × (Unit → List T × (T → T))))
                              (fun (x6 : List (T × (Unit → List T × (T → T)))) =>
                                Const.lcase
                                  (α := T × (Unit → List T × (T → T)))
                                  (β := List (T × (Unit → List T × (T → T))))
                                  x6
                                  ([] : List (T × (Unit → List T × (T → T))))
                                  (fun (_ : T × (Unit → List T × (T → T)))
                                     (x8 : List (T × (Unit → List T × (T → T)))) =>
                                    x8))
                              x3
                              (leaf 0))
                            (leaf 0, fun (_ : Unit) => (([] : List T), fun (_ : T) => leaf 0))
                            (fun (x6 : T × (Unit → List T × (T → T)))
                               (_ : List (T × (Unit → List T × (T → T)))) =>
                              x6)).2
                            ();
                          let x7 : List T ×
                            (T →
                              T) := (Const.lcase
                            (α := T × (Unit → List T × (T → T)))
                            (β := T × (Unit → List T × (T → T)))
                            (Const.iter
                              (α := List (T × (Unit → List T × (T → T))))
                              (fun (x7 : List (T × (Unit → List T × (T → T)))) =>
                                Const.lcase
                                  (α := T × (Unit → List T × (T → T)))
                                  (β := List (T × (Unit → List T × (T → T))))
                                  x7
                                  ([] : List (T × (Unit → List T × (T → T))))
                                  (fun (_ : T × (Unit → List T × (T → T)))
                                     (x9 : List (T × (Unit → List T × (T → T)))) =>
                                    x9))
                              x3
                              (leaf 1))
                            (leaf 0, fun (_ : Unit) => (([] : List T), fun (_ : T) => leaf 0))
                            (fun (x7 : T × (Unit → List T × (T → T)))
                               (_ : List (T × (Unit → List T × (T → T)))) =>
                              x7)).2
                            ();
                          («tail» (x7).1,
                            fun (x8 : T) =>
                              let x9 : T := Const.lcase
                                (α := T)
                                (β := T)
                                (x7).1
                                (leaf 0)
                                (fun (x9 : T) (_ : List T) => x9);
                              let x10 : T := «node2»
                                (leaf 0)
                                (if (x9).label ≠ 0 then «varDoc» x8 else «tUnder»)
                                («tyDoc» x6);
                              let x11 : T := (x7).2 (Const.add x8 (leaf 1));
                              let x12 : T := x11;
                              if (Const.eq (Const.label x12) (leaf 2)).label ≠ 0 then
                                let x13 : T := Const.child x12 (leaf 0);
                                let x14 : T := Const.child x12 (leaf 1);
                                «fn» (Const.node (leaf 0) (x10 :: (Const.children x13))) x14
                              else
                                «fn» (Const.node (leaf 0) («single» x10)) («shDoc» x11))
                        else
                          if (Const.eq (Const.label x4) (leaf 10)).label ≠ 0 then
                            let x6 : List T ×
                              (T →
                                T) := (Const.lcase
                              (α := T × (Unit → List T × (T → T)))
                              (β := T × (Unit → List T × (T → T)))
                              (Const.iter
                                (α := List (T × (Unit → List T × (T → T))))
                                (fun (x6 : List (T × (Unit → List T × (T → T)))) =>
                                  Const.lcase
                                    (α := T × (Unit → List T × (T → T)))
                                    (β := List (T × (Unit → List T × (T → T))))
                                    x6
                                    ([] : List (T × (Unit → List T × (T → T))))
                                    (fun (_ : T × (Unit → List T × (T → T)))
                                       (x8 : List (T × (Unit → List T × (T → T)))) =>
                                      x8))
                                x3
                                (leaf 0))
                              (leaf 0, fun (_ : Unit) => (([] : List T), fun (_ : T) => leaf 0))
                              (fun (x6 : T × (Unit → List T × (T → T)))
                                 (_ : List (T × (Unit → List T × (T → T)))) =>
                                x6)).2
                              ();
                            let x7 : List T ×
                              (T →
                                T) := (Const.lcase
                              (α := T × (Unit → List T × (T → T)))
                              (β := T × (Unit → List T × (T → T)))
                              (Const.iter
                                (α := List (T × (Unit → List T × (T → T))))
                                (fun (x7 : List (T × (Unit → List T × (T → T)))) =>
                                  Const.lcase
                                    (α := T × (Unit → List T × (T → T)))
                                    (β := List (T × (Unit → List T × (T → T))))
                                    x7
                                    ([] : List (T × (Unit → List T × (T → T))))
                                    (fun (_ : T × (Unit → List T × (T → T)))
                                       (x9 : List (T × (Unit → List T × (T → T)))) =>
                                      x9))
                                x3
                                (leaf 1))
                              (leaf 0, fun (_ : Unit) => (([] : List T), fun (_ : T) => leaf 0))
                              (fun (x7 : T × (Unit → List T × (T → T)))
                                 (_ : List (T × (Unit → List T × (T → T)))) =>
                                x7)).2
                              ();
                            («orList» (x6).1 (x7).1,
                              fun (x8 : T) =>
                                let x9 : T := (x6).2 x8;
                                let x10 : T := (x7).2 x8;
                                let x11 : T := x9;
                                if (Const.eq (Const.label x11) (leaf 3)).label ≠ 0 then
                                  let x12 : T := Const.child x11 (leaf 0);
                                  let x13 : List
                                    T := Const.iter
                                    (α := List T)
                                    (fun (x13 : List T) =>
                                      Const.lcase
                                        (α := T)
                                        (β := List T)
                                        x13
                                        ([] : List T)
                                        (fun (_ : T) (x15 : List T) => x15))
                                    (Const.children x11)
                                    (leaf 1);
                                  «ap» x12 («append» x13 («single» («argDoc» x10)))
                                else
                                  if (Const.eq (Const.label x11) (leaf 2)).label ≠ 0 then
                                    let x12 : T := Const.child x11 (leaf 0);
                                    let x13 : T := Const.child x11 (leaf 1);
                                    «compound» («letDoc» (Const.children x12) x13 x10)
                                  else
                                    «ap» («argDoc» x9) («single» («argDoc» x10)))
                          else
                            if (Const.eq (Const.label x4) (leaf 11)).label ≠ 0 then
                              «closed» «tUnitV»
                            else
                              if (Const.eq (Const.label x4) (leaf 12)).label ≠ 0 then
                                let x6 : List T ×
                                  (T →
                                    T) := (Const.lcase
                                  (α := T × (Unit → List T × (T → T)))
                                  (β := T × (Unit → List T × (T → T)))
                                  (Const.iter
                                    (α := List (T × (Unit → List T × (T → T))))
                                    (fun (x6 : List (T × (Unit → List T × (T → T)))) =>
                                      Const.lcase
                                        (α := T × (Unit → List T × (T → T)))
                                        (β := List (T × (Unit → List T × (T → T))))
                                        x6
                                        ([] : List (T × (Unit → List T × (T → T))))
                                        (fun (_ : T × (Unit → List T × (T → T)))
                                           (x8 : List (T × (Unit → List T × (T → T)))) =>
                                          x8))
                                    x3
                                    (leaf 0))
                                  (leaf 0, fun (_ : Unit) => (([] : List T), fun (_ : T) => leaf 0))
                                  (fun (x6 : T × (Unit → List T × (T → T)))
                                     (_ : List (T × (Unit → List T × (T → T)))) =>
                                    x6)).2
                                  ();
                                let x7 : List T ×
                                  (T →
                                    T) := (Const.lcase
                                  (α := T × (Unit → List T × (T → T)))
                                  (β := T × (Unit → List T × (T → T)))
                                  (Const.iter
                                    (α := List (T × (Unit → List T × (T → T))))
                                    (fun (x7 : List (T × (Unit → List T × (T → T)))) =>
                                      Const.lcase
                                        (α := T × (Unit → List T × (T → T)))
                                        (β := List (T × (Unit → List T × (T → T))))
                                        x7
                                        ([] : List (T × (Unit → List T × (T → T))))
                                        (fun (_ : T × (Unit → List T × (T → T)))
                                           (x9 : List (T × (Unit → List T × (T → T)))) =>
                                          x9))
                                    x3
                                    (leaf 1))
                                  (leaf 0, fun (_ : Unit) => (([] : List T), fun (_ : T) => leaf 0))
                                  (fun (x7 : T × (Unit → List T × (T → T)))
                                     (_ : List (T × (Unit → List T × (T → T)))) =>
                                    x7)).2
                                  ();
                                («orList» (x6).1 (x7).1,
                                  fun (x8 : T) =>
                                    «atomic»
                                      («grp»
                                        («cat5»
                                          «tLp»
                                          («shDoc» ((x6).2 x8))
                                          «tComma»
                                          («indented» («shDoc» ((x7).2 x8)))
                                          «tRp»)))
                              else
                                if (Const.eq (Const.label x4) (leaf 13)).label ≠ 0 then
                                  let x6 : List T ×
                                    (T →
                                      T) := (Const.lcase
                                    (α := T × (Unit → List T × (T → T)))
                                    (β := T × (Unit → List T × (T → T)))
                                    (Const.iter
                                      (α := List (T × (Unit → List T × (T → T))))
                                      (fun (x6 : List (T × (Unit → List T × (T → T)))) =>
                                        Const.lcase
                                          (α := T × (Unit → List T × (T → T)))
                                          (β := List (T × (Unit → List T × (T → T))))
                                          x6
                                          ([] : List (T × (Unit → List T × (T → T))))
                                          (fun (_ : T × (Unit → List T × (T → T)))
                                             (x8 : List (T × (Unit → List T × (T → T)))) =>
                                            x8))
                                      x3
                                      (leaf 0))
                                    (leaf 0,
                                      fun (_ : Unit) => (([] : List T), fun (_ : T) => leaf 0))
                                    (fun (x6 : T × (Unit → List T × (T → T)))
                                       (_ : List (T × (Unit → List T × (T → T)))) =>
                                      x6)).2
                                    ();
                                  ((x6).1,
                                    fun (x7 : T) =>
                                      «atomic» («cat3» «tLp» («shDoc» ((x6).2 x7)) «tDot1»))
                                else
                                  if (Const.eq (Const.label x4) (leaf 14)).label ≠ 0 then
                                    let x6 : List T ×
                                      (T →
                                        T) := (Const.lcase
                                      (α := T × (Unit → List T × (T → T)))
                                      (β := T × (Unit → List T × (T → T)))
                                      (Const.iter
                                        (α := List (T × (Unit → List T × (T → T))))
                                        (fun (x6 : List (T × (Unit → List T × (T → T)))) =>
                                          Const.lcase
                                            (α := T × (Unit → List T × (T → T)))
                                            (β := List (T × (Unit → List T × (T → T))))
                                            x6
                                            ([] : List (T × (Unit → List T × (T → T))))
                                            (fun (_ : T × (Unit → List T × (T → T)))
                                               (x8 : List (T × (Unit → List T × (T → T)))) =>
                                              x8))
                                        x3
                                        (leaf 0))
                                      (leaf 0,
                                        fun (_ : Unit) => (([] : List T), fun (_ : T) => leaf 0))
                                      (fun (x6 : T × (Unit → List T × (T → T)))
                                         (_ : List (T × (Unit → List T × (T → T)))) =>
                                        x6)).2
                                      ();
                                    ((x6).1,
                                      fun (x7 : T) =>
                                        «atomic» («cat3» «tLp» («shDoc» ((x6).2 x7)) «tDot2»))
                                  else
                                    if (Const.eq (Const.label x4) (leaf 15)).label ≠ 0 then
                                      let x6 : T := Const.child x4 (leaf 0);
                                      (([] : List T), fun (_ : T) => «compound» («quoteDoc» x6))
                                    else
                                      if (Const.eq (Const.label x4) (leaf 16)).label ≠ 0 then
                                        let x6 : List T ×
                                          (T →
                                            T) := (Const.lcase
                                          (α := T × (Unit → List T × (T → T)))
                                          (β := T × (Unit → List T × (T → T)))
                                          (Const.iter
                                            (α := List (T × (Unit → List T × (T → T))))
                                            (fun (x6 : List (T × (Unit → List T × (T → T)))) =>
                                              Const.lcase
                                                (α := T × (Unit → List T × (T → T)))
                                                (β := List (T × (Unit → List T × (T → T))))
                                                x6
                                                ([] : List (T × (Unit → List T × (T → T))))
                                                (fun (_ : T × (Unit → List T × (T → T)))
                                                   (x8 : List (T × (Unit → List T × (T → T)))) =>
                                                  x8))
                                            x3
                                            (leaf 0))
                                          (leaf 0,
                                            fun (_ : Unit) =>
                                              (([] : List T), fun (_ : T) => leaf 0))
                                          (fun (x6 : T × (Unit → List T × (T → T)))
                                             (_ : List (T × (Unit → List T × (T → T)))) =>
                                            x6)).2
                                          ();
                                        let x7 : List T ×
                                          (T →
                                            T) := (Const.lcase
                                          (α := T × (Unit → List T × (T → T)))
                                          (β := T × (Unit → List T × (T → T)))
                                          (Const.iter
                                            (α := List (T × (Unit → List T × (T → T))))
                                            (fun (x7 : List (T × (Unit → List T × (T → T)))) =>
                                              Const.lcase
                                                (α := T × (Unit → List T × (T → T)))
                                                (β := List (T × (Unit → List T × (T → T))))
                                                x7
                                                ([] : List (T × (Unit → List T × (T → T))))
                                                (fun (_ : T × (Unit → List T × (T → T)))
                                                   (x9 : List (T × (Unit → List T × (T → T)))) =>
                                                  x9))
                                            x3
                                            (leaf 1))
                                          (leaf 0,
                                            fun (_ : Unit) =>
                                              (([] : List T), fun (_ : T) => leaf 0))
                                          (fun (x7 : T × (Unit → List T × (T → T)))
                                             (_ : List (T × (Unit → List T × (T → T)))) =>
                                            x7)).2
                                          ();
                                        let x8 : List T ×
                                          (T →
                                            T) := (Const.lcase
                                          (α := T × (Unit → List T × (T → T)))
                                          (β := T × (Unit → List T × (T → T)))
                                          (Const.iter
                                            (α := List (T × (Unit → List T × (T → T))))
                                            (fun (x8 : List (T × (Unit → List T × (T → T)))) =>
                                              Const.lcase
                                                (α := T × (Unit → List T × (T → T)))
                                                (β := List (T × (Unit → List T × (T → T))))
                                                x8
                                                ([] : List (T × (Unit → List T × (T → T))))
                                                (fun (_ : T × (Unit → List T × (T → T)))
                                                   (x10 : List (T × (Unit → List T × (T → T)))) =>
                                                  x10))
                                            x3
                                            (leaf 2))
                                          (leaf 0,
                                            fun (_ : Unit) =>
                                              (([] : List T), fun (_ : T) => leaf 0))
                                          (fun (x8 : T × (Unit → List T × (T → T)))
                                             (_ : List (T × (Unit → List T × (T → T)))) =>
                                            x8)).2
                                          ();
                                        («orList» (x6).1 («orList» (x7).1 (x8).1),
                                          fun (x9 : T) =>
                                            «compound»
                                              («grp»
                                                («cat»
                                                  («tIf» ::
                                                    ((«shDoc» ((x6).2 x9)) ::
                                                      («tThen» ::
                                                        ((«indented» («shDoc» ((x7).2 x9))) ::
                                                          («line» ::
                                                            («tElse» ::
                                                              («single»
                                                                («indented»
                                                                  («shDoc» ((x8).2 x9)))))))))))))
                                      else
                                        if (Const.eq (Const.label x4) (leaf 17)).label ≠ 0 then
                                          let x6 : List T ×
                                            (T →
                                              T) := (Const.lcase
                                            (α := T × (Unit → List T × (T → T)))
                                            (β := T × (Unit → List T × (T → T)))
                                            (Const.iter
                                              (α := List (T × (Unit → List T × (T → T))))
                                              (fun (x6 : List (T × (Unit → List T × (T → T)))) =>
                                                Const.lcase
                                                  (α := T × (Unit → List T × (T → T)))
                                                  (β := List (T × (Unit → List T × (T → T))))
                                                  x6
                                                  ([] : List (T × (Unit → List T × (T → T))))
                                                  (fun (_ : T × (Unit → List T × (T → T)))
                                                     (x8 : List (T × (Unit → List T × (T → T)))) =>
                                                    x8))
                                              x3
                                              (leaf 0))
                                            (leaf 0,
                                              fun (_ : Unit) =>
                                                (([] : List T), fun (_ : T) => leaf 0))
                                            (fun (x6 : T × (Unit → List T × (T → T)))
                                               (_ : List (T × (Unit → List T × (T → T)))) =>
                                              x6)).2
                                            ();
                                          (([] : List T),
                                            fun (_ : T) =>
                                              «ap» «tFold» («single» («namedArg» «tAlpha» x6)))
                                        else
                                          if (Const.eq (Const.label x4) (leaf 18)).label ≠ 0 then
                                            let x6 : List T ×
                                              (T →
                                                T) := (Const.lcase
                                              (α := T × (Unit → List T × (T → T)))
                                              (β := T × (Unit → List T × (T → T)))
                                              (Const.iter
                                                (α := List (T × (Unit → List T × (T → T))))
                                                (fun (x6 : List (T × (Unit → List T × (T → T)))) =>
                                                  Const.lcase
                                                    (α := T × (Unit → List T × (T → T)))
                                                    (β := List (T × (Unit → List T × (T → T))))
                                                    x6
                                                    ([] : List (T × (Unit → List T × (T → T))))
                                                    (fun (_ : T × (Unit → List T × (T → T)))
                                                       (x8 : List
                                                         (T × (Unit → List T × (T → T)))) =>
                                                      x8))
                                                x3
                                                (leaf 0))
                                              (leaf 0,
                                                fun (_ : Unit) =>
                                                  (([] : List T), fun (_ : T) => leaf 0))
                                              (fun (x6 : T × (Unit → List T × (T → T)))
                                                 (_ : List (T × (Unit → List T × (T → T)))) =>
                                                x6)).2
                                              ();
                                            (([] : List T),
                                              fun (_ : T) =>
                                                «ap» «tIter» («single» («namedArg» «tAlpha» x6)))
                                          else
                                            if (Const.eq (Const.label x4) (leaf 19)).label ≠ 0 then
                                              let x6 : List T ×
                                                (T →
                                                  T) := (Const.lcase
                                                (α := T × (Unit → List T × (T → T)))
                                                (β := T × (Unit → List T × (T → T)))
                                                (Const.iter
                                                  (α := List (T × (Unit → List T × (T → T))))
                                                  (fun (x6 : List
                                                       (T × (Unit → List T × (T → T)))) =>
                                                    Const.lcase
                                                      (α := T × (Unit → List T × (T → T)))
                                                      (β := List (T × (Unit → List T × (T → T))))
                                                      x6
                                                      ([] : List (T × (Unit → List T × (T → T))))
                                                      (fun (_ : T × (Unit → List T × (T → T)))
                                                         (x8 : List
                                                           (T × (Unit → List T × (T → T)))) =>
                                                        x8))
                                                  x3
                                                  (leaf 0))
                                                (leaf 0,
                                                  fun (_ : Unit) =>
                                                    (([] : List T), fun (_ : T) => leaf 0))
                                                (fun (x6 : T × (Unit → List T × (T → T)))
                                                   (_ : List (T × (Unit → List T × (T → T)))) =>
                                                  x6)).2
                                                ();
                                              «closed»
                                                («cat3» «tNilLp» («argDoc» ((x6).2 (leaf 0))) «tRp»)
                                            else
                                              if (Const.eq
                                                (Const.label x4)
                                                (leaf 20)).label ≠ 0 then
                                                let x6 : List T ×
                                                  (T →
                                                    T) := (Const.lcase
                                                  (α := T × (Unit → List T × (T → T)))
                                                  (β := T × (Unit → List T × (T → T)))
                                                  (Const.iter
                                                    (α := List (T × (Unit → List T × (T → T))))
                                                    (fun (x6 : List
                                                         (T × (Unit → List T × (T → T)))) =>
                                                      Const.lcase
                                                        (α := T × (Unit → List T × (T → T)))
                                                        (β := List (T × (Unit → List T × (T → T))))
                                                        x6
                                                        ([] : List (T × (Unit → List T × (T → T))))
                                                        (fun (_ : T × (Unit → List T × (T → T)))
                                                           (x8 : List
                                                             (T × (Unit → List T × (T → T)))) =>
                                                          x8))
                                                    x3
                                                    (leaf 0))
                                                  (leaf 0,
                                                    fun (_ : Unit) =>
                                                      (([] : List T), fun (_ : T) => leaf 0))
                                                  (fun (x6 : T × (Unit → List T × (T → T)))
                                                     (_ : List (T × (Unit → List T × (T → T)))) =>
                                                    x6)).2
                                                  ();
                                                let x7 : List T ×
                                                  (T →
                                                    T) := (Const.lcase
                                                  (α := T × (Unit → List T × (T → T)))
                                                  (β := T × (Unit → List T × (T → T)))
                                                  (Const.iter
                                                    (α := List (T × (Unit → List T × (T → T))))
                                                    (fun (x7 : List
                                                         (T × (Unit → List T × (T → T)))) =>
                                                      Const.lcase
                                                        (α := T × (Unit → List T × (T → T)))
                                                        (β := List (T × (Unit → List T × (T → T))))
                                                        x7
                                                        ([] : List (T × (Unit → List T × (T → T))))
                                                        (fun (_ : T × (Unit → List T × (T → T)))
                                                           (x9 : List
                                                             (T × (Unit → List T × (T → T)))) =>
                                                          x9))
                                                    x3
                                                    (leaf 1))
                                                  (leaf 0,
                                                    fun (_ : Unit) =>
                                                      (([] : List T), fun (_ : T) => leaf 0))
                                                  (fun (x7 : T × (Unit → List T × (T → T)))
                                                     (_ : List (T × (Unit → List T × (T → T)))) =>
                                                    x7)).2
                                                  ();
                                                («orList» (x6).1 (x7).1,
                                                  fun (x8 : T) =>
                                                    «atomic»
                                                      («grp»
                                                        («cat5»
                                                          «tLp»
                                                          («argDoc» ((x6).2 x8))
                                                          «tConsOp»
                                                          («indented» («argDoc» ((x7).2 x8)))
                                                          «tRp»)))
                                              else
                                                if (Const.eq
                                                  (Const.label x4)
                                                  (leaf 21)).label ≠ 0 then
                                                  let x6 : List T ×
                                                    (T →
                                                      T) := (Const.lcase
                                                    (α := T × (Unit → List T × (T → T)))
                                                    (β := T × (Unit → List T × (T → T)))
                                                    (Const.iter
                                                      (α := List (T × (Unit → List T × (T → T))))
                                                      (fun (x6 : List
                                                           (T × (Unit → List T × (T → T)))) =>
                                                        Const.lcase
                                                          (α := T × (Unit → List T × (T → T)))
                                                          (β := List
                                                            (T × (Unit → List T × (T → T))))
                                                          x6
                                                          ([] : List (T ×
                                                            (Unit → List T × (T → T))))
                                                          (fun (_ : T × (Unit → List T × (T → T)))
                                                             (x8 : List
                                                               (T × (Unit → List T × (T → T)))) =>
                                                            x8))
                                                      x3
                                                      (leaf 0))
                                                    (leaf 0,
                                                      fun (_ : Unit) =>
                                                        (([] : List T), fun (_ : T) => leaf 0))
                                                    (fun (x6 : T × (Unit → List T × (T → T)))
                                                       (_ : List (T × (Unit → List T × (T → T)))) =>
                                                      x6)).2
                                                    ();
                                                  let x7 : List T ×
                                                    (T →
                                                      T) := (Const.lcase
                                                    (α := T × (Unit → List T × (T → T)))
                                                    (β := T × (Unit → List T × (T → T)))
                                                    (Const.iter
                                                      (α := List (T × (Unit → List T × (T → T))))
                                                      (fun (x7 : List
                                                           (T × (Unit → List T × (T → T)))) =>
                                                        Const.lcase
                                                          (α := T × (Unit → List T × (T → T)))
                                                          (β := List
                                                            (T × (Unit → List T × (T → T))))
                                                          x7
                                                          ([] : List (T ×
                                                            (Unit → List T × (T → T))))
                                                          (fun (_ : T × (Unit → List T × (T → T)))
                                                             (x9 : List
                                                               (T × (Unit → List T × (T → T)))) =>
                                                            x9))
                                                      x3
                                                      (leaf 1))
                                                    (leaf 0,
                                                      fun (_ : Unit) =>
                                                        (([] : List T), fun (_ : T) => leaf 0))
                                                    (fun (x7 : T × (Unit → List T × (T → T)))
                                                       (_ : List (T × (Unit → List T × (T → T)))) =>
                                                      x7)).2
                                                    ();
                                                  (([] : List T),
                                                    fun (_ : T) =>
                                                      «ap»
                                                        «tFoldr»
                                                        ((«namedArg» «tAlpha» x6) ::
                                                          («single» («namedArg» «tBeta» x7))))
                                                else
                                                  if (Const.eq
                                                    (Const.label x4)
                                                    (leaf 22)).label ≠ 0 then
                                                    let x6 : T := Const.child x4 (leaf 0);
                                                    «closed»
                                                      («cat2»
                                                        «tConstDot»
                                                        («text»
                                                          (Const.children
                                                            («at» «primNames» (Const.label x6)))))
                                                  else
                                                    if (Const.eq
                                                      (Const.label x4)
                                                      (leaf 23)).label ≠ 0 then
                                                      let x6 : T := Const.child x4 (leaf 0);
                                                      «closed»
                                                        («cat3»
                                                          «tLg»
                                                          («text»
                                                            (Const.children
                                                              (Const.child x0 (Const.label x6))))
                                                          «tRg»)
                                                    else
                                                      if (Const.eq
                                                        (Const.label x4)
                                                        (leaf 24)).label ≠ 0 then
                                                        let x6 : List T ×
                                                          (T →
                                                            T) := (Const.lcase
                                                          (α := T × (Unit → List T × (T → T)))
                                                          (β := T × (Unit → List T × (T → T)))
                                                          (Const.iter
                                                            (α := List
                                                              (T × (Unit → List T × (T → T))))
                                                            (fun (x6 : List
                                                                 (T × (Unit → List T × (T → T)))) =>
                                                              Const.lcase
                                                                (α := T × (Unit → List T × (T → T)))
                                                                (β := List
                                                                  (T × (Unit → List T × (T → T))))
                                                                x6
                                                                ([] : List (T ×
                                                                  (Unit → List T × (T → T))))
                                                                (fun (_ : T ×
                                                                     (Unit → List T × (T → T)))
                                                                   (x8 : List
                                                                     (T ×
                                                                       (Unit →
                                                                         List T × (T → T)))) =>
                                                                  x8))
                                                            x3
                                                            (leaf 0))
                                                          (leaf 0,
                                                            fun (_ : Unit) =>
                                                              (([] : List T),
                                                                fun (_ : T) => leaf 0))
                                                          (fun (x6 : T × (Unit → List T × (T → T)))
                                                             (_ : List
                                                               (T × (Unit → List T × (T → T)))) =>
                                                            x6)).2
                                                          ();
                                                        let x7 : List T ×
                                                          (T →
                                                            T) := (Const.lcase
                                                          (α := T × (Unit → List T × (T → T)))
                                                          (β := T × (Unit → List T × (T → T)))
                                                          (Const.iter
                                                            (α := List
                                                              (T × (Unit → List T × (T → T))))
                                                            (fun (x7 : List
                                                                 (T × (Unit → List T × (T → T)))) =>
                                                              Const.lcase
                                                                (α := T × (Unit → List T × (T → T)))
                                                                (β := List
                                                                  (T × (Unit → List T × (T → T))))
                                                                x7
                                                                ([] : List (T ×
                                                                  (Unit → List T × (T → T))))
                                                                (fun (_ : T ×
                                                                     (Unit → List T × (T → T)))
                                                                   (x9 : List
                                                                     (T ×
                                                                       (Unit →
                                                                         List T × (T → T)))) =>
                                                                  x9))
                                                            x3
                                                            (leaf 1))
                                                          (leaf 0,
                                                            fun (_ : Unit) =>
                                                              (([] : List T),
                                                                fun (_ : T) => leaf 0))
                                                          (fun (x7 : T × (Unit → List T × (T → T)))
                                                             (_ : List
                                                               (T × (Unit → List T × (T → T)))) =>
                                                            x7)).2
                                                          ();
                                                        (([] : List T),
                                                          fun (_ : T) =>
                                                            «ap»
                                                              «tLcase»
                                                              ((«namedArg» «tAlpha» x6) ::
                                                                («single» («namedArg» «tBeta» x7))))
                                                      else
                                                        «closed» «tUnder»))
      x1).2
      ();
    x2

def «defDoc» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «cat3»
      «line»
      «line»
      («grp»
        («cat»
          («tDef» ::
            ((«text» (Const.children x0)) ::
              («tAssign» :: («single» («indented» x1)))))));
    x2

def «emitLean» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := Const.child x0 (leaf 1);
                   let x2 : List T := Const.children (Const.child x0 (leaf 0));
                   let x3 : T := «length» x2;
                   «layout»
                     («cat»
                       («tHeader» ::
                         («append»
                           (Const.foldr
                             (α := T)
                             (β := T × List T)
                             (fun (x4 : T) (x5 : T × List T) =>
                               (Const.add (x5).1 (leaf 1),
                                 ((«defDoc»
                                   (Const.child x1 (Const.sub (Const.sub x3 (leaf 1)) (x5).1))
                                   («shDoc» ((«emTerm» x1 x4).2 (leaf 0)))) ::
                                   (x5).2)))
                             (leaf 0, ([] : List T))
                             x2).2
                           («single» «tFooter»)))));
    x1

def «mainLean» :=
  fun (x0 : T) =>
    let x1 : T := «compileWith» «emitLean» x0; x1

end GebBoot

end
