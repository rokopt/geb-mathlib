module

public import GebMirror.Metalogic.Translation

/-! Generated from a Geb program by `bootstrap/stage1/lean.geb`. -/

@[expose] public section

open Geb.Kernel
open Geb.Kernel renaming Tree → T

namespace GebMirror.Metalogic

def «dNode» :=
  fun (x0 : T) (x1 : List T) (x2 : List T) =>
    let x3 : T := «mNode» x0 x1 x2; x3

def «dRefl» :=
  «pr» («dNode» (leaf 0) ([] : List T) ([] : List T)) (leaf 0)

def «dTrans» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (if («p2» x0).label ≠ 0 then
      if («p2» x1).label ≠ 0 then
        «pr»
          («dNode» (leaf 1) ([] : List T) («l2» («p1» x0) («p1» x1)))
          (leaf 1)
      else
        x0
    else
      x1);
    x2

def «dCong» :=
  fun (x0 : List T) =>
    let x1 : T := (if («anyT» «p2» x0).label ≠ 0 then
      «pr» («dNode» (leaf 2) ([] : List T) («mapT» «p1» x0)) (leaf 1)
    else
      «dRefl»);
    x1

def «sameShape» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := Const.label x0;
                   if (Const.eq x2 (leaf 0)).label ≠ 0 then
                     leaf 1
                   else
                     if (Const.eq (Const.label x1) x2).label ≠ 0 then
                       if («or»
                         (Const.eq x2 (leaf 7))
                         (Const.eq x2 (leaf 11))).label ≠ 0 then
                         Const.eq («mD» x0 (leaf 0)) («mD» x1 (leaf 0))
                       else
                         leaf 1
                     else
                       leaf 0);
    x2

def «setAt» :=
  fun (x0 : List T) (x1 : T) (x2 : T) =>
    let x3 : List
      T := «mapT»
      (fun (x3 : T) =>
        if (Const.eq x3 x1).label ≠ 0 then x2 else «at» x0 x3)
      («range» («length» x0));
    x3

def «mtTail» :=
  fun (x0 : List (T → T → List T → T)) =>
    let x1 : List
      (T →
        T →
          List T →
            T) := Const.lcase
      (α := T → T → List T → T)
      (β := List (T → T → List T → T))
      x0
      ([] : List (T → T → List T → T))
      (fun (_ : T → T → List T → T) (x2 : List (T → T → List T → T)) => x2);
    x1

def «mtAt» :=
  fun (x0 : List (T → T → List T → T)) (x1 : T) =>
    let x2 : T →
      T →
        List T →
          T := Const.lcase
      (α := T → T → List T → T)
      (β := T → T → List T → T)
      (Const.iter (α := List (T → T → List T → T)) «mtTail» x0 x1)
      (fun (_ : T) (_ : T) (_ : List T) => «none»)
      (fun (x2 : T → T → List T → T) (_ : List (T → T → List T → T)) => x2);
    x2

def «matchVar» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : List T) =>
    let x4 : T := (if (Const.lt x0 x1).label ≠ 0 then
      if (Const.equal x2 («mVar» x0)).label ≠ 0 then
        «some» (Const.node (leaf 0) x3)
      else
        «none»
    else
      let x4 : T := (if (Const.eq x1 (leaf 0)).label ≠ 0 then
        x2
      else
        «rename» x2 (fun (x4 : T) => Const.sub x4 x1));
      if («or»
        (Const.eq x1 (leaf 0))
        (Const.equal
          («rename» x4 (fun (x5 : T) => Const.add x5 x1))
          x2)).label ≠ 0 then
        let x5 : T := «nth» x3 (Const.sub x0 x1);
        if («isSome» x5).label ≠ 0 then
          if («isSome» («get» x5)).label ≠ 0 then
            if (Const.equal («get» («get» x5)) x4).label ≠ 0 then
              «some» (Const.node (leaf 0) x3)
            else
              «none»
          else
            «some»
              (Const.node (leaf 0) («setAt» x3 (Const.sub x0 x1) («some» x4)))
        else
          if (Const.equal x4 («mVar» (Const.sub x0 x1))).label ≠ 0 then
            «some» (Const.node (leaf 0) x3)
          else
            «none»
      else
        «none»);
    x4

def «matchAll» :=
  fun (x0 : List (T → T → List T → T))
    (x1 : T)
    (x2 : List T)
    (x3 : List T) =>
    let x4 : T := Const.foldr
      (α := T → T → List T → T)
      (β := List T → T → T)
      (fun (x4 : T → T → List T → T)
         (x5 : List T → T → T)
         (x6 : List T)
         (x7 : T) =>
        Const.lcase
          (α := T)
          (β := T)
          x6
          x7
          (fun (x8 : T) (x9 : List T) =>
            x5 x9 («bindO» x7 (fun (x10 : T) => x4 x1 x8 (Const.children x10)))))
      (fun (_ : List T) (x5 : T) => x5)
      («mtTail» x0)
      x2
      («some» (Const.node (leaf 0) x3));
    x4

def «matchStep» :=
  fun (x0 : T) (x1 : List (T → T → List T → T)) =>
    let x2 : T →
      T →
        List T →
          T := (fun (x2 : T) (x3 : T) (x4 : List T) =>
      let x5 : T := Const.label x0;
      if (Const.eq x5 (leaf 0)).label ≠ 0 then
        «matchVar» («mD» x0 (leaf 0)) x2 x3 x4
      else
        let x6 : List T := «mArgs» x3;
        let x7 : T := «length» x6;
        if («and»
          («and»
            (Const.eq x5 (Const.label x3))
            (Const.equal (Const.child x0 (leaf 0)) (Const.child x3 (leaf 0))))
          (Const.eq («length» («mArgs» x0)) x7)).label ≠ 0 then
          if («and»
            (Const.eq x5 (leaf 5))
            (Const.eq x7 (leaf 1))).label ≠ 0 then
            «mtAt» x1 (leaf 1) (Const.add x2 (leaf 1)) («at» x6 (leaf 0)) x4
          else
            if («and»
              («or» (Const.eq x5 (leaf 8)) (Const.eq x5 (leaf 9)))
              (Const.eq x7 (leaf 3))).label ≠ 0 then
              if («and»
                (Const.equal («mArg» x0 (leaf 0)) («at» x6 (leaf 0)))
                (Const.equal («mArg» x0 (leaf 1)) («at» x6 (leaf 1)))).label ≠ 0 then
                «mtAt» x1 (leaf 3) x2 («at» x6 (leaf 2)) x4
              else
                «none»
            else
              if («and»
                (Const.eq x5 (leaf 10))
                (Const.eq x7 (leaf 2))).label ≠ 0 then
                if (Const.equal
                  («mArg» x0 (leaf 0))
                  («at» x6 (leaf 0))).label ≠ 0 then
                  «mtAt» x1 (leaf 2) x2 («at» x6 (leaf 1)) x4
                else
                  «none»
              else
                «matchAll» x1 x2 x6 x4
        else
          «none»);
    x2

def «matchTerm» :=
  fun (x0 : T) =>
    let x1 : T →
      T → List T → T := Const.para
      (α := T → T → List T → T)
      «matchStep»
      x0;
    x1

def «noMatch» := fun (_ : T) (_ : T) (_ : List T) => «none»

def «thmRewrite» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List T)
    (x4 : List T)
    (x5 : T)
    (x6 : List T)
    (x7 : T → T → List T → T)
    (x8 : T)
    (x9 : T) =>
    let x10 : T := «bindO»
      (x7 (leaf 0) x9 («replicate» x8 «none»))
      (fun (x10 : T) =>
        «bindO»
          («allSomeT» (Const.children x10))
          (fun (x11 : T) =>
            let x12 : List T := «l4» x5 (Const.node (leaf 0) x6) x11 (leaf 0);
            «mapO»
              (fun (x13 : T) => «pr» x13 («dNode» (leaf 16) x12 ([] : List T)))
              («rootStep» x0 x1 x2 x3 x4 (leaf 16) x12 x9)));
    x10

def «tryRule» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List T)
    (x4 : List T)
    (x5 : T × (T → T → List T → T))
    (x6 : T) =>
    let x7 : T := (let x7 : T := (x5).1;
                   let x8 : T := Const.label x7;
                   if (Const.eq x8 (leaf 0)).label ≠ 0 then
                     let x9 : T := Const.child x7 (leaf 0);
                     let x10 : List T := Const.children (Const.child x7 (leaf 1));
                     «mapO»
                       (fun (x11 : T) => «pr» x11 («dNode» x9 x10 ([] : List T)))
                       («rootStep» x0 x1 x2 x3 x4 x9 x10 x6)
                   else
                     if (Const.eq x8 (leaf 1)).label ≠ 0 then
                       if («and»
                         (Const.eq (Const.label x6) (leaf 11))
                         (Const.eq
                           («mD» x6 (leaf 0))
                           (Const.child x7 (leaf 0)))).label ≠ 0 then
                         «mapO»
                           (fun (x9 : T) =>
                             «pr» x9 («dNode» (leaf 8) ([] : List T) ([] : List T)))
                           («rootStep» x0 x1 x2 x3 x4 (leaf 8) ([] : List T) x6)
                       else
                         «none»
                     else
                       if (Const.eq x8 (leaf 2)).label ≠ 0 then
                         if («and»
                           (Const.eq (Const.label x6) (leaf 11))
                           («and»
                             (Const.lt («mD» x6 (leaf 0)) (Const.child x7 (leaf 0)))
                             («not»
                               («anyT»
                                 (fun (x9 : T) => Const.eq x9 («mD» x6 (leaf 0)))
                                 (Const.children (Const.child x7 (leaf 1))))))).label ≠ 0 then
                           «mapO»
                             (fun (x9 : T) =>
                               «pr» x9 («dNode» (leaf 8) ([] : List T) ([] : List T)))
                             («rootStep» x0 x1 x2 x3 x4 (leaf 8) ([] : List T) x6)
                         else
                           «none»
                       else
                         if (Const.eq x8 (leaf 3)).label ≠ 0 then
                           if («and»
                             (Const.eq (Const.label x6) (leaf 0))
                             (Const.equal
                               («nth» x3 («mD» x6 (leaf 0)))
                               («some» «one»))).label ≠ 0 then
                             «mapO»
                               (fun (x9 : T) =>
                                 «pr» x9 («dNode» (leaf 7) ([] : List T) ([] : List T)))
                               («rootStep» x0 x1 x2 x3 x4 (leaf 7) ([] : List T) x6)
                           else
                             «none»
                         else
                           if (Const.eq x8 (leaf 4)).label ≠ 0 then
                             let x9 : T := Const.child x7 (leaf 0);
                             let x10 : List T := Const.children (Const.child x7 (leaf 1));
                             «bindO»
                               («bindO» («nth» x1 x9) «entryLanguage»)
                               (fun (x11 : T) =>
                                 «bindO»
                                   («eqParts» («thConcl» x11))
                                   (fun (x12 : T) =>
                                     if («sameShape» («p1» x12) x6).label ≠ 0 then
                                       «thmRewrite»
                                         x0
                                         x1
                                         x2
                                         x3
                                         x4
                                         x9
                                         x10
                                         («matchTerm»
                                           (if («isEmpty» x10).label ≠ 0 then
                                             «p1» x12
                                           else
                                             «osubst» x10 («p1» x12)))
                                         («length» («thCtx» x11))
                                         x6
                                     else
                                       «none»))
                           else
                             if (Const.eq x8 (leaf 5)).label ≠ 0 then
                               if («sameShape» (Const.child x7 (leaf 2)) x6).label ≠ 0 then
                                 «thmRewrite»
                                   x0
                                   x1
                                   x2
                                   x3
                                   x4
                                   (Const.child x7 (leaf 0))
                                   (Const.children (Const.child x7 (leaf 1)))
                                   (x5).2
                                   (Const.child x7 (leaf 3))
                                   x6
                               else
                                 «none»
                             else
                               if (Const.eq x8 (leaf 6)).label ≠ 0 then
                                 let x9 : List T := «l2» (Const.child x7 (leaf 0)) (leaf 0);
                                 «mapO»
                                   (fun (x10 : T) => «pr» x10 («dNode» (leaf 17) x9 ([] : List T)))
                                   («rootStep» x0 x1 x2 x3 x4 (leaf 17) x9 x6)
                               else
                                 «none»);
    x7

def «rootRewrite» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List (T × (T → T → List T → T)))
    (x4 : List T)
    (x5 : List T)
    (x6 : T) =>
    let x7 : T := Const.foldr
      (α := T × (T → T → List T → T))
      (β := T → T)
      (fun (x7 : T × (T → T → List T → T)) (x8 : T → T) (x9 : T) =>
        let x10 : T := «tryRule» x0 x1 x2 x4 x5 x7 x9;
        if («isSome» x10).label ≠ 0 then x10 else x8 x9)
      (fun (_ : T) => «none»)
      x3
      x6;
    x7

def «prepareRule» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T ×
      (T →
        T →
          List T →
            T) := (if (Const.eq (Const.label x1) (leaf 4)).label ≠ 0 then
      let x2 : T := Const.child x1 (leaf 0);
      let x3 : List T := Const.children (Const.child x1 (leaf 1));
      let x4 : T := «bindO» («nth» x0 x2) «entryLanguage»;
      let x5 : T := «bindO» x4 (fun (x5 : T) => «eqParts» («thConcl» x5));
      if («isSome» x5).label ≠ 0 then
        let x6 : T := (if («isEmpty» x3).label ≠ 0 then
          «p1» («get» x5)
        else
          «osubst» x3 («p1» («get» x5)));
        (Const.node
          (leaf 5)
          («l4» x2 (Const.node (leaf 0) x3) x6 («length» («thCtx» («get» x4)))),
          «matchTerm» x6)
      else
        (x1, «noMatch»)
    else
      (x1, «noMatch»));
    x2

def «prepareRules» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      (T ×
        (T →
          T →
            List T →
              T)) := Const.foldr
      (α := T)
      (β := List (T × (T → T → List T → T)))
      (fun (x2 : T) (x3 : List (T × (T → T → List T → T))) =>
        ((«prepareRule» x0 x2) :: x3))
      ([] : List (T × (T → T → List T → T)))
      x1;
    x2

def «rebuild» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := Const.node
      (Const.label x0)
      ((Const.child x0 (leaf 0)) :: («mapT» «p1» x1));
    x2

def «marked» :=
  fun (x0 : List T) =>
    let x1 : T := «anyT» (fun (x1 : T) => «p2» («p2» x1)) x0; x1

def «zipTs» :=
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
          ([] : List T)
          (fun (x5 : T) (x6 : List T) => ((«pr» x2 x5) :: (x3 x6))))
      (fun (_ : List T) => ([] : List T))
      x0
      x1;
    x2

def «normStep» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List (T × (T → T → List T → T)))
    (x4 : List T → List T → T → T) =>
    let x5 : List T →
      List T →
        T →
          T := (fun (x5 : List T) (x6 : List T) (x7 : T) =>
      «bindO»
        («childCtxs» x0 x2 x7 x5 x6)
        (fun (x8 : T) =>
          let x9 : List T := Const.children x8;
          «bindO»
            («allSomeT»
              («mapT»
                (fun (x10 : T) =>
                  let x11 : T := «p1» x10;
                  x4 (Const.children («p1» x11)) (Const.children («p2» x11)) («p2» x10))
                («zipTs» x9 («mArgs» x7))))
            (fun (x10 : T) =>
              let x11 : List T := Const.children x10;
              let x12 : T := «rebuild» x7 x11;
              let x13 : T := (if («marked» x11).label ≠ 0 then
                «pr»
                  («dNode»
                    (leaf 2)
                    ([] : List T)
                    («mapT» (fun (x13 : T) => «p1» («p2» x13)) x11))
                  (leaf 1)
              else
                «dRefl»);
              let x14 : T := «rootRewrite» x0 x1 x2 x3 x5 x6 x12;
              if («isSome» x14).label ≠ 0 then
                let x15 : T := «get» x14;
                «mapO»
                  (fun (x16 : T) =>
                    «pr»
                      («p1» x16)
                      («dTrans» x13 («dTrans» («pr» («p2» x15) (leaf 1)) («p2» x16))))
                  (x4 x5 x6 («p1» x15))
              else
                «some» («pr» x12 x13))));
    x5

def «normalize» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List (T × (T → T → List T → T)))
    (x4 : T) =>
    let x5 : List T →
      List T →
        T →
          T := Const.iter
      (α := List T → List T → T → T)
      («normStep» x0 x1 x2 x3)
      (fun (_ : List T) (_ : List T) (x7 : T) => «some» («pr» x7 «dRefl»))
      x4;
    x5

def «joinBy» :=
  fun (x0 : List T → List T → T → T)
    (x1 : List T)
    (x2 : List T)
    (x3 : T)
    (x4 : T) =>
    let x5 : T := «bindO»
      (x0 x1 x2 x3)
      (fun (x5 : T) =>
        «bindO»
          (x0 x1 x2 x4)
          (fun (x6 : T) =>
            if (Const.equal («p1» x5) («p1» x6)).label ≠ 0 then
              «some»
                («dNode»
                  (leaf 18)
                  ([] : List T)
                  («l2» («p1» («p2» x5)) («p1» («p2» x6))))
            else
              «none»));
    x5

def «byNorm» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List (T × (T → T → List T → T)))
    (x4 : T)
    (x5 : List T)
    (x6 : List T)
    (x7 : T)
    (x8 : T) =>
    let x9 : T := «joinBy» («normalize» x0 x1 x2 x3 x4) x5 x6 x7 x8; x9

def «instAt» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := «subst» x2 («instVar» («mArr» x0 x1 «mStar»)); x3

def «byNatInd» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : T)
    (x4 : T)
    (x5 : T)
    (x6 : List (T × (T → T → List T → T)))
    (x7 : T)
    (x8 : List T)
    (x9 : List T)
    (x10 : T)
    (x11 : T) =>
    let x12 : T := Const.lcase
      (α := T)
      (β := T)
      x8
      «none»
      (fun (_ : T) (x13 : List T) =>
        «bindO»
          («lowerHyps» x0 x2 x13 x9)
          (fun (x14 : T) =>
            let x15 : List T := Const.children x14;
            «bindO»
              («byNorm»
                x0
                x1
                x2
                x6
                x7
                x13
                x15
                («instAt» x3 ([] : List T) x10)
                («instAt» x3 ([] : List T) x11))
              (fun (x16 : T) =>
                «bindO»
                  («byNorm»
                    x0
                    x1
                    x2
                    x6
                    x7
                    x8
                    x9
                    («natSuccAt» x4 x10)
                    («subst» x5 («atVar0» x10)))
                  (fun (x17 : T) =>
                    «mapO»
                      (fun (x18 : T) =>
                        «dNode» (leaf 19) («l3» x3 x4 x5) («l3» x16 x17 x18))
                      («byNorm»
                        x0
                        x1
                        x2
                        x6
                        x7
                        x8
                        x9
                        («natSuccAt» x4 x11)
                        («subst» x5 («atVar0» x11)))))));
    x12

def «byListInd» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : T)
    (x4 : T)
    (x5 : T)
    (x6 : List (T × (T → T → List T → T)))
    (x7 : T)
    (x8 : List T)
    (x9 : List T)
    (x10 : T)
    (x11 : T) =>
    let x12 : T := Const.lcase
      (α := T)
      (β := T)
      x8
      «none»
      (fun (x12 : T) (x13 : List T) =>
        «bindO»
          («listPart» x12)
          (fun (x14 : T) =>
            «bindO»
              («lowerHyps» x0 x2 x13 x9)
              (fun (x15 : T) =>
                let x16 : List T := Const.children x15;
                let x17 : List T := (x12 :: (x14 :: x13));
                let x18 : List T := «mapT» «weaken2» x16;
                «bindO»
                  («byNorm»
                    x0
                    x1
                    x2
                    x6
                    x7
                    x13
                    x16
                    («instAt» x3 («single» x14) x10)
                    («instAt» x3 («single» x14) x11))
                  (fun (x19 : T) =>
                    «bindO»
                      («byNorm»
                        x0
                        x1
                        x2
                        x6
                        x7
                        x17
                        x18
                        («listConsAt» x4 x14 x10)
                        («subst» x5 («atVar0» («weakenElem» x10))))
                      (fun (x20 : T) =>
                        «mapO»
                          (fun (x21 : T) =>
                            «dNode» (leaf 20) («l3» x3 x4 x5) («l3» x19 x20 x21))
                          («byNorm»
                            x0
                            x1
                            x2
                            x6
                            x7
                            x17
                            x18
                            («listConsAt» x4 x14 x11)
                            («subst» x5 («atVar0» («weakenElem» x11)))))))));
    x12

def «withHyp» :=
  fun (x0 : List (T × (T → T → List T → T))) (x1 : T) =>
    let x2 : List
      (T ×
        (T →
          T →
            List T →
              T)) := Const.foldr
      (α := T × (T → T → List T → T))
      (β := List (T × (T → T → List T → T)))
      (fun (x2 : T × (T → T → List T → T))
         (x3 : List (T × (T → T → List T → T))) =>
        (x2 :: x3))
      ((Const.node (leaf 6) («single» x1), «noMatch») ::
        ([] : List (T × (T → T → List T → T))))
      x0;
    x2

def «byNatIndHyp» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : T)
    (x4 : T)
    (x5 : List (T × (T → T → List T → T)))
    (x6 : T)
    (x7 : List T)
    (x8 : List T)
    (x9 : T)
    (x10 : T) =>
    let x11 : T := Const.lcase
      (α := T)
      (β := T)
      x7
      «none»
      (fun (_ : T) (x12 : List T) =>
        «bindO»
          («lowerHyps» x0 x2 x12 x8)
          (fun (x13 : T) =>
            let x14 : List T := Const.children x13;
            «bindO»
              («byNorm»
                x0
                x1
                x2
                x5
                x6
                x12
                x14
                («instAt» x3 ([] : List T) x9)
                («instAt» x3 ([] : List T) x10))
              (fun (x15 : T) =>
                let x16 : List T := «append» x8 («single» («mEq» x9 x10));
                «bindO»
                  («normalize» x0 x1 x2 x5 x6 x7 x16 («mEq» x9 x10))
                  (fun (x17 : T) =>
                    let x18 : T := «p1» x17;
                    «bindO»
                      («byNorm»
                        x0
                        x1
                        x2
                        («withHyp» x5 («length» x16))
                        x6
                        x7
                        («append» x16 («single» x18))
                        («natSuccAt» x4 x9)
                        («natSuccAt» x4 x10))
                      (fun (x19 : T) =>
                        let x20 : T := «dNode»
                          (leaf 24)
                          («single» («mEq» x9 x10))
                          («l2»
                            («p1» («p2» x17))
                            («dNode» (leaf 21) («single» («length» x8)) ([] : List T)));
                        «some»
                          («dNode»
                            (leaf 28)
                            («l2» x3 x4)
                            («l2» x15 («dNode» (leaf 22) («single» x18) («l2» x20 x19)))))))));
    x11

def «byListIndHyp» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : T)
    (x4 : T)
    (x5 : List (T × (T → T → List T → T)))
    (x6 : T)
    (x7 : List T)
    (x8 : List T)
    (x9 : T)
    (x10 : T) =>
    let x11 : T := Const.lcase
      (α := T)
      (β := T)
      x7
      «none»
      (fun (x11 : T) (x12 : List T) =>
        «bindO»
          («listPart» x11)
          (fun (x13 : T) =>
            «bindO»
              («lowerHyps» x0 x2 x12 x8)
              (fun (x14 : T) =>
                let x15 : List T := Const.children x14;
                «bindO»
                  («byNorm»
                    x0
                    x1
                    x2
                    x5
                    x6
                    x12
                    x15
                    («instAt» x3 («single» x13) x9)
                    («instAt» x3 («single» x13) x10))
                  (fun (x16 : T) =>
                    let x17 : List T := (x11 :: (x13 :: x12));
                    let x18 : T := «weakenElem» («mEq» x9 x10);
                    let x19 : List T := «append» («mapT» «weaken2» x15) («single» x18);
                    «bindO»
                      («normalize» x0 x1 x2 x5 x6 x17 x19 x18)
                      (fun (x20 : T) =>
                        let x21 : T := «p1» x20;
                        «bindO»
                          («byNorm»
                            x0
                            x1
                            x2
                            («withHyp» x5 («length» x19))
                            x6
                            x17
                            («append» x19 («single» x21))
                            («listConsAt» x4 x13 x9)
                            («listConsAt» x4 x13 x10))
                          (fun (x22 : T) =>
                            let x23 : T := «dNode»
                              (leaf 24)
                              («single» x18)
                              («l2»
                                («p1» («p2» x20))
                                («dNode» (leaf 21) («single» («length» x15)) ([] : List T)));
                            «some»
                              («dNode»
                                (leaf 29)
                                («l2» x3 x4)
                                («l2» x16 («dNode» (leaf 22) («single» x21) («l2» x23 x22))))))))));
    x11

def «headChild» :=
  fun (x0 : T) =>
    let x1 : T := (if («or»
      («mIs» (leaf 3) (leaf 1) x0)
      («mIs» (leaf 4) (leaf 1) x0)).label ≠ 0 then
      «some» (leaf 0)
    else
      if («or»
        («mIs» (leaf 8) (leaf 3) x0)
        («mIs» (leaf 9) (leaf 3) x0)).label ≠ 0 then
        «some» (leaf 2)
      else
        if («mIs» (leaf 10) (leaf 2) x0).label ≠ 0 then
          «some» (leaf 1)
        else
          «none»);
    x1

def «keepsFold» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (if («or»
      (Const.eq x0 (leaf 8))
      (Const.eq x0 (leaf 9))).label ≠ 0 then
      Const.lt x1 (leaf 2)
    else
      if (Const.eq x0 (leaf 10)).label ≠ 0 then
        Const.eq x1 (leaf 0)
      else
        leaf 0);
    x2

def «keepsWeak» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (if (Const.eq x0 (leaf 5)).label ≠ 0 then
      leaf 1
    else
      «keepsFold» x0 x1);
    x2

def «ufTail» :=
  fun (x0 : List (T → T)) =>
    let x1 : List
      (T →
        T) := Const.lcase
      (α := T → T)
      (β := List (T → T))
      x0
      ([] : List (T → T))
      (fun (_ : T → T) (x2 : List (T → T)) => x2);
    x1

def «ufAt» :=
  fun (x0 : List (T → T)) (x1 : T) =>
    let x2 : T →
      T := Const.lcase
      (α := T → T)
      (β := T → T)
      (Const.iter (α := List (T → T)) «ufTail» x0 x1)
      (fun (_ : T) => leaf 0)
      (fun (x2 : T → T) (_ : List (T → T)) => x2);
    x2

def «ufSum» :=
  fun (x0 : List (T → T)) (x1 : T) =>
    let x2 : T := Const.foldr
      (α := T → T)
      (β := T)
      (fun (x2 : T → T) (x3 : T) => Const.add (x2 x1) x3)
      (leaf 0)
      («ufTail» x0);
    x2

def «usesStep» :=
  fun (x0 : T) (x1 : List (T → T)) =>
    let x2 : T →
      T := (fun (x2 : T) =>
      let x3 : T := Const.label x0;
      let x4 : T := «length» («mArgs» x0);
      if (Const.eq x3 (leaf 0)).label ≠ 0 then
        if (Const.eq («mD» x0 (leaf 0)) x2).label ≠ 0 then leaf 1 else leaf 0
      else
        if (Const.eq x3 (leaf 5)).label ≠ 0 then
          Const.mul (leaf 2) («ufSum» x1 (Const.add x2 (leaf 1)))
        else
          if («and»
            («or» (Const.eq x3 (leaf 8)) (Const.eq x3 (leaf 9)))
            (Const.eq x4 (leaf 3))).label ≠ 0 then
            «ufAt» x1 (leaf 3) x2
          else
            if («and»
              (Const.eq x3 (leaf 10))
              (Const.eq x4 (leaf 2))).label ≠ 0 then
              «ufAt» x1 (leaf 2) x2
            else
              «ufSum» x1 x2);
    x2

def «uses» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := Const.para (α := T → T) «usesStep» x0 x1; x2

def «atRoot» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List (T × (T → T → List T → T)))
    (x4 : T → List T → List T → T → T)
    (x5 : List T)
    (x6 : List T)
    (x7 : T)
    (x8 : T)
    (x9 : T) =>
    let x10 : T := (let x10 : T := «rootRewrite» x0 x1 x2 x3 x5 x6 x8;
                    if («isSome» x10).label ≠ 0 then
                      let x11 : T := «get» x10;
                      «mapO»
                        (fun (x12 : T) =>
                          «pr»
                            («p1» x12)
                            («dTrans» x9 («dTrans» («pr» («p2» x11) (leaf 1)) («p2» x12))))
                        (x4 x7 x5 x6 («p1» x11))
                    else
                      «some» («pr» x8 x9));
    x10

def «headStep» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List (T × (T → T → List T → T)))
    (x4 : T → List T → List T → T → T)
    (x5 : List T)
    (x6 : List T)
    (x7 : T) =>
    let x8 : T := (if («mIs» (leaf 6) (leaf 2) x7).label ≠ 0 then
      «bindO»
        (x4 (leaf 0) x5 x6 («mArg» x7 (leaf 0)))
        (fun (x8 : T) =>
          let x9 : T := «p1» x8;
          let x10 : T := «mArg» x7 (leaf 1);
          «bindO»
            (if («mIs» (leaf 5) (leaf 1) x9).label ≠ 0 then
              if (Const.lt
                («uses» («mArg» x9 (leaf 0)) (leaf 0))
                (leaf 2)).label ≠ 0 then
                «some» («pr» x10 «dRefl»)
              else
                x4 (leaf 1) x5 x6 x10
            else
              x4 (leaf 0) x5 x6 x10)
            (fun (x11 : T) =>
              «atRoot»
                x0
                x1
                x2
                x3
                x4
                x5
                x6
                (leaf 0)
                («mApp» x9 («p1» x11))
                («dCong» («l2» («p2» x8) («p2» x11)))))
    else
      let x8 : T := «rootRewrite» x0 x1 x2 x3 x5 x6 x7;
      if («isSome» x8).label ≠ 0 then
        let x9 : T := «get» x8;
        «mapO»
          (fun (x10 : T) =>
            «pr» («p1» x10) («dTrans» («pr» («p2» x9) (leaf 1)) («p2» x10)))
          (x4 (leaf 0) x5 x6 («p1» x9))
      else
        let x9 : T := «headChild» x7;
        if («isSome» x9).label ≠ 0 then
          let x10 : T := «get» x9;
          let x11 : List T := «mArgs» x7;
          «bindO»
            («nth» x11 x10)
            (fun (x12 : T) =>
              «bindO»
                (x4 (leaf 0) x5 x6 x12)
                (fun (x13 : T) =>
                  if («p2» («p2» x13)).label ≠ 0 then
                    «atRoot»
                      x0
                      x1
                      x2
                      x3
                      x4
                      x5
                      x6
                      (leaf 0)
                      (Const.node
                        (Const.label x7)
                        ((Const.child x7 (leaf 0)) :: («setAt» x11 x10 («p1» x13))))
                      («dCong»
                        («mapT»
                          (fun (x14 : T) =>
                            if (Const.eq x14 x10).label ≠ 0 then «p2» x13 else «dRefl»)
                          («range» («length» x11))))
                  else
                    «some» («pr» x7 «dRefl»)))
        else
          «some» («pr» x7 «dRefl»));
    x8

def «deepStep» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List (T × (T → T → List T → T)))
    (x4 : T → List T → List T → T → T)
    (x5 : T)
    (x6 : List T)
    (x7 : List T)
    (x8 : T)
    (x9 : T) =>
    let x10 : T := (let x10 : T := Const.label x8;
                    let x11 : List T := «mArgs» x8;
                    if (Const.eq x5 (leaf 1)).label ≠ 0 then
                      «bindO»
                        («allSomeT»
                          («mapT»
                            (fun (x12 : T) =>
                              if («keepsWeak» x10 x12).label ≠ 0 then
                                «some» («pr» («at» x11 x12) «dRefl»)
                              else
                                x4 (leaf 1) x6 x7 («at» x11 x12))
                            («range» («length» x11))))
                        (fun (x12 : T) =>
                          let x13 : List T := Const.children x12;
                          let x14 : T := «rebuild» x8 x13;
                          let x15 : T := «dTrans» x9 («dCong» («mapT» «p2» x13));
                          if («marked» x13).label ≠ 0 then
                            «atRoot» x0 x1 x2 x3 x4 x6 x7 (leaf 1) x14 x15
                          else
                            «some» («pr» x14 x15))
                    else
                      «bindO»
                        («childCtxs» x0 x2 x8 x6 x7)
                        (fun (x12 : T) =>
                          let x13 : List T := Const.children x12;
                          «bindO»
                            (let x14 : List T := «zipTs» x13 x11;
                             «allSomeT»
                               («mapT»
                                 (fun (x15 : T) =>
                                   let x16 : T := «at» x14 x15;
                                   let x17 : T := «p1» x16;
                                   if («and»
                                     (Const.eq x5 (leaf 2))
                                     («keepsFold» x10 x15)).label ≠ 0 then
                                     «some» («pr» («p2» x16) «dRefl»)
                                   else
                                     x4
                                       x5
                                       (Const.children («p1» x17))
                                       (Const.children («p2» x17))
                                       («p2» x16))
                                 («range» («length» x14))))
                            (fun (x14 : T) =>
                              let x15 : List T := Const.children x14;
                              let x16 : T := «rebuild» x8 x15;
                              if (Const.eq x5 (leaf 2)).label ≠ 0 then
                                let x17 : T := «dTrans» x9 («dCong» («mapT» «p2» x15));
                                if («marked» x15).label ≠ 0 then
                                  «atRoot» x0 x1 x2 x3 x4 x6 x7 (leaf 2) x16 x17
                                else
                                  «some» («pr» x16 x17)
                              else
                                let x17 : T := «dCong» («mapT» «p2» x15);
                                let x18 : T := «rootRewrite» x0 x1 x2 x3 x6 x7 x16;
                                if («isSome» x18).label ≠ 0 then
                                  let x19 : T := «get» x18;
                                  «mapO»
                                    (fun (x20 : T) =>
                                      «pr»
                                        («p1» x20)
                                        («dTrans»
                                          x9
                                          («dTrans»
                                            x17
                                            («dTrans» («pr» («p2» x19) (leaf 1)) («p2» x20)))))
                                    (x4 (leaf 3) x6 x7 («p1» x19))
                                else
                                  «some» («pr» x16 («dTrans» x9 x17)))));
    x10

def «evalStep» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List (T × (T → T → List T → T)))
    (x4 : T → List T → List T → T → T) =>
    let x5 : T →
      List T →
        List T →
          T →
            T := (fun (x5 : T) (x6 : List T) (x7 : List T) (x8 : T) =>
      «bindO»
        («headStep» x0 x1 x2 x3 x4 x6 x7 x8)
        (fun (x9 : T) =>
          if (Const.eq x5 (leaf 0)).label ≠ 0 then
            «some» x9
          else
            «deepStep» x0 x1 x2 x3 x4 x5 x6 x7 («p1» x9) («p2» x9)));
    x5

def «eval» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List (T × (T → T → List T → T)))
    (x4 : T) =>
    let x5 : T →
      List T →
        List T →
          T →
            T := Const.iter
      (α := T → List T → List T → T → T)
      («evalStep» x0 x1 x2 x3)
      (fun (_ : T) (_ : List T) (_ : List T) (x8 : T) =>
        «some» («pr» x8 «dRefl»))
      x4;
    x5

def «whnf» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List (T × (T → T → List T → T)))
    (x4 : T) =>
    let x5 : List T → List T → T → T := «eval» x0 x1 x2 x3 x4 (leaf 0); x5

def «normalizeW» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List (T × (T → T → List T → T)))
    (x4 : T) =>
    let x5 : List T → List T → T → T := «eval» x0 x1 x2 x3 x4 (leaf 3); x5

def «byNormW» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List (T × (T → T → List T → T)))
    (x4 : T)
    (x5 : List T)
    (x6 : List T)
    (x7 : T)
    (x8 : T) =>
    let x9 : T := «joinBy» («normalizeW» x0 x1 x2 x3 x4) x5 x6 x7 x8; x9

def «abstractVar» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «mLam»
      x1
      («subst»
        («weaken1» x2)
        (fun (x3 : T) =>
          if (Const.eq x3 (Const.add x0 (leaf 1))).label ≠ 0 then
            «mVar» (leaf 0)
          else
            «mVar» x3));
    x3

def «byFunExt» :=
  fun (x0 : T) (x1 : T) (x2 : List T → List T → T → T → T) =>
    let x3 : List T →
      List T →
        T →
          T →
            T := (fun (x3 : List T) (x4 : List T) (x5 : T) (x6 : T) =>
      «bindO»
        («bindO» («mTypeIn» x0 x1 x3 x5) «expParts»)
        (fun (x7 : T) =>
          «mapO»
            (fun (x8 : T) => «dNode» (leaf 26) ([] : List T) («single» x8))
            (x2
              ((«p1» x7) :: x3)
              («mapT» «weaken1» x4)
              («mApp» («weaken1» x5) («mVar» (leaf 0)))
              («mApp» («weaken1» x6) («mVar» (leaf 0))))));
    x3

def «bySplit» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : List T → List T → T → T → T) =>
    let x4 : List T →
      List T →
        T →
          T →
            T := (fun (x4 : List T) (x5 : List T) (x6 : T) (x7 : T) =>
      «bindO»
        («nth» x4 x2)
        (fun (x8 : T) =>
          «bindO»
            («coprodParts» x8)
            (fun (x9 : T) =>
              let x10 : T := «p1» x9;
              let x11 : T := «p2» x9;
              let x12 : T := «abstractVar» x2 x8 x6;
              let x13 : T := «abstractVar» x2 x8 x7;
              let x14 : T →
                T →
                  T := (fun (x14 : T) (x15 : T) =>
                «mApp» («weaken1» x15) («mArr» x14 («l2» x10 x11) («mVar» (leaf 0))));
              «bindO»
                (x3 (x10 :: x4) («mapT» «weaken1» x5) (x14 x0 x12) (x14 x0 x13))
                (fun (x15 : T) =>
                  «bindO»
                    (x3 (x11 :: x4) («mapT» «weaken1» x5) (x14 x1 x12) (x14 x1 x13))
                    (fun (x16 : T) =>
                      let x17 : T := «dNode»
                        (leaf 26)
                        ([] : List T)
                        («single» («dNode» (leaf 34) («l2» x0 x1) («l2» x15 x16)));
                      let x18 : T := «dNode»
                        (leaf 2)
                        ([] : List T)
                        («l2»
                          («dNode» (leaf 3) ([] : List T) ([] : List T))
                          («dNode» (leaf 3) ([] : List T) ([] : List T)));
                      let x19 : T := «dNode»
                        (leaf 18)
                        ([] : List T)
                        («l2»
                          («dNode»
                            (leaf 2)
                            ([] : List T)
                            («l2»
                              («dNode» (leaf 17) («l2» («length» x5) (leaf 0)) ([] : List T))
                              («dNode» (leaf 0) ([] : List T) ([] : List T))))
                          («dNode» (leaf 0) ([] : List T) ([] : List T)));
                      let x20 : T := «mEq»
                        («mApp» x12 («mVar» x2))
                        («mApp» x13 («mVar» x2));
                      «some»
                        («dNode»
                          (leaf 22)
                          («single» («mEq» x12 x13))
                          («l2» x17 («dNode» (leaf 24) («single» x20) («l2» x18 x19)))))))));
    x4

def «byListIndWith» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : T)
    (x3 : T)
    (x4 : List T → List T → T → T → T)
    (x5 : List T → List T → T → T → T) =>
    let x6 : List T →
      List T →
        T →
          T →
            T := (fun (x6 : List T) (x7 : List T) (x8 : T) (x9 : T) =>
      Const.lcase
        (α := T)
        (β := T)
        x6
        «none»
        (fun (x10 : T) (x11 : List T) =>
          «bindO»
            («listPart» x10)
            (fun (x12 : T) =>
              «bindO»
                («lowerHyps» x0 x1 x11 x7)
                (fun (x13 : T) =>
                  let x14 : List T := Const.children x13;
                  «bindO»
                    (x4
                      x11
                      x14
                      («instAt» x2 («single» x12) x8)
                      («instAt» x2 («single» x12) x9))
                    (fun (x15 : T) =>
                      «mapO»
                        (fun (x16 : T) => «dNode» (leaf 29) («l2» x2 x3) («l2» x15 x16))
                        (x5
                          (x10 :: (x12 :: x11))
                          («append»
                            («mapT» «weaken2» x14)
                            («single» («weakenElem» («mEq» x8 x9))))
                          («listConsAt» x3 x12 x8)
                          («listConsAt» x3 x12 x9)))))));
    x6

def «byRoseInd» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : T)
    (x4 : T)
    (x5 : T)
    (x6 : T)
    (x7 : List (T × (T → T → List T → T)))
    (x8 : T)
    (x9 : List T)
    (x10 : T)
    (x11 : T) =>
    let x12 : T := (if (Const.eq («length» x9) (leaf 1)).label ≠ 0 then
      let x12 : T := «at» x9 (leaf 0);
      «bindO»
        («roseLabel» x12)
        (fun (x13 : T) =>
          «bindO»
            («mTypeIn» x0 x2 x9 x10)
            (fun (x14 : T) =>
              let x15 : List T := «l2» («list» x12) x13;
              «bindO»
                («byNorm»
                  x0
                  x1
                  x2
                  x7
                  x8
                  x15
                  ([] : List T)
                  («roseNodeAt» x3 x12 x13 x10)
                  («subst» x6 («atVar0» («roseMapAt» x4 x5 x14 x10))))
                (fun (x16 : T) =>
                  «mapO»
                    (fun (x17 : T) => «dNode» (leaf 32) («l4» x3 x4 x5 x6) («l2» x16 x17))
                    («byNorm»
                      x0
                      x1
                      x2
                      x7
                      x8
                      x15
                      ([] : List T)
                      («roseNodeAt» x3 x12 x13 x11)
                      («subst» x6 («atVar0» («roseMapAt» x4 x5 x14 x11)))))))
    else
      «none»);
    x12

def «byRoseIndHyp» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : List T → List T → T → T → T) =>
    let x4 : List T →
      List T →
        T →
          T →
            T := (fun (x4 : List T) (_ : List T) (x6 : T) (x7 : T) =>
      if (Const.eq («length» x4) (leaf 1)).label ≠ 0 then
        let x8 : T := «at» x4 (leaf 0);
        «bindO»
          («roseLabel» x8)
          (fun (x9 : T) =>
            «mapO»
              (fun (x10 : T) => «dNode» (leaf 33) («l3» x0 x1 x2) («single» x10))
              (x3
                («l2» («list» x8) x9)
                («single» («roseHyp» x1 x2 («mEq» x6 x7)))
                («roseNodeAt» x0 x8 x9 x6)
                («roseNodeAt» x0 x8 x9 x7)))
      else
        «none»);
    x4

end GebMirror.Metalogic

end
