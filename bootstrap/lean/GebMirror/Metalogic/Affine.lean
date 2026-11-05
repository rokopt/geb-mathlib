module

public import GebMirror.Metalogic.Printer

/-! Generated from a Geb program by `bootstrap/stage1/lean.geb`. -/

@[expose] public section

open Geb.Kernel
open Geb.Kernel renaming Tree → T

namespace GebMirror.Metalogic

def «Affine/CFs.tail» :=
  fun (x0 : List (T → T → T)) =>
    Const.lcase
      (α := T → T → T)
      (β := List (T → T → T))
      x0
      ([] : List (T → T → T))
      (fun (_ : T → T → T) (x2 : List (T → T → T)) => x2)

def «Affine.isData» :=
  fun (x0 : T) =>
    let x1 : T := Const.fold
      (α := T)
      (fun (x1 : T) (x2 : List T) =>
        «Prelude.and»
          («Base.not» (Const.eq x1 (leaf 3)))
          («Base.allT» (fun (x3 : T) => x3) x2))
      x0;
    x1

def «Affine.dBang» :=
  fun (x0 : T) =>
    let x1 : T := Const.label (Const.child x0 (leaf 0)); x1

def «Affine.dKids» :=
  fun (x0 : T) =>
    let x1 : List T := «Prelude.tail» (Const.children x0); x1

def «Affine.dMk» :=
  fun (x0 : T) (x1 : T) (x2 : List T) =>
    let x3 : T := Const.node x0 (x1 :: x2); x3

def «Affine.dTy» :=
  fun (x0 : T) =>
    let x1 : T := Const.fold
      (α := T)
      (fun (x1 : T) (x2 : List T) => Const.node x1 («Prelude.tail» x2))
      x0;
    x1

def «Affine.dData» :=
  fun (x0 : T) => let x1 : T := «Affine.isData» («Affine.dTy» x0); x1

def «Affine.dZero» :=
  fun (x0 : T) =>
    let x1 : T := Const.fold
      (α := T)
      (fun (x1 : T) (x2 : List T) => Const.node x1 ((leaf 0) :: x2))
      x0;
    x1

def «Affine.dArrow» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Affine.dMk»
      (leaf 3)
      (leaf 0)
      (x0 :: («Prelude.single» x1));
    x2

def «Affine.dList» :=
  fun (x0 : T) =>
    let x1 : T := «Affine.dMk» (leaf 4) (leaf 0) («Prelude.single» x0); x1

def «Affine.withBang» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (if («Affine.dData» x0).label ≠ 0 then
      x0
    else
      «Affine.dMk» (Const.label x0) x1 («Affine.dKids» x0));
    x2

def «Affine.dShift» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Affine.withBang» x0 (Const.add («Affine.dBang» x0) x1);
    x2

def «Affine.dUnbox» :=
  fun (x0 : T) =>
    let x1 : T := «Affine.withBang»
      x0
      (Const.sub («Affine.dBang» x0) (leaf 1));
    x1

def «Affine.decorate» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := Const.fold
      (α := T → T)
      (fun (x2 : T) (x3 : List (T → T)) =>
        let x4 : List T →
          T := Const.foldr
          (α := T → T)
          (β := List T → T)
          (fun (x4 : T → T) (x5 : List T → T) (x6 : List T) =>
            Const.lcase
              (α := T)
              (β := T)
              x6
              «Prelude.none»
              (fun (x7 : T) (x8 : List T) =>
                «Base.bindO»
                  (x4 x7)
                  (fun (x9 : T) =>
                    «Base.mapO»
                      (fun (x10 : T) => Const.node (leaf 0) (x9 :: (Const.children x10)))
                      (x5 x8))))
          (fun (x4 : List T) =>
            if («Base.isEmpty» x4).label ≠ 0 then
              «Prelude.some» (Const.node (leaf 0) ([] : List T))
            else
              «Prelude.none»)
          x3;
        fun (x5 : T) =>
          «Base.mapO»
            (fun (x6 : T) =>
              let x7 : List T := Const.children x6;
              «Affine.dMk»
                x2
                (if («Prelude.and»
                  («Base.not» (Const.eq x2 (leaf 3)))
                  («Base.allT» «Affine.dData» x7)).label ≠ 0 then
                  leaf 0
                else
                  Const.label x5)
                x7)
            (x4 (Const.children x5)))
      x0
      x1;
    x2

def «Affine.isPrefix» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := Const.equal
      x0
      (Const.node
        (leaf 0)
        («Base.take»
          («Prelude.length» (Const.children x0))
          (Const.children x1)));
    x2

def «Affine.snocPath» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := Const.node
      (leaf 0)
      («Prelude.append» (Const.children x0) («Prelude.single» x1));
    x2

def «Affine.countPath» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) =>
        if (Const.equal x2 x0).label ≠ 0 then Const.add x3 (leaf 1) else x3)
      (leaf 0)
      x1;
    x2

def «Affine.belowPath» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := «Base.anyT»
      (fun (x2 : T) =>
        «Prelude.and»
          (Const.lt
            («Prelude.length» (Const.children x0))
            («Prelude.length» (Const.children x2)))
          («Affine.isPrefix» x0 x2))
      x1;
    x2

def «Affine.ctStep» :=
  fun (x0 : List T) (x1 : T) (x2 : List (T → T → T)) =>
    let x3 : T →
      T →
        T := (let x3 : T →
                T →
                  T →
                    T := Const.foldr
                (α := T → T → T)
                (β := T → T → T → T)
                (fun (x3 : T → T → T)
                   (x4 : T → T → T → T)
                   (x5 : T)
                   (x6 : T)
                   (x7 : T) =>
                  let x8 : T := «Affine.snocPath» x5 x7;
                  «Prelude.and»
                    (if («Base.anyT»
                      (fun (x9 : T) => «Affine.isPrefix» x8 x9)
                      x0).label ≠ 0 then
                      x3 x8 x6
                    else
                      leaf 1)
                    (x4 x5 x6 (Const.add x7 (leaf 1))))
                (fun (_ : T) (_ : T) (_ : T) => leaf 1)
                («Affine/CFs.tail» x2);
              fun (x4 : T) (x5 : T) =>
                let x6 : T := Const.add («Affine.dBang» x1) x5;
                let x7 : T := «Affine.countPath» x4 x0;
                if («Affine.dData» x1).label ≠ 0 then
                  leaf 1
                else
                  if («Prelude.or»
                    (Const.lt (leaf 1) x7)
                    («Prelude.and»
                      (Const.lt (leaf 0) x7)
                      («Affine.belowPath» x4 x0))).label ≠ 0 then
                    Const.lt (leaf 0) x6
                  else
                    «Prelude.or» (Const.lt (leaf 0) x7) (x3 x4 x6 (leaf 0)));
    x3

def «Affine.contracts» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := Const.para
      (α := T → T → T)
      («Affine.ctStep» x0)
      x1
      (Const.node (leaf 0) ([] : List T))
      (leaf 0);
    x2

def «Affine.dPlace» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := Const.foldr
      (α := T)
      (β := T → T)
      (fun (x2 : T) (x3 : T → T) (x4 : T) =>
        «Base.bindO»
          («Prelude.nth» («Affine.dKids» x4) x2)
          (fun (x5 : T) =>
            x3
              (if («Affine.dData» x4).label ≠ 0 then
                x5
              else
                «Affine.dShift» x5 («Affine.dBang» x4))))
      «Prelude.some»
      x1
      x0;
    x2

def «Affine.plMk» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := Const.node (leaf 0) (x0 :: («Prelude.single» x1)); x2

def «Affine.plVar» :=
  fun (x0 : T) => let x1 : T := Const.child x0 (leaf 0); x1

def «Affine.plPath» :=
  fun (x0 : T) => let x1 : T := Const.child x0 (leaf 1); x1

def «Affine.termPlace» :=
  fun (x0 : T) =>
    let x1 : T := Const.para
      (α := T)
      (fun (x1 : T) (x2 : List T) =>
        let x3 : T := Const.label x1;
        let x4 : T := Const.eq («Prelude.length» x2) (leaf 1);
        if (Const.eq x3 (leaf 8)).label ≠ 0 then
          if (x4).label ≠ 0 then
            «Prelude.some»
              («Affine.plMk»
                (Const.label («Prelude.at» (Const.children x1) (leaf 0)))
                (Const.node (leaf 0) ([] : List T)))
          else
            «Prelude.none»
        else
          if (Const.eq x3 (leaf 13)).label ≠ 0 then
            if (x4).label ≠ 0 then
              «Base.mapO»
                (fun (x5 : T) =>
                  «Affine.plMk»
                    («Affine.plVar» x5)
                    («Affine.snocPath» («Affine.plPath» x5) (leaf 0)))
                («Prelude.at» x2 (leaf 0))
            else
              «Prelude.none»
          else
            if (Const.eq x3 (leaf 14)).label ≠ 0 then
              if (x4).label ≠ 0 then
                «Base.mapO»
                  (fun (x5 : T) =>
                    «Affine.plMk»
                      («Affine.plVar» x5)
                      («Affine.snocPath» («Affine.plPath» x5) (leaf 1)))
                  («Prelude.at» x2 (leaf 0))
              else
                «Prelude.none»
            else
              «Prelude.none»)
      x0;
    x1

def «Affine.eraseT» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := T → List T)
      (fun (x2 : T) (x3 : T → List T) (x4 : T) =>
        if («Prelude.and» («Base.not» x4) (Const.equal x2 x0)).label ≠ 0 then
          x3 (leaf 1)
        else
          (x2 :: (x3 x4)))
      (fun (_ : T) => ([] : List T))
      x1
      (leaf 0);
    x2

def «Affine.diffT» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T → List T)
      (fun (x2 : T) (x3 : List T → List T) (x4 : List T) =>
        x3 («Affine.eraseT» x2 x4))
      (fun (x2 : List T) => x2)
      x1
      x0;
    x2

def «Affine.usageMax» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List T := «Prelude.append» x0 («Affine.diffT» x1 x0); x2

def «Affine.res» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := «Prelude.some»
      (Const.node
        (leaf 0)
        (x0 :: («Prelude.single» (Const.node (leaf 0) x1))));
    x2

def «Affine.rD» :=
  fun (x0 : T) => let x1 : T := Const.child x0 (leaf 0); x1

def «Affine.rU» :=
  fun (x0 : T) =>
    let x1 : List T := Const.children (Const.child x0 (leaf 1)); x1

def «Affine.ctxAt» :=
  fun (x0 : List T) (x1 : T) => let x2 : T := «Prelude.nth» x0 x1; x2

def «Affine.occurrence» :=
  fun (x0 : List T) (x1 : T) (x2 : T) =>
    let x3 : T := «Base.bindO»
      («Affine.ctxAt» x0 («Affine.plVar» x2))
      (fun (x3 : T) =>
        let x4 : T := Const.child x3 (leaf 1);
        «Base.bindO»
          («Affine.dPlace»
            (Const.child x3 (leaf 0))
            (Const.children («Affine.plPath» x2)))
          (fun (x5 : T) =>
            if (Const.lt x1 x4).label ≠ 0 then
              «Prelude.none»
            else
              if («Affine.dData» x5).label ≠ 0 then
                «Affine.res» x5 («Prelude.single» x2)
              else
                if (Const.lt («Affine.dBang» x5) (Const.sub x1 x4)).label ≠ 0 then
                  «Prelude.none»
                else
                  «Affine.res»
                    («Affine.withBang»
                      x5
                      (Const.sub («Affine.dBang» x5) (Const.sub x1 x4)))
                    («Prelude.single» x2)));
    x3

def «Affine.enter» :=
  fun (x0 : List T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : T := (if («Base.allT»
      (fun (x4 : T) =>
        let x5 : T := «Affine.ctxAt» x0 («Affine.plVar» x4);
        if («Prelude.isSome» x5).label ≠ 0 then
          «Base.not» (Const.lt x2 (Const.child («Prelude.get» x5) (leaf 1)))
        else
          leaf 0)
      («Affine.rU» x3)).label ≠ 0 then
      let x4 : T := «Affine.rD» x3;
      if («Affine.dData» x4).label ≠ 0 then
        «Prelude.some» x3
      else
        if (Const.lt (Const.add («Affine.dBang» x4) x2) x1).label ≠ 0 then
          «Prelude.none»
        else
          «Affine.res»
            («Affine.withBang»
              x4
              (Const.sub (Const.add («Affine.dBang» x4) x2) x1))
            («Affine.rU» x3)
    else
      «Prelude.none»);
    x4

def «Affine.subOf» :=
  fun (x0 : List T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : T := «Base.bindO»
      x2
      (fun (x4 : T) => «Affine.enter» x0 x1 (Const.label x3) x4);
    x4

def «Affine.iterD» :=
  fun (x0 : T) =>
    let x1 : T := «Affine.dArrow»
      («Affine.dMk» (leaf 3) (leaf 1) (x0 :: («Prelude.single» x0)))
      («Affine.dArrow»
        («Affine.dShift» x0 (leaf 1))
        («Affine.dArrow»
          («Affine.dZero» (leaf 0))
          («Affine.dShift» x0 (leaf 1))));
    x1

def «Affine.foldD» :=
  fun (x0 : T) =>
    let x1 : T := «Affine.dArrow»
      («Affine.dMk»
        (leaf 3)
        (leaf 1)
        ((«Affine.dZero» (leaf 0)) ::
          («Prelude.single» («Affine.dArrow» («Affine.dList» x0) x0))))
      («Affine.dArrow»
        («Affine.dZero» (leaf 0))
        («Affine.dShift» x0 (leaf 1)));
    x1

def «Affine.foldrD» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Affine.dArrow»
      («Affine.dMk»
        (leaf 3)
        (leaf 1)
        ((«Affine.dUnbox» x0) :: («Prelude.single» («Affine.dArrow» x1 x1))))
      («Affine.dArrow»
        («Affine.dShift» x1 (leaf 1))
        («Affine.dArrow» («Affine.dList» x0) («Affine.dShift» x1 (leaf 1))));
    x2

def «Affine.lcaseD» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Affine.dArrow»
      («Affine.dList» x0)
      («Affine.dArrow»
        x1
        («Affine.dArrow»
          («Affine.dArrow» x0 («Affine.dArrow» («Affine.dList» x0) x1))
          x1));
    x2

def «Affine.noBang» :=
  fun (x0 : T) =>
    let x1 : T := «Prelude.or»
      («Affine.dData» x0)
      (Const.eq («Affine.dBang» x0) (leaf 0));
    x1

def «Affine.lcaseSat» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : T := (let x5 : T := «Affine.rD» x2;
                   let x6 : T := «Affine.rD» x3;
                   let x7 : T := «Affine.rD» x4;
                   let x8 : List T := «Affine.dKids» x7;
                   if («Prelude.and»
                     (Const.equal («Affine.dTy» x5) («Check.tyList» x0))
                     («Prelude.and»
                       (Const.equal («Affine.dTy» x6) x1)
                       («Prelude.and»
                         (Const.equal
                           («Affine.dTy» x7)
                           («Check.tyArrow» x0 («Check.tyArrow» («Check.tyList» x0) x1)))
                         («Prelude.and»
                           («Affine.noBang» x5)
                           (Const.eq («Prelude.length» x8) (leaf 2)))))).label ≠ 0 then
                     let x9 : T := «Prelude.at» x8 (leaf 1);
                     let x10 : List T := «Affine.dKids» x9;
                     if («Prelude.and»
                       (Const.eq («Prelude.length» x10) (leaf 2))
                       («Prelude.and»
                         (Const.eq («Affine.dBang» x7) (leaf 0))
                         («Prelude.and»
                           (Const.eq («Affine.dBang» x9) (leaf 0))
                           («Prelude.and»
                             (Const.equal
                               («Prelude.some» («Prelude.at» x8 (leaf 0)))
                               («Prelude.nth» («Affine.dKids» x5) (leaf 0)))
                             («Prelude.and»
                               (Const.equal («Prelude.at» x10 (leaf 0)) x5)
                               (Const.equal («Prelude.at» x10 (leaf 1)) x6)))))).label ≠ 0 then
                       «Affine.res»
                         x6
                         («Prelude.append»
                           («Affine.rU» x2)
                           («Affine.usageMax» («Affine.rU» x3) («Affine.rU» x4)))
                     else
                       «Prelude.none»
                   else
                     «Prelude.none»);
    x5

def «Affine.project» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := «Affine.rD» x1;
                   if («Prelude.and»
                     (Const.eq (Const.label x2) (leaf 2))
                     («Affine.noBang» x2)).label ≠ 0 then
                     «Base.mapO»
                       (fun (x3 : T) =>
                         Const.node
                           (leaf 0)
                           (x3 :: («Prelude.single» (Const.child x1 (leaf 1)))))
                       («Prelude.nth» («Affine.dKids» x2) x0)
                   else
                     «Prelude.none»);
    x2

def «Affine.abstraction» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : List T := «Affine.rU» x1;
                   if («Affine.contracts»
                     (Const.foldr
                       (α := T)
                       (β := List T)
                       (fun (x3 : T) (x4 : List T) =>
                         if (Const.eq («Affine.plVar» x3) (leaf 0)).label ≠ 0 then
                           ((«Affine.plPath» x3) :: x4)
                         else
                           x4)
                       ([] : List T)
                       x2)
                     x0).label ≠ 0 then
                     «Affine.res»
                       («Affine.dArrow» x0 («Affine.rD» x1))
                       (Const.foldr
                         (α := T)
                         (β := List T)
                         (fun (x3 : T) (x4 : List T) =>
                           if (Const.eq («Affine.plVar» x3) (leaf 0)).label ≠ 0 then
                             x4
                           else
                             ((«Affine.plMk»
                               (Const.sub («Affine.plVar» x3) (leaf 1))
                               («Affine.plPath» x3)) ::
                               x4))
                         ([] : List T)
                         x2)
                   else
                     «Prelude.none»);
    x2

def «Affine.isSpine2» :=
  fun (x0 : T) =>
    let x1 : T := «Prelude.and»
      («Prelude.and»
        (Const.eq (Const.label x0) (leaf 10))
        (Const.eq («Prelude.length» (Const.children x0)) (leaf 2)))
      (let x1 : T := «Prelude.at» (Const.children x0) (leaf 0);
       «Prelude.and»
         («Prelude.and»
           (Const.eq (Const.label x1) (leaf 10))
           (Const.eq («Prelude.length» (Const.children x1)) (leaf 2)))
         (let x2 : T := «Prelude.at» (Const.children x1) (leaf 0);
          «Prelude.and»
            (Const.eq (Const.label x2) (leaf 24))
            (Const.eq («Prelude.length» (Const.children x2)) (leaf 2))));
    x1

def «Affine.spineTy» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Prelude.at»
      (Const.children
        («Prelude.at»
          (Const.children («Prelude.at» (Const.children x0) (leaf 0)))
          (leaf 0)))
      x1;
    x2

def «Affine.one» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (if (x0).label ≠ 0 then x1 else «Prelude.none»); x2

def «Affine.subAt» :=
  fun (x0 : T → List T → List T → T → T)
    (x1 : List T)
    (x2 : List T)
    (x3 : T)
    (x4 : T) =>
    let x5 : T := «Affine.subOf» x2 x3 (x0 (leaf 0) x1 x2 x4) x4; x5

def «Affine.semVar» :=
  fun (x0 : List T) (x1 : T) (x2 : List T) (x3 : List T) =>
    let x4 : T := «Affine.one»
      («Prelude.and»
        (Const.eq («Prelude.length» x2) (leaf 1))
        («Base.isEmpty» x3))
      («Affine.occurrence»
        x0
        x1
        («Affine.plMk»
          (Const.label («Prelude.at» x2 (leaf 0)))
          (Const.node (leaf 0) ([] : List T))));
    x4

def «Affine.semProj» :=
  fun (x0 : T)
    (x1 : T → List T → List T → T → T)
    (x2 : List T)
    (x3 : List T)
    (x4 : T)
    (x5 : List T)
    (x6 : List T) =>
    let x7 : T := «Affine.one»
      (Const.eq («Prelude.length» x5) (leaf 1))
      (let x7 : T := «Affine.termPlace» («Prelude.at» x5 (leaf 0));
       if («Prelude.isSome» x7).label ≠ 0 then
         «Affine.one»
           («Base.isEmpty» x6)
           («Affine.occurrence»
             x3
             x4
             («Affine.plMk»
               («Affine.plVar» («Prelude.get» x7))
               («Affine.snocPath» («Affine.plPath» («Prelude.get» x7)) x0)))
       else
         «Affine.one»
           (Const.eq («Prelude.length» x6) (leaf 1))
           («Base.bindO»
             («Affine.subAt» x1 x2 x3 x4 («Prelude.at» x6 (leaf 0)))
             (fun (x8 : T) => «Affine.project» x0 x8)));
    x7

def «Affine.semLam» :=
  fun (x0 : T → List T → List T → T → T)
    (x1 : List T)
    (x2 : List T)
    (x3 : T)
    (x4 : List T)
    (x5 : List T) =>
    let x6 : T := «Affine.one»
      («Prelude.and»
        (Const.eq («Prelude.length» x4) (leaf 2))
        («Prelude.and»
          (Const.eq («Prelude.length» x5) (leaf 2))
          («Check.isTy» («Prelude.at» x4 (leaf 0)))))
      («Base.bindO»
        («Affine.decorate»
          («Prelude.at» x4 (leaf 0))
          («Prelude.at» x5 (leaf 0)))
        (fun (x6 : T) =>
          let x7 : List
            T := ((Const.node (leaf 0) (x6 :: («Prelude.single» x3))) :: x2);
          «Base.bindO»
            («Affine.subAt» x0 x1 x7 x3 («Prelude.at» x5 (leaf 1)))
            (fun (x8 : T) => «Affine.abstraction» x6 x8)));
    x6

def «Affine.semSpine» :=
  fun (x0 : T → List T → List T → T → T)
    (x1 : T → List T → List T → T → T)
    (x2 : List T)
    (x3 : List T)
    (x4 : List T) =>
    let x5 : T := (let x5 : T := «Prelude.length» x4;
                   let x6 : T := x0
                     (leaf 1)
                     x2
                     x3
                     (Const.node (leaf 0) («Base.take» (Const.sub x5 (leaf 1)) x4));
                   Const.node
                     (leaf 0)
                     («Prelude.append»
                       (Const.children x6)
                       («Prelude.single»
                         (x1 (leaf 0) x2 x3 («Prelude.at» x4 (Const.sub x5 (leaf 1)))))));
    x5

def «Affine.semSat» :=
  fun (x0 : T)
    (x1 : T → List T → List T → T → T)
    (x2 : T → List T → List T → T → T)
    (x3 : List T)
    (x4 : List T)
    (x5 : T)
    (x6 : List T) =>
    let x7 : T := «Affine.one»
      (Const.eq («Prelude.length» x6) (leaf 3))
      (let x7 : List
         T := Const.children
         (x1
           (leaf 1)
           x3
           x4
           (Const.node
             (leaf 0)
             ((«Prelude.at» x6 (leaf 0)) ::
               («Prelude.single» («Prelude.at» x6 (leaf 1))))));
       «Base.bindO»
         («Affine.subOf»
           x4
           x5
           («Prelude.at» x7 (leaf 0))
           («Prelude.at» x6 (leaf 0)))
         (fun (x8 : T) =>
           «Base.bindO»
             («Affine.subOf»
               x4
               x5
               («Prelude.at» x7 (leaf 1))
               («Prelude.at» x6 (leaf 1)))
             (fun (x9 : T) =>
               «Base.bindO»
                 («Affine.subAt» x2 x3 x4 x5 («Prelude.at» x6 (leaf 2)))
                 (fun (x10 : T) =>
                   «Affine.lcaseSat»
                     («Affine.spineTy» x0 (leaf 0))
                     («Affine.spineTy» x0 (leaf 1))
                     x8
                     x9
                     x10))));
    x7

def «Affine.semApp» :=
  fun (x0 : T → List T → List T → T → T)
    (x1 : T → List T → List T → T → T)
    (x2 : List T)
    (x3 : List T)
    (x4 : T)
    (x5 : List T) =>
    let x6 : T := «Affine.one»
      (Const.eq («Prelude.length» x5) (leaf 2))
      («Base.bindO»
        («Affine.subAt» x0 x2 x3 x4 («Prelude.at» x5 (leaf 0)))
        (fun (x6 : T) =>
          «Base.bindO»
            («Affine.subAt» x1 x2 x3 x4 («Prelude.at» x5 (leaf 1)))
            (fun (x7 : T) =>
              let x8 : T := «Affine.rD» x6;
              let x9 : List T := «Affine.dKids» x8;
              «Affine.one»
                («Prelude.and»
                  (Const.eq («Prelude.length» x9) (leaf 2))
                  («Prelude.and»
                    (Const.eq (Const.label x8) (leaf 3))
                    («Prelude.and»
                      (Const.eq («Affine.dBang» x8) (leaf 0))
                      (Const.equal («Prelude.at» x9 (leaf 0)) («Affine.rD» x7)))))
                («Affine.res»
                  («Prelude.at» x9 (leaf 1))
                  («Prelude.append» («Affine.rU» x6) («Affine.rU» x7))))));
    x6

def «Affine.semPair» :=
  fun (x0 : T → List T → List T → T → T)
    (x1 : T → List T → List T → T → T)
    (x2 : List T)
    (x3 : List T)
    (x4 : T)
    (x5 : List T) =>
    let x6 : T := «Affine.one»
      (Const.eq («Prelude.length» x5) (leaf 2))
      («Base.bindO»
        («Affine.subAt» x0 x2 x3 x4 («Prelude.at» x5 (leaf 0)))
        (fun (x6 : T) =>
          «Base.bindO»
            («Affine.subAt» x1 x2 x3 x4 («Prelude.at» x5 (leaf 1)))
            (fun (x7 : T) =>
              «Affine.res»
                («Affine.dMk»
                  (leaf 2)
                  (leaf 0)
                  ((«Affine.rD» x6) :: («Prelude.single» («Affine.rD» x7))))
                («Prelude.append» («Affine.rU» x6) («Affine.rU» x7)))));
    x6

def «Affine.semCond» :=
  fun (x0 : T → List T → List T → T → T)
    (x1 : T → List T → List T → T → T)
    (x2 : T → List T → List T → T → T)
    (x3 : List T)
    (x4 : List T)
    (x5 : T)
    (x6 : List T) =>
    let x7 : T := «Affine.one»
      (Const.eq («Prelude.length» x6) (leaf 3))
      («Base.bindO»
        («Affine.subAt» x0 x3 x4 x5 («Prelude.at» x6 (leaf 0)))
        (fun (x7 : T) =>
          «Base.bindO»
            («Affine.subAt» x1 x3 x4 x5 («Prelude.at» x6 (leaf 1)))
            (fun (x8 : T) =>
              «Base.bindO»
                («Affine.subAt» x2 x3 x4 x5 («Prelude.at» x6 (leaf 2)))
                (fun (x9 : T) =>
                  «Affine.one»
                    («Prelude.and»
                      (Const.equal («Affine.dTy» («Affine.rD» x7)) (leaf 0))
                      (Const.equal («Affine.rD» x8) («Affine.rD» x9)))
                    («Affine.res»
                      («Affine.rD» x8)
                      («Prelude.append»
                        («Affine.rU» x7)
                        («Affine.usageMax» («Affine.rU» x8) («Affine.rU» x9))))))));
    x7

def «Affine.semCons» :=
  fun (x0 : T → List T → List T → T → T)
    (x1 : T → List T → List T → T → T)
    (x2 : List T)
    (x3 : List T)
    (x4 : T)
    (x5 : List T) =>
    let x6 : T := «Affine.one»
      (Const.eq («Prelude.length» x5) (leaf 2))
      («Base.bindO»
        («Affine.subAt» x0 x2 x3 x4 («Prelude.at» x5 (leaf 0)))
        (fun (x6 : T) =>
          «Base.bindO»
            («Affine.subAt» x1 x2 x3 x4 («Prelude.at» x5 (leaf 1)))
            (fun (x7 : T) =>
              let x8 : T := «Affine.rD» x7;
              «Affine.one»
                («Prelude.and»
                  (Const.equal
                    («Affine.dTy» x8)
                    («Check.tyList» («Affine.dTy» («Affine.rD» x6))))
                  («Prelude.or»
                    («Affine.dData» x8)
                    («Prelude.and»
                      (Const.eq («Affine.dBang» x8) (leaf 0))
                      (Const.equal
                        (Const.node (leaf 0) («Affine.dKids» x8))
                        (Const.node (leaf 0) («Prelude.single» («Affine.rD» x6)))))))
                («Affine.res»
                  («Affine.dList» («Affine.rD» x6))
                  («Prelude.append» («Affine.rU» x6) («Affine.rU» x7))))));
    x6

def «Affine.semOne» :=
  fun (x0 : T) (x1 : List T) (x2 : List T) =>
    let x3 : T := «Affine.one»
      («Prelude.and»
        (Const.eq («Prelude.length» x1) (leaf 1))
        («Prelude.and»
          (Const.eq («Prelude.length» x2) (leaf 1))
          («Check.isTy» («Prelude.at» x1 (leaf 0)))))
      («Base.bindO»
        («Affine.decorate»
          («Prelude.at» x1 (leaf 0))
          («Prelude.at» x2 (leaf 0)))
        (fun (x3 : T) =>
          «Affine.res»
            (if (Const.eq x0 (leaf 19)).label ≠ 0 then
              «Affine.dList» x3
            else
              if (Const.eq x0 (leaf 18)).label ≠ 0 then
                «Affine.iterD» x3
              else
                «Affine.foldD» x3)
            ([] : List T)));
    x3

def «Affine.semTwo» :=
  fun (x0 : T) (x1 : List T) (x2 : List T) =>
    let x3 : T := «Affine.one»
      («Prelude.and»
        (Const.eq («Prelude.length» x1) (leaf 2))
        («Prelude.and»
          (Const.eq («Prelude.length» x2) (leaf 2))
          («Prelude.and»
            («Check.isTy» («Prelude.at» x1 (leaf 0)))
            («Check.isTy» («Prelude.at» x1 (leaf 1))))))
      («Base.bindO»
        («Affine.decorate»
          («Prelude.at» x1 (leaf 0))
          («Prelude.at» x2 (leaf 0)))
        (fun (x3 : T) =>
          «Base.bindO»
            («Affine.decorate»
              («Prelude.at» x1 (leaf 1))
              («Prelude.at» x2 (leaf 1)))
            (fun (x4 : T) =>
              if (Const.eq x0 (leaf 24)).label ≠ 0 then
                «Affine.res» («Affine.lcaseD» x3 x4) ([] : List T)
              else
                «Affine.one»
                  («Prelude.or»
                    («Affine.dData» x3)
                    (Const.lt (leaf 0) («Affine.dBang» x3)))
                  («Affine.res» («Affine.foldrD» x3 x4) ([] : List T)))));
    x3

def «Affine.semPrim» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : T := «Affine.one»
      («Prelude.and»
        (Const.eq («Prelude.length» x0) (leaf 1))
        («Base.isEmpty» x1))
      («Base.mapO»
        (fun (x2 : T) =>
          Const.node
            (leaf 0)
            ((«Affine.dZero» x2) ::
              («Prelude.single» (Const.node (leaf 0) ([] : List T)))))
        («Prelude.nth»
          «Check.primTypes»
          (Const.label («Prelude.at» x0 (leaf 0)))));
    x2

def «Affine.semRef» :=
  fun (x0 : List T) (x1 : List T) (x2 : List T) =>
    let x3 : T := «Affine.one»
      («Prelude.and»
        (Const.eq («Prelude.length» x1) (leaf 1))
        (Const.eq («Prelude.length» x2) (leaf 2)))
      (let x3 : T := «Prelude.at» x2 (leaf 0);
       let x4 : T := «Prelude.at» x2 (leaf 1);
       «Base.bindO»
         («Prelude.nth» x0 (Const.label x3))
         (fun (x5 : T) =>
           «Affine.one»
             («Prelude.and»
               (Const.eq
                 (Const.child x5 (leaf 0))
                 (Const.label («Prelude.at» x1 (leaf 0))))
               («Prelude.and»
                 («Base.isEmpty» (Const.children x3))
                 («Base.isEmpty» (Const.children x4))))
             («Affine.res»
               («Affine.dShift» (Const.child x5 (leaf 1)) (Const.label x4))
               ([] : List T))));
    x3

def «Affine.semLeaf» :=
  fun (x0 : T) (x1 : List T) (x2 : List T) (x3 : List T) =>
    let x4 : T := (if (Const.eq x0 (leaf 11)).label ≠ 0 then
      «Affine.one»
        («Prelude.and» («Base.isEmpty» x2) («Base.isEmpty» x3))
        («Affine.res» («Affine.dZero» (leaf 1)) ([] : List T))
    else
      if (Const.eq x0 (leaf 15)).label ≠ 0 then
        «Affine.one»
          («Prelude.and»
            (Const.eq («Prelude.length» x2) (leaf 1))
            («Base.isEmpty» x3))
          («Affine.res» («Affine.dZero» (leaf 0)) ([] : List T))
      else
        if (Const.eq x0 (leaf 22)).label ≠ 0 then
          «Affine.semPrim» x2 x3
        else
          if (Const.eq x0 (leaf 23)).label ≠ 0 then
            «Affine.semRef» x1 x2 x3
          else
            if («Prelude.or»
              (Const.eq x0 (leaf 21))
              (Const.eq x0 (leaf 24))).label ≠ 0 then
              «Affine.semTwo» x0 x2 x3
            else
              if («Prelude.or»
                (Const.eq x0 (leaf 19))
                («Prelude.or»
                  (Const.eq x0 (leaf 18))
                  («Prelude.or»
                    (Const.eq x0 (leaf 17))
                    (Const.eq x0 (leaf 25))))).label ≠ 0 then
                «Affine.semOne» x0 x2 x3
              else
                «Prelude.none»);
    x4

def «Affine.semStep» :=
  fun (x0 : T)
    (x1 : T → List T → List T → T → T)
    (x2 : T → List T → List T → T → T)
    (x3 : T → List T → List T → T → T)
    (x4 : T)
    (x5 : List T)
    (x6 : List T)
    (x7 : T) =>
    let x8 : T := (let x8 : T := Const.label x0;
                   let x9 : List T := Const.children x0;
                   let x10 : T := Const.label x7;
                   let x11 : List T := Const.children x7;
                   if (Const.lt x8 (leaf 9)).label ≠ 0 then
                     if (Const.eq x8 (leaf 8)).label ≠ 0 then
                       «Affine.semVar» x6 x10 x9 x11
                     else
                       «Prelude.none»
                   else
                     if (Const.eq x8 (leaf 9)).label ≠ 0 then
                       «Affine.semLam» x2 x5 x6 x10 x9 x11
                     else
                       if (Const.eq x8 (leaf 10)).label ≠ 0 then
                         «Affine.one»
                           (Const.eq («Prelude.length» x9) (leaf 2))
                           (if (Const.eq x4 (leaf 1)).label ≠ 0 then
                             «Affine.semSpine» x1 x2 x5 x6 x11
                           else
                             if («Affine.isSpine2» («Prelude.at» x9 (leaf 0))).label ≠ 0 then
                               «Affine.semSat» («Prelude.at» x9 (leaf 0)) x1 x2 x5 x6 x10 x11
                             else
                               «Affine.semApp» x1 x2 x5 x6 x10 x11)
                       else
                         if (Const.eq x8 (leaf 12)).label ≠ 0 then
                           «Affine.one»
                             (Const.eq («Prelude.length» x9) (leaf 2))
                             («Affine.semPair» x1 x2 x5 x6 x10 x11)
                         else
                           if (Const.eq x8 (leaf 13)).label ≠ 0 then
                             «Affine.semProj» (leaf 0) x1 x5 x6 x10 x9 x11
                           else
                             if (Const.eq x8 (leaf 14)).label ≠ 0 then
                               «Affine.semProj» (leaf 1) x1 x5 x6 x10 x9 x11
                             else
                               if (Const.eq x8 (leaf 16)).label ≠ 0 then
                                 «Affine.one»
                                   (Const.eq («Prelude.length» x9) (leaf 3))
                                   («Affine.semCond» x1 x2 x3 x5 x6 x10 x11)
                               else
                                 if (Const.eq x8 (leaf 20)).label ≠ 0 then
                                   «Affine.one»
                                     (Const.eq («Prelude.length» x9) (leaf 2))
                                     («Affine.semCons» x1 x2 x5 x6 x10 x11)
                                 else
                                   if («Prelude.and»
                                     (Const.eq x4 (leaf 1))
                                     («Prelude.or»
                                       (Const.eq x8 (leaf 21))
                                       (Const.eq x8 (leaf 24)))).label ≠ 0 then
                                     Const.node (leaf 0) ([] : List T)
                                   else
                                     «Affine.semLeaf» x8 x5 x9 x11);
    x8

def «Affine.sem0» :=
  fun (_ : T) (_ : List T) (_ : List T) (_ : T) => «Prelude.none»

def «Affine.semThree» :=
  fun (x0 : T) (x1 : List (T → List T → List T → T → T)) =>
    let x2 : T →
      List T →
        List T →
          T →
            T := Const.lcase
      (α := T → List T → List T → T → T)
      (β := T → List T → List T → T → T)
      x1
      («Affine.semStep» x0 «Affine.sem0» «Affine.sem0» «Affine.sem0»)
      (fun (x2 : T → List T → List T → T → T)
         (x3 : List (T → List T → List T → T → T)) =>
        Const.lcase
          (α := T → List T → List T → T → T)
          (β := T → List T → List T → T → T)
          x3
          («Affine.semStep» x0 x2 «Affine.sem0» «Affine.sem0»)
          (fun (x4 : T → List T → List T → T → T)
             (x5 : List (T → List T → List T → T → T)) =>
            Const.lcase
              (α := T → List T → List T → T → T)
              (β := T → List T → List T → T → T)
              x5
              («Affine.semStep» x0 x2 x4 «Affine.sem0»)
              (fun (x6 : T → List T → List T → T → T)
                 (_ : List (T → List T → List T → T → T)) =>
                «Affine.semStep» x0 x2 x4 x6)));
    x2

def «Affine.sem» :=
  fun (x0 : T) =>
    let x1 : T →
      List T →
        List T →
          T →
            T := Const.para
      (α := T → List T → List T → T → T)
      «Affine.semThree»
      x0;
    x1

def «Affine.instanceOf» :=
  fun (x0 : List T) (x1 : List T) (x2 : T) =>
    let x3 : T := «Base.bindO»
      («Prelude.nth» x0 (Const.label x2))
      (fun (x3 : T) =>
        let x4 : List T := Const.children x2;
        if («Prelude.and»
          (Const.eq («Prelude.length» x4) (leaf 1))
          (Const.eq
            (Const.label («Prelude.at» x4 (leaf 0)))
            (leaf 0))).label ≠ 0 then
          «Base.mapO»
            (fun (x5 : T) =>
              Const.node
                (leaf 0)
                («Prelude.append»
                  x1
                  («Prelude.single»
                    (Const.node
                      (leaf 0)
                      ((Const.label x2) :: («Prelude.single» (Const.child x5 (leaf 0))))))))
            («Affine.sem» x3 (leaf 0) x1 ([] : List T) («Prelude.at» x4 (leaf 0)))
        else
          «Prelude.none»);
    x3

def «Affine.check» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := Const.foldr
      (α := T)
      (β := List T → T)
      (fun (x2 : T) (x3 : List T → T) (x4 : List T) =>
        «Base.bindO»
          («Affine.instanceOf» x0 x4 x2)
          (fun (x5 : T) => x3 (Const.children x5)))
      (fun (x2 : List T) => «Prelude.some» (Const.node (leaf 0) x2))
      (Const.children x1)
      ([] : List T);
    x2

end GebMirror.Metalogic

end
