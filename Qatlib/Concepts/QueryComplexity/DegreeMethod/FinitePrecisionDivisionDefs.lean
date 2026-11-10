/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExecution
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs

open Turing
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec (Bits)
open Qatlib
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM

abbrev Slot := Fin 6 ⊕ Fin 5

structure Local where
  mul : MulVar
  read : Option Bool
  signA : Bool
  signB : Bool
  nonzeroA : Bool
  nonzeroB : Bool
  nonzeroD : Bool
  deriving DecidableEq

def localEquiv : Local ≃ (MulVar × Option Bool × Bool × Bool × Bool × Bool × Bool) where
  toFun v := (v.mul,v.read,v.signA,v.signB,v.nonzeroA,v.nonzeroB,v.nonzeroD)
  invFun v := ⟨v.1,v.2.1,v.2.2.1,v.2.2.2.1,v.2.2.2.2.1,v.2.2.2.2.2.1,v.2.2.2.2.2.2⟩
  left_inv v := by cases v; rfl
  right_inv v := by rcases v with ⟨m,r,a,b,c,d,e⟩; rfl

instance : Fintype Local := Fintype.ofEquiv _ localEquiv.symm

def Local.init : Local := ⟨MulVar.init,none,false,false,false,false,false⟩
instance : Inhabited Local := ⟨Local.init⟩

def Local.clear (v : Local) : Local := { v with read := none }
def Local.load (v : Local) (o : Option Bool) : Local := { v with read := o }
def Local.remember (p : Fin 4) (v : Local) (o : Option Bool) : Local :=
  { v with
    read := o
    nonzeroA := v.nonzeroA || (p == 1 && o.getD false)
    nonzeroB := v.nonzeroB || (p == 2 && o.getD false)
    nonzeroD := v.nonzeroD || (p == 3 && o.getD false) }

def Local.putMul (v : Local) (w : MulVar) : Local := { v with mul := w }
def Local.valid (v : Local) : Bool := v.nonzeroA && v.nonzeroB && v.nonzeroD

inductive Label where
  | signA | signB
  | parse : Fin 3 → Label
  | payload : Fin 3 → Label
  | last
  | test
  | loadC | frameA
  | first : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.Label → Label
  | saveNumerator
  | loadB | frameD
  | second : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.Label → Label
  | startOutput | numerator | reverseDenominator | denominator
  | invalid : Fin 4 → Label
  deriving DecidableEq, Fintype

instance : Inhabited Label := ⟨.signA⟩

def nextField (p : Fin 3) : Label :=
  if h : p.val+1 < 3 then .parse ⟨p.val+1,h⟩ else .last

def input (sa sb : Bool) (A D B C : Bits) : Bits :=
  (sa :: sb :: (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.frame A ++ Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.frame D ++ Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.frame B ++ C)).reverse

def output (sa sb : Bool) (N E : Bits) : Bits :=
    true :: (sa ^^ sb) ::
    (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.frame N ++ E)

def program : Label → TM2.Stmt (fun _ : Slot => Bool) Label Local
  | .signA => .pop (.inr 4) Local.load
      (.load (fun v => { v with signA := v.read.getD false, read := none })
        (.goto (fun _ => .signB)))
  | .signB => .pop (.inr 4) Local.load
      (.load (fun v => { v with signB := v.read.getD false, read := none })
        (.goto (fun _ => .parse 0)))
  | .parse p => .pop (.inr 4) Local.load
      (.branch (fun v => v.read.getD false)
        (.goto (fun _ => .payload p))
        (.load Local.clear (.goto (fun _ => nextField p))))
  | .payload p => .pop (.inr 4) (Local.remember p.castSucc)
      (.push (.inr p.castSucc.castSucc) (fun v => v.read.getD false)
        (.load Local.clear (.goto (fun _ => .parse p))))
  | .last => .pop (.inr 4) (Local.remember 3)
      (.branch (fun v => v.read.isSome)
        (.push (.inr 3) (fun v => v.read.getD false)
          (.load Local.clear (.goto (fun _ => .last))))
        (.load Local.clear (.goto (fun _ => .test))))
  | .test => .branch Local.valid (.goto (fun _ => .loadC)) (.goto (fun _ => .invalid 0))
  | .loadC => .pop (.inr 3) Local.load
      (.branch (fun v => v.read.isSome)
        (.push (.inl 5) (fun v => v.read.getD false)
          (.load Local.clear (.goto (fun _ => .loadC))))
        (.push (.inl 5) (fun _ => false) (.load Local.clear (.goto (fun _ => .frameA)))))
  | .frameA => .pop (.inr 0) Local.load
      (.branch (fun v => v.read.isSome)
        (.push (.inl 5) (fun v => v.read.getD false)
          (.push (.inl 5) (fun _ => true) (.load Local.clear (.goto (fun _ => .frameA)))))
        (.load Local.clear (.goto (fun _ => .first .parse))))
  | .first l => StackCall.stmt Sum.inl Label.first .saveNumerator Local.mul Local.putMul
      (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.program l)
  | .saveNumerator => .pop (.inl 2) Local.load
      (.branch (fun v => v.read.isSome)
        (.push (.inr 0) (fun v => v.read.getD false)
          (.load Local.clear (.goto (fun _ => .saveNumerator))))
        (.load Local.clear (.goto (fun _ => .loadB))))
  | .loadB => .pop (.inr 2) Local.load
      (.branch (fun v => v.read.isSome)
        (.push (.inl 5) (fun v => v.read.getD false)
          (.load Local.clear (.goto (fun _ => .loadB))))
        (.push (.inl 5) (fun _ => false) (.load Local.clear (.goto (fun _ => .frameD)))))
  | .frameD => .pop (.inr 1) Local.load
      (.branch (fun v => v.read.isSome)
        (.push (.inl 5) (fun v => v.read.getD false)
          (.push (.inl 5) (fun _ => true) (.load Local.clear (.goto (fun _ => .frameD)))))
        (.load Local.clear (.goto (fun _ => .second .parse))))
  | .second l => StackCall.stmt Sum.inl Label.second .startOutput Local.mul Local.putMul
      (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.program l)
  | .startOutput => .push (.inr 1) (fun _ => true)
      (.push (.inr 1) (fun v => v.signA ^^ v.signB) (.goto (fun _ => .numerator)))
  | .numerator => .pop (.inr 0) Local.load
      (.branch (fun v => v.read.isSome)
        (.push (.inr 1) (fun _ => true)
          (.push (.inr 1) (fun v => v.read.getD false)
            (.load Local.clear (.goto (fun _ => .numerator)))))
        (.push (.inr 1) (fun _ => false)
          (.load Local.clear (.goto (fun _ => .reverseDenominator)))))
  | .reverseDenominator => .pop (.inl 2) Local.load
      (.branch (fun v => v.read.isSome)
        (.push (.inl 0) (fun v => v.read.getD false)
          (.load Local.clear (.goto (fun _ => .reverseDenominator))))
        (.load Local.clear (.goto (fun _ => .denominator))))
  | .denominator => .pop (.inl 0) Local.load
      (.branch (fun v => v.read.isSome)
        (.push (.inr 1) (fun v => v.read.getD false)
          (.load Local.clear (.goto (fun _ => .denominator))))
        (.load (fun _ => Local.init) .halt))
  | .invalid p => .pop (.inr p.castSucc) Local.load
      (.branch (fun v => v.read.isSome) (.load Local.clear (.goto (fun _ => .invalid p)))
        (if h : p.val+1 < 4 then .load Local.clear (.goto (fun _ => .invalid ⟨p.val+1,h⟩))
         else .push (.inr 1) (fun _ => false) (.load (fun _ => Local.init) .halt)))

end Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs
