/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionTransfers
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false


open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.BinaryCompare
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Expansion
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Increment
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatTag
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NativeEcho
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.TableCopy
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionParsing

open Turing
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec (Bits binaryValue)
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks

def afterBit (p : Fin 4) (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local) (b : Bool) : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local :=
  (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.remember p v (some b)).clear

def afterWord (p : Fin 4) (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local) (xs : Bits) : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local :=
  { v with
    read := none
    nonzeroA := v.nonzeroA || (p == 1 && xs.any id)
    nonzeroB := v.nonzeroB || (p == 2 && xs.any id)
    nonzeroD := v.nonzeroD || (p == 3 && xs.any id) }

theorem afterWord_nil (p : Fin 4) (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local) : afterWord p v [] = v.clear := by
  simp [afterWord,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.clear]

theorem afterWord_cons (p : Fin 4) (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local) (b : Bool) (xs : Bits) :
    afterWord p (afterBit p v b) xs = afterWord p v (b::xs) := by
  fin_cases p <;> cases b <;> simp [afterWord,afterBit,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.remember,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.clear]

theorem parse_run (p : Fin 3) (xs tail master : Bits) (S : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Slot → Bits) (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local) :
    stackRun Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program (2*xs.length+1)
      ⟨some (.parse p),v,setTwo S (.inr 4) (.inr p.castSucc.castSucc) (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.frame xs++tail) master⟩ =
      some ⟨some (nextField p),afterWord p.castSucc v xs,
        setTwo S (.inr 4) (.inr p.castSucc.castSucc) tail (xs.reverse++master)⟩ := by
  have hn : (Sum.inr (4 : Fin 5) : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Slot) ≠ .inr p.castSucc.castSucc := by
    fin_cases p <;> decide
  induction xs generalizing master v with
  | nil => simp [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.frame,stackRun,TM2.step,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program,TM2.stepAux,hn,afterWord_nil]
  | cons b bs ih =>
      have hs : stackRun Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program 2
          ⟨some (.parse p),v,setTwo S (.inr 4) (.inr p.castSucc.castSucc) (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.frame (b::bs)++tail) master⟩ =
          some ⟨some (.parse p),afterBit p.castSucc v b,
            setTwo S (.inr 4) (.inr p.castSucc.castSucc) (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.frame bs++tail) (b::master)⟩ := by
        simp [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.frame,stackRun,TM2.step,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program,TM2.stepAux,hn,Ne.symm hn,
          afterBit,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.remember,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.load,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.clear]
      rw [show 2*(b::bs).length+1=2+(2*bs.length+1) by simp; omega,
        run_add,hs,Option.bind_some,ih,afterWord_cons]
      simp [List.reverse_cons,List.append_assoc]

theorem last_run (xs master : Bits) (S : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Slot → Bits) (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local) :
    stackRun Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program (xs.length+1)
      ⟨some .last,v,setTwo S (.inr 4) (.inr 3) xs master⟩ =
      some ⟨some .test,afterWord 3 v xs,setTwo S (.inr 4) (.inr 3) [] (xs.reverse++master)⟩ := by
  induction xs generalizing master v with
  | nil => simp [stackRun,TM2.step,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program,TM2.stepAux,afterWord_nil,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.remember,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.clear]
  | cons b bs ih =>
      have hs : TM2.step Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program ⟨some .last,v,setTwo S (.inr 4) (.inr 3) (b::bs) master⟩ =
          some ⟨some .last,afterBit 3 v b,setTwo S (.inr 4) (.inr 3) bs (b::master)⟩ := by
        simp [TM2.step,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program,TM2.stepAux,afterBit,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.remember,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.clear]
      rw [List.length_cons,stackRun,hs,Option.bind_some,ih,afterWord_cons]
      simp [List.reverse_cons,List.append_assoc]

theorem any_iff_positive (xs : Bits) : xs.any id = true ↔ 0 < binaryValue xs := by
  induction xs with
  | nil => simp [binaryValue]
  | cons b bs ih =>
      cases b <;> simp [Qatlib.Concepts.QueryComplexity.DegreeMethod.binaryValue_cons',
        Qatlib.Concepts.QueryComplexity.DegreeMethod.bitNat,ih]

def parsed (sa sb : Bool) (A D B C : Bits) : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local :=
  afterWord 3 (afterWord 2 (afterWord 1 (afterWord 0
    { Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.init with signA := sa, signB := sb } A) D) B) C

theorem parsed_valid (sa sb : Bool) (A D B C : Bits) :
    (parsed sa sb A D B C).valid = (D.any id && B.any id && C.any id) := by
  simp [parsed,afterWord,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.init,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.valid]

theorem parsed_nonzero (sa sb : Bool) (A D B C : Bits)
    (hD : 0 < binaryValue D) (hB : 0 < binaryValue B) (hC : 0 < binaryValue C) :
    (parsed sa sb A D B C).valid = true := by
  rw [parsed_valid,(any_iff_positive D).mpr hD,(any_iff_positive B).mpr hB,
    (any_iff_positive C).mpr hC]
  rfl

end Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionParsing
