/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionCalls
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Emitter
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Expansion
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Increment
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.TableCopy
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.WordValidator
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionPreparation

open Turing
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec (Bits)
open Qatlib
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks

def emptyWork : Fin 6 → Bits := fun _ => []
def work (k : Fin 6) (xs : Bits) : Fin 6 → Bits := Function.update emptyWork k xs

@[simp] theorem empty_update (k : Fin 6) : Function.update emptyWork k [] = emptyWork := by
  funext j
  by_cases h : j=k <;> simp [Function.update_apply,emptyWork,h]

@[simp] theorem work_nil (k : Fin 6) : work k [] = emptyWork := by
  exact empty_update k

@[simp] theorem work_update (k : Fin 6) (xs ys : Bits) :
    Function.update (work k xs) k ys = work k ys := by simp [work]

@[simp] theorem store_update_left (W : Fin 6 → Bits) (A D B C raw xs : Bits) (k : Fin 6) :
    Function.update (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store W A D B C raw) (.inl k) xs =
      Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store (Function.update W k xs) A D B C raw := by
  funext j
  cases j with
  | inl j => simp [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store,Function.update_apply]
  | inr j => simp [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store]

theorem frame_flatMap (xs : Bits) : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.frame xs = xs.flatMap (bitPair false) ++ [false] := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.frame,bitPair,ih]

theorem frame_reverse (xs : Bits) :
    (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.frame xs).reverse = false :: xs.reverse.flatMap (bitPair true) := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.frame,List.reverse_cons,ih,List.flatMap_append,bitPair,List.append_assoc]

theorem loadC_run (A D B C : Bits) (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local) :
    stackRun Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program (C.length+1)
      ⟨some .loadC,v,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store emptyWork A D B C.reverse []⟩ =
      some ⟨some .frameA,v.clear,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store (work 5 (false::C)) A D B [] []⟩ := by
  have h := move_run (.inr 3) (.inl 5) .loadC
    (.push (.inl 5) (fun _ => false) (.load Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.clear (.goto (fun _ => .frameA))))
    rfl (by decide) C.reverse [] (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store emptyWork A D B [] []) v
  simpa [setTwo,work,List.reverse_reverse,TM2.stepAux,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.clear,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.load] using! h

theorem frameA_run (A D B C : Bits) (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local) :
    stackRun Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program (A.length+1)
      ⟨some .frameA,v,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store (work 5 (false::C)) A.reverse D B [] []⟩ =
      some ⟨some (.first .parse),v.clear,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store (work 5 (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.frame A++C)) [] D B [] []⟩ := by
  have h := pair_run (.inr 0) (.inl 5) .frameA false
    (.load Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.clear (.goto (fun _ => .first .parse))) rfl (by decide)
    A.reverse (false::C) (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store emptyWork [] D B [] []) v
  simpa [setTwo,work,List.reverse_reverse,TM2.stepAux,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.clear,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.load,
    frame_flatMap,List.append_assoc] using! h

theorem saveNumerator_run (N D B : Bits) (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local) :
    stackRun Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program (N.length+1)
      ⟨some .saveNumerator,v,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store (work 2 N.reverse) [] D B [] []⟩ =
      some ⟨some .loadB,v.clear,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store emptyWork N D B [] []⟩ := by
  have h := move_run (.inl 2) (.inr 0) .saveNumerator
    (.load Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.clear (.goto (fun _ => .loadB))) rfl (by decide)
    N.reverse [] (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store emptyWork [] D B [] []) v
  simpa [setTwo,work,List.reverse_reverse,TM2.stepAux,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.clear,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.load] using! h

theorem loadB_run (N D B : Bits) (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local) :
    stackRun Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program (B.length+1)
      ⟨some .loadB,v,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store emptyWork N D B.reverse [] []⟩ =
      some ⟨some .frameD,v.clear,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store (work 5 (false::B)) N D [] [] []⟩ := by
  have h := move_run (.inr 2) (.inl 5) .loadB
    (.push (.inl 5) (fun _ => false) (.load Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.clear (.goto (fun _ => .frameD))))
    rfl (by decide) B.reverse [] (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store emptyWork N D [] [] []) v
  simpa [setTwo,work,List.reverse_reverse,TM2.stepAux,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.clear,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.load] using! h

theorem frameD_run (N D B : Bits) (v : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local) :
    stackRun Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.program (D.length+1)
      ⟨some .frameD,v,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store (work 5 (false::B)) N D.reverse [] [] []⟩ =
      some ⟨some (.second .parse),v.clear,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store (work 5 (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.frame D++B)) N [] [] [] []⟩ := by
  have h := pair_run (.inr 1) (.inl 5) .frameD false
    (.load Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.clear (.goto (fun _ => .second .parse))) rfl (by decide)
    D.reverse (false::B) (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionReader.store emptyWork N [] [] [] []) v
  simpa [setTwo,work,List.reverse_reverse,TM2.stepAux,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.clear,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionDefs.Local.load,
    frame_flatMap,List.append_assoc] using! h

@[simp] theorem parsed_clear (sa sb : Bool) (A D B C : Bits) :
    (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionParsing.parsed sa sb A D B C).clear = Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionParsing.parsed sa sb A D B C := rfl

@[simp] theorem parsed_putMul (sa sb : Bool) (A D B C : Bits) :
    (Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionParsing.parsed sa sb A D B C).putMul MulVar.init = Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionParsing.parsed sa sb A D B C := rfl

end Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDivisionPreparation
