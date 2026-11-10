/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false


open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Cleanup
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Emitter
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Expansion
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.FrameCopy
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Increment
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.PairZip
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.ReadonlyCompare
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.TableCopy
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExecution

open Turing
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec (Bits binaryValue)
open Qatlib
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks

theorem stacks_update54 (u b a m y t w₅ w₄ : Bits) :
    Function.update (Function.update (mulStacks u b a m y t) 5 w₅) 4 w₄ =
      mulStacks u b a m w₄ w₅ := by
  funext i
  fin_cases i <;> simp [mulStacks]

theorem stacks_update02 (u b a m y t w₀ w₂ : Bits) :
    Function.update (Function.update (mulStacks u b a m y t) 0 w₀) 2 w₂ =
      mulStacks w₀ b w₂ m y t := by
  funext i
  fin_cases i <;> simp [mulStacks]

theorem parse_run (x y master : Bits) (v : MulVar) :
    stackRun Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.program (2*x.length+1)
      ⟨some .parse,v,mulStacks [] [] [] master [] (frame x ++ y)⟩ =
      some ⟨some .multiplier,MulVar.init,mulStacks [] [] [] (x.reverse++master) [] y⟩ := by
  induction x generalizing master v with
  | nil =>
      simp [frame,stackRun,TM2.step,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.program,TM2.stepAux,MulVar.readMbit,mulStacks_update_five]
  | cons b xs ih =>
      have hstep : stackRun Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.program 2
          ⟨some .parse,v,mulStacks [] [] [] master [] (frame (b::xs)++y)⟩ =
          some ⟨some .parse,MulVar.init,mulStacks [] [] [] (b::master) [] (frame xs++y)⟩ := by
        simp [frame,stackRun,TM2.step,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.program,TM2.stepAux,MulVar.readMbit,
          mulStacks_update_five,mulStacks_update_three]
      rw [show 2*(b::xs).length+1=2+(2*xs.length+1) by simp; omega,
        run_add,hstep,Option.bind_some,ih]
      simp [List.reverse_cons,List.append_assoc]

theorem multiplier_run (input master out : Bits) (v : MulVar) :
    stackRun Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.program (input.length+1)
      ⟨some .multiplier,v,mulStacks [] [] [] master out input⟩ =
      some ⟨some (.multiply .outer),MulVar.init,
        mulStacks [] [] [] master (input.reverse++out) []⟩ := by
  induction input generalizing out v with
  | nil => simp [stackRun,TM2.step,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.program,TM2.stepAux,MulVar.readMbit,mulStacks_update_five]
  | cons b bs ih =>
      have hs : TM2.step Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.program ⟨some .multiplier,v,mulStacks [] [] [] master out (b::bs)⟩ =
          some ⟨some .multiplier,MulVar.init,mulStacks [] [] [] master (b::out) bs⟩ := by
        simp [TM2.step,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.program,TM2.stepAux,MulVar.readMbit,stacks_update54]
      rw [List.length_cons,stackRun,hs,Option.bind_some,ih]
      simp [List.reverse_cons,List.append_assoc]

theorem mul_halt (x y : Bits) :
    stackRun mulProgram (mulTotalTicks x y y.length+2) (mulStart x y) =
      some ⟨none,MulVar.init,mulStacks (mulAcc x y y.length) [] [] x.reverse [] []⟩ := by
  have hd : y.reverse.drop (y.length+1) = [] := List.drop_eq_nil_of_le (by simp)
  rw [show mulTotalTicks x y y.length+2=mulTotalTicks x y y.length+(1+1) by omega,
    run_add,mulProgram_sweep,Option.bind_some]
  simp [stackRun,mulCfg,TM2.step,mulProgram,TM2.stepAux,MulVar.readBit,
    mulStacks_update_four,hd]

theorem multiply_call (x y : Bits) :
    stackRun Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.program (mulTotalTicks x y y.length+2)
      ⟨some (.multiply .outer),MulVar.init,mulStacks [] [] [] x.reverse y.reverse []⟩ =
      some ⟨some .clear,MulVar.init,mulStacks (mulAcc x y y.length) [] [] x.reverse [] []⟩ := by
  have h := StackCall.execution (stackCode:=id) (labelCode:=Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.Label.multiply) (returnTo:=Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.Label.clear)
    (get:=id) (put:=fun _ v : MulVar => v) (E:=id)
    (hE:=fun _ _ => rfl) (hupdate:=fun _ _ _ => rfl)
    (hget:=fun _ _ => rfl) (hput:=fun _ _ _ => rfl)
    mulProgram Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.program (fun _ => rfl) MulVar.init _ _ _ (mul_halt x y)
  simpa only [StackCall.cfg,mulStart,Option.map_some,Option.getD_some,Option.map_none,
    Option.getD_none,id_eq] using! h.1

theorem clear_run (master acc : Bits) (v : MulVar) :
    stackRun Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.program (master.length+1)
      ⟨some .clear,v,mulStacks acc [] [] master [] []⟩ =
      some ⟨some .output,MulVar.init,mulStacks acc [] [] [] [] []⟩ := by
  induction master generalizing v with
  | nil => simp [stackRun,TM2.step,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.program,TM2.stepAux,MulVar.readMbit,mulStacks_update_three]
  | cons b bs ih =>
      have hs : TM2.step Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.program ⟨some .clear,v,mulStacks acc [] [] (b::bs) [] []⟩ =
          some ⟨some .clear,MulVar.readMbit v (some b),mulStacks acc [] [] bs [] []⟩ := by
        simp [TM2.step,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.program,TM2.stepAux,MulVar.readMbit,mulStacks_update_three]
      rw [List.length_cons,stackRun,hs,Option.bind_some,ih]

theorem output_run (input out : Bits) (v : MulVar) :
    stackRun Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.program (input.length+1)
      ⟨some .output,v,mulStacks input [] out [] [] []⟩ =
      some ⟨none,MulVar.init,mulStacks [] [] (input.reverse++out) [] [] []⟩ := by
  induction input generalizing out v with
  | nil => simp [stackRun,TM2.step,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.program,TM2.stepAux,MulVar.readMbit,mulStacks_update_zero]
  | cons b bs ih =>
      have hs : TM2.step Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.program ⟨some .output,v,mulStacks (b::bs) [] out [] [] []⟩ =
          some ⟨some .output,MulVar.readMbit v (some b),mulStacks bs [] (b::out) [] [] []⟩ := by
        simp [TM2.step,Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.program,TM2.stepAux,MulVar.readMbit,stacks_update02]
      rw [List.length_cons,stackRun,hs,Option.bind_some,ih]
      simp [List.reverse_cons,List.append_assoc]

theorem raw_start (x y : Bits) :
    (TM2.init (5 : Fin 6) (mulInput x y).reverse : TM2.Cfg (fun _ : Fin 6 => Bool) Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.Label MulVar) =
      ⟨some .parse,MulVar.init,mulStacks [] [] [] [] [] (frame x++y)⟩ := by
  simp only [TM2.init,mulInput,List.reverse_reverse]
  congr 1
  funext i
  fin_cases i <;> simp [mulStacks]

theorem raw_execution (x y : Bits) :
    stackRun Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.program (sourceSteps x y) (TM2.init (5 : Fin 6) (mulInput x y).reverse) =
      some ⟨none,MulVar.init,Function.update (fun _ => []) (2 : Fin 6)
        (mulAcc x y y.length).reverse⟩ := by
  rw [raw_start]
  have hp := parse_run x y [] MulVar.init
  simp only [List.append_nil] at hp
  have hy := multiplier_run y x.reverse [] MulVar.init
  simp only [List.append_nil] at hy
  have hc := clear_run x.reverse (mulAcc x y y.length) MulVar.init
  simp only [List.length_reverse] at hc
  have ho := output_run (mulAcc x y y.length) [] MulVar.init
  simp only [List.append_nil] at ho
  have ht : sourceSteps x y = (2*x.length+1)+((y.length+1)+
      ((mulTotalTicks x y y.length+2)+((x.length+1)+((mulAcc x y y.length).length+1)))) := by
    simp only [sourceSteps]; omega
  rw [ht,run_add,hp,Option.bind_some,run_add,hy,Option.bind_some,
    run_add,multiply_call,Option.bind_some,run_add,hc,Option.bind_some,ho]
  congr 2
  funext i
  fin_cases i <;> simp [mulStacks]

end Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExecution
