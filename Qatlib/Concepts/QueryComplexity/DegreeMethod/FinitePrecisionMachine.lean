/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionBounds
import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExecution
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Cleanup
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Emitter
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.PairZip
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.TableCopy
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExecution
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionMachine

open Turing
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec (Bits Runs binaryValue)
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks
open Qatlib

def inputSize (x y : Bits) : ℕ := 1+x.length+y.length

theorem size_pos (x y : Bits) : 1 ≤ inputSize x y := by simp [inputSize]; omega

theorem sourceSteps_bound (x y : Bits) : sourceSteps x y ≤ 32*(inputSize x y)^2 := by
  let L := inputSize x y
  have hx : x.length ≤ L := by dsimp [L,inputSize]; omega
  have hy : y.length ≤ L := by dsimp [L,inputSize]; omega
  have hinner : 4*x.length+4*y.length+8 ≤ 8*L := by dsimp [L,inputSize]; omega
  have hT : mulTotalTicks x y y.length ≤ 8*L^2 := by
    calc
      _ ≤ y.length*(4*x.length+4*y.length+8) := mulTotalTicks_le x y y.length
      _ ≤ L*(8*L) := Nat.mul_le_mul hy hinner
      _ = _ := by ring
  have hA := mulAcc_length x y y.length
  have hL := size_pos x y
  have hL2 : L ≤ L^2 := by nlinarith
  dsimp [sourceSteps,L,inputSize] at *
  nlinarith

theorem program_nodes_le : programNodes Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.program ≤ 5 := by
  unfold programNodes
  apply Finset.sup_le
  intro l _
  cases l with
  | multiply l => cases l <;> simp [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.program,StackCall.stmt,mulProgram,stackNodes]
  | parse | payload | multiplier | clear | output => simp [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.program,stackNodes]

theorem sweep_factor_le : sweepFactor Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.program ≤ 61 := by
  have h := program_nodes_le
  unfold sweepFactor
  nlinarith

theorem initial_height (x y : Bits) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight (TM2.init (5 : Fin 6) (mulInput x y).reverse :
      TM2.Cfg (fun _ : Fin 6 => Bool) Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.Label MulVar).stk ≤ 2*inputSize x y := by
  unfold Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight
  apply Finset.sup_le
  intro i _
  by_cases hi : i = 5
  · subst i
    simp only [TM2.init,Function.update_self,List.length_reverse,mulInput_length]
    dsimp [inputSize]
    omega
  · simp only [TM2.init,Function.update_of_ne hi,List.length_nil]
    omega

theorem real_clocks (x y : Bits) :
    stackRunClock Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.program (sourceSteps x y) (TM2.init (5 : Fin 6) (mulInput x y).reverse) ≤
        318176*(inputSize x y)^4 ∧
    stackRunMaxClock Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.program (sourceSteps x y) (TM2.init (5 : Fin 6) (mulInput x y).reverse) ≤
        9943*(inputSize x y)^2 := by
  let L := inputSize x y
  have hL : 1 ≤ L := size_pos x y
  have hL2 : L ≤ L^2 := by nlinarith
  have hn := sourceSteps_bound x y
  have hH := initial_height x y
  have hA := program_nodes_le
  have hS := sweep_factor_le
  have hheight : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight (TM2.init (5 : Fin 6) (mulInput x y).reverse :
      TM2.Cfg (fun _ : Fin 6 => Bool) Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.Label MulVar).stk +
      sourceSteps x y*programNodes Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.program+1 ≤ 163*L^2 := by
    have hm := Nat.mul_le_mul hn hA
    dsimp only [L] at *
    nlinarith
  constructor
  · refine (runClock_le Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.program _ _).trans ?_
    have hmul := Nat.mul_le_mul (Nat.mul_le_mul hn hS) hheight
    convert! hmul using 1; ring
  · refine (runMaxClock_le Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.program _ _).trans ?_
    have hmul := Nat.mul_le_mul hS hheight
    convert! hmul using 1; ring

theorem uniform_mul_machine :
    ∃ (q : ℕ) (M : TM0.Machine Symbol (Fin (q+1))) (C : ℕ), 0 < C ∧
      ∀ x y : Bits, Runs M (mulInput x y) (mulAcc x y y.length)
        (C*(inputSize x y)^4) (C*(inputSize x y)^2) := by
  obtain ⟨q,M,D,hD,hM⟩ :=
      raw_compiler_separate Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.program (5 : Fin 6) 2
  refine ⟨q,M,320000*D,by positivity,?_⟩
  intro x y
  have hr :=
      hM (mulInput x y) (mulAcc x y y.length) (sourceSteps x y) MulVar.init (raw_execution x y)
  have hL := size_pos x y
  have hio : 1+(mulInput x y).length ≤ 2*inputSize x y := by
    rw [mulInput_length]; dsimp [inputSize]; omega
  have hout : 1+(mulAcc x y y.length).length ≤ 2*inputSize x y := by
    have h := mulAcc_length x y y.length
    dsimp [inputSize]
    omega
  have hi2 := Nat.pow_le_pow_left hio 2
  have ho2 := Nat.pow_le_pow_left hout 2
  have h24 : (inputSize x y)^2 ≤ (inputSize x y)^4 := by
    nlinarith [sq_nonneg ((inputSize x y : ℤ)^2-1)]
  obtain ⟨ht,hs⟩ := real_clocks x y
  apply runs_mono hr
  · have hsum : (1+(mulInput x y).length)^2+
        stackRunClock Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.program (sourceSteps x y) (TM2.init (5 : Fin 6) (mulInput x y).reverse)+
        (1+(mulAcc x y y.length).length)^2 ≤ 320000*(inputSize x y)^4 := by nlinarith
    exact (Nat.mul_le_mul_left D hsum).trans_eq (by ring)
  · have hsum : (1+(mulInput x y).length)^2+
        stackRunMaxClock Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.program (sourceSteps x y) (TM2.init (5 : Fin 6) (mulInput x y).reverse)+
        (1+(mulAcc x y y.length).length)^2 ≤ 320000*(inputSize x y)^2 := by nlinarith
    exact (Nat.mul_le_mul_left D hsum).trans_eq (by ring)

end Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionMachine
