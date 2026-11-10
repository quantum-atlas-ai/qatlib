/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionCore
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Emitter
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatTag
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.PairZip
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.ReadonlyRepeat
open Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
open Turing Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks
set_option autoImplicit false

theorem read_frame_actual (bits tail out : Bits) (v : FramedTake.Local) : ∃ ticks last,
    stackRun FramedTake.program ticks
      ⟨some (.read (.read .unary)),v,FramedTake.store (framed bits++tail) [] [] out⟩ =
      some ⟨none,last,FramedTake.store tail [] [] (bits.reverse++out)⟩ ∧
    stackRunClock FramedTake.program ticks
      ⟨some (.read (.read .unary)),v,FramedTake.store (framed bits++tail) [] [] out⟩ ≤
      5000*(bits.length+1)*(1+(framed bits++tail).length+out.length)^2 ∧
    stackRunMaxClock FramedTake.program ticks
      ⟨some (.read (.read .unary)),v,FramedTake.store (framed bits++tail) [] [] out⟩ ≤
      5000*(bits.length+1)*(1+(framed bits++tail).length+out.length)^2 := by
  obtain ⟨ticks,last,hr,hc⟩ := FramedTake.complete bits tail out v
  exact ⟨ticks,last,hr,hc,(maxClock_le_clock _ _ _).trans hc⟩

theorem write_frame_actual (bits out : Bits) (v : Symbol) : ∃ ticks,
    stackRun FrameCopy.program ticks
      ⟨some (.copy false .emit),v,FrameCopy.store bits.reverse [] [] [] [] out⟩ =
      some ⟨none,none,FrameCopy.store bits.reverse [] [] [] [] (framed bits++out)⟩ ∧
    stackRunClock FrameCopy.program ticks
      ⟨some (.copy false .emit),v,FrameCopy.store bits.reverse [] [] [] [] out⟩ ≤
      10000*(1+bits.length+out.length)^3 ∧
    stackRunMaxClock FrameCopy.program ticks
      ⟨some (.copy false .emit),v,FrameCopy.store bits.reverse [] [] [] [] out⟩ ≤
      10000*(1+bits.length+out.length)^3 := by
  obtain ⟨ticks,hr,hc⟩ := FrameCopy.complete bits out v
  exact ⟨ticks,hr,hc,(maxClock_le_clock _ _ _).trans hc⟩

example : framed [false] ≠ Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs.frame [false] := by decide

end Qatlib.Concepts.AdversaryBounds.AdvDuality

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality.Product
open Turing Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks
open Qatlib
set_option autoImplicit false

theorem core_nodes : programNodes mulProgram ≤ 5 := by
  unfold programNodes
  apply Finset.sup_le
  intro l _
  cases l <;> simp [mulProgram,stackNodes]

theorem core_sweep : sweepFactor mulProgram ≤ 61 := by
  have h := core_nodes
  unfold sweepFactor
  nlinarith

theorem core_initial_height (x y : Bits) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight (mulStart x y).stk ≤ 1+x.length+y.length := by
  unfold Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight
  apply Finset.sup_le
  intro k _
  fin_cases k
  all_goals simp [mulStart,mulStacks]
  all_goals omega

theorem core_ticks (x y : Bits) :
    mulTotalTicks x y y.length+2 ≤ 10*(1+x.length+y.length)^2 := by
  let L := 1+x.length+y.length
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hL2 : L ≤ L^2 := Nat.le_pow (by decide)
  have hlen : y.length ≤ L := by dsimp [L]; omega
  have hf : 4*x.length+4*y.length+8 ≤ 8*L := by dsimp [L]; omega
  have h := (Qatlib.Concepts.QueryComplexity.DegreeMethod.mulTotalTicks_le x y y.length).trans
    (Nat.mul_le_mul hlen hf)
  dsimp only [L] at *
  nlinarith

theorem mul_core_complete (x y : Bits) :
    let L := 1+x.length+y.length
    stackRun mulProgram (mulTotalTicks x y y.length+2)
      ⟨some .outer,MulVar.init,mulStacks [] [] [] x.reverse y.reverse []⟩ =
      some ⟨none,MulVar.init,mulStacks (mulAcc x y y.length) [] [] x.reverse [] []⟩ ∧
    stackRunClock mulProgram (mulTotalTicks x y y.length+2) (mulStart x y) ≤ 31720*L^4 ∧
    stackRunMaxClock mulProgram (mulTotalTicks x y y.length+2) (mulStart x y) ≤ 3172*L^2 ∧
    binaryValue (mulAcc x y y.length) = binaryValue x * binaryValue y := by
  let L := 1+x.length+y.length
  let n := mulTotalTicks x y y.length+2
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hL2 : L ≤ L^2 := Nat.le_pow (by decide)
  have h1 : 1 ≤ L^2 := Nat.one_le_pow 2 L hL
  have hn : n ≤ 10*L^2 := core_ticks x y
  have hH :
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight
      (mulStart x y).stk ≤ L := core_initial_height x y
  have hwork : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight (mulStart x y).stk+n*programNodes mulProgram+1 ≤ 52*L^2 := by
    have hprod := Nat.mul_le_mul hn core_nodes
    nlinarith
  have hc : stackRunClock mulProgram n (mulStart x y) ≤ 31720*L^4 := by
    calc
      _ ≤ n*sweepFactor mulProgram*(Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight (mulStart x y).stk+n*programNodes mulProgram+1) :=
        Qatlib.Concepts.QueryComplexity.DegreeMethod.runClock_le _ _ _
      _ ≤ (10*L^2)*61*(52*L^2) := Nat.mul_le_mul (Nat.mul_le_mul hn core_sweep) hwork
      _ = _ := by ring
  have hs : stackRunMaxClock mulProgram n (mulStart x y) ≤ 3172*L^2 := by
    calc
      _ ≤ sweepFactor mulProgram*(Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks.stackHeight (mulStart x y).stk+n*programNodes mulProgram+1) :=
        Qatlib.Concepts.QueryComplexity.DegreeMethod.runMaxClock_le _ _ _
      _ ≤ 61*(52*L^2) := Nat.mul_le_mul core_sweep hwork
      _ = _ := by ring
  exact ⟨Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExecution.mul_halt x y,hc,hs,mulAcc_value_full x y⟩

end Qatlib.Concepts.AdversaryBounds.AdvDuality.Product

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality.Sum
open Turing
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks
open Qatlib
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionNative
open Qatlib
set_option autoImplicit false

def finalAddVar (x y : Bits) : AddVar :=
  ⟨(addTurns (max x.length y.length) ⟨false,x,y,[]⟩).carry,none,none⟩

theorem add_exact_end (x y : Bits) :
    stackRun addProgram (max x.length y.length+1) (addStart x y) =
      some ⟨none,finalAddVar x y,addStacks [] [] (bitAdd x y).reverse⟩ ∧
    stackRunClock addProgram (max x.length y.length+1) (addStart x y) ≤ addClockBound x y ∧
    stackRunMaxClock addProgram (max x.length y.length+1) (addStart x y) ≤ addClockBound x y := by
  have hs : addCfgAt 0 x y = addStart x y := by
    simp [addCfgAt,addCfgLoop,addStart,addTurns,AddVar.init]
  have he : addCfgAt (max x.length y.length+1) x y = addCfgFinal x y :=
    addCfgAt_eq_final x y (by omega)
  have hout : (bitAdd x y).reverse =
      if (addTurns (max x.length y.length) ⟨false,x,y,[]⟩).carry then
        true::(addTurns (max x.length y.length) ⟨false,x,y,[]⟩).os
      else (addTurns (max x.length y.length) ⟨false,x,y,[]⟩).os := by
    cases h : (addTurns (max x.length y.length) ⟨false,x,y,[]⟩).carry <;>
      simp [bitAdd,carryAdd,carryAddAux,h]
  have h := addProgram_advance x y 0 (max x.length y.length+1) (by omega)
  simp only [hs,Nat.zero_add,he] at h
  have hr : stackRun addProgram (max x.length y.length+1) (addStart x y) =
      some ⟨none,finalAddVar x y,addStacks [] [] (bitAdd x y).reverse⟩ := by
    simpa only [addCfgFinal,finalAddVar,hout] using! h.1
  have hc : stackRunClock addProgram (max x.length y.length+1) (addStart x y) ≤ addClockBound x y := by
    simpa only [addClockBound,carryAddPositions] using! h.2
  exact ⟨hr,hc,(maxClock_le_clock _ _ _).trans hc⟩

end Qatlib.Concepts.AdversaryBounds.AdvDuality.Sum
