/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.BiasedProcess.NativeFamily
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
namespace Qatlib.Papers.QAOAScaling23.BiasedProcess.NativeFamily
open scoped Classical ENNReal
open Qatlib.Foundations.ProbabilityCore.FiniteBranch
open CausalSearch WeightedCost BudgetPrefix
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.QuantumAccess
variable {I : Type} [Fintype I] [DecidableEq I]

def tail (B N : ℕ) (hB : 0<B) : List ℕ := NativeRows.confidenceTail B (8*(N+1)) hB

theorem tail_spec (B N : ℕ) (hB : 0<B) : 1::tail B N hB=publicSchedule B N :=
  NativeRows.confidenceTail_spec B (8*(N+1)) hB

theorem family_cap (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ) (seed : I) (cost : I → ℝ)
    (h0 : 0<Born.weights cost (Born.preparedLaw U hU seed) 0) (B N : ℕ) (hN : 1≤N)
    (hB : 37500*(N:ℝ)/Real.sqrt (Born.weights cost (Born.preparedLaw U hU seed) 0)≤(B:ℝ))
    (r : ℕ) (hr : r+1<(costLevels cost).card) :
    1≤(B:ℝ)*Real.sqrt (MeasureProb (preparedAAState U seed) (strictMarked cost (threshold cost r hr))) := by
  apply public_budget_cap _ _ 2500 (N:ℝ) h0
    (Born.optimal_le_strict_mass U hU seed cost _ (by rw [threshold_rank]; omega)) (by norm_num)
    (by exact_mod_cast hN) B
  convert hB using 1; ring

theorem family_charge_bound (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ) (seed : I) (cost : I → ℝ)
    (h0 : 0<Born.weights cost (Born.preparedLaw U hU seed) 0) (B N : ℕ) (hN : 1≤N)
    (hBpos : 0<B)
    (hB : 37500*(N:ℝ)/Real.sqrt (Born.weights cost (Born.preparedLaw U hU seed) 0)≤(B:ℝ)) :
    ∀ j,0<j → rowCharge (rows U hU seed cost h0 (tail B N hBpos)) j≤
      2*2500*(N:ℝ)/Real.sqrt (prefixSum (Born.weights cost (Born.preparedLaw U hU seed)) j) := by
  intro j hj
  cases j with
  | zero => omega
  | succ r =>
    change (∑ a,((rows U hU seed cost h0 (tail B N hBpos) r).law a).toReal *
      ((rows U hU seed cost h0 (tail B N hBpos) r).charge a : ℝ))≤_
    by_cases hr : r+1<(costLevels cost).card
    · unfold rows
      rw [entry_actual U hU seed cost h0 (tail B N hBpos) r hr]
      have hb:=NativeRows.actual_charge_bound U hU seed cost (threshold cost r hr) r
        (threshold_rank cost r hr) (actual_prefix_pos U hU seed cost h0 r) (tail B N hBpos)
        B (5*B+8*(N+1)) (tail_spec B N hBpos) (family_cap U hU seed cost h0 B N hN hB r hr)
      rw [Born.strict_mass_prefix U hU seed cost (threshold cost r hr),threshold_rank] at hb
      apply hb.trans
      apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
      have hn : (1:ℝ)≤N := by exact_mod_cast hN
      nlinarith
    · unfold rows
      rw [entry_outside U hU seed cost h0 (tail B N hBpos) r hr]
      rw [Outside.fallback_charge]
      positivity

theorem family_bad_bound (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ) (seed : I) (cost : I → ℝ)
    (h0 : 0<Born.weights cost (Born.preparedLaw U hU seed) 0) (B N : ℕ) (hN : 1≤N)
    (hBpos : 0<B)
    (hB : 37500*(N:ℝ)/Real.sqrt (Born.weights cost (Born.preparedLaw U hU seed) 0)≤(B:ℝ)) :
    ∀ r,rowBadMean (rows U hU seed cost h0 (tail B N hBpos)) r≤(25/32:ℝ)^(8*(N+1)) := by
  intro r
  unfold rowBadMean
  by_cases hr : r+1<(costLevels cost).card
  · unfold rows
    rw [entry_actual U hU seed cost h0 (tail B N hBpos) r hr]
    exact NativeRows.actual_bad_bound U hU seed cost (threshold cost r hr) r
      (threshold_rank cost r hr) (actual_prefix_pos U hU seed cost h0 r) (tail B N hBpos)
      B (8*(N+1)) (tail_spec B N hBpos) (family_cap U hU seed cost h0 B N hN hB r hr)
  · unfold rows
    rw [entry_outside U hU seed cost h0 (tail B N hBpos) r hr]
    rw [Outside.fallback_bad]
    positivity

omit [DecidableEq I] in

theorem family_bad_union (cost : I → ℝ) (N : ℕ) (hcard : Fintype.card I≤2^N) :
    ((costLevels cost).card:ℝ)*(25/32:ℝ)^(8*(N+1))≤1/6 := by
  have hclasses : ((costLevels cost).card:ℝ)≤(2:ℝ)^N := by
    exact_mod_cast Born.classes_le_bit_bound cost N hcard
  exact (mul_le_mul_of_nonneg_right hclasses (by positivity)).trans (public_confidence_union N)
end Qatlib.Papers.QAOAScaling23.BiasedProcess.NativeFamily
