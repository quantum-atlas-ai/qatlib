/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PopulationGap.AmplitudeReadoutDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.NativeRiskDefs
import Qatlib.Concepts.NativeNumerics.EmpiricalRisk.EmpiricalRiskConsumers
import Qatlib.Concepts.RiskEstimation.VaRQuantile.BisectFiniteRoutingSubgoalQuan
import Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase
import Qatlib.Concepts.CircuitImpl.MultiControl.NoWorkTwoLevelSynthesis
import Qatlib.Concepts.RiskEstimation.PopulationGap.Implementation
import Qatlib.Concepts.RiskEstimation.PopulationGap.ImplementationDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.GatesDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.OrderShorDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.FiniteBitAccessDefs

/-!
# Bit and space budgets for dyadic emitters

This module bounds the integer numerator of a dyadic load and defines a conservative bit budget.
It supplies a bounded Euclidean GCD correctness result and correct space schedules with explicit
peak space for the emitter parameters.

The quantum risk-analysis setting is described in [WoernerEgger2019].

## Main statements

* `loadNumerator_bits_lt`: For `|x| ≤ L`, the absolute loaded numerator is strictly less than `2
  ^ loadBitCost k L`.
* `riskEmitter_gcd`: For `|x| ≤ L`, the Euclidean algorithm with the emitter-scale step bound
  computes the GCD of the loaded numerator's natural absolute value and `2 ^ k`.
* `emitter_peakSpace_le`: A correct emitter space schedule exists with word length `loadBitCost
  k L`, event count `e`, and peak space `loadBitCost k L * (e - 1)`.

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PeriodSampling.FactorAlgorithm

open Qatlib
open Matrix
open scoped ENNReal Classical BigOperators
open Qatlib
open Qatlib.Concepts.RiskEstimation.CDFEstimation
open Qatlib.Concepts.RiskEstimation.CVaREstimation
open Qatlib
open Qatlib.Concepts.RiskEstimation.PopulationGap
open Qatlib.Concepts.RiskEstimation.VaRQuantile
open Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018
open Qatlib
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {I : Type} [Fintype I] [DecidableEq I]
variable {n N : ℕ}

namespace Qatlib.Concepts.RiskEstimation.PopulationGap
open scoped Matrix.Norms.L2Operator
open Qatlib.Concepts.RiskEstimation.PopulationGap (clause11 euclid_gcd_fuel)
open Qatlib.Concepts.RiskEstimation.PopulationGap (shorBitLength euclidGcd euclidStepBound)
open Qatlib.Concepts.RiskEstimation.PopulationGap (SpaceSchedule)

/-- The loading bit budget `k + 1 + L`. -/
def loadBitCost (k L : ℕ) : ℕ := k + 1 + L

/-- For `|x| ≤ L`, the loaded numerator lies strictly between `-2 ^ k * (L + 1)` and `2 ^ k * (L
+ 1)`. -/
theorem loadNumerator_bounds (k L : ℕ) {x : ℝ} (hx : |x| ≤ (L : ℝ)) :
    -(2 : ℝ)^k * ((L : ℝ) + 1) < ((loadNumerator k x : ℤ) : ℝ) ∧
      ((loadNumerator k x : ℤ) : ℝ) < (2 : ℝ)^k * ((L : ℝ) + 1) := by
  have hle : ((loadNumerator k x : ℤ) : ℝ) ≤ x * (2 : ℝ)^k := by
    have h := Int.floor_le (x * (2 : ℝ)^k)
    simp only [loadNumerator]
    exact h
  have hlt : ((loadNumerator k x : ℤ) : ℝ) > x * (2 : ℝ)^k - 1 := by
    have h := Int.lt_floor_add_one (x * (2 : ℝ)^k)
    simp only [loadNumerator]
    linarith
  have hxp : x * (2 : ℝ)^k ≤ (L : ℝ) * (2 : ℝ)^k := by
    have hx1 : x ≤ (L : ℝ) := (abs_le.mp hx).2
    exact mul_le_mul_of_nonneg_right hx1 (by positivity : (0:ℝ) ≤ (2:ℝ)^k)
  have hxm : (-(L : ℝ)) * (2 : ℝ)^k ≤ x * (2 : ℝ)^k := by
    have hx1 : (-(L : ℝ)) ≤ x := (abs_le.mp hx).1
    exact mul_le_mul_of_nonneg_right hx1 (by positivity : (0:ℝ) ≤ (2:ℝ)^k)
  have hpow : (1:ℝ) ≤ (2:ℝ)^k := by exact_mod_cast Nat.one_le_pow' k 1
  have hstep : (-(L : ℝ)) * (2 : ℝ)^k - 1 ≥ -(2 : ℝ)^k * ((L : ℝ) + 1) := by
    nlinarith
  constructor
  · linarith
  · linarith

/-- For `|x| ≤ L`, the absolute loaded numerator is strictly less than `2 ^ k * (L + 1)`. -/
theorem loadNumerator_abs_lt (k L : ℕ) {x : ℝ} (hx : |x| ≤ (L : ℝ)) :
    |(loadNumerator k x : ℝ)| < (2 : ℝ)^k * ((L : ℝ) + 1) := by
  obtain ⟨h1, h2⟩ := loadNumerator_bounds k L hx
  rw [abs_lt]
  constructor <;> nlinarith [h1, h2]

/-- For `|x| ≤ L`, the absolute loaded numerator is strictly less than `2 ^ loadBitCost k L`. -/
theorem loadNumerator_bits_lt (k L : ℕ) {x : ℝ} (hx : |x| ≤ (L : ℝ)) :
    |(loadNumerator k x : ℝ)| < (2 : ℝ)^loadBitCost k L := by
  have h1 := loadNumerator_abs_lt k L hx
  have h2 : (2 : ℝ)^loadBitCost k L = (2 : ℝ)^k * (2 : ℝ)^(L + 1) := by
    simp only [loadBitCost]
    rw [← pow_add]
    ring
  have h3 : (2 : ℝ)^(L + 1) > (L : ℝ) + 1 := by
    have hpow' : ((2 : ℕ) ^ (L + 1) : ℝ) > ((L : ℕ) + 1 : ℝ) := by
      exact_mod_cast (two_pow_gt L)
    have h1' : ((2 : ℕ) ^ (L + 1) : ℝ) = (2 : ℝ)^(L + 1) := by simp
    have h2' : ((L : ℕ) + 1 : ℝ) = (L : ℝ) + 1 := by simp
    linarith
  calc |(loadNumerator k x : ℝ)| < (2 : ℝ)^k * ((L : ℝ) + 1) := h1
    _ < (2 : ℝ)^k * (2 : ℝ)^(L + 1) := mul_lt_mul_of_pos_left h3 (by positivity)
    _ = (2 : ℝ)^loadBitCost k L := h2.symm

/-- The emitter scale `2 ^ (k + L + 2)`. -/
def emitterScale (k L : ℕ) : ℕ := 2 ^ (k + L + 2)

/-- The emitter scale has `shorBitLength` equal to `k + L + 3`. -/
theorem emitterScale_bitLength (k L : ℕ) :
    shorBitLength (emitterScale k L) = k + L + 3 := by
  rw [shorBitLength, emitterScale, log2_pow_two]

/-- For `|x| ≤ L`, the Euclidean algorithm with the emitter-scale step bound computes the GCD of
the loaded numerator's natural absolute value and `2 ^ k`. -/
theorem riskEmitter_gcd (k L : ℕ) {x : ℝ} (hx : |x| ≤ (L : ℝ)) :
    euclidGcd (euclidStepBound (emitterScale k L))
      ((loadNumerator k x).natAbs) (2 ^ k) = Nat.gcd ((loadNumerator k x).natAbs) (2 ^ k) := by
  have hbits := emitterScale_bitLength k L
  have hden : (2 : ℕ)^k < 2 ^ shorBitLength (emitterScale k L) := by
    rw [hbits]
    have hbig : (2 : ℕ)^(L + 3) > 1 := by
      have h := two_pow_gt_succ L
      omega
    calc (2 : ℕ)^k = (2 : ℕ)^k * 1 := by simp
      _ < (2 : ℕ)^k * (2 : ℕ)^(L + 3) := Nat.mul_lt_mul_of_pos_left hbig (by positivity)
      _ = (2 : ℕ)^(k + (L + 3)) := (Nat.pow_add ..).symm
      _ = 2 ^ (k + L + 3) := by rw [show k + (L + 3) = k + L + 3 by omega]
  have hnum' : ((loadNumerator k x).natAbs : ℕ) < 2 ^ shorBitLength (emitterScale k L) := by
    rw [hbits]
    have hreal : ((loadNumerator k x).natAbs : ℝ) < (2 : ℝ)^(k + L + 3) := by
      rw [natAbs_cast_eq]
      have h1 := loadNumerator_abs_lt k L hx
      have h3 : (2 : ℝ)^(L + 3) > (L : ℝ) + 1 := by
        have hpow' : ((2 : ℕ) ^ (L + 3) : ℝ) > ((L : ℕ) + 3 : ℝ) := by
          exact_mod_cast (two_pow_gt_succ L)
        have h1' : ((2 : ℕ) ^ (L + 3) : ℝ) = (2 : ℝ)^(L + 3) := by simp
        have h2' : ((L : ℕ) + 3 : ℝ) = (L : ℝ) + 3 := by simp
        linarith
      have hp : (2 : ℝ)^k > 0 := by positivity
      have h4 : (2 : ℝ)^k * ((L : ℝ) + 1) < (2 : ℝ)^(k + L + 3) := by
        calc (2 : ℝ)^k * ((L : ℝ) + 1) < (2 : ℝ)^k * (2 : ℝ)^(L + 3) := by
              exact mul_lt_mul_of_pos_left h3 (by positivity)
          _ = (2 : ℝ)^(k + (L + 3)) := by rw [← pow_add]
          _ = (2 : ℝ)^(k + L + 3) := by rw [show k + (L + 3) = k + L + 3 by omega]
      linarith
    have hcast : ((2 : ℕ)^(k + L + 3) : ℝ) = (2 : ℝ)^(k + L + 3) := by simp
    rw [← hcast] at hreal
    exact_mod_cast hreal
  exact (clause11.1.1 _ _ _ hnum' hden)

/-- For any word length `w` and event count `e`, a correct space schedule exists with those
parameters and peak space `w * (e - 1)`. -/
theorem emitter_peakSpace (w e : ℕ) :
    ∃ S : SpaceSchedule, S.wordLen = w ∧ S.events = e ∧ SpaceSchedule.Correct S ∧
      S.peakSpace = w * (e - 1) :=
  clause11.2.1.2.2 w e

/-- A correct emitter space schedule exists with word length `loadBitCost k L`, event count `e`,
and peak space `loadBitCost k L * (e - 1)`. -/
theorem emitter_peakSpace_le (k L e : ℕ) :
    ∃ S : SpaceSchedule, S.wordLen = loadBitCost k L ∧ S.events = e ∧
      SpaceSchedule.Correct S ∧ S.peakSpace = loadBitCost k L * (e - 1) := by
  obtain ⟨S, h1, h2, h3, h4⟩ := emitter_peakSpace (loadBitCost k L) e
  refine ⟨S, h1, h2, h3, ?_⟩
  unfold SpaceSchedule.peakSpace at h4 ⊢
  rw [h1, h2] at h4 ⊢
  exact h4

/-- Rational order is equivalent to the order of the corresponding real casts. -/
theorem rat_le_iff (a b : ℚ) : (a ≤ b) ↔ ((a : ℝ) ≤ (b : ℝ)) := by
  constructor
  · intro h
    exact_mod_cast h
  · intro h
    exact_mod_cast h
end Qatlib.Concepts.RiskEstimation.PopulationGap
