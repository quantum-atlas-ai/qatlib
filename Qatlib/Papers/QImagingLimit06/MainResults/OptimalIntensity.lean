/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QImagingLimit06.MainResults.FisherCore
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QImagingLimit06.MainResults

def intensitySignal {ι : Type} [Fintype ι] (N p a : ℝ) (g absU0 uI : ι → ℝ) : ℝ :=
  (2 * N * p / a) * ∑ k, g k * absU0 k * uI k

def intensityNoisePower {ι : Type} [Fintype ι] (N : ℝ) (g absU0 : ι → ℝ) : ℝ :=
  N * ∑ k, (g k * absU0 k) ^ 2

theorem intensity_snr_le_bound {ι : Type} [Fintype ι] (N p a : ℝ)
    (g absU0 uI : ι → ℝ) (_hN : 0 < N) (huI : ∑ k, uI k ^ 2 = 1) :
    (intensitySignal N p a g absU0 uI) ^ 2 ≤
      (4 * N * p ^ 2 / a ^ 2) * intensityNoisePower N g absU0 := by
  have hCS : (∑ k, g k * absU0 k * uI k) ^ 2 ≤ ∑ k, (g k * absU0 k) ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
      (fun k => g k * absU0 k) uI
    simpa [huI, mul_assoc] using h
  have hpos : (0 : ℝ) ≤ (2 * N * p / a) ^ 2 := sq_nonneg _
  have hstep := mul_le_mul_of_nonneg_left hCS hpos
  have hgoal : ((2 * N * p / a) * ∑ k, g k * absU0 k * uI k) ^ 2 =
      (2 * N * p / a) ^ 2 * (∑ k, g k * absU0 k * uI k) ^ 2 := by ring
  have heq : (2 * N * p / a) ^ 2 * ∑ k, (g k * absU0 k) ^ 2 =
      (4 * N * p ^ 2 / a ^ 2) * (N * ∑ k, (g k * absU0 k) ^ 2) := by ring
  unfold intensitySignal intensityNoisePower
  rw [hgoal]
  linarith [hstep, heq]

theorem intensity_snr_at_optimal_gain {ι : Type} [Fintype ι] (N p a β : ℝ)
    (g absU0 uI : ι → ℝ) (huI : ∑ k, uI k ^ 2 = 1)
    (hprop : ∀ k, g k * absU0 k = β * uI k) :
    (intensitySignal N p a g absU0 uI) ^ 2 =
      (4 * N * p ^ 2 / a ^ 2) * intensityNoisePower N g absU0 := by
  have hT : ∑ k, g k * absU0 k * uI k = β := by
    calc ∑ k, g k * absU0 k * uI k = ∑ k, β * uI k * uI k := by
          exact Finset.sum_congr rfl fun k _ => by rw [hprop k]
      _ = β * ∑ k, uI k ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = β := by rw [huI, mul_one]
  have hS : ∑ k, (g k * absU0 k) ^ 2 = β ^ 2 := by
    calc ∑ k, (g k * absU0 k) ^ 2 = ∑ k, (β * uI k) ^ 2 := by
          exact Finset.sum_congr rfl fun k _ => by rw [hprop k]
      _ = β ^ 2 * ∑ k, uI k ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = β ^ 2 := by rw [huI, mul_one]
  unfold intensitySignal intensityNoisePower
  rw [hT, hS]
  ring

theorem optimal_intensity_pmin {N a p : ℝ} (hN : 0 < N) (ha : 0 < a)
    (hp : 0 < p) (hSNR : 4 * N * p ^ 2 / a ^ 2 = 1) :
    p = a / (2 * Real.sqrt N) :=
  pmin_of_snr_one hN ha hp hSNR

end Qatlib.Papers.QImagingLimit06.MainResults
