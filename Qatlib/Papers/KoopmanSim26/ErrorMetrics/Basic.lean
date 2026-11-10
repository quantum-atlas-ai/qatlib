/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.KoopmanFlow.Sampling

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.KoopmanSim26.ErrorMetrics

def relativeSquaredError {E : Type*} [SeminormedAddCommGroup E] (prediction reference : E) : ℝ :=
  ‖prediction-reference‖^2 / ‖reference‖^2

theorem relativeSquaredError_nonneg {E : Type*} [SeminormedAddCommGroup E]
    (prediction reference : E) : 0 ≤ relativeSquaredError prediction reference := by
  unfold relativeSquaredError
  positivity

theorem relativeSquaredError_eq_zero_iff {E : Type*} [NormedAddCommGroup E]
    (prediction reference : E) (href : reference ≠ 0) :
    relativeSquaredError prediction reference = 0 ↔ prediction = reference := by
  have hd : ‖reference‖^2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr href)
  simp [relativeSquaredError, div_eq_zero_iff, hd, norm_eq_zero, sub_eq_zero]

theorem seven_stage_error {E : Type*} [PseudoMetricSpace E] (stage : ℕ → E)
    (error : ℕ → ℝ) (h : ∀ i < 7, dist (stage i) (stage (i+1)) ≤ error i) :
    dist (stage 0) (stage 7) ≤ ∑ i ∈ Finset.range 7, error i :=
  dist_le_range_sum_of_dist_le 7 (fun hi => h _ hi)

theorem decoded_error_bound {E Y : Type*} [PseudoMetricSpace E] [PseudoMetricSpace Y]
    (stage : ℕ → E) (error : ℕ → ℝ) (decoder : E → Y) (K : NNReal)
    (hdecoder : LipschitzWith K decoder) (reference : Y)
    (h : ∀ i < 7, dist (stage i) (stage (i+1)) ≤ error i) :
    dist (decoder (stage 7)) reference ≤
      (K : ℝ) * (∑ i ∈ Finset.range 7, error i) + dist (decoder (stage 0)) reference := by
  refine (dist_triangle _ (decoder (stage 0)) _).trans ?_
  have hstage := (hdecoder.dist_le_mul (stage 7) (stage 0)).trans
    (mul_le_mul_of_nonneg_left (by simpa only [dist_comm] using seven_stage_error stage error h) K.coe_nonneg)
  exact add_le_add hstage (le_refl _)

def hellingerFidelity {I : Type} [Fintype I] (p q : FinDist I) : ℝ :=
  (∑ i, Real.sqrt (p.prob i) * Real.sqrt (q.prob i))^2

theorem hellingerFidelity_mem_unit {I : Type} [Fintype I] (p q : FinDist I) :
    0 ≤ hellingerFidelity p q ∧ hellingerFidelity p q ≤ 1 := by
  have hnonneg : 0 ≤ ∑ i, Real.sqrt (p.prob i) * Real.sqrt (q.prob i) := by positivity
  have hupper := Real.sum_sqrt_mul_sqrt_le Finset.univ p.nonneg q.nonneg
  rw [p.sum_one, q.sum_one] at hupper
  simp only [Real.sqrt_one, one_mul] at hupper
  constructor
  · exact sq_nonneg _
  · unfold hellingerFidelity
    nlinarith

end Qatlib.Papers.KoopmanSim26.ErrorMetrics
