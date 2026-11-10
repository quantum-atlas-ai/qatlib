/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PhaseEst07.MainResults.Shared.PathShift
import Qatlib.Papers.PhaseEst07.MainResults.Shared.SinusoidSums
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PhaseEst07.MainResults.VarianceState

open Qatlib.Papers.PhaseEst07.MainResults.Shared
open scoped BigOperators

noncomputable def sourceVarianceVector (q : ℕ) (j : ℕ) : ℝ :=
  Real.sqrt (2 / ((q + 1 : ℕ) : ℝ)) *
    Real.sin (((j : ℝ) + 1) * Real.pi / ((q + 1 : ℕ) : ℝ))

theorem source_sin_mul_sin_eq (A B : ℝ) :
    Real.sin A * Real.sin B = (Real.cos (A - B) - Real.cos (A + B)) / 2 := by
  rw [Real.cos_sub, Real.cos_add]
  ring

theorem source_variance_vector_normalized (q : ℕ) (hq : 1 ≤ q) :
    ∑ j ∈ Finset.range q, (sourceVarianceVector q j) ^ 2 = 1 := by
  have hM2 : 2 ≤ q + 1 := by omega
  have hq1 : q + 1 - 1 = q := by omega
  have hsum := sum_sin_sq_pi_div (q + 1) hM2
  rw [hq1] at hsum
  have hterm : ∀ j ∈ Finset.range q,
      (sourceVarianceVector q j) ^ 2
        = (2 / ((q + 1 : ℕ) : ℝ)) *
            Real.sin (((j : ℝ) + 1) * Real.pi / ((q + 1 : ℕ) : ℝ)) ^ 2 := by
    intro j _
    unfold sourceVarianceVector
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hsum]
  have hMpos : (0 : ℝ) < ((q + 1 : ℕ) : ℝ) := by positivity
  field_simp

theorem source_cos_odd_shift_q (q : ℕ) (hq : 1 ≤ q) :
    ∑ j ∈ Finset.range q,
        Real.cos ((2 * (j : ℝ) + 3) * Real.pi / ((q + 1 : ℕ) : ℝ))
      = - Real.cos (Real.pi / ((q + 1 : ℕ) : ℝ)) := by
  have hM2 : 2 ≤ q + 1 := by omega
  have hodd := sum_cos_odd_zero (q + 1) hM2
  rw [Fin.sum_univ_eq_sum_range
    (fun k => Real.cos ((2 * (k : ℝ) + 1) * Real.pi / ((q + 1 : ℕ) : ℝ))) (q + 1)] at hodd
  rw [Finset.sum_range_succ'] at hodd
  simp only [Nat.cast_zero, mul_zero, zero_add, one_mul] at hodd
  have hcongr : (∑ k ∈ Finset.range q,
        Real.cos ((2 * (((k + 1 : ℕ)) : ℝ) + 1) * Real.pi / ((q + 1 : ℕ) : ℝ)))
      = (∑ k ∈ Finset.range q,
        Real.cos ((2 * (k : ℝ) + 3) * Real.pi / ((q + 1 : ℕ) : ℝ))) := by
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    push_cast
    ring
  rw [hcongr] at hodd
  linarith

theorem source_variance_adjacent_correlation (q : ℕ) (hq : 1 ≤ q) :
    ∑ j ∈ Finset.range q, sourceVarianceVector q j * sourceVarianceVector q (j + 1)
      = Real.cos (Real.pi / ((q + 1 : ℕ) : ℝ)) := by
  set θ : ℝ := Real.pi / ((q + 1 : ℕ) : ℝ) with hθ
  have hterm : ∀ j ∈ Finset.range q,
      sourceVarianceVector q j * sourceVarianceVector q (j + 1)
        = (2 / ((q + 1 : ℕ) : ℝ)) *
            ((Real.cos θ - Real.cos ((2 * (j : ℝ) + 3) * θ)) / 2) := by
    intro j _
    unfold sourceVarianceVector
    have harg1 : ((j : ℝ) + 1) * Real.pi / ((q + 1 : ℕ) : ℝ) = ((j : ℝ) + 1) * θ := by
      rw [hθ]; ring
    have harg2 : ((((j + 1 : ℕ)) : ℝ) + 1) * Real.pi / ((q + 1 : ℕ) : ℝ)
        = ((j : ℝ) + 2) * θ := by
      rw [hθ]; push_cast; ring
    rw [harg1, harg2]
    rw [show (Real.sqrt (2 / ((q + 1 : ℕ) : ℝ)) * Real.sin (((j : ℝ) + 1) * θ))
          * (Real.sqrt (2 / ((q + 1 : ℕ) : ℝ)) * Real.sin (((j : ℝ) + 2) * θ))
        = (Real.sqrt (2 / ((q + 1 : ℕ) : ℝ))) ^ 2 *
            (Real.sin (((j : ℝ) + 1) * θ) * Real.sin (((j : ℝ) + 2) * θ)) by ring]
    rw [Real.sq_sqrt (by positivity), source_sin_mul_sin_eq]
    rw [show ((j : ℝ) + 1) * θ - ((j : ℝ) + 2) * θ = -θ by ring,
        show ((j : ℝ) + 1) * θ + ((j : ℝ) + 2) * θ = (2 * (j : ℝ) + 3) * θ by ring,
        Real.cos_neg]
  rw [show ∑ j ∈ Finset.range q, sourceVarianceVector q j * sourceVarianceVector q (j + 1)
        = ∑ j ∈ Finset.range q,
            (2 / ((q + 1 : ℕ) : ℝ)) *
              ((Real.cos θ - Real.cos ((2 * (j : ℝ) + 3) * θ)) / 2)
        from Finset.sum_congr rfl hterm]
  rw [← Finset.mul_sum]
  have hoddθ : ∑ j ∈ Finset.range q, Real.cos ((2 * (j : ℝ) + 3) * θ) = - Real.cos θ := by
    rw [hθ]
    have h := source_cos_odd_shift_q q hq
    simpa only [mul_div_assoc] using h
  rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, hoddθ]
  have hinner : ((q : ℝ) * Real.cos θ - -Real.cos θ) / 2
      = ((((q + 1 : ℕ)) : ℝ) * Real.cos θ) / 2 := by
    have hq1' : ((q : ℕ) : ℝ) + 1 = (((q + 1 : ℕ)) : ℝ) := by push_cast; ring
    rw [← hq1']; ring
  rw [hinner]
  have hMne : (((q + 1 : ℕ)) : ℝ) ≠ 0 := by positivity
  field_simp

noncomputable def sourceVarianceCost (q : ℕ) : ℝ :=
  (1 - ∑ j ∈ Finset.range q, sourceVarianceVector q j * sourceVarianceVector q (j + 1)) / 2

theorem source_variance_minimum_cost (q : ℕ) (hq : 1 ≤ q) :
    sourceVarianceCost q = Real.sin (Real.pi / (2 * ((q + 1 : ℕ) : ℝ))) ^ 2 := by
  have hsq : Real.sin (Real.pi / (2 * ((q + 1 : ℕ) : ℝ))) ^ 2
      = (1 - Real.cos (Real.pi / ((q + 1 : ℕ) : ℝ))) / 2 := by
    have h2 : (2 : ℝ) * (Real.pi / (2 * ((q + 1 : ℕ) : ℝ)))
        = Real.pi / ((q + 1 : ℕ) : ℝ) := by
      field_simp
    rw [Real.sin_sq_eq_half_sub, h2]
    ring
  unfold sourceVarianceCost
  rw [source_variance_adjacent_correlation q hq, hsq]

theorem source_variance_vector_end (q : ℕ) :
    sourceVarianceVector q q = 0 := by
  unfold sourceVarianceVector
  have harg : ((q : ℝ) + 1) * Real.pi / ((q + 1 : ℕ) : ℝ) = Real.pi := by
    have hcast : ((q + 1 : ℕ) : ℝ) = (q : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    field_simp
  rw [harg, Real.sin_pi, mul_zero]

theorem source_variance_cost_ge (q : ℕ) (hq : 1 ≤ q) (x : ℕ → ℝ)
    (hx : ∑ j ∈ Finset.range q, (x j) ^ 2 = 1) :
    Real.sin (Real.pi / (2 * ((q + 1 : ℕ) : ℝ))) ^ 2
      ≤ (1 - ∑ j ∈ Finset.range (q - 1), x j * x (j + 1)) / 2 := by
  have hq0 : 0 < q := hq
  have hshift := path_shift_le q hq0 x
  have hcos : Real.cos (theta q) = Real.cos (Real.pi / ((q + 1 : ℕ) : ℝ)) := by
    unfold theta
    congr 1
    push_cast
    ring
  have hcorr : ∑ j ∈ Finset.range (q - 1), x j * x (j + 1)
      ≤ Real.cos (Real.pi / ((q + 1 : ℕ) : ℝ)) := by
    rw [hcos, hx] at hshift
    simpa using hshift
  have hsq : Real.sin (Real.pi / (2 * ((q + 1 : ℕ) : ℝ))) ^ 2
      = (1 - Real.cos (Real.pi / ((q + 1 : ℕ) : ℝ))) / 2 := by
    have h2 : (2 : ℝ) * (Real.pi / (2 * ((q + 1 : ℕ) : ℝ)))
        = Real.pi / ((q + 1 : ℕ) : ℝ) := by field_simp
    rw [Real.sin_sq_eq_half_sub, h2]
    ring
  rw [hsq]
  linarith

theorem source_variance_attains (q : ℕ) (hq : 1 ≤ q) :
    (1 - ∑ j ∈ Finset.range (q - 1),
        sourceVarianceVector q j * sourceVarianceVector q (j + 1)) / 2
      = Real.sin (Real.pi / (2 * ((q + 1 : ℕ) : ℝ))) ^ 2 := by
  have hsplit : (∑ j ∈ Finset.range q,
        sourceVarianceVector q j * sourceVarianceVector q (j + 1))
      = (∑ j ∈ Finset.range (q - 1),
          sourceVarianceVector q j * sourceVarianceVector q (j + 1)) := by
    have hq1 : q = (q - 1) + 1 := by omega
    have h := Finset.sum_range_succ
      (fun j => sourceVarianceVector q j * sourceVarianceVector q (j + 1)) (q - 1)
    rw [← hq1] at h
    rw [h]
    have hz : sourceVarianceVector q (q - 1) * sourceVarianceVector q q = 0 := by
      rw [source_variance_vector_end, mul_zero]
    rw [hz, add_zero]
  rw [← hsplit, ← source_variance_minimum_cost q hq]
  unfold sourceVarianceCost
  ring

end Qatlib.Papers.PhaseEst07.MainResults.VarianceState
