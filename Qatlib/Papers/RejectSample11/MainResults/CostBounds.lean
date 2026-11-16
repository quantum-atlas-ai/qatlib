/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.RejectSample11.MainResults.SamplingLowerBound

@[expose] public section


set_option autoImplicit false
open scoped BigOperators

open Qatlib.Papers.RejectSample11.MainResults

namespace Qatlib.Papers.RejectSample11.MainResults

/-- The source Eq. (8) box and unit direction force a strictly positive query
budget; this establishes the positivity side condition rather than assuming it. -/
theorem feasible_query_positive {m : ℕ} (π σ : Fin m → ℚ) (p T : ℝ)
    (g : Fin m → ℝ) (hπ : ∀ i, 0 ≤ π i)
    (h : samplingAngleFeasible π σ p T g) : 0 < T := by
  obtain ⟨hnorm, hcoord, _⟩ := h
  by_contra ht
  have hT : T ≤ 0 := le_of_not_gt ht
  have hgzero : ∀ i, g i = 0 := by
    intro i
    have hπi : (0 : ℝ) ≤ (π i : ℝ) := by exact_mod_cast hπ i
    exact le_antisymm ((hcoord i).2.trans (mul_nonpos_of_nonpos_of_nonneg hT hπi))
      (hcoord i).1
  simp only [hgzero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero] at hnorm
  norm_num at hnorm

/-- A normalized source and the Eq. (8) coordinate box require at least one
query in the reduced direction-vector model. No algorithm symmetrization is assumed proved. -/
theorem feasible_query_one_le {m : ℕ} (π σ : Fin m → ℚ) (p T : ℝ)
    (g : Fin m → ℝ) (hπ : ∀ i, 0 ≤ π i)
    (hnormπ : (∑ i, (π i : ℝ) ^ 2) = 1)
    (h : samplingAngleFeasible π σ p T g) : 1 ≤ T := by
  have hT := feasible_query_positive π σ p T g hπ h
  obtain ⟨hnorm, hcoord, _⟩ := h
  have hsq : (∑ i, g i ^ 2) ≤ ∑ i, (T * (π i : ℝ)) ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    exact pow_le_pow_left₀ (hcoord i).1 (hcoord i).2 2
  simp_rw [mul_pow] at hsq
  rw [← Finset.mul_sum, hnormπ, mul_one, hnorm] at hsq
  nlinarith

end Qatlib.Papers.RejectSample11.MainResults
