/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.SieveLaw.MixedSelectivePerturbation

/-!
# Distance between normalized positive branches

This module bounds the trace-norm distance between `normalizedPositiveBranch` outputs of
positive semidefinite matrices with positive real traces. The symmetric estimate uses the larger
output trace in the denominator, refining the normalization estimates for quantum operations
discussed in [Watrous2018].

## Main statements

* `normalized_positive_branch_distance`: a symmetric normalization bound using the maximum
  branch mass.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.HspRecovery.SieveLaw

open Matrix
open scoped Classical ComplexOrder Matrix.Norms.L2Operator

set_option autoImplicit false

/-- For a positive semidefinite first matrix and positive real traces of both matrices,
normalized trace-norm distance is bounded by the sum of unnormalized distance and trace
difference divided by the second trace. -/
private theorem normalized_branch_distance_right {I : Type} [Fintype I]
    [DecidableEq I] (σ τ : Matrix I I ℂ) (hσ : σ.PosSemidef)
    (hp : 0 < (Matrix.trace σ).re) (hq : 0 < (Matrix.trace τ).re) :
    Matrix.traceNorm (normalizedPositiveBranch σ - normalizedPositiveBranch τ) ≤
      (Matrix.traceNorm (σ - τ) + |(Matrix.trace σ).re - (Matrix.trace τ).re|) /
        (Matrix.trace τ).re := by
  have hns : normalizedPositiveBranch σ
      = (((Matrix.trace σ).re)⁻¹ : ℂ) • σ := by
    rw [normalizedPositiveBranch, if_pos hp]
  have hnt : normalizedPositiveBranch τ
      = (((Matrix.trace τ).re)⁻¹ : ℂ) • τ := by
    rw [normalizedPositiveBranch, if_pos hq]
  have hcoe : (((((Matrix.trace σ).re)⁻¹ - ((Matrix.trace τ).re)⁻¹ : ℝ) : ℂ)) • σ
      = (((Matrix.trace σ).re)⁻¹ : ℂ) • σ - (((Matrix.trace τ).re)⁻¹ : ℂ) • σ := by
    rw [Complex.ofReal_sub, Complex.ofReal_inv, Complex.ofReal_inv, sub_smul]
  have hsplit : normalizedPositiveBranch σ - normalizedPositiveBranch τ
      = (((Matrix.trace τ).re)⁻¹ : ℂ) • (σ - τ)
        + ((((Matrix.trace σ).re)⁻¹ - ((Matrix.trace τ).re)⁻¹ : ℝ) : ℂ) • σ := by
    rw [hns, hnt, smul_sub, hcoe]
    abel
  have hnormσ : Matrix.traceNorm σ = (Matrix.trace σ).re :=
    posSemidef_traceNorm_eq_re hσ
  have hfirst : Matrix.traceNorm ((((Matrix.trace τ).re)⁻¹ : ℂ) • (σ - τ))
      = Matrix.traceNorm (σ - τ) / (Matrix.trace τ).re := by
    rw [Matrix.traceNorm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hq]
    ring
  have hsecond : Matrix.traceNorm
      (((((Matrix.trace σ).re)⁻¹ - ((Matrix.trace τ).re)⁻¹ : ℝ) : ℂ) • σ)
      = |(Matrix.trace σ).re - (Matrix.trace τ).re| / (Matrix.trace τ).re := by
    rw [Matrix.traceNorm_smul, Complex.norm_real, Real.norm_eq_abs, hnormσ]
    have hsp : ((Matrix.trace σ).re)⁻¹ - ((Matrix.trace τ).re)⁻¹
        = ((Matrix.trace τ).re - (Matrix.trace σ).re) /
          ((Matrix.trace σ).re * (Matrix.trace τ).re) := by
      field_simp [ne_of_gt hp, ne_of_gt hq]
    have hconv : |(Matrix.trace τ).re - (Matrix.trace σ).re| /
        ((Matrix.trace σ).re * (Matrix.trace τ).re) * (Matrix.trace σ).re
        = |(Matrix.trace τ).re - (Matrix.trace σ).re| / (Matrix.trace τ).re := by
      field_simp [ne_of_gt hp, ne_of_gt hq]
    rw [hsp, abs_div, abs_of_pos (mul_pos hp hq), hconv, abs_sub_comm]
  rw [hsplit]
  calc
    Matrix.traceNorm
        ((((Matrix.trace τ).re)⁻¹ : ℂ) • (σ - τ) +
          ((((Matrix.trace σ).re)⁻¹ - ((Matrix.trace τ).re)⁻¹ : ℝ) : ℂ) • σ)
      ≤ Matrix.traceNorm ((((Matrix.trace τ).re)⁻¹ : ℂ) • (σ - τ)) +
          Matrix.traceNorm
            (((((Matrix.trace σ).re)⁻¹ - ((Matrix.trace τ).re)⁻¹ : ℝ) : ℂ) • σ) :=
        Matrix.traceNorm_add_le _ _
    _ = Matrix.traceNorm (σ - τ) / (Matrix.trace τ).re +
        |(Matrix.trace σ).re - (Matrix.trace τ).re| / (Matrix.trace τ).re := by
      rw [hfirst, hsecond]
    _ = (Matrix.traceNorm (σ - τ) +
        |(Matrix.trace σ).re - (Matrix.trace τ).re|) / (Matrix.trace τ).re := by
      ring

/-- Exchanging the order of a matrix difference preserves its trace norm. -/
private theorem trace_norm_sub_swap {I : Type} [Fintype I]
    (A B : Matrix I I ℂ) : Matrix.traceNorm (A - B) = Matrix.traceNorm (B - A) := by
  have hsub : A - B = -(B - A) := by abel
  rw [hsub, Matrix.traceNorm_neg]

/-- For positive semidefinite matrices of positive real trace, normalized trace-norm distance is
bounded by the sum of unnormalized distance and trace difference divided by the larger
trace. -/
theorem normalized_positive_branch_distance :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (σ τ : Matrix I I ℂ),
      σ.PosSemidef → τ.PosSemidef →
      0 < (Matrix.trace σ).re → 0 < (Matrix.trace τ).re →
      Matrix.traceNorm (normalizedPositiveBranch σ - normalizedPositiveBranch τ) ≤
        (Matrix.traceNorm (σ - τ) + |(Matrix.trace σ).re - (Matrix.trace τ).re|) /
          max (Matrix.trace σ).re (Matrix.trace τ).re := by
  intro I _ _ σ τ hσ hτ hp hq
  by_cases hpq : (Matrix.trace σ).re ≤ (Matrix.trace τ).re
  · rw [max_eq_right hpq]
    exact normalized_branch_distance_right σ τ hσ hp hq
  · have hqp : (Matrix.trace τ).re ≤ (Matrix.trace σ).re :=
      le_of_lt (lt_of_not_ge hpq)
    rw [max_eq_left hqp]
    have hswap := normalized_branch_distance_right τ σ hτ hq hp
    rw [trace_norm_sub_swap (normalizedPositiveBranch τ) (normalizedPositiveBranch σ),
      trace_norm_sub_swap τ σ, abs_sub_comm] at hswap
    exact hswap

end Qatlib.Concepts.HspRecovery.SieveLaw
