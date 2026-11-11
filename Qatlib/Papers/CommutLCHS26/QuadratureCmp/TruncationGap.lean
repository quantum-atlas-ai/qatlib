/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.QuadratureCmp.Trapezoid
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

/-!
# A strict gap between operator and lattice tails

This module compares the actual operator truncation error with the scalar lattice-tail bound in
the quadrature analysis of [AftabAnTrivisa2026]. For zero Hamiltonian and identity dissipative
matrix, the operator tail becomes a Fourier transform of the truncated scalar coefficient.

Fourier decay and nonvanishing of the coefficient yield a positive time at which the
one-dimensional operator truncation error is strictly smaller than the lattice tail at unit step
and cutoff.

## Main statements

* `tail_identity_fourier`: Represents the identity-dissipation tail as a scalar Fourier
  transform times the identity.
* `exists_operator_tail_lt_latticeTail`: Constructs a strict inequality between the operator
  error and its lattice-tail bound.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.CommutLCHS26.QuadratureCmp.TruncationGap
open Complex Set Filter MeasureTheory
open scoped Topology FourierTransform
open Qatlib.Papers.CommutLCHS26.MainResults.KernelStrip
open Qatlib.Papers.CommutLCHS26.QuadratureCmp.Trapezoid

/-- For positive `b`, the scalar coefficient is nonzero at every real argument. -/
theorem coefficient_ne_zero (n : ℕ) (b c d x : ℝ) (hb : 0 < b) :
    coefficient n b c d (x : ℂ) ≠ 0 := by
  unfold coefficient
  apply div_ne_zero
  · apply mul_ne_zero
    · apply mul_ne_zero
      · exact_mod_cast (show (b + 1) ^ n / (2 * Real.pi) ≠ 0 by positivity)
      · exact Complex.exp_ne_zero _
    · exact Complex.exp_ne_zero _
  · exact mul_ne_zero (lower_ne_zero (ρ := 0) (by norm_num) (by simp))
      (upper_pow_ne_zero n (ρ := 0) (Or.inr hb) (by simp))

/-- For positive `b`, there is a positive time at which the Fourier transform of the coefficient
restricted to `|x| > R`, evaluated at `T / (2 * π)`, has norm less than the coefficient norm
at `2`. -/
theorem exists_small_fourier_tail (n : ℕ) (b c d R : ℝ) (hb : 0 < b) :
    ∃ T : ℝ, 0 < T ∧
      ‖𝓕 (({x : ℝ | R < |x|}).indicator (fun x : ℝ => coefficient n b c d (x : ℂ)))
        (T / (2 * Real.pi))‖ < ‖coefficient n b c d (2 : ℂ)‖ := by
  let f := ({x : ℝ | R < |x|}).indicator (fun x : ℝ => coefficient n b c d (x : ℂ))
  have hw : Tendsto (𝓕 f) atTop (𝓝 0) :=
    (Real.zero_at_infty_fourier f).mono_left (by rw [cocompact_eq_atBot_atTop]; exact le_sup_right)
  have hp : 0 < ‖coefficient n b c d (2 : ℂ)‖ := norm_pos_iff.mpr
    (by exact_mod_cast coefficient_ne_zero n b c d 2 hb)
  have hwn : Tendsto (fun w => ‖𝓕 f w‖) atTop (𝓝 (0 : ℝ)) := by simpa using! hw.norm
  have he := hwn (Iio_mem_nhds hp)
  obtain ⟨w, hw₀, hw₁⟩ := ((eventually_gt_atTop (0 : ℝ)).and he).exists
  refine ⟨2 * Real.pi * w, mul_pos (mul_pos (by norm_num) Real.pi_pos) hw₀, ?_⟩
  have hd : 2 * Real.pi * w / (2 * Real.pi) = w := by field_simp
  rw [hd]
  exact hw₁

open scoped Matrix.Norms.L2Operator ComplexOrder
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- For zero Hamiltonian and identity dissipative matrix, the propagator is `exp(-T * I * z)`
times the identity. -/
theorem propagator_identity (T : ℝ) (z : ℂ) :
    propagator (0 : Matrix ι ι ℂ) 1 T z =
      Complex.exp ((-T : ℂ) * I * z) • (1 : Matrix ι ι ℂ) := by
  unfold propagator
  simp only [zero_add, smul_smul]
  simpa only [Algebra.algebraMap_eq_smul_one, Complex.exp_eq_exp_ℂ, mul_assoc] using!
    (NormedSpace.algebraMap_exp_comm (𝕂 := ℂ) (𝔸 := Matrix ι ι ℂ) ((-T : ℂ) * I * z)).symm

/-- For zero Hamiltonian and identity dissipative matrix, the tail integral at time `2 * π * w`
equals the Fourier transform of the truncated coefficient at `w`, multiplied by the
identity. -/
theorem tail_identity_fourier (n : ℕ) (b c d R w : ℝ) :
    (∫ x in {x : ℝ | R < |x|},
      integrand n b c d (2 * Real.pi * w) (0 : Matrix ι ι ℂ) 1 (x : ℂ)) =
      (𝓕 (({x : ℝ | R < |x|}).indicator (fun x : ℝ => coefficient n b c d (x : ℂ))) w) •
        (1 : Matrix ι ι ℂ) := by
  have hs : MeasurableSet {x : ℝ | R < |x|} :=
      measurableSet_lt measurable_const continuous_abs.measurable
  rw [Real.fourier_real_eq_integral_exp_smul, ← integral_smul_const, ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : R < |x|
  · simp only [Set.indicator_apply, mem_setOf_eq, if_pos hx]
    simp only [integrand, propagator_identity, smul_smul, smul_eq_mul]
    congr 1
    have hz : (-((2 * Real.pi * w : ℝ) : ℂ)) * I * (x : ℂ) =
        ((-2 * Real.pi * x * w : ℝ) : ℂ) * I := by push_cast; ring
    rw [hz]
    ring
  · simp only [Set.indicator_apply, mem_setOf_eq, if_neg hx, smul_zero, zero_smul]

/-- For positive `b` and `c`, there is a positive time when the one-dimensional operator
truncation error at radius `1` is strictly less than the scalar lattice tail at step `1` and
cutoff `1`. -/
theorem exists_operator_tail_lt_latticeTail (n : ℕ) (b c d : ℝ) (hb : 0 < b) (hc : 0 < c) :
    ∃ T : ℝ, 0 < T ∧
      operatorTruncationError n b c d T (0 : Matrix (Fin 1) (Fin 1) ℂ) 1 1 <
        latticeTail n b c d 1 1 := by
  obtain ⟨T, hT, he⟩ := exists_small_fourier_tail n b c d 1 hb
  have hm : operatorTruncationError n b c d T (0 : Matrix (Fin 1) (Fin 1) ℂ) 1 1 =
      ‖𝓕 (({x : ℝ | (1 : ℝ) < |x|}).indicator (fun x : ℝ => coefficient n b c d (x : ℂ)))
        (T / (2 * Real.pi))‖ := by
    rw [operatorTruncationError_eq_tail n b c d hb hc _ _ Matrix.isHermitian_zero
      Matrix.PosSemidef.one hT.le 1]
    have hi : 2 * Real.pi * (T / (2 * Real.pi)) = T := by field_simp
    have hf := tail_identity_fourier (ι := Fin 1) n b c d 1 (T / (2 * Real.pi))
    rw [hi] at hf
    rw [hf, norm_smul, norm_one, mul_one]
  have hs := (summable_coefficient_norm n b c d hb hc (h := 1) (by norm_num)).subtype
    (fun q : ℤ => q ∉ Finset.Icc (-1 : ℤ) 1)
  have hl : ‖coefficient n b c d (2 : ℂ)‖ ≤ latticeTail n b c d 1 1 := by
    unfold latticeTail
    rw [one_mul]
    have hsingle := hs.le_tsum (i := ⟨2, by norm_num⟩) (fun _ _ => norm_nonneg _)
    simpa only [Int.reduceNeg, Int.cast_ofNat, one_mul, Complex.ofReal_ofNat] using! hsingle
  exact ⟨T, hT, hm.trans_lt (he.trans_le hl)⟩

end Qatlib.Papers.CommutLCHS26.QuadratureCmp.TruncationGap
