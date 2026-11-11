/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPCAAssume18.ClassicalPca.OutputAccuracy

/-!
# Precision constraints for PCA accuracy

Shows that the selected precision parameter is positive and that its three branches imply the
Gram tolerances needed for cutoff preservation, squared singular value accuracy, spectral
isolation, and vector accuracy. These estimates specialize the perturbation analysis for the PCA
parameters in [Tang2021].

## Main statements

* `pca_tolerance_spectrum`: The eigenvalue-error precision branch implies `2 * pcaGramTolerance
  K e ≤ s` under the stated nonnegativity assumptions.
* `pca_tolerance_vector`: Under the stated parameter, eigenvalue, and row-norm bounds, the
  combined rescaling and phase-error expression is at most `v`.

## References

* [Tang, 2021][Tang2021]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical BigOperators Matrix.Norms.L2Operator
namespace Qatlib.Papers.QPCAAssume18.ClassicalPca
open Matrix
open Qatlib.Concepts.SketchArith.SketchBuild
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb

/-- The selected PCA precision parameter is positive when both error tolerances, the gap
parameter, and the effective rank parameter are positive. -/
theorem pca_source_parameter_pos (s v eta K : ℝ) (hs : 0 < s) (hv : 0 < v)
    (heta : 0 < eta) (hK : 0 < K) : 0 < epsParameter s v eta K := by
  unfold epsParameter
  exact lt_min (lt_min (by positivity) (by positivity)) (by positivity)

/-- For `K ≥ 1`, its square root lies between one and `K`. -/
theorem pca_rank_sqrt (K : ℝ) (hK : 1 ≤ K) : 1 ≤ Real.sqrt K ∧ Real.sqrt K ≤ K := by
  have h0 : 0 ≤ K := by linarith
  have hs := Real.sq_sqrt h0
  have hn := Real.sqrt_nonneg K
  constructor <;> nlinarith

/-- The inverse-square-root precision constraint and `F = K * sigma^2` imply that the
energy-scaled Gram tolerance is at most `sigma^2 / 4`. -/
theorem pca_tolerance_cutoff (F sigma K e : ℝ) (hsigma : 0 < sigma) (hK : 1 ≤ K)
    (hF : F = K * sigma ^ 2) (he : e ≤ (1 / 4) * (Real.sqrt K)⁻¹) :
    pcaGramTolerance K e * F ≤ sigma ^ 2 / 4 := by
  have hK0 : 0 < K := by linarith
  have hs := (pca_rank_sqrt K hK).1
  have he1 : e ≤ 1 / 4 := by
    have hi : (Real.sqrt K)⁻¹ ≤ 1 := (inv_le_one₀ (by linarith)).mpr hs
    nlinarith
  rw [pcaGramTolerance,hF,div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : (0:ℝ)<100*K^2)).mpr
  have hm := mul_le_mul_of_nonneg_right he1 (by positivity : (0:ℝ)≤K*sigma^2)
  nlinarith [sq_nonneg (K-1), mul_nonneg (sub_nonneg.mpr hK) (sq_nonneg sigma)]

/-- The eigenvalue-error precision branch implies `2 * pcaGramTolerance K e ≤ s` under the
stated nonnegativity assumptions. -/
theorem pca_tolerance_spectrum (K e s : ℝ) (hK : 1 ≤ K) (hs : 0 ≤ s)
    (he : e ≤ (1 / 10) * s * (K * Real.sqrt K)) :
    2 * pcaGramTolerance K e ≤ s := by
  have hK0 : 0 < K := by linarith
  have hroot := (pca_rank_sqrt K hK).2
  have hem : e ≤ (1/10)*s*K^2 := he.trans (by nlinarith [mul_nonneg hs (sub_nonneg.mpr hroot)])
  unfold pcaGramTolerance
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by positivity : (0:ℝ)<100*K^2)).mpr
  nlinarith [mul_nonneg hs (sq_nonneg K)]

/-- The vector-error precision branch with `0 ≤ v ≤ 1` implies `2 * pcaGramTolerance K e ≤ eta /
2`. -/
theorem pca_tolerance_gap (K e v eta : ℝ) (hK : 1 ≤ K) (hv : 0 ≤ v) (hv1 : v ≤ 1)
    (heta : 0 ≤ eta) (he : e ≤ v ^ 2 * eta) :
    2 * pcaGramTolerance K e ≤ eta / 2 := by
  have hK0 : 0 < K := by linarith
  have hv2 : v^2 ≤ 1 := by nlinarith
  have hem : e ≤ eta := he.trans (by nlinarith)
  unfold pcaGramTolerance
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by positivity : (0:ℝ)<100*K^2)).mpr
  nlinarith [sq_nonneg (K-1), mul_nonneg heta (by nlinarith : (0:ℝ)≤K^2-1)]

/-- A sketch with energy at most the input energy has operator norm at most `sigma * K` when the
input energy is `K * sigma^2` and `K ≥ 1`. -/
theorem pca_row_operator_bound {n d q : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (R : Matrix (Fin q) (Fin d) ℂ) (sigma K : ℝ) (hsigma : 0 < sigma) (hK : 1 ≤ K)
    (hF : sketchSquared A = K * sigma ^ 2) (hR : sketchSquared R ≤ sketchSquared A) :
    ‖R‖ ≤ sigma * K := by
  have hK0 : 0 ≤ K := by linarith
  have hfrob : spectralFrobenius R ≤ sigma * K := by
    unfold spectralFrobenius
    change Real.sqrt (sketchSquared R) ≤ sigma*K
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    have hm : K*sigma^2 ≤ (sigma*K)^2 := by
      nlinarith [mul_nonneg (sq_nonneg sigma) (by nlinarith [sq_nonneg (K-1)] : 0 ≤ K^2-K)]
    exact hR.trans (hF.trans_le hm)
  exact (spectral_operator_norm_le_frobenius R).trans hfrob

/-- Under the stated parameter, eigenvalue, and row-norm bounds, the combined rescaling and
phase-error expression is at most `v`. -/
theorem pca_tolerance_vector (F sigma K e eta v mu r : ℝ)
    (hF0 : 0 < F) (hsigma : 0 < sigma) (hK : 1 ≤ K) (he0 : 0 ≤ e)
    (heta : 0 < eta) (heta1 : eta ≤ 1) (hv : 0 ≤ v) (hv1 : v ≤ 1)
    (hF : F = K*sigma^2) (he : e ≤ v^2*eta)
    (hmu : sigma^2/2 ≤ mu) (hr : r ≤ sigma*K) :
    (pcaGramTolerance K e * F) / mu + (4 / (eta*F)) *
      (pcaGramTolerance K e * F + 2*r*(pcaGramTolerance K e*F)/sigma) ≤ v := by
  have hK0 : 0 < K := by linarith
  have hmu0 : 0 < mu := lt_of_lt_of_le (by positivity) hmu
  have ht0 : 0 ≤ pcaGramTolerance K e := by unfold pcaGramTolerance; positivity
  have hfirst : (pcaGramTolerance K e * F)/mu ≤ 2*pcaGramTolerance K e*K := by
    apply (div_le_iff₀ hmu0).mpr
    have hm := mul_le_mul_of_nonneg_left hmu (by positivity : 0 ≤ 2*pcaGramTolerance K e*K)
    rw [hF]
    nlinarith
  have hinner : 2*r*(pcaGramTolerance K e*F)/sigma ≤ 2*K*(pcaGramTolerance K e*F) := by
    apply (div_le_iff₀ hsigma).mpr
    nlinarith [mul_le_mul_of_nonneg_right hr (by positivity : 0≤2*(pcaGramTolerance K e*F))]
  have hsecond : (4/(eta*F))*(pcaGramTolerance K e*F + 2*r*(pcaGramTolerance K e*F)/sigma) ≤
      12*pcaGramTolerance K e*K/eta := by
    calc
      _ ≤ (4/(eta*F))*(pcaGramTolerance K e*F+2*K*(pcaGramTolerance K e*F)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 4*pcaGramTolerance K e*(1+2*K)/eta := by field_simp
      _ ≤ _ := by
        apply (div_le_div_iff_of_pos_right heta).mpr
        nlinarith
  have hjoin : 2*pcaGramTolerance K e*K + 12*pcaGramTolerance K e*K/eta ≤
      14*pcaGramTolerance K e*K/eta := by
    apply (le_div_iff₀ heta).mpr
    have hd : 12*pcaGramTolerance K e*K/eta*eta=12*pcaGramTolerance K e*K := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left heta1 (by positivity : 0≤2*pcaGramTolerance K e*K)]
  have hlast : 14*pcaGramTolerance K e*K/eta ≤ v := by
    unfold pcaGramTolerance
    apply (div_le_iff₀ heta).mpr
    rw [← mul_div_assoc, div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0<100*K^2)).mpr
    have hv2 : v^2≤v := by nlinarith
    have hev : e≤v*eta := he.trans (mul_le_mul_of_nonneg_right hv2 heta.le)
    have hm := mul_le_mul_of_nonneg_right hev hK0.le
    nlinarith [mul_nonneg (mul_nonneg hv heta.le) (by nlinarith [sq_nonneg (K-1)] : 0≤100*K^2-14*K)]
  exact (add_le_add hfirst hsecond).trans (hjoin.trans hlast)

end Qatlib.Papers.QPCAAssume18.ClassicalPca
