/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPCAAssume18.ClassicalPca.ActualGramLaw
import Mathlib.Analysis.InnerProductSpace.Adjoint
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.QPCAAssume18.ClassicalPca
open Matrix
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb

theorem pca_matrix_mul {m n d : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (B : Matrix (Fin n) (Fin d) ℂ) (v : EuclideanSpace ℂ (Fin d)) :
    (A * B).toEuclideanLin v = A.toEuclideanLin (B.toEuclideanLin v) := by
  exact congrArg (fun f : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) => f v)
    (Matrix.toLpLin_mul 2 2 2 A B)

theorem pca_matrix_sub {m d : ℕ} (A B : Matrix (Fin m) (Fin d) ℂ)
    (v : EuclideanSpace ℂ (Fin d)) :
    (A - B).toEuclideanLin v = A.toEuclideanLin v - B.toEuclideanLin v := by
  rw [map_sub]
  rfl

theorem pca_lift_norm_sq {q d : ℕ} (R : Matrix (Fin q) (Fin d) ℂ)
    (w : EuclideanSpace ℂ (Fin q)) :
    ‖Rᴴ.toEuclideanLin w‖ ^ 2 = (inner ℂ w ((R * Rᴴ).toEuclideanLin w)).re := by
  have h := LinearMap.adjoint_inner_left R.toEuclideanLin (Rᴴ.toEuclideanLin w) w
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint] at h
  calc
    _ = (inner ℂ (Rᴴ.toEuclideanLin w) (Rᴴ.toEuclideanLin w)).re :=
      (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
    _ = (inner ℂ w (R.toEuclideanLin (Rᴴ.toEuclideanLin w))).re := congrArg Complex.re h
    _ = _ := by rw [pca_matrix_mul]

theorem pca_lift_norm_error {q d : ℕ} (R : Matrix (Fin q) (Fin d) ℂ)
    (W : Matrix (Fin q) (Fin q) ℂ) (w : EuclideanSpace ℂ (Fin q)) (mu eta : ℝ)
    (hw : ‖w‖ = 1) (haction : (W * Wᴴ).toEuclideanLin w = (mu : ℂ) • w)
    (hgram : spectralFrobenius (W * Wᴴ - R * Rᴴ) ≤ eta) :
    |‖Rᴴ.toEuclideanLin w‖ ^ 2 - mu| ≤ eta := by
  have hnorm : ‖R * Rᴴ - W * Wᴴ‖ ≤ eta := by
    rw [norm_sub_rev]
    exact (spectral_operator_norm_le_frobenius _).trans hgram
  have hwinner : inner ℂ w w = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hw, RCLike.ofReal_one, one_pow]
  have hid : (inner ℂ w ((R * Rᴴ - W * Wᴴ).toEuclideanLin w)).re =
      ‖Rᴴ.toEuclideanLin w‖ ^ 2 - mu := by
    rw [pca_matrix_sub, inner_sub_right, haction, inner_smul_right, hwinner, mul_one]
    simp only [Complex.sub_re, Complex.ofReal_re]
    rw [← pca_lift_norm_sq]
  rw [← hid]
  calc
    _ ≤ ‖inner ℂ w ((R * Rᴴ - W * Wᴴ).toEuclideanLin w)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖w‖ * ‖(R * Rᴴ - W * Wᴴ).toEuclideanLin w‖ := norm_inner_le_norm _ _
    _ ≤ ‖w‖ * (‖R * Rᴴ - W * Wᴴ‖ * ‖w‖) :=
      mul_le_mul_of_nonneg_left (Matrix.l2_opNorm_mulVec _ w) (norm_nonneg _)
    _ ≤ eta := by rw [hw]; simpa only [mul_one, one_mul] using! hnorm

theorem pca_lift_norm_lower {q d : ℕ} (R : Matrix (Fin q) (Fin d) ℂ)
    (W : Matrix (Fin q) (Fin q) ℂ) (w : EuclideanSpace ℂ (Fin q)) (mu eta sigma : ℝ)
    (hw : ‖w‖ = 1) (haction : (W * Wᴴ).toEuclideanLin w = (mu : ℂ) • w)
    (hgram : spectralFrobenius (W * Wᴴ - R * Rᴴ) ≤ eta)
    (hsigma : 0 < sigma) (hmu : sigma ^ 2 / 2 ≤ mu) (heta : eta ≤ sigma ^ 2 / 4) :
    sigma / 2 ≤ ‖Rᴴ.toEuclideanLin w‖ := by
  have h := (abs_le.mp (pca_lift_norm_error R W w mu eta hw haction hgram)).1
  have hn := norm_nonneg (Rᴴ.toEuclideanLin w)
  nlinarith

theorem pca_lift_residual {n q d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (R : Matrix (Fin q) (Fin d) ℂ) (W : Matrix (Fin q) (Fin q) ℂ)
    (w : EuclideanSpace ℂ (Fin q)) (mu etaRow etaCol : ℝ)
    (hw : ‖w‖ = 1) (haction : (W * Wᴴ).toEuclideanLin w = (mu : ℂ) • w)
    (hrow : spectralFrobenius (Rᴴ * R - Aᴴ * A) ≤ etaRow)
    (hcol : spectralFrobenius (W * Wᴴ - R * Rᴴ) ≤ etaCol) :
    ‖(Aᴴ * A).toEuclideanLin (Rᴴ.toEuclideanLin w) - (mu : ℂ) • (Rᴴ.toEuclideanLin w)‖ ≤
      etaRow * ‖Rᴴ.toEuclideanLin w‖ + ‖R‖ * etaCol := by
  let x := Rᴴ.toEuclideanLin w
  have hrowOp : ‖Aᴴ * A - Rᴴ * R‖ ≤ etaRow := by
    rw [norm_sub_rev]
    exact (spectral_operator_norm_le_frobenius _).trans hrow
  have hcolOp : ‖R * Rᴴ - W * Wᴴ‖ ≤ etaCol := by
    rw [norm_sub_rev]
    exact (spectral_operator_norm_le_frobenius _).trans hcol
  have hmiddle : (Rᴴ * R).toEuclideanLin x = Rᴴ.toEuclideanLin ((R * Rᴴ).toEuclideanLin w) := by
    dsimp [x]
    rw [← pca_matrix_mul, ← pca_matrix_mul, Matrix.mul_assoc]
  have hid : (Aᴴ * A).toEuclideanLin x - (mu : ℂ) • x =
      (Aᴴ * A - Rᴴ * R).toEuclideanLin x +
        Rᴴ.toEuclideanLin ((R * Rᴴ - W * Wᴴ).toEuclideanLin w) := by
    rw [pca_matrix_sub, pca_matrix_sub, map_sub, haction, map_smul, ← hmiddle]
    dsimp [x]
    abel
  rw [hid]
  calc
    _ ≤ ‖(Aᴴ * A - Rᴴ * R).toEuclideanLin x‖ +
        ‖Rᴴ.toEuclideanLin ((R * Rᴴ - W * Wᴴ).toEuclideanLin w)‖ := norm_add_le _ _
    _ ≤ ‖Aᴴ * A - Rᴴ * R‖ * ‖x‖ + ‖Rᴴ‖ * (‖R * Rᴴ - W * Wᴴ‖ * ‖w‖) := by
      have hleft := Matrix.l2_opNorm_mulVec (Aᴴ * A - Rᴴ * R) x
      have hinner := Matrix.l2_opNorm_mulVec (R * Rᴴ - W * Wᴴ) w
      have houter := Matrix.l2_opNorm_mulVec Rᴴ ((R * Rᴴ - W * Wᴴ).toEuclideanLin w)
      exact add_le_add hleft (houter.trans (mul_le_mul_of_nonneg_left hinner (norm_nonneg Rᴴ)))
    _ ≤ _ := by
      rw [Matrix.l2_opNorm_conjTranspose, hw, mul_one]
      exact add_le_add (mul_le_mul_of_nonneg_right hrowOp (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hcolOp (norm_nonneg R))

def pcaUnitLift {q d : ℕ} (R : Matrix (Fin q) (Fin d) ℂ)
    (w : EuclideanSpace ℂ (Fin q)) : EuclideanSpace ℂ (Fin d) :=
  ((‖Rᴴ.toEuclideanLin w‖ : ℂ))⁻¹ • Rᴴ.toEuclideanLin w

theorem pcaUnitLift_norm {q d : ℕ} (R : Matrix (Fin q) (Fin d) ℂ)
    (w : EuclideanSpace ℂ (Fin q)) (hx : 0 < ‖Rᴴ.toEuclideanLin w‖) :
    ‖pcaUnitLift R w‖ = 1 := by
  rw [pcaUnitLift, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
  exact inv_mul_cancel₀ hx.ne'

theorem pcaUnitLift_residual {n q d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (R : Matrix (Fin q) (Fin d) ℂ) (W : Matrix (Fin q) (Fin q) ℂ)
    (w : EuclideanSpace ℂ (Fin q)) (mu etaRow etaCol sigma : ℝ)
    (hw : ‖w‖ = 1) (haction : (W * Wᴴ).toEuclideanLin w = (mu : ℂ) • w)
    (hrow : spectralFrobenius (Rᴴ * R - Aᴴ * A) ≤ etaRow)
    (hcol : spectralFrobenius (W * Wᴴ - R * Rᴴ) ≤ etaCol)
    (hsigma : 0 < sigma) (hmu : sigma ^ 2 / 2 ≤ mu) (heta : etaCol ≤ sigma ^ 2 / 4) :
    ‖(Aᴴ * A).toEuclideanLin (pcaUnitLift R w) - (mu : ℂ) • pcaUnitLift R w‖ ≤
      etaRow + 2 * ‖R‖ * etaCol / sigma := by
  have hnorm := pca_lift_norm_lower R W w mu etaCol sigma hw haction hcol hsigma hmu heta
  have hx : 0 < ‖Rᴴ.toEuclideanLin w‖ := lt_of_lt_of_le (by linarith : (0 : ℝ) < sigma / 2) hnorm
  have hres := pca_lift_residual A R W w mu etaRow etaCol hw haction hrow hcol
  have hCol0 : 0 ≤ etaCol := (Real.sqrt_nonneg _).trans hcol
  have hid : (Aᴴ * A).toEuclideanLin (pcaUnitLift R w) - (mu : ℂ) • pcaUnitLift R w =
      ((‖Rᴴ.toEuclideanLin w‖ : ℂ))⁻¹ •
        ((Aᴴ * A).toEuclideanLin (Rᴴ.toEuclideanLin w) - (mu : ℂ) • Rᴴ.toEuclideanLin w) := by
    rw [pcaUnitLift, map_smul, smul_sub]
    module
  rw [hid, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
  calc
    _ ≤ ‖Rᴴ.toEuclideanLin w‖⁻¹ * (etaRow * ‖Rᴴ.toEuclideanLin w‖ + ‖R‖ * etaCol) :=
      mul_le_mul_of_nonneg_left hres (by positivity)
    _ = etaRow + ‖R‖ * etaCol / ‖Rᴴ.toEuclideanLin w‖ := by field_simp
    _ ≤ _ := by
      have hdiv := one_div_le_one_div_of_le (by linarith : (0 : ℝ) < sigma / 2) hnorm
      have hm := mul_le_mul_of_nonneg_left hdiv (mul_nonneg (norm_nonneg R) hCol0)
      have heq : ‖R‖ * etaCol * (1 / (sigma / 2)) = 2 * ‖R‖ * etaCol / sigma := by ring
      rw [heq] at hm
      simp only [div_eq_mul_inv] at hm ⊢
      linarith

end Qatlib.Papers.QPCAAssume18.ClassicalPca
