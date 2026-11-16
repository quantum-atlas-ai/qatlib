/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PureStateMath.LinearChange.MatrixNorm
public import Qatlib.Foundations.PureStateMath.LinearChange.ProductBound

@[expose] public section


/-! # The actual Ryser estimator and its full spectral-norm bound

Aaronson--Arkhipov, arXiv:1011.3245v1, Lemma 64. The norm is the
unchanged source supremum over the complex squared-mass unit ball.
The finite product bound follows from actual Euclidean mass and AM-GM.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
namespace Qatlib.Papers.LinearOptics10.StockmeyerSrc.RyserBound
open Qatlib.Foundations.PureStateMath.LinearChange
open MatrixNorm

/-- The exact original signed product estimator on an actual complex input matrix. -/
def rysSum {n : ℕ} (V : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) : ℂ :=
  (∏ i, x i)*∏ i, ∑ j, V i j*x j

/-- Every genuine sign vector has squared Euclidean mass exactly its actual dimension. -/
theorem signMass {n : ℕ} (x : Fin n → ℂ) (hx : ∀ i, x i = 1 ∨ x i = -1) :
    ∑ i, Complex.normSq (x i) = (n : ℝ) := by
  have he (i : Fin n) : Complex.normSq (x i) = 1 := by
    rcases hx i with h | h <;> simp [h]
  simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- Actual unit-modulus signs give a product of norm exactly one, including the empty product. -/
theorem signProd {n : ℕ} (x : Fin n → ℂ) (hx : ∀ i, x i = 1 ∨ x i = -1) :
    ‖∏ i, x i‖ = 1 := by
  rw [norm_prod]
  have he (i : Fin n) : ‖x i‖ = 1 := by
    rcases hx i with h | h <;> simp [h]
  simp only [he, Finset.prod_const_one]

/-- The entire original Ryser-estimator spectral-norm target holds for every complex matrix and sign vector. -/
theorem estimatorBound (n : ℕ) (V : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ)
    (hx : ∀ i, x i = 1 ∨ x i = -1) : ‖rysSum V x‖ ≤ matOpNorm V^n := by
  have hK := normNonneg V
  have hb := actionBound V x
  rw [signMass x hx] at hb
  have hsY : 0 ≤ ∑ i, Complex.normSq ((V *ᵥ x) i) :=
    Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hsq : (Real.sqrt (∑ i, Complex.normSq ((V *ᵥ x) i)))^2 ≤
      (matOpNorm V*Real.sqrt (n : ℝ))^2 :=
    (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hK (Real.sqrt_nonneg _))).mpr hb
  rw [Real.sq_sqrt hsY, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)] at hsq
  have hsum : (∑ i, Complex.normSq ((V *ᵥ x) i)) ≤ (n : ℝ)*matOpNorm V^2 := by
    simpa only [mul_comm] using hsq
  have hp := ProductBound.complexProd (V *ᵥ x) (matOpNorm V) hK hsum
  simpa only [rysSum, norm_mul, signProd x hx, one_mul, Matrix.mulVec, dotProduct] using hp

end Qatlib.Papers.LinearOptics10.StockmeyerSrc.RyserBound
