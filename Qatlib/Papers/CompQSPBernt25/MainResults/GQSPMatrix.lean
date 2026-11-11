/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.LinearAlgebra.Matrix.Notation

set_option backward.isDefEq.respectTransparency false

/-! Source: Berntson and Sünderhauf, *Complementary polynomials in quantum signal
processing*, arXiv:2406.04246v2 (CMP 406, 161 (2025)), Proposition A.1.1, equations
(1.2), (A.1), (A.2), and (A.3).

Proposition A.1.1 computes the remaining entries of the matrix realized by the
generalized quantum signal processing (GQSP) sequence (1.2). The matrix has the
form (A.1), where the unit-modulus factor `u_d` of (A.2) is read off from the
determinant of both sides of (1.2) using (A.3) and the unitarity of the GQSP
word. The source states the identity on the unit circle; there `Q*(1/z)` is the
conjugate of `Q(z)`, which is the form used below.

The GQSP word is defined here from its two factors: the initial phase matrix of
(1.2) and the signal-and-phase layers. No phase-factor synthesis, gate
decomposition, or cost claim is made. -/

set_option autoImplicit false
noncomputable section
open Matrix

namespace Qatlib.Papers.CompQSPBernt25.MainResults

/-- For a unitary `2 × 2` complex matrix the second row is determined by the
first row and the determinant: `U₀₁` and `U₁₁` are the cofactors of the inverse. -/
lemma bottom_row_of_unitary (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : U * Uᴴ = 1) :
    U 1 0 = -(U.det) * star (U 0 1) ∧ U 1 1 = (U.det) * star (U 0 0) := by
  have hdet : U.det ≠ 0 := Matrix.det_ne_zero_of_right_inverse hU
  have hinv : U⁻¹ = Uᴴ := inv_eq_right_inv hU
  have hsmul : U⁻¹ = (U.det)⁻¹ • U.adjugate := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv]
  have h10 : star (U 0 1) = (U.det)⁻¹ * (-(U 1 0)) := by
    have h : Uᴴ 1 0 = ((U.det)⁻¹ • U.adjugate) 1 0 := by rw [← hinv, hsmul]
    simpa [Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_fin_two,
      Matrix.conjTranspose_apply] using h
  have h11 : star (U 0 0) = (U.det)⁻¹ * (U 1 1) := by
    have h : Uᴴ 0 0 = ((U.det)⁻¹ • U.adjugate) 0 0 := by rw [← hinv, hsmul]
    simpa [Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_fin_two,
      Matrix.conjTranspose_apply] using h
  constructor
  · rw [h10]
    field_simp
  · rw [h11]
    field_simp

/-- `e^{ix}` for real `x`, the unit-modulus phase appearing in (1.2). -/
def gqspPhase (x : ℝ) : ℂ := Complex.exp ((x : ℂ) * Complex.I)

/-- Phases of (1.2) add: `e^{i(a+b)} = e^{ia} e^{ib}`. -/
lemma gqspPhase_add (a b : ℝ) : gqspPhase (a + b) = gqspPhase a * gqspPhase b := by
  unfold gqspPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Every GQSP phase has unit modulus, so it is inverted by conjugation. -/
lemma gqspPhase_mul_star (x : ℝ) : gqspPhase x * star (gqspPhase x) = 1 := by
  have h : gqspPhase x * star (gqspPhase x) = ((‖gqspPhase x‖ : ℝ) : ℂ)^2 := by
    rw [Complex.star_def, Complex.mul_conj']
  rw [h]
  simp [gqspPhase, Complex.norm_exp_ofReal_mul_I]

/-- The conjugate of a real cosine is itself. -/
lemma starRingEnd_cos_real (x : ℝ) :
    (starRingEnd ℂ) (Complex.cos ((x : ℝ) : ℂ)) = Complex.cos ((x : ℝ) : ℂ) := by
  rw [starRingEnd_apply, Complex.star_def, ← Complex.cos_conj, Complex.conj_ofReal]

/-- The conjugate of a real sine is itself. -/
lemma starRingEnd_sin_real (x : ℝ) :
    (starRingEnd ℂ) (Complex.sin ((x : ℝ) : ℂ)) = Complex.sin ((x : ℝ) : ℂ) := by
  rw [starRingEnd_apply, Complex.star_def, ← Complex.sin_conj, Complex.conj_ofReal]

/-- The real symmetric orthogonal layer `[[cos θ, sin θ], [sin θ, -cos θ]]`. -/
def gqspReflect (theta : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos theta : ℂ), (Real.sin theta : ℂ);
     (Real.sin theta : ℂ), -((Real.cos theta : ℂ))]

/-- The initial phase matrix of the GQSP sequence (1.2). -/
def gqspInit (lam phi0 theta0 : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![gqspPhase (lam + phi0) * (Real.cos theta0 : ℂ), gqspPhase lam * (Real.sin theta0 : ℂ);
     gqspPhase phi0 * (Real.sin theta0 : ℂ), -((Real.cos theta0 : ℂ))]

/-- One signal-and-phase layer of the GQSP sequence (1.2). -/
def gqspLayer (phi theta : ℝ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![z, 0; 0, 1] *
    !![gqspPhase phi * (Real.cos theta : ℂ), (Real.sin theta : ℂ);
       gqspPhase phi * (Real.sin theta : ℂ), -((Real.cos theta : ℂ))]

/-- The initial matrix of (1.2) factors into diagonal phases around the real
reflection `gqspReflect`. -/
lemma gqspInit_decomp (lam phi0 theta0 : ℝ) :
    gqspInit lam phi0 theta0 =
      !![gqspPhase lam, 0; 0, 1] * gqspReflect theta0 * !![gqspPhase phi0, 0; 0, 1] := by
  have h : gqspPhase (lam + phi0) = gqspPhase lam * gqspPhase phi0 := gqspPhase_add lam phi0
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gqspInit, gqspReflect, Matrix.mul_apply, Fin.sum_univ_two, h] <;> ring_nf

/-- A signal-and-phase layer of (1.2) factors into diagonal phases around the
real reflection `gqspReflect`. -/
lemma gqspLayer_decomp (phi theta : ℝ) (z : ℂ) :
    gqspLayer phi theta z =
      !![z, 0; 0, 1] * gqspReflect theta * !![gqspPhase phi, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gqspLayer, gqspReflect, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf

/-- The real reflection `[[cos θ, sin θ], [sin θ, -cos θ]]` is unitary. -/
lemma gqspReflect_unitary (theta : ℝ) : gqspReflect theta * (gqspReflect theta)ᴴ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gqspReflect, Matrix.mul_apply, Fin.sum_univ_two,
      starRingEnd_cos_real, starRingEnd_sin_real] <;>
    ring_nf <;>
    simp [Complex.cos_sq_add_sin_sq, Complex.sin_sq_add_cos_sq]

/-- A unit-modulus complex number is inverted by conjugation. -/
lemma mul_starRingEnd_eq_one {a : ℂ} (ha : ‖a‖ = 1) : a * (starRingEnd ℂ) a = 1 := by
  rw [starRingEnd_apply, Complex.star_def, Complex.mul_conj', ha]
  norm_num

/-- A diagonal matrix with unit-modulus entries is unitary. -/
lemma diagonal_unitary (a b : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    !![a, 0; 0, b] * (!![a, 0; 0, b] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two,
      mul_starRingEnd_eq_one ha, mul_starRingEnd_eq_one hb]

/-- A product of unitary matrices is unitary. -/
lemma unitary_mul {A B : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A * Aᴴ = 1) (hB : B * Bᴴ = 1) : (A * B) * (A * B)ᴴ = 1 := by
  have hstar : (A * B)ᴴ = Bᴴ * Aᴴ := Matrix.conjTranspose_mul A B
  rw [hstar]
  have heq : (A * B) * (Bᴴ * Aᴴ) = A * (B * Bᴴ) * Aᴴ := by noncomm_ring
  rw [heq, hB, mul_one, hA]

/-- Every GQSP phase has unit modulus. -/
lemma gqspPhase_norm (x : ℝ) : ‖gqspPhase x‖ = 1 := by
  simp [gqspPhase, Complex.norm_exp_ofReal_mul_I]

/-- The initial phase matrix of (1.2) is unitary. -/
lemma gqspInit_unitary (lam phi0 theta0 : ℝ) :
    gqspInit lam phi0 theta0 * (gqspInit lam phi0 theta0)ᴴ = 1 := by
  rw [gqspInit_decomp]
  exact unitary_mul
    (unitary_mul (diagonal_unitary _ _ (gqspPhase_norm lam) (by simp))
      (gqspReflect_unitary theta0))
    (diagonal_unitary _ _ (gqspPhase_norm phi0) (by simp))

/-- A signal-and-phase layer of (1.2) is unitary on the unit circle. -/
lemma gqspLayer_unitary (phi theta : ℝ) (z : ℂ) (hz : ‖z‖ = 1) :
    gqspLayer phi theta z * (gqspLayer phi theta z)ᴴ = 1 := by
  rw [gqspLayer_decomp]
  exact unitary_mul
    (unitary_mul (diagonal_unitary _ _ hz (by simp)) (gqspReflect_unitary theta))
    (diagonal_unitary _ _ (gqspPhase_norm phi) (by simp))

/-- The `d`-fold product of signal-and-phase layers in (1.2). -/
def gqspLayers (phi theta : ℕ → ℝ) : ℕ → ℂ → Matrix (Fin 2) (Fin 2) ℂ
  | 0, _ => 1
  | d + 1, z => gqspLayers phi theta d z * gqspLayer (phi (d + 1)) (theta (d + 1)) z

/-- The matrix realized by the GQSP sequence (1.2). -/
def gqspMatrix (lam : ℝ) (phi theta : ℕ → ℝ) (d : ℕ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  gqspInit lam (phi 0) (theta 0) * gqspLayers phi theta d z

/-- The unit-modulus factor `u_d(z)` of (A.2). -/
def gqspPhaseFactor (lam : ℝ) (phi : ℕ → ℝ) (d : ℕ) (z : ℂ) : ℂ :=
  (-1) ^ d * z ^ d * gqspPhase (lam + ∑ j ∈ Finset.range (d + 1), phi j)

/-- The `d`-fold layer product of (1.2) is unitary on the unit circle. -/
lemma gqspLayers_unitary (phi theta : ℕ → ℝ) (d : ℕ) (z : ℂ) (hz : ‖z‖ = 1) :
    gqspLayers phi theta d z * (gqspLayers phi theta d z)ᴴ = 1 := by
  induction d with
  | zero => simp [gqspLayers]
  | succ d ih =>
    rw [gqspLayers]
    exact unitary_mul ih (gqspLayer_unitary _ _ z hz)

/-- The GQSP matrix of (1.2) is unitary on the unit circle. -/
lemma gqspMatrix_unitary (lam : ℝ) (phi theta : ℕ → ℝ) (d : ℕ) (z : ℂ)
    (hz : ‖z‖ = 1) :
    gqspMatrix lam phi theta d z * (gqspMatrix lam phi theta d z)ᴴ = 1 := by
  simpa [gqspMatrix] using unitary_mul (gqspInit_unitary lam (phi 0) (theta 0))
    (gqspLayers_unitary phi theta d z hz)

/-- The determinant of a diagonal `2 × 2` matrix is the product of its entries. -/
lemma det_diag (a b : ℂ) : (!![a, 0; 0, b] : Matrix (Fin 2) (Fin 2) ℂ).det = a * b := by
  rw [Matrix.det_fin_two]
  simp

/-- The reflection `gqspReflect θ` has determinant `-1`, matching the third
determinant in (A.3). -/
lemma det_gqspReflect (theta : ℝ) : (gqspReflect theta).det = -1 := by
  rw [Matrix.det_fin_two]
  simp [gqspReflect]
  rw [← Complex.cos_sq_add_sin_sq ((theta : ℝ) : ℂ)]
  ring

/-- The determinant of the initial matrix of (1.2) is `-e^{i(λ+φ₀)}`, matching
the first determinant in (A.3). -/
lemma det_gqspInit (lam phi0 theta0 : ℝ) :
    (gqspInit lam phi0 theta0).det = - gqspPhase (lam + phi0) := by
  rw [gqspInit_decomp, Matrix.det_mul, Matrix.det_mul, det_diag, det_diag,
    det_gqspReflect]
  ring_nf
  rw [← gqspPhase_add]

/-- The determinant of a layer of (1.2) is `-z e^{iφ}`, matching the second and
third determinants in (A.3). -/
lemma det_gqspLayer (phi theta : ℝ) (z : ℂ) :
    (gqspLayer phi theta z).det = - (z * gqspPhase phi) := by
  rw [gqspLayer_decomp, Matrix.det_mul, Matrix.det_mul, det_diag, det_diag,
    det_gqspReflect]
  simp only [mul_one]
  ring

/-- The determinant of the `d`-fold layer product collects the `d` factors `z`
and the layer phases. -/
lemma det_gqspLayers (phi theta : ℕ → ℝ) (d : ℕ) (z : ℂ) :
    (gqspLayers phi theta d z).det =
      (-1) ^ d * z ^ d * gqspPhase (∑ j ∈ Finset.range d, phi (j + 1)) := by
  induction d with
  | zero => simp [gqspLayers, gqspPhase]
  | succ d ih =>
    rw [gqspLayers, Matrix.det_mul, ih, det_gqspLayer, Finset.sum_range_succ]
    calc
      (-1) ^ d * z ^ d * gqspPhase (∑ j ∈ Finset.range d, phi (j + 1)) *
          -(z * gqspPhase (phi (d + 1)))
          = -(((-1) ^ d * z ^ d) * (z * (gqspPhase (∑ j ∈ Finset.range d, phi (j + 1)) *
              gqspPhase (phi (d + 1))))) := by ring
      _ = -(((-1) ^ d * z ^ d) *
            (z * gqspPhase (∑ j ∈ Finset.range d, phi (j + 1) + phi (d + 1)))) := by
            rw [← gqspPhase_add]
      _ = (-1) ^ (d + 1) * z ^ (d + 1) *
            gqspPhase (∑ j ∈ Finset.range d, phi (j + 1) + phi (d + 1)) := by
            rw [pow_succ]
            ring

/-- The determinant of the GQSP matrix is `-u_d(z)`, i.e. minus the factor of
(A.2); this is the computation (A.3) of the source. -/
lemma det_gqspMatrix (lam : ℝ) (phi theta : ℕ → ℝ) (d : ℕ) (z : ℂ) :
    (gqspMatrix lam phi theta d z).det = - gqspPhaseFactor lam phi d z := by
  rw [gqspMatrix, Matrix.det_mul, det_gqspInit, det_gqspLayers, gqspPhaseFactor,
    Finset.sum_range_succ']
  set S : ℝ := ∑ k ∈ Finset.range d, phi (k + 1)
  calc
    -gqspPhase (lam + phi 0) * ((-1) ^ d * z ^ d * gqspPhase S)
        = -(((-1) ^ d * z ^ d) * (gqspPhase (lam + phi 0) * gqspPhase S)) := by ring
    _ = -(((-1) ^ d * z ^ d) * gqspPhase ((lam + phi 0) + S)) := by
          rw [← gqspPhase_add]
    _ = -((-1) ^ d * z ^ d * gqspPhase (lam + (S + phi 0))) := by
          rw [show (lam + phi 0) + S = lam + (S + phi 0) by ring]

/-- Proposition A.1.1: the second row of the GQSP matrix is determined by the
first row and the unit-modulus factor `u_d(z)`, so the matrix realized by (1.2)
has the form (A.1) with `u_d` as in (A.2). On the unit circle the source's
`Q*(1/z)` is `conj (Q z)`, which is the form used here. -/
theorem gqsp_second_row (lam : ℝ) (phi theta : ℕ → ℝ) (d : ℕ) (z : ℂ) (hz : ‖z‖ = 1) :
    gqspMatrix lam phi theta d z 1 0 =
        gqspPhaseFactor lam phi d z * star (gqspMatrix lam phi theta d z 0 1) ∧
      gqspMatrix lam phi theta d z 1 1 =
        - (gqspPhaseFactor lam phi d z * star (gqspMatrix lam phi theta d z 0 0)) := by
  have h := bottom_row_of_unitary _ (gqspMatrix_unitary lam phi theta d z hz)
  have hdet := det_gqspMatrix lam phi theta d z
  constructor
  · rw [h.1, hdet]
    ring
  · rw [h.2, hdet]
    ring

/-- Proposition A.1.1 in matrix form: the GQSP matrix of (1.2) is (A.1) with
`u_d(z)` given by (A.2). -/
theorem gqsp_matrix_form (lam : ℝ) (phi theta : ℕ → ℝ) (d : ℕ) (z : ℂ)
    (hz : ‖z‖ = 1) :
    gqspMatrix lam phi theta d z =
      !![gqspMatrix lam phi theta d z 0 0, gqspMatrix lam phi theta d z 0 1;
         gqspPhaseFactor lam phi d z * star (gqspMatrix lam phi theta d z 0 1),
         - (gqspPhaseFactor lam phi d z * star (gqspMatrix lam phi theta d z 0 0))] := by
  obtain ⟨h10, h11⟩ := gqsp_second_row lam phi theta d z hz
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h10, h11]

end Qatlib.Papers.CompQSPBernt25.MainResults
