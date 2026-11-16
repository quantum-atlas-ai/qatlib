/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AncilFreeClfT14.MainResults.LegacyChoice
public import Qatlib.Papers.AncilFreeClfT14.MainResults.LegacyAlgebra
public import Mathlib.Analysis.Complex.Trigonometric

@[expose] public section


/-! # A concrete noncanonical phase-tag counterexample
The dyadic unitary and exact target satisfy every original premise. The
archived conclusion confuses an integer tag with its representative modulo eight.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AncilFreeClfT14.MainResults.Legacy

open Qatlib.Papers.AncilFreeClfT14.MainResults

/-- The algebraic omega of CoreModel is the actual pi/4 complex phase. -/
theorem omegaExp : omega = Complex.exp (Complex.I * ((Real.pi / 4 : ℝ) : ℂ)) := by
  rw [omega_eq_sqrt2_half]
  apply Complex.ext <;>
    simp [Complex.exp_re, Complex.exp_im, Complex.mul_re, Complex.mul_im,
      Real.cos_pi_div_four, Real.sin_pi_div_four]

/-- The phase is nonzero, as required for all inverse computations. -/
theorem omegaNe : omega ≠ 0 := by
  rw [omegaExp]
  exact Complex.exp_ne_zero _

/-- Complex conjugation of this phase is its inverse. -/
theorem omegaConj : (starRingEnd ℂ) omega = omega⁻¹ := by
  rw [omegaExp, ← Complex.exp_conj]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul]
  exact Complex.exp_neg _

/-- The inverse phase has an actual integer cyclotomic coordinate vector. -/
theorem omegaInvCoord : omega⁻¹ = -omega ^ (3 : ℕ) := by
  have hfour : omega ^ (4 : ℕ) = -1 := by
    calc
      omega ^ (4 : ℕ) = (omega ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
      _ = -1 := by rw [omega_sq]; norm_num [Complex.I_sq]
  apply mul_left_cancel₀ omegaNe
  rw [mul_inv_cancel₀ omegaNe]
  calc
    (1 : ℂ) = -omega ^ (4 : ℕ) := by rw [hfour]; norm_num
    _ = omega * (-omega ^ (3 : ℕ)) := by ring

/-- Integer phase tag seven and inverse omega give exactly the same factor. -/
theorem omegaSeven : omega ^ (7 : ℤ) = omega⁻¹ := by
  have hn : omega ^ (7 : ℕ) = omega⁻¹ := by
    calc
      omega ^ (7 : ℕ) = omega ^ (7 : ℕ) * (omega * omega⁻¹) := by
        rw [mul_inv_cancel₀ omegaNe, mul_one]
      _ = omega ^ (8 : ℕ) * omega⁻¹ := by rw [pow_succ]; ring
      _ = omega⁻¹ := by rw [omegaEight, one_mul]
  simpa only [zpow_ofNat] using hn

/-- The inverse phase satisfies the actual Domega membership predicate. -/
theorem invDyadic : omega⁻¹ ∈ Domega := by
  refine ⟨⟨-1, 0, 0, 0⟩, 0, ?_⟩
  simp [Zomega.toComplex, omegaInvCoord]

/-- The seven-tagged record evaluates to diag(inverse omega,one). -/
theorem tagSevenMat :
    (UTGeneralForm.mk omega⁻¹ 0 7).mat =
      (!![omega⁻¹, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hn : omega ^ (7 : ℕ) = omega⁻¹ := by
    simpa only [zpow_ofNat] using omegaSeven
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [UTGeneralForm.mat, hn, map_inv₀, omegaConj, omegaNe]

/-- That actual diagonal matrix is unitary. -/
theorem tagSevenUnit : IsUnitaryUTG (UTGeneralForm.mk omega⁻¹ 0 7) := by
  unfold IsUnitaryUTG
  rw [tagSevenMat]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      map_inv₀, omegaConj, omegaNe]

/-- Multiplying this matrix by the prescribed pi/8 phase gives the exact Rz(pi/4). -/
theorem phaseMatches :
    Complex.exp (Complex.I * ((Real.pi / 8 : ℝ) : ℂ)) •
        (UTGeneralForm.mk omega⁻¹ 0 7).mat = Rz (Real.pi / 4) := by
  have hhalf :
      Complex.exp (Complex.I * ((Real.pi / 8 : ℝ) : ℂ)) * omega⁻¹ =
        Complex.exp (-(Complex.I * ((Real.pi / 8 : ℝ) : ℂ))) := by
    rw [omegaExp, ← Complex.exp_neg, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hl :
      Complex.exp (-((Real.pi / 4 : ℝ) : ℂ) * Complex.I / 2) =
        Complex.exp (-(Complex.I * ((Real.pi / 8 : ℝ) : ℂ))) := by
    congr 1
    push_cast
    ring
  have hr :
      Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I / 2) =
        Complex.exp (Complex.I * ((Real.pi / 8 : ℝ) : ℂ)) := by
    congr 1
    push_cast
    ring
  rw [tagSevenMat]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rz, Matrix.smul_apply, smul_eq_mul]
  · convert hhalf.trans hl.symm using 1 <;> push_cast <;> congr 1; ring
  · convert hr.symm using 1 <;> push_cast <;> congr 1

/-- Every original Lemma9.6 premise holds at theta=pi/4,epsilon=zero and tag seven. -/
theorem tagSevenFits :
    (UTGeneralForm.mk omega⁻¹ 0 7).u ∈ Domega ∧
    (UTGeneralForm.mk omega⁻¹ 0 7).t ∈ Domega ∧
    IsUnitaryUTG (UTGeneralForm.mk omega⁻¹ 0 7) ∧
    opNorm (Rz (Real.pi / 4) -
      Complex.exp (Complex.I * ((Real.pi / 8 : ℝ) : ℂ)) •
        (UTGeneralForm.mk omega⁻¹ 0 7).mat) ≤ 0 ∧
    (0 : ℝ) < threshold7 := by
  refine ⟨invDyadic, zeroDyadic, tagSevenUnit, ?_, thresholdPos⟩
  simpa only [phaseMatches, sub_self, opNormZero] using (le_refl (0 : ℝ))

/-- The complete literal Lemma9.6 is refuted by a noncanonical but admissible phase tag. -/
theorem legacy96False : ¬
    (∀ (θ ε : ℝ), ε < threshold7 → ∀ U : UTGeneralForm,
      U.u ∈ Domega → U.t ∈ Domega → IsUnitaryUTG U →
      opNorm (Rz θ -
        Complex.exp (Complex.I * ((Real.pi / 8 : ℝ) : ℂ)) • U.mat) ≤ ε →
      U.l = -1) := by
  intro h
  have hf := h (Real.pi / 4) 0 tagSevenFits.2.2.2.2
    (UTGeneralForm.mk omega⁻¹ 0 7) tagSevenFits.1 tagSevenFits.2.1
    tagSevenFits.2.2.1 tagSevenFits.2.2.2.1
  norm_num at hf

end Qatlib.Papers.AncilFreeClfT14.MainResults.Legacy
