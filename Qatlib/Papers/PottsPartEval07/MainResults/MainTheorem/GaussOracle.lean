/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module


public import Qatlib.Papers.GaussSumEst02.CharacterState
public import Qatlib.Foundations.PureStateMath.Qubit

@[expose] public section

/-!
# The actual unitary Gauss-phase query

The query is the finite additive Fourier transform followed by the character
square correction. The correction at zero is one, so the operator is unitary
on the entire field register. The prepared character state vanishes at zero,
and its eigenvalue is the actual normalized Gauss sum.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem

open scoped BigOperators ComplexConjugate
open Qatlib.Papers.GaussSumEst02.MainResults.Source
open Qatlib.Foundations.PureStateMath

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The normalized additive Fourier transform at the supplied nonzero frequency. -/
def gaussFourier (additive : AddChar F) (frequency : F) : Matrix F F ℂ :=
  fun y x => (Real.sqrt (Fintype.card F : ℝ) : ℂ)⁻¹ * additive.toFun (frequency * y * x)

/-- The actual Fourier transform is unitary by finite-field additive orthogonality. -/
theorem gaussFourier_unitary (additive : AddChar F) (frequency : F) (hf : frequency ≠ 0) :
    gaussFourier additive frequency ∈ Matrix.unitaryGroup F ℂ := by
  have hQ : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hsq : (Real.sqrt (Fintype.card F : ℝ) : ℂ) ^ 2 = (Fintype.card F : ℂ) := by
    exact_mod_cast Real.sq_sqrt hQ.le
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext x y
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, RCLike.star_def]
  have hterm : ∀ z : F,
      conj (gaussFourier additive frequency z x) * gaussFourier additive frequency z y =
      ((Real.sqrt (Fintype.card F : ℝ) : ℂ)⁻¹) ^ 2 *
        additive.toFun (frequency * (y - x) * z) := by
    intro z
    simp only [gaussFourier, map_mul, map_inv₀, Complex.conj_ofReal, additive.conj_apply]
    rw [sq]
    calc _ = ((Real.sqrt (Fintype.card F : ℝ) : ℂ)⁻¹ *
        (Real.sqrt (Fintype.card F : ℝ) : ℂ)⁻¹) *
        (additive.toFun (-(frequency * z * x)) * additive.toFun (frequency * z * y)) := by ring
      _ = _ := by rw [← additive.map_add']; congr 2; ring
  simp only [hterm]
  rw [← Finset.mul_sum]
  by_cases hxy : x = y
  · subst y
    simp only [sub_self, mul_zero, zero_mul, additive.map_zero', Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one, ite_true]
    rw [inv_pow, hsq]
    exact inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero : (Fintype.card F : ℂ) ≠ 0)
  · rw [additive.sum_mul_eq_zero (mul_ne_zero hf (sub_ne_zero.mpr (Ne.symm hxy))),
      mul_zero, ite_eq_right hxy]

/-- The character-square correction, extended unitarily at zero. -/
def gaussCorrection (character : MultChar F) : Matrix F F ℂ :=
  Matrix.diagonal fun y => if y = 0 then 1 else character.toFun y ^ 2

/-- Every correction entry has norm one, including the zero entry. -/
theorem gaussCorrection_unitary (character : MultChar F) :
    gaussCorrection character ∈ Matrix.unitaryGroup F ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext x y
  simp only [gaussCorrection, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  by_cases hxy : x = y
  · subst y
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply, ite_true]
    by_cases hx : x = 0
    · simp [hx]
    · rw [ite_eq_right hx]
      have hn : ‖character.toFun x ^ 2‖ = 1 := by rw [norm_pow, character.norm_eq_one x hx]; norm_num
      have hh := Complex.mul_conj' (character.toFun x ^ 2)
      rw [hn, Complex.ofReal_one, one_pow] at hh
      simp only [Pi.star_apply, ite_eq_right hx]
      simpa [mul_comm] using hh
  · simp [hxy]

/-- The actual Gauss-phase oracle is the product of the correction and Fourier transform. -/
def gaussOracle (character : MultChar F) (additive : AddChar F) (frequency : F) : Matrix F F ℂ :=
  gaussCorrection character * gaussFourier additive frequency

/-- Both factors of the actual Gauss oracle are unitary. -/
theorem gaussOracle_unitary (character : MultChar F) (additive : AddChar F)
    (frequency : F) (hf : frequency ≠ 0) :
    gaussOracle character additive frequency ∈ Matrix.unitaryGroup F ℂ :=
  Submonoid.mul_mem _ (gaussCorrection_unitary character) (gaussFourier_unitary additive frequency hf)

omit [DecidableEq F] in
/-- The Fourier matrix acts on the actual prepared character state by its defining finite sum. -/
theorem gaussFourier_character (character : MultChar F) (additive : AddChar F) (frequency : F) :
    ApplyGate (gaussFourier additive frequency) (chiState character) =
      fourierChi character additive frequency := by
  ext y
  simp only [ApplyGate, Matrix.mulVec, dotProduct, gaussFourier, fourierChi]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

omit [DecidableEq F] in
/-- The actual query's eigenstate has unit norm. -/
theorem gauss_state_normalized (character : MultChar F) : Normalized (chiState character) :=
  Qatlib.Papers.GaussSumEst02.CharacterState.chiState_normSq character

/-- The actual unitary query has the normalized Gauss sum as its character-state eigenvalue. -/
theorem gaussOracle_eigen (character : MultChar F) (hn : character.IsNontrivial)
    (additive : AddChar F) (frequency : F) (hf : frequency ≠ 0) :
    ApplyGate (gaussOracle character additive frequency) (chiState character) =
      (gaussSum character.toFun additive frequency /
        (Real.sqrt (Fintype.card F : ℝ) : ℂ)) • chiState character := by
  change (gaussCorrection character * gaussFourier additive frequency).mulVec (chiState character) = _
  rw [← Matrix.mulVec_mulVec]
  change ApplyGate (gaussCorrection character)
    (ApplyGate (gaussFourier additive frequency) (chiState character)) = _
  rw [gaussFourier_character]
  have he := algorithm1_phase_change character additive hn hf
  ext y
  rw [ApplyGate, gaussCorrection, Matrix.mulVec_diagonal]
  by_cases hy : y = 0
  · subst y
    have hz : fourierChi character additive frequency 0 = 0 := by
      unfold fourierChi chiState
      simp only [mul_zero, zero_mul, additive.map_zero', mul_one]
      rw [← Finset.sum_div, multChar_sum_eq_zero character hn]
      simp
    simp [hz, chiState, character.map_zero']
  · rw [ite_eq_right hy]
    exact congrFun he y

/-- The actual Gauss sum supplies the unitary oracle's phase, without an assumed eigenvalue. -/
theorem gauss_phase_eigen (character : MultChar F) (hn : character.IsNontrivial)
    (additive : AddChar F) (frequency : F) (hf : frequency ≠ 0) :
    ∃ phase : ℝ,
      gaussSum character.toFun additive frequency =
        (Real.sqrt (Fintype.card F : ℝ) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * phase) ∧
      ApplyGate (gaussOracle character additive frequency) (chiState character) =
        Complex.exp (2 * Real.pi * Complex.I * phase) • chiState character := by
  obtain ⟨angle, hangle⟩ := gaussSum_polar character additive hn hf
  have harg : 2 * (Real.pi : ℂ) * Complex.I * ((angle / (2 * Real.pi) : ℝ) : ℂ) =
      (angle : ℂ) * Complex.I := by
    push_cast
    field_simp
  refine ⟨angle / (2 * Real.pi), ?_, ?_⟩
  · simpa only [harg] using hangle
  · rw [gaussOracle_eigen character hn additive frequency hf, hangle, harg]
    have hroot : (Real.sqrt (Fintype.card F : ℝ) : ℂ) ≠ 0 := by
      have hQ : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
      exact_mod_cast (Real.sqrt_pos.mpr hQ).ne'
    congr 1
    field_simp

end Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem
