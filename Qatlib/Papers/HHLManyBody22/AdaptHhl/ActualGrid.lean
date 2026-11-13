/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HHLManyBody22.AdaptHhl.AdaptScaling
import Qatlib.Concepts.HhlAlgorithms.GridExactHHL.GridHHLSolutionOutput
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# AdaptHHL scaling on an exact spectral grid

`adaptGridMatrix` rescales the represented grid HHL matrix by `2^nr*d`. Assuming the grid matrix
is invertible, the module identifies its pseudoinverse with the inverse and relates the success
amplitude to the inverse of this rescaled matrix.

For a unitary eigenbasis and positive `d`, `adapt_actual_probability_output` describes both the
success probability and the conditional output. The remaining results recover the inverse
solution norm and guarantee a normalized successful output for normalized input. See
[BaskaranEtAl2023].

## Main statements

* `adapt_actual_probability_output`: For a unitary eigenbasis, positive `d`, and an invertible
  grid matrix, success probability is `d^2` times the total Born mass of the rescaled inverse
  solution, and the output is its `ConditionalState`.
* `adapt_actual_inverse_norm`: Under the stated unitarity, invertibility, and positive scaling
  hypotheses, the rescaled inverse solution norm is the square root of the grid HHL success
  probability divided by `d`.
* `adapt_actual_success_exists`: With a unitary eigenbasis, invertible grid matrix, and
  normalized input, grid HHL success probability is positive and at least `(hhlCoefficient
  nr)^2`, and the successful output exists and is normalized.

## References

* [Baskaran et al., 2023][BaskaranEtAl2023]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators Classical
namespace Qatlib.Papers.HHLManyBody22.AdaptHhl
open Matrix
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.HhlAlgorithms.GridExactHHL

/-- The grid HHL matrix rescaled by the complex scalar `2^nr*d`. -/
def adaptGridMatrix {D : ℕ} (nr : ℕ) (d : ℝ) (label : Fin D→Fin (2^nr))
    (V : Matrix (Fin D) (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  (((2:ℝ)^nr*d:ℝ):ℂ) • gridHHLMatrix label V

/-- For a matrix with invertible determinant, `matrixPseudoinverse A` equals `A⁻¹`. -/
theorem adapt_pseudoinverse_eq_inverse {D : ℕ} (A : Matrix (Fin D) (Fin D) ℂ)
    (hA : IsUnit A.det) : matrixPseudoinverse A=A⁻¹ := by
  symm
  apply matrixPseudoinverse_unique
  · rw [Matrix.mul_nonsing_inv _ hA,Matrix.one_mul]
  · rw [Matrix.nonsing_inv_mul _ hA,Matrix.one_mul]
  · rw [Matrix.mul_nonsing_inv _ hA,Matrix.conjTranspose_one]
  · rw [Matrix.nonsing_inv_mul _ hA,Matrix.conjTranspose_one]

/-- For positive `d` and an invertible grid matrix, the inverse of `adaptGridMatrix` is the grid
matrix inverse scaled by `(2^nr*d)⁻¹`. -/
theorem adaptGridMatrix_inverse {D : ℕ} (nr : ℕ) (d : ℝ) (hd : 0<d)
    (label : Fin D→Fin (2^nr)) (V : Matrix (Fin D) (Fin D) ℂ)
    (hG : IsUnit (gridHHLMatrix label V).det) :
    (adaptGridMatrix nr d label V)⁻¹=
      (((2:ℝ)^nr*d:ℝ):ℂ)⁻¹ • (gridHHLMatrix label V)⁻¹ := by
  have hk : (((2:ℝ)^nr*d:ℝ):ℂ)≠0 := by
    exact_mod_cast (ne_of_gt (mul_pos (by positivity) hd))
  exact Matrix.inv_smul' _ (Units.mk0 _ hk) hG

/-- For positive `d` and an invertible grid matrix, the grid HHL success vector with coefficient
`hhlCoefficient nr` equals `d` times the solution for `adaptGridMatrix`. See
[BaskaranEtAl2023]. -/
theorem adapt_actual_success_amplitude {D : ℕ} (nr : ℕ) (d : ℝ) (hd : 0<d)
    (label : Fin D→Fin (2^nr)) (V : Matrix (Fin D) (Fin D) ℂ)
    (hG : IsUnit (gridHHLMatrix label V).det) (b : Fin D→ℂ) :
    ((hhlCoefficient nr:ℝ):ℂ) • (matrixPseudoinverse (gridHHLMatrix label V)*ᵥb)=
      (d:ℂ) • ((adaptGridMatrix nr d label V)⁻¹*ᵥb) := by
  rw [adapt_pseudoinverse_eq_inverse _ hG,adaptGridMatrix_inverse nr d hd label V hG,
    Matrix.smul_mulVec,smul_smul]
  congr 1
  simp only [hhlCoefficient,Complex.ofReal_inv,Complex.ofReal_mul,Complex.ofReal_pow,
    Complex.ofReal_ofNat]
  have hd0 : (d:ℂ)≠0 := by exact_mod_cast hd.ne'
  have htwo : (2:ℂ)^nr≠0 := pow_ne_zero _ (by norm_num)
  field_simp

/-- For a unitary eigenbasis, positive `d`, and an invertible grid matrix, success probability
is `d^2` times the total Born mass of the rescaled inverse solution, and the output is its
`ConditionalState`. See [BaskaranEtAl2023]. -/
theorem adapt_actual_probability_output {D : ℕ} (nr : ℕ) (d : ℝ) (hd : 0<d)
    (label : Fin D→Fin (2^nr)) (V : Matrix (Fin D) (Fin D) ℂ)
    (hV : V∈Matrix.unitaryGroup (Fin D) ℂ) (hG : IsUnit (gridHHLMatrix label V).det)
    (b : Fin D→ℂ) :
    gridHHLProbability label V (hhlCoefficient nr) b=
      d^2*MeasureProb ((adaptGridMatrix nr d label V)⁻¹*ᵥb) Finset.univ ∧
    gridHHLOutput label V (hhlCoefficient nr) b=
      ConditionalState ((adaptGridMatrix nr d label V)⁻¹*ᵥb) := by
  have hc : 0<hhlCoefficient nr := by unfold hhlCoefficient; positivity
  have hc1 : hhlCoefficient nr≤1/((2^nr:ℕ):ℝ) := by simp [hhlCoefficient]
  obtain ⟨hp,ho,_⟩ := grid_hhl_actual_probability_and_output label V (hhlCoefficient nr) b
    (by positivity) hV hc.le hc1
  have hs := adapt_actual_success_amplitude nr d hd label V hG b
  refine ⟨?_,?_⟩
  · rw [← measureProb_smul_real] at hp
    rw [hs,measureProb_smul_real] at hp
    exact hp
  · rw [ho hc,← conditionalState_smul hc,hs,conditionalState_smul hd]

/-- Under the stated unitarity, invertibility, and positive scaling hypotheses, the rescaled
inverse solution norm is the square root of the grid HHL success probability divided by `d`.
See [BaskaranEtAl2023]. -/
theorem adapt_actual_inverse_norm {D : ℕ} (nr : ℕ) (d : ℝ) (hd : 0<d)
    (label : Fin D→Fin (2^nr)) (V : Matrix (Fin D) (Fin D) ℂ)
    (hV : V∈Matrix.unitaryGroup (Fin D) ℂ) (hG : IsUnit (gridHHLMatrix label V).det)
    (b : Fin D→ℂ) :
    Real.sqrt (MeasureProb ((adaptGridMatrix nr d label V)⁻¹*ᵥb) Finset.univ)=
      Real.sqrt (gridHHLProbability label V (hhlCoefficient nr) b)/d := by
  rw [(adapt_actual_probability_output nr d hd label V hV hG b).1,
    Real.sqrt_mul (sq_nonneg d),Real.sqrt_sq hd.le]
  field_simp

/-- With a unitary eigenbasis, invertible grid matrix, and normalized input, grid HHL success
probability is positive and at least `(hhlCoefficient nr)^2`, and the successful output
exists and is normalized. See [BaskaranEtAl2023]. -/
theorem adapt_actual_success_exists {D : ℕ} (nr : ℕ)
    (label : Fin D→Fin (2^nr)) (V : Matrix (Fin D) (Fin D) ℂ)
    (hV : V∈Matrix.unitaryGroup (Fin D) ℂ) (hG : IsUnit (gridHHLMatrix label V).det)
    (b : Fin D→ℂ) (hb : Normalized b) :
    (hhlCoefficient nr)^2≤gridHHLProbability label V (hhlCoefficient nr) b ∧
    0<gridHHLProbability label V (hhlCoefficient nr) b ∧
    ∃φ,gridHHLOutput label V (hhlCoefficient nr) b=some φ ∧ Normalized φ := by
  apply grid_hhl_consistent_input_derived_success label V (hhlCoefficient nr) b
    (by positivity) hV (by unfold hhlCoefficient; positivity) (by simp [hhlCoefficient]) hb
  exact ⟨(gridHHLMatrix label V)⁻¹*ᵥb,by
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hG,Matrix.one_mulVec]⟩

end Qatlib.Papers.HHLManyBody22.AdaptHhl
