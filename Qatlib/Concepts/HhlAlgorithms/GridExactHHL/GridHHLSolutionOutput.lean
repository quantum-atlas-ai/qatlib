/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.GridExactHHL.ExactGridHHL
import Qatlib.Concepts.CoherentSim.CoherentOAA.Pseudoinverse
import Qatlib.Concepts.BlockEncoding.Basic

/-!
# Exact grid HHL output and pseudoinverse semantics

This module computes the complete output of `gridHHLCircuit`: inverse phase estimation resets
the phase register, and the successful flag branch is the scaled matrix pseudoinverse applied to
the input. It identifies the spectral reciprocal with `matrixPseudoinverse`, allowing zero
spectral labels. This is the exact-grid realization of the reciprocal-eigenvalue mechanism in
[HarrowHassidimLloyd2009].

The module derives the success mass and optional conditional state, proves positive success for
normalized consistent inputs with positive rotation scale, and handles zero spectrum and zero
rotation separately.

## Main statements

* `grid_hhl_spectral_reciprocal_eq_pseudoinverse`: identification of the spectral reciprocal.
* `grid_hhl_uncompute_and_postselected_pseudoinverse`: the successful amplitudes and reset phase
  register.
* `grid_hhl_actual_probability_and_output`: the success mass and conditional output.
* `grid_hhl_consistent_input_derived_success`: a positive success bound for consistent
  normalized inputs.

## References

* [Harrow, Hassidim, and Lloyd, 2009][HarrowHassidimLloyd2009]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.BornMetrics.EventProbability

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.BlockEncoding

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace Qatlib.Concepts.HhlAlgorithms.GridExactHHL

open Matrix
open scoped Classical
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

/-- The complex grid eigenvalue `(label i).val / M`. -/
noncomputable def gridHHLScale {D : ℕ} (M : ℕ) (label : Fin D → Fin M) (i : Fin D) : ℂ :=
  ((label i).val : ℂ) / (M : ℂ)

/-- The reciprocal grid value `M / (label i).val` at nonzero labels, with value zero at label
zero. -/
noncomputable def gridHHLReciprocalScale {D : ℕ} (M : ℕ) (label : Fin D → Fin M) (i : Fin D) : ℂ :=
  if (label i).val = 0 then 0 else (M : ℂ) / ((label i).val : ℂ)

/-- The real indicator that the spectral label is nonzero. -/
noncomputable def gridHHLSupportR {D M : ℕ} (label : Fin D → Fin M) (i : Fin D) : ℝ :=
  if (label i).val = 0 then 0 else 1

/-- The complex coercion of the nonzero spectral-label indicator. -/
noncomputable def gridHHLSupport {D M : ℕ} (label : Fin D → Fin M) (i : Fin D) : ℂ :=
  (gridHHLSupportR label i : ℂ)

/-- The spectral reciprocal matrix obtained by conjugating the guarded reciprocal grid values by
`V` and `Vᴴ`. -/
noncomputable def gridHHLReciprocal {D M : ℕ} (label : Fin D → Fin M) (V : Operator D) :
    Operator D :=
  V * Matrix.diagonal (gridHHLReciprocalScale M label) * Vᴴ

/-- The matrix obtained by conjugating the diagonal indicator of nonzero spectral labels by `V`
and `Vᴴ`. -/
noncomputable def gridHHLRangeProjector {D M : ℕ} (label : Fin D → Fin M) (V : Operator D) :
    Operator D :=
  V * Matrix.diagonal (gridHHLSupport (M := M) label) * Vᴴ

/-- For positive grid size, a grid eigenvalue times its guarded reciprocal is its nonzero-label
indicator. -/
theorem gridHHLScale_mul_reciprocal {D M : ℕ} (hM : 0 < M) (label : Fin D → Fin M)
    (i : Fin D) :
    gridHHLScale M label i * gridHHLReciprocalScale M label i = gridHHLSupport (M := M) label i := by
  by_cases hj : (label i).val = 0
  · simp [gridHHLScale, gridHHLReciprocalScale, gridHHLSupport, gridHHLSupportR, hj]
  · have hj0 : (((label i).val : ℕ) : ℂ) ≠ 0 := by
      intro h0
      have h0' : ((label i).val : ℕ) = 0 := by exact_mod_cast congrArg Complex.re h0
      exact hj h0'
    have hM0 : (M : ℂ) ≠ 0 := by
      intro h0
      have h0' : (M : ℕ) = 0 := by exact_mod_cast congrArg Complex.re h0
      omega
    rw [gridHHLScale, gridHHLReciprocalScale, gridHHLSupport, gridHHLSupportR]
    simp only [hj, if_false, Complex.ofReal_one]
    field_simp

/-- Multiplication by the support indicator leaves the grid eigenvalue unchanged. -/
theorem gridHHLSupport_mul_scale {D M : ℕ} (label : Fin D → Fin M) (i : Fin D) :
    gridHHLSupport (M := M) label i * gridHHLScale M label i = gridHHLScale M label i := by
  by_cases hj : (label i).val = 0
  · simp [gridHHLScale, gridHHLSupport, gridHHLSupportR, hj]
  · simp [gridHHLScale, gridHHLSupport, gridHHLSupportR, hj]

/-- Multiplication by the support indicator leaves the guarded reciprocal grid value unchanged. -/
theorem gridHHLSupport_mul_reciprocal {D M : ℕ} (label : Fin D → Fin M) (i : Fin D) :
    gridHHLSupport (M := M) label i * gridHHLReciprocalScale M label i
      = gridHHLReciprocalScale M label i := by
  by_cases hj : (label i).val = 0
  · simp [gridHHLReciprocalScale, gridHHLSupport, gridHHLSupportR, hj]
  · simp [gridHHLReciprocalScale, gridHHLSupport, gridHHLSupportR, hj]

/-- For positive grid size and unitary `V`, the grid matrix times its spectral reciprocal is the
spectral range projector. -/
theorem gridHHLMatrix_mul_reciprocal {D M : ℕ} (hM : 0 < M) (label : Fin D → Fin M)
    (V : Operator D) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    gridHHLMatrix label V * gridHHLReciprocal label V = gridHHLRangeProjector label V := by
  have hVU : Vᴴ * V = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hV
    rwa [Matrix.star_eq_conjTranspose] at h
  have hcore : Matrix.diagonal (gridHHLScale M label)
      * Matrix.diagonal (gridHHLReciprocalScale M label)
      = Matrix.diagonal (gridHHLSupport (M := M) label) := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    simp only [Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      rw [gridHHLScale_mul_reciprocal hM label]
    · simp [hij]
  have hinner : Vᴴ * (V * (Matrix.diagonal (gridHHLReciprocalScale M label) * Vᴴ))
      = Matrix.diagonal (gridHHLReciprocalScale M label) * Vᴴ := by
    rw [← Matrix.mul_assoc, hVU, Matrix.one_mul]
  have hstep : Matrix.diagonal (gridHHLScale M label)
      * (Vᴴ * (V * (Matrix.diagonal (gridHHLReciprocalScale M label) * Vᴴ)))
      = Matrix.diagonal (gridHHLSupport (M := M) label) * Vᴴ := by
    rw [hinner, ← Matrix.mul_assoc, hcore]
  show (V * Matrix.diagonal (gridHHLScale M label) * Vᴴ)
      * (V * Matrix.diagonal (gridHHLReciprocalScale M label) * Vᴴ)
      = V * Matrix.diagonal (gridHHLSupport (M := M) label) * Vᴴ
  calc (V * Matrix.diagonal (gridHHLScale M label) * Vᴴ)
      * (V * Matrix.diagonal (gridHHLReciprocalScale M label) * Vᴴ)
      = V * (Matrix.diagonal (gridHHLScale M label)
        * (Vᴴ * (V * (Matrix.diagonal (gridHHLReciprocalScale M label) * Vᴴ)))) := by
        simp only [Matrix.mul_assoc]
    _ = V * (Matrix.diagonal (gridHHLSupport (M := M) label) * Vᴴ) := by rw [hstep]
    _ = V * Matrix.diagonal (gridHHLSupport (M := M) label) * Vᴴ := by
      rw [Matrix.mul_assoc]

/-- Sandwiching a real diagonal matrix between a complex matrix and its adjoint gives a
self-adjoint matrix. -/
theorem conj_diagonal_mul_adjoint {D : ℕ} (V : Matrix (Fin D) (Fin D) ℂ) (d : Fin D → ℝ) :
    (V * Matrix.diagonal (fun i => (d i : ℂ)) * Vᴴ)ᴴ
      = V * Matrix.diagonal (fun i => (d i : ℂ)) * Vᴴ := by
  have hD : (Matrix.diagonal (fun i => (d i : ℂ)))ᴴ = Matrix.diagonal (fun i => (d i : ℂ)) := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Ne.symm hij]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_mul, hD,
    Matrix.mul_assoc]

/-- The spectral range-projector matrix is self-adjoint for every `V`. -/
theorem gridHHLRangeProjector_adjoint {D M : ℕ} (label : Fin D → Fin M) (V : Operator D) :
    (gridHHLRangeProjector label V)ᴴ = gridHHLRangeProjector label V :=
  conj_diagonal_mul_adjoint V (gridHHLSupportR (M := M) label)

/-- The nonzero spectral-label indicator is idempotent. -/
theorem gridHHLSupport_sq {D M : ℕ} (label : Fin D → Fin M) (i : Fin D) :
    gridHHLSupport (M := M) label i * gridHHLSupport (M := M) label i
      = gridHHLSupport (M := M) label i := by
  by_cases hj : (label i).val = 0
  · simp [gridHHLSupport, gridHHLSupportR, hj]
  · simp [gridHHLSupport, gridHHLSupportR, hj]

/-- For positive grid size, the guarded reciprocal grid value times its grid eigenvalue is the
support indicator. -/
theorem gridHHLReciprocalScale_mul_scale {D M : ℕ} (hM : 0 < M) (label : Fin D → Fin M)
    (i : Fin D) :
    gridHHLReciprocalScale M label i * gridHHLScale M label i = gridHHLSupport (M := M) label i := by
  simpa [mul_comm] using (gridHHLScale_mul_reciprocal hM label i)

/-- If `Vᴴ * V = 1`, left multiplication by `Vᴴ` cancels the leading `V` in `V * X`. -/
private theorem conjV_mul {D : ℕ} (V X : Operator D) (hVU : Vᴴ * V = 1) :
    Vᴴ * (V * X) = X := by
  rw [← Matrix.mul_assoc, hVU, Matrix.one_mul]

/-- If `Vᴴ * V = 1` and the diagonal product `diagonal d * diagonal e` equals `diagonal d`, the
corresponding nested sandwich simplifies to `V * (diagonal d * Vᴴ)`. -/
private theorem sandwich {D : ℕ} (V : Operator D) (d e : Fin D → ℂ)
    (hVU : Vᴴ * V = 1) (h : Matrix.diagonal d * Matrix.diagonal e = Matrix.diagonal d) :
    V * (Matrix.diagonal d * (Vᴴ * (V * (Matrix.diagonal e * Vᴴ))))
      = V * (Matrix.diagonal d * Vᴴ) := by
  calc V * (Matrix.diagonal d * (Vᴴ * (V * (Matrix.diagonal e * Vᴴ))))
      = V * (Matrix.diagonal d * ((Vᴴ * V) * (Matrix.diagonal e * Vᴴ))) := by
        congr 2
        rw [Matrix.mul_assoc]
    _ = V * (Matrix.diagonal d * (Matrix.diagonal e * Vᴴ)) := by rw [hVU, Matrix.one_mul]
    _ = V * (Matrix.diagonal d * Vᴴ) := by
        congr 1
        rw [← Matrix.mul_assoc, h]

/-- For unitary `V`, the spectral range-projector matrix is idempotent. -/
theorem gridHHLRangeProjector_sq {D M : ℕ} (label : Fin D → Fin M) (V : Operator D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    gridHHLRangeProjector (M := M) label V * gridHHLRangeProjector label V
      = gridHHLRangeProjector label V := by
  have hVU : Vᴴ * V = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hV
    rwa [Matrix.star_eq_conjTranspose] at h
  have hcore : Matrix.diagonal (gridHHLSupport (M := M) label)
      * Matrix.diagonal (gridHHLSupport (M := M) label)
      = Matrix.diagonal (gridHHLSupport (M := M) label) := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    simp only [Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      rw [gridHHLSupport_sq label]
    · simp [hij]
  show (V * Matrix.diagonal (gridHHLSupport (M := M) label) * Vᴴ)
      * (V * Matrix.diagonal (gridHHLSupport (M := M) label) * Vᴴ)
      = V * Matrix.diagonal (gridHHLSupport (M := M) label) * Vᴴ
  calc (V * Matrix.diagonal (gridHHLSupport (M := M) label) * Vᴴ)
      * (V * Matrix.diagonal (gridHHLSupport (M := M) label) * Vᴴ)
      = V * (Matrix.diagonal (gridHHLSupport (M := M) label)
        * (Vᴴ * (V * (Matrix.diagonal (gridHHLSupport (M := M) label) * Vᴴ)))) := by
        simp only [Matrix.mul_assoc]
    _ = V * (Matrix.diagonal (gridHHLSupport (M := M) label)
        * (Matrix.diagonal (gridHHLSupport (M := M) label) * Vᴴ)) := by
        rw [conjV_mul V _ hVU]
    _ = V * (Matrix.diagonal (gridHHLSupport (M := M) label) * Vᴴ) := by
      congr 1
      rw [← Matrix.mul_assoc, hcore]
    _ = V * Matrix.diagonal (gridHHLSupport (M := M) label) * Vᴴ := by
      rw [Matrix.mul_assoc]

/-- For unitary `V`, left multiplication by the spectral range projector leaves the grid matrix
unchanged. -/
theorem gridHHLRangeProjector_mul_matrix {D M : ℕ} (label : Fin D → Fin M) (V : Operator D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    gridHHLRangeProjector (M := M) label V * gridHHLMatrix label V = gridHHLMatrix label V := by
  have hVU : Vᴴ * V = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hV
    rwa [Matrix.star_eq_conjTranspose] at h
  have hcore : Matrix.diagonal (gridHHLSupport (M := M) label)
      * Matrix.diagonal (gridHHLScale M label) = Matrix.diagonal (gridHHLScale M label) := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    simp only [Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      rw [gridHHLSupport_mul_scale label]
    · simp [hij]
  show (V * Matrix.diagonal (gridHHLSupport (M := M) label) * Vᴴ)
      * (V * Matrix.diagonal (gridHHLScale M label) * Vᴴ)
      = V * Matrix.diagonal (gridHHLScale M label) * Vᴴ
  calc (V * Matrix.diagonal (gridHHLSupport (M := M) label) * Vᴴ)
      * (V * Matrix.diagonal (gridHHLScale M label) * Vᴴ)
      = V * (Matrix.diagonal (gridHHLSupport (M := M) label)
        * (Vᴴ * (V * (Matrix.diagonal (gridHHLScale M label) * Vᴴ)))) := by
        simp only [Matrix.mul_assoc]
    _ = V * (Matrix.diagonal (gridHHLSupport (M := M) label)
        * (Matrix.diagonal (gridHHLScale M label) * Vᴴ)) := by
        rw [conjV_mul V _ hVU]
    _ = V * (Matrix.diagonal (gridHHLScale M label) * Vᴴ) := by
      congr 1
      rw [← Matrix.mul_assoc, hcore]
    _ = V * Matrix.diagonal (gridHHLScale M label) * Vᴴ := by rw [Matrix.mul_assoc]

/-- For unitary `V`, left multiplication by the spectral range projector leaves the spectral
reciprocal unchanged. -/
theorem gridHHLRangeProjector_mul_reciprocal {D M : ℕ} (label : Fin D → Fin M) (V : Operator D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    gridHHLRangeProjector (M := M) label V * gridHHLReciprocal label V
      = gridHHLReciprocal label V := by
  have hVU : Vᴴ * V = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hV
    rwa [Matrix.star_eq_conjTranspose] at h
  have hcore : Matrix.diagonal (gridHHLSupport (M := M) label)
      * Matrix.diagonal (gridHHLReciprocalScale M label)
      = Matrix.diagonal (gridHHLReciprocalScale M label) := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    simp only [Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      rw [gridHHLSupport_mul_reciprocal label]
    · simp [hij]
  show (V * Matrix.diagonal (gridHHLSupport (M := M) label) * Vᴴ)
      * (V * Matrix.diagonal (gridHHLReciprocalScale M label) * Vᴴ)
      = V * Matrix.diagonal (gridHHLReciprocalScale M label) * Vᴴ
  calc (V * Matrix.diagonal (gridHHLSupport (M := M) label) * Vᴴ)
      * (V * Matrix.diagonal (gridHHLReciprocalScale M label) * Vᴴ)
      = V * (Matrix.diagonal (gridHHLSupport (M := M) label)
        * (Vᴴ * (V * (Matrix.diagonal (gridHHLReciprocalScale M label) * Vᴴ)))) := by
        simp only [Matrix.mul_assoc]
    _ = V * (Matrix.diagonal (gridHHLSupport (M := M) label)
        * (Matrix.diagonal (gridHHLReciprocalScale M label) * Vᴴ)) := by
        rw [conjV_mul V _ hVU]
    _ = V * (Matrix.diagonal (gridHHLReciprocalScale M label) * Vᴴ) := by
      congr 1
      rw [← Matrix.mul_assoc, hcore]
    _ = V * Matrix.diagonal (gridHHLReciprocalScale M label) * Vᴴ := by
        rw [Matrix.mul_assoc]

/-- For positive grid size and unitary `V`, the spectral reciprocal times the grid matrix is the
spectral range projector. -/
theorem gridHHLReciprocal_mul_matrix {D M : ℕ} (hM : 0 < M) (label : Fin D → Fin M)
    (V : Operator D) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    gridHHLReciprocal label V * gridHHLMatrix label V = gridHHLRangeProjector label V := by
  have hVU : Vᴴ * V = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hV
    rwa [Matrix.star_eq_conjTranspose] at h
  have hcore : Matrix.diagonal (gridHHLReciprocalScale M label)
      * Matrix.diagonal (gridHHLScale M label) = Matrix.diagonal (gridHHLSupport (M := M) label) := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    simp only [Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      rw [gridHHLReciprocalScale_mul_scale hM label]
    · simp [hij]
  show (V * Matrix.diagonal (gridHHLReciprocalScale M label) * Vᴴ)
      * (V * Matrix.diagonal (gridHHLScale M label) * Vᴴ)
      = V * Matrix.diagonal (gridHHLSupport (M := M) label) * Vᴴ
  calc (V * Matrix.diagonal (gridHHLReciprocalScale M label) * Vᴴ)
      * (V * Matrix.diagonal (gridHHLScale M label) * Vᴴ)
      = V * (Matrix.diagonal (gridHHLReciprocalScale M label)
        * (Vᴴ * (V * (Matrix.diagonal (gridHHLScale M label) * Vᴴ)))) := by
        simp only [Matrix.mul_assoc]
    _ = V * (Matrix.diagonal (gridHHLReciprocalScale M label)
        * (Matrix.diagonal (gridHHLScale M label) * Vᴴ)) := by
        rw [conjV_mul V _ hVU]
    _ = V * (Matrix.diagonal (gridHHLSupport (M := M) label) * Vᴴ) := by
      congr 1
      rw [← Matrix.mul_assoc, hcore]
    _ = V * Matrix.diagonal (gridHHLSupport (M := M) label) * Vᴴ := by rw [Matrix.mul_assoc]

/-- For positive grid size and unitary `V`, the guarded spectral reciprocal equals the matrix
pseudoinverse of the grid matrix. -/
theorem grid_hhl_spectral_reciprocal_eq_pseudoinverse {D M : ℕ} (hM : 0 < M)
    (label : Fin D → Fin M) (V : Operator D) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    gridHHLReciprocal label V = matrixPseudoinverse (gridHHLMatrix label V) := by
  refine matrixPseudoinverse_unique (gridHHLMatrix label V) (gridHHLReciprocal label V)
    ?_ ?_ ?_ ?_
  · calc gridHHLMatrix label V * gridHHLReciprocal label V * gridHHLMatrix label V
      = gridHHLRangeProjector label V * gridHHLMatrix label V :=
        (gridHHLMatrix_mul_reciprocal hM label V hV).symm ▸ rfl
    _ = gridHHLMatrix label V := gridHHLRangeProjector_mul_matrix label V hV
  · calc gridHHLReciprocal label V * gridHHLMatrix label V * gridHHLReciprocal label V
      = gridHHLRangeProjector label V * gridHHLReciprocal label V :=
        (gridHHLReciprocal_mul_matrix hM label V hV).symm ▸ rfl
    _ = gridHHLReciprocal label V := gridHHLRangeProjector_mul_reciprocal label V hV
  · rw [gridHHLMatrix_mul_reciprocal hM label V hV]
    exact gridHHLRangeProjector_adjoint label V
  · rw [gridHHLReciprocal_mul_matrix hM label V hV]
    exact gridHHLRangeProjector_adjoint label V

/-- The Fourier matrix maps a computational basis state to its corresponding phase state. -/
theorem gridHHLqft_ket (M : ℕ) (j : Fin M) :
    ApplyGate (QFTMatrix M) (Ket j) = PhaseState M j := by
  funext y
  show ∑ x, QFTMatrix M y x * Ket j x = PhaseState M j y
  simp only [qftMatrix_apply]
  rw [Finset.sum_eq_single j]
  · rw [Ket, if_pos rfl, mul_one, phaseState_apply]
    have hcomm : ((y.val : ℤ) * (j.val : ℤ)) = (j.val : ℤ) * (y.val : ℤ) := mul_comm _ _
    rw [hcomm]
  · intro m _ hm
    rw [Ket, if_neg hm, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- Each column of a unitary `V` is an eigenvector of the grid oracle with root-of-unity
eigenvalue indexed by its spectral label. -/
theorem gridHHLOracle_mulVec_column {D M : ℕ} (label : Fin D → Fin M) (V : Operator D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (i : Fin D) :
    gridHHLOracle label V *ᵥ (V *ᵥ Ket i)
      = primRoot M ^ (((label i).val : ℤ)) • (V *ᵥ Ket i) := by
  have hUV : Vᴴ * V = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hV
    rwa [Matrix.star_eq_conjTranspose] at h
  have hcol : Matrix.mulVec Vᴴ (Matrix.mulVec V (Ket i)) = Ket i := by
    have h := Matrix.mulVec_mulVec (Ket i) Vᴴ V
    rw [hUV] at h
    simp only [Matrix.one_mulVec] at h
    exact h
  have h1 : Matrix.mulVec (V * Matrix.diagonal (fun k => primRoot M ^ (((label k).val : ℤ))) * Vᴴ)
      (Matrix.mulVec V (Ket i))
      = Matrix.mulVec (V * Matrix.diagonal (fun k => primRoot M ^ (((label k).val : ℤ))))
          (Matrix.mulVec Vᴴ (Matrix.mulVec V (Ket i))) := by
    have h := Matrix.mulVec_mulVec (Matrix.mulVec V (Ket i))
      (V * Matrix.diagonal (fun k => primRoot M ^ (((label k).val : ℤ)))) Vᴴ
    rw [h]
  show Matrix.mulVec (V * Matrix.diagonal (fun k => primRoot M ^ (((label k).val : ℤ))) * Vᴴ)
      (Matrix.mulVec V (Ket i))
      = primRoot M ^ (((label i).val : ℤ)) • Matrix.mulVec V (Ket i)
  have hdiag : Matrix.mulVec
      (Matrix.diagonal (fun k => primRoot M ^ (((label k).val : ℤ)))) (Ket i)
      = primRoot M ^ (((label i).val : ℤ)) • Ket i := by
    funext x
    simp only [Matrix.mulVec, dotProduct, Matrix.diagonal_apply]
    by_cases hx : x = i
    · subst hx
      simp [Ket]
    · simp [Ket, hx]
  rw [h1, hcol]
  rw [← Matrix.mulVec_mulVec, hdiag, Matrix.mulVec_smul]

/-- The phase-data relabeling sends `((a, i), flag)` to `(a, (flag, i))`. -/
theorem gridHHLPhaseData_apply {D M : ℕ} (p : (Fin M × Fin D) × Bool) :
    gridHHLPhaseData (D := D) (M := M) p = (p.1.1, (p.2, p.1.2)) := rfl

/-- The inverse phase-data relabeling sends `(a, (flag, i))` to `((a, i), flag)`. -/
theorem gridHHLPhaseData_symm_apply {D M : ℕ} (q : Fin M × (Bool × Fin D)) :
    (gridHHLPhaseData (D := D) (M := M)).symm q = ((q.1, q.2.2), q.2.1) := rfl

/-- The tensor product of a phase-data state and a flag state, relabeled into phase, flag, and
data order. -/
noncomputable def gridHHLWorkspaceState {D M : ℕ} (φ : QState (Fin M × Fin D)) (g : QState Bool) :
    QState (Fin M × (Bool × Fin D)) :=
  relabelState (gridHHLPhaseData (D := D) (M := M)) (TensorState φ g)

/-- A workspace-state amplitude at `(a, (flag, i))` is the phase-data amplitude at `(a, i)`
times the flag amplitude. -/
theorem gridHHLWorkspaceState_apply {D M : ℕ} (φ : QState (Fin M × Fin D)) (g : QState Bool)
    (a : Fin M) (flag : Bool) (i : Fin D) :
    gridHHLWorkspaceState (D := D) (M := M) φ g (a, (flag, i)) = φ (a, i) * g flag := by
  show (TensorState φ g) ((gridHHLPhaseData (D := D) (M := M)).symm (a, (flag, i)))
    = φ (a, i) * g flag
  rw [gridHHLPhaseData_symm_apply]
  rfl

/-- Applying `Q` tensored with the identity acts on each slice of a bipartite state with the
second coordinate fixed. -/
theorem applyGate_tensorGate_pair {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J] (Q : Matrix I I ℂ) (φ : QState (I × J)) :
    ApplyGate (TensorGate (I := I) (J := J) Q 1) φ
      = fun p => (ApplyGate Q (fun i => φ (i, p.2))) p.1 := by
  funext p
  obtain ⟨a, i⟩ := p
  show ∑ q : I × J, (TensorGate (I := I) (J := J) Q 1) (a, i) q * φ q
      = ∑ a' : I, Q a a' * φ (a', i)
  simp only [TensorGate, Matrix.kroneckerMap, Matrix.of_apply, Fintype.sum_prod_type,
    Matrix.one_apply]
  refine Finset.sum_congr (M := ℂ) (s₁ := (Finset.univ : Finset I)) rfl fun x _ => ?_
  rw [Finset.sum_eq_single i]
  · simp
  · intro y _ hy
    rw [if_neg (Ne.symm hy)]
    ring
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- Apply a matrix to the phase coordinate of a phase-data state, independently for each data
coordinate. -/
noncomputable def gridHHLPhaseOnly {D M : ℕ} (Q : Matrix (Fin M) (Fin M) ℂ)
    (φ : QState (Fin M × Fin D)) : QState (Fin M × Fin D) :=
  fun p => (ApplyGate Q (fun a => φ (a, p.2))) p.1

/-- The lifted phase matrix acts on the phase-data component of a workspace state and preserves
its flag state. -/
theorem gridHHLFourier_apply {D M : ℕ} (Q : Matrix (Fin M) (Fin M) ℂ)
    (φ : QState (Fin M × Fin D)) (g : QState Bool) :
    ApplyGate (gridHHLFourier (D := D) (M := M) Q) (gridHHLWorkspaceState (D := D) (M := M) φ g)
      = gridHHLWorkspaceState (D := D) (M := M) (gridHHLPhaseOnly Q φ) g := by
  funext p
  obtain ⟨a, flag, i⟩ := p
  show ApplyGate (relabelGate (gridHHLPhaseData (D := D) (M := M))
      (TensorGate (I := Fin M × Fin D) (J := Bool) (TensorGate (I := Fin M) (J := Fin D) Q 1) 1))
      (relabelState (gridHHLPhaseData (D := D) (M := M)) (TensorState φ g)) (a, (flag, i))
      = (ApplyGate Q (fun a' => φ (a', i))) a * g flag
  have hp : ApplyGate (TensorGate (I := Fin M) (J := Fin D) Q (1 : Matrix (Fin D) (Fin D) ℂ)) φ
      = fun p => (ApplyGate Q (fun i => φ (i, p.2))) p.1 :=
    applyGate_tensorGate_pair (I := Fin M) (J := Fin D) Q φ
  rw [applyGate_relabelGate, applyGate_tensorGate, applyGate_one, hp]
  show relabelState (gridHHLPhaseData (D := D) (M := M))
      (TensorState (gridHHLPhaseOnly Q φ) g) (a, (flag, i))
      = (ApplyGate Q (fun a' => φ (a', i))) a * g flag
  show (TensorState (gridHHLPhaseOnly Q φ) g)
      ((gridHHLPhaseData (D := D) (M := M)).symm (a, (flag, i)))
      = (ApplyGate Q (fun a' => φ (a', i))) a * g flag
  rw [gridHHLPhaseData_symm_apply]
  rfl

/-- The lifted controlled-powers matrix acts on the phase-data component of a workspace state
and preserves its flag state. -/
theorem gridHHLPowers_apply {D M : ℕ} (U : Operator D) (φ : QState (Fin M × Fin D))
    (g : QState Bool) :
    ApplyGate (gridHHLPowers (D := D) (M := M) U) (gridHHLWorkspaceState (D := D) (M := M) φ g)
      = gridHHLWorkspaceState (D := D) (M := M) (ControlledPowers U M *ᵥ φ) g := by
  funext p
  obtain ⟨a, flag, i⟩ := p
  show ApplyGate (relabelGate (gridHHLPhaseData (D := D) (M := M))
      (TensorGate (I := Fin M × Fin D) (J := Bool) (ControlledPowers U M) 1))
      (relabelState (gridHHLPhaseData (D := D) (M := M)) (TensorState φ g)) (a, (flag, i))
      = (ControlledPowers U M *ᵥ φ) (a, i) * g flag
  rw [applyGate_relabelGate, applyGate_tensorGate, applyGate_one]
  show relabelState (gridHHLPhaseData (D := D) (M := M))
      (TensorState (ControlledPowers U M *ᵥ φ) g) (a, (flag, i))
      = (ControlledPowers U M *ᵥ φ) (a, i) * g flag
  show (TensorState (ControlledPowers U M *ᵥ φ) g)
      ((gridHHLPhaseData (D := D) (M := M)).symm (a, (flag, i)))
      = (ControlledPowers U M *ᵥ φ) (a, i) * g flag
  rw [gridHHLPhaseData_symm_apply]
  rfl

/-- An entry of a relabeled gate is the original matrix entry at the inverse images of its row
and column indices. -/
theorem relabelGate_submatrix {I J : Type*} (e : I ≃ J) (M : Matrix I I ℂ) (p q : J) :
    relabelGate e M p q = M (e.symm p) (e.symm q) := by
  show Matrix.reindex e e M p q = _
  rw [Matrix.reindex_apply, Matrix.submatrix_apply]

/-- The flag-data relabeling sends `((a, flag), i)` to `(a, (flag, i))`. -/
theorem gridHHLFlagData_apply {D M : ℕ} (p : (Fin M × Bool) × Fin D) :
    gridHHLFlagData (D := D) (M := M) p = (p.1.1, (p.1.2, p.2)) := rfl

/-- The inverse flag-data relabeling sends `(a, (flag, i))` to `((a, flag), i)`. -/
theorem gridHHLFlagData_symm_apply {D M : ℕ} (q : Fin M × (Bool × Fin D)) :
    (gridHHLFlagData (D := D) (M := M)).symm q = ((q.1, q.2.1), q.2.2) := rfl

/-- The block-diagonal flag rotation has zero entries between distinct phase labels. -/
theorem gridHHLRotation_apply_ne {M : ℕ} (c : ℝ) (a b : Fin M) (flag flag' : Bool)
    (h : a ≠ b) : gridHHLRotation M c (a, flag) (b, flag') = 0 := by
  show BlockDiag (gridHHLBlock M c) (a, flag) (b, flag') = 0
  rw [Qatlib.Concepts.QueryComplexity.DegreeMethod.blockDiag_apply, if_neg h]

/-- At a fixed phase label, the flag rotation has the entries of the corresponding two-by-two
flag block. -/
theorem gridHHLRotation_apply {M : ℕ} (c : ℝ) (a : Fin M) (flag flag' : Bool) :
    gridHHLRotation M c (a, flag) (a, flag') = gridHHLBlock M c a flag flag' := by
  show BlockDiag (gridHHLBlock M c) (a, flag) (a, flag') = _
  rw [Qatlib.Concepts.QueryComplexity.DegreeMethod.blockDiag_apply, if_pos rfl]

/-- At each phase and data coordinate, the lifted flag gate transforms the two flag amplitudes
by the cosine-sine block formulas. -/
theorem gridHHLFlag_apply {D M : ℕ} (c : ℝ) (s : QState (Fin M × (Bool × Fin D)))
    (a : Fin M) (i : Fin D) :
    ApplyGate (gridHHLFlag (D := D) (M := M) c) s (a, (false, i))
      = (gridHHLCos M c a : ℂ) * s (a, (false, i))
        - (gridHHLSin M c a : ℂ) * s (a, (true, i))
    ∧ ApplyGate (gridHHLFlag (D := D) (M := M) c) s (a, (true, i))
      = (gridHHLSin M c a : ℂ) * s (a, (false, i))
        + (gridHHLCos M c a : ℂ) * s (a, (true, i)) := by
  have hfin : ∀ (q : Bool),
      ∑ b : Fin M, ∑ t : Bool, ∑ j : Fin D,
        (gridHHLRotation M c (a, q) (b, t) * (if i = j then 1 else 0)) * s (b, (t, j))
        = (gridHHLBlock M c a q false : ℂ) * s (a, (false, i))
          + (gridHHLBlock M c a q true : ℂ) * s (a, (true, i)) := by
    intro q
    have hcross : ∀ (b : Fin M) (h : a ≠ b),
        ∑ t : Bool, ∑ j : Fin D,
          (gridHHLRotation M c (a, q) (b, t) * (if i = j then 1 else 0)) * s (b, (t, j)) = 0 := by
      intro b h
      refine Finset.sum_eq_zero fun t _ => ?_
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [gridHHLRotation_apply_ne c a b q t h]
      simp
    have hf : (∑ b : Fin M, ∑ t : Bool, ∑ j : Fin D,
          (gridHHLRotation M c (a, q) (b, t) * (if i = j then 1 else 0)) * s (b, (t, j)))
        = ∑ t : Bool, ∑ j : Fin D,
          (gridHHLRotation M c (a, q) (a, t) * (if i = j then 1 else 0)) * s (a, (t, j)) := by
      refine Finset.sum_eq_single a (fun b _ hb => hcross b (Ne.symm hb))
        (fun h => absurd (Finset.mem_univ a) h)
    rw [hf]
    have hfin : ∀ (t : Bool),
        ∑ j : Fin D, (gridHHLRotation M c (a, q) (a, t) * (if i = j then 1 else 0))
            * s (a, (t, j))
          = gridHHLBlock M c a q t * s (a, (t, i)) := by
      intro t
      rw [Finset.sum_eq_single i]
      · rw [gridHHLRotation_apply c a q t, gridHHLBlock]
        simp
      · intro j _ hj
        rw [if_neg (Ne.symm hj)]
        ring
      · intro h
        exact absurd (Finset.mem_univ i) h
    rw [Fintype.sum_bool, hfin false, hfin true]
    ring
  refine ⟨?_, ?_⟩
  · show ∑ q : Fin M × (Bool × Fin D),
        (relabelGate (gridHHLFlagData (D := D) (M := M))
          (TensorGate (I := Fin M × Bool) (J := Fin D) (gridHHLRotation M c)
            (1 : Matrix (Fin D) (Fin D) ℂ))) (a, (false, i)) q * s q
      = (gridHHLCos M c a : ℂ) * s (a, (false, i))
        - (gridHHLSin M c a : ℂ) * s (a, (true, i))
    simp only [relabelGate_submatrix, gridHHLFlagData_symm_apply]
    simp only [TensorGate, Matrix.kroneckerMap, Matrix.of_apply, Fintype.sum_prod_type,
      Matrix.one_apply]
    rw [hfin false, gridHHLBlock]
    simp only [Matrix.of_apply, gridHHLCos, gridHHLSin]
    ring
  · show ∑ q : Fin M × (Bool × Fin D),
        (relabelGate (gridHHLFlagData (D := D) (M := M))
          (TensorGate (I := Fin M × Bool) (J := Fin D) (gridHHLRotation M c)
            (1 : Matrix (Fin D) (Fin D) ℂ))) (a, (true, i)) q * s q
      = (gridHHLSin M c a : ℂ) * s (a, (false, i))
        + (gridHHLCos M c a : ℂ) * s (a, (true, i))
    simp only [relabelGate_submatrix, gridHHLFlagData_symm_apply]
    simp only [TensorGate, Matrix.kroneckerMap, Matrix.of_apply, Fintype.sum_prod_type,
      Matrix.one_apply]
    rw [hfin true, gridHHLBlock]
    simp only [Matrix.of_apply, gridHHLCos, gridHHLSin]

/-- For positive grid size, the Fourier transform of the zero basis state has constant amplitude
`1 / √M`. -/
theorem gridHHLqft_zero (M : ℕ) (hM : 0 < M) (j : Fin M) :
    ApplyGate (QFTMatrix M) (Ket (⟨0, hM⟩ : Fin M)) j = ((Real.sqrt (M : ℝ) : ℂ)⁻¹) := by
  show ∑ x, QFTMatrix M j x * (Ket (⟨0, hM⟩ : Fin M) x) = _
  rw [Finset.sum_eq_single ⟨0, hM⟩]
  · have he : ((j.val : ℤ) * (((⟨0, hM⟩ : Fin M).val : ℤ))) = 0 := by rfl
    rw [qftMatrix_apply, Ket, if_pos rfl, he, zpow_zero, mul_one, mul_one]
  · intro x _ hx
    rw [Ket, if_neg hx]
    ring
  · intro h
    exact absurd (Finset.mem_univ (⟨0, hM⟩ : Fin M)) h

/-- A finite sum weighted by the equality indicator for `j` evaluates to the summand at `j`. -/
@[simp] theorem gridHHL_selector_sum {I : Type*} [Fintype I] [DecidableEq I] (j : I)
    (g : I → ℂ) : (∑ i, g i * (if i = j then 1 else 0)) = g j := by
  have h : (∑ i, g i * (if i = j then 1 else 0)) = g j * 1 := by
    rw [Finset.sum_eq_single j (f := fun i => g i * (if i = j then 1 else 0))]
    · simp
    · intro i _ hi
      rw [if_neg hi, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  simp only [mul_one] at h
  exact h

/-- Each coordinate of `V *ᵥ w` is the sum of the corresponding column coordinates weighted by
`w`. -/
theorem matrix_mulVec_apply {I : Type*} [Fintype I] [DecidableEq I] (V : Matrix I I ℂ)
    (w : QState I) (j : I) :
    (V *ᵥ w) j = ∑ i, w i * (V *ᵥ Ket i) j := by
  simp only [Matrix.mulVec, dotProduct, Ket, gridHHL_selector_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- A matrix-vector product is the linear combination of the matrix columns with coefficients
given by the vector. -/
theorem matrix_mulVec_eq_sum {I : Type*} [Fintype I] [DecidableEq I] (V : Matrix I I ℂ)
    (w : QState I) : V *ᵥ w = ∑ i, w i • (V *ᵥ Ket i) := by
  funext j
  have h := matrix_mulVec_apply V w j
  have hA : (∑ i, w i • (V *ᵥ Ket i)) j = ∑ i, w i * (V *ᵥ Ket i) j := by
    rw [Fintype.sum_apply]
    refine Finset.sum_congr (M := ℂ) rfl fun i _ => ?_
    exact Pi.smul_apply (w i) (V *ᵥ Ket i) j
  rw [hA]
  exact h

/-- A state expands in the columns of a unitary `V` with coefficients given by `Vᴴ *ᵥ b`. -/
theorem gridHHL_eigen_expansion {D M : ℕ} (V : Operator D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (b : QState (Fin D)) :
    b = ∑ i, (Vᴴ *ᵥ b) i • (V *ᵥ Ket i) := by
  have hUV : V * Vᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp hV
    rwa [Matrix.star_eq_conjTranspose] at h
  calc b = 1 *ᵥ b := (Matrix.one_mulVec b).symm
    _ = (V * Vᴴ) *ᵥ b := by rw [hUV]
    _ = V *ᵥ (Vᴴ *ᵥ b) := (Matrix.mulVec_mulVec b V Vᴴ).symm
    _ = ∑ i, (Vᴴ *ᵥ b) i • (V *ᵥ Ket i) := matrix_mulVec_eq_sum V (Vᴴ *ᵥ b)

/-- A finite sum of states with scalar equality-indicator coefficients selects the state at the
indicated index. -/
theorem sum_smul_eq_single {ι β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq β]
    {i : ι} (g : ι → QState β) :
    (∑ j, (if j = i then (1 : ℂ) else 0) • g j) = g i := by
  rw [Finset.sum_eq_single i (f := fun j => (if j = i then (1 : ℂ) else 0) • g j)]
  · simp
  · intro j _ hj
    by_cases hji : j = i
    · exact absurd hji hj
    · simp [hji]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- For positive grid size, the inverse Fourier transform maps the constant uniform-amplitude
state to the zero basis state. -/
theorem gridHHLqft_conjTranspose_zero (M : ℕ) (hM : 0 < M) :
    ApplyGate (QFTMatrix M)ᴴ (fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹) = Ket (⟨0, hM⟩ : Fin M) := by
  have h0 : PhaseState M 0 = fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹ := by
    funext a
    rw [phaseState_apply]
    have hz : ((0 : ℕ) : ℤ) * (a.val : ℤ) = 0 := by ring
    rw [hz, zpow_zero, mul_one]
  rw [← h0]
  exact qftMatrix_conjTranspose_mulVec_phaseState hM ⟨0, hM⟩

/-- Applying a gate commutes with scalar multiplication of a state. -/
theorem gridHHL_applyGate_state_smul {I : Type*} [Fintype I] [DecidableEq I] (Q : Matrix I I ℂ) (c : ℂ)
    (v : QState I) : ApplyGate Q (c • v) = c • ApplyGate Q v := by
  funext p
  show ∑ q, Q p q * (c * v q) = c * ∑ q, Q p q * v q
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ => by ring

/-- Applying the Fourier matrix only to the phase coordinate of a basis-state tensor produces
the matching phase state times the unchanged data state. -/
theorem gridHHLPhaseOnly_qft_ket {D M : ℕ} (j : Fin M) (χ : QState (Fin D)) :
    gridHHLPhaseOnly (D := D) (M := M) (QFTMatrix M) (TensorState (Ket j) χ)
      = fun p => PhaseState M j p.1 * χ p.2 := by
  funext p
  obtain ⟨a, i⟩ := p
  have hs : (fun a' : Fin M => (Ket j a') * χ i) = (χ i) • Ket j := by
    funext a'
    show (Ket j a') * χ i = χ i * (Ket j a')
    ring
  show ApplyGate (QFTMatrix M) (fun a' => (Ket j a') * χ i) a = PhaseState M j a * χ i
  rw [hs, gridHHL_applyGate_state_smul, gridHHLqft_ket]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- For `Uᴴ * U = 1` and an eigenstate with the matching root-of-unity eigenvalue, controlled
powers of `Uᴴ` remove the phase-state factor and restore uniform phase amplitudes. -/
theorem controlledPowers_conjTranspose_kickback {D M : ℕ} (U : Operator D) (k : ℕ)
    (χ : QState (Fin D)) (hU : Uᴴ * U = 1)
    (hχ : U *ᵥ χ = (primRoot M ^ ((k : ℤ))) • χ) :
    ControlledPowers Uᴴ M *ᵥ TensorState (PhaseState M k) χ
      = TensorState (fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹) χ := by
  have h1 : (Uᴴ * U) *ᵥ χ = Uᴴ *ᵥ (U *ᵥ χ) := (Matrix.mulVec_mulVec χ Uᴴ U).symm
  rw [hU, Matrix.one_mulVec, hχ, mulVec_smul] at h1
  have hback : Uᴴ *ᵥ χ = (primRoot M ^ ((k : ℤ)))⁻¹ • χ := by
    have h2 : (primRoot M ^ ((k : ℤ)))⁻¹ • χ = Uᴴ *ᵥ χ := by
      calc (primRoot M ^ ((k : ℤ)))⁻¹ • χ
          = (primRoot M ^ ((k : ℤ)))⁻¹ • ((primRoot M ^ ((k : ℤ))) • (Uᴴ *ᵥ χ)) := by
            rw [← h1]
        _ = Uᴴ *ᵥ χ := by
          rw [smul_smul, inv_mul_cancel₀ (zpow_ne_zero _ (primRoot_ne_zero M)), one_smul]
    exact h2.symm
  have hev := mulVec_pow_of_eigen hback
  funext p
  obtain ⟨a, i⟩ := p
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, ControlledPowers,
    Matrix.of_apply, TensorState, phaseState_apply]
  rw [Finset.sum_eq_single a]
  · have hsum : (∑ j : Fin D, ((Uᴴ ^ (a.val : ℕ)) i j)
          * ((Real.sqrt (M : ℝ) : ℂ)⁻¹ * primRoot M ^ (((k : ℤ) * (a.val : ℤ))) * χ j))
        = ((Real.sqrt (M : ℝ) : ℂ)⁻¹ * primRoot M ^ (((k : ℤ) * (a.val : ℤ))))
          * ((Uᴴ ^ (a.val : ℕ)) *ᵥ χ) i := by
      simp only [Matrix.mulVec, dotProduct]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [if_true]
    rw [hsum, hev a.val, Pi.smul_apply]
    have hX : (primRoot M ^ ((k : ℤ))) ^ ((a.val : ℕ) : ℤ)
        = primRoot M ^ ((k : ℤ) * (a.val : ℤ)) := by
      have h := _root_.zpow_mul' (primRoot M) (a.val : ℤ) (k : ℤ)
      rw [mul_comm (a.val : ℤ) (k : ℤ)] at h
      exact h.symm
    have h3 : ((primRoot M ^ ((k : ℤ)))⁻¹) ^ (a.val : ℕ)
        = (primRoot M ^ ((k : ℤ) * (a.val : ℤ)))⁻¹ := by
      rw [← _root_.zpow_neg_one, ← zpow_natCast, ← _root_.zpow_mul', mul_neg, mul_one,
        _root_.zpow_neg, hX]
    have hone : primRoot M ^ ((k : ℤ) * (a.val : ℤ))
        * ((primRoot M ^ ((k : ℤ)))⁻¹ ^ (a.val : ℕ)) = 1 := by
      calc primRoot M ^ ((k : ℤ) * (a.val : ℤ)) * ((primRoot M ^ ((k : ℤ)))⁻¹ ^ (a.val : ℕ))
          = primRoot M ^ ((k : ℤ) * (a.val : ℤ)) * (primRoot M ^ ((k : ℤ) * (a.val : ℤ)))⁻¹ := by
            rw [h3]
        _ = 1 := mul_inv_cancel₀ (zpow_ne_zero ((k : ℤ) * (a.val : ℤ)) (primRoot_ne_zero M))
    rw [smul_eq_mul]
    calc (Real.sqrt (M : ℝ) : ℂ)⁻¹ * primRoot M ^ ((k : ℤ) * (a.val : ℤ))
          * ((primRoot M ^ ((k : ℤ)))⁻¹ ^ (a.val : ℕ) * χ i)
        = (Real.sqrt (M : ℝ) : ℂ)⁻¹ * (primRoot M ^ ((k : ℤ) * (a.val : ℤ))
            * (primRoot M ^ ((k : ℤ)))⁻¹ ^ (a.val : ℕ)) * χ i := by ring
      _ = (Real.sqrt (M : ℝ) : ℂ)⁻¹ * χ i := by rw [hone, mul_one]
  · intro m _ hm
    simp [show a ≠ m from fun e => hm e.symm]
  · intro hcon
    exact absurd (Finset.mem_univ a) hcon

/-- The adjoint of the identity complex matrix is the identity. -/
theorem one_conjTranspose {n : Type*} [Fintype n] [DecidableEq n] :
    (1 : Matrix n n ℂ)ᴴ = 1 := by
  ext i j
  rw [Matrix.conjTranspose_apply, Matrix.one_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Ne.symm hij]

/-- The adjoint of a controlled-powers matrix is the controlled-powers matrix of the adjoint. -/
theorem conjTranspose_controlledPowers {D M : ℕ} (U : Operator D) :
    (ControlledPowers U M)ᴴ = ControlledPowers Uᴴ M := by
  funext p
  funext q
  obtain ⟨a, i⟩ := p
  obtain ⟨b, j⟩ := q
  rw [Matrix.conjTranspose_apply]
  simp only [ControlledPowers, Matrix.of_apply]
  by_cases h : b = a
  · rw [if_pos h, if_pos h.symm, ← Matrix.conjTranspose_apply, Matrix.conjTranspose_pow]
    have hval : a.val = b.val := congrArg Fin.val h.symm
    rw [hval]
  · rw [if_neg h, if_neg (Ne.symm h)]
    simp

/-- A phase-data gate tensored with the flag identity and relabeled to workspace order acts only
on the phase-data component of a workspace state. -/
theorem applyGate_relabelGate_tensorGate {D M : ℕ} (A : Matrix (Fin M × Fin D) (Fin M × Fin D) ℂ)
    (φ : QState (Fin M × Fin D)) (g : QState Bool) :
    ApplyGate (relabelGate (gridHHLPhaseData (D := D) (M := M))
      (TensorGate (I := Fin M × Fin D) (J := Bool) A 1))
      (gridHHLWorkspaceState (D := D) (M := M) φ g)
      = gridHHLWorkspaceState (D := D) (M := M) (A *ᵥ φ) g := by
  funext p
  obtain ⟨a, flag, i⟩ := p
  show ApplyGate (relabelGate (gridHHLPhaseData (D := D) (M := M)) (TensorGate A 1))
      (relabelState (gridHHLPhaseData (D := D) (M := M)) (TensorState φ g)) (a, (flag, i)) = _
  rw [applyGate_relabelGate, applyGate_tensorGate, applyGate_one]
  show relabelState (gridHHLPhaseData (D := D) (M := M)) (TensorState (A *ᵥ φ) g) (a, (flag, i))
      = (A *ᵥ φ) (a, i) * g flag
  show (TensorState (A *ᵥ φ) g) ((gridHHLPhaseData (D := D) (M := M)).symm (a, (flag, i)))
      = (A *ᵥ φ) (a, i) * g flag
  rw [gridHHLPhaseData_symm_apply]
  rfl

/-- The adjoint lifted controlled-powers matrix applies controlled powers of `Uᴴ` to the
phase-data state and preserves the flag state. -/
theorem gridHHLPowers_apply_adjoint {D M : ℕ} (U : Operator D) (φ : QState (Fin M × Fin D))
    (g : QState Bool) :
    ApplyGate (gridHHLPowers (D := D) (M := M) U)ᴴ (gridHHLWorkspaceState (D := D) (M := M) φ g)
      = gridHHLWorkspaceState (D := D) (M := M) (ControlledPowers Uᴴ M *ᵥ φ) g := by
  rw [gridHHLPowers, relabelGate, TensorGate, Matrix.conjTranspose_reindex,
    Matrix.conjTranspose_kronecker, one_conjTranspose, conjTranspose_controlledPowers]
  exact applyGate_relabelGate_tensorGate (D := D) (M := M) (ControlledPowers Uᴴ M) φ g

/-- Apply Fourier transformation, adjoint controlled powers, and inverse Fourier transformation
to a phase-data state with a separate flag state. -/
noncomputable def gridHHLUncompute {D M : ℕ} (U : Operator D) (ψ : QState (Fin M × Fin D))
    (g : QState Bool) : QState (Fin M × (Bool × Fin D)) :=
  ApplyGate (gridHHLFourier (D := D) (M := M) (QFTMatrix M)ᴴ)
    (ApplyGate (gridHHLPowers (D := D) (M := M) U)ᴴ
      (ApplyGate (gridHHLFourier (D := D) (M := M) (QFTMatrix M))
        (gridHHLWorkspaceState (D := D) (M := M) ψ g)))

/-- The uncomputation state equals the workspace embedding of the corresponding phase-data
Fourier and adjoint-controlled-powers operations. -/
theorem gridHHLUncompute_apply {D M : ℕ} (U : Operator D) (ψ : QState (Fin M × Fin D))
    (g : QState Bool) :
    gridHHLUncompute (D := D) (M := M) U ψ g
      = gridHHLWorkspaceState (D := D) (M := M)
          (gridHHLPhaseOnly (QFTMatrix M)ᴴ
            (ControlledPowers Uᴴ M *ᵥ (gridHHLPhaseOnly (QFTMatrix M) ψ))) g := by
  rw [gridHHLUncompute, gridHHLFourier_apply, gridHHLPowers_apply_adjoint,
    gridHHLFourier_apply]

/-- Applying a gate distributes over a finite linear combination of states. -/
theorem applyGate_sum {I ι : Type*} [Fintype I] [Fintype ι] (Q : Matrix I I ℂ)
    (c : ι → ℂ) (ψ : ι → QState I) :
    ApplyGate Q (∑ i, c i • ψ i) = ∑ i, c i • ApplyGate Q (ψ i) := by
  unfold ApplyGate
  rw [mulVec_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec_smul]

/-- Multiplication on the right by a complex scalar distributes over a finite sum. -/
theorem sum_mul_const {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℂ) (a : ℂ) :
    (∑ i, f i) * a = ∑ i, f i * a := by
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [← ih]
      ring

/-- For positive grid size and an eigenstate with the matching grid eigenphase, uncomputation
replaces its phase label by zero and preserves the data and flag states. -/
theorem gridHHLUncompute_ket {D M : ℕ} (U : Operator D) (k : Fin M) (χ : QState (Fin D))
    (g : QState Bool) (hM : 0 < M) (hU : Uᴴ * U = 1)
    (hχ : U *ᵥ χ = (primRoot M ^ ((k.val : ℤ))) • χ) :
    gridHHLUncompute (D := D) (M := M) U (TensorState (Ket k) χ) g
      = gridHHLWorkspaceState (D := D) (M := M) (TensorState (Ket (⟨0, hM⟩ : Fin M)) χ) g := by
  have hinner : (fun q : Fin M × Fin D => PhaseState M k q.1 * χ q.2)
      = TensorState (PhaseState M k) χ := by
    funext q
    rfl
  rw [gridHHLUncompute_apply, gridHHLPhaseOnly_qft_ket]
  funext p
  obtain ⟨a, flag, i⟩ := p
  have hscale : (fun a' : Fin M => TensorState (fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹) χ (a', i))
      = χ i • (fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹) := by
    funext a'
    show (Real.sqrt (M : ℝ) : ℂ)⁻¹ * χ i = χ i * (Real.sqrt (M : ℝ) : ℂ)⁻¹
    rw [mul_comm]
  rw [gridHHLWorkspaceState_apply]
  show (ApplyGate (QFTMatrix M)ᴴ
      (fun a' => (ControlledPowers Uᴴ M *ᵥ
        (fun q : Fin M × Fin D => PhaseState M k q.1 * χ q.2)) (a', i))) a
      * g flag
    = (Ket (⟨0, hM⟩ : Fin M) a * χ i) * g flag
  rw [hinner, controlledPowers_conjTranspose_kickback U k.val χ hU hχ, hscale,
    gridHHL_applyGate_state_smul, gridHHLqft_conjTranspose_zero (M := M) hM]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- For positive grid size, uncomputation resets every matching eigenphase label in a finite
eigenstate superposition to zero, preserving coefficients and the flag state. -/
theorem gridHHLUncompute_sum {D M : ℕ} (U : Operator D) (c : Fin D → ℂ)
    (χ : Fin D → QState (Fin D)) (k : Fin D → Fin M) (g : QState Bool) (hM : 0 < M)
    (hU : Uᴴ * U = 1)
    (hχ : ∀ i, U *ᵥ χ i = (primRoot M ^ ((k i).val : ℤ)) • χ i) :
    gridHHLUncompute (D := D) (M := M) U
        (∑ i, c i • TensorState (Ket (k i)) (χ i)) g
      = gridHHLWorkspaceState (D := D) (M := M)
          (∑ i, c i • TensorState (Ket (⟨0, hM⟩ : Fin M)) (χ i)) g := by
  have hws : gridHHLWorkspaceState (D := D) (M := M)
        (∑ i, c i • TensorState (Ket (k i)) (χ i)) g
      = ∑ i, c i • gridHHLWorkspaceState (D := D) (M := M) (TensorState (Ket (k i)) (χ i)) g := by
    funext p
    obtain ⟨a, flag, j⟩ := p
    simp only [gridHHLWorkspaceState_apply, Fintype.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [sum_mul_const]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hws' : gridHHLWorkspaceState (D := D) (M := M)
        (∑ i, c i • TensorState (Ket (⟨0, hM⟩ : Fin M)) (χ i)) g
      = ∑ i, c i • gridHHLWorkspaceState (D := D) (M := M)
          (TensorState (Ket (⟨0, hM⟩ : Fin M)) (χ i)) g := by
    funext p
    obtain ⟨a, flag, j⟩ := p
    simp only [gridHHLWorkspaceState_apply, Fintype.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [sum_mul_const]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hlin : gridHHLUncompute (D := D) (M := M) U
        (∑ i, c i • TensorState (Ket (k i)) (χ i)) g
      = ∑ i, c i • gridHHLUncompute (D := D) (M := M) U (TensorState (Ket (k i)) (χ i)) g := by
    simp only [gridHHLUncompute, hws, applyGate_sum, applyGate_sum]
  rw [hlin, hws']
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gridHHLUncompute_ket U (k i) (χ i) g hM hU (hχ i)]

/-- Multiplication on the left by a complex scalar distributes over a finite sum. -/
theorem mul_sum_const {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ℂ) (f : ι → ℂ) :
    a * ∑ i, f i = ∑ i, a * f i := by
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [← ih]
      ring

/-- Embedding a phase-data linear combination with a fixed flag state distributes over the
linear combination. -/
theorem gridHHLWorkspaceState_sum {D M : ℕ} (c : Fin D → ℂ)
    (ψ : Fin D → QState (Fin M × Fin D)) (g : QState Bool) :
    gridHHLWorkspaceState (D := D) (M := M) (∑ i, c i • ψ i) g
      = ∑ i, c i • gridHHLWorkspaceState (D := D) (M := M) (ψ i) g := by
  funext p
  obtain ⟨a, flag, j⟩ := p
  simp only [gridHHLWorkspaceState_apply, Fintype.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [sum_mul_const]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Applying a matrix only to the phase coordinate equals applying its tensor product with the
data identity. -/
theorem gridHHLPhaseOnly_eq_tensorGate {D M : ℕ} (Q : Matrix (Fin M) (Fin M) ℂ)
    (φ : QState (Fin M × Fin D)) :
    gridHHLPhaseOnly (D := D) (M := M) Q φ
      = ApplyGate (TensorGate (I := Fin M) (J := Fin D) Q (1 : Matrix (Fin D) (Fin D) ℂ)) φ := by
  funext p
  obtain ⟨a, i⟩ := p
  show ApplyGate Q (fun a' => φ (a', i)) a
    = ApplyGate (TensorGate (I := Fin M) (J := Fin D) Q (1 : Matrix (Fin D) (Fin D) ℂ)) φ (a, i)
  rw [applyGate_tensorGate_pair]

/-- For positive grid size, the phase-only Fourier transform of zero phase tensored with a data
state gives uniform phase amplitudes times that state. -/
theorem gridHHLPhaseOnly_qft_uniform {D M : ℕ} (hM : 0 < M) (χ : QState (Fin D)) :
    gridHHLPhaseOnly (D := D) (M := M) (QFTMatrix M) (TensorState (Ket (⟨0, hM⟩ : Fin M)) χ)
      = fun p => (Real.sqrt (M : ℝ) : ℂ)⁻¹ * χ p.2 := by
  funext p
  obtain ⟨a, i⟩ := p
  have h0 : PhaseState M 0 = fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹ := by
    funext b
    rw [phaseState_apply]
    have hz : ((0 : ℕ) : ℤ) * (b.val : ℤ) = 0 := by ring
    rw [hz, zpow_zero, mul_one]
  have hs : (fun a' : Fin M => (Ket (⟨0, hM⟩ : Fin M) a') * χ i)
      = χ i • Ket (⟨0, hM⟩ : Fin M) := by
    funext a'
    show (Ket (⟨0, hM⟩ : Fin M) a') * χ i = χ i * (Ket (⟨0, hM⟩ : Fin M) a')
    ring
  show ApplyGate (QFTMatrix M) (fun a' => (Ket (⟨0, hM⟩ : Fin M) a') * χ i) a
    = (Real.sqrt (M : ℝ) : ℂ)⁻¹ * χ i
  rw [hs, gridHHL_applyGate_state_smul, gridHHLqft_ket, h0]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- For positive grid size and unitary `V`, forward phase estimation attaches each grid label to
its eigenvector component and preserves the false flag state. -/
theorem gridHHLForwardReadout {D M : ℕ} (hM : 0 < M) (V : Operator D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (label : Fin D → Fin M) (b : QState (Fin D)) :
    Run 1 (gridHHLQPEBlock (M := M) (gridHHLOracle label V))
      (TensorState (Ket (⟨0, hM⟩ : Fin M)) (TensorState (Ket (false : Bool)) b))
      = gridHHLWorkspaceState (D := D) (M := M)
          (∑ i, (Vᴴ *ᵥ b) i • TensorState (Ket (label i)) (V *ᵥ Ket i)) (Ket (false : Bool)) := by
  have h1 : ApplyGate (gridHHLFourier (D := D) (M := M) (QFTMatrix M))
      (TensorState (Ket (⟨0, hM⟩ : Fin M)) (TensorState (Ket (false : Bool)) b))
      = gridHHLWorkspaceState (D := D) (M := M)
          (TensorState (fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹) b) (Ket (false : Bool)) := by
    have hrec : TensorState (Ket (⟨0, hM⟩ : Fin M)) (TensorState (Ket (false : Bool)) b)
        = gridHHLWorkspaceState (D := D) (M := M) (TensorState (Ket (⟨0, hM⟩ : Fin M)) b)
            (Ket (false : Bool)) := by
      funext p
      obtain ⟨a, flag, i⟩ := p
      show (TensorState (Ket (⟨0, hM⟩ : Fin M)) (TensorState (Ket (false : Bool)) b)) (a, (flag, i))
        = (TensorState (Ket (⟨0, hM⟩ : Fin M)) b) (a, i) * (Ket (false : Bool)) flag
      simp only [TensorState]
      ring
    rw [hrec, gridHHLFourier_apply, gridHHLPhaseOnly_qft_uniform hM]
    funext p
    obtain ⟨a, flag, i⟩ := p
    simp only [gridHHLWorkspaceState_apply, TensorState, Ket]
  have hA : ControlledPowers (gridHHLOracle label V) M *ᵥ
        (∑ i, (Vᴴ *ᵥ b) i •
          TensorState (fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹) (V *ᵥ Ket i))
      = ∑ i, (Vᴴ *ᵥ b) i • TensorState (PhaseState M (label i).val) (V *ᵥ Ket i) := by
    rw [mulVec_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [mulVec_smul, controlledPowers_kickback (gridHHLOracle_mulVec_column label V hV i)]
  have hB : ControlledPowers (gridHHLOracle label V) M *ᵥ
        (TensorState (fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹) b)
      = ∑ i, (Vᴴ *ᵥ b) i • TensorState (PhaseState M (label i).val) (V *ᵥ Ket i) := by
    have hexp : TensorState (fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹) b
        = ∑ i, (Vᴴ *ᵥ b) i •
            TensorState (fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹) (V *ᵥ Ket i) := by
      funext p
      obtain ⟨a, j⟩ := p
      have hb : b j = ∑ i, (Vᴴ *ᵥ b) i * (V *ᵥ Ket i) j := by
        have h := congrArg (fun z : QState (Fin D) => z j)
          (gridHHL_eigen_expansion (D := D) (M := M) V hV b)
        simpa only [Fintype.sum_apply, Pi.smul_apply, smul_eq_mul] using h
      simp only [TensorState, Fintype.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [hb, mul_sum_const]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hexp]
    exact hA
  have h2 : ApplyGate (gridHHLPowers (D := D) (M := M) (gridHHLOracle label V))
      (gridHHLWorkspaceState (D := D) (M := M)
        (TensorState (fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹) b) (Ket (false : Bool)))
      = gridHHLWorkspaceState (D := D) (M := M)
          (∑ i, (Vᴴ *ᵥ b) i • TensorState (PhaseState M (label i).val) (V *ᵥ Ket i))
          (Ket (false : Bool)) := by
    rw [gridHHLPowers_apply, hB]
  have h3 : gridHHLPhaseOnly (D := D) (M := M) (QFTMatrix M)ᴴ
      (∑ i, (Vᴴ *ᵥ b) i • TensorState (PhaseState M (label i).val) (V *ᵥ Ket i))
      = ∑ i, (Vᴴ *ᵥ b) i • TensorState (Ket (label i)) (V *ᵥ Ket i) := by
    rw [← hA, gridHHLPhaseOnly_eq_tensorGate]
    exact qpe_exact_readout_linear M hM (gridHHLOracle label V) (fun i => (Vᴴ *ᵥ b) i)
      (fun i => V *ᵥ Ket i) label (gridHHLOracle_mulVec_column label V hV)
  simp only [gridHHLQPEBlock, Run]
  rw [h1, h2, gridHHLFourier_apply, h3]

/-- On a workspace state with a false flag, the lifted flag rotation produces sine-weighted true
amplitudes and cosine-weighted false amplitudes. -/
theorem gridHHLFlag_workspace {D M : ℕ} (c : ℝ) (φ : QState (Fin M × Fin D)) (a : Fin M)
    (i : Fin D) :
    ApplyGate (gridHHLFlag (D := D) (M := M) c)
        (gridHHLWorkspaceState (D := D) (M := M) φ (Ket (false : Bool))) (a, (true, i))
      = (gridHHLSin M c a) * φ (a, i)
    ∧ ApplyGate (gridHHLFlag (D := D) (M := M) c)
        (gridHHLWorkspaceState (D := D) (M := M) φ (Ket (false : Bool))) (a, (false, i))
      = (gridHHLCos M c a) * φ (a, i) := by
  obtain ⟨h1, h2⟩ := gridHHLFlag_apply c (gridHHLWorkspaceState (D := D) (M := M) φ
    (Ket (false : Bool))) a i
  refine ⟨?_, ?_⟩
  · rw [h2, gridHHLWorkspaceState_apply, gridHHLWorkspaceState_apply]
    simp [Ket]
  · rw [h1, gridHHLWorkspaceState_apply, gridHHLWorkspaceState_apply]
    simp [Ket]

/-- A finite sum of pointwise sums of complex numbers equals the sum of the two finite sums. -/
theorem sum_add_distrib {ι : Type*} [Fintype ι] (f g : ι → ℂ) :
    (∑ i, (f i + g i)) = (∑ i, f i) + ∑ i, g i := by
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi]; rw [ih]; ring

/-- Applying a gate preserves addition of states. -/
theorem applyGate_add {I : Type*} [Fintype I] [DecidableEq I] (Q : Matrix I I ℂ) (x y : QState I) :
    ApplyGate Q (x + y) = ApplyGate Q x + ApplyGate Q y := by
  funext p
  show ∑ q, Q p q * (x q + y q) = ∑ q, Q p q * x q + ∑ q, Q p q * y q
  calc (∑ q, Q p q * (x q + y q)) = ∑ q, (Q p q * x q + Q p q * y q) := by
        exact Finset.sum_congr rfl fun q _ => by ring
    _ = (∑ q, Q p q * x q) + ∑ q, Q p q * y q := sum_add_distrib _ _

/-- Running a circuit with a fixed oracle preserves addition of input states. -/
theorem Run_add {I : Type*} [Fintype I] [DecidableEq I] (o : Matrix I I ℂ) (C : Circuit I) :
    ∀ (x y : QState I), Run o C (x + y) = Run o C x + Run o C y := by
  induction C with
  | nil => intro x y; rfl
  | cons s C ih =>
      intro x y
      cases s with
      | query => simp only [Run, applyGate_add, ih]
      | gate U => simp only [Run, applyGate_add, ih]

/-- A phase-dependent multiplier can be evaluated at the selected index inside a scalar
equality-indicator term. -/
theorem mul_selector' {M : ℕ} (d : Fin M → ℂ) (c x : ℂ) (a i : Fin M) :
    d a * (c * ((if a = i then (1 : ℂ) else 0) * x))
      = c * d i * ((if a = i then (1 : ℂ) else 0) * x) := by
  by_cases h : a = i
  · simp [h, mul_comm, mul_left_comm]
  · simp [h]

/-- Multiplying a grid-labeled eigenstate expansion by a phase-register weight multiplies each
eigenvector coefficient by the weight at its grid label. -/
theorem tensorState_sum_mul_phase {D M : ℕ} (label : Fin D → Fin M) (V : Operator D)
    (b : QState (Fin D)) (w : Fin M → ℂ) :
    (fun p => w p.1 * ((∑ i, (Vᴴ *ᵥ b) i • TensorState (Ket (label i)) (V *ᵥ Ket i)) p))
      = ∑ i, ((Vᴴ *ᵥ b) i * w (label i)) • TensorState (Ket (label i)) (V *ᵥ Ket i) := by
  funext p
  simp only [Fintype.sum_apply, Pi.smul_apply, TensorState, Ket, smul_eq_mul]
  rw [mul_sum_const]
  exact Finset.sum_congr rfl fun i _ => by
    show w p.1 * ((Vᴴ *ᵥ b) i * ((if p.1 = label i then 1 else 0) * (V *ᵥ Ket i) p.2))
      = (Vᴴ *ᵥ b) i * w (label i) * ((if p.1 = label i then 1 else 0) * (V *ᵥ Ket i) p.2)
    exact mul_selector' w ((Vᴴ *ᵥ b) i) ((V *ᵥ Ket i) p.2) p.1 (label i)

/-- The flag rotation on a false-flag workspace state splits into a cosine-weighted false branch
and a sine-weighted true branch. -/
theorem gridHHLFlag_decompose {D M : ℕ} (c : ℝ) (φ : QState (Fin M × Fin D)) :
    ApplyGate (gridHHLFlag (D := D) (M := M) c)
        (gridHHLWorkspaceState (D := D) (M := M) φ (Ket (false : Bool)))
      = gridHHLWorkspaceState (D := D) (M := M) (fun p => ((gridHHLCos M c p.1 : ℂ) * φ p)) (Ket (false : Bool))
        + gridHHLWorkspaceState (D := D) (M := M) (fun p => ((gridHHLSin M c p.1 : ℂ) * φ p)) (Ket (true : Bool)) := by
  funext p
  obtain ⟨a, flag, i⟩ := p
  obtain ⟨h1, h2⟩ := gridHHLFlag_apply c
    (gridHHLWorkspaceState (D := D) (M := M) φ (Ket (false : Bool))) a i
  cases flag
  · rw [h1]
    simp [gridHHLWorkspaceState_apply, Pi.add_apply, Ket]
  · rw [h2]
    simp [gridHHLWorkspaceState_apply, Pi.add_apply, Ket]

/-- For positive grid size and unitary `V`, the grid HHL circuit resets the phase register to
zero and splits the spectral input into cosine-weighted false and sine-weighted true flag
branches. -/
theorem gridHHLRun_workspace {D M : ℕ} (hM : 0 < M) (label : Fin D → Fin M) (V : Operator D)
    (c : ℝ) (b : QState (Fin D)) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    Run 1 (gridHHLCircuit (D := D) (M := M) label V c)
      (TensorState (Ket (⟨0, hM⟩ : Fin M)) (TensorState (Ket (false : Bool)) b))
      = gridHHLWorkspaceState (D := D) (M := M)
          (∑ i, ((Vᴴ *ᵥ b) i * (gridHHLCos M c (label i) : ℂ))
            • TensorState (Ket (⟨0, hM⟩ : Fin M)) (V *ᵥ Ket i)) (Ket (false : Bool))
        + gridHHLWorkspaceState (D := D) (M := M)
          (∑ i, ((Vᴴ *ᵥ b) i * (gridHHLSin M c (label i) : ℂ))
            • TensorState (Ket (⟨0, hM⟩ : Fin M)) (V *ᵥ Ket i)) (Ket (true : Bool)) := by
  have hOrt : gridHHLOracle label V ∈ Matrix.unitaryGroup (Fin D) ℂ :=
    (grid_hhl_spectral_matrix_and_oracle_unitary D M label V hM hV).2.2
  have hU : (gridHHLOracle label V)ᴴ * (gridHHLOracle label V) = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hOrt
    rwa [Matrix.star_eq_conjTranspose] at h
  have hstep : ∀ (ψ : QState (Fin M × Fin D)) (g : QState Bool),
      Run 1 (gridHHLQPEBlockInv (M := M) (gridHHLOracle label V))
          (gridHHLWorkspaceState (D := D) (M := M) ψ g)
        = gridHHLUncompute (D := D) (M := M) (gridHHLOracle label V) ψ g := by
    intro ψ g
    simp only [gridHHLQPEBlockInv, Run, gridHHLUncompute]
  rw [show Run 1 (gridHHLCircuit (D := D) (M := M) label V c)
        (TensorState (Ket (⟨0, hM⟩ : Fin M)) (TensorState (Ket (false : Bool)) b))
      = Run 1 (gridHHLQPEBlockInv (M := M) (gridHHLOracle label V))
        (ApplyGate (gridHHLFlag (D := D) (M := M) c)
          (Run 1 (gridHHLQPEBlock (M := M) (gridHHLOracle label V))
            (TensorState (Ket (⟨0, hM⟩ : Fin M)) (TensorState (Ket (false : Bool)) b))))
      by simp only [gridHHLCircuit, gridHHLQPEBlock, gridHHLQPEBlockInv,
        List.cons_append, List.nil_append, Run]]
  rw [gridHHLForwardReadout hM V hV label b, gridHHLFlag_decompose c]
  rw [tensorState_sum_mul_phase label V b (fun j => (gridHHLCos M c j : ℂ))]
  rw [tensorState_sum_mul_phase label V b (fun j => (gridHHLSin M c j : ℂ))]
  rw [Run_add, hstep, hstep]
  exact congrArg₂ (· + ·)
    (gridHHLUncompute_sum (gridHHLOracle label V)
      (fun i => (Vᴴ *ᵥ b) i * (gridHHLCos M c (label i) : ℂ))
      (fun i => V *ᵥ Ket i) label (Ket (false : Bool)) hM hU
      (gridHHLOracle_mulVec_column label V hV))
    (gridHHLUncompute_sum (gridHHLOracle label V)
      (fun i => (Vᴴ *ᵥ b) i * (gridHHLSin M c (label i) : ℂ))
      (fun i => V *ᵥ Ket i) label (Ket (true : Bool)) hM hU
      (gridHHLOracle_mulVec_column label V hV))

/-- A finite sum weighted by the equality indicator with fixed index on the left selects the
summand at that index. -/
theorem gridHHL_selector_sum' {I : Type*} [Fintype I] [DecidableEq I] (i : I) (g : I → ℂ) :
    (∑ x, g x * (if i = x then (1 : ℂ) else 0)) = g i := by
  have h : (∑ x, g x * (if i = x then (1 : ℂ) else 0)) = g i * 1 := by
    rw [Finset.sum_eq_single i (f := fun x => g x * (if i = x then 1 else 0))]
    · simp
    · intro x _ hx
      by_cases h : i = x
      · exact absurd h.symm hx
      · rw [if_neg h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  simp only [mul_one] at h
  exact h

/-- Scalar multiplication of a state evaluates pointwise as multiplication of its amplitude. -/
theorem smul_apply' {I : Type*} (c : ℂ) (f : QState I) (i : I) : (c • f) i = c * f i := rfl

/-- Scalar multiplication of a state is the function obtained by multiplying every amplitude by
the scalar. -/
theorem smul_def' {I : Type*} (c : ℂ) (f : QState I) : c • f = fun i => c * f i := rfl

/-- Scalar multiplication distributes over a finite sum of states. -/
theorem smul_sum {ι I : Type*} [Fintype ι] (c : ℂ) (ψ : ι → QState I) :
    c • (∑ i, ψ i) = ∑ i, c • ψ i := by
  funext j
  rw [smul_apply', Fintype.sum_apply, mul_sum_const]
  simp only [Fintype.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- A diagonal matrix applied to a vector is the sum of basis states weighted by the diagonal
entries times the vector coordinates. -/
theorem mulVec_diagonal {D : ℕ} (d : Fin D → ℂ) (w : QState (Fin D)) :
    Matrix.diagonal d *ᵥ w = ∑ i, (d i * w i) • Ket i := by
  funext j
  simp only [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, Fintype.sum_apply,
    smul_apply', Ket]
  rw [Finset.sum_eq_single j]
  · simp only [if_true]
    exact (gridHHL_selector_sum' j (fun x => d x * w x)).symm
  · intro i _ h
    rw [if_neg (Ne.symm h)]
    ring
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- For positive grid size, applying the spectral reciprocal gives the column expansion weighted
by reciprocal grid values and the coefficients of `Vᴴ *ᵥ b`. -/
theorem gridHHLReciprocal_mulVec {D M : ℕ} (hM : 0 < M) (label : Fin D → Fin M)
    (V : Operator D) (b : QState (Fin D)) :
    gridHHLReciprocal label V *ᵥ b
      = ∑ i, ((Vᴴ *ᵥ b) i * (gridHHLReciprocalScale M label i)) • (V *ᵥ Ket i) := by
  rw [gridHHLReciprocal, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    mulVec_diagonal (gridHHLReciprocalScale M label) (Vᴴ *ᵥ b),
    matrix_mulVec_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Fintype.sum_apply, smul_apply']
  simp only [Ket]
  rw [gridHHL_selector_sum' i]
  simp only [smul_def']
  funext i'
  ring

/-- The reciprocal flag sine amplitude is the rotation scale times the guarded reciprocal grid
value. -/
theorem gridHHLSin_reciprocalScale {D M : ℕ} (c : ℝ) (label : Fin D → Fin M) (i : Fin D) :
    (gridHHLSin M c (label i) : ℂ) = (c : ℂ) * (gridHHLReciprocalScale M label i) := by
  by_cases h : (label i).val = 0
  · rw [gridHHLSin, gridHHLReciprocalScale, if_pos h, if_pos h]
    simp
  · rw [gridHHLSin, gridHHLReciprocalScale, if_neg h, if_neg h]
    push_cast
    have hne : ((label i).val : ℂ) ≠ 0 := by exact_mod_cast h
    field_simp

/-- For positive grid size and unitary `V`, the sine-weighted eigenvector expansion is the
rotation scale times the matrix pseudoinverse applied to the input. -/
theorem gridHHLSin_mulVec {D M : ℕ} (hM : 0 < M) (label : Fin D → Fin M) (V : Operator D)
    (c : ℝ) (b : QState (Fin D)) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    (c : ℂ) • (matrixPseudoinverse (gridHHLMatrix label V) *ᵥ b)
      = ∑ i, ((Vᴴ *ᵥ b) i * ((gridHHLSin M c (label i)) : ℂ)) • (V *ᵥ Ket i) := by
  rw [← grid_hhl_spectral_reciprocal_eq_pseudoinverse hM label V hV,
    gridHHLReciprocal_mulVec hM label V b, smul_sum]
  ext j
  simp only [Fintype.sum_apply, smul_apply']
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gridHHLSin_reciprocalScale c label i]
  ring

/-- For positive grid size and unitary `V`, the true-flag output at zero phase is the scaled
pseudoinverse state, and every amplitude at nonzero phase vanishes. -/
theorem gridHHLRun_pointwise {D M : ℕ} (hM : 0 < M) (label : Fin D → Fin M) (V : Operator D)
    (c : ℝ) (b : QState (Fin D)) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    (∀ a i, (Run (1 : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ)
        (gridHHLCircuit (D := D) (M := M) label V c)
        (TensorState (Ket (⟨0, hM⟩ : Fin M)) (TensorState (Ket (false : Bool)) b))) (a, (true, i))
        = if a.val = 0 then ((c : ℂ) • (matrixPseudoinverse (gridHHLMatrix label V) *ᵥ b)) i else 0)
      ∧ (∀ a flag i, a.val ≠ 0 →
        (Run (1 : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ)
          (gridHHLCircuit (D := D) (M := M) label V c)
          (TensorState (Ket (⟨0, hM⟩ : Fin M)) (TensorState (Ket (false : Bool)) b)))
          (a, (flag, i)) = 0) := by
  have hrun := gridHHLRun_workspace hM label V c b hV
  have hsin : ∀ (a : Fin M) (j : Fin D), a = (⟨0, hM⟩ : Fin M) →
      (∑ k, (Vᴴ *ᵥ b) k * ((gridHHLSin M c (label k)) : ℂ) * ((V *ᵥ Ket k) j))
        = ((c : ℂ) • (matrixPseudoinverse (gridHHLMatrix label V) *ᵥ b)) j := by
    intro a j ha
    subst ha
    have hpt : ∀ (j : Fin D),
        ((c : ℂ) • (matrixPseudoinverse (gridHHLMatrix label V) *ᵥ b)) j
          = ∑ k, (Vᴴ *ᵥ b) k * ((gridHHLSin M c (label k)) : ℂ)
            * (V *ᵥ Ket k) j := by
      intro j
      have h := congrArg (fun z : QState (Fin D) => z j) (gridHHLSin_mulVec hM label V c b hV)
      simpa only [Fintype.sum_apply, smul_apply'] using h
    rw [hpt j]
  refine ⟨?_, ?_⟩
  · intro a i
    rw [hrun]
    simp only [gridHHLWorkspaceState_apply, Pi.add_apply, Ket,
      Fintype.sum_apply, Pi.smul_apply, TensorState]
    by_cases ha : a = (⟨0, hM⟩ : Fin M)
    · rw [if_pos (congrArg Fin.val ha)]
      simp [ha]
      rw [hsin a i ha]
      rfl
    · rw [if_neg (fun hval => ha (Fin.ext hval))]
      simp [ha]
  · intro a flag i ha
    rw [hrun]
    simp only [gridHHLWorkspaceState_apply, Pi.add_apply, Ket,
      Fintype.sum_apply, Pi.smul_apply, TensorState]
    have hz : a ≠ (⟨0, hM⟩ : Fin M) := by
      intro hc
      exact ha (by simpa using congrArg Fin.val hc)
    simp [hz]

/-- Under the unitary-frame and valid rotation-scale hypotheses, the grid HHL circuit resets
phase to zero and has successful amplitudes equal to the scaled pseudoinverse applied to the
input, realizing the reciprocal mechanism of [HarrowHassidimLloyd2009]. -/
theorem grid_hhl_uncompute_and_postselected_pseudoinverse {D M : ℕ} (hM : 0 < M)
    (label : Fin D → Fin M) (V : Operator D) (c : ℝ) (b : QState (Fin D))
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1 / (M : ℝ)) :
    let out := Run (1 : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ)
        (gridHHLCircuit (D := D) (M := M) label V c)
        (TensorState (Ket (⟨0, hM⟩ : Fin M)) (TensorState (Ket (false : Bool)) b))
    (∀ a i, out (a, (true, i))
        = if a.val = 0 then ((c : ℂ) • (matrixPseudoinverse (gridHHLMatrix label V) *ᵥ b)) i else 0)
      ∧ (∀ a flag i, a.val ≠ 0 → out (a, (flag, i)) = 0) :=
  gridHHLRun_pointwise hM label V c b hV

/-- Scaling a state by a real number multiplies its total Born mass by the square of that
number. -/
theorem measureProb_smul_real {I : Type*} [Fintype I] [DecidableEq I] (c : ℝ) (ψ : QState I) :
    MeasureProb ((c : ℂ) • ψ) Finset.univ = c ^ 2 * MeasureProb ψ Finset.univ := by
  have h := measureProb_smul (c : ℂ) ψ Finset.univ
  rwa [Complex.norm_real, Real.norm_eq_abs, sq_abs] at h

/-- The total Born mass of all workspace amplitudes whose flag is true. -/
noncomputable def gridHHLFlagBorn {D M : ℕ} (w : QState (Fin M × (Bool × Fin D))) : ℝ :=
  ∑ a, ∑ i, ‖w (a, (true, i))‖ ^ 2

/-- The data-state slice of a workspace state at zero phase and true flag. -/
noncomputable def gridHHLSuccessBlock {D M : ℕ} (hM : 0 < M)
    (w : QState (Fin M × (Bool × Fin D))) : QState (Fin D) :=
  fun i => w ((⟨0, hM⟩ : Fin M), (true, i))

/-- For a positive grid size, the true-flag Born mass obtained by running the grid HHL circuit
from zero phase and false flag. -/
noncomputable def gridHHLProbabilityAux {D M : ℕ} (hM : 0 < M) (label : Fin D → Fin M)
    (V : Operator D) (c : ℝ) (b : QState (Fin D)) : ℝ :=
  gridHHLFlagBorn (Run (1 : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ)
    (gridHHLCircuit (D := D) (M := M) label V c)
    (TensorState (Ket (⟨0, hM⟩ : Fin M)) (TensorState (Ket (false : Bool)) b)))

/-- The grid HHL true-flag Born mass, defined to be zero when the grid size is zero. -/
noncomputable def gridHHLProbability {D M : ℕ} (label : Fin D → Fin M) (V : Operator D)
    (c : ℝ) (b : QState (Fin D)) : ℝ :=
  if h : 0 < M then gridHHLProbabilityAux h label V c b else 0

/-- For a positive grid size, the optional conditional state of the zero-phase, true-flag output
slice of the grid HHL circuit. -/
noncomputable def gridHHLOutputAux {D M : ℕ} (hM : 0 < M) (label : Fin D → Fin M)
    (V : Operator D) (c : ℝ) (b : QState (Fin D)) : Option (QState (Fin D)) :=
  ConditionalState (gridHHLSuccessBlock hM
    (Run (1 : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ)
      (gridHHLCircuit (D := D) (M := M) label V c)
      (TensorState (Ket (⟨0, hM⟩ : Fin M)) (TensorState (Ket (false : Bool)) b))))

/-- The optional conditional grid HHL output, defined to be absent when the grid size is zero. -/
noncomputable def gridHHLOutput {D M : ℕ} (label : Fin D → Fin M) (V : Operator D)
    (c : ℝ) (b : QState (Fin D)) : Option (QState (Fin D)) :=
  if h : 0 < M then gridHHLOutputAux h label V c b else none

/-- The sum of two finite real sums equals the finite sum of their pointwise sums. -/
theorem sum_add_two {ι : Type*} [Fintype ι] (f g : ι → ℝ) :
    (∑ i, f i) + ∑ i, g i = ∑ i, (f i + g i) := by
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, ih, add_assoc, add_left_comm, add_comm]

/-- Two finite sums of a real-valued function can be interchanged. -/
theorem sum_swap {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι → κ → ℝ) :
    (∑ a, ∑ b, f a b) = ∑ b, ∑ a, f a b := by
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha, ih]
      rw [sum_add_two]

/-- If all true-flag amplitudes are supported at zero phase and equal `c` times a data state
there, their total Born mass is `c²` times the data-state mass. -/
theorem gridHHLFlagBorn_eq_of {D M : ℕ} (hM : 0 < M)
    (w : QState (Fin M × (Bool × Fin D))) (v : QState (Fin D)) (c : ℝ)
    (h : ∀ a i, w (a, (true, i)) = if a.val = 0 then ((c : ℂ) • v) i else 0) :
    gridHHLFlagBorn w = c ^ 2 * MeasureProb v Finset.univ := by
  have hstep : ∀ (a : Fin M) (i : Fin D), ‖w (a, (true, i))‖ ^ 2
      = ‖(if a.val = 0 then ((c : ℂ) • v) i else 0)‖ ^ 2 := by
    intro a i
    rw [h a i]
  have h2 : (∑ (i : Fin D), ∑ (a : Fin M), ‖(if a.val = 0 then ((c : ℂ) • v) i else 0)‖ ^ 2)
      = ∑ (i : Fin D), ‖((c : ℂ) • v) i‖ ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single ⟨0, hM⟩]
    · show ‖(if (⟨0, hM⟩ : Fin M).val = 0 then ((c : ℂ) • v) i else 0)‖ ^ 2
        = ‖((c : ℂ) • v) i‖ ^ 2
      rw [if_pos (by rfl)]
    · intro a _ ha
      have hne : (a : Fin M).val ≠ 0 := by
        intro hz
        exact ha (Fin.ext hz)
      rw [if_neg hne]
      simp
    · intro h
      exact absurd (Finset.mem_univ (⟨0, hM⟩ : Fin M)) h
  unfold gridHHLFlagBorn
  simp_rw [hstep]
  rw [sum_swap, h2]
  calc ∑ i, ‖((c : ℂ) • v) i‖ ^ 2
      = MeasureProb ((c : ℂ) • v) Finset.univ := by
        unfold MeasureProb BornProb
        rfl
    _ = c ^ 2 * MeasureProb v Finset.univ := measureProb_smul_real c v

/-- For positive grid size and unitary `V`, the grid HHL true-flag Born mass is `c²` times the
total mass of the pseudoinverse applied to the input. -/
theorem gridHHLFlagBorn_eq {D M : ℕ} (hM : 0 < M) (label : Fin D → Fin M) (V : Operator D)
    (c : ℝ) (b : QState (Fin D)) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    gridHHLProbabilityAux hM label V c b
      = c ^ 2 * MeasureProb (matrixPseudoinverse (gridHHLMatrix label V) *ᵥ b) Finset.univ := by
  obtain ⟨hpt, -⟩ := gridHHLRun_pointwise hM label V c b hV
  unfold gridHHLProbabilityAux
  refine gridHHLFlagBorn_eq_of hM _ (matrixPseudoinverse (gridHHLMatrix label V) *ᵥ b) c ?_
  exact hpt

/-- Multiplication by a positive real scalar leaves the post-measurement state for the full
outcome set unchanged. -/
theorem postMeasure_smul {I : Type*} [Fintype I] [DecidableEq I] {c : ℝ} (hc : 0 < c)
    (ψ : QState I) : PostMeasure ((c : ℂ) • ψ) Finset.univ = PostMeasure ψ Finset.univ := by
  have hP : 0 ≤ MeasureProb ψ Finset.univ := measureProb_nonneg ψ _
  have hne : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hkey : (Real.sqrt (MeasureProb ((c : ℂ) • ψ) Finset.univ) : ℂ)
      = (c : ℂ) * (Real.sqrt (MeasureProb ψ Finset.univ) : ℂ) := by
    have h1 : Real.sqrt (MeasureProb ((c : ℂ) • ψ) Finset.univ)
        = Real.sqrt (c ^ 2 * MeasureProb ψ Finset.univ) := by
      rw [measureProb_smul_real]
    have hz : 0 ≤ c * Real.sqrt (MeasureProb ψ Finset.univ) :=
      mul_nonneg hc.le (Real.sqrt_nonneg _)
    rw [h1]
    rw [show c ^ 2 * MeasureProb ψ Finset.univ
        = (c * Real.sqrt (MeasureProb ψ Finset.univ)) ^ 2 by
          rw [mul_pow, Real.sq_sqrt hP]]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hz]
    exact Complex.ofReal_mul c (Real.sqrt (MeasureProb ψ Finset.univ))
  funext i
  have hcol : Collapse ((c : ℂ) • ψ) Finset.univ i
      = (c : ℂ) * Collapse ψ Finset.univ i := by
    rw [collapse_apply, collapse_apply]
    simp
  rw [PostMeasure, PostMeasure, hkey, hcol]
  calc ((c : ℂ) * (Real.sqrt (MeasureProb ψ Finset.univ) : ℂ))⁻¹
          * ((c : ℂ) * Collapse ψ Finset.univ i)
      = (c : ℂ)⁻¹ * ((Real.sqrt (MeasureProb ψ Finset.univ) : ℂ)⁻¹
          * ((c : ℂ) * Collapse ψ Finset.univ i)) := by
        rw [_root_.mul_inv_rev]
        ring
    _ = (Real.sqrt (MeasureProb ψ Finset.univ) : ℂ)⁻¹ * Collapse ψ Finset.univ i := by
      have e1 : (c : ℂ)⁻¹ * ((Real.sqrt (MeasureProb ψ Finset.univ) : ℂ)⁻¹
            * ((c : ℂ) * Collapse ψ Finset.univ i))
          = ((c : ℂ)⁻¹ * (c : ℂ))
            * ((Real.sqrt (MeasureProb ψ Finset.univ) : ℂ)⁻¹ * Collapse ψ Finset.univ i) := by
        ring
      rw [e1, inv_mul_cancel₀ hne, one_mul]

/-- Multiplication by a positive real scalar leaves the optional conditional state unchanged. -/
theorem conditionalState_smul {I : Type*} [Fintype I] [DecidableEq I] {c : ℝ} (hc : 0 < c)
    (ψ : QState I) : ConditionalState ((c : ℂ) • ψ) = ConditionalState ψ := by
  have hP : 0 ≤ MeasureProb ψ Finset.univ := measureProb_nonneg ψ _
  have hm : MeasureProb ((c : ℂ) • ψ) Finset.univ
      = c ^ 2 * MeasureProb ψ Finset.univ := measureProb_smul_real c ψ
  by_cases h : 0 < MeasureProb ψ Finset.univ
  · have h2 : 0 < MeasureProb ((c : ℂ) • ψ) Finset.univ := by
      rw [hm]
      positivity
    simp only [ConditionalState, if_pos h, if_pos h2]
    rw [postMeasure_smul hc ψ]
  · have hz : MeasureProb ψ Finset.univ = 0 := le_antisymm (le_of_not_gt h) hP
    simp only [ConditionalState]
    rw [hm, hz, mul_zero]
    simp

/-- Under the exact-grid unitary and rotation hypotheses, success mass is `c²` times the
pseudoinverse-state mass; for positive `c` the output is its conditional state, and for zero
`c` the output is absent. This computes the reciprocal-eigenvalue output mechanism of
[HarrowHassidimLloyd2009]. -/
theorem grid_hhl_actual_probability_and_output {D M : ℕ} (label : Fin D → Fin M) (V : Operator D)
    (c : ℝ) (b : QState (Fin D)) (hM : 0 < M) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1 / (M : ℝ)) :
    let v := matrixPseudoinverse (gridHHLMatrix label V) *ᵥ b
    gridHHLProbability label V c b = c ^ 2 * MeasureProb v Finset.univ ∧
    (0 < c → gridHHLOutput label V c b = ConditionalState v) ∧
    (c = 0 → gridHHLOutput label V c b = none) := by
  have hprob : gridHHLProbability label V c b
      = c ^ 2 * MeasureProb (matrixPseudoinverse (gridHHLMatrix label V) *ᵥ b) Finset.univ := by
    rw [gridHHLProbability, dif_pos hM]
    exact gridHHLFlagBorn_eq hM label V c b hV
  have hsucc : gridHHLSuccessBlock hM
      (Run (1 : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ)
        (gridHHLCircuit (D := D) (M := M) label V c)
        (TensorState (Ket (⟨0, hM⟩ : Fin M)) (TensorState (Ket (false : Bool)) b)))
      = (c : ℂ) • (matrixPseudoinverse (gridHHLMatrix label V) *ᵥ b) := by
    obtain ⟨hpt, -⟩ := gridHHLRun_pointwise hM label V c b hV
    funext i
    simp only [gridHHLSuccessBlock]
    have h := hpt (⟨0, hM⟩ : Fin M) i
    simp only at h
    rw [h]
    simp
  refine ⟨hprob, ?_, ?_⟩
  · intro hc
    rw [gridHHLOutput, dif_pos hM, gridHHLOutputAux, hsucc, conditionalState_smul hc]
  · intro hc
    obtain ⟨hpt, -⟩ := gridHHLRun_pointwise hM label V 0 b hV
    have hz : gridHHLSuccessBlock hM
        (Run (1 : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ)
          (gridHHLCircuit (D := D) (M := M) label V 0)
          (TensorState (Ket (⟨0, hM⟩ : Fin M)) (TensorState (Ket (false : Bool)) b)))
        = 0 := by
      funext i
      simp only [gridHHLSuccessBlock]
      have h := hpt (⟨0, hM⟩ : Fin M) i
      simp only at h
      rw [h]
      simp
    rw [gridHHLOutput, dif_pos hM, hc, gridHHLOutputAux, hz, conditionalState_zero]

/-- Every grid eigenvalue has complex norm at most one when the grid size is positive. -/
theorem gridHHLScale_norm_le {D M : ℕ} (hM : 0 < M) (label : Fin D → Fin M) (i : Fin D) :
    ‖(gridHHLScale M label i : ℂ)‖ ≤ 1 := by
  have h2 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hA : ‖((label i).val : ℂ)‖ = ((label i).val : ℝ) := by simp
  have hB : ‖(M : ℂ)‖ = (M : ℝ) := by simp
  rw [gridHHLScale, norm_div, hA, hB]
  refine (div_le_iff₀ h2).2 ?_
  simp only [one_mul]
  exact_mod_cast (label i).isLt.le

/-- For positive grid size and unitary `V`, applying the grid matrix does not increase the sum
of squared coordinate norms. -/
theorem gridHHLMatrix_contraction {D M : ℕ} (hM : 0 < M) (label : Fin D → Fin M)
    (V : Operator D) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (x : QState (Fin D)) :
    ∑ i, ‖(gridHHLMatrix label V *ᵥ x) i‖ ^ 2 ≤ ∑ i, ‖x i‖ ^ 2 := by
  have hstarV : Vᴴ ∈ Matrix.unitaryGroup (Fin D) ℂ := mem_unitaryGroup_adjoint hV
  have hpt : ∀ (i : Fin D) (z : QState (Fin D)),
      ‖(Matrix.diagonal (gridHHLScale M label) *ᵥ z) i‖ ^ 2
        = ‖(gridHHLScale M label i)‖ ^ 2 * ‖z i‖ ^ 2 := by
    intro i z
    have h1 : (Matrix.diagonal (gridHHLScale M label) *ᵥ z) i
        = gridHHLScale M label i * z i := by
      show ∑ j, (Matrix.diagonal (gridHHLScale M label) i j) * z j = _
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [Ne.symm hj]
      · intro h
        exact absurd (Finset.mem_univ i) h
    rw [h1, norm_mul]
    ring
  have hle : ∀ (i : Fin D) (z : QState (Fin D)),
      ‖(gridHHLScale M label i)‖ ^ 2 * ‖z i‖ ^ 2 ≤ ‖z i‖ ^ 2 := by
    intro i z
    have h1 := gridHHLScale_norm_le hM label i
    have h0 : 0 ≤ ‖(gridHHLScale M label i)‖ := norm_nonneg _
    have h1' : ‖(gridHHLScale M label i)‖ ^ 2 ≤ 1 := by nlinarith
    have h3 : 0 ≤ ‖z i‖ ^ 2 := sq_nonneg _
    simpa using mul_le_mul_of_nonneg_right h1' h3
  have hstep : gridHHLMatrix label V *ᵥ x
      = V *ᵥ (Matrix.diagonal (gridHHLScale M label) *ᵥ (Vᴴ *ᵥ x)) := by
    rw [gridHHLMatrix, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rfl
  rw [hstep]
  calc ∑ i, ‖(V *ᵥ (Matrix.diagonal (gridHHLScale M label) *ᵥ (Vᴴ *ᵥ x))) i‖ ^ 2
      = ∑ i, ‖(Matrix.diagonal (gridHHLScale M label) *ᵥ (Vᴴ *ᵥ x)) i‖ ^ 2 := by
        simpa only [Complex.normSq_eq_norm_sq] using
          sum_normSq_mulVec_of_mem_unitaryGroup hV _
    _ = ∑ i, ‖(gridHHLScale M label i)‖ ^ 2 * ‖(Vᴴ *ᵥ x) i‖ ^ 2 :=
        Finset.sum_congr rfl fun i _ => hpt i _
    _ ≤ ∑ i, ‖(Vᴴ *ᵥ x) i‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => hle i _
    _ = ∑ i, ‖x i‖ ^ 2 := by
        simpa only [Complex.normSq_eq_norm_sq] using
          sum_normSq_mulVec_of_mem_unitaryGroup hstarV x

/-- If the grid linear system has a solution, applying its matrix pseudoinverse to the
right-hand side also gives a solution, for positive grid size and unitary `V`. -/
theorem gridHHLMatrix_mulVec_pseudoinverse {D M : ℕ} (hM : 0 < M) (label : Fin D → Fin M)
    (V : Operator D) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (b x : QState (Fin D))
    (hx : gridHHLMatrix label V *ᵥ x = b) :
    gridHHLMatrix label V *ᵥ (matrixPseudoinverse (gridHHLMatrix label V) *ᵥ b) = b := by
  rw [← grid_hhl_spectral_reciprocal_eq_pseudoinverse hM label V hV,
    Matrix.mulVec_mulVec, gridHHLMatrix_mul_reciprocal hM label V hV, ← hx,
    Matrix.mulVec_mulVec, gridHHLRangeProjector_mul_matrix label V hV, hx]

/-- For positive grid size, unitary `V`, and `0 < c ≤ 1 / M`, a normalized consistent input has
success mass at least `c²`, strictly positive success, and a normalized conditional output. -/
theorem grid_hhl_consistent_input_derived_success {D M : ℕ} (label : Fin D → Fin M) (V : Operator D)
    (c : ℝ) (b : QState (Fin D)) :
    0 < M → V ∈ Matrix.unitaryGroup (Fin D) ℂ → 0 < c → c ≤ 1 / (M : ℝ) → Normalized b →
    (∃ x : QState (Fin D), gridHHLMatrix label V *ᵥ x = b) →
    c ^ 2 ≤ gridHHLProbability label V c b ∧ 0 < gridHHLProbability label V c b ∧
    ∃ φ, gridHHLOutput label V c b = some φ ∧ Normalized φ := by
  intro hM hV hc hc1 hnb hx
  obtain ⟨x, hxb⟩ := hx
  have hnb' : ∑ i, ‖b i‖ ^ 2 = 1 := hnb
  have hAv := gridHHLMatrix_mulVec_pseudoinverse hM label V hV b x hxb
  have hcontraction := gridHHLMatrix_contraction hM label V hV
    (matrixPseudoinverse (gridHHLMatrix label V) *ᵥ b)
  have h1 : (1 : ℝ) ≤
      (∑ i, ‖(matrixPseudoinverse (gridHHLMatrix label V) *ᵥ b) i‖ ^ 2) := by
    rw [hAv] at hcontraction
    rw [← hnb']
    exact hcontraction
  have hmpge : (1 : ℝ) ≤ MeasureProb (matrixPseudoinverse (gridHHLMatrix label V) *ᵥ b)
      Finset.univ := by
    unfold MeasureProb BornProb
    exact h1
  have hmp : 0 < MeasureProb (matrixPseudoinverse (gridHHLMatrix label V) *ᵥ b) Finset.univ :=
    lt_of_lt_of_le zero_lt_one hmpge
  have hout : gridHHLOutput label V c b
      = some (PostMeasure (matrixPseudoinverse (gridHHLMatrix label V) *ᵥ b) Finset.univ) := by
    have h4 := (grid_hhl_actual_probability_and_output label V c b hM hV hc.le hc1).2.1 hc
    rw [h4]
    simp only [ConditionalState, if_pos hmp]
  have hprob : gridHHLProbability label V c b
      = c ^ 2 * MeasureProb (matrixPseudoinverse (gridHHLMatrix label V) *ᵥ b) Finset.univ :=
    (grid_hhl_actual_probability_and_output label V c b hM hV hc.le hc1).1
  refine ⟨?_, ?_, ⟨PostMeasure (matrixPseudoinverse (gridHHLMatrix label V) *ᵥ b) Finset.univ,
    hout, normalized_postMeasure hmp⟩⟩
  · rw [hprob]
    have h2 : (0 : ℝ) ≤ c ^ 2 := sq_nonneg c
    nlinarith [hmpge]
  · rw [hprob]
    have h2 : (0 : ℝ) < c ^ 2 := sq_pos_of_pos hc
    nlinarith [hmpge]

/-- The zero state has total Born mass zero. -/
theorem measureProb_zero {I : Type*} [Fintype I] : MeasureProb (0 : QState I) Finset.univ = 0 := by
  simp [MeasureProb, BornProb]

/-- For positive grid size and unitary `V`, if every spectral label is zero then the matrix
pseudoinverse sends every input to zero. -/
theorem gridHHLReciprocal_zero_of_label_zero {D M : ℕ} (hM : 0 < M) (label : Fin D → Fin M)
    (V : Operator D) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (b : QState (Fin D))
    (hz : ∀ i, (label i).val = 0) :
    matrixPseudoinverse (gridHHLMatrix label V) *ᵥ b = 0 := by
  rw [← grid_hhl_spectral_reciprocal_eq_pseudoinverse hM label V hV,
    gridHHLReciprocal_mulVec hM label V b]
  apply Finset.sum_eq_zero
  intro i _
  have h1 : gridHHLReciprocalScale M label i = 0 := by
    rw [gridHHLReciprocalScale, if_pos (hz i)]
  rw [h1, mul_zero, smul_def']
  funext j
  simp only [Pi.zero_apply, zero_mul]

/-- For positive grid size and unitary `V`, zero rotation gives zero success mass and no output.
The same holds for every valid nonnegative rotation scale when all spectral labels are zero. -/
theorem grid_hhl_zero_spectrum_and_zero_rotation {D M : ℕ} (label : Fin D → Fin M)
    (V : Operator D) (b : QState (Fin D)) :
    0 < M → V ∈ Matrix.unitaryGroup (Fin D) ℂ →
    (gridHHLProbability label V 0 b = 0 ∧ gridHHLOutput label V 0 b = none) ∧
    (∀ c, 0 ≤ c → c ≤ 1 / (M : ℝ) → (∀ i, (label i).val = 0) →
      gridHHLProbability label V c b = 0 ∧ gridHHLOutput label V c b = none) := by
  intro hM hV
  have hzero0 : gridHHLSuccessBlock hM
      (Run (1 : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ)
        (gridHHLCircuit (D := D) (M := M) label V 0)
        (TensorState (Ket (⟨0, hM⟩ : Fin M)) (TensorState (Ket (false : Bool)) b)))
      = 0 := by
    obtain ⟨hpt, -⟩ := gridHHLRun_pointwise hM label V 0 b hV
    funext i
    simp only [gridHHLSuccessBlock]
    have h := hpt (⟨0, hM⟩ : Fin M) i
    simp only at h
    rw [h]
    simp
  have hzero : ∀ (c : ℝ), gridHHLSuccessBlock hM
      (Run (1 : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ)
        (gridHHLCircuit (D := D) (M := M) label V c)
        (TensorState (Ket (⟨0, hM⟩ : Fin M)) (TensorState (Ket (false : Bool)) b)))
      = (c : ℂ) • (matrixPseudoinverse (gridHHLMatrix label V) *ᵥ b) := by
    intro c
    obtain ⟨hpt, -⟩ := gridHHLRun_pointwise hM label V c b hV
    funext i
    simp only [gridHHLSuccessBlock]
    have h := hpt (⟨0, hM⟩ : Fin M) i
    simp only at h
    rw [h]
    simp
  constructor
  · have h1 := (grid_hhl_actual_probability_and_output label V 0 b hM hV (le_refl 0)
      (by positivity)).1
    have hz' : (0 : ℝ) ^ 2 = 0 := by ring
    rw [h1, hz', zero_mul]
    rw [gridHHLOutput, dif_pos hM, gridHHLOutputAux, hzero0, conditionalState_zero]
    simp
  · intro c hc0 hc1 hz
    have hnull : matrixPseudoinverse (gridHHLMatrix label V) *ᵥ b = 0 :=
      gridHHLReciprocal_zero_of_label_zero hM label V hV b hz
    have h1 := (grid_hhl_actual_probability_and_output label V c b hM hV hc0 hc1).1
    rw [h1, hnull, measureProb_zero, mul_zero]
    rw [gridHHLOutput, dif_pos hM, gridHHLOutputAux, hzero c, hnull, smul_zero,
      conditionalState_zero]
    simp

end Qatlib.Concepts.HhlAlgorithms.GridExactHHL
