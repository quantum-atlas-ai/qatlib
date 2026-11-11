/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.LCU
import Qatlib.Concepts.BlockEncoding.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Real.Sqrt
import Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding

/-!
# Linear combinations with complex coefficients

`coefficientMass`, `coefficientAmplitude`, and `coefficientPhase` separate finite complex
coefficients into normalized weights and phases. Absorbing phases into the selected unitaries
produces a block encoding of their linear combination with normalization equal to the sum of
coefficient norms.

A second construction places the phases in the right preparation frame. Orthogonal Boolean
preparation frames handle the case where all coefficients vanish.

For the block-encoding framework, see [GilyenSuLowWiebe2019].

## Main statements

* `coefficientLCU_blockEncoding`: encodes the weighted sum exactly when the coefficient mass is
  positive.
* `coefficientLCU_bilinear_projectedEncoding`: uses different left and right preparation
  amplitudes.
* `coefficientLCU_zero_blockEncoding`: handles zero coefficient mass with scale one.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option warningAsError false
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.LCU

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.BlockEncoding.EncodingCore

open Matrix
open scoped Matrix.Norms.L2Operator

variable {J I : Type*}

/-- The total mass of a finite complex coefficient family, defined as the sum of its coefficient
norms. -/
noncomputable def coefficientMass [Fintype J] (c : J → ℂ) : ℝ := ∑ j, ‖c j‖

/-- The nonnegative real amplitude given by the square root of a coefficient's norm divided by
the total mass, viewed in `ℂ`. -/
noncomputable def coefficientAmplitude [Fintype J] (c : J → ℂ) (j : J) : ℂ :=
  (Real.sqrt (‖c j‖ / coefficientMass c) : ℂ)

/-- The unit phase of a nonzero complex number, with phase one assigned to zero. -/
noncomputable def coefficientPhase (z : ℂ) : ℂ := if z = 0 then 1 else z / (‖z‖ : ℂ)

/-- Multiplies each selected matrix by the unit phase of its coefficient. -/
noncomputable def phaseAbsorbed (c : J → ℂ) (U : J → Matrix I I ℂ)
    (j : J) : Matrix I I ℂ := coefficientPhase (c j) • U j

/-- The coefficient phase assigned to zero is one. -/
@[simp] theorem coefficientPhase_zero : coefficientPhase 0 = 1 := by
  simp [coefficientPhase]

/-- The coefficient phase of every complex number has norm one. -/
theorem coefficientPhase_norm (z : ℂ) : ‖coefficientPhase z‖ = 1 := by
  by_cases hz : z = 0
  · simp [coefficientPhase, hz]
  · simp [coefficientPhase, hz, Complex.norm_real, norm_ne_zero_iff.mpr hz]

/-- The conjugate of a coefficient phase times that phase equals one. -/
theorem coefficientPhase_unit (z : ℂ) :
    star (coefficientPhase z) * coefficientPhase z = 1 := by
  have hn : Complex.normSq (coefficientPhase z) = 1 := by
    rw [Complex.normSq_eq_norm_sq, coefficientPhase_norm]
    norm_num
  have hc := congrArg (fun x : ℝ => (x : ℂ)) hn
  simpa only [Complex.normSq_eq_conj_mul_self, Complex.star_def,
    Complex.ofReal_one] using hc

/-- Multiplying a coefficient's norm by its phase recovers the coefficient. -/
theorem norm_mul_coefficientPhase (z : ℂ) :
    (‖z‖ : ℂ) * coefficientPhase z = z := by
  by_cases hz : z = 0
  · simp [hz]
  · have hn : (‖z‖ : ℂ) ≠ 0 := by
      exact_mod_cast (norm_ne_zero_iff.mpr hz)
    simp only [coefficientPhase, if_neg hz]
    field_simp

section Coefficients

variable [Fintype J]

/-- The total coefficient mass is nonnegative. -/
theorem coefficientMass_nonneg (c : J → ℂ) : 0 ≤ coefficientMass c :=
  Finset.sum_nonneg fun j _ => norm_nonneg (c j)

/-- The total coefficient mass vanishes exactly when every coefficient vanishes. -/
theorem coefficientMass_eq_zero_iff (c : J → ℂ) :
    coefficientMass c = 0 ↔ ∀ j, c j = 0 := by
  classical
  simp only [coefficientMass, Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => norm_nonneg (c j)), Finset.mem_univ, forall_const, norm_eq_zero]

/-- The total coefficient mass is positive exactly when at least one coefficient is nonzero. -/
theorem coefficientMass_pos_iff (c : J → ℂ) :
    0 < coefficientMass c ↔ ∃ j, c j ≠ 0 := by
  rw [lt_iff_le_and_ne]
  simp only [coefficientMass_nonneg, true_and]
  rw [ne_comm, ne_eq, coefficientMass_eq_zero_iff, not_forall]

/-- For positive total mass, the squared amplitude equals the coefficient norm divided by that
mass. -/
theorem coefficientAmplitude_weight (c : J → ℂ) (hα : 0 < coefficientMass c)
    (j : J) :
    star (coefficientAmplitude c j) * coefficientAmplitude c j =
      ((‖c j‖ / coefficientMass c : ℝ) : ℂ) := by
  simp only [coefficientAmplitude, Complex.star_def, Complex.conj_ofReal]
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (div_nonneg (norm_nonneg _) hα.le)]

/-- For positive total mass, the coefficient amplitudes have total squared magnitude one. -/
theorem coefficientAmplitude_normalized (c : J → ℂ) (hα : 0 < coefficientMass c) :
    ∑ j, star (coefficientAmplitude c j) * coefficientAmplitude c j = 1 := by
  simp_rw [coefficientAmplitude_weight c hα]
  have hr : ∑ j, ‖c j‖ / coefficientMass c = 1 := by
    rw [← Finset.sum_div]
    exact div_self hα.ne'
  exact_mod_cast hr

/-- The squared amplitude times its coefficient phase equals the coefficient divided by the
total mass. -/
theorem coefficientAmplitude_phase_factor (c : J → ℂ)
    (hα : 0 < coefficientMass c) (j : J) :
    (star (coefficientAmplitude c j) * coefficientAmplitude c j) *
        coefficientPhase (c j) = c j / (coefficientMass c : ℂ) := by
  rw [coefficientAmplitude_weight c hα, Complex.ofReal_div]
  calc
    (‖c j‖ : ℂ) / (coefficientMass c : ℂ) * coefficientPhase (c j) =
        ((‖c j‖ : ℂ) * coefficientPhase (c j)) / (coefficientMass c : ℂ) := by ring
    _ = _ := by rw [norm_mul_coefficientPhase]

/-- The right preparation amplitude obtained by multiplying the nonnegative coefficient
amplitude by its phase. -/
noncomputable def coefficientRightAmplitude (c : J → ℂ) (j : J) : ℂ :=
  coefficientAmplitude c j * coefficientPhase (c j)

/-- Including the coefficient phase leaves an amplitude's squared magnitude unchanged. -/
theorem coefficientRightAmplitude_weight (c : J → ℂ) (j : J) :
    star (coefficientRightAmplitude c j) * coefficientRightAmplitude c j =
      star (coefficientAmplitude c j) * coefficientAmplitude c j := by
  simp only [coefficientRightAmplitude, star_mul]
  calc
    star (coefficientPhase (c j)) * star (coefficientAmplitude c j) *
        (coefficientAmplitude c j * coefficientPhase (c j)) =
      (star (coefficientAmplitude c j) * coefficientAmplitude c j) *
        (star (coefficientPhase (c j)) * coefficientPhase (c j)) := by ring
    _ = _ := by rw [coefficientPhase_unit, mul_one]

/-- For positive total mass, the right preparation amplitudes have total squared magnitude one. -/
theorem coefficientRightAmplitude_normalized (c : J → ℂ)
    (hα : 0 < coefficientMass c) :
    ∑ j, star (coefficientRightAmplitude c j) * coefficientRightAmplitude c j = 1 := by
  simp_rw [coefficientRightAmplitude_weight]
  exact coefficientAmplitude_normalized c hα

end Coefficients

section Encoding

variable [Fintype J] [Fintype I] [DecidableEq J] [DecidableEq I]

omit [Fintype J] [DecidableEq J] in

/-- Absorbing a coefficient's phase into a selected unitary preserves unitarity. -/
theorem phaseAbsorbed_unitary (c : J → ℂ) (U : J → Matrix I I ℂ)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup I ℂ) (j : J) :
    phaseAbsorbed c U j ∈ Matrix.unitaryGroup I ℂ := by
  have hz : coefficientPhase (c j) ∈ unitary ℂ :=
    ⟨coefficientPhase_unit _, by simpa only [mul_comm] using coefficientPhase_unit (c j)⟩
  exact Unitary.smul_mem_of_mem hz (hU j)

omit [Fintype I] [DecidableEq J] [DecidableEq I] in

/-- The LCU matrix with coefficient amplitudes and phase-absorbed matrices equals the
coefficient-weighted sum divided by total mass. -/
theorem coefficientLCU_matrix (c : J → ℂ) (U : J → Matrix I I ℂ)
    (hα : 0 < coefficientMass c) :
    lcuMatrix (coefficientAmplitude c) (phaseAbsorbed c U) =
      ∑ j, (c j / (coefficientMass c : ℂ)) • U j := by
  classical
  unfold lcuMatrix
  apply Finset.sum_congr rfl
  intro j _
  rw [phaseAbsorbed, smul_smul, coefficientAmplitude_phase_factor c hα]

/-- For positive coefficient mass and unitary summands, phase-absorbed selection and coefficient
preparation give an exact projected encoding of the normalized sum. -/
theorem coefficientLCU_projectedEncoding (c : J → ℂ) (U : J → Matrix I I ℂ)
    (hα : 0 < coefficientMass c) (hU : ∀ j, U j ∈ Matrix.unitaryGroup I ℂ) :
    ProjectedUnitaryEncoding (∑ j, (c j / (coefficientMass c : ℂ)) • U j)
      (select (phaseAbsorbed c U)) (prepareLift (coefficientAmplitude c))
      (prepareLift (coefficientAmplitude c)) := by
  rw [← coefficientLCU_matrix c U hα]
  exact lcu_projectedUnitaryEncoding _ _ (coefficientAmplitude_normalized c hα)
    (phaseAbsorbed_unitary c U hU)

omit [Fintype I] [DecidableEq J] [DecidableEq I] in

/-- Scaling the normalized coefficient-weighted sum by its positive total mass recovers the
original linear combination. -/
theorem coefficientLCU_rescale (c : J → ℂ) (U : J → Matrix I I ℂ)
    (hα : 0 < coefficientMass c) :
    coefficientMass c • (∑ j, (c j / (coefficientMass c : ℂ)) • U j) =
      ∑ j, c j • U j := by
  classical
  have hn : (coefficientMass c : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
  ext i k
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, Complex.real_smul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  field_simp

/-- A nonzero coefficient family and unitary summands give a zero-error block encoding of their
linear combination with scale equal to total coefficient mass. -/
theorem coefficientLCU_blockEncoding (c : J → ℂ) (U : J → Matrix I I ℂ)
    (hα : 0 < coefficientMass c) (hU : ∀ j, U j ∈ Matrix.unitaryGroup I ℂ) :
    BlockEncoding (∑ j, c j • U j) (select (phaseAbsorbed c U))
      (prepareLift (coefficientAmplitude c)) (prepareLift (coefficientAmplitude c))
      (coefficientMass c) 0 := by
  have h := coefficientLCU_projectedEncoding c U hα hU
  refine ⟨h.unitary, h.left_isometry, h.right_isometry, hα, le_rfl, ?_⟩
  rw [h.encoded, coefficientLCU_rescale c U hα, sub_self, norm_zero]

/-- Using unmodified selection and different left and right coefficient amplitudes gives an
exact projected encoding of the normalized linear combination. -/
theorem coefficientLCU_bilinear_projectedEncoding (c : J → ℂ)
    (U : J → Matrix I I ℂ) (hα : 0 < coefficientMass c)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup I ℂ) :
    ProjectedUnitaryEncoding (∑ j, (c j / (coefficientMass c : ℂ)) • U j)
      (select U) (prepareLift (coefficientAmplitude c))
      (prepareLift (coefficientRightAmplitude c)) := by
  apply lcu_factorized_projectedUnitaryEncoding _ _ _ _
    (coefficientAmplitude_normalized c hα) (coefficientRightAmplitude_normalized c hα)
    _ hU
  intro j
  simpa only [coefficientRightAmplitude, ← mul_assoc] using
    coefficientAmplitude_phase_factor c hα j

end Encoding

section Zero

variable [Fintype I] [DecidableEq I]

/-- Selecting identity between orthogonal Boolean preparation frames gives an exact projected
encoding of the zero matrix. -/
theorem zeroLCU_projectedEncoding :
    ProjectedUnitaryEncoding (0 : Matrix I I ℂ)
      (select (fun _ : Bool => (1 : Matrix I I ℂ)))
      (prepareLift (Qatlib.Foundations.PureStateMath.Ket false))
      (prepareLift (Qatlib.Foundations.PureStateMath.Ket true)) := by
  have ha : ∑ b : Bool, star (Qatlib.Foundations.PureStateMath.Ket false b) * Qatlib.Foundations.PureStateMath.Ket false b = 1 := by
    simp [Qatlib.Foundations.PureStateMath.Ket]
  have hb : ∑ b : Bool, star (Qatlib.Foundations.PureStateMath.Ket true b) * Qatlib.Foundations.PureStateMath.Ket true b = 1 := by
    simp [Qatlib.Foundations.PureStateMath.Ket]
  have h := lcuBilinear_projectedUnitaryEncoding (Qatlib.Foundations.PureStateMath.Ket false)
    (Qatlib.Foundations.PureStateMath.Ket true) (fun _ : Bool => (1 : Matrix I I ℂ)) ha hb
    (fun _ => (Matrix.unitaryGroup I ℂ).one_mem)
  simpa [lcuBilinearMatrix, Qatlib.Foundations.PureStateMath.Ket] using h

/-- When coefficient mass is zero, orthogonal Boolean preparation frames give a zero-error block
encoding of the linear combination with scale one. -/
theorem coefficientLCU_zero_blockEncoding [Fintype J] (c : J → ℂ)
    (U : J → Matrix I I ℂ) (hα : coefficientMass c = 0) :
    BlockEncoding (∑ j, c j • U j)
      (select (fun _ : Bool => (1 : Matrix I I ℂ)))
      (prepareLift (Qatlib.Foundations.PureStateMath.Ket false))
      (prepareLift (Qatlib.Foundations.PureStateMath.Ket true)) 1 0 := by
  have hc := (coefficientMass_eq_zero_iff c).mp hα
  simpa [hc] using Qatlib.Concepts.BlockEncoding.ProjectedUnitaryEncoding.toBlockEncoding
    (zeroLCU_projectedEncoding (I := I))

end Zero

end Qatlib.Concepts.BlockEncoding.EncodingCore
