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
set_option warningAsError false
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.LCU

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.BlockEncoding.EncodingCore

open Matrix
open scoped Matrix.Norms.L2Operator

variable {J I : Type*}

noncomputable def coefficientMass [Fintype J] (c : J → ℂ) : ℝ := ∑ j, ‖c j‖

noncomputable def coefficientAmplitude [Fintype J] (c : J → ℂ) (j : J) : ℂ :=
  (Real.sqrt (‖c j‖ / coefficientMass c) : ℂ)

noncomputable def coefficientPhase (z : ℂ) : ℂ := if z = 0 then 1 else z / (‖z‖ : ℂ)

noncomputable def phaseAbsorbed (c : J → ℂ) (U : J → Matrix I I ℂ)
    (j : J) : Matrix I I ℂ := coefficientPhase (c j) • U j

@[simp] theorem coefficientPhase_zero : coefficientPhase 0 = 1 := by
  simp [coefficientPhase]

theorem coefficientPhase_norm (z : ℂ) : ‖coefficientPhase z‖ = 1 := by
  by_cases hz : z = 0
  · simp [coefficientPhase, hz]
  · simp [coefficientPhase, hz, Complex.norm_real, norm_ne_zero_iff.mpr hz]

theorem coefficientPhase_unit (z : ℂ) :
    star (coefficientPhase z) * coefficientPhase z = 1 := by
  have hn : Complex.normSq (coefficientPhase z) = 1 := by
    rw [Complex.normSq_eq_norm_sq, coefficientPhase_norm]
    norm_num
  have hc := congrArg (fun x : ℝ => (x : ℂ)) hn
  simpa only [Complex.normSq_eq_conj_mul_self, Complex.star_def,
    Complex.ofReal_one] using hc

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

theorem coefficientMass_nonneg (c : J → ℂ) : 0 ≤ coefficientMass c :=
  Finset.sum_nonneg fun j _ => norm_nonneg (c j)

theorem coefficientMass_eq_zero_iff (c : J → ℂ) :
    coefficientMass c = 0 ↔ ∀ j, c j = 0 := by
  classical
  simp only [coefficientMass, Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => norm_nonneg (c j)), Finset.mem_univ, forall_const, norm_eq_zero]

theorem coefficientMass_pos_iff (c : J → ℂ) :
    0 < coefficientMass c ↔ ∃ j, c j ≠ 0 := by
  rw [lt_iff_le_and_ne]
  simp only [coefficientMass_nonneg, true_and]
  rw [ne_comm, ne_eq, coefficientMass_eq_zero_iff, not_forall]

theorem coefficientAmplitude_weight (c : J → ℂ) (hα : 0 < coefficientMass c)
    (j : J) :
    star (coefficientAmplitude c j) * coefficientAmplitude c j =
      ((‖c j‖ / coefficientMass c : ℝ) : ℂ) := by
  simp only [coefficientAmplitude, Complex.star_def, Complex.conj_ofReal]
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (div_nonneg (norm_nonneg _) hα.le)]

theorem coefficientAmplitude_normalized (c : J → ℂ) (hα : 0 < coefficientMass c) :
    ∑ j, star (coefficientAmplitude c j) * coefficientAmplitude c j = 1 := by
  simp_rw [coefficientAmplitude_weight c hα]
  have hr : ∑ j, ‖c j‖ / coefficientMass c = 1 := by
    rw [← Finset.sum_div]
    exact div_self hα.ne'
  exact_mod_cast hr

theorem coefficientAmplitude_phase_factor (c : J → ℂ)
    (hα : 0 < coefficientMass c) (j : J) :
    (star (coefficientAmplitude c j) * coefficientAmplitude c j) *
        coefficientPhase (c j) = c j / (coefficientMass c : ℂ) := by
  rw [coefficientAmplitude_weight c hα, Complex.ofReal_div]
  calc
    (‖c j‖ : ℂ) / (coefficientMass c : ℂ) * coefficientPhase (c j) =
        ((‖c j‖ : ℂ) * coefficientPhase (c j)) / (coefficientMass c : ℂ) := by ring
    _ = _ := by rw [norm_mul_coefficientPhase]

noncomputable def coefficientRightAmplitude (c : J → ℂ) (j : J) : ℂ :=
  coefficientAmplitude c j * coefficientPhase (c j)

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

theorem coefficientRightAmplitude_normalized (c : J → ℂ)
    (hα : 0 < coefficientMass c) :
    ∑ j, star (coefficientRightAmplitude c j) * coefficientRightAmplitude c j = 1 := by
  simp_rw [coefficientRightAmplitude_weight]
  exact coefficientAmplitude_normalized c hα

end Coefficients

section Encoding

variable [Fintype J] [Fintype I] [DecidableEq J] [DecidableEq I]

omit [Fintype J] [DecidableEq J] in

theorem phaseAbsorbed_unitary (c : J → ℂ) (U : J → Matrix I I ℂ)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup I ℂ) (j : J) :
    phaseAbsorbed c U j ∈ Matrix.unitaryGroup I ℂ := by
  have hz : coefficientPhase (c j) ∈ unitary ℂ :=
    ⟨coefficientPhase_unit _, by simpa only [mul_comm] using coefficientPhase_unit (c j)⟩
  exact Unitary.smul_mem_of_mem hz (hU j)

omit [Fintype I] [DecidableEq J] [DecidableEq I] in

theorem coefficientLCU_matrix (c : J → ℂ) (U : J → Matrix I I ℂ)
    (hα : 0 < coefficientMass c) :
    lcuMatrix (coefficientAmplitude c) (phaseAbsorbed c U) =
      ∑ j, (c j / (coefficientMass c : ℂ)) • U j := by
  classical
  unfold lcuMatrix
  apply Finset.sum_congr rfl
  intro j _
  rw [phaseAbsorbed, smul_smul, coefficientAmplitude_phase_factor c hα]

theorem coefficientLCU_projectedEncoding (c : J → ℂ) (U : J → Matrix I I ℂ)
    (hα : 0 < coefficientMass c) (hU : ∀ j, U j ∈ Matrix.unitaryGroup I ℂ) :
    ProjectedUnitaryEncoding (∑ j, (c j / (coefficientMass c : ℂ)) • U j)
      (select (phaseAbsorbed c U)) (prepareLift (coefficientAmplitude c))
      (prepareLift (coefficientAmplitude c)) := by
  rw [← coefficientLCU_matrix c U hα]
  exact lcu_projectedUnitaryEncoding _ _ (coefficientAmplitude_normalized c hα)
    (phaseAbsorbed_unitary c U hU)

omit [Fintype I] [DecidableEq J] [DecidableEq I] in

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

theorem coefficientLCU_blockEncoding (c : J → ℂ) (U : J → Matrix I I ℂ)
    (hα : 0 < coefficientMass c) (hU : ∀ j, U j ∈ Matrix.unitaryGroup I ℂ) :
    BlockEncoding (∑ j, c j • U j) (select (phaseAbsorbed c U))
      (prepareLift (coefficientAmplitude c)) (prepareLift (coefficientAmplitude c))
      (coefficientMass c) 0 := by
  have h := coefficientLCU_projectedEncoding c U hα hU
  refine ⟨h.unitary, h.left_isometry, h.right_isometry, hα, le_rfl, ?_⟩
  rw [h.encoded, coefficientLCU_rescale c U hα, sub_self, norm_zero]

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
