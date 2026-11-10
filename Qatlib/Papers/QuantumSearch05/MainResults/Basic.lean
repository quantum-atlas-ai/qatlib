/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LcuPostselect.ScaledLCU.ApproximateCoefficientLCU
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.BornMetrics.EventProbability

namespace Qatlib.Papers.QuantumSearch05.MainResults

def piThird : ℂ := Qatlib.Concepts.LcuPostselect.ScaledLCU.LCUFixedPoint.omega

def sourcePhaseShift {H : Type*} [Fintype H] [DecidableEq H]
    (P : Matrix H H ℂ) : Matrix H H ℂ :=
  Qatlib.Concepts.LcuPostselect.ScaledLCU.LCUFixedPoint.phase P

def fixedPointStep {H : Type*} [Fintype H] [DecidableEq H]
    (U P : Matrix H H ℂ) (s : H) : Matrix H H ℂ :=
  Qatlib.Concepts.LcuPostselect.ScaledLCU.LCUFixedPoint.step U P s

def iterate {H : Type*} [Fintype H] [DecidableEq H]
    (U P : Matrix H H ℂ) (s : H) : ℕ → Matrix H H ℂ
  | 0 => U
  | m + 1 => fixedPointStep (iterate U P s m) P s

def queries (m : ℕ) : ℕ := (3 ^ m - 1) / 2

@[simp] theorem iterate_zero {H : Type*} [Fintype H] [DecidableEq H]
    (U P : Matrix H H ℂ) (s : H) : iterate U P s 0 = U := rfl

@[simp] theorem iterate_succ {H : Type*} [Fintype H] [DecidableEq H]
    (U P : Matrix H H ℂ) (s : H) (m : ℕ) :
    iterate U P s (m + 1) = fixedPointStep (iterate U P s m) P s := rfl

theorem fixedPointStep_eq {H : Type*} [Fintype H] [DecidableEq H]
    (U P : Matrix H H ℂ) (s : H) :
    fixedPointStep U P s =
      U * sourcePhaseShift (outerProduct (Ket s)) * Uᴴ * sourcePhaseShift P * U := rfl

theorem iterate_unitary {H : Type*} [Fintype H] [DecidableEq H]
    (U P : Matrix H H ℂ) (s : H)
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (hP : IsOrthogonalProjector P) :
    ∀ m, iterate U P s m ∈ Matrix.unitaryGroup H ℂ := by
  intro m
  induction m with
  | zero => simpa using hU
  | succ m ih =>
    simpa [iterate_succ] using!
      Qatlib.Concepts.LcuPostselect.ScaledLCU.LCUFixedPoint.step_unitary
        s ih hP

theorem three_pow_odd (m : ℕ) : ∃ k, 3 ^ m = 2 * k + 1 := by
  induction m with
  | zero => exact ⟨0, rfl⟩
  | succ m ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨3 * k + 1, ?_⟩
    rw [pow_succ, hk]
    ring

theorem three_pow_eq_two_mul_queries (m : ℕ) :
    3 ^ m = 2 * queries m + 1 := by
  obtain ⟨k, hk⟩ := three_pow_odd m
  have hk1 : 3 ^ m - 1 = 2 * k := by omega
  have hq : queries m = k := by
    unfold queries
    rw [hk1, Nat.mul_div_cancel_left k (by norm_num)]
  rw [hq, hk]

theorem projectiveBranchMass_outerProduct {H : Type*} [Fintype H] [DecidableEq H]
    (t ψ : QState H) (ht : Normalized t) :
    ProjectiveBranchMass (outerProduct t) true ψ = ‖Inner t ψ‖ ^ 2 := by
  unfold ProjectiveBranchMass ProjectiveBranch ApplyGate
  simp only [if_true]
  rw [outerProduct_mulVec, measureProb_smul, measureProb_univ ht, mul_one]

theorem one_step_success_eq_one_sub_cube {H : Type*} [Fintype H] [DecidableEq H]
    (U P : Matrix H H ℂ) (s : H)
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (hP : IsOrthogonalProjector P)
    (ε : ℝ) (hε : ProjectiveBranchMass P true (U *ᵥ Ket s) = 1 - ε) :
    ProjectiveBranchMass P true (fixedPointStep U P s *ᵥ Ket s) = 1 - ε ^ 3 := by
  have h :=
    Qatlib.Concepts.LcuPostselect.ScaledLCU.LCUFixedPoint.step_failure
      s hU hP
  rw [hε] at h
  have hcube : (1 - (1 - ε)) ^ 3 = ε ^ 3 := by ring
  rw [hcube] at h
  simp only [fixedPointStep]
  linarith

theorem one_step_amplitude_eq_one_sub_cube {H : Type*} [Fintype H] [DecidableEq H]
    (U : Matrix H H ℂ) (t : QState H) (s : H)
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (ht : Normalized t)
    (ε : ℝ) (hε : ‖Inner t (U *ᵥ Ket s)‖ ^ 2 = 1 - ε) :
    ‖Inner t (fixedPointStep U (outerProduct t) s *ᵥ Ket s)‖ ^ 2 = 1 - ε ^ 3 := by
  have hbridge := projectiveBranchMass_outerProduct t (U *ᵥ Ket s) ht
  have hbridge2 := projectiveBranchMass_outerProduct t
    (fixedPointStep U (outerProduct t) s *ᵥ Ket s) ht
  rw [← hbridge] at hε
  rw [← hbridge2]
  exact one_step_success_eq_one_sub_cube U (outerProduct t) s hU
    (isOrthogonalProjector_outerProduct ht) ε hε

theorem iterate_failure {H : Type*} [Fintype H] [DecidableEq H]
    (U P : Matrix H H ℂ) (s : H)
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (hP : IsOrthogonalProjector P) (m : ℕ) :
    1 - ProjectiveBranchMass P true (iterate U P s m *ᵥ Ket s) =
      (1 - ProjectiveBranchMass P true (U *ᵥ Ket s)) ^ (3 ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hW := iterate_unitary U P s hU hP m
    have hstep :=
      Qatlib.Concepts.LcuPostselect.ScaledLCU.LCUFixedPoint.step_failure
        s hW hP
    simp only [iterate_succ, fixedPointStep] at hstep ⊢
    rw [hstep, ih, ← pow_mul, pow_succ]

theorem iterate_success_eq_one_sub_pow {H : Type*} [Fintype H] [DecidableEq H]
    (U P : Matrix H H ℂ) (s : H)
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (hP : IsOrthogonalProjector P)
    (ε : ℝ) (hε : ProjectiveBranchMass P true (U *ᵥ Ket s) = 1 - ε) (m : ℕ) :
    ProjectiveBranchMass P true (iterate U P s m *ᵥ Ket s) = 1 - ε ^ (3 ^ m) := by
  have h := iterate_failure U P s hU hP m
  rw [hε] at h
  have hcube : (1 - (1 - ε)) = ε := by ring
  rw [hcube] at h
  linarith

theorem iterate_success_eq_one_sub_pow_queries {H : Type*} [Fintype H] [DecidableEq H]
    (U P : Matrix H H ℂ) (s : H)
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (hP : IsOrthogonalProjector P)
    (ε : ℝ) (hε : ProjectiveBranchMass P true (U *ᵥ Ket s) = 1 - ε) (m : ℕ) :
    ProjectiveBranchMass P true (iterate U P s m *ᵥ Ket s) =
      1 - ε ^ (2 * queries m + 1) := by
  rw [← three_pow_eq_two_mul_queries m]
  exact iterate_success_eq_one_sub_pow U P s hU hP ε hε m

theorem uncertainty_one_step_failure {H : Type*} [Fintype H] [DecidableEq H]
    (U P : Matrix H H ℂ) (s : H)
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (hP : IsOrthogonalProjector P)
    (f : ℝ) (hf : ProjectiveBranchMass P true (U *ᵥ Ket s) = f) :
    1 - ProjectiveBranchMass P true (fixedPointStep U P s *ᵥ Ket s) = (1 - f) ^ 3 := by
  have h :=
    Qatlib.Concepts.LcuPostselect.ScaledLCU.LCUFixedPoint.step_failure
      s hU hP
  rw [hf] at h
  simp only [fixedPointStep]
  exact h

theorem uncertainty_one_step_success {H : Type*} [Fintype H] [DecidableEq H]
    (U P : Matrix H H ℂ) (s : H)
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (hP : IsOrthogonalProjector P)
    (f : ℝ) (hf : ProjectiveBranchMass P true (U *ᵥ Ket s) = f) :
    ProjectiveBranchMass P true (fixedPointStep U P s *ᵥ Ket s) = 1 - (1 - f) ^ 3 := by
  have h := uncertainty_one_step_failure U P s hU hP f hf
  linarith

theorem uncertainty_failure_range {H : Type*} [Fintype H] [DecidableEq H]
    (U P : Matrix H H ℂ) (s : H)
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (hP : IsOrthogonalProjector P)
    (f : ℝ) (hlo : 3 / 4 < f) (hhi : f < 1)
    (hf : ProjectiveBranchMass P true (U *ᵥ Ket s) = f) :
    0 < 1 - ProjectiveBranchMass P true (fixedPointStep U P s *ᵥ Ket s) ∧
      1 - ProjectiveBranchMass P true (fixedPointStep U P s *ᵥ Ket s) < 1 / 64 := by
  rw [uncertainty_one_step_failure U P s hU hP f hf]
  have h1 : (0 : ℝ) < 1 - f := by linarith
  have h2 : (1 : ℝ) - f < 1 / 4 := by linarith
  refine ⟨pow_pos h1 3, ?_⟩
  nlinarith [h1, h2, sq_nonneg (1 - f)]

end Qatlib.Papers.QuantumSearch05.MainResults
