/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuantumSearch05.MainResults.Basic
import Qatlib.Foundations.BornMetrics.EventProbability
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Foundations.InstrumentCore.Measurement

namespace Qatlib.Papers.QuantumSearch05.MainResults

def classicalTwoPickFailure (f : ℝ) : ℝ := (1 - f) ^ 2

def younesSuccess (f : ℝ) : ℝ := f * (1 + 4 * (1 - f) ^ 2)

def younesFailure (f : ℝ) : ℝ := 1 - younesSuccess f

def phaseShiftFailure (f : ℝ) : ℝ := (1 - f) ^ 3

theorem younes_failure_eq (f : ℝ) :
    younesFailure f = (1 - f) * (1 - 4 * f * (1 - f)) := by
  unfold younesFailure younesSuccess
  ring

theorem classical_failure_range (f : ℝ) (h0 : 3 / 4 < f) (h1 : f < 1) :
    0 < classicalTwoPickFailure f ∧ classicalTwoPickFailure f < 1 / 16 := by
  unfold classicalTwoPickFailure
  have h : 0 < 1 - f := by linarith
  have h2 : 1 - f < 1 / 4 := by linarith
  refine ⟨pow_pos h 2, ?_⟩
  have := pow_lt_pow_left₀ h2 h.le (by norm_num : (2 : ℕ) ≠ 0)
  norm_num at this ⊢
  exact this

theorem phaseShift_failure_range (f : ℝ) (h0 : 3 / 4 < f) (h1 : f < 1) :
    0 < phaseShiftFailure f ∧ phaseShiftFailure f < 1 / 64 := by
  unfold phaseShiftFailure
  have h : 0 < 1 - f := by linarith
  have h2 : 1 - f < 1 / 4 := by linarith
  refine ⟨pow_pos h 3, ?_⟩
  have := pow_lt_pow_left₀ h2 h.le (by norm_num : (3 : ℕ) ≠ 0)
  norm_num at this ⊢
  exact this

theorem phaseShift_failure_le_classical (f : ℝ) (h0 : 0 ≤ f) (h1 : f ≤ 1) :
    phaseShiftFailure f ≤ classicalTwoPickFailure f := by
  unfold phaseShiftFailure classicalTwoPickFailure
  have h : 0 ≤ 1 - f := by linarith
  have hsq : 0 ≤ f * (1 - f) ^ 2 := mul_nonneg h0 (sq_nonneg (1 - f))
  nlinarith

theorem phaseShift_failure_le_quarter_classical (f : ℝ) (h0 : 3 / 4 ≤ f)
    (h1 : f ≤ 1) : phaseShiftFailure f ≤ (1 / 4) * classicalTwoPickFailure f := by
  unfold phaseShiftFailure classicalTwoPickFailure
  have ha : 0 ≤ 1 - f := by linarith
  have hb : 1 - f - 1 / 4 ≤ 0 := by linarith
  have hprod : (1 - f) ^ 2 * (1 - f - 1 / 4) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (1 - f)) hb
  nlinarith

theorem phaseShift_failure_le_quarter_younes (f : ℝ) (h0 : 3 / 4 ≤ f)
    (h1 : f ≤ 1) : phaseShiftFailure f ≤ (1 / 4) * younesFailure f := by
  rw [younes_failure_eq]
  unfold phaseShiftFailure
  have ha : 0 ≤ 1 - f := by linarith
  have hfac : (1 / 4) * ((1 - f) * (1 - 4 * f * (1 - f))) - (1 - f) ^ 3 =
      (1 / 4) * (1 - f) * (4 * f - 3) := by ring
  have hprod : 0 ≤ (1 / 4) * (1 - f) * (4 * f - 3) :=
    mul_nonneg (mul_nonneg (by norm_num) ha) (by linarith)
  linarith [hfac, hprod]

theorem younes_success_range (f : ℝ) (h0 : 3 / 4 ≤ f) (h1 : f ≤ 1) :
    25 / 27 ≤ younesSuccess f ∧ younesSuccess f ≤ 1 := by
  have htop : 1 - younesSuccess f = (1 - f) * (2 * f - 1) ^ 2 := by
    unfold younesSuccess; ring
  have hbot : 27 * younesSuccess f - 25 = (3 * f - 1) * (6 * f - 5) ^ 2 := by
    unfold younesSuccess; ring
  have hA : 0 ≤ (1 - f) * (2 * f - 1) ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg (2 * f - 1))
  have hB : 0 ≤ (3 * f - 1) * (6 * f - 5) ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg (6 * f - 5))
  constructor <;> linarith

theorem projectiveBranchMass_projector {I : Type*} [Fintype I] [DecidableEq I]
    (S : Finset I) (ψ : QState I) :
    ProjectiveBranchMass (Projector S) true ψ = MeasureProb ψ S := by
  have h : ProjectiveBranchMass (Projector S) true ψ =
      MeasureProb (Collapse ψ S) Finset.univ := rfl
  rw [h]
  have h2 : MeasureProb (Collapse ψ S) Finset.univ =
      ∑ i, ‖Collapse ψ S i‖ ^ 2 := by
    simp [MeasureProb, BornProb]
  rw [h2, sum_normSq_collapse]

theorem hadamard_marked_failure (n : ℕ) (M : Finset (Reg n)) :
    1 - ProjectiveBranchMass (Projector M) true
        (fixedPointStep (HadamardN n) (Projector M) (ZeroStr n) *ᵥ Ket (ZeroStr n)) =
      (1 - (M.card : ℝ) / Fintype.card (Reg n)) ^ 3 := by
  have hU : HadamardN n ∈ Matrix.unitaryGroup (Reg n) ℂ := hadamardN_unitary n
  have hP : IsOrthogonalProjector (Projector M) := projector_isOrthogonalProjector M
  have hmass : ProjectiveBranchMass (Projector M) true
      (HadamardN n *ᵥ Ket (ZeroStr n)) =
        (M.card : ℝ) / Fintype.card (Reg n) := by
    rw [show HadamardN n *ᵥ Ket (ZeroStr n) =
        ApplyGate (HadamardN n) (Ket (ZeroStr n)) from rfl,
      applyGate_hadamardN_ket_zero, projectiveBranchMass_projector, measureProb_uniform]
  exact uncertainty_one_step_failure (HadamardN n) (Projector M) (ZeroStr n)
    hU hP _ hmass

theorem hadamard_marked_success (n : ℕ) (M : Finset (Reg n)) :
    ProjectiveBranchMass (Projector M) true
        (fixedPointStep (HadamardN n) (Projector M) (ZeroStr n) *ᵥ Ket (ZeroStr n)) =
      1 - (1 - (M.card : ℝ) / Fintype.card (Reg n)) ^ 3 := by
  have h := hadamard_marked_failure n M
  linarith

theorem hadamard_marked_failure_range (n : ℕ) (M : Finset (Reg n))
    (hlo : 3 / 4 < (M.card : ℝ) / Fintype.card (Reg n))
    (hhi : (M.card : ℝ) / Fintype.card (Reg n) < 1) :
    0 < 1 - ProjectiveBranchMass (Projector M) true
        (fixedPointStep (HadamardN n) (Projector M) (ZeroStr n) *ᵥ Ket (ZeroStr n)) ∧
      1 - ProjectiveBranchMass (Projector M) true
        (fixedPointStep (HadamardN n) (Projector M) (ZeroStr n) *ᵥ Ket (ZeroStr n)) <
        1 / 64 := by
  rw [hadamard_marked_failure]
  exact phaseShift_failure_range _ hlo hhi

end Qatlib.Papers.QuantumSearch05.MainResults
