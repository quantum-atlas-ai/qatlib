/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuantumSearch05.MainResults.Basic
import Qatlib.Foundations.BornMetrics.EventProbability
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement

/-!
# Search failure laws with uncertain marked fraction

Defines scalar failure expressions for two classical picks, the Younes success formula, and the
π/3 phase-shift method. The module compares these expressions and specializes fixed-point search
to the uniform Hadamard state for an arbitrary marked subset. See [Grover2005].

## Main statements

* `phaseShift_failure_le_quarter_younes`: compares failure when the marked fraction is at least
  three quarters.
* `hadamard_marked_success`: computes success from the marked-set cardinality.

## References

* [Grover, 2005][Grover2005]
-/

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

/-- The two-pick classical failure expression `(1 - f) ^ 2`. -/
def classicalTwoPickFailure (f : ℝ) : ℝ := (1 - f) ^ 2

/-- The scalar Younes success expression `f * (1 + 4 * (1 - f) ^ 2)`. -/
def younesSuccess (f : ℝ) : ℝ := f * (1 + 4 * (1 - f) ^ 2)

/-- The complement `1 - younesSuccess f` of the Younes success expression. -/
def younesFailure (f : ℝ) : ℝ := 1 - younesSuccess f

/-- The fixed-point phase-shift failure expression `(1 - f) ^ 3`. -/
def phaseShiftFailure (f : ℝ) : ℝ := (1 - f) ^ 3

/-- The Younes failure expression factors as `(1 - f) * (1 - 4 * f * (1 - f))`. -/
theorem younes_failure_eq (f : ℝ) :
    younesFailure f = (1 - f) * (1 - 4 * f * (1 - f)) := by
  unfold younesFailure younesSuccess
  ring

/-- For `3 / 4 < f < 1`, the two-pick classical failure is strictly between zero and `1 / 16`
[Grover2005]. -/
theorem classical_failure_range (f : ℝ) (h0 : 3 / 4 < f) (h1 : f < 1) :
    0 < classicalTwoPickFailure f ∧ classicalTwoPickFailure f < 1 / 16 := by
  unfold classicalTwoPickFailure
  have h : 0 < 1 - f := by linarith
  have h2 : 1 - f < 1 / 4 := by linarith
  refine ⟨pow_pos h 2, ?_⟩
  have := pow_lt_pow_left₀ h2 h.le (by norm_num : (2 : ℕ) ≠ 0)
  norm_num at this ⊢
  exact this

/-- For `3 / 4 < f < 1`, the phase-shift failure is strictly between zero and `1 / 64`
[Grover2005]. -/
theorem phaseShift_failure_range (f : ℝ) (h0 : 3 / 4 < f) (h1 : f < 1) :
    0 < phaseShiftFailure f ∧ phaseShiftFailure f < 1 / 64 := by
  unfold phaseShiftFailure
  have h : 0 < 1 - f := by linarith
  have h2 : 1 - f < 1 / 4 := by linarith
  refine ⟨pow_pos h 3, ?_⟩
  have := pow_lt_pow_left₀ h2 h.le (by norm_num : (3 : ℕ) ≠ 0)
  norm_num at this ⊢
  exact this

/-- For `f ∈ [0,1]`, the phase-shift failure is at most the two-pick classical failure. -/
theorem phaseShift_failure_le_classical (f : ℝ) (h0 : 0 ≤ f) (h1 : f ≤ 1) :
    phaseShiftFailure f ≤ classicalTwoPickFailure f := by
  unfold phaseShiftFailure classicalTwoPickFailure
  have h : 0 ≤ 1 - f := by linarith
  have hsq : 0 ≤ f * (1 - f) ^ 2 := mul_nonneg h0 (sq_nonneg (1 - f))
  nlinarith

/-- For `3 / 4 ≤ f ≤ 1`, the phase-shift failure is at most one quarter of the two-pick
classical failure [Grover2005]. -/
theorem phaseShift_failure_le_quarter_classical (f : ℝ) (h0 : 3 / 4 ≤ f)
    (h1 : f ≤ 1) : phaseShiftFailure f ≤ (1 / 4) * classicalTwoPickFailure f := by
  unfold phaseShiftFailure classicalTwoPickFailure
  have ha : 0 ≤ 1 - f := by linarith
  have hb : 1 - f - 1 / 4 ≤ 0 := by linarith
  have hprod : (1 - f) ^ 2 * (1 - f - 1 / 4) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (1 - f)) hb
  nlinarith

/-- For `3 / 4 ≤ f ≤ 1`, the phase-shift failure is at most one quarter of the Younes failure
[Grover2005]. -/
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

/-- For `3 / 4 ≤ f ≤ 1`, the Younes success expression lies between `25 / 27` and one
[Grover2005]. -/
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

/-- The true-branch mass of the computational-basis projector for `S` equals the measurement
probability of `S` [Grover2005]. -/
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

/-- For a marked subset of the `n`-qubit basis, one fixed-point step from the Hadamard state has
failure equal to the cube of one minus the marked fraction [Grover2005]. -/
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

/-- For a marked subset of the `n`-qubit basis, one fixed-point step from the Hadamard state has
success equal to one minus the cube of the unmarked fraction [Grover2005]. -/
theorem hadamard_marked_success (n : ℕ) (M : Finset (Reg n)) :
    ProjectiveBranchMass (Projector M) true
        (fixedPointStep (HadamardN n) (Projector M) (ZeroStr n) *ᵥ Ket (ZeroStr n)) =
      1 - (1 - (M.card : ℝ) / Fintype.card (Reg n)) ^ 3 := by
  have h := hadamard_marked_failure n M
  linarith

/-- If the marked fraction lies strictly between three quarters and one, one fixed-point step
from the Hadamard state has failure strictly between zero and `1 / 64` [Grover2005]. -/
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
