/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LcuPostselect.ScaledLCU.ApproximateCoefficientLCU

/-!
# Fixed-point quantum search

Defines the π/3 phase-shift search step, its recursive iterates, and the associated query count.
For unitary input evolution and an orthogonal target projector, each step cubes the failure
probability, yielding explicit success formulas after any number of iterations. See
[Grover2005].

## Main statements

* `iterate_failure`: raises the initial failure to `3 ^ m`.
* `iterate_success_eq_one_sub_pow_queries`: expresses success in terms of the query count.

## References

* [Grover, 2005][Grover2005]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.BornMetrics.EventProbability

namespace Qatlib.Papers.QuantumSearch05.MainResults

/-- The complex π/3 phase factor used in the fixed-point search construction. -/
def piThird : ℂ := Qatlib.Concepts.LcuPostselect.ScaledLCU.LCUFixedPoint.omega

/-- The π/3 phase-shift matrix associated with `P`. -/
def sourcePhaseShift {H : Type*} [Fintype H] [DecidableEq H]
    (P : Matrix H H ℂ) : Matrix H H ℂ :=
  Qatlib.Concepts.LcuPostselect.ScaledLCU.LCUFixedPoint.phase P

/-- The fixed-point search composition using `U`, the source basis state `s`, and the target
matrix `P`. -/
def fixedPointStep {H : Type*} [Fintype H] [DecidableEq H]
    (U P : Matrix H H ℂ) (s : H) : Matrix H H ℂ :=
  Qatlib.Concepts.LcuPostselect.ScaledLCU.LCUFixedPoint.step U P s

/-- The recursive fixed-point search matrices, starting at `U` and applying `fixedPointStep` at
each successor. -/
def iterate {H : Type*} [Fintype H] [DecidableEq H]
    (U P : Matrix H H ℂ) (s : H) : ℕ → Matrix H H ℂ
  | 0 => U
  | m + 1 => fixedPointStep (iterate U P s m) P s

/-- The recursive-search query-count expression `(3 ^ m - 1) / 2` in natural-number arithmetic. -/
def queries (m : ℕ) : ℕ := (3 ^ m - 1) / 2

/-- The zeroth fixed-point search iterate is the initial matrix `U`. -/
@[simp] theorem iterate_zero {H : Type*} [Fintype H] [DecidableEq H]
    (U P : Matrix H H ℂ) (s : H) : iterate U P s 0 = U := rfl

/-- The successor iterate is obtained by applying one fixed-point step to the current iterate. -/
@[simp] theorem iterate_succ {H : Type*} [Fintype H] [DecidableEq H]
    (U P : Matrix H H ℂ) (s : H) (m : ℕ) :
    iterate U P s (m + 1) = fixedPointStep (iterate U P s m) P s := rfl

/-- Expands a fixed-point step as `U * sourcePhaseShift (outerProduct (Ket s)) * Uᴴ *
sourcePhaseShift P * U`. -/
theorem fixedPointStep_eq {H : Type*} [Fintype H] [DecidableEq H]
    (U P : Matrix H H ℂ) (s : H) :
    fixedPointStep U P s =
      U * sourcePhaseShift (outerProduct (Ket s)) * Uᴴ * sourcePhaseShift P * U := rfl

/-- If `U` is unitary and `P` is an orthogonal projector, every fixed-point search iterate is
unitary. -/
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

/-- Every natural power of three has the form `2 * k + 1`. -/
theorem three_pow_odd (m : ℕ) : ∃ k, 3 ^ m = 2 * k + 1 := by
  induction m with
  | zero => exact ⟨0, rfl⟩
  | succ m ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨3 * k + 1, ?_⟩
    rw [pow_succ, hk]
    ring

/-- The exponent `3 ^ m` equals `2 * queries m + 1` [Grover2005]. -/
theorem three_pow_eq_two_mul_queries (m : ℕ) :
    3 ^ m = 2 * queries m + 1 := by
  obtain ⟨k, hk⟩ := three_pow_odd m
  have hk1 : 3 ^ m - 1 = 2 * k := by omega
  have hq : queries m = k := by
    unfold queries
    rw [hk1, Nat.mul_div_cancel_left k (by norm_num)]
  rw [hq, hk]

/-- For normalized `t`, the true-branch mass of its rank-one projector on `ψ` equals `‖Inner t
ψ‖ ^ 2`. -/
theorem projectiveBranchMass_outerProduct {H : Type*} [Fintype H] [DecidableEq H]
    (t ψ : QState H) (ht : Normalized t) :
    ProjectiveBranchMass (outerProduct t) true ψ = ‖Inner t ψ‖ ^ 2 := by
  unfold ProjectiveBranchMass ProjectiveBranch ApplyGate
  simp only [if_true]
  rw [outerProduct_mulVec, measureProb_smul, measureProb_univ ht, mul_one]

/-- For unitary `U` and an orthogonal target projector, initial success `1 - ε` becomes `1 - ε ^
3` after one fixed-point step [Grover2005]. -/
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

/-- For unitary `U` and normalized target `t`, one fixed-point step changes squared target
overlap `1 - ε` to `1 - ε ^ 3` [Grover2005]. -/
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

/-- For unitary `U` and an orthogonal target projector, the failure after `m` fixed-point steps
equals the initial failure raised to `3 ^ m` [Grover2005]. -/
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

/-- Under unitary and projector hypotheses, initial success `1 - ε` becomes `1 - ε ^ (3 ^ m)`
after `m` fixed-point steps [Grover2005]. -/
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

/-- Under unitary and projector hypotheses, the success after `m` fixed-point steps is `1 - ε ^
(2 * queries m + 1)` when initial success is `1 - ε` [Grover2005]. -/
theorem iterate_success_eq_one_sub_pow_queries {H : Type*} [Fintype H] [DecidableEq H]
    (U P : Matrix H H ℂ) (s : H)
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (hP : IsOrthogonalProjector P)
    (ε : ℝ) (hε : ProjectiveBranchMass P true (U *ᵥ Ket s) = 1 - ε) (m : ℕ) :
    ProjectiveBranchMass P true (iterate U P s m *ᵥ Ket s) =
      1 - ε ^ (2 * queries m + 1) := by
  rw [← three_pow_eq_two_mul_queries m]
  exact iterate_success_eq_one_sub_pow U P s hU hP ε hε m

/-- Under unitary and projector hypotheses, initial success `f` gives one-step failure `(1 - f)
^ 3` [Grover2005]. -/
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

/-- Under unitary and projector hypotheses, initial success `f` gives one-step success `1 - (1 -
f) ^ 3`. -/
theorem uncertainty_one_step_success {H : Type*} [Fintype H] [DecidableEq H]
    (U P : Matrix H H ℂ) (s : H)
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (hP : IsOrthogonalProjector P)
    (f : ℝ) (hf : ProjectiveBranchMass P true (U *ᵥ Ket s) = f) :
    ProjectiveBranchMass P true (fixedPointStep U P s *ᵥ Ket s) = 1 - (1 - f) ^ 3 := by
  have h := uncertainty_one_step_failure U P s hU hP f hf
  linarith

/-- If initial success lies strictly between three quarters and one, one fixed-point step has
failure strictly between zero and `1 / 64`, assuming unitary evolution and an orthogonal
target projector [Grover2005]. -/
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
