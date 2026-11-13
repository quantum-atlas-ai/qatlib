/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuantumSearch05.MainResults.Basic
import Qatlib.Foundations.BornMetrics.EventProbability
import Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws

/-!
# Fixed-point search algebra and convergence

Derives the π/3 amplitude identities behind cubic failure reduction and proves that a
fixed-point step cannot increase failure. Query-count recurrences and power estimates give a
scalar comparison with classical repetition and convergence to arbitrarily high success from
positive initial success. See [Grover2005].

## Main statements

* `section3_displayed_failure`: computes the cubic failure expression.
* `exists_iterate_success_ge`: obtains success at least `1 - η` for any positive `η`.

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
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError

namespace Qatlib.Papers.QuantumSearch05.MainResults

/-- The squared difference `(piThird - 1) ^ 2` equals `-piThird`. -/
theorem piThird_sub_sq : (piThird - 1) ^ 2 = -piThird := by
  simpa [piThird] using
    Qatlib.Concepts.LcuPostselect.ScaledLCU.LCUFixedPoint.omega_sub_sq

/-- The fixed-point amplitude expression `piThird + (1 - ε) * (piThird - 1) ^ 2` simplifies to
`ε * piThird` [Grover2005]. -/
theorem section3_amplitude (ε : ℝ) :
    piThird + ((1 - ε : ℝ) : ℂ) * (piThird - 1) ^ 2 = (ε : ℂ) * piThird := by
  rw [piThird_sub_sq]
  push_cast
  ring

/-- The squared norm of the fixed-point amplitude expression is `ε ^ 2`. -/
theorem section3_amplitude_norm_sq (ε : ℝ) :
    ‖piThird + ((1 - ε : ℝ) : ℂ) * (piThird - 1) ^ 2‖ ^ 2 = ε ^ 2 := by
  have hω : ‖piThird‖ ^ 2 = 1 := by
    simpa [piThird] using
      Qatlib.Concepts.LcuPostselect.ScaledLCU.LCUFixedPoint.omega_norm_sq
  rw [section3_amplitude, norm_mul, mul_pow, hω, mul_one, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]

/-- The displayed amplitude-based failure expression simplifies to `ε ^ 3` [Grover2005]. -/
theorem section3_displayed_failure (ε : ℝ) :
    (1 - (1 - ε)) * ‖piThird + ((1 - ε : ℝ) : ℂ) * (piThird - 1) ^ 2‖ ^ 2 = ε ^ 3 := by
  rw [section3_amplitude_norm_sq]
  ring

/-- For real branch mass `x`, the amplitude-based failure expression equals `(1 - x) ^ 3`. -/
theorem section3_failure_in_mass (x : ℝ) :
    (1 - x) * ‖piThird + (x : ℂ) * (piThird - 1) ^ 2‖ ^ 2 = (1 - x) ^ 3 := by
  have h : piThird + (x : ℂ) * (piThird - 1) ^ 2 =
      ((1 - x : ℝ) : ℂ) * piThird := by
    have h' := section3_amplitude (1 - x)
    simpa using h'
  have hω : ‖piThird‖ ^ 2 = 1 := by
    simpa [piThird] using
      Qatlib.Concepts.LcuPostselect.ScaledLCU.LCUFixedPoint.omega_norm_sq
  rw [h, norm_mul, mul_pow, hω, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

/-- For `p ∈ [0,1]`, cubing `1 - p` does not increase it. -/
theorem failure_cube_le (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    (1 - p) ^ 3 ≤ 1 - p := by
  have h2 : 0 ≤ 1 - p := by linarith
  have h3 : (1 - p) ^ 2 ≤ 1 := by nlinarith
  have := mul_le_mul_of_nonneg_left h3 h2
  nlinarith

/-- The true-branch mass of an orthogonal projector on a normalized state is at most one. -/
theorem projectiveBranchMass_le_one {H : Type*} [Fintype H] [DecidableEq H]
    {P : Matrix H H ℂ} (hP : IsOrthogonalProjector P) {ψ : QState H}
    (hψ : Normalized ψ) : ProjectiveBranchMass P true ψ ≤ 1 := by
  have hadd := projectiveBranchMass_add hP ψ
  rw [measureProb_univ hψ] at hadd
  have h0 : 0 ≤ ProjectiveBranchMass P false ψ := projectiveBranchMass_nonneg P false ψ
  linarith

/-- For unitary input evolution and an orthogonal target projector, one fixed-point step does
not increase the failure probability. -/
theorem one_step_failure_le_initial {H : Type*} [Fintype H] [DecidableEq H]
    (U P : Matrix H H ℂ) (s : H)
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (hP : IsOrthogonalProjector P) :
    1 - ProjectiveBranchMass P true (fixedPointStep U P s *ᵥ Ket s) ≤
      1 - ProjectiveBranchMass P true (U *ᵥ Ket s) := by
  have hnorm : Normalized (U *ᵥ Ket s) := normalized_applyGate hU (normalized_ket s)
  have h0 : 0 ≤ ProjectiveBranchMass P true (U *ᵥ Ket s) :=
    projectiveBranchMass_nonneg P true (U *ᵥ Ket s)
  have h1 : ProjectiveBranchMass P true (U *ᵥ Ket s) ≤ 1 :=
    projectiveBranchMass_le_one hP hnorm
  have hstep :=
    Qatlib.Concepts.LcuPostselect.ScaledLCU.LCUFixedPoint.step_failure
      s hU hP
  simp only [fixedPointStep]
  rw [hstep]
  exact failure_cube_le _ h0 h1

/-- The fixed-point query count satisfies `queries (m + 1) = 3 * queries m + 1` [Grover2005]. -/
theorem queries_succ (m : ℕ) : queries (m + 1) = 3 * queries m + 1 := by
  have h := three_pow_eq_two_mul_queries m
  have h' : 3 ^ (m + 1) = 2 * (3 * queries m + 1) + 1 := by
    rw [pow_succ, h]; ring
  unfold queries
  rw [show 3 ^ (m + 1) - 1 = 2 * (3 * queries m + 1) by omega]
  exact Nat.mul_div_cancel_left _ (by norm_num)

/-- For unitary input evolution and an orthogonal target projector, the iterated failure equals
the initial failure raised to `2 * queries m + 1` [Grover2005]. -/
theorem iterate_failure_queries {H : Type*} [Fintype H] [DecidableEq H]
    (U P : Matrix H H ℂ) (s : H)
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (hP : IsOrthogonalProjector P) (m : ℕ) :
    1 - ProjectiveBranchMass P true (iterate U P s m *ᵥ Ket s) =
      (1 - ProjectiveBranchMass P true (U *ᵥ Ket s)) ^ (2 * queries m + 1) := by
  rw [iterate_failure U P s hU hP m, three_pow_eq_two_mul_queries m]

/-- For `ε ∈ [0,1]`, the scalar failure expression `ε ^ (2 * q + 1)` is at most `ε ^ (q + 1)`
[Grover2005]. -/
theorem quantum_failure_le_classical_query (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1)
    (q : ℕ) : ε ^ (2 * q + 1) ≤ ε ^ (q + 1) :=
  pow_le_pow_of_le_one h0 h1 (by omega)

/-- Every natural number `n` is at most `3 ^ n`. -/
theorem self_le_three_pow : ∀ n : ℕ, n ≤ 3 ^ n := by
  intro n
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    have hp : 0 < 3 ^ n := by positivity
    nlinarith

/-- For unitary input evolution and an orthogonal target projector with positive initial
success, some fixed-point iterate has failure at most any prescribed positive `η`
[Grover2005]. -/
theorem exists_iterate_failure_le {H : Type*} [Fintype H] [DecidableEq H]
    (U P : Matrix H H ℂ) (s : H)
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (hP : IsOrthogonalProjector P)
    (hp : 0 < ProjectiveBranchMass P true (U *ᵥ Ket s)) (η : ℝ) (hη : 0 < η) :
    ∃ m, 1 - ProjectiveBranchMass P true (iterate U P s m *ᵥ Ket s) ≤ η := by
  let p := ProjectiveBranchMass P true (U *ᵥ Ket s)
  have hnorm : Normalized (U *ᵥ Ket s) := normalized_applyGate hU (normalized_ket s)
  have hp1 : p ≤ 1 := projectiveBranchMass_le_one hP hnorm
  have h0 : 0 ≤ 1 - p := by dsimp only [p]; linarith
  have h1 : 1 - p < 1 := by dsimp only [p]; linarith
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hη h1
  refine ⟨n, ?_⟩
  rw [iterate_failure U P s hU hP n]
  exact (pow_le_pow_of_le_one h0 h1.le (self_le_three_pow n)).trans hn.le

/-- For unitary input evolution and an orthogonal target projector with positive initial
success, some fixed-point iterate has success at least `1 - η` for every positive `η`. -/
theorem exists_iterate_success_ge {H : Type*} [Fintype H] [DecidableEq H]
    (U P : Matrix H H ℂ) (s : H)
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (hP : IsOrthogonalProjector P)
    (hp : 0 < ProjectiveBranchMass P true (U *ᵥ Ket s)) (η : ℝ) (hη : 0 < η) :
    ∃ m, 1 - η ≤ ProjectiveBranchMass P true (iterate U P s m *ᵥ Ket s) := by
  obtain ⟨m, hm⟩ := exists_iterate_failure_le U P s hU hP hp η hη
  exact ⟨m, by linarith⟩

end Qatlib.Papers.QuantumSearch05.MainResults
