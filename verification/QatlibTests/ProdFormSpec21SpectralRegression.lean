module

/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

public import Qatlib.Papers.ProdFormSpec21.MainResults.EigenstateDecomposition
public import Qatlib.Papers.ProdFormSpec21.MainResults.PureStateLeakage
public import Qatlib.Papers.ProdFormSpec21.MainResults.EnergyShiftOperator
public import Qatlib.Papers.ProdFormSpec21.MainResults.AdiabaticTrotterOptimization
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# ProdFormSpec21 consumer regression tests

Ordinary-`module` consumer checks for the Dev-layer Corollary 1,
Theorem 1, Lemma 3 and Proposition 1 / Corollary 3 results.  The
decomposition is instantiated on a genuine two-dimensional Euclidean
state with amplitudes `3/5` and `4/5`; the leakage, energy-shift and
Trotter-bound results are instantiated on one-dimensional and numeric
instances with non-zero operator distances and errors.
-/

@[expose] public section

set_option autoImplicit false

namespace QatlibTests.ProdFormSpec21SpectralRegression

open Qatlib.Papers.ProdFormSpec21.MainResults
open Qatlib.Papers.ProdFormSpec21.MainResults
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

/-! ## Corollary 1 on a two-dimensional Euclidean state -/

/-- The ideal evolved eigenstate `e₀` in `EuclideanSpace ℂ (Fin 2)`. -/
noncomputable def idealState : EuclideanSpace ℂ (Fin 2) :=
  EuclideanSpace.single 0 1

/-- A Trotterized state with amplitudes `3/5` and `4/5`. -/
noncomputable def trotState : EuclideanSpace ℂ (Fin 2) :=
  EuclideanSpace.single 0 ((3 / 5 : ℝ) : ℂ) +
    EuclideanSpace.single 1 ((4 / 5 : ℝ) : ℂ)

/-- The ideal state has squared Euclidean norm `1`. -/
theorem idealState_norm_sq : ‖idealState‖ ^ 2 = 1 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp [idealState]

/-- The ideal state is a unit Euclidean vector. -/
theorem idealState_norm : ‖idealState‖ = 1 := by
  have hnn : (0 : ℝ) ≤ ‖idealState‖ := norm_nonneg _
  calc ‖idealState‖ = Real.sqrt (‖idealState‖ ^ 2) := by
        rw [Real.sqrt_sq hnn]
    _ = 1 := by rw [idealState_norm_sq, Real.sqrt_one]

/-- The Trotterized `3/5, 4/5` state has squared Euclidean norm `1`. -/
theorem trotState_norm_sq : ‖trotState‖ ^ 2 = 1 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp [trotState]
  norm_num

/-- The Trotterized state has unit Euclidean norm. -/
theorem trotState_norm : ‖trotState‖ = 1 := by
  have hnn : (0 : ℝ) ≤ ‖trotState‖ := norm_nonneg _
  calc ‖trotState‖ = Real.sqrt (‖trotState‖ ^ 2) := by
        rw [Real.sqrt_sq hnn]
    _ = 1 := by rw [trotState_norm_sq, Real.sqrt_one]

/-- The overlap of the two states is `3/5`. -/
theorem overlap_eq : ⟪idealState, trotState⟫_ℂ = ((3 / 5 : ℝ) : ℂ) := by
  simp [idealState, trotState, EuclideanSpace.inner_single_left]

/-- Corollary 1 decomposition on the concrete state: the residual is
orthogonal to the ideal state and the fidelity defect is `16/25`. -/
theorem fidelity_defect_fin2 :
    ⟪idealState, trotState - ⟪idealState, trotState⟫_ℂ • idealState⟫_ℂ = 0 ∧
      1 - ‖⟪idealState, trotState⟫_ℂ‖ ^ 2 = 16 / 25 := by
  obtain ⟨horth, _, _⟩ :=
    orthogonal_residual_decomposition idealState trotState idealState_norm
  refine ⟨horth, ?_⟩
  rw [overlap_eq, Complex.norm_real]
  norm_num

/-- The fidelity bound of Eq. (17) on the concrete state, with
`h = δt = lam = L = 1` residual estimates `4/5 ≤ 1` and `4/5 ≤ 1`. -/
theorem fidelity_bound_fin2 :
    1 - ‖⟪idealState, trotState⟫_ℂ‖ ^ 2 ≤
      min ((1 * 1 / 1 : ℝ) ^ 2) ((1 * 1 * 1 ^ 2 : ℝ) ^ 2) := by
  have hres : ‖trotState - ⟪idealState, trotState⟫_ℂ • idealState‖ ≤ 1 := by
    have hnorm : ‖trotState - ⟪idealState, trotState⟫_ℂ • idealState‖ ^ 2
        = 16 / 25 := by
      obtain ⟨_, _, hpyth⟩ :=
        orthogonal_residual_decomposition idealState trotState idealState_norm
      rw [overlap_eq] at hpyth ⊢
      rw [trotState_norm] at hpyth
      have hn : ‖((3 / 5 : ℝ) : ℂ)‖ = 3 / 5 := by
        rw [Complex.norm_real]
        norm_num
      rw [hn] at hpyth
      linarith
    have h0 : (0 : ℝ) ≤ ‖trotState - ⟪idealState, trotState⟫_ℂ • idealState‖ :=
      norm_nonneg _
    nlinarith [hnorm, h0]
  have h := fidelity_defect_le_min_of_residual_le idealState trotState
    idealState_norm trotState_norm 1 1 1 1 (by norm_num) (by norm_num)
    (by simpa using hres) (by simpa using hres)
  simpa only [Nat.cast_one] using h

/-- Accumulation of three real phase increments of `1/10`. -/
theorem phase_sum_three :
    |∑ _j : Fin 3, (1 / 10 : ℝ)| ≤ (3 : ℝ) * (1 / 10) * 1 ^ 2 :=
  phase_sum_abs_le 3 (by norm_num) (1 / 10) 1 (fun _ => 1 / 10)
    (fun _ => by norm_num)

/-! ## Theorem 1 leakage on a one-dimensional space with distance `1` -/

/-- Pure-state leakage for `P = U = 1`, `Q = 0` on `ℂ`: the leakage
`1 - ‖1‖² = 0` is at most `4 * ‖(1 : ℂ →L[ℂ] ℂ) - 0‖² = 4`. -/
theorem leakage_one_dim :
    1 - ‖(1 : ℂ →L[ℂ] ℂ) ((1 : ℂ →L[ℂ] ℂ) (1 : ℂ))‖ ^ 2
      ≤ 4 * ‖(1 : ℂ →L[ℂ] ℂ) - 0‖ ^ 2 := by
  have h := pure_state_leakage_le (1 : ℂ →L[ℂ] ℂ) (0 : ℂ →L[ℂ] ℂ)
    (1 : ℂ →L[ℂ] ℂ) (by
      intro x
      simp) (by
      intro x
      simp) (by
      intro x
      simp) (1 : ℂ) (by norm_num) (by simp)
  exact h

/-! ## Lemma 3 energy shift on a one-dimensional space -/

/-- First-order diagonal bound for a second-order remainder
`(1/4) • id` at step `δt = 1/2`: the expectation norm `1/4` is at most
the operator norm `‖(1/4) • id‖`. -/
theorem first_order_diagonal_one_dim :
    ‖⟪(1 : ℂ), ((1 / 4 : ℂ) • (1 : ℂ →L[ℂ] ℂ)) (1 : ℂ)⟫_ℂ‖
      ≤ ‖(1 / 4 : ℂ) • (1 : ℂ →L[ℂ] ℂ)‖ := by
  have h := first_order_diagonal_bound
    ((1 / 4 : ℂ) • (1 : ℂ →L[ℂ] ℂ)) (0 : ℂ →L[ℂ] ℂ)
    ((1 / 4 : ℂ) • (1 : ℂ →L[ℂ] ℂ)) (1 : ℂ) (by norm_num) (1 / 2)
    (by simp) (by simp)
  exact h

/-- Eigenvalue shift `|1/4 - 0|` for the common eigenvector `1` of
`0` and `(1/4) • id` is at most the operator norm of the difference. -/
theorem eigenvalue_shift_one_dim :
    |(1 / 4 : ℝ) - 0| ≤ ‖(1 / 4 : ℂ) • (1 : ℂ →L[ℂ] ℂ) - 0‖ := by
  have h := eigenvalue_shift_le_opNorm (0 : ℂ →L[ℂ] ℂ)
    ((1 / 4 : ℂ) • (1 : ℂ →L[ℂ] ℂ)) (1 : ℂ) (by norm_num) 0 (1 / 4)
    (by simp) (by simp)
  exact h

/-! ## Proposition 1 two-term bound at numeric parameters -/

/-- Global lower bound `2 ≤ twoTermBound 2 3 6 1 4`. -/
theorem two_term_lower_numeric : 2 ≤ twoTermBound 2 3 6 1 4 := by
  have h := two_term_bound_ge 2 3 6 1 4 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-- At the paper's critical time the model's value is `13/12` times
its attained minimum, with positive parameters. -/
theorem two_term_factor_numeric :
    twoTermBound 2 3 6 1 (Qatlib.Papers.ProdFormSpec21.MainResults.criticalT 2 3 6) =
      13 / 12 * twoTermBound 2 3 6 1 (6 * 2 / 3) := by
  rw [two_term_bound_at_balanced_time 2 3 6 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)]
  exact two_term_bound_at_critical_factor 2 3 6 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- A Trotter error bounded by the two-term bound at `T_c` is at most
`13/6` for `D = 2, C₁ = 3, M = 6, lam = 1`. -/
theorem trotter_error_numeric :
    (2 : ℝ) ≤ 13 / 6 * (2 * 3 / (6 * 1 ^ 3)) := by
  have hTc_pos : (0 : ℝ) <
      Qatlib.Papers.ProdFormSpec21.MainResults.criticalT 2 3 6 := by
    unfold Qatlib.Papers.ProdFormSpec21.MainResults.criticalT
    norm_num
  have hge := two_term_bound_ge 2 3 6 1
    (Qatlib.Papers.ProdFormSpec21.MainResults.criticalT 2 3 6)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hTc_pos
  have h := trotter_error_le_at_critical 2 2 3 6 1 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by
      norm_num at hge
      exact hge)
  exact h

/-- The operator-norm comparison of a preserved projector and a zero
output, using the two component estimates at the critical time. -/
theorem matrix_error_numeric :
    totalTrotterError (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 1 ≤ 13 / 3 := by
  have h := total_trotter_error_le_at_critical
    (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 1 1 2 3 3 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [adiabaticError, criticalT])
    (by norm_num [trotterErr, criticalT])
  norm_num at h
  exact h

end QatlibTests.ProdFormSpec21SpectralRegression
