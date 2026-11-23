/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Qatlib.Papers.HamLCUSim12.Multiproduct.Lemma2NearbyFailureCorrectedHami

@[expose] public section

/-!
# Uniform failure bounds for the two-unitary LCU on qubit registers

The corrected Lemma 2 circuit is consumed on non-degenerate qubit registers `Fin (2 ^ n)`
with `0 < n`, with the proximity hypothesis expressed either through the true Euclidean
operator norm `‖Ua - Ub‖` or through the equivalent uniform
state-action bound. Both statements place the uniform constant `C = 1` outside the universal
quantifiers, so the failure bound `C * κ * Δ² / (κ + 1)²` holds uniformly for every register
size, weight ratio, and proximity level. See [ChildsWiebe2012], Lemma 2.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.HamLCUSim12.FullSimulation

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.HamLCUSim12.LCUDeferred
open Qatlib.Papers.HamLCUSim12.Multiproduct
open scoped Matrix.Norms.L2Operator

/-- Bridge from the Euclidean operator norm to the uniform state-action sum: if
`‖A‖ ≤ Δ` in the Euclidean operator norm, then the squared Euclidean norm of the
image of every normalized state is at most `Δ²`. -/
private theorem sum_sq_mulVec_le {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) {Δ : ℝ} (h : ‖A‖ ≤ Δ) (φ : QState I) (hφ : Normalized φ) :
    (∑ x : I, ‖(A *ᵥ φ) x‖ ^ 2) ≤ Δ ^ 2 := by
  have hcoer : ∀ f : I → ℂ, ∀ i : I,
      ((EuclideanSpace.equiv I ℂ).symm f : I → ℂ) i = f i := fun f i => rfl
  have hkey := Matrix.l2_opNorm_mulVec A ((EuclideanSpace.equiv I ℂ).symm φ)
  have hnorm : ‖(EuclideanSpace.equiv I ℂ).symm φ‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp_rw [hcoer]
    exact hφ
  have hsum : (∑ x : I, ‖(A *ᵥ φ) x‖ ^ 2)
      = ‖(EuclideanSpace.equiv I ℂ).symm (A *ᵥ φ)‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp_rw [hcoer]
  rw [hsum]
  have hone : ‖(EuclideanSpace.equiv I ℂ).symm φ‖ = 1 :=
    (sq_eq_one_iff.mp hnorm).resolve_right
      (fun hneg => by linarith [norm_nonneg ((EuclideanSpace.equiv I ℂ).symm φ)])
  have h1 : ‖(EuclideanSpace.equiv I ℂ).symm (A *ᵥ φ)‖ ≤ ‖A‖ := by
    have h2 : ‖(EuclideanSpace.equiv I ℂ).symm (A *ᵥ φ)‖
        ≤ ‖A‖ * ‖(EuclideanSpace.equiv I ℂ).symm φ‖ := hkey
    rw [hone, mul_one] at h2
    exact h2
  calc ‖(EuclideanSpace.equiv I ℂ).symm (A *ᵥ φ)‖ ^ 2
      ≤ ‖A‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ Δ ^ 2 := pow_le_pow_left₀ (norm_nonneg A) h 2

/-- Uniform failure bound for the corrected Lemma 2 circuit with the proximity hypothesis
in Euclidean operator-norm form: there is a uniform constant `C = 1` such
that on every non-degenerate qubit register `Fin (2 ^ n)` (`0 < n`), for all unitary
`Ua, Ub` with `‖Ua - Ub‖ ≤ Δ`, the corrected failure probability is at most
`C * κ * Δ² / (κ + 1)²` on every normalized input. -/
theorem uniform_nqubit_lcu_failure_opNorm : ∃ C : ℝ, C = 1 ∧ 0 < C ∧
    ∀ (n : ℕ), 0 < n →
    ∀ (Ua Ub : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ),
      Ua ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ →
      Ub ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ →
    ∀ (κ Δ : ℝ), 0 ≤ κ → 0 ≤ Δ → ‖Ua - Ub‖ ≤ Δ →
    ∀ (ψ : QState (Fin (2 ^ n))), Normalized ψ →
      lemma2FailureProbCorrected κ Ua Ub ψ ≤ C * κ * Δ ^ 2 / (κ + 1) ^ 2 := by
  refine ⟨1, rfl, one_pos, ?_⟩
  intro n hn Ua Ub hUa hUb κ Δ hκ hΔ hop ψ hψ
  have hclose : ∀ φ : QState (Fin (2 ^ n)), Normalized φ →
      (∑ x : Fin (2 ^ n), ‖((Ua - Ub) *ᵥ φ) x‖ ^ 2) ≤ Δ ^ 2 :=
    fun φ hφ => sum_sq_mulVec_le (Ua - Ub) hop φ hφ
  have h := lemma2NearbyFailureCorrected (Fin (2 ^ n)) κ hκ Ua Ub hUa hUb Δ hΔ hclose ψ hψ
  rw [one_mul]
  exact h

/-- Uniform failure bound for the corrected Lemma 2 circuit with the proximity hypothesis
in uniform state-action form: there is a uniform constant `C = 1` such that on every
non-degenerate qubit register `Fin (2 ^ n)` (`0 < n`), for all unitary `Ua, Ub` whose
difference maps every normalized state to a vector of squared norm at most `Δ²`, the
corrected failure probability is at most `C * κ * Δ² / (κ + 1)²` on every normalized
input. -/
theorem uniform_nqubit_lcu_failure_stateAction : ∃ C : ℝ, C = 1 ∧ 0 < C ∧
    ∀ (n : ℕ), 0 < n →
    ∀ (Ua Ub : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ),
      Ua ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ →
      Ub ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ →
    ∀ (κ Δ : ℝ), 0 ≤ κ → 0 ≤ Δ →
      (∀ φ : QState (Fin (2 ^ n)), Normalized φ →
        (∑ x : Fin (2 ^ n), ‖((Ua - Ub) *ᵥ φ) x‖ ^ 2) ≤ Δ ^ 2) →
    ∀ (ψ : QState (Fin (2 ^ n))), Normalized ψ →
      lemma2FailureProbCorrected κ Ua Ub ψ ≤ C * κ * Δ ^ 2 / (κ + 1) ^ 2 := by
  refine ⟨1, rfl, one_pos, ?_⟩
  intro n hn Ua Ub hUa hUb κ Δ hκ hΔ hclose ψ hψ
  have h := lemma2NearbyFailureCorrected (Fin (2 ^ n)) κ hκ Ua Ub hUa hUb Δ hΔ hclose ψ hψ
  rw [one_mul]
  exact h

end Qatlib.Papers.HamLCUSim12.FullSimulation
