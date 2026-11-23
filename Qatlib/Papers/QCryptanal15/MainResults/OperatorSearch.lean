/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QCryptanal15.MainResults.SimpleDifferential.Q2Distinguisher
public import Qatlib.Foundations.PureStateMath.Reflection.Basic
public import Qatlib.Foundations.OperatorErrors.OperatorError

@[expose] public section

/-!
# Operator and state-space contracts for the Grover search step

The paper's marked-set search uses a phase oracle followed by reflection about the
uniform state.  This module instantiates that step on a finite, nonempty Hilbert
space.  It proves the actual operator-norm and state-norm statements needed by the
search analysis, and exposes the constant in the finite-domain half-success budget
before the instance quantifiers.

The cryptographic oracle, the random-function comparison, and Theorem 5's
quantum-walk pair search remain outside this interface.  The results here
concern the finite Grover step used by the simple-differential distinguisher:
diffusion after the marked-set phase oracle.
-/

set_option autoImplicit false
set_option warningAsError true
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib.Papers.QCryptanal15.MainResults.SimpleDifferential
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.QCryptanal15.MainResults

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- One Grover search step, namely the uniform-state diffusion after the marked-set
phase oracle. -/
def groverStep (A : Finset I) : Matrix I I ℂ := Diffusion I * SetOracle A

/-- The finite-domain Grover step is unitary whenever the search domain is nonempty. -/
theorem grover_step_unitary (A : Finset I) (hI : 0 < Fintype.card I) :
    groverStep A ∈ Matrix.unitaryGroup I ℂ := by
  exact mul_mem (diffusion_unitary hI) (setOracle_unitary A)

/-- The Grover step has exact Euclidean operator norm one. -/
theorem grover_step_l2Operator_norm (A : Finset I) [Nonempty I]
    (hI : 0 < Fintype.card I) :
    ‖groverStep A‖ = 1 := by
  exact CStarRing.norm_of_mem_unitary (grover_step_unitary A hI)

/-- Applying one Grover step preserves the actual `EuclideanSpace` norm of every state. -/
theorem grover_step_euclidean_norm (A : Finset I) (hI : 0 < Fintype.card I)
    (ψ : EuclideanSpace ℂ I) :
    ‖(WithLp.toLp 2 (groverStep A *ᵥ ψ.ofLp) : EuclideanSpace ℂ I)‖ = ‖ψ‖ := by
  have hsq := sum_normSq_mulVec_of_mem_unitaryGroup
    (grover_step_unitary A hI) ψ.ofLp
  have hsq' :
      ‖(WithLp.toLp 2 (groverStep A *ᵥ ψ.ofLp) : EuclideanSpace ℂ I)‖ ^ 2 =
        ‖ψ‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simpa only [Complex.normSq_eq_norm_sq] using hsq
  nlinarith [norm_nonneg (WithLp.toLp 2 (groverStep A *ᵥ ψ.ofLp) : EuclideanSpace ℂ I),
    norm_nonneg ψ]

/-- A single positive constant works for every nonempty finite search domain in the
half-success Grover budget. -/
theorem grover_half_success_uniform_constant :
    ∃ C : ℝ, 0 < C ∧
      ∀ {J : Type*} [Fintype J] [DecidableEq J]
        (A : Finset J) (eps : ℝ),
        0 < eps → eps < 1 →
        (A.card : ℝ) / (Fintype.card J : ℝ) = eps →
        ∃ k : ℕ,
          0 < Fintype.card J ∧
          (k : ℝ) ≤ C / Real.sqrt eps + 1 ∧
            1 / 2 ≤ MeasureProb (GroverState A k) A := by
  refine ⟨Real.pi / 8, by positivity, ?_⟩
  intro J _ _ A eps heps0 heps1 hfrac
  have hJ : 0 < Fintype.card J := by
    by_contra h
    have hzero : (Fintype.card J : ℝ) = 0 := by
      exact_mod_cast Nat.eq_zero_of_not_pos h
    rw [hzero, div_zero] at hfrac
    linarith
  obtain ⟨k, hk, hsuccess⟩ :=
    grover_half_budget_iterations hJ A eps heps0 heps1 hfrac
  refine ⟨k, hJ, ?_, hsuccess⟩
  calc
    (k : ℝ) ≤ Real.pi / (8 * Real.sqrt eps) + 1 := hk
    _ = (Real.pi / 8) / Real.sqrt eps + 1 := by
      field_simp [Real.sqrt_ne_zero'.mpr heps0]

end Qatlib.Papers.QCryptanal15.MainResults
