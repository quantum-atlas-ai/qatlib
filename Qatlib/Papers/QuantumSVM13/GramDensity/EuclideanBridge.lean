/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QuantumSVM13.GramDensity
public import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge

@[expose] public section

/-!
# Euclidean Gram-state and classifier bridges

This module transports the weighted training state used by the quantum support-vector-machine
kernel construction to the genuine finite-dimensional `EuclideanSpace` model.  It also records the
Euclidean swap-test branch identity and an operator-norm certificate for the identity action on the
prepared state.  The hypotheses exclude empty datasets and zero training rows.

The preparation and circuit costs of the source algorithm are outside this interface.  The results
here certify its finite-dimensional state and readout algebra in the true ℓ² geometry.

References

* [RebentrostMohseniLloyd2014]
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.GramReadout
open Qatlib.Papers.QuantumSVM13.GramDensity

namespace Qatlib.Papers.QuantumSVM13.GramDensity

variable {M N : ℕ}

/-- The actual weighted Gram state represented in complex Euclidean space. -/
noncomputable def gramStateEuclidean (x : Fin M → Fin N → ℝ) :
    EuclideanSpace ℂ (Fin M × Fin N) :=
  toEuclidean_fromVec (gramState (dataUnit x) (dataWeight x))

/-- A nonempty dataset with nonzero rows produces a unit Euclidean ℓ² Gram state
[RebentrostMohseniLloyd2014]. -/
theorem gramState_euclidean_norm (x : Fin M → Fin N → ℝ) (hM : 0 < M)
    (hx : ∀ i, 0 < ∑ k, (x i k) ^ 2) :
    ‖gramStateEuclidean x‖ = 1 := by
  unfold gramStateEuclidean
  exact (normalized_iff_norm_toEuclidean_fromVec _).mp
    (kernelDensity_bridge x hM hx).1

/-- The finite-dimensional swap-test minus branch is the squared Euclidean distance to the
half-difference, hence equals `(1 - ⟪ψ, φ⟫_ℝ) / 2` for unit real states
[RebentrostMohseniLloyd2014]. -/
noncomputable def euclideanMinusBranchWeight (ψ φ : EuclideanSpace ℝ (Fin N)) : ℝ :=
  ‖(1 / 2 : ℝ) • (ψ - φ)‖ ^ 2

/-- Euclidean swap-test readout classifies the sign of the real overlap at the one-half threshold.
The norm is the genuine `EuclideanSpace` ℓ² norm. -/
theorem euclidean_swap_test_branch_formula (ψ φ : EuclideanSpace ℝ (Fin N))
    (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    euclideanMinusBranchWeight ψ φ = (1 - ⟪ψ, φ⟫_ℝ) / 2 := by
  have hsub : ‖ψ - φ‖ ^ 2 = 2 - 2 * ⟪ψ, φ⟫_ℝ := by
    rw [← real_inner_self_eq_norm_sq, inner_sub_sub_self]
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hψ, hφ]
    rw [real_inner_comm]
    ring
  unfold euclideanMinusBranchWeight
  have hhalf : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by norm_num
  rw [norm_smul, hhalf, mul_pow, hsub]
  ring

/-- The identity matrix acts isometrically on the prepared Gram state, and its Euclidean L2 operator
norm is exactly one.  This is an explicit operator certificate for the state-space consumer
[RebentrostMohseniLloyd2014]. -/
theorem gramState_identity_operator_certificate (x : Fin M → Fin N → ℝ) (hM : 0 < M)
    (hx : ∀ i, 0 < ∑ k, (x i k) ^ 2) :
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin M × Fin N))
        (1 : Matrix (Fin M × Fin N) (Fin M × Fin N) ℂ) (gramStateEuclidean x) =
      gramStateEuclidean x ∧
      ‖(1 : Matrix (Fin M × Fin N) (Fin M × Fin N) ℂ)‖ = 1 := by
  refine ⟨?_, ?_⟩
  · simp
  · rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    have hN : 0 < N := by
      by_contra hN0
      have hN' : N = 0 := Nat.eq_zero_of_not_pos hN0
      subst N
      have hrow := hx ⟨0, hM⟩
      simp at hrow
    have hprod : (Finset.univ : Finset (Fin M × Fin N)).Nonempty := by
      refine ⟨(⟨0, hM⟩, ⟨0, hN⟩), Finset.mem_univ _⟩
    rw [Pi.norm_def, Finset.sup_const hprod]
    norm_num

end Qatlib.Papers.QuantumSVM13.GramDensity
