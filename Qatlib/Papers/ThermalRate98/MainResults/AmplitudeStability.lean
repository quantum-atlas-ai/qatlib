/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.SpectralReadout.PhaseReadout.BornPerturbation

@[expose] public section

/-!
# Euclidean stability of Eq. 47 amplitude recovery

Equation 47 of [LidarWang1999] recovers position amplitudes by applying the
unitary matrix whose columns are energy eigenvectors. Its adjoint gives the
exact energy coordinates of the position state. A unitary transform preserves
Euclidean ℓ² amplitude error, and replacing the exact energy coordinates with a
normalized approximation changes any position event probability by at most
twice that error.

The bound assumes an exact coefficient matrix and exact application of that
matrix. Estimating its entries and conditioning on energy measurement outcomes
are separate steps.

## Main statements

* `eq47_unitary_recovery_isometry`: unitary recovery preserves Euclidean error.
* `eq47_born_stability_uniform`: a uniform factor-two Born-mass stability bound.
* `eq47_encoded_qubits_born_stability`: stability relative to the exact position state.

## References

* [Lidar and Wang, 1999][LidarWang1999]
-/

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.SpectralReadout.PhaseReadout
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.ThermalRate98.MainResults

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

omit [Nonempty I] in

/-- A unitary Eq. 47 coefficient transform preserves the Euclidean ℓ² distance
between two amplitude vectors.  See [LidarWang1999]. -/
theorem eq47_unitary_recovery_isometry (A : Matrix I I ℂ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (ξ ζ : QState I) :
    ‖toEuclidean_fromVec (ApplyGate A ξ - ApplyGate A ζ)‖ =
      ‖toEuclidean_fromVec (ξ - ζ)‖ := by
  have hsub : ApplyGate A ξ - ApplyGate A ζ = ApplyGate A (ξ - ζ) := by
    funext i
    simp only [ApplyGate, Matrix.mulVec, dotProduct, Pi.sub_apply]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => (mul_sub _ _ _).symm
  rw [hsub, ← toEuclideanCLM_applyGate A (ξ - ζ)]
  exact norm_toEuclideanCLM_of_mem_unitaryGroup hA _

/-- There is a dimension-independent constant `C` such that, for every nonempty
finite register, every unitary Eq. 47 transform, and every pair of normalized
amplitudes, each Born event changes by at most `C` times their Euclidean input
error.  The proof gives `C = 2`.  See [LidarWang1999]. -/
theorem eq47_born_stability_uniform :
    ∃ C > 0, ∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I],
      ∀ (A : Matrix I I ℂ), A ∈ Matrix.unitaryGroup I ℂ →
      ∀ (ξ ζ : QState I), Normalized ξ → Normalized ζ →
      ∀ S : Finset I,
        |MeasureProb (ApplyGate A ξ) S - MeasureProb (ApplyGate A ζ) S| ≤
          C * ‖toEuclidean_fromVec (ξ - ζ)‖ := by
  refine ⟨2, by norm_num, fun I _ _ _ A hA ξ ζ hξ hζ S => ?_⟩
  exact measureProb_applyGate_sub_le_two_mul_l2 A ξ ζ S hA hξ hζ

/-- On every positive-qubit register, reconstructing position amplitudes from
approximate energy coordinates changes any position event probability by at most
a uniform constant times the Euclidean error in those coordinates. The exact
energy coordinates are obtained from the position state by the adjoint of the
coefficient matrix in Equation 47 of [LidarWang1999]. -/
theorem eq47_encoded_qubits_born_stability :
    ∃ C > 0, ∀ ν : ℕ, 0 < ν →
      ∀ (A : Matrix (Fin (2 ^ ν)) (Fin (2 ^ ν)) ℂ),
        A ∈ Matrix.unitaryGroup (Fin (2 ^ ν)) ℂ →
        ∀ (ψ ξ : QState (Fin (2 ^ ν))), Normalized ψ → Normalized ξ →
        ∀ S : Finset (Fin (2 ^ ν)),
          |MeasureProb (ApplyGate A ξ) S - MeasureProb ψ S| ≤
            C * ‖toEuclidean_fromVec (ξ - ApplyGate (star A) ψ)‖ := by
  obtain ⟨C, hC, h⟩ := eq47_born_stability_uniform
  refine ⟨C, hC, ?_⟩
  intro ν _ A hA ψ ξ hψ hξ S
  have hrec : ApplyGate A (ApplyGate (star A) ψ) = ψ := by
    rw [← applyGate_mul, Matrix.mem_unitaryGroup_iff.mp hA, applyGate_one]
  simpa only [hrec] using
    h (Fin (2 ^ ν)) A hA ξ (ApplyGate (star A) ψ) hξ
      (normalized_applyGate (Unitary.star_mem hA) hψ) S

end Qatlib.Papers.ThermalRate98.MainResults
