/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.SchattenDiamond.DiamondNorm.FiniteDiamondNorm
public import Qatlib.Concepts.MixedFidelity.FidelityMetric.ChannelHelpers.RankOneTraceNormEquality
public import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge

@[expose] public section

/-!
# From finite diamond distance to output trace and observable errors

Appendix A of [Campbell2019] converts a diamond-norm estimate for a pair of channels into
two downstream guarantees: the trace distance between the outputs on any normalized input,
and the difference of expectation values for any bounded observable. This module proves both
conversions directly from the locked finite-reference diamond norm, with the reference
dimension fixed to one. The factor `2` relating the diamond distance to the raw trace norm is
kept explicit and the same uniform constant works in every dimension, so the result applies
unchanged to the qDRIFT channel comparisons of the paper.

The pure-state form uses `EuclideanSpace` amplitudes and the `L²` operator norm of the
observable, matching the physical setting of the source.

## Main statements

* `traceNorm_outerProduct_of_normalized`: a normalized pure state has trace norm one.
* `finite_diamond_output_and_observable_transfer`: a uniform output-trace and observable
  transfer bound.
* `finite_diamond_pure_state_observable_transfer`: the same observable bound for a normalized
  `EuclideanSpace` state.

## References

* [Campbell, 2019][Campbell2019]
* [Watrous, 2018][Watrous2018]
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.SchattenDiamond.DiamondNorm
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Papers.RandCompiler19.DiamondTools

open Matrix
open scoped Matrix.Norms.L2Operator ENNReal BigOperators

/-- A normalized pure state has a rank-one density matrix of trace norm one. -/
theorem traceNorm_outerProduct_of_normalized {D : ℕ} (ψ : QState (Fin D))
    (hψ : Normalized ψ) : Matrix.traceNorm (outerProduct ψ) = 1 := by
  have hvec : outerProduct ψ = Matrix.vecMulVec ψ (star ψ) := by
    ext i j
    simp [outerProduct, Matrix.vecMulVec, Pi.star_apply]
  rw [hvec, Qatlib.Concepts.MixedFidelity.FidelityMetric.traceNorm_rankOne_eq]
  have hsum : (∑ i, Complex.normSq (ψ i)) = 1 := by
    have h := hψ
    unfold Normalized at h
    simpa [Complex.normSq_eq_norm_sq] using h
  rw [hsum]
  norm_num

/-- If two maps are within finite diamond distance `δ`, then on every input of trace norm at
  most one the raw trace norm of the output difference is at most `2 * δ`, and the modulus
  of the trace difference tested against any `M` is at most `2 * ‖M‖ * δ`. The constant is
  uniform in the dimension, the maps and the accuracy. -/
theorem finite_diamond_output_and_observable_transfer :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D : ℕ) (_ : 0 < D) (T S : Operator D →ₗ[ℂ] Operator D)
        (δ : ℝ) (_ : 0 ≤ δ),
        finiteDiamondDistance T S ≤ ENNReal.ofReal δ →
        ∀ (ρ M : Operator D), Matrix.traceNorm ρ ≤ 1 →
          Matrix.traceNorm (T ρ - S ρ) ≤ C * δ ∧
          ‖Matrix.trace (M * T ρ) - Matrix.trace (M * S ρ)‖ ≤
            C * ‖M‖ * δ := by
  refine ⟨2, by norm_num, ?_⟩
  intro D hD T S δ hδ hdiam ρ M hρ
  have hnorm : finiteDiamondNorm (T - S) ≤ ENNReal.ofReal (2 * δ) := by
    have h := mul_le_mul_of_nonneg_left hdiam (by positivity : (0 : ℝ≥0∞) ≤ 2)
    rw [finiteDiamondDistance] at h
    have hconst : (2 : ℝ≥0∞) * ((1 / 2 : ℝ≥0∞) * finiteDiamondNorm (T - S)) =
        finiteDiamondNorm (T - S) := by
      rw [← mul_assoc]
      have h2half : (2 : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) = 1 := by
        rw [show (1 / 2 : ℝ≥0∞) = (2 : ℝ≥0∞)⁻¹ by norm_num]
        exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
      rw [h2half, one_mul]
    rw [hconst] at h
    have hof : (2 : ℝ≥0∞) * ENNReal.ofReal δ = ENNReal.ofReal (2 * δ) := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rwa [hof] at h
  let e : Fin D × Fin 1 ≃ Fin D := Equiv.prodUnique (Fin D) (Fin 1)
  let X : Matrix (Fin D × Fin 1) (Fin D × Fin 1) ℂ := Matrix.reindex e.symm e.symm ρ
  have hXnorm : Matrix.traceNorm X ≤ 1 := by
    dsimp only [X]
    rw [diamond_traceNorm_reindex e.symm]
    exact hρ
  have htensor : tensorLeft (T - S) X = Matrix.reindex e.symm e.symm (T ρ - S ρ) := by
    ext p q
    simp [tensorLeft, X, e, Equiv.prodUnique]
    change (T - S) ρ p.1 q.1 = T ρ p.1 q.1 - S ρ p.1 q.1
    rfl
  have hout : Matrix.traceNorm (T ρ - S ρ) ≤ 2 * δ := by
    have huniform :=
      (finiteDiamondNorm_le_iff_uniform D D (T - S) (2 * δ) (by positivity)).mp
        hnorm 1 X
    calc
      Matrix.traceNorm (T ρ - S ρ) = Matrix.traceNorm (tensorLeft (T - S) X) := by
        rw [htensor, diamond_traceNorm_reindex e.symm]
      _ ≤ (2 * δ) * Matrix.traceNorm X := huniform
      _ ≤ (2 * δ) * 1 := mul_le_mul_of_nonneg_left hXnorm (by positivity)
      _ = 2 * δ := mul_one _
  refine ⟨hout, ?_⟩
  rw [← Matrix.trace_sub, ← Matrix.mul_sub]
  calc
    ‖Matrix.trace (M * (T ρ - S ρ))‖ ≤
        Matrix.traceNorm (M * (T ρ - S ρ)) := Matrix.abs_trace_le_traceNorm _
    _ ≤ ‖M‖ * Matrix.traceNorm (T ρ - S ρ) :=
      Matrix.traceNorm_mul_le_opNorm_traceNorm _ _
    _ ≤ ‖M‖ * (2 * δ) := mul_le_mul_of_nonneg_left hout (norm_nonneg M)
    _ = 2 * ‖M‖ * δ := by ring

/-- The observable transfer bound specialized to a normalized state in `EuclideanSpace`. -/
theorem finite_diamond_pure_state_observable_transfer :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D : ℕ) (_ : 0 < D) (T S : Operator D →ₗ[ℂ] Operator D)
        (δ : ℝ) (_ : 0 ≤ δ),
        finiteDiamondDistance T S ≤ ENNReal.ofReal δ →
        ∀ (ψ : EuclideanSpace ℂ (Fin D)), ‖ψ‖ = 1 →
          ∀ (M : Operator D),
            ‖Matrix.trace (M * T (outerProduct (toVec_fromEuclidean ψ))) -
                Matrix.trace (M * S (outerProduct (toVec_fromEuclidean ψ)))‖ ≤
              C * ‖M‖ * δ := by
  obtain ⟨C, hC, h⟩ := finite_diamond_output_and_observable_transfer
  refine ⟨C, hC, ?_⟩
  intro D hD T S δ hδ hdiam ψ hψ M
  have hnorm : Normalized (toVec_fromEuclidean ψ) :=
    (normalized_iff_norm_toEuclidean_fromVec _).mpr (by
      rw [toEuclidean_fromVec_toVec_fromEuclidean]
      exact hψ)
  have hρ : Matrix.traceNorm (outerProduct (toVec_fromEuclidean ψ)) ≤ 1 := by
    exact le_of_eq (traceNorm_outerProduct_of_normalized _ hnorm)
  exact (h D hD T S δ hδ hdiam (outerProduct (toVec_fromEuclidean ψ)) M hρ).2

end Qatlib.Papers.RandCompiler19.DiamondTools
