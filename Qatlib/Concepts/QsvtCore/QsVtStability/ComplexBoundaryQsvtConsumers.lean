/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.QsVtStability.ComplexBoundaryQsvt
import Qatlib.Concepts.BlockEncoding.Postselection

/-!
# Conditional outputs under boundary QSVT errors

This module transfers the boundary operator-error estimate to output norms and normalized states
for the same odd complex-phase word. In the QSVT robustness framework of [GilyenSuLowWiebe2019],
an error smaller than the ideal output norm gives a success-norm lower bound and a
conditional-state distance bound.

## Main statements

* `complex_boundary_same_word_conditional_output`: Bound the actual output norm and normalized
  error using the boundary robustness rate.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open Qatlib.Concepts.BlockEncoding.Postselection

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Qatlib.Concepts.QsvtCore.QsVtStability
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- For an odd unit-phase word applied to an approximate block encoding, let `η = 4 * zs.length
* √(ε / α)` and let `τ` be the ideal output norm. If `η < τ`, the actual output has squared
norm at least `(τ - η) ^ 2` and normalized error at most `2 * η / τ` [GilyenSuLowWiebe2019]. -/
theorem complex_boundary_same_word_conditional_output :
    ∀ (H I O : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
      [Fintype O] [DecidableEq O] (A : Matrix O I ℂ) (U : Matrix H H ℂ)
      (L : Matrix H O ℂ) (R : Matrix H I ℂ) (α ε : ℝ) (base : ℂ) (zs : List ℂ),
      BlockEncoding A U L R α ε → ‖(α⁻¹ : ℝ) • A‖ ≤ 1 →
      IsPhase base → (∀ z ∈ zs, IsPhase z) → zs.length % 2 = 1 →
      ∀ ψ : QState I, Normalized ψ →
      let y := compress L (phasedAlternating U (rangeProjector R) (rangeProjector L) base zs) R *ᵥ ψ
      let v := oddSingularTransform ((α⁻¹ : ℝ) • A) (interiorResponse base zs) *ᵥ ψ
      let τ := ‖toEuclidean_fromVec v‖
      let η := 4*zs.length*Real.sqrt (ε/α)
      η < τ → (τ-η)^2 ≤ ‖toEuclidean_fromVec y‖^2 ∧
        ‖toEuclidean_fromVec (((‖toEuclidean_fromVec y‖⁻¹ : ℝ) : ℂ) • y -
          ((τ⁻¹ : ℝ) : ℂ) • v)‖ ≤ 2*η/τ := by
  intro H I O _ _ _ _ _ _ A U L R α ε base zs h hA hb hzs hodd ψ hψ y v τ η hgap
  have herr := (complex_boundary_actual_encoded_word H I O A U L R α ε base zs
    h hA hb hzs hodd).1
  have hclose : ‖toEuclidean_fromVec y-toEuclidean_fromVec v‖ ≤ η := by
    have hn : ‖toEuclidean_fromVec ψ‖ = 1 := (normalized_iff_norm_toEuclidean_fromVec ψ).mp hψ
    have hm := l2_norm_mulVec_fromVec_le
      (compress L (phasedAlternating U (rangeProjector R) (rangeProjector L) base zs) R -
        oddSingularTransform ((α⁻¹ : ℝ) • A) (interiorResponse base zs)) ψ
    rw [hn, mul_one] at hm
    have hm' : ‖toEuclidean_fromVec y-toEuclidean_fromVec v‖ ≤
      ‖compress L (phasedAlternating U (rangeProjector R) (rangeProjector L) base zs) R -
        oddSingularTransform ((α⁻¹ : ℝ) • A) (interiorResponse base zs)‖ := by
      simpa only [Matrix.sub_mulVec, toEuclidean_fromVec, WithLp.toLp_sub] using! hm
    exact hm'.trans herr
  have hlow : τ-η ≤ ‖toEuclidean_fromVec y‖ := by
    have hh := (norm_sub_norm_le (toEuclidean_fromVec v) (toEuclidean_fromVec y)).trans
      (by simpa only [norm_sub_rev] using! hclose)
    dsimp only [τ]
    linarith
  refine ⟨pow_le_pow_left₀ (by linarith) hlow 2, ?_⟩
  simpa only [NormedSpace.normalize, toEuclidean_fromVec, WithLp.toLp_sub,
    WithLp.toLp_smul, Complex.coe_smul] using! (normalize_error_of_gap hclose hgap).2

end Qatlib.Concepts.QsvtCore.QsVtStability
