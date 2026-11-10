/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsDefs
import Qatlib.Concepts.ReferenceError.DensityToRaw.ChannelTraceContraction
import Qatlib.Concepts.GibbsMetropolis.RationalBath.ApproximateRationalGibbs
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteLaws.FiniteOutputDistinguishability
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace Qatlib.Concepts.MixedFidelity.FidelityMetric.FinitePOVMTraceDistance
open Matrix Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt
open scoped BigOperators Classical ComplexOrder
noncomputable section
variable {O : Type} [Fintype O] [DecidableEq O] {d : ℕ}

def recordMap (E : Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt.FinitePOVM O d) : MatrixMap (Fin d) O ℂ where
  toFun A := Matrix.diagonal fun o => Matrix.trace (E.effect o * A)
  map_add' := by intro A B; ext i j; by_cases h : i=j <;> simp [Matrix.mul_add, Matrix.trace_add, Matrix.diagonal_apply,h]
  map_smul' := by intro c A; ext i j; simp [Matrix.trace_smul, Matrix.diagonal_apply, mul_ite]

theorem record_positive (E : Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt.FinitePOVM O d) : (Qatlib.Concepts.MixedFidelity.FidelityMetric.FinitePOVMTraceDistance.recordMap E).IsPositive := by
  intro A hA
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro o
  have hp : ((E.factor o)*A*(E.factor o)ᴴ).PosSemidef :=
    hA.mul_mul_conjTranspose_same (E.factor o)
  have he : Matrix.trace (E.effect o * A) =
      (E.weight o : ℂ) * Matrix.trace ((E.factor o)*A*(E.factor o)ᴴ) := by
    rw [E.effect_eq_factor, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    congr 1
    exact (Matrix.trace_mul_cycle (A:=E.factor o) (B:=A) (C:=(E.factor o)ᴴ)).symm
  rw [he]
  exact mul_nonneg (by exact_mod_cast E.weight_nonneg o) hp.trace_nonneg

theorem record_tracePreserving (E : Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt.FinitePOVM O d) : (Qatlib.Concepts.MixedFidelity.FidelityMetric.FinitePOVMTraceDistance.recordMap E).IsTracePreserving := by
  intro A
  simp only [Qatlib.Concepts.MixedFidelity.FidelityMetric.FinitePOVMTraceDistance.recordMap,
      LinearMap.coe_mk, AddHom.coe_mk, Matrix.trace_diagonal]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, E.effect_sum, Matrix.one_mul]

theorem record_density (E : Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt.FinitePOVM O d) (A : Qatlib.Foundations.PureStateMath.Operator d) (hA : Qatlib.Foundations.PureStateMath.IsDensityOperator A) :
    Qatlib.Concepts.MixedFidelity.FidelityMetric.FinitePOVMTraceDistance.recordMap E A = Matrix.diagonal (fun o => ((Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt.povmRecordLaw E A hA).prob o : ℂ)) := by
  change Matrix.diagonal (fun o => Matrix.trace (E.effect o*A)) = _
  apply congrArg Matrix.diagonal
  funext o
  exact Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt.povmBorn_trace_real E A hA o

private theorem diagonal_norm (v : O → ℝ) :
    Matrix.traceNorm (Matrix.diagonal fun o => (v o : ℂ)) = ∑ o, |v o| := by
  open MatrixOrder in
  have hs : CFC.sqrt ((Matrix.diagonal fun i => (v i : ℂ))ᴴ *
      Matrix.diagonal (fun i => (v i : ℂ))) = Matrix.diagonal (fun i => ((|v i| : ℝ) : ℂ)) := by
    apply CFC.sqrt_unique
    · rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
      congr 1; funext i
      simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
      congr 1
      nlinarith [sq_abs (v i)]
    · apply Matrix.PosSemidef.nonneg
      rw [Matrix.posSemidef_diagonal_iff]
      intro i
      exact_mod_cast abs_nonneg (v i)
  unfold Matrix.traceNorm
  rw [hs]
  simp

theorem measured_tv_le (E : Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt.FinitePOVM O d) (A B : Qatlib.Foundations.PureStateMath.Operator d)
    (hA : Qatlib.Foundations.PureStateMath.IsDensityOperator A) (hB : Qatlib.Foundations.PureStateMath.IsDensityOperator B) :
    Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteInformationDivergence.tv (Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt.povmRecordLaw E A hA) (Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt.povmRecordLaw E B hB) ≤
      Matrix.traceNorm (A-B)/2 := by
  have hc := Qatlib.Concepts.ReferenceError.DensityToRaw.positive_trace_preserving_hermitian_trace_contraction (Qatlib.Concepts.MixedFidelity.FidelityMetric.FinitePOVMTraceDistance.recordMap E)
    (Qatlib.Concepts.MixedFidelity.FidelityMetric.FinitePOVMTraceDistance.record_positive E) (Qatlib.Concepts.MixedFidelity.FidelityMetric.FinitePOVMTraceDistance.record_tracePreserving E) (hA.1.isHermitian.sub hB.1.isHermitian)
  rw [map_sub,
      Qatlib.Concepts.MixedFidelity.FidelityMetric.FinitePOVMTraceDistance.record_density E A hA, Qatlib.Concepts.MixedFidelity.FidelityMetric.FinitePOVMTraceDistance.record_density E B hB, Matrix.diagonal_sub] at hc
  simp only [← Complex.ofReal_sub] at hc
  rw [diagonal_norm] at hc
  exact div_le_div_of_nonneg_right hc (by norm_num)

theorem measured_advantage_le (E : Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt.FinitePOVM O d) (A B : Qatlib.Foundations.PureStateMath.Operator d)
    (hA : Qatlib.Foundations.PureStateMath.IsDensityOperator A) (hB : Qatlib.Foundations.PureStateMath.IsDensityOperator B) :
    Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteOutputDistinguishability.advantage (Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt.povmRecordLaw E A hA) (Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt.povmRecordLaw E B hB) ≤
      Matrix.traceNorm (A-B)/2 := by
  rw [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteOutputDistinguishability.advantage_eq_tv]
  exact Qatlib.Concepts.MixedFidelity.FidelityMetric.FinitePOVMTraceDistance.measured_tv_le E A B hA hB

theorem after_common_channel {k : ℕ} (E : Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt.FinitePOVM O k)
    (T : MatrixMap (Fin d) (Fin k) ℂ) (hpos : T.IsPositive) (htp : T.IsTracePreserving)
    (A B : Qatlib.Foundations.PureStateMath.Operator d) (hA : Qatlib.Foundations.PureStateMath.IsDensityOperator A) (hB : Qatlib.Foundations.PureStateMath.IsDensityOperator B) :
    let hTA : Qatlib.Foundations.PureStateMath.IsDensityOperator (T A) :=
        ⟨hpos hA.1, (htp A).trans hA.2⟩
    let hTB : Qatlib.Foundations.PureStateMath.IsDensityOperator (T B) :=
        ⟨hpos hB.1, (htp B).trans hB.2⟩
    Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteOutputDistinguishability.advantage (Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt.povmRecordLaw E (T A) hTA) (Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt.povmRecordLaw E (T B) hTB) ≤
      Matrix.traceNorm (A-B)/2 := by
  (try dsimp only)
  apply (Qatlib.Concepts.MixedFidelity.FidelityMetric.FinitePOVMTraceDistance.measured_advantage_le E (T A) (T B) _ _).trans
  have h := Qatlib.Concepts.ReferenceError.DensityToRaw.positive_trace_preserving_hermitian_trace_contraction T hpos htp
    (hA.1.isHermitian.sub hB.1.isHermitian)
  rw [map_sub] at h
  exact div_le_div_of_nonneg_right h (by norm_num)

end
end Qatlib.Concepts.MixedFidelity.FidelityMetric.FinitePOVMTraceDistance
