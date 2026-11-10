/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedFidelity.FidelityMetric.ChannelHelpers.RankOneTraceNormEquality
import Qatlib.Concepts.MixedFidelity.FidelityMetric.ChannelHelpers.FinitePOVMTraceDistance
import Qatlib.Concepts.GibbsMetropolis.RationalBath.ApproximateRationalGibbs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace Qatlib.Concepts.MixedFidelity.FidelityMetric.BadLabelMixtureBound
open Matrix Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt
open scoped BigOperators Classical ComplexOrder
noncomputable section
variable {X : Type} [Fintype X] [DecidableEq X] {d k : ℕ}

def average (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (rho : X → Qatlib.Foundations.PureStateMath.DensityOperator d) : Qatlib.Foundations.PureStateMath.Operator d :=
  ∑ x, (p.prob x : ℂ) • (rho x).val

omit [DecidableEq X] in

theorem average_density (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (rho : X → Qatlib.Foundations.PureStateMath.DensityOperator d) :
    Qatlib.Foundations.PureStateMath.IsDensityOperator (Qatlib.Concepts.MixedFidelity.FidelityMetric.BadLabelMixtureBound.average p rho) := by
  constructor
  · exact Matrix.posSemidef_sum Finset.univ fun x _ =>
      (rho x).property.1.smul (RCLike.ofReal_nonneg.mpr (p.nonneg x))
  · simp only [Qatlib.Concepts.MixedFidelity.FidelityMetric.BadLabelMixtureBound.average,Matrix.trace_sum,Matrix.trace_smul,smul_eq_mul]
    simp_rw [(rho _).property.2,mul_one]
    rw [← Complex.ofReal_sum,p.sum_one,Complex.ofReal_one]

def state (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (rho : X → Qatlib.Foundations.PureStateMath.DensityOperator d) : Qatlib.Foundations.PureStateMath.DensityOperator d :=
  ⟨Qatlib.Concepts.MixedFidelity.FidelityMetric.BadLabelMixtureBound.average p rho,Qatlib.Concepts.MixedFidelity.FidelityMetric.BadLabelMixtureBound.average_density p rho⟩

theorem density_distance_le_two (rho sigma : Qatlib.Foundations.PureStateMath.DensityOperator d) :
    Matrix.traceNorm (rho.val-sigma.val) ≤ 2 := by
  have hr : Matrix.traceNorm rho.val=1 := by
    rw [Qatlib.Concepts.GibbsMetropolis.RationalBath.rationalGibbs_psd_traceNorm _ rho.property.1,rho.property.2]; rfl
  have hs : Matrix.traceNorm sigma.val=1 := by
    rw [Qatlib.Concepts.GibbsMetropolis.RationalBath.rationalGibbs_psd_traceNorm _ sigma.property.1,sigma.property.2]; rfl
  have h := Matrix.traceNorm_add_le rho.val (-sigma.val)
  simpa only [← sub_eq_add_neg,Matrix.traceNorm_neg,hr,hs,one_add_one_eq_two] using h

theorem trace_distance_le_bad_mass (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (rho sigma : X → Qatlib.Foundations.PureStateMath.DensityOperator d)
    (bad : Finset X) (hgood : ∀ x, x ∉ bad → rho x=sigma x) :
    Matrix.traceNorm (Qatlib.Concepts.MixedFidelity.FidelityMetric.BadLabelMixtureBound.average p rho-Qatlib.Concepts.MixedFidelity.FidelityMetric.BadLabelMixtureBound.average p sigma)/2 ≤ ∑ x ∈ bad,p.prob x := by
  have he : Qatlib.Concepts.MixedFidelity.FidelityMetric.BadLabelMixtureBound.average p rho-Qatlib.Concepts.MixedFidelity.FidelityMetric.BadLabelMixtureBound.average p sigma =
      ∑ x, (p.prob x : ℂ) • ((rho x).val-(sigma x).val) := by
    simp only [Qatlib.Concepts.MixedFidelity.FidelityMetric.BadLabelMixtureBound.average,smul_sub,Finset.sum_sub_distrib]
  rw [he]
  have h := Qatlib.Concepts.MixedFidelity.FidelityMetric.traceNorm_weighted_sum_le p.prob p.nonneg
    (fun x => (rho x).val-(sigma x).val)
  have hb : (∑ x, p.prob x*Matrix.traceNorm ((rho x).val-(sigma x).val)) ≤
      2*∑ x ∈ bad,p.prob x := by
    have hs : (∑ x ∈ bad,p.prob x) = ∑ x : X, if x ∈ bad then p.prob x else 0 := by simp
    rw [hs,Finset.mul_sum]
    simp only [mul_ite,mul_zero]
    apply Finset.sum_le_sum
    intro x _
    by_cases hx : x ∈ bad
    · rw [if_pos hx]
      have hd :=
          mul_le_mul_of_nonneg_left
          (Qatlib.Concepts.MixedFidelity.FidelityMetric.BadLabelMixtureBound.density_distance_le_two (rho x) (sigma x)) (p.nonneg x)
      linarith
    · simp [hx,hgood x hx]
  linarith

theorem measured_after_channel {Y : Type} [Fintype Y] [DecidableEq Y]
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (rho sigma : X → Qatlib.Foundations.PureStateMath.DensityOperator d) (bad : Finset X)
    (hgood : ∀ x, x ∉ bad → rho x=sigma x)
    (E : Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt.FinitePOVM Y k) (T : MatrixMap (Fin d) (Fin k) ℂ)
    (hT : T.IsPositive) (ht : T.IsTracePreserving) :
    let hr : Qatlib.Foundations.PureStateMath.IsDensityOperator (T (Qatlib.Concepts.MixedFidelity.FidelityMetric.BadLabelMixtureBound.average p rho)) :=
      ⟨hT (Qatlib.Concepts.MixedFidelity.FidelityMetric.BadLabelMixtureBound.average_density p rho).1,(ht _).trans (Qatlib.Concepts.MixedFidelity.FidelityMetric.BadLabelMixtureBound.average_density p rho).2⟩
    let hs : Qatlib.Foundations.PureStateMath.IsDensityOperator (T (Qatlib.Concepts.MixedFidelity.FidelityMetric.BadLabelMixtureBound.average p sigma)) :=
      ⟨hT (Qatlib.Concepts.MixedFidelity.FidelityMetric.BadLabelMixtureBound.average_density p sigma).1,(ht _).trans (Qatlib.Concepts.MixedFidelity.FidelityMetric.BadLabelMixtureBound.average_density p sigma).2⟩
    Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteOutputDistinguishability.advantage
      (Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt.povmRecordLaw E (T (Qatlib.Concepts.MixedFidelity.FidelityMetric.BadLabelMixtureBound.average p rho)) hr)
      (Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt.povmRecordLaw E (T (Qatlib.Concepts.MixedFidelity.FidelityMetric.BadLabelMixtureBound.average p sigma)) hs) ≤ ∑ x ∈ bad,p.prob x := by
  exact (Qatlib.Concepts.MixedFidelity.FidelityMetric.FinitePOVMTraceDistance.after_common_channel E T hT ht _ _
    (Qatlib.Concepts.MixedFidelity.FidelityMetric.BadLabelMixtureBound.average_density p rho) (Qatlib.Concepts.MixedFidelity.FidelityMetric.BadLabelMixtureBound.average_density p sigma)).trans
      (Qatlib.Concepts.MixedFidelity.FidelityMetric.BadLabelMixtureBound.trace_distance_le_bad_mass p rho sigma bad hgood)

end
end Qatlib.Concepts.MixedFidelity.FidelityMetric.BadLabelMixtureBound
