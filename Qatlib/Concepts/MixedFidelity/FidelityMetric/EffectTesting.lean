/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedFidelity.FidelityMetric.ChannelHelpers.FinitePOVMTraceDistance
import Qatlib.Concepts.MixedFidelity.FidelityMetric.MixedFidelity
import Mathlib.Tactic

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Effect Testing

An arbitrary positive binary effect and its positive complement form an actual canonical finite POVM by their internally constructed square-root factors.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix ComplexOrder MatrixOrder

namespace Qatlib.Concepts.MixedFidelity.FidelityMetric.EffectTesting
open Qatlib.Concepts.MbqcFlow.FlowDecision
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt
open Qatlib.Concepts.MixedFidelity.FidelityMetric
open Qatlib.Concepts.MixedFidelity.FidelityMetric.FinitePOVMTraceDistance
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

/-- An arbitrary positive binary effect and its positive complement form an actual canonical finite POVM by their internally constructed square-root factors. -/
def binaryOfEffect {D : ℕ} (E : Operator D) (hE : E.PosSemidef) (hEc : (1-E).PosSemidef) : FinitePOVM Bool D where
  effect o := if o then E else 1-E
  effect_sum := by simp only [Fintype.sum_bool,ite_true,Bool.false_eq_true,ite_false]; abel
  weight _ := 1
  weight_nonneg _ := by norm_num
  factor o := CFC.sqrt (if o then E else 1-E)
  effect_eq_factor o := by
    have hp : (if o then E else 1-E).PosSemidef := by cases o <;> assumption
    simp only [Complex.ofReal_one,one_smul]
    rw [(Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (if o then E else 1-E))).1]
    exact (CFC.sqrt_mul_sqrt_self _ hp.nonneg).symm

/-- Every structural binary effect on the whole input obeys the genuine quantum trace-distance testing bound. -/
theorem effect_difference_le {D : ℕ} (E A B : Operator D) (hE : E.PosSemidef) (hEc : (1-E).PosSemidef)
    (hA : IsDensityOperator A) (hB : IsDensityOperator B) :
    |(Matrix.trace (E*A)).re-(Matrix.trace (E*B)).re|≤traceDistance A B := by
  let P := binaryOfEffect E hE hEc
  let p := povmRecordLaw P A hA
  let q := povmRecordLaw P B hB
  have ht := FiniteDistributionVariation.event_distance p q ({true} : Finset Bool)
  have htv := measured_tv_le P A B hA hB
  change _ ≤ Matrix.traceNorm (A-B)/2
  have hh : |(Matrix.trace (E*A)).re-(Matrix.trace (E*B)).re|≤FiniteInformationDivergence.tv p q := by
    simpa only [Finset.sum_singleton,p,q,povmRecordLaw,P,binaryOfEffect,ite_true] using ht
  exact hh.trans htv

/-- A complete input's actual two-hypothesis error sum is at least half its squared root fidelity for every positive event effect; no output-risk certificate is assumed. -/
theorem binary_error_lower {D : ℕ} (E A B : Operator D) (hE : E.PosSemidef) (hEc : (1-E).PosSemidef)
    (hA : IsDensityOperator A) (hB : IsDensityOperator B) :
    (Froot A B)^2/2≤(Matrix.trace (E*A)).re+(Matrix.trace ((1-E)*B)).re := by
  have hd := effect_difference_le E A B hE hEc hA hB
  have hf := (g1 D A B hA hB).2.1
  have hg := (g3 D A B hA hB).1.2
  have hs : 0≤1-(Froot A B)^2 := by nlinarith [hf.1,hf.2.1]
  have hsq := Real.sq_sqrt hs
  have hroot := Real.sqrt_nonneg (1-(Froot A B)^2)
  have he : (Matrix.trace ((1-E)*B)).re=1-(Matrix.trace (E*B)).re := by
    rw [Matrix.sub_mul,Matrix.one_mul,Matrix.trace_sub,hB.2]
    simp only [Complex.sub_re,Complex.one_re]
  rw [he]
  have hb := (abs_le.mp hd).1
  nlinarith [sq_nonneg (1-Real.sqrt (1-(Froot A B)^2))]

end Qatlib.Concepts.MixedFidelity.FidelityMetric.EffectTesting
