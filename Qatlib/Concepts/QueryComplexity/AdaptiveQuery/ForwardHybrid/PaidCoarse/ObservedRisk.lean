/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedMixedState
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedQueryBudget
import Qatlib.Concepts.HspRecovery.SieveLaw.SharpSelectiveStability
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardHybrid.PaidCoarse.ProjectiveRisk

/-!
# Trace norm stability of observed record statistics

This module defines `weightedBranchMap` for a finite quantum instrument and
`observedRecordExpectation` for a mixed state observed circuit. Nonnegative weights preserve
positivity, and weights at most one give an upper bound on the output trace.

For positive semidefinite inputs with equal trace and weights in `[0, 1]`, the change in the
weighted outcome statistic is bounded by half the trace norm of the input difference. The
observed circuit result uses the instrument interpretation of observation records and trace
distance estimates described in [Watrous2018].

## Main statements

* `weighted_instrument_input_error`: trace norm stability for bounded instrument statistics.
* `observedRecordExpectation_eq_instrument`: the instrument expression for a record expectation.
* `observed_record_input_error`: trace norm stability for bounded observation record statistics.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse

open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {d : ℕ}

/-- The complex linear map obtained by summing the branches of a finite instrument with real
weights. -/
noncomputable def weightedBranchMap {O : Type*} [Fintype O]
    (J : Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument O d d) (f : O → ℝ) : Qatlib.Foundations.PureStateMath.Operator d →ₗ[ℂ] Qatlib.Foundations.PureStateMath.Operator d :=
  ∑ o, (f o : ℂ) • J.branch o

/-- The real trace of a weighted branch map is the corresponding weighted sum of instrument
outcome probabilities. -/
theorem trace_weightedBranchMap {O : Type*} [Fintype O]
    (J : Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument O d d) (f : O → ℝ) (ρ : Qatlib.Foundations.PureStateMath.Operator d) :
    (trace (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.weightedBranchMap J f ρ)).re =
      ∑ o, Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb J ρ o * f o := by
  simp [Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.weightedBranchMap, LinearMap.sum_apply, trace_sum, trace_smul,
    Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb, Complex.mul_re, mul_comm]

/-- A weighted branch map with nonnegative weights sends positive semidefinite inputs to
positive semidefinite outputs. -/
theorem weightedBranchMap_positive {O : Type*} [Fintype O]
    (J : Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument O d d) (f : O → ℝ) (hf : ∀ o, 0 ≤ f o)
    (ρ : Qatlib.Foundations.PureStateMath.Operator d) (hρ : ρ.PosSemidef) :
    (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.weightedBranchMap J f ρ).PosSemidef := by
  simp only [Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.weightedBranchMap, LinearMap.sum_apply, LinearMap.smul_apply]
  exact Matrix.posSemidef_sum _ fun o _ =>
    ((J.cp o).positive hρ).smul (RCLike.ofReal_nonneg.mpr (hf o))

/-- If every weight is at most one, the real trace of the weighted branch map on a positive
semidefinite input is at most the input's real trace. -/
theorem weightedBranchMap_tni {O : Type*} [Fintype O]
    (J : Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument O d d) (f : O → ℝ) (hf : ∀ o, f o ≤ 1)
    (ρ : Qatlib.Foundations.PureStateMath.Operator d) (hρ : ρ.PosSemidef) :
    (trace (Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.weightedBranchMap J f ρ)).re ≤ (trace ρ).re := by
  rw [Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.trace_weightedBranchMap, ← Qatlib.Concepts.AdaptiveCP.BranchTrace.sum_instrumentProb J ρ]
  apply Finset.sum_le_sum
  intro o _
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (hf o) (Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb_nonneg J hρ o)

/-- For positive semidefinite inputs with equal real trace and weights in `[0, 1]`, weighted
instrument outcome sums differ by at most half the trace norm of the input difference. -/
theorem weighted_instrument_input_error {O : Type*} [Fintype O]
    (J : Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument O d d) (f : O → ℝ) (hf : ∀ o, 0 ≤ f o ∧ f o ≤ 1)
    (ρ τ : Qatlib.Foundations.PureStateMath.Operator d) (hρ : ρ.PosSemidef) (hτ : τ.PosSemidef)
    (heq : (trace ρ).re = (trace τ).re) :
    |(∑ o, Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb J ρ o * f o) -
        (∑ o, Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb J τ o * f o)| ≤ traceNorm (ρ - τ) / 2 := by
  let T :=
      Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.weightedBranchMap J f
  have hb := Qatlib.Concepts.HspRecovery.SieveLaw.positive_tni_trace_zero_budget T
    (fun A hA => Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.weightedBranchMap_positive J f (fun o => (hf o).1) A hA)
    (fun A hA => Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.weightedBranchMap_tni J f (fun o => (hf o).2) A hA)
    (ρ - τ) (hρ.isHermitian.sub hτ.isHermitian)
    (by rw [trace_sub, Complex.sub_re, heq, sub_self])
  have hm : |(trace (T (ρ - τ))).re| ≤ traceNorm (T (ρ - τ)) :=
    (Complex.abs_re_le_norm _).trans (Matrix.abs_trace_le_traceNorm _)
  have hh : |(trace (T (ρ - τ))).re| ≤ traceNorm (ρ - τ) / 2 := by
    linarith
  rw [map_sub, trace_sub, Complex.sub_re] at hh
  simpa only [T,
      Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.trace_weightedBranchMap] using hh

/-- The expectation of a real observation record statistic, formed by summing the statistic
against the mixed trace masses. -/
noncomputable def observedRecordExpectation (O : Qatlib.Foundations.PureStateMath.Operator d)
    (P : Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedCircuit (Fin d)) (ρ : Qatlib.Foundations.PureStateMath.Operator d)
    (f : List (ℕ × ℕ) → ℝ) : ℝ :=
  ((Qatlib.Concepts.AdversaryBounds.AdvDuality.observedMixedTraces O P ρ).map fun t => Qatlib.Concepts.AdversaryBounds.AdvDuality.mixedMass t * f t.outcomes).sum

/-- For a unitary oracle and a well formed observed circuit, the record expectation equals the
weighted outcome sum of its associated instrument. -/
theorem observedRecordExpectation_eq_instrument (O : Qatlib.Foundations.PureStateMath.Operator d)
    (hO : O ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (P : Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedCircuit (Fin d)) (hP : Qatlib.Concepts.AdversaryBounds.AdvDuality.observedWellFormed P)
    (ρ : Qatlib.Foundations.PureStateMath.Operator d) (f : List (ℕ × ℕ) → ℝ) :
    Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation O P ρ f =
      ∑ i, Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb (Qatlib.Concepts.ShadowModels.ShadowChannel.observedInstrument O hO P hP) ρ i *
        f (Qatlib.Concepts.ShadowModels.ShadowChannel.observedLeaf O P i).outcomes := by
  exact (Qatlib.Concepts.AdversaryBounds.AdvDuality.observedMixedTraces_event_statistic O hO P hP ρ
    (fun t => f t.outcomes)).1.symm

/-- For positive semidefinite inputs with equal real trace, a record statistic in `[0, 1]`
changes by at most half the trace norm of the input difference under a fixed well formed
observed circuit with unitary oracle. -/
theorem observed_record_input_error (O : Qatlib.Foundations.PureStateMath.Operator d)
    (hO : O ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (P : Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedCircuit (Fin d)) (hP : Qatlib.Concepts.AdversaryBounds.AdvDuality.observedWellFormed P)
    (ρ τ : Qatlib.Foundations.PureStateMath.Operator d) (hρ : ρ.PosSemidef) (hτ : τ.PosSemidef)
    (heq : (trace ρ).re = (trace τ).re)
    (f : List (ℕ × ℕ) → ℝ) (hf : ∀ h, 0 ≤ f h ∧ f h ≤ 1) :
    |observedRecordExpectation O P ρ f - Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation O P τ f|
      ≤ traceNorm (ρ - τ) / 2 := by
  rw [Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation_eq_instrument O hO P hP,
    Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.observedRecordExpectation_eq_instrument O hO P hP]
  exact Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse.weighted_instrument_input_error (Qatlib.Concepts.ShadowModels.ShadowChannel.observedInstrument O hO P hP)
    (fun i => f (Qatlib.Concepts.ShadowModels.ShadowChannel.observedLeaf O P i).outcomes) (fun i => hf _) ρ τ hρ hτ heq

end Qatlib.Concepts.QueryComplexity.AdaptiveQuery.ForwardAdaptiveHybrid.PaidCoarse
