/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.ErrorStream.AmplifiedPeriodDefs
import Qatlib.Concepts.AmplitudeCore.InvFreeSampling.AmplifiedNoiseExecution

/-!
# Completion results for amplified period recovery

This module proves the completion statements defined in `AmplifiedPeriodDefs`. The results
combine verified fixed-noise candidates, cyclic verification, Haar preparation and fair
sampling, fresh Bernoulli observations, and zero-mode transport.

`aq_completion_fresh_access_cost` records the fresh-pass ledger, and
`aq_completion_fresh_record` identifies the fields of the corresponding observation record.

The error-stream setting is developed in [Cornwell2014].

## Main statements

* `aq_completion_fixed_noise_endpoint`: candidate verification, cost, and ambiguity results.
* `aq_completion_fresh_access_endpoint`: fresh-observation consistency and recovery.
* `aq_completion_zero_mode_endpoint`: the zero-mode transport package.

## References

* [Cornwell, 2014][Cornwell2014]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QftPreparation.LocalQft
open Qatlib.Concepts.AmpTransform.ErrorStream
open Qatlib.Concepts.AmpTransform.FullLayerCF
open Qatlib.Concepts.AmpTransform.HaarPairTest
open Qatlib.Concepts.AmplitudeCore.InvFreeSampling

set_option autoImplicit false

namespace Qatlib.Concepts.AmpTransform.ErrorStream

open Qatlib
open scoped Classical BigOperators ENNReal

/-- Establish the fixed-noise completion package: verified candidate records, their query bound,
the denoising result, and the explicit two-period ambiguity example. -/
theorem aq_completion_fixed_noise_endpoint : aqCompletionFixedNoiseEndpoint := by
  refine ⟨?_, ?_, fullLayerCFDenoiseUniqueP_answer, ?_⟩
  · intro N h s M B xs p hp
    exact aqCandidateRecord_verified h s M B xs p hp
  · intro N h s M B k xs
    exact aqCandidateRecordQueries_cap h s M B k xs
  · obtain ⟨hG2, hG4, hd2, hd4, heq, hguard, hv2, hv4⟩ :=
      same_oracle_two_planted_periods
    refine ⟨?_, ?_, ?_⟩
    · simpa using! heq
    · simpa using! hv2
    · simpa using! hv4

/-- Establish successful three-query cyclic verification for the planted period and the
universal three-query cost bound. -/
theorem aq_completion_wrap_endpoint : aqCompletionWrapEndpoint := by
  refine ⟨?_, ?_⟩
  · intro N hN h s M P hM hP hMP G hmark
    exact aqCyclicVerify_true N hN h s M P hM hP hMP G hmark
  · intro N hN h s M q
    exact aqCyclicVerify_cost N hN h s M q

/-- Combine the general Haar result, the fair-label sampler distribution, and the local QFT
gate-count identity. -/
theorem aq_completion_haar_endpoint : aqCompletionHaarEndpoint := by
  refine ⟨haarGeneralWN_answer, ?_, ?_⟩
  · intro C fuel hC
    exact (aqFairLabelSampler_distribution_and_bits C fuel hC).1
  · intro n
    exact (aqLocalQFT_actual_matrix_and_cost n).2.1

/-- Establish Bernoulli site marginals, candidate consistency probabilities, and recovery when
every false candidate is refuted. -/
theorem aq_completion_fresh_access_endpoint : aqCompletionFreshAccessEndpoint := by
  refine ⟨?_, ?_, ?_⟩
  · intro N p hp hp1 i
    exact aq_bernoulli_site_marginal N p hp hp1 i
  · intro N s M P P' p hp hp1
    exact aq_fresh_consistency_probability N s M P P' p hp hp1
  · intro N s M P p cands hP σ hrefute
    exact (aq_fresh_disambiguation_succeeds N s M P p cands hP σ hrefute).2

/-- Establish the Bernoulli zero-mode transport completion statement. -/
theorem aq_completion_zero_mode_endpoint : aqCompletionZeroModeEndpoint :=
  bernoulliErrorStreamZeroModeTransport

/-- The fresh-pass record has `N * t` oracle accesses and classical work `N * k + t`. -/
theorem aq_completion_fresh_access_cost (N t k : ℕ) :
    (aqFreshPassCost N t k).oracleAccesses = N * t ∧
      (aqFreshPassCost N t k).classicalWork = N * k + t := by
  exact ⟨rfl, rfl⟩

/-- Constructing a fresh completion record preserves the supplied candidates and observation in
their respective fields. -/
theorem aq_completion_fresh_record (N : ℕ) (cands : Finset ℕ) (obs : Finset (Fin N)) :
    ({ candidates := cands, observation := obs } : aqFreshCompletionRecord N).candidates = cands ∧
      ({ candidates := cands, observation := obs } : aqFreshCompletionRecord N).observation = obs := by
  exact ⟨rfl, rfl⟩

end Qatlib.Concepts.AmpTransform.ErrorStream
