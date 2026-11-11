/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.ErrorStream.AmplifiedNoiseRefinedDefs

/-!
# Noise and resource bounds for amplified Fourier recovery

This module verifies noise envelope and candidate recovery results for amplified Fourier
transforms, with background in [Cornwell2014]. It treats the single marked item envelope
separately, bounds the actual independent noise average, and records the failure of the original
envelope bridge. Fixed noise ambiguity examples accompany fresh noise consistency and failure
bounds.

The module also connects finite fair bit tapes to Bernoulli streams, including exact dyadic
probabilities and convergence, and records verification, density counting, Haar preparation, and
local QFT resource formulas.

## Main statements

* `clause23_endpoint_holds`: envelope bounds, single item behavior, and bridge refutation.
* `aqNext_fixed_record_two_planted`: distinct planted periods can share a verified fixed record.
* `aqNext_effective_stream_tendsto`: finite tape stream probabilities converge to Bernoulli
  probabilities.
* `aqNextPublicDensityCounting_actual`: exact cardinality readout probability and circuit
  counts.

## References

* [Cornwell, 2014][Cornwell2014]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.HspRecovery.CfOrder
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.QftPreparation.LocalQft
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.AmpTransform.ErrorStream
open Qatlib.Concepts.AmpTransform.HaarPairTest
open Qatlib.Concepts.AmpTransform.LegendreWindow
open Qatlib.Concepts.AmpTransform.NoiseEnvelope
open Qatlib.Concepts.AmpTransform.SuccessRatio
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QftPreparation.LocalQFTImplementation
open Qatlib.Concepts.AmpTransform.ErrorStream
open Qatlib.Concepts.AmplitudeCore.InvFreeSampling

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Concepts.FourierRecovery.ModularFourier

open Qatlib
open Matrix
open scoped Classical BigOperators ENNReal

/-- For `L ≠ -1`, the envelope at `M = 1` equals the single marked item slice. -/
theorem aqNext_m1_envelope_identity (N : ℕ) (L : ℝ) (hL : L ≠ -1) :
    aqEnvelope (N : ℝ) 1 L = aqM1Slice (N : ℝ) L := by
  have hne : L + 1 ≠ 0 := by
    intro hc
    apply hL
    linarith
  unfold aqEnvelope aqM1Slice
  simp only [one_pow]
  by_cases hz : (N : ℝ) - L - 1 = 0
  · simp [hz]
  · have hne2 : ((N : ℝ) - L - 1) * (L + 1) ≠ 0 := mul_ne_zero hz hne
    apply (div_eq_div_iff hne2 hz).mpr
    ring

/-- On the open single item window, the full envelope equals `aqM1Slice`. -/
theorem aqNext_envelope_m1_on_open_window {N : ℕ} (hN : 0 < N) {L : ℝ}
    (h : aqM1Window N L) :
    aqEnvelope (N : ℝ) 1 L = aqM1Slice (N : ℝ) L := by
  have hL : L ≠ -1 := by
    intro hc
    exact (lt_irrefl (-1 : ℝ)) (hc ▸ h.1)
  exact aqNext_m1_envelope_identity N L hL

/-- For positive `N`, the single item envelope slice is strictly increasing on its open window. -/
theorem aqNext_m1_envelope_strictly_increasing {N : ℕ} (hN : 0 < N) {L₁ L₂ : ℝ}
    (h₁ : aqM1Window N L₁) (h₂ : aqM1Window N L₂) (hlt : L₁ < L₂) :
    aqM1Slice (N : ℝ) L₁ < aqM1Slice (N : ℝ) L₂ := by
  have hN' : (1 : ℝ) ≤ (N : ℝ) := by
    have : (1 : ℕ) ≤ N := by omega
    exact_mod_cast this
  have hpos₂ : 0 < (N : ℝ) - L₂ - 1 := by linarith [h₂.2]
  have hlt' : (N : ℝ) - L₂ - 1 < (N : ℝ) - L₁ - 1 := by linarith
  unfold aqM1Slice
  exact one_div_lt_one_div_of_lt hpos₂ hlt'

/-- On the open single item window, the envelope slice is strictly greater than `1 / N`. -/
theorem aqNext_m1_envelope_gt_inv_N {N : ℕ} (hN : 0 < N) {L : ℝ}
    (h : aqM1Window N L) :
    (1 : ℝ) / N < aqM1Slice (N : ℝ) L := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have : (1 : ℕ) ≤ N := by omega
    exact_mod_cast this
  have hpos : 0 < (N : ℝ) - L - 1 := by linarith [h.2]
  have hlt : (N : ℝ) - L - 1 < N := by linarith [h.1]
  unfold aqM1Slice
  exact one_div_lt_one_div_of_lt hpos hlt

/-- Every point in the open single item window has another point with strictly smaller envelope
value. -/
theorem aqNext_m1_envelope_no_optimal {N : ℕ} (hN : 0 < N) {L : ℝ}
    (h : aqM1Window N L) :
    ∃ L', aqM1Window N L' ∧ aqM1Slice (N : ℝ) L' < aqM1Slice (N : ℝ) L := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have : (1 : ℕ) ≤ N := by omega
    exact_mod_cast this
  have hhalf : (0 : ℝ) < (L + 1) / 2 := by linarith [h.1]
  have hlt : L - (L + 1) / 2 < L := by linarith
  refine ⟨L - (L + 1) / 2, ⟨?_, ?_⟩, ?_⟩
  · linarith
  · linarith [h.2]
  · exact aqNext_m1_envelope_strictly_increasing hN
      (L₁ := L - (L + 1) / 2) (L₂ := L)
      ⟨by linarith, by linarith [h.2]⟩ h hlt

/-- For `N > 1` and `0 ≤ L < N - 1`, the single item slice is at least `1 / (N - 1)`, with
equality exactly at `L = 0`. -/
theorem aqNext_m1_envelope_physical_minimum {N : ℕ} (hN : 1 < N) {L : ℝ}
    (hL : 0 ≤ L) (hL' : L < (N : ℝ) - 1) :
    (1 : ℝ) / ((N : ℝ) - 1) ≤ aqM1Slice (N : ℝ) L ∧
      (aqM1Slice (N : ℝ) L = (1 : ℝ) / ((N : ℝ) - 1) ↔ L = 0) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have : (1 : ℕ) ≤ N := by omega
    exact_mod_cast this
  have hpos : 0 < (N : ℝ) - L - 1 := by linarith
  have hle : (N : ℝ) - L - 1 ≤ (N : ℝ) - 1 := by linarith
  have hpos0 : 0 < (N : ℝ) - 1 := by linarith
  constructor
  · unfold aqM1Slice
    exact one_div_le_one_div_of_le hpos hle
  · constructor
    · intro heq
      unfold aqM1Slice at heq
      have hz := (div_eq_div_iff (by linarith : ((N : ℝ) - L - 1) ≠ 0)
        (by linarith : ((N : ℝ) - 1) ≠ 0)).mp heq
      linarith
    · intro hL0
      subst hL0
      unfold aqM1Slice
      rw [show (N : ℝ) - 0 - 1 = N - 1 by ring]

/-- The proposition `ExpectedNoiseEnvelopeBridgeOriginal` is false. -/
theorem aqNext_envelope_bridge_refuted :
    ¬ Qatlib.Concepts.AmpTransform.NoiseEnvelope.ExpectedNoiseEnvelopeBridgeOriginal :=
  Qatlib.Concepts.AmpTransform.NoiseEnvelope.expectedNoiseEnvelopeBridge_false

/-- The normalized independent uniform noise average, weighted by the tangent and gain factors,
is bounded by `aqEnvelope` under the stated size and norm hypotheses. -/
theorem aqNext_actual_iid_average_bounded (N M L : ℕ) [NeZero N] (y : ZMod N) (c : ℂ)
    (hy : y ≠ 0) (hM : 1 ≤ M) (hsize : M + L < N) (hc : ‖c‖ ≤ (M : ℝ)) :
    (((N : ℝ) ^ L)⁻¹ * (∑ ω : Fin L → ZMod N,
      ‖c + ∑ i, ZMod.stdAddChar (ω i * y)‖ ^ 2)) /
        ((M : ℝ) + L) ^ 2 * (Real.tan (aqAngle N (M + L))) ^ 2 * aqGain N (M + L) ≤
      aqEnvelope (N : ℝ) (M : ℝ) (L : ℝ) := by
  have h := Qatlib.Concepts.AmpTransform.NoiseEnvelope.expectedNoiseEnvelope_actual_tan_average
    N M L y c hy hM hsize hc
  simpa [aqEnvelope] using! h

/-- Establishes `clause23_endpoint`, combining envelope minimization, the independent noise
average bound, single item behavior, and refutation of the original bridge. -/
theorem clause23_endpoint_holds : clause23_endpoint := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro M N hM hN L hL1 hL2
    have h := errorExpectationMinimizedAtMinL M N hM hN
    simpa [aqEnvelope, aqMinL] using! h L hL1 hL2
  · intro N M L _inst y c hy hM hsize hc
    exact aqNext_actual_iid_average_bounded N M L y c hy hM hsize hc
  · intro N hN L hL hL'
    exact aqNext_m1_envelope_physical_minimum hN hL hL'
  · intro N hN L h
    exact aqNext_envelope_m1_on_open_window hN h
  · intro N hN L₁ L₂ h₁ h₂ hlt
    exact aqNext_m1_envelope_strictly_increasing hN h₁ h₂ hlt
  · intro N hN L h
    exact aqNext_m1_envelope_gt_inv_N hN h
  · intro N hN L h
    exact aqNext_m1_envelope_no_optimal hN h
  · exact aqNext_envelope_bridge_refuted

/-- At the single item endpoint with an empty noise set, the squared Fourier phase norm is one;
this is a special case of the Lemma 20 expression in [Cornwell2014]. -/
theorem aq_lemma20_T1_endpoint {n N s P y : ℕ} (hN : N = 2 ^ n) (hy : y < N) (hy0 : y ≠ 0) :
    ‖(1 : ℂ) / (1 : ℂ) * amplifiedQFTOmega N ^ (s * y) +
      (1 : ℂ) / (1 : ℂ) * (∑ z ∈ (∅ : Finset ℕ), amplifiedQFTOmega N ^ (z * y))‖ ^ 2 = 1 := by
  have hsum : (∑ z ∈ (∅ : Finset ℕ), amplifiedQFTOmega N ^ (z * y)) = 0 := by simp
  have hnorm : ‖amplifiedQFTOmega N ^ (s * y)‖ = 1 :=
    zoo_amplified_qft_lemma20_omega_norm N (s * y)
  simp only [hsum, add_zero, div_one, norm_one, one_mul, hnorm, one_pow]

/-- The squared normalized Fourier phase expression is at most one under the stated progression,
disjointness, cyclicity, and dense regime hypotheses. -/
theorem aq_lemma20_dense_regime {n N M L T s P y : ℕ} (A G : Finset ℕ)
    (hN : N = 2 ^ n) (hA : A = (Finset.range M).image (fun r => s + r * P))
    (hA_sub : A ⊆ Finset.range N) (hG_sub : G ⊆ Finset.range N) (hA_card : A.card = M)
    (hG_card : G.card = L) (hdisj : Disjoint A G) (hT : T = M + L) (hTpos : 0 < T)
    (hy : y < N) (hy0 : y ≠ 0) (hcyc : (P * y) % N = 0) (hdense : 2 * N < 2 * T) :
    ‖(M : ℂ) / (T : ℂ) * amplifiedQFTOmega N ^ (s * y) +
      (1 : ℂ) / (T : ℂ) * (∑ z ∈ G, amplifiedQFTOmega N ^ (z * y))‖ ^ 2 ≤ (1 : ℝ) :=
  zoo_amplified_qft_lemma20 n N M L T s P y A G hN hA hA_sub hG_sub hA_card hG_card hdisj
    hT hTpos hy hy0 hcyc

/-- When the comparison likelihood is nonzero, the success ratio is the quotient of the two
candidate likelihoods. -/
theorem aq_successRatio_eq_div {N s M P P' : ℕ} (p : ℝ) (obs : Finset (Fin N))
    (hne : aqCandidateLikelihood N s M P' p obs ≠ 0) :
    aqSuccessRatio N s M P P' p obs =
      aqCandidateLikelihood N s M P p obs / aqCandidateLikelihood N s M P' p obs := by
  simp [aqSuccessRatio, hne]

/-- The success ratio is zero when the comparison candidate has zero likelihood. -/
theorem aq_successRatio_of_refuted {N s M P P' : ℕ} (p : ℝ) (obs : Finset (Fin N))
    (hz : aqCandidateLikelihood N s M P' p obs = 0) :
    aqSuccessRatio N s M P P' p obs = 0 := by
  simp [aqSuccessRatio, hz]

/-- For a noise parameter in `[0, 1]`, the success ratio is nonnegative. -/
theorem aq_successRatio_nonneg {N s M P P' : ℕ} (p : ℝ) (obs : Finset (Fin N))
    (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ aqSuccessRatio N s M P P' p obs := by
  by_cases hne : aqCandidateLikelihood N s M P' p obs = 0
  · simp [aqSuccessRatio, hne]
  · rw [aq_successRatio_eq_div p obs hne]
    have hP : 0 ≤ aqCandidateLikelihood N s M P p obs := by
      by_cases hc : aqCandidateConsistent N s M P obs
      · simp [aqCandidateLikelihood, hc]
        positivity
      · simp [aqCandidateLikelihood, hc]
    have hP' : 0 < aqCandidateLikelihood N s M P' p obs := by
      have h0 : 0 ≤ aqCandidateLikelihood N s M P' p obs := by
        by_cases hc : aqCandidateConsistent N s M P' obs
        · simp [aqCandidateLikelihood, hc]
          positivity
        · simp [aqCandidateLikelihood, hc]
      exact lt_of_le_of_ne h0 (Ne.symm hne)
    have hdiv : 0 ≤ aqCandidateLikelihood N s M P p obs / aqCandidateLikelihood N s M P' p obs :=
      div_nonneg hP (le_of_lt hP')
    simpa [aqSuccessRatio, hne] using! hdiv

/-- The amplification angle increases with the marked count when `0 < M ≤ L` and `2 * L ≤ N`. -/
theorem aqAngle_mono {N M L : ℕ} (hN : 0 < N) (hM : 0 < M) (hML : M ≤ L) (hLN : 2 * L ≤ N) :
    aqAngle N M ≤ aqAngle N L := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hdiv : (M : ℝ) / (N : ℝ) ≤ (L : ℝ) / (N : ℝ) := by
    gcongr
  have hsq : Real.sqrt ((M : ℝ) / (N : ℝ)) ≤ Real.sqrt ((L : ℝ) / (N : ℝ)) :=
    Real.sqrt_le_sqrt hdiv
  have hL : (L : ℝ) / (N : ℝ) ≤ 1 / 2 := by
    apply (div_le_iff₀ hNR).mpr
    have h : 2 * (L : ℝ) ≤ (N : ℝ) := by exact_mod_cast hLN
    linarith
  exact Real.arcsin_le_arcsin hsq

/-- The amplification round count decreases with the marked count when `0 < M ≤ L` and `2 * L ≤
N`. -/
theorem aqRounds_anti {N M L : ℕ} (hN : 0 < N) (hM : 0 < M) (hML : M ≤ L) (hLN : 2 * L ≤ N) :
    aqRounds N M ≥ aqRounds N L := by
  have hθ := aqAngle_mono hN hM hML hLN
  have hθM : 0 < aqAngle N M := by
    rw [aqAngle]
    exact Real.arcsin_pos.mpr (Real.sqrt_pos_of_pos (by
      have : (0 : ℝ) < M := by exact_mod_cast hM
      positivity))
  have h1 : Real.pi / (4 * aqAngle N M) ≥ Real.pi / (4 * aqAngle N L) := by
    gcongr
  exact Nat.floor_mono h1

/-- Under the stated sparse regime hypotheses, the layer round count is at most the public
count, and adding the round saving recovers the public count. -/
theorem aq_layer_round_le_public {N M L : ℕ} (hN : 0 < N) (hM : 0 < M) (hML : M ≤ L)
    (hLN : 2 * L ≤ N) :
    aqLayerRoundCount N M L ≤ aqPublicRoundCount N M ∧
      aqRoundSaving N M L + aqLayerRoundCount N M L = aqPublicRoundCount N M := by
  have hanti := aqRounds_anti hN hM hML hLN
  constructor
  · exact hanti
  · unfold aqRoundSaving aqPublicRoundCount aqLayerRoundCount
    omega

/-- The cyclic verification procedure records cost at most three. -/
theorem aqNextCyclicVerify_cost (N : ℕ) (hN : 0 < N) (h : Fin N → Bool) (s M q : ℕ) :
    (aqNextCyclicVerify N hN h s M q).2 ≤ 3 := by
  unfold aqNextCyclicVerify
  split <;> simp

/-- With at least two planted progression points, positive period, and `M * P ≤ N`, the
specified marked oracle passes cyclic verification with cost three. -/
theorem aqNextCyclicVerify_true (N : ℕ) (hN : 0 < N) (h : Fin N → Bool) (s M P : ℕ)
    (hM : 2 ≤ M) (hP : 0 < P) (hMP : M * P ≤ N) (G : Finset (Fin N))
    (hmark : ∀ x, h x = decide (x ∈ ((Finset.range M).image (fun r : ℕ =>
      (⟨(s + r * P) % N, Nat.mod_lt _ hN⟩ : Fin N))) ∪ G)) :
    aqNextCyclicVerify N hN h s M P = (true, 3) := by
  have hm (r : ℕ) (hr : r < M) : h ⟨(s + r * P) % N, Nat.mod_lt _ hN⟩ = true := by
    rw [hmark]
    apply decide_eq_true
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨r, Finset.mem_range.mpr hr, rfl⟩)
  have hz := hm 0 (by omega)
  have h1 := hm 1 (by omega)
  have hlast := hm (M - 1) (by omega)
  simp only [zero_mul, add_zero] at hz
  simp only [one_mul] at h1
  simp [aqNextCyclicVerify, hP, hM, hMP, hz, h1, hlast]

/-- The public density readout returns the exact marked set cardinality with probability at
least `8 / π^2`; its circuit has `32 * N - 1` queries and `5 * (32 * N - 1) + 3` gates. -/
theorem aqNextPublicDensityCounting_actual (N : ℕ) (hN : 0 < N) (C : Finset (Fin N)) :
    8 / Real.pi ^ 2 ≤
      ∑ z ∈ Finset.univ.filter (fun z : Fin (32 * N) => aqNextPublicDensityReadout N z = C.card),
        (aeLaw (32 * N) (QFTMatrix N) ⟨0, hN⟩ C (qftMatrix_unitary hN)
          (by omega)).prob z ∧
    QueryCount (countedAECircuit (32 * N) (QFTMatrix N) (⟨0, hN⟩ : Fin N)) = 32 * N - 1 ∧
    GateCount (countedAECircuit (32 * N) (QFTMatrix N) (⟨0, hN⟩ : Fin N)) =
      5 * (32 * N - 1) + 3 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have ht : (C.card : ℝ) ≤ N := by
    have hh := Finset.card_le_card (Finset.subset_univ C)
    simpa using! hh
  have hs : Real.sqrt ((C.card : ℝ) * ((N : ℝ) - C.card)) ≤ N := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨hn.le, by nlinarith [sq_nonneg ((C.card : ℝ) - N / 2)]⟩
  have he : 2 * Real.pi * Real.sqrt ((C.card : ℝ) * ((N : ℝ) - C.card)) /
      (32 * (N : ℝ)) + Real.pi ^ 2 * N / (32 * (N : ℝ)) ^ 2 < 1 / 2 := by
    have h1 : 2 * Real.pi * Real.sqrt ((C.card : ℝ) * ((N : ℝ) - C.card)) /
        (32 * (N : ℝ)) ≤ 1 / 4 := by
      apply (div_le_iff₀ (by positivity)).mpr
      have hh := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2 * Real.pi by positivity)
      nlinarith [mul_nonneg hn.le (sub_nonneg.mpr Real.pi_lt_four.le)]
    have hp : Real.pi ^ 2 ≤ 16 * (N : ℝ) := by
      nlinarith [Real.pi_pos, Real.pi_lt_four]
    have h2 : Real.pi ^ 2 * N / (32 * (N : ℝ)) ^ 2 ≤ 1 / 64 := by
      apply (div_le_iff₀ (by positivity)).mpr
      have hh := mul_le_mul_of_nonneg_right hp hn.le
      nlinarith
    linarith
  have hmass := amplitude_counting_actual_consumer N (32 * N) hN (by omega) C
  have hc := prepared_ae_access_ledger (32 * N) (by omega) (QFTMatrix N) (⟨0, hN⟩ : Fin N)
  refine ⟨hmass.trans ?_, hc.1, hc.2.1⟩
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    have hw : |(N : ℝ) * aeEstimate (32 * N) z - (C.card : ℝ)| < 1 / 2 := by
      apply hz.trans_lt
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using! he
    have hw' := abs_lt.mp hw
    unfold aqNextPublicDensityReadout
    apply (Nat.floor_eq_iff (show 0 ≤ (N : ℝ) * aeEstimate (32 * N) z + 1 / 2 by
      have hh := Nat.cast_nonneg (α := ℝ) C.card
      linarith)).mpr
    constructor <;> linarith
  · intro z _ _
    exact (aeLaw (32 * N) (QFTMatrix N) ⟨0, hN⟩ C (qftMatrix_unitary hN) (by omega)).nonneg z

/-- Combines successful cyclic verification at cost three with the exact query and gate counts
of the public density counting circuit. -/
theorem aq_unknown_M_recovery_cost {N : ℕ} (hN : 0 < N) (h : Fin N → Bool) (s M P : ℕ)
    (hM : 2 ≤ M) (hP : 0 < P) (hMP : M * P ≤ N) (G : Finset (Fin N))
    (hmark : ∀ x, h x = decide (x ∈ ((Finset.range M).image (fun r : ℕ =>
      (⟨(s + r * P) % N, Nat.mod_lt _ hN⟩ : Fin N))) ∪ G)) :
    aqNextCyclicVerify N hN h s M P = (true, 3) ∧
      (aqNextCyclicVerify N hN h s M P).2 ≤ 3 ∧
      QueryCount (countedAECircuit (32 * N) (QFTMatrix N) (⟨0, hN⟩ : Fin N)) = 32 * N - 1 ∧
      GateCount (countedAECircuit (32 * N) (QFTMatrix N) (⟨0, hN⟩ : Fin N))
        = 5 * (32 * N - 1) + 3 := by
  obtain ⟨hcount, hq, hg⟩ := aqNextPublicDensityCounting_actual N hN
    (Finset.univ.filter (fun x : Fin N => decide (x ∈ G)))
  exact ⟨aqNextCyclicVerify_true N hN h s M P hM hP hMP G hmark,
    aqNextCyclicVerify_cost N hN h s M P, hq, hg⟩

/-- For positive `n`, the dyadic Haar preparation is unitary and maps its seed basis state to
the uniform state. -/
theorem aq_haar_dyadic_preparation (n : ℕ) (hn : 0 < n) :
    haarDyadicPreparation n ∈ Matrix.unitaryGroup (Reg (n - 1) × Bool) ℂ ∧
      haarDyadicPreparation n *ᵥ Ket (haarDyadicSeed n) = Uniform (Reg (n - 1) × Bool) :=
  haarDyadicPreparation_spec n

/-- The prepared Haar pair word uses `j` data queries, one input query, and `j + 2` fixed gates. -/
theorem aq_haar_pair_ledger (n : ℕ) (hn : 0 < n) (j : ℕ) :
    preparedDataQueries (aqHaarPairWord (haarDyadicPreparation n) (haarDyadicSeed n) j) = j ∧
      preparedInputQueries (aqHaarPairWord (haarDyadicPreparation n) (haarDyadicSeed n) j) = 1 ∧
      preparedFixedGates (aqHaarPairWord (haarDyadicPreparation n) (haarDyadicSeed n) j) = j + 2 := by
  obtain ⟨hspec, hprep⟩ := haarDyadicPreparation_spec n
  have hw := haarPairWordSemantics (Reg (n - 1)) (haarDyadicPreparation n)
    (haarDyadicSeed n) hspec hprep j
  exact ⟨hw.2.1, hw.2.2.1, hw.2.2.2.1⟩

/-- The amplification schedule is the floor of `π / (4 * aqAngle N M)`, and its squared sine
factor is at most one. -/
theorem aq_haar_and_amplified_share_schedule (N M : ℕ) (hN : 0 < N) (hM : 0 < M)
    (hMN : 2 * M ≤ N) :
    aqRounds N M = Nat.floor (Real.pi / (4 * aqAngle N M)) ∧
      (Real.sin (2 * (aqRounds N M : ℝ) * aqAngle N M)) ^ 2 ≤ 1 := by
  refine ⟨rfl, ?_⟩
  exact Real.sin_sq_le_one _

/-- The bounded fair label sampler assigns equal mass to each label, has rejection mass at most
`2^(-fuel)`, expected bit cost at most `2 * Nat.clog 2 C`, and bounded cost `fuel * Nat.clog
2 C`. -/
theorem aq_fair_sampler_ledger (C fuel : ℕ) (hC : 0 < C) :
    (∀ j : Fin C, CostedLaw.event (aqFairLabelSampler C fuel)
      (fun z => z.1 = Sum.inl j) =
      (1 - coinRejectMass (Nat.clog 2 C) C ^ fuel) / (C : ℝ≥0∞)) ∧
    CostedLaw.event (aqFairLabelSampler C fuel) (fun z => z.1 = Sum.inr ()) ≤
      (1 / 2 : ℝ≥0∞) ^ fuel ∧
    CostedLaw.expectedCost (aqFairLabelSampler C fuel) ≤
      ((2 * Nat.clog 2 C : ℕ) : ℝ≥0∞) ∧
    CostedLaw.BoundedBy (aqFairLabelSampler C fuel) (fuel * Nat.clog 2 C) :=
  aqFairLabelSampler_distribution_and_bits C fuel hC

/-- The local QFT has the relabeled Fourier matrix, `n + n * (n - 1) / 2 + n / 2` gates, and
zero queries. -/
theorem aq_local_qft_cost (n : ℕ) :
    localProgramMatrix (localQFT n) =
      relabelGate (bitVecEquiv n).symm (QFTMatrix (2 ^ n)) ∧
    GateCount (localProgramCircuit (localQFT n)) = n + n * (n - 1) / 2 + n / 2 ∧
    QueryCount (localProgramCircuit (localQFT n)) = 0 :=
  aqLocalQFT_actual_matrix_and_cost n

/-- The fair bit ledger is `N * k`, while verification records `N * t` oracle accesses and `N *
k + t` classical work. -/
theorem aq_fair_bit_ledger (N t k : ℕ) :
    aqFairBitLedger N k = N * k ∧
      (aqVerifyCost N t k).oracleAccesses = N * t ∧
      (aqVerifyCost N t k).classicalWork = N * k + t := by
  simp [aqFairBitLedger, aqVerifyCost, aqFreshPassCost]

/-- No deterministic map from a fixed number of fair bits to three labels has equally sized
fibers. -/
theorem aq_fair_sampler_needs_rejection (k : ℕ) :
    ¬ ∃ f : Fin (2 ^ k) → Fin 3, ∀ x y : Fin 3,
      (Finset.univ.filter (fun b => f b = x)).card =
        (Finset.univ.filter (fun b => f b = y)).card :=
  three_label_bounded_fair_bits_impossible k

/-- For `M ≥ 2` and positive `N`, the envelope is minimized at `aqMinL M N` throughout `-M < L <
N - M`. -/
theorem aq_envelope_minimised_at_MinL {M N : ℕ} (hM : 2 ≤ M) (hN : 0 < N) (L : ℝ)
    (hL1 : -(M : ℝ) < L) (hL2 : L < (N : ℝ) - (M : ℝ)) :
    aqEnvelope N M (aqMinL M N) ≤ aqEnvelope N M L := by
  have h := errorExpectationMinimizedAtMinL M N hM hN
  simpa [aqEnvelope, aqMinL] using! h L hL1 hL2

/-- The sum of the Fourier phases vanishes when the frequency is nonzero modulo positive `N`. -/
theorem aq_geometric_sum_zero {N y : ℕ} (hN : 0 < N) (hne : y % N ≠ 0) :
    ∑ z ∈ Finset.range N, aqPhase N z y = 0 :=
  errorStreamGeometricSumZero N y hN hne

/-- The probability that a fresh Bernoulli noise stream leaves a candidate consistent equals `p`
raised to the candidate separation. -/
theorem aqNext_consistency_mass (N s M P P' : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (∑ σ : Fin N → Bool, (bernoulliStreamLaw N p hp hp1).prob σ *
      (if aqCandidateConsistent N s M P' (aqFreshMarked N s M P σ) then 1 else 0))
      = p ^ (aqCandidateSeparation N s M P P') :=
  aq_fresh_consistency_probability N s M P P' p hp hp1

/-- The fresh failure mass is bounded by the sum of `pmax` raised to each false candidate's
separation, when `0 ≤ p ≤ pmax < 1`. -/
theorem aqNext_failure_mass_le {N s M P : ℕ} {cands : Finset ℕ} {p pmax : ℝ} (hp : 0 ≤ p)
    (hp1 : p ≤ pmax) (hmax : pmax < 1) :
    aqFreshFailureMass N s M P cands p hp (le_trans hp1 hmax.le) ≤
      ∑ P' ∈ cands \ {P}, pmax ^ (aqCandidateSeparation N s M P P') := by
  classical
  have hp1' : p ≤ 1 := le_trans hp1 hmax.le

  have hpoint : ∀ σ : Fin N → Bool,
      (if ∃ P' ∈ cands \ {P},
          aqCandidateConsistent N s M P' (aqFreshMarked N s M P σ) then (1 : ℝ) else 0)
        ≤ ∑ P' ∈ cands \ {P},
            (if aqCandidateConsistent N s M P' (aqFreshMarked N s M P σ) then (1 : ℝ) else 0) := by
    intro σ
    by_cases hex : ∃ P' ∈ cands \ {P},
        aqCandidateConsistent N s M P' (aqFreshMarked N s M P σ)
    · rw [if_pos hex]
      obtain ⟨P', hP', hc⟩ := hex
      have hone : (1 : ℝ) ≤ ∑ P' ∈ cands \ {P},
          (if aqCandidateConsistent N s M P' (aqFreshMarked N s M P σ) then (1 : ℝ) else 0) := by
        have h1 : (if aqCandidateConsistent N s M P' (aqFreshMarked N s M P σ)
              then (1 : ℝ) else 0)
            ≤ ∑ x ∈ cands \ {P},
              (if aqCandidateConsistent N s M x (aqFreshMarked N s M P σ) then (1 : ℝ) else 0) := by
          refine Finset.single_le_sum
            (f := fun Q => if aqCandidateConsistent N s M Q (aqFreshMarked N s M P σ)
              then (1 : ℝ) else 0) ?_ hP'
          intro i _
          show 0 ≤ (if aqCandidateConsistent N s M i (aqFreshMarked N s M P σ)
            then (1 : ℝ) else 0)
          by_cases h : aqCandidateConsistent N s M i (aqFreshMarked N s M P σ) <;> simp [h]
        rw [if_pos hc] at h1
        exact h1
      linarith
    · rw [if_neg hex]
      exact Finset.sum_nonneg fun P' _ => by split <;> norm_num
  calc
    aqFreshFailureMass N s M P cands p hp (le_trans hp1 hmax.le)
        = ∑ σ : Fin N → Bool, (bernoulliStreamLaw N p hp (le_trans hp1 hmax.le)).prob σ *
            (if ∃ P' ∈ cands \ {P},
                aqCandidateConsistent N s M P' (aqFreshMarked N s M P σ) then (1 : ℝ) else 0) := rfl
    _ ≤ ∑ σ : Fin N → Bool, ∑ P' ∈ cands \ {P},
            (bernoulliStreamLaw N p hp (le_trans hp1 hmax.le)).prob σ *
              (if aqCandidateConsistent N s M P' (aqFreshMarked N s M P σ) then (1 : ℝ) else 0) := by
        refine Finset.sum_le_sum (s := (Finset.univ : Finset (Fin N → Bool))) fun σ _ => ?_
        calc
          (bernoulliStreamLaw N p hp (le_trans hp1 hmax.le)).prob σ *
              (if ∃ P'' ∈ cands \ {P},
                  aqCandidateConsistent N s M P'' (aqFreshMarked N s M P σ) then (1 : ℝ) else 0)
              ≤ (bernoulliStreamLaw N p hp (le_trans hp1 hmax.le)).prob σ *
                  ∑ P' ∈ cands \ {P},
                    (if aqCandidateConsistent N s M P' (aqFreshMarked N s M P σ) then (1 : ℝ) else 0) :=
                mul_le_mul_of_nonneg_left (hpoint σ)
                  ((bernoulliStreamLaw N p hp (le_trans hp1 hmax.le)).nonneg σ)
          _ = ∑ P' ∈ cands \ {P},
                (bernoulliStreamLaw N p hp (le_trans hp1 hmax.le)).prob σ *
                  (if aqCandidateConsistent N s M P' (aqFreshMarked N s M P σ) then (1 : ℝ) else 0) := by
                rw [Finset.mul_sum]
    _ = ∑ P' ∈ cands \ {P}, ∑ σ : Fin N → Bool,
          (bernoulliStreamLaw N p hp (le_trans hp1 hmax.le)).prob σ *
            (if aqCandidateConsistent N s M P' (aqFreshMarked N s M P σ) then (1 : ℝ) else 0) := by
        rw [Finset.sum_comm]
    _ ≤ ∑ P' ∈ cands \ {P}, pmax ^ (aqCandidateSeparation N s M P P') := by
        refine Finset.sum_le_sum fun P' _ => ?_
        rw [aqNext_consistency_mass N s M P P' p hp hp1']
        exact pow_le_pow_left₀ hp hp1 _

/-- A candidate returned by the disambiguation fold belongs to the scanned list or equals the
initial candidate; with no initial candidate it belongs to the list. -/
private theorem aqNext_disambiguate_fold_mem {N s M : ℕ} (p : ℝ) (obs : Finset (Fin N)) :
    ∀ (l : List ℕ) (best : Option ℕ) (Q : ℕ),
      l.foldl (fun best P => aqDisambiguateStep N s M p obs best P) best = some Q →
        (best = none → Q ∈ l) ∧ (∀ b, best = some b → Q ∈ l ∨ Q = b) := by
  intro l
  induction l with
  | nil =>
    intro best Q hfold
    have h : best = some Q := by simpa using! hfold
    constructor
    · intro hnone
      rw [hnone] at h
      simp at h
    · intro b hb
      rw [hb] at h
      simp at h
      exact Or.inr h.symm
  | cons x l ih =>
    intro best Q hfold
    have hfold' : l.foldl (fun best P => aqDisambiguateStep N s M p obs best P)
        (aqDisambiguateStep N s M p obs best x) = some Q := by
      simpa [List.foldl_cons] using! hfold
    constructor
    · intro hnone
      have hx : aqDisambiguateStep N s M p obs best x = some x := by
        unfold aqDisambiguateStep
        simp [hnone]
      have hrec := ih x Q (hx ▸ hfold')
      rcases hrec.2 x rfl with hl | hq
      · exact List.mem_cons_of_mem x hl
      · exact hq ▸ List.mem_cons_self
    · intro b hb
      by_cases hlt : aqCandidateLikelihood N s M x p obs >
          aqCandidateLikelihood N s M b p obs
      · have hx : aqDisambiguateStep N s M p obs best x = some x := by
          unfold aqDisambiguateStep
          rw [hb]
          simp [hlt]
        have hrec := ih x Q (hx ▸ hfold')
        rcases hrec.2 x rfl with hl | hq
        · exact Or.inl (List.mem_cons_of_mem x hl)
        · exact Or.inl (hq ▸ List.mem_cons_self)
      · have hb' : aqDisambiguateStep N s M p obs best x = some b := by
          unfold aqDisambiguateStep
          rw [hb]
          simp [hlt]
        have hrec := ih b Q (hb' ▸ hfold')
        rcases hrec.2 b rfl with hl | hq
        · exact Or.inl (List.mem_cons_of_mem x hl)
        · exact Or.inr hq

/-- Every candidate returned by fresh disambiguation belongs to the compatible candidate set. -/
theorem aqNext_disambiguation_output_sound {N s M : ℕ} (cands : Finset ℕ) (p : ℝ)
    (obs : Finset (Fin N)) (Q : ℕ)
    (hQ : aqFreshDisambiguate N s M cands p obs = some Q) :
    Q ∈ aqFreshCompatible N s M cands obs := by
  classical
  have hfold : (aqFreshCompatible N s M cands obs).toList.foldl
      (fun best P => aqDisambiguateStep N s M p obs best P) none = some Q := hQ
  have hmem := aqNext_disambiguate_fold_mem p obs
    (aqFreshCompatible N s M cands obs).toList none Q hfold
  have h1 : Q ∈ (aqFreshCompatible N s M cands obs).toList := hmem.1 rfl
  exact (Finset.mem_toList.mp h1)

/-- The observation set `{0, 1, 2}` in `Fin 8` is consistent with both periods one and two for
offset zero and length two. -/
theorem aqNext_fixed_noise_ambiguous_concrete :
    aqCandidateConsistent 8 0 2 1 ({0, 1, 2} : Finset (Fin 8)) ∧
      aqCandidateConsistent 8 0 2 2 ({0, 1, 2} : Finset (Fin 8)) := by
  constructor
  · intro x hx

    simp only [aqProgressionSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rcases hx with ⟨r, hr, hval⟩
    have hr' : r < 2 := Finset.mem_range.mp hr
    rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
    · have hxv : x.val = 0 := by simp at hval; omega
      have hx0 : x = (0 : Fin 8) := Fin.ext hxv
      simp [hx0]
    · have hxv : x.val = 1 := by simp at hval; omega
      have hx1 : x = (1 : Fin 8) := Fin.ext hxv
      simp [hx1]
  · intro x hx
    simp only [aqProgressionSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rcases hx with ⟨r, hr, hval⟩
    have hr' : r < 2 := Finset.mem_range.mp hr
    rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
    · have hxv : x.val = 0 := by simp at hval; omega
      have hx0 : x = (0 : Fin 8) := Fin.ext hxv
      simp [hx0]
    · have hxv : x.val = 2 := by simp at hval; omega
      have hx2 : x = (2 : Fin 8) := Fin.ext hxv
      simp [hx2]

/-- There exist two distinct candidate periods consistent with the same fixed observation set. -/
theorem aqNext_fixed_noise_ambiguous :
    ∃ (N s M P P' : ℕ) (obs : Finset (Fin N)),
      P ≠ P' ∧ aqCandidateConsistent N s M P obs ∧
        aqCandidateConsistent N s M P' obs :=
  ⟨8, 0, 2, 1, 2, ({0, 1, 2} : Finset (Fin 8)), by norm_num,
    aqNext_fixed_noise_ambiguous_concrete.1, aqNext_fixed_noise_ambiguous_concrete.2⟩

/-- The separation of the concrete period one and period two candidates is one. -/
theorem aqNext_fixed_noise_separation_one :
    aqCandidateSeparation 8 0 2 1 2 = 1 := by
  rw [aqCandidateSeparation]
  refine Finset.card_eq_one.mpr ⟨⟨2, by norm_num⟩, ?_⟩
  ext x
  simp only [aqProgressionSet, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ,
    Finset.mem_singleton, true_and]
  constructor
  · rintro ⟨⟨r, hr, hval⟩, hnot⟩
    have hr' : r < 2 := Finset.mem_range.mp hr
    rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
    · exfalso
      exact hnot ⟨0, Finset.mem_range.mpr (by norm_num), by simp [hval]⟩
    · have hxv : x.val = 2 := by simpa using! hval
      exact Fin.ext hxv
  · intro hx
    subst hx
    refine ⟨⟨1, by norm_num, ?_⟩, ?_⟩
    · simp
    · intro hmem
      rcases hmem with ⟨r, hr, hval⟩
      have hr' : r < 2 := Finset.mem_range.mp hr
      have hval' : (2 : ℕ) = 0 + r * 1 := by simpa using! hval
      omega

/-- Positive candidate separation and `0 ≤ p < 1` give strictly positive fresh rejection
probability `1 - p^separation`. -/
theorem aqNext_fresh_separates {N s M P P' : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hp1' : p < 1) (hsep : 0 < aqCandidateSeparation N s M P P') :
    0 < 1 - p ^ (aqCandidateSeparation N s M P P') := by
  have hle : p ^ aqCandidateSeparation N s M P P' ≤ p := by
    have hmono : ∀ n : ℕ, 1 ≤ n → p ^ n ≤ p := by
      intro n hn
      induction n with
      | zero => omega
      | succ n ih =>
        rw [pow_succ]
        by_cases hn0 : 1 ≤ n
        · have h := ih hn0
          calc p ^ n * p ≤ p * p := mul_le_mul_of_nonneg_right h hp
            _ ≤ 1 * p := mul_le_mul_of_nonneg_right hp1 (by linarith)
            _ = p := one_mul p
        · have hn0' : n = 0 := by omega
          subst hn0'
          simp
    exact hmono _ (by omega)
  have hlt : p ^ aqCandidateSeparation N s M P P' < 1 := lt_of_le_of_lt hle hp1'
  linarith

/-- The same run cost is the sum of the continued fraction and three access verification cost
and the fresh pass cost. -/
theorem aqNext_same_run_cost_eq (N t k : ℕ) :
    aqSameRunCost N t k =
      ({ oracleAccesses := 3
         classicalWork :=
           (cfDepth N + 1) + (cfDepth N + 1) * (cfDepth N + 2) / 2 } :
        aqExecutionCost).add
        (aqFreshPassCost N t k) := by
  simp [aqSameRunCost, aqFreshPassCost, aqExecutionCost.add]

/-- A fixed noise record is true exactly on the union of the planted progression and the noise
set. -/
theorem aqNext_fixed_noise_record_mem {N s M P : ℕ} {G : Finset (Fin N)} {x : Fin N} :
    aqNextFixedNoiseRecord N s M P G x = true ↔
      x ∈ aqProgressionSet N s M P ∪ G := by
  have hmem : (aqNextProgressionMember N s M P x = true ↔
      ∃ r < M, x.val = s + r * P) := by
    simp only [aqNextProgressionMember, decide_eq_true_eq]
  have hprog : ((∃ r < M, x.val = s + r * P) ↔ x ∈ aqProgressionSet N s M P) := by
    simp only [aqProgressionSet, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨r, hr, hval⟩
      exact ⟨r, Finset.mem_range.mpr hr, hval⟩
    · rintro ⟨r, hr, hval⟩
      exact ⟨r, Finset.mem_range.mp hr, hval⟩
  simp only [aqNextFixedNoiseRecord, decide_eq_true_eq, Finset.mem_union]
  constructor
  · intro h
    rcases h with h1 | h2
    · exact Or.inl (hprog.mp (hmem.mp h1))
    · exact Or.inr h2
  · intro h
    rcases h with h1 | h2
    · exact Or.inl (hmem.mpr (hprog.mpr h1))
    · exact Or.inr h2

/-- A positive candidate passes verification when its three required positions lie in range and
are marked. -/
private theorem aqNext_verify_of_marks {N : ℕ} (f : Fin N → Bool) (s M q : ℕ)
    (h : 0 < q ∧ s < N ∧ s + q < N ∧ s + (M - 1) * q < N)
    (h0 : f ⟨s, h.2.1⟩ = true) (h1 : f ⟨s + q, h.2.2.1⟩ = true)
    (h2 : f ⟨s + (M - 1) * q, h.2.2.2⟩ = true) :
    (aqNextVerify f s M q).1 = true := by
  unfold aqNextVerify
  rw [dif_pos h]
  simp [h0, h1, h2]

/-- Every in range planted progression point is marked by the fixed noise record. -/
private theorem aqNext_planted_marked {N s M P : ℕ} {G : Finset (Fin N)} {x : Fin N}
    (v : ℕ) (hv : x.val = v) (hx : ∃ r < M, v = s + r * P) :
    aqNextFixedNoiseRecord N s M P G x = true := by
  simp only [aqNextFixedNoiseRecord, aqNextProgressionMember, decide_eq_true_eq]
  obtain ⟨r, hr, hval⟩ := hx
  exact Or.inl ⟨r, hr, hv.trans hval⟩

/-- When `M, P ≥ 2` and the planted progression lies in range, its period passes fixed record
verification. -/
private theorem aqNext_planted_verified {N s M P : ℕ} {G : Finset (Fin N)}
    (hM : 2 ≤ M) (hP : 2 ≤ P) (hb : s + (M - 1) * P < N) :
    (aqNextVerify (aqNextFixedNoiseRecord N s M P G) s M P).1 = true := by
  have hMP : P ≤ (M - 1) * P := by
    have h1 : 1 ≤ M - 1 := by omega
    simpa using! Nat.mul_le_mul_right P h1
  refine aqNext_verify_of_marks _ s M P ?_ ?_ ?_ ?_
  · exact ⟨by omega, by omega, by omega, hb⟩
  · exact aqNext_planted_marked s rfl ⟨0, by omega, by simp⟩
  · exact aqNext_planted_marked (s + P) rfl ⟨1, by omega, by simp⟩
  · exact aqNext_planted_marked (s + (M - 1) * P) rfl ⟨M - 1, by omega, by simp⟩

/-- A good Fourier window sample makes the recovery attempt return the planted period under the
stated range and separation bounds. -/
theorem aqNext_attempt_true_period_hit {N : ℕ} (s M P B : ℕ) (G : Finset (Fin N))
    (y : Fin N) (hM : 2 ≤ M) (hP : 2 ≤ P) (hb : s + (M - 1) * P < N)
    (hPB : P ≤ B) (hsepB : 2 * B ^ 2 < N) (hy : y ∈ aqGoodWindow N P) :
    (aqNextAttempt (aqNextFixedNoiseRecord N s M P G) s M B y).1 = some P := by
  have hd := aq_good_decode N P B y (by omega) hPB hsepB hy
  obtain ⟨a, ha⟩ := hd
  have hver := aqNext_planted_verified (N := N) (s := s) (M := M) (P := P) (G := G)
    hM hP hb
  unfold aqNextAttempt
  (try dsimp only)
  rw [ha]
  simp [hver]

/-- Every value returned by a recovery attempt passes the fixed record verification check. -/
theorem aqNext_attempt_output_verified {N : ℕ} (s M P B : ℕ) (G : Finset (Fin N))
    (y : Fin N) (hM : 2 ≤ M) (hP : 2 ≤ P) (hb : s + (M - 1) * P < N)
    (hPB : P ≤ B) (hsepB : 2 * B ^ 2 < N) (q : ℕ)
    (hq : (aqNextAttempt (aqNextFixedNoiseRecord N s M P G) s M B y).1 = some q) :
    (aqNextVerify (aqNextFixedNoiseRecord N s M P G) s M q).1 = true := by
  unfold aqNextAttempt at hq
  (try dsimp only at hq)
  split at hq
  · simp at hq
  · rename_i c hc
    (try dsimp only at hq)
    split at hq
    · rename_i hv
      rw [Option.some.inj hq] at hv
      exact hv
    · simp at hq

/-- A recovery attempt uses at most three verification accesses and `cfDepth N + 1` decoding
steps, with the stated triangular generation work. -/
theorem aqNext_attempt_cost {N : ℕ} (s M P B : ℕ) (G : Finset (Fin N)) (y : Fin N) :
    (aqNextAttempt (aqNextFixedNoiseRecord N s M P G) s M B y).2.1 ≤ 3 ∧
      (aqNextAttempt (aqNextFixedNoiseRecord N s M P G) s M B y).2.2.1 ≤ cfDepth N + 1 ∧
      (aqNextAttempt (aqNextFixedNoiseRecord N s M P G) s M B y).2.2.2 =
        (cfDepth N + 1) * (cfDepth N + 2) / 2 := by
  have hN : 0 < N := Nat.zero_lt_of_lt y.isLt
  have hd := continued_fraction_bad_output_soundness_and_work B N y.val
  have hg : (cfRationalDecode B N y.val).2.2 = (cfDepth N + 1) * (cfDepth N + 2) / 2 := by
    simp [cfRationalDecode, (show N ≠ 0 by omega), cfGenerationWork_eq]
  have hv : ∀ q : ℕ, (aqNextVerify (aqNextFixedNoiseRecord N s M P G) s M q).2 ≤ 3 := by
    intro q
    exact aqVerify_cost _ _ _ _
  refine ⟨?_, ?_, ?_⟩
  · unfold aqNextAttempt
    (try dsimp only)
    split
    · simp
    · exact hv _
  · unfold aqNextAttempt
    (try dsimp only)
    split <;> exact hd.1
  · unfold aqNextAttempt
    (try dsimp only)
    split <;> exact hg

/-- The points zero and one are marked in the concrete period one fixed noise record. -/
private theorem aqNext_period_one_marked (x : Fin 8) (hx : x.val = 0 ∨ x.val = 1) :
    aqNextFixedNoiseRecord 8 0 2 1 ({0, 1, 2} : Finset (Fin 8)) x = true := by
  simp only [aqNextFixedNoiseRecord, aqNextProgressionMember, decide_eq_true_eq]
  rcases hx with h0 | h1
  · exact Or.inl ⟨0, by omega, by simp [h0]⟩
  · exact Or.inl ⟨1, by omega, by simp [h1]⟩

/-- The points zero and two are marked in the concrete period two fixed noise record. -/
private theorem aqNext_period_two_marked (x : Fin 8) (hx : x.val = 0 ∨ x.val = 2) :
    aqNextFixedNoiseRecord 8 0 2 2 ({0, 1, 2} : Finset (Fin 8)) x = true := by
  simp only [aqNextFixedNoiseRecord, aqNextProgressionMember, decide_eq_true_eq]
  rcases hx with h0 | h1
  · exact Or.inl ⟨0, by omega, by simp [h0]⟩
  · exact Or.inl ⟨1, by omega, by simp [h1]⟩

/-- The concrete periods one and two produce identical fixed noise records, and each passes its
corresponding verification check. -/
theorem aqNext_fixed_record_two_planted_concrete :
    (∀ x : Fin 8, aqNextFixedNoiseRecord 8 0 2 1 ({0, 1, 2} : Finset (Fin 8)) x = true ↔
        aqNextFixedNoiseRecord 8 0 2 2 ({0, 1, 2} : Finset (Fin 8)) x = true) ∧
      (aqNextVerify (aqNextFixedNoiseRecord 8 0 2 1 ({0, 1, 2} : Finset (Fin 8))) 0 2 1).1 = true ∧
      (aqNextVerify (aqNextFixedNoiseRecord 8 0 2 2 ({0, 1, 2} : Finset (Fin 8))) 0 2 2).1 = true := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    rw [aqNext_fixed_noise_record_mem, aqNext_fixed_noise_record_mem]
    simp only [Finset.mem_union]
    constructor
    · intro h
      rcases h with h1 | h2
      · have hx : x.val = 0 ∨ x.val = 1 := by
          simp only [aqProgressionSet, Finset.mem_filter, Finset.mem_univ, true_and] at h1
          rcases h1 with ⟨r, hr, hval⟩
          have hr' : r < 2 := Finset.mem_range.mp hr
          rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
          · simp at hval
            omega
          · simp at hval
            omega
        rcases hx with h0 | h1'
        · have hx0 : x = (0 : Fin 8) := Fin.ext h0
          simp [hx0]
        · have hx1 : x = (1 : Fin 8) := Fin.ext h1'
          simp [hx1]
      · exact Or.inr h2
    · intro h
      rcases h with h1 | h2
      · have hx : x.val = 0 ∨ x.val = 2 := by
          simp only [aqProgressionSet, Finset.mem_filter, Finset.mem_univ, true_and] at h1
          rcases h1 with ⟨r, hr, hval⟩
          have hr' : r < 2 := Finset.mem_range.mp hr
          rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
          · simp at hval
            omega
          · simp at hval
            omega
        rcases hx with h0 | h1'
        · have hx0 : x = (0 : Fin 8) := Fin.ext h0
          simp [hx0]
        · have hx2 : x = (2 : Fin 8) := Fin.ext h1'
          simp [hx2]
      · exact Or.inr h2
  · refine aqNext_verify_of_marks (aqNextFixedNoiseRecord 8 0 2 1
      ({0, 1, 2} : Finset (Fin 8))) 0 2 1 ?_ ?_ ?_ ?_
    · exact ⟨by omega, by omega, by omega, by omega⟩
    · exact aqNext_period_one_marked _ (Or.inl rfl)
    · exact aqNext_period_one_marked _ (Or.inr rfl)
    · exact aqNext_period_one_marked _ (Or.inr rfl)
  · refine aqNext_verify_of_marks (aqNextFixedNoiseRecord 8 0 2 2
      ({0, 1, 2} : Finset (Fin 8))) 0 2 2 ?_ ?_ ?_ ?_
    · exact ⟨by omega, by omega, by omega, by omega⟩
    · exact aqNext_period_two_marked _ (Or.inl rfl)
    · exact aqNext_period_two_marked _ (Or.inr rfl)
    · exact aqNext_period_two_marked _ (Or.inr rfl)

/-- Two distinct planted periods can produce identical fixed noise records while both pass
verification. -/
theorem aqNext_fixed_record_two_planted :
    ∃ (N s M P P' : ℕ) (G : Finset (Fin N)),
      P ≠ P' ∧
        (∀ x : Fin N, aqNextFixedNoiseRecord N s M P G x = true ↔
          aqNextFixedNoiseRecord N s M P' G x = true) ∧
        (aqNextVerify (aqNextFixedNoiseRecord N s M P G) s M P).1 = true ∧
        (aqNextVerify (aqNextFixedNoiseRecord N s M P' G) s M P').1 = true :=
  ⟨8, 0, 2, 1, 2, ({0, 1, 2} : Finset (Fin 8)), by norm_num,
    aqNext_fixed_record_two_planted_concrete.1,
    aqNext_fixed_record_two_planted_concrete.2.1,
    aqNext_fixed_record_two_planted_concrete.2.2⟩

/-- The selected Bernoulli tape set has cardinality `a` when `a ≤ 2^k`. -/
theorem aqNext_tapes_card (k a : ℕ) (ha : a ≤ 2 ^ k) :
    (aqNextBernoulliTapes k a ha).card = a := by
  have hcard : (aqNextBernoulliTapes k a ha).card = (Finset.univ : Finset (Fin a)).card := by
    unfold aqNextBernoulliTapes
    rw [Finset.card_image_iff]
    intro x _ y _ hxy
    have h := congrArg (bitVecEquiv k) hxy
    have hval : x.val = y.val := by simpa using! h
    exact Fin.ext hval
  rw [hcard, Finset.card_univ]
  simp

/-- The Bernoulli draw is true exactly on the selected tape set. -/
theorem aqNext_draw_iff (k a : ℕ) (ha : a ≤ 2 ^ k) (tape : Reg k) :
    aqNextBernoulliDraw k a ha tape = true ↔ tape ∈ aqNextBernoulliTapes k a ha := by
  simp [aqNextBernoulliDraw]

/-- Exactly `a` tapes of length `k` make the Bernoulli draw true. -/
theorem aqNext_marked_count (k a : ℕ) (ha : a ≤ 2 ^ k) :
    (∑ tape : Reg k, (if aqNextBernoulliDraw k a ha tape = true then 1 else 0)) = a := by
  have hcard : (∑ tape : Reg k, (if aqNextBernoulliDraw k a ha tape = true then 1 else 0))
      = (aqNextBernoulliTapes k a ha).card := by
    have h := Finset.card_filter (fun tape : Reg k => aqNextBernoulliDraw k a ha tape = true)
      (Finset.univ : Finset (Reg k))
    have hfilter : (Finset.univ : Finset (Reg k)).filter
        (fun tape : Reg k => aqNextBernoulliDraw k a ha tape = true)
        = aqNextBernoulliTapes k a ha := by
      ext tape
      simp [aqNextBernoulliDraw]
    calc
      (∑ tape : Reg k, (if aqNextBernoulliDraw k a ha tape = true then 1 else 0))
          = ((Finset.univ : Finset (Reg k)).filter
              (fun tape : Reg k => aqNextBernoulliDraw k a ha tape = true)).card := h.symm
      _ = (aqNextBernoulliTapes k a ha).card := by rw [hfilter]
  rw [hcard, aqNext_tapes_card k a ha]

/-- The effective probability of a true Bernoulli draw equals its dyadic parameter. -/
theorem aqNext_effective_site_prob (k a : ℕ) (ha : a ≤ 2 ^ k) :
    aqNextEffectiveSiteProb k a ha = aqNextEffectiveParameter k a := by
  unfold aqNextEffectiveSiteProb aqNextEffectiveParameter
  have hprob : ∀ tape : Reg k, (uniformFairTapeLaw k).prob tape = ((2 : ℝ) ^ k)⁻¹ :=
    fun _ => rfl
  have hcountR : (∑ tape : Reg k,
        (if aqNextBernoulliDraw k a ha tape = true then 1 else 0) : ℝ) = (a : ℝ) := by
    exact_mod_cast aqNext_marked_count k a ha
  have hmain : (∑ tape : Reg k, (uniformFairTapeLaw k).prob tape *
        (if aqNextBernoulliDraw k a ha tape = true then 1 else 0))
      = ((2 : ℝ) ^ k)⁻¹ * (a : ℝ) := by
    have hsum : (∑ tape : Reg k, (uniformFairTapeLaw k).prob tape *
        (if aqNextBernoulliDraw k a ha tape = true then 1 else 0))
        = ∑ tape : Reg k, ((2 : ℝ) ^ k)⁻¹ *
          (if aqNextBernoulliDraw k a ha tape = true then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro tape _
      rw [hprob tape]
    rw [hsum, ← Finset.mul_sum, hcountR]
  rw [hmain, div_eq_mul_inv, mul_comm]

/-- The probability of a false Bernoulli draw is one minus the effective true probability. -/
theorem aqNext_site_indicator_complement (k a : ℕ) (ha : a ≤ 2 ^ k) :
    (∑ tape : Reg k, (uniformFairTapeLaw k).prob tape *
        (if aqNextBernoulliDraw k a ha tape = false then 1 else 0))
      = 1 - aqNextEffectiveSiteProb k a ha := by
  have hsplit : ∀ tape : Reg k,
      (if aqNextBernoulliDraw k a ha tape = false then (1 : ℝ) else 0) =
        1 - (if aqNextBernoulliDraw k a ha tape = true then (1 : ℝ) else 0) := by
    intro tape
    cases h : aqNextBernoulliDraw k a ha tape <;> simp [h]
  calc
    (∑ tape : Reg k, (uniformFairTapeLaw k).prob tape *
        (if aqNextBernoulliDraw k a ha tape = false then 1 else 0))
      = ∑ tape : Reg k, (uniformFairTapeLaw k).prob tape *
          (1 - (if aqNextBernoulliDraw k a ha tape = true then 1 else 0)) := by
            apply Finset.sum_congr rfl
            intro tape _
            exact congrArg (fun x => (uniformFairTapeLaw k).prob tape * x) (hsplit tape)
    _ = (∑ tape : Reg k, (uniformFairTapeLaw k).prob tape) -
        ∑ tape : Reg k, (uniformFairTapeLaw k).prob tape *
          (if aqNextBernoulliDraw k a ha tape = true then 1 else 0) := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro tape _
            ring
    _ = 1 - aqNextEffectiveSiteProb k a ha := by
      rw [(uniformFairTapeLaw k).sum_one]
      unfold aqNextEffectiveSiteProb
      rfl

/-- The expectation of a product of site functions under the Bernoulli stream law factors into
the product of the site expectations. -/
theorem aqNext_bernoulli_stream_independent (N : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (g : Fin N → Bool → ℝ) :
    (∑ σ : Fin N → Bool, (aqNextBernoulliStreamLaw N p hp hp1).prob σ * ∏ i, g i (σ i))
      = ∏ i, (∑ b : Bool, (aqNextBernoulliSiteLaw p hp hp1).prob b * g i b) := by
  unfold aqNextBernoulliStreamLaw
  exact FinDist.expect_prod (aqNextBernoulliSiteLaw p hp hp1) g

/-- The effective tape stream probability factors into Bernoulli site weights at the effective
dyadic parameter. -/
theorem aqNext_effective_stream_prob (N k a : ℕ) (ha : a ≤ 2 ^ k) (σ : Fin N → Bool) :
    aqNextEffectiveStreamProb N k a ha σ
      = ∏ i : Fin N, (if σ i then aqNextEffectiveParameter k a
          else 1 - aqNextEffectiveParameter k a) := by
  have hkey : ∀ ω : Fin N → Reg k,
      (∏ i : Fin N, (if aqNextBernoulliDraw k a ha (ω i) = σ i then (1 : ℝ) else 0))
        = (if aqNextBernoulliStream N k a ha ω = σ then 1 else 0) := by
    intro ω
    by_cases hall : ∀ i, aqNextBernoulliDraw k a ha (ω i) = σ i
    · have hstream : aqNextBernoulliStream N k a ha ω = σ := by
        funext i
        exact hall i
      have h1 : (∏ i : Fin N,
          (if aqNextBernoulliDraw k a ha (ω i) = σ i then (1 : ℝ) else 0)) = 1 :=
        Finset.prod_eq_one fun i _ => by simp [hall i]
      simp [h1, hstream]
    · have hex : ∃ i, aqNextBernoulliDraw k a ha (ω i) ≠ σ i := not_forall.mp hall
      have h0 : (∏ i : Fin N,
          (if aqNextBernoulliDraw k a ha (ω i) = σ i then (1 : ℝ) else 0)) = 0 := by
        obtain ⟨i, hi⟩ := hex
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
      have hstream : aqNextBernoulliStream N k a ha ω ≠ σ := by
        intro heq
        obtain ⟨i, hi⟩ := hex
        exact hi (congrFun heq i)
      simp [h0, hstream]
  have hsite (i : Fin N) :
      (∑ tape : Reg k, (uniformFairTapeLaw k).prob tape *
          (if aqNextBernoulliDraw k a ha tape = σ i then 1 else 0))
        = (if σ i then aqNextEffectiveParameter k a else 1 - aqNextEffectiveParameter k a) := by
    by_cases hσ : σ i = true
    · have h1 : (∑ tape : Reg k, (uniformFairTapeLaw k).prob tape *
          (if aqNextBernoulliDraw k a ha tape = σ i then 1 else 0))
        = ∑ tape : Reg k, (uniformFairTapeLaw k).prob tape *
          (if aqNextBernoulliDraw k a ha tape = true then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro tape _
        simp [hσ]
      have h2 : (∑ tape : Reg k, (uniformFairTapeLaw k).prob tape *
          (if aqNextBernoulliDraw k a ha tape = true then 1 else 0))
          = aqNextEffectiveSiteProb k a ha := rfl
      rw [h1, h2, aqNext_effective_site_prob]
      simp [hσ]
    · have h1 : (∑ tape : Reg k, (uniformFairTapeLaw k).prob tape *
          (if aqNextBernoulliDraw k a ha tape = σ i then 1 else 0))
        = ∑ tape : Reg k, (uniformFairTapeLaw k).prob tape *
          (if aqNextBernoulliDraw k a ha tape = false then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro tape _
        simp [hσ]
      rw [h1, aqNext_site_indicator_complement, aqNext_effective_site_prob]
      simp [hσ]
  unfold aqNextEffectiveStreamProb
  calc
    (∑ tapes : Fin N → Reg k, (uniformFairTapeProductLaw k N).prob tapes *
        (if aqNextBernoulliStream N k a ha tapes = σ then 1 else 0))
      = ∑ ω : Fin N → Reg k, (uniformFairTapeLaw k).probOf ω *
          (∏ i : Fin N, (if aqNextBernoulliDraw k a ha (ω i) = σ i then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro ω _
        have h1 : (uniformFairTapeProductLaw k N).prob ω = (uniformFairTapeLaw k).probOf ω := rfl
        rw [h1, hkey ω]
      _ = ∏ i : Fin N, ∑ tape : Reg k, (uniformFairTapeLaw k).prob tape *
          (if aqNextBernoulliDraw k a ha tape = σ i then 1 else 0) :=
        FinDist.expect_prod (uniformFairTapeLaw k)
          (fun i tape => if aqNextBernoulliDraw k a ha tape = σ i then 1 else 0)
      _ = ∏ i : Fin N, (if σ i then aqNextEffectiveParameter k a
          else 1 - aqNextEffectiveParameter k a) := by
        apply Finset.prod_congr rfl
        intro i _
        exact hsite i

/-- The Bernoulli stream probability is the product of `p` at true sites and `1 - p` at false
sites. -/
theorem aqNext_bernoulli_stream_prob (N : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (σ : Fin N → Bool) :
    (aqNextBernoulliStreamLaw N p hp hp1).prob σ
      = ∏ i : Fin N, (if σ i then p else 1 - p) := by
  unfold aqNextBernoulliStreamLaw aqNextBernoulliSiteLaw
  simp [FinDist.probOf]

/-- The effective dyadic parameter lies in `[0, 1]` when `a ≤ 2^k`. -/
theorem aqNext_effective_parameter_range (k a : ℕ) (ha : a ≤ 2 ^ k) :
    0 ≤ aqNextEffectiveParameter k a ∧ aqNextEffectiveParameter k a ≤ 1 := by
  have h2k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  constructor
  · apply div_nonneg
    · exact_mod_cast Nat.zero_le a
    · positivity
  · apply (div_le_iff₀ h2k).2
    have h : (a : ℝ) ≤ (2 ^ k : ℝ) := by exact_mod_cast ha
    simpa using! h

/-- The effective tape stream has exactly the Bernoulli stream probabilities at its effective
dyadic parameter. -/
theorem aqNext_effective_stream_eq_bernoulli (N k a : ℕ) (ha : a ≤ 2 ^ k) (σ : Fin N → Bool) :
    aqNextEffectiveStreamProb N k a ha σ
      = (aqNextBernoulliStreamLaw N (aqNextEffectiveParameter k a)
          (aqNext_effective_parameter_range k a ha).1
          (aqNext_effective_parameter_range k a ha).2).prob σ := by
  rw [aqNext_effective_stream_prob]
  unfold aqNextBernoulliStreamLaw aqNextBernoulliSiteLaw
  simp [FinDist.probOf]

/-- For `p ∈ [0, 1]`, the Bernoulli threshold at precision `k` is at most `2^k`. -/
theorem aqNext_threshold_le (k : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    aqNextBernoulliThreshold k p ≤ 2 ^ k :=
  aqNextThresholdFits k p hp0 hp1

/-- The dyadic threshold parameter is at most `p` and differs from it by strictly less than
`2^(-k)`. -/
theorem aqNext_effective_parameter_bounds (k : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (aqNextBernoulliThreshold k p : ℝ) / (2 : ℝ) ^ k ≤ p ∧
      p < (aqNextBernoulliThreshold k p : ℝ) / (2 : ℝ) ^ k + 1 / (2 : ℝ) ^ k := by
  have h2k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hfl : (aqNextBernoulliThreshold k p : ℝ) ≤ p * (2 : ℝ) ^ k :=
    Nat.floor_le (mul_nonneg hp0 (by positivity))
  have hlt : p * (2 : ℝ) ^ k < (aqNextBernoulliThreshold k p : ℝ) + 1 :=
    Nat.lt_floor_add_one (p * (2 : ℝ) ^ k)
  constructor
  · apply (div_le_iff₀ h2k).2
    exact hfl
  · have hdiv : (aqNextBernoulliThreshold k p : ℝ) / (2 : ℝ) ^ k + 1 / (2 : ℝ) ^ k
        = ((aqNextBernoulliThreshold k p : ℝ) + 1) / (2 : ℝ) ^ k := by
      field_simp
    rw [hdiv]
    apply (lt_div_iff₀ h2k).2
    exact hlt

/-- For `p ∈ [0, 1]`, the dyadic threshold parameters converge to `p` as the precision
increases. -/
theorem aqNext_effective_parameter_tendsto (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Filter.Tendsto (fun k => (aqNextBernoulliThreshold k p : ℝ) / (2 : ℝ) ^ k)
      Filter.atTop (nhds p) := by
  have hbounds : ∀ k : ℕ,
      0 ≤ p - (aqNextBernoulliThreshold k p : ℝ) / (2 : ℝ) ^ k ∧
        p - (aqNextBernoulliThreshold k p : ℝ) / (2 : ℝ) ^ k ≤ 1 / (2 : ℝ) ^ k := by
    intro k
    have hb := aqNext_effective_parameter_bounds k p hp0 hp1
    constructor
    · linarith [hb.1]
    · linarith [hb.2]
  have hinv : Filter.Tendsto (fun k : ℕ => 1 / (2 : ℝ) ^ k) Filter.atTop (nhds 0) := by
    have h := (tendsto_inv_atTop_zero : Filter.Tendsto (fun r : ℝ => r⁻¹) Filter.atTop (nhds 0)).comp
      (tendsto_pow_atTop_atTop_of_one_lt (α := ℝ) (by norm_num : (1 : ℝ) < 2))
    simpa [div_eq_mul_inv, one_mul] using! h
  have h1 : Filter.Tendsto (fun k : ℕ => p - (aqNextBernoulliThreshold k p : ℝ) / (2 : ℝ) ^ k)
      Filter.atTop (nhds 0) :=
    squeeze_zero (fun k => (hbounds k).1) (fun k => (hbounds k).2) hinv
  have h2 := (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => p) Filter.atTop (nhds p)).sub h1
  simpa [sub_sub_cancel, sub_zero] using! h2

/-- For each fixed Boolean stream, its effective tape probability converges to the Bernoulli
probability at `p`. -/
theorem aqNext_effective_stream_tendsto (N : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (σ : Fin N → Bool) :
    Filter.Tendsto (fun k => aqNextEffectiveStreamProb N k (aqNextBernoulliThreshold k p)
        (aqNext_threshold_le k p hp0 hp1) σ)
      Filter.atTop (nhds ((aqNextBernoulliStreamLaw N p hp0 hp1).prob σ)) := by
  have hparam := aqNext_effective_parameter_tendsto p hp0 hp1
  have hsite (i : Fin N) :
      Filter.Tendsto (fun k : ℕ => (if σ i then (aqNextBernoulliThreshold k p : ℝ) / (2 : ℝ) ^ k
          else 1 - (aqNextBernoulliThreshold k p : ℝ) / (2 : ℝ) ^ k))
        Filter.atTop (nhds (if σ i then p else 1 - p)) := by
    by_cases hσ : σ i = true
    · simpa [hσ] using! hparam
    · have h2 : Filter.Tendsto
          (fun k : ℕ => 1 - (aqNextBernoulliThreshold k p : ℝ) / (2 : ℝ) ^ k)
          Filter.atTop (nhds (1 - p)) := by
        convert! (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1)).sub hparam
          using 1
      simpa [hσ] using! h2
  have hprod : Filter.Tendsto (fun k : ℕ => ∏ i : Fin N, (if σ i then
        (aqNextBernoulliThreshold k p : ℝ) / (2 : ℝ) ^ k
      else 1 - (aqNextBernoulliThreshold k p : ℝ) / (2 : ℝ) ^ k))
      Filter.atTop (nhds (∏ i : Fin N, (if σ i then p else 1 - p))) := by
    have h := tendsto_finsetProd (s := (Finset.univ : Finset (Fin N)))
      (f := fun i k => (if σ i then (aqNextBernoulliThreshold k p : ℝ) / (2 : ℝ) ^ k
        else 1 - (aqNextBernoulliThreshold k p : ℝ) / (2 : ℝ) ^ k))
      (a := fun i => (if σ i then p else 1 - p))
      (by intro i _; exact hsite i)
    simpa using! h
  have hlaw : (aqNextBernoulliStreamLaw N p hp0 hp1).prob σ
      = ∏ i : Fin N, (if σ i then p else 1 - p) := by
    unfold aqNextBernoulliStreamLaw aqNextBernoulliSiteLaw
    simp [FinDist.probOf]
  have hstream : (fun k : ℕ => aqNextEffectiveStreamProb N k (aqNextBernoulliThreshold k p)
        (aqNext_threshold_le k p hp0 hp1) σ)
      = (fun k : ℕ => ∏ i : Fin N, (if σ i then
          (aqNextBernoulliThreshold k p : ℝ) / (2 : ℝ) ^ k
        else 1 - (aqNextBernoulliThreshold k p : ℝ) / (2 : ℝ) ^ k)) := by
    funext k
    rw [aqNext_effective_stream_prob]
    simp [aqNextEffectiveParameter]
  rw [hstream, hlaw]
  exact hprod

/-- The precision `k` threshold of the dyadic parameter `a / 2^k` is exactly `a`. -/
theorem aqNext_effective_exact_of_dyadic (k a : ℕ) (ha : a ≤ 2 ^ k) :
    aqNextBernoulliThreshold k ((a : ℝ) / (2 : ℝ) ^ k) = a := by
  have h2k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have heq : ((a : ℝ) / (2 : ℝ) ^ k) * (2 : ℝ) ^ k = (a : ℝ) := by
    field_simp
  rw [aqNextBernoulliThreshold, heq]
  exact Nat.floor_natCast a

/-- A dyadic parameter with natural numerator is nonnegative. -/
theorem aqNext_dyadic_nonneg (k a : ℕ) : 0 ≤ (a : ℝ) / (2 : ℝ) ^ k := by
  apply div_nonneg
  · exact_mod_cast Nat.zero_le a
  · positivity

/-- The dyadic parameter `a / 2^k` is at most one when `a ≤ 2^k`. -/
theorem aqNext_dyadic_le_one (k a : ℕ) (ha : a ≤ 2 ^ k) : (a : ℝ) / (2 : ℝ) ^ k ≤ 1 := by
  have h2k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  apply (div_le_iff₀ h2k).2
  have h : (a : ℝ) ≤ (2 ^ k : ℝ) := by exact_mod_cast ha
  simpa using! h

/-- For the dyadic parameter `a / 2^k`, effective tape stream probabilities equal the
corresponding Bernoulli stream probabilities exactly. -/
theorem aqNext_effective_stream_exact_of_dyadic (N k a : ℕ) (ha : a ≤ 2 ^ k)
    (σ : Fin N → Bool) :
    aqNextEffectiveStreamProb N k a ha σ
      = (aqNextBernoulliStreamLaw N ((a : ℝ) / (2 : ℝ) ^ k)
          (aqNext_dyadic_nonneg k a) (aqNext_dyadic_le_one k a ha)).prob σ := by
  have h1 : aqNextEffectiveStreamProb N k a ha σ
      = ∏ i : Fin N, (if σ i then aqNextEffectiveParameter k a
          else 1 - aqNextEffectiveParameter k a) :=
    aqNext_effective_stream_prob N k a ha σ
  have h2 : (aqNextBernoulliStreamLaw N ((a : ℝ) / (2 : ℝ) ^ k)
        (aqNext_dyadic_nonneg k a) (aqNext_dyadic_le_one k a ha)).prob σ
      = ∏ i : Fin N, (if σ i then (a : ℝ) / (2 : ℝ) ^ k
          else 1 - (a : ℝ) / (2 : ℝ) ^ k) :=
    aqNext_bernoulli_stream_prob N ((a : ℝ) / (2 : ℝ) ^ k) (aqNext_dyadic_nonneg k a)
      (aqNext_dyadic_le_one k a ha) σ
  rw [h1, h2]
  simp [aqNextEffectiveParameter]

/-- The Bernoulli bit cost plus `t` equals the classical work of a fresh pass. -/
theorem aqNext_bit_cost_eq_fresh_pass (N t k : ℕ) :
    aqNextBernoulliBitCost N k + t = (aqNextFreshPassCost N t k).classicalWork := rfl

/-- The classical work of a fresh pass is the Bernoulli bit cost plus `t`. -/
theorem aqNext_fresh_pass_cost_eq (N t k : ℕ) :
    (aqNextFreshPassCost N t k).classicalWork = aqNextBernoulliBitCost N k + t := rfl

/-- Establishes `clause24_endpoint`, covering the single item identity and the dense regime
bound for the Lemma 20 Fourier expression in [Cornwell2014]. -/
theorem clause24_endpoint_holds : clause24_endpoint := by
  refine ⟨?_, ?_⟩
  · intro n N s y hN hy hy0
    exact aq_lemma20_T1_endpoint (P := 2) hN hy hy0
  · intro n N M L T s P y A G hN hA hA_sub hG_sub hA_card hG_card hdisj hT hTpos
      hy hy0 hcyc hdense
    exact aq_lemma20_dense_regime A G hN hA hA_sub hG_sub hA_card hG_card hdisj hT hTpos
      hy hy0 hcyc hdense

/-- Establishes `clause26_endpoint`, combining fresh noise disambiguation, fixed record
ambiguity, verified recovery costs, and finite bit Bernoulli realization and convergence. -/
theorem clause26_endpoint_holds : clause26_endpoint := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N p hp hp1 g
    exact aq_bernoulli_stream_independent N p hp hp1 g
  · intro N s M P σ
    exact aq_true_period_always_consistent N s M P σ
  · intro N s M cands obs
    rfl
  · intro N s M P cands P' hP' σ hmem
    exact (Finset.mem_filter.mp hmem).2
  · intro N s M P cands P' hP' σ hnot hmem
    exact hnot (Finset.mem_filter.mp hmem).2
  · intro N s M P P' p hp hp1
    exact aq_fresh_consistency_probability N s M P P' p hp hp1
  · intro N s M P p cands hP σ hrefute
    exact aq_fresh_disambiguation_succeeds N s M P p cands hP σ hrefute
  · intro N s M P cands hP σ hne
    exact aq_fresh_failure_contained N s M P cands hP σ hne
  · intro N s M P p pmax hp hp1 hmax cands hP P' hP'

    have hp1' : p ≤ 1 := le_trans hp1 hmax.le
    have h1 := aq_fresh_consistency_probability N s M P P' p hp hp1'
    rw [h1]
    exact pow_le_pow_left₀ hp hp1 _
  · intro N s M P cands p pmax hp hp1 hmax
    exact aqNext_failure_mass_le hp hp1 hmax
  · intro N s M cands p obs Q
    exact aqNext_disambiguation_output_sound cands p obs Q
  · exact aqNext_fixed_noise_ambiguous
  · intro N s M P P' p hp hp1 hp1' hsep
    exact aqNext_fresh_separates hp hp1 hp1' hsep
  · intro N t k
    exact aqNext_same_run_cost_eq N t k
  · intro N s M P B G y hM hP hb hPB hsepB hy
    exact aqNext_attempt_true_period_hit s M P B G y hM hP hb hPB hsepB (by simpa using! hy)
  · intro N s M P B G y hM hP hb hPB hsepB q hq
    exact aqNext_attempt_output_verified s M P B G y hM hP hb hPB hsepB q hq
  · intro N s M P B G y
    exact aqNext_attempt_cost s M P B G y
  · exact aqNext_fixed_record_two_planted

  · intro k a ha
    exact aqNext_effective_site_prob k a ha
  · intro k a ha
    exact aqNext_effective_parameter_range k a ha
  · intro N k a ha σ
    refine ⟨aqNext_effective_parameter_range k a ha, ?_⟩
    exact aqNext_effective_stream_eq_bernoulli N k a ha σ
  · intro k p hp hp1
    exact aqNext_threshold_le k p hp hp1
  · intro k p hp hp1
    exact aqNext_effective_parameter_bounds k p hp hp1
  · intro k p hp hp1
    exact aqNext_effective_parameter_tendsto p hp hp1
  · intro N p hp hp1 σ
    exact aqNext_effective_stream_tendsto N p hp hp1 σ
  · intro k a ha
    exact aqNext_effective_exact_of_dyadic k a ha
  · intro N k a ha σ
    refine ⟨⟨aqNext_dyadic_nonneg k a, aqNext_dyadic_le_one k a ha⟩, ?_⟩
    exact aqNext_effective_stream_exact_of_dyadic N k a ha σ
  · intro N t k
    exact aqNext_bit_cost_eq_fresh_pass N t k

/-- Establishes `clause27_endpoint`, specifying the likelihood quotient, its zero denominator
convention, and nonnegativity of the success ratio. -/
theorem clause27_endpoint_holds : clause27_endpoint := by
  refine ⟨?_, ?_, ?_⟩
  · intro N s M P P' p obs
    by_cases hne : aqCandidateLikelihood N s M P' p obs = 0
    · rw [aq_successRatio_of_refuted p obs hne]
      simp [hne]
    · rw [aq_successRatio_eq_div p obs hne]
      simp [hne]
  · intro N s M P P' p obs hz
    exact aq_successRatio_of_refuted p obs hz
  · intro N s M P P' p obs hp hp1
    exact aq_successRatio_nonneg p obs hp hp1

/-- Establishes `clause28_endpoint`, combining angle monotonicity, round count monotonicity, and
the layer saving identity. -/
theorem clause28_endpoint_holds : clause28_endpoint := by
  refine ⟨?_, ?_, ?_⟩
  · intro N M hN hM hMN
    exact aqAngle_mono hN hM (by omega) hMN
  · intro N M hN hM hMN
    exact aqRounds_anti hN hM (by omega) hMN
  · intro N M L hN hM hML hLN
    exact aq_layer_round_le_public hN hM hML hLN

/-- Establishes `clause29_endpoint`, combining cyclic verification guarantees with exact public
density counting probabilities and resource counts. -/
theorem clause29_endpoint_holds : clause29_endpoint := by
  refine ⟨?_, ?_, ?_⟩
  · intro N hN h s M P G hM hP hMP hmark
    exact aq_unknown_M_recovery_cost hN h s M P hM hP hMP G hmark
  · intro N hN h s M P G hM hP hMP hmark
    exact ⟨aqNextCyclicVerify_true N hN h s M P hM hP hMP G hmark,
      aqNextCyclicVerify_cost N hN h s M P⟩
  · intro N hN C
    exact aqNextPublicDensityCounting_actual N hN C

/-- Establishes `clause30_endpoint`, combining dyadic Haar preparation, the Haar pair resource
ledger, and the amplification schedule. -/
theorem clause30_endpoint_holds : clause30_endpoint := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    exact aq_haar_dyadic_preparation n hn
  · intro n hn j
    exact aq_haar_pair_ledger n hn j
  · intro N M hN hM hMN
    exact aq_haar_and_amplified_share_schedule N M hN hM hMN

/-- Establishes `clause31_endpoint`, combining local QFT resource counts, the fair bit ledger,
and the obstruction to uniform three label sampling from a fixed bit budget. -/
theorem clause31_endpoint_holds : clause31_endpoint := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact (aq_local_qft_cost n).2
  · intro N t k
    exact aq_fair_bit_ledger N t k
  · intro k
    exact aq_fair_sampler_needs_rejection k

/-- Establishes `clause32_endpoint`, combining envelope minimization with vanishing nontrivial
geometric phase sums. -/
theorem clause32_endpoint_holds : clause32_endpoint := by
  refine ⟨?_, ?_⟩
  · intro M N hM hN L hL1 hL2
    exact aq_envelope_minimised_at_MinL hM hN L hL1 hL2
  · intro N y hN hne
    exact aq_geometric_sum_zero hN hne

end Qatlib.Concepts.FourierRecovery.ModularFourier
