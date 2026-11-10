/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.ErrorStream.AmplifiedPeriodRefinedDefs
import Qatlib.Concepts.AmplitudeCore.InvFreeSampling.AmplifiedNoiseExecution
import Qatlib.Concepts.FourierRecovery.ModularFourier.AmplifiedNoise
import Qatlib.Concepts.AmpTransform.FullLayerCF.FullLayerCFDenoiseUniquePAmpl
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QftPreparation.LocalQft
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.AmpTransform.ErrorStream
open Qatlib.Concepts.AmpTransform.FullLayerCF
open Qatlib.Concepts.AmpTransform.HaarPairTest
open Qatlib.Concepts.AmpTransform.NoiseEnvelope
open Qatlib.Concepts.AmpTransform.SuccessRatio
open Qatlib.Concepts.FourierRecovery.ModularFourier
open Qatlib.Concepts.AmpTransform.ErrorStream
open Qatlib.Concepts.AmplitudeCore.InvFreeSampling

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Qatlib.Concepts.AmpTransform.FullLayerCF

open Qatlib
open scoped Classical BigOperators ENNReal

theorem aqVerifiedCandidates_mem {N s M : ℕ} (h : Fin N → Bool) {P : ℕ} (hP : P < N)
    (hv : (aqVerify h s M P).1 = true) : P ∈ aqVerifiedCandidates N h s M := by
  simp [aqVerifiedCandidates, hP, hv]

theorem aqVerifiedCandidates_two {N s M : ℕ} (h : Fin N → Bool) {P P' : ℕ}
    (hP : P < N) (hP' : P' < N) (hne : P ≠ P')
    (hv : (aqVerify h s M P).1 = true) (hv' : (aqVerify h s M P').1 = true) :
    ∃ q ∈ aqVerifiedCandidates N h s M, q ≠ P := by
  refine ⟨P', aqVerifiedCandidates_mem h hP' hv', Ne.symm hne⟩

theorem aqPeriodSeparation_pos {N s M P P' : ℕ}
    (hnsub : ¬ aqPeriodProgression N s M P' ⊆ aqPeriodProgression N s M P) :
    0 < aqPeriodSeparation N s M P P' := by
  unfold aqPeriodSeparation aqCandidateSeparation
  have hcard : 0 < (aqProgressionSet N s M P' \ aqProgressionSet N s M P).card := by
    by_contra hcon
    have hempty : aqProgressionSet N s M P' \ aqProgressionSet N s M P = ∅ := by
      exact Finset.card_eq_zero.mp (Nat.eq_zero_of_not_pos hcon)
    have hsub : aqProgressionSet N s M P' ⊆ aqProgressionSet N s M P := by
      intro x hx
      have hnot : x ∉ aqProgressionSet N s M P' \ aqProgressionSet N s M P := by
        rw [hempty]
        simp
      by_contra hxt
      exact hnot (Finset.mem_sdiff.mpr ⟨hx, hxt⟩)
    exact hnsub hsub
  exact hcard

theorem aqPeriodConsistency_mass {N s M P P' : ℕ} (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (∑ σ : Fin N → Bool, (bernoulliStreamLaw N p hp hp1).prob σ *
      (if aqCandidateConsistent N s M P' (aqFreshMarked N s M P σ) then 1 else 0))
      = p ^ (aqPeriodSeparation N s M P P') := by
  exact aq_fresh_consistency_probability N s M P P' p hp hp1

theorem aqTwoStageUnique {N s M P : ℕ} (p : ℝ) (cands : Finset ℕ) (hP : P ∈ cands)
    (σ : Fin N → Bool)
    (hrefute : ∀ P' ∈ cands \ {P},
      ¬ aqCandidateConsistent N s M P' (aqFreshMarked N s M P σ)) :
    aqFreshCompatible N s M cands (aqFreshMarked N s M P σ) = {P} ∧
      aqFreshDisambiguate N s M cands p (aqFreshMarked N s M P σ) = some P :=
  aq_fresh_disambiguation_succeeds N s M P p cands hP σ hrefute

theorem aqZeroProgression_empty {N s P : ℕ} : aqPeriodProgression N s 0 P = ∅ := by
  simp [aqPeriodProgression, aqProgressionSet]

theorem aqZeroSeparation {N s P P' : ℕ} : aqPeriodSeparation N s 0 P P' = 0 := by
  unfold aqPeriodSeparation aqCandidateSeparation
  have h1 : aqProgressionSet N s 0 P' = ∅ := by
    simpa [aqPeriodProgression] using! aqZeroProgression_empty (N := N) (s := s) (P := P')
  have h2 : aqProgressionSet N s 0 P = ∅ := by
    simpa [aqPeriodProgression] using! aqZeroProgression_empty (N := N) (s := s) (P := P)
  simp [h1, h2]

theorem aqZeroNoInformation {N s M P P' : ℕ} (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hM : M = 0) :
    (∑ σ : Fin N → Bool, (bernoulliStreamLaw N p hp hp1).prob σ *
      (if aqCandidateConsistent N s M P' (aqFreshMarked N s M P σ) then 1 else 0)) = 1 := by
  subst hM
  have h := aqPeriodConsistency_mass (N := N) (s := s) (M := 0) (P := P) (P' := P') p hp hp1
  rw [aqZeroSeparation] at h
  rw [h]
  simp [pow_zero]

theorem aqLayerScheduleDensity {N M L : ℕ} (hN : 0 < N) (hM : 0 < M) (hML : M ≤ L)
    (hLN : 2 * L ≤ N) :
    aqLayerRoundCount N M L = aqRounds N L ∧ aqPublicRoundCount N M = aqRounds N M := by
  constructor <;> rfl

theorem aqLayerStepDistinct {N s M L P : ℕ} (hM : 0 < M) (hML : M < L) (hP : 0 < P)
    (hbound : s + (L - 1) * P < N) :
    aqPeriodProgression N s M P ≠ aqPeriodProgression N s L P := by
  intro heq
  have hlt : s + (L - 1) * P < N := hbound
  have hmem : (⟨s + (L - 1) * P, hlt⟩ : Fin N) ∈ aqPeriodProgression N s L P := by
    simp only [aqPeriodProgression, aqProgressionSet, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨L - 1, Finset.mem_range.mpr (by omega), rfl⟩
  have hmem' : (⟨s + (L - 1) * P, hlt⟩ : Fin N) ∈ aqPeriodProgression N s M P :=
    heq ▸ hmem
  simp only [aqPeriodProgression, aqProgressionSet, Finset.mem_filter, Finset.mem_univ,
    true_and] at hmem'
  obtain ⟨r, hr, heq'⟩ := hmem'
  have hr' : r < M := Finset.mem_range.mp hr
  have hcon : L - 1 = r := mul_right_cancel₀ hP.ne' (Nat.add_left_cancel heq')
  omega

private theorem aqNextUniformEntry (N : ℕ) [NeZero N] (x : ZMod N) :
    preparedAAState (zmodQFTGate (N := N)) 0 x = (Real.sqrt (N : ℝ) : ℂ)⁻¹ := by
  simp [preparedAAState, ApplyGate, Matrix.mulVec, dotProduct, Ket, zmodQFTGate_apply]

private theorem aqNextUniformMass (N : ℕ) [NeZero N] (S : Finset (ZMod N)) :
    MeasureProb (preparedAAState (zmodQFTGate (N := N)) 0) S = (S.card : ℝ)/N := by
  simp only [MeasureProb, BornProb, aqNextUniformEntry, norm_inv,
    Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg N), Finset.sum_const, nsmul_eq_mul]
  ring

private theorem aqNextQftSelected (N : ℕ) [NeZero N]
    (S : Finset (ZMod N)) (y : ZMod N) :
    ApplyGate zmodQFTGate (Collapse (preparedAAState (zmodQFTGate (N := N)) 0) S) y =
      (N : ℂ)⁻¹ * distinctNoiseFourier S y := by
  have hs : (Real.sqrt (N : ℝ) : ℂ)⁻¹ * (Real.sqrt (N : ℝ) : ℂ)⁻¹ = (N : ℂ)⁻¹ := by
    rw [← pow_two, inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
    simp
  simp only [ApplyGate, Matrix.mulVec, dotProduct, zmodQFTGate_apply,
    collapse_apply, aqNextUniformEntry]
  have he (x : ZMod N) : (Real.sqrt (N : ℝ) : ℂ)⁻¹ * ZMod.stdAddChar (y*x) *
      (if x ∈ S then (Real.sqrt (N : ℝ) : ℂ)⁻¹ else 0) =
      if x ∈ S then (N : ℂ)⁻¹ * ZMod.stdAddChar (x*y) else 0 := by
    by_cases hx : x ∈ S
    · simp only [if_pos hx]
      rw [mul_right_comm, hs, mul_comm y x]
    · simp [hx]
  simp_rw [he]
  rw [Finset.sum_ite_mem_eq, ← Finset.mul_sum]
  rfl

private theorem aqNextQftSelectedZero (N : ℕ) [NeZero N] (S : Finset (ZMod N)) :
    ApplyGate zmodQFTGate (Collapse (preparedAAState (zmodQFTGate (N := N)) 0) S) 0 =
      (((S.card : ℝ)/N : ℝ) : ℂ) := by
  rw [aqNextQftSelected]
  simp only [distinctNoiseFourier, mul_zero, AddChar.map_zero_eq_one,
    Finset.sum_const, nsmul_eq_mul, mul_one]
  push_cast
  ring

private theorem aqNextQftUniformZero (N : ℕ) [NeZero N] :
    ApplyGate zmodQFTGate (preparedAAState (zmodQFTGate (N := N)) 0) 0 = 1 := by
  have hc : Collapse (preparedAAState (zmodQFTGate (N := N)) 0) Finset.univ =
      preparedAAState (zmodQFTGate (N := N)) 0 := by
    ext x
    simp [collapse_apply]
  rw [← hc, aqNextQftSelectedZero]
  simp [ZMod.card, (NeZero.ne N)]

theorem aqNextAmplifiedZeroBorn (N k : ℕ) [NeZero N]
    (B : Finset (ZMod N)) (θ : ℝ) (hθ : 0 < θ) (hθp : θ < Real.pi/2)
    (hm : (Real.sin θ)^2 = (B.card : ℝ)/N) :
    BornProb (Run (preparedMark B) (conditionalAmplifiedQFTCircuit N k) (Ket 0)) 0 =
      (Real.cos (2*(k : ℝ)*θ))^2 := by
  have hr := prepared_aa_actual_rotation (zmodQFTGate (N := N)) 0 B θ k
    (zmodQFTGate_unitary (NeZero.pos N)) hθ hθp
    ((aqNextUniformMass N B).trans hm.symm)
  have hc : Real.cos θ ≠ 0 := (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθp⟩).ne'
  have hs : Real.sin θ ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hθ (by linarith [Real.pi_pos])).ne'
  have hcos : (Real.cos θ)^2 = 1 - (B.card : ℝ)/N := by
    have ht := Real.sin_sq_add_cos_sq θ
    rw [hm] at ht
    linarith
  have he : Real.cos ((2*(k : ℝ)+1)*θ)/Real.cos θ*(1-(B.card : ℝ)/N) +
      Real.sin ((2*(k : ℝ)+1)*θ)/Real.sin θ*((B.card : ℝ)/N) = Real.cos (2*(k : ℝ)*θ) := by
    rw [← hcos, ← hm]
    have hbad : Real.cos ((2*(k : ℝ)+1)*θ)/Real.cos θ*(Real.cos θ)^2 =
        Real.cos ((2*(k : ℝ)+1)*θ)*Real.cos θ := by field_simp
    have hgood : Real.sin ((2*(k : ℝ)+1)*θ)/Real.sin θ*(Real.sin θ)^2 =
        Real.sin ((2*(k : ℝ)+1)*θ)*Real.sin θ := by field_simp
    rw [hbad, hgood, ← Real.cos_sub]
    congr 1
    ring
  have ha : Run (preparedMark B) (conditionalAmplifiedQFTCircuit N k) (Ket 0) 0 =
      (Real.cos (2*(k : ℝ)*θ) : ℂ) := by
    rw [conditionalAmplifiedQFTCircuit, run_append, run_gate, run_nil, hr]
    simp only [ApplyGate, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_sub,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    change ((Real.cos ((2*(k : ℝ)+1)*θ)/Real.cos θ : ℝ) : ℂ) *
        (ApplyGate zmodQFTGate (preparedAAState (zmodQFTGate (N := N)) 0) 0 -
          ApplyGate zmodQFTGate (Collapse (preparedAAState (zmodQFTGate (N := N)) 0) B) 0) +
      ((Real.sin ((2*(k : ℝ)+1)*θ)/Real.sin θ : ℝ) : ℂ) *
        ApplyGate zmodQFTGate (Collapse (preparedAAState (zmodQFTGate (N := N)) 0) B) 0 = _
    rw [aqNextQftUniformZero, aqNextQftSelectedZero]
    exact_mod_cast he
  rw [BornProb, ha, Complex.norm_real, Real.norm_eq_abs, sq_abs]

private theorem aqNextProgressionCard (N s M P : ℕ) [NeZero N] (hP : 0 < P)
    (hbound : s+(M-1)*P < N) :
    ((Finset.range M).image (fun r : ℕ => (s+r*P : ZMod N))).card = M := by
  have hlabel (r : ℕ) (hr : r ∈ Finset.range M) : s+r*P < N := by
    have hr' : r ≤ M-1 := by have := Finset.mem_range.mp hr; omega
    exact (Nat.add_le_add_left (Nat.mul_le_mul_right P hr') s).trans_lt hbound
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro r hr t ht heq
  have h := congrArg ZMod.val heq
  simp only [← Nat.cast_add, ← Nat.cast_mul] at h
  rw [ZMod.val_natCast_of_lt (hlabel r hr), ZMod.val_natCast_of_lt (hlabel t ht)] at h
  exact mul_right_cancel₀ hP.ne' (Nat.add_left_cancel h)

theorem aqNextBernoulliErrorStreamZeroModeTransport :
    BernoulliErrorStreamZeroModeTransport := by
  intro N k _ p _hp _hp1 d hd s M P θ _hM hP hbound _hMN hθ
  (try dsimp only)
  let A : Finset (ZMod N) := (Finset.range M).image (fun r : ℕ => (s+r*P : ZMod N))
  let C := Finset.univ \ A
  have hA : A.card = M := aqNextProgressionCard N s M P hP hbound
  have hcard : C.card+A.card = N := by
    simpa only [Finset.card_univ, ZMod.card] using!
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
  have hC : C.card = N-M := by omega
  have hU := zmodQFTGate_unitary (N := N) (NeZero.pos N)
  have hw := prepared_aa_actual_circuit (zmodQFTGate (N := N)) 0 A k hU
  have hsets : ∀ L : ℕ, L ≤ C.card → ∀ S ∈ C.powersetCard L,
      Disjoint A S ∧ (A ∪ S).card = M+L := by
    intro L _hL S hS
    simpa only [hA] using! conditional_noise_record A S L hS
  have hrecord : ∀ L : ℕ, L < C.card → ∀ S ∈ C.powersetCard L,
      BornProb (Run (preparedMark (A ∪ S)) (conditionalAmplifiedQFTCircuit N k) (Ket 0)) 0 =
        (Real.cos (2*(k : ℝ)*θ L))^2 := by
    intro L hL S hS
    have ht := hθ L (by omega)
    apply aqNextAmplifiedZeroBorn N k (A ∪ S) (θ L) ht.1 ht.2.1
    rw [(hsets L hL.le S hS).2]
    exact ht.2.2
  have hmean (L : ℕ) (hL : L < C.card) :
      conditionalNoiseMean C L (fun S => BornProb
        (Run (preparedMark (A ∪ S)) (conditionalAmplifiedQFTCircuit N k) (Ket 0)) 0) =
        (Real.cos (2*(k : ℝ)*θ L))^2 := by
    rw [← conditionalNoiseMean_const C L hL.le ((Real.cos (2*(k : ℝ)*θ L))^2)]
    unfold conditionalNoiseMean
    congr 1
    apply Finset.sum_congr rfl
    intro S hS
    exact hrecord L hL S hS
  refine ⟨hA, hC, ?_, ?_, ?_, hsets, hrecord, hmean, ?_, ?_⟩
  · simp only [conditionalAmplifiedQFTCircuit, isUnitaryCircuit_append, isUnitaryCircuit_gate,
      isUnitaryCircuit_nil, and_true]
    exact ⟨hw.1, hU⟩
  · simp [conditionalAmplifiedQFTCircuit, queryCount_append, hw.2.1]
  · simp [conditionalAmplifiedQFTCircuit, gateCount_append, hw.2.2.1]
  · apply Finset.sum_congr rfl
    intro L hL
    exact congrArg ((C.card.choose L : ℝ)*p^L*(1-p)^(C.card-L) * ·)
      (hmean L (Finset.mem_range.mp hL))
  · simpa only [hA] using! bernoulli_complement_transport N p d hd A
      (fun S => BornProb (Run (preparedMark (A ∪ S)) (conditionalAmplifiedQFTCircuit N k) (Ket 0)) 0)

theorem aqNext_density_counting_queries (N : ℕ) (hN : 0 < N) :
    QueryCount (countedAECircuit (32 * N) (QFTMatrix N) (⟨0, hN⟩ : Fin N)) = 32 * N - 1 := by
  exact (aqNextPublicDensityCounting_actual N hN (∅ : Finset (Fin N))).2.1

theorem aqNext_recovery_query_runtime (N M L : ℕ) :
    aqNextPublicRecoveryQueries N M = aqNextDensityCountingQueries N + aqPublicRoundCount N M ∧
      aqNextLayerRecoveryQueries N M L = aqNextDensityCountingQueries N + aqLayerRoundCount N M L := by
  constructor <;> rfl

theorem aqNext_recovery_query_saving (N M L : ℕ) (hN : 0 < N) (hM : 0 < M)
    (hML : M ≤ L) (hLN : 2 * L ≤ N) :
    aqNextRecoveryQuerySaving N M L = aqRoundSaving N M L := by
  unfold aqNextRecoveryQuerySaving aqNextPublicRecoveryQueries aqNextLayerRecoveryQueries
    aqRoundSaving aqPublicRoundCount aqLayerRoundCount
  simp only [aqNextDensityCountingQueries]
  omega

theorem aqNext_recovery_gate_saving (N M L : ℕ) (hN : 0 < N) (hM : 0 < M)
    (hML : M ≤ L) (hLN : 2 * L ≤ N) :
    (5 * (32 * N - 1) + 3) + (3 * aqPublicRoundCount N M + 2) -
        ((5 * (32 * N - 1) + 3) + (3 * aqLayerRoundCount N M L + 2))
      = 3 * aqRoundSaving N M L := by
  have h := aqNext_recovery_query_saving N M L hN hM hML hLN
  unfold aqRoundSaving aqPublicRoundCount aqLayerRoundCount at h ⊢
  omega

theorem aqNext_optimal_layer_rounds (N M : ℕ) (hN : 0 < N) (hM : 0 < M) :
    (∀ L : ℕ, M ≤ L → 2 * L ≤ N → aqRounds N (N / 2) ≤ aqRounds N L) ∧
      2 * (N / 2) ≤ N := by
  constructor
  · intro L hML hLN
    have hLpos : 0 < L := lt_of_lt_of_le hM hML
    have hL : L ≤ N / 2 := by omega
    have hhalf : 2 * (N / 2) ≤ N := by omega
    exact aqRounds_anti hN hLpos hL hhalf
  · omega

theorem aqNext_optimal_layer_runtime (N M : ℕ) (hN : 0 < N) (hM : 0 < M)
    (L : ℕ) (hML : M ≤ L) (hLN : 2 * L ≤ N) :
    aqNextLayerRecoveryQueries N M (N / 2) ≤ aqNextLayerRecoveryQueries N M L := by
  have h := (aqNext_optimal_layer_rounds N M hN hM).1 L hML hLN
  unfold aqNextLayerRecoveryQueries aqLayerRoundCount
  omega

theorem clause4_endpoint : Clause4TwoStageRecovery := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro N s M h P hP hv
    exact aqVerifiedCandidates_mem h hP hv
  · intro N s M P P' hnsub
    exact aqPeriodSeparation_pos hnsub
  · intro N s M P P' p hp hp1 hsep
    exact aqPeriodConsistency_mass p hp hp1
  · intro N s M P p cands hP σ hrefute
    exact aqTwoStageUnique p cands hP σ hrefute

theorem clause5_endpoint : Clause5LayerStepDistinction := by
  refine And.intro ?_
      (And.intro ?_ (And.intro ?_ (And.intro ?_ (And.intro ?_ (And.intro ?_ (And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))))))))
  · intro N hN h s M P hM hP hMP G hmark
    exact aqCyclicVerify_true N hN h s M P hM hP hMP G hmark
  · intro N hN h s M q
    exact aqCyclicVerify_cost N hN h s M q
  · intro N M L hN hM hML hLN
    exact (aq_layer_round_le_public (N := N) (M := M) (L := L) hN hM hML hLN).1
  · intro N M L hN hM hML hLN
    rfl
  · intro N hN h s M P hM hP hMP G hmark
    exact aqNextCyclicVerify_true N hN h s M P hM hP hMP G hmark
  · intro N hN h s M q
    exact aqNextCyclicVerify_cost N hN h s M q
  · intro N hN C
    exact aqNextPublicDensityCounting_actual N hN C
  · intro N M L hN hM hML hLN
    exact aqLayerScheduleDensity hN hM hML hLN
  · intro N s M L P hM hML hP hbound
    exact aqLayerStepDistinct hM hML hP hbound
  · decide

theorem clause6_endpoint : Clause6ZeroMPromise := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact haarGeneralWN_answer
  · intro C fuel hC j
    exact (aqFairLabelSampler_distribution_and_bits C fuel hC).1 j
  · intro n
    exact (aqLocalQFT_actual_matrix_and_cost n).2.1
  · intro N s M P P' hM
    exact ⟨aqZeroProgression_empty, aqZeroSeparation⟩
  · intro N s M P P' p hp hp1 hM
    exact aqZeroNoInformation p hp hp1 hM
  · intro N hN
    exact aqNext_density_counting_queries N hN
  · intro N M L hN hM hML hLN
    exact aqNext_recovery_query_saving N M L hN hM hML hLN
  · intro N M L hN hM hML hLN
    exact aqNext_recovery_gate_saving N M L hN hM hML hLN
  · intro N M hN hM
    exact aqNext_optimal_layer_rounds N M hN hM
  · intro N M hN hM L hML hLN
    exact aqNext_optimal_layer_runtime N M hN hM L hML hLN
  · intro N M hN hM L hML hLN
    rfl

theorem clause7_endpoint : Clause7FixedNoiseBoundary := by
  obtain ⟨hG2, hG4, hd2, hd4, heq, hguard, hv2, hv4⟩ :=
    same_oracle_two_planted_periods
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [aqBoundaryOracle] using! heq
  · simpa [aqBoundaryOracle] using! hv2
  · simpa [aqBoundaryOracle] using! hv4
  · have hnsub : ¬ aqPeriodProgression 128 0 4 2 ⊆ aqPeriodProgression 128 0 4 4 := by
      intro hsub
      have hmem : (2 : Fin 128) ∈ aqPeriodProgression 128 0 4 2 := by
        simp [aqPeriodProgression, aqProgressionSet]
      have hnot : (2 : Fin 128) ∉ aqPeriodProgression 128 0 4 4 := by
        intro hx
        simp [aqPeriodProgression, aqProgressionSet] at hx
        obtain ⟨r, hr, he⟩ := hx
        omega
      exact hnot (hsub hmem)
    exact aqPeriodSeparation_pos hnsub
  · exact aqVerifiedCandidates_mem aqBoundaryOracle (by decide)
      (by simpa [aqBoundaryOracle] using! hv2)
  · exact aqVerifiedCandidates_mem aqBoundaryOracle (by decide)
      (by simpa [aqBoundaryOracle] using! hv4)

theorem clause8_endpoint : Clause8ZeroModeRuntime := by
  refine ⟨aqNextBernoulliErrorStreamZeroModeTransport, ?_⟩
  intro N k _ p hp hp1 d hd s M P θ hM hP hs hMN hθ
  have h := aqNextBernoulliErrorStreamZeroModeTransport N k p hp hp1 d hd s M P θ hM hP hs hMN hθ
  (try dsimp only at h)
  exact ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2.1, rfl, rfl⟩

end Qatlib.Concepts.AmpTransform.FullLayerCF
