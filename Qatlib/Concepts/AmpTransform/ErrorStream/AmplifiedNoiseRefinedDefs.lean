/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.ErrorStream.AmplifiedNoiseExecutionDefs
import Qatlib.Concepts.AmplitudeCore.InvFreeSampling.AmplifiedNoiseExecution
import Qatlib.Concepts.AmpTransform.ErrorStream.Lemma20RestrictedAmpl
import Qatlib.Concepts.AmpTransform.ErrorStream.Lemma20ProbabilityBoundAmpl
import Qatlib.Concepts.AmpTransform.FullLayerCF.WrapUnknownMRecovery
import Qatlib.Concepts.QftPreparation.LocalQft
import Qatlib.Concepts.AmpTransform.HaarPairTest.HaarGeneralWNAmpl
import Qatlib.Concepts.AmpTransform.NoiseEnvelope.ErrorExpectationMinimizedAtMinLAmpl
import Qatlib.Concepts.AmpTransform.ErrorStream.ErrorStreamGeometricSumZeroAmpl
import Qatlib.Concepts.AmpTransform.NoiseEnvelope.ExpectedNoiseEnvelopeBridgeAmpl
import Qatlib.Concepts.AmpTransform.LegendreWindow.LegendreFullBoundaryAmpl
import Qatlib.Concepts.AmpTransform.LegendreWindow.LegendreCompleteWindow
import Qatlib.Concepts.AmpTransform.FullLayerCF.FullLayerCFDenoiseUniquePAmpl
import Mathlib.NumberTheory.DiophantineApproximation.Basic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.HspRecovery.CfOrder
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.AmpTransform.ErrorStream
open Qatlib.Concepts.AmpTransform.FullLayerCF
open Qatlib.Concepts.AmpTransform.HaarPairTest
open Qatlib.Concepts.AmpTransform.LegendreWindow
open Qatlib.Concepts.AmpTransform.NoiseEnvelope
open Qatlib.Concepts.QftPreparation.LocalQFTImplementation

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Concepts.AmpTransform.ErrorStream

open Qatlib
open Matrix
open scoped Classical BigOperators

def aqLayerAtLeastPublic (M L : ℕ) : Prop := M ≤ L

noncomputable def aqRoundSaving (N M L : ℕ) : ℕ := aqPublicRoundCount N M - aqLayerRoundCount N M L

noncomputable def aqSuccessRatio (N s M P P' : ℕ) (p : ℝ) (obs : Finset (Fin N)) : ℝ :=
  if aqCandidateLikelihood N s M P' p obs = 0 then 0
  else aqCandidateLikelihood N s M P p obs / aqCandidateLikelihood N s M P' p obs

def aqSeparation (N s M P P' : ℕ) : ℕ := aqCandidateSeparation N s M P P'

def aqFairBitLedger (N k : ℕ) : ℕ := N * k

def aqVerifyCost (N t k : ℕ) : aqExecutionCost := aqFreshPassCost N t k

noncomputable def aqMinL (M N : ℝ) : ℝ :=
  -(M ^ 2) + Real.sqrt (M * (M - 1) * (M * (M - 1) + N))

noncomputable def aqEnvelope (N M L : ℝ) : ℝ :=
  (L + M ^ 2) / ((N - L - M) * (L + M))

noncomputable def aqM1Slice (N L : ℝ) : ℝ := 1 / (N - L - 1)

def aqM1Window (N : ℕ) (L : ℝ) : Prop := -1 < L ∧ L < (N : ℝ) - 1

noncomputable def aqIidAverage (N M L : ℕ) : ℝ :=
  ((L : ℝ) + (M : ℝ) ^ 2) / (((N : ℝ) - L - M) * ((L : ℝ) + M))

def aqLegendreTie (ξ : ℝ) (q : ℚ) : Prop :=
  q.den = 1 ∧ ξ = (q : ℝ) - 1 / 2

def clause23_endpoint : Prop :=
  (∀ (M N : ℕ) (hM : 2 ≤ M) (hN : 0 < N) (L : ℝ),
      -(M : ℝ) < L → L < (N : ℝ) - (M : ℝ) →
      aqEnvelope (N : ℝ) (M : ℝ) (aqMinL (M : ℝ) (N : ℝ)) ≤ aqEnvelope (N : ℝ) (M : ℝ) L)
  ∧ (∀ (N M L : ℕ) [NeZero N] (y : ZMod N) (c : ℂ),
      y ≠ 0 → 1 ≤ M → M + L < N → ‖c‖ ≤ (M : ℝ) →
      (((N : ℝ) ^ L)⁻¹ * (∑ ω : Fin L → ZMod N,
        ‖c + ∑ i, ZMod.stdAddChar (ω i * y)‖ ^ 2)) / ((M : ℝ) + L) ^ 2 *
        (Real.tan (aqAngle N (M + L))) ^ 2 * aqGain N (M + L) ≤
        aqEnvelope (N : ℝ) (M : ℝ) (L : ℝ))
  ∧ (∀ (N : ℕ) (hN : 1 < N) (L : ℝ), 0 ≤ L → L < (N : ℝ) - 1 →
      1 / ((N : ℝ) - 1) ≤ aqM1Slice (N : ℝ) L ∧
        (aqM1Slice (N : ℝ) L = 1 / ((N : ℝ) - 1) ↔ L = 0))
  ∧ (∀ (N : ℕ) (hN : 0 < N) (L : ℝ), aqM1Window N L →
      aqEnvelope (N : ℝ) 1 L = aqM1Slice (N : ℝ) L)
  ∧ (∀ (N : ℕ) (hN : 0 < N) {L₁ L₂ : ℝ},
      aqM1Window N L₁ → aqM1Window N L₂ → L₁ < L₂ →
      aqM1Slice (N : ℝ) L₁ < aqM1Slice (N : ℝ) L₂)
  ∧ (∀ (N : ℕ) (hN : 0 < N) (L : ℝ), aqM1Window N L →
      (1 : ℝ) / N < aqM1Slice (N : ℝ) L)
  ∧ (∀ (N : ℕ) (hN : 0 < N) (L : ℝ), aqM1Window N L →
      ∃ L', aqM1Window N L' ∧ aqM1Slice (N : ℝ) L' < aqM1Slice (N : ℝ) L)
  ∧ (¬ Qatlib.Concepts.AmpTransform.NoiseEnvelope.ExpectedNoiseEnvelopeBridgeOriginal)

def clause24_endpoint : Prop :=
  (∀ (n N s y : ℕ), N = 2 ^ n → y < N → y ≠ 0 →
      ‖(1 : ℂ) / (1 : ℂ) * amplifiedQFTOmega N ^ (s * y) +
        (1 : ℂ) / (1 : ℂ) * (∑ z ∈ (∅ : Finset ℕ), amplifiedQFTOmega N ^ (z * y))‖ ^ 2 = 1)
  ∧ (∀ (n N M L T s P y : ℕ) (A G : Finset ℕ),
      N = 2 ^ n → A = (Finset.range M).image (fun r => s + r * P) →
      A ⊆ Finset.range N → G ⊆ Finset.range N → A.card = M → G.card = L →
      Disjoint A G → T = M + L → 0 < T → y < N → y ≠ 0 → (P * y) % N = 0 →
      2 * N < 2 * T →
      ‖(M : ℂ) / (T : ℂ) * amplifiedQFTOmega N ^ (s * y) +
        (1 : ℂ) / (T : ℂ) * (∑ z ∈ G, amplifiedQFTOmega N ^ (z * y))‖ ^ 2 ≤ (1 : ℝ))

def aqIdentifiableProgression (N s M P : ℕ) : Prop :=
  0 < P ∧ s + (M - 1) * P < N

noncomputable def aqDisambiguateStep (N s M : ℕ) (p : ℝ) (obs : Finset (Fin N))
    (best : Option ℕ) (Q : ℕ) : Option ℕ :=
  match best with
  | none => some Q
  | some b =>
      if aqCandidateLikelihood N s M Q p obs > aqCandidateLikelihood N s M b p obs then
        some Q
      else some b

noncomputable def aqFreshFailureMass (N s M P : ℕ) (cands : Finset ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) : ℝ :=
  ∑ σ : Fin N → Bool, (bernoulliStreamLaw N p hp hp1).prob σ *
    (if ∃ P' ∈ cands \ {P}, aqCandidateConsistent N s M P' (aqFreshMarked N s M P σ)
      then 1 else 0)

def aqSameRunCost (N t k : ℕ) : aqExecutionCost :=
  { oracleAccesses := 3 + N * t
    classicalWork :=
      (cfDepth N + 1) + (cfDepth N + 1) * (cfDepth N + 2) / 2 + (N * k + t) }

def aqNextProgressionMember (N s M P : ℕ) (x : Fin N) : Bool :=
  decide (∃ r < M, x.val = s + r * P)

def aqNextFixedNoiseRecord (N s M P : ℕ) (G : Finset (Fin N)) : Fin N → Bool :=
  fun x => decide (aqNextProgressionMember N s M P x = true ∨ x ∈ G)

def aqNextVerify {N : ℕ} (f : Fin N → Bool) (s M q : ℕ) : Bool × ℕ :=
  if h : 0 < q ∧ s < N ∧ s + q < N ∧ s + (M - 1) * q < N then
    ([⟨s, h.2.1⟩, ⟨s + q, h.2.2.1⟩, ⟨s + (M - 1) * q, h.2.2.2⟩] : List (Fin N)).foldl
      (fun a x => (a.1 && f x, a.2 + 1)) (true, 0)
  else (false, 0)

def aqNextAttempt {N : ℕ} (f : Fin N → Bool) (s M B : ℕ) (y : Fin N) : Option ℕ × ℕ × ℕ × ℕ :=
  let d := cfRationalDecode B N y.val
  match d.1 with
  | none => (none, 0, d.2.1, d.2.2)
  | some c =>
    let v := aqNextVerify f s M c.2
    (if v.1 then some c.2 else none, v.2, d.2.1, d.2.2)

noncomputable def aqNextGoodWindow (N P : ℕ) : Finset (Fin N) := aqGoodWindow N P

def aqNextCyclicVerify (N : ℕ) (hN : 0 < N) (h : Fin N → Bool) (s M q : ℕ) : Bool × ℕ :=
  if 0 < q ∧ 2 ≤ M ∧ M * q ≤ N then
    ([⟨s % N, Nat.mod_lt _ hN⟩, ⟨(s + q) % N, Nat.mod_lt _ hN⟩,
      ⟨(s + (M - 1) * q) % N, Nat.mod_lt _ hN⟩] : List (Fin N)).foldl
      (fun a x => (a.1 && h x, a.2 + 1)) (true, 0)
  else (false, 0)

noncomputable def aqNextPublicDensityReadout (N : ℕ) (z : Fin (32 * N)) : ℕ :=
  Nat.floor ((N : ℝ) * aeEstimate (32 * N) z + 1 / 2)

noncomputable def aqNextBernoulliSiteLaw (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) : FinDist Bool where
  prob b := if b then p else 1 - p
  nonneg b := by
    cases b <;> simp [hp, sub_nonneg.mpr hp1]
  sum_one := by
    rw [Fintype.sum_bool]
    simp

noncomputable def aqNextBernoulliStreamLaw (N : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    FinDist (Fin N → Bool) where
  prob σ := (aqNextBernoulliSiteLaw p hp hp1).probOf σ
  nonneg σ := Finset.prod_nonneg fun i _ => (aqNextBernoulliSiteLaw p hp hp1).nonneg (σ i)
  sum_one := (aqNextBernoulliSiteLaw p hp hp1).sum_probOf N

noncomputable def aqNextBernoulliThreshold (k : ℕ) (p : ℝ) : ℕ := Nat.floor (p * (2 : ℝ) ^ k)

def aqNextBernoulliTapes (k a : ℕ) (ha : a ≤ 2 ^ k) : Finset (Reg k) :=
  (Finset.univ : Finset (Fin a)).image
    (fun x => (bitVecEquiv k).symm ⟨x.val, Nat.lt_of_lt_of_le x.isLt ha⟩)

def aqNextBernoulliDraw (k a : ℕ) (ha : a ≤ 2 ^ k) (tape : Reg k) : Bool :=
  decide (tape ∈ aqNextBernoulliTapes k a ha)

def aqNextBernoulliStream (N k a : ℕ) (ha : a ≤ 2 ^ k) (tapes : Fin N → Reg k) :
    Fin N → Bool :=
  fun i => aqNextBernoulliDraw k a ha (tapes i)

def aqNextBernoulliBitCost (N k : ℕ) : ℕ := N * k

def aqNextFreshPassCost (N t k : ℕ) : aqExecutionCost :=
  { oracleAccesses := N * t
    classicalWork := N * k + t }

noncomputable def aqNextEffectiveParameter (k a : ℕ) : ℝ := (a : ℝ) / (2 : ℝ) ^ k

noncomputable def aqNextEffectiveSiteProb (k a : ℕ) (ha : a ≤ 2 ^ k) : ℝ :=
  ∑ tape : Reg k, (uniformFairTapeLaw k).prob tape *
    (if aqNextBernoulliDraw k a ha tape = true then 1 else 0)

noncomputable def aqNextEffectiveStreamProb (N k a : ℕ) (ha : a ≤ 2 ^ k)
    (σ : Fin N → Bool) : ℝ :=
  ∑ tapes : Fin N → Reg k, (uniformFairTapeProductLaw k N).prob tapes *
    (if aqNextBernoulliStream N k a ha tapes = σ then 1 else 0)

def aqNextThresholdFits (k : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    aqNextBernoulliThreshold k p ≤ 2 ^ k := by
  apply Nat.cast_le.mpr
  have hfl : (aqNextBernoulliThreshold k p : ℝ) ≤ p * (2 : ℝ) ^ k :=
    Nat.floor_le (mul_nonneg hp (by positivity))
  have h1 : p * (2 : ℝ) ^ k ≤ (2 : ℝ) ^ k := by
    have hm := mul_le_mul_of_nonneg_right hp1 (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ k)
    simpa using! hm
  have h2 : (aqNextBernoulliThreshold k p : ℝ) ≤ (2 : ℝ) ^ k := hfl.trans h1
  have h3 : ((aqNextBernoulliThreshold k p : ℕ) : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by
    have hc : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by
      rw [Nat.cast_pow]
      norm_num
    rw [hc]
    exact h2
  exact Nat.cast_le.mp h3

def aqNextEffectiveIsBernoulli (k a : ℕ) (ha : a ≤ 2 ^ k) : Prop :=
  0 ≤ aqNextEffectiveParameter k a ∧ aqNextEffectiveParameter k a ≤ 1

def aqNextDyadicIsBernoulli (k a : ℕ) (ha : a ≤ 2 ^ k) : Prop :=
  0 ≤ (a : ℝ) / (2 : ℝ) ^ k ∧ (a : ℝ) / (2 : ℝ) ^ k ≤ 1

def clause26_endpoint : Prop :=
  (∀ (N : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (g : Fin N → Bool → ℝ),
      (∑ σ : Fin N → Bool, (bernoulliStreamLaw N p hp hp1).prob σ * ∏ i, g i (σ i))
        = ∏ i, ∑ b : Bool, (bernoulliSiteLaw p hp hp1).prob b * g i b)
  ∧ (∀ (N s M P : ℕ) (σ : Fin N → Bool),
      aqCandidateConsistent N s M P (aqFreshMarked N s M P σ))
  ∧ (∀ (N s M : ℕ) (cands : Finset ℕ) (obs : Finset (Fin N)),
      aqFreshCompatible N s M cands obs =
        cands.filter fun P => aqCandidateConsistent N s M P obs)
  ∧ (∀ (N s M P : ℕ) (cands : Finset ℕ) (P' : ℕ) (hP' : P' ∈ cands)
      (σ : Fin N → Bool),
      P' ∈ aqFreshCompatible N s M cands (aqFreshMarked N s M P σ) →
        aqCandidateConsistent N s M P' (aqFreshMarked N s M P σ))
  ∧ (∀ (N s M P : ℕ) (cands : Finset ℕ) (P' : ℕ) (hP' : P' ∈ cands)
      (σ : Fin N → Bool),
      ¬ aqCandidateConsistent N s M P' (aqFreshMarked N s M P σ) →
        P' ∉ aqFreshCompatible N s M cands (aqFreshMarked N s M P σ))
  ∧ (∀ (N s M P P' : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1),
      (∑ σ : Fin N → Bool, (bernoulliStreamLaw N p hp hp1).prob σ *
        (if aqCandidateConsistent N s M P' (aqFreshMarked N s M P σ) then 1 else 0))
        = p ^ aqCandidateSeparation N s M P P')
  ∧ (∀ (N s M P : ℕ) (p : ℝ) (cands : Finset ℕ) (hP : P ∈ cands) (σ : Fin N → Bool),
      (∀ P' ∈ cands \ {P},
        ¬ aqCandidateConsistent N s M P' (aqFreshMarked N s M P σ)) →
      aqFreshCompatible N s M cands (aqFreshMarked N s M P σ) = {P} ∧
        aqFreshDisambiguate N s M cands p (aqFreshMarked N s M P σ) = some P)
  ∧ (∀ (N s M P : ℕ) (cands : Finset ℕ) (hP : P ∈ cands) (σ : Fin N → Bool),
      aqFreshCompatible N s M cands (aqFreshMarked N s M P σ) ≠ {P} →
      ∃ P' ∈ cands \ {P}, aqCandidateConsistent N s M P' (aqFreshMarked N s M P σ))
  ∧ (∀ (N s M P : ℕ) (p pmax : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ pmax)
      (hmax : pmax < 1) (cands : Finset ℕ) (hP : P ∈ cands),
      ∀ P' ∈ cands \ {P},
        (∑ σ : Fin N → Bool, (bernoulliStreamLaw N p hp (le_trans hp1 hmax.le)).prob σ *
          (if aqCandidateConsistent N s M P' (aqFreshMarked N s M P σ) then 1 else 0))
          ≤ pmax ^ aqCandidateSeparation N s M P P')
  ∧ (∀ (N s M P : ℕ) (cands : Finset ℕ) (p pmax : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ pmax)
      (hmax : pmax < 1),
      aqFreshFailureMass N s M P cands p hp (le_trans hp1 hmax.le) ≤
        ∑ P' ∈ cands \ {P}, pmax ^ (aqCandidateSeparation N s M P P'))
  ∧ (∀ (N s M : ℕ) (cands : Finset ℕ) (p : ℝ) (obs : Finset (Fin N)) (Q : ℕ),
      aqFreshDisambiguate N s M cands p obs = some Q →
        Q ∈ aqFreshCompatible N s M cands obs)
  ∧ (∃ (N s M P P' : ℕ) (obs : Finset (Fin N)),
      P ≠ P' ∧ aqCandidateConsistent N s M P obs ∧ aqCandidateConsistent N s M P' obs)
  ∧ (∀ (N s M P P' : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hp1' : p < 1)
      (hsep : 0 < aqCandidateSeparation N s M P P'),
      0 < 1 - p ^ (aqCandidateSeparation N s M P P'))
  ∧ (∀ (N t k : ℕ),
      aqSameRunCost N t k =
        ({ oracleAccesses := 3
           classicalWork :=
             (cfDepth N + 1) + (cfDepth N + 1) * (cfDepth N + 2) / 2 } :
          aqExecutionCost).add
          (aqFreshPassCost N t k))
  ∧ (∀ (N s M P B : ℕ) (G : Finset (Fin N)) (y : Fin N)
      (hM : 2 ≤ M) (hP : 2 ≤ P) (hb : s + (M - 1) * P < N) (hPB : P ≤ B)
      (hsepB : 2 * B ^ 2 < N) (hy : y ∈ aqNextGoodWindow N P),
      (aqNextAttempt (aqNextFixedNoiseRecord N s M P G) s M B y).1 = some P)
  ∧ (∀ (N s M P B : ℕ) (G : Finset (Fin N)) (y : Fin N)
      (hM : 2 ≤ M) (hP : 2 ≤ P) (hb : s + (M - 1) * P < N) (hPB : P ≤ B)
      (hsepB : 2 * B ^ 2 < N) (q : ℕ),
      (aqNextAttempt (aqNextFixedNoiseRecord N s M P G) s M B y).1 = some q →
        (aqNextVerify (aqNextFixedNoiseRecord N s M P G) s M q).1 = true)
  ∧ (∀ (N s M P B : ℕ) (G : Finset (Fin N)) (y : Fin N),
      (aqNextAttempt (aqNextFixedNoiseRecord N s M P G) s M B y).2.1 ≤ 3 ∧
        (aqNextAttempt (aqNextFixedNoiseRecord N s M P G) s M B y).2.2.1 ≤ cfDepth N + 1 ∧
        (aqNextAttempt (aqNextFixedNoiseRecord N s M P G) s M B y).2.2.2 =
          (cfDepth N + 1) * (cfDepth N + 2) / 2)
  ∧ (∃ (N s M P P' : ℕ) (G : Finset (Fin N)),
      P ≠ P' ∧
        (∀ x : Fin N, aqNextFixedNoiseRecord N s M P G x = true ↔
          aqNextFixedNoiseRecord N s M P' G x = true) ∧
        (aqNextVerify (aqNextFixedNoiseRecord N s M P G) s M P).1 = true ∧
        (aqNextVerify (aqNextFixedNoiseRecord N s M P' G) s M P').1 = true)
  ∧ (∀ (k a : ℕ) (ha : a ≤ 2 ^ k),
      aqNextEffectiveSiteProb k a ha = aqNextEffectiveParameter k a)
  ∧ (∀ (k a : ℕ) (ha : a ≤ 2 ^ k),
      0 ≤ aqNextEffectiveParameter k a ∧ aqNextEffectiveParameter k a ≤ 1)
  ∧ (∀ (N k a : ℕ) (ha : a ≤ 2 ^ k) (σ : Fin N → Bool),
      ∃ h : 0 ≤ aqNextEffectiveParameter k a ∧ aqNextEffectiveParameter k a ≤ 1,
        aqNextEffectiveStreamProb N k a ha σ
          = (aqNextBernoulliStreamLaw N (aqNextEffectiveParameter k a) h.1 h.2).prob σ)
  ∧ (∀ (k : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1),
      aqNextBernoulliThreshold k p ≤ 2 ^ k)
  ∧ (∀ (k : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1),
      (aqNextBernoulliThreshold k p : ℝ) / (2 : ℝ) ^ k ≤ p ∧
        p < (aqNextBernoulliThreshold k p : ℝ) / (2 : ℝ) ^ k + 1 / (2 : ℝ) ^ k)
  ∧ (∀ (k : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1),
      Filter.Tendsto (fun k => (aqNextBernoulliThreshold k p : ℝ) / (2 : ℝ) ^ k)
        Filter.atTop (nhds p))
  ∧ (∀ (N : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (σ : Fin N → Bool),
      Filter.Tendsto (fun k => aqNextEffectiveStreamProb N k (aqNextBernoulliThreshold k p)
          (aqNextThresholdFits k p hp hp1) σ)
        Filter.atTop (nhds ((aqNextBernoulliStreamLaw N p hp hp1).prob σ)))
  ∧ (∀ (k a : ℕ) (ha : a ≤ 2 ^ k),
      aqNextBernoulliThreshold k ((a : ℝ) / (2 : ℝ) ^ k) = a)
  ∧ (∀ (N k a : ℕ) (ha : a ≤ 2 ^ k) (σ : Fin N → Bool),
      ∃ h : 0 ≤ (a : ℝ) / (2 : ℝ) ^ k ∧ (a : ℝ) / (2 : ℝ) ^ k ≤ 1,
        aqNextEffectiveStreamProb N k a ha σ
          = (aqNextBernoulliStreamLaw N ((a : ℝ) / (2 : ℝ) ^ k) h.1 h.2).prob σ)
  ∧ (∀ (N t k : ℕ),
      aqNextBernoulliBitCost N k + t = (aqNextFreshPassCost N t k).classicalWork)

def clause27_endpoint : Prop :=
  (∀ (N s M P P' : ℕ) (p : ℝ) (obs : Finset (Fin N)),
      aqSuccessRatio N s M P P' p obs =
        (if aqCandidateLikelihood N s M P' p obs = 0 then 0
         else aqCandidateLikelihood N s M P p obs / aqCandidateLikelihood N s M P' p obs))
  ∧ (∀ (N s M P P' : ℕ) (p : ℝ) (obs : Finset (Fin N)),
      aqCandidateLikelihood N s M P' p obs = 0 → aqSuccessRatio N s M P P' p obs = 0)
  ∧ (∀ (N s M P P' : ℕ) (p : ℝ) (obs : Finset (Fin N)) (hp : 0 ≤ p) (hp1 : p ≤ 1),
      0 ≤ aqSuccessRatio N s M P P' p obs)

def clause28_endpoint : Prop :=
  (∀ (N M : ℕ), 0 < N → 0 < M → 2 * (M + 1) ≤ N → aqAngle N M ≤ aqAngle N (M + 1))
  ∧ (∀ (N M : ℕ), 0 < N → 0 < M → 2 * (M + 1) ≤ N →
      aqPublicRoundCount N M ≥ aqLayerRoundCount N M (M + 1))
  ∧ (∀ (N M L : ℕ), 0 < N → 0 < M → M ≤ L → 2 * L ≤ N →
      aqLayerRoundCount N M L ≤ aqPublicRoundCount N M ∧
        aqRoundSaving N M L + aqLayerRoundCount N M L = aqPublicRoundCount N M)

def clause29_endpoint : Prop :=
  (∀ (N : ℕ) (hN : 0 < N) (h : Fin N → Bool) (s M P : ℕ) (G : Finset (Fin N))
      (hM : 2 ≤ M) (hP : 0 < P) (hMP : M * P ≤ N)
      (hmark : ∀ x, h x = decide (x ∈ ((Finset.range M).image (fun r : ℕ =>
        (⟨(s + r * P) % N, Nat.mod_lt _ hN⟩ : Fin N))) ∪ G)),
      aqCyclicVerify N hN h s M P = (true, 3) ∧
        (aqCyclicVerify N hN h s M P).2 ≤ 3 ∧
        QueryCount (countedAECircuit (32 * N) (QFTMatrix N) (⟨0, hN⟩ : Fin N)) = 32 * N - 1 ∧
        GateCount (countedAECircuit (32 * N) (QFTMatrix N) (⟨0, hN⟩ : Fin N))
          = 5 * (32 * N - 1) + 3)
  ∧ (∀ (N : ℕ) (hN : 0 < N) (h : Fin N → Bool) (s M P : ℕ) (G : Finset (Fin N))
      (hM : 2 ≤ M) (hP : 0 < P) (hMP : M * P ≤ N)
      (hmark : ∀ x, h x = decide (x ∈ ((Finset.range M).image (fun r : ℕ =>
        (⟨(s + r * P) % N, Nat.mod_lt _ hN⟩ : Fin N))) ∪ G)),
      aqNextCyclicVerify N hN h s M P = (true, 3) ∧
        (aqNextCyclicVerify N hN h s M P).2 ≤ 3)
  ∧ (∀ (N : ℕ) (hN : 0 < N) (C : Finset (Fin N)),
      8 / Real.pi ^ 2 ≤
        ∑ z ∈ Finset.univ.filter (fun z : Fin (32 * N) => aqNextPublicDensityReadout N z = C.card),
          (aeLaw (32 * N) (QFTMatrix N) ⟨0, hN⟩ C (qftMatrix_unitary hN)
            (by omega)).prob z ∧
        QueryCount (countedAECircuit (32 * N) (QFTMatrix N) (⟨0, hN⟩ : Fin N)) = 32 * N - 1 ∧
        GateCount (countedAECircuit (32 * N) (QFTMatrix N) (⟨0, hN⟩ : Fin N))
          = 5 * (32 * N - 1) + 3)

def clause30_endpoint : Prop :=
  (∀ (n : ℕ), 0 < n →
      haarDyadicPreparation n ∈ Matrix.unitaryGroup (Reg (n - 1) × Bool) ℂ ∧
        haarDyadicPreparation n *ᵥ Ket (haarDyadicSeed n) = Uniform (Reg (n - 1) × Bool))
  ∧ (∀ (n : ℕ), 0 < n → ∀ j : ℕ,
      preparedDataQueries (aqHaarPairWord (haarDyadicPreparation n) (haarDyadicSeed n) j) = j ∧
        preparedInputQueries (aqHaarPairWord (haarDyadicPreparation n) (haarDyadicSeed n) j) = 1 ∧
        preparedFixedGates (aqHaarPairWord (haarDyadicPreparation n) (haarDyadicSeed n) j) = j + 2)
  ∧ (∀ (N M : ℕ), 0 < N → 0 < M → 2 * M ≤ N →
      aqRounds N M = Nat.floor (Real.pi / (4 * aqAngle N M)) ∧
        (Real.sin (2 * (aqRounds N M : ℝ) * aqAngle N M)) ^ 2 ≤ 1)

def clause31_endpoint : Prop :=
  (∀ (n : ℕ),
      GateCount (localProgramCircuit (localQFT n)) = n + n * (n - 1) / 2 + n / 2 ∧
        QueryCount (localProgramCircuit (localQFT n)) = 0)
  ∧ (∀ (N t k : ℕ),
      aqFairBitLedger N k = N * k ∧
        (aqVerifyCost N t k).oracleAccesses = N * t ∧
        (aqVerifyCost N t k).classicalWork = N * k + t)
  ∧ (∀ (k : ℕ),
      ¬ ∃ f : Fin (2 ^ k) → Fin 3, ∀ x y : Fin 3,
        (Finset.univ.filter (fun b => f b = x)).card =
          (Finset.univ.filter (fun b => f b = y)).card)

def clause32_endpoint : Prop :=
  (∀ (M N : ℕ), 2 ≤ M → 0 < N → ∀ L : ℝ, -(M : ℝ) < L → L < (N : ℝ) - (M : ℝ) →
      aqEnvelope (N : ℝ) (M : ℝ) (aqMinL (M : ℝ) (N : ℝ)) ≤ aqEnvelope (N : ℝ) (M : ℝ) L)
  ∧ (∀ (N y : ℕ), 0 < N → y % N ≠ 0 → ∑ z ∈ Finset.range N, aqPhase N z y = 0)

end Qatlib.Concepts.AmpTransform.ErrorStream
