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

/-!
# Refined error-stream recovery statements

This module defines likelihood ratios, noise envelopes, verification routines, and finite-tape
Bernoulli samplers used by the refined recovery statements. The propositions `clause23_endpoint`
through `clause32_endpoint` collect the relevant analytic bounds, recovery conditions, and
resource identities.

The finite-tape definitions retain the realized dyadic parameter explicitly, while the envelope
statements distinguish the single-signal boundary from the higher-cardinality minimization
problem.

The error-stream setting is developed in [Cornwell2014].

## Main statements

* `aqEnvelope` and `aqMinL`: the real noise envelope and its minimizer expression.
* `aqNextAttempt`: bounded decoding with three-site verification and cost counters.
* `clause26_endpoint`: fresh-observation and effective Bernoulli transport statements.
* `clause31_endpoint`: QFT, verification, and fair-bit resource statements.

## References

* [Cornwell, 2014][Cornwell2014]
-/

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

/-- The condition `M ≤ L` comparing the public and layer size parameters. -/
def aqLayerAtLeastPublic (M L : ℕ) : Prop := M ≤ L

/-- The natural-number difference between the public and layer-dependent amplification round
counts. -/
noncomputable def aqRoundSaving (N M L : ℕ) : ℕ := aqPublicRoundCount N M - aqLayerRoundCount N M L

/-- The ratio of the likelihoods of candidates `P` and `P'`, defined to be zero when the
denominator likelihood vanishes. -/
noncomputable def aqSuccessRatio (N s M P P' : ℕ) (p : ℝ) (obs : Finset (Fin N)) : ℝ :=
  if aqCandidateLikelihood N s M P' p obs = 0 then 0
  else aqCandidateLikelihood N s M P p obs / aqCandidateLikelihood N s M P' p obs

/-- The number of sites separating the candidate progression from the planted progression, as
given by `aqCandidateSeparation`. -/
def aqSeparation (N s M P P' : ℕ) : ℕ := aqCandidateSeparation N s M P P'

/-- The fair-bit ledger `N * k` for `N` tapes of length `k`. -/
def aqFairBitLedger (N k : ℕ) : ℕ := N * k

/-- The execution-cost record `aqFreshPassCost N t k` for fresh verification. -/
def aqVerifyCost (N t k : ℕ) : aqExecutionCost := aqFreshPassCost N t k

/-- The real envelope minimizer expression `-M ^ 2 + sqrt (M * (M - 1) * (M * (M - 1) + N))`. -/
noncomputable def aqMinL (M N : ℝ) : ℝ :=
  -(M ^ 2) + Real.sqrt (M * (M - 1) * (M * (M - 1) + N))

/-- The rational noise-envelope expression `(L + M ^ 2) / ((N - L - M) * (L + M))`. -/
noncomputable def aqEnvelope (N M L : ℝ) : ℝ :=
  (L + M ^ 2) / ((N - L - M) * (L + M))

/-- The single-signal envelope slice `1 / (N - L - 1)`. -/
noncomputable def aqM1Slice (N L : ℝ) : ℝ := 1 / (N - L - 1)

/-- The open interval condition `-1 < L < N - 1` for the single-signal envelope slice. -/
def aqM1Window (N : ℕ) (L : ℝ) : Prop := -1 < L ∧ L < (N : ℝ) - 1

/-- The rational expression `(L + M ^ 2) / ((N - L - M) * (L + M))` with natural size parameters
interpreted as reals. -/
noncomputable def aqIidAverage (N M L : ℕ) : ℝ :=
  ((L : ℝ) + (M : ℝ) ^ 2) / (((N : ℝ) - L - M) * ((L : ℝ) + M))

/-- The half-integer boundary condition that `q` has denominator one and `ξ = q - 1 / 2`. -/
def aqLegendreTie (ξ : ℝ) (q : ℚ) : Prop :=
  q.den = 1 ∧ ξ = (q : ℝ) - 1 / 2

/-- The conjunction of envelope minimization, an independent-noise upper bound, the
single-signal boundary properties, and the negation of
`ExpectedNoiseEnvelopeBridgeOriginal`. -/
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

/-- The conjunction of the one-signal empty-noise Fourier identity and the normalized resonant
signal-plus-noise bound under the stated cardinality and register assumptions. -/
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

/-- The condition that a progression has positive period and its last site lies within the
register. -/
def aqIdentifiableProgression (N s M P : ℕ) : Prop :=
  0 < P ∧ s + (M - 1) * P < N

/-- Update the current candidate to `Q` if no candidate is stored or `Q` has strictly larger
likelihood, retaining the incumbent on ties. -/
noncomputable def aqDisambiguateStep (N s M : ℕ) (p : ℝ) (obs : Finset (Fin N))
    (best : Option ℕ) (Q : ℕ) : Option ℕ :=
  match best with
  | none => some Q
  | some b =>
      if aqCandidateLikelihood N s M Q p obs > aqCandidateLikelihood N s M b p obs then
        some Q
      else some b

/-- The Bernoulli probability that at least one candidate other than `P` remains consistent with
a fresh protected observation. -/
noncomputable def aqFreshFailureMass (N s M P : ℕ) (cands : Finset ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) : ℝ :=
  ∑ σ : Fin N → Bool, (bernoulliStreamLaw N p hp hp1).prob σ *
    (if ∃ P' ∈ cands \ {P}, aqCandidateConsistent N s M P' (aqFreshMarked N s M P σ)
      then 1 else 0)

/-- The execution-cost record charging three source checks, fresh oracle accesses,
continued-fraction work, and the fresh-pass classical ledger. -/
def aqSameRunCost (N t k : ℕ) : aqExecutionCost :=
  { oracleAccesses := 3 + N * t
    classicalWork :=
      (cfDepth N + 1) + (cfDepth N + 1) * (cfDepth N + 2) / 2 + (N * k + t) }

/-- Decide whether a register location equals `s + r * P` for some `r < M`. -/
def aqNextProgressionMember (N s M P : ℕ) (x : Fin N) : Bool :=
  decide (∃ r < M, x.val = s + r * P)

/-- The Boolean oracle marking the union of the finite progression and the fixed noise set `G`. -/
def aqNextFixedNoiseRecord (N s M P : ℕ) (G : Finset (Fin N)) : Fin N → Bool :=
  fun x => decide (aqNextProgressionMember N s M P x = true ∨ x ∈ G)

/-- For a positive candidate with all three locations in bounds, check `s`, `s + q`, and `s + (M
- 1) * q`, returning acceptance and the number of oracle queries. -/
def aqNextVerify {N : ℕ} (f : Fin N → Bool) (s M q : ℕ) : Bool × ℕ :=
  if h : 0 < q ∧ s < N ∧ s + q < N ∧ s + (M - 1) * q < N then
    ([⟨s, h.2.1⟩, ⟨s + q, h.2.2.1⟩, ⟨s + (M - 1) * q, h.2.2.2⟩] : List (Fin N)).foldl
      (fun a x => (a.1 && f x, a.2 + 1)) (true, 0)
  else (false, 0)

/-- Decode a bounded rational candidate from a Fourier label, verify its denominator, and return
the optional period with query and continued-fraction costs. -/
def aqNextAttempt {N : ℕ} (f : Fin N → Bool) (s M B : ℕ) (y : Fin N) : Option ℕ × ℕ × ℕ × ℕ :=
  let d := cfRationalDecode B N y.val
  match d.1 with
  | none => (none, 0, d.2.1, d.2.2)
  | some c =>
    let v := aqNextVerify f s M c.2
    (if v.1 then some c.2 else none, v.2, d.2.1, d.2.2)

/-- The rational recovery window `aqGoodWindow N P` for the period `P`. -/
noncomputable def aqNextGoodWindow (N P : ℕ) : Finset (Fin N) := aqGoodWindow N P

/-- Check three sites modulo `N` when the candidate is positive, has length at least two, and
satisfies `M * q ≤ N`. -/
def aqNextCyclicVerify (N : ℕ) (hN : 0 < N) (h : Fin N → Bool) (s M q : ℕ) : Bool × ℕ :=
  if 0 < q ∧ 2 ≤ M ∧ M * q ≤ N then
    ([⟨s % N, Nat.mod_lt _ hN⟩, ⟨(s + q) % N, Nat.mod_lt _ hN⟩,
      ⟨(s + (M - 1) * q) % N, Nat.mod_lt _ hN⟩] : List (Fin N)).foldl
      (fun a x => (a.1 && h x, a.2 + 1)) (true, 0)
  else (false, 0)

/-- Round `N * aeEstimate (32 * N) z` to the nearest natural number using an added half before
taking the floor. -/
noncomputable def aqNextPublicDensityReadout (N : ℕ) (z : Fin (32 * N)) : ℕ :=
  Nat.floor ((N : ℝ) * aeEstimate (32 * N) z + 1 / 2)

/-- The Boolean Bernoulli distribution assigning probability `p` to true and `1 - p` to false. -/
noncomputable def aqNextBernoulliSiteLaw (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) : FinDist Bool where
  prob b := if b then p else 1 - p
  nonneg b := by
    cases b <;> simp [hp, sub_nonneg.mpr hp1]
  sum_one := by
    rw [Fintype.sum_bool]
    simp

/-- The product distribution of `N` independent Boolean Bernoulli sites. -/
noncomputable def aqNextBernoulliStreamLaw (N : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    FinDist (Fin N → Bool) where
  prob σ := (aqNextBernoulliSiteLaw p hp hp1).probOf σ
  nonneg σ := Finset.prod_nonneg fun i _ => (aqNextBernoulliSiteLaw p hp hp1).nonneg (σ i)
  sum_one := (aqNextBernoulliSiteLaw p hp hp1).sum_probOf N

/-- The integer threshold obtained by flooring `p * 2 ^ k`. -/
noncomputable def aqNextBernoulliThreshold (k : ℕ) (p : ℝ) : ℕ := Nat.floor (p * (2 : ℝ) ^ k)

/-- The set of `k`-bit tapes whose encoded integers lie below the fitting threshold `a`. -/
def aqNextBernoulliTapes (k a : ℕ) (ha : a ≤ 2 ^ k) : Finset (Reg k) :=
  (Finset.univ : Finset (Fin a)).image
    (fun x => (bitVecEquiv k).symm ⟨x.val, Nat.lt_of_lt_of_le x.isLt ha⟩)

/-- Return true exactly when the tape belongs to `aqNextBernoulliTapes k a ha`. -/
def aqNextBernoulliDraw (k a : ℕ) (ha : a ≤ 2 ^ k) (tape : Reg k) : Bool :=
  decide (tape ∈ aqNextBernoulliTapes k a ha)

/-- Apply the finite-tape Bernoulli draw to the tape at each register location. -/
def aqNextBernoulliStream (N k a : ℕ) (ha : a ≤ 2 ^ k) (tapes : Fin N → Reg k) :
    Fin N → Bool :=
  fun i => aqNextBernoulliDraw k a ha (tapes i)

/-- The bit ledger `N * k` for a register of `N` tapes of length `k`. -/
def aqNextBernoulliBitCost (N k : ℕ) : ℕ := N * k

/-- The fresh-pass cost record with `N * t` oracle accesses and classical work `N * k + t`. -/
def aqNextFreshPassCost (N t k : ℕ) : aqExecutionCost :=
  { oracleAccesses := N * t
    classicalWork := N * k + t }

/-- The dyadic Bernoulli parameter `a / 2 ^ k` associated with threshold `a`. -/
noncomputable def aqNextEffectiveParameter (k a : ℕ) : ℝ := (a : ℝ) / (2 : ℝ) ^ k

/-- The probability that the threshold draw is true under a uniform fair `k`-bit tape. -/
noncomputable def aqNextEffectiveSiteProb (k a : ℕ) (ha : a ≤ 2 ^ k) : ℝ :=
  ∑ tape : Reg k, (uniformFairTapeLaw k).prob tape *
    (if aqNextBernoulliDraw k a ha tape = true then 1 else 0)

/-- The probability that independent uniform fair tapes produce the specified Boolean stream. -/
noncomputable def aqNextEffectiveStreamProb (N k a : ℕ) (ha : a ≤ 2 ^ k)
    (σ : Fin N → Bool) : ℝ :=
  ∑ tapes : Fin N → Reg k, (uniformFairTapeProductLaw k N).prob tapes *
    (if aqNextBernoulliStream N k a ha tapes = σ then 1 else 0)

/-- For `0 ≤ p ≤ 1`, the floored threshold is at most `2 ^ k`. -/
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

/-- The condition that the effective threshold parameter lies between zero and one. -/
def aqNextEffectiveIsBernoulli (k a : ℕ) (ha : a ≤ 2 ^ k) : Prop :=
  0 ≤ aqNextEffectiveParameter k a ∧ aqNextEffectiveParameter k a ≤ 1

/-- The condition that the dyadic ratio `a / 2 ^ k` lies between zero and one. -/
def aqNextDyadicIsBernoulli (k a : ℕ) (ha : a ≤ 2 ^ k) : Prop :=
  0 ≤ (a : ℝ) / (2 : ℝ) ^ k ∧ (a : ℝ) / (2 : ℝ) ^ k ≤ 1

/-- The conjunction of fresh-observation consistency and recovery bounds, fixed-noise candidate
guarantees, execution costs, and exact and limiting finite-tape Bernoulli identities. -/
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

/-- The likelihood-ratio formula, its zero-denominator case, and nonnegativity for Bernoulli
parameters. -/
def clause27_endpoint : Prop :=
  (∀ (N s M P P' : ℕ) (p : ℝ) (obs : Finset (Fin N)),
      aqSuccessRatio N s M P P' p obs =
        (if aqCandidateLikelihood N s M P' p obs = 0 then 0
         else aqCandidateLikelihood N s M P p obs / aqCandidateLikelihood N s M P' p obs))
  ∧ (∀ (N s M P P' : ℕ) (p : ℝ) (obs : Finset (Fin N)),
      aqCandidateLikelihood N s M P' p obs = 0 → aqSuccessRatio N s M P P' p obs = 0)
  ∧ (∀ (N s M P P' : ℕ) (p : ℝ) (obs : Finset (Fin N)) (hp : 0 ≤ p) (hp1 : p ≤ 1),
      0 ≤ aqSuccessRatio N s M P P' p obs)

/-- The monotonicity and round-count comparisons for public and layer-dependent amplification,
including the round-saving identity. -/
def clause28_endpoint : Prop :=
  (∀ (N M : ℕ), 0 < N → 0 < M → 2 * (M + 1) ≤ N → aqAngle N M ≤ aqAngle N (M + 1))
  ∧ (∀ (N M : ℕ), 0 < N → 0 < M → 2 * (M + 1) ≤ N →
      aqPublicRoundCount N M ≥ aqLayerRoundCount N M (M + 1))
  ∧ (∀ (N M L : ℕ), 0 < N → 0 < M → M ≤ L → 2 * L ≤ N →
      aqLayerRoundCount N M L ≤ aqPublicRoundCount N M ∧
        aqRoundSaving N M L + aqLayerRoundCount N M L = aqPublicRoundCount N M)

/-- The cyclic three-query verification guarantees and public density-readout success bound,
with the stated amplitude-estimation circuit query and gate counts. -/
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

/-- The dyadic Haar preparation and prepared-word cost identities, together with the
amplification round formula and trigonometric gain bound. -/
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

/-- The local QFT cost formula, fair-bit and verification ledgers, and impossibility of mapping
a fixed number of fair bits uniformly to three labels. -/
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

/-- The conjunction of noise-envelope minimization and vanishing of the complete Fourier phase
sum at nonzero frequency modulo `N`. -/
def clause32_endpoint : Prop :=
  (∀ (M N : ℕ), 2 ≤ M → 0 < N → ∀ L : ℝ, -(M : ℝ) < L → L < (N : ℝ) - (M : ℝ) →
      aqEnvelope (N : ℝ) (M : ℝ) (aqMinL (M : ℝ) (N : ℝ)) ≤ aqEnvelope (N : ℝ) (M : ℝ) L)
  ∧ (∀ (N y : ℕ), 0 < N → y % N ≠ 0 → ∑ z ∈ Finset.range N, aqPhase N z y = 0)

end Qatlib.Concepts.AmpTransform.ErrorStream
