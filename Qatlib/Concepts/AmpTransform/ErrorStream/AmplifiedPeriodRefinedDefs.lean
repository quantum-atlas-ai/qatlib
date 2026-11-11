/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.ErrorStream.AmplifiedNoiseRefinedDefs
import Qatlib.Concepts.AmpTransform.ErrorStream.BernoulliZeroModeTransportAmpl
import Qatlib.Concepts.AmpTransform.SuccessRatio.AmplifiedPeriodRecovery
import Qatlib.Concepts.AmpTransform.NoiseEnvelope.AmplifiedProgression

/-!
# Refined period-recovery interfaces and resource ledgers

This module defines source-verified candidates and two-stage fresh-observation recovery,
together with progression separation and query ledgers. `Clause4TwoStageRecovery` through
`Clause8ZeroModeRuntime` state recovery, layer-comparison, degeneracy, ambiguity, and zero-mode
resource requirements.

`aqBoundaryOracle` gives the concrete fixed-noise oracle used to express ambiguity between two
different verified periods.

The error-stream setting is developed in [Cornwell2014].

## Main statements

* `aqTwoStageRecover`: fresh disambiguation of source-verified candidates.
* `Clause5LayerStepDistinction`: cyclic verification and layer-dependent costs.
* `Clause7FixedNoiseBoundary`: a concrete two-period ambiguity statement.
* `Clause8ZeroModeRuntime`: zero-mode transport with resource ledgers.

## References

* [Cornwell, 2014][Cornwell2014]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.QftPreparation.LocalQft
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.AmpTransform.ErrorStream
open Qatlib.Concepts.AmpTransform.FullLayerCF
open Qatlib.Concepts.AmpTransform.HaarPairTest
open Qatlib.Concepts.AmpTransform.NoiseEnvelope
open Qatlib.Concepts.AmpTransform.SuccessRatio
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.QftPreparation.LocalQFTImplementation

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Qatlib.Concepts.AmpTransform.ErrorStream

open Qatlib
open scoped Classical BigOperators ENNReal

/-- The candidate periods below `N` accepted by the source-oracle verifier. -/
def aqVerifiedCandidates (N : ℕ) (h : Fin N → Bool) (s M : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun P : ℕ => (aqVerify h s M P).1 = true)

/-- Filter the source-verified candidates by consistency with a fresh observation. -/
def aqTwoStageCompatible (N : ℕ) (h : Fin N → Bool) (s M : ℕ)
    (obs : Finset (Fin N)) : Finset ℕ :=
  aqFreshCompatible N s M (aqVerifiedCandidates N h s M) obs

/-- Apply likelihood-based fresh disambiguation to the source-verified candidate set. -/
noncomputable def aqTwoStageRecover (N : ℕ) (h : Fin N → Bool) (s M : ℕ) (p : ℝ)
    (obs : Finset (Fin N)) : Option ℕ :=
  aqFreshDisambiguate N s M (aqVerifiedCandidates N h s M) p obs

/-- The candidate-progression separation used for period identification. -/
def aqPeriodSeparation (N s M P P' : ℕ) : ℕ :=
  aqCandidateSeparation N s M P P'

/-- The finite register progression `aqProgressionSet N s M P`. -/
def aqPeriodProgression (N s M P : ℕ) : Finset (Fin N) :=
  aqProgressionSet N s M P

/-- The natural-number layer count `N - M + 1`. -/
def aqZeroModeLayers (N M : ℕ) : ℕ := N - M + 1

/-- The product of the zero-mode layer count and the per-layer gate ledger `3 * k + 2`. -/
def aqZeroModeRuntime (N M k : ℕ) : ℕ :=
  aqZeroModeLayers N M * (3 * k + 2)

/-- The density-counting query ledger `32 * N - 1`. -/
def aqNextDensityCountingQueries (N : ℕ) : ℕ := 32 * N - 1

/-- The sum of the density-counting ledger and the public amplification round count. -/
def aqNextPublicRecoveryQueries (N M : ℕ) : ℕ :=
  aqNextDensityCountingQueries N + aqPublicRoundCount N M

/-- The sum of the density-counting ledger and the layer-dependent amplification round count. -/
def aqNextLayerRecoveryQueries (N M L : ℕ) : ℕ :=
  aqNextDensityCountingQueries N + aqLayerRoundCount N M L

/-- The natural-number difference between public and layer-dependent recovery query ledgers. -/
def aqNextRecoveryQuerySaving (N M L : ℕ) : ℕ :=
  aqNextPublicRecoveryQueries N M - aqNextLayerRecoveryQueries N M L

/-- The conjunction of verified-candidate inclusion, positivity of separation for noncontained
progressions, exact fresh-consistency probability, and recovery after refuting false
candidates. -/
def Clause4TwoStageRecovery : Prop :=
  (∀ (N s M : ℕ) (h : Fin N → Bool) (P : ℕ) (hP : P < N),
      (aqVerify h s M P).1 = true → P ∈ aqVerifiedCandidates N h s M)
  ∧ (∀ (N s M P P' : ℕ),
      ¬ aqPeriodProgression N s M P' ⊆ aqPeriodProgression N s M P →
        0 < aqPeriodSeparation N s M P P')
  ∧ (∀ (N s M P P' : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1),
      0 < aqPeriodSeparation N s M P P' →
        (∑ σ : Fin N → Bool, (bernoulliStreamLaw N p hp hp1).prob σ *
          (if aqCandidateConsistent N s M P' (aqFreshMarked N s M P σ) then 1 else 0))
          = p ^ (aqPeriodSeparation N s M P P'))
  ∧ (∀ (N s M P : ℕ) (p : ℝ) (cands : Finset ℕ) (hP : P ∈ cands) (σ : Fin N → Bool),
      (∀ P' ∈ cands \ {P},
        ¬ aqCandidateConsistent N s M P' (aqFreshMarked N s M P σ)) →
        aqFreshCompatible N s M cands (aqFreshMarked N s M P σ) = {P} ∧
          aqFreshDisambiguate N s M cands p (aqFreshMarked N s M P σ) = some P)

/-- The cyclic-verification, density-counting, and round-saving statements, together with
distinctions between progression lengths and period steps. -/
def Clause5LayerStepDistinction : Prop :=
  (∀ (N : ℕ) (hN : 0 < N) (h : Fin N → Bool) (s M P : ℕ)
      (hM : 2 ≤ M) (hP : 0 < P) (hMP : M * P ≤ N) (G : Finset (Fin N))
      (hmark : ∀ x, h x = decide (x ∈ ((Finset.range M).image (fun r : ℕ =>
        (⟨(s + r * P) % N, Nat.mod_lt _ hN⟩ : Fin N))) ∪ G)),
      aqCyclicVerify N hN h s M P = (true, 3))
  ∧ (∀ (N : ℕ) (hN : 0 < N) (h : Fin N → Bool) (s M q : ℕ),
      (aqCyclicVerify N hN h s M q).2 ≤ 3)
  ∧ (∀ (N M L : ℕ) (hN : 0 < N) (hM : 0 < M) (hML : M ≤ L) (hLN : 2 * L ≤ N),
      aqLayerRoundCount N M L ≤ aqPublicRoundCount N M)
  ∧ (∀ (N M L : ℕ) (hN : 0 < N) (hM : 0 < M) (hML : M ≤ L) (hLN : 2 * L ≤ N),
      aqPublicRoundCount N M - aqLayerRoundCount N M L = aqRoundSaving N M L)

  ∧ (∀ (N : ℕ) (hN : 0 < N) (h : Fin N → Bool) (s M P : ℕ)
      (hM : 2 ≤ M) (hP : 0 < P) (hMP : M * P ≤ N) (G : Finset (Fin N))
      (hmark : ∀ x, h x = decide (x ∈ ((Finset.range M).image (fun r : ℕ =>
        (⟨(s + r * P) % N, Nat.mod_lt _ hN⟩ : Fin N))) ∪ G)),
      aqNextCyclicVerify N hN h s M P = (true, 3))
  ∧ (∀ (N : ℕ) (hN : 0 < N) (h : Fin N → Bool) (s M q : ℕ),
      (aqNextCyclicVerify N hN h s M q).2 ≤ 3)
  ∧ (∀ (N : ℕ) (hN : 0 < N) (C : Finset (Fin N)),
      8 / Real.pi ^ 2 ≤
        ∑ z ∈ Finset.univ.filter (fun z : Fin (32 * N) => aqNextPublicDensityReadout N z = C.card),
          (aeLaw (32 * N) (QFTMatrix N) ⟨0, hN⟩ C (qftMatrix_unitary hN)
            (by omega)).prob z ∧
        QueryCount (countedAECircuit (32 * N) (QFTMatrix N) (⟨0, hN⟩ : Fin N)) = 32 * N - 1 ∧
        GateCount (countedAECircuit (32 * N) (QFTMatrix N) (⟨0, hN⟩ : Fin N))
          = 5 * (32 * N - 1) + 3)

  ∧ (∀ (N M L : ℕ) (hN : 0 < N) (hM : 0 < M) (hML : M ≤ L) (hLN : 2 * L ≤ N),
      aqLayerRoundCount N M L = aqRounds N L ∧ aqPublicRoundCount N M = aqRounds N M)
  ∧ (∀ (N s M L P : ℕ) (hM : 0 < M) (hML : M < L) (hP : 0 < P)
      (hbound : s + (L - 1) * P < N),
      aqPeriodProgression N s M P ≠ aqPeriodProgression N s L P)
  ∧ (0 < aqPeriodSeparation 128 0 2 4 2)

/-- The Haar, sampling, and QFT statements together with zero-length progression degeneracy and
the density-counting and layer-dependent resource comparisons. -/
def Clause6ZeroMPromise : Prop :=
  HaarGeneralWN
  ∧ (∀ (C fuel : ℕ) (hC : 0 < C),
      ∀ j : Fin C,
        CostedLaw.event (aqFairLabelSampler C fuel)
            (fun z => z.1 = Sum.inl j) =
          (1 - coinRejectMass (Nat.clog 2 C) C ^ fuel) / (C : ℝ≥0∞))
  ∧ (∀ n : ℕ,
      GateCount (localProgramCircuit (localQFT n)) = n + n * (n - 1) / 2 + n / 2)
  ∧ (∀ (N s M P P' : ℕ), M = 0 →
      aqPeriodProgression N s 0 P = ∅ ∧ aqPeriodSeparation N s 0 P P' = 0)
  ∧ (∀ (N s M P P' : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1), M = 0 →
      (∑ σ : Fin N → Bool, (bernoulliStreamLaw N p hp hp1).prob σ *
        (if aqCandidateConsistent N s M P' (aqFreshMarked N s M P σ) then 1 else 0)) = 1)

  ∧ (∀ (N : ℕ) (hN : 0 < N),
      QueryCount (countedAECircuit (32 * N) (QFTMatrix N) (⟨0, hN⟩ : Fin N)) = 32 * N - 1)
  ∧ (∀ (N M L : ℕ) (hN : 0 < N) (hM : 0 < M) (hML : M ≤ L) (hLN : 2 * L ≤ N),
      aqNextRecoveryQuerySaving N M L = aqRoundSaving N M L)
  ∧ (∀ (N M L : ℕ) (hN : 0 < N) (hM : 0 < M) (hML : M ≤ L) (hLN : 2 * L ≤ N),
      (5 * (32 * N - 1) + 3) + (3 * aqPublicRoundCount N M + 2) -
          ((5 * (32 * N - 1) + 3) + (3 * aqLayerRoundCount N M L + 2))
        = 3 * aqRoundSaving N M L)
  ∧ (∀ (N M : ℕ) (hN : 0 < N) (hM : 0 < M),
      (∀ L : ℕ, M ≤ L → 2 * L ≤ N → aqRounds N (N / 2) ≤ aqRounds N L) ∧
        2 * (N / 2) ≤ N)
  ∧ (∀ (N M : ℕ) (hN : 0 < N) (hM : 0 < M) (L : ℕ), M ≤ L → 2 * L ≤ N →
      aqNextLayerRecoveryQueries N M (N / 2) ≤ aqNextLayerRecoveryQueries N M L)
  ∧ (∀ (N M : ℕ) (hN : 0 < N) (hM : 0 < M) (L : ℕ), M ≤ L → 2 * L ≤ N →
      aqNextPublicRecoveryQueries N M - aqNextLayerRecoveryQueries N M L
        = aqNextRecoveryQuerySaving N M L)

/-- The size-128 oracle marking the period-two progression of length four together with noise
sites eight and twelve. -/
def aqBoundaryOracle : Fin 128 → Bool :=
  fun x => decide (x ∈ (aqProgressionSet 128 0 4 2 ∪ ({8, 12} : Finset (Fin 128))))

/-- The explicit fixed-noise boundary example in which periods two and four yield the same
oracle, pass verification, and remain in the verified candidate set despite positive
separation. -/
def Clause7FixedNoiseBoundary : Prop :=
  ((aqProgressionSet 128 0 4 2 ∪ ({8, 12} : Finset (Fin 128))) =
      (aqProgressionSet 128 0 4 4 ∪ ({2, 6} : Finset (Fin 128)))) ∧
  ((aqVerify aqBoundaryOracle 0 4 2).1 = true) ∧
  ((aqVerify aqBoundaryOracle 0 4 4).1 = true) ∧
  (0 < aqPeriodSeparation 128 0 4 4 2) ∧
  (2 ∈ aqVerifiedCandidates 128 aqBoundaryOracle 0 4) ∧
  (4 ∈ aqVerifiedCandidates 128 aqBoundaryOracle 0 4)

/-- The Bernoulli zero-mode transport statement together with progression cardinalities and the
layer, query, and gate ledgers under the stated assumptions. -/
def Clause8ZeroModeRuntime : Prop :=
  BernoulliErrorStreamZeroModeTransport
  ∧ (∀ (N k : ℕ) [NeZero N] (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
      (d : FinDist (Finset (ZMod N)))
      (hd : ∀ S : Finset (ZMod N), d.prob S = p ^ S.card * (1 - p) ^ (N - S.card))
      (s M P : ℕ) (θ : ℕ → ℝ)
      (hM : 2 ≤ M) (hP : 0 < P) (hs : s + (M - 1) * P < N) (hMN : M + 2 ≤ N)
      (hθ : ∀ L : ℕ, L < N - M →
        0 < θ L ∧ θ L < Real.pi / 2 ∧
          (Real.sin (θ L)) ^ 2 = ((M + L : ℕ) : ℝ) / (N : ℝ)),
      (Finset.image (fun r : ℕ => (s + r * P : ZMod N)) (Finset.range M)).card = M ∧
      (Finset.univ \ (Finset.image (fun r : ℕ => (s + r * P : ZMod N)) (Finset.range M))).card
          = N - M ∧
      QueryCount (conditionalAmplifiedQFTCircuit N k) = k ∧
      GateCount (conditionalAmplifiedQFTCircuit N k) = 3 * k + 2 ∧
      aqZeroModeLayers N M = N - M + 1 ∧
      aqZeroModeRuntime N M k = (N - M + 1) * (3 * k + 2))

end Qatlib.Concepts.AmpTransform.ErrorStream
