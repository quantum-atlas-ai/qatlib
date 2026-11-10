/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FixedPtSearch14.FixedPoint.SearchEstimationDefs
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CountRelDefs
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeReadoutRefined
import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.CountingCertainty
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeReadoutRefined
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTQSearch
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTTh17
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CountRelNext
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open Qatlib.Concepts.AEMeanReadout.RankOneSubspace
open Qatlib.Concepts.AEMeanReadout.RankOneSubspace.CountingCertainty
open Qatlib.Concepts.AEMeanReadout.RankOneSubspace.RankOneReflection
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.MonteCarloMean.LayeredMean
open Qatlib.Concepts.MonteCarloMean.PilotVariance
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.WalkSearch.QuantumAccess
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Papers.FixedPtSearch14.FixedPoint.SearchEstimationCore

open Qatlib
open Matrix
open scoped ENNReal Classical
open BHMTQSearch
open RandomizedExecution
open Filter
open scoped Topology
open BHMTTh17

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Qatlib.Papers.FixedPtSearch14.FixedPoint
namespace SearchEstimationCore

variable {I : Type} [Fintype I] [DecidableEq I]

theorem clause78_endpoint :

    (∀ (M : ℕ) (i : Fin M), sourceDepth M i = i.val + 1) ∧
    (∀ (l : ℕ) (i : Fin (qSearchWindow l)),
      sourceDepth (qSearchWindow l) i = i.val + 1) ∧

    (∀ (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
      (l : ℕ),
      CostedLaw.expectation (sourceQSearchRound A hA j₀ S l) (fun out => (out.2.1 : ℝ≥0∞))
        ≤ ENNReal.ofReal (6 * ((6/5:ℝ)^l)) ∧
      CostedLaw.expectation (sourceQSearchRound A hA j₀ S l) (fun out => (out.2.2 : ℝ≥0∞))
        ≤ ENNReal.ofReal (4 * ((6/5:ℝ)^l))) ∧

    (∀ (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
      (T : ℕ),
      0 < MeasureProb (preparedAAState A j₀) S →
      CostedLaw.expectation (sourceQSearchLoop A hA j₀ S T 0) (fun out => (out.2.1 : ℝ≥0∞))
        ≤ ENNReal.ofReal (400 / Real.sqrt (MeasureProb (preparedAAState A j₀) S)) ∧
      CostedLaw.expectation (sourceQSearchLoop A hA j₀ S T 0) (fun out => (out.2.2 : ℝ≥0∞))
        ≤ ENNReal.ofReal (400 / Real.sqrt (MeasureProb (preparedAAState A j₀) S))) ∧

    (∀ (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
      (l : ℕ),
      roundSuccessMass (sourceQSearchRound A hA j₀ S l)
        - roundSuccessMass (BHMTQSearch.qSearchRound A hA j₀ S l)
        = (1 - MeasureProb (preparedAAState A j₀) S)
          * ((depthSuccessMass A j₀ S (qSearchWindow l) - depthSuccessMass A j₀ S 0)
              / (qSearchWindow l : ℝ))) ∧

    (∀ (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
      (T : ℕ),
      0 < MeasureProb (preparedAAState A j₀) S →
      CostedLaw.expectation (sourceQSearchLoop A hA j₀ S T 0) (fun out => (out.2.1 : ℝ≥0∞))
        ≤ ENNReal.ofReal (400 / Real.sqrt (MeasureProb (preparedAAState A j₀) S)) ∧
      CostedLaw.expectation (sourceQSearchLoop A hA j₀ S T 0) (fun out => (out.2.2 : ℝ≥0∞))
        ≤ ENNReal.ofReal (400 / Real.sqrt (MeasureProb (preparedAAState A j₀) S)) ∧
      CostedLaw.expectation (BHMTQSearch.qSearchLoop A hA j₀ S T 0) (fun out => (out.2.1 : ℝ≥0∞))
        ≤ ENNReal.ofReal (400 / Real.sqrt (MeasureProb (preparedAAState A j₀) S)) ∧
      CostedLaw.expectation (BHMTQSearch.qSearchLoop A hA j₀ S T 0) (fun out => (out.2.2 : ℝ≥0∞))
        ≤ ENNReal.ofReal (400 / Real.sqrt (MeasureProb (preparedAAState A j₀) S))) ∧

    (∀ (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I),
      MeasureProb (preparedAAState A j₀) S = 0 →
      ∀ n, sourceSurvival A hA j₀ S n = 1) ∧

    (∀ (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I),
      0 < MeasureProb (preparedAAState A j₀) S →
      Tendsto (sourceSurvival A hA j₀ S) atTop (𝓝 0)) ∧

    (∀ (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
      (r c1 c2 : ℕ) (cfg : Configuration SourceRunState (SourceRunOutcome I)),
      cfg ∈ (sourceTransition A hA j₀ S r c1 c2).support →
      ∀ y c1' c2', cfg = Sum.inl (some y, c1', c2') → y ∈ S) ∧

    (∀ (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I),
      Tendsto (fun N => CostedLaw.expectation (runFor (sourceNext A hA j₀ S) N
          (sourceInitial (I := I)))
          (fun x => (sourceAccumulated (fun c1 c2 => c1) x.1 : ℝ≥0∞)))
        atTop (𝓝 (sourceStopLedgerExpectation A hA j₀ S
          (fun out => (out.2.1 : ℝ≥0∞))))) ∧

    (∀ (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I),
      0 < MeasureProb (preparedAAState A j₀) S →
      sourceStopLedgerExpectation A hA j₀ S (fun out => (out.2.1 : ℝ≥0∞))
        ≤ ENNReal.ofReal (400 / Real.sqrt (MeasureProb (preparedAAState A j₀) S)) ∧
      sourceStopLedgerExpectation A hA j₀ S (fun out => (out.2.2 : ℝ≥0∞))
        ≤ ENNReal.ofReal (400 / Real.sqrt (MeasureProb (preparedAAState A j₀) S))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro M i
    rfl
  · intro l i
    rfl
  · intro A hA j₀ S l
    exact s2_source_round_ledger_cost A hA j₀ S l
  · intro A hA j₀ S T ha
    exact s2_source_search_two_ledger_budget A hA j₀ S T ha
  · intro A hA j₀ S l
    exact s2_source_search_exact_relation_to_frozen_shifted A hA j₀ S l
  · intro A hA j₀ S T ha
    exact source_and_shifted_two_ledger_budget A hA j₀ S T ha
  · intro A hA j₀ S ha n
    exact s2_unbounded_search_never_halts A hA j₀ S ha n
  · intro A hA j₀ S ha
    exact s2_unbounded_search_terminates A hA j₀ S ha
  · intro A hA j₀ S r c1 c2 cfg hcfg
    exact s2_unbounded_search_halts_marked A hA j₀ S r c1 c2 cfg hcfg
  · intro A hA j₀ S
    exact s2_stop_cost_expectation_is_limit A hA j₀ S
  · intro A hA j₀ S ha
    exact s2_unbounded_stop_cost_retains_sqrt_a_budget A hA j₀ S ha

theorem clause8_endpoint
    (A : Matrix I I ℂ) (j : I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (f : I → ℚ) (nu eps : ℚ)
    (N h : ℕ) (K r : ℕ)
    (hk : ∀ ω : Fin N → I, pilotPrecision N h f nu eps ω < K)
    (hN : 0 < N) (hf : ∀ i, |f i| ≤ 1) (hnu : 0 < nu) (hnu1 : nu ≤ 1/4) (heps : 0 < eps)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hδ : (8/9 : ℝ)^r + 2/((N : ℝ)*(nu : ℝ)^2) ≤ δ) :
    (∑ rec : unknownSigmaFullRecord I N K r,
        (unknownSigmaLaw A j hA f nu eps N h K r hk).prob rec) = 1 ∧
    (SignedMean.mass (unknownSigmaLaw A j hA f nu eps N h K r hk)
        (unknownSigmaFails A j hA f nu eps N h K r hk)
      ≤ (8/9 : ℝ)^r + 2/((N : ℝ)*(nu : ℝ)^2)) ∧
    (SignedMean.mass (unknownSigmaLaw A j hA f nu eps N h K r hk)
        (fun rec => ¬ unknownSigmaFails A j hA f nu eps N h K r hk rec) ≥ 1 - δ) ∧
    (unknownSigmaSecondMoment A j hA f ≤ 1 ∧ unknownSigmaFourthMoment A j hA f ≤ 1) ∧
    ((signedMeanSource A j hA).variance (fun i => (f i : ℝ))^2
      ≤ unknownSigmaFourthMoment A j hA f) ∧
    (∀ ωp : Fin N → I, unknownSigmaLedgerLe
        (unknownSigmaLedger N r (pilotPrecision N h f nu eps ωp))
        (unknownSigmaLedger N r (unknownSigmaWorstPrecision eps))) ∧
    (unknownSigmaExpectedAccesses A j hA f nu eps N h K r hk
      ≤ unknownSigmaLedgerAccesses N r
            (unknownSigmaGoodPrecision ((signedMeanSource A j hA).variance (fun i => (f i : ℝ)))
              (nu : ℝ) h (eps : ℝ))
        + ((unknownSigmaSecondMoment A j hA f + unknownSigmaFourthMoment A j hA f)
            / ((N : ℝ)*(nu : ℝ)^2)) *
          unknownSigmaLedgerAccesses N r (unknownSigmaWorstPrecision eps)) ∧

    (∀ (N : ℕ) (nu : ℝ) (hnu : 0 < nu) (δ : ℝ) (r : ℕ),
      (8/9 : ℝ)^r < δ →
      ∃ (A : Matrix (Fin 2) (Fin 2) ℂ) (j : Fin 2)
        (hA : A ∈ Matrix.unitaryGroup (Fin 2) ℂ) (f : Fin 2 → ℚ),
        unknownSigmaSecondMoment A j hA f > 0 ∧
        unknownSigmaSecondMoment A j hA f + unknownSigmaFourthMoment A j hA f
          > (N : ℝ) * (nu : ℝ)^2 * (δ - (8/9 : ℝ)^r)) ∧

    (∀ (A : Matrix I I ℂ) (j : I) (hA : A ∈ Matrix.unitaryGroup I ℂ) (f : I → ℚ)
      (N : ℕ) (nu : ℝ) (r : ℕ) (hN : 0 < N) (hnu : 0 < nu) (δ : ℝ),
      (8/9 : ℝ)^r < δ →
      (unknownSigmaSecondMoment A j hA f + unknownSigmaFourthMoment A j hA f
          ≤ (N : ℝ) * (nu : ℝ)^2 * (δ - (8/9 : ℝ)^r)) →
      (signedMeanSource A j hA).probEvent (L := N)
          (AmplitudeReadoutRefined.nextPilotBadMoment A j hA f N nu)
        ≤ δ - (8/9 : ℝ)^r) ∧

    (∀ ωp : Fin N → I,
      unknownSigmaLedgerAccesses N r (pilotPrecision N h f nu eps ωp)
        ≤ unknownSigmaLedgerAccesses N r (unknownSigmaWorstPrecision eps)) ∧

    (∀ ωp : Fin N → I,
      unknownSigmaLedgerLe
          (unknownSigmaLedger N r (pilotPrecision N h f nu eps ωp))
          (unknownSigmaLedger N r (unknownSigmaWorstPrecision eps)) ∧
      (unknownSigmaLedger N r (unknownSigmaWorstPrecision eps)).layerCopies
          = (2*r+1) * (2 * AmplitudeReadoutRefined.nextTrialQueries (unknownSigmaWorstPrecision eps)) ∧
      (unknownSigmaLedger N r (unknownSigmaWorstPrecision eps)).measurements
          = N + (2*r+1) * (1 + 2*AmplitudeReadoutRefined.nextTrialQueries (unknownSigmaWorstPrecision eps)) ∧
      (unknownSigmaLedger N r (unknownSigmaWorstPrecision eps)).gates
          = N + (2*r+1) * (1 + 2*AmplitudeReadoutRefined.nextTrialQueries (unknownSigmaWorstPrecision eps)
              * (5*(layerGrid (unknownSigmaWorstPrecision eps) - 1)+3))) ∧

    (∀ (ωp : Fin N → I)
      (ωt : unknownSigmaTrialRecord I r (pilotPrecision N h f nu eps ωp)),
      unknownSigmaResources A j hA f nu eps N h K r hk
          (⟨unknownSigmaPilotIndex N h f nu eps K hk ωp, (ωp, ωt)⟩ :
            unknownSigmaFullRecord I N K r)
        = unknownSigmaLedger N r (pilotPrecision N h f nu eps ωp) ∧
      (unknownSigmaLedger N r (pilotPrecision N h f nu eps ωp)).sourcePreparations
          = N + (2*r+1) ∧
      (unknownSigmaLedger N r (pilotPrecision N h f nu eps ωp)).layerCopies
          = (2*r+1) * (2 * AmplitudeReadoutRefined.nextTrialQueries (pilotPrecision N h f nu eps ωp)) ∧
      (unknownSigmaLedger N r (pilotPrecision N h f nu eps ωp)).measurements
          = N + (2*r+1) * (1 + 2*AmplitudeReadoutRefined.nextTrialQueries (pilotPrecision N h f nu eps ωp)) ∧
      (unknownSigmaLedger N r (pilotPrecision N h f nu eps ωp)).gates
          = N + (2*r+1) * (1 + 2*AmplitudeReadoutRefined.nextTrialQueries (pilotPrecision N h f nu eps ωp)
              * (5*(layerGrid (pilotPrecision N h f nu eps ωp) - 1)+3))) := by
  rcases Qatlib.Concepts.AEMeanReadout.LocalAEBackend.clause8_endpoint
      A j hA f nu eps N h K r hk hN hf hnu hnu1 heps δ hδ0 hδ1 hδ with
    ⟨b1, b2, b3, b4, b5, b6, b7⟩
  refine ⟨b1, b2, b3, b4, b5, b6, b7, ?_, ?_, ?_, ?_, ?_⟩
  · intro N nu hnu δ r hδ
    exact unknownSigma_tail_promise_necessary_s2 N nu hnu δ r hδ
  · intro A j hA f N nu r hN hnu δ hδ hreserve
    exact nextPilotBadMoment_mass_le_reserve_s2 A j hA f N nu r hN hnu δ hδ hreserve
  · intro ωp
    exact AmplitudeReadoutRefined.unknownSigma_worst_path_accesses A j hA f nu eps
      N h K r hk hN hf hnu hnu1 heps ωp
  · intro ωp
    have h := AmplitudeReadoutRefined.unknownSigma_worst_path_components
      A j hA f nu eps N h K r hk hN hf hnu hnu1 heps ωp
    exact ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2.2.2⟩
  · intro ωp ωt
    have h := AmplitudeReadoutRefined.unknownSigma_component_budget
      A j hA f nu eps N h K r hk ωp ωt
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2.2.2⟩

theorem clause81_endpoint :

    (∀ (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (g : Fin (n + 1) → Bool)
      (hA : A * A.conjTranspose = 1) (θ : ℝ) (hθ0 : 0 < θ) (hθπ : θ ≤ Real.pi / 2)
      (hmass : Real.sin θ ^ 2 = CountingCertainty.nextGoodMass A g)
      (ha0 : 0 < CountingCertainty.nextGoodMass A g)
      (ha1 : CountingCertainty.nextGoodMass A g < 1)
      (m : ℕ) (hm : (m : ℝ) = CountingCertainty.nextHalfStep θ),
      ∑ i, Complex.normSq (RankOneReflection.goodPart g
        (((RankOneReflection.iterate A g (-1) (-1)) ^ m).mulVec (fun i => A i 0)) i) = 1) ∧

    (∀ (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (g : Fin (n + 1) → Bool)
      (hA : A * A.conjTranspose = 1) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
      (hmass : Real.sin θ ^ 2 = CountingCertainty.nextGoodMass A g)
      (ha0 : 0 < CountingCertainty.nextGoodMass A g)
      (ha1 : CountingCertainty.nextGoodMass A g < 1) (φ ϕ : ℂ),
      (∀ (m : ℕ) (h : (m : ℝ) = CountingCertainty.nextHalfStep θ),
        ∑ i, Complex.normSq (RankOneReflection.goodPart g
          (CountingCertainty.nextCertaintyProgram A g θ φ ϕ
            (.integral m h)) i) = 1) ∧
      (∀ (hne : ∀ m : ℕ, (m : ℝ) ≠ CountingCertainty.nextHalfStep θ),
        ∃ (φ' ϕ' : ℂ),
          ‖φ'‖ = 1 ∧ ‖ϕ'‖ = 1 ∧
          CountingCertainty.NextSlowdownEquations A g θ φ' ϕ' ∧
          ∑ i, Complex.normSq (RankOneReflection.goodPart g
            (CountingCertainty.nextCertaintyProgram A g θ φ' ϕ'
              (.nonIntegral hne)) i) = 1)) ∧

    (∀ (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ)
      (hA : A * A.conjTranspose = 1)
      (P₀ : CountingCertainty.NextZeroProjector I) (φ : ℂ),
      A * (1 + (φ - 1) • P₀.toMatrix) * A.conjTranspose
        = 1 + (φ - 1) • (A * P₀.toMatrix * A.conjTranspose)) ∧
    (∀ (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ)
      (hA : A * A.conjTranspose = 1) (g : I → Bool)
      (P₀ : CountingCertainty.NextZeroProjector I) (φ ϕ : ℂ)
      (ψg ψb : I → ℂ) (c₁ c₂ c₃ c₄ : ℂ),
      ((A * P₀.toMatrix * A.conjTranspose).mulVec
          ((Matrix.diagonal (fun i => if g i then ϕ else 1)).mulVec ψg)
          = c₁ • ψg + c₂ • ψb) →
      ((A * P₀.toMatrix * A.conjTranspose).mulVec
          ((Matrix.diagonal (fun i => if g i then ϕ else 1)).mulVec ψb)
          = c₃ • ψg + c₄ • ψb) →
      (CountingCertainty.nextIterateGen A g P₀ φ ϕ).mulVec ψg
          = -((Matrix.diagonal (fun i => if g i then ϕ else 1)).mulVec ψg
              + (φ - 1) • (c₁ • ψg + c₂ • ψb)) ∧
      (CountingCertainty.nextIterateGen A g P₀ φ ϕ).mulVec ψb
          = -((Matrix.diagonal (fun i => if g i then ϕ else 1)).mulVec ψb
              + (φ - 1) • (c₃ • ψg + c₄ • ψb))) ∧

    (∀ (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (g : Fin (n + 1) → Bool)
      (P₀ : CountingCertainty.NextZeroProjector (Fin (n + 1))) (φ ϕ : ℂ),
      P₀.toMatrix = Matrix.single 0 0 (1 : ℂ) →
      CountingCertainty.nextIterateGen A g P₀ φ ϕ
        = RankOneReflection.iterate A g φ ϕ) ∧

    ((1 : Matrix (Fin 2) (Fin 2) ℂ) * (1 : Matrix (Fin 2) (Fin 2) ℂ) *
        (1 : Matrix (Fin 2) (Fin 2) ℂ) = (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
      (1 : Matrix (Fin 2) (Fin 2) ℂ) * (1 : Matrix (Fin 2) (Fin 2) ℂ) *
        (Matrix.single 0 0 (1 : ℂ)) ≠ (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧

    (∀ (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (g : Fin (n + 1) → Bool)
      (hA : A * A.conjTranspose = 1) (θ : ℝ) (hθ0 : 0 < θ) (hθπ : θ ≤ Real.pi / 2)
      (br : CountingCertainty.NextCertaintyBranch θ),
      (CountingCertainty.nextCertaintyPrepareAccesses θ br : ℝ)
        ≤ 2 * (CountingCertainty.nextHalfStep θ + 1)) := by
  exact AmplitudeReadoutRefined.clause22_endpoint

theorem clause84_endpoint
    (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (N : ℕ) (hN : 0 < N) (Sc : Finset (Fin N))
    (ε : ℝ) (hε : 0 < ε)
    :
    (BooleanEvaluationOracle (preparedMark S) S ∧
      ControlledPhaseImplementation (preparedMark S) S ∧
      (∀ M : ℕ, ∀ hM : 2 ≤ M,
        RecordOracleCostTransport M A j S (preparedMark S) hA hM)) ∧
    (JointRecordOracleCostTransport (basicApproxCountPrefixWeight hN Sc)
        (fun ω => recordGrids (fun l : Fin (basicApproxCountLoopCap N) => 2 * 2 ^ l.val)
          (basicApproxCountExecFlag N ω)
          (basicApproxCountFinalM ε (basicApproxCountStop N ω)))
        (fun ω => basicApproxCountTotalCost N ε ω) ∧
      (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val),
          (basicApproxCountPrefixWeight hN Sc ω) * ((basicApproxCountTotalCost N ε ω : ℕ) : ℝ))
        = (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val),
            (basicApproxCountPrefixWeight hN Sc ω) *
              ((pathMarks (basicApproxCountExecutedGrids N ε ω) : ℕ) : ℝ))
          + ∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val),
            (basicApproxCountPrefixWeight hN Sc ω) *
              ((basicApproxCountExecutedGrids N ε ω).length : ℝ) ∧
      (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val),
          (basicApproxCountPrefixWeight hN Sc ω) *
            ((pathPrep (basicApproxCountExecutedGrids N ε ω) : ℕ) : ℝ))
        = 2 * (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val),
            (basicApproxCountPrefixWeight hN Sc ω) *
              ((pathMarks (basicApproxCountExecutedGrids N ε ω) : ℕ) : ℝ))
          + ∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val),
            (basicApproxCountPrefixWeight hN Sc ω) *
              ((basicApproxCountExecutedGrids N ε ω).length : ℝ) ∧
      (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val),
          (basicApproxCountPrefixWeight hN Sc ω) *
            ((pathControl (basicApproxCountExecutedGrids N ε ω) : ℕ) : ℝ))
        = ∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val),
          (basicApproxCountPrefixWeight hN Sc ω) *
            ((pathMarks (basicApproxCountExecutedGrids N ε ω) : ℕ) : ℝ) ∧
      (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val),
          (basicApproxCountPrefixWeight hN Sc ω) * (0 : ℝ)) = 0 ∧
      (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val),
          (basicApproxCountPrefixWeight hN Sc ω) *
            ((pathFixed (basicApproxCountExecutedGrids N ε ω) : ℕ) : ℝ))
        = 5 * (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val),
            (basicApproxCountPrefixWeight hN Sc ω) *
              ((pathMarks (basicApproxCountExecutedGrids N ε ω) : ℕ) : ℝ))
          + 3 * ∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val),
            (basicApproxCountPrefixWeight hN Sc ω) *
              ((basicApproxCountExecutedGrids N ε ω).length : ℝ)) ∧
    (JointRecordOracleCostTransport (exactCountPathWeight hN Sc (exactCountM₀_ge_two_s2 (N := N) hN))
        (exactCountExecutedGrids N)
        (fun z => 2 * exactCountM₀ N + exactCountGrid N
          ((N : ℝ)*aeEstimate (exactCountM₀ N) z.1)
          ((N : ℝ)*aeEstimate (exactCountM₀ N) z.2)) ∧
      (∑ z : Fin (exactCountM₀ N) × Fin (exactCountM₀ N),
          (exactCountPathWeight hN Sc (exactCountM₀_ge_two_s2 (N := N) hN) z) *
            ((2 * exactCountM₀ N + exactCountGrid N
              ((N : ℝ)*aeEstimate (exactCountM₀ N) z.1)
              ((N : ℝ)*aeEstimate (exactCountM₀ N) z.2) : ℕ) : ℝ))
        = (∑ z : Fin (exactCountM₀ N) × Fin (exactCountM₀ N),
            (exactCountPathWeight hN Sc (exactCountM₀_ge_two_s2 (N := N) hN) z) *
              ((pathMarks (exactCountExecutedGrids N z) : ℕ) : ℝ))
          + ∑ z : Fin (exactCountM₀ N) × Fin (exactCountM₀ N),
            (exactCountPathWeight hN Sc (exactCountM₀_ge_two_s2 (N := N) hN) z) *
              ((exactCountExecutedGrids N z).length : ℝ)) ∧
    ((∀ M : ℕ, ∀ jj : Fin M,
        RecordLedgerTransport (sourceDepth M jj) (recordLedger (sourceDepth M jj))) ∧
      (∀ M : ℕ, sourceRoundSourceLedger M = sourceRoundControlledMarkLedger M + M)) ∧
    (¬ (∀ (L : ℕ) (Ω : Type) [Fintype Ω] (w : Ω → ℝ)
        (exec : Ω → Fin L → Bool) (Mfin sourceLedger : Ω → ℕ),
        (∀ ω, sourceLedger ω =
          (recordGrids (fun l : Fin L => 2 * 2 ^ l.val) (exec ω) (Mfin ω)).sum) →
        JointRecordOracleCostTransport w
          (fun ω => recordGrids (fun l : Fin L => 2 * 2 ^ l.val) (exec ω) (Mfin ω))
          sourceLedger) ∧
      (∀ grids : List ℕ, 0 ∈ grids →
        ¬ ∃ L : OracleCostLedger, PathLedgerTransport grids L) ∧
      (∀ grids : List ℕ, (∀ g ∈ grids, 1 ≤ g) →
        ∃ L : OracleCostLedger, PathLedgerTransport grids L)) := by
  have hM0 : 2 ≤ exactCountM₀ N := exactCountM₀_ge_two_s2 (N := N) hN
  have hM : ∀ z : Fin (exactCountM₀ N) × Fin (exactCountM₀ N),
      2 ≤ exactCountGrid N ((N : ℝ)*aeEstimate (exactCountM₀ N) z.1)
        ((N : ℝ)*aeEstimate (exactCountM₀ N) z.2) := by
    intro z
    exact exactCountGrid_ge_two_on_estimates_s2 (N := N) hN z.1 z.2
  exact Qatlib.Concepts.AEMeanReadout.LocalAEBackend.clause84_endpoint
    A j S hA N hN Sc ε hε hM0 hM

theorem clause87_endpoint
    (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (a₀ ε : ℝ) (ha0 : 0 < a₀) (ha0a : a₀ ≤ MeasureProb (preparedAAState A j) S)
    (ha1 : MeasureProb (preparedAAState A j) S ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (2 ≤ nextRelativeGrid a₀ ε ∧
      nextAeWindow (nextRelativeGrid a₀ ε) (MeasureProb (preparedAAState A j) S)
        ≤ ε * MeasureProb (preparedAAState A j) S ∧
      16 * Real.pi / (ε * Real.sqrt a₀) ≤ (nextRelativeGrid a₀ ε : ℝ) ∧
      (nextRelativeGrid a₀ ε : ℝ) ≤ 16 * Real.pi / (ε * Real.sqrt a₀) + 1) ∧
    ((∑ z ∈ Finset.univ.filter (fun z : Fin (nextRelativeGrid a₀ ε) =>
        |aeEstimate (nextRelativeGrid a₀ ε) z - MeasureProb (preparedAAState A j) S|
          ≤ ε * MeasureProb (preparedAAState A j) S),
      (aeLaw (nextRelativeGrid a₀ ε) A j S hA
        (nextRelativeGrid_two ha0 (le_trans ha0a ha1) hε hε1)).prob z) ≥ 8 / Real.pi ^ 2 ∧
      8 / Real.pi ^ 2 > 2 / 3) ∧
    (MeasureProb (preparedAAState A j) S = 0 →
      ∀ z : Fin (nextRelativeGrid a₀ ε), z.val = 0 →
        (aeLaw (nextRelativeGrid a₀ ε) A j S hA
          (nextRelativeGrid_two ha0 (le_trans ha0a ha1) hε hε1)).prob z = 1 ∧
        aeEstimate (nextRelativeGrid a₀ ε) z = 0 ∧
        |aeEstimate (nextRelativeGrid a₀ ε) z - 0| ≤ ε * 0) ∧
    (∀ M : ℕ, ∀ hM : 2 ≤ M, ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ nextAeWindow M a > ε * a) ∧
    (aeForwardAccesses (aeAccessWord (I := I) (nextRelativeGrid a₀ ε)) = nextRelativeGrid a₀ ε ∧
      aeBackwardAccesses (aeAccessWord (I := I) (nextRelativeGrid a₀ ε)) = nextRelativeGrid a₀ ε - 1 ∧
      QueryCount (countedAECircuit (nextRelativeGrid a₀ ε) A j) = nextRelativeGrid a₀ ε - 1 ∧
      GateCount (countedAECircuit (nextRelativeGrid a₀ ε) A j)
        = 5 * (nextRelativeGrid a₀ ε - 1) + 3 ∧
      aeFixedMacros (aeFlagAccessWord (I := I) (nextRelativeGrid a₀ ε)) = 2 * (nextRelativeGrid a₀ ε - 1) ∧
      aeFixedMacros (aeFourierAccessWord (I := I) (nextRelativeGrid a₀ ε)) = 2) ∧
    (∀ M : ℝ, 16 * Real.pi / (ε * Real.sqrt a₀) ≤ M →
      16 * Real.pi / (ε * Real.sqrt (MeasureProb (preparedAAState A j) S)) ≤ M) :=
  Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeReadoutRefined.clause92_endpoint A j S hA a₀ ε ha0 ha0a ha1 hε hε1

theorem clause80_endpoint
    {n : ℕ} (hn : 0 < n)
    (F : Fin n → Bool) (G : (Fin n → Bool) → Fin n → Fin n)
    (M T : ℕ) (j : ℕ) (w : NextHeuristicWeights)
    (hT : 1 ≤ T)
    (hcard : 0 < (nextGoodSeeds F G).card)
    (hdensity : nextHeuristicDensity F G ≤ 1 / 2)
    (hMature : 1 ≤ (M : ℝ)
      * Real.sin (2 * nextHeuristicAngle (nextHeuristicDensity F G)))
    (hWin : 1 ≤ (geometricWindow M j : ℝ)
      * Real.sin (2 * nextHeuristicAngle (nextHeuristicDensity F G))) :
    (∀ tr ∈ (nextHeuristicConsumer F G (QFTMatrix n) (qftMatrix_unitary hn)
        (⟨0, hn⟩ : Fin n) M T).support,
        tr.output = tr.seedTrace.result.map (G F) ∧
        (∀ x, (tr.output = some x → F x = true)) ∧
        tr.gForward = tr.seedTrace.validationQueries ∧
        tr.gBackward = tr.seedTrace.validationQueries ∧
        tr.fValidation = tr.seedTrace.validationQueries) ∧
    (CostedLaw.event
        (nextHeuristicConsumer F G (QFTMatrix n) (qftMatrix_unitary hn) (⟨0, hn⟩ : Fin n) M T)
        (fun tr => tr.output = none)
      = CostedLaw.event
          (searchForSchedule (QFTMatrix n) (qftMatrix_unitary hn) (⟨0, hn⟩ : Fin n)
            (nextGoodSeeds F G) (nextGoodSeedValid F G) (geometricSearchSchedule M T))
          (fun tr => tr.result = none) ∧
      (CostedLaw.event
          (nextHeuristicConsumer F G (QFTMatrix n) (qftMatrix_unitary hn) (⟨0, hn⟩ : Fin n) M T)
          (fun tr => tr.output = none)).toReal ≤ (25/32 : ℝ)^(T - j) ∧
      ((MeasureProb (preparedAAState (QFTMatrix n) (⟨0, hn⟩ : Fin n)) (nextGoodSeeds F G) = 0 →
        CostedLaw.event
            (nextHeuristicConsumer F G (QFTMatrix n) (qftMatrix_unitary hn) (⟨0, hn⟩ : Fin n) M T)
            (fun tr => tr.output = none) = 1)) ∧
      (∀ tr ∈ (nextHeuristicConsumer F G (QFTMatrix n) (qftMatrix_unitary hn)
          (⟨0, hn⟩ : Fin n) M T).support,
        tr.seedTrace.validationQueries ≤ T ∧
        tr.seedTrace.phaseQueries ≤ nextHeuristicSigmaP M T ∧
        tr.gForward ≤ T ∧ tr.gBackward ≤ T ∧ tr.fValidation ≤ T) ∧
    (∀ tr ∈ (nextHeuristicConsumer F G (QFTMatrix n) (qftMatrix_unitary hn)
        (⟨0, hn⟩ : Fin n) M T).support,
        nextHeuristicTotalCost w tr
          = w.gate * tr.seedTrace.macroGates
            + w.bit * tr.seedTrace.bits
            + w.phase * tr.seedTrace.phaseQueries
            + w.prepare * tr.seedTrace.prepareCalls
            + w.validation * tr.fValidation
            + w.gForward * tr.gForward
            + w.gBackward * tr.gBackward) ∧
    (CostedLaw.expectation
        (nextHeuristicConsumer F G (QFTMatrix n) (qftMatrix_unitary hn) (⟨0, hn⟩ : Fin n) M T)
        (fun tr => nextHeuristicCost w tr)
      ≤ ENNReal.ofReal (nextHeuristicCostConstant w
          / Real.sqrt (2 * nextHeuristicDensity F G))) ∧
    (CostedLaw.expectation
        (nextHeuristicConsumer F G (QFTMatrix n) (qftMatrix_unitary hn) (⟨0, hn⟩ : Fin n) M T)
        (fun tr => nextHeuristicCost w tr)
      ≤ ENNReal.ofReal ((nextHeuristicCostConstant w / Real.sqrt 2)
          * Real.sqrt ((nextHeuristicSigmaP M T : ℝ) * (n : ℝ))))) :=
  Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeReadoutRefined.clause87_endpoint hn F G M T j w hT hcard hdensity
    hMature hWin

theorem clause89_endpoint
    {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (hcard : 1 ≤ (S.card : ℝ)) (hcardN : (S.card : ℝ) ≤ (N : ℝ) / 2)
    (hM₀ : 2 ≤ nextCor4RoughGrid N)
    (hM : ∀ z₁ z₂ : Fin (nextCor4RoughGrid N),
      2 ≤ nextCor4Grid N
        ((N : ℝ) * aeEstimate (nextCor4RoughGrid N) z₁)
        ((N : ℝ) * aeEstimate (nextCor4RoughGrid N) z₂)) :
    (3 / 4 ≤ nextCor4SuccessMass hN S hM₀ hM) ∧
    (S.card = 0 →
      ∀ y : Fin (nextCor4RoughGrid N), y.val = 0 →
        (aeLaw (nextCor4RoughGrid N) (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
          (qftMatrix_unitary hN) hM₀).prob y = 1 ∧
        exactCountOutput N y = 0) ∧
    (Nat.clog 2 (N + 1) ≤ nextCor4OutputBits N ∧
      2 * nextCor4OutputBits N ≤ nextCor4SpaceBudget N ∧
      Nat.clog 2 (N + 1) ≤ Qatlib.Concepts.AEMeanReadout.LocalAEBackend.effCountBitBudget N 0 ∧
      2 * Qatlib.Concepts.AEMeanReadout.LocalAEBackend.effCountBitBudget N 0 ≤
        Qatlib.Concepts.AEMeanReadout.LocalAEBackend.effCountSpaceBudget N 0) ∧
    (∀ j : ℕ, (∑ z ∈ overSet S j, firstProb hN S z)
        ≤ 1 / (2 * ((((4 ^ (j + 1) : ℕ) : ℝ)) - 1))) ∧
    (∀ j : ℕ, (∑ z ∈ (overSet S j) ×ˢ (overSet S j),
        (firstProb hN S z.1) * (firstProb hN S z.2))
        ≤ (1 / (2 * ((((4 ^ (j + 1) : ℕ) : ℝ)) - 1))) *
          (1 / (2 * ((((4 ^ (j + 1) : ℕ) : ℝ)) - 1)))) ∧
    (∀ j : ℕ, ∀ v : ℝ, 0 ≤ v → v ≤ (N : ℝ) →
      v ≤ (S.card : ℝ) + ladderWindow N (N + 3) (S.card : ℝ) →
      ladderCost v N
        ≤ ladderCost (S.card : ℝ) N * (if v ≤ (S.card : ℝ) then 1 else 0)
          + ladderCost ((S.card : ℝ) + ladderWindow N 0 (S.card : ℝ)) N
              * (if (S.card : ℝ) < v then 1 else 0)
          + ∑ k ∈ Finset.range (N + 3),
              (if (S.card : ℝ) + ladderWindow N k (S.card : ℝ) < v
               then ladderCost ((S.card : ℝ) + ladderWindow N (k + 1) (S.card : ℝ)) N
               else 0)) ∧
    ((N : ℝ) ≤ ladderWindow N (N + 3) (S.card : ℝ)) ∧
    ((∑ z ∈ (Finset.univ : Finset (Fin (nextCor4RoughGrid N))) ×ˢ
        (Finset.univ : Finset (Fin (nextCor4RoughGrid N))),
      (firstProb hN S z.1) * (firstProb hN S z.2) *
        ladderCost (pairMin z) N)
      ≤ 6 * Real.sqrt ((S.card : ℝ) * (N : ℝ))) ∧

    (2 * (nextCor4RoughGrid N : ℝ) +
        (∑ z ∈ (Finset.univ : Finset (Fin (nextCor4RoughGrid N))) ×ˢ
          (Finset.univ : Finset (Fin (nextCor4RoughGrid N))),
          (firstProb hN S z.1) * (firstProb hN S z.2) *
            ladderCost (pairMin z) N)
      ≤ 650 * Real.sqrt ((S.card : ℝ) * (N : ℝ))) :=
  Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeReadoutRefined.clause94_endpoint hN S hcard hcardN hM₀ hM

theorem clause88_endpoint
    {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (hcard : 0 < (S.card : ℝ)) (hcardN : (S.card : ℝ) ≤ (N : ℝ) / 2)
    (c : ℝ) (hc : 1 ≤ c)
    (hω : ∀ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
      2 ≤ countRelFinalGrid c (basicApproxCountStop N ω))
    (hscale : ∀ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
      (2 / (5 * Real.pi)) * Real.sqrt ((N : ℝ) / (S.card : ℝ))
        ≤ (2 : ℝ) ^ basicApproxCountStop N ω) :

    (∀ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
      2 ≤ countRelFinalGrid c (basicApproxCountStop N ω)) ∧

    (∀ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
      ∀ y : Fin (countRelFinalGrid c (basicApproxCountStop N ω)),
        countRelGood hN S c ω y ↔
          |((countRelOutput c ω y : ℤ) : ℝ) - (S.card : ℝ)| < (S.card : ℝ) / c) ∧

    (∀ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
      ∀ y : Fin (countRelFinalGrid c (basicApproxCountStop N ω)),
        |(N : ℝ) * aeEstimate (countRelFinalGrid c (basicApproxCountStop N ω)) y
            - (S.card : ℝ)| ≤ 17 * ((S.card : ℝ) / c) / 64 →
          |((countRelOutput c ω y : ℤ) : ℝ) - (S.card : ℝ)| < (S.card : ℝ) / c) ∧

    (∀ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
      countRelWindow (countRelFinalGrid c (basicApproxCountStop N ω)) 17 N (S.card : ℝ)
        ≤ 17 * ((S.card : ℝ) / c) / 64) ∧

    (∀ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
      31 / 32 ≤ countRelFinalGood hN S c ω (hω ω)) ∧

    (S.card = 0 →
      ∀ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
        (countRelFinalLaw hN S c ω (hω ω)).prob ⟨0, by
          have hg := countRel_grid_two hc (basicApproxCountStop N ω)
          omega⟩ = 1 ∧
          countRelOutput c ω ⟨0, by
          have hg := countRel_grid_two hc (basicApproxCountStop N ω)
          omega⟩ = 0) ∧

    (3 / 4 : ℝ) ≤ ∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
      basicApproxCountPrefixWeight hN S ω *
        countRelFinalGood hN S c ω (countRel_grid_two hc (basicApproxCountStop N ω)) ∧

    ((119 * Real.pi / 2) * c * Real.sqrt ((N : ℝ) / (S.card : ℝ))
        ≤ ∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
          basicApproxCountPrefixWeight hN S ω *
            ((countRelTotalCost N c ω : ℕ) : ℝ)) ∧
    ((∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
          basicApproxCountPrefixWeight hN S ω *
            ((countRelTotalCost N c ω : ℕ) : ℝ))
        ≤ 34000 * c * Real.sqrt ((N : ℝ) / (S.card : ℝ))) ∧

    (∃ n : ℕ, n + 1 ≤ basicApproxCountLoopCap N ∧
      (∀ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
        countRelPrefixZero N n ω →
          (2 / (5 * Real.pi)) * Real.sqrt ((N : ℝ) / (S.card : ℝ))
            ≤ (2 : ℝ) ^ basicApproxCountStop N ω)) :=
  Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeReadoutRefined.clause93_endpoint hN S hcard hcardN c hc hω hscale

theorem clause86_endpoint
    {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (hcard : 1 ≤ (S.card : ℝ)) (hcardN : (S.card : ℝ) ≤ (N : ℝ) / 2)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hM₀ : 2 ≤ nextCor4RoughGrid N)
    (hM : ∀ z₁ z₂ : Fin (nextCor4RoughGrid N),
      2 ≤ nextCor4Grid N
        ((N : ℝ) * aeEstimate (nextCor4RoughGrid N) z₁)
        ((N : ℝ) * aeEstimate (nextCor4RoughGrid N) z₂))
    (hω : ∀ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
      2 ≤ basicApproxCountFinalM ε (basicApproxCountStop N ω))
    (θ : ℝ) (hθ0 : 0 < θ)
    (hangle : θ * Real.sqrt (N : ℝ) ≤ Real.pi / 2 * Real.sqrt (S.card : ℝ))
    (n : ℕ) (hn : n + 1 ≤ basicApproxCountLoopCap N)
    (hcross : (1 / 5 : ℝ) < (2 : ℝ) ^ (n + 1) * θ) :

    (1 ≤ nextApproxCountPrecision (S.card : ℝ) ε ∧
      (ε * (S.card : ℝ) < 1 → nextApproxCountPrecision (S.card : ℝ) ε = 1) ∧
      (1 ≤ ε * (S.card : ℝ) → 2 ≤ nextApproxCountPrecision (S.card : ℝ) ε)) ∧

    (((2 / 3 : ℝ) ≤
      ∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
        basicApproxCountPrefixWeight hN S ω *
          nextApproxCountRelGood hN S ε ω (hω ω)) ∧
    ((∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
        basicApproxCountPrefixWeight hN S ω *
          ((nextApproxCountRelCost ε ω : ℕ) : ℝ))
      ≤ 2000 * (1 / ε) * Real.sqrt ((N : ℝ) / (S.card : ℝ))) ∧
    (1 ≤ ε * (S.card : ℝ) →
      (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
        basicApproxCountPrefixWeight hN S ω *
          ((nextApproxCountRelCost ε ω : ℕ) : ℝ))
        ≤ 6000 * nextApproxCountScale (N : ℝ) (S.card : ℝ) ε)) ∧

    ((3 / 4 ≤ nextApproxCountExactSuccessMass hN S hM₀ hM) ∧
    (nextApproxCountExactCost hN S ≤ 650 * Real.sqrt ((S.card : ℝ) * (N : ℝ))) ∧
    (ε * (S.card : ℝ) < 1 →
      650 * Real.sqrt ((S.card : ℝ) * (N : ℝ))
        ≤ 1300 * nextApproxCountScale (N : ℝ) (S.card : ℝ) ε) ∧
    (ε * (N : ℝ) ≤ 1 / 3 →
      650 * Real.sqrt ((S.card : ℝ) * (N : ℝ))
        ≤ 1300 * nextApproxCountScale (N : ℝ) (S.card : ℝ) ε)) ∧

    ((S.card = 0 →
      (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
        basicApproxCountPrefixWeight hN S ω *
          nextApproxCountRelZero hN S ε ω (hω ω)) = 1) ∧
    (S.card = 0 →
      (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val),
        basicApproxCountPrefixWeight hN S ω *
          ((nextApproxCountRelCost ε ω : ℕ) : ℝ))
        = 2 * (2 : ℝ) ^ basicApproxCountLoopCap N - 2
          + (basicApproxCountFinalM ε (basicApproxCountLoopCap N) : ℝ))) ∧

    (Nat.clog 2 (N + 1) ≤ nextCor4OutputBits N ∧
      2 * nextCor4OutputBits N ≤ nextCor4SpaceBudget N) ∧

    ((∀ (L₁ L₂ : ℕ) (v : ℝ),
        (18 / 5) * Real.sqrt ((N : ℝ) / (S.card : ℝ)) ≤ (L₁ : ℝ) →
        (1 / 6) * Real.sqrt (((N : ℝ) - (S.card : ℝ)) / (ε * (N : ℝ))) ≤ (L₂ : ℝ) →
        (S.card : ℝ) / 2 ≤ v → v ≤ 3 * (S.card : ℝ) / 2 →
        nextCor4Window (nextApproxCountFinalGrid
            (nextApproxCountM (nextApproxCountM1 ε L₁ L₂) (nextCor4Grid N v v)))
            1 N (S.card : ℝ) ≤ ε * (S.card : ℝ) / 3 ∨
        nextCor4Window (nextApproxCountFinalGrid
            (nextApproxCountM (nextApproxCountM1 ε L₁ L₂) (nextCor4Grid N v v)))
            1 N (S.card : ℝ) < 1 / 2) ∧
     (∀ (ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2 * 2 ^ l.val)),
        CountRelNext.countRelPrefixZero N n ω →
        (18 / 5) * Real.sqrt ((N : ℝ) / (S.card : ℝ)) ≤ (nextApproxCountL1 ω : ℝ)) ∧
     (∀ (r₁ r₂ : ℝ),
        ((N : ℝ) - (S.card : ℝ)) / 4 ≤ r₁ →
        ((N : ℝ) - (S.card : ℝ)) / 4 ≤ r₂ →
        Real.sqrt (((N : ℝ) - (S.card : ℝ)) / (ε * (N : ℝ))) + 1
          ≤ (nextApproxCountL2 ε N r₁ r₂ : ℝ))) :=
  Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeReadoutRefined.clause91_endpoint hN S hcard hcardN ε hε hε1 hM₀ hM hω
    θ hθ0 hangle n hn hcross

theorem clause82_endpoint {N : ℕ} (hN : 0 < N) (M k : ℕ) (hM : 2 ≤ M) (z : Fin M)
    (S : Finset (Fin N)) :

    nextNativeOutputSpec M k z ∧

    nextNativeLayerSpec ∧

    nextNativeRecordSpec hN M k hM S ∧

    nextNativeAccessSpec hN M k hM z S ∧

    nextNativeResourceSpec hN M k hM S :=
  Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeReadoutRefined.clause23_endpoint hN M k hM z S

end SearchEstimationCore
end Qatlib.Papers.FixedPtSearch14.FixedPoint
