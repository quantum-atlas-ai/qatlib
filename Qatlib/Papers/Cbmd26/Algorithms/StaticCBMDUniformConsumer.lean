/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.StaticCBMDConsumer
import Qatlib.Papers.Cbmd26.Algorithms.OriginalAStaticUniformOuter
import Qatlib.Papers.Cbmd26.Algorithms.StaticFinalQueryBudget
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.SignalPrimitive.HermitianQSVT
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace CBMD
open Matrix Polynomial
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

local instance cbmdStaticCBMDUniformConsumerInstance1 (J : Type) [DecidableEq J] : DecidableEq (OriginalStaticLabels J) :=
  inferInstanceAs (DecidableEq (J × (Fin 4 × (Bool × (Bool × Bool)))))

variable {Anc I : Type} [Fintype Anc] [DecidableEq Anc] [Fintype I] [DecidableEq I]

def StaticCBMDResult (a₀ : Anc) (α t ε η : ℝ) (P : Polynomial ℂ)
    (base : Fin 4 → ℂ) (zs : Fin 4 → List ℂ)
    (L H : Matrix I I ℂ) (U : Matrix (Anc × I) (Anc × I) ℂ)
    (B : Matrix I I ℂ) (i₀ : I) (ψ : QState I) : Prop :=
    let m := staticAmplificationWindow η
    ∃ hm : NeZero m,
    letI := hm
      let cs := staticCBMDWord (I := I) a₀ α t ε η P base zs
      let O :=
          controlOracle (parallelOracle (J := OriginalStaticLabels (StaticCBMDIndex α t ε η)) U)
      let Bin := originalStaticInputLift (J := StaticCBMDIndex α t ε η) B
      let j₀ := staticKernelZero α t (staticAnalyticBudget ε η)
      let zero : StaticCBMDSpace Anc I α t ε η := (false,((j₀,0,false,false,false),(a₀,i₀)))
      let S := originalStaticSuccessEvent (I := I) j₀ a₀
      let A := evaluate O cs * Bin
      ∃ (_hcs : WellFormedAdjointCircuit cs) (hA : A ∈ Matrix.unitaryGroup (StaticCBMDSpace Anc I α t ε η) ℂ),
        adjointQueryCount cs ≤ staticCBMDQueryBudget α t ε η ∧
        ENNReal.ofReal (1/8 : ℝ) ≤
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (randomizedAAHerald A hA zero S m) (fun x => x.2 = true) ∧
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (randomizedAAHerald A hA zero S m)
          (fun x => (preparedInputQueries
            (countedAAWord (preparedTrial cs) zero S (aaRounds x.1)) : ℝ≥0∞)) ≤
          ENNReal.ofReal ((4 * staticMassBudget + 1) / η) ∧
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (randomizedAAHerald A hA zero S m)
          (fun x => (preparedDataQueries
            (countedAAWord (preparedTrial cs) zero S (aaRounds x.1)) : ℝ≥0∞)) ≤
          ENNReal.ofReal (staticPaperQueryConstant * ((1 + α * t) / η) * Real.log (2 / (ε * η))) ∧
        (∀ choice : Bool × Fin m,
          (preparedInputQueries (countedAAWord (preparedTrial cs) zero S (aaRounds choice)) : ℝ) ≤
            4 * (4 * staticMassBudget + 1) / η ∧
          (preparedDataQueries (countedAAWord (preparedTrial cs) zero S (aaRounds choice)) : ℝ) ≤
            4 * staticPaperQueryConstant * ((1 + α * t) / η) * Real.log (2 / (ε * η))) ∧
        (∀ k, PreparedCircuitValid (countedAAWord (preparedTrial cs) zero S k) ∧
          ApplyGate (evaluatePrepared O Bin (countedAAWord (preparedTrial cs) zero S k)) (Ket zero) =
            Run (preparedMark S) (preparedAACircuit A zero k) (Ket zero)) ∧
        (∀ choice : Bool × Fin m,
          (choice, true) ∈ (randomizedAAHerald A hA zero S m).support →
          ∃ (y : QState I) (z : ℂ),
            ConditionalState ((originalStaticDecodedFrame (tagFrame a₀ (1 : Matrix I I ℂ)) j₀)ᴴ *ᵥ
              Run (preparedMark S) (preparedAACircuit A zero (aaRounds choice)) (Ket zero)) = some y ∧
            ‖z‖ = 1 ∧ Normalized y ∧
            IsNormalizedApplication (NormedSpace.exp (t • (-(L + Complex.I • H)))) ψ
              ((star z) • y) ε)

theorem static_cbmd_uniform_original_oracle_algorithm
    (a₀ : Anc) (α t ε η : ℝ) (hα : 0 < α) (ht : 0 ≤ t)
    (hε : 0 < ε) (hεhalf : ε ≤ 1/2) (hη : 0 < η) :
    ∃ (P : Polynomial ℂ) (base : Fin 4 → ℂ) (zs : Fin 4 → List ℂ),
      ∀ (L H : Matrix I I ℂ) (U : Matrix (Anc × I) (Anc × I) ℂ),
      L.PosSemidef → H.IsHermitian →
      BlockEncoding (L + Complex.I • H) U
        (tagFrame a₀ (1 : Matrix I I ℂ)) (tagFrame a₀ (1 : Matrix I I ℂ)) α 0 →
      ∀ (B : Matrix I I ℂ), B ∈ Matrix.unitaryGroup I ℂ →
      ∀ (i₀ : I) (ψ : QState I), ApplyGate B (Ket i₀) = ψ →
      η ≤ ‖stateVector ((NormedSpace.exp (t • (-(L + Complex.I • H)))) *ᵥ ψ)‖ →
      StaticCBMDResult a₀ α t ε η P base zs L H U B i₀ ψ := by
  let δ := staticAnalyticBudget ε η
  let es := staticSampleBudget ε η
  let j₀ := staticKernelZero α t δ
  let R := tagFrame a₀ (1 : Matrix I I ℂ)
  have hR : IsIsometry R := tagFrame_isIsometry a₀ _ (by simp [IsIsometry])
  have hes : 0 < es := by
    dsimp [es, staticSampleBudget]
    have := staticMassBudget_ge_one
    positivity
  obtain ⟨P,base,zs,_,_,hu⟩ := originalA_static_uniform_outer R hR α
    (staticKernelNormalization α δ) t es (staticKernelFrequency α t δ)
    (staticKernelNormalization_pos hα δ) hes (staticKernel_normalization_bound hα t δ)
    (staticKernelWeight α t δ) j₀ (staticKernel_mass_pos α t δ)
  refine ⟨P,base,zs,?_⟩
  intro L H U hL hH henc B hB i₀ ψ hprepare htarget
  have hψ : Normalized ψ := by
    rw [← hprepare]
    exact normalized_applyGate hB (normalized_ket i₀)
  have hη1 : η ≤ 1 := by
    have he := stateVector_mulVec_norm_le (NormedSpace.exp (t • (-(L + Complex.I • H)))) ψ
    rw [(normalized_iff_stateVector_norm ψ).mp hψ, mul_one] at he
    exact htarget.trans (he.trans (static_dissipative_target_norm_le_one L H hL hH t ht))
  have hε1 : ε ≤ 1 := by linarith
  have hb := static_chosen_error_budgets ε η hε hε1 hη hη1
  have herror := static_chosen_total_error α t ε η hε hε1 hη hη1
  have hw := static_chosen_window η hη hη1
  let m := staticAmplificationWindow η
  have hm : NeZero m := ⟨hw.1.ne'⟩
  letI := hm
  let cs := staticCBMDWord (I := I) a₀ α t ε η P base zs
  let O := controlOracle (parallelOracle (J := OriginalStaticLabels (StaticCBMDIndex α t ε η)) U)
  let Bin := originalStaticInputLift (J := StaticCBMDIndex α t ε η) (Anc := Anc) B
  let F := originalStaticDecodedFrame R j₀
  let zero : StaticCBMDSpace Anc I α t ε η := (false,((j₀,0,false,false,false),(a₀,i₀)))
  let S := originalStaticSuccessEvent (I := I) j₀ a₀
  let target := NormedSpace.exp (t • (-(L + Complex.I • H)))
  obtain ⟨hw₀,he₀,hq₀⟩ := hu L H U hL.isHermitian hH henc
  have hcs : WellFormedAdjointCircuit cs :=
    basisConvertedWord_wellFormed originalStaticAveragePrepare originalStaticAveragePrepare_unitary _ hw₀
  have hdecoded := originalStaticDecodedWord_blockEncoding U R hR α
    (staticKernelNormalization α δ) (staticKernelFrequency α t δ) (staticKernelWeight α t δ) j₀
    (ComplexPolynomialSplit.branchDegrees (normalizedApproximation P (es/2))) base zs _ _ _ he₀
  have hf := staticKernel_target_error H L hH hL
    (originalA_hermitian_part_norm_bound L H hL.isHermitian hH U R α henc) ht hb.1 hb.2.1
  have he : BlockEncoding target (evaluate O cs) F F
      (4 * coefficientMass (staticKernelWeight α t δ))
      (es * coefficientMass (staticKernelWeight α t δ) + δ) := hdecoded.perturb hb.1.le hf
  have hq : adjointQueryCount cs ≤ staticCBMDQueryBudget α t ε η := by
    simpa only [cs, staticCBMDWord, originalStaticDecodedWord,
      (basisConvertedWord_cost _ _).1] using! hq₀
  have hO : O ∈ Matrix.unitaryGroup (StaticCBMDSpace Anc I α t ε η) ℂ :=
    controlOracle_unitary (parallelOracle_unitary henc.unitary)
  have hBin : Bin ∈ Matrix.unitaryGroup (StaticCBMDSpace Anc I α t ε η) ℂ :=
    originalStaticInputLift_unitary B hB
  have hinit : ApplyGate Bin (Ket zero) = F *ᵥ ψ :=
    originalStaticInputLift_prepare B j₀ a₀ i₀ ψ hprepare
  have hproj : rangeProjector F = Projector S := originalStaticDecodedFrame_rangeProjector j₀ a₀
  have hwindow : 2 * (4 * coefficientMass (staticKernelWeight α t δ)) / η ≤ (m : ℝ) := by
    have hmass : coefficientMass (staticKernelWeight α t δ) ≤ staticMassBudget :=
      (staticKernel_mass_le α t δ).trans (by unfold staticMassBudget; linarith)
    have hmass' := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmass (by norm_num : (0:ℝ) ≤ 8)) hη.le
    calc
      _ = 8 * coefficientMass (staticKernelWeight α t δ) / η := by ring
      _ ≤ 8 * staticMassBudget / η := hmass'
      _ ≤ (m : ℝ) := hw.2.1
  have hgap : es * coefficientMass (staticKernelWeight α t δ) + δ ≤ η/2 := by
    apply herror.trans
    nlinarith only [hεhalf, hη.le, mul_nonneg hε.le hη.le]
  have haa := counted_blockEncoding_randomized_amplification target O Bin cs hO hBin hcs
    F F _ _ η he zero S ψ hψ hinit hproj hη htarget hgap m hwindow
  simp only [evaluate_preparedTrial] at haa
  have hA : evaluate O cs * Bin ∈ Matrix.unitaryGroup (StaticCBMDSpace Anc I α t ε η) ℂ :=
    (Matrix.unitaryGroup _ ℂ).mul_mem he.unitary hBin
  have hqR : (adjointQueryCount cs : ℝ) ≤ (staticCBMDQueryBudget α t ε η : ℝ) := Nat.cast_le.mpr hq
  have hmean0 : 0 ≤ (4 * staticMassBudget + 1) / η :=
    div_nonneg (by linarith [staticMassBudget_ge_one]) hη.le
  have henvelope : ((4 * staticMassBudget + 1) / η) * (staticCBMDQueryBudget α t ε η : ℝ) ≤
      staticPaperQueryConstant * ((1 + α*t)/η) * Real.log (2/(ε*η)) :=
    staticChosen_query_envelope_bound α t ε η hα.le ht hε hε1 hη hη1
  have htotal : (((m : ℝ)+1)/2) * (adjointQueryCount cs : ℝ) ≤
      staticPaperQueryConstant * ((1 + α*t)/η) * Real.log (2/(ε*η)) :=
    (mul_le_mul hw.2.2 hqR (Nat.cast_nonneg _) hmean0).trans henvelope
  refine ⟨hm,hcs,hA,hq,haa.1,haa.2.1.le.trans (ENNReal.ofReal_le_ofReal hw.2.2),
    haa.2.2.1.le.trans (ENNReal.ofReal_le_ofReal htotal),?_,haa.2.2.2.1,?_⟩
  · intro choice
    obtain ⟨hi,hd⟩ := randomizedAA_path_budget cs zero S m choice
    have hm1 : 1 ≤ 2*m := by have := hw.1; change 0 < m at this; omega
    have hworst : ((2*m-1 : ℕ) : ℝ) ≤ 4 * (((m:ℝ)+1)/2) := by
      rw [Nat.cast_sub hm1, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
      linarith
    constructor
    · calc
        _ ≤ ((2*m-1 : ℕ) : ℝ) := Nat.cast_le.mpr hi
        _ ≤ 4 * (((m:ℝ)+1)/2) := hworst
        _ ≤ 4 * ((4*staticMassBudget+1)/η) := mul_le_mul_of_nonneg_left hw.2.2 (by norm_num)
        _ = _ := by ring
    · have hdR : (preparedDataQueries (countedAAWord (preparedTrial cs) zero S (aaRounds choice)) : ℝ) ≤
          ((2*m-1 : ℕ) : ℝ) * (adjointQueryCount cs : ℝ) := by
        simpa only [Nat.cast_mul] using! (Nat.cast_le (α := ℝ)).mpr hd
      calc
        _ ≤ ((2*m-1 : ℕ) : ℝ) * (adjointQueryCount cs : ℝ) := hdR
        _ ≤ (4 * (((m:ℝ)+1)/2)) * (adjointQueryCount cs : ℝ) :=
          mul_le_mul_of_nonneg_right hworst (Nat.cast_nonneg _)
        _ = 4 * ((((m:ℝ)+1)/2) * (adjointQueryCount cs : ℝ)) := by ring
        _ ≤ 4 * (staticPaperQueryConstant * ((1+α*t)/η) * Real.log (2/(ε*η))) :=
          mul_le_mul_of_nonneg_left htotal (by norm_num)
        _ = _ := by ring
  · intro choice hs
    obtain ⟨y,z,hy,hz,hyn,happ⟩ := blockEncoding_randomized_supported_output target (evaluate O cs)
      Bin F F _ _ he hBin zero S ψ hψ hinit hproj (by linarith) m choice hs
    refine ⟨y,z,hy,hz,hyn,happ.1,happ.2.1,happ.2.2.trans ?_⟩
    apply (div_le_iff₀ (hη.trans_le htarget)).mpr
    have hεη := mul_le_mul_of_nonneg_left htarget hε.le
    change 2 * (staticSampleBudget ε η * coefficientMass
      (staticKernelWeight α t (staticAnalyticBudget ε η)) + staticAnalyticBudget ε η) ≤ _
    nlinarith only [herror, hεη, mul_nonneg hε.le hη.le]

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
