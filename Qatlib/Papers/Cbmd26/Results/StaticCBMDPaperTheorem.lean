/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.StaticCBMDUniformConsumer
import Qatlib.Papers.Cbmd26.Algorithms.OutputNormEstimateBudget

/-!
# Static CBMD with output-norm query bounds

`StaticCBMDPaperResult` expresses the static algorithm's heralding, output accuracy, and
expected and pathwise query guarantees using the actual output norm. Uniform polynomial and
phase choices satisfy this result for admissible dissipative matrices and fixed-factor output
estimates in the static setting of [WangEtAl2026].

## Main statements

* `static_cbmd_paper_theorem4`: constructs uniform circuit parameters satisfying the paper-form
  static result.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

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

open Qatlib.Papers.Cbmd26.Algorithms.CBMD

namespace Qatlib.Papers.Cbmd26.Results

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace CBMD
open Matrix Polynomial
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal
local instance cbmdStaticCBMDPaperTheoremInstance1 (J : Type) [DecidableEq J] : DecidableEq (OriginalStaticLabels J) :=
  inferInstanceAs (DecidableEq (J × (Fin 4 × (Bool × (Bool × Bool)))))
variable {Anc I : Type} [Fintype Anc] [DecidableEq Anc] [Fintype I] [DecidableEq I]

/-- The static preparation specification combining circuit validity, heralding probability at
least `1/8`, expected and pathwise input and data query bounds in terms of the actual output
norm, and conditional normalized-output accuracy up to phase. -/
def StaticCBMDPaperResult (a₀ : Anc) (α t ε η c : ℝ) (P : Polynomial ℂ)
    (base : Fin 4 → ℂ) (zs : Fin 4 → List ℂ)
    (L H : Matrix I I ℂ) (U : Matrix (Anc × I) (Anc × I) ℂ)
    (B : Matrix I I ℂ) (i₀ : I) (ψ : QState I) : Prop :=
    let ν := ‖stateVector ((NormedSpace.exp (t • (-(L + Complex.I • H)))) *ᵥ ψ)‖
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
          ENNReal.ofReal (c * ((4 * staticMassBudget + 1) / ν)) ∧
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (randomizedAAHerald A hA zero S m)
          (fun x => (preparedDataQueries
            (countedAAWord (preparedTrial cs) zero S (aaRounds x.1)) : ℝ≥0∞)) ≤
          ENNReal.ofReal ((staticPaperQueryConstant * c * outputEstimateLogFactor c) * ((1 + α * t) / ν) * Real.log (2 / (ε * ν))) ∧
        (∀ choice : Bool × Fin m,
          (preparedInputQueries (countedAAWord (preparedTrial cs) zero S (aaRounds choice)) : ℝ) ≤
            4 * c * ((4 * staticMassBudget + 1) / ν) ∧
          (preparedDataQueries (countedAAWord (preparedTrial cs) zero S (aaRounds choice)) : ℝ) ≤
            4 * (staticPaperQueryConstant * c * outputEstimateLogFactor c) * ((1 + α * t) / ν) * Real.log (2 / (ε * ν))) ∧
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

/-- For the stated positive normalization and output estimate, nonnegative time, `0 < ε ≤ 1/2`,
and factor `c ≥ 1`, polynomial and phase data can be chosen uniformly so that every
admissible static instance satisfies `StaticCBMDPaperResult`. This is the static
specialization of [Wang et al., Theorem 4][WangEtAl2026]. -/
theorem static_cbmd_paper_theorem4
    (a₀ : Anc) (α t ε η c : ℝ) (hα : 0 < α) (ht : 0 ≤ t)
    (hε : 0 < ε) (hεhalf : ε ≤ 1/2) (hη : 0 < η) (hc : 1 ≤ c) :
    ∃ (P : Polynomial ℂ) (base : Fin 4 → ℂ) (zs : Fin 4 → List ℂ),
      ∀ (L H : Matrix I I ℂ) (U : Matrix (Anc × I) (Anc × I) ℂ),
      L.PosSemidef → H.IsHermitian →
      BlockEncoding (L + Complex.I • H) U
        (tagFrame a₀ (1 : Matrix I I ℂ)) (tagFrame a₀ (1 : Matrix I I ℂ)) α 0 →
      ∀ (B : Matrix I I ℂ), B ∈ Matrix.unitaryGroup I ℂ →
      ∀ (i₀ : I) (ψ : QState I), ApplyGate B (Ket i₀) = ψ →
      η ≤ ‖stateVector ((NormedSpace.exp (t • (-(L + Complex.I • H)))) *ᵥ ψ)‖ →
      ‖stateVector ((NormedSpace.exp (t • (-(L + Complex.I • H)))) *ᵥ ψ)‖ ≤ c * η →
      StaticCBMDPaperResult a₀ α t ε η c P base zs L H U B i₀ ψ := by
  obtain ⟨P,base,zs,hu⟩ := static_cbmd_uniform_original_oracle_algorithm (I := I)
    a₀ α t ε η hα ht hε hεhalf hη
  refine ⟨P,base,zs,?_⟩
  intro L H U hL hH henc B hB i₀ ψ hprepare htarget hupper
  have hψ : Normalized ψ := by
    rw [← hprepare]
    exact normalized_applyGate hB (normalized_ket i₀)
  let ν := ‖stateVector ((NormedSpace.exp (t • (-(L + Complex.I • H)))) *ᵥ ψ)‖
  have hν1 : ν ≤ 1 := by
    have he := stateVector_mulVec_norm_le (NormedSpace.exp (t • (-(L + Complex.I • H)))) ψ
    rw [(normalized_iff_stateVector_norm ψ).mp hψ, mul_one] at he
    exact he.trans (static_dissipative_target_norm_le_one L H hL hH t ht)
  have hε1 : ε ≤ 1 := by linarith
  have hinput : (4 * staticMassBudget + 1) / η ≤ c * ((4 * staticMassBudget + 1) / ν) :=
    (output_estimate_envelope_bound hη htarget hupper (by linarith [staticMassBudget_ge_one])).2
  have hdata : staticPaperQueryConstant * ((1 + α*t)/η) * Real.log (2/(ε*η)) ≤
      (staticPaperQueryConstant * c * outputEstimateLogFactor c) *
        ((1 + α*t)/ν) * Real.log (2/(ε*ν)) :=
    static_true_output_query_bound hα.le ht hε hε1 hη htarget hupper hc hν1
  obtain ⟨hm,hcs,hA,hq,hsucc,hi,hd,hpaths,hrun,hout⟩ :=
      hu L H U hL hH henc B hB i₀ ψ hprepare htarget
  letI := hm
  refine ⟨hm,hcs,hA,hq,hsucc,hi.trans (ENNReal.ofReal_le_ofReal hinput),
    hd.trans (ENNReal.ofReal_le_ofReal hdata),?_,hrun,hout⟩
  intro choice
  constructor
  · apply (hpaths choice).1.trans
    calc
      _ = 4 * ((4 * staticMassBudget + 1) / η) := by ring
      _ ≤ 4 * (c * ((4 * staticMassBudget + 1) / ν)) :=
        mul_le_mul_of_nonneg_left hinput (by norm_num)
      _ = _ := by ring
  · apply (hpaths choice).2.trans
    calc
      _ = 4 * (staticPaperQueryConstant * ((1 + α*t)/η) * Real.log (2/(ε*η))) := by ring
      _ ≤ 4 * ((staticPaperQueryConstant * c * outputEstimateLogFactor c) *
        ((1 + α*t)/ν) * Real.log (2/(ε*ν))) := mul_le_mul_of_nonneg_left hdata (by norm_num)
      _ = _ := by ring

end CBMD

end
end Qatlib.Papers.Cbmd26.Results
