/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.StaticCBMDParameters
import Qatlib.Papers.Cbmd26.Algorithms.StaticComputationalFrame
import Qatlib.Papers.Cbmd26.Algorithms.StaticQueryBudget

/-!
# Static CBMD state preparation

This module assembles a static contour-based matrix decomposition circuit from an exact encoding
of `L + Complex.I • H`, with `L` positive semidefinite and `H` Hermitian. It combines sample
approximation, computational postselection, and randomized amplitude amplification for the
static setting of [WangEtAl2026].

## Main statements

* `staticCBMDWord`: the circuit querying the original matrix oracle.
* `static_cbmd_original_oracle_algorithm`: gives a heralded normalized-output algorithm with
  success probability at least `1/8` and explicit expected query bounds.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

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

/-- The static kernel index type at the analytic error budget `staticAnalyticBudget ε η`. -/
abbrev StaticCBMDIndex (α t ε η : ℝ) := StaticKernelIndex α t (staticAnalyticBudget ε η)
/-- The original-oracle static workspace for the chosen kernel index and the input
ancilla-system space `Anc × I`. -/
abbrev StaticCBMDSpace (Anc I : Type) (α t ε η : ℝ) :=
  OriginalStaticSpace (StaticCBMDIndex α t ε η) (Anc × I)

local instance cbmdStaticCBMDConsumerInstance1 (J : Type) [DecidableEq J] : DecidableEq (OriginalStaticLabels J) :=
  inferInstanceAs (DecidableEq (J × (Fin 4 × (Bool × (Bool × Bool)))))

variable {Anc I : Type} [Fintype Anc] [DecidableEq Anc] [Fintype I] [DecidableEq I]

/-- The decoded static CBMD word using the chosen kernel samples, normalized polynomial
approximation, and four-branch phase lists. -/
def staticCBMDWord (a₀ : Anc) (α t ε η : ℝ) (P : Polynomial ℂ)
    (base : Fin 4 → ℂ) (zs : Fin 4 → List ℂ) :
    List (AdjointStep (StaticCBMDSpace Anc I α t ε η)) :=
  originalStaticDecodedWord (tagFrame a₀ (1 : Matrix I I ℂ)) α
    (staticKernelNormalization α (staticAnalyticBudget ε η))
    (staticKernelFrequency α t (staticAnalyticBudget ε η))
    (staticKernelWeight α t (staticAnalyticBudget ε η))
    (staticKernelZero α t (staticAnalyticBudget ε η))
    (ComplexPolynomialSplit.branchDegrees (normalizedApproximation P (staticSampleBudget ε η / 2)))
    base zs

/-- The explicit source-query budget obtained from the dyadic approximation order at the chosen
static sample error and kernel normalization. -/
def staticCBMDQueryBudget (α t ε η : ℝ) : ℕ :=
  8 * (2 * dyadicOrder ((staticSampleBudget ε η / 2) /
    (2 * Real.exp (2 * |t * staticKernelNormalization α (staticAnalyticBudget ε η)|))) + 1)

/-- An exact encoding of the dissipative generator and a unitary input preparation yield a valid
static CBMD circuit with heralding probability at least `1/8` and explicit expected input
and data query bounds. Every supported successful branch returns an `ε`-accurate normalized
exponential output up to a unit-modulus phase. -/
theorem static_cbmd_original_oracle_algorithm
    (L H : Matrix I I ℂ) (hL : L.PosSemidef) (hH : H.IsHermitian)
    (U : Matrix (Anc × I) (Anc × I) ℂ) (a₀ : Anc) (α t ε η : ℝ)
    (henc : BlockEncoding (L + Complex.I • H) U
      (tagFrame a₀ (1 : Matrix I I ℂ)) (tagFrame a₀ (1 : Matrix I I ℂ)) α 0)
    (ht : 0 ≤ t) (hε : 0 < ε) (hεhalf : ε ≤ 1/2) (hη : 0 < η)
    (B : Matrix I I ℂ) (hB : B ∈ Matrix.unitaryGroup I ℂ)
    (i₀ : I) (ψ : QState I) (hprepare : ApplyGate B (Ket i₀) = ψ)
    (htarget : η ≤ ‖stateVector ((NormedSpace.exp (t • (-(L + Complex.I • H)))) *ᵥ ψ)‖) :
    let m := staticAmplificationWindow η
    ∃ hm : NeZero m,
    letI := hm
    ∃ (P : Polynomial ℂ) (base : Fin 4 → ℂ) (zs : Fin 4 → List ℂ),
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
          ENNReal.ofReal (((4 * staticMassBudget + 1) / η) * staticCBMDQueryBudget α t ε η) ∧
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
              ((star z) • y) ε) := by
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
  let δ := staticAnalyticBudget ε η
  let es := staticSampleBudget ε η
  let j₀ := staticKernelZero α t δ
  have hf := staticKernel_family H L hH hL henc.normalization_pos ht hb.1 hb.2.1
    (originalA_hermitian_part_norm_bound L H hL.isHermitian hH U _ α henc)
  have hwindow : 8 * coefficientMass (staticKernelWeight α t δ) / η ≤ (m : ℝ) :=
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        ((staticKernel_mass_le α t δ).trans (by unfold staticMassBudget; linarith))
        (by norm_num : (0:ℝ) ≤ 8)) hη.le).trans hw.2.1
  have hgap : es * coefficientMass (staticKernelWeight α t δ) + δ ≤ η/2 := by
    apply herror.trans
    nlinarith
  obtain ⟨P, base, zs, hcs, hA, hq, hsucc, hi, hd, hrun, hout⟩ :=
    originalA_static_decoded_amplified_target L H hL.isHermitian hH U
      (tagFrame a₀ (1 : Matrix I I ℂ)) α (staticKernelNormalization α δ) t es δ
      (staticKernelFrequency α t δ) henc hf.2.2.2.1 hb.2.2.1 hb.1.le hf.2.2.2.2.1
      (staticKernelWeight α t δ) j₀ hf.2.1
      (NormedSpace.exp (t • (-(L + Complex.I • H)))) hf.1
      (originalStaticInputLift B) (originalStaticInputLift_unitary B hB)
      (false,((j₀,0,false,false,false),(a₀,i₀))) (originalStaticSuccessEvent j₀ a₀)
      ψ hψ (originalStaticInputLift_prepare B j₀ a₀ i₀ ψ hprepare)
      (originalStaticDecodedFrame_rangeProjector j₀ a₀)
      η hη htarget hgap m hwindow
  refine ⟨hm, P, base, zs, hcs, hA, hq, hsucc, ?_, ?_, hrun, ?_⟩
  · exact hi.le.trans (ENNReal.ofReal_le_ofReal hw.2.2)
  · apply hd.le.trans
    apply ENNReal.ofReal_le_ofReal
    have hcount := (originalStaticDecodedWord_cost (tagFrame a₀ (1 : Matrix I I ℂ))
      α (staticKernelNormalization α δ) (staticKernelFrequency α t δ)
      (staticKernelWeight α t δ) j₀
      (ComplexPolynomialSplit.branchDegrees (normalizedApproximation P (es/2))) base zs).1
    rw [hcount] at hq
    have hqr : (2 * ∑ k, (zs k).length : ℕ) ≤ staticCBMDQueryBudget α t ε η := hq
    have hqrR : ((2 * ∑ k, (zs k).length : ℕ) : ℝ) ≤ (staticCBMDQueryBudget α t ε η : ℝ) :=
      Nat.cast_le.mpr hqr
    have hmean0 : 0 ≤ (4 * staticMassBudget + 1) / η :=
      div_nonneg (by linarith [staticMassBudget_ge_one]) hη.le
    exact mul_le_mul hw.2.2 hqrR (Nat.cast_nonneg _) hmean0
  · intro choice hs
    obtain ⟨y,z,hy,hz,hyn,happ⟩ := hout choice hs
    refine ⟨y,z,hy,hz,hyn,happ.1,happ.2.1,happ.2.2.trans ?_⟩
    apply (div_le_iff₀ (hη.trans_le htarget)).mpr
    have hεη := mul_le_mul_of_nonneg_left htarget hε.le
    change 2 * (staticSampleBudget ε η * coefficientMass
      (staticKernelWeight α t (staticAnalyticBudget ε η)) + staticAnalyticBudget ε η) ≤ _
    nlinarith only [herror, hεη, mul_nonneg hε.le hη.le]

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
