/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.DynamicOriginalGridConsumer
import Qatlib.Papers.Cbmd26.Algorithms.DynamicKernelGridTarget
import Qatlib.Papers.Cbmd26.Algorithms.ComputationalAmplificationBridge
import Qatlib.Papers.Cbmd26.Algorithms.DynamicHalfAccuracyBudget

/-!
# Dynamic CBMD from the original matrix oracle

Specializes the dynamic grid construction to the kernel frequencies, simulation accuracy, and
degree chosen by the CBMD budgets. It defines `dynamicCBMDWord` and `dynamicCBMDSource`, then
combines the grid approximation with computational amplitude amplification in
`dynamic_cbmd_original_oracle_algorithm`. These results support the contour-based algorithms of
[WangEtAl2026].

## Main statements

* `dynamicCBMDWord`: fixes the compiled original-oracle word at the chosen parameters.
* `dynamic_cbmd_original_oracle_algorithm`: proves amplification and the displayed data-query
  bound.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.InteractionEvo.DysonGrid
open Qatlib.Concepts.InteractionEvo.MeanDerivGrid.DysonMeanDerivativeGrid
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.SharedAncilla.AncillaProduct
open Qatlib.Concepts.SignalPrimitive.HermitianQSVT
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.LchsSimulation.TimeOrdered
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.CoherentSim.TaylorEncoding

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option synthInstance.maxSize 2048
noncomputable section
namespace CBMD
open Matrix Set
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal
set_option warningAsError false

/-- Abbreviates the static kernel index type at the chosen analytic budget. -/
abbrev DynamicCBMDFrequency (α T ε η : ℝ) := StaticKernelIndex α T (staticAnalyticBudget ε η)
/-- Abbreviates the dynamic grid time-address type at the chosen kernel normalization and
simulation accuracy. -/
abbrev DynamicCBMDTime (α T : ℝ) (N : ℕ) (ε η : ℝ) :=
  DynamicGridTimeIndex (staticKernelNormalization α (staticAnalyticBudget ε η)) T N
    (dynamicSimulationAccuracy ε η)
/-- Defines the dynamic grid polynomial degree at the chosen kernel normalization and simulation
accuracy. -/
def dynamicCBMDDegree (α T ε η : ℝ) : ℕ :=
  dynamicGridDegree (staticKernelNormalization α (staticAnalyticBudget ε η)) T
    (dynamicSimulationAccuracy ε η)
/-- Abbreviates the final fresh-register workspace for the chosen frequency, time-address, and
degree parameters. -/
abbrev DynamicCBMDSpace (Anc I : Type) (α T : ℝ) (N : ℕ) (ε η : ℝ) :=
  DynamicFreshFinalSpace (DynamicCBMDFrequency α T ε η) Anc (DynamicCBMDTime α T N ε η) I
    (dynamicCBMDDegree α T ε η)
/-- Abbreviates the auxiliary-register type for the chosen dynamic CBMD parameters. -/
abbrev DynamicCBMDAux (Anc : Type) (α T : ℝ) (N : ℕ) (ε η : ℝ) :=
  DynamicFreshAux (DynamicCBMDFrequency α T ε η) Anc (DynamicCBMDTime α T N ε η)
    (dynamicCBMDDegree α T ε η)

variable {Anc I : Type} [Fintype Anc] [DecidableEq Anc] [Fintype I] [DecidableEq I]
local instance cbmdDynamicCBMDConsumerInstance1 (Anc : Type) [DecidableEq Anc] : DecidableEq (DynamicSampleAnc Anc) :=
  inferInstanceAs (DecidableEq (Bool × (Bool × Anc)))
local instance cbmdDynamicCBMDConsumerInstance2 (T : Type) [DecidableEq T] : DecidableEq (DynamicOriginalLabels T) :=
  inferInstanceAs (DecidableEq (T × (Bool × (Bool × Bool))))
local instance cbmdDynamicCBMDConsumerInstance3 (Anc J : Type) (K : ℕ) [DecidableEq Anc] [DecidableEq J] :
    DecidableEq (DynamicFreshStored Anc J K) :=
  inferInstanceAs (DecidableEq (TaylorWordLabel J K × FreshSignals (DynamicSampleAnc Anc) K))
local instance cbmdDynamicCBMDConsumerInstance4 (F Anc J I : Type) (K : ℕ) [DecidableEq F] [DecidableEq Anc]
    [DecidableEq J] [DecidableEq I] : DecidableEq (DynamicFreshFinalSpace F Anc J I K) :=
  inferInstanceAs (DecidableEq (Bool × ((DynamicOriginalLabels (DynamicFreshStored Anc J K) × F) × (J × (Anc × I)))))
local instance cbmdDynamicCBMDConsumerInstance5 (F Anc J : Type) (K : ℕ) [DecidableEq F] [DecidableEq Anc]
    [DecidableEq J] : DecidableEq (DynamicFreshAux F Anc J K) :=
  inferInstanceAs (DecidableEq (Bool × ((DynamicOriginalLabels (DynamicFreshStored Anc J K) × F) × (J × Anc))))

/-- Instantiates the original-oracle dynamic grid word with the chosen kernel weights,
frequencies, normalization, and simulation accuracy. -/
def dynamicCBMDWord (a₀ : Anc) (α T : ℝ) (N : ℕ) (ε η : ℝ) :
    List (AdjointStep (DynamicCBMDSpace Anc I α T N ε η)) :=
  dynamicOriginalGridWord a₀ α (staticKernelNormalization α (staticAnalyticBudget ε η)) T N
    (dynamicSimulationAccuracy ε η) (staticKernelFrequency α T (staticAnalyticBudget ε η))
    (staticKernelWeight α T (staticAnalyticBudget ε η))
    (staticKernelZero α T (staticAnalyticBudget ε η))

/-- Defines the controlled original-oracle source selected at the fine-grid times and lifted
across the dynamic CBMD labels. -/
def dynamicCBMDSource (U : ℝ → Matrix (Anc × I) (Anc × I) ℂ)
    (τ : ℕ → ℝ) (α T : ℝ) (N : ℕ) (ε η : ℝ) :
    Matrix (DynamicCBMDSpace Anc I α T N ε η) (DynamicCBMDSpace Anc I α T N ε η) ℂ :=
  controlOracle (parallelOracle
    (J := DynamicOriginalLabels (DynamicFreshStored Anc (DynamicCBMDTime α T N ε η)
      (dynamicCBMDDegree α T ε η)) × DynamicCBMDFrequency α T ε η)
    (select (dynamicFineTimeOracle U τ (staticKernelNormalization α (staticAnalyticBudget ε η))
      T N (dynamicSimulationAccuracy ε η))))

/-- Separates the dynamic CBMD workspace into its auxiliary registers and system register. -/
def dynamicCBMDEquiv (Anc I : Type) (α T : ℝ) (N : ℕ) (ε η : ℝ) :
    DynamicCBMDSpace Anc I α T N ε η ≃ DynamicCBMDAux Anc α T N ε η × I :=
  dynamicFreshFinalEquiv _ _ _ _ _

/-- Defines the clean auxiliary basis label using the kernel zero, zero time address, and
initial ancilla. -/
def dynamicCBMDCleanAux (a₀ : Anc) (α T : ℝ) (N : ℕ) (ε η : ℝ) :
    DynamicCBMDAux Anc α T N ε η :=
  dynamicFreshCleanAux (staticKernelZero α T (staticAnalyticBudget ε η))
    (dynamicGridZeroAddress (staticKernelNormalization α (staticAnalyticBudget ε η)) T N
      (dynamicSimulationAccuracy ε η)) a₀ (dynamicCBMDDegree α T ε η)

/-- Defines the displayed dynamic query bound from `α * T`, the output estimate, and two
logarithmic accuracy factors. -/
def dynamicCBMDQueryBound (α T ε η : ℝ) : ℝ :=
  (18 * dynamicPaperQueryConstant) * ((1 + α * T) / η) * Real.log (2 / (ε * η)) *
    (Real.log (2 + α * T) + Real.log (2 / (ε * η)))

/-- Under exact original-oracle encodings and the weighted grid-error bound, proves
computational amplification of the dissipative evolution, the exact data-query count, and
its displayed bound [WangEtAl2026]. -/
theorem dynamic_cbmd_original_oracle_algorithm
    (a₀ : Anc) (α T ε η : ℝ) (hα : 0 < α) (hT : 0 < T)
    (hε : 0 < ε) (hεhalf : ε ≤ 1/2) (hη : 0 < η)
    (τ : ℕ → ℝ) (N : ℕ) (hτ : Monotone τ) (hτ0 : τ 0 = 0) (hτN : τ N = T)
    (L H : ℝ → Matrix I I ℂ)
    (P : _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.FinitePiecewiseContinuousOn (fun u => (H u,L u)) 0 T)
    (hL : ∀ t ∈ Icc 0 T, (L t).PosSemidef)
    (hH : ∀ t ∈ Icc 0 T, (H t).IsHermitian)
    (U : ℝ → Matrix (Anc × I) (Anc × I) ℂ)
    (henc : ∀ t ∈ Icc 0 T, BlockEncoding (L t + Complex.I • H t) (U t)
      (tagFrame a₀ (1 : Matrix I I ℂ)) (tagFrame a₀ (1 : Matrix I I ℂ)) α 0)
    (hgrid : (∑ j, ‖staticKernelWeight α T (staticAnalyticBudget ε η) j‖ *
      ‖dynamicKernelSample P α (staticAnalyticBudget ε η) j -
        dynamicSuppliedGridSample H L τ N α T (staticAnalyticBudget ε η) j‖) ≤ ε * η / 16)
    (B : Matrix I I ℂ) (hB : B ∈ Matrix.unitaryGroup I ℂ)
    (i₀ : I) (ψ : QState I) (hprepare : ApplyGate B (Ket i₀) = ψ)
    (htarget : η ≤ ‖stateVector (P.evolution (-Complex.I) T *ᵥ ψ)‖) :
    ComputationalAmplificationResult (dynamicCBMDEquiv Anc I α T N ε η)
      (dynamicCBMDCleanAux a₀ α T N ε η) (dynamicCBMDSource U τ α T N ε η)
      (dynamicCBMDWord (I := I) a₀ α T N ε η) B i₀ ψ (P.evolution (-Complex.I) T) ε η ∧
    adjointQueryCount (dynamicCBMDWord (I := I) a₀ α T N ε η) =
      6 * dynamicSegmentCount (staticKernelNormalization α (staticAnalyticBudget ε η)) T *
        dynamicCBMDDegree α T ε η ∧
    ((4 * staticMassBudget + 1) / η) *
      (adjointQueryCount (dynamicCBMDWord (I := I) a₀ α T N ε η) : ℝ) ≤
        dynamicCBMDQueryBound α T ε η := by
  let δ := staticAnalyticBudget ε η
  let ζ := dynamicSimulationAccuracy ε η
  let Λ := staticKernelNormalization α δ
  have hψ : Normalized ψ := by
    rw [← hprepare]
    exact normalized_applyGate hB (normalized_ket i₀)
  have hη1 : η ≤ 1 := by
    have hv := stateVector_mulVec_norm_le (P.evolution (-Complex.I) T) ψ
    rw [(normalized_iff_stateVector_norm ψ).mp hψ, mul_one] at hv
    exact htarget.trans (hv.trans (dynamicKernel_target_contraction P hH hL))
  have hε1 : ε ≤ 1 := by linarith
  have hz := dynamicSimulationAccuracy_bounds hε hε1 hη hη1
  have ho := dynamic_original_grid_lcu a₀ α Λ T N ζ hα (staticKernelNormalization_pos hα δ)
    hT hz.1 hz.2.1 τ hτ hτ0 hτN (staticKernelFrequency α T δ)
    (staticKernel_normalization_bound hα T δ) (staticKernelWeight α T δ)
    (staticKernelZero α T δ) (staticKernel_mass_pos α T δ)
    L H (fun t ht => (hL t ht).isHermitian) hH U henc
  (try dsimp only at ho)
  have hnorm : ∀ t ∈ Icc 0 T, ‖L t + Complex.I • H t‖ ≤ α :=
    fun t ht => exact_blockEncoding_norm_bound _ _ _ _ (henc t ht)
  have htgt := dynamicSuppliedGrid_chosen_target_error P τ N hT.le hH hL hnorm
    hε hε1 hη hη1 hgrid
  have he := ho.2.2.1.perturb
    (show 0 ≤ δ + ε*η/16 by dsimp [δ,staticAnalyticBudget]; positivity) htgt
  rw [dynamicFreshFinalFrame_computational] at he
  have hmass : coefficientMass (staticKernelWeight α T δ) ≤ 4 * staticMassBudget := by
    have hm := staticKernel_mass_le α T δ
    have hC := staticMassBudget_ge_one
    unfold staticMassBudget at *
    linarith
  have herr : ζ * coefficientMass (staticKernelWeight α T δ) + (δ + ε*η/16) ≤ ε*η/4 := by
    have hb := dynamicKernel_grid_simulation_budget α T ε η hε hε1 hη hη1
    change ζ * coefficientMass (staticKernelWeight α T δ) + δ + ε*η/16 ≤ ε*η/4 at hb
    linarith only [hb]
  have haa := computational_amplification (dynamicCBMDEquiv Anc I α T N ε η)
    (dynamicCBMDCleanAux a₀ α T N ε η) (dynamicCBMDSource U τ α T N ε η)
    (dynamicCBMDWord (I := I) a₀ α T N ε η) B ho.2.1 ho.1 hB i₀ ψ hprepare
    (P.evolution (-Complex.I) T) _ _ ε η he hmass hε hε1 hη hη1 htarget herr
  have hcount : adjointQueryCount (dynamicCBMDWord (I := I) a₀ α T N ε η) =
      6 * dynamicSegmentCount (staticKernelNormalization α (staticAnalyticBudget ε η)) T *
        dynamicCBMDDegree α T ε η := ho.2.2.2.1
  refine ⟨haa,hcount,?_⟩
  rw [hcount]
  have hq := dynamicHalfAccuracy_amplified_query_bound hα.le hT.le hε hε1 hη hη1
    (by norm_num : (0 : ℝ) ≤ 6)
  (try dsimp only at hq)
  convert! hq using 1 <;> simp only [dynamicCBMDQueryBound, dynamicCBMDDegree,
    dynamicGridDegree, Nat.cast_mul, Nat.cast_ofNat] <;> ring

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
