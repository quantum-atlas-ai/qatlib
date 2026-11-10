/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.DynamicFreshRegisterBridge
import Qatlib.Papers.Cbmd26.Algorithms.SelectedOracleWordBridge
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
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
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.CoherentSim.TaylorEncoding

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxSize 2048
noncomputable section
namespace CBMD
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
variable {F Anc J I : Type} [Fintype F] [DecidableEq F]
  [Fintype Anc] [DecidableEq Anc] [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]

local instance cbmdDynamicOuterWordBridgeInstance1 (Anc : Type) [DecidableEq Anc] : DecidableEq (DynamicSampleAnc Anc) :=
  inferInstanceAs (DecidableEq (Bool × (Bool × Anc)))
local instance cbmdDynamicOuterWordBridgeInstance2 (T : Type) [DecidableEq T] : DecidableEq (DynamicOriginalLabels T) :=
  inferInstanceAs (DecidableEq (T × (Bool × (Bool × Bool))))
local instance cbmdDynamicOuterWordBridgeInstance3 (J W : Type) [DecidableEq J] [DecidableEq W] :
    DecidableEq (DynamicSampleWorkspace J W) :=
  inferInstanceAs (DecidableEq (Bool × (J × (Bool × (Bool × W)))))
local instance cbmdDynamicOuterWordBridgeInstance4 (Anc J : Type) (K : ℕ) [DecidableEq Anc] [DecidableEq J] :
    DecidableEq (DynamicFreshStored Anc J K) :=
  inferInstanceAs (DecidableEq (TaylorWordLabel J K × FreshSignals (DynamicSampleAnc Anc) K))
local instance cbmdDynamicOuterWordBridgeInstance5 (F Anc J I : Type) (K : ℕ) [DecidableEq F] [DecidableEq Anc]
    [DecidableEq J] [DecidableEq I] : DecidableEq (DynamicFreshSpace F Anc J I K) :=
  inferInstanceAs (DecidableEq (F × (TaylorWordLabel J K ×
    (FreshSignals (DynamicSampleAnc Anc) K × (Bool × (J × (DynamicSampleAnc Anc × I)))))))

local instance cbmdDynamicOuterWordBridgeInstance6 (F Anc J I : Type) (K : ℕ) [DecidableEq F] [DecidableEq Anc]
    [DecidableEq J] [DecidableEq I] : DecidableEq (DynamicFreshFinalSpace F Anc J I K) :=
  inferInstanceAs (DecidableEq (Bool × ((DynamicOriginalLabels (DynamicFreshStored Anc J K) × F) × (J × (Anc × I)))))

def dynamicOuterOriginalWord (K : ℕ) (α Λ : ℝ) (s : F → ℝ)
    (c : F → ℂ) (f₀ : F)
    (cs : List (AdjointStep (TaylorWordLabel J K ×
      FreshQueryWorkspace (DynamicSampleAnc Anc) J I K))) :
    List (AdjointStep (DynamicFreshFinalSpace F Anc J I K)) :=
  dynamicTimeOriginalWord α Λ (fun fj : F × J => s fj.1)
    (dynamicFreshReindexedWord K (selectedCoefficientWord c f₀ cs))

theorem dynamicOuterOriginalWord_cost (K : ℕ) (α Λ : ℝ) (s : F → ℝ)
    (c : F → ℂ) (f₀ : F)
    (cs : List (AdjointStep (TaylorWordLabel J K ×
      FreshQueryWorkspace (DynamicSampleAnc Anc) J I K))) :
    adjointQueryCount (dynamicOuterOriginalWord K α Λ s c f₀ cs) = 2 * adjointQueryCount cs ∧
    adjointGateCount (dynamicOuterOriginalWord K α Λ s c f₀ cs) =
      adjointGateCount cs + 3 + 12 * adjointQueryCount cs := by
  obtain ⟨hq,hg⟩ := dynamicTimeOriginalWord_cost α Λ (fun fj : F × J => s fj.1)
    (dynamicFreshReindexedWord K (selectedCoefficientWord c f₀ cs))
  simpa only [dynamicOuterOriginalWord, (dynamicFreshReindexedWord_cost _ _).1,
    (dynamicFreshReindexedWord_cost _ _).2, (selectedCoefficientWord_cost _ _ _).1,
    (selectedCoefficientWord_cost _ _ _).2] using! And.intro hq hg

theorem dynamicOuterOriginalWord_blockEncoding (K : ℕ) (α Λ : ℝ) (s : F → ℝ)
    (hα : 0 < α) (hΛ : 0 < Λ) (hbound : ∀ f, α * Real.sqrt (1 + (s f)^2) ≤ Λ)
    (c : F → ℂ) (f₀ : F) (hmass : 0 < coefficientMass c)
    (j₀ : J) (a₀ : Anc) (ζ : ℝ)
    (U : J → Matrix (Anc × I) (Anc × I) ℂ)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup (Anc × I) ℂ)
    (cs : List (AdjointStep (TaylorWordLabel J K ×
      FreshQueryWorkspace (DynamicSampleAnc Anc) J I K)))
    (hcs : WellFormedAdjointCircuit cs) (A : F → Matrix I I ℂ)
    (henc : ∀ f, BlockEncoding (A f)
      (evaluate (parallelOracle (J := TaylorWordLabel J K)
        (freshPrimitiveQuery K (fun j =>
          (paddedFirstOrderInputUnitary (U j) α Λ (s f)).submatrix
            (sampleAncillaEquiv Anc I) (sampleAncillaEquiv Anc I)))) cs)
      (tagFrame (taylorEmptyLabel J K) (freshWordFrame j₀ (false,false,a₀) K))
      (tagFrame (taylorEmptyLabel J K) (freshWordFrame j₀ (false,false,a₀) K)) 1 ζ) :
    WellFormedAdjointCircuit (dynamicOuterOriginalWord K α Λ s c f₀ cs) ∧
    BlockEncoding (∑ f, c f • A f)
      (evaluate (controlOracle (parallelOracle
        (J := DynamicOriginalLabels (DynamicFreshStored Anc J K) × F) (select U)))
        (dynamicOuterOriginalWord K α Λ s c f₀ cs))
      (dynamicFreshFinalFrame (I := I) f₀ j₀ a₀ K)
      (dynamicFreshFinalFrame (I := I) f₀ j₀ a₀ K)
      (coefficientMass c) (ζ * coefficientMass c) ∧
    adjointQueryCount (dynamicOuterOriginalWord K α Λ s c f₀ cs) = 2 * adjointQueryCount cs ∧
    adjointGateCount (dynamicOuterOriginalWord K α Λ s c f₀ cs) =
      adjointGateCount cs + 3 + 12 * adjointQueryCount cs := by
  let V := fun f j => paddedFirstOrderInputUnitary (U j) α Λ (s f)
  let Q := fun f => parallelOracle (J := TaylorWordLabel J K)
    (freshPrimitiveQuery K (fun j => (V f j).submatrix
      (sampleAncillaEquiv Anc I) (sampleAncillaEquiv Anc I)))
  have hscale : scaledLCUCoefficients c (fun _ => (1 : ℝ)) = c := by
    funext f
    simp [scaledLCUCoefficients]
  obtain ⟨hw,he,_⟩ := selectedCoefficientWord_blockEncoding c f₀ Q cs hcs A
    (tagFrame (taylorEmptyLabel J K) (freshWordFrame j₀ (false,false,a₀) K))
    (fun _ => 1) (fun _ => ζ) henc (by simpa only [hscale] using! hmass)
  rw [hscale] at hw he
  simp only [mul_one] at he
  rw [← Finset.sum_mul] at he
  have hr := reindexWorkspace_blockEncoding (dynamicFreshWorkspaceEquiv F Anc J I K)
    _ _ _ _ _ he
  rw [← dynamicFreshReindexedWord_evaluate K V] at hr
  have hfinal := dynamicTimeOriginalWord_blockEncoding α Λ (fun fj : F × J => s fj.1)
    hα hΛ (fun fj => hbound fj.1) U hU
    (dynamicFreshReindexedWord K (selectedCoefficientWord c f₀ cs))
    (dynamicFreshReindexedWord_wellFormed K _ hw) _ _ _ _ hr
  refine ⟨hfinal.1, ?_, dynamicOuterOriginalWord_cost K α Λ s c f₀ cs⟩
  simpa only [dynamicOuterOriginalWord, dynamicFreshFinalFrame, coefficientMass,
    mul_comm ζ] using! hfinal.2.1

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
