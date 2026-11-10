/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.DynamicOuterWordBridge
import Qatlib.Papers.Cbmd26.Algorithms.DynamicSampleInputBridge
import Qatlib.Papers.Cbmd26.Algorithms.DynamicGridConsumer
import Qatlib.Papers.Cbmd26.Algorithms.DynamicGridAddressBridge
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
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.CoherentSim.TaylorEncoding

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 2048
noncomputable section
namespace CBMD
open Matrix Set
open scoped BigOperators Matrix.Norms.L2Operator
set_option warningAsError false

abbrev DynamicGridTimeIndex (Λ T : ℝ) (N : ℕ) (ζ : ℝ) :=
  Fin (dynamicSegmentCount Λ T * dynamicGridFineCount Λ T N ζ)

def dynamicFineTimeOracle {Anc I : Type} (U : ℝ → Matrix (Anc × I) (Anc × I) ℂ)
    (τ : ℕ → ℝ) (Λ T : ℝ) (N : ℕ) (ζ : ℝ)
    (j : DynamicGridTimeIndex Λ T N ζ) : Matrix (Anc × I) (Anc × I) ℂ :=
  suppliedGridOracle U τ N
    (T * j.val / (dynamicSegmentCount Λ T * dynamicGridFineCount Λ T N ζ : ℕ))

variable {F Anc I : Type} [Fintype F] [DecidableEq F]
  [Fintype Anc] [DecidableEq Anc] [Fintype I] [DecidableEq I]

local instance cbmdDynamicOriginalGridConsumerInstance1 (Anc : Type) [DecidableEq Anc] : DecidableEq (DynamicSampleAnc Anc) :=
  inferInstanceAs (DecidableEq (Bool × (Bool × Anc)))
local instance cbmdDynamicOriginalGridConsumerInstance2 (T : Type) [DecidableEq T] : DecidableEq (DynamicOriginalLabels T) :=
  inferInstanceAs (DecidableEq (T × (Bool × (Bool × Bool))))
local instance cbmdDynamicOriginalGridConsumerInstance3 (Anc J : Type) (K : ℕ) [DecidableEq Anc] [DecidableEq J] :
    DecidableEq (DynamicFreshStored Anc J K) :=
  inferInstanceAs (DecidableEq (TaylorWordLabel J K × FreshSignals (DynamicSampleAnc Anc) K))
local instance cbmdDynamicOriginalGridConsumerInstance4 (F Anc J I : Type) (K : ℕ) [DecidableEq F] [DecidableEq Anc]
    [DecidableEq J] [DecidableEq I] : DecidableEq (DynamicFreshFinalSpace F Anc J I K) :=
  inferInstanceAs (DecidableEq (Bool × ((DynamicOriginalLabels (DynamicFreshStored Anc J K) × F) × (J × (Anc × I)))))

def dynamicOriginalGridWord (a₀ : Anc) (α Λ T : ℝ) (N : ℕ) (ζ : ℝ)
    (s : F → ℝ) (c : F → ℂ) (f₀ : F) :
    List (AdjointStep (DynamicFreshFinalSpace F Anc (DynamicGridTimeIndex Λ T N ζ) I
      (dynamicGridDegree Λ T ζ))) :=
  dynamicOuterOriginalWord (dynamicGridDegree Λ T ζ) α Λ s c f₀
    (dynamicGridWord (I := I) ((false,false,a₀) : DynamicSampleAnc Anc) Λ T N ζ)

theorem dynamic_original_grid_lcu
    (a₀ : Anc) (α Λ T : ℝ) (N : ℕ) (ζ : ℝ)
    (hα : 0 < α) (hΛ : 0 < Λ) (hT : 0 < T) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (τ : ℕ → ℝ) (hτ : Monotone τ) (hτ0 : τ 0 = 0) (hτN : τ N = T)
    (s : F → ℝ) (hbound : ∀ f, α * Real.sqrt (1 + (s f)^2) ≤ Λ)
    (c : F → ℂ) (f₀ : F) (hmass : 0 < coefficientMass c)
    (L H : ℝ → Matrix I I ℂ)
    (hL : ∀ t ∈ Icc 0 T, (L t).IsHermitian)
    (hH : ∀ t ∈ Icc 0 T, (H t).IsHermitian)
    (U : ℝ → Matrix (Anc × I) (Anc × I) ℂ)
    (henc : ∀ t ∈ Icc 0 T, BlockEncoding (L t + Complex.I • H t) (U t)
      (tagFrame a₀ (1 : Matrix I I ℂ)) (tagFrame a₀ (1 : Matrix I I ℂ)) α 0) :
    let J := DynamicGridTimeIndex Λ T N ζ
    let K := dynamicGridDegree Λ T ζ
    let cs := dynamicOriginalGridWord (I := I) a₀ α Λ T N ζ s c f₀
    let O := controlOracle (parallelOracle
      (J := DynamicOriginalLabels (DynamicFreshStored Anc J K) × F)
      (select (dynamicFineTimeOracle U τ Λ T N ζ)))
    let R := dynamicFreshFinalFrame (I := I) f₀ (dynamicGridZeroAddress Λ T N ζ) a₀ K
    WellFormedAdjointCircuit cs ∧ O ∈ Matrix.unitaryGroup _ ℂ ∧
    BlockEncoding (∑ f, c f • suppliedGridEvolution τ
      (fun j => H (τ j) + (s f : ℂ) • L (τ j)) N)
      (evaluate O cs) R R (coefficientMass c) (ζ * coefficientMass c) ∧
    adjointQueryCount cs = 6 * dynamicSegmentCount Λ T * K ∧
    adjointGateCount cs = dynamicSegmentCount Λ T * (42*K+13) + 3 := by
  let J := DynamicGridTimeIndex Λ T N ζ
  let K := dynamicGridDegree Λ T ζ
  let Uj := dynamicFineTimeOracle U τ Λ T N ζ
  let cs₀ := dynamicGridWord (I := I) ((false,false,a₀) : DynamicSampleAnc Anc) Λ T N ζ
  have hQ : 0 < dynamicSegmentCount Λ T * dynamicGridFineCount Λ T N ζ :=
    Nat.mul_pos (dynamicSegmentCount_bounds hΛ.le hT.le).1 (dynamicGridFineCount_pos Λ T N ζ)
  have htime (j : J) : suppliedGridSampleTime τ N
      (T*j.val/(dynamicSegmentCount Λ T * dynamicGridFineCount Λ T N ζ : ℕ)) ∈ Icc 0 T := by
    have hj := uniformGridTime_mem hT hQ j
    simpa only [hτN] using!
        suppliedGridSampleTime_mem (N := N) hτ hτ0 hj.1 (by simpa only [hτN] using! hj.2)
  have hUj : ∀ j : J, Uj j ∈ Matrix.unitaryGroup (Anc × I) ℂ :=
    fun j => (henc _ (htime j)).unitary
  have hτmem (j : ℕ) (hj : j < N) : τ j ∈ Icc 0 T := by
    exact ⟨by simpa only [hτ0] using! hτ (Nat.zero_le j), by simpa only [hτN] using! hτ hj.le⟩
  have hfield (f : F) (j : J) :
      dynamicGridNormalizedSample τ (fun k => H (τ k) + (s f : ℂ) • L (τ k)) Λ T N ζ j =
      (Λ : ℂ)⁻¹ • (H (suppliedGridSampleTime τ N
        (T*j.val/(dynamicSegmentCount Λ T * dynamicGridFineCount Λ T N ζ : ℕ))) +
        (s f : ℂ) • L (suppliedGridSampleTime τ N
        (T*j.val/(dynamicSegmentCount Λ T * dynamicGridFineCount Λ T N ζ : ℕ)))) := by
    unfold dynamicGridNormalizedSample dynamicGridSample
    rw [suppliedGridField_original hτ0 (fun t => H t + (s f : ℂ) • L t)
      (uniformGridTime_mem hT hQ j).1 (by simpa only [hτN] using! (uniformGridTime_mem hT hQ j).2)]
  have hsim (f : F) := dynamic_grid_simulation_counted ((false,false,a₀) : DynamicSampleAnc Anc)
    hτ hτ0 (fun k => H (τ k) + (s f : ℂ) • L (τ k)) hΛ hT hζ hζ1 N hτN
    (fun j hj => ⟨(hH _ (hτmem j hj)).add ((hL _ (hτmem j hj)).smul (by simp [IsSelfAdjoint])),
      (original_first_order_norm_bound (L (τ j)) (H (τ j)) (hL _ (hτmem j hj))
        (hH _ (hτmem j hj)) (U (τ j)) a₀ α (s f) (henc _ (hτmem j hj))).trans (hbound f)⟩)
    (fun j : J => (paddedFirstOrderInputUnitary (Uj j) α Λ (s f)).submatrix
      (sampleAncillaEquiv Anc I) (sampleAncillaEquiv Anc I))
    (fun j => by
      rw [hfield]
      exact dynamic_padded_sample_encoding _ _ (hL _ (htime j)) (hH _ (htime j))
        (Uj j) a₀ α Λ (s f) (henc _ (htime j)) (hbound f))
  (try dsimp only at hsim)
  have ho := dynamicOuterOriginalWord_blockEncoding K α Λ s hα hΛ hbound c f₀ hmass
    (dynamicGridZeroAddress Λ T N ζ) a₀ ζ Uj hUj cs₀ (hsim f₀).1
    (fun f => suppliedGridEvolution τ (fun j => H (τ j) + (s f : ℂ) • L (τ j)) N)
    (fun f => (hsim f).2.2.1)
  (try dsimp only)
  refine ⟨ho.1, controlOracle_unitary (parallelOracle_unitary (select_unitary _ hUj)), ho.2.1, ?_,
      ?_⟩
  · calc
      _ = 2 * adjointQueryCount cs₀ := ho.2.2.1
      _ = _ := by rw [(hsim f₀).2.2.2.1]; ring
  · calc
      _ = adjointGateCount cs₀ + 3 + 12 * adjointQueryCount cs₀ := ho.2.2.2
      _ = _ := by rw [(hsim f₀).2.2.2.1, (hsim f₀).2.2.2.2.1]; ring

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
