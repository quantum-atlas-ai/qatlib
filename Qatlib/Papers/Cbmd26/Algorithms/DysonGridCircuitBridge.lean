/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.DysonCoefficientBridge
import Qatlib.Concepts.InteractionEvo.MeanDerivGrid.DysonMeanDerivativeGrid
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
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
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.LchsSimulation.TimeOrdered
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.CoherentSim.TaylorEncoding

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace CBMD
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

section Target
variable {J I : Type} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]

theorem gridWordCoefficients_dyson_target (M K : ℕ) (t Λ : ℝ)
    (address : Fin M → J) (B : J → Matrix I I ℂ) (H : ℝ → Matrix I I ℂ)
    (hB : ∀ j, (Λ : ℂ) • B (address j) = H (t * j.val / M)) :
    (∑ w : (Σ l : Fin (K + 1), Fin l.val → J),
      gridWordCoefficients (List.ofFn address) K (gridStepCoefficient t Λ M) w •
        taylorBranchWord B K K le_rfl (.inl w)) = dysonGridTruncatedSum H t M K := by
  rw [gridWordCoefficients_target]
  have hm : (List.ofFn address).map (fun j => gridStepCoefficient t Λ M • B j) =
      List.ofFn (fun j : Fin M =>
        -((t / (M : ℝ) : ℝ) : ℂ) • (Complex.I • H (t * j.val / M))) := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext j
    exact gridStepCoefficient_sample M t Λ address B H hB j
  rw [hm]
  exact Fin.sum_univ_eq_sum_range (fun k => dysonGridDegreeSum H t M k) (K + 1)

end Target

section Circuit
variable {A J I : Type} [Fintype A] [DecidableEq A] [Fintype J] [DecidableEq J]
  [Fintype I] [DecidableEq I]

private instance dysonFreshWorkspaceDecEq (K : ℕ) :
    DecidableEq (FreshQueryWorkspace A J I K) :=
  @instDecidableEqProd (FreshSignals A K) (Bool × (J × (A × I)))
    (freshSignalsDecidableEq A K) inferInstance

private instance dysonFreshLabelWorkspaceDecEq (K : ℕ) :
    DecidableEq (TaylorWordLabel J K × FreshQueryWorkspace A J I K) :=
  @instDecidableEqProd (TaylorWordLabel J K) (FreshQueryWorkspace A J I K)
    inferInstance (dysonFreshWorkspaceDecEq K)

def dysonGridLCUWord (j₀ : J) (M K : ℕ) (t Λ : ℝ) (address : Fin M → J) :
    List (AdjointStep (TaylorWordLabel J K × FreshQueryWorkspace A J I K)) :=
  coherentFreshLCUWord j₀ (taylorEmptyLabel J K) K (routedFreshChoices j₀ K K le_rfl)
    (routedPaddedCoefficients K
      (gridWordCoefficients (List.ofFn address) K (gridStepCoefficient t Λ M)))

theorem dyson_grid_lcu_counted (j₀ : J) (a₀ : A) (M K : ℕ) (t Λ : ℝ)
    (address : Fin M → J) (B : J → Matrix I I ℂ)
    (U : J → Matrix (A × I) (A × I) ℂ) (H : ℝ → Matrix I I ℂ)
    (ht : 0 ≤ t) (hΛ : 0 ≤ Λ) (hM : 0 < M) (hlog : Λ * t ≤ Real.log 2)
    (hB : ∀ j, (Λ : ℂ) • B (address j) = H (t * j.val / M))
    (henc : ∀ j, ProjectedUnitaryEncoding (B j) (U j) (encodingFiber a₀) (encodingFiber a₀)) :
    WellFormedAdjointCircuit (dysonGridLCUWord (A := A) (I := I) j₀ M K t Λ address) ∧
    parallelOracle (J := TaylorWordLabel J K) (freshPrimitiveQuery K U) ∈
      Matrix.unitaryGroup (TaylorWordLabel J K × FreshQueryWorkspace A J I K) ℂ ∧
    BlockEncoding (dysonGridTruncatedSum H t M K)
      (evaluate (parallelOracle (J := TaylorWordLabel J K) (freshPrimitiveQuery K U))
        (dysonGridLCUWord j₀ M K t Λ address))
      (tagFrame (taylorEmptyLabel J K) (freshWordFrame j₀ a₀ K))
      (tagFrame (taylorEmptyLabel J K) (freshWordFrame j₀ a₀ K)) 2 0 ∧
    adjointQueryCount (dysonGridLCUWord (A := A) (I := I) j₀ M K t Λ address) = K ∧
    adjointGateCount (dysonGridLCUWord (A := A) (I := I) j₀ M K t Λ address) = 2 * K + 3 := by
  have h := coherent_fresh_padded_lcu_counted j₀ a₀ K
    (gridWordCoefficients (List.ofFn address) K (gridStepCoefficient t Λ M)) B U
    (sampled_grid_coefficients_mass_le_two M K t Λ address ht hΛ hM hlog) henc
  rw [gridWordCoefficients_dyson_target M K t Λ address B H hB] at h
  exact h

end Circuit
end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
