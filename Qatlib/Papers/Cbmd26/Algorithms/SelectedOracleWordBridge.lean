/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.IndexedQSVTBridge
import Qatlib.Papers.Cbmd26.Algorithms.ControlledAccessBridge

/-!
# Coefficient LCU words for selected oracles

`selectedCoefficientWord` wraps a common oracle word with coefficient preparation to implement a
linear combination over a selected oracle family. The construction supports the contour-based
matrix decompositions of [WangEtAl2026].

## Main statements

* `selectedCoefficientWord_evaluate`: identifies the evaluated word with the coefficient LCU
  unitary.
* `selectedCoefficientWord_blockEncoding`: combines branch encodings with weighted normalization
  and error while preserving the query count.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.SignalPrimitive.HermitianQSVT
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
noncomputable section
namespace CBMD
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
variable {J W I : Type} [Fintype J] [DecidableEq J] [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I]

/-- The coefficient LCU word obtained by lifting a common oracle word to a spectator label
register and adding coefficient preparation. -/
def selectedCoefficientWord (c : J → ℂ) (j₀ : J) (cs : List (AdjointStep W)) :
    List (AdjointStep (J × W)) := outerCoefficientWord c j₀ (spectatorLiftWord J cs)

omit [Fintype I] [DecidableEq I] in

/-- Evaluating the selected coefficient word yields the coefficient LCU unitary of the
individually evaluated branch words. -/
theorem selectedCoefficientWord_evaluate (c : J → ℂ) (j₀ : J)
    (U : J → Matrix W W ℂ) (cs : List (AdjointStep W)) :
    evaluate (select U) (selectedCoefficientWord c j₀ cs) =
      coefficientLCUUnitary c (fun j => evaluate (U j) cs) j₀ :=
  outerCoefficientWord_evaluate c j₀ (select U) _ _ (evaluate_spectatorLiftWord_select U cs)

omit [Fintype I] [DecidableEq I] [Fintype W] in

/-- Coefficient wrapping preserves the adjoint-oracle query count and adds three fixed gates. -/
theorem selectedCoefficientWord_cost (c : J → ℂ) (j₀ : J) (cs : List (AdjointStep W)) :
    adjointQueryCount (selectedCoefficientWord c j₀ cs) = adjointQueryCount cs ∧
    adjointGateCount (selectedCoefficientWord c j₀ cs) = adjointGateCount cs + 3 := by
  obtain ⟨hq,hg⟩ := outerCoefficientWord_cost c j₀ (spectatorLiftWord J cs)
  simpa only [(spectatorLiftWord_cost J cs).1, (spectatorLiftWord_cost J cs).2] using!
      And.intro hq hg

/-- A well-formed common word encoding each branch yields a well-formed coefficient LCU encoding
of `∑ j, c j • A j`, with weighted normalization and error. The construction preserves the
common word's query count when the scaled coefficient mass is positive. -/
theorem selectedCoefficientWord_blockEncoding (c : J → ℂ) (j₀ : J)
    (U : J → Matrix W W ℂ) (cs : List (AdjointStep W))
    (hcs : WellFormedAdjointCircuit cs) (A : J → Matrix I I ℂ) (F : Matrix W I ℂ)
    (β ε : J → ℝ) (henc : ∀ j, BlockEncoding (A j) (evaluate (U j) cs) F F (β j) (ε j))
    (hmass : 0 < coefficientMass (scaledLCUCoefficients c β)) :
    WellFormedAdjointCircuit (selectedCoefficientWord (scaledLCUCoefficients c β) j₀ cs) ∧
    BlockEncoding (∑ j, c j • A j)
      (evaluate (select U) (selectedCoefficientWord (scaledLCUCoefficients c β) j₀ cs))
      (tagFrame j₀ F) (tagFrame j₀ F) (∑ j, ‖c j‖ * β j) (∑ j, ‖c j‖ * ε j) ∧
    adjointQueryCount (selectedCoefficientWord (scaledLCUCoefficients c β) j₀ cs) = adjointQueryCount cs := by
  have he := counted_outer_lcu_encoding c j₀ (select U) (spectatorLiftWord J cs)
    (fun j => evaluate (U j) cs) (evaluate_spectatorLiftWord_select U cs)
    (spectatorLiftWord_wellFormed J hcs) A F β ε henc hmass
  exact ⟨he.1,he.2.1,(selectedCoefficientWord_cost _ j₀ cs).1⟩

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
