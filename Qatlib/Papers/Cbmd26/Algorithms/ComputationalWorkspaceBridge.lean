/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.StaticComputationalFrame

/-!
# Computational success frames and input preparation

The `computationalWorkspaceFrame` construction transports an ancilla-tagged system frame across
an equivalence between a workspace and a product basis. Its range projector is the computational
event `computationalWorkspaceEvent`, and `computationalWorkspaceInput` lifts system input
preparation to that workspace. These results support the contour-based algorithms of
[WangEtAl2026].

## Main statements

* `computationalWorkspaceFrame_rangeProjector`: identifies the success projector.
* `computationalWorkspaceInput_prepare`: transports prepared input states into the success
  frame.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
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
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
noncomputable section
namespace CBMD
open Matrix
open scoped Matrix.Norms.L2Operator

variable {W Aux I : Type} [Fintype W] [DecidableEq W] [Fintype Aux] [DecidableEq Aux]
  [Fintype I] [DecidableEq I]

/-- Transports the system frame with fixed ancilla tag `a₀` to the workspace basis through `e`. -/
def computationalWorkspaceFrame (e : W ≃ Aux × I) (a₀ : Aux) : Matrix W I ℂ :=
  reindexFrame e (tagFrame a₀ (1 : Matrix I I ℂ))

/-- Defines the workspace basis event whose ancilla component under `e` equals `a₀`. -/
def computationalWorkspaceEvent (e : W ≃ Aux × I) (a₀ : Aux) : Finset W :=
  Finset.univ.filter fun w => (e w).1 = a₀

/-- Lifts a system matrix to every ancilla sector and reindexes it to the workspace. -/
def computationalWorkspaceInput (e : W ≃ Aux × I) (B : Matrix I I ℂ) : Matrix W W ℂ :=
  (parallelOracle (J := Aux) B).submatrix e e

omit [DecidableEq W] in

/-- The computational workspace frame is an isometry. -/
theorem computationalWorkspaceFrame_isIsometry (e : W ≃ Aux × I) (a₀ : Aux) :
    IsIsometry (computationalWorkspaceFrame e a₀) :=
  reindexFrame_isIsometry e _ (tagFrame_isIsometry a₀ _ (by simp [IsIsometry]))

/-- The range projector of the computational workspace frame equals the projector of its
computational success event. -/
theorem computationalWorkspaceFrame_rangeProjector (e : W ≃ Aux × I) (a₀ : Aux) :
    rangeProjector (computationalWorkspaceFrame e a₀) =
      Projector (computationalWorkspaceEvent e a₀) := by
  unfold computationalWorkspaceFrame reindexFrame rangeProjector
  rw [Matrix.conjTranspose_submatrix, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id]
  change (rangeProjector (tagFrame a₀ (1 : Matrix I I ℂ))).submatrix e e = _
  rw [computationalTag_rangeProjector]
  ext p q
  simp [Projector, Matrix.diagonal_apply, computationalTagEvent, computationalWorkspaceEvent]

/-- Lifting a unitary system matrix gives a unitary workspace input matrix. -/
theorem computationalWorkspaceInput_unitary (e : W ≃ Aux × I) (B : Matrix I I ℂ)
    (hB : B ∈ Matrix.unitaryGroup I ℂ) :
    computationalWorkspaceInput e B ∈ Matrix.unitaryGroup W ℂ :=
  relabelGate_mem_unitary (parallelOracle_unitary hB) e.symm

/-- A system preparation from `i₀` lifts to preparation of the framed state from the workspace
basis state corresponding to `(a₀, i₀)`. -/
theorem computationalWorkspaceInput_prepare (e : W ≃ Aux × I) (B : Matrix I I ℂ)
    (a₀ : Aux) (i₀ : I) (ψ : QState I) (hB : ApplyGate B (Ket i₀) = ψ) :
    ApplyGate (computationalWorkspaceInput e B) (Ket (e.symm (a₀,i₀))) =
      computationalWorkspaceFrame e a₀ *ᵥ ψ := by
  have hk : relabelState e.symm (Ket (a₀,i₀)) = Ket (e.symm (a₀,i₀)) := by
    funext w
    simp only [relabelState_apply, Equiv.symm_symm, Ket]
    simp only [Equiv.apply_eq_iff_eq_symm_apply]
  have he := applyGate_relabelGate e.symm (parallelOracle (J := Aux) B) (Ket (a₀,i₀))
  rw [hk, computationalTag_prepare B a₀ i₀ ψ hB] at he
  change ApplyGate (computationalWorkspaceInput e B) (Ket (e.symm (a₀,i₀))) = _ at he
  rw [he]
  unfold computationalWorkspaceFrame reindexFrame
  ext w
  rfl

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
