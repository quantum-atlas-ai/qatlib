/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.OriginalAStaticDecodedWord
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
set_option maxHeartbeats 600000
noncomputable section
namespace CBMD
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

section Tagged
variable {K I : Type} [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I]

def computationalTagEvent (k₀ : K) : Finset (K × I) :=
  Finset.univ.filter fun p => p.1 = k₀

theorem computationalTag_rangeProjector (k₀ : K) :
    rangeProjector (tagFrame k₀ (1 : Matrix I I ℂ)) =
      Projector (computationalTagEvent (I := I) k₀) := by
  ext ⟨k,i⟩ ⟨l,j⟩
  by_cases hk : k = k₀ <;> by_cases hl : l = k₀ <;> by_cases hij : i = j <;>
    simp [rangeProjector, tagFrame, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, Projector, Matrix.diagonal_apply, computationalTagEvent,
      hk, hl, hij, Prod.ext_iff]
  grind

theorem computationalTag_prepare (B : Matrix I I ℂ) (k₀ : K) (i₀ : I)
    (ψ : QState I) (hB : ApplyGate B (Ket i₀) = ψ) :
    ApplyGate (parallelOracle (J := K) B) (Ket (k₀,i₀)) =
      tagFrame k₀ (1 : Matrix I I ℂ) *ᵥ ψ := by
  ext ⟨k,i⟩
  have hi := congrFun hB i
  simp [ApplyGate, Ket, Matrix.mulVec, dotProduct] at hi
  by_cases hk : k = k₀
  · subst k
    simpa [ApplyGate, parallelOracle, select, Ket, tagFrame, Matrix.mulVec,
      dotProduct, Fintype.sum_prod_type, Matrix.one_apply] using! hi
  · simp [ApplyGate, parallelOracle, select, Ket, tagFrame, Matrix.mulVec,
      dotProduct, Matrix.one_apply, hk]
end Tagged

section Static
variable {J Anc I : Type} [Fintype J] [DecidableEq J] [Fintype Anc] [DecidableEq Anc]
  [Fintype I] [DecidableEq I]
local instance cbmdStaticComputationalFrameInstance1 : DecidableEq (OriginalStaticLabels J) :=
  inferInstanceAs (DecidableEq (J × (Fin 4 × (Bool × (Bool × Bool)))))

abbrev OriginalStaticAncillas (J Anc : Type) := Bool × (OriginalStaticLabels J × Anc)

def originalStaticComputationalEquiv : OriginalStaticSpace J (Anc × I) ≃
    OriginalStaticAncillas J Anc × I where
  toFun := fun ⟨b,l,a,i⟩ => ((b,l,a),i)
  invFun := fun ⟨⟨b,l,a⟩,i⟩ => (b,l,a,i)
  left_inv _ := rfl
  right_inv _ := rfl

def originalStaticCleanAncilla (j₀ : J) (a₀ : Anc) : OriginalStaticAncillas J Anc :=
  (false,((j₀,0,false,false,false),a₀))

def originalStaticSuccessEvent (j₀ : J) (a₀ : Anc) :
    Finset (OriginalStaticSpace J (Anc × I)) :=
  Finset.univ.filter fun p =>
    (originalStaticComputationalEquiv p).1 = originalStaticCleanAncilla j₀ a₀

def originalStaticInputLift (B : Matrix I I ℂ) :
    Matrix (OriginalStaticSpace J (Anc × I)) (OriginalStaticSpace J (Anc × I)) ℂ :=
  (parallelOracle (J := OriginalStaticAncillas J Anc) B).submatrix
    originalStaticComputationalEquiv originalStaticComputationalEquiv

omit [Fintype J] [Fintype Anc] [Fintype I] in

theorem originalStaticDecodedFrame_computational (j₀ : J) (a₀ : Anc) :
    originalStaticDecodedFrame (tagFrame a₀ (1 : Matrix I I ℂ)) j₀ =
      reindexFrame originalStaticComputationalEquiv
        (tagFrame (originalStaticCleanAncilla j₀ a₀) (1 : Matrix I I ℂ)) := by
  ext ⟨b,⟨j,k,c,d,e⟩,a,i⟩ l
  simp [originalStaticDecodedFrame, reindexFrame, originalStaticWorkspaceEquiv,
    originalStaticComputationalEquiv, originalStaticCleanAncilla, tagFrame,
    Matrix.one_apply, Prod.ext_iff]
  split_ifs <;> simp_all

theorem originalStaticDecodedFrame_rangeProjector (j₀ : J) (a₀ : Anc) :
    rangeProjector (originalStaticDecodedFrame (tagFrame a₀ (1 : Matrix I I ℂ)) j₀) =
      Projector (originalStaticSuccessEvent (I := I) j₀ a₀) := by
  rw [originalStaticDecodedFrame_computational]
  change (tagFrame (originalStaticCleanAncilla j₀ a₀) (1 : Matrix I I ℂ)).submatrix
      originalStaticComputationalEquiv id *
    ((tagFrame (originalStaticCleanAncilla j₀ a₀) (1 : Matrix I I ℂ)).submatrix
      originalStaticComputationalEquiv id)ᴴ = _
  rw [Matrix.conjTranspose_submatrix, ← Matrix.submatrix_mul]
  swap
  · exact Function.bijective_id
  change (rangeProjector (tagFrame (originalStaticCleanAncilla j₀ a₀)
    (1 : Matrix I I ℂ))).submatrix originalStaticComputationalEquiv
      originalStaticComputationalEquiv = _
  rw [computationalTag_rangeProjector]
  ext p q
  simp [Projector, Matrix.diagonal_apply, computationalTagEvent,
    originalStaticSuccessEvent]

theorem originalStaticInputLift_unitary (B : Matrix I I ℂ)
    (hB : B ∈ Matrix.unitaryGroup I ℂ) :
    originalStaticInputLift (J := J) (Anc := Anc) B ∈
      Matrix.unitaryGroup (OriginalStaticSpace J (Anc × I)) ℂ := by
  exact relabelGate_mem_unitary (parallelOracle_unitary hB)
    originalStaticComputationalEquiv.symm

theorem originalStaticInputLift_prepare (B : Matrix I I ℂ) (j₀ : J) (a₀ : Anc) (i₀ : I)
    (ψ : QState I) (hB : ApplyGate B (Ket i₀) = ψ) :
    ApplyGate (originalStaticInputLift (J := J) (Anc := Anc) B)
      (Ket (false,((j₀,0,false,false,false),(a₀,i₀)))) =
      originalStaticDecodedFrame (tagFrame a₀ (1 : Matrix I I ℂ)) j₀ *ᵥ ψ := by
  rw [originalStaticDecodedFrame_computational]
  ext p
  have h := congrFun (computationalTag_prepare B
    (originalStaticCleanAncilla j₀ a₀) i₀ ψ hB) (originalStaticComputationalEquiv p)
  simpa [ApplyGate, originalStaticInputLift, reindexFrame, Matrix.mulVec, dotProduct,
    originalStaticComputationalEquiv, originalStaticCleanAncilla, Ket,
    Fintype.sum_prod_type, parallelOracle, select] using! h
end Static
end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
