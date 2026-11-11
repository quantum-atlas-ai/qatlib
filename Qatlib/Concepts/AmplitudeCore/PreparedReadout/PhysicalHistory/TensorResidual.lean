/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.BinaryClockSignalWord
import Qatlib.Foundations.PureStateMath.BornBridge.RelabelOperatorNorm

/-!
# Tensor stability of simulation residuals

The residual `E * F - F * U` measures the failure of an implementation to intertwine with its
logical operator. The module converts full-output bounds into operator-norm bounds and
transports these bounds through identity tensor factors, including arbitrary joint input states.

`rowRelabel` transports output frames along basis equivalences, while the isometry results
preserve valid embeddings. These finite-dimensional norm and tensor-product constructions fit
the framework of [Watrous2018].

## Main statements

* `operator_error_of_full_output`: derives an operator bound from bounds on all input vectors.
* `tensor_full_output_error`: bounds errors on joint system and ancillary states.
* `rowRelabel_isometry`: preserves an isometric frame under output relabeling.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.TensorResidual

open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.QspSimulation.JacobiAnger
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory

open Qatlib.Foundations.InstrumentCore.Measurement

open MeasureTheory
open scoped Classical BigOperators Kronecker Matrix.Norms.L2Operator

/-- A uniform relative full-output error bound implies the corresponding operator-norm
intertwining error bound. -/
theorem operator_error_of_full_output {O I : Type*} [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] (E : Matrix O O ℂ) (F : Matrix O I ℂ)
    (U : Matrix I I ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ ψ : QState I,
      ‖toEuclidean_fromVec (E *ᵥ (F *ᵥ ψ) - F *ᵥ (U *ᵥ ψ))‖ ≤
        ε * ‖toEuclidean_fromVec ψ‖) : ‖E * F - F * U‖ ≤ ε := by
  apply l2_opNorm_le_of_mulVec_le hε
  intro ψ
  simpa only [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec] using! h ψ

/-- Tensoring the intertwining maps with an identity tensors their residual with that same
identity. -/
theorem tensor_residual {O I A : Type*} [Fintype O] [Fintype I] [Fintype A]
    [DecidableEq A] (E : Matrix O O ℂ) (F : Matrix O I ℂ) (U : Matrix I I ℂ) :
    (E ⊗ₖ (1 : Matrix A A ℂ)) * (F ⊗ₖ (1 : Matrix A A ℂ)) -
        (F ⊗ₖ (1 : Matrix A A ℂ)) * (U ⊗ₖ (1 : Matrix A A ℂ)) =
      (E * F - F * U) ⊗ₖ (1 : Matrix A A ℂ) := by
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  ext ⟨o, a⟩ ⟨i, b⟩
  simp only [Matrix.kronecker_apply, Matrix.sub_apply, sub_mul]

/-- Tensoring with an identity preserves an upper bound on the operator norm of the intertwining
residual. -/
theorem tensor_operator_error {O I A : Type*} [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]
    (E : Matrix O O ℂ) (F : Matrix O I ℂ) (U : Matrix I I ℂ)
    (ε : ℝ) (h : ‖E * F - F * U‖ ≤ ε) :
    ‖(E ⊗ₖ (1 : Matrix A A ℂ)) * (F ⊗ₖ (1 : Matrix A A ℂ)) -
        (F ⊗ₖ (1 : Matrix A A ℂ)) * (U ⊗ₖ (1 : Matrix A A ℂ))‖ ≤ ε := by
  rw [tensor_residual, l2_norm_kronecker]
  exact (mul_le_of_le_one_right (norm_nonneg _) l2_norm_one_le).trans h

/-- The tensor-extended intertwining error on any joint state is bounded by the residual bound
times the state norm. -/
theorem tensor_full_output_error {O I A : Type*} [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]
    (E : Matrix O O ℂ) (F : Matrix O I ℂ) (U : Matrix I I ℂ)
    (ε : ℝ) (h : ‖E * F - F * U‖ ≤ ε) (Ψ : QState (I × A)) :
    ‖toEuclidean_fromVec
      ((E ⊗ₖ (1 : Matrix A A ℂ)) *ᵥ ((F ⊗ₖ (1 : Matrix A A ℂ)) *ᵥ Ψ) -
        (F ⊗ₖ (1 : Matrix A A ℂ)) *ᵥ ((U ⊗ₖ (1 : Matrix A A ℂ)) *ᵥ Ψ))‖ ≤
      ε * ‖toEuclidean_fromVec Ψ‖ := by
  have hn := l2_norm_mulVec_fromVec_le
    ((E ⊗ₖ (1 : Matrix A A ℂ)) * (F ⊗ₖ (1 : Matrix A A ℂ)) -
      (F ⊗ₖ (1 : Matrix A A ℂ)) * (U ⊗ₖ (1 : Matrix A A ℂ))) Ψ
  simp only [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec] at hn
  exact hn.trans (mul_le_mul_of_nonneg_right (tensor_operator_error E F U ε h) (norm_nonneg _))

/-- Relabel the output rows of a rectangular matrix along an equivalence. -/
noncomputable def rowRelabel {O P I : Type*} (e : O ≃ P) (F : Matrix O I ℂ) : Matrix P I ℂ :=
  fun p i => F (e.symm p) i

/-- Applying a row-relabeled matrix is equivalent to relabeling its output state. -/
theorem rowRelabel_mulVec {O P I : Type*} [Fintype I]
    (e : O ≃ P) (F : Matrix O I ℂ) (Ψ : QState I) :
    rowRelabel e F *ᵥ Ψ = relabelState e (F *ᵥ Ψ) := rfl

/-- Gate and state relabeling commute with matrix action. -/
private theorem relabel_mulVec {O P : Type*} [Fintype O] [Fintype P]
    (e : O ≃ P) (U : Matrix O O ℂ) (v : QState O) :
    relabelGate e U *ᵥ relabelState e v = relabelState e (U *ᵥ v) :=
  applyGate_relabelGate e U v

/-- Relabeling the output rows preserves the isometry property. -/
theorem rowRelabel_isometry {O P I : Type*} [Fintype O] [DecidableEq O]
    [Fintype P] [DecidableEq P] [Fintype I] [DecidableEq I]
    (e : O ≃ P) (F : Matrix O I ℂ) (hF : IsIsometry F) : IsIsometry (rowRelabel e F) := by
  change Fᴴ * F = 1 at hF
  change (rowRelabel e F)ᴴ * rowRelabel e F = 1
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, rowRelabel]
  rw [e.symm.sum_comp (fun o : O => star (F o i) * F o j)]
  exact congrFun (congrFun hF i) j

/-- Tensoring an isometric frame with an identity gives an isometric frame. -/
theorem tensor_frame_isometry {O I A : Type*} [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]
    (F : Matrix O I ℂ) (hF : IsIsometry F) : IsIsometry (F ⊗ₖ (1 : Matrix A A ℂ)) := by
  change Fᴴ * F = 1 at hF
  change (F ⊗ₖ (1 : Matrix A A ℂ))ᴴ * (F ⊗ₖ (1 : Matrix A A ℂ)) = 1
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, hF, Matrix.one_mul, Matrix.one_kronecker_one]

end Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.TensorResidual
