/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.QuantumGibbsDefs
import Qatlib.Concepts.ReferenceError.RefTraceError.FiniteReferenceTraceError
open Qatlib.Foundations.PureStateMath
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.QspSimulation.Achievability

namespace Qatlib.Concepts.MbqcFlow.FlowDecision

open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped BigOperators ComplexOrder

theorem readoutKraus_complete {D M : ℕ}
    (U : Matrix (Fin M × Fin D) (Fin M × Fin D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin M × Fin D) ℂ) (a : Fin M) :
    (∑ o, (readoutKraus U a o)ᴴ * readoutKraus U a o) = 1 := by
  have h := Matrix.mem_unitaryGroup_iff'.mp hU
  ext i j
  have he := congrFun (congrFun h (a,i)) (a,j)
  simpa only [Matrix.star_eq_conjTranspose, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, readoutKraus,
    Matrix.one_apply, Prod.mk.injEq, true_and] using he

def readoutInstrument {D M : ℕ}
    (U : Matrix (Fin M × Fin D) (Fin M × Fin D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin M × Fin D) ℂ) (a : Fin M) : Instrument (Fin M) D D :=
  Instrument.ofKraus (readoutKraus U a) (readoutKraus_complete U hU a)

theorem readoutKraus_actual_vector {D M : ℕ}
    (U : Matrix (Fin M × Fin D) (Fin M × Fin D) ℂ) (a o : Fin M)
    (ψ : QState (Fin D)) (i : Fin D) :
    (U *ᵥ TensorState (Ket a) ψ) (o,i) = (readoutKraus U a o *ᵥ ψ) i := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, TensorState,
    Qatlib.Foundations.PureStateMath.Ket, readoutKraus, mul_ite, ite_mul]

theorem readout_pure_probability {D M : ℕ}
    (U : Matrix (Fin M × Fin D) (Fin M × Fin D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin M × Fin D) ℂ) (a o : Fin M)
    (ψ : QState (Fin D)) :
    instrumentProb (readoutInstrument U hU a) (outerProduct ψ) o =
      ∑ i, ‖(U *ᵥ TensorState (Ket a) ψ) (o,i)‖^2 := by
  simp_rw [readoutKraus_actual_vector]
  change (Matrix.trace (conjBranch (readoutKraus U a o) (outerProduct ψ))).re = _
  rw [conjBranch_outerProduct, trace_outerProduct]
  rfl

theorem readout_reference_branch {D M R : ℕ}
    (U : Matrix (Fin M × Fin D) (Fin M × Fin D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin M × Fin D) ℂ) (a o : Fin M)
    (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) :
    tensorLeft ((readoutInstrument U hU a).branch o) ρ =
      TensorGate (readoutKraus U a o) (1 : Operator R) * ρ *
        (TensorGate (readoutKraus U a o) (1 : Operator R))ᴴ :=
  tensorLeft_conjBranch _ ρ

theorem readout_reference_laws {D M R : ℕ}
    (U : Matrix (Fin M × Fin D) (Fin M × Fin D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin M × Fin D) ℂ) (a o : Fin M)
    (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) (hρ : ρ.PosSemidef) :
    (tensorLeft ((readoutInstrument U hU a).branch o) ρ).PosSemidef ∧
      (Matrix.trace (tensorLeft ((readoutInstrument U hU a).branch o) ρ)).re ≤
        (Matrix.trace ρ).re ∧
      Matrix.trace (∑ z, tensorLeft ((readoutInstrument U hU a).branch z) ρ) =
        Matrix.trace ρ :=
  ⟨tensorLeft_posSemidef ((readoutInstrument U hU a).cp o) hρ,
    (readoutInstrument U hU a).tensorLeft_tni hρ o,
    (readoutInstrument U hU a).tensorLeft_total ρ⟩

theorem readout_coarse_probability {D M K : ℕ}
    (U : Matrix (Fin M × Fin D) (Fin M × Fin D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin M × Fin D) ℂ) (a : Fin M)
    (label : Fin M → Fin K) (z : Fin K) (ψ : QState (Fin D)) :
    instrumentProb ((readoutInstrument U hU a).coarsen label) (outerProduct ψ) z =
      ∑ o ∈ Finset.univ.filter (fun o => label o = z),
        ∑ i, ‖(U *ᵥ TensorState (Ket a) ψ) (o,i)‖^2 := by
  rw [instrumentProb_coarsen]
  simp_rw [readout_pure_probability]

def compiledReadout {D M : ℕ}
    (O : Matrix (Fin M × Fin D) (Fin M × Fin D) ℂ)
    (hO : O ∈ Matrix.unitaryGroup (Fin M × Fin D) ℂ)
    (cs : List (AdjointStep (Fin M × Fin D))) (hcs : WellFormedAdjointCircuit cs)
    (a : Fin M) : Instrument (Fin M) D D :=
  readoutInstrument (evaluate O cs) (hcs.evaluate_unitary hO) a

theorem compiled_readout_probability {D M : ℕ}
    (O : Matrix (Fin M × Fin D) (Fin M × Fin D) ℂ)
    (hO : O ∈ Matrix.unitaryGroup (Fin M × Fin D) ℂ)
    (cs : List (AdjointStep (Fin M × Fin D))) (hcs : WellFormedAdjointCircuit cs)
    (a o : Fin M) (ψ : QState (Fin D)) :
    instrumentProb (compiledReadout O hO cs hcs a) (outerProduct ψ) o =
      ∑ i, ‖(evaluate O cs *ᵥ TensorState (Ket a) ψ) (o,i)‖^2 :=
  readout_pure_probability _ _ _ _ _

end Qatlib.Concepts.MbqcFlow.FlowDecision
