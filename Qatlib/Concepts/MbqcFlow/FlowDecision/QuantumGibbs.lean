/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.QuantumGibbsDefs
import Qatlib.Concepts.ReferenceError.RefTraceError.FiniteReferenceTraceError

/-!
# Instruments from unitary ancilla readout

Constructs `readoutInstrument` from a unitary acting on an ancilla and a system, with a fixed
ancilla input basis label. It proves Kraus completeness and identifies pure-input outcome
probabilities with sums of squared output amplitudes.

The module also treats reference extensions, coarse outcome labels, and readout after a
well-formed compiled adjoint circuit through `compiledReadout`. The measurement construction
follows the standard unitary-and-ancilla framework of [NielsenChuang2010].

## Main statements

* `readoutKraus_complete`: completeness of the unitary block Kraus operators.
* `readout_reference_laws`: positivity and trace laws with a reference system.
* `compiled_readout_probability`: Born probabilities for compiled circuits.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

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

/-- For a unitary joint matrix and fixed input ancilla label, the readout Kraus adjoint-products
sum to the identity. -/
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

/-- The instrument obtained from the Kraus blocks of a unitary joint ancilla-system matrix with
fixed ancilla input. -/
def readoutInstrument {D M : ℕ}
    (U : Matrix (Fin M × Fin D) (Fin M × Fin D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin M × Fin D) ℂ) (a : Fin M) : Instrument (Fin M) D D :=
  Instrument.ofKraus (readoutKraus U a) (readoutKraus_complete U hU a)

/-- The joint output amplitude at ancilla label `o` equals the corresponding component of the
readout Kraus operator applied to the system vector. -/
theorem readoutKraus_actual_vector {D M : ℕ}
    (U : Matrix (Fin M × Fin D) (Fin M × Fin D) ℂ) (a o : Fin M)
    (ψ : QState (Fin D)) (i : Fin D) :
    (U *ᵥ TensorState (Ket a) ψ) (o,i) = (readoutKraus U a o *ᵥ ψ) i := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, TensorState,
    Qatlib.Foundations.PureStateMath.Ket, readoutKraus, mul_ite, ite_mul]

/-- The instrument probability on a pure outer product equals the sum of squared joint output
amplitudes at the selected ancilla label. -/
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

/-- Extending a readout branch by a reference identity gives conjugation by the Kraus operator
tensored with that identity. -/
theorem readout_reference_branch {D M R : ℕ}
    (U : Matrix (Fin M × Fin D) (Fin M × Fin D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin M × Fin D) ℂ) (a o : Fin M)
    (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) :
    tensorLeft ((readoutInstrument U hU a).branch o) ρ =
      TensorGate (readoutKraus U a o) (1 : Operator R) * ρ *
        (TensorGate (readoutKraus U a o) (1 : Operator R))ᴴ :=
  tensorLeft_conjBranch _ ρ

/-- On a positive semidefinite joint input, each reference-extended branch is positive
semidefinite and has no larger real trace, while the sum of branch traces equals the input
trace. -/
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

/-- A coarse-grained pure-input readout probability is the sum of squared joint output
amplitudes over all ancilla labels in the selected coarse class. -/
theorem readout_coarse_probability {D M K : ℕ}
    (U : Matrix (Fin M × Fin D) (Fin M × Fin D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin M × Fin D) ℂ) (a : Fin M)
    (label : Fin M → Fin K) (z : Fin K) (ψ : QState (Fin D)) :
    instrumentProb ((readoutInstrument U hU a).coarsen label) (outerProduct ψ) z =
      ∑ o ∈ Finset.univ.filter (fun o => label o = z),
        ∑ i, ‖(U *ᵥ TensorState (Ket a) ψ) (o,i)‖^2 := by
  rw [instrumentProb_coarsen]
  simp_rw [readout_pure_probability]

/-- The readout instrument formed by evaluating a well-formed adjoint circuit with a unitary
oracle. -/
def compiledReadout {D M : ℕ}
    (O : Matrix (Fin M × Fin D) (Fin M × Fin D) ℂ)
    (hO : O ∈ Matrix.unitaryGroup (Fin M × Fin D) ℂ)
    (cs : List (AdjointStep (Fin M × Fin D))) (hcs : WellFormedAdjointCircuit cs)
    (a : Fin M) : Instrument (Fin M) D D :=
  readoutInstrument (evaluate O cs) (hcs.evaluate_unitary hO) a

/-- The pure-input probability of a compiled readout outcome equals the sum of squared
evaluated-circuit amplitudes at that ancilla label. -/
theorem compiled_readout_probability {D M : ℕ}
    (O : Matrix (Fin M × Fin D) (Fin M × Fin D) ℂ)
    (hO : O ∈ Matrix.unitaryGroup (Fin M × Fin D) ℂ)
    (cs : List (AdjointStep (Fin M × Fin D))) (hcs : WellFormedAdjointCircuit cs)
    (a o : Fin M) (ψ : QState (Fin D)) :
    instrumentProb (compiledReadout O hO cs hcs a) (outerProduct ψ) o =
      ∑ i, ‖(evaluate O cs *ᵥ TensorState (Ket a) ψ) (o,i)‖^2 :=
  readout_pure_probability _ _ _ _ _

end Qatlib.Concepts.MbqcFlow.FlowDecision
