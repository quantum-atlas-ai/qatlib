/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LocalMachine.LocalTransport.ControlledQueryCircuit
import Qatlib.Concepts.QsvtCore.QueryLowerBound.SubroutineExpansion
import Qatlib.Concepts.SpectralFilter.PhaseReadout.CountedPhaseReflection

/-!
# Clean phase estimation circuit expansion

This module expands phase estimation around an adjoint-query circuit body, including its
controlled implementation, input state, lifted frame, and event mass. The construction follows
the phase estimation framework described in [NielsenChuang2010].

The expansion theorem identifies the resulting action with the counted phase estimation circuit
and records the gate and query costs of both the word and its adjoint.

## Main statements

* `controlled_clean_body_actual_semantics_and_cost`: controlled compilation preserves
  well-formedness and both instruction counts.
* `clean_qpe_actual_expansion_semantics_and_paid_inverse`: the expanded word has the required
  semantics and explicit forward and inverse costs.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability

namespace Qatlib.Concepts.CoherentSim.CleanQPEBands

open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Kronecker

/-- The controlled compilation of an adjoint-query circuit body. -/
noncomputable def controlledCleanBody {H : Type} [Fintype H] [DecidableEq H]
    (body : List (AdjointStep H)) : List (AdjointStep (Bool × H)) :=
  compileControlled body

/-- The phase estimation instruction word obtained by substituting the lifted controlled body
into the compiled counted phase circuit. -/
noncomputable def cleanQPEWord {H : Type} [Fintype H] [DecidableEq H]
    (M : ℕ) (body : List (AdjointStep H)) :
    List (AdjointStep (Fin M × (Bool × H))) :=
  substituteAdjointCircuit
    (phaseLiftWord (TensorGate (1 : Operator M)) (controlledCleanBody body))
    (phaseCompileCircuit (countedPhaseCircuit M))

/-- The phase estimation input with the phase register at zero, the control qubit false, and
system state `ξ`. -/
noncomputable def cleanQPEInput {H : Type} (M : ℕ) (hM : 0 < M) (ξ : QState H) :
    QState (Fin M × (Bool × H)) :=
  TensorState (Ket (⟨0, hM⟩ : Fin M)) (TensorState (Ket false) ξ)

/-- The frame `R` tensored with identities on the phase register and control qubit. -/
noncomputable def cleanQPEFrame {H I : Type} [DecidableEq H] [DecidableEq I]
    (M : ℕ) (R : Matrix H I ℂ) :
    Matrix (Fin M × (Bool × H)) (Fin M × (Bool × I)) ℂ :=
  (1 : Operator M) ⊗ₖ ((1 : Matrix Bool Bool ℂ) ⊗ₖ R)

/-- The sum of squared output amplitudes over all coordinates whose phase register belongs to
`E`. -/
noncomputable def cleanQPEEventMass {H : Type} [Fintype H]
    (M : ℕ) (out : QState (Fin M × (Bool × H))) (E : Finset (Fin M)) : ℝ :=
  ∑ p ∈ Finset.univ.filter (fun p => p.1 ∈ E), ‖out p‖ ^ 2

/-- Controlled compilation preserves well-formedness, evaluates to the controlled body operator,
and preserves both query and gate counts. -/
theorem controlled_clean_body_actual_semantics_and_cost
    (H : Type) [Fintype H] [DecidableEq H] (O : Matrix H H ℂ)
    (body : List (AdjointStep H)) (hbody : WellFormedAdjointCircuit body) :
    WellFormedAdjointCircuit (controlledCleanBody body) ∧
      evaluate (controlOracle O) (controlledCleanBody body) =
        controlOracle (evaluate O body) ∧
      adjointQueryCount (controlledCleanBody body) = adjointQueryCount body ∧
      adjointGateCount (controlledCleanBody body) = adjointGateCount body :=
  ⟨compileControlled_wellFormed hbody, evaluate_compileControlled O body,
    queryCount_compileControlled body, gateCount_compileControlled body⟩

/-- For positive `M`, the expanded phase estimation word is well formed, uses `(M - 1)` times
the body query count, and has gate count `2 * (M - 1) + 2 + (M - 1) * adjointGateCount
body`. Its adjoint has the same counts, and its action equals that of the counted phase
circuit with the evaluated controlled body. -/
theorem clean_qpe_actual_expansion_semantics_and_paid_inverse
    (H : Type) [Fintype H] [DecidableEq H] (M : ℕ) (O : Matrix H H ℂ)
    (body : List (AdjointStep H)) (hM : 0 < M)
    (hbody : WellFormedAdjointCircuit body) :
    let word := cleanQPEWord M body
    WellFormedAdjointCircuit word ∧
      adjointQueryCount word = (M - 1) * adjointQueryCount body ∧
      adjointGateCount word = 2 * (M - 1) + 2 + (M - 1) * adjointGateCount body ∧
      adjointQueryCount (adjointCircuit word) = adjointQueryCount word ∧
      adjointGateCount (adjointCircuit word) = adjointGateCount word ∧
      ∀ ξ : QState (Fin M × (Bool × H)),
        evaluate (TensorGate (1 : Operator M) (controlOracle O)) word *ᵥ ξ =
          Run (TensorGate (1 : Operator M) (controlOracle (evaluate O body)))
            (countedPhaseCircuit M) ξ := by
  let lift : Matrix (Bool × H) (Bool × H) ℂ →
      Matrix (Fin M × (Bool × H)) (Fin M × (Bool × H)) ℂ :=
    TensorGate (1 : Operator M)
  let cb := compileControlled body
  let outer := phaseCompileCircuit (countedPhaseCircuit (I := H) M)
  have hr := counted_offgrid_qpe_clean_flag M hM (evaluate O body) (0 : QState H)
  have ho := phaseCompileCircuit_counts (countedPhaseCircuit (I := H) M)
  have hb := phaseLiftWord_counts lift cb
  have hs := substitute_adjoint_evaluate_cost (lift (controlOracle O))
    (phaseLiftWord lift cb) outer
  have hl : evaluate (lift (controlOracle O)) (phaseLiftWord lift cb) =
      lift (controlOracle (evaluate O body)) := by
    rw [phaseLiftWord_evaluate lift
      (by exact tensorGate_one)
      (by intro U V; dsimp [lift]; rw [tensorGate_mul, Matrix.one_mul])
      (by intro U; simp [lift, tensorGate_conjTranspose]), evaluate_compileControlled]
  refine ⟨hs.2.2.2
    (phaseLiftWord_wellFormed lift
      (fun _ h => tensorGate_unitary (Submonoid.one_mem _) h)
      (compileControlled_wellFormed hbody))
    (phaseCompileCircuit_wellFormed hr.2.2.2), ?_, ?_,
    adjointQueryCount_adjointCircuit _, adjointGateCount_adjointCircuit _, ?_⟩
  · change adjointQueryCount (substituteAdjointCircuit (phaseLiftWord lift cb) outer) = _
    rw [hs.2.1, hb.1, queryCount_compileControlled, ho.1, hr.2.1]
  · change adjointGateCount (substituteAdjointCircuit (phaseLiftWord lift cb) outer) = _
    rw [hs.2.2.1, hb.2, gateCount_compileControlled, ho.1, ho.2, hr.2.1, hr.2.2.1]
  · intro ξ
    change evaluate (lift (controlOracle O))
      (substituteAdjointCircuit (phaseLiftWord lift cb) outer) *ᵥ ξ = _
    rw [hs.1, hl]
    exact phaseCompileCircuit_evaluate _ _ ξ

end Qatlib.Concepts.CoherentSim.CleanQPEBands
