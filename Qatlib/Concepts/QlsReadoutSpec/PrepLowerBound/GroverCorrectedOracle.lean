/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound.GroverLowerBoundInstance
import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel

/-!
# Corrected Grover preparation oracle

The phase oracle `bOracleCorrected` prepares the marked-sign input state while preserving the
auxiliary registers. The compiler `phaseCompile` implements its circuit semantics using a bit
oracle and a phase-kickback qubit, preserving query counts and unitarity. Related mathematical
background is given in [BennettEtAl1997].

## Main statements

* `bOracleCorrected_prepare`: Action on the solver starting state.
* `phaseCompile_run`: Exact correspondence between compiled and phase-oracle executions.

## References

* [Bennett et al., 1997][BennettEtAl1997]
-/

open Qatlib.Concepts.QueryComplexity.AdversarySearch

open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound
open Matrix
open scoped Classical
variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

/-- The phase oracle that flips the sign precisely when the data index equals the marked index
`x`. -/
def bOracleCorrected (x : I) : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ :=
  PhaseOracle (fun p : (I × Bool) × W => decide (p.1.1=x))

/-- The register equivalence moving the phase-kickback qubit into the oracle bit position and
grouping the original ancillary registers as workspace. -/
def phaseCompileEquiv : (((I × Bool) × W) × Bool) ≃ ((I × Bool) × (Bool × W)) where
  toFun p := ((p.1.1.1,p.2),(p.1.1.2,p.1.2))
  invFun p := (((p.1.1,p.2.1),p.2.2),p.1.2)
  left_inv := by rintro ⟨⟨⟨i,b⟩,w⟩,a⟩; rfl
  right_inv := by rintro ⟨⟨i,a⟩,b,w⟩; rfl

/-- The bit-oracle circuit obtained by lifting a phase-oracle circuit with an extra qubit and
relabeling its registers. -/
def phaseCompile (C : Circuit ((I × Bool) × W)) : Circuit ((I × Bool) × (Bool × W)) :=
  relabelCircuit phaseCompileEquiv (LiftCircuit C)

/-- The compiled starting state obtained by tensoring the input with `Minus` and relabeling the
registers. -/
def phaseCompileStart (ψ : QState ((I × Bool) × W)) : QState ((I × Bool) × (Bool × W)) :=
  relabelState phaseCompileEquiv (TensorState ψ Minus)

/-- The corrected marked-index preparation oracle is unitary. -/
theorem bOracleCorrected_unitary (x : I) :
    bOracleCorrected (W := W) x ∈ Matrix.unitaryGroup ((I × Bool) × W) ℂ :=
  phaseOracle_unitary _

/-- The corrected oracle maps the solver starting state to `bState x` tensored with the
unchanged auxiliary states. -/
theorem bOracleCorrected_prepare (x : I) (ν : QState Bool) (ω : QState W) :
    bOracleCorrected x *ᵥsolverStart ν ω =
      fun p => bState x p.1.1*ν p.1.2*ω p.2 := by
  ext p
  rw [show bOracleCorrected x*ᵥsolverStart ν ω = ApplyGate (bOracleCorrected x) (solverStart ν ω) from rfl]
  unfold bOracleCorrected
  rw [applyGate_phaseOracle]
  by_cases h : p.1.1=x
  · simp [bState,solverStart,uniformQState,h]
    ring
  · simp [bState,solverStart,uniformQState,h]
omit [Fintype I] [Fintype W] in

/-- Relabeling the lifted marked-index bit oracle gives the workspace bit oracle used by the
compiled circuit. -/
private theorem relabeled_bit_oracle (x : I) :
    relabelGate (phaseCompileEquiv (I := I) (W := W))
      (BitOracleOn (fun p : (I × Bool) × W => decide (p.1.1=x))) =
      workspaceBitOracle (W := Bool × W) (fun i => decide (i=x)) := by
  ext p q
  rcases p with ⟨⟨i,a⟩,b,w⟩
  rcases q with ⟨⟨j,c⟩,d,v⟩
  simp only [relabelGate,Matrix.reindex_apply,Matrix.submatrix_apply,
    phaseCompileEquiv,Equiv.coe_fn_symm_mk,workspaceBitOracle,TensorGate,BitOracleOn,
    permMatrix,Matrix.of_apply,BitFlip]
  by_cases hij : i=j <;> by_cases hbd : b=d <;> by_cases hwv : w=v <;>
    simp [Prod.mk.injEq,hij,hbd,hwv]

/-- Phase compilation preserves the query count and sends a unitary circuit to a unitary
circuit. -/
theorem phaseCompile_counts_unitary (C : Circuit ((I × Bool) × W))
    (hC : IsUnitaryCircuit C) : QueryCount (phaseCompile C)=QueryCount C ∧ IsUnitaryCircuit (phaseCompile C) := by
  have hh := relabelCircuit_legality_resources (phaseCompileEquiv (I := I) (W := W)) (LiftCircuit C)
  exact ⟨hh.2.1.trans (queryCount_liftCircuit C),hh.1.mpr hC.lift⟩

/-- Running the compiled bit-oracle circuit equals the relabeled tensor product of the corrected
phase-oracle output with `Minus`. -/
theorem phaseCompile_run (C : Circuit ((I × Bool) × W)) (ψ : QState ((I × Bool) × W)) (x : I) :
    Run (workspaceBitOracle (W := Bool × W) (fun i => decide (i=x))) (phaseCompile C) (phaseCompileStart ψ) =
      relabelState phaseCompileEquiv (TensorState (Run (bOracleCorrected x) C ψ) Minus) := by
  have hh := (run_relabelCircuit_readout (phaseCompileEquiv (I := I) (W := W))
    (BitOracleOn (fun p : (I × Bool) × W => decide (p.1.1=x))) (LiftCircuit C)
    (TensorState ψ Minus) Finset.univ).1
  rw [relabeled_bit_oracle,run_liftCircuit_bitOracleOn] at hh
  exact hh

end Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound
