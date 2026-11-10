/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound.GroverLowerBoundInstance
import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel
set_option warningAsError false


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

def bOracleCorrected (x : I) : Matrix ((I × Bool) × W) ((I × Bool) × W) ℂ :=
  PhaseOracle (fun p : (I × Bool) × W => decide (p.1.1=x))

def phaseCompileEquiv : (((I × Bool) × W) × Bool) ≃ ((I × Bool) × (Bool × W)) where
  toFun p := ((p.1.1.1,p.2),(p.1.1.2,p.1.2))
  invFun p := (((p.1.1,p.2.1),p.2.2),p.1.2)
  left_inv := by rintro ⟨⟨⟨i,b⟩,w⟩,a⟩; rfl
  right_inv := by rintro ⟨⟨i,a⟩,b,w⟩; rfl

def phaseCompile (C : Circuit ((I × Bool) × W)) : Circuit ((I × Bool) × (Bool × W)) :=
  relabelCircuit phaseCompileEquiv (LiftCircuit C)

def phaseCompileStart (ψ : QState ((I × Bool) × W)) : QState ((I × Bool) × (Bool × W)) :=
  relabelState phaseCompileEquiv (TensorState ψ Minus)

theorem bOracleCorrected_unitary (x : I) :
    bOracleCorrected (W := W) x ∈ Matrix.unitaryGroup ((I × Bool) × W) ℂ :=
  phaseOracle_unitary _

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

theorem phaseCompile_counts_unitary (C : Circuit ((I × Bool) × W))
    (hC : IsUnitaryCircuit C) : QueryCount (phaseCompile C)=QueryCount C ∧ IsUnitaryCircuit (phaseCompile C) := by
  have hh := relabelCircuit_legality_resources (phaseCompileEquiv (I := I) (W := W)) (LiftCircuit C)
  exact ⟨hh.2.1.trans (queryCount_liftCircuit C),hh.1.mpr hC.lift⟩

theorem phaseCompile_run (C : Circuit ((I × Bool) × W)) (ψ : QState ((I × Bool) × W)) (x : I) :
    Run (workspaceBitOracle (W := Bool × W) (fun i => decide (i=x))) (phaseCompile C) (phaseCompileStart ψ) =
      relabelState phaseCompileEquiv (TensorState (Run (bOracleCorrected x) C ψ) Minus) := by
  have hh := (run_relabelCircuit_readout (phaseCompileEquiv (I := I) (W := W))
    (BitOracleOn (fun p : (I × Bool) × W => decide (p.1.1=x))) (LiftCircuit C)
    (TensorState ψ Minus) Finset.univ).1
  rw [relabeled_bit_oracle,run_liftCircuit_bitOracleOn] at hh
  exact hh

end Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound
