/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Foundations.BornMetrics.EventProbability
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open scoped BigOperators
namespace Qatlib.Papers.ManyBodyFermi97.MainResults.TwoParticleAntisym

def input : QState (Bool × Bool) := Ket (false,true)

noncomputable def printed : QState (Bool × Bool) := (1/2 : ℂ) • (Ket (false,true)-Ket (true,false))

noncomputable def corrected : QState (Bool × Bool) :=
  ((Real.sqrt 2 : ℂ)⁻¹) • (Ket (false,true)-Ket (true,false))

theorem printed_norm_sq : ‖toEuclidean_fromVec printed‖^2=(1/2 : ℝ) := by
  rw [norm_toEuclidean_fromVec_sq]
  norm_num [printed, Ket, Fintype.sum_prod_type, Fintype.sum_bool]

theorem no_unitary_printed (C : Circuit (Bool × Bool)) (hC : IsUnitaryCircuit C) :
    Run 1 C input ≠ printed := by
  intro heq
  have hOne : (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) ∈ Matrix.unitaryGroup (Bool × Bool) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']; simp
  have hn := hC.normalized_run hOne (normalized_ket (false,true))
  change Normalized (Run 1 C input) at hn
  rw [heq] at hn
  have hn' : ‖toEuclidean_fromVec printed‖^2=1 := by
    simpa only [norm_toEuclidean_fromVec_sq] using! hn
  rw [printed_norm_sq] at hn'
  norm_num at hn'

noncomputable def word : Circuit (Bool × Bool) :=
  [.gate (TensorGate Hadamard 1), .gate CNOT, .gate (TensorGate PauliZ 1)]

theorem word_run : Run 1 word input = corrected := by
  funext p
  obtain ⟨b,c⟩ := p
  cases b <;> cases c <;>
    norm_num [word, Run, ApplyGate, TensorGate, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Fintype.sum_bool, input, corrected, Ket, Hadamard,
      CNOT, permMatrix, cnotFlip, PauliZ, Matrix.diagonal]

theorem word_valid_cost : IsUnitaryCircuit word ∧ QueryCount word=0 ∧ GateCount word=3 := by
  have hOne : (1 : Matrix Bool Bool ℂ) ∈ Matrix.unitaryGroup Bool ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']; simp
  refine ⟨?_, rfl, rfl⟩
  simp only [word, isUnitaryCircuit_gate, isUnitaryCircuit_nil, and_true]
  exact ⟨tensorGate_unitary hadamard_unitary hOne, cnot_unitary,
    tensorGate_unitary pauliZ_unitary hOne⟩

theorem corrected_normalized : Normalized corrected := by
  rw [← word_run]
  have hOne : (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) ∈ Matrix.unitaryGroup (Bool × Bool) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']; simp
  exact word_valid_cost.1.normalized_run hOne (normalized_ket (false,true))
end Qatlib.Papers.ManyBodyFermi97.MainResults.TwoParticleAntisym
