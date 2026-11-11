/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Foundations.BornMetrics.EventProbability
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge

/-!
# Two-particle normalization and a preparation circuit

This module checks the printed two-particle antisymmetric target against norm preservation and
proves that no unitary circuit maps `input` to that target. It defines a corrected normalized
vector and prepares it exactly with a Hadamard gate, a controlled NOT, and a Pauli Z gate.

The mathematical setting is that of [AbramsLloyd1997].

## Main statements

* `no_unitary_printed`: No unitary circuit sends the normalized basis input to the printed
  two-particle target.
* `word_run`: The three-gate circuit sends the basis input exactly to the corrected
  antisymmetric vector.
* `word_valid_cost`: The preparation circuit is unitary and consists of three gates with no
  queries.

## References

* [Abrams and Lloyd, 1997][AbramsLloyd1997]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open scoped BigOperators
namespace Qatlib.Papers.ManyBodyFermi97.MainResults.TwoParticleAntisym

/-- The computational basis state with occupations labeled by `(false, true)`. -/
def input : QState (Bool × Bool) := Ket (false,true)

/-- The difference of the two exchanged basis states scaled by the printed coefficient `1 / 2`. -/
noncomputable def printed : QState (Bool × Bool) := (1/2 : ℂ) • (Ket (false,true)-Ket (true,false))

/-- The normalized antisymmetric difference of the two exchanged basis states, scaled by `1 /
sqrt(2)`. -/
noncomputable def corrected : QState (Bool × Bool) :=
  ((Real.sqrt 2 : ℂ)⁻¹) • (Ket (false,true)-Ket (true,false))

/-- The printed two-particle target has Euclidean squared norm `1 / 2`. -/
theorem printed_norm_sq : ‖toEuclidean_fromVec printed‖^2=(1/2 : ℝ) := by
  rw [norm_toEuclidean_fromVec_sq]
  norm_num [printed, Ket, Fintype.sum_prod_type, Fintype.sum_bool]

/-- No unitary circuit sends the normalized basis input to the printed two-particle target.
[AbramsLloyd1997] -/
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

/-- The three-gate circuit applying a Hadamard on the first qubit, a controlled NOT, and a Pauli
Z on the first qubit. -/
noncomputable def word : Circuit (Bool × Bool) :=
  [.gate (TensorGate Hadamard 1), .gate CNOT, .gate (TensorGate PauliZ 1)]

/-- The three-gate circuit sends the basis input exactly to the corrected antisymmetric vector.
[AbramsLloyd1997] -/
theorem word_run : Run 1 word input = corrected := by
  funext p
  obtain ⟨b,c⟩ := p
  cases b <;> cases c <;>
    norm_num [word, Run, ApplyGate, TensorGate, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Fintype.sum_bool, input, corrected, Ket, Hadamard,
      CNOT, permMatrix, cnotFlip, PauliZ, Matrix.diagonal]

/-- The preparation circuit is unitary and consists of three gates with no queries.
[AbramsLloyd1997] -/
theorem word_valid_cost : IsUnitaryCircuit word ∧ QueryCount word=0 ∧ GateCount word=3 := by
  have hOne : (1 : Matrix Bool Bool ℂ) ∈ Matrix.unitaryGroup Bool ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']; simp
  refine ⟨?_, rfl, rfl⟩
  simp only [word, isUnitaryCircuit_gate, isUnitaryCircuit_nil, and_true]
  exact ⟨tensorGate_unitary hadamard_unitary hOne, cnot_unitary,
    tensorGate_unitary pauliZ_unitary hOne⟩

/-- The corrected two-particle antisymmetric vector is normalized. -/
theorem corrected_normalized : Normalized corrected := by
  rw [← word_run]
  have hOne : (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) ∈ Matrix.unitaryGroup (Bool × Bool) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']; simp
  exact word_valid_cost.1.normalized_run hOne (normalized_ket (false,true))
end Qatlib.Papers.ManyBodyFermi97.MainResults.TwoParticleAntisym
