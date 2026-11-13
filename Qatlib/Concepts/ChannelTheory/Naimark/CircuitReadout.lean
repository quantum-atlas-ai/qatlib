/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ChannelTheory.Naimark.UnitaryReadout
import Qatlib.Foundations.QueryWordCore.Circuit

/-!
# Circuit execution, unitary channels, and basis readout

Unitary gate-and-query circuits determine bundled unitary matrices. Their
vector execution agrees with matrix multiplication, and their action on mixed
states agrees with the corresponding unitary channel. For a basis input, basis
POVM outcome probabilities are squared execution amplitudes; the final theorem
sums this identity over a finite event.

These are the circuit and measurement semantics of [NielsenChuang2010]; see
[Nielsen & Chuang, Chapter 8][NielsenChuang2010] for the channel description.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.ChannelTheory.Naimark.CircuitReadout

open Matrix
open scoped BigOperators ComplexOrder
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ChannelTheory.Naimark.UnitaryReadout

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The unitary matrix obtained by composing the gates and unitary oracle calls of a unitary
circuit in execution order. -/
def circuitUnitary (O : Matrix.unitaryGroup I ℂ) :
    (C : Circuit I) → IsUnitaryCircuit C → Matrix.unitaryGroup I ℂ
  | [], _ => 1
  | Step.gate V :: C, hC =>
      circuitUnitary O C ((isUnitaryCircuit_gate V C).mp hC).2 *
        ⟨V, ((isUnitaryCircuit_gate V C).mp hC).1⟩
  | Step.query :: C, hC =>
      circuitUnitary O C ((isUnitaryCircuit_query C).mp hC) * O

/-- Executing a unitary circuit agrees with applying its composed unitary matrix to the input
amplitudes. -/
theorem run_eq_circuitUnitary (O : Matrix.unitaryGroup I ℂ) (C : Circuit I)
    (hC : IsUnitaryCircuit C) (ψ : I → ℂ) :
    Run (O : Matrix I I ℂ) C ψ = (circuitUnitary O C hC : Matrix I I ℂ) *ᵥ ψ := by
  induction C generalizing ψ with
  | nil => simp [Run, circuitUnitary]
  | cons step C ih =>
    cases step with
    | gate V =>
      rw [Run, ih ((isUnitaryCircuit_gate V C).mp hC).2]
      exact Matrix.mulVec_mulVec _ _ _
    | query =>
      rw [Run, ih ((isUnitaryCircuit_query C).mp hC)]
      exact Matrix.mulVec_mulVec _ _ _

/-- Running a circuit on a basis state extracts the corresponding column of its composed unitary
matrix. -/
theorem circuit_basis_entry (O : Matrix.unitaryGroup I ℂ) (C : Circuit I)
    (hC : IsUnitaryCircuit C) (seed i : I) :
    Run (O : Matrix I I ℂ) C (_root_.Ket.basis seed : I → ℂ) i =
      (circuitUnitary O C hC : Matrix I I ℂ) i seed := by
  rw [run_eq_circuitUnitary O C hC]
  simp [Matrix.mulVec, dotProduct, _root_.Ket.basis, _root_.Ket.coe_fun_eq]

/-- The mixed-state channel of a unitary circuit has entries given by the double sum of
basis-run amplitudes against the input density matrix. -/
theorem circuit_mixed_matrix (O : Matrix.unitaryGroup I ℂ) (C : Circuit I)
    (hC : IsUnitaryCircuit C) (ρ : MState I) (i j : I) :
    (CPTPMap.ofUnitary (circuitUnitary O C hC) ρ).m i j =
      ∑ p : I, ∑ q : I,
        Run (O : Matrix I I ℂ) C (_root_.Ket.basis p : I → ℂ) i * ρ.m p q *
          star (Run (O : Matrix I I ℂ) C (_root_.Ket.basis q : I → ℂ) j) := by
  rw [unitary_matrix]
  simp only [circuit_basis_entry O C hC, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]

/-- On a pure basis input, the circuit channel output is the outer product of the circuit run
amplitudes. -/
theorem circuit_basis_matrix (O : Matrix.unitaryGroup I ℂ) (C : Circuit I)
    (hC : IsUnitaryCircuit C) (seed : I) :
    (CPTPMap.ofUnitary (circuitUnitary O C hC) (MState.pure (_root_.Ket.basis seed))).m =
      fun i j => Run (O : Matrix I I ℂ) C (_root_.Ket.basis seed : I → ℂ) i *
        star (Run (O : Matrix I I ℂ) C (_root_.Ket.basis seed : I → ℂ) j) := by
  simpa only [run_eq_circuitUnitary O C hC] using
    unitary_basis_matrix (circuitUnitary O C hC) seed

/-- Basis readout of a unitary circuit on a basis input satisfies the Born rule;
see [Nielsen & Chuang, quantum operations][NielsenChuang2010]. -/
theorem circuit_basis_probability (O : Matrix.unitaryGroup I ℂ) (C : Circuit I)
    (hC : IsUnitaryCircuit C) (seed i : I) :
    (((basisPOVM I).measure
      (CPTPMap.ofUnitary (circuitUnitary O C hC) (MState.pure (_root_.Ket.basis seed))))
      i : ℝ) = ‖Run (O : Matrix I I ℂ) C (_root_.Ket.basis seed : I → ℂ) i‖ ^ 2 := by
  simpa only [run_eq_circuitUnitary O C hC] using
    unitary_basis_probability (circuitUnitary O C hC) seed i

/-- The basis measurement probability of a finite event after running a unitary circuit on a
basis input equals the sum of squared output amplitudes over that event. -/
theorem circuit_basis_event (O : Matrix.unitaryGroup I ℂ) (C : Circuit I)
    (hC : IsUnitaryCircuit C) (seed : I) (S : Finset I) :
    (∑ i ∈ S, (((basisPOVM I).measure
      (CPTPMap.ofUnitary (circuitUnitary O C hC) (MState.pure (_root_.Ket.basis seed))))
      i : ℝ)) = ∑ i ∈ S,
        ‖Run (O : Matrix I I ℂ) C (_root_.Ket.basis seed : I → ℂ) i‖ ^ 2 := by
  simp only [circuit_basis_probability]

end Qatlib.Concepts.ChannelTheory.Naimark.CircuitReadout
