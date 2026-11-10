/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ChannelTheory.Naimark.UnitaryReadout
import Qatlib.Foundations.QueryWordCore.Circuit
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.ChannelTheory.Naimark.CircuitReadout

open Matrix
open scoped BigOperators ComplexOrder
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ChannelTheory.Naimark.UnitaryReadout

variable {I : Type} [Fintype I] [DecidableEq I]

def circuitUnitary (O : Matrix.unitaryGroup I ℂ) :
    (C : Circuit I) → IsUnitaryCircuit C → Matrix.unitaryGroup I ℂ
  | [], _ => 1
  | Step.gate V :: C, hC =>
      circuitUnitary O C ((isUnitaryCircuit_gate V C).mp hC).2 *
        ⟨V, ((isUnitaryCircuit_gate V C).mp hC).1⟩
  | Step.query :: C, hC =>
      circuitUnitary O C ((isUnitaryCircuit_query C).mp hC) * O

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

theorem circuit_basis_entry (O : Matrix.unitaryGroup I ℂ) (C : Circuit I)
    (hC : IsUnitaryCircuit C) (seed i : I) :
    Run (O : Matrix I I ℂ) C (_root_.Ket.basis seed : I → ℂ) i =
      (circuitUnitary O C hC : Matrix I I ℂ) i seed := by
  rw [run_eq_circuitUnitary O C hC]
  simp [Matrix.mulVec, dotProduct, _root_.Ket.basis, _root_.Ket.coe_fun_eq]

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

theorem circuit_basis_matrix (O : Matrix.unitaryGroup I ℂ) (C : Circuit I)
    (hC : IsUnitaryCircuit C) (seed : I) :
    (CPTPMap.ofUnitary (circuitUnitary O C hC) (MState.pure (_root_.Ket.basis seed))).m =
      fun i j => Run (O : Matrix I I ℂ) C (_root_.Ket.basis seed : I → ℂ) i *
        star (Run (O : Matrix I I ℂ) C (_root_.Ket.basis seed : I → ℂ) j) := by
  simpa only [run_eq_circuitUnitary O C hC] using
    unitary_basis_matrix (circuitUnitary O C hC) seed

theorem circuit_basis_probability (O : Matrix.unitaryGroup I ℂ) (C : Circuit I)
    (hC : IsUnitaryCircuit C) (seed i : I) :
    (((basisPOVM I).measure
      (CPTPMap.ofUnitary (circuitUnitary O C hC) (MState.pure (_root_.Ket.basis seed))))
      i : ℝ) = ‖Run (O : Matrix I I ℂ) C (_root_.Ket.basis seed : I → ℂ) i‖ ^ 2 := by
  simpa only [run_eq_circuitUnitary O C hC] using
    unitary_basis_probability (circuitUnitary O C hC) seed i

theorem circuit_basis_event (O : Matrix.unitaryGroup I ℂ) (C : Circuit I)
    (hC : IsUnitaryCircuit C) (seed : I) (S : Finset I) :
    (∑ i ∈ S, (((basisPOVM I).measure
      (CPTPMap.ofUnitary (circuitUnitary O C hC) (MState.pure (_root_.Ket.basis seed))))
      i : ℝ)) = ∑ i ∈ S,
        ‖Run (O : Matrix I I ℂ) C (_root_.Ket.basis seed : I → ℂ) i‖ ^ 2 := by
  simp only [circuit_basis_probability]

end Qatlib.Concepts.ChannelTheory.Naimark.CircuitReadout
