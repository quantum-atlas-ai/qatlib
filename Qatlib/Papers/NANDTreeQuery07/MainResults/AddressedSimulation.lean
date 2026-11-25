/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.NANDTreeQuery07.MainResults.TwoQuerySimulation

@[expose] public section

/-!
# Two-query simulation at an arbitrary address

Implements the query, rotation, and uncompute sequence from [ChildsEtAl2009Formula],
Equations (2)–(4), on a register containing an arbitrary finite address.

## References

* [Childs et al., 2009][ChildsEtAl2009Formula]
-/

set_option autoImplicit false

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Papers.NANDTreeQuery07.MainResults

namespace Qatlib.Papers.NANDTreeQuery07.MainResults

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The controlled rotation acts separately on the two Boolean registers at each address. -/
noncomputable def addressedControlledR (t : ℝ) :
    Matrix (Bool × (I × Bool)) (Bool × (I × Bool)) ℂ :=
  fun p q => if p.2.1 = q.2.1 then controlledR t (p.1, p.2.2) (q.1, q.2.2) else 0

/-- A matrix applied to a basis vector yields the column indexed by that vector. -/
private theorem applyGate_ket_entry {J : Type*} [Fintype J] [DecidableEq J]
    (A : Matrix J J ℂ) (q p : J) : ApplyGate A (Ket q) p = A p q := by
  have h : Ket q = Pi.single q (1 : ℂ) := by
    funext i
    simp [Ket, Pi.single_apply]
  simp only [ApplyGate, h, Matrix.mulVec_single_one, Matrix.col_apply]

/-- At a basis address, the oracle XORs the addressed bit into the ancilla and keeps the
other coordinates. -/
private theorem applyGate_addressed_oracle (x : I → Bool) (b : Bool) (k : I) (a : Bool) :
    ApplyGate (TensorGate (1 : Matrix Bool Bool ℂ) (BitOracleOn x)) (Ket (b, (k, a))) =
      Ket (b, (k, a ^^ x k)) := by
  rw [← tensorState_ket_ket b (k, a), applyGate_tensorGate, applyGate_one,
    applyGate_bitOracleOn_ket, tensorState_ket_ket]

/-- An addressed rotation leaves the basis state fixed when the ancilla is false. -/
private theorem applyGate_addressed_rotation_false (t : ℝ) (b : Bool) (k : I) :
    ApplyGate (addressedControlledR t) (Ket (b, (k, false))) = Ket (b, (k, false)) := by
  funext p
  obtain ⟨p, j, a⟩ := p
  by_cases h : j = k
  · subst j
    simpa [addressedControlledR, applyGate_ket_entry, Ket] using
      congrFun (applyGate_controlledR_ket_false t b) (p, a)
  · simp [addressedControlledR, applyGate_ket_entry, Ket, h]

/-- With a true ancilla, the rotation acts within the current address with the same
two amplitudes as the Boolean rotation. -/
private theorem applyGate_addressed_rotation_true (t : ℝ) (b : Bool) (k : I) :
    ApplyGate (addressedControlledR t) (Ket (b, (k, true))) =
      (Real.cos t : ℂ) • Ket (b, (k, true)) +
        (Complex.I * (Real.sin t : ℂ)) • Ket (!b, (k, true)) := by
  funext p
  obtain ⟨p, j, a⟩ := p
  by_cases h : j = k
  · subst j
    simpa [addressedControlledR, applyGate_ket_entry, Ket, Pi.add_apply, Pi.smul_apply] using
      congrFun (applyGate_controlledR_ket_true t b) (p, a)
  · simp [addressedControlledR, applyGate_ket_entry, Ket, Pi.add_apply, Pi.smul_apply, h]

/-- The query, controlled rotation, and uncompute block realizes the local basis evolution
of the addressed input bit, with the ancilla returned to false. -/
theorem two_query_realizes_hamiltonian_evolution_addressed (x : I → Bool) (t : ℝ)
    (b : Bool) (k : I) :
    Run (TensorGate (1 : Matrix Bool Bool ℂ) (BitOracleOn x))
      [Step.query, Step.gate (addressedControlledR t), Step.query] (Ket (b, (k, false))) =
      (Real.cos (bitReal (x k) * t) : ℂ) • Ket (b, (k, false)) +
        (Complex.I * (Real.sin (bitReal (x k) * t) : ℂ)) • Ket (!b, (k, false)) := by
  simp only [run_query, run_gate, run_nil]
  rw [applyGate_addressed_oracle]
  simp only [Bool.false_xor]
  cases h : x k
  · rw [applyGate_addressed_rotation_false, applyGate_addressed_oracle]
    simp [h]
  · rw [applyGate_addressed_rotation_true, ApplyGate_add, ApplyGate_smul, ApplyGate_smul,
      applyGate_addressed_oracle, applyGate_addressed_oracle]
    simp [h]

omit [Fintype I] in
/-- The addressed local simulation block uses exactly two queries. -/
theorem addressed_two_query_count (t : ℝ) :
    QueryCount ([Step.query, Step.gate (addressedControlledR t), Step.query] :
      Circuit (Bool × (I × Bool))) = 2 := rfl

end Qatlib.Papers.NANDTreeQuery07.MainResults
