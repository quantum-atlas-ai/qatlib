/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.InstrumentMachinePrefix

/-!
# Scalar Readout from Instrument Machine Records

This module defines `instrumentMachineDecode`, a scalar readout obtained by replaying a finite
outcome record and consulting the resulting halt instruction. It returns zero when replay does
not produce a halted endpoint with a halt instruction. The interpretation of trace as branch
mass is the standard one for quantum operations in [Watrous2018].

For traces that actually halt, `instrumentMachineDecode_correct` identifies this readout with
the supplied endpoint-dependent decoder. Nonnegativity of branch masses then bounds the halted
machine mass in a scalar error window by the corresponding event mass of the unrolled circuit.

## Main statements

* `instrumentMachineHalted_instruction` identifies the halt instruction at a halted trace
  endpoint.
* `instrumentMachineDecode_correct` proves correctness of record-based scalar decoding on halted
  traces.
* `instrumentMachineHaltMass_le_unroll_scalar` bounds halted scalar-window mass by the unrolled
  circuit event mass for positive semidefinite inputs.

## References

- [Watrous, 2018][Watrous2018], *The Theory of Quantum Information*.
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.Execution.CircuitCompile

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
open scoped ComplexOrder

/-- The endpoint of a halted bounded machine trace carries a halt instruction whose Boolean
value is the trace's acceptance value. -/
theorem instrumentMachineHalted_instruction {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (O : Operator D) (T : ℕ) (c : C) (rho : Operator D)
    (t : InstrumentMachineTrace D C) (ht : t ∈ instrumentMachineTraces M O T c rho)
    (hhalt : t.endpoint.halted = true) :
    M t.endpoint.control = .halt t.accepted := by
  induction T generalizing c rho t with
  | zero =>
    simp only [instrumentMachineTraces, List.mem_singleton] at ht
    subst t
    contradiction
  | succ T ih =>
    cases h : M c with
    | halt b =>
      simp only [instrumentMachineTraces, h, List.mem_singleton] at ht
      subst t
      exact h
    | gate G next =>
      simp only [instrumentMachineTraces, h, List.mem_map] at ht
      obtain ⟨u,hu,rfl⟩ := ht
      exact ih next _ u hu hhalt
    | query next =>
      simp only [instrumentMachineTraces, h, List.mem_map] at ht
      obtain ⟨u,hu,rfl⟩ := ht
      exact ih next _ u hu hhalt
    | instrument s I next =>
      simp only [instrumentMachineTraces, h, List.mem_flatten, List.mem_ofFn] at ht
      obtain ⟨xs,⟨o,rfl⟩,ht⟩ := ht
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
      exact ih (next o) _ u hu hhalt

/-- Decode a scalar from an outcome record by replaying it and reading the endpoint's halt
instruction. Return zero if replay fails, the endpoint is pending, or its instruction is not
a halt. -/
noncomputable def instrumentMachineDecode {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (T : ℕ) (c : C)
    (decode : C → Bool → List (ℕ×ℕ) → ℝ) (rec : List (ℕ×ℕ)) : ℝ :=
  match instrumentMachineReplay M T c rec with
  | none => 0
  | some e => if e.halted then match M e.control with
    | .halt b => decode e.control b rec
    | _ => 0
    else 0

/-- On the outcome record of a halted machine trace, record-based decoding equals the supplied
decoder evaluated at that trace's control endpoint, acceptance value, and outcomes. -/
theorem instrumentMachineDecode_correct {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (O : Operator D) (T : ℕ) (c : C) (rho : Operator D)
    (decode : C → Bool → List (ℕ×ℕ) → ℝ)
    (t : InstrumentMachineTrace D C) (ht : t ∈ instrumentMachineTraces M O T c rho)
    (hhalt : t.endpoint.halted = true) :
    instrumentMachineDecode M T c decode t.outcomes =
      decode t.endpoint.control t.accepted t.outcomes := by
  unfold instrumentMachineDecode
  rw [instrumentMachineReplay_correct M O T c rho t ht]
  simp only [hhalt, ↓reduceIte]
  rw [instrumentMachineHalted_instruction M O T c rho t ht hhalt]

/-- A pointwise inequality on the elements of a list yields the same inequality between the sums
of the two mapped real-valued functions. -/
private theorem readout_sum_map_mono {A : Type*} (xs : List A) (f g : A → ℝ)
    (h : ∀ x ∈ xs, f x ≤ g x) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => exact le_rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h x (by simp)) (ih fun y hy => h y (by simp [hy]))

/-- For a positive semidefinite input, the halted machine mass whose decoded value is within
`epsilon` of `a` is bounded by the unrolled circuit mass in the same record-decoded scalar
window. -/
theorem instrumentMachineHaltMass_le_unroll_scalar {D : ℕ} {C : Type*}
    (M : InstrumentMachine D C) (O : Operator D) (T : ℕ) (c : C) (rho : Operator D)
    (hrho : rho.PosSemidef) (decode : C → Bool → List (ℕ×ℕ) → ℝ) (a epsilon : ℝ) :
    instrumentMachineHaltMass M O T c rho
      (fun c b rec => decide (|decode c b rec-a| ≤ epsilon)) ≤
    instrumentCircuitEventMass O (unrollInstrumentMachine M T c) rho
      (fun _ rec => decide (|instrumentMachineDecode M T c decode rec-a| ≤ epsilon)) := by
  unfold instrumentMachineHaltMass instrumentCircuitEventMass
  rw [← unrollInstrumentMachine_traces M O T c rho]
  simp only [List.map_map, Function.comp_def]
  apply readout_sum_map_mono
  intro t ht
  have hn : 0 ≤ mixedMass t.toMixedBranchTrace :=
    (RCLike.nonneg_iff.mp
      (instrumentMachineTraces_posSemidef M O T c rho hrho t ht).trace_nonneg).1
  by_cases hh : t.endpoint.halted = true
  · have heq := instrumentMachineDecode_correct M O T c rho decode t ht hh
    simp only [heq, hh, Bool.true_and]
    exact le_rfl
  · have hh0 : t.endpoint.halted = false := by
      cases h : t.endpoint.halted
      · rfl
      · exact False.elim (hh h)
    simp only [hh0, Bool.false_and, Bool.false_eq_true, if_false]
    split_ifs
    · exact hn
    · exact le_rfl

end Qatlib.Concepts.AdversaryBounds.AdvDuality
