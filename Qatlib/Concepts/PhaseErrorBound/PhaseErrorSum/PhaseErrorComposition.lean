/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.QsvtCore

/-!
# Accumulation of dyadic phase errors

This module bounds the difference between products of unit-modulus complex numbers by the sum of
their individual errors. It applies this telescoping estimate to finite dyadic phase programs
and their controlled versions, using the circuit error perspective of [NielsenChuang2010].

The results `g1` and `g2` transport the scalar estimate to matrix error on `paddedNativeFrame`,
retaining exact gate counts for the program and its adjoint.

## Main statements

* `product_error`: unit norm of the implemented product and the additive product-error bound.
* `g1`: scalar phase implementation with frame error bounded by the sum of phase errors.
* `g2`: the corresponding bound with control on an arbitrary data wire.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

namespace Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

/-- For two families of unit-modulus complex numbers with entrywise errors bounded by `ε`, the
first product has norm one and the difference of the products is bounded by the sum of `ε`
over the finite set. -/
theorem product_error {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (u z : ι → ℂ) (ε : ι → ℝ)
    (hu : ∀ i, ‖u i‖ = 1) (hz : ∀ i, ‖z i‖ = 1)
    (he : ∀ i, ‖u i - z i‖ ≤ ε i) :
    ‖∏ i ∈ s, u i‖ = 1 ∧ ‖(∏ i ∈ s, u i) - ∏ i ∈ s, z i‖ ≤ ∑ i ∈ s, ε i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    constructor
    · rw [norm_mul, hu a, ih.1, one_mul]
    · have hid : u a * (∏ i ∈ s, u i) - z a * (∏ i ∈ s, z i) =
          (u a - z a) * (∏ i ∈ s, u i) + z a * ((∏ i ∈ s, u i) - ∏ i ∈ s, z i) := by ring
      rw [hid]
      calc
        _ ≤ ‖(u a - z a) * (∏ i ∈ s, u i)‖ +
            ‖z a * ((∏ i ∈ s, u i) - ∏ i ∈ s, z i)‖ := norm_add_le _ _
        _ = ‖u a - z a‖ + ‖(∏ i ∈ s, u i) - ∏ i ∈ s, z i‖ := by
          rw [norm_mul, norm_mul, ih.1, hz a, mul_one, one_mul]
        _ ≤ ε a + ∑ i ∈ s, ε i := add_le_add (he a) ih.2

/-- The dyadic phase product differs from a product of unit-modulus targets by at most the sum
of the individual phase-factor error bounds. -/
theorem phase_product_error (m : ℕ) (ps : Fin m → ℕ × Bool)
    (z : Fin m → ℂ) (ε : Fin m → ℝ)
    (hz : ∀ i, ‖z i‖ = 1)
    (he : ∀ i, ‖Complex.exp (dyadicPhaseAngle (ps i).1 (ps i).2 * Complex.I) - z i‖ ≤ ε i) :
    ‖paddedPhaseProduct (List.ofFn ps) - ∏ i, z i‖ ≤ ∑ i, ε i := by
  simpa only [paddedPhaseProduct, List.map_ofFn, List.prod_ofFn, Function.comp_apply] using
    (product_error Finset.univ
      (fun i => Complex.exp (dyadicPhaseAngle (ps i).1 (ps i).2 * Complex.I)) z ε
      (fun i => Complex.norm_exp_ofReal_mul_I _) hz he).2

/-- For unit-modulus targets and nonnegative individual error bounds, the padded scalar phase
program has frame error at most their sum. It is unitary, uses zero queries, and has `7 * m`
gates in both forward and adjoint programs. -/
theorem g1 :
    ∀ (n m : ℕ) (ps : Fin m → ℕ × Bool) (z : Fin m → ℂ) (ε : Fin m → ℝ),
      (∀ i, ‖z i‖ = 1) → (∀ i, 0 ≤ ε i) →
      (∀ i, ‖Complex.exp (dyadicPhaseAngle (ps i).1 (ps i).2 * Complex.I) - z i‖ ≤ ε i) →
      let gs := paddedScalarPhaseSequenceWord n (List.ofFn ps)
      ‖localProgramMatrix gs * paddedNativeFrame n -
        paddedNativeFrame n * ((∏ i, z i) • (1 : Matrix (Reg n) (Reg n) ℂ))‖ ≤ ∑ i, ε i ∧
      QueryCount (localProgramCircuit gs) = 0 ∧
      GateCount (localProgramCircuit gs) = 7 * m ∧
      GateCount (localProgramCircuit (localProgramAdjoint gs)) = 7 * m ∧
      IsUnitaryCircuit (localProgramCircuit gs) := by
  intro n m ps z ε hz _hε he
  exact ⟨(padded_scalar_sequence_frame_error n (List.ofFn ps) _).trans
      (phase_product_error m ps z ε hz he),
    by simpa only [List.length_ofFn] using padded_scalar_sequence_cost n (List.ofFn ps)⟩

/-- For unit-modulus targets and nonnegative individual error bounds, the padded phase program
controlled by wire `a` has frame error at most their sum. It is unitary, uses zero queries,
and has `7 * m` gates in both forward and adjoint programs. -/
theorem g2 :
    ∀ (n m : ℕ) (a : Fin n) (ps : Fin m → ℕ × Bool) (z : Fin m → ℂ) (ε : Fin m → ℝ),
      (∀ i, ‖z i‖ = 1) → (∀ i, 0 ≤ ε i) →
      (∀ i, ‖Complex.exp (dyadicPhaseAngle (ps i).1 (ps i).2 * Complex.I) - z i‖ ≤ ε i) →
      let gs := paddedControlledPhaseSequenceWord n a (List.ofFn ps)
      ‖localProgramMatrix gs * paddedNativeFrame n -
        paddedNativeFrame n * scopedPhaseGate (fun x => x a) (∏ i, z i)‖ ≤ ∑ i, ε i ∧
      QueryCount (localProgramCircuit gs) = 0 ∧
      GateCount (localProgramCircuit gs) = 7 * m ∧
      GateCount (localProgramCircuit (localProgramAdjoint gs)) = 7 * m ∧
      IsUnitaryCircuit (localProgramCircuit gs) := by
  intro n m a ps z ε hz _hε he
  exact ⟨(padded_controlled_sequence_frame_error n a (List.ofFn ps) _).trans
      (phase_product_error m ps z ε hz he),
    by simpa only [List.length_ofFn] using padded_controlled_sequence_cost n a (List.ofFn ps)⟩

end Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
