/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic.Ext
import Mathlib.Tactic.SplitIfs
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Foundations.InstrumentCore.Measurement.Basic

/-!
# Additive oracle matrices and readout

Defines the reversible additive oracle `(x, z) ↦ (x, z + f x)` and its matrix `AddOracle`.
Proves its action on amplitudes and basis states, its composition and inverse identities, and
its unitarity.

For a zero output register, the readout probabilities are expressed through fibers of `f`, and
the input marginal is preserved. This is the oracle model used in quantum sampling algorithms
[NielsenChuang2010].

## Main statements

* `addOracle_unitary`: proves unitarity of the additive oracle.
* `run_addOracle_repeat_query_ket`: computes repeated queries on basis states.
* `marginalProbRight_run_addOracle_zero`: expresses output probabilities through oracle fibers.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib
open Qatlib
open Qatlib

namespace Qatlib.Concepts.HspRecovery.CyclicRecovery

open Matrix

variable {I R : Type*}

/-- A circuit consisting of one oracle query has query count one and gate count zero. -/
theorem addOracle_query_resources :
    QueryCount ([Step.query] : Circuit (I × R)) = 1 ∧
    GateCount ([Step.query] : Circuit (I × R)) = 0 := by
  constructor <;> rfl

/-- The permutation sending `(x, z)` to `(x, z + f x)`, with inverse given by subtraction of `f
x`. -/
def addOracleEquiv [AddGroup R] (f : I → R) : Equiv.Perm (I × R) where
  toFun p := (p.1, p.2 + f p.1)
  invFun p := (p.1, p.2 - f p.1)
  left_inv p := by simp
  right_inv p := by simp

/-- The additive oracle permutation sends `(x, z)` to `(x, z + f x)`. -/
@[simp] theorem addOracleEquiv_apply [AddGroup R] (f : I → R) (x : I) (z : R) :
    addOracleEquiv f (x, z) = (x, z + f x) := rfl

/-- The inverse additive oracle permutation sends `(x, z)` to `(x, z - f x)`. -/
@[simp] theorem addOracleEquiv_symm_apply [AddGroup R] (f : I → R) (x : I) (z : R) :
    (addOracleEquiv f).symm (x, z) = (x, z - f x) := rfl

/-- Negating the oracle function gives the inverse additive oracle permutation. -/
theorem addOracleEquiv_neg [AddGroup R] (f : I → R) :
    addOracleEquiv (-f) = (addOracleEquiv f).symm := by
  ext p <;> simp [addOracleEquiv, sub_eq_add_neg]

variable [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R] [AddCommGroup R]

/-- The complex permutation matrix implementing addition of `f x` to the output register. -/
noncomputable def AddOracle (f : I → R) : Matrix (I × R) (I × R) ℂ :=
  Equiv.Perm.permMatrix ℂ (addOracleEquiv f).symm

omit [Fintype I] [Fintype R] in

/-- The additive oracle matrix equals the permutation matrix associated with `addOracleEquiv f`. -/
theorem addOracle_eq_permMatrix (f : I → R) :
    AddOracle f = permMatrix (addOracleEquiv f) := by
  ext p q
  simp [AddOracle, permMatrix, Equiv.toPEquiv_apply, ← Equiv.apply_eq_iff_eq_symm_apply, eq_comm]

/-- At output index `(x, z)`, the oracle-transformed amplitude equals the input amplitude at
`(x, z - f x)`. -/
theorem applyGate_addOracle (f : I → R) (ψ : QState (I × R)) (x : I) (z : R) :
    ApplyGate (AddOracle f) ψ (x, z) = ψ (x, z - f x) := by
  simp [ApplyGate, AddOracle, Matrix.permMatrix_mulVec, addOracleEquiv]

/-- The additive oracle sends the basis state at `(x, z)` to the basis state at `(x, z + f x)`. -/
theorem applyGate_addOracle_ket (f : I → R) (x : I) (z : R) :
    ApplyGate (AddOracle f) (Ket (x, z)) = Ket (x, z + f x) := by
  funext p
  rcases p with ⟨y, w⟩
  rw [applyGate_addOracle]
  by_cases h : y = x
  · subst y
    simp [Ket, sub_eq_iff_eq_add]
  · simp [Ket, h]

omit [Fintype I] [Fintype R] in

/-- The additive oracle for the zero function is the identity matrix. -/
@[simp] theorem addOracle_zero : AddOracle (0 : I → R) = 1 := by
  have h : addOracleEquiv (0 : I → R) = Equiv.refl (I × R) := by
    ext p <;> simp [addOracleEquiv]
  simp [AddOracle, h]

/-- The additive oracle for `f + g` is the matrix product of the oracles for `f` and `g`. -/
theorem addOracle_add (f g : I → R) : AddOracle (f + g) = AddOracle f * AddOracle g := by
  have h : addOracleEquiv (f + g) = addOracleEquiv f * addOracleEquiv g := by
    ext p <;> simp [addOracleEquiv, Equiv.Perm.mul_apply, add_left_comm, add_comm]
  change Equiv.Perm.permMatrix ℂ ((addOracleEquiv (f + g))⁻¹) =
    Equiv.Perm.permMatrix ℂ ((addOracleEquiv f)⁻¹) *
      Equiv.Perm.permMatrix ℂ ((addOracleEquiv g)⁻¹)
  rw [h, _root_.mul_inv_rev, Matrix.permMatrix_mul]

omit [Fintype I] [Fintype R] in

/-- The conjugate transpose of an additive oracle is the oracle for the negated function. -/
theorem addOracle_conjTranspose (f : I → R) : (AddOracle f)ᴴ = AddOracle (-f) := by
  simp [AddOracle, addOracleEquiv_neg, Equiv.Perm.inv_def]

/-- Multiplying an additive oracle by the oracle for the negated function gives the identity. -/
theorem addOracle_mul_neg (f : I → R) : AddOracle f * AddOracle (-f) = 1 := by
  rw [← addOracle_add, add_neg_cancel, addOracle_zero]

/-- Multiplying the oracle for the negated function by the original additive oracle gives the
identity. -/
theorem addOracle_neg_mul (f : I → R) : AddOracle (-f) * AddOracle f = 1 := by
  rw [← addOracle_add, neg_add_cancel, addOracle_zero]

/-- Every additive oracle matrix is unitary. -/
theorem addOracle_unitary (f : I → R) : AddOracle f ∈ Matrix.unitaryGroup (I × R) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, addOracle_conjTranspose]
  exact addOracle_neg_mul f

/-- If each function value satisfies `f x + f x = 0`, the additive oracle squares to the
identity. -/
theorem addOracle_mul_self_of_add_self_eq_zero (f : I → R) (hf : ∀ x, f x + f x = 0) :
    AddOracle f * AddOracle f = 1 := by
  rw [← addOracle_add, show f + f = 0 from funext hf, addOracle_zero]

/-- Running the one-query circuit applies the additive oracle matrix to the input state. -/
theorem run_addOracle_query (f : I → R) (ψ : QState (I × R)) :
    Run (AddOracle f) [Step.query] ψ = ApplyGate (AddOracle f) ψ := rfl

/-- A single additive oracle query preserves normalization of the input state. -/
theorem normalized_run_addOracle_query (f : I → R) {ψ : QState (I × R)}
    (hψ : Normalized ψ) : Normalized (Run (AddOracle f) [Step.query] ψ) :=
  normalized_applyGate (addOracle_unitary f) hψ

omit [AddCommGroup R] in

/-- Repeating the one-query circuit `k` times uses exactly `k` queries and no gate macros. -/
theorem addOracle_repeat_query_resources (k : ℕ) :
    QueryCount (RepeatCircuit ([Step.query] : Circuit (I × R)) k) = k ∧
    GateCount (RepeatCircuit ([Step.query] : Circuit (I × R)) k) = 0 := by
  simp [queryCount_repeatCircuit, gateCount_repeatCircuit]

/-- After `k` additive oracle queries, the basis state at `(x, z)` becomes the basis state at
`(x, z + k • f x)`. -/
theorem run_addOracle_repeat_query_ket (f : I → R) (k : ℕ) (x : I) (z : R) :
    Run (AddOracle f) (RepeatCircuit [Step.query] k) (Ket (x, z)) =
      Ket (x, z + k • f x) := by
  induction k generalizing z with
  | zero => simp [RepeatCircuit]
  | succ k ih =>
    simp only [RepeatCircuit, run_append, run_addOracle_query, applyGate_addOracle_ket, ih]
    simp [succ_nsmul, add_assoc, add_comm]

/-- With a zero output register, the queried amplitude at `(x, z)` is `ψ x` when `z = f x` and
zero otherwise. -/
theorem run_addOracle_zero_apply (f : I → R) (ψ : QState I) (x : I) (z : R) :
    Run (AddOracle f) [Step.query] (TensorState ψ (Ket 0)) (x, z) =
      if z = f x then ψ x else 0 := by
  rw [run_addOracle_query, applyGate_addOracle]
  simp [TensorState, Ket, sub_eq_zero]

/-- With a zero output register, the joint Born probability at `(x, z)` is the input probability
at `x` when `z = f x` and zero otherwise. -/
theorem bornProb_run_addOracle_zero (f : I → R) (ψ : QState I) (x : I) (z : R) :
    BornProb (Run (AddOracle f) [Step.query] (TensorState ψ (Ket 0))) (x, z) =
      if z = f x then BornProb ψ x else 0 := by
  unfold BornProb
  rw [run_addOracle_zero_apply]
  split_ifs <;> simp

/-- The output-register probability of a finite set `T` is the input probability of the indices
whose function values belong to `T`. -/
theorem marginalProbRight_run_addOracle_zero (f : I → R) (ψ : QState I) (T : Finset R) :
    MarginalProbRight (Run (AddOracle f) [Step.query] (TensorState ψ (Ket 0))) T =
      MeasureProb ψ (Finset.univ.filter fun x => f x ∈ T) := by
  simp only [MarginalProbRight, MeasureProb, Finset.sum_product,
    bornProb_run_addOracle_zero, Finset.sum_filter]
  simp

/-- An additive oracle query with zero output register preserves every input-register event
probability. -/
theorem marginalProbLeft_run_addOracle_zero (f : I → R) (ψ : QState I) (S : Finset I) :
    MarginalProbLeft (Run (AddOracle f) [Step.query] (TensorState ψ (Ket 0))) S =
      MeasureProb ψ S := by
  simp only [MarginalProbLeft, MeasureProb, Finset.sum_product, bornProb_run_addOracle_zero]
  simp

/-- The probability of output label `z` equals the input probability of the fiber `f x = z`. -/
theorem addOracle_label_weight (f : I → R) (ψ : QState I) (z : R) :
    MarginalProbRight (Run (AddOracle f) [Step.query] (TensorState ψ (Ket 0))) {z} =
      MeasureProb ψ (Finset.univ.filter fun x => f x = z) := by
  simpa using marginalProbRight_run_addOracle_zero f ψ {z}

/-- An output label outside the image of `f` has probability zero after an additive oracle
query. -/
theorem addOracle_label_weight_eq_zero (f : I → R) (ψ : QState I) (z : R)
    (hz : ∀ x, f x ≠ z) :
    MarginalProbRight (Run (AddOracle f) [Step.query] (TensorState ψ (Ket 0))) {z} = 0 := by
  rw [addOracle_label_weight]
  simp [hz, MeasureProb]

/-- Querying a normalized input state tensored with the zero output basis state produces a
normalized joint state. -/
theorem normalized_run_addOracle_zero (f : I → R) {ψ : QState I} (hψ : Normalized ψ) :
    Normalized (Run (AddOracle f) [Step.query] (TensorState ψ (Ket 0))) :=
  normalized_run_addOracle_query f (normalized_tensorState hψ (normalized_ket 0))

end Qatlib.Concepts.HspRecovery.CyclicRecovery
