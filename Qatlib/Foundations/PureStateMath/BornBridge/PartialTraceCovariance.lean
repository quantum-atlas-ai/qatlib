/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge

/-!
# Partial trace under local matrix evolution

This module proves that `PartialTrace` commutes with matrix multiplication on the retained
subsystem and with finite linear combinations. It applies these identities to pure states,
weighted mixtures, and local unitary evolution of density operators, following the standard
reduced-state calculus [Watrous2018].

## Main statements

* `partialTrace_tensorLeft_sandwich`: Local left and right factors pass through the partial
  trace.
* `partialTrace_tensorLeft_mixture`: Local conjugation and partial trace distribute over
  weighted finite sums.
* `partialTrace_tensorLeft_unitary_evolution`: Local unitary evolution produces the conjugated
  reduced density operator.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Foundations.PureStateMath.BornBridge

/-- Applying a matrix to a state transforms its outer product by left multiplication with that
matrix and right multiplication with its conjugate transpose. -/
private theorem outerProduct_applyGate_matrix {I : Type*} [Fintype I]
    (W : Matrix I I ℂ) (ψ : QState I) :
    outerProduct (ApplyGate W ψ) = W * outerProduct ψ * W.conjTranspose := by
  ext i j
  have starNorm : ∀ z : ℂ, (starRingEnd ℂ) z = star z := fun _ => rfl
  simp only [outerProduct_apply, ApplyGate, Matrix.mulVec, dotProduct, Matrix.mul_apply,
    Matrix.conjTranspose_apply, map_sum, map_mul]
  simp only [starNorm]
  rw [Finset.mul_sum]
  simp only [Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- Left multiplication by `A ⊗ 1` passes through the partial trace as left multiplication by
`A`. -/
theorem partialTrace_mul_tensorLeft (D E : ℕ) (A : Operator D)
    (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) :
    PartialTrace (TensorGate A (1 : Operator E) * ρ) = A * PartialTrace ρ := by
  ext i j
  simp only [PartialTrace, Matrix.mul_apply, tensorGate_apply, Matrix.one_apply,
    Fintype.sum_prod_type, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Right multiplication by `A ⊗ 1` passes through the partial trace as right multiplication by
`A`. -/
theorem partialTrace_tensorLeft_mul (D E : ℕ) (A : Operator D)
    (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) :
    PartialTrace (ρ * TensorGate A (1 : Operator E)) = PartialTrace ρ * A := by
  ext i j
  simp only [PartialTrace, Matrix.mul_apply, tensorGate_apply, Matrix.one_apply,
    Fintype.sum_prod_type, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- The partial trace of a matrix sandwiched between `A ⊗ 1` and the adjoint of `B ⊗ 1` is `A *
PartialTrace ρ * B.conjTranspose`. -/
theorem partialTrace_tensorLeft_sandwich (D E : ℕ) (A B : Operator D)
    (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) :
    PartialTrace (TensorGate A (1 : Operator E) * ρ *
        (TensorGate B (1 : Operator E)).conjTranspose)
      = A * PartialTrace ρ * B.conjTranspose := by
  simp only [tensorGate_conjTranspose, Matrix.conjTranspose_one]
  rw [Matrix.mul_assoc, partialTrace_mul_tensorLeft, partialTrace_tensorLeft_mul, mul_assoc]

/-- Applying `A ⊗ 1` to a pure-state vector conjugates its reduced outer product by `A`. -/
theorem partialTrace_outerProduct_apply_tensorLeft (D E : ℕ) (A : Operator D)
    (ψ : QState (Fin D × Fin E)) :
    PartialTrace (outerProduct (ApplyGate (TensorGate A (1 : Operator E)) ψ))
      = A * PartialTrace (outerProduct ψ) * A.conjTranspose := by
  rw [outerProduct_applyGate_matrix, partialTrace_tensorLeft_sandwich]

/-- Partial trace preserves matrix addition. -/
theorem partialTrace_add {D E : ℕ}
    (ρ σ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) :
    PartialTrace (ρ + σ) = PartialTrace ρ + PartialTrace σ := by
  ext i j
  simp [PartialTrace, Finset.sum_add_distrib]

/-- Partial trace commutes with multiplication by a complex scalar. -/
theorem partialTrace_smul {D E : ℕ} (c : ℂ)
    (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) :
    PartialTrace (c • ρ) = c • PartialTrace ρ := by
  ext i j
  change (∑ a : Fin E, c * ρ (i, a) (j, a)) = c * ∑ a : Fin E, ρ (i, a) (j, a)
  exact (Finset.mul_sum _ _ _).symm

/-- Partial trace commutes with finite sums of bipartite matrices. -/
theorem partialTrace_sum {D E : ℕ} {J : Type*} [Fintype J]
    (ρ : J → Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) :
    PartialTrace (∑ j, ρ j) = ∑ j, PartialTrace (ρ j) := by
  ext i k
  simp only [PartialTrace, Matrix.sum_apply]
  exact Finset.sum_comm

/-- Local conjugation and partial trace distribute over a finite complex-weighted sum,
conjugating each reduced matrix by `A`. -/
theorem partialTrace_tensorLeft_mixture {J : Type*} [Fintype J]
    (D E : ℕ) (A : Operator D) (w : J → ℂ)
    (ρ : J → Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) :
    PartialTrace (TensorGate A (1 : Operator E) * (∑ j, w j • ρ j) *
        (TensorGate A (1 : Operator E)).conjTranspose)
      = ∑ j, w j • (A * PartialTrace (ρ j) * A.conjTranspose) := by
  rw [partialTrace_tensorLeft_sandwich, partialTrace_sum]
  simp_rw [partialTrace_smul]
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by rw [mul_smul_comm, smul_mul_assoc]

open scoped ComplexOrder

/-- Local unitary conjugation of a positive semidefinite trace-one matrix has a reduced density
operator equal to `U * PartialTrace ρ * U.conjTranspose`. -/
theorem partialTrace_tensorLeft_unitary_evolution (D E : ℕ) (U : Operator D)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ)
    (hρ : ρ.PosSemidef) (htrace : Matrix.trace ρ = 1) :
    IsDensityOperator
        (PartialTrace (TensorGate U (1 : Operator E) * ρ *
          (TensorGate U (1 : Operator E)).conjTranspose)) ∧
      PartialTrace (TensorGate U (1 : Operator E) * ρ *
          (TensorGate U (1 : Operator E)).conjTranspose)
        = U * PartialTrace ρ * U.conjTranspose := by
  have hred : IsDensityOperator (PartialTrace ρ) :=
    isDensityOperator_partialTrace hρ htrace
  have hcov := partialTrace_tensorLeft_sandwich D E U U ρ
  have hU' : U.conjTranspose * U = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff').mp hU
    rwa [Matrix.star_eq_conjTranspose] at h
  refine ⟨?_, hcov⟩
  rw [hcov]
  refine ⟨hred.1.mul_mul_conjTranspose_same U, ?_⟩
  calc Matrix.trace (U * PartialTrace ρ * U.conjTranspose)
      = Matrix.trace (U.conjTranspose * (U * PartialTrace ρ)) :=
        Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((U.conjTranspose * U) * PartialTrace ρ) := by
        rw [Matrix.mul_assoc]
    _ = 1 := by rw [hU', Matrix.one_mul, hred.2]

end Qatlib.Foundations.PureStateMath.BornBridge
