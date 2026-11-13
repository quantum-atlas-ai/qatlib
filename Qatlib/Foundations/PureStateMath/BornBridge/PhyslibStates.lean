/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import QuantumInfo.States.Mixed.MState

/-!
# Equivalences with Physlib state representations

This module identifies Qatlib's normalized vectors and density matrices with Physlib's `Ket` and
`MState` representations. The equivalences preserve the underlying amplitudes or matrices and
are compatible with pure-state formation, tensor products, and partial trace, implementing the
standard state representations of quantum information [Watrous2018].

It also identifies `SchattenOne` with Physlib's matrix trace norm.

## Main statements

* `normalizedStateEquivKet`: Normalized Qatlib vectors correspond to Physlib kets.
* `densityMatrixEquivMState`: Positive semidefinite trace-one matrices correspond to mixed
  states.
* `densityOperatorEquivMState_partialTrace`: The state equivalence commutes with tracing out the
  right subsystem.
* `schattenOne_eq_physlib_traceNorm`: The two trace-norm definitions agree.

## References

* [Watrous, 2018][Watrous2018]
-/

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Foundations.PureStateMath.BornBridge

open scoped ComplexOrder

section Pure

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The equivalence between normalized Qatlib state vectors and Physlib kets, preserving the
underlying vector. -/
noncomputable def normalizedStateEquivKet (I : Type*) [Fintype I] [DecidableEq I] :
    {ψ : QState I // Normalized ψ} ≃ _root_.Ket I where
  toFun ψ := { vec := ψ.val, normalized' := ψ.property }
  invFun ψ := ⟨ψ.vec, ψ.normalized'⟩
  left_inv ψ := by
    cases ψ
    rfl
  right_inv ψ := by
    cases ψ
    rfl

/-- Converting a normalized state to a Physlib ket leaves its underlying vector unchanged. -/
@[simp] theorem normalizedStateEquivKet_vec (ψ : {ψ : QState I // Normalized ψ}) :
    (normalizedStateEquivKet I ψ).vec = ψ.val := rfl

/-- Every amplitude of the converted Physlib ket equals the corresponding amplitude of the
original normalized state. -/
@[simp] theorem normalizedStateEquivKet_apply
    (ψ : {ψ : QState I // Normalized ψ}) (i : I) :
    normalizedStateEquivKet I ψ i = ψ.val i := rfl

/-- Converting a Physlib ket back to a normalized Qatlib state yields its underlying vector. -/
@[simp] theorem normalizedStateEquivKet_symm_val (ψ : _root_.Ket I) :
    ((normalizedStateEquivKet I).symm ψ).val = ψ.vec := rfl

/-- The normalized-state equivalence sends a Qatlib basis ket to the corresponding Physlib basis
ket. -/
@[simp] theorem normalizedStateEquivKet_basis (i : I) :
    normalizedStateEquivKet I ⟨Qatlib.Foundations.PureStateMath.Ket i, normalized_ket i⟩ =
      _root_.Ket.basis i := by
  apply _root_.Ket.ext
  intro j
  simp [normalizedStateEquivKet, Qatlib.Foundations.PureStateMath.Ket, _root_.Ket.basis,
    _root_.Ket.coe_fun_eq, eq_comm]

/-- The matrix of the Physlib pure state associated with a converted normalized vector is its
outer product. -/
@[simp] theorem pure_normalizedStateEquivKet_m
    (ψ : {ψ : QState I // Normalized ψ}) :
    (MState.pure (normalizedStateEquivKet I ψ)).m =
      fun i j => ψ.val i * star (ψ.val j) := by
  rfl

end Pure

section Mixed

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The equivalence between positive semidefinite trace-one matrices and Physlib mixed states. -/
noncomputable def densityMatrixEquivMState (I : Type*) [Fintype I] [DecidableEq I] :
    {ρ : Matrix I I ℂ // ρ.PosSemidef ∧ Matrix.trace ρ = 1} ≃ MState I where
  toFun ρ :=
    { M := ⟨ρ.val, ρ.property.1.1⟩
      nonneg := HermitianMat.zero_le_iff.mpr ρ.property.1
      tr := (HermitianMat.trace_eq_one_iff
        (⟨ρ.val, ρ.property.1.1⟩ : HermitianMat I ℂ)).mpr ρ.property.2 }
  invFun ρ := ⟨ρ.m, ρ.psd, ρ.tr'⟩
  left_inv ρ := by
    apply Subtype.ext
    rfl
  right_inv ρ := by
    apply MState.ext_m
    rfl

/-- Converting a density matrix to a Physlib mixed state preserves its underlying matrix. -/
@[simp] theorem densityMatrixEquivMState_m
    (ρ : {ρ : Matrix I I ℂ // ρ.PosSemidef ∧ Matrix.trace ρ = 1}) :
    (densityMatrixEquivMState I ρ).m = ρ.val := rfl

/-- Converting a Physlib mixed state back to a density matrix yields its underlying matrix. -/
@[simp] theorem densityMatrixEquivMState_symm_val (ρ : MState I) :
    ((densityMatrixEquivMState I).symm ρ).val = ρ.m := rfl

/-- The equivalence between Qatlib density operators of dimension `D` and Physlib mixed states
indexed by `Fin D`. -/
noncomputable def densityOperatorEquivMState (D : ℕ) :
    DensityOperator D ≃ MState (Fin D) :=
  densityMatrixEquivMState (Fin D)

/-- The density-operator equivalence preserves the underlying matrix. -/
@[simp] theorem densityOperatorEquivMState_m {D : ℕ} (ρ : DensityOperator D) :
    (densityOperatorEquivMState D ρ).m = ρ.val := rfl

/-- The inverse density-operator equivalence returns the underlying matrix of the Physlib mixed
state. -/
@[simp] theorem densityOperatorEquivMState_symm_val {D : ℕ} (ρ : MState (Fin D)) :
    ((densityOperatorEquivMState D).symm ρ).val = ρ.m := rfl

/-- The matrix of the Physlib pure state obtained from a normalized Qatlib vector satisfies
`IsPureDensityOperator`. -/
theorem pure_normalizedStateEquivKet_isPureDensityOperator {D : ℕ}
    (ψ : {ψ : QState (Fin D) // Normalized ψ}) :
    IsPureDensityOperator (MState.pure (normalizedStateEquivKet (Fin D) ψ)).m := by
  refine ⟨⟨(MState.pure _).psd, (MState.pure _).tr'⟩, ?_⟩
  exact MState.pure_mul_self _

/-- The density-matrix equivalence sends the outer product of a normalized vector to the Physlib
pure state of the corresponding ket. -/
theorem densityMatrixEquivMState_pure {I : Type*} [Fintype I] [DecidableEq I]
    {ψ : QState I} (hψ : Normalized ψ) :
    densityMatrixEquivMState I
      ⟨outerProduct ψ, (outerProduct_density hψ).1, (outerProduct_density hψ).2⟩
      = MState.pure (normalizedStateEquivKet I ⟨ψ, hψ⟩) := by
  apply MState.ext_m
  rw [densityMatrixEquivMState_m, pure_normalizedStateEquivKet_m]
  ext i j
  show outerProduct ψ i j = ψ i * star (ψ j)
  rw [outerProduct_apply]
  rfl

open scoped ComplexOrder in

/-- The tensor product of two positive semidefinite matrices is positive semidefinite. -/
theorem posSemidef_tensorGate {I : Type*} [Fintype I] [DecidableEq I]
    {J : Type*} [Fintype J] [DecidableEq J]
    {ρ : Matrix I I ℂ} (hρ : ρ.PosSemidef) {σ : Matrix J J ℂ} (hσ : σ.PosSemidef) :
    (TensorGate ρ σ).PosSemidef :=
  Matrix.PosSemidef.PosSemidef_kronecker hρ hσ

/-- The trace of `TensorGate ρ σ` is the product of the traces of `ρ` and `σ`. -/
theorem trace_tensorGate {I : Type*} [Fintype I] [DecidableEq I]
    {J : Type*} [Fintype J] [DecidableEq J]
    (ρ : Matrix I I ℂ) (σ : Matrix J J ℂ) :
    Matrix.trace (TensorGate ρ σ) = Matrix.trace ρ * Matrix.trace σ :=
  Matrix.trace_kronecker ρ σ

/-- The tensor product of converted density matrices equals the conversion of their matrix
tensor product. -/
theorem densityMatrixEquivMState_prod {I : Type*} [Fintype I] [DecidableEq I]
    {J : Type*} [Fintype J] [DecidableEq J]
    {ρ : Matrix I I ℂ} (hρ : ρ.PosSemidef) (htrρ : Matrix.trace ρ = 1)
    {σ : Matrix J J ℂ} (hσ : σ.PosSemidef) (htrσ : Matrix.trace σ = 1) :
    (densityMatrixEquivMState I ⟨ρ, hρ, htrρ⟩) ⊗ᴹ (densityMatrixEquivMState J ⟨σ, hσ, htrσ⟩)
      = densityMatrixEquivMState (I × J)
          ⟨TensorGate ρ σ, posSemidef_tensorGate hρ hσ, by
            rw [trace_tensorGate, htrρ, htrσ, mul_one]⟩ := by
  apply MState.ext_m
  rfl

/-- The product of two converted pure states equals the mixed state represented by the tensor
product of their outer products. -/
theorem densityMatrixEquivMState_pure_prod {I : Type*} [Fintype I] [DecidableEq I]
    {J : Type*} [Fintype J] [DecidableEq J]
    {ψ : QState I} (hψ : Normalized ψ) {φ : QState J} (hφ : Normalized φ) :
    (MState.pure (normalizedStateEquivKet I ⟨ψ, hψ⟩))
      ⊗ᴹ (MState.pure (normalizedStateEquivKet J ⟨φ, hφ⟩))
      = densityMatrixEquivMState (I × J)
          ⟨TensorGate (outerProduct ψ) (outerProduct φ),
            posSemidef_tensorGate (outerProduct_density hψ).1 (outerProduct_density hφ).1,
            by rw [trace_tensorGate, (outerProduct_density hψ).2, (outerProduct_density hφ).2,
              mul_one]⟩ := by
  rw [← densityMatrixEquivMState_pure hψ, ← densityMatrixEquivMState_pure hφ,
    densityMatrixEquivMState_prod ((outerProduct_density hψ).1) ((outerProduct_density hψ).2)
      ((outerProduct_density hφ).1) ((outerProduct_density hφ).2)]

end Mixed

section PartialTrace

variable {D E : ℕ}

/-- Qatlib's `PartialTrace` equals Physlib's `Matrix.traceRight` on bipartite matrices. -/
theorem partialTrace_eq_physlib_traceRight
    (A : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) :
    PartialTrace A = Matrix.traceRight A := rfl

/-- The partial trace of a Physlib mixed state's matrix is the matrix of its right-subsystem
trace. -/
@[simp] theorem partialTrace_mState (ρ : MState (Fin D × Fin E)) :
    PartialTrace ρ.m = ρ.traceRight.m := rfl

/-- Converting a partially traced density matrix gives the same Physlib mixed state as
converting first and then tracing out the right subsystem. -/
theorem densityOperatorEquivMState_partialTrace
    (A : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ)
    (hA : A.PosSemidef) (htrace : Matrix.trace A = 1) :
    densityOperatorEquivMState D
        ⟨PartialTrace A, isDensityOperator_partialTrace hA htrace⟩ =
      (densityMatrixEquivMState (Fin D × Fin E) ⟨A, hA, htrace⟩).traceRight := by
  apply MState.ext_m
  rfl

/-- The inverse density-operator equivalence applied after Physlib's right trace yields the
partial trace of the original matrix. -/
@[simp] theorem densityOperatorEquivMState_symm_traceRight
    (ρ : MState (Fin D × Fin E)) :
    ((densityOperatorEquivMState D).symm ρ.traceRight).val = PartialTrace ρ.m := rfl

end PartialTrace

section TraceNorm

open scoped MatrixOrder

/-- Qatlib's `SchattenOne` equals Physlib's `Matrix.traceNorm` for every finite-dimensional
operator. -/
@[simp] theorem schattenOne_eq_physlib_traceNorm {D : ℕ} (A : Operator D) :
    SchattenOne A = Matrix.traceNorm A := by
  unfold SchattenOne Matrix.traceNorm
  rw [CFC.sqrt_eq_real_sqrt (A.conjTranspose * A)
    (Matrix.nonneg_iff_posSemidef.mpr A.posSemidef_conjTranspose_mul_self),
    cfcₙ_eq_cfc]
  rfl

end TraceNorm

end Qatlib.Foundations.PureStateMath.BornBridge
