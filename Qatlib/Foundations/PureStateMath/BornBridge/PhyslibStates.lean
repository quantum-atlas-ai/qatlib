/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import QuantumInfo.States.Mixed.MState
set_option warningAsError false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Foundations.PureStateMath.BornBridge

open scoped ComplexOrder

section Pure

variable {I : Type*} [Fintype I] [DecidableEq I]

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

@[simp] theorem normalizedStateEquivKet_vec (ψ : {ψ : QState I // Normalized ψ}) :
    (normalizedStateEquivKet I ψ).vec = ψ.val := rfl

@[simp] theorem normalizedStateEquivKet_apply
    (ψ : {ψ : QState I // Normalized ψ}) (i : I) :
    normalizedStateEquivKet I ψ i = ψ.val i := rfl

@[simp] theorem normalizedStateEquivKet_symm_val (ψ : _root_.Ket I) :
    ((normalizedStateEquivKet I).symm ψ).val = ψ.vec := rfl

@[simp] theorem normalizedStateEquivKet_basis (i : I) :
    normalizedStateEquivKet I ⟨Qatlib.Foundations.PureStateMath.Ket i, normalized_ket i⟩ =
      _root_.Ket.basis i := by
  apply _root_.Ket.ext
  intro j
  simp [normalizedStateEquivKet, Qatlib.Foundations.PureStateMath.Ket, _root_.Ket.basis,
    _root_.Ket.coe_fun_eq, eq_comm]

@[simp] theorem pure_normalizedStateEquivKet_m
    (ψ : {ψ : QState I // Normalized ψ}) :
    (MState.pure (normalizedStateEquivKet I ψ)).m =
      fun i j => ψ.val i * star (ψ.val j) := by
  rfl

end Pure

section Mixed

variable {I : Type*} [Fintype I] [DecidableEq I]

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

@[simp] theorem densityMatrixEquivMState_m
    (ρ : {ρ : Matrix I I ℂ // ρ.PosSemidef ∧ Matrix.trace ρ = 1}) :
    (densityMatrixEquivMState I ρ).m = ρ.val := rfl

@[simp] theorem densityMatrixEquivMState_symm_val (ρ : MState I) :
    ((densityMatrixEquivMState I).symm ρ).val = ρ.m := rfl

noncomputable def densityOperatorEquivMState (D : ℕ) :
    DensityOperator D ≃ MState (Fin D) :=
  densityMatrixEquivMState (Fin D)

@[simp] theorem densityOperatorEquivMState_m {D : ℕ} (ρ : DensityOperator D) :
    (densityOperatorEquivMState D ρ).m = ρ.val := rfl

@[simp] theorem densityOperatorEquivMState_symm_val {D : ℕ} (ρ : MState (Fin D)) :
    ((densityOperatorEquivMState D).symm ρ).val = ρ.m := rfl

theorem pure_normalizedStateEquivKet_isPureDensityOperator {D : ℕ}
    (ψ : {ψ : QState (Fin D) // Normalized ψ}) :
    IsPureDensityOperator (MState.pure (normalizedStateEquivKet (Fin D) ψ)).m := by
  refine ⟨⟨(MState.pure _).psd, (MState.pure _).tr'⟩, ?_⟩
  exact MState.pure_mul_self _

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

theorem posSemidef_tensorGate {I : Type*} [Fintype I] [DecidableEq I]
    {J : Type*} [Fintype J] [DecidableEq J]
    {ρ : Matrix I I ℂ} (hρ : ρ.PosSemidef) {σ : Matrix J J ℂ} (hσ : σ.PosSemidef) :
    (TensorGate ρ σ).PosSemidef :=
  Matrix.PosSemidef.PosSemidef_kronecker hρ hσ

theorem trace_tensorGate {I : Type*} [Fintype I] [DecidableEq I]
    {J : Type*} [Fintype J] [DecidableEq J]
    (ρ : Matrix I I ℂ) (σ : Matrix J J ℂ) :
    Matrix.trace (TensorGate ρ σ) = Matrix.trace ρ * Matrix.trace σ :=
  Matrix.trace_kronecker ρ σ

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

theorem partialTrace_eq_physlib_traceRight
    (A : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) :
    PartialTrace A = Matrix.traceRight A := rfl

@[simp] theorem partialTrace_mState (ρ : MState (Fin D × Fin E)) :
    PartialTrace ρ.m = ρ.traceRight.m := rfl

theorem densityOperatorEquivMState_partialTrace
    (A : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ)
    (hA : A.PosSemidef) (htrace : Matrix.trace A = 1) :
    densityOperatorEquivMState D
        ⟨PartialTrace A, isDensityOperator_partialTrace hA htrace⟩ =
      (densityMatrixEquivMState (Fin D × Fin E) ⟨A, hA, htrace⟩).traceRight := by
  apply MState.ext_m
  rfl

@[simp] theorem densityOperatorEquivMState_symm_traceRight
    (ρ : MState (Fin D × Fin E)) :
    ((densityOperatorEquivMState D).symm ρ.traceRight).val = PartialTrace ρ.m := rfl

end PartialTrace

section TraceNorm

open scoped MatrixOrder

@[simp] theorem schattenOne_eq_physlib_traceNorm {D : ℕ} (A : Operator D) :
    SchattenOne A = Matrix.traceNorm A := by
  unfold SchattenOne Matrix.traceNorm
  rw [CFC.sqrt_eq_real_sqrt (A.conjTranspose * A)
    (Matrix.nonneg_iff_posSemidef.mpr A.posSemidef_conjTranspose_mul_self),
    cfcₙ_eq_cfc]
  rfl

end TraceNorm

end Qatlib.Foundations.PureStateMath.BornBridge
