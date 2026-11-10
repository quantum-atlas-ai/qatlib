/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit

namespace Qatlib.Foundations.PureStateMath

open Matrix
open scoped Kronecker

set_option linter.unusedSectionVars false

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

noncomputable def TensorState (ψ : QState I) (φ : QState J) : QState (I × J) :=
  fun p => ψ p.1 * φ p.2

@[simp] theorem tensorState_apply (ψ : QState I) (φ : QState J) (i : I) (j : J) :
    TensorState ψ φ (i, j) = ψ i * φ j := rfl

theorem tensorState_ket_ket (i : I) (j : J) : TensorState (Ket i) (Ket j) = Ket (i, j) := by
  funext p
  obtain ⟨a, b⟩ := p
  simp only [TensorState, Ket, Prod.mk.injEq]
  by_cases ha : a = i <;> by_cases hb : b = j <;> simp [ha, hb]

theorem bornProb_tensorState (ψ : QState I) (φ : QState J) (i : I) (j : J) :
    BornProb (TensorState ψ φ) (i, j) = BornProb ψ i * BornProb φ j := by
  simp [BornProb, TensorState, mul_pow]

theorem measureProb_tensorState_prod (ψ : QState I) (φ : QState J) (S : Finset I)
    (T : Finset J) :
    MeasureProb (TensorState ψ φ) (S ×ˢ T) = MeasureProb ψ S * MeasureProb φ T := by
  unfold MeasureProb
  rw [Finset.sum_product, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact bornProb_tensorState ψ φ i j

theorem measureProb_tensorState_left {φ : QState J} (hφ : Normalized φ) (ψ : QState I)
    (S : Finset I) :
    MeasureProb (TensorState ψ φ) (S ×ˢ Finset.univ) = MeasureProb ψ S := by
  rw [measureProb_tensorState_prod, measureProb_univ hφ, mul_one]

theorem measureProb_tensorState_right {ψ : QState I} (hψ : Normalized ψ) (φ : QState J)
    (T : Finset J) :
    MeasureProb (TensorState ψ φ) (Finset.univ ×ˢ T) = MeasureProb φ T := by
  rw [measureProb_tensorState_prod, measureProb_univ hψ, one_mul]

theorem normalized_tensorState {ψ : QState I} {φ : QState J} (hψ : Normalized ψ)
    (hφ : Normalized φ) : Normalized (TensorState ψ φ) := by
  have h := measureProb_tensorState_prod ψ φ Finset.univ Finset.univ
  rw [Finset.univ_product_univ, measureProb_univ hψ, measureProb_univ hφ, mul_one] at h
  exact h

noncomputable def TensorGate (U : Matrix I I ℂ) (V : Matrix J J ℂ) :
    Matrix (I × J) (I × J) ℂ := U ⊗ₖ V

theorem tensorGate_apply (U : Matrix I I ℂ) (V : Matrix J J ℂ) (i k : I) (j l : J) :
    TensorGate U V (i, j) (k, l) = U i k * V j l := rfl

theorem tensorGate_mul (U U' : Matrix I I ℂ) (V V' : Matrix J J ℂ) :
    TensorGate U V * TensorGate U' V' = TensorGate (U * U') (V * V') := by
  simp only [TensorGate]
  rw [← Matrix.mul_kronecker_mul]

theorem tensorGate_one : TensorGate (1 : Matrix I I ℂ) (1 : Matrix J J ℂ) = 1 :=
  Matrix.one_kronecker_one

theorem tensorGate_conjTranspose (U : Matrix I I ℂ) (V : Matrix J J ℂ) :
    (TensorGate U V)ᴴ = TensorGate Uᴴ Vᴴ :=
  Matrix.conjTranspose_kronecker U V

theorem tensorGate_unitary {U : Matrix I I ℂ} {V : Matrix J J ℂ}
    (hU : U ∈ Matrix.unitaryGroup I ℂ) (hV : V ∈ Matrix.unitaryGroup J ℂ) :
    TensorGate U V ∈ Matrix.unitaryGroup (I × J) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hU hV ⊢
  rw [TensorGate, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hU, hV,
    Matrix.one_kronecker_one]

theorem applyGate_tensorGate (U : Matrix I I ℂ) (V : Matrix J J ℂ) (ψ : QState I)
    (φ : QState J) :
    ApplyGate (TensorGate U V) (TensorState ψ φ) = TensorState (ApplyGate U ψ) (ApplyGate V φ) := by
  funext p
  obtain ⟨i, j⟩ := p
  simp only [ApplyGate, TensorGate, TensorState, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Matrix.kronecker_apply]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

noncomputable def LiftGate (U : Matrix I I ℂ) : Matrix (I × Bool) (I × Bool) ℂ :=
  TensorGate U 1

theorem liftGate_unitary {U : Matrix I I ℂ} (hU : U ∈ Matrix.unitaryGroup I ℂ) :
    LiftGate U ∈ Matrix.unitaryGroup (I × Bool) ℂ :=
  tensorGate_unitary hU (Submonoid.one_mem _)

theorem applyGate_liftGate (U : Matrix I I ℂ) (ψ : QState I) (χ : QState Bool) :
    ApplyGate (LiftGate U) (TensorState ψ χ) = TensorState (ApplyGate U ψ) χ := by
  rw [LiftGate, applyGate_tensorGate, applyGate_one]

def regAppendEquiv (m n : ℕ) : Reg (m + n) ≃ Reg m × Reg n :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)).trans
    (Equiv.sumArrowEquivProdArrow (Fin m) (Fin n) Bool)

theorem regAppendEquiv_apply_fst (m n : ℕ) (x : Reg (m + n)) (i : Fin m) :
    (regAppendEquiv m n x).1 i = x (Fin.castAdd n i) := rfl

theorem regAppendEquiv_apply_snd (m n : ℕ) (x : Reg (m + n)) (j : Fin n) :
    (regAppendEquiv m n x).2 j = x (Fin.natAdd m j) := rfl

end Qatlib.Foundations.PureStateMath
