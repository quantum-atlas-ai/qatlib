/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.LcuFrame.Moments
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Foundations.MatrixGeometry.LcuFrame
set_option autoImplicit false
noncomputable section
open Matrix
variable {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]

def embedding (β : J → ℝ) : Matrix (J × I) I ℂ :=
  fun ji x => if ji.2=x then (β ji.1 : ℂ) else 0

def select (P : J → Matrix I I ℂ) : Matrix (J × I) (J × I) ℂ :=
  fun ji kl => if ji.1=kl.1 then P ji.1 ji.2 kl.2 else 0

omit [Fintype J] [DecidableEq J] in

theorem embedding_mulVec (β : J → ℝ) (φ : State I) : embedding (I := I) β *ᵥ φ = phi0 β φ := by
  ext ji
  simp [embedding, phi0, Matrix.mulVec, dotProduct]

omit [DecidableEq I] in

theorem select_mulVec (P : J → Matrix I I ℂ) (ψ : State (J × I)) (j : J) (i : I) :
    (select P *ᵥ ψ) (j,i) = ∑ x, P j i x * ψ (j,x) := by
  simp [select, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]

omit [DecidableEq I] in

theorem select_phi0 (β : J → ℝ) (P : J → Matrix I I ℂ) (φ : State I) :
    select P *ᵥ phi0 β φ = Vphi0 β P φ := by
  ext ji
  rcases ji with ⟨j,i⟩
  rw [select_mulVec]
  simp only [phi0, Vphi0, Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

omit [DecidableEq J] in

theorem embedding_gram (β : J → ℝ) (hβ : ∑ j, β j^2=1) :
    (embedding (I := I) β)ᴴ * embedding (I := I) β = 1 := by
  ext x y
  by_cases h : x=y
  · subst y
    have hc : (∑ j, (β j : ℂ)^2)=1 := by exact_mod_cast hβ
    simpa [embedding, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      apply_ite, pow_two] using hc
  · simp [embedding, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      apply_ite, h, Ne.symm h]

theorem select_embedding (β : J → ℝ) (P : J → Matrix I I ℂ) :
    select P * embedding (I := I) β = fun ji x => (β ji.1 : ℂ) * P ji.1 ji.2 x := by
  ext ji x
  rcases ji with ⟨j,i⟩
  simp [Matrix.mul_apply, select, embedding, Fintype.sum_prod_type, mul_comm]

theorem compression (β : J → ℝ) (P : J → Matrix I I ℂ) :
    (embedding (I := I) β)ᴴ * select P * embedding (I := I) β = ham β P := by
  rw [Matrix.mul_assoc, select_embedding]
  ext x y
  simp [embedding, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    ham, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, pow_two, mul_assoc, apply_ite]

omit [DecidableEq I] in

theorem select_mul (P Q : J → Matrix I I ℂ) :
    select P * select Q = select (fun j => P j * Q j) := by
  ext ji kl
  rcases ji with ⟨j,i⟩
  rcases kl with ⟨k,l⟩
  by_cases h : j=k
  · subst k
    simp [select, Matrix.mul_apply, Fintype.sum_prod_type]
  · simp [select, Matrix.mul_apply, Fintype.sum_prod_type, h]

omit [Fintype J] [Fintype I] in

theorem select_one : select (fun _ : J => (1 : Matrix I I ℂ)) = 1 := by
  ext ji kl
  rcases ji with ⟨j,i⟩
  rcases kl with ⟨k,l⟩
  by_cases h : j=k
  · subst k; simp [select, Matrix.one_apply]
  · simp [select, h]

theorem select_square (P : J → Matrix I I ℂ) (hP : ∀ j, P j * P j=1) :
    select P * select P = 1 := by
  rw [select_mul]
  simp only [hP]
  exact select_one

omit [Fintype J] [Fintype I] [DecidableEq I] in

theorem select_adjoint (P : J → Matrix I I ℂ) (hP : ∀ j, (P j)ᴴ=P j) :
    (select P)ᴴ=select P := by
  ext ji kl
  rcases ji with ⟨j,i⟩
  rcases kl with ⟨k,l⟩
  by_cases h : j=k
  · subst k
    simpa [select, Matrix.conjTranspose_apply] using congrFun (congrFun (hP j) i) l
  · simp [select, Matrix.conjTranspose_apply, h, Ne.symm h]

def signalProjector (β : J → ℝ) : Matrix (J × I) (J × I) ℂ :=
    embedding (I := I) β * (embedding (I := I) β)ᴴ

omit [DecidableEq J] in

theorem embedding_adjoint_phi0 (β : J → ℝ) (hβ : ∑ j, β j^2=1) (φ : State I) :
    (embedding (I := I) β)ᴴ *ᵥ phi0 β φ = φ := by
  rw [← embedding_mulVec, Matrix.mulVec_mulVec, embedding_gram β hβ, Matrix.one_mulVec]

theorem embedding_adjoint_Vphi0 (β : J → ℝ) (P : J → Matrix I I ℂ) (φ : State I) :
    (embedding (I := I) β)ᴴ *ᵥ Vphi0 β P φ = ham β P *ᵥ φ := by
  rw [← select_phi0, ← embedding_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    compression]

theorem embedding_adjoint_phi1 (β : J → ℝ) (P : J → Matrix I I ℂ) (φ : State I) (E : ℝ)
    (hβ : ∑ j, β j^2=1) (heig : ham β P *ᵥ φ=(E : ℂ) • φ) :
    (embedding (I := I) β)ᴴ *ᵥ phi1 β P φ E = 0 := by
  change (embedding (I := I) β)ᴴ *ᵥ
    (((Real.sqrt (1-E^2) : ℂ))⁻¹ • (Vphi0 β P φ - (E : ℂ) • phi0 β φ))=0
  rw [Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_smul,
    embedding_adjoint_Vphi0, embedding_adjoint_phi0 β hβ, heig, sub_self, smul_zero]

end
end Qatlib.Foundations.MatrixGeometry.LcuFrame
