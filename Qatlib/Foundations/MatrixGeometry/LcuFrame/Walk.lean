/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.LcuFrame.Normalization
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Foundations.MatrixGeometry.LcuFrame
set_option autoImplicit false
noncomputable section
open Matrix
variable {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]

def reflection (β : J → ℝ) : Matrix (J × I) (J × I) ℂ :=
  1 - (2 : ℂ) • signalProjector β

def walk (β : J → ℝ) (P : J → Matrix I I ℂ) : Matrix (J × I) (J × I) ℂ :=
  -(reflection β * select P)

omit [DecidableEq J] in

theorem signalProjector_square (β : J → ℝ) (hβ : ∑ j, β j^2=1) :
    signalProjector (I := I) β * signalProjector β = signalProjector β := by
  unfold signalProjector
  calc
    _ = embedding (I := I) β * ((embedding (I := I) β)ᴴ * embedding (I := I) β) * (embedding (I := I) β)ᴴ := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (embedding (I := I) β)ᴴ]
      exact (Matrix.mul_assoc _ _ _).symm
    _ = _ := by rw [embedding_gram β hβ]; simp

omit [Fintype J] [DecidableEq J] in

theorem signalProjector_adjoint (β : J → ℝ) :
    (signalProjector (I := I) β)ᴴ=signalProjector β := by
  simp [signalProjector,Matrix.conjTranspose_mul]

theorem reflection_square (β : J → ℝ) (hβ : ∑ j, β j^2=1) :
    reflection (I := I) β * reflection β = 1 := by
  have hp := signalProjector_square (I := I) β hβ
  unfold reflection
  simp only [sub_mul,mul_sub,one_mul,mul_one,smul_mul_assoc,mul_smul_comm,hp]
  module

omit [Fintype J] in

theorem reflection_adjoint (β : J → ℝ) : (reflection (I := I) β)ᴴ=reflection β := by
  simp [reflection,signalProjector_adjoint]

theorem walk_unitary (β : J → ℝ) (P : J → Matrix I I ℂ) (hβ : ∑ j, β j^2=1)
    (hPH : ∀ j, (P j)ᴴ=P j) (hP2 : ∀ j, P j*P j=1) :
    walk β P ∈ Matrix.unitaryGroup (J × I) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose]
  simp only [walk,Matrix.conjTranspose_neg,Matrix.conjTranspose_mul,reflection_adjoint,
    select_adjoint P hPH,neg_mul_neg]
  calc
    _ = select P * (reflection β * reflection β) * select P := by simp only [mul_assoc]
    _ = 1 := by rw [reflection_square β hβ]; simpa using select_square P hP2

theorem reflection_phi0 (β : J → ℝ) (φ : State I) (hβ : ∑ j, β j^2=1) :
    reflection β *ᵥ phi0 β φ = -phi0 β φ := by
  simp only [reflection,Matrix.sub_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec,
    signalProjector,← Matrix.mulVec_mulVec,embedding_adjoint_phi0 β hβ,embedding_mulVec]
  module

theorem reflection_phi1 (β : J → ℝ) (P : J → Matrix I I ℂ) (φ : State I) (E : ℝ)
    (hβ : ∑ j, β j^2=1) (heig : ham β P *ᵥ φ=(E : ℂ) • φ) :
    reflection β *ᵥ phi1 β P φ E = phi1 β P φ E := by
  simp only [reflection,Matrix.sub_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec,
    signalProjector,← Matrix.mulVec_mulVec,embedding_adjoint_phi1 β P φ E hβ heig,
    Matrix.mulVec_zero,smul_zero,sub_zero]

omit [Fintype J] [DecidableEq J] [DecidableEq I] in

theorem Vphi0_decompose (β : J → ℝ) (P : J → Matrix I I ℂ) (φ : State I) (E : ℝ)
    (hE : E^2<1) :
    Vphi0 β P φ = (E : ℂ) • phi0 β φ + (Real.sqrt (1-E^2) : ℂ) • phi1 β P φ E := by
  have hs : (Real.sqrt (1-E^2) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by nlinarith : (0:ℝ)<1-E^2)).ne'
  change _ = (E : ℂ) • phi0 β φ + (Real.sqrt (1-E^2) : ℂ) •
    ((Real.sqrt (1-E^2) : ℂ)⁻¹ • (Vphi0 β P φ - (E : ℂ) • phi0 β φ))
  rw [smul_smul,mul_inv_cancel₀ hs,one_smul]
  module

theorem select_phi1 (β : J → ℝ) (P : J → Matrix I I ℂ) (φ : State I) (E : ℝ)
    (hP2 : ∀ j, P j*P j=1) (hE : E^2<1) :
    select P *ᵥ phi1 β P φ E =
      (Real.sqrt (1-E^2) : ℂ) • phi0 β φ - (E : ℂ) • phi1 β P φ E := by
  have hs : (Real.sqrt (1-E^2) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by nlinarith : (0:ℝ)<1-E^2)).ne'
  have hsq : (Real.sqrt (1-E^2) : ℂ)^2 = 1-(E : ℂ)^2 := by
    have h := Real.sq_sqrt (by nlinarith : (0:ℝ)≤1-E^2)
    exact_mod_cast h
  have hVV : select P *ᵥ Vphi0 β P φ = phi0 β φ := by
    rw [← select_phi0,Matrix.mulVec_mulVec,select_square P hP2,Matrix.one_mulVec]
  change select P *ᵥ ((Real.sqrt (1-E^2) : ℂ)⁻¹ •
    (Vphi0 β P φ - (E : ℂ) • phi0 β φ)) = _
  rw [Matrix.mulVec_smul,Matrix.mulVec_sub,Matrix.mulVec_smul,hVV,select_phi0,
    Vphi0_decompose β P φ E hE]
  ext i
  simp only [Pi.smul_apply,Pi.sub_apply,Pi.add_apply,smul_eq_mul]
  field_simp
  linear_combination -(phi0 β φ i) * hsq

theorem walk_phi0 (β : J → ℝ) (P : J → Matrix I I ℂ) (φ : State I) (E : ℝ)
    (hβ : ∑ j, β j^2=1) (heig : ham β P *ᵥ φ=(E : ℂ) • φ) (hE : E^2<1) :
    walk β P *ᵥ phi0 β φ = (E : ℂ) • phi0 β φ -
      (Real.sqrt (1-E^2) : ℂ) • phi1 β P φ E := by
  rw [walk,Matrix.neg_mulVec,← Matrix.mulVec_mulVec,select_phi0,Vphi0_decompose β P φ E hE,
    Matrix.mulVec_add,Matrix.mulVec_smul,Matrix.mulVec_smul,reflection_phi0 β φ hβ,
    reflection_phi1 β P φ E hβ heig]
  module

theorem walk_phi1 (β : J → ℝ) (P : J → Matrix I I ℂ) (φ : State I) (E : ℝ)
    (hβ : ∑ j, β j^2=1) (hP2 : ∀ j, P j*P j=1)
    (heig : ham β P *ᵥ φ=(E : ℂ) • φ) (hE : E^2<1) :
    walk β P *ᵥ phi1 β P φ E = (Real.sqrt (1-E^2) : ℂ) • phi0 β φ +
      (E : ℂ) • phi1 β P φ E := by
  rw [walk,Matrix.neg_mulVec,← Matrix.mulVec_mulVec,select_phi1 β P φ E hP2 hE,
    Matrix.mulVec_sub,Matrix.mulVec_smul,Matrix.mulVec_smul,reflection_phi0 β φ hβ,
    reflection_phi1 β P φ E hβ heig]
  module

end
end Qatlib.Foundations.MatrixGeometry.LcuFrame
