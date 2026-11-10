/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.SpectralCutoff.Evolution
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
open Matrix Unitary
open scoped Classical BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace Qatlib.Foundations.MatrixGeometry.SpectralCutoff
variable {I : Type*} [Fintype I] [DecidableEq I]
local instance : CStarAlgebra (Matrix I I ℂ) where
local instance : NormedAlgebra ℚ (Matrix I I ℂ) := NormedAlgebra.restrictScalars ℚ ℂ (Matrix I I ℂ)

theorem low_weight_norm (H : Matrix I I ℂ) (hH : H.IsHermitian) (Δ lam : ℝ) (hlam : 0 ≤ lam) :
    ‖NormedSpace.exp ((lam:ℂ) • H)*low H hH Δ‖ ≤ Real.exp (lam*Δ) := by
  let C : Matrix I I ℂ ≃⋆ₐ[ℂ] Matrix I I ℂ :=conjStarAlgAut ℂ (Matrix I I ℂ) hH.eigenvectorUnitary
  rw [exp_spectral H hH (lam:ℂ),low,← map_mul]
  change ‖C _‖ ≤ _
  rw [(StarAlgEquiv.isometry (A:=Matrix I I ℂ) (B:=Matrix I I ℂ) C).norm_map_of_map_zero (map_zero C),mask,
    Matrix.diagonal_mul_diagonal,Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (Real.exp_pos _).le).mpr
  intro i
  by_cases hi:hH.eigenvalues i ≤ Δ
  · simp only [if_pos hi,mul_one,Complex.norm_exp,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hi hlam)
  · simp only [if_neg hi,mul_zero,norm_zero]
    exact (Real.exp_pos _).le

theorem high_weight_norm (H : Matrix I I ℂ) (hH : H.IsHermitian) (Λ lam : ℝ) (hlam : 0 ≤ lam) :
    ‖high H hH Λ*NormedSpace.exp ((-lam:ℂ) • H)‖ ≤ Real.exp (-lam*Λ) := by
  let C : Matrix I I ℂ ≃⋆ₐ[ℂ] Matrix I I ℂ :=conjStarAlgAut ℂ (Matrix I I ℂ) hH.eigenvectorUnitary
  have he : high H hH Λ=C (diagonal (fun i=>if hH.eigenvalues i ≤ Λ then 0 else 1)) := by
    change 1-C (mask H hH Λ)=_
    rw [← map_one C,← map_sub]
    apply congrArg C
    ext i j
    by_cases hij:i=j
    · subst j; by_cases hi:hH.eigenvalues i ≤ Λ <;> simp [mask,hi]
    · simp [mask,hij]
  rw [he,exp_spectral H hH (-lam:ℂ),← map_mul]
  rw [(StarAlgEquiv.isometry (A:=Matrix I I ℂ) (B:=Matrix I I ℂ) C).norm_map_of_map_zero (map_zero C),
    Matrix.diagonal_mul_diagonal,Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (Real.exp_pos _).le).mpr
  intro i
  by_cases hi:hH.eigenvalues i ≤ Λ
  · simp only [if_pos hi,zero_mul,norm_zero]
    exact (Real.exp_pos _).le
  · simp only [if_neg hi,one_mul,Complex.norm_exp,Complex.mul_re,
      Complex.neg_re,Complex.ofReal_re,Complex.neg_im,Complex.ofReal_im,neg_zero,mul_zero,sub_zero]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (le_of_not_ge hi) (neg_nonpos.mpr hlam))

def weighted (H A : Matrix I I ℂ) (lam : ℝ) : Matrix I I ℂ :=
  NormedSpace.exp ((lam:ℂ) • H)*A*NormedSpace.exp ((-lam:ℂ) • H)

theorem weighted_sum {α : Type*} (H : Matrix I I ℂ) (lam : ℝ) (s : Finset α) (A : α→Matrix I I ℂ) :
    weighted H (∑i∈s,A i) lam=∑i∈s,weighted H (A i) lam := by
  simp only [weighted,Finset.mul_sum,Finset.sum_mul]

theorem weighted_smul (H A : Matrix I I ℂ) (lam t : ℝ) :
    weighted H (t • A) lam=t • weighted H A lam := by
  simp only [weighted,mul_smul_comm,smul_mul_assoc]

theorem weighted_mul (H A B : Matrix I I ℂ) (lam : ℝ) :
    weighted H (A*B) lam=weighted H A lam*weighted H B lam := by
  let E:=NormedSpace.exp ((lam:ℂ) • H)
  let F:=NormedSpace.exp ((-lam:ℂ) • H)
  have hFE : F*E=1 := by
    dsimp only [F,E]
    rw [neg_smul]
    calc
      _ = NormedSpace.exp (-((lam:ℂ) • H)+((lam:ℂ) • H)) :=
        (NormedSpace.exp_add_of_commute (𝔸:=Matrix I I ℂ) ((Commute.refl (((lam:ℂ) • H))).neg_left)).symm
      _ = 1 := by rw [neg_add_cancel,NormedSpace.exp_zero]
  change E*(A*B)*F=(E*A*F)*(E*B*F)
  calc
    _=E*A*(F*E)*B*F := by rw [hFE]; noncomm_ring
    _=_ := by noncomm_ring

theorem weighted_leakage (H A : Matrix I I ℂ) (hH : H.IsHermitian) (Δ Λ lam : ℝ) (hlam : 0 ≤ lam) :
    ‖high H hH Λ*A*low H hH Δ‖ ≤ Real.exp (-lam*(Λ-Δ))*‖weighted H A lam‖ := by
  let E:=NormedSpace.exp ((lam:ℂ) • H)
  let F:=NormedSpace.exp ((-lam:ℂ) • H)
  have hFE : F*E=1 := by
    dsimp only [F,E]
    rw [neg_smul]
    calc
      _ = NormedSpace.exp (-((lam:ℂ) • H)+((lam:ℂ) • H)) :=
        (NormedSpace.exp_add_of_commute (𝔸:=Matrix I I ℂ) ((Commute.refl (((lam:ℂ) • H))).neg_left)).symm
      _ = 1 := by rw [neg_add_cancel,NormedSpace.exp_zero]
  have he : high H hH Λ*A*low H hH Δ=(high H hH Λ*F)*weighted H A lam*(E*low H hH Δ) := by
    change _=(high H hH Λ*F)*(E*A*F)*(E*low H hH Δ)
    calc
      _=high H hH Λ*(F*E)*A*(F*E)*low H hH Δ := by rw [hFE]; noncomm_ring
      _=_ := by noncomm_ring
  rw [he]
  calc
    _ ≤ ‖high H hH Λ*F‖*‖weighted H A lam‖*‖E*low H hH Δ‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ Real.exp (-lam*Λ)*‖weighted H A lam‖*Real.exp (lam*Δ) := by
      gcongr
      · exact high_weight_norm H hH Λ lam hlam
      · exact low_weight_norm H hH Δ lam hlam
    _ = _ := by
      rw [mul_right_comm,← Real.exp_add,show -lam*Λ+lam*Δ = -lam*(Λ-Δ) by ring]

end Qatlib.Foundations.MatrixGeometry.SpectralCutoff
