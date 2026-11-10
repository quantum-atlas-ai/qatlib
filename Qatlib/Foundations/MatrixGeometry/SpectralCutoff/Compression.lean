/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.SpectralCutoff.Projectors

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
open Matrix Unitary
open scoped Classical BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace Qatlib.Foundations.MatrixGeometry.SpectralCutoff
variable {I : Type*} [Fintype I] [DecidableEq I]

local instance : CStarAlgebra (Matrix I I ℂ) where

theorem compressed_energy (H : Matrix I I ℂ) (hH : H.IsHermitian) (Λ : ℝ) :
    low H hH Λ*H*low H hH Λ=
      conjStarAlgAut ℂ (Matrix I I ℂ) hH.eigenvectorUnitary
        (diagonal (fun i=>if hH.eigenvalues i ≤ Λ then (hH.eigenvalues i:ℂ) else 0)) := by
  let C : Matrix I I ℂ ≃⋆ₐ[ℂ] Matrix I I ℂ :=conjStarAlgAut ℂ (Matrix I I ℂ) hH.eigenvectorUnitary
  have hh : H=C (diagonal (fun i=>(hH.eigenvalues i:ℂ))) := hH.spectral_theorem
  calc
    _=C (mask H hH Λ)*C (diagonal (fun i=>(hH.eigenvalues i:ℂ)))*C (mask H hH Λ) :=
      congrArg (fun B=>low H hH Λ*B*low H hH Λ) hh
    _=C (mask H hH Λ*diagonal (fun i=>(hH.eigenvalues i:ℂ))*mask H hH Λ) := by rw [map_mul,map_mul]
    _=_ := by
      apply congrArg C
      simp only [mask,Matrix.diagonal_mul_diagonal]
      apply congrArg Matrix.diagonal
      funext i
      split_ifs <;> simp

theorem compressed_energy_ceiling (H : Matrix I I ℂ) (hH : H.IsHermitian) (Λ : ℝ) :
    (((Λ:ℂ)•low H hH Λ)-low H hH Λ*H*low H hH Λ).PosSemidef := by
  let C : Matrix I I ℂ ≃⋆ₐ[ℂ] Matrix I I ℂ :=conjStarAlgAut ℂ (Matrix I I ℂ) hH.eigenvectorUnitary
  let D:=diagonal (fun i=>if hH.eigenvalues i ≤ Λ then (Λ-hH.eigenvalues i:ℂ) else 0)
  have hD : D.PosSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]
    intro i
    split_ifs with hi
    · exact_mod_cast sub_nonneg.mpr hi
    · exact le_rfl
  have he : (((Λ:ℂ)•low H hH Λ)-low H hH Λ*H*low H hH Λ)=C D := by
    rw [compressed_energy]
    change (Λ:ℂ)•C (mask H hH Λ)-C _=C D
    rw [← map_smul,← map_sub]
    apply congrArg C
    ext i j
    by_cases hij:i=j
    · subst j
      by_cases hi:hH.eigenvalues i ≤ Λ <;> simp [D,mask,hi]
    · simp [D,mask,hij]
  rw [he]
  simpa only [C,conjStarAlgAut_apply,Matrix.star_eq_conjTranspose] using
    hD.mul_mul_conjTranspose_same (hH.eigenvectorUnitary:Matrix I I ℂ)

theorem compressed_energy_norm (H : Matrix I I ℂ) (hH : H.PosSemidef) (Λ : ℝ) (hΛ : 0 ≤ Λ) :
    ‖low H hH.isHermitian Λ*H*low H hH.isHermitian Λ‖ ≤ Λ := by
  let C :
      Matrix I I ℂ ≃⋆ₐ[ℂ] Matrix I I ℂ :=conjStarAlgAut ℂ
      (Matrix I I ℂ) hH.isHermitian.eigenvectorUnitary
  let D : Matrix I I ℂ :=
      diagonal (fun i=>if hH.isHermitian.eigenvalues i ≤ Λ then (hH.isHermitian.eigenvalues i:ℂ) else 0)
  have hc : ‖C D‖=‖D‖ :=
    (StarAlgEquiv.isometry (A:=Matrix I I ℂ) (B:=Matrix I I ℂ) C).norm_map_of_map_zero (map_zero C) D
  have hd : ‖D‖ ≤ Λ := by
    rw [Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg hΛ).mpr
    intro i
    by_cases hi:hH.isHermitian.eigenvalues i ≤ Λ
    · simpa only
        [if_pos hi,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hH.eigenvalues_nonneg i)] using hi
    · simp [hi,hΛ]
  rw [compressed_energy H hH.isHermitian Λ]
  exact hc.trans_le hd

theorem compression_psd_domination (H A : Matrix I I ℂ) (hH : H.PosSemidef)
    (hA : A.PosSemidef) (hHA : (H-A).PosSemidef) (Λ : ℝ) :
    0 ≤ low H hH.isHermitian Λ*A*low H hH.isHermitian Λ ∧
      low H hH.isHermitian Λ*A*low H hH.isHermitian Λ ≤
      low H hH.isHermitian Λ*H*low H hH.isHermitian Λ := by
  have hp : (low H hH.isHermitian Λ*A*low H hH.isHermitian Λ).PosSemidef := by
    simpa only [low_hermitian] using hA.conjTranspose_mul_mul_same (low H hH.isHermitian Λ)
  refine ⟨hp.nonneg,?_⟩
  change (low H hH.isHermitian Λ*H*low H hH.isHermitian Λ-
    low H hH.isHermitian Λ*A*low H hH.isHermitian Λ).PosSemidef
  convert hHA.conjTranspose_mul_mul_same (low H hH.isHermitian Λ) using 1
  rw [low_hermitian]
  noncomm_ring

theorem compression_norm (H A : Matrix I I ℂ) (hH : H.PosSemidef)
    (hA : A.PosSemidef) (hHA : (H-A).PosSemidef) (Λ : ℝ) (hΛ : 0 ≤ Λ) :
    ‖low H hH.isHermitian Λ*A*low H hH.isHermitian Λ‖ ≤ Λ := by
  obtain ⟨hp,hle⟩:=compression_psd_domination H A hH hA hHA Λ
  exact (CStarAlgebra.norm_le_norm_of_le_of_nonneg (A:=Matrix I I ℂ) hle hp).trans
      (compressed_energy_norm H hH Λ hΛ)

omit [Fintype I] [DecidableEq I] in

theorem psd_group_domination {M : ℕ} (A : Fin M→Matrix I I ℂ) (hA : ∀m,(A m).PosSemidef) (m : Fin M) :
    ((∑j,A j)-A m).PosSemidef := by
  have he : ((∑j,A j)-A m)=∑j∈Finset.univ.erase m,A j := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ m)]
    abel
  rw [he]
  exact Matrix.posSemidef_sum _ (fun j _=>hA j)

theorem psd_group_compression {M : ℕ} (A : Fin M→Matrix I I ℂ) (hA : ∀m,(A m).PosSemidef)
    (m : Fin M) (Λ : ℝ) (hΛ : 0 ≤ Λ) :
    let hH:=(Matrix.posSemidef_sum Finset.univ (fun j _=>hA j))
    ‖low (∑j,A j) hH.isHermitian Λ*A m*low (∑j,A j) hH.isHermitian Λ‖ ≤ Λ :=
  compression_norm _ _ (Matrix.posSemidef_sum _ (fun j _=>hA j)) (hA m) (psd_group_domination A hA m) Λ hΛ

end Qatlib.Foundations.MatrixGeometry.SpectralCutoff
