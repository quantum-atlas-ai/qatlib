/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Tactic
set_option warningAsError false

set_option autoImplicit false

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Qatlib.Concepts.KrausCompile.Normalize

noncomputable local instance matrixCStar {d : ℕ} :
    CStarAlgebra (Matrix (Fin d) (Fin d) ℂ) where

noncomputable def unsignedSum {d r : ℕ} (K : Fin r → Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ := ∑ i, (K i).conjTranspose * K i

noncomputable def gamma {d r : ℕ} (K : Fin r → Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  ‖(Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)) (unsignedSum K)‖

noncomputable def normalizedKraus {d r : ℕ} (K : Fin r → Matrix (Fin d) (Fin d) ℂ)
    (i : Fin r) : Matrix (Fin d) (Fin d) ℂ := (Real.sqrt (gamma K))⁻¹ • K i

theorem normalizedKraus_eq_complex {d r : ℕ}
    (K : Fin r → Matrix (Fin d) (Fin d) ℂ) (i : Fin r) :
    normalizedKraus K i = ((Real.sqrt (gamma K) : ℂ)⁻¹) • K i := by
  unfold normalizedKraus
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  congr 1
  exact map_inv₀ (algebraMap ℝ ℂ) (Real.sqrt (gamma K))

theorem unsignedSum_psd {d r : ℕ} (K : Fin r → Matrix (Fin d) (Fin d) ℂ) :
    (unsignedSum K).PosSemidef :=
  Matrix.posSemidef_sum _ (fun i _ => Matrix.posSemidef_conjTranspose_mul_self (K i))

theorem identity_le_unsignedSum {d r : ℕ} (K : Fin r → Matrix (Fin d) (Fin d) ℂ)
    (α : Fin r → ℂ) (hα : ∀ i, α i = 1 ∨ α i = -1)
    (hTP : ∑ i, α i • ((K i).conjTranspose * K i) = 1) :
    (1 : Matrix (Fin d) (Fin d) ℂ) ≤ unsignedSum K := by
  have heach (i : Fin r) : α i • ((K i).conjTranspose * K i) ≤
      (K i).conjTranspose * K i := by
    rcases hα i with hi | hi
    · simp [hi]
    · rw [hi, neg_one_smul]
      exact neg_le_self (Matrix.posSemidef_conjTranspose_mul_self (K i)).nonneg
  simpa only [hTP, unsignedSum] using
    (Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i))

theorem gamma_ge_one {d r : ℕ} (hd : 0 < d) (K : Fin r → Matrix (Fin d) (Fin d) ℂ)
    (α : Fin r → ℂ) (hα : ∀ i, α i = 1 ∨ α i = -1)
    (hTP : ∑ i, α i • ((K i).conjTranspose * K i) = 1) : 1 ≤ gamma K := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have h := CStarAlgebra.norm_le_norm_of_le_of_nonneg
    (identity_le_unsignedSum K α hα hTP)
    zero_le_one
  simpa only [norm_one, Matrix.cstar_norm_def, gamma] using h

theorem unsignedSum_le_gamma_one {d r : ℕ} (K : Fin r → Matrix (Fin d) (Fin d) ℂ) :
    unsignedSum K ≤ gamma K • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  have hsa : IsSelfAdjoint (unsignedSum K) := by
    simpa only [IsSelfAdjoint, Matrix.star_eq_conjTranspose] using!
      (unsignedSum_psd K).isHermitian
  have h := hsa.le_algebraMap_norm_self
  simpa only [Algebra.algebraMap_eq_smul_one, Matrix.cstar_norm_def, gamma] using h

theorem normalizedSum_eq {d r : ℕ} (K : Fin r → Matrix (Fin d) (Fin d) ℂ) :
    unsignedSum (normalizedKraus K) = (gamma K)⁻¹ • unsignedSum K := by
  have hγ : 0 ≤ gamma K := norm_nonneg _
  have hcoeff : (Real.sqrt (gamma K))⁻¹ * (Real.sqrt (gamma K))⁻¹ = (gamma K)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hγ]
  unfold unsignedSum normalizedKraus
  simp only [Matrix.conjTranspose_smul, star_trivial, smul_mul_assoc,
    mul_smul_comm, smul_smul, hcoeff, Finset.smul_sum]

theorem normalizedSum_le_one {d r : ℕ} (hd : 0 < d)
    (K : Fin r → Matrix (Fin d) (Fin d) ℂ)
    (α : Fin r → ℂ) (hα : ∀ i, α i = 1 ∨ α i = -1)
    (hTP : ∑ i, α i • ((K i).conjTranspose * K i) = 1) :
    unsignedSum (normalizedKraus K) ≤ (1 : Matrix (Fin d) (Fin d) ℂ) := by
  have hγpos : 0 < gamma K := lt_of_lt_of_le zero_lt_one (gamma_ge_one hd K α hα hTP)
  have h := smul_le_smul_of_nonneg_left (unsignedSum_le_gamma_one K)
    (inv_nonneg.mpr hγpos.le)
  rw [smul_smul, inv_mul_cancel₀ hγpos.ne', one_smul] at h
  simpa only [normalizedSum_eq] using h

theorem complex_normalizedSum_le_one {d r : ℕ} (hd : 0 < d)
    (K : Fin r → Matrix (Fin d) (Fin d) ℂ)
    (α : Fin r → ℂ) (hα : ∀ i, α i = 1 ∨ α i = -1)
    (hTP : ∑ i, α i • ((K i).conjTranspose * K i) = 1) :
    (∑ i, (((Real.sqrt (gamma K) : ℂ)⁻¹) • K i).conjTranspose *
      (((Real.sqrt (gamma K) : ℂ)⁻¹) • K i)) ≤ (1 : Matrix (Fin d) (Fin d) ℂ) := by
  simpa only [unsignedSum, normalizedKraus_eq_complex] using normalizedSum_le_one hd K α hα hTP

noncomputable def completion {d r : ℕ} (K : Fin r → Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ := CFC.sqrt (1 - unsignedSum (normalizedKraus K))

theorem completion_gram {d r : ℕ} (hd : 0 < d)
    (K : Fin r → Matrix (Fin d) (Fin d) ℂ)
    (α : Fin r → ℂ) (hα : ∀ i, α i = 1 ∨ α i = -1)
    (hTP : ∑ i, α i • ((K i).conjTranspose * K i) = 1) :
    (completion K).conjTranspose * completion K = 1 - unsignedSum (normalizedKraus K) := by
  have hR : 0 ≤ 1 - unsignedSum (normalizedKraus K) :=
    sub_nonneg.mpr (normalizedSum_le_one hd K α hα hTP)
  have hroot : IsSelfAdjoint (completion K) := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)
  change star (completion K) * completion K = _
  rw [hroot.star_eq]
  exact CFC.sqrt_mul_sqrt_self _ hR

theorem automatic_normalization_completion {d r : ℕ} (hd : 0 < d)
    (K : Fin r → Matrix (Fin d) (Fin d) ℂ)
    (α : Fin r → ℂ) (hα : ∀ i, α i = 1 ∨ α i = -1)
    (hTP : ∑ i, α i • ((K i).conjTranspose * K i) = 1) :
    1 ≤ gamma K ∧
    (∑ i : Fin (r+1),
      (Fin.snoc (α := fun _ => Matrix (Fin d) (Fin d) ℂ) (normalizedKraus K) (completion K) i).conjTranspose *
      Fin.snoc (α := fun _ => Matrix (Fin d) (Fin d) ℂ) (normalizedKraus K) (completion K) i) = 1 := by
  refine ⟨gamma_ge_one hd K α hα hTP, ?_⟩
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rw [completion_gram hd K α hα hTP]
  change unsignedSum (normalizedKraus K) + (1 - unsignedSum (normalizedKraus K)) = 1
  abel

end Qatlib.Concepts.KrausCompile.Normalize
