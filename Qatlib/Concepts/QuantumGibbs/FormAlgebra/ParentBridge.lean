/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuantumGibbs.FormAlgebra.ParentWeight
set_option warningAsError false

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QuantumGibbs.FormAlgebra

open Matrix
open scoped MatrixOrder ComplexOrder

variable {D : ℕ}

section DiagonalRoot

theorem sqrt_exp (t : ℝ) : Real.sqrt (Real.exp t) = Real.exp (t / 2) := by
  rw [show Real.exp t = Real.exp (t / 2) * Real.exp (t / 2) from by
      rw [← Real.exp_add]
      congr 1
      ring]
  exact Real.sqrt_mul_self (Real.exp_nonneg _)

theorem CFC_sqrt_diagonal (f : Fin D → ℝ) (hf : ∀ i, 0 ≤ f i) :
    CFC.sqrt (Matrix.diagonal fun i => ((f i : ℝ) : ℂ))
      = Matrix.diagonal fun i => ((Real.sqrt (f i) : ℝ) : ℂ) := by
  have ha : 0 ≤ (Matrix.diagonal fun i => ((f i : ℝ) : ℂ)) :=
    (Matrix.PosSemidef.diagonal (fun i => Complex.zero_le_real.mpr (hf i))).nonneg
  have hb : 0 ≤ (Matrix.diagonal fun i => ((Real.sqrt (f i) : ℝ) : ℂ)) :=
    (Matrix.PosSemidef.diagonal (fun i => Complex.zero_le_real.mpr (Real.sqrt_nonneg (f i)))).nonneg
  rw [CFC.sqrt_eq_iff (Matrix.diagonal fun i => ((f i : ℝ) : ℂ))
      (Matrix.diagonal fun i => ((Real.sqrt (f i) : ℝ) : ℂ)) ha hb,
    Matrix.diagonal_mul_diagonal]
  ext i j
  rw [Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, if_pos rfl, ← Complex.ofReal_mul, Real.mul_self_sqrt (hf i)]
  · rw [if_neg hij, if_neg hij]

theorem fourthRoot_diagonal (f : Fin D → ℝ) (hf : ∀ i, 0 ≤ f i) :
    fourthRoot (Matrix.diagonal fun i => ((f i : ℝ) : ℂ))
      = Matrix.diagonal fun i => ((Real.sqrt (Real.sqrt (f i)) : ℝ) : ℂ) := by
  unfold fourthRoot
  rw [show CFC.sqrt (Matrix.diagonal fun i => ((f i : ℝ) : ℂ))
        = Matrix.diagonal fun i => ((Real.sqrt (f i) : ℝ) : ℂ) from CFC_sqrt_diagonal f hf]
  exact CFC_sqrt_diagonal (fun i => Real.sqrt (f i)) (fun i => Real.sqrt_nonneg (f i))

end DiagonalRoot

section MatUnit

def matUnit (i j : Fin D) (c : ℂ) : Operator D :=
  Matrix.of fun k l => if k = i ∧ l = j then c else 0

theorem matUnit_apply (i j : Fin D) (c : ℂ) (k l : Fin D) :
    matUnit i j c k l = if k = i ∧ l = j then c else 0 := rfl

theorem diagonal_mul_matUnit (d : Fin D → ℂ) (i j : Fin D) (c : ℂ) :
    Matrix.diagonal d * matUnit i j c = (d i) • matUnit i j c := by
  ext k l
  rw [Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul, matUnit_apply]
  by_cases h : k = i
  · simp [h]
  · simp [h]

theorem matUnit_mul_diagonal (d : Fin D → ℂ) (i j : Fin D) (c : ℂ) :
    matUnit i j c * Matrix.diagonal d = (d j) • matUnit i j c := by
  ext k l
  rw [Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul, matUnit_apply]
  by_cases h : l = j
  · by_cases h2 : k = i
    · simp [h, h2, mul_comm]
    · simp [h, h2]
  · simp [h]

end MatUnit

theorem diagonal_inv_eq (d : Fin D → ℂ) (hd : ∀ k, d k ≠ 0) :
    (Matrix.diagonal d)⁻¹ = Matrix.diagonal fun k => (d k)⁻¹ := by
  have hdet : (Matrix.diagonal d).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => hd k
  have hunit : IsUnit (Matrix.diagonal d) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr hdet
  have hfun : (fun k => (d k)⁻¹ * d k) = fun _ => (1 : ℂ) := funext fun k => inv_mul_cancel₀ (hd k)
  have hSA : Matrix.diagonal (fun k => (d k)⁻¹) * Matrix.diagonal d = 1 := by
    rw [Matrix.diagonal_mul_diagonal, hfun, Matrix.diagonal_one]
  refine IsUnit.mul_right_cancel hunit ?_
  rw [hSA, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)]

section GibbsDiag

noncomputable def gibbsDiag (lam : Fin D → ℝ) (β : ℝ) : Operator D :=
  Matrix.diagonal fun k =>
    (((Real.exp (-(β * lam k))) / (∑ k' : Fin D, Real.exp (-(β * lam k'))) : ℝ) : ℂ)

theorem gibbsDiag_entry_nonneg (lam : Fin D → ℝ) (β : ℝ) (k : Fin D) :
    0 ≤ Real.exp (-(β * lam k)) / ∑ k' : Fin D, Real.exp (-(β * lam k')) := by
  positivity

theorem gibbsDiag_nonneg (lam : Fin D → ℝ) (β : ℝ) : 0 ≤ gibbsDiag lam β := by
  rw [gibbsDiag]
  exact (Matrix.PosSemidef.diagonal (fun k => Complex.zero_le_real.mpr
    (div_nonneg (Real.exp_nonneg _)
      (Finset.sum_nonneg fun k _ => Real.exp_nonneg _)))).nonneg

theorem sharp_matUnit (lam : Fin D → ℝ) (β : ℝ) (i j : Fin D) (c : ℂ) :
    sharp (gibbsDiag lam β) (matUnit i j c)
      = ((Real.exp (-(β * (lam i - lam j)) / 4) : ℝ) : ℂ) • matUnit i j c := by
  classical
  set Z := ∑ k' : Fin D, Real.exp (-(β * lam k')) with hZdef
  have hZ : 0 < Z := Finset.sum_pos (fun k _ => Real.exp_pos _) ⟨i, Finset.mem_univ i⟩
  set g : Fin D → ℝ := fun k => Real.exp (-(β * lam k)) / Z with hgdef
  have hgnn : ∀ k, 0 ≤ g k := fun k => div_nonneg (le_of_lt (Real.exp_pos _)) hZ.le
  have hgpos : ∀ k, 0 < g k := fun k => div_pos (Real.exp_pos _) hZ
  have hR : fourthRoot (gibbsDiag lam β)
      = Matrix.diagonal fun k => ((Real.sqrt (Real.sqrt (g k)) : ℝ) : ℂ) := by
    rw [gibbsDiag, hgdef]
    exact fourthRoot_diagonal g hgnn
  have hreal : Real.sqrt (Real.sqrt (g i)) * (Real.sqrt (Real.sqrt (g j)))⁻¹
      = Real.exp (-(β * (lam i - lam j)) / 4) := by
    have hgi : g i = Real.exp (-(β * lam i)) / Z := rfl
    have hgj : g j = Real.exp (-(β * lam j)) / Z := rfl
    have hdiv : g i / g j = Real.exp (-(β * (lam i - lam j))) := by
      rw [hgi, hgj,
        show (Real.exp (-(β * lam i)) / Z) / (Real.exp (-(β * lam j)) / Z)
            = Real.exp (-(β * lam i)) / Real.exp (-(β * lam j)) from by field_simp,
        ← Real.exp_sub]
      congr 1
      ring
    have key : Real.sqrt (Real.sqrt (g i)) / Real.sqrt (Real.sqrt (g j))
        = Real.sqrt (Real.sqrt (g i / g j)) := by
      rw [← Real.sqrt_div (Real.sqrt_nonneg (g i)) (Real.sqrt (g j)),
        ← Real.sqrt_div (hgpos i).le (g j)]
    rw [← div_eq_mul_inv, key, hdiv, sqrt_exp, sqrt_exp]
    congr 1
    field_simp
    ring
  have hgj4 : (((Real.sqrt (Real.sqrt (g j)) : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (ne_of_gt (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (hgpos j))))
  have hd0 : ∀ k, ((Real.sqrt (Real.sqrt (g k)) : ℝ) : ℂ) ≠ 0 :=
    fun k => Complex.ofReal_ne_zero.mpr
      (ne_of_gt (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (hgpos k))))
  have hRinv : (Matrix.diagonal fun k => ((Real.sqrt (Real.sqrt (g k)) : ℝ) : ℂ))⁻¹
      = Matrix.diagonal fun k => (((Real.sqrt (Real.sqrt (g k)) : ℝ) : ℂ))⁻¹ :=
    diagonal_inv_eq _ hd0
  rw [sharp, hR, hRinv, diagonal_mul_matUnit, Matrix.smul_mul, matUnit_mul_diagonal,
    smul_smul]
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, hreal]

end GibbsDiag

theorem CFC_sqrt_conj (U M : Operator D) (hU : Uᴴ * U = 1) (hM : 0 ≤ M) :
    CFC.sqrt (U * M * Uᴴ) = U * CFC.sqrt M * Uᴴ := by
  have hc1 : (0 : Operator D) ≤ U * M * Uᴴ := by
    have h := (Matrix.PosSemidef.conjTranspose_mul_mul_same hM.posSemidef Uᴴ).nonneg
    rwa [Matrix.conjTranspose_conjTranspose] at h
  have hc2 : (0 : Operator D) ≤ U * CFC.sqrt M * Uᴴ := by
    have h := (Matrix.PosSemidef.conjTranspose_mul_mul_same
      (CFC.sqrt_nonneg M).posSemidef Uᴴ).nonneg
    rwa [Matrix.conjTranspose_conjTranspose] at h
  refine (CFC.sqrt_eq_iff (U * M * Uᴴ) (U * CFC.sqrt M * Uᴴ) hc1 hc2).mpr ?_
  have e1 : U * CFC.sqrt M * Uᴴ * (U * CFC.sqrt M * Uᴴ)
      = U * (CFC.sqrt M * (Uᴴ * U) * CFC.sqrt M) * Uᴴ := by
    repeat' rw [← Matrix.mul_assoc]
  rw [e1, hU, Matrix.mul_one, CFC.sqrt_mul_sqrt_self M hM]

theorem fourthRoot_conj (U M : Operator D) (hU : Uᴴ * U = 1) (hM : 0 ≤ M) :
    fourthRoot (U * M * Uᴴ) = U * fourthRoot M * Uᴴ := by
  have hs : 0 ≤ CFC.sqrt M := CFC.sqrt_nonneg M
  unfold fourthRoot
  rw [CFC_sqrt_conj U M hU hM, CFC_sqrt_conj U (CFC.sqrt M) hU hs]

theorem conj_mul_conj (U M N : Operator D) :
    U * M * Uᴴ * (U * N * Uᴴ) = U * (M * (Uᴴ * U) * N) * Uᴴ := by
  repeat' rw [← Matrix.mul_assoc]

theorem fourthRoot_gibbsDiag_isUnit (lam : Fin D → ℝ) (β : ℝ) (i : Fin D) :
    IsUnit (fourthRoot (gibbsDiag lam β)) := by
  classical
  have hZpos : 0 < ∑ k : Fin D, Real.exp (-(β * lam k)) :=
    Finset.sum_pos (fun k _ => Real.exp_pos _) ⟨i, Finset.mem_univ i⟩
  have hgnn : ∀ k, 0 ≤ Real.exp (-(β * lam k))
      / ∑ k' : Fin D, Real.exp (-(β * lam k')) :=
    fun k => div_nonneg (Real.exp_nonneg _) hZpos.le
  have hgpos : ∀ k, 0 < Real.exp (-(β * lam k))
      / ∑ k' : Fin D, Real.exp (-(β * lam k')) :=
    fun k => div_pos (Real.exp_pos _) hZpos
  have hRdiag : fourthRoot (gibbsDiag lam β)
      = Matrix.diagonal fun k => ((Real.sqrt (Real.sqrt (Real.exp (-(β * lam k))
          / ∑ k' : Fin D, Real.exp (-(β * lam k')))) : ℝ) : ℂ) := by
    rw [gibbsDiag]
    exact fourthRoot_diagonal _ hgnn
  rw [Matrix.isUnit_iff_isUnit_det, hRdiag, Matrix.det_diagonal]
  refine isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun k _ => ?_)
  exact Complex.ofReal_ne_zero.mpr
    (ne_of_gt (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (hgpos k))))

theorem conj_inv (U M : Operator D) (hU : Uᴴ * U = 1) (hM : IsUnit M) :
    (U * M * Uᴴ)⁻¹ = U * M⁻¹ * Uᴴ := by
  have hUU : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  have hdetU : U.det ≠ 0 := by
    intro h0
    have h1 : (Uᴴ * U).det = (1 : Operator D).det := by rw [hU]
    rw [Matrix.det_mul, Matrix.det_one, Matrix.det_conjTranspose, h0] at h1
    simp at h1
  have hdetM : M.det ≠ 0 := by
    rw [Matrix.isUnit_iff_isUnit_det] at hM
    exact hM.ne_zero
  have hdetX : (U * M * Uᴴ).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
    simp [hdetU, hdetM]
  have hXunit : IsUnit (U * M * Uᴴ) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr hdetX
  have hMinv : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdetM)
  have hYX : U * M⁻¹ * Uᴴ * (U * M * Uᴴ) = 1 := by
    rw [conj_mul_conj, hU, Matrix.mul_one, hMinv, Matrix.mul_one, hUU]
  refine IsUnit.mul_right_cancel hXunit ?_
  rw [hYX, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdetX)]

theorem sharp_matUnit_conj (lam : Fin D → ℝ) (β : ℝ) (U : Operator D)
    (hU : Uᴴ * U = 1) (i j : Fin D) (c : ℂ) :
    sharp (U * gibbsDiag lam β * Uᴴ) (U * matUnit i j c * Uᴴ)
      = ((Real.exp (-(β * (lam i - lam j)) / 4) : ℝ) : ℂ) • (U * matUnit i j c * Uᴴ) := by
  classical
  have hUU : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  have hRunit := fourthRoot_gibbsDiag_isUnit lam β i
  have hkey : fourthRoot (gibbsDiag lam β) * matUnit i j c
        * (fourthRoot (gibbsDiag lam β))⁻¹
      = ((Real.exp (-(β * (lam i - lam j)) / 4) : ℝ) : ℂ) • matUnit i j c :=
    sharp_matUnit lam β i j c
  rw [sharp, fourthRoot_conj U _ hU (gibbsDiag_nonneg lam β), conj_inv U _ hU hRunit,
    conj_mul_conj, hU, Matrix.mul_one, conj_mul_conj, hU, Matrix.mul_one, hkey,
    Matrix.mul_smul, Matrix.smul_mul]

noncomputable def hermUnitary (A : Operator D) (hA : A.IsHermitian) : Operator D :=
  (hA.eigenvectorUnitary : Operator D)

theorem hermUnitary_star_mul (A : Operator D) (hA : A.IsHermitian) :
    (hermUnitary A hA)ᴴ * hermUnitary A hA = 1 :=
  Unitary.coe_star_mul_self hA.eigenvectorUnitary

noncomputable def hermSpectralBlock (A : Operator D) (hA : A.IsHermitian)
    (i j : Fin D) (c : ℂ) : Operator D :=
  hermUnitary A hA * matUnit i j c * (hermUnitary A hA)ᴴ

noncomputable def hermGibbs (A : Operator D) (hA : A.IsHermitian) (β : ℝ) : Operator D :=
  hermUnitary A hA * gibbsDiag (fun i => hA.eigenvalues i) β * (hermUnitary A hA)ᴴ

theorem sharp_hermSpectralBlock (A : Operator D) (hA : A.IsHermitian) (β : ℝ)
    (i j : Fin D) (c : ℂ) :
    sharp (hermGibbs A hA β) (hermSpectralBlock A hA i j c)
      = ((Real.exp (-(β * (hA.eigenvalues i - hA.eigenvalues j)) / 4) : ℝ) : ℂ)
        • hermSpectralBlock A hA i j c :=
  sharp_matUnit_conj _ β _ (hermUnitary_star_mul A hA) i j c

end Qatlib.Concepts.QuantumGibbs.FormAlgebra
