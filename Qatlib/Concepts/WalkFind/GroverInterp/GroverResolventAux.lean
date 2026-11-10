/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Module
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Matrix
namespace Qatlib.Concepts.WalkFind.GroverInterp

theorem grover_symmetric_factor (m : ℕ)
    (U : Matrix (Fin m) (Fin m) ℂ) (z w : ℂ)
    (hu : star U * U = 1) (hzw : w * z = 1) :
    (U - w • 1) * star U * (U - z • 1) =
      U + star U - (z + w) • 1 := by
  have hu' : U * star U = 1 := mul_eq_one_comm.mp hu
  have hzw' : z * w = 1 := by simpa [mul_comm] using hzw
  simp only [Matrix.sub_mul, Matrix.mul_sub,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hu, hu',
    smul_sub, smul_smul, hzw', one_smul, add_smul]
  module

theorem grover_paired_resolvent (m : ℕ)
    (U : Matrix (Fin m) (Fin m) ℂ) (z w : ℂ)
    (hu : star U * U = 1) (hzw : w * z = 1)
    (hz : IsUnit (U - z • 1)) (hw : IsUnit (U - w • 1)) :
    let K := U + star U - (z + w) • 1
    IsUnit K ∧
      (U - z • 1)⁻¹ * U - (U - w • 1)⁻¹ * U = (z - w) • K⁻¹ := by
  classical
  let Az := U - z • (1 : Matrix (Fin m) (Fin m) ℂ)
  let Aw := U - w • (1 : Matrix (Fin m) (Fin m) ℂ)
  let K := U + star U - (z + w) • (1 : Matrix (Fin m) (Fin m) ℂ)
  have hzdet := (Matrix.isUnit_iff_isUnit_det _).mp hz
  have hwdet := (Matrix.isUnit_iff_isUnit_det _).mp hw
  have hstar : IsUnit (star U) := isUnit_iff_exists_inv.mpr ⟨U, hu⟩
  have hfacz : Aw * star U * Az = K := grover_symmetric_factor m U z w hu hzw
  have hfacw : Az * star U * Aw = K := by
    simpa [add_comm] using grover_symmetric_factor m U w z hu (by simpa [mul_comm] using hzw)
  have hK : IsUnit K := hfacz ▸ (hw.mul hstar).mul hz
  have hKdet := (Matrix.isUnit_iff_isUnit_det _).mp hK
  have hez : K * (Az⁻¹ * U) = Aw := by
    rw [← hfacz]
    calc
      _ = Aw * star U * (Az * Az⁻¹) * U := by simp only [Matrix.mul_assoc]
      _ = Aw := by rw [Matrix.mul_nonsing_inv _ hzdet, Matrix.mul_one,
        Matrix.mul_assoc, hu, Matrix.mul_one]
  have hew : K * (Aw⁻¹ * U) = Az := by
    rw [← hfacw]
    calc
      _ = Az * star U * (Aw * Aw⁻¹) * U := by simp only [Matrix.mul_assoc]
      _ = Az := by rw [Matrix.mul_nonsing_inv _ hwdet, Matrix.mul_one,
        Matrix.mul_assoc, hu, Matrix.mul_one]
  refine ⟨hK, ?_⟩
  change Az⁻¹ * U - Aw⁻¹ * U = (z - w) • K⁻¹
  have he : K * (Az⁻¹ * U - Aw⁻¹ * U) = (z - w) • 1 := by
    rw [Matrix.mul_sub, hez, hew]
    dsimp only [Az, Aw]
    module
  have hi := congrArg (fun B => K⁻¹ * B) he
  try dsimp only at hi
  rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hKdet, Matrix.one_mul,
    Matrix.mul_smul, Matrix.mul_one] at hi
  exact hi

theorem grover_inverse_overlap_eigenbasis (m : ℕ)
    (K B : Matrix (Fin m) (Fin m) ℂ) (eig : Fin m → ℂ)
    (hB : B * star B = 1) (hK : IsUnit K)
    (he : ∀ j, K *ᵥ (fun i => B i j) = eig j • (fun i => B i j))
    (good : Fin m → ℂ) :
    star good ⬝ᵥ (K⁻¹ *ᵥ good) =
      ∑ j, star ((star B *ᵥ good) j) * ((star B *ᵥ good) j) / eig j := by
  classical
  have heig (j : Fin m) : eig j ≠ 0 := by
    intro hzero
    have hcol : (fun i => B i j) = 0 := by
      apply Matrix.mulVec_injective_iff_isUnit.mpr hK
      simpa only [hzero, zero_smul, Matrix.mulVec_zero] using he j
    have hc (i : Fin m) : B i j = 0 := congrFun hcol i
    have ho := congrArg (fun A : Matrix (Fin m) (Fin m) ℂ => A j j)
      (mul_eq_one_comm.mp hB)
    simp [Matrix.mul_apply, Matrix.star_eq_conjTranspose, hc] at ho
  let c := star B *ᵥ good
  let D := Matrix.diagonal (fun j => (eig j)⁻¹)
  have hKB : K * B = B * Matrix.diagonal eig := by
    ext i j
    rw [Matrix.mul_diagonal]
    have h := congrFun (he j) i
    simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Pi.smul_apply, smul_eq_mul, mul_comm] using h
  have hD : Matrix.diagonal eig * D = 1 := by
    simp only [D, Matrix.diagonal_mul_diagonal, mul_inv_cancel₀ (heig _)]
    exact Matrix.diagonal_one
  have hKD : K * (B * D) = B := by
    rw [← Matrix.mul_assoc, hKB, Matrix.mul_assoc, hD, Matrix.mul_one]
  have hinv : K⁻¹ * B = B * D := by
    have h := congrArg (fun A => K⁻¹ * A) hKD
    try dsimp only at h
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _
      ((Matrix.isUnit_iff_isUnit_det _).mp hK), Matrix.one_mul] at h
    exact h.symm
  have hgc : good = B *ᵥ c := by
    dsimp only [c]
    rw [Matrix.mulVec_mulVec, hB, Matrix.one_mulVec]
  have hrow : star good ᵥ* B = star c := by
    dsimp only [c]
    rw [Matrix.star_mulVec]
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  calc
    _ = star good ⬝ᵥ ((K⁻¹ * B) *ᵥ c) := by rw [← Matrix.mulVec_mulVec, ← hgc]
    _ = star c ⬝ᵥ (D *ᵥ c) := by
      rw [hinv, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hrow]
    _ = _ := by
      simp only [dotProduct, Pi.star_apply, D, Matrix.mulVec_diagonal,
        div_eq_mul_inv]
      congr 1
      ext j
      dsimp only [c]
      ring

theorem grover_symmetric_eigenvector (m : ℕ)
    (U : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ) (μ : ℂ) (c : ℝ)
    (hu : star U * U = 1) (hμ : star μ * μ = 1)
    (he : U *ᵥ v = μ • v) :
    (U + star U - ((2 * c : ℝ) : ℂ) • 1) *ᵥ v =
      ((2 * (μ.re - c) : ℝ) : ℂ) • v := by
  have hadj : star U *ᵥ v = star μ • v := by
    have h := congrArg (fun w => star U *ᵥ w) he
    try dsimp only at h
    rw [Matrix.mulVec_mulVec, hu, Matrix.one_mulVec, Matrix.mulVec_smul] at h
    have hs := congrArg (fun w => star μ • w) h
    (try dsimp only at hs)
    rw [smul_smul, hμ, one_smul] at hs
    exact hs.symm
  have hc : μ + star μ - ((2*c : ℝ) : ℂ) = ((2*(μ.re-c) : ℝ) : ℂ) := by
    apply Complex.ext <;> simp only [Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.star_def, Complex.conj_re,
      Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im] <;> ring
  rw [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, he, hadj, ← add_smul, ← sub_smul, hc]

theorem grover_weighted_pole_split (m : ℕ) (μ : Fin m → ℂ)
    (w s : Fin m → ℝ) (α c : ℝ)
    (hw : ∀ j, μ j = 1 → w j = 0) (hs : ∀ j, μ j ≠ 1 → s j = 0)
    (hsum : (∑ j, s j) = 1) :
    (∑ j, (w j + α^2 * s j) / ((μ j).re - c)) =
      α^2 / (1-c) - ∑ j, w j / (c - if μ j = 1 then -1 else (μ j).re) := by
  classical
  have ht (j : Fin m) : (w j + α^2*s j) / ((μ j).re - c) =
      -(w j / (c - if μ j = 1 then -1 else (μ j).re)) + α^2*(s j/(1-c)) := by
    by_cases hj : μ j = 1
    · simp only [hj, Complex.one_re, if_pos, hw j hj, zero_add, zero_div, neg_zero]
      ring
    · simp only [hj, if_false, hs j hj, mul_zero, add_zero, zero_div, add_zero]
      rw [← neg_sub c (μ j).re, div_neg]
  simp_rw [ht]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum,
    ← Finset.sum_div, hsum]
  ring

theorem grover_weighted_pole_split_sq (m : ℕ) (μ : Fin m → ℂ)
    (w s : Fin m → ℝ) (α c : ℝ)
    (hw : ∀ j, μ j = 1 → w j = 0) (hs : ∀ j, μ j ≠ 1 → s j = 0)
    (hsum : (∑ j, s j) = 1) :
    (∑ j, (w j + α^2 * s j) / ((μ j).re - c)^2) =
      α^2 / (1-c)^2 + ∑ j, w j / (c - if μ j = 1 then -1 else (μ j).re)^2 := by
  classical
  have ht (j : Fin m) : (w j + α^2*s j) / ((μ j).re - c)^2 =
      w j / (c - if μ j = 1 then -1 else (μ j).re)^2 + α^2*(s j/(1-c)^2) := by
    by_cases hj : μ j = 1
    · simp only [hj, Complex.one_re, if_pos, hw j hj, zero_add, zero_div]
      ring
    · simp only [hj, if_false, hs j hj, mul_zero, add_zero, zero_div, add_zero]
      rw [show ((μ j).re-c)^2=(c-(μ j).re)^2 by ring]
  simp_rw [ht]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div, hsum]
  ring

end Qatlib.Concepts.WalkFind.GroverInterp
