/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

open Matrix
set_option autoImplicit false

namespace Qatlib.Papers.ArxivCs0506068.TraceSpectrum

noncomputable section

variable {D : ℕ}

theorem dotProduct_vecMulVec (a b x : Fin D → ℝ) :
    x ⬝ᵥ ((vecMulVec a b) *ᵥ x) = (x ⬝ᵥ a) * (b ⬝ᵥ x) := by
  simp only [dotProduct, mulVec, vecMulVec_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_comm, mul_left_comm]

theorem trace_vecMulVec (a b : Fin D → ℝ) :
    (vecMulVec a b).trace = a ⬝ᵥ b := by
  simp [Matrix.trace, vecMulVec_apply, dotProduct]

def sqNorm (x : Fin D → ℝ) : ℝ := ∑ i, x i * x i

theorem sqNorm_nonneg (x : Fin D → ℝ) : 0 ≤ sqNorm x :=
  Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))

theorem trace_eq_sum_diag (A : Matrix (Fin D) (Fin D) ℝ) :
    A.trace = ∑ i, A i i := by
  simp [Matrix.trace]

theorem diag_nonneg_of_posSemidef {A : Matrix (Fin D) (Fin D) ℝ} (hA : A.PosSemidef)
    (i : Fin D) : 0 ≤ A i i :=
  hA.diag_nonneg (i := i)

theorem diag_le_trace {A : Matrix (Fin D) (Fin D) ℝ} (hA : A.PosSemidef)
    (i : Fin D) : A i i ≤ A.trace := by
  rw [trace_eq_sum_diag]
  exact Finset.single_le_sum (fun j _ => diag_nonneg_of_posSemidef hA j) (Finset.mem_univ i)

theorem inner_le_trace {A : Matrix (Fin D) (Fin D) ℝ} (hA : A.PosSemidef)
    (x : Fin D → ℝ) :
    x ⬝ᵥ (A *ᵥ x) ≤ sqNorm x * A.trace := by
  obtain ⟨m, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hA
  rw [hv, Matrix.sum_mulVec, dotProduct_sum, Matrix.trace_sum]
  have hterm : ∀ i : Fin m,
      x ⬝ᵥ (vecMulVec (v i) (star (v i)) *ᵥ x) ≤
        sqNorm x * (vecMulVec (v i) (star (v i))).trace := by
    intro i
    have hs : star (v i) = v i := by funext j; simp
    rw [hs, dotProduct_vecMulVec, trace_vecMulVec]
    rw [show (v i ⬝ᵥ v i) = ∑ j, (v i j) ^ 2 from by
      simp only [dotProduct]; exact Finset.sum_congr rfl (fun j _ => by ring)]
    rw [show sqNorm x = ∑ j, (x j) ^ 2 from by
      simp only [sqNorm]; exact Finset.sum_congr rfl (fun j _ => by ring)]
    rw [show (x ⬝ᵥ v i) * (v i ⬝ᵥ x) = (x ⬝ᵥ v i) ^ 2 from by
      rw [dotProduct_comm]; ring]
    rw [show x ⬝ᵥ v i = ∑ j, x j * v i j from rfl]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  calc ∑ i, x ⬝ᵥ (vecMulVec (v i) (star (v i)) *ᵥ x)
      ≤ ∑ i, sqNorm x * (vecMulVec (v i) (star (v i))).trace :=
        Finset.sum_le_sum (fun i _ => hterm i)
    _ = sqNorm x * ∑ i, (vecMulVec (v i) (star (v i))).trace := by
        rw [Finset.mul_sum]

theorem trace_le_card_mul_of_unit_le {A : Matrix (Fin D) (Fin D) ℝ}
    (_hA : A.PosSemidef) (b : ℝ)
    (h : ∀ x : Fin D → ℝ, sqNorm x = 1 → x ⬝ᵥ (A *ᵥ x) ≤ b) :
    A.trace ≤ D * b := by
  have hdiag : ∀ i : Fin D, A i i ≤ b := by
    intro i
    have hx : sqNorm (fun j => if j = i then (1 : ℝ) else 0) = 1 := by
      simp [sqNorm]
    have hb := h (fun j => if j = i then (1 : ℝ) else 0) hx
    have hq : (fun j => if j = i then (1 : ℝ) else 0) ⬝ᵥ
        (A *ᵥ (fun j => if j = i then (1 : ℝ) else 0)) = A i i := by
      simp [dotProduct, mulVec]
    simpa [hq] using hb
  rw [trace_eq_sum_diag]
  calc ∑ i, A i i ≤ ∑ _i : Fin D, b := Finset.sum_le_sum (fun i _ => hdiag i)
    _ = D * b := by simp [Finset.sum_const, mul_comm]

theorem trace_ge_of_witness {A : Matrix (Fin D) (Fin D) ℝ} (hA : A.PosSemidef)
    (x : Fin D → ℝ) (a : ℝ) (hx : sqNorm x = 1) (h : a ≤ x ⬝ᵥ (A *ᵥ x)) :
    a ≤ A.trace := by
  have hle := inner_le_trace hA x
  rw [hx, one_mul] at hle
  exact h.trans hle

theorem trace_sandwich {A : Matrix (Fin D) (Fin D) ℝ} (hA : A.PosSemidef)
    (a b : ℝ) (hcomplete : ∃ x, sqNorm x = 1 ∧ a ≤ x ⬝ᵥ (A *ᵥ x))
    (hsound : ∀ x, sqNorm x = 1 → x ⬝ᵥ (A *ᵥ x) ≤ b) :
    a ≤ A.trace ∧ A.trace ≤ D * b := by
  obtain ⟨x, hx, hax⟩ := hcomplete
  exact ⟨trace_ge_of_witness hA x a hx hax, trace_le_card_mul_of_unit_le hA b hsound⟩

theorem totallyMixed_eq_trace_div (A : Matrix (Fin D) (Fin D) ℝ) :
    (∑ i, (fun j => if j = i then (1 : ℝ) else 0) ⬝ᵥ
      (A *ᵥ (fun j => if j = i then (1 : ℝ) else 0))) / D = A.trace / D := by
  have h : ∀ i : Fin D, (fun j => if j = i then (1 : ℝ) else 0) ⬝ᵥ
      (A *ᵥ (fun j => if j = i then (1 : ℝ) else 0)) = A i i := by
    intro i; simp [dotProduct, mulVec]
  simp only [h, trace_eq_sum_diag]

theorem qma_pp_yes (m : ℕ) {A : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℝ}
    (hA : A.PosSemidef)
    (hcomplete : ∃ x, sqNorm x = 1 ∧
      1 - 1 / (2 : ℝ) ^ (m + 2) ≤ x ⬝ᵥ (A *ᵥ x)) :
    (3 : ℝ) / 4 ≤ A.trace := by
  obtain ⟨x, hx, hqx⟩ := hcomplete
  have hge : 1 - 1 / (2 : ℝ) ^ (m + 2) ≤ A.trace :=
    trace_ge_of_witness hA x _ hx hqx
  have hle : (3 : ℝ) / 4 ≤ 1 - 1 / (2 : ℝ) ^ (m + 2) := by
    have hpow : (4 : ℝ) ≤ (2 : ℝ) ^ (m + 2) := by
      calc (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
        _ ≤ (2 : ℝ) ^ (m + 2) := by
            apply pow_le_pow_right₀ (by norm_num)
            omega
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (m + 2) := by positivity
    have : 1 / (2 : ℝ) ^ (m + 2) ≤ 1 / 4 :=
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hpow
    linarith
  exact hle.trans hge

theorem qma_pp_no (m : ℕ) {A : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℝ}
    (hA : A.PosSemidef)
    (hsound : ∀ x, sqNorm x = 1 →
      x ⬝ᵥ (A *ᵥ x) ≤ 1 / (2 : ℝ) ^ (m + 2)) :
    A.trace ≤ 1 / 4 := by
  have h := trace_le_card_mul_of_unit_le hA (1 / (2 : ℝ) ^ (m + 2)) hsound
  have hcard : ((2 ^ m : ℕ) : ℝ) = (2 : ℝ) ^ m := by push_cast; ring
  rw [hcard] at h
  have hpow : (2 : ℝ) ^ m * (1 / (2 : ℝ) ^ (m + 2)) = 1 / 4 := by
    rw [pow_add]
    have hpos : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
    norm_num
    field_simp
  linarith [h, hpow]

end

end Qatlib.Papers.ArxivCs0506068.TraceSpectrum
