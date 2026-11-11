/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Trace bounds from quadratic forms

This module bounds traces of real positive semidefinite matrices using their quadratic forms on
unit vectors. It identifies the average over the standard basis with trace divided by dimension
and derives the trace separation used in the QMA-to-PP argument. See [MarriottWatrous2005].

## Main statements

* `inner_le_trace`: bounds a quadratic form by squared norm times trace.
* `trace_sandwich`: combines witness and uniform upper bounds.
* `qma_pp_yes`: gives the completeness-side trace bound.
* `qma_pp_no`: gives the soundness-side trace bound.

## References

* [Marriott and Watrous, 2005][MarriottWatrous2005]
-/

open Matrix
set_option autoImplicit false

namespace Qatlib.Papers.ArxivCs0506068.TraceSpectrum

noncomputable section

variable {D : ℕ}

/-- The quadratic form of the outer-product matrix `vecMulVec a b` factors as `(x ⬝ᵥ a) * (b ⬝ᵥ
x)`. -/
theorem dotProduct_vecMulVec (a b x : Fin D → ℝ) :
    x ⬝ᵥ ((vecMulVec a b) *ᵥ x) = (x ⬝ᵥ a) * (b ⬝ᵥ x) := by
  simp only [dotProduct, mulVec, vecMulVec_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_comm, mul_left_comm]

/-- The trace of `vecMulVec a b` is the dot product of `a` and `b`. -/
theorem trace_vecMulVec (a b : Fin D → ℝ) :
    (vecMulVec a b).trace = a ⬝ᵥ b := by
  simp [Matrix.trace, vecMulVec_apply, dotProduct]

/-- The squared Euclidean norm of a real vector, defined by its dot product with itself. -/
def sqNorm (x : Fin D → ℝ) : ℝ := ∑ i, x i * x i

/-- The squared Euclidean norm is nonnegative. -/
theorem sqNorm_nonneg (x : Fin D → ℝ) : 0 ≤ sqNorm x :=
  Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))

/-- The trace of a finite square matrix is the sum of its diagonal entries. -/
theorem trace_eq_sum_diag (A : Matrix (Fin D) (Fin D) ℝ) :
    A.trace = ∑ i, A i i := by
  simp [Matrix.trace]

/-- Every diagonal entry of a real positive semidefinite matrix is nonnegative. -/
theorem diag_nonneg_of_posSemidef {A : Matrix (Fin D) (Fin D) ℝ} (hA : A.PosSemidef)
    (i : Fin D) : 0 ≤ A i i :=
  hA.diag_nonneg (i := i)

/-- Each diagonal entry of a real positive semidefinite matrix is at most its trace. -/
theorem diag_le_trace {A : Matrix (Fin D) (Fin D) ℝ} (hA : A.PosSemidef)
    (i : Fin D) : A i i ≤ A.trace := by
  rw [trace_eq_sum_diag]
  exact Finset.single_le_sum (fun j _ => diag_nonneg_of_posSemidef hA j) (Finset.mem_univ i)

/-- The quadratic form of a positive semidefinite matrix at `x` is at most `sqNorm x` times the
trace. -/
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

/-- If the quadratic form is at most `b` on every unit vector, its trace is at most `D * b`. See
[Marriott and Watrous, Theorem 3.4][MarriottWatrous2005]. -/
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

/-- A unit vector with quadratic-form value at least `a` gives the lower trace bound `a ≤
A.trace` for a positive semidefinite matrix. -/
theorem trace_ge_of_witness {A : Matrix (Fin D) (Fin D) ℝ} (hA : A.PosSemidef)
    (x : Fin D → ℝ) (a : ℝ) (hx : sqNorm x = 1) (h : a ≤ x ⬝ᵥ (A *ᵥ x)) :
    a ≤ A.trace := by
  have hle := inner_le_trace hA x
  rw [hx, one_mul] at hle
  exact h.trans hle

/-- For a positive semidefinite matrix, a unit witness with quadratic-form value at least `a`
and a uniform unit-vector bound `b` give `a ≤ A.trace` and `A.trace ≤ D * b`. See [Marriott
and Watrous, Theorem 3.4][MarriottWatrous2005]. -/
theorem trace_sandwich {A : Matrix (Fin D) (Fin D) ℝ} (hA : A.PosSemidef)
    (a b : ℝ) (hcomplete : ∃ x, sqNorm x = 1 ∧ a ≤ x ⬝ᵥ (A *ᵥ x))
    (hsound : ∀ x, sqNorm x = 1 → x ⬝ᵥ (A *ᵥ x) ≤ b) :
    a ≤ A.trace ∧ A.trace ≤ D * b := by
  obtain ⟨x, hx, hax⟩ := hcomplete
  exact ⟨trace_ge_of_witness hA x a hx hax, trace_le_card_mul_of_unit_le hA b hsound⟩

/-- The average quadratic-form value on the standard basis equals the trace divided by `D`. See
[Marriott and Watrous, Theorem 3.6][MarriottWatrous2005]. -/
theorem totallyMixed_eq_trace_div (A : Matrix (Fin D) (Fin D) ℝ) :
    (∑ i, (fun j => if j = i then (1 : ℝ) else 0) ⬝ᵥ
      (A *ᵥ (fun j => if j = i then (1 : ℝ) else 0))) / D = A.trace / D := by
  have h : ∀ i : Fin D, (fun j => if j = i then (1 : ℝ) else 0) ⬝ᵥ
      (A *ᵥ (fun j => if j = i then (1 : ℝ) else 0)) = A i i := by
    intro i; simp [dotProduct, mulVec]
  simp only [h, trace_eq_sum_diag]

/-- A unit witness with acceptance at least `1 - 2 ^ (-(m + 2))` forces the trace to be at least
three quarters in dimension `2 ^ m`. See [Marriott and Watrous, Theorem
3.4][MarriottWatrous2005]. -/
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

/-- If every unit vector has acceptance at most `2 ^ (-(m + 2))`, the trace is at most one
quarter in dimension `2 ^ m`. See [Marriott and Watrous, Theorem 3.4][MarriottWatrous2005]. -/
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
