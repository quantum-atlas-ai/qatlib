/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-!
# Fibonacci matrices and a determinant obstruction to density

The explicit Fibonacci matrices `Fmat` and `Rmat` define unitary generators `S1` and `S2`. Their
word products have determinants whose tenth powers equal one, and `not_S1S2Dense` uses this
restriction to refute the assertion that these words approximate every matrix in `U(2)`
[KauffmanLomonaco2006].

## Main statements

* `S1_unitary`: proves unitarity of the first generator.
* `S2_unitary`: proves unitarity of the second generator.
* `det_wordProduct_pow_ten`: gives the determinant restriction on every word.
* `not_S1S2Dense`: refutes density in the full unitary group.

## References

* [Kauffman and Lomonaco, 2006][KauffmanLomonaco2006]
-/

set_option autoImplicit false

noncomputable section

open Matrix

namespace Qatlib.Papers.AnyonicSpin06.MainResults.FibonacciDensity

/-- The golden ratio `(1 + sqrt 5) / 2`. -/
def goldenRatio : ℝ := (1 + Real.sqrt 5) / 2

/-- The real parameter `(sqrt 5 - 1) / 2`. -/
def tau : ℝ := (Real.sqrt 5 - 1) / 2

/-- The Fibonacci parameter `tau` is nonnegative. -/
lemma tau_nonneg : 0 ≤ tau := by
  unfold tau
  have h5 : (1 : ℝ) ≤ Real.sqrt 5 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  linarith

/-- The Fibonacci parameter satisfies `tau ^ 2 + tau = 1`. -/
lemma tau_sq_add : tau ^ 2 + tau = 1 := by
  unfold tau
  have h5 : (Real.sqrt 5) ^ 2 = (5 : ℝ) := Real.sq_sqrt (by norm_num)
  nlinarith [h5]

/-- The product of `sqrt tau` with itself equals `tau`. -/
lemma sqrt_tau_sq : Real.sqrt tau * Real.sqrt tau = tau := by
  rw [← pow_two, Real.sq_sqrt tau_nonneg]

/-- The symmetric Fibonacci matrix with diagonal entries `tau`, `-tau` and off-diagonal entries
`sqrt tau`. -/
def Fmat : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(tau : ℂ), (Real.sqrt tau : ℂ); (Real.sqrt tau : ℂ), -(tau : ℂ)]

/-- The complex phase `exp (I * 3 * π / 5)`. -/
def A5 : ℂ := Complex.exp (Complex.I * ((3 * Real.pi / 5 : ℝ) : ℂ))

/-- The diagonal Fibonacci matrix with entries `-A5 ^ 4` and `A5 ^ 8`. -/
def Rmat : Matrix (Fin 2) (Fin 2) ℂ := !![-(A5 ^ 4), 0; 0, A5 ^ 8]

/-- The phase `A5` has complex norm one. -/
lemma norm_A5 : ‖A5‖ = 1 := by
  unfold A5
  rw [Complex.norm_exp]
  have h : (Complex.I * ((3 * Real.pi / 5 : ℝ) : ℂ)).re
      = - ((3 * Real.pi / 5 : ℝ) : ℂ).im := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im]
  rw [h, Complex.ofReal_im]
  simp

/-- For a complex number of norm one, its conjugate times itself equals one. -/
lemma star_mul_self_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) : star z * z = 1 := by
  have h : (star z) * z = (Complex.normSq z : ℂ) := by
    simpa [Complex.star_def] using (Complex.normSq_eq_conj_mul_self (z := z)).symm
  rw [h, Complex.normSq_eq_norm_sq, hz]
  norm_num

/-- For a complex number of norm one, the number times its conjugate equals one. -/
lemma mul_star_self_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) :
    z * (starRingEnd ℂ) z = 1 := by
  rw [starRingEnd_apply]
  have h : z * star z = (Complex.normSq z : ℂ) := by
    simpa [Complex.star_def] using Complex.mul_conj z
  rw [h, Complex.normSq_eq_norm_sq, hz]
  norm_num

/-- The square of `Fmat` equals the identity matrix. -/
lemma F_sq : Fmat * Fmat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Fmat, Matrix.mul_apply, Fin.sum_univ_two]
  · have hs : (Real.sqrt tau : ℂ) * (Real.sqrt tau : ℂ) = (tau : ℂ) := by
      rw [← Complex.ofReal_mul, sqrt_tau_sq]
    have h : tau * tau + tau = 1 := by simpa [pow_two] using tau_sq_add
    have hc : (tau : ℂ) * (tau : ℂ) + (tau : ℂ) = 1 := by exact_mod_cast h
    rw [hs, hc]
  · ring
  · ring
  · have hs : (Real.sqrt tau : ℂ) * (Real.sqrt tau : ℂ) = (tau : ℂ) := by
      rw [← Complex.ofReal_mul, sqrt_tau_sq]
    have h : tau * tau + tau = 1 := by simpa [pow_two] using tau_sq_add
    have hc : (tau : ℂ) * (tau : ℂ) + (tau : ℂ) = 1 := by exact_mod_cast h
    rw [hs, add_comm, hc]

/-- The matrix `Fmat` is self-adjoint. -/
lemma star_Fmat : star Fmat = Fmat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Fmat]

/-- The matrix `Fmat` belongs to the unitary group. -/
lemma F_unitary : Fmat ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  rw [star_Fmat, F_sq]

/-- The matrix `Rmat` belongs to the unitary group. -/
lemma R_unitary : Rmat ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rmat, Matrix.mul_apply, Fin.sum_univ_two]
  · have h : ‖A5 ^ 4‖ = 1 := by rw [norm_pow, norm_A5, one_pow]
    simpa [star_pow] using mul_star_self_of_norm_one h
  · have h : ‖A5 ^ 8‖ = 1 := by rw [norm_pow, norm_A5, one_pow]
    simpa [star_pow] using mul_star_self_of_norm_one h

/-- The first Fibonacci generator, equal to `Rmat`. -/
def S1 : Matrix (Fin 2) (Fin 2) ℂ := Rmat

/-- The second Fibonacci generator, obtained as `Fmat * Rmat * Fmat`. -/
def S2 : Matrix (Fin 2) (Fin 2) ℂ := Fmat * Rmat * Fmat

/-- The first Fibonacci generator `S1` is unitary [KauffmanLomonaco2006]. -/
theorem S1_unitary : S1 ∈ Matrix.unitaryGroup (Fin 2) ℂ := R_unitary

/-- The second Fibonacci generator `S2` is unitary [KauffmanLomonaco2006]. -/
theorem S2_unitary : S2 ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  unfold S2
  exact mul_mem (mul_mem F_unitary R_unitary) F_unitary

/-- The ordered product of generators encoded by a Boolean list, with true selecting `S1` and
false selecting `S2`. -/
def wordProduct : List Bool → Matrix (Fin 2) (Fin 2) ℂ
  | [] => 1
  | b :: w => (if b then S1 else S2) * wordProduct w

/-- The assertion that words in `S1` and `S2` approximate every unitary two-by-two matrix to any
positive entrywise tolerance. -/
def S1S2Dense : Prop :=
  ∀ U ∈ Matrix.unitaryGroup (Fin 2) ℂ, ∀ ε : ℝ, 0 < ε →
    ∃ w : List Bool, ∀ i j, ‖wordProduct w i j - U i j‖ < ε

/-- The fifth power of `A5` equals minus one. -/
theorem A5_pow_five : A5 ^ 5 = -1 := by
  unfold A5
  rw [← Complex.exp_nat_mul]
  have h : (5 : ℕ) * (Complex.I * ((3 * Real.pi / 5 : ℝ) : ℂ))
      = (3 : ℕ) * (Complex.I * ((Real.pi : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [h, Complex.exp_nat_mul]
  have hpi : Complex.exp (Complex.I * ((Real.pi : ℝ) : ℂ)) = -1 := by
    have hI : Complex.I * ((Real.pi : ℝ) : ℂ) = (Real.pi : ℂ) * Complex.I := by ring
    rw [hI, Complex.exp_pi_mul_I]
  rw [hpi]
  norm_num

/-- The tenth power of `A5` equals one [KauffmanLomonaco2006]. -/
theorem A5_pow_ten : A5 ^ 10 = 1 := by
  have h : A5 ^ 10 = (A5 ^ 5) ^ 2 := by rw [← pow_mul]
  rw [h, A5_pow_five]
  norm_num

/-- The determinant of `Fmat` equals minus one. -/
theorem det_Fmat : Fmat.det = -1 := by
  rw [Matrix.det_fin_two]
  simp only [Fmat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  have hs : (Real.sqrt tau : ℂ) * (Real.sqrt tau : ℂ) = (tau : ℂ) := by
    rw [← Complex.ofReal_mul, sqrt_tau_sq]
  have h : tau * tau + tau = 1 := by simpa [pow_two] using tau_sq_add
  have hc : (tau : ℂ) * (tau : ℂ) + (tau : ℂ) = 1 := by exact_mod_cast h
  linear_combination -hc - hs

/-- The determinant of `S1` equals `-A5 ^ 12` [KauffmanLomonaco2006]. -/
theorem det_S1 : S1.det = -(A5 ^ 12) := by
  unfold S1 Rmat
  rw [Matrix.det_fin_two]
  simp
  ring

/-- The determinants of `S2` and `S1` are equal. -/
theorem det_S2 : S2.det = S1.det := by
  unfold S2 S1
  rw [Matrix.det_mul, Matrix.det_mul, det_Fmat]
  ring

/-- The tenth power of the determinant of `S1` equals one. -/
theorem det_S1_pow_ten : S1.det ^ 10 = 1 := by
  rw [det_S1]
  have h1 : (-(A5 ^ 12)) ^ 10 = (A5 ^ 12) ^ 10 := by
    rw [neg_pow]
    norm_num
  rw [h1, ← pow_mul, show (12 : ℕ) * 10 = 10 * 12 from by norm_num, pow_mul,
    A5_pow_ten]
  norm_num

/-- The tenth power of the determinant of `S2` equals one. -/
theorem det_S2_pow_ten : S2.det ^ 10 = 1 := by
  rw [det_S2]
  exact det_S1_pow_ten

/-- The determinant of every word in the Fibonacci generators has tenth power equal to one
[KauffmanLomonaco2006]. -/
theorem det_wordProduct_pow_ten (w : List Bool) :
    (wordProduct w).det ^ 10 = 1 := by
  induction w with
  | nil => simp [wordProduct]
  | cons b w ih =>
      have hg : ((if b then S1 else S2)).det ^ 10 = 1 := by
        split_ifs
        · exact det_S1_pow_ten
        · exact det_S2_pow_ten
      show (((if b then S1 else S2) * wordProduct w).det) ^ 10 = 1
      rw [Matrix.det_mul, mul_pow, hg, ih, one_mul]

/-- The determinant of every word in the Fibonacci generators has complex norm one. -/
theorem norm_det_wordProduct (w : List Bool) : ‖(wordProduct w).det‖ = 1 := by
  induction w with
  | nil => simp [wordProduct]
  | cons b w ih =>
      have hg : ‖((if b then S1 else S2)).det‖ = 1 := by
        split_ifs
        · rw [det_S1, norm_neg, norm_pow, norm_A5]
          norm_num
        · rw [det_S2, det_S1, norm_neg, norm_pow, norm_A5]
          norm_num
      show ‖(((if b then S1 else S2) * wordProduct w).det)‖ = 1
      rw [Matrix.det_mul, norm_mul, hg, ih, one_mul]

/-- For complex `z` and `w` of norm at most one, the norm of `z ^ n - w ^ n` is at most `n * ‖z
- w‖`. -/
theorem pow_sub_pow_norm_le {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ∀ n : ℕ, ‖z ^ n - w ^ n‖ ≤ (n : ℝ) * ‖z - w‖ := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hsplit :
          z ^ (n + 1) - w ^ (n + 1) = z ^ n * (z - w) + (z ^ n - w ^ n) * w := by
        ring
      rw [hsplit]
      have h1 : ‖z ^ n‖ ≤ 1 := by
        rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg z) hz
      have hnd : (0 : ℝ) ≤ ‖z - w‖ := norm_nonneg _
      have e1 : ‖z ^ n‖ * ‖z - w‖ ≤ 1 * ‖z - w‖ :=
        mul_le_mul_of_nonneg_right h1 hnd
      have e2 : ‖z ^ n - w ^ n‖ * ‖w‖ ≤ ((n : ℝ) * ‖z - w‖) * 1 :=
        mul_le_mul ih hw (norm_nonneg w) (by positivity)
      calc ‖z ^ n * (z - w) + (z ^ n - w ^ n) * w‖
          ≤ ‖z ^ n * (z - w)‖ + ‖(z ^ n - w ^ n) * w‖ := norm_add_le _ _
        _ = ‖z ^ n‖ * ‖z - w‖ + ‖z ^ n - w ^ n‖ * ‖w‖ := by rw [norm_mul, norm_mul]
        _ ≤ 1 * ‖z - w‖ + ((n : ℝ) * ‖z - w‖) * 1 := add_le_add e1 e2
        _ = ((n + 1 : ℕ) : ℝ) * ‖z - w‖ := by push_cast; ring

/-- If `a`, `b`, `c`, and `d` are within nonnegative tolerance `δ` of `1`, a unit complex number
`u`, `0`, and `0`, respectively, then `‖a * b - c * d - u‖ ≤ 2 * δ + 2 * δ ^ 2`. -/
theorem det_close {a b c d u : ℂ} {δ : ℝ} (hδ : 0 ≤ δ)
    (h1 : ‖a - 1‖ ≤ δ) (h2 : ‖b - u‖ ≤ δ) (h3 : ‖c‖ ≤ δ) (h4 : ‖d‖ ≤ δ)
    (hu : ‖u‖ = 1) :
    ‖a * b - c * d - u‖ ≤ 2 * δ + 2 * δ ^ 2 := by
  have key : a * b - c * d - u
      = (b - u) + (a - 1) * u + (a - 1) * (b - u) - c * d := by ring
  rw [key]
  have hA : ‖(a - 1) * u‖ ≤ δ := by
    rw [norm_mul, hu, mul_one]; exact h1
  have hB : ‖(a - 1) * (b - u)‖ ≤ δ * δ := by
    rw [norm_mul]; exact mul_le_mul h1 h2 (norm_nonneg _) hδ
  have hC : ‖c * d‖ ≤ δ * δ := by
    rw [norm_mul]; exact mul_le_mul h3 h4 (norm_nonneg _) hδ
  have htri : ‖(b - u) + (a - 1) * u + (a - 1) * (b - u) - c * d‖
      ≤ ‖b - u‖ + (‖(a - 1) * u‖ + (‖(a - 1) * (b - u)‖ + ‖c * d‖)) := by
    have e1 := norm_sub_le ((b - u) + (a - 1) * u + (a - 1) * (b - u)) (c * d)
    have e2 := norm_add_le ((b - u) + (a - 1) * u) ((a - 1) * (b - u))
    have e3 := norm_add_le (b - u) ((a - 1) * u)
    linarith
  nlinarith [htri, hA, hB, hC]

/-- The tenth power of `exp (I * π / 10)` equals minus one. -/
theorem exp_I_pi_div_ten_pow_ten :
    (Complex.exp (Complex.I * ((Real.pi / 10 : ℝ) : ℂ))) ^ 10 = -1 := by
  rw [← Complex.exp_nat_mul]
  have h : (10 : ℕ) * (Complex.I * ((Real.pi / 10 : ℝ) : ℂ))
      = (Real.pi : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_pi_mul_I]

/-- The complex number `exp (I * π / 10)` has norm one. -/
theorem norm_exp_I_pi_div_ten :
    ‖Complex.exp (Complex.I * ((Real.pi / 10 : ℝ) : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have h : (Complex.I * ((Real.pi / 10 : ℝ) : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im]
  rw [h]
  simp

/-- Words in `S1` and `S2` do not approximate every unitary two-by-two matrix to arbitrary
positive entrywise tolerance [KauffmanLomonaco2006]. -/
theorem not_S1S2Dense : ¬ S1S2Dense := by
  intro hd
  set u : ℂ := Complex.exp (Complex.I * ((Real.pi / 10 : ℝ) : ℂ)) with hu
  have hu_norm : ‖u‖ = 1 := by
    rw [hu]; exact norm_exp_I_pi_div_ten
  set U : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, u] with hU
  have hU_mem : U ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hU, Matrix.mul_apply, Fin.sum_univ_two]
    simpa using mul_star_self_of_norm_one hu_norm
  obtain ⟨w, hw⟩ := hd U hU_mem (1 / 25) (by norm_num)
  have h00 : ‖wordProduct w 0 0 - 1‖ < 1 / 25 := by
    have := hw 0 0; simpa [hU] using this
  have h11 : ‖wordProduct w 1 1 - u‖ < 1 / 25 := by
    have := hw 1 1; simpa [hU] using this
  have h01 : ‖wordProduct w 0 1‖ < 1 / 25 := by
    have := hw 0 1; simpa [hU] using this
  have h10 : ‖wordProduct w 1 0‖ < 1 / 25 := by
    have := hw 1 0; simpa [hU] using this
  have hdetW : (wordProduct w).det
      = wordProduct w 0 0 * wordProduct w 1 1
        - wordProduct w 0 1 * wordProduct w 1 0 := Matrix.det_fin_two _
  have hclose : ‖(wordProduct w).det - u‖ ≤ 2 * (1 / 25) + 2 * (1 / 25) ^ 2 := by
    rw [hdetW]
    exact det_close (by norm_num) (le_of_lt h00) (le_of_lt h11)
      (le_of_lt h01) (le_of_lt h10) hu_norm
  have hclose' : ‖(wordProduct w).det - u‖ < 1 / 5 := by
    have hlt : (2 : ℝ) * (1 / 25) + 2 * (1 / 25) ^ 2 < 1 / 5 := by norm_num
    linarith
  have hz : ‖(wordProduct w).det‖ ≤ 1 := le_of_eq (norm_det_wordProduct w)
  have h1u : ‖u‖ ≤ 1 := le_of_eq hu_norm
  have hlip := pow_sub_pow_norm_le hz h1u 10
  have hten : (wordProduct w).det ^ 10 = 1 := det_wordProduct_pow_ten w
  have hu10 : u ^ 10 = -1 := by rw [hu]; exact exp_I_pi_div_ten_pow_ten
  have hfar : (1 : ℝ) / 5 ≤ ‖(wordProduct w).det - u‖ := by
    have h2 : ‖(wordProduct w).det ^ 10 - u ^ 10‖ = 2 := by
      rw [hten, hu10]
      norm_num
    have hle : (2 : ℝ) ≤ 10 * ‖(wordProduct w).det - u‖ := by
      have h := hlip
      rw [h2] at h
      norm_num at h
      exact h
    linarith
  linarith [hclose', hfar]

end Qatlib.Papers.AnyonicSpin06.MainResults.FibonacciDensity
