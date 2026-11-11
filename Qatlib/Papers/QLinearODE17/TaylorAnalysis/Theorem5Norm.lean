/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLinearODE17.TaylorAnalysis.Theorem5Columns

/-!
# Operator norm of diagonal Taylor inverses

This module passes from squared entry bounds to operator norms and controls the number of
history labels. The scalar inverse estimate is then lifted coordinatewise to the inverse V2
Taylor system for diagonal matrices. See [BerryEtAl2017ODE] for the paper's setting.

## Main statements

* `taylor_opNorm_le_of_entry_sq`: A bound `c²` on the sum of squared entry norms implies the
  operator-norm bound `‖M‖ ≤ c` for nonnegative `c`.
* `taylorV2_diagonal_inverse_norm_le`: For diagonal `D` with entries in the left unit half-disk
  and the stated parameter bounds, the inverse V2 Taylor matrix has norm at most `3 * sqrt k *
  (m+p)`.

## References

* [Berry et al., 2017][BerryEtAl2017ODE]
-/

open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
set_option backward.isDefEq.respectTransparency false


set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QLinearODE17.TaylorAnalysis
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
set_option warningAsError false

/-- A bound `c²` on the sum of squared entry norms implies the operator-norm bound `‖M‖ ≤ c` for
nonnegative `c`. -/
theorem taylor_opNorm_le_of_entry_sq {I : Type} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hM : (∑ i,∑ j,‖M i j‖^2) ≤ c^2) : ‖M‖ ≤ c := by
  apply taylor_opNorm_le_of_vec_sq hc
  intro x
  have hpoint (i : I) : ‖(M *ᵥ x) i‖^2 ≤ (∑ j,‖M i j‖^2)*(∑ j,‖x j‖^2) := by
    have hn : ‖(M *ᵥ x) i‖ ≤ ∑ j,‖M i j‖*‖x j‖ := by
      simpa only [Matrix.mulVec,dotProduct,norm_mul] using!
        norm_sum_le (Finset.univ : Finset I) (fun j => M i j*x j)
    exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans
      (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖M i j‖) (fun j => ‖x j‖))
  calc
    _ ≤ ∑ i,(∑ j,‖M i j‖^2)*(∑ j,‖x j‖^2) := Finset.sum_le_sum (fun i _ => hpoint i)
    _ = (∑ i,∑ j,‖M i j‖^2)*(∑ j,‖x j‖^2) := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hM (Finset.sum_nonneg (fun _ _ => by positivity))

/-- For `k ≥ 5` and `p > 0`, the number of Taylor labels is at most `(6/5) * k * (m+p)`. -/
theorem taylor_label_count_le (m k p : ℕ) (hk : 5 ≤ k) (hp : 0 < p) :
    (m*(k+1)+p+1 : ℕ) ≤ (6/5 : ℝ)*(k : ℝ)*((m+p : ℕ) : ℝ) := by
  have hkr : (5 : ℝ) ≤ k := by exact_mod_cast hk
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hmR : (0 : ℝ) ≤ m := by positivity
  have hkm := mul_le_mul_of_nonneg_right hkr hmR
  have hkp := mul_le_mul_of_nonneg_right hkr (show (0 : ℝ) ≤ p by positivity)
  push_cast
  nlinarith

/-- Under the degree, factorial, padding, and left-half-disk hypotheses, the scalar inverse norm
is at most `3 * sqrt k * (m+p)`. -/
theorem scalarInverseMatrix_norm_le (m k p : ℕ) (hk : 5 ≤ k) (hp : 0 < p) (z : ℂ)
    (hfac : 2*m ≤ Nat.factorial (k+1)) (hz : ‖z‖ ≤ 1) (hre : z.re ≤ 0) :
    ‖scalarInverseMatrix m k p z‖ ≤ 3*Real.sqrt (k : ℝ)*((m+p : ℕ) : ℝ) := by
  apply taylor_opNorm_le_of_entry_sq _ _ (by positivity)
  rw [Finset.sum_comm]
  have hs :=
      Finset.sum_le_sum (s := Finset.univ)
      (fun c _ => scalarInverseMatrix_column_sq_le m k p hk hp z hfac hz hre c)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  have hL := taylor_label_count_le m k p hk hp
  have hh := mul_le_mul_of_nonneg_right hL
    (show (0 : ℝ) ≤ (((31/30 : ℝ)^2*(87/32))*(57/25))*((m+p : ℕ) : ℝ) by positivity)
  have hc : (0 : ℝ) ≤ (k : ℝ)*((m+p : ℕ) : ℝ)^2 := by positivity
  rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity : (0 : ℝ) ≤ k)]
  norm_num at hs hh ⊢
  nlinarith

variable {N : Type} [Fintype N] [DecidableEq N]

/-- The action of `taylorV2InvDiag` on each fixed state coordinate is the corresponding scalar
inverse-matrix action on its label coordinates. -/
theorem taylorV2InvDiag_mulVec (m k p : ℕ) (D : Matrix N N ℂ)
    (x : Fin (m*(k+1)+p+1) × N → ℂ) (l : Fin (m*(k+1)+p+1)) (n : N) :
    (taylorV2InvDiag m k p D *ᵥ x) (l,n) =
      (scalarInverseMatrix m k p (D n n) *ᵥ (fun j => x (j,n))) l := by
  simp [taylorV2InvDiag,Matrix.blockDiagonal_apply,Matrix.mulVec,dotProduct,
    Fintype.sum_prod_type,ite_mul]

/-- For diagonal `D` with entries in the left unit half-disk and the stated parameter bounds,
the inverse V2 Taylor matrix has norm at most `3 * sqrt k * (m+p)`. -/
theorem taylorV2_diagonal_inverse_norm_le (m k p : ℕ) (D : Matrix N N ℂ)
    (hm : 0 < m) (hk : 5 ≤ k) (hp : 0 < p) (hfac : 2*m ≤ Nat.factorial (k+1))
    (hd : ∀ i j : N,i≠j → D i j=0) (hz : ∀ n,‖D n n‖ ≤ 1) (hre : ∀ n,(D n n).re ≤ 0) :
    ‖(taylorStepMatrixV2 m k p D)⁻¹‖ ≤ 3*Real.sqrt (k : ℝ)*((m+p : ℕ) : ℝ) := by
  rw [← taylorV2InvDiag_eq_inv m k p D hm hd]
  apply taylor_opNorm_le_of_vec_sq (by positivity)
  intro x
  rw [Fintype.sum_prod_type,Fintype.sum_prod_type,Finset.sum_comm]
  calc
    _ = ∑ n,∑ l,‖(scalarInverseMatrix m k p (D n n) *ᵥ (fun j => x (j,n))) l‖^2 := by
      simp_rw [taylorV2InvDiag_mulVec]
    _ ≤ ∑ n,(3*Real.sqrt (k : ℝ)*((m+p : ℕ) : ℝ))^2*(∑ l,‖x (l,n)‖^2) := by
      apply Finset.sum_le_sum
      intro n _
      have h := taylor_mulVec_sq_le (scalarInverseMatrix m k p (D n n)) (fun j => x (j,n))
      have hn :=
          pow_le_pow_left₀ (norm_nonneg _)
          (scalarInverseMatrix_norm_le m k p hk hp (D n n) hfac (hz n) (hre n)) 2
      exact h.trans (mul_le_mul_of_nonneg_right hn (Finset.sum_nonneg (fun _ _ => by positivity)))
    _ = _ := by rw [← Finset.mul_sum,Finset.sum_comm]

end Qatlib.Papers.QLinearODE17.TaylorAnalysis
