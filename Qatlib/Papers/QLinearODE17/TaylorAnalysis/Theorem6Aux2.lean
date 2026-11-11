/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLinearODE17.TaylorAnalysis.Theorem6AltAux
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Source remainder and diagonal matrix identities

This module relates `taylorSrcPoly` to `taylorPoly` and bounds its error against `(exp z - 1) /
z`. Matrix identities for diagonal powers, similarity, scaling, and finite sums support
coordinatewise Taylor evolution. See [BerryEtAl2017ODE] for the paper's setting.

## Main statements

* `taylorSrcPoly_mul`: Multiplying `taylorSrcPoly k z` by `z` gives `taylorPoly k z - 1`.
* `sum_mulVec`: Matrix-vector multiplication distributes over a finite sum of matrices.

## References

* [Berry et al., 2017][BerryEtAl2017ODE]
-/

open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.QLinearODE17.TaylorAnalysis

open Matrix

/-- Multiplying `taylorSrcPoly k z` by `z` gives `taylorPoly k z - 1`. -/
theorem taylorSrcPoly_mul (k : ℕ) (z : ℂ) :
    z * taylorSrcPoly k z = taylorPoly k z - 1 := by
  have hsplit : taylorPoly k z =
      1 + ∑ i ∈ Finset.range k, z ^ (i + 1) / ((Nat.factorial (i + 1) : ℕ) : ℂ) := by
    rw [taylorPoly, Finset.sum_range_succ']
    have hz0' : z ^ 0 / ((Nat.factorial 0 : ℕ) : ℂ) = 1 := by simp
    rw [hz0', add_comm]
  rw [hsplit, add_sub_cancel_left, taylorSrcPoly, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_div_assoc', pow_succ, mul_comm]

/-- For nonzero `z` with `‖z‖ ≤ 1` and `k ≥ 5`, the source-polynomial error is at most `(7/6) *
‖z‖^k / (k+1)!`. -/
theorem exp_src_defect (k : ℕ) (z : ℂ) (hk : 5 ≤ k) (hz1 : ‖z‖ ≤ 1) (hz0 : z ≠ 0) :
    ‖(Complex.exp z - 1) / z - taylorSrcPoly k z‖ ≤
      (7 / 6 : ℝ) * ‖z‖ ^ k / ((Nat.factorial (k + 1) : ℕ) : ℝ) := by
  have hkey : (Complex.exp z - 1) / z - taylorSrcPoly k z =
      (Complex.exp z - taylorPoly k z) / z := by
    apply mul_left_cancel₀ hz0
    have e1 : z * ((Complex.exp z - 1) / z - taylorSrcPoly k z) =
        Complex.exp z - taylorPoly k z := by
      rw [mul_sub, mul_div_assoc', mul_div_cancel_left₀ _ hz0, taylorSrcPoly_mul]
      ring
    rw [e1, mul_div_assoc', mul_div_cancel_left₀ _ hz0]
  have hzpos : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
  have hzne : ‖z‖ ≠ 0 := ne_of_gt hzpos
  have hdef := taylorPoly_defect k z hk hz1
  have hstep1 : ‖Complex.exp z - taylorPoly k z‖ / ‖z‖ ≤
      ((7 / 6 : ℝ) * ‖z‖ ^ (k + 1) / ((Nat.factorial (k + 1) : ℕ) : ℝ)) / ‖z‖ :=
    (div_le_div_iff₀ hzpos hzpos).mpr
      (mul_le_mul_of_nonneg_right hdef (le_of_lt hzpos))
  rw [hkey, norm_div]
  refine hstep1.trans ?_
  rw [pow_succ]
  field_simp
  norm_num

/-- If `Re z ≤ 0`, then `‖exp z‖ ≤ 1`. -/
theorem complex_norm_exp_le_one (z : ℂ) (hz : z.re ≤ 0) : ‖Complex.exp z‖ ≤ 1 := by
  rw [Complex.norm_exp]
  exact Real.exp_le_one_iff.mpr hz

section Diag

variable {N : Type} [Fintype N] [DecidableEq N]

omit [DecidableEq N] in

/-- Multiplication by a diagonal matrix acts coordinatewise by its diagonal entries. -/
theorem diag_mulVec (D : Matrix N N ℂ) (hd : ∀ i j : N, i ≠ j → D i j = 0)
    (v : QState N) (n : N) : (D *ᵥ v) n = D n n * v n := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single_of_mem n (Finset.mem_univ n) (fun j _ hj => by
    rw [hd n j (Ne.symm hj), zero_mul])]

/-- Every natural power of a diagonal matrix has the corresponding powers on its diagonal and
zero off the diagonal. -/
theorem diag_pow (D : Matrix N N ℂ) (hd : ∀ i j : N, i ≠ j → D i j = 0) (r : ℕ) :
    ∀ (i j : N), (D ^ r) i j = if i = j then (D i i) ^ r else 0 := by
  induction r with
  | zero =>
    intro i j
    rw [pow_zero, Matrix.one_apply]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij]
  | succ r ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    by_cases hij : i = j
    · rw [hij]
      rw [if_pos rfl]
      rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j) (fun c _ hc => by
        rw [ih j c, if_neg (Ne.symm hc)]
        ring)]
      rw [ih j j, if_pos rfl, pow_succ]
    · rw [if_neg hij]
      apply Finset.sum_eq_zero
      intro c _
      by_cases h1 : i = c
      · rw [← h1, hd i j hij]
        ring
      · rw [ih i c, if_neg h1]
        ring

/-- Under the stated two-sided inverse hypotheses, similarity by `V` commutes with natural
matrix powers. -/
theorem simil_pow (A V D : Matrix N N ℂ) (hA : A = V * D * V⁻¹)
    (hV1 : V * V⁻¹ = 1) (hV2 : V⁻¹ * V = 1) (r : ℕ) : A ^ r = V * (D ^ r) * V⁻¹ := by
  induction r with
  | zero => simp [hV1]
  | succ r ih =>
    rw [pow_succ, ih, hA, pow_succ]
    have hmid2 : V⁻¹ * (V * (D * V⁻¹)) = D * V⁻¹ := by
      rw [← Matrix.mul_assoc, hV2, one_mul]
    simp only [Matrix.mul_assoc]
    rw [hmid2]

/-- Real scalar multiplication of `V * D * V⁻¹` can be applied to the middle factor `D`. -/
theorem smul_simil (h : ℝ) (V D : Matrix N N ℂ) : h • (V * D * V⁻¹) = V * (h • D) * V⁻¹ := by
  rw [← Algebra.smul_mul_assoc, ← Algebra.mul_smul_comm]

omit [DecidableEq N] in

/-- Matrix-vector multiplication distributes over a finite sum of matrices. -/
theorem sum_mulVec {ι : Type} (s : Finset ι) (Ms : ι → Matrix N N ℂ) (v : QState N) :
    (∑ i ∈ s, Ms i) *ᵥ v = ∑ i ∈ s, (Ms i *ᵥ v) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Matrix.add_mulVec, ih, Finset.sum_insert ha]

end Diag

end Qatlib.Papers.QLinearODE17.TaylorAnalysis
