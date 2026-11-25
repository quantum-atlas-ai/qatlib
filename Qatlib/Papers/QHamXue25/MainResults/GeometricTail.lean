/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section

/-!
# Homotopy truncation and an integer order

A uniform contraction along deformation orders gives an absolutely convergent
tail in a Banach space. Choosing the integer order by the logarithm of the
target error bounds the geometric majorant.
-/

set_option autoImplicit false



namespace Qatlib.Papers.QHamXue25.MainResults

/-- Repeated application of the homotopy contraction bounds the order-`i` norm. -/
private theorem term_norm_bound {E : Type*} [NormedAddCommGroup E] (U : ℕ → E)
    (α : ℝ) (hα : 0 ≤ α) (hrec : ∀ i, ‖U (i + 1)‖ ≤ α * ‖U i‖) (i : ℕ) :
    ‖U i‖ ≤ α ^ i * ‖U 0‖ := by
  induction i with
  | zero => simp
  | succ i ih =>
    calc
      _ ≤ α * (α ^ i * ‖U 0‖) := (hrec i).trans (mul_le_mul_of_nonneg_left ih hα)
      _ = _ := by rw [pow_succ']; ring

/-- The discarded deformation orders are summable and satisfy Eq. (10). -/
theorem truncation_tail_le {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (U : ℕ → E) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hrec : ∀ i, ‖U (i + 1)‖ ≤ α * ‖U i‖) (m : ℕ) :
    Summable (fun j : ℕ => U (m + 1 + j)) ∧
      ‖∑' j : ℕ, U (m + 1 + j)‖ ≤ α ^ (m + 1) / (1 - α) * ‖U 0‖ := by
  let b := α ^ (m + 1) * ‖U 0‖
  have hg := (hasSum_geometric_of_norm_lt_one (ξ := α) (by rwa [Real.norm_of_nonneg hα0])).mul_left b
  have hpoint (j : ℕ) : ‖U (m + 1 + j)‖ ≤ b * α ^ j := by
    calc
      _ ≤ α ^ (m + 1 + j) * ‖U 0‖ := term_norm_bound U α hα0 hrec _
      _ = _ := by dsimp [b]; rw [pow_add]; ring
  refine ⟨Summable.of_norm_bounded hg.summable hpoint, ?_⟩
  calc
    _ ≤ b * (1 - α)⁻¹ := tsum_of_norm_bounded hg hpoint
    _ = _ := by dsimp [b]; ring

/-- The natural ceiling of the logarithmic cutoff in Eq. (11) controls
the geometric error majorant. -/
theorem truncation_order_le (α β ε : ℝ) (ha : 0 < α) (ha1 : α < 1)
    (hb : 0 < β) (he : 0 < ε) :
    α ^ ⌈Real.logb (1 / α) (β / ((1 - α) * ε))⌉₊ / (1 - α) * β ≤ ε := by
  have hd : 0 < 1 - α := sub_pos.mpr ha1
  have hbase : 1 < 1 / α := (lt_div_iff₀ ha).2 (by simpa using ha1)
  let X := β / ((1 - α) * ε)
  let k : ℕ := ⌈Real.logb (1 / α) X⌉₊
  have hX : 0 < X := div_pos hb (mul_pos hd he)
  have hk : Real.logb (1 / α) X ≤ (k : ℝ) := Nat.le_ceil _
  have hp : X ≤ (1 / α) ^ k := calc
    X = (1 / α) ^ Real.logb (1 / α) X :=
      (Real.rpow_logb (zero_lt_one.trans hbase) hbase.ne' hX).symm
    _ ≤ (1 / α) ^ (k : ℝ) := Real.rpow_le_rpow_of_exponent_le hbase.le hk
    _ = _ := Real.rpow_natCast _ _
  have h := mul_le_mul_of_nonneg_right hp (pow_nonneg ha.le k)
  rw [← mul_pow, div_mul_cancel₀ 1 ha.ne', one_pow] at h
  change α ^ k / (1 - α) * β ≤ ε
  rw [show α ^ k / (1 - α) * β = (X * α ^ k) * ε by dsimp [X]; field_simp]
  exact mul_le_of_le_one_left he.le h

/-- The source order after converting its one-based cutoff to degree `m`
gives a tail norm at most the target error. -/
theorem truncation_tail_le_error {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (U : ℕ → E) (α β ε : ℝ) (ha : 0 < α) (ha1 : α < 1) (hb : 0 < β) (he : 0 < ε)
    (hrec : ∀ i, ‖U (i + 1)‖ ≤ α * ‖U i‖) (hU : ‖U 0‖ ≤ β) :
    let m := ⌈Real.logb (1 / α) (β / ((1 - α) * ε))⌉₊ - 1
    ‖∑' j : ℕ, U (m + 1 + j)‖ ≤ ε := by
  let k : ℕ := ⌈Real.logb (1 / α) (β / ((1 - α) * ε))⌉₊
  change ‖∑' j : ℕ, U ((k - 1) + 1 + j)‖ ≤ ε
  have hk : k ≤ (k - 1) + 1 := by omega
  have hpow : α ^ ((k - 1) + 1) ≤ α ^ k :=
    pow_le_pow_of_le_one ha.le ha1.le hk
  have hq : 0 ≤ α ^ ((k - 1) + 1) / (1 - α) := by positivity
  calc
    _ ≤ α ^ ((k - 1) + 1) / (1 - α) * ‖U 0‖ :=
      (truncation_tail_le U α ha.le ha1 hrec (k - 1)).2
    _ ≤ α ^ ((k - 1) + 1) / (1 - α) * β := mul_le_mul_of_nonneg_left hU hq
    _ ≤ α ^ k / (1 - α) * β := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hpow (sub_nonneg.mpr ha1.le)) hb.le
    _ ≤ ε := truncation_order_le α β ε ha ha1 hb he

end Qatlib.Papers.QHamXue25.MainResults
