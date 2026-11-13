/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.KernelWeightAlgebra
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Summability of integer sampling weights

`latticeCauchy` is a discrete Cauchy profile dominating the integer weight norms. A telescoping
comparison proves summability for spacing parameter at least one and bounds the full lattice
mass by five.

The comparison yields absolute summability of the complex integer weights and bounds every
finite norm sum by `5 * integerWeightConstant`. These bounds control LCU coefficient mass in
[WangEtAl2026].

## Main statements

* `latticeCauchy_tsum_le_five`: bounds the discrete Cauchy mass.
* `integerWeight_lattice_norm_tsum_le`: bounds the total sampling weight norm.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false

namespace CBMD

open scoped BigOperators

/-- The discrete Cauchy profile `a / (a² + k²)` on integer indices. -/
noncomputable def latticeCauchy (a : ℝ) (k : ℤ) : ℝ :=
  a / (a ^ 2 + (k : ℝ) ^ 2)

/-- For `a ≥ 1`, the positive-index Cauchy term at `n + 1` is bounded by `2a / (a + n) - 2a / (a
+ n + 1)`. -/
private theorem latticeCauchy_nat_le_telescope {a : ℝ} (ha : 1 ≤ a) (n : ℕ) :
    a / (a ^ 2 + ((n : ℝ) + 1) ^ 2) ≤
      2 * a / (a + n) - 2 * a / (a + (n + 1 : ℕ)) := by
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have h0 : 0 < a + n := by positivity
  have h1 : 0 < a + (n + 1 : ℕ) := by positivity
  have hden : 0 < a ^ 2 + ((n : ℝ) + 1) ^ 2 := by positivity
  have hpoly : (a + n) * (a + (n + 1 : ℕ)) ≤
      2 * (a ^ 2 + ((n : ℝ) + 1) ^ 2) := by
    push_cast
    nlinarith [sq_nonneg (a - ((n : ℝ) + 1))]
  calc
    a / (a ^ 2 + ((n : ℝ) + 1) ^ 2) ≤
        2 * a / ((a + n) * (a + (n + 1 : ℕ))) := by
      apply (div_le_div_iff₀ hden (mul_pos h0 h1)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hpoly ha0.le]
    _ = 2 * a / (a + n) - 2 * a / (a + (n + 1 : ℕ)) := by
      field_simp
      push_cast
      ring

/-- For `a ≥ 1`, every finite initial sum of the positive-index Cauchy terms is at most two. -/
theorem latticeCauchy_sum_range_le_two {a : ℝ} (ha : 1 ≤ a) (N : ℕ) :
    (∑ n ∈ Finset.range N, latticeCauchy a (n + 1)) ≤ 2 := by
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ha
  calc
    (∑ n ∈ Finset.range N, latticeCauchy a (n + 1)) ≤
        ∑ n ∈ Finset.range N,
          (2 * a / (a + n) - 2 * a / (a + (n + 1 : ℕ))) := by
      apply Finset.sum_le_sum
      intro n _
      simpa only [latticeCauchy, Int.cast_add, Int.cast_natCast, Int.cast_one] using
        latticeCauchy_nat_le_telescope ha n
    _ = 2 * a / a - 2 * a / (a + N) := by
      rw [Finset.sum_range_sub']
      simp
    _ ≤ 2 := by
      rw [mul_div_cancel_right₀ 2 ha0.ne']
      exact sub_le_self _ (by positivity)

/-- For `a ≥ 1`, the discrete Cauchy profile is summable over the integers. -/
theorem latticeCauchy_summable {a : ℝ} (ha : 1 ≤ a) :
    Summable (latticeCauchy a) := by
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have hplus : Summable (fun n : ℕ => latticeCauchy a (n + 1)) :=
    summable_of_sum_range_le (fun n => by unfold latticeCauchy; positivity)
      (latticeCauchy_sum_range_le_two ha)
  have hminus : (fun n : ℕ => latticeCauchy a (-(n + 1))) =
      (fun n : ℕ => latticeCauchy a (n + 1)) := by
    funext n
    simp only [latticeCauchy, Int.cast_neg, even_two, Even.neg_pow]
  exact hplus.of_add_one_of_neg_add_one (hminus ▸ hplus)

/-- For `a ≥ 1`, the full discrete Cauchy sum over the integers is at most five. -/
theorem latticeCauchy_tsum_le_five {a : ℝ} (ha : 1 ≤ a) :
    (∑' k : ℤ, latticeCauchy a k) ≤ 5 := by
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have hplus : Summable (fun n : ℕ => latticeCauchy a (n + 1)) :=
    summable_of_sum_range_le (fun n => by unfold latticeCauchy; positivity)
      (latticeCauchy_sum_range_le_two ha)
  have hminus : (fun n : ℕ => latticeCauchy a (-(n + 1))) =
      (fun n : ℕ => latticeCauchy a (n + 1)) := by
    funext n
    simp only [latticeCauchy, Int.cast_neg, even_two, Even.neg_pow]
  rw [tsum_of_add_one_of_neg_add_one hplus (hminus ▸ hplus), hminus]
  have hs : (∑' n : ℕ, latticeCauchy a (n + 1)) ≤ 2 :=
    Real.tsum_le_of_sum_range_le (fun n => by unfold latticeCauchy; positivity)
      (latticeCauchy_sum_range_le_two ha)
  have hz : latticeCauchy a 0 ≤ 1 := by
    simp only [latticeCauchy, Int.cast_zero, zero_pow (by omega : (2 : ℕ) ≠ 0), add_zero]
    apply (div_le_one (sq_pos_of_pos ha0)).mpr
    nlinarith
  linarith

/-- For positive `a`, the discrete Cauchy profile equals `(1 / a) * (1 / (1 + (k / a)²))`. -/
theorem latticeCauchy_eq_scaled {a : ℝ} (ha : 0 < a) (k : ℤ) :
    latticeCauchy a k = (1 / a) * (1 / (1 + ((k : ℝ) / a) ^ 2)) := by
  unfold latticeCauchy
  field_simp

/-- For `a ≥ 1`, the scaled Cauchy values `1 / (1 + (k / a)²)` are summable over integer
indices. -/
theorem scaled_cauchy_summable {a : ℝ} (ha : 1 ≤ a) :
    Summable (fun k : ℤ => 1 / (1 + ((k : ℝ) / a) ^ 2)) := by
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have h := (latticeCauchy_summable ha).mul_left a
  convert! h using 1
  funext k
  rw [latticeCauchy_eq_scaled ha0]
  field_simp

/-- For `a ≥ 1`, the sum of `1 / (1 + (k / a)²)`, divided by `a`, is at most five. -/
theorem scaled_cauchy_tsum_le_five {a : ℝ} (ha : 1 ≤ a) :
    (1 / a) * (∑' k : ℤ, 1 / (1 + ((k : ℝ) / a) ^ 2)) ≤ 5 := by
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ha
  rw [← tsum_mul_left]
  simpa only [← latticeCauchy_eq_scaled ha0] using latticeCauchy_tsum_le_five ha

/-- For `a ≥ 1`, each sampled integer weight norm is at most `integerWeightConstant *
latticeCauchy a k`. -/
private theorem integerWeight_lattice_norm_le (m : ℕ) {a : ℝ} (ha : 1 ≤ a) (k : ℤ) :
    ‖integerWeight m a ((k : ℝ) / a)‖ ≤ integerWeightConstant * latticeCauchy a k := by
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ha
  calc
    _ ≤ integerWeightConstant / (a * (1 + ((k : ℝ) / a) ^ 2)) :=
      integerWeight_norm_le m ha0 _
    _ = integerWeightConstant * latticeCauchy a k := by
      rw [latticeCauchy_eq_scaled ha0]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- For `a ≥ 1`, the norms of the integer weights sampled at `k / a` form a summable series. -/
theorem integerWeight_lattice_norm_summable (m : ℕ) {a : ℝ} (ha : 1 ≤ a) :
    Summable (fun k : ℤ => ‖integerWeight m a ((k : ℝ) / a)‖) := by
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (integerWeight_lattice_norm_le m ha)
    ((latticeCauchy_summable ha).mul_left integerWeightConstant)

/-- For `a ≥ 1`, the complex integer weights sampled at `k / a` form a summable series. -/
theorem integerWeight_lattice_summable (m : ℕ) {a : ℝ} (ha : 1 ≤ a) :
    Summable (fun k : ℤ => integerWeight m a ((k : ℝ) / a)) :=
  (integerWeight_lattice_norm_summable m ha).of_norm

/-- For `a ≥ 1`, the total norm of all sampled integer weights is at most `5 *
integerWeightConstant`. -/
theorem integerWeight_lattice_norm_tsum_le (m : ℕ) {a : ℝ} (ha : 1 ≤ a) :
    (∑' k : ℤ, ‖integerWeight m a ((k : ℝ) / a)‖) ≤ 5 * integerWeightConstant := by
  calc
    _ ≤ ∑' k : ℤ, integerWeightConstant * latticeCauchy a k :=
      Summable.tsum_le_tsum (integerWeight_lattice_norm_le m ha)
        (integerWeight_lattice_norm_summable m ha)
        ((latticeCauchy_summable ha).mul_left integerWeightConstant)
    _ = integerWeightConstant * (∑' k : ℤ, latticeCauchy a k) := tsum_mul_left
    _ ≤ integerWeightConstant * 5 :=
      mul_le_mul_of_nonneg_left (latticeCauchy_tsum_le_five ha) integerWeightConstant_nonneg
    _ = 5 * integerWeightConstant := mul_comm _ _

/-- For `a ≥ 1`, the sum of sampled integer weight norms over any finite index set is at most `5
* integerWeightConstant`. -/
theorem integerWeight_lattice_norm_sum_le (m : ℕ) {a : ℝ} (ha : 1 ≤ a) (s : Finset ℤ) :
    (∑ k ∈ s, ‖integerWeight m a ((k : ℝ) / a)‖) ≤ 5 * integerWeightConstant := by
  exact (Summable.sum_le_tsum s (fun _ _ => norm_nonneg _)
    (integerWeight_lattice_norm_summable m ha)).trans (integerWeight_lattice_norm_tsum_le m ha)

end CBMD

end Qatlib.Foundations.CbmdAnalysis.Core
