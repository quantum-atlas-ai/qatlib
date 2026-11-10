/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.MatProdVerify04.MainResults

open Finset

theorem findEntry_sum_bound {n q m : ℝ} (hn : 0 < n) (hq : 0 < q) (hm : 0 ≤ m)
    (L : ℕ) :
    (∑ l ∈ Finset.range L, 4 * (((n / (2 : ℝ) ^ l) ^ 2 / q) ^ ((1 : ℝ) / 3)) * m)
      ≤ 4 * ((n ^ 2 / q) ^ ((1 : ℝ) / 3)) * m * L := by
  have hpow1 : ∀ l : ℕ, (1 : ℝ) ≤ (2 : ℝ) ^ l := fun l =>
    one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hterm : ∀ l ∈ Finset.range L,
      4 * (((n / (2 : ℝ) ^ l) ^ 2 / q) ^ ((1 : ℝ) / 3)) * m
        ≤ 4 * ((n ^ 2 / q) ^ ((1 : ℝ) / 3)) * m := by
    intro l _
    have h2l : (0 : ℝ) < (2 : ℝ) ^ l := by positivity
    have hdiv_nonneg : 0 ≤ n / (2 : ℝ) ^ l := by positivity
    have hdiv_le : n / (2 : ℝ) ^ l ≤ n := by
      rw [div_le_iff₀ h2l]
      nlinarith [hn.le, hpow1 l]
    have hsq : (n / (2 : ℝ) ^ l) ^ 2 ≤ n ^ 2 := by
      have hnn : 0 ≤ n := hn.le
      nlinarith [hdiv_nonneg, hdiv_le, hnn]
    have hbase : (n / (2 : ℝ) ^ l) ^ 2 / q ≤ n ^ 2 / q :=
      div_le_div_of_nonneg_right hsq hq.le
    have hx0 : 0 ≤ (n / (2 : ℝ) ^ l) ^ 2 / q := by positivity
    have hp : ((n / (2 : ℝ) ^ l) ^ 2 / q) ^ ((1 : ℝ) / 3)
        ≤ (n ^ 2 / q) ^ ((1 : ℝ) / 3) :=
      Real.rpow_le_rpow hx0 hbase (by norm_num)
    nlinarith [hp, hm]
  calc (∑ l ∈ Finset.range L,
        4 * (((n / (2 : ℝ) ^ l) ^ 2 / q) ^ ((1 : ℝ) / 3)) * m)
      ≤ ∑ _l ∈ Finset.range L, 4 * ((n ^ 2 / q) ^ ((1 : ℝ) / 3)) * m :=
        Finset.sum_le_sum hterm
    _ = 4 * ((n ^ 2 / q) ^ ((1 : ℝ) / 3)) * m * L := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

theorem quadrant_shrink {n q q' : ℝ} (hq : 0 < q)
    (hq' : q / 4 ≤ q') : (n / 2) ^ 2 / q' ≤ n ^ 2 / q := by
  have hn2 : (0 : ℝ) ≤ n ^ 2 := sq_nonneg n
  have hq'pos : 0 < q' := lt_of_lt_of_le (by positivity : (0 : ℝ) < q / 4) hq'
  rw [div_le_iff₀ hq'pos, div_mul_eq_mul_div, le_div_iff₀ hq]
  nlinarith [hn2, hq']

end Qatlib.Papers.MatProdVerify04.MainResults
