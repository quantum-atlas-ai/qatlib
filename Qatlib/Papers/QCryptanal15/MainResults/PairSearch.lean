/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCryptanal15.MainResults.Complexity.Core

/-!
# Subset pair-search cost identities

The subset scale `n/√k` normalizes the expected pair-density expression. `theorem5_cost`
transfers a supplied two-thirds-power cost bound to this scale, and
`theorem5_constant_probability` gives the associated real-power probability inequality. The
mathematical context is [KaplanEtAl2015].

## Main statements

* `theorem5_cost`: A cost bounded by `C * m^(2/3)` for every positive `m` is bounded at `m =
  n/√k` by `C * n^(2/3) * k^(-1/3)` for positive `n` and `k`.
* `theorem5_constant_probability`: For real `k > 1`, the expression `1 - (1 - 1/k)^k` is at
  least one half.

## References

* [Kaplan et al., 2015][KaplanEtAl2015]
-/

set_option warningAsError false

set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace Qatlib.Papers.QCryptanal15.MainResults.PairSearch

open Complexity

/-- For positive `n` and `k`, the normalized subset scale satisfies `k * ((n/√k)/n)² = 1`. See
[KaplanEtAl2015]. -/
theorem theorem5_subset_pair_density (n k : ℝ) (hn : 0 < n) (hk : 0 < k) :
    k * (n / Real.sqrt k / n) ^ 2 = 1 := by
  have hsqrtpos : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk
  have hratio : n / Real.sqrt k / n = 1 / Real.sqrt k := by
    field_simp
  rw [hratio, div_pow, one_pow, Real.sq_sqrt hk.le]
  field_simp

/-- A cost bounded by `C * m^(2/3)` for every positive `m` is bounded at `m = n/√k` by `C *
n^(2/3) * k^(-1/3)` for positive `n` and `k`. See [KaplanEtAl2015]. -/
theorem theorem5_cost (n k C : ℝ) (hn : 0 < n) (hk : 0 < k)
    (cost : ℝ → ℝ)
    (hCost : ∀ m : ℝ, 0 < m → cost m ≤ C * m ^ (2 / 3 : ℝ)) :
    cost (n / Real.sqrt k) ≤ C * n ^ (2 / 3 : ℝ) * k ^ (-(1 / 3) : ℝ) := by
  have hsqrtpos : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk
  have hsubpos : 0 < n / Real.sqrt k := div_pos hn hsqrtpos
  calc
    cost (n / Real.sqrt k) ≤ C * (n / Real.sqrt k) ^ (2 / 3 : ℝ) := hCost _ hsubpos
    _ = C * (n ^ (2 / 3 : ℝ) * k ^ (-(1 / 3) : ℝ)) := by
      rw [subset_cost_eq n k hn hk]
    _ = C * n ^ (2 / 3 : ℝ) * k ^ (-(1 / 3) : ℝ) := by ring

/-- For real `k > 1`, the expression `1 - (1 - 1/k)^k` is at least one half. See
[KaplanEtAl2015]. -/
theorem theorem5_constant_probability (k : ℝ) (hk : 1 < k) :
    1 / 2 ≤ 1 - (1 - 1 / k) ^ k := by
  have hk0 : 0 < k := by linarith
  have hpos : 0 < 1 - 1 / k := by
    rw [sub_pos]
    exact (div_lt_one hk0).mpr hk
  have hlog : Real.log (1 - 1 / k) * k ≤ -1 := by
    have h := Real.log_le_sub_one_of_pos hpos
    have h2 : 1 - 1 / k - 1 = -(1 / k) := by ring
    rw [h2] at h
    have hm : Real.log (1 - 1 / k) * k ≤ (-(1 / k)) * k :=
      mul_le_mul_of_nonneg_right h hk0.le
    have hneg : (-(1 / k)) * k = -1 := by
      field_simp
    rwa [hneg] at hm
  have hpow : (1 - 1 / k) ^ k ≤ Real.exp (-1) := by
    rw [Real.rpow_def_of_pos hpos]
    exact Real.exp_le_exp.mpr hlog
  have hexp : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_eq_one_div]
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    exact one_div_le_one_div_of_le (by norm_num) h2
  linarith

/-- For positive `n` and `k`, there exists the positive subset scale `m = n/√k` satisfying the
stated transferred cost bound. See [KaplanEtAl2015]. -/
theorem theorem5_subset_size_cost (n k C : ℝ) (hn : 0 < n) (hk : 0 < k)
    (cost : ℝ → ℝ)
    (hCost : ∀ m : ℝ, 0 < m → cost m ≤ C * m ^ (2 / 3 : ℝ)) :
    ∃ m : ℝ, m = n / Real.sqrt k ∧ 0 < m ∧
      cost m ≤ C * n ^ (2 / 3 : ℝ) * k ^ (-(1 / 3) : ℝ) := by
  have hsqrtpos : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk
  exact ⟨n / Real.sqrt k, rfl, div_pos hn hsqrtpos,
    theorem5_cost n k C hn hk cost hCost⟩

end Qatlib.Papers.QCryptanal15.MainResults.PairSearch
