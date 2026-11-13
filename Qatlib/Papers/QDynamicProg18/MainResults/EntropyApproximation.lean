/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QDynamicProg18.MainResults.Model

set_option backward.isDefEq.respectTransparency false

/-!
# Binary Entropy Upper Bound on Partial Sums of Binomial Coefficients

This module proves Theorem 3: for every `1 ≤ k` with `2 * k ≤ n`, the partial binomial
sum `∑_{i=0}^k C(n, i)` is bounded above by `2^{H(k / n) n}`, where `H` denotes the
binary Shannon entropy in bits (`binEntropyBits`).

## Main statements

* `sum_choose_le_two_pow`: `∑_{i=0}^k C(n, i) ≤ 2^n` in `ℕ` for `k ≤ n`.
* `sum_choose_le_two_pow_real`: real-valued form of `sum_choose_le_two_pow`.
* `entropy_approximation`: Theorem 3 bound `∑_{i=0}^k C(n, i) ≤ 2^{binEntropyBits (k / n) * n}`
  for `1 ≤ k` and `2 * k ≤ n`.

## References

* [Ambainis et al., 2019][AmbainisEtAl2019QDP], Theorem 3, Section 2, p. 4.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QDynamicProg18.MainResults

open Classical

/-- Partial row sum of Pascal's triangle bounded by the full row sum `2^n`. -/
theorem sum_choose_le_two_pow {n k : ℕ} (hk : k ≤ n) :
    (∑ i ∈ Finset.range (k + 1), n.choose i) ≤ 2 ^ n := by
  rw [← Nat.sum_range_choose n]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono (Nat.succ_le_succ hk)
  · intro i _ _
    exact Nat.zero_le _

/-- Real-cast form of `sum_choose_le_two_pow`. -/
theorem sum_choose_le_two_pow_real {n k : ℕ} (hk : k ≤ n) :
    (∑ i ∈ Finset.range (k + 1), (n.choose i : ℝ)) ≤ (2 : ℝ) ^ n := by
  have h := sum_choose_le_two_pow hk
  exact_mod_cast h

/-- **Theorem 3 (Entropy approximation)**: for all `n, k : ℕ` with `1 ≤ k` and `2 * k ≤ n`,
`∑_{i=0}^k C(n, i) ≤ 2^{H(k / n) · n}`, where `H = binEntropyBits` is the binary entropy in bits. -/
theorem entropy_approximation (n k : ℕ) (hk1 : 1 ≤ k) (hk2 : 2 * k ≤ n) :
    (∑ i ∈ Finset.range (k + 1), (n.choose i : ℝ)) ≤
      (2 : ℝ) ^ (binEntropyBits ((k : ℝ) / n) * n) := by
  have hkn : k ≤ n := by omega
  have hn : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hk : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hsub : ((n - k : ℕ) : ℝ) = (n : ℝ) - k := Nat.cast_sub hkn
  let p : ℝ := (k : ℝ) / n
  have hp : 0 < p := div_pos hk hn
  have hhalf : p ≤ 1 / 2 := by
    apply (div_le_iff₀ hn).2
    have h2 : 2 * (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk2
    linarith
  have h1p : 0 < 1 - p := by linarith
  have hp1p : p ≤ 1 - p := by linarith
  have hpn : p * (n : ℝ) = k := div_mul_cancel₀ _ hn.ne'
  have h1pn : (1 - p) * (n : ℝ) = ((n - k : ℕ) : ℝ) := by
    rw [hsub]
    nlinarith [hpn]
  let W : ℝ := p ^ k * (1 - p) ^ (n - k)
  have hW : 0 < W := mul_pos (pow_pos hp _) (pow_pos h1p _)
  have hlog : Real.log 2 * (binEntropyBits p * (n : ℝ)) = -Real.log W := by
    rw [binEntropyBits_eq, Real.log_mul (pow_pos hp _).ne' (pow_pos h1p _).ne',
      Real.log_pow, Real.log_pow, ← hpn, ← h1pn]
    field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  have hpow : (2 : ℝ) ^ (binEntropyBits p * (n : ℝ)) = W⁻¹ := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), hlog,
      Real.exp_neg, Real.exp_log hW]
  change (∑ i ∈ Finset.range (k + 1), (n.choose i : ℝ)) ≤
    (2 : ℝ) ^ (binEntropyBits p * (n : ℝ))
  rw [hpow, ← one_div]
  apply (le_div_iff₀ hW).2
  rw [Finset.sum_mul]
  calc
    (∑ i ∈ Finset.range (k + 1), (n.choose i : ℝ) * W) ≤
        ∑ i ∈ Finset.range (k + 1), p ^ i * (1 - p) ^ (n - i) * (n.choose i : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      have hik : i ≤ k := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
      have hweight : W ≤ p ^ i * (1 - p) ^ (n - i) := by
        calc
          W = p ^ i * p ^ (k - i) * (1 - p) ^ (n - k) := by
            rw [← pow_add, Nat.add_sub_of_le hik]
          _ ≤ p ^ i * (1 - p) ^ (k - i) * (1 - p) ^ (n - k) := by
            gcongr
          _ = p ^ i * (1 - p) ^ (n - i) := by
            rw [mul_assoc, ← pow_add, show k - i + (n - k) = n - i by omega]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hweight (Nat.cast_nonneg (n.choose i))
    _ ≤ ∑ i ∈ Finset.range (n + 1), p ^ i * (1 - p) ^ (n - i) * (n.choose i : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_succ hkn))
      intro i _ _
      positivity
    _ = 1 := by rw [← add_pow, show p + (1 - p) = 1 by ring, one_pow]

end Qatlib.Papers.QDynamicProg18.MainResults
