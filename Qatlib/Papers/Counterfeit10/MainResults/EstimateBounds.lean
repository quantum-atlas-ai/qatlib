/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

/-!
# Finite geometric estimates behind Lemmas 4 and 6 (Counterfeit10, §3)

Formal companion to Iwama–Nishimura–Raymond–Teruyama,
*Quantum Counterfeit Coin Problems*, arXiv:1009.0416v1, Section 3.2.

The analytical content of Lemma 4 and Lemma 6 is bookkeeping of *finite geometric sums* coming
from successive ratios of binomial coefficients.

* Lemma 4 splits `γ` into a "large `m`" tail `T_{>k/2c}` and a "small `m`" part
  `T_{≤k/2c}`; for the latter it uses that the ratio `r(m) = t(m+1)/t(m)` grows with `m`, so that
  the largest term is the last one and the sum is dominated by a geometric series of ratio `≤ 1/4`.
  `geom_tail_of_growth` formalises exactly this: if `4 * t m ≤ t (m+1)` then the partial sum up to
  `K` is at most `(4/3) * t K`.
* Lemma 6 bounds the tilted probability by the geometric tail `Σ_{m≥1} t'(m)` with successive
  ratio `r'(0)`. `geom_tail_le` formalises the resulting geometric-series bound, and `rprime0_le`
  proves the paper's explicit estimate `r'(0) = O(k/c)` (with the constants made explicit in the
  regime `c ≥ 5`, `k ≤ N/2` where the inequality is literally true).

These are the estimates; the probabilistic interpretation of `t` as a distribution is not needed
for the inequalities, so it is stated abstractly.
-/

namespace Qatlib.Papers.Counterfeit10.MainResults

/-- Partial geometric sums of ratio `r ∈ [0,1)` are bounded by the infinite geometric series
`1 / (1 - r)`. -/
lemma geom_range_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (M : ℕ) :
    ∑ m ∈ Finset.range M, r ^ m ≤ 1 / (1 - r) := by
  have hpos : (0 : ℝ) < 1 - r := by linarith
  have hkey : (∑ m ∈ Finset.range M, r ^ m) * (1 - r) = 1 - r ^ M := by
    exact geom_sum_mul_neg r M
  rw [le_div_iff₀ hpos, hkey]
  have : (0 : ℝ) ≤ r ^ M := pow_nonneg hr0 M
  linarith

/-- Lemma 4, small-`m` part: if the terms grow by a factor of at least `4` at each step, then the
partial sum up to `K` is dominated by `(4/3)` times the largest (last) term.  This is the paper's
`T_{≤k/2c} ≤ (4/3) t(k/2c)`. -/
theorem geom_tail_of_growth {t : ℕ → ℝ} (ht : ∀ m, 0 ≤ t m)
    (hstep : ∀ m, 4 * t m ≤ t (m + 1)) :
    ∀ K, ∑ m ∈ Finset.range (K + 1), t m ≤ (4 / 3) * t K := by
  intro K
  induction K with
  | zero =>
      rw [Finset.sum_range_succ, Finset.sum_range_zero]
      nlinarith [ht 0]
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have ih' : (∑ m ∈ Finset.range (Nat.succ n), t m) ≤ (4 / 3) * t n := ih
      have hs : 4 * t n ≤ t (Nat.succ n) := hstep n
      linarith [ih', hs]

/-- Lemma 6, geometric core: if the probability masses `t m` have successive ratio at most `r`,
then the tail `Σ_{m<k} t (m+1)` is at most `r/(1-r)` times the initial mass `t 0`. -/
theorem geom_tail_le {t : ℕ → ℝ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ht : ∀ m, 0 ≤ t m) (hstep : ∀ m, t (m + 1) ≤ r * t m) (k : ℕ) :
    ∑ m ∈ Finset.range k, t (m + 1) ≤ (r / (1 - r)) * t 0 := by
  have hpow : ∀ m, t m ≤ r ^ m * t 0 := by
    intro m
    induction m with
    | zero => simp
    | succ n ih =>
        calc t (n + 1) ≤ r * t n := hstep n
          _ ≤ r * (r ^ n * t 0) := mul_le_mul_of_nonneg_left ih hr0
          _ = r ^ (n + 1) * t 0 := by rw [pow_succ]; ring
  have hsum : (∑ m ∈ Finset.range k, r ^ (m + 1)) =
      r * (∑ m ∈ Finset.range k, r ^ m) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [pow_succ]; ring
  calc ∑ m ∈ Finset.range k, t (m + 1)
      ≤ ∑ m ∈ Finset.range k, r ^ (m + 1) * t 0 :=
          Finset.sum_le_sum (fun m _ => hpow (m + 1))
    _ = (∑ m ∈ Finset.range k, r ^ (m + 1)) * t 0 := by rw [Finset.sum_mul]
    _ = (r * (∑ m ∈ Finset.range k, r ^ m)) * t 0 := by rw [hsum]
    _ ≤ (r * (1 / (1 - r))) * t 0 := by
          apply mul_le_mul_of_nonneg_right _ (ht 0)
          exact mul_le_mul_of_nonneg_left (geom_range_le hr0 hr1 k) hr0
    _ = (r / (1 - r)) * t 0 := by ring

/-- The unit-mass form of Lemma 6: with `t 0 ≤ 1` the tilted probability is at most
`r/(1-r)`. -/
theorem geom_tail_le_unit {t : ℕ → ℝ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ht : ∀ m, 0 ≤ t m) (ht0 : t 0 ≤ 1)
    (hstep : ∀ m, t (m + 1) ≤ r * t m) (k : ℕ) :
    ∑ m ∈ Finset.range k, t (m + 1) ≤ r / (1 - r) := by
  have h := geom_tail_le hr0 hr1 ht hstep k
  have hnonneg : 0 ≤ r / (1 - r) := div_nonneg hr0 (by linarith)
  calc ∑ m ∈ Finset.range k, t (m + 1) ≤ (r / (1 - r)) * t 0 := h
    _ ≤ (r / (1 - r)) * 1 := mul_le_mul_of_nonneg_left ht0 hnonneg
    _ = r / (1 - r) := by ring

/-- Lemma 6: when the successive ratio `r` of the hypergeometric masses is at most `1/2`, the
tilted probability `Σ_{m<k} t(m+1)` is at most `2r`.  This is the paper's
`Σ t'(m) ≤ r'(0)/(1-r'(0)) = O(r'(0))`. -/
theorem lemma6_tilted_prob_bound {t : ℕ → ℝ} {r : ℝ}
    (hr0 : 0 ≤ r) (hrhalf : r ≤ 1 / 2)
    (ht : ∀ m, 0 ≤ t m) (ht0 : t 0 ≤ 1)
    (hstep : ∀ m, t (m + 1) ≤ r * t m) (k : ℕ) :
    ∑ m ∈ Finset.range k, t (m + 1) ≤ 2 * r := by
  have h := geom_tail_le_unit hr0 (by linarith) ht ht0 hstep k
  have hden : (0 : ℝ) < 1 - r := by linarith
  have h2 : r / (1 - r) ≤ 2 * r := by
    rw [div_le_iff₀ hden]
    nlinarith [hr0, hrhalf]
  linarith

/-- Lemma 6 with the explicit `k/c` rate: if the successive ratio is at most `20 · k/c` and at
most `1/2`, the tilted probability is at most `40 · k/c`. -/
theorem lemma6_prob_le_forty_k_over_c {t : ℕ → ℝ} {k c r : ℝ}
    (hr0 : 0 ≤ r) (hrhalf : r ≤ 1 / 2) (hrr : r ≤ 20 * (k / c))
    (ht : ∀ m, 0 ≤ t m) (ht0 : t 0 ≤ 1)
    (hstep : ∀ m, t (m + 1) ≤ r * t m) (n : ℕ) :
    ∑ m ∈ Finset.range n, t (m + 1) ≤ 40 * (k / c) := by
  have h := lemma6_tilted_prob_bound hr0 hrhalf ht ht0 hstep n
  linarith [h, hrr]

/-- Lemma 6, explicit constant: in the regime `N > 0`, `k ≤ N/2`, `c ≥ 5`, the first successive
ratio `r'(0) = (k · 2N/c) / (N - k - 2N/c + 1)` of the hypergeometric masses is at most
`20 · k/c`. -/
theorem rprime0_le {k N c : ℝ} (hN : 0 < N) (hk : 0 ≤ k) (hc : 5 ≤ c) (hkc : k ≤ N / 2) :
    (k * (2 * N / c)) / (N - k - 2 * N / c + 1) ≤ 20 * (k / c) := by
  have hc0 : (0 : ℝ) < c := by linarith
  have h2Nc : 2 * N / c ≤ 2 * N / 5 := by
    rw [div_le_div_iff₀ hc0 (by norm_num : (0 : ℝ) < 5)]
    nlinarith [hN, hc]
  have hden : N / 10 ≤ N - k - 2 * N / c + 1 := by nlinarith [h2Nc, hkc, hN]
  have hdenpos : (0 : ℝ) < N - k - 2 * N / c + 1 := by linarith
  rw [div_le_iff₀ hdenpos]
  have hkdiv : (0 : ℝ) ≤ k / c := div_nonneg hk (le_of_lt hc0)
  have hk20 : (0 : ℝ) ≤ 20 * (k / c) := mul_nonneg (by norm_num) hkdiv
  have hR : 20 * (k / c) * (N / 10) ≤ 20 * (k / c) * (N - k - 2 * N / c + 1) :=
    mul_le_mul_of_nonneg_left hden hk20
  have hL : 20 * (k / c) * (N / 10) = k * (2 * N / c) := by
    field_simp [ne_of_gt hc0]; ring
  rw [← hL]; exact hR

end Qatlib.Papers.Counterfeit10.MainResults
