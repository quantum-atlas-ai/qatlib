/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabGaps09.MainResults.CubeMoments
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Several gap sums and retry expressions

The module defines a family of second-order gap sums on the Boolean cube and the fraction of
configurations for which every sum is positive. It computes means and covariances, proves the
one-sum half-cube bound, and establishes existence of retry counts making the success expression
at least one half, in the setting of [FarhiEtAl2011].

## Main statements

* `cubeMean_multiGap` and `cubeCov_multiGap`: the moments of the indexed gap sums.
* `successFraction_k1_ge_half`: eventual success fraction at least one half for one sum with
  positive total coefficient.
* `constant_retries_exists` and `polynomial_retries`: existence of positive retry counts for the
  stated success parameters.

## References

* [Farhi et al., 2011][FarhiEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Finset Filter
open scoped BigOperators
open Qatlib.Papers.AdiabGaps09.MainResults

namespace Qatlib.Papers.AdiabGaps09.MainResults.ManySolutions

/-- The gap sum `∑ i, cSq (z i) * d r i` for the coefficient vector indexed by `r`. -/
def multiGap {k n : ℕ} (d : Fin k → Fin n → ℝ) (z : Fin n → Bool) (r : Fin k) : ℝ :=
  ∑ i, cSq (z i) * d r i

/-- The condition that every gap sum indexed by `r : Fin k` is strictly positive at `z`. -/
def MultiSuccess {k n : ℕ} (d : Fin k → Fin n → ℝ) (z : Fin n → Bool) : Prop :=
  ∀ r : Fin k, 0 < multiGap d z r

/-- The number of Boolean configurations satisfying `MultiSuccess d`, divided by `2 ^ n`. -/
def successFraction {k n : ℕ} (d : Fin k → Fin n → ℝ) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun z : Fin n → Bool => MultiSuccess d z)).card : ℝ)
    / (2 : ℝ) ^ n

/-- The uniform mean of the gap sum indexed by `r` is `(5/4) * ∑ i, d r i`. See [FarhiEtAl2011]. -/
theorem cubeMean_multiGap {k n : ℕ} (d : Fin k → Fin n → ℝ) (r : Fin k) :
    cubeMean (fun z => multiGap d z r) = (5 / 4) * ∑ i, d r i :=
  cubeMean_second_order (d r)

/-- Each indexed gap sum equals its mean `(5/4) * ∑ i, d r i` plus the centered sum `Tsum (d r)
z`. -/
theorem multiGap_eq {k n : ℕ} (d : Fin k → Fin n → ℝ) (z : Fin n → Bool) (r : Fin k) :
    multiGap d z r = (5 / 4) * (∑ i, d r i) + Tsum (d r) z :=
  secondOrderGap_eq n (d r) z

/-- The uniform cube covariance of the gap sums indexed by `q` and `r` equals `∑ i, d q i * d r
i`. See [FarhiEtAl2011]. -/
theorem cubeCov_multiGap {k n : ℕ} (d : Fin k → Fin n → ℝ) (q r : Fin k) :
    cubeCov (fun z => multiGap d z q) (fun z => multiGap d z r)
      = ∑ i, d q i * d r i := by
  have hq : (fun z : Fin n → Bool => multiGap d z q)
      = fun z => (5 / 4) * (∑ i, d q i) + Tsum (d q) z := by
    funext z
    exact multiGap_eq d z q
  have hr : (fun z : Fin n → Bool => multiGap d z r)
      = fun z => (5 / 4) * (∑ i, d r i) + Tsum (d r) z := by
    funext z
    exact multiGap_eq d z r
  unfold cubeCov
  rw [hq, hr]
  have hprod : cubeMean (fun z : Fin n → Bool =>
      ((5 / 4) * (∑ i, d q i) + Tsum (d q) z)
        * ((5 / 4) * (∑ i, d r i) + Tsum (d r) z))
      = ((5 / 4) * (∑ i, d q i)) * ((5 / 4) * (∑ i, d r i))
        + ∑ i, d q i * d r i := by
    have hexp : (fun z : Fin n → Bool =>
        ((5 / 4) * (∑ i, d q i) + Tsum (d q) z)
          * ((5 / 4) * (∑ i, d r i) + Tsum (d r) z))
        = fun z => ((5 / 4) * (∑ i, d q i)) * ((5 / 4) * (∑ i, d r i))
            + ((5 / 4) * (∑ i, d q i)) * Tsum (d r) z
            + ((5 / 4) * (∑ i, d r i)) * Tsum (d q) z
            + Tsum (d q) z * Tsum (d r) z := by
      funext z
      ring
    rw [hexp]
    rw [cubeMean_add, cubeMean_add, cubeMean_add, cubeMean_const, cubeMean_smul,
      cubeMean_smul, cubeMean_Tsum, cubeMean_Tsum, cubeMean_Tsum_mul]
    ring
  have hmq : cubeMean (fun z : Fin n → Bool =>
      (5 / 4) * (∑ i, d q i) + Tsum (d q) z) = (5 / 4) * (∑ i, d q i) := by
    rw [cubeMean_add, cubeMean_const, cubeMean_Tsum, add_zero]
  have hmr : cubeMean (fun z : Fin n → Bool =>
      (5 / 4) * (∑ i, d r i) + Tsum (d r) z) = (5 / 4) * (∑ i, d r i) := by
    rw [cubeMean_add, cubeMean_const, cubeMean_Tsum, add_zero]
  rw [hprod, hmq, hmr]
  ring

/-- The fraction of configurations satisfying `MultiSuccess` is nonnegative. -/
theorem successFraction_nonneg {k n : ℕ} (d : Fin k → Fin n → ℝ) :
    0 ≤ successFraction (k := k) (n := n) d := by
  unfold successFraction
  positivity

/-- The fraction of configurations satisfying `MultiSuccess` is at most one. See
[FarhiEtAl2011]. -/
theorem successFraction_le_one {k n : ℕ} (d : Fin k → Fin n → ℝ) :
    successFraction (k := k) (n := n) d ≤ 1 := by
  classical
  unfold successFraction
  rw [div_le_one (two_pow_pos n)]
  have h := Finset.card_le_univ
    (Finset.univ.filter (fun z : Fin n → Bool => MultiSuccess d z))
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h
  exact_mod_cast h

/-- For a single coefficient vector, `MultiSuccess` is equivalent to strict positivity of
`secondOrderGap d z`. -/
theorem multiSuccess_k1_iff {n : ℕ} (d : Fin n → ℝ) (z : Fin n → Bool) :
    MultiSuccess (k := 1) (fun (_ : Fin 1) (i : Fin n) => d i) z
      ↔ 0 < secondOrderGap d z := by
  constructor
  · intro h
    have h0 := h 0
    simpa [multiGap] using! h0
  · intro h r
    fin_cases r
    simpa [multiGap] using! h

/-- If the sum of coefficients is eventually positive, the success fraction for the single
indexed gap sum is eventually at least one half. See [FarhiEtAl2011]. -/
theorem successFraction_k1_ge_half (d : (n : ℕ) → Fin n → ℝ)
    (h : ∀ᶠ n in Filter.atTop, 0 < ∑ i, d n i) :
    ∀ᶠ n in Filter.atTop,
      1 / 2 ≤ successFraction (k := 1) (n := n)
        (fun (_ : Fin 1) (i : Fin n) => d n i) := by
  classical
  filter_upwards [h] with n hn
  have hbase := card_ge_half_of_mean (d n)
  have hsub : (Finset.univ.filter (fun z : Fin n → Bool =>
        (5 / 4) * ∑ i, d n i ≤ secondOrderGap (d n) z))
      ⊆ (Finset.univ.filter (fun z : Fin n → Bool =>
        0 < secondOrderGap (d n) z)) := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    nlinarith [hn]
  have hcard : ((Finset.univ.filter (fun z : Fin n → Bool =>
        0 < secondOrderGap (d n) z)).card : ℝ) ≥ (2 : ℝ) ^ n / 2 := by
    refine le_trans hbase ?_
    exact_mod_cast Finset.card_le_card hsub
  have hfil : (Finset.univ.filter (fun z : Fin n → Bool =>
        MultiSuccess (k := 1) (fun (_ : Fin 1) (i : Fin n) => d n i) z))
      = Finset.univ.filter (fun z : Fin n → Bool => 0 < secondOrderGap (d n) z) := by
    apply Finset.filter_congr
    intro z _
    exact multiSuccess_k1_iff (d n) z
  unfold successFraction
  rw [hfil, le_div_iff₀ (two_pow_pos n)]
  calc (1 / 2) * (2 : ℝ) ^ n = (2 : ℝ) ^ n / 2 := by ring
    _ ≤ _ := hcard

/-- For `0 < p ≤ 1`, some positive natural number `K` satisfies `1 - (1 - p) ^ K ≥ 1/2`. See
[FarhiEtAl2011]. -/
theorem constant_retries_exists (p : ℝ) (hp0 : 0 < p) (_hp1 : p ≤ 1) :
    ∃ K : ℕ, 0 < K ∧ 1 / 2 ≤ 1 - (1 - p) ^ K := by
  have hb : 1 - p < 1 := by linarith
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 2) hb
  refine ⟨K, ?_, by linarith⟩
  rcases Nat.eq_zero_or_pos K with h | h
  · subst h
    simp only [pow_zero] at hK
    exact absurd hK (by norm_num)
  · exact h

/-- For natural `k ≥ 1` and `c > 0`, some positive natural number `K` satisfies `1 - (1 - 1 /
k^c) ^ K ≥ 1/2`. See [FarhiEtAl2011]. -/
theorem polynomial_retries (k c : ℕ) (hk : 1 ≤ k) (_hc : 0 < c) :
    ∃ K : ℕ, 0 < K ∧ 1 / 2 ≤ 1 - (1 - 1 / ((k : ℝ) ^ c)) ^ K := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hpow : (1 : ℝ) ≤ (k : ℝ) ^ c := one_le_pow₀ hk1
  have hp0 : 0 < 1 / ((k : ℝ) ^ c) := by positivity
  have hp1 : 1 / ((k : ℝ) ^ c) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact hpow
  exact constant_retries_exists (1 / ((k : ℝ) ^ c)) hp0 hp1

/-- The dot product of two coefficient vectors divided by the product of their Euclidean norms. -/
def correlation {n : ℕ} (dq dr : Fin n → ℝ) : ℝ :=
  (∑ i, dq i * dr i)
    / (Real.sqrt (∑ i, (dq i) ^ 2) * Real.sqrt (∑ i, (dr i) ^ 2))

/-- For a family consisting of one coefficient vector, `multiGap` equals `secondOrderGap`. -/
theorem multiGap_one {n : ℕ} (d : Fin n → ℝ) (z : Fin n → Bool) :
    multiGap (fun (_ : Fin 1) => d) z 0 = secondOrderGap d z := by
  unfold multiGap
  simp [secondOrderGap]

end Qatlib.Papers.AdiabGaps09.MainResults.ManySolutions
