/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LearningGraph11.MainResults.AsymptoticAlgebra

set_option backward.isDefEq.respectTransparency false

/-!
# LearningGraph11 Theorem 10: the minimum-degree complexity estimate

Fixed source: arXiv:1109.5135v1 (LaTeX `chicago_submitted.tex`, lines 1129-1143),
Theorem 10 and its proof (pp. 15-16).

For a graph `H` on `k ≥ 3` vertices with `m` edges and minimum degree `d ≥ 1` there is a
quantum query algorithm deciding whether `H` is a subgraph of an `n`-vertex graph with
`O(n^{2−2/k−(2k−d−3)/(k(d+1)(m−d+2))})` queries.

The proof (paper pp. 15-16) bounds the learning graph `G₂` by `S⁰ + U⁰ + C⁰`, where, with
`r = n^{1−1/k}`, `s = n^{−t}`, `t = (2k−d−3)/(k(d+1)(m′+2))` and `m′ = m − d`,

* `S⁰ = s r²`,
* `U⁰ = s r √n (n/r)^{(k−2)/2}`,
* `C⁰ = s^{−m′/2} (n/r)^{(k−1)/2} √n r^{d/(d+1)}`,

and each of the three terms equals `n^{2−2/k−t}`. This file formalizes this real-valued
cost computation with `m′` written as `m − d`; the reduction to a quantum query algorithm
(paper Theorem 1) and the `O(·)` constant are outside the source model, and the explicit
factor `3` records the additive constant.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.LearningGraph11.MainResults

open Finset
open scoped BigOperators

/-- Theorem 10's balanced exponent `2 − 2/k − (2k−d−3)/(k(d+1)(m−d+2))` (p. 16). -/
def thm10Exponent (k d m : ℕ) : ℝ :=
  2 - 2 / (k : ℝ)
    - (2 * (k : ℝ) - (d : ℝ) - 3) / ((k : ℝ) * ((d : ℝ) + 1) * ((m : ℝ) - (d : ℝ) + 2))

/-- Theorem 10's balance parameter `t = (2k−d−3)/(k(d+1)(m−d+2))` (p. 16). -/
def thm10t (k d m : ℕ) : ℝ :=
  (2 * (k : ℝ) - (d : ℝ) - 3) / ((k : ℝ) * ((d : ℝ) + 1) * ((m : ℝ) - (d : ℝ) + 2))

/-- Theorem 10's parameter `r = n^{1-1/k}` (p. 16). -/
def thm10r (k : ℕ) (n : ℝ) : ℝ := n ^ (1 - 1 / (k : ℝ))

/-- Theorem 10's parameter `s = n^{-t}` (p. 16). -/
def thm10s (k d m : ℕ) (n : ℝ) : ℝ := n ^ (-(thm10t k d m))

/-- Stage 0 of `G₂`: `S⁰ = s r² = n^{2-2/k-t}`. -/
theorem thm10_stage0 (k d m : ℕ) (hk : 3 ≤ k) (hd : 1 ≤ d) (hdm : d ≤ m)
    (n : ℝ) (hn : 1 ≤ n) :
    thm10s k d m n * (thm10r k n) ^ (2 : ℝ) = n ^ (thm10Exponent k d m) := by
  by_cases hn1 : n = 1
  · subst hn1
    simp [thm10s, thm10r, thm10t, thm10Exponent]
  · have h1 : 1 < n := lt_of_le_of_ne hn (Ne.symm hn1)
    have hpos : 0 < n := lt_trans zero_lt_one h1
    simp only [thm10s, thm10r]
    set a : ℝ := 1 - 1 / (k : ℝ) with ha
    set T : ℝ := thm10t k d m with hT
    have hexp : -T + a * 2 = thm10Exponent k d m := by
      rw [thm10Exponent, ha, hT, thm10t]
      have hk0 : (k : ℝ) ≠ 0 := by
        have h : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
        exact ne_of_gt h
      have hd1 : ((d : ℝ) + 1) ≠ 0 := by positivity
      have hmd : (0 : ℝ) ≤ (m : ℝ) - (d : ℝ) := by
        have h : ((m - d : ℕ) : ℝ) = (m : ℝ) - (d : ℝ) := Nat.cast_sub hdm
        rw [← h]
        exact Nat.cast_nonneg _
      have hm2 : (m : ℝ) - (d : ℝ) + 2 ≠ 0 := by
        intro h0
        linarith
      field_simp
      ring
    rw [← Real.rpow_mul hpos.le, ← Real.rpow_add hpos, hexp]

/-- Stage `k − 1` of `G₂`: `U⁰ = s r √n (n/r)^{(k-2)/2} = n^{2-2/k-t}`. -/
theorem thm10_stage_u (k d m : ℕ) (hk : 3 ≤ k) (hd : 1 ≤ d) (hdm : d ≤ m)
    (n : ℝ) (hn : 1 ≤ n) :
    thm10s k d m n * thm10r k n * Real.sqrt n
        * (n / thm10r k n) ^ (((k : ℝ) - 2) / 2) = n ^ (thm10Exponent k d m) := by
  by_cases hn1 : n = 1
  · subst hn1
    simp [thm10s, thm10r, thm10t, thm10Exponent]
  · have h1 : 1 < n := lt_of_le_of_ne hn (Ne.symm hn1)
    have hpos : 0 < n := lt_trans zero_lt_one h1
    simp only [thm10s, thm10r]
    set a : ℝ := 1 - 1 / (k : ℝ) with ha
    set T : ℝ := thm10t k d m with hT
    set b : ℝ := ((k : ℝ) - 2) / 2 with hb
    have hdiv : n ^ b / n ^ (a * b) = n ^ (b - a * b) := by
      rw [Real.rpow_sub hpos b (a * b)]
    have hexp : -T + a + 1 / 2 + (b - a * b) = thm10Exponent k d m := by
      rw [thm10Exponent, ha, hT, hb, thm10t]
      have hk0 : (k : ℝ) ≠ 0 := by
        have h : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
        exact ne_of_gt h
      have hd1 : ((d : ℝ) + 1) ≠ 0 := by positivity
      have hmd : (0 : ℝ) ≤ (m : ℝ) - (d : ℝ) := by
        have h : ((m - d : ℕ) : ℝ) = (m : ℝ) - (d : ℝ) := Nat.cast_sub hdm
        rw [← h]
        exact Nat.cast_nonneg _
      have hm2 : (m : ℝ) - (d : ℝ) + 2 ≠ 0 := by
        intro h0
        linarith
      field_simp
      ring
    rw [Real.sqrt_eq_rpow, Real.div_rpow hpos.le (Real.rpow_nonneg hpos.le a) b,
      ← Real.rpow_mul hpos.le, hdiv, rpow_mul_four hpos, hexp]

/-- Final stage `k + m' + 1` of `G₂`:
`C⁰ = s^{-m'/2} (n/r)^{(k-1)/2} √n r^{d/(d+1)} = n^{2-2/k-t}`, `m' = m - d`. -/
theorem thm10_stage_c (k d m : ℕ) (hk : 3 ≤ k) (hd : 1 ≤ d) (hdm : d ≤ m)
    (n : ℝ) (hn : 1 ≤ n) :
    (thm10s k d m n) ^ (-(((m : ℝ) - (d : ℝ)) / 2))
        * (n / thm10r k n) ^ (((k : ℝ) - 1) / 2)
        * Real.sqrt n * (thm10r k n) ^ ((d : ℝ) / ((d : ℝ) + 1))
      = n ^ (thm10Exponent k d m) := by
  by_cases hn1 : n = 1
  · subst hn1
    simp [thm10s, thm10r, thm10t, thm10Exponent]
  · have h1 : 1 < n := lt_of_le_of_ne hn (Ne.symm hn1)
    have hpos : 0 < n := lt_trans zero_lt_one h1
    simp only [thm10s, thm10r]
    set a : ℝ := 1 - 1 / (k : ℝ) with ha
    set T : ℝ := thm10t k d m with hT
    set b : ℝ := ((k : ℝ) - 1) / 2 with hb
    set c : ℝ := (d : ℝ) / ((d : ℝ) + 1) with hc
    set mp : ℝ := (m : ℝ) - (d : ℝ) with hmp
    have hnr : n ^ (1 - a) = n / n ^ a := by
      rw [Real.rpow_sub hpos (1 : ℝ) a, Real.rpow_one]
    have hexp : (-T) * (-(mp / 2)) + (1 - a) * b + 1 / 2 + a * c
        = thm10Exponent k d m := by
      rw [thm10Exponent, ha, hT, hb, hc, hmp, thm10t]
      have hk0 : (k : ℝ) ≠ 0 := by
        have h : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
        exact ne_of_gt h
      have hd1 : ((d : ℝ) + 1) ≠ 0 := by positivity
      have hmd : (0 : ℝ) ≤ (m : ℝ) - (d : ℝ) := by
        have h : ((m - d : ℕ) : ℝ) = (m : ℝ) - (d : ℝ) := Nat.cast_sub hdm
        rw [← h]
        exact Nat.cast_nonneg _
      have hm2 : (m : ℝ) - (d : ℝ) + 2 ≠ 0 := by
        intro h0
        linarith
      field_simp
      ring
    rw [← hnr, Real.sqrt_eq_rpow, ← Real.rpow_mul hpos.le (-T) (-(mp / 2)),
      ← Real.rpow_mul hpos.le (1 - a) b, ← Real.rpow_mul hpos.le a c,
      rpow_mul_four hpos, hexp]

/-- Fixed source arXiv:1109.5135v1, Theorem 10 (p. 16), learning-graph cost form: with the
paper's parameter choice, the total `S⁰ + U⁰ + C⁰` of the `G₂` stages is at most
`3 n^{2−2/k−(2k−d−3)/(k(d+1)(m−d+2))}`. -/
theorem source_theorem_10 (k d m : ℕ) (hk : 3 ≤ k) (hd : 1 ≤ d) (hdm : d ≤ m)
    (n : ℝ) (hn : 1 ≤ n) :
    thm10s k d m n * (thm10r k n) ^ (2 : ℝ)
      + thm10s k d m n * thm10r k n * Real.sqrt n
          * (n / thm10r k n) ^ (((k : ℝ) - 2) / 2)
      + (thm10s k d m n) ^ (-(((m : ℝ) - (d : ℝ)) / 2))
          * (n / thm10r k n) ^ (((k : ℝ) - 1) / 2)
          * Real.sqrt n * (thm10r k n) ^ ((d : ℝ) / ((d : ℝ) + 1))
    ≤ 3 * n ^ (thm10Exponent k d m) := by
  rw [thm10_stage0 k d m hk hd hdm n hn, thm10_stage_u k d m hk hd hdm n hn,
    thm10_stage_c k d m hk hd hdm n hn]
  nlinarith

end Qatlib.Papers.LearningGraph11.MainResults
