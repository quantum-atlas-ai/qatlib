/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LearningGraph11.MainResults.AsymptoticAlgebra

set_option backward.isDefEq.respectTransparency false

/-!
# LearningGraph11 Theorem 9: the `G₁` complexity estimate

Fixed source: arXiv:1109.5135v1, Theorem 9 and its proof (p. 14).

For a graph `H` on `k ≥ 3` vertices with `m ≥ 1` edges there is a quantum query algorithm
deciding whether `H` is a subgraph of an `n`-vertex graph with
`O(n^{2−2/(k+1)−k/((k+1)(m+1))})` queries.

The proof (paper p. 14) shows that the learning graph `G₁` of Section 4.1 has complexity at
most `S⁰ + U⁰ + U⁰⁰⁰`, where, with `r = n^{1−1/(k+1)}` and `s = n^{−t}`,
`t = k/((k+1)(m+1))`,

* `S⁰ = s r²`,
* `U⁰ = s r √n (n/r)^{(k−1)/2}`,
* `U⁰⁰⁰ = r (n/r)^{k/2} s^{−(m−1)/2}`,

and that each of the three terms equals `n^{2−2/(k+1)−t}`. This file formalizes exactly this
real-valued cost computation: the three stage terms at the paper's parameter choice are
proved equal to the single power, so their sum is at most `3` times it. The reduction from
a learning graph to a quantum query algorithm (paper Theorem 1) and the `O(·)` constant are
outside the source model; the factor `3` makes the constant explicit.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.LearningGraph11.MainResults

open Finset
open scoped BigOperators

/-- Theorem 9's balanced exponent `2 − 2/(k+1) − k/((k+1)(m+1))` (p. 14). -/
def thm9Exponent (k m : ℕ) : ℝ :=
  2 - 2 / ((k : ℝ) + 1) - (k : ℝ) / (((k : ℝ) + 1) * ((m : ℝ) + 1))

/-- Theorem 9's parameter `r = n^{1-1/(k+1)}` (p. 14). -/
def thm9r (k : ℕ) (n : ℝ) : ℝ := n ^ (1 - 1 / ((k : ℝ) + 1))

/-- Theorem 9's parameter `s = n^{-k/((k+1)(m+1))}` (p. 14). -/
def thm9s (k m : ℕ) (n : ℝ) : ℝ :=
  n ^ (-((k : ℝ) / (((k : ℝ) + 1) * ((m : ℝ) + 1))))

/-- Stage 0 of `G₁`: `S⁰ = s r² = n^{2-2/(k+1)-t}`. -/
theorem thm9_stage0 (k m : ℕ) (hk : 3 ≤ k) (hm : 1 ≤ m) (n : ℝ) (hn : 1 ≤ n) :
    thm9s k m n * (thm9r k n) ^ (2 : ℝ) = n ^ (thm9Exponent k m) := by
  by_cases hn1 : n = 1
  · subst hn1
    simp [thm9s, thm9r, thm9Exponent]
  · have h1 : 1 < n := lt_of_le_of_ne hn (Ne.symm hn1)
    have hpos : 0 < n := lt_trans zero_lt_one h1
    have hexp : -((k : ℝ) / (((k : ℝ) + 1) * ((m : ℝ) + 1)))
        + (1 - 1 / ((k : ℝ) + 1)) * 2 = thm9Exponent k m := by
      rw [thm9Exponent]
      have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
      have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
    simp only [thm9s, thm9r]
    rw [← Real.rpow_mul hpos.le, ← Real.rpow_add hpos, hexp]

/-- Stage `k` of `G₁`: `U⁰ = s r √n (n/r)^{(k-1)/2} = n^{2-2/(k+1)-t}`. -/
theorem thm9_stage_u (k m : ℕ) (hk : 3 ≤ k) (hm : 1 ≤ m) (n : ℝ) (hn : 1 ≤ n) :
    thm9s k m n * thm9r k n * Real.sqrt n
        * (n / thm9r k n) ^ (((k : ℝ) - 1) / 2) = n ^ (thm9Exponent k m) := by
  by_cases hn1 : n = 1
  · subst hn1
    simp [thm9s, thm9r, thm9Exponent]
  · have h1 : 1 < n := lt_of_le_of_ne hn (Ne.symm hn1)
    have hpos : 0 < n := lt_trans zero_lt_one h1
    simp only [thm9s, thm9r]
    set a : ℝ := 1 - 1 / ((k : ℝ) + 1) with ha
    set T : ℝ := (k : ℝ) / (((k : ℝ) + 1) * ((m : ℝ) + 1)) with hT
    set b : ℝ := ((k : ℝ) - 1) / 2 with hb
    have hdiv : n ^ b / n ^ (a * b) = n ^ (b - a * b) := by
      rw [Real.rpow_sub hpos b (a * b)]
    have hexp : -T + a + 1 / 2 + (b - a * b) = thm9Exponent k m := by
      rw [thm9Exponent, ha, hT, hb]
      have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
      have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
    rw [Real.sqrt_eq_rpow, Real.div_rpow hpos.le (Real.rpow_nonneg hpos.le a) b,
      ← Real.rpow_mul hpos.le, hdiv, rpow_mul_four hpos, hexp]

/-- Stage `k + m + 1` of `G₁`: `U⁰⁰⁰ = r (n/r)^{k/2} s^{-(m-1)/2} = n^{2-2/(k+1)-t}`. -/
theorem thm9_stage_um (k m : ℕ) (hk : 3 ≤ k) (hm : 1 ≤ m) (n : ℝ) (hn : 1 ≤ n) :
    thm9r k n * (n / thm9r k n) ^ ((k : ℝ) / 2)
        * (thm9s k m n) ^ (-(((m : ℝ) - 1) / 2)) = n ^ (thm9Exponent k m) := by
  by_cases hn1 : n = 1
  · subst hn1
    simp [thm9s, thm9r, thm9Exponent]
  · have h1 : 1 < n := lt_of_le_of_ne hn (Ne.symm hn1)
    have hpos : 0 < n := lt_trans zero_lt_one h1
    simp only [thm9s, thm9r]
    set a : ℝ := 1 - 1 / ((k : ℝ) + 1) with ha
    set T : ℝ := (k : ℝ) / (((k : ℝ) + 1) * ((m : ℝ) + 1)) with hT
    set b : ℝ := (k : ℝ) / 2 with hb
    set c : ℝ := -(((m : ℝ) - 1) / 2) with hc
    have hnr : n ^ (1 - a) = n / n ^ a := by
      rw [Real.rpow_sub hpos (1 : ℝ) a, Real.rpow_one]
    have hexp : a + (1 - a) * b + (-T) * c = thm9Exponent k m := by
      rw [thm9Exponent, ha, hT, hb, hc]
      have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
      have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
    rw [← hnr, ← Real.rpow_mul hpos.le (1 - a) b, ← Real.rpow_mul hpos.le (-T) c,
      rpow_mul_three hpos, hexp]

/-- Fixed source arXiv:1109.5135v1, Theorem 9 (p. 14), learning-graph cost form: with the
paper's parameter choice, the total `S⁰ + U⁰ + U⁰⁰⁰` of the `G₁` stages is at most
`3 n^{2−2/(k+1)−k/((k+1)(m+1))}`. -/
theorem source_theorem_9 (k m : ℕ) (hk : 3 ≤ k) (hm : 1 ≤ m) (n : ℝ) (hn : 1 ≤ n) :
    thm9s k m n * (thm9r k n) ^ (2 : ℝ)
      + thm9s k m n * thm9r k n * Real.sqrt n
          * (n / thm9r k n) ^ (((k : ℝ) - 1) / 2)
      + thm9r k n * (n / thm9r k n) ^ ((k : ℝ) / 2)
          * (thm9s k m n) ^ (-(((m : ℝ) - 1) / 2))
    ≤ 3 * n ^ (thm9Exponent k m) := by
  rw [thm9_stage0 k m hk hm n hn, thm9_stage_u k m hk hm n hn,
    thm9_stage_um k m hk hm n hn]
  nlinarith

end Qatlib.Papers.LearningGraph11.MainResults
