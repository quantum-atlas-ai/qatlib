/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma A.2: the state-combination routine succeeds with constant probability

Paper: Childs, Jao, Soukharev, *Constructing elliptic curve isogenies in quantum
subexponential time*, arXiv:1012.4019v3, Lemma A.2 and its proof (Appendix A).

Algorithm 4 combines `k` states `|ψ_{x_1}⟩, …, |ψ_{x_k}⟩` with labels in
`{0, …, B-1}` into one state with a label in `{0, …, B'-1}`.  Lemma A.2 states
that it runs in time `2^k poly(log N)` and succeeds with probability `Ω(1)`
provided

`4k ≤ B/B' ≤ 2^k/k`.

The proof (Appendix A) bounds the three abort probabilities:

* Step 2 aborts when some `x_i ≥ 2B'⌊B/2B'⌋`; the union bound gives
  `k · 2B'/B ≤ 1/2` using `B/B' ≥ 4k`;
* Step 8 aborts when `ν = 1`; at most `kB/B'` bad values of `q`, each with
  probability `1/2^k`, so the failure is at most `kB/(B' 2^{k+1}) ≤ 1/2`
  using `B/B' ≤ 2^k/k`;
* the projection of Steps 12–16 aborts with constant probability.

This module formalizes the two ratio bounds used in the proof and the
composition step: if the successive stages survive with probability at least
`1/2` each, the overall success probability is at least `1/16`, a positive
constant (`Ω(1)`).  The distribution of `|r* - r⋆|` and the exact per-stage
constants are taken from the source's analysis; see the PR notes.
-/

set_option autoImplicit false

namespace Qatlib.Papers.EllipticIsog10.MainResults

/-- **Lemma A.2, Step 2 abort bound.**  If `4k ≤ B/B'` (with `k, B' > 0`), then
the union bound for the Step 2 abort probability, `k · (2B'/B)`, is at most
`1/2`. -/
theorem lemmaA2_step2_abort (k B B' : ℕ) (hk : 0 < k) (hB' : 0 < B')
    (hratio : 4 * (k : ℝ) ≤ (B : ℝ) / (B' : ℝ)) :
    (k : ℝ) * (2 * (B' : ℝ) / (B : ℝ)) ≤ 1 / 2 := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hB'pos : (0 : ℝ) < (B' : ℝ) := by exact_mod_cast hB'
  -- `4k ≤ B/B'` gives `4kB' ≤ B`, hence `B > 0`.
  have hcleared : 4 * (k : ℝ) * (B' : ℝ) ≤ (B : ℝ) := by
    have := hratio
    rw [le_div_iff₀ hB'pos] at this
    linarith
  have hBpos : (0 : ℝ) < (B : ℝ) := by
    have : 0 < 4 * (k : ℝ) * (B' : ℝ) := by positivity
    linarith
  have hgoal : (k : ℝ) * (2 * (B' : ℝ) / (B : ℝ)) = 2 * (k : ℝ) * (B' : ℝ) / (B : ℝ) := by
    ring
  rw [hgoal, div_le_iff₀ hBpos]
  nlinarith [hcleared]

/-- **Lemma A.2, Step 8 abort bound.**  If `B/B' ≤ 2^k/k` (with `k, B' > 0`),
then the probability `kB/(B' 2^{k+1})` of hitting a bad outcome `ν = 1` is at
most `1/2`. -/
theorem lemmaA2_nu_abort (k B B' : ℕ) (hk : 0 < k) (hB' : 0 < B')
    (hratio : (B : ℝ) / (B' : ℝ) ≤ (2 : ℝ) ^ k / (k : ℝ)) :
    (k : ℝ) * (B : ℝ) / ((B' : ℝ) * 2 ^ (k + 1)) ≤ 1 / 2 := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hB'pos : (0 : ℝ) < (B' : ℝ) := by exact_mod_cast hB'
  -- `kB ≤ 2^k B'`
  have hbb : (B : ℝ) ≤ ((2 : ℝ) ^ k / (k : ℝ)) * (B' : ℝ) := by
    have := mul_le_mul_of_nonneg_right hratio (le_of_lt hB'pos)
    rwa [div_mul_cancel₀ _ (ne_of_gt hB'pos)] at this
  have hmain : (k : ℝ) * (B : ℝ) ≤ (2 : ℝ) ^ k * (B' : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hbb (le_of_lt hkpos)
    have heq : (k : ℝ) * (((2 : ℝ) ^ k / (k : ℝ)) * (B' : ℝ)) = (2 : ℝ) ^ k * (B' : ℝ) := by
      field_simp
    linarith [hmul, heq]
  have hden : (0 : ℝ) < (B' : ℝ) * 2 ^ (k + 1) := by positivity
  rw [div_le_iff₀ hden]
  have hp : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by
    rw [pow_succ]
    ring
  rw [hp]
  nlinarith [hmain]

/-- **Lemma A.2, success composition.**  If the four abort stages of Algorithm 4
each survive with probability at least `1/2`, the overall success probability is
at least `(1/2)^4 = 1/16`, a positive constant, i.e. `Ω(1)`. -/
theorem lemmaA2_success (p₂ p₈ p₁₀ p₁₂ : ℝ)
    (h₂ : 1 / 2 ≤ p₂) (h₈ : 1 / 2 ≤ p₈) (h₁₀ : 1 / 2 ≤ p₁₀) (h₁₂ : 1 / 2 ≤ p₁₂) :
    1 / 16 ≤ p₂ * p₈ * p₁₀ * p₁₂ := by
  have h₂0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hp2 : (0 : ℝ) ≤ p₂ := le_trans h₂0 h₂
  have hp8 : (0 : ℝ) ≤ p₈ := le_trans h₂0 h₈
  have hp10 : (0 : ℝ) ≤ p₁₀ := le_trans h₂0 h₁₀
  have hq1 : (1 / 2 : ℝ) * (1 / 2) ≤ p₂ * p₈ :=
    mul_le_mul h₂ h₈ h₂0 hp2
  have hq2 : ((1 / 2 : ℝ) * (1 / 2)) * (1 / 2) ≤ (p₂ * p₈) * p₁₀ :=
    mul_le_mul hq1 h₁₀ h₂0 (by positivity)
  have hq3 : (((1 / 2 : ℝ) * (1 / 2)) * (1 / 2)) * (1 / 2) ≤ ((p₂ * p₈) * p₁₀) * p₁₂ :=
    mul_le_mul hq2 h₁₂ h₂0 (by positivity)
  have hconst : (((1 / 2 : ℝ) * (1 / 2)) * (1 / 2)) * (1 / 2) = 1 / 16 := by norm_num
  have hpoly : (p₂ * p₈) * p₁₀ * p₁₂ = p₂ * p₈ * p₁₀ * p₁₂ := by ring
  rw [hconst] at hq3
  rw [hpoly] at hq3
  exact hq3

/-- **Lemma A.2, ratio arithmetic assembled.**  Under the source's hypothesis
`4k ≤ B/B' ≤ 2^k/k`, both explicit abort probabilities are at most `1/2`, which
is the quantitative input to the constant-success claim. -/
theorem lemmaA2_ratio_bounds (k B B' : ℕ) (hk : 0 < k) (hB' : 0 < B')
    (hlo : 4 * (k : ℝ) ≤ (B : ℝ) / (B' : ℝ))
    (hhi : (B : ℝ) / (B' : ℝ) ≤ (2 : ℝ) ^ k / (k : ℝ)) :
    (k : ℝ) * (2 * (B' : ℝ) / (B : ℝ)) ≤ 1 / 2 ∧
      (k : ℝ) * (B : ℝ) / ((B' : ℝ) * 2 ^ (k + 1)) ≤ 1 / 2 :=
  ⟨lemmaA2_step2_abort k B B' hk hB' hlo, lemmaA2_nu_abort k B B' hk hB' hhi⟩

end Qatlib.Papers.EllipticIsog10.MainResults
