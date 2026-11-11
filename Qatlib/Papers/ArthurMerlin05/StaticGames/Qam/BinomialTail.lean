/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ArthurMerlin05.StaticGames.Core.Toolkit
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Chernoff bounds for the binomial tail

Source: Marriott--Watrous, *Quantum Arthur--Merlin Games*, arXiv:cs/0506068v1,
§3--§4 (proofs of Theorems 3.3 and 4.2, equations (6)--(8)).

The error-reduction steps in the paper play `N` independent repetitions of a
game and accept when the number of successes crosses a threshold.  The analysis
therefore needs a quantitative tail bound for the binomial distribution.  This
file proves the Chernoff bound from scratch:

* `binomTail`: the upper tail `Σ_{j ≥ T} C(N,j) p^j (1−p)^{N−j}`;
* `binomTailLower`: the lower tail `Σ_{j < T} C(N,j) p^j (1−p)^{N−j}`;
* `sum_binom_mass`: the total mass is `(p + (1−p))^N = 1`;
* `binomTail_le_exp_mgf`, `binomTailLower_le_exp_mgf`: the exponential
  moment-generating bounds
  `e^{−tT} (1 − p + p e^{t})^N` and `e^{sT} (1 − p + p e^{−s})^N`;
* `exp_le_one_add_add_sq`, `exp_neg_le_one_sub_add_sq`: the quadratic Taylor
  estimates `e^{±x} ≤ 1 ± x + x²` on `[0,1]`;
* `one_add_pow_le_exp`: `(1+a)^N ≤ e^{Na}` for `a ≥ 0`;
* `binomTail_chernoff`, `binomTailLower_chernoff`: the bounds
  `binomTail N p (N(p+δ)) ≤ e^{−Nδ²/4}` and
  `binomTailLower N p (N(p−δ)) ≤ e^{−Nδ²/4}` for `0 ≤ p ≤ 1`, `0 ≤ δ ≤ 2`;
* `binomTail_half_pow`, `binomTailLower_half_pow`: the `(1/2)^r` forms used in
  the paper, requiring `N δ² ≥ 4 r log 2`.

These are genuine analytic inequalities, not restatements of a paper
conclusion.  The constant `N δ²/4` is slightly better than the paper's
`N = 8 q² r` bookkeeping, so the results here strengthen the paper's Chernoff
step.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ArthurMerlin05.StaticGames.Qam

open Finset
open scoped BigOperators

/-- The upper binomial tail `Σ_{j ≥ T} C(N,j) p^j (1−p)^{N−j}`, with the
threshold written as a real number `T`. -/
noncomputable def binomTail (N : ℕ) (p T : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (N + 1),
    if T ≤ (j : ℝ) then (N.choose j : ℝ) * p ^ j * (1 - p) ^ (N - j) else 0

/-- The lower binomial tail `Σ_{j < T} C(N,j) p^j (1−p)^{N−j}`. -/
noncomputable def binomTailLower (N : ℕ) (p T : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (N + 1),
    if (j : ℝ) < T then (N.choose j : ℝ) * p ^ j * (1 - p) ^ (N - j) else 0

/-- The full binomial mass `Σ_{j=0}^N C(N,j) p^j (1−p)^{N−j}` equals
`(p + (1−p))^N = 1` (the binomial theorem). -/
theorem sum_binom_mass (N : ℕ) (p : ℝ) :
    (∑ j ∈ Finset.range (N + 1), (N.choose j : ℝ) * p ^ j * (1 - p) ^ (N - j))
      = 1 := by
  have h := add_pow p (1 - p) N
  rw [show p + (1 - p) = (1 : ℝ) by ring, one_pow] at h
  calc (∑ j ∈ Finset.range (N + 1), (N.choose j : ℝ) * p ^ j * (1 - p) ^ (N - j))
      = ∑ j ∈ Finset.range (N + 1), p ^ j * (1 - p) ^ (N - j) * (N.choose j : ℝ) := by
        refine Finset.sum_congr rfl fun j _ => by ring
    _ = 1 := h.symm

/-- Pointwise Chernoff domination: for `t ≥ 0` the indicator function of
`{T ≤ j}` is bounded above by `e^{t(j−T)}`. -/
theorem indicator_le_exp (t : ℝ) (ht : 0 ≤ t) (j T : ℝ) :
    (if T ≤ j then (1 : ℝ) else 0) ≤ Real.exp (t * (j - T)) := by
  split_ifs with h
  · exact Real.one_le_exp (mul_nonneg ht (by linarith))
  · exact (Real.exp_pos (t * (j - T))).le

/-- Mirror Chernoff domination: for `s ≥ 0` the indicator function of
`{j < T}` is bounded above by `e^{s(T−j)}`. -/
theorem indicator_lt_le_exp (s : ℝ) (hs : 0 ≤ s) (j T : ℝ) :
    (if j < T then (1 : ℝ) else 0) ≤ Real.exp (s * (T - j)) := by
  split_ifs with h
  · exact Real.one_le_exp (mul_nonneg hs (by linarith))
  · exact (Real.exp_pos (s * (T - j))).le

/-- Exponential-moment bound for the upper tail:
`binomTail N p T ≤ e^{−tT} (1 − p + p e^{t})^N` for `0 ≤ p ≤ 1` and `t ≥ 0`. -/
theorem binomTail_le_exp_mgf (N : ℕ) {p t T : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ht : 0 ≤ t) :
    binomTail N p T ≤ Real.exp (-(t * T)) * (1 - p + p * Real.exp t) ^ N := by
  have hq0 : 0 ≤ 1 - p := by linarith
  -- Step 1: pointwise domination by the exponential weights
  have hpoint : ∀ j ∈ Finset.range (N + 1),
      (if T ≤ (j : ℝ) then (N.choose j : ℝ) * p ^ j * (1 - p) ^ (N - j) else 0)
        ≤ (N.choose j : ℝ) * p ^ j * (1 - p) ^ (N - j) * Real.exp (t * ((j : ℝ) - T)) := by
    intro j _
    have hC : (0 : ℝ) ≤ (N.choose j : ℝ) := by exact_mod_cast Nat.zero_le _
    have hg : 0 ≤ (N.choose j : ℝ) * p ^ j * (1 - p) ^ (N - j) :=
      mul_nonneg (mul_nonneg hC (pow_nonneg hp0 j)) (pow_nonneg hq0 _)
    split_ifs with h
    · have hone : (1 : ℝ) ≤ Real.exp (t * ((j : ℝ) - T)) :=
        Real.one_le_exp (mul_nonneg ht (by linarith))
      nlinarith
    · exact mul_nonneg hg (Real.exp_pos _).le
  have hstep1 : binomTail N p T
      ≤ ∑ j ∈ Finset.range (N + 1),
          (N.choose j : ℝ) * p ^ j * (1 - p) ^ (N - j) * Real.exp (t * ((j : ℝ) - T)) := by
    unfold binomTail
    exact Finset.sum_le_sum hpoint
  -- Step 2: factor the exponential weight
  have hkey : ∀ j ∈ Finset.range (N + 1),
      (N.choose j : ℝ) * p ^ j * (1 - p) ^ (N - j) * Real.exp (t * ((j : ℝ) - T))
        = Real.exp (-(t * T)) *
            ((N.choose j : ℝ) * (p * Real.exp t) ^ j * (1 - p) ^ (N - j)) := by
    intro j _
    have hexpj : Real.exp (t * (j : ℝ)) = Real.exp t ^ j := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have harg : t * ((j : ℝ) - T) = t * (j : ℝ) + -(t * T) := by ring
    rw [harg, Real.exp_add, hexpj, mul_pow]
    ring
  have hstep2 : (∑ j ∈ Finset.range (N + 1),
        (N.choose j : ℝ) * p ^ j * (1 - p) ^ (N - j) * Real.exp (t * ((j : ℝ) - T)))
      = Real.exp (-(t * T)) *
          ∑ j ∈ Finset.range (N + 1),
            (N.choose j : ℝ) * (p * Real.exp t) ^ j * (1 - p) ^ (N - j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hkey
  -- Step 3: binomial theorem
  have hbinom : (∑ j ∈ Finset.range (N + 1),
        (N.choose j : ℝ) * (p * Real.exp t) ^ j * (1 - p) ^ (N - j))
      = (p * Real.exp t + (1 - p)) ^ N := by
    rw [add_pow]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hbase : p * Real.exp t + (1 - p) = 1 - p + p * Real.exp t := by ring
  rw [hbase] at hbinom
  refine le_trans hstep1 ?_
  rw [hstep2, hbinom]

/-- Exponential-moment bound for the lower tail:
`binomTailLower N p T ≤ e^{sT} (1 − p + p e^{−s})^N` for `0 ≤ p ≤ 1` and
`s ≥ 0`. -/
theorem binomTailLower_le_exp_mgf (N : ℕ) {p s T : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hs : 0 ≤ s) :
    binomTailLower N p T ≤ Real.exp (s * T) * (1 - p + p * Real.exp (-s)) ^ N := by
  have hq0 : 0 ≤ 1 - p := by linarith
  have hpoint : ∀ j ∈ Finset.range (N + 1),
      (if (j : ℝ) < T then (N.choose j : ℝ) * p ^ j * (1 - p) ^ (N - j) else 0)
        ≤ (N.choose j : ℝ) * p ^ j * (1 - p) ^ (N - j) * Real.exp (s * (T - (j : ℝ))) := by
    intro j _
    have hC : (0 : ℝ) ≤ (N.choose j : ℝ) := by exact_mod_cast Nat.zero_le _
    have hg : 0 ≤ (N.choose j : ℝ) * p ^ j * (1 - p) ^ (N - j) :=
      mul_nonneg (mul_nonneg hC (pow_nonneg hp0 j)) (pow_nonneg hq0 _)
    split_ifs with h
    · have hone : (1 : ℝ) ≤ Real.exp (s * (T - (j : ℝ))) :=
        Real.one_le_exp (mul_nonneg hs (by linarith))
      nlinarith
    · exact mul_nonneg hg (Real.exp_pos _).le
  have hstep1 : binomTailLower N p T
      ≤ ∑ j ∈ Finset.range (N + 1),
          (N.choose j : ℝ) * p ^ j * (1 - p) ^ (N - j) * Real.exp (s * (T - (j : ℝ))) := by
    unfold binomTailLower
    exact Finset.sum_le_sum hpoint
  have hkey : ∀ j ∈ Finset.range (N + 1),
      (N.choose j : ℝ) * p ^ j * (1 - p) ^ (N - j) * Real.exp (s * (T - (j : ℝ)))
        = Real.exp (s * T) *
            ((N.choose j : ℝ) * (p * Real.exp (-s)) ^ j * (1 - p) ^ (N - j)) := by
    intro j _
    have hexpj : Real.exp (-(s * (j : ℝ))) = Real.exp (-s) ^ j := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have harg : s * (T - (j : ℝ)) = -(s * (j : ℝ)) + s * T := by ring
    rw [harg, Real.exp_add, hexpj, mul_pow]
    ring
  have hstep2 : (∑ j ∈ Finset.range (N + 1),
        (N.choose j : ℝ) * p ^ j * (1 - p) ^ (N - j) * Real.exp (s * (T - (j : ℝ))))
      = Real.exp (s * T) *
          ∑ j ∈ Finset.range (N + 1),
            (N.choose j : ℝ) * (p * Real.exp (-s)) ^ j * (1 - p) ^ (N - j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hkey
  have hbinom : (∑ j ∈ Finset.range (N + 1),
        (N.choose j : ℝ) * (p * Real.exp (-s)) ^ j * (1 - p) ^ (N - j))
      = (p * Real.exp (-s) + (1 - p)) ^ N := by
    rw [add_pow]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hbase : p * Real.exp (-s) + (1 - p) = 1 - p + p * Real.exp (-s) := by ring
  rw [hbase] at hbinom
  refine le_trans hstep1 ?_
  rw [hstep2, hbinom]

/-- Quadratic upper estimate `e^x ≤ 1 + x + x²` for `0 ≤ x ≤ 1`, from the
Taylor bound `Real.exp_bound'` at order two. -/
theorem exp_le_one_add_add_sq {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 := by
  have h := Real.exp_bound' h0 h1 (n := 2) (by norm_num)
  have hsum : (∑ m ∈ Finset.range 2, x ^ m / (m.factorial : ℝ)) = 1 + x := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    norm_num
  rw [hsum] at h
  have hval : x ^ 2 * (((2 : ℕ) : ℝ) + 1) / ((Nat.factorial 2 : ℝ) * ((2 : ℕ) : ℝ))
      = 3 * x ^ 2 / 4 := by
    rw [Nat.factorial_two]; ring
  rw [hval] at h
  nlinarith

/-- Quadratic upper estimate `e^{−x} ≤ 1 − x + x²` for `0 ≤ x ≤ 1`, from
`e^x ≥ 1 + x` and `1/(1+x) ≤ 1 − x + x²`. -/
theorem exp_neg_le_one_sub_add_sq {x : ℝ} (h0 : 0 ≤ x) (_h1 : x ≤ 1) :
    Real.exp (-x) ≤ 1 - x + x ^ 2 := by
  have hx1 : 0 < 1 + x := by linarith
  have hexp : (1 + x) ≤ Real.exp x := by simpa [add_comm] using Real.add_one_le_exp x
  have hstep : Real.exp (-x) ≤ (1 + x)⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ hx1 hexp
  have h2 : (1 + x)⁻¹ ≤ 1 - x + x ^ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hx1]
    nlinarith [pow_nonneg h0 3]
  linarith

/-- `(1 + a)^N ≤ e^{Na}` for `a ≥ 0`, from `1 + a ≤ e^a`. -/
theorem one_add_pow_le_exp (a : ℝ) (N : ℕ) (ha : 0 ≤ a) :
    (1 + a) ^ N ≤ Real.exp (N * a) := by
  calc (1 + a) ^ N ≤ Real.exp a ^ N :=
        pow_le_pow_left₀ (by linarith) (by simpa [add_comm] using Real.add_one_le_exp a) N
    _ = Real.exp (N * a) := (Real.exp_nat_mul a N).symm

/-- Chernoff bound for the upper tail: for `0 ≤ p ≤ 1` and `0 ≤ δ ≤ 2`,
`binomTail N p (N(p+δ)) ≤ e^{−Nδ²/4}`. -/
theorem binomTail_chernoff (N : ℕ) {p δ : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hδ0 : 0 ≤ δ) (hδ2 : δ ≤ 2) :
    binomTail N p (N * (p + δ)) ≤ Real.exp (-((N : ℝ) * δ ^ 2 / 4)) := by
  set t : ℝ := δ / 2 with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := by rw [ht]; linarith
  have hmgf := binomTail_le_exp_mgf (N := N) (p := p) (t := t) (T := (N : ℝ) * (p + δ))
    hp0 hp1 ht0
  -- bound the base `1 − p + p e^t`
  have he : Real.exp t ≤ 1 + t + t ^ 2 := exp_le_one_add_add_sq ht0 ht1
  have hmul : p * Real.exp t ≤ p * (1 + t + t ^ 2) := mul_le_mul_of_nonneg_left he hp0
  have hbase_le : 1 - p + p * Real.exp t ≤ Real.exp (p * (t + t ^ 2)) := by
    have h1 : 1 - p + p * Real.exp t ≤ 1 + p * (t + t ^ 2) := by nlinarith [hmul]
    have h2 : (1 : ℝ) + p * (t + t ^ 2) ≤ Real.exp (p * (t + t ^ 2)) := by
      simpa [add_comm] using Real.add_one_le_exp (p * (t + t ^ 2))
    linarith
  have hbase0 : 0 ≤ 1 - p + p * Real.exp t := by
    have := Real.exp_pos t
    nlinarith
  have hpow : (1 - p + p * Real.exp t) ^ N
      ≤ Real.exp ((N : ℝ) * (p * (t + t ^ 2))) := by
    calc (1 - p + p * Real.exp t) ^ N ≤ Real.exp (p * (t + t ^ 2)) ^ N :=
          pow_le_pow_left₀ hbase0 hbase_le N
      _ = Real.exp ((N : ℝ) * (p * (t + t ^ 2))) := (Real.exp_nat_mul _ N).symm
  have hE : Real.exp (-(t * ((N : ℝ) * (p + δ)))) * (1 - p + p * Real.exp t) ^ N
      ≤ Real.exp (-((N : ℝ) * δ ^ 2 / 4)) := by
    calc Real.exp (-(t * ((N : ℝ) * (p + δ)))) * (1 - p + p * Real.exp t) ^ N
        ≤ Real.exp (-(t * ((N : ℝ) * (p + δ)))) *
            Real.exp ((N : ℝ) * (p * (t + t ^ 2))) :=
          mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
      _ = Real.exp (-(t * ((N : ℝ) * (p + δ))) + (N : ℝ) * (p * (t + t ^ 2))) := by
          rw [← Real.exp_add]
      _ ≤ Real.exp (-((N : ℝ) * δ ^ 2 / 4)) := by
          apply Real.exp_le_exp.mpr
          have hpd : (N : ℝ) * p * δ ^ 2 / 4 ≤ (N : ℝ) * δ ^ 2 / 4 := by
            have hmul2 := mul_le_mul_of_nonneg_right hp1
              (show (0 : ℝ) ≤ (N : ℝ) * δ ^ 2 / 4 by positivity)
            calc (N : ℝ) * p * δ ^ 2 / 4 = p * ((N : ℝ) * δ ^ 2 / 4) := by ring
              _ ≤ 1 * ((N : ℝ) * δ ^ 2 / 4) := hmul2
              _ = (N : ℝ) * δ ^ 2 / 4 := by ring
          rw [ht]
          nlinarith [hpd]
  refine le_trans hmgf ?_
  exact hE

/-- Chernoff bound for the lower tail: for `0 ≤ p ≤ 1` and `0 ≤ δ ≤ 2`,
`binomTailLower N p (N(p−δ)) ≤ e^{−Nδ²/4}`. -/
theorem binomTailLower_chernoff (N : ℕ) {p δ : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hδ0 : 0 ≤ δ) (hδ2 : δ ≤ 2) :
    binomTailLower N p (N * (p - δ)) ≤ Real.exp (-((N : ℝ) * δ ^ 2 / 4)) := by
  set s : ℝ := δ / 2 with hs
  have hs0 : 0 ≤ s := by positivity
  have hs1 : s ≤ 1 := by rw [hs]; linarith
  have hmgf := binomTailLower_le_exp_mgf (N := N) (p := p) (s := s) (T := (N : ℝ) * (p - δ))
    hp0 hp1 hs0
  have he : Real.exp (-s) ≤ 1 - s + s ^ 2 := exp_neg_le_one_sub_add_sq hs0 hs1
  have hmul : p * Real.exp (-s) ≤ p * (1 - s + s ^ 2) := mul_le_mul_of_nonneg_left he hp0
  have hbase_le : 1 - p + p * Real.exp (-s) ≤ Real.exp (-(p * (s - s ^ 2))) := by
    have h1 : 1 - p + p * Real.exp (-s) ≤ 1 - p * (s - s ^ 2) := by nlinarith [hmul]
    have h2 : (1 : ℝ) - p * (s - s ^ 2) ≤ Real.exp (-(p * (s - s ^ 2))) := by
      have := Real.add_one_le_exp (-(p * (s - s ^ 2)))
      linarith
    linarith
  have hbase0 : 0 ≤ 1 - p + p * Real.exp (-s) := by
    have := Real.exp_pos (-s)
    nlinarith
  have hpow : (1 - p + p * Real.exp (-s)) ^ N
      ≤ Real.exp ((N : ℝ) * (-(p * (s - s ^ 2)))) := by
    calc (1 - p + p * Real.exp (-s)) ^ N
        ≤ Real.exp (-(p * (s - s ^ 2))) ^ N := pow_le_pow_left₀ hbase0 hbase_le N
      _ = Real.exp ((N : ℝ) * (-(p * (s - s ^ 2)))) := (Real.exp_nat_mul _ N).symm
  have hE : Real.exp (s * ((N : ℝ) * (p - δ))) * (1 - p + p * Real.exp (-s)) ^ N
      ≤ Real.exp (-((N : ℝ) * δ ^ 2 / 4)) := by
    calc Real.exp (s * ((N : ℝ) * (p - δ))) * (1 - p + p * Real.exp (-s)) ^ N
        ≤ Real.exp (s * ((N : ℝ) * (p - δ))) *
            Real.exp ((N : ℝ) * (-(p * (s - s ^ 2)))) :=
          mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
      _ = Real.exp (s * ((N : ℝ) * (p - δ)) + (N : ℝ) * (-(p * (s - s ^ 2)))) := by
          rw [← Real.exp_add]
      _ ≤ Real.exp (-((N : ℝ) * δ ^ 2 / 4)) := by
          apply Real.exp_le_exp.mpr
          have hpd : (N : ℝ) * p * δ ^ 2 / 4 ≤ (N : ℝ) * δ ^ 2 / 4 := by
            have hmul2 := mul_le_mul_of_nonneg_right hp1
              (show (0 : ℝ) ≤ (N : ℝ) * δ ^ 2 / 4 by positivity)
            calc (N : ℝ) * p * δ ^ 2 / 4 = p * ((N : ℝ) * δ ^ 2 / 4) := by ring
              _ ≤ 1 * ((N : ℝ) * δ ^ 2 / 4) := hmul2
              _ = (N : ℝ) * δ ^ 2 / 4 := by ring
          rw [hs]
          nlinarith [hpd]
  refine le_trans hmgf ?_
  exact hE

/-- `(1/2)^r = e^{−r log 2}`. -/
theorem half_pow_eq_exp (r : ℕ) :
    ((1 / 2 : ℝ) ^ r) = Real.exp (-((r : ℝ) * Real.log 2)) := by
  have hlog : Real.log (1 / 2) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  calc (1 / 2 : ℝ) ^ r = Real.exp (Real.log (1 / 2)) ^ r := by
        rw [Real.exp_log (by norm_num)]
    _ = Real.exp ((r : ℝ) * Real.log (1 / 2)) := (Real.exp_nat_mul _ r).symm
    _ = Real.exp (-((r : ℝ) * Real.log 2)) := by rw [hlog]; ring

/-- The paper's `2^{−r}` upper-tail form: if `N δ² ≥ 4 r log 2` then
`binomTail N p (N(p+δ)) ≤ (1/2)^r`. -/
theorem binomTail_half_pow (N : ℕ) {p δ : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hδ0 : 0 ≤ δ) (hδ2 : δ ≤ 2) {r : ℕ}
    (hN : (r : ℝ) * Real.log 2 ≤ (N : ℝ) * δ ^ 2 / 4) :
    binomTail N p (N * (p + δ)) ≤ (1 / 2 : ℝ) ^ r := by
  have h := binomTail_chernoff N hp0 hp1 hδ0 hδ2
  rw [half_pow_eq_exp]
  refine le_trans h (Real.exp_le_exp.mpr ?_)
  linarith

/-- The paper's `2^{−r}` lower-tail form: if `N δ² ≥ 4 r log 2` then
`binomTailLower N p (N(p−δ)) ≤ (1/2)^r`. -/
theorem binomTailLower_half_pow (N : ℕ) {p δ : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hδ0 : 0 ≤ δ) (hδ2 : δ ≤ 2) {r : ℕ}
    (hN : (r : ℝ) * Real.log 2 ≤ (N : ℝ) * δ ^ 2 / 4) :
    binomTailLower N p (N * (p - δ)) ≤ (1 / 2 : ℝ) ^ r := by
  have h := binomTailLower_chernoff N hp0 hp1 hδ0 hδ2
  rw [half_pow_eq_exp]
  refine le_trans h (Real.exp_le_exp.mpr ?_)
  linarith

end Qatlib.Papers.ArthurMerlin05.StaticGames.Qam
