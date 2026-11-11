/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HypercubeWalk01.MainResults.DiscreteWalk
import Qatlib.Papers.HypercubeWalk01.MainResults.CubePlancherel
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

/-!
# Discrete hypercube mixing from coefficient estimates

This module assembles binomial and trigonometric estimates into a conditional discrete-time
mixing bound in the setting of [MooreRussell2001]. The main result
`discreteWalk_mixing_of_coeff_estimate` assumes a parity Fourier bound and a uniform coefficient
estimate and deduces distance of order `n ^ (-7 / 6)` at rounded odd multiples of `π * n / 4`.

## Main statements

* `bracket_bound`: bounds the binomial expression when the cosine parameter is at most `2 / n`.
* `discreteWalk_mixing_of_coeff_estimate`: deduces the asymptotic mixing bound from the two
  supplied Fourier estimates.

## References

* [Moore and Russell, 2001][MooreRussell2001]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Finset
open scoped BigOperators symmDiff

open Qatlib.Concepts.ShadowModels.BooleanCubeFourier

namespace Qatlib.Papers.HypercubeWalk01.MainResults

/-- The binomial sum `∑ k = 0..n, choose n k * c ^ (2 * k)` equals `(1 + c ^ 2) ^ n`. -/
theorem sum_choose_cpow (n : ℕ) (c : ℝ) :
    (∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℝ) * c ^ (2 * k)) = (1 + c^2)^n := by
  rw [show (1:ℝ) + c^2 = c^2 + 1 by ring, add_pow]
  simp only [one_pow, mul_one]
  refine Finset.sum_congr rfl ?_
  intro k hk
  rw [pow_mul]
  ring

/-- For `n ≥ 1`, the sum over indices from one to `n - 1` equals the sum from zero to `n` minus
its two endpoint terms. -/
theorem sum_middle_shift (n : ℕ) (hn : 1 ≤ n) (f : ℕ → ℝ) :
    (∑ k ∈ Finset.range (n - 1), f (k + 1))
      = (∑ k ∈ Finset.range (n + 1), f k) - f 0 - f n := by
  have h1 : (∑ k ∈ Finset.range (n + 1), f k) = (∑ k ∈ Finset.range n, f (k + 1)) + f 0 := by
    rw [Finset.sum_range_succ']
  have h2 : (∑ k ∈ Finset.range n, f (k + 1)) = (∑ k ∈ Finset.range (n - 1), f (k + 1)) + f n := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [Finset.sum_range_succ]
    rw [show n - 1 + 1 = n by omega]
  rw [h1, h2]; ring

/-- For `n ≥ 2`, removing the two endpoint terms from the even-power binomial sum gives `(1 + c
^ 2) ^ n - 1 - c ^ (2 * n)`. -/
theorem middle_choose_cpow (n : ℕ) (hn : 2 ≤ n) (c : ℝ) :
    (∑ k ∈ Finset.range (n - 1), (Nat.choose n (k + 1) : ℝ) * c ^ (2 * (k + 1)))
      = (1 + c^2)^n - 1 - c^(2*n) := by
  have h1 : 1 ≤ n := by omega
  have hs := sum_middle_shift n h1 (fun j => (Nat.choose n j : ℝ) * c ^ (2 * j))
  have hfull := sum_choose_cpow n c
  rw [hs, hfull]
  simp only [Nat.choose_zero_right, Nat.choose_self, Nat.cast_one]
  ring

/-- For `n ≥ 2`, the sum of the interior binomial coefficients is `2 ^ n - 2`. -/
theorem middle_choose (n : ℕ) (hn : 2 ≤ n) :
    (∑ k ∈ Finset.range (n - 1), (Nat.choose n (k + 1) : ℝ)) = (2:ℝ)^n - 2 := by
  have h1 : 1 ≤ n := by omega
  have hs := sum_middle_shift n h1 (fun j => (Nat.choose n j : ℝ))
  have hfull : (∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℝ)) = (2:ℝ)^n := by
    rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
  rw [hs, hfull]
  simp only [Nat.choose_zero_right, Nat.choose_self, Nat.cast_one]
  ring

/-- For `n ≥ 2` and `c ≥ 0`, the interior binomial sum weighted by `2 * c ^ (2 * k) + 2 * c ^ n`
is at most `2 * ((2 * c) ^ n + (1 + c ^ 2) ^ n - 1)`. -/
theorem discBinomialAssembly (n : ℕ) (hn : 2 ≤ n) {c : ℝ} (hc0 : 0 ≤ c) :
    (∑ k ∈ Finset.range (n - 1), (Nat.choose n (k + 1) : ℝ) * (2 * c ^ (2*(k+1)) + 2 * c ^ n))
      ≤ 2 * ((2*c)^n + (1 + c^2)^n - 1) := by
  have hpow := middle_choose_cpow n hn c
  have hch := middle_choose n hn
  have hexp : (∑ k ∈ Finset.range (n - 1),
        (Nat.choose n (k + 1) : ℝ) * (2 * c ^ (2*(k+1)) + 2 * c ^ n))
      = 2 * (∑ k ∈ Finset.range (n - 1), (Nat.choose n (k + 1) : ℝ) * c ^ (2*(k+1)))
        + 2 * c ^ n * (∑ k ∈ Finset.range (n - 1), (Nat.choose n (k + 1) : ℝ)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro k hk
    ring
  rw [hexp, hpow, hch]
  have hc2n : 0 ≤ c ^ (2*n) := pow_nonneg hc0 _
  have hcn : 0 ≤ c ^ n := pow_nonneg hc0 _
  have hkey : 2 * ((1 + c^2)^n - 1 - c^(2*n)) + 2 * c^n * ((2:ℝ)^n - 2)
      = 2 * ((2*c)^n + (1 + c^2)^n - 1) - (2 * c^(2*n) + 4 * c^n) := by
    rw [mul_pow]
    ring
  rw [hkey]
  linarith

/-- For `0 ≤ y < 1`, the finite geometric sum through `y ^ n` is at most `1 / (1 - y)`. -/
theorem geom_partial_le (n : ℕ) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    (∑ k ∈ Finset.range (n+1), y^k) ≤ 1/(1-y) := by
  have hy0' : y ≠ 1 := ne_of_lt hy1
  rw [geom_sum_eq hy0' (n+1)]
  have hden : (0:ℝ) < 1 - y := by linarith
  have heq : (y^(n+1)-1)/(y-1) = (1 - y^(n+1))/(1-y) := by
    rw [show y^(n+1)-1 = -(1 - y^(n+1)) by ring,
        show y-1 = -(1-y) by ring, neg_div_neg_eq]
  rw [heq]
  apply div_le_div_of_nonneg_right _ hden.le
  have : (0:ℝ) ≤ y^(n+1) := pow_nonneg hy0 _
  linarith

/-- For `x ≥ 0` and `n * x < 1`, the power `(1 + x) ^ n` is at most `1 / (1 - n * x)`. -/
theorem one_add_pow_le_geom (n : ℕ) {x : ℝ} (hx : 0 ≤ x) (hnx : (n:ℝ)*x < 1) :
    (1 + x)^n ≤ 1 / (1 - (n:ℝ)*x) := by
  have hsum_pow : (1 + x)^n = ∑ k ∈ Finset.range (n+1), (Nat.choose n k : ℝ) * x^k := by
    rw [add_comm (1:ℝ) x, add_pow]
    refine Finset.sum_congr rfl ?_
    intro m hm
    simp only [one_pow, mul_one]
    ring
  rw [hsum_pow]
  have hy0 : (0:ℝ) ≤ (n:ℝ)*x := by positivity
  have hterm : ∀ k ∈ Finset.range (n+1), (Nat.choose n k : ℝ) * x^k ≤ ((n:ℝ)*x)^k := by
    intro k hk
    have hxpow : (0:ℝ) ≤ x^k := pow_nonneg hx k
    have hle : (Nat.choose n k : ℝ) ≤ (n:ℝ)^k := by
      exact_mod_cast Nat.choose_le_pow n k
    calc (Nat.choose n k : ℝ)*x^k ≤ (n:ℝ)^k * x^k :=
          mul_le_mul_of_nonneg_right hle hxpow
      _ = ((n:ℝ)*x)^k := by rw [mul_pow]
  calc ∑ k ∈ Finset.range (n+1), (Nat.choose n k:ℝ)*x^k
      ≤ ∑ k ∈ Finset.range (n+1), ((n:ℝ)*x)^k := Finset.sum_le_sum hterm
    _ ≤ 1/(1 - (n:ℝ)*x) := geom_partial_le n hy0 hnx

/-- For `n ≥ 8` and `0 ≤ c ≤ 2 / n`, the expression `(2 * c) ^ n + (1 + c ^ 2) ^ n - 1` is at
most `12 / n`. -/
theorem bracket_bound (n : ℕ) (hn : 8 ≤ n) {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 2/n) :
    (2*c)^n + (1 + c^2)^n - 1 ≤ 12/n := by
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn8 : (8:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hc2 : c^2 ≤ 4/(n:ℝ)^2 := by
    have h1 : c^2 ≤ (2/(n:ℝ))^2 := pow_le_pow_left₀ hc0 hc 2
    calc c^2 ≤ (2/(n:ℝ))^2 := h1
      _ = 4/(n:ℝ)^2 := by field_simp; ring
  have hnc2 : (n:ℝ)*c^2 ≤ 4/(n:ℝ) := by
    have h1 : (n:ℝ)*c^2 ≤ (n:ℝ)*(4/(n:ℝ)^2) := mul_le_mul_of_nonneg_left hc2 hnR.le
    calc (n:ℝ)*c^2 ≤ (n:ℝ)*(4/(n:ℝ)^2) := h1
      _ = 4/(n:ℝ) := by field_simp
  have h4n : 4/(n:ℝ) ≤ 1/2 := by
    rw [div_le_iff₀ hnR]; nlinarith
  have hy0 : (0:ℝ) ≤ (n:ℝ)*c^2 := by positivity
  have hnc2lt : (n:ℝ)*c^2 < 1 := by linarith
  have hg := one_add_pow_le_geom n (pow_nonneg hc0 2) hnc2lt
  have hbound1 : (1 + c^2)^n - 1 ≤ 8/n := by
    have hden : (0:ℝ) < 1 - (n:ℝ)*c^2 := by linarith
    have hfrac : 1/(1 - (n:ℝ)*c^2) - 1 = ((n:ℝ)*c^2)/(1 - (n:ℝ)*c^2) := by
      field_simp; ring
    have hhalf : (1:ℝ)/(1 - (n:ℝ)*c^2) ≤ 2 := by
      rw [div_le_iff₀ hden]; nlinarith
    have hle2 : ((n:ℝ)*c^2)/(1 - (n:ℝ)*c^2) ≤ ((n:ℝ)*c^2) * 2 := by
      have h := mul_le_mul_of_nonneg_left hhalf hy0
      simpa [div_eq_mul_inv] using h
    have hsum2 : ((n:ℝ)*c^2) * 2 ≤ 8/n := by
      have h1 : ((n:ℝ)*c^2)*2 ≤ (4/(n:ℝ))*2 := by nlinarith
      have h2 : (4/(n:ℝ))*2 = 8/n := by ring
      linarith
    linarith
  have h2c0 : (0:ℝ) ≤ 2*c := by positivity
  have h2c : (2:ℝ)*c ≤ 4/n := by
    have h1 : (2:ℝ)*c ≤ 2*(2/n) := by linarith
    calc (2:ℝ)*c ≤ 2*(2/n) := h1
      _ = 4/n := by ring
  have hpow2 : (2*c)^n ≤ 4/n := by
    have hbase : (2*c)^n ≤ ((4:ℝ)/n)^n := pow_le_pow_left₀ h2c0 h2c n
    have h4n1 : (4:ℝ)/n ≤ 1 := by
      rw [div_le_one hnR]
      have : (4:ℝ) ≤ (n:ℝ) := by linarith
      exact this
    have hself : ((4:ℝ)/n)^n ≤ (4:ℝ)/n := pow_le_of_le_one (by positivity) h4n1 (by omega)
    linarith
  have hsumadd : (2*c)^n + ((1 + c^2)^n - 1) ≤ 4/n + 8/n := add_le_add hpow2 hbound1
  have heq : (4:ℝ)/n + 8/n = 12/n := by ring
  linarith

/-- The total variation expression relative to the time-dependent parity mass function is
nonnegative. -/
theorem tvDistParityAt_nonneg (n t : ℕ) (P : Cube n → ℝ) :
    0 ≤ tvDistParityAt n t P := by
  unfold tvDistParityAt
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg (fun x _ => abs_nonneg _)

/-- The Fourier coefficient of `discDist n t` at `S` is `discCoeff n t S.card`. -/
theorem discDist_fourierCoeff (n t : ℕ) (S : Finset (Fin n)) :
    fourierCoeff (discDist n t) S = discCoeff n t S.card := by
  change fourierCoeff
      (fun x => uniformMass n * ∑ S : Finset (Fin n), discCoeff n t S.card * chi S x) S
    = discCoeff n t S.card
  exact fourierCoeff_synthesis (fun T => discCoeff n t T.card) S

/-- If `discDist n t` has total mass one, its squared distance from uniform is bounded by the
binomially weighted sum of its nonempty squared coefficients divided by four. -/
theorem discDist_tvDist_sq_le (n t : ℕ) (hP : ∑ x, discDist n t x = 1) :
    (tvDist (discDist n t)) ^ 2 ≤
      (1 / 4) * ∑ k ∈ Finset.range n,
        (Nat.choose n (k + 1) : ℝ) * (discCoeff n t (k + 1)) ^ 2 := by
  calc (tvDist (discDist n t)) ^ 2
      ≤ (1 / 4) * ∑ S ∈ Finset.univ.erase (∅ : Finset (Fin n)),
            (fourierCoeff (discDist n t) S) ^ 2 :=
        tvDist_sq_le (discDist n t) hP
    _ = (1 / 4) * ∑ S ∈ Finset.univ.erase (∅ : Finset (Fin n)),
            (fun k => (discCoeff n t k) ^ 2) S.card := by
        congr 1
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [discDist_fourierCoeff]
    _ = (1 / 4) * ∑ k ∈ Finset.range n,
            (Nat.choose n (k + 1) : ℝ) * (discCoeff n t (k + 1)) ^ 2 := by
        rw [sum_by_card_nonempty (fun k => (discCoeff n t k) ^ 2)]

/-- Assuming the stated parity Fourier bound and uniform coefficient estimate, there are `C > 0`
and `N` such that every `n ≥ N` mixes within `C * n ^ (-7 / 6)` of the corresponding parity
mass at rounded odd multiples of `π * n / 4`. This is a conditional form of the estimate in
[Moore and Russell, Theorem 1][MooreRussell2001]. -/
theorem discreteWalk_mixing_of_coeff_estimate
    (hDS : ∀ (n t : ℕ), 1 ≤ n → (tvDistParityAt n t (discDist n t))^2 ≤
        (1/4) * ∑ k ∈ Finset.range (n-1),
          (Nat.choose n (k+1) : ℝ) * (discCoeff n t (k+1))^2)
    (hB : ∃ K : ℝ, 0 < K ∧ ∀ (n t k : ℕ), 0 < k → k < n →
        (discCoeff n t k)^2 ≤ K * (n:ℝ)^(-(4/3):ℝ) *
          (2 * |Real.cos (2*(t:ℝ)/(n:ℝ))|^(2*k) +
            2 * |Real.cos (2*(t:ℝ)/(n:ℝ))|^n)) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ (n : ℕ), N ≤ n → ∀ k : ℕ, Odd k →
      IsInstantaneousMixingAt n ⌈(k : ℝ) * (Real.pi / 4) * (n : ℝ)⌉₊
        (C * (n : ℝ) ^ (-(7 / 6) : ℝ))
        (discDist n ⌈(k : ℝ) * (Real.pi / 4) * (n : ℝ)⌉₊) := by
  obtain ⟨K, hKpos, hB'⟩ := hB
  refine ⟨Real.sqrt (6*K) + 1, by positivity, 8, ?_⟩
  intro n hn k hk
  have hn0 : 0 < n := by omega
  have hn2 : 2 ≤ n := by omega
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn0
  set t : ℕ := ⌈(k : ℝ) * (Real.pi / 4) * (n : ℝ)⌉₊ with ht
  set c : ℝ := |Real.cos (2*(t:ℝ)/(n:ℝ))| with hc
  have hc0 : 0 ≤ c := abs_nonneg _
  have hc2n : c ≤ 2/(n:ℝ) := by
    have h := cos_two_t_at_ceil_odd_multiple (n := n) (k := k) hn0 hk
    simpa [c, t] using h

  have hsum_le :
      (∑ k' ∈ Finset.range (n - 1), (Nat.choose n (k' + 1) : ℝ) * (discCoeff n t (k' + 1)) ^ 2)
        ≤ K * (n:ℝ)^(-(4/3):ℝ) *
          (∑ k' ∈ Finset.range (n - 1),
            (Nat.choose n (k' + 1) : ℝ) * (2 * c ^ (2*(k'+1)) + 2 * c ^ n)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro k' hk'
    rw [Finset.mem_range] at hk'
    have hk'pos : 0 < k' + 1 := by omega
    have hk'lt : k' + 1 < n := by omega
    have hb := hB' n t (k'+1) hk'pos hk'lt
    have hb' : (discCoeff n t (k' + 1)) ^ 2 ≤
        K * (n:ℝ)^(-(4/3):ℝ) * (2 * c ^ (2*(k'+1)) + 2 * c ^ n) := by
      simpa [c] using hb
    calc (Nat.choose n (k' + 1) : ℝ) * (discCoeff n t (k' + 1)) ^ 2
        ≤ (Nat.choose n (k' + 1) : ℝ) *
            (K * (n:ℝ)^(-(4/3):ℝ) * (2 * c ^ (2*(k'+1)) + 2 * c ^ n)) := by
          apply mul_le_mul_of_nonneg_left hb'
          positivity
      _ = K * (n:ℝ)^(-(4/3):ℝ) *
            ((Nat.choose n (k' + 1) : ℝ) * (2 * c ^ (2*(k'+1)) + 2 * c ^ n)) := by
          ring

  have hbin := discBinomialAssembly n hn2 hc0
  have hbr := bracket_bound n hn hc0 hc2n
  have hpow_eq : (n:ℝ)^(-(4/3):ℝ) * (1/(n:ℝ)) = (n:ℝ)^(-(7/3):ℝ) := by
    have h1 : (n:ℝ)^(-(7/3):ℝ) = (n:ℝ)^(-(4/3):ℝ) * (n:ℝ)^(-1:ℝ) := by
      rw [← Real.rpow_add hnR]
      norm_num
    rw [h1, Real.rpow_neg_one]
    ring
  have hTV2 : (tvDistParityAt n t (discDist n t))^2 ≤ 6 * K * (n:ℝ)^(-(7/3):ℝ) := by
    have hDSn := hDS n t (by omega)
    calc (tvDistParityAt n t (discDist n t))^2
        ≤ (1/4) * (∑ k' ∈ Finset.range (n - 1),
            (Nat.choose n (k' + 1) : ℝ) * (discCoeff n t (k' + 1)) ^ 2) := hDSn
      _ ≤ (1/4) * (K * (n:ℝ)^(-(4/3):ℝ) *
            (∑ k' ∈ Finset.range (n - 1),
              (Nat.choose n (k' + 1) : ℝ) * (2 * c ^ (2*(k'+1)) + 2 * c ^ n))) := by
          apply mul_le_mul_of_nonneg_left hsum_le (by norm_num)
      _ = (1/4) * K * (n:ℝ)^(-(4/3):ℝ) *
            (∑ k' ∈ Finset.range (n - 1),
              (Nat.choose n (k' + 1) : ℝ) * (2 * c ^ (2*(k'+1)) + 2 * c ^ n)) := by
          ring
      _ ≤ (1/4) * K * (n:ℝ)^(-(4/3):ℝ) * (2 * ((2*c)^n + (1 + c^2)^n - 1)) := by
          apply mul_le_mul_of_nonneg_left hbin
          positivity
      _ ≤ (1/4) * K * (n:ℝ)^(-(4/3):ℝ) * (2 * (12/n)) := by
          apply mul_le_mul_of_nonneg_left
          · nlinarith [hbr]
          · positivity
      _ = 6 * K * ((n:ℝ)^(-(4/3):ℝ) * (1/(n:ℝ))) := by ring
      _ = 6 * K * (n:ℝ)^(-(7/3):ℝ) := by rw [hpow_eq]

  have h6K : (0:ℝ) ≤ 6*K := by positivity
  have hnn := tvDistParityAt_nonneg n t (discDist n t)
  have hTV : tvDistParityAt n t (discDist n t) ≤ Real.sqrt (6*K) * (n:ℝ)^(-(7/6):ℝ) := by
    have hsq : Real.sqrt ((tvDistParityAt n t (discDist n t))^2)
        = tvDistParityAt n t (discDist n t) := Real.sqrt_sq hnn
    rw [← hsq]
    calc Real.sqrt ((tvDistParityAt n t (discDist n t))^2)
        ≤ Real.sqrt (6*K*(n:ℝ)^(-(7/3):ℝ)) := Real.sqrt_le_sqrt hTV2
      _ = Real.sqrt (6*K) * Real.sqrt ((n:ℝ)^(-(7/3):ℝ)) := by
          rw [Real.sqrt_mul h6K]
      _ = Real.sqrt (6*K) * (n:ℝ)^(-(7/6):ℝ) := by
          congr 1
          rw [Real.sqrt_eq_rpow]
          rw [← Real.rpow_mul (le_of_lt hnR)]
          norm_num
  have hCle : Real.sqrt (6*K) * (n:ℝ)^(-(7/6):ℝ)
      ≤ (Real.sqrt (6*K) + 1) * (n:ℝ)^(-(7/6):ℝ) := by
    apply mul_le_mul_of_nonneg_right (by linarith)
    exact Real.rpow_nonneg (le_of_lt hnR) _
  exact le_trans hTV hCle

end Qatlib.Papers.HypercubeWalk01.MainResults
