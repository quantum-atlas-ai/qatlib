/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QQueryGraph04.MainResults.Model.Basic

/-!
# Analytic estimates for graph query costs

This module supplies finite-sum, square-root, and geometric estimates for the cost and error
expressions in `Model.Basic`. In particular, it bounds Borůvka phase errors, directed-tree
errors, and tier failure terms by explicit constants.

The source paper is [DurrEtAl2006].

## Main statements

* `sum_sqrt_mul_le`: The sum of products √(a u)√(b u) over a finite set is at most the product
  of the square roots of the two corresponding sums.
* `boruvkaError_le`: The accumulated Borůvka error is at most 1/4.
* `tierFailure_le_third`: Every tier failure expression is at most 1/3.

## References

* [Dürr et al., 2006][DurrEtAl2006]
-/

set_option autoImplicit false

namespace Qatlib.Papers.QQueryGraph04.MainResults.Model

open Finset

/-- The sum of products √(a u)√(b u) over a finite set is at most the product of the square
roots of the two corresponding sums [DurrEtAl2006]. -/
theorem sum_sqrt_mul_le {ι : Type*} (s : Finset ι) (a b : ι → ℕ) :
    (∑ u ∈ s, Real.sqrt (a u) * Real.sqrt (b u)) ≤
      Real.sqrt (∑ u ∈ s, (a u : ℝ)) * Real.sqrt (∑ u ∈ s, (b u : ℝ)) := by
  have hsq := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun u => Real.sqrt (a u)) (fun u => Real.sqrt (b u))
  have hA : (∑ u ∈ s, (Real.sqrt (a u)) ^ 2) = ∑ u ∈ s, (a u : ℝ) := by
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Real.sq_sqrt (Nat.cast_nonneg _)]
  have hB : (∑ u ∈ s, (Real.sqrt (b u)) ^ 2) = ∑ u ∈ s, (b u : ℝ) := by
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [hA, hB] at hsq
  have hS : 0 ≤ ∑ u ∈ s, Real.sqrt (a u) * Real.sqrt (b u) :=
    Finset.sum_nonneg fun u _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc (∑ u ∈ s, Real.sqrt (a u) * Real.sqrt (b u))
      = Real.sqrt ((∑ u ∈ s, Real.sqrt (a u) * Real.sqrt (b u)) ^ 2) :=
        (Real.sqrt_sq hS).symm
    _ ≤ Real.sqrt ((∑ u ∈ s, (a u : ℝ)) * ∑ u ∈ s, (b u : ℝ)) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (∑ u ∈ s, (a u : ℝ)) * Real.sqrt (∑ u ∈ s, (b u : ℝ)) :=
        Real.sqrt_mul (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) _

/-- The sum of 1/√(j + 1) over j < n is at most 2√n. -/
theorem sum_inv_sqrt_range (n : ℕ) :
    (∑ j ∈ Finset.range n, (1 : ℝ) / Real.sqrt ((j : ℝ) + 1)) ≤
      2 * Real.sqrt (n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hstep : (1 : ℝ) / Real.sqrt ((n : ℝ) + 1) ≤
        2 * (Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ)) := by
      have hx : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
      have hy : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
      have hxy : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) + 1) :=
        Real.sqrt_le_sqrt (by linarith)
      have hden : 0 < Real.sqrt ((n : ℝ) + 1) + Real.sqrt (n : ℝ) := by positivity
      have hprod : (Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ)) *
          (Real.sqrt ((n : ℝ) + 1) + Real.sqrt (n : ℝ)) = 1 := by
        have h1 : Real.sqrt ((n : ℝ) + 1) ^ 2 = (n : ℝ) + 1 :=
          Real.sq_sqrt (by positivity)
        have h2 : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
        nlinarith
      have hval : 2 * (Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ)) =
          2 / (Real.sqrt ((n : ℝ) + 1) + Real.sqrt (n : ℝ)) := by
        rw [eq_div_iff_mul_eq hden.ne']
        nlinarith [hprod]
      rw [hval, div_le_div_iff₀ hx hden]
      nlinarith [hxy]
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    nlinarith [ih, hstep]

/-- The sum of √(N/(j + 1)) over j < n is at most 2√(Nn) [DurrEtAl2006]. -/
theorem sum_sqrt_div_range (N n : ℕ) :
    (∑ j ∈ Finset.range n, Real.sqrt ((N : ℝ) / ((j : ℝ) + 1))) ≤
      2 * Real.sqrt ((N : ℝ) * (n : ℝ)) := by
  have hdiv : ∀ j : ℕ, Real.sqrt ((N : ℝ) / ((j : ℝ) + 1)) =
      Real.sqrt (N : ℝ) * (1 / Real.sqrt ((j : ℝ) + 1)) := by
    intro j
    rw [Real.sqrt_div (Nat.cast_nonneg N)]
    ring
  calc (∑ j ∈ Finset.range n, Real.sqrt ((N : ℝ) / ((j : ℝ) + 1)))
      = ∑ j ∈ Finset.range n, Real.sqrt (N : ℝ) * (1 / Real.sqrt ((j : ℝ) + 1)) := by
        exact Finset.sum_congr rfl fun j _ => hdiv j
    _ = Real.sqrt (N : ℝ) * ∑ j ∈ Finset.range n, (1 / Real.sqrt ((j : ℝ) + 1)) := by
        rw [Finset.mul_sum]
    _ ≤ Real.sqrt (N : ℝ) * (2 * Real.sqrt (n : ℝ)) := by
        have hN : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
        exact mul_le_mul_of_nonneg_left (sum_inv_sqrt_range n) hN
    _ ≤ 2 * Real.sqrt ((N : ℝ) * (n : ℝ)) := by
        rw [Real.sqrt_mul (Nat.cast_nonneg N)]
        have hN : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
        have hn : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
        nlinarith

/-- The accumulated Borůvka error is exactly 1/4 − 1/2^(M + 2). -/
theorem boruvkaError_eq (M : ℕ) :
    boruvkaError M = 1 / 4 - 1 / (2 : ℝ) ^ (M + 2) := by
  induction M with
  | zero => norm_num [boruvkaError]
  | succ M ih =>
    have hstep : boruvkaError (M + 1) = boruvkaError M + 1 / (2 : ℝ) ^ (M + 3) := by
      simp only [boruvkaError]
      rw [Finset.sum_range_succ]
    rw [hstep, ih]
    have hpow : (2 : ℝ) ^ (M + 3) = 2 ^ (M + 2) * 2 := by
      rw [show M + 3 = M + 2 + 1 by ring, pow_succ]
    rw [show M + 1 + 2 = M + 3 by ring, hpow]
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (M + 2) := by positivity
    field_simp
    ring

/-- The accumulated Borůvka error is at most 1/4. -/
theorem boruvkaError_le (M : ℕ) : boruvkaError M ≤ 1 / 4 := by
  rw [boruvkaError_eq]
  have : (0 : ℝ) < 1 / (2 : ℝ) ^ (M + 2) := by positivity
  linarith

/-- The square root of (1/2)^ℓ equals (1/√2)^ℓ. -/
theorem sqrt_half_pow (ℓ : ℕ) :
    Real.sqrt ((1 / 2 : ℝ) ^ ℓ) = (1 / Real.sqrt 2) ^ ℓ := by
  induction ℓ with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]
    congr 1
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one, one_div]

/-- The reciprocal of √2 is at most 3/4. -/
theorem inv_sqrt_two_le_three_quarters : (1 / Real.sqrt 2 : ℝ) ≤ 3 / 4 := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rw [div_le_iff₀ h2]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]

/-- The finite sum of (ℓ + 3)(3/4)^ℓ over ℓ < M equals 24 − (24 + 4M)(3/4)^M. -/
theorem boruvkaGeomSum_eq (M : ℕ) :
    (∑ ℓ ∈ Finset.range M, ((ℓ : ℝ) + 3) * (3 / 4 : ℝ) ^ ℓ) =
      24 - (24 + 4 * (M : ℝ)) * (3 / 4 : ℝ) ^ M := by
  induction M with
  | zero => norm_num
  | succ M ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    push_cast
    ring

/-- The finite sum of (ℓ + 3)(3/4)^ℓ is at most 24. -/
theorem boruvkaGeomSum_le (M : ℕ) :
    (∑ ℓ ∈ Finset.range M, ((ℓ : ℝ) + 3) * (3 / 4 : ℝ) ^ ℓ) ≤ 24 := by
  rw [boruvkaGeomSum_eq]
  have hpos : (0 : ℝ) ≤ (24 + 4 * (M : ℝ)) * (3 / 4 : ℝ) ^ M := by positivity
  linarith

/-- For nonnegative A, √(A/2^ℓ) equals √A times (1/√2)^ℓ. -/
theorem sqrt_div_pow_two (A : ℝ) (hA : 0 ≤ A) (ℓ : ℕ) :
    Real.sqrt (A / (2 : ℝ) ^ ℓ) = Real.sqrt A * (1 / Real.sqrt 2) ^ ℓ := by
  have hsplit : A / (2 : ℝ) ^ ℓ = A * (1 / 2 : ℝ) ^ ℓ := by
    rw [one_div_pow, div_eq_mul_one_div]
  rw [hsplit, Real.sqrt_mul hA, sqrt_half_pow]

/-- For every natural number i, 2i ≤ 2ⁱ. -/
theorem two_mul_le_two_pow (i : ℕ) : 2 * i ≤ 2 ^ i := by
  induction i with
  | zero => simp
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; norm_num
    · have h2k : (2 : ℕ) ≤ 2 ^ k := by
        calc (2 : ℕ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      calc 2 * (k + 1) = 2 * k + 2 := by ring
        _ ≤ 2 ^ k + 2 ^ k := by omega
        _ = 2 ^ (k + 1) := by rw [pow_succ]; ring

/-- For every natural number i, (1/2)^(2ⁱ)·2ⁱ is at most (1/2)ⁱ. -/
theorem half_pow_two_pow_mul_pow_two_le (i : ℕ) :
    (1 / 2 : ℝ) ^ (2 ^ i) * (2 : ℝ) ^ i ≤ (1 / 2 : ℝ) ^ i := by
  have h2i : 2 * i ≤ 2 ^ i := two_mul_le_two_pow i
  have hkey : (2 : ℝ) ^ (2 * i) ≤ (2 : ℝ) ^ (2 ^ i) :=
    pow_le_pow_right₀ (by norm_num) h2i
  have hsq : (2 : ℝ) ^ (2 * i) = (2 : ℝ) ^ i * (2 : ℝ) ^ i := by
    rw [two_mul, pow_add]
  rw [one_div_pow, one_div_pow]
  rw [show (1 : ℝ) / (2 : ℝ) ^ (2 ^ i) * (2 : ℝ) ^ i =
      (2 : ℝ) ^ i / (2 : ℝ) ^ (2 ^ i) by ring]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  rw [hsq] at hkey
  linarith

/-- Every finite initial sum of powers of 1/2 is at most 2. -/
theorem geom_half_sum_le (m : ℕ) :
    (∑ i ∈ Finset.range m, (1 / 2 : ℝ) ^ i) ≤ 2 := by
  have hgeom : (∑ i ∈ Finset.range m, (1 / 2 : ℝ) ^ i) =
      2 - 2 * (1 / 2 : ℝ) ^ m := by
    rw [geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
    field_simp
    ring
  rw [hgeom]
  have hpos : (0 : ℝ) ≤ 2 * (1 / 2 : ℝ) ^ m := by positivity
  linarith

/-- For every natural number i, 2^(3i/4) is at most 2ⁱ. -/
theorem rpow_two_three_quarters_le (i : ℕ) :
    Real.rpow 2 ((3 : ℝ) * i / 4) ≤ (2 : ℝ) ^ i := by
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    simp
  · have hexp : (3 : ℝ) * i / 4 ≤ (i : ℝ) := by
      have hi' : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
      nlinarith
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp
    have hnat : Real.rpow 2 ((i : ℕ) : ℝ) = (2 : ℝ) ^ i := Real.rpow_natCast 2 i
    calc Real.rpow 2 ((3 : ℝ) * i / 4) ≤ Real.rpow 2 ((i : ℕ) : ℝ) := h
      _ = (2 : ℝ) ^ i := hnat

/-- For n ≥ 1, the directed-tree error expression is at most 1/10. -/
theorem directedTreeError_le (n : ℕ) (hn : 1 ≤ n) : directedTreeError n ≤ 1 / 10 := by
  unfold directedTreeError
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 20 * n)]
  nlinarith

/-- Every tier failure expression is at most 1/3 [DurrEtAl2006]. -/
theorem tierFailure_le_third (i : ℕ) : tierFailure i ≤ 1 / 3 := by
  unfold tierFailure
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (2 ^ (i + 2)) := by positivity
  rw [div_le_iff₀ hpos]
  have hle : (3 : ℝ) * 2 ^ i ≤ (2 : ℝ) ^ (i + 2) := by
    have hone : (2 : ℝ) ^ (i + 2) = 4 * 2 ^ i := by
      rw [pow_add]
      norm_num
      ring
    rw [hone]
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) i]
  have hexp : i + 2 ≤ 2 ^ (i + 2) := by
    have := Nat.lt_two_pow_self (n := i + 2)
    omega
  have hmono : (2 : ℝ) ^ (i + 2) ≤ (2 : ℝ) ^ (2 ^ (i + 2)) :=
    pow_le_pow_right₀ (by norm_num) hexp
  linarith

end Qatlib.Papers.QQueryGraph04.MainResults.Model
