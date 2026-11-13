/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QcaDynamics.PathCoeffs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finsupp.Basic

/-!
# Path sums and hypergeometric propagators

This module defines the odd and even path amplitudes and their finite binomially weighted sums.
For nonzero cosine and the stated positive light-cone coordinates, it rewrites these sums as
terminating Gauss hypergeometric expressions. See [Meyer1996a].

## Main statements

* `pathSumOdd_eq_hypergeometric`: For `u ≥ 1` and `cos θ ≠ 0`, the odd path sum equals the
  stated Gauss hypergeometric expression with parameters `1 - u`, `-v`, and one at argument
  `-tan² θ`.
* `pathSumEven_eq_hypergeometric`: For `u, v ≥ 1` and `cos θ ≠ 0`, the even path sum equals the
  stated Gauss hypergeometric expression with parameters `1 - u`, `1 - v`, and two at argument
  `-tan² θ`.

## References

* [Meyer, 1996][Meyer1996a]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Complex

open Qatlib.Concepts.QcaDynamics.PathCoeffs

namespace Qatlib.Papers.QCellAutomata96.MainResults

/-- For `c ≠ 0` and `n ≤ m`, factor `(a * b)^n * c^(m - n)` as `c^m * (a * (b / c))^n`. -/
lemma factor_pow {a b c : ℂ} {n m : ℕ} (hc : c ≠ 0) (h : n ≤ m) :
    (a * b) ^ n * c ^ (m - n) = c ^ m * (a * (b / c)) ^ n := by
  have hbc : b ^ n = (b / c) ^ n * c ^ n := by
    rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero n hc)]
  calc
    (a * b) ^ n * c ^ (m - n) = (a ^ n * b ^ n) * c ^ (m - n) := by rw [mul_pow]
    _ = a ^ n * ((b / c) ^ n * c ^ n) * c ^ (m - n) := by rw [hbc]
    _ = a ^ n * (b / c) ^ n * (c ^ n * c ^ (m - n)) := by ring
    _ = a ^ n * (b / c) ^ n * c ^ m := by
      rw [← pow_add, Nat.add_sub_of_le h]
    _ = c ^ m * (a * (b / c)) ^ n := by rw [mul_pow]; ring

/-- The path amplitude with `2 * k - 1` sine factors and the remaining cosine factors. -/
def oddAmp (θ : ℝ) (u v k : ℕ) : ℂ :=
  (I * (Real.sin θ : ℂ)) ^ (2 * k - 1) * (Real.cos θ : ℂ) ^ (u + v - (2 * k - 1))

/-- The path amplitude with `2 * k` sine factors and the remaining cosine factors. -/
def evenAmp (θ : ℝ) (u v k : ℕ) : ℂ :=
  (I * (Real.sin θ : ℂ)) ^ (2 * k) * (Real.cos θ : ℂ) ^ (u + v - 2 * k)

/-- When `cos θ ≠ 0` and `2 * k - 1 ≤ u + v`, the odd amplitude factors into `cos θ^(u + v)`
times `(i * tan θ)^(2 * k - 1)`. -/
theorem oddAmp_factor (θ : ℝ) (u v k : ℕ) (h : 2 * k - 1 ≤ u + v) (hc : Real.cos θ ≠ 0) :
    oddAmp θ u v k =
      (Real.cos θ : ℂ) ^ (u + v) * (I * (Real.tan θ : ℂ)) ^ (2 * k - 1) := by
  unfold oddAmp
  have hc' : (Real.cos θ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  have htan : I * ((Real.sin θ : ℂ) / (Real.cos θ : ℂ)) = I * (Real.tan θ : ℂ) := by
    rw [Real.tan_eq_sin_div_cos]
    push_cast
    ring
  rw [factor_pow (a := I) (b := (Real.sin θ : ℂ)) (c := (Real.cos θ : ℂ)) hc' h]
  rw [htan]

/-- When `cos θ ≠ 0` and `2 * k ≤ u + v`, the even amplitude factors into `cos θ^(u + v)` times
`(i * tan θ)^(2 * k)`. -/
theorem evenAmp_factor (θ : ℝ) (u v k : ℕ)
    (h : 2 * k ≤ u + v) (hc : Real.cos θ ≠ 0) :
    evenAmp θ u v k =
      (Real.cos θ : ℂ) ^ (u + v) * (I * (Real.tan θ : ℂ)) ^ (2 * k) := by
  unfold evenAmp
  have hc' : (Real.cos θ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  have htan : I * ((Real.sin θ : ℂ) / (Real.cos θ : ℂ)) = I * (Real.tan θ : ℂ) := by
    rw [Real.tan_eq_sin_div_cos]
    push_cast
    ring
  rw [factor_pow (a := I) (b := (Real.sin θ : ℂ)) (c := (Real.cos θ : ℂ)) hc' h]
  rw [htan]

/-- The finite sum of odd path amplitudes weighted by the binomial multiplicity `choose (u - 1)
k * choose v k`. -/
def pathSumOdd (θ : ℝ) (u v : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (min u (v + 1)),
    ((Nat.choose (u - 1) k : ℂ) * (Nat.choose v k : ℂ)) * oddAmp θ u v (k + 1)

/-- The finite sum of even path amplitudes weighted by the binomial multiplicity `choose u (k +
1) * choose (v - 1) k`. -/
def pathSumEven (θ : ℝ) (u v : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (min u v),
    ((Nat.choose u (k + 1) : ℂ) * (Nat.choose (v - 1) k : ℂ)) * evenAmp θ u v (k + 1)

/-- For `u ≥ 1` and `cos θ ≠ 0`, the odd path sum equals the stated Gauss hypergeometric
expression with parameters `1 - u`, `-v`, and one at argument `-tan² θ`. See [Meyer1996a]. -/
theorem pathSumOdd_eq_hypergeometric (θ : ℝ) (u v : ℕ) (hu : 1 ≤ u)
    (hc : Real.cos θ ≠ 0) :
    pathSumOdd θ u v =
      (Real.cos θ : ℂ) ^ (u + v) * (I * (Real.tan θ : ℂ)) *
        ₂F₁ (1 - (u : ℂ)) (-(v : ℂ)) 1 (-((Real.tan θ : ℂ) ^ 2)) := by
  have hparam : 1 - (u : ℂ) = -((u - 1 : ℕ) : ℂ) := by
    rw [Nat.cast_sub hu]
    push_cast
    ring
  have hrange : min (u - 1) v + 1 = min u (v + 1) := by omega
  have hphase : (I * (Real.tan θ : ℂ)) ^ 2 = -((Real.tan θ : ℂ) ^ 2) := by
    rw [mul_pow]
    norm_num
  rw [hparam, gauss_negative_nat_finite_sum, hrange, Finset.mul_sum]
  unfold pathSumOdd
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  have hpow : 2 * (j + 1) - 1 ≤ u + v := by omega
  rw [oddAmp_factor θ u v (j + 1) hpow hc,
    show 2 * (j + 1) - 1 = 2 * j + 1 by omega, pow_succ, pow_mul, hphase]
  ring

/-- For `u, v ≥ 1` and `cos θ ≠ 0`, the even path sum equals the stated Gauss hypergeometric
expression with parameters `1 - u`, `1 - v`, and two at argument `-tan² θ`. See
[Meyer1996a]. -/
theorem pathSumEven_eq_hypergeometric (θ : ℝ) (u v : ℕ) (hu : 1 ≤ u)
    (hv : 1 ≤ v) (hc : Real.cos θ ≠ 0) :
    pathSumEven θ u v =
      (Real.cos θ : ℂ) ^ (u + v) * (-((u : ℂ) * (Real.tan θ : ℂ) ^ 2)) *
        ₂F₁ (1 - (u : ℂ)) (1 - (v : ℂ)) 2 (-((Real.tan θ : ℂ) ^ 2)) := by
  have hparamu : 1 - (u : ℂ) = -((u - 1 : ℕ) : ℂ) := by
    rw [Nat.cast_sub hu]
    push_cast
    ring
  have hparamv : 1 - (v : ℂ) = -((v - 1 : ℕ) : ℂ) := by
    rw [Nat.cast_sub hv]
    push_cast
    ring
  have hphase : (I * (Real.tan θ : ℂ)) ^ 2 = -((Real.tan θ : ℂ) ^ 2) := by
    rw [mul_pow]
    norm_num
  have hpath : pathSumEven θ u v = (Real.cos θ : ℂ) ^ (u + v) *
      (∑ j ∈ Finset.range (min u v), (u.choose (j + 1) : ℂ) *
        ((v - 1).choose j : ℂ) * (-((Real.tan θ : ℂ) ^ 2)) ^ (j + 1)) := by
    unfold pathSumEven
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hpow : 2 * (j + 1) ≤ u + v := by omega
    rw [evenAmp_factor θ u v (j + 1) hpow hc, pow_mul, hphase]
    ring
  rw [hpath, even_binomial_sum_gauss u v hu hv, hparamu, hparamv]
  ring

/-- Every complex linear map on finitely supported lattice sequences preserves superpositions of
the form `φ + c • ψ`. -/
theorem linearMap_superposition (E : (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ →₀ ℂ)) :
    ∀ (φ ψ : ℤ →₀ ℂ) (c : ℂ), E (φ + c • ψ) = E φ + c • E ψ := by
  intro φ ψ c
  rw [map_add, map_smul]

end Qatlib.Papers.QCellAutomata96.MainResults
