/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Choose.Basic

/-!
# Hypergeometric path coefficient identities

Proves terminating Gauss hypergeometric expansions with nonpositive integer upper parameters and
lower parameter one or two. The final identity `even_binomial_sum_gauss` rewrites a shifted
binomial sum in hypergeometric form, for path coefficient calculations in lattice dynamics
associated with [Meyer1996a].

## Main statements

* `gauss_negative_nat_finite_sum`: expands the lower-parameter-one function as a finite binomial
  sum.
* `gauss_negative_nat_finite_sum_two`: gives the corresponding lower-parameter-two expansion.
* `even_binomial_sum_gauss`: rewrites the shifted even-path binomial sum.

## References

* [Meyer, 1996][Meyer1996a]
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
noncomputable section
open Complex
open scoped BigOperators

namespace Qatlib.Concepts.QcaDynamics.PathCoeffs

/-- The rising factorial evaluated at `-n` equals `(-1) ^ k` times `k!` times the binomial
coefficient `n.choose k`. -/
theorem negative_pochhammer_choose (n k : ℕ) :
    (ascPochhammer ℂ k).eval (-(n : ℂ)) =
      (-1 : ℂ)^k * (k.factorial : ℂ) * (n.choose k : ℂ) := by
  rw [ascPochhammer_eval_neg_eq_descPochhammer,
    descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  ring

/-- A Gauss hypergeometric function with a zero upper parameter equals one. -/
theorem hypergeometric_zero_upper (b c z : ℂ) : ₂F₁ (0 : ℂ) b c z = 1 := by
  rw [ordinaryHypergeometric_eq_tsum]
  (try dsimp only)
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    simp [hn]

/-- For upper parameters `-n` and `-m` and lower parameter one, the hypergeometric coefficient
of degree `j` is the product of the two binomial coefficients. -/
theorem gauss_negative_nat_coefficient (n m j : ℕ) :
    ordinaryHypergeometricCoefficient (-(n:ℂ)) (-(m:ℂ)) 1 j =
      (n.choose j : ℂ) * (m.choose j : ℂ) := by
  unfold ordinaryHypergeometricCoefficient
  rw [negative_pochhammer_choose, negative_pochhammer_choose, ascPochhammer_eval_one]
  have hf : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  calc
    _ = ((-1:ℂ)^j * (-1:ℂ)^j) * ((n.choose j : ℂ)*(m.choose j : ℂ)) := by
      field_simp
    _ = _ := by rw [← mul_pow]; norm_num

/-- The Gauss hypergeometric function with upper parameters `-n`, `-m` and lower parameter one
is its finite binomial expansion through degree `min n m`. -/
theorem gauss_negative_nat_finite_sum (n m : ℕ) (z : ℂ) :
    ₂F₁ (-(n:ℂ)) (-(m:ℂ)) 1 z =
      ∑ j ∈ Finset.range (min n m + 1), (n.choose j : ℂ)*(m.choose j : ℂ)*z^j := by
  rw [ordinaryHypergeometric_eq_tsum]
  (try dsimp only)
  change (∑' j, ordinaryHypergeometricCoefficient (-(n:ℂ)) (-(m:ℂ)) 1 j * z^j) = _
  simp_rw [gauss_negative_nat_coefficient]
  apply tsum_eq_sum
  intro j hj
  have hj' : min n m < j := by simpa only [Finset.mem_range, not_lt] using! hj
  rcases min_lt_iff.mp hj' with hn | hm
  · simp [Nat.choose_eq_zero_of_lt hn]
  · simp [Nat.choose_eq_zero_of_lt hm]

/-- For upper parameters `-n`, `-m` and lower parameter two, the degree `j` coefficient is the
product of the binomial coefficients divided by `j + 1`. -/
theorem gauss_negative_nat_coefficient_two (n m j : ℕ) :
    ordinaryHypergeometricCoefficient (-(n:ℂ)) (-(m:ℂ)) 2 j =
      (n.choose j : ℂ) * (m.choose j : ℂ) / ((j+1:ℕ):ℂ) := by
  have hp2 : (ascPochhammer ℂ j).eval 2 = ((j+1).factorial : ℂ) := by
    simpa only [Nat.factorial_one, Nat.cast_one, one_mul, Nat.cast_one, one_add_one_eq_two,
      Nat.add_comm 1 j] using factorial_mul_ascPochhammer ℂ 1 j
  unfold ordinaryHypergeometricCoefficient
  rw [negative_pochhammer_choose, negative_pochhammer_choose, hp2, Nat.factorial_succ]
  push_cast
  have hf : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hj : ((j:ℂ)+1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  calc
    _ = ((-1:ℂ)^j * (-1:ℂ)^j) *
      ((n.choose j : ℂ)*(m.choose j : ℂ)) / ((j:ℂ)+1) := by
      field_simp
    _ = _ := by rw [← mul_pow]; norm_num

/-- The Gauss hypergeometric function with upper parameters `-n`, `-m` and lower parameter two
is the finite sum with coefficients `(n.choose j) * (m.choose j) / (j + 1)`. -/
theorem gauss_negative_nat_finite_sum_two (n m : ℕ) (z : ℂ) :
    ₂F₁ (-(n:ℂ)) (-(m:ℂ)) 2 z =
      ∑ j ∈ Finset.range (min n m + 1),
        ((n.choose j : ℂ)*(m.choose j : ℂ)/((j+1:ℕ):ℂ))*z^j := by
  rw [ordinaryHypergeometric_eq_tsum]
  (try dsimp only)
  change (∑' j, ordinaryHypergeometricCoefficient (-(n:ℂ)) (-(m:ℂ)) 2 j * z^j) = _
  simp_rw [gauss_negative_nat_coefficient_two]
  apply tsum_eq_sum
  intro j hj
  have hj' : min n m < j := by simpa only [Finset.mem_range, not_lt] using! hj
  rcases min_lt_iff.mp hj' with hn | hm
  · simp [Nat.choose_eq_zero_of_lt hn]
  · simp [Nat.choose_eq_zero_of_lt hm]

/-- For positive `u`, expresses the complex cast of `u.choose (j + 1)` as `u` times `(u -
1).choose j` divided by `j + 1`. -/
theorem choose_succ_complex (u j : ℕ) (hu : 1 ≤ u) :
    (u.choose (j+1) : ℂ) =
      (u:ℂ) * ((u-1).choose j : ℂ) / ((j:ℂ)+1) := by
  have hu' : u-1+1 = u := by omega
  have hnat := Nat.add_one_mul_choose_eq (u-1) j
  rw [hu'] at hnat
  apply (eq_div_iff (by exact_mod_cast Nat.succ_ne_zero j)).mpr
  exact_mod_cast hnat.symm

/-- For positive `u` and `v`, the ranges ending at `min u v` and at `min (u - 1) (v - 1) + 1`
coincide. -/
theorem even_gauss_range (u v : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v) :
    Finset.range (min u v) = Finset.range (min (u-1) (v-1) + 1) := by
  congr 1
  omega

/-- For positive `u` and `v`, rewrites the shifted binomial sum as `u * z` times the Gauss
hypergeometric function with upper parameters `1 - u`, `1 - v` and lower parameter two. -/
theorem even_binomial_sum_gauss (u v : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v) (z : ℂ) :
    (∑ j ∈ Finset.range (min u v),
      (u.choose (j+1):ℂ)*((v-1).choose j:ℂ)*z^(j+1)) =
      (u:ℂ)*z*₂F₁ (-((u-1:ℕ):ℂ)) (-((v-1:ℕ):ℂ)) 2 z := by
  rw [gauss_negative_nat_finite_sum_two, even_gauss_range u v hu hv,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [choose_succ_complex u j hu, pow_succ]
  push_cast
  ring

end Qatlib.Concepts.QcaDynamics.PathCoeffs
