/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.BCHWordLog
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Positivity

/-!
# Eulerian weights for BCH coefficients

`betaCoefficient` is an alternating binomial sum whose factorial and binomial closed forms
determine logarithm weights of cut polynomials. The linear functional `logarithmWeight` applies
the alternating formal logarithm weights to polynomial coefficients.

The functions `descentWeight` and `phiWeight` package the resulting rational coefficients and
their reciprocal degree bounds for the BCH estimates in [AftabAnTrivisa2026].

## Main statements

* `betaCoefficient_factorial`: evaluates the alternating binomial sum.
* `logarithmWeight_cutPolynomial`: computes the logarithm weight of a cut polynomial.
* `abs_phiWeight_le`: bounds the bracket weight by the reciprocal squared positive degree.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.BCHEulerian
open scoped BigOperators

/-- The alternating binomial sum of reciprocals `a + j + 1` with binomial weights from degree
`b`. -/
def betaCoefficient (a b : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (b + 1), (b.choose j : ℚ) * ((-1 : ℚ) ^ j / (a + j + 1))

/-- Increasing the second beta coefficient index gives the difference of two neighboring beta
coefficients. -/
theorem betaCoefficient_succ (a b : ℕ) :
    betaCoefficient a (b + 1) = betaCoefficient a b - betaCoefficient (a + 1) b := by
  unfold betaCoefficient
  rw [Finset.sum_choose_succ_mul (fun i _ => (-1 : ℚ) ^ i / (a + i + 1)) b]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_succ]
  push_cast
  ring

/-- The beta coefficient equals `a! b! / (a + b + 1)!`. -/
theorem betaCoefficient_factorial (a b : ℕ) :
    betaCoefficient a b = (a.factorial : ℚ) * b.factorial / (a + b + 1).factorial := by
  induction b generalizing a with
  | zero =>
    simp only [betaCoefficient, zero_add, Finset.range_one, Finset.sum_singleton,
      Nat.choose_self, Nat.cast_one, pow_zero, add_zero, one_mul, Nat.factorial_zero,
      mul_one, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have ha : (a.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero a
    norm_num only [Nat.cast_zero, add_zero]
    field_simp
  | succ b ih =>
    rw [betaCoefficient_succ, ih, ih]
    have hn : a + (b + 1) + 1 = (a + b + 1) + 1 := by omega
    have hm : a + 1 + b + 1 = (a + b + 1) + 1 := by omega
    rw [hn, hm]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have ha : (a.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero a
    have hb : (b.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero b
    have hab : ((a + b).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (a + b)
    field_simp
    ring

/-- The beta coefficient is the reciprocal of the product of `a + b + 1` and the binomial
coefficient choosing `a` from `a + b`. -/
theorem betaCoefficient_choose (a b : ℕ) :
    betaCoefficient a b = 1 / ((a + b + 1 : ℚ) * ((a + b).choose a : ℚ)) := by
  rw [betaCoefficient_factorial, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hc : (a + b).choose a ≠ 0 := Nat.choose_ne_zero (Nat.le_add_right a b)
  have h : ((a + b).choose a : ℚ) * a.factorial * b.factorial = (a + b).factorial := by
    exact_mod_cast (by simpa only [Nat.add_sub_cancel_left] using
      Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right a b))
  have hab : ((a + b).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (a + b)
  have hc' : ((a + b).choose a : ℚ) ≠ 0 := by exact_mod_cast hc
  field_simp
  push_cast
  rw [← h]
  ring

/-- The rational linear functional assigning the formal logarithm weight `(-1)^(k - 1) / k` to a
monomial of degree `k`, with weight zero at degree zero. -/
def logarithmWeight : Polynomial ℚ →ₗ[ℚ] ℚ where
  toFun p := Finsupp.linearCombination ℚ (fun k : ℕ => (-1 : ℚ) ^ (k - 1) / (k : ℚ)) p.toFinsupp.coeff
  map_add' p q := map_add _ p.toFinsupp.coeff q.toFinsupp.coeff
  map_smul' c p := map_smul _ c p.toFinsupp.coeff

/-- A monomial of positive degree `k + 1` has logarithm weight equal to its coefficient times
`(-1)^k / (k + 1)`. -/
theorem logarithmWeight_monomial (k : ℕ) (c : ℚ) :
    logarithmWeight (Polynomial.monomial (k + 1) c) = c * ((-1 : ℚ) ^ k / (k + 1)) := by
  change Finsupp.linearCombination ℚ _ (Finsupp.single (k + 1) c) = _
  rw [Finsupp.linearCombination_single]
  simp only [Nat.add_sub_cancel, smul_eq_mul, Nat.cast_add, Nat.cast_one]

/-- For a polynomial of degree at most `n`, the logarithm weight is the finite weighted sum of
its positive degree coefficients. -/
theorem logarithmWeight_eq_sum (p : Polynomial ℚ) (n : ℕ) (hp : p.natDegree ≤ n) :
    logarithmWeight p = ∑ k ∈ Finset.range n, ((-1 : ℚ) ^ k / (k + 1)) * p.coeff (k + 1) := by
  change p.sum (fun k c => c * ((-1 : ℚ) ^ (k - 1) / (k : ℚ))) = _
  rw [Polynomial.sum_over_range' p
    (f := fun k c => c * ((-1 : ℚ) ^ (k - 1) / (k : ℚ)))
    (fun _ => zero_mul _) (n + 1) (by omega),
    Finset.sum_range_succ']
  simp only [Nat.add_sub_cancel, Nat.cast_zero, div_zero, mul_zero, add_zero,
    Nat.cast_add, Nat.cast_one]
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

/-- The polynomial `X^(a + 1) * (1 + X)^b` expands into monomials with binomial coefficients. -/
theorem cutPolynomial_expansion (a b : ℕ) :
    (Polynomial.X : Polynomial ℚ) ^ (a + 1) * (1 + Polynomial.X) ^ b =
      ∑ j ∈ Finset.range (b + 1), Polynomial.monomial (a + j + 1) (b.choose j : ℚ) := by
  rw [add_comm (1 : Polynomial ℚ) Polynomial.X, add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [one_pow, mul_one]
  rw [← Polynomial.C_mul_X_pow_eq_monomial, ← mul_assoc, ← pow_add]
  have hn : a + 1 + j = a + j + 1 := by omega
  rw [hn]
  simp only [Polynomial.C_eq_natCast]
  ring

/-- The logarithm weight of `X^(a + 1) * (1 + X)^b` is `(-1)^a` divided by the product of `a + b
+ 1` and the binomial coefficient choosing `a` from `a + b`. -/
theorem logarithmWeight_cutPolynomial (a b : ℕ) :
    logarithmWeight ((Polynomial.X : Polynomial ℚ) ^ (a + 1) * (1 + Polynomial.X) ^ b) =
      (-1 : ℚ) ^ a / ((a + b + 1 : ℚ) * ((a + b).choose a : ℚ)) := by
  rw [cutPolynomial_expansion, map_sum]
  simp only [logarithmWeight_monomial, pow_add, Nat.cast_add]
  have he : (∑ j ∈ Finset.range (b + 1), (b.choose j : ℚ) *
      ((-1 : ℚ) ^ a * (-1 : ℚ) ^ j / (a + j + 1))) =
      (-1 : ℚ) ^ a * betaCoefficient a b := by
    rw [betaCoefficient, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, betaCoefficient_choose]
  ring

/-- The rational descent weight `(-1)^d / (n * choose (n - 1) d)`. -/
def descentWeight (n d : ℕ) : ℚ :=
  (-1 : ℚ) ^ d / ((n : ℚ) * ((n - 1).choose d : ℚ))

/-- The rational bracket weight `(-1)^d / (n^2 * choose (n - 1) d)`. -/
def phiWeight (n d : ℕ) : ℚ :=
  (-1 : ℚ) ^ d / ((n : ℚ) ^ 2 * ((n - 1).choose d : ℚ))

/-- Dividing the descent weight by the degree gives the corresponding phi weight. -/
theorem descentWeight_div_degree (n d : ℕ) : descentWeight n d / (n : ℚ) = phiWeight n d := by
  rw [descentWeight, phiWeight, div_div]
  congr 1
  ring

/-- For a positive degree and a descent count below that degree, the absolute descent weight is
at most the reciprocal degree. -/
theorem abs_descentWeight_le (n d : ℕ) (hn : 0 < n) (hd : d < n) :
    |descentWeight n d| ≤ 1 / (n : ℚ) := by
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have hc : 0 < (n - 1).choose d := Nat.choose_pos (by omega)
  have hc' : (0 : ℚ) < (n - 1).choose d := by exact_mod_cast hc
  have hc1 : (1 : ℚ) ≤ (n - 1).choose d := by exact_mod_cast hc
  rw [descentWeight, abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_mul,
    abs_of_pos hn', abs_of_pos hc']
  exact one_div_le_one_div_of_le hn' (le_mul_of_one_le_right hn'.le hc1)

/-- For a positive degree and a descent count below that degree, the absolute phi weight is at
most the reciprocal squared degree. -/
theorem abs_phiWeight_le (n d : ℕ) (hn : 0 < n) (hd : d < n) :
    |phiWeight n d| ≤ 1 / (n : ℚ) ^ 2 := by
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have hc : 0 < (n - 1).choose d := Nat.choose_pos (by omega)
  have hc' : (0 : ℚ) < (n - 1).choose d := by exact_mod_cast hc
  have hc1 : (1 : ℚ) ≤ (n - 1).choose d := by exact_mod_cast hc
  rw [phiWeight, abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_mul,
    abs_pow, abs_of_pos hn', abs_of_pos hc']
  exact one_div_le_one_div_of_le (sq_pos_of_pos hn') (le_mul_of_one_le_right (sq_nonneg _) hc1)

/-- The phi weight for zero descents is the reciprocal squared degree. -/
theorem phiWeight_zero (n : ℕ) : phiWeight n 0 = 1 / (n : ℚ) ^ 2 := by
  simp only [phiWeight, pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]

end Qatlib.Papers.CommutLCHS26.MainResults.BCHEulerian
