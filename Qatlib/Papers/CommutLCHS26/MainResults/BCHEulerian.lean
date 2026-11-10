/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.BCHWordLog
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Positivity
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.BCHEulerian
open scoped BigOperators

def betaCoefficient (a b : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (b + 1), (b.choose j : ℚ) * ((-1 : ℚ) ^ j / (a + j + 1))

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

def logarithmWeight : Polynomial ℚ →ₗ[ℚ] ℚ where
  toFun p := Finsupp.linearCombination ℚ (fun k : ℕ => (-1 : ℚ) ^ (k - 1) / (k : ℚ)) p.toFinsupp.coeff
  map_add' p q := map_add _ p.toFinsupp.coeff q.toFinsupp.coeff
  map_smul' c p := map_smul _ c p.toFinsupp.coeff

theorem logarithmWeight_monomial (k : ℕ) (c : ℚ) :
    logarithmWeight (Polynomial.monomial (k + 1) c) = c * ((-1 : ℚ) ^ k / (k + 1)) := by
  change Finsupp.linearCombination ℚ _ (Finsupp.single (k + 1) c) = _
  rw [Finsupp.linearCombination_single]
  simp only [Nat.add_sub_cancel, smul_eq_mul, Nat.cast_add, Nat.cast_one]

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

def descentWeight (n d : ℕ) : ℚ :=
  (-1 : ℚ) ^ d / ((n : ℚ) * ((n - 1).choose d : ℚ))

def phiWeight (n d : ℕ) : ℚ :=
  (-1 : ℚ) ^ d / ((n : ℚ) ^ 2 * ((n - 1).choose d : ℚ))

theorem descentWeight_div_degree (n d : ℕ) : descentWeight n d / (n : ℚ) = phiWeight n d := by
  rw [descentWeight, phiWeight, div_div]
  congr 1
  ring

theorem abs_descentWeight_le (n d : ℕ) (hn : 0 < n) (hd : d < n) :
    |descentWeight n d| ≤ 1 / (n : ℚ) := by
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have hc : 0 < (n - 1).choose d := Nat.choose_pos (by omega)
  have hc' : (0 : ℚ) < (n - 1).choose d := by exact_mod_cast hc
  have hc1 : (1 : ℚ) ≤ (n - 1).choose d := by exact_mod_cast hc
  rw [descentWeight, abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_mul,
    abs_of_pos hn', abs_of_pos hc']
  exact one_div_le_one_div_of_le hn' (le_mul_of_one_le_right hn'.le hc1)

theorem abs_phiWeight_le (n d : ℕ) (hn : 0 < n) (hd : d < n) :
    |phiWeight n d| ≤ 1 / (n : ℚ) ^ 2 := by
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have hc : 0 < (n - 1).choose d := Nat.choose_pos (by omega)
  have hc' : (0 : ℚ) < (n - 1).choose d := by exact_mod_cast hc
  have hc1 : (1 : ℚ) ≤ (n - 1).choose d := by exact_mod_cast hc
  rw [phiWeight, abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_mul,
    abs_pow, abs_of_pos hn', abs_of_pos hc']
  exact one_div_le_one_div_of_le (sq_pos_of_pos hn') (le_mul_of_one_le_right (sq_nonneg _) hc1)

theorem phiWeight_zero (n : ℕ) : phiWeight n 0 = 1 / (n : ℚ) ^ 2 := by
  simp only [phiWeight, pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]

end Qatlib.Papers.CommutLCHS26.MainResults.BCHEulerian
