/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

set_option backward.isDefEq.respectTransparency false

/-!
# Elementary Variance Decomposition and Exponential-Series Lower Bound

This module formalizes Lemma 4 (law of total variance on finite product distributions) and Lemma 2
(the `(1 - 1 / x)^x` power-series lower bound for `1 < |x|`) from the supplementary material of
[Rudolph et al., 2024][RudolphEtAl2024].

## Main statements

* `prodLaw`, `prodLaw_expect`, `prodLaw_meanSq`: product law of two `FinDist` laws and its
  iterated moments.
* `variance_eq_meanSq_sub_sq`, `lemma4_total_variance`: finite variance identity and law of total
  variance.
* `lemma2_one_sub_inv_pow_lower`: lower bound `(1 - 1 / x)^x ≥ (1 / e) * (1 - ∑' j, 1 / ((j + 2) * x^(j + 1)))`
  for `1 < |x|`.

## References

* [Rudolph et al., 2024][RudolphEtAl2024]
-/

set_option autoImplicit false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.Trainability23.VarianceScaling.Elementary

open scoped BigOperators

/-- The product of two finite laws, `(p × q) (a,b) = p a * q b`. This is the finite model of the
independent parameter blocks `α` and `β` in Lemma 4. -/
noncomputable def prodLaw {A B : Type*} [Fintype A] [Fintype B]
    (p : FinDist A) (q : FinDist B) : FinDist (A × B) where
  prob z := p.prob z.1 * q.prob z.2
  nonneg z := mul_nonneg (p.nonneg z.1) (q.nonneg z.2)
  sum_one := by
    rw [Fintype.sum_prod_type]
    have h : ∀ a, ∑ b : B, p.prob a * q.prob b = p.prob a := by
      intro a
      rw [← Finset.mul_sum, q.sum_one, mul_one]
    rw [Finset.sum_congr rfl (fun a _ => h a), p.sum_one]

/-- The expectation of a function of the product pair, written as the iterated expectation. -/
theorem prodLaw_expect {A B : Type*} [Fintype A] [Fintype B]
    (p : FinDist A) (q : FinDist B) (f : A × B → ℝ) :
    (prodLaw p q).expect f = ∑ a, p.prob a * ∑ b, q.prob b * f (a, b) := by
  unfold FinDist.expect
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [prodLaw]
  ring

/-- The sum form of `prodLaw_expect`: the first moment as an explicit double sum. -/
theorem prodLaw_sum {A B : Type*} [Fintype A] [Fintype B]
    (p : FinDist A) (q : FinDist B) (f : A × B → ℝ) :
    ∑ z : A × B, (prodLaw p q).prob z * f z
      = ∑ a, p.prob a * ∑ b, q.prob b * f (a, b) := by
  simpa only [FinDist.expect] using prodLaw_expect p q f

/-- The second moment of a function of the product pair, written as the iterated second moment. -/
theorem prodLaw_meanSq {A B : Type*} [Fintype A] [Fintype B]
    (p : FinDist A) (q : FinDist B) (f : A × B → ℝ) :
    ∑ z : A × B, (prodLaw p q).prob z * (f z) ^ 2
      = ∑ a, p.prob a * ∑ b, q.prob b * (f (a, b)) ^ 2 := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [prodLaw]
  ring

/-- Mean-square form of the finite variance: `Var = E[f²] - (E[f])²`. -/
theorem variance_eq_meanSq_sub_sq {X : Type*} [Fintype X] (p : FinDist X) (f : X → ℝ) :
    p.variance f = (∑ x, p.prob x * (f x) ^ 2) - (p.expect f) ^ 2 := by
  have hpt : ∀ x : X, p.prob x * (f x - p.expect f) ^ 2
      = p.prob x * (f x) ^ 2 - 2 * p.expect f * (p.prob x * f x)
        + (p.expect f) ^ 2 * p.prob x := fun x => by ring
  have h1 : ∑ x, 2 * p.expect f * (p.prob x * f x) = 2 * p.expect f * p.expect f := by
    rw [← Finset.mul_sum]
    rfl
  have h2 : ∑ x, (p.expect f) ^ 2 * p.prob x = (p.expect f) ^ 2 := by
    rw [← Finset.mul_sum, p.sum_one, mul_one]
  calc p.variance f
      = ∑ x, p.prob x * (f x - p.expect f) ^ 2 := rfl
    _ = ∑ x, (p.prob x * (f x) ^ 2 - 2 * p.expect f * (p.prob x * f x)
          + (p.expect f) ^ 2 * p.prob x) := Finset.sum_congr rfl fun x _ => hpt x
    _ = (∑ x, p.prob x * (f x) ^ 2) - 2 * p.expect f * p.expect f + (p.expect f) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, h1, h2]
    _ = (∑ x, p.prob x * (f x) ^ 2) - (p.expect f) ^ 2 := by ring

/-- **Lemma 4, Eq. (354)**. For `f (α, β)` on independent finite blocks with product law,
`Var_{(α,β)} f = E_α [Var_β f] + Var_α [E_β f]`. -/
theorem lemma4_total_variance {A B : Type*} [Fintype A] [Fintype B]
    (p : FinDist A) (q : FinDist B) (f : A × B → ℝ) :
    (prodLaw p q).variance f
      = (∑ a, p.prob a * q.variance (fun b => f (a, b)))
        + p.variance (fun a => ∑ b, q.prob b * f (a, b)) := by
  have hsplit : ∑ a, p.prob a * ((∑ b, q.prob b * (f (a, b)) ^ 2)
        - (∑ b, q.prob b * f (a, b)) ^ 2)
      = (∑ a, p.prob a * ∑ b, q.prob b * (f (a, b)) ^ 2)
        - ∑ a, p.prob a * (∑ b, q.prob b * f (a, b)) ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  simp only [variance_eq_meanSq_sub_sq, prodLaw_meanSq, prodLaw_sum, FinDist.expect]
  rw [hsplit]
  ring

/-- **Lemma 2, Eq. (275)**. For real `x` with `1 < |x|`, the elementary lower bound
`(1 - 1/x)^x ≥ (1/e)(1 - Σ_{j≥1} 1/((j+1) x^j))`. -/
theorem lemma2_one_sub_inv_pow_lower (x : ℝ) (hx : 1 < |x|) :
    Real.rpow (1 - 1 / x) x ≥
      (1 / Real.exp 1) * (1 - ∑' j : ℕ, 1 / (((j : ℝ) + 2) * x ^ (j + 1))) := by
  have hx0 : x ≠ 0 := abs_pos.mp (lt_trans zero_lt_one hx)
  have hy : |1 / x| < 1 := by
    rw [abs_div, abs_one]
    exact (div_lt_one (lt_trans zero_lt_one hx)).mpr hx
  have hpos : 0 < 1 - 1 / x := sub_pos.mpr (abs_lt.mp hy).2
  have htail : HasSum (fun j : ℕ => (1 / x) ^ (j + 2) / ((j : ℝ) + 2))
      (-Real.log (1 - 1 / x) - 1 / x) := by
    simpa [Finset.sum_range_one, Nat.cast_add, Nat.cast_one, Nat.add_assoc, add_assoc,
      one_add_one_eq_two] using
      (hasSum_nat_add_iff' 1).mpr (Real.hasSum_pow_div_log_of_abs_lt_one hy)
  have hseries : HasSum (fun j : ℕ => 1 / (((j : ℝ) + 2) * x ^ (j + 1)))
      (-x * Real.log (1 - 1 / x) - 1) := by
    convert htail.mul_left x using 1
    · ext j
      simp only [one_div_pow, pow_succ]
      field_simp [hx0]
    · field_simp [hx0]
  have hlog : Real.log (1 - 1 / x) * x =
      -1 - ∑' j : ℕ, 1 / (((j : ℝ) + 2) * x ^ (j + 1)) := by
    linarith [hseries.tsum_eq]
  change (1 - 1 / x) ^ x ≥ _
  rw [Real.rpow_def_of_pos hpos, hlog, sub_eq_add_neg, Real.exp_add,
    Real.exp_neg, ← one_div]
  apply mul_le_mul_of_nonneg_left _ (le_of_lt (one_div_pos.mpr (Real.exp_pos 1)))
  linarith [Real.add_one_le_exp (-∑' j : ℕ, 1 / (((j : ℝ) + 2) * x ^ (j + 1)))]

end Qatlib.Papers.Trainability23.VarianceScaling.Elementary
