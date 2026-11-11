/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.SharpMarkovHelpers
import Mathlib.Tactic.IntervalCases
import Qatlib.Concepts.QueryComplexity.DegreeMethod.SharpMarkovBernstein
import Qatlib.Concepts.QueryComplexity.DegreeMethod.SharpMarkovLobatto
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Sharp Markov derivative bound

This module proves the sharp inequality `|p'(x)| ≤ d ^ 2 * C` for a real polynomial of
degree at most `d` bounded in absolute value by `C` on `[-1, 1]`.
This is the Markov estimate recorded in [NayakWu1998].

The proof combines explicit low-degree interpolation, the algebraic Bernstein bound,
and Chebyshev–Lobatto estimates near the endpoints.

## Main statements

* `sharp_markov_cubic_derivative_identity`: four-node interpolation of a cubic derivative.
* `sharp_markov_degree_three`: the cubic bound with constant nine.
* `sharp_markov_derivative`: the sharp bound for every degree.

## References

* [Nayak and Wu, 1998, Fact A.5][NayakWu1998]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

/-- The sum of the absolute values of the four specified cubic derivative interpolation weights
is at most nine on `[-1, 1]`. -/
theorem sharp_markov_cubic_weight_sum (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(-2 * x^2 + 4/3*x + 1/6)| + |4*x^2 - 4/3*x - 4/3| +
      |-4*x^2 - 4/3*x + 4/3| + |2*x^2 + 4/3*x - 1/6| ≤ 9 := by
  have hsq : x^2 ≤ 1 := by nlinarith [hx.1,hx.2]
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> nlinarith [hx.1,hx.2,sq_nonneg x,sq_nonneg (x-1/6),sq_nonneg (x+1/6)]

/-- For a polynomial of degree at most three, its derivative is the specified weighted
combination of its values at `-1`, `-1 / 2`, `1 / 2`, and `1`. -/
theorem sharp_markov_cubic_derivative_identity (p : Polynomial ℝ)
    (hd : p.natDegree ≤ 3) (x : ℝ) :
    p.derivative.eval x =
      (-2*x^2 + 4/3*x + 1/6) * p.eval (-1) +
      (4*x^2 - 4/3*x - 4/3) * p.eval (-1/2) +
      (-4*x^2 - 4/3*x + 4/3) * p.eval (1/2) +
      (2*x^2 + 4/3*x - 1/6) * p.eval 1 := by
  rw [p.as_sum_range_C_mul_X_pow' (show p.natDegree < 4 by omega)]
  norm_num [Finset.sum_range_succ, Polynomial.derivative_mul, Polynomial.derivative_pow]
  ring

/-- A polynomial of degree at most three bounded by `C ≥ 0` on `[-1, 1]` has derivative bounded
there by `9 * C`. -/
theorem sharp_markov_degree_three (p : Polynomial ℝ) (hd : p.natDegree ≤ 3)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ C)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) : |p.derivative.eval x| ≤ 9*C := by
  have h1 := hb (-1) (by norm_num)
  have h2 := hb (-1/2) (by norm_num)
  have h3 := hb (1/2) (by norm_num)
  have h4 := hb 1 (by norm_num)
  rw [sharp_markov_cubic_derivative_identity p hd x]
  calc
    _ ≤ |(-2*x^2 + 4/3*x + 1/6) * p.eval (-1)| +
        |(4*x^2 - 4/3*x - 4/3) * p.eval (-1/2)| +
        |(-4*x^2 - 4/3*x + 4/3) * p.eval (1/2)| +
        |(2*x^2 + 4/3*x - 1/6) * p.eval 1| := by
      exact (abs_add_le _ _).trans
        (add_le_add ((abs_add_le _ _).trans
          (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    _ ≤ |(-2*x^2 + 4/3*x + 1/6)| * C + |4*x^2 - 4/3*x - 4/3| * C +
        |-4*x^2 - 4/3*x + 4/3| * C + |2*x^2 + 4/3*x - 1/6| * C := by
      simp only [abs_mul]
      gcongr
    _ ≤ 9*C := by
      rw [← add_mul, ← add_mul, ← add_mul]
      exact mul_le_mul_of_nonneg_right (sharp_markov_cubic_weight_sum x hx) hC

/-- If a polynomial has degree at most both `d` and three and is bounded by `C ≥ 0` on `[-1,
1]`, its derivative is bounded there by `d ^ 2 * C`. -/
theorem sharp_markov_of_degree_le_three (d : ℕ) (p : Polynomial ℝ) (C : ℝ)
    (hd : p.natDegree ≤ d) (h3 : p.natDegree ≤ 3) (hC : 0 ≤ C)
    (hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ C)
    (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |p.derivative.eval x| ≤ (d : ℝ)^2 * C := by
  by_cases h : 3 ≤ d
  · have hr : (3 : ℝ) ≤ d := by exact_mod_cast h
    exact (sharp_markov_degree_three p h3 hC hb hx).trans
      (mul_le_mul_of_nonneg_right (by nlinarith : (9 : ℝ) ≤ (d : ℝ)^2) hC)
  · interval_cases d
    · simp [sharp_markov_degree_zero p hd x]
    · simpa using sharp_markov_degree_one p hd hC hb x
    · convert sharp_markov_degree_two p hd hC hb hx using 1
      norm_num

/-- A real polynomial of degree at most `d` bounded by `C ≥ 0` on `[-1, 1]` has derivative
bounded there by `d ^ 2 * C`. See [Nayak and Wu, Fact A.5][NayakWu1998]. -/
theorem sharp_markov_derivative (d : ℕ) (p : Polynomial ℝ) (C : ℝ)
    (hdeg : p.natDegree ≤ d) (hC : 0 ≤ C)
    (hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ C)
    (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |p.derivative.eval x| ≤ (d : ℝ) ^ 2 * C := by
  by_cases hd0 : d = 0
  · subst d
    rw [sharp_markov_degree_zero p hdeg x]
    simp
  have hd : 1 ≤ d := by omega
  have hdr : (0 : ℝ) < d := by positivity
  let α : ℝ := Real.pi / (2 * (d : ℝ))
  let a : ℝ := Real.cos α
  have hα0 : 0 ≤ α := by dsimp [α]; positivity
  have hαpi : α ≤ Real.pi / 2 := by
    dsimp [α]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * d)).mpr
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith [Real.pi_pos]
  have ha0 : 0 ≤ a := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hαpi⟩
  by_cases hright : a ≤ x
  · exact sharpLobatto_tail_bound d p C hd hdeg hC hb x hright hx.2
  by_cases hleft : x ≤ -a
  · let q : Polynomial ℝ := p.comp (Polynomial.C (-1) * Polynomial.X + Polynomial.C 0)
    have hqdeg : q.natDegree ≤ d := (sharp_markov_affine_degree p (-1) 0).trans hdeg
    have hqb : ∀ y ∈ Set.Icc (-1 : ℝ) 1, |q.eval y| ≤ C := by
      intro y hy
      simpa [q, Polynomial.eval_comp] using hb (-y) ⟨by linarith [hy.2], by linarith [hy.1]⟩
    have htail := sharpLobatto_tail_bound d q C hd hqdeg hC hqb (-x)
      (by linarith) (by linarith [hx.1])
    have hqd := sharp_markov_affine_derivative p (-1) 0 (-x)
    dsimp only [q] at htail
    rw [hqd] at htail
    simpa only [neg_one_mul, neg_neg, add_zero, abs_neg] using htail
  have hxa : x ^ 2 ≤ a ^ 2 := by
    have h1 : 0 ≤ a - x := by linarith [not_le.mp hright]
    have h2 : 0 ≤ a + x := by linarith [not_le.mp hleft]
    nlinarith [mul_nonneg h1 h2]
  have hxsq : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have hs0 : 0 ≤ Real.sin α := Real.sin_nonneg_of_nonneg_of_le_pi hα0 (by linarith [Real.pi_pos])
  have hsin_sqrt : Real.sin α ≤ Real.sqrt (1 - x ^ 2) := by
    have he := Real.sin_sq_add_cos_sq α
    have hs := Real.sq_sqrt hxsq
    have hsr := Real.sqrt_nonneg (1 - x ^ 2)
    change x ^ 2 ≤ (Real.cos α) ^ 2 at hxa
    nlinarith
  have hsin : 1 ≤ (d : ℝ) * Real.sin α := by
    have h := mul_le_mul_of_nonneg_left (Real.mul_le_sin hα0 hαpi) hdr.le
    have heq : (d : ℝ) * (2 / Real.pi * α) = 1 := by
      dsimp [α]
      field_simp
    rwa [heq] at h
  have hweight : 1 ≤ (d : ℝ) * Real.sqrt (1 - x ^ 2) :=
    hsin.trans (mul_le_mul_of_nonneg_left hsin_sqrt hdr.le)
  have hbern := sharpBernstein_interior d p C hd hdeg hC hb x hx
  calc
    |p.derivative.eval x| ≤ ((d : ℝ) * Real.sqrt (1 - x ^ 2)) * |p.derivative.eval x| := by
      simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hweight (abs_nonneg (p.derivative.eval x))
    _ ≤ (d : ℝ) * ((d : ℝ) * C) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbern hdr.le
    _ = (d : ℝ) ^ 2 * C := by ring

end Qatlib.Concepts.QueryComplexity.DegreeMethod
