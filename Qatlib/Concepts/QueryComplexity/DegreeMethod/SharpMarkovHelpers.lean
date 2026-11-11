/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Auxiliary estimates for the sharp Markov inequality

This module establishes endpoint, low-degree, affine-change, and Chebyshev derivative
estimates used to prove the sharp Markov inequality from [NayakWu1998].

The results handle vanishing amplitude, degrees zero through two, and the bound
`|T_d'(x)| ≤ d ^ 2` on `[-1, 1]`.

## Main statements

* `sharp_markov_endpoint_right`: the sharp derivative estimate at one.
* `sharp_markov_degree_two`: the quadratic derivative bound.
* `sharp_markov_chebyshev`: the derivative bound for Chebyshev polynomials.

## References

* [Nayak and Wu, 1998, Fact A.5][NayakWu1998]
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Qatlib.Concepts.QueryComplexity.DegreeMethod
open Polynomial

/-- A real polynomial whose absolute value is at most zero throughout `[-1, 1]` is the zero
polynomial. -/
theorem sharp_markov_zero_amplitude (p : Polynomial ℝ)
    (hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ 0) : p = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot p
  apply (Set.Icc_infinite (by norm_num : (-1 : ℝ) < 1)).mono
  intro x hx
  change p.eval x = 0
  exact abs_eq_zero.mp (le_antisymm (hb x hx) (abs_nonneg _))

/-- Composing a real polynomial with an affine polynomial does not increase its natural degree. -/
theorem sharp_markov_affine_degree (p : Polynomial ℝ) (a b : ℝ) :
    (p.comp (Polynomial.C a*Polynomial.X+Polynomial.C b)).natDegree ≤ p.natDegree := by
  have hq : (Polynomial.C a*Polynomial.X+Polynomial.C b).natDegree ≤ 1 := by
    apply Polynomial.natDegree_add_le_of_degree_le
    · exact Polynomial.natDegree_mul_le.trans (by simp)
    · simp
  exact Polynomial.natDegree_comp_le.trans
    ((Nat.mul_le_mul_left p.natDegree hq).trans_eq (Nat.mul_one _))

/-- The derivative of `p (a * x + b)` equals `a * p'(a * x + b)`. -/
theorem sharp_markov_affine_derivative (p : Polynomial ℝ) (a b x : ℝ) :
    (p.comp (Polynomial.C a*Polynomial.X+Polynomial.C b)).derivative.eval x =
      a*p.derivative.eval (a*x+b) := by
  simp [Polynomial.derivative_comp]

/-- A polynomial of degree at most `d` bounded by `C ≥ 0` on `[-1, 1]` has derivative at one
bounded by `d ^ 2 * C`. -/
theorem sharp_markov_endpoint_right {d : ℕ} {p : Polynomial ℝ}
    (hd : p.natDegree ≤ d) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ C) :
    |p.derivative.eval 1| ≤ (d : ℝ)^2*C := by
  rcases hC.eq_or_lt with hc | hc
  · have hz := sharp_markov_zero_amplitude p (by simpa only [← hc] using hb)
    simp [hz,← hc]
  · let g := C⁻¹ • p
    have hdeg : g.degree ≤ d := g.degree_le_natDegree.trans (by
      exact_mod_cast (Polynomial.natDegree_smul_le C⁻¹ p).trans hd)
    have hnorm : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |g.eval x| ≤ 1 := by
      intro x hx
      simp only [g,Polynomial.eval_smul,smul_eq_mul,abs_mul,abs_inv,abs_of_pos hc]
      exact (mul_le_mul_of_nonneg_left (hb x hx) (inv_nonneg.mpr hc.le)).trans_eq
        (inv_mul_cancel₀ hc.ne')
    have hp := Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one
      (n := d) (k := 1) (x := 1) le_rfl hdeg hnorm
    have hn := Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one
      (n := d) (k := 1) (x := 1) (P := -g) le_rfl (by simpa using hdeg)
      (fun x hx => by simpa using hnorm x hx)
    simp only [Function.iterate_one,Polynomial.derivative_neg,Polynomial.eval_neg,
      Polynomial.Chebyshev.derivative_T_eval_one] at hp hn
    norm_cast at hp hn
    push_cast at hp hn
    have habs : |g.derivative.eval 1| ≤ (d : ℝ)^2 := abs_le.mpr ⟨by linarith,hp⟩
    simp only [g,Polynomial.derivative_smul,Polynomial.eval_smul,smul_eq_mul,
      abs_mul,abs_inv,abs_of_pos hc] at habs
    have he := mul_le_mul_of_nonneg_left habs hc.le
    simpa [← mul_assoc,hc.ne',mul_comm] using he

/-- A polynomial of degree at most `d` bounded by `C ≥ 0` on `[-1, 1]` has derivative at minus
one bounded by `d ^ 2 * C`. -/
theorem sharp_markov_endpoint_left {d : ℕ} {p : Polynomial ℝ}
    (hd : p.natDegree ≤ d) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ C) :
    |p.derivative.eval (-1)| ≤ (d : ℝ)^2*C := by
  have hmap (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) : -x ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hx.1,hx.2]
  have he := sharp_markov_endpoint_right
    ((sharp_markov_affine_degree p (-1) 0).trans hd) hC
    (fun x hx => by simpa using hb (-x) (hmap x hx))
  rw [sharp_markov_affine_derivative] at he
  simpa only [neg_one_mul,add_zero,abs_neg] using he

/-- A polynomial of natural degree at most zero has zero derivative at every real point. -/
theorem sharp_markov_degree_zero (p : Polynomial ℝ) (hd : p.natDegree ≤ 0) (x : ℝ) :
    p.derivative.eval x = 0 := by
  rw [Polynomial.derivative_of_natDegree_zero (Nat.eq_zero_of_le_zero hd)]
  simp

/-- An affine polynomial bounded by `C ≥ 0` on `[-1, 1]` has derivative bounded by `C` at every
real point. -/
theorem sharp_markov_degree_one (p : Polynomial ℝ) (hd : p.natDegree ≤ 1)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ C) (x : ℝ) :
    |p.derivative.eval x| ≤ C := by
  have he := sharp_markov_endpoint_right hd hC hb
  rw [Polynomial.eq_X_add_C_of_natDegree_le_one hd] at he ⊢
  simpa using he

/-- An affine polynomial whose endpoint absolute values are at most `C` has absolute value at
most `C` throughout `[-1, 1]`. -/
theorem affine_polynomial_abs_le_of_endpoints (q : Polynomial ℝ)
    (hd : q.natDegree ≤ 1) {C : ℝ}
    (hl : |q.eval (-1)| ≤ C) (hr : |q.eval 1| ≤ C)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) : |q.eval x| ≤ C := by
  have ha : 0 ≤ (1-x)/2 := by linarith [hx.2]
  have hb : 0 ≤ (1+x)/2 := by linarith [hx.1]
  have he : q.eval x = ((1-x)/2)*q.eval (-1)+((1+x)/2)*q.eval 1 := by
    rw [Polynomial.eq_X_add_C_of_natDegree_le_one hd]
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    ring
  rw [he]
  calc
    _ ≤ |((1-x)/2)*q.eval (-1)|+|((1+x)/2)*q.eval 1| := abs_add_le _ _
    _ = ((1-x)/2)*|q.eval (-1)|+((1+x)/2)*|q.eval 1| := by
      rw [abs_mul,abs_mul,abs_of_nonneg ha,abs_of_nonneg hb]
    _ ≤ ((1-x)/2)*C+((1+x)/2)*C :=
      add_le_add (mul_le_mul_of_nonneg_left hl ha) (mul_le_mul_of_nonneg_left hr hb)
    _ = C := by ring

/-- A polynomial of degree at most two bounded by `C ≥ 0` on `[-1, 1]` has derivative bounded
there by `4 * C`. -/
theorem sharp_markov_degree_two (p : Polynomial ℝ) (hd : p.natDegree ≤ 2)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ C)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) : |p.derivative.eval x| ≤ 4*C := by
  have hd' : p.derivative.natDegree ≤ 1 :=
    (Polynomial.natDegree_derivative_le p).trans (Nat.sub_le_sub_right hd 1)
  apply affine_polynomial_abs_le_of_endpoints p.derivative hd' _ _ hx
  · convert sharp_markov_endpoint_left hd hC hb using 1; norm_num
  · convert sharp_markov_endpoint_right hd hC hb using 1; norm_num

/-- For a natural number `n`, `|sin (n * θ)| ≤ n * |sin θ|`. -/
theorem sharp_markov_abs_sin_mul (n : ℕ) (θ : ℝ) :
    |Real.sin ((n : ℝ)*θ)| ≤ (n : ℝ)*|Real.sin θ| := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ,add_mul,one_mul,Real.sin_add]
    calc
      _ ≤ |Real.sin ((n:ℝ)*θ)*Real.cos θ|+|Real.cos ((n:ℝ)*θ)*Real.sin θ| := abs_add_le _ _
      _ ≤ |Real.sin ((n:ℝ)*θ)| *1+1*|Real.sin θ| := by
        rw [abs_mul,abs_mul]
        gcongr
        · exact abs_le.mpr ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩
        · exact abs_le.mpr ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩
      _ ≤ (n:ℝ)*|Real.sin θ|+|Real.sin θ| := by simpa only [mul_one,one_mul] using add_le_add_left ih |Real.sin θ|
      _ = _ := by ring

/-- The derivative of the degree-`d` Chebyshev polynomial of the first kind has absolute value
at most `d ^ 2` on `[-1, 1]`. -/
theorem sharp_markov_chebyshev (d : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(Polynomial.Chebyshev.T ℝ (d:ℤ)).derivative.eval x| ≤ (d:ℝ)^2 := by
  have hd : (Polynomial.Chebyshev.T ℝ (d:ℤ)).natDegree ≤ d := by
    simp only [Polynomial.Chebyshev.natDegree_T,Int.natAbs_natCast,le_refl]
  have hb : ∀ y ∈ Set.Icc (-1 : ℝ) 1, |(Polynomial.Chebyshev.T ℝ (d:ℤ)).eval y| ≤ 1 := by
    intro y hy
    rw [← Real.cos_arccos hy.1 hy.2,Polynomial.Chebyshev.T_real_cos]
    exact abs_le.mpr ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩
  by_cases hl : x = -1
  · subst x
    simpa only [mul_one] using sharp_markov_endpoint_left hd (by norm_num : (0:ℝ) ≤ 1) hb
  by_cases hr : x = 1
  · subst x
    simpa only [mul_one] using sharp_markov_endpoint_right hd (by norm_num : (0:ℝ) ≤ 1) hb
  let θ := Real.arccos x
  have hθ : 0 < θ := Real.arccos_pos.mpr (lt_of_le_of_ne hx.2 hr)
  have hθpi : θ < Real.pi := Real.arccos_lt_pi.mpr (lt_of_le_of_ne hx.1 (Ne.symm hl))
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ hθpi
  have hU : (Polynomial.Chebyshev.U ℝ ((d:ℤ)-1)).eval x * Real.sin θ = Real.sin ((d:ℝ)*θ) := by
    have he := Polynomial.Chebyshev.U_real_cos (θ := θ) (n := (d:ℤ)-1)
    simpa only [θ,Real.cos_arccos hx.1 hx.2,Int.cast_sub,Int.cast_natCast,Int.cast_one,sub_add_cancel] using he
  have habs : |(Polynomial.Chebyshev.U ℝ ((d:ℤ)-1)).eval x| ≤ (d:ℝ) := by
    have he := congrArg abs hU
    rw [abs_mul,abs_of_pos hs] at he
    have hsin := sharp_markov_abs_sin_mul d θ
    rw [← he,abs_of_pos hs] at hsin
    exact le_of_mul_le_mul_right hsin hs
  rw [Polynomial.Chebyshev.T_derivative_eq_U]
  simp only [Polynomial.eval_mul,Int.cast_natCast,Polynomial.eval_natCast,abs_mul,
    abs_of_nonneg (Nat.cast_nonneg d : (0:ℝ) ≤ d)]
  calc
    _ ≤ (d:ℝ)*(d:ℝ) := mul_le_mul_of_nonneg_left habs (Nat.cast_nonneg _)
    _ = _ := by ring

end Qatlib.Concepts.QueryComplexity.DegreeMethod
