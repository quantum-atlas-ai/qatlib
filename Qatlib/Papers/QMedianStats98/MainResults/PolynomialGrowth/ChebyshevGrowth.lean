/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal

/-!
# Chebyshev control of polynomial growth

This module proves the exterior polynomial-growth estimate recorded as Corollary A.4 in
[NayakWu1998]. A real polynomial of degree at most `d` bounded by `c` on `[-a, a]` is bounded
outside that interval by `c * |T_d(x/a)|`.

The normalized estimate on `[1, ∞)` follows from Chebyshev extremality. Scaling and reflection
extend it to arbitrary positive interval radius and both exterior rays, including the case `c =
0`.

## Main statements

- `abs_eval_le_eval_T_of_one_le`: gives the normalized exterior estimate.
- `corollary_A_4`: gives the scaled two-sided Chebyshev growth bound.

## References

[Nayak and Wu, 1998][NayakWu1998]
-/

set_option autoImplicit false

namespace Qatlib.Papers.QMedianStats98.MainResults.PolynomialGrowth

open Polynomial

/-- If a real polynomial has degree at most `d` and absolute value at most one on `[-1, 1]`,
then its absolute value at any `y ≥ 1` is at most `T_d(y)`. -/
theorem abs_eval_le_eval_T_of_one_le {d : ℕ} {P : Polynomial ℝ}
    (hdeg : P.natDegree ≤ d)
    (hb : ∀ y ∈ Set.Icc (-1 : ℝ) 1, |P.eval y| ≤ 1)
    {y : ℝ} (hy : 1 ≤ y) :
    |P.eval y| ≤ (Polynomial.Chebyshev.T ℝ (d : ℤ)).eval y := by
  have hPd : P.degree ≤ d := Polynomial.degree_le_of_natDegree_le hdeg
  have hnegd : (-P).degree ≤ d := by simpa using hPd
  have hnegs : ∀ z ∈ Set.Icc (-1 : ℝ) 1, |(-P).eval z| ≤ 1 := by
    intro z hz
    simpa using hb z hz
  have h1 := Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one
    (n := d) (P := P) (k := 0) hy hPd hb
  have h2 := Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one
    (n := d) (P := -P) (k := 0) hy hnegd hnegs
  simp only [Function.iterate_zero_apply] at h1 h2
  rw [abs_le]
  constructor
  · simp only [Polynomial.eval_neg] at h2
    linarith
  · exact h1

/-- For `a > 0` and `c ≥ 0`, a real polynomial of degree at most `d` bounded by `c` on `[-a, a]`
satisfies `|p(x)| ≤ c * |T_d(x/a)|` whenever `|x| ≥ a`. This is Corollary A.4 of
[NayakWu1998]. -/
theorem corollary_A_4 {d : ℕ} {p : Polynomial ℝ} {a c x : ℝ}
    (ha : 0 < a) (hc : 0 ≤ c) (hdeg : p.natDegree ≤ d)
    (hb : ∀ y : ℝ, |y| ≤ a → |p.eval y| ≤ c)
    (hx : a ≤ |x|) :
    |p.eval x| ≤ c * |(Polynomial.Chebyshev.T ℝ (d : ℤ)).eval (x / a)| := by
  rcases lt_or_eq_of_le hc with hcpos | hc0
  · let q : Polynomial ℝ := Polynomial.C c⁻¹ * p.comp (Polynomial.C a * Polynomial.X)
    have hqdeg : q.natDegree ≤ d := by
      have hX : (Polynomial.C a * Polynomial.X).natDegree ≤ 1 := by
        refine (Polynomial.natDegree_mul_le).trans ?_
        have hC : (Polynomial.C a).natDegree = 0 := Polynomial.natDegree_C a
        have hx1 : (Polynomial.X : Polynomial ℝ).natDegree = 1 := Polynomial.natDegree_X
        omega
      calc q.natDegree
          ≤ (Polynomial.C c⁻¹).natDegree + (p.comp (Polynomial.C a * Polynomial.X)).natDegree :=
            Polynomial.natDegree_mul_le
        _ ≤ 0 + p.natDegree * (Polynomial.C a * Polynomial.X).natDegree := by
            gcongr
            · simp [Polynomial.natDegree_C]
            · exact Polynomial.natDegree_comp_le
        _ ≤ d := by
            have := Nat.mul_le_mul hdeg hX
            omega
    have hqbound : ∀ y ∈ Set.Icc (-1 : ℝ) 1, |q.eval y| ≤ 1 := by
      intro y hy
      have hyabs : |y| ≤ 1 := abs_le.mpr hy
      have hay : |a * y| ≤ a := by
        rw [abs_mul, abs_of_pos ha]
        calc a * |y| ≤ a * 1 := by gcongr
          _ = a := mul_one a
      have hpy := hb (a * y) hay
      have hqeval : q.eval y = c⁻¹ * p.eval (a * y) := by
        simp only [q, Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_C,
          Polynomial.eval_X]
      rw [hqeval, abs_mul, abs_of_pos (inv_pos.mpr hcpos)]
      calc c⁻¹ * |p.eval (a * y)| ≤ c⁻¹ * c := by gcongr
        _ = 1 := inv_mul_cancel₀ (ne_of_gt hcpos)
    have key : ∀ (P : Polynomial ℝ), P.natDegree ≤ d →
        (∀ y ∈ Set.Icc (-1 : ℝ) 1, |P.eval y| ≤ 1) →
        ∀ z : ℝ, 1 ≤ z → |P.eval z| ≤ (Polynomial.Chebyshev.T ℝ (d : ℤ)).eval z :=
      fun P hPd hPb z hz => abs_eval_le_eval_T_of_one_le hPd hPb hz
    have hq_pos : ∀ z : ℝ, 1 ≤ z → |q.eval z| ≤ (Polynomial.Chebyshev.T ℝ (d : ℤ)).eval z :=
      key q hqdeg hqbound
    have hq_neg : ∀ z : ℝ, 1 ≤ z →
        |q.eval (-z)| ≤ (Polynomial.Chebyshev.T ℝ (d : ℤ)).eval z := by
      intro z hz
      have hb2 : ∀ y ∈ Set.Icc (-1 : ℝ) 1, |(q.comp (-Polynomial.X)).eval y| ≤ 1 := by
        intro y hy
        have hy' : -y ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [hy.2], by linarith [hy.1]⟩
        simpa [Polynomial.eval_comp] using hqbound (-y) hy'
      have hd2 : (q.comp (-Polynomial.X)).natDegree ≤ d := by
        calc (q.comp (-Polynomial.X)).natDegree
            ≤ q.natDegree * (-Polynomial.X).natDegree := Polynomial.natDegree_comp_le
          _ = q.natDegree * 1 := by rw [Polynomial.natDegree_neg, Polynomial.natDegree_X]
          _ ≤ d := by simpa using hqdeg
      have h := key (q.comp (-Polynomial.X)) hd2 hb2 z hz
      simpa [Polynomial.eval_comp] using h

    have hpx : p.eval x = c * q.eval (x / a) := by
      have hq : q.eval (x / a) = c⁻¹ * p.eval x := by
        simp only [q, Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_C,
          Polynomial.eval_X]
        rw [mul_div_cancel₀ x (ne_of_gt ha)]
      rw [hq, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hcpos), one_mul]
    rcases le_or_gt (0 : ℝ) x with hx0 | hxneg
    · have hz : 1 ≤ x / a := (le_div_iff₀ ha).mpr (by linarith [abs_of_nonneg hx0 ▸ hx])
      have hbnd := hq_pos (x / a) hz
      have hT := Polynomial.Chebyshev.one_le_eval_T_real (d : ℤ) hz
      calc |p.eval x| = c * |q.eval (x / a)| := by rw [hpx, abs_mul, abs_of_pos hcpos]
        _ ≤ c * (Polynomial.Chebyshev.T ℝ (d : ℤ)).eval (x / a) := by gcongr
        _ = c * |(Polynomial.Chebyshev.T ℝ (d : ℤ)).eval (x / a)| := by
            rw [abs_of_nonneg (le_trans zero_le_one hT)]
    · have hxa : x / a = -((-x) / a) := by rw [neg_div, neg_neg]
      have hz : 1 ≤ (-x) / a := (le_div_iff₀ ha).mpr (by linarith [abs_of_neg hxneg ▸ hx])
      have hbnd := hq_neg ((-x) / a) hz
      have hT := Polynomial.Chebyshev.one_le_eval_T_real (d : ℤ) hz
      have hTabs : |(Polynomial.Chebyshev.T ℝ (d : ℤ)).eval (x / a)|
          = (Polynomial.Chebyshev.T ℝ (d : ℤ)).eval ((-x) / a) := by
        rw [hxa, Polynomial.Chebyshev.T_eval_neg, abs_mul, abs_unit_intCast, one_mul]
        exact abs_of_nonneg (le_trans zero_le_one hT)
      calc |p.eval x| = c * |q.eval (x / a)| := by rw [hpx, abs_mul, abs_of_pos hcpos]
        _ = c * |q.eval (-((-x) / a))| := by rw [hxa]
        _ ≤ c * (Polynomial.Chebyshev.T ℝ (d : ℤ)).eval ((-x) / a) := by gcongr
        _ = c * |(Polynomial.Chebyshev.T ℝ (d : ℤ)).eval (x / a)| := by rw [hTabs]
  · subst hc0
    have hpzero : p = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      apply Set.Infinite.mono _ (Set.Icc_infinite (show -a < a by linarith))
      intro y hy
      have hyabs : |y| ≤ a := abs_le.mpr hy
      have hzero : |p.eval y| = 0 := le_antisymm (hb y hyabs) (abs_nonneg _)
      exact abs_eq_zero.mp hzero
    rw [hpzero]
    simp

end Qatlib.Papers.QMedianStats98.MainResults.PolynomialGrowth
