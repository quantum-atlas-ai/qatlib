/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.Amplification.OptimalThresholdAllocationStat

/-!
# Optimal threshold allocation

Proves that allocating thresholds proportionally to the two-thirds powers of nonnegative weights
minimizes the sum of each weight divided by the square root of its threshold.
`ThresholdOptimalThresholdAllocation_answer` also gives normalization, bounds, the objective
value `quasinorm23`, and uniqueness when all weights are positive.

The proof uses scalar tangent inequalities with explicit equality conditions, supplying the
threshold optimization used in the variable-time amplification analysis of [LowSu2026].

## Main statements

* `term_tangent_bound`: gives the scalar tangent inequality for the objective.
* `term_tangent_bound_eq_iff`: characterizes equality for positive arguments.
* `ThresholdOptimalThresholdAllocation_answer`: proves the minimizing allocation and its
  uniqueness for positive weights.

## References

* [Low and Su, 2026][LowSu2026]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QlsReadoutSpec.Amplification

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.QlsReadoutSpec.Amplification

open Qatlib.Concepts.QlsReadoutSpec.Amplification
open scoped Classical BigOperators

/-- For nonnegative `u` and `v`, `2 * u ^ 3 + v ^ 3` is at least `3 * u ^ 2 * v`. -/
private theorem two_cube_add_cube_ge (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    2 * u ^ 3 + v ^ 3 ≥ 3 * u ^ 2 * v := by
  have hfac : 2 * u ^ 3 + v ^ 3 - 3 * u ^ 2 * v = (u - v) ^ 2 * (2 * u + v) := by
    ring
  have hnonneg : 0 ≤ (u - v) ^ 2 * (2 * u + v) :=
    mul_nonneg (sq_nonneg _) (by nlinarith [hu, hv])
  linarith [hfac, hnonneg]

/-- For nonnegative `u` and `v`, equality in `2 * u ^ 3 + v ^ 3 ≥ 3 * u ^ 2 * v` holds exactly
when `u = v`. -/
private theorem two_cube_add_cube_ge_eq_iff (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    2 * u ^ 3 + v ^ 3 = 3 * u ^ 2 * v ↔ u = v := by
  constructor
  · intro h
    have hfac : 2 * u ^ 3 + v ^ 3 - 3 * u ^ 2 * v = (u - v) ^ 2 * (2 * u + v) := by
      ring
    have hz : (u - v) ^ 2 * (2 * u + v) = 0 := by linarith [hfac, h]
    rcases mul_eq_zero.mp hz with h1 | h1
    · have huv : u - v = 0 := sq_eq_zero_iff.mp h1
      linarith
    · have hu0 : u = 0 := by linarith [hu, hv, h1]
      have hv0 : v = 0 := by linarith [hu, hv, h1]
      linarith
  · intro h
    subst h
    ring

/-- For nonnegative `a` and positive `b` and `c`, `a ^ 3 / b + c ^ 3 * b ^ 2 / 2` is at least `3
* c * a ^ 2 / 2`. -/
private theorem poly_tangent_bound (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 3 / b + (1 / 2 : ℝ) * c ^ 3 * b ^ 2 ≥ (3 / 2) * c * a ^ 2 := by
  have hkey0 := two_cube_add_cube_ge a (c * b) ha (mul_nonneg (le_of_lt hc) (le_of_lt hb))
  have hkey : 2 * a ^ 3 + c ^ 3 * b ^ 3 ≥ 3 * (c * a ^ 2 * b) := by
    have e1 : (c * b) ^ 3 = c ^ 3 * b ^ 3 := by ring
    have e2 : 3 * a ^ 2 * (c * b) = 3 * (c * a ^ 2 * b) := by ring
    nlinarith [hkey0, e1, e2]
  rw [ge_iff_le, ← sub_le_iff_le_add, le_div_iff₀ hb]
  have hcalc :
      ((3 / 2 : ℝ) * c * a ^ 2 - (1 / 2) * c ^ 3 * b ^ 2) * b
        = (3 / 2) * (c * a ^ 2 * b) - (1 / 2) * (c ^ 3 * b ^ 3) := by
    ring
  rw [hcalc]
  nlinarith [hkey]

/-- For positive `a`, `b`, and `c`, equality in the polynomial tangent inequality holds exactly
when `a ^ 2 = c ^ 2 * b ^ 2`. -/
private theorem poly_tangent_bound_eq_iff (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 3 / b + (1 / 2 : ℝ) * c ^ 3 * b ^ 2 = (3 / 2) * c * a ^ 2 ↔ a ^ 2 = c ^ 2 * b ^ 2 := by
  constructor
  · intro heq
    have hmul :
        (a ^ 3 / b + (1 / 2 : ℝ) * c ^ 3 * b ^ 2) * b = ((3 / 2) * c * a ^ 2) * b := by
      rw [heq]
    have hexp :
        (a ^ 3 / b + (1 / 2 : ℝ) * c ^ 3 * b ^ 2) * b = a ^ 3 + (1 / 2) * c ^ 3 * b ^ 3 := by
      rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hb)]
      ring
    rw [hexp] at hmul
    have hkey0 := two_cube_add_cube_ge_eq_iff a (c * b) (le_of_lt ha)
      (mul_nonneg (le_of_lt hc) (le_of_lt hb))
    have hh : 2 * a ^ 3 + (c * b) ^ 3 = 3 * a ^ 2 * (c * b) := by
      nlinarith [hmul]
    have haeq : a = c * b := hkey0.mp hh
    have hsq : a ^ 2 = (c * b) ^ 2 := by rw [haeq]
    rwa [mul_pow] at hsq
  · intro heq
    have haeq : a = c * b := by
      have h1 : a ^ 2 = (c * b) ^ 2 := by rwa [mul_pow]
      exact (pow_left_inj₀ (le_of_lt ha) (mul_nonneg (le_of_lt hc) (le_of_lt hb))
        two_ne_zero).mp h1
    rw [haeq]
    have h : (c * b) ^ 3 / b + (1 / 2 : ℝ) * c ^ 3 * b ^ 2 = (3 / 2) * c * (c * b) ^ 2 := by
      field_simp [ne_of_gt hb]
      ring
    exact h

/-- For nonnegative `x`, the cube of `Real.sqrt x` equals `x.rpow (3 / 2)`. -/
private theorem cube_sqrt (x : ℝ) (hx : 0 ≤ x) : (Real.sqrt x) ^ 3 = x.rpow (3 / 2) := by
  rw [Real.sqrt_eq_rpow]
  have h := Real.rpow_mul_natCast hx (1 / 2 : ℝ) 3
  push_cast at h
  norm_num at h
  exact h.symm

/-- For nonnegative `x`, the square of `Real.sqrt x` equals `x`. -/
private theorem sq_sqrt (x : ℝ) (hx : 0 ≤ x) : (Real.sqrt x) ^ 2 = x := by
  rw [Real.sqrt_eq_rpow]
  have h := Real.rpow_mul_natCast hx (1 / 2 : ℝ) 2
  push_cast at h
  norm_num at h
  exact h.symm

/-- For nonnegative `w`, raising `w.rpow (2 / 3)` to the power `3 / 2` recovers `w`. -/
private theorem rpow_two_thirds_three_halves (w : ℝ) (hw : 0 ≤ w) :
    (w.rpow (2 / 3)).rpow (3 / 2) = w := by
  have h := Real.rpow_mul hw (2 / 3 : ℝ) (3 / 2)
  rw [show ((2 / 3 : ℝ) * (3 / 2)) = 1 by norm_num, Real.rpow_one] at h
  exact h.symm

/-- For nonnegative `x` and positive `s`, `x / sqrt (x.rpow (2 / 3) / s)` equals `x.rpow (2 / 3)
* sqrt s`. -/
private theorem div_sqrt_alpha_eq (x s : ℝ) (hx : 0 ≤ x) (hs : 0 < s) :
    x / Real.sqrt (x.rpow (2 / 3) / s) = x.rpow (2 / 3) * Real.sqrt s := by
  by_cases hx0 : x = 0
  · have h0 : Real.rpow (0 : ℝ) (2 / 3) = 0 :=
      Real.zero_rpow (by norm_num : (2 / 3 : ℝ) ≠ 0)
    rw [hx0, h0, zero_div, zero_mul]
  · have hx23 : 0 ≤ x.rpow (2 / 3) := Real.rpow_nonneg hx _
    have key : ∀ (p q : ℝ), 0 ≤ p → 0 < q → p ^ 3 / (p / q) = p ^ 2 * q := by
      intro p q hp hq
      by_cases hp0 : p = 0
      · rw [hp0]
        simp
      · rw [div_div_eq_mul_div, show p ^ 3 * q = (p ^ 2 * q) * p by ring,
          mul_div_cancel_right₀ _ hp0]

    have hnum : x = (Real.sqrt (x.rpow (2 / 3))) ^ 3 :=
      calc x = (x.rpow (2 / 3)).rpow (3 / 2) := (rpow_two_thirds_three_halves x hx).symm
        _ = (Real.sqrt (x.rpow (2 / 3))) ^ 3 := (cube_sqrt _ hx23).symm
    have hden : Real.sqrt (x.rpow (2 / 3) / s)
        = Real.sqrt (x.rpow (2 / 3)) / Real.sqrt s := Real.sqrt_div hx23 s
    have hrhs : (Real.sqrt (x.rpow (2 / 3))) ^ 2 * Real.sqrt s
        = x.rpow (2 / 3) * Real.sqrt s := by rw [sq_sqrt _ hx23]
    calc x / Real.sqrt (x.rpow (2 / 3) / s)
        = (Real.sqrt (x.rpow (2 / 3))) ^ 3
            / (Real.sqrt (x.rpow (2 / 3)) / Real.sqrt s) :=
          congrArg₂ HDiv.hDiv hnum hden
      _ = (Real.sqrt (x.rpow (2 / 3))) ^ 2 * Real.sqrt s :=
          key _ _ (Real.sqrt_nonneg _) (Real.sqrt_pos.mpr hs)
      _ = x.rpow (2 / 3) * Real.sqrt s := hrhs

/-- For nonnegative `x` and positive `t` and `s`, `x.rpow (3 / 2) / sqrt t + s.rpow (3 / 2) * t
/ 2` is at least `3 * sqrt s * x / 2`. -/
private theorem term_tangent_bound (x t s : ℝ) (hx : 0 ≤ x) (ht : 0 < t) (hs : 0 < s) :
    x.rpow (3 / 2) / Real.sqrt t + (1 / 2) * s.rpow (3 / 2) * t
      ≥ (3 / 2) * Real.sqrt s * x := by
  have h3x : x.rpow (3 / 2) = (Real.sqrt x) ^ 3 := (cube_sqrt x hx).symm
  have h3s : s.rpow (3 / 2) = (Real.sqrt s) ^ 3 := (cube_sqrt s (le_of_lt hs)).symm
  have h2t : (Real.sqrt t) ^ 2 = t := sq_sqrt t (le_of_lt ht)
  have h2x : (Real.sqrt x) ^ 2 = x := sq_sqrt x hx
  calc x.rpow (3 / 2) / Real.sqrt t + (1 / 2) * s.rpow (3 / 2) * t
      = (Real.sqrt x) ^ 3 / Real.sqrt t + (1 / 2) * (Real.sqrt s) ^ 3 * t := by
          rw [h3x, h3s]
    _ = (Real.sqrt x) ^ 3 / Real.sqrt t
          + (1 / 2) * (Real.sqrt s) ^ 3 * (Real.sqrt t) ^ 2 := by
          conv_rhs => rw [h2t]
    _ ≥ (3 / 2) * Real.sqrt s * (Real.sqrt x) ^ 2 :=
          poly_tangent_bound _ _ _ (Real.sqrt_nonneg _) (Real.sqrt_pos.mpr ht)
            (Real.sqrt_pos.mpr hs)
    _ = (3 / 2) * Real.sqrt s * x := by rw [h2x]

/-- For positive `x`, `t`, and `s`, equality in the threshold tangent inequality holds exactly
when `x = s * t`. -/
private theorem term_tangent_bound_eq_iff (x t s : ℝ) (hx : 0 < x) (ht : 0 < t) (hs : 0 < s) :
    x.rpow (3 / 2) / Real.sqrt t + (1 / 2) * s.rpow (3 / 2) * t
      = (3 / 2) * Real.sqrt s * x ↔ x = s * t := by
  have h3x : x.rpow (3 / 2) = (Real.sqrt x) ^ 3 := (cube_sqrt x (le_of_lt hx)).symm
  have h3s : s.rpow (3 / 2) = (Real.sqrt s) ^ 3 := (cube_sqrt s (le_of_lt hs)).symm
  have h2t : (Real.sqrt t) ^ 2 = t := sq_sqrt t (le_of_lt ht)
  have h2x : (Real.sqrt x) ^ 2 = x := sq_sqrt x (le_of_lt hx)
  have h2s : (Real.sqrt s) ^ 2 = s := sq_sqrt s (le_of_lt hs)
  have hLHS : x.rpow (3 / 2) / Real.sqrt t + (1 / 2) * s.rpow (3 / 2) * t
      = (Real.sqrt x) ^ 3 / Real.sqrt t
          + (1 / 2) * (Real.sqrt s) ^ 3 * (Real.sqrt t) ^ 2 := by
    rw [h3x, h3s]
    conv_rhs => rw [h2t]
  have hRHS : (3 / 2) * Real.sqrt s * x = (3 / 2) * Real.sqrt s * (Real.sqrt x) ^ 2 := by
    conv_rhs => rw [h2x]
  have hcond : x = s * t ↔ (Real.sqrt x) ^ 2 = (Real.sqrt s) ^ 2 * (Real.sqrt t) ^ 2 := by
    rw [sq_sqrt x (le_of_lt hx), sq_sqrt s (le_of_lt hs), sq_sqrt t (le_of_lt ht)]
  rw [hLHS, hRHS, hcond]
  exact poly_tangent_bound_eq_iff (Real.sqrt x) (Real.sqrt t) (Real.sqrt s)
    (Real.sqrt_pos.mpr hx) (Real.sqrt_pos.mpr ht) (Real.sqrt_pos.mpr hs)

/-- Proves that thresholds proportional to the two-thirds powers of the weights attain
`quasinorm23` and minimize the weighted inverse-square-root objective, uniquely for strictly
positive weights; see [Low and Su, Proposition 6][LowSu2026]. -/
theorem ThresholdOptimalThresholdAllocation_answer : ThresholdOptimalThresholdAllocation := by
  intro n w hw hsum α

  set S : ℝ := ∑ k, (w k).rpow (2 / 3) with hSdef
  have hS : 0 < S := by
    obtain ⟨j, hj⟩ : ∃ j : Fin n, 0 < w j := by
      by_contra hc
      simp only [not_exists, not_lt] at hc
      have h0 : ∀ j : Fin n, w j = 0 := fun j => le_antisymm (hc j) (hw j)
      have hz : (∑ j : Fin n, w j) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        exact h0 j
      rw [hz] at hsum
      exact lt_irrefl 0 hsum
    have hjr : 0 < (w j).rpow (2 / 3) := Real.rpow_pos_of_pos hj _
    have hle : (w j).rpow (2 / 3) ≤ S := by
      refine Finset.single_le_sum (fun k _ => Real.rpow_nonneg (hw k) _) ?_
      exact Finset.mem_univ j
    exact lt_of_lt_of_le hjr hle
  have hα : ∀ j : Fin n, α j = (w j).rpow (2 / 3) / S := by
    intro j
    rfl

  have hq : quasinorm23 w = S.rpow (3 / 2) := by
    have hsum' : (∑ j, (max 0 (w j)).rpow (2 / 3)) = S := by
      apply Finset.sum_congr rfl
      intro j _
      rw [max_eq_right (hw j)]
    unfold quasinorm23
    rw [hsum']

  have hterm : ∀ j : Fin n, w j / Real.sqrt (α j) = (w j).rpow (2 / 3) * Real.sqrt S := by
    intro j
    rw [hα j]
    exact div_sqrt_alpha_eq (w j) S (hw j) hS
  have hSS : Real.sqrt S * S = S.rpow (3 / 2) := by
    rw [Real.sqrt_eq_rpow]
    have h := Real.rpow_add hS (1 / 2 : ℝ) 1
    rw [show ((1 / 2 : ℝ) + 1) = 3 / 2 by norm_num, Real.rpow_one] at h
    exact h.symm
  have hcalc : (∑ j, w j / Real.sqrt (α j)) = S * Real.sqrt S := by
    rw [Finset.sum_congr rfl (fun j _ => hterm j)]
    rw [← Finset.sum_mul, ← hSdef]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h1 : (∑ j, α j) = S / S := by
      have hsumα : (∑ j, α j) = ∑ j, (w j).rpow (2 / 3) / S :=
        Finset.sum_congr rfl (fun j _ => hα j)
      rw [hsumα, ← Finset.sum_div, ← hSdef]
    rw [h1, div_self (ne_of_gt hS)]
  · intro j
    rw [hα j]
    constructor
    · exact div_nonneg (Real.rpow_nonneg (hw j) _) (le_of_lt hS)
    · rw [div_le_one hS]
      refine Finset.single_le_sum (fun k _ => Real.rpow_nonneg (hw k) _) ?_
      exact Finset.mem_univ j
  · rw [hq, hcalc, mul_comm, hSS]
  · intro β hβnonneg hβpos hβsum
    rw [hq]
    have hterm' : ∀ j : Fin n,
        (3 / 2) * Real.sqrt S * (w j).rpow (2 / 3) - (1 / 2) * S.rpow (3 / 2) * β j
          ≤ w j / Real.sqrt (β j) := by
      intro j
      by_cases hwj : w j = 0
      · have h0 : Real.rpow (0 : ℝ) (2 / 3) = 0 :=
          Real.zero_rpow (by norm_num : (2 / 3 : ℝ) ≠ 0)
        rw [hwj, h0, mul_zero, zero_sub, zero_div]
        have hβj : 0 ≤ β j := hβnonneg j
        have hS32 : 0 ≤ S.rpow (3 / 2) := Real.rpow_nonneg (le_of_lt hS) _
        nlinarith
      · have hwj' : 0 < w j := lt_of_le_of_ne (hw j) (Ne.symm hwj)
        have hβj : 0 < β j := hβpos j hwj'
        have h23 : 0 ≤ (w j).rpow (2 / 3) := Real.rpow_nonneg (hw j) _
        have hbind := term_tangent_bound ((w j).rpow (2 / 3)) (β j) S h23 hβj hS
        rw [rpow_two_thirds_three_halves (w j) (hw j)] at hbind
        linarith
    have hsumterm : (∑ j, w j / Real.sqrt (β j))
        ≥ ∑ j, ((3 / 2) * Real.sqrt S * (w j).rpow (2 / 3) - (1 / 2) * S.rpow (3 / 2) * β j) :=
      Finset.sum_le_sum (fun j _ => hterm' j)
    have hcalc' : (∑ j, ((3 / 2) * Real.sqrt S * (w j).rpow (2 / 3) - (1 / 2) * S.rpow (3 / 2) * β j))
        = S.rpow (3 / 2) := by
      rw [Finset.sum_sub_distrib]
      have ha : (∑ j, (3 / 2) * Real.sqrt S * (w j).rpow (2 / 3))
          = (3 / 2) * Real.sqrt S * S := by
        rw [← Finset.mul_sum, ← hSdef]
      have hb : (∑ j, (1 / 2) * S.rpow (3 / 2) * β j)
          = (1 / 2) * S.rpow (3 / 2) * 1 := by
        rw [← Finset.mul_sum, hβsum]
      rw [ha, hb, mul_one]
      have h3 : (3 / 2 : ℝ) * Real.sqrt S * S = (3 / 2) * S.rpow (3 / 2) := by
        rw [mul_assoc, hSS]
      nlinarith
    linarith [hsumterm, hcalc']
  · intro β hβpos hwhpos hβsum
    constructor
    · intro heq
      have hslack : ∀ j : Fin n,
          0 ≤ w j / Real.sqrt (β j) + (1 / 2) * S.rpow (3 / 2) * β j
              - (3 / 2) * Real.sqrt S * (w j).rpow (2 / 3) := by
        intro j
        have hwj : 0 < w j := hwhpos j
        have hβj : 0 < β j := hβpos j
        have h23 : 0 ≤ (w j).rpow (2 / 3) := Real.rpow_nonneg (le_of_lt hwj) _
        have h := term_tangent_bound ((w j).rpow (2 / 3)) (β j) S h23 hβj hS
        rw [rpow_two_thirds_three_halves (w j) (le_of_lt hwj)] at h
        linarith
      have hsum0 :
          (∑ j, (w j / Real.sqrt (β j) + (1 / 2) * S.rpow (3 / 2) * β j
              - (3 / 2) * Real.sqrt S * (w j).rpow (2 / 3))) = 0 := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
        have h1 : (∑ j, w j / Real.sqrt (β j)) = S.rpow (3 / 2) := by
          rw [← hq]
          exact heq
        have h2 : (∑ j, (1 / 2) * S.rpow (3 / 2) * β j) = (1 / 2) * S.rpow (3 / 2) := by
          rw [← Finset.mul_sum, hβsum, mul_one]
        have h3 : (∑ j, (3 / 2) * Real.sqrt S * (w j).rpow (2 / 3))
            = (3 / 2) * Real.sqrt S * S := by
          rw [← Finset.mul_sum, ← hSdef]
        have h3' : (3 / 2 : ℝ) * Real.sqrt S * S = (3 / 2) * S.rpow (3 / 2) := by
          rw [mul_assoc, hSS]
        nlinarith
      have hper : ∀ j : Fin n,
          w j / Real.sqrt (β j) + (1 / 2) * S.rpow (3 / 2) * β j
              - (3 / 2) * Real.sqrt S * (w j).rpow (2 / 3) = 0 := by
        intro j
        have h := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hslack j)).mp hsum0
        exact h j (Finset.mem_univ j)
      funext j
      have hwj : 0 < w j := hwhpos j
      have hβj : 0 < β j := hβpos j
      have h23 : 0 < (w j).rpow (2 / 3) := Real.rpow_pos_of_pos hwj _
      have hbind := term_tangent_bound_eq_iff ((w j).rpow (2 / 3)) (β j) S h23 hβj hS
      rw [rpow_two_thirds_three_halves (w j) (le_of_lt hwj)] at hbind
      have heqj : (w j).rpow (2 / 3) = S * β j := hbind.mp (by linarith [hper j])
      have hβjα : β j = (w j).rpow (2 / 3) / S := by
        rw [eq_div_iff (ne_of_gt hS), mul_comm]
        exact heqj.symm
      rw [hα j, hβjα]
    · intro hβ
      rw [hβ]
      rw [hq, hcalc, mul_comm, hSS]

end Qatlib.Concepts.QlsReadoutSpec.Amplification
