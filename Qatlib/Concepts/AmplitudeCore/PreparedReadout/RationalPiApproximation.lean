/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic.Common
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Rational Machin approximations to pi

`atanRatSeries` computes finite rational arctangent sums, and `piRatApprox` combines them using
Machin's identity. Derivative and monotonicity estimates bound the arctangent remainder and
yield an explicit dyadic error bound for the computed approximation to π.

These rational constants support numerical phase decoding in quantum algorithms;
[NielsenChuang2010] provides background on that application.

## Main statements

* `rational_arctan_series_explicit_remainder`: bounds the rational arctangent approximation
  error.
* `rational_machin_pi_identity`: proves Machin's identity.
* `rational_machin_pi_computed_precision`: gives positivity, an upper bound of four, and the
  dyadic precision estimate.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.AmplitudeCore.PreparedReadout

set_option autoImplicit false

/-- The rational partial sum of the arctangent power series with `L` terms. -/
def atanRatSeries (x : ℚ) : ℕ → ℚ
  | 0 => 0
  | L + 1 => atanRatSeries x L + (-1 : ℚ) ^ L * x ^ (2 * L + 1) / (2 * L + 1)

/-- The real polynomial consisting of the first `L` arctangent-series terms. -/
private noncomputable def atanPoly (L : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range L, (-1 : ℝ) ^ (j : ℕ) * t ^ (2 * j + 1) / (2 * j + 1)

/-- Casting the rational arctangent partial sum to the reals yields `atanPoly`. -/
theorem atanRatSeries_cast (x : ℚ) : ∀ L : ℕ,
    ((atanRatSeries x L : ℚ) : ℝ) = atanPoly L (x : ℝ) := by
  intro L
  induction L with
  | zero => simp [atanRatSeries, atanPoly]
  | succ L ih =>
      have hcast : ((atanRatSeries x (L + 1) : ℚ) : ℝ)
          = ((atanRatSeries x L : ℚ) : ℝ)
            + (-1 : ℝ) ^ L * (x : ℝ) ^ (2 * L + 1) / (2 * L + 1) := by
        rw [atanRatSeries]
        push_cast
        ring
      rw [hcast, ih]
      simp only [atanPoly, Finset.sum_range_succ]

/-- The one-term rational arctangent partial sum equals its argument. -/
theorem atanRatSeries_one (x : ℚ) : atanRatSeries x 1 = x := by
  norm_num [atanRatSeries]

/-- The one-term real arctangent polynomial equals its argument. -/
private theorem atanPoly_one (t : ℝ) : atanPoly 1 t = t := by
  norm_num [atanPoly]

/-- The derivative of `atanPoly L` is the finite alternating sum of even powers. -/
private theorem hasDerivAt_atanPoly : ∀ (L : ℕ) (t : ℝ),
    HasDerivAt (atanPoly L) (∑ j ∈ Finset.range L, (-1 : ℝ) ^ (j : ℕ) * t ^ (2 * j)) t := by
  intro L
  induction L with
  | zero =>
      intro t
      show HasDerivAt (fun _ : ℝ => (0 : ℝ)) (0 : ℝ) t
      exact hasDerivAt_const t (0 : ℝ)
  | succ L ih =>
      intro t
      have hterm : HasDerivAt (fun s : ℝ => (-1 : ℝ) ^ (L : ℕ) * s ^ (2 * L + 1)
          / (2 * L + 1)) ((-1 : ℝ) ^ (L : ℕ) * t ^ (2 * L)) t := by
        have h1 := ((hasDerivAt_id t).pow (2 * L + 1)).const_mul ((-1 : ℝ) ^ (L : ℕ))
        exact (h1.div_const (2 * L + 1)).congr_deriv (by
          simp only [id_eq]
          field_simp
          push_cast [Nat.cast_mul]
          ring)
      have hsplit : atanPoly (L + 1) = fun s => atanPoly L s
          + (-1 : ℝ) ^ (L : ℕ) * s ^ (2 * L + 1) / (2 * L + 1) := by
        funext s
        norm_num [atanPoly, Finset.sum_range_succ]
      rw [hsplit]
      simpa using! ((ih t).add hterm).congr_deriv (by rw [Finset.sum_range_succ])

/-- The derivative of the arctangent remainder is `(-1)^L * t^(2 * L) / (1 + t²)`. -/
private theorem hasDerivAt_arctan_sub_atanPoly (L : ℕ) (t : ℝ) :
    HasDerivAt (fun s => Real.arctan s - atanPoly L s)
      ((-1 : ℝ) ^ (L : ℕ) * t ^ (2 * L) / (1 + t ^ 2)) t := by
  have hsum : ∑ j ∈ Finset.range L, (-1 : ℝ) ^ (j : ℕ) * t ^ (2 * j)
      = (1 - (-1 : ℝ) ^ (L : ℕ) * t ^ (2 * L)) / (1 + t ^ 2) := by
    have hterm : ∀ j ∈ Finset.range L,
        (-1 : ℝ) ^ (j : ℕ) * t ^ (2 * j) = ((-1 : ℝ) * t ^ 2) ^ (j : ℕ) := by
      intro j _
      rw [mul_pow, ← pow_mul]
    have hne : ((-1 : ℝ) * t ^ 2) ≠ 1 := by
      intro h
      have h2 : t ^ 2 = -1 := by linarith
      linarith [sq_nonneg t]
    have hpos : (1 : ℝ) + t ^ 2 ≠ 0 := by positivity
    have hne2 : ((-1 : ℝ) * t ^ 2 - 1) ≠ 0 := by
      intro h
      have h3 : (-1 : ℝ) * t ^ 2 = 1 := by linarith
      have h4 : t ^ 2 = -1 := by linarith
      linarith [sq_nonneg t]
    have hkey : ((-1 : ℝ) * t ^ 2) ^ (L : ℕ) = (-1 : ℝ) ^ (L : ℕ) * t ^ (2 * L) := by
      rw [mul_pow, ← pow_mul]
    rw [Finset.sum_congr rfl hterm, geom_sum_eq hne, hkey,
      div_eq_div_iff hne2 hpos]
    ring
  have hd := (Real.hasDerivAt_arctan t).sub (hasDerivAt_atanPoly L t)
  rw [hsum] at hd
  refine hd.congr_deriv ?_
  field_simp
  ring

/-- Every natural power of minus one lies between minus one and one. -/
private theorem neg_one_pow_bounds (L : ℕ) :
    (-1 : ℝ) ≤ (-1 : ℝ) ^ (L : ℕ) ∧ (-1 : ℝ) ^ (L : ℕ) ≤ 1 := by
  have habs : |(-1 : ℝ) ^ (L : ℕ)| ≤ 1 := by
    rw [abs_pow, abs_neg, abs_one, one_pow]
  exact abs_le.mp habs

/-- The first omitted power term minus the arctangent remainder is monotone on the nonnegative
reals. -/
private theorem monotoneOn_compensate_sub (L : ℕ) :
    MonotoneOn (fun t : ℝ => t ^ (2 * L + 1) / (2 * L + 1)
      - (Real.arctan t - atanPoly L t)) (Set.Ici 0) := by
  have hdiff : Differentiable ℝ (fun t : ℝ => t ^ (2 * L + 1) / (2 * L + 1)
      - (Real.arctan t - atanPoly L t)) := by
    intro u
    have h1 := (hasDerivAt_id u).pow (2 * L + 1)
    exact ((h1.div_const (2 * L + 1)).sub
      (hasDerivAt_arctan_sub_atanPoly L u)).differentiableAt
  refine monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ)) hdiff.continuous.continuousOn
    (hdiff.differentiableOn.mono interior_subset) ?_
  rw [interior_Ici]
  intro u hu
  have hu' : 0 ≤ u := (Set.mem_Ioi.mp hu).le
  have hsign := (neg_one_pow_bounds L).2
  have hderiv : HasDerivAt (fun t : ℝ => t ^ (2 * L + 1) / (2 * L + 1)
      - (Real.arctan t - atanPoly L t))
      (u ^ (2 * L) * ((1 + u ^ 2) - (-1 : ℝ) ^ (L : ℕ)) / (1 + u ^ 2)) u := by
    have h1 : HasDerivAt (fun t : ℝ => t ^ (2 * L + 1))
        ((2 * L + 1) * u ^ (2 * L)) u := by
      simpa [id_eq] using! (hasDerivAt_id u).pow (2 * L + 1)
    have hA : HasDerivAt (fun t : ℝ => t ^ (2 * L + 1) / (2 * L + 1))
        (u ^ (2 * L)) u :=
      (h1.div_const (2 * L + 1)).congr_deriv (by field_simp)
    exact (hA.sub (hasDerivAt_arctan_sub_atanPoly L u)).congr_deriv (by field_simp)
  rw [hderiv.deriv]
  refine div_nonneg (mul_nonneg (pow_nonneg hu' (2 * L)) ?_) (by positivity)
  nlinarith [sq_nonneg u, hsign]

/-- The first omitted power term plus the arctangent remainder is monotone on the nonnegative
reals. -/
private theorem monotoneOn_compensate_add (L : ℕ) :
    MonotoneOn (fun t : ℝ => t ^ (2 * L + 1) / (2 * L + 1)
      + (Real.arctan t - atanPoly L t)) (Set.Ici 0) := by
  have hdiff : Differentiable ℝ (fun t : ℝ => t ^ (2 * L + 1) / (2 * L + 1)
      + (Real.arctan t - atanPoly L t)) := by
    intro u
    have h1 := (hasDerivAt_id u).pow (2 * L + 1)
    exact ((h1.div_const (2 * L + 1)).add
      (hasDerivAt_arctan_sub_atanPoly L u)).differentiableAt
  refine monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ)) hdiff.continuous.continuousOn
    (hdiff.differentiableOn.mono interior_subset) ?_
  rw [interior_Ici]
  intro u hu
  have hu' : 0 ≤ u := (Set.mem_Ioi.mp hu).le
  have hsign := neg_one_pow_bounds L
  have hderiv : HasDerivAt (fun t : ℝ => t ^ (2 * L + 1) / (2 * L + 1)
      + (Real.arctan t - atanPoly L t))
      (u ^ (2 * L) * ((1 + u ^ 2) + (-1 : ℝ) ^ (L : ℕ)) / (1 + u ^ 2)) u := by
    have h1 : HasDerivAt (fun t : ℝ => t ^ (2 * L + 1))
        ((2 * L + 1) * u ^ (2 * L)) u := by
      simpa [id_eq] using! (hasDerivAt_id u).pow (2 * L + 1)
    have hA : HasDerivAt (fun t : ℝ => t ^ (2 * L + 1) / (2 * L + 1))
        (u ^ (2 * L)) u :=
      (h1.div_const (2 * L + 1)).congr_deriv (by field_simp)
    exact (hA.add (hasDerivAt_arctan_sub_atanPoly L u)).congr_deriv (by field_simp)
  rw [hderiv.deriv]
  refine div_nonneg (mul_nonneg (pow_nonneg hu' (2 * L)) ?_) (by positivity)
  nlinarith [sq_nonneg u, hsign.1, hsign.2]

/-- Every arctangent partial-sum polynomial vanishes at zero. -/
private theorem atanPoly_zero (L : ℕ) : atanPoly L 0 = 0 := by
  rw [atanPoly]
  exact Finset.sum_eq_zero fun j _ => by simp

/-- For nonnegative `t`, the arctangent remainder is bounded in absolute value by `t^(2 * L + 1)
/ (2 * L + 1)`. -/
private theorem arctan_series_remainder_nonneg (L : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    |Real.arctan t - atanPoly L t| ≤ t ^ (2 * L + 1) / (2 * L + 1) := by
  have hzero : ((0 : ℝ) ^ (2 * L + 1) / (2 * L + 1)
      - (Real.arctan 0 - atanPoly L 0)) = 0 := by
    simp [atanPoly_zero]
  have hzero' : ((0 : ℝ) ^ (2 * L + 1) / (2 * L + 1)
      + (Real.arctan 0 - atanPoly L 0)) = 0 := by
    simp [atanPoly_zero]
  have hm1 := monotoneOn_compensate_sub L (Set.mem_Ici.mpr (le_refl 0))
    (Set.mem_Ici.mpr ht) ht
  have hm2 := monotoneOn_compensate_add L (Set.mem_Ici.mpr (le_refl 0))
    (Set.mem_Ici.mpr ht) ht
  exact abs_le.mpr ⟨by linarith [hzero, hm1], by linarith [hzero', hm2]⟩

/-- The arctangent partial-sum polynomial is odd. -/
private theorem atanPoly_neg (L : ℕ) (t : ℝ) :
    atanPoly L (-t) = -atanPoly L t := by
  rw [atanPoly, atanPoly, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hoddN : Odd (2 * j + 1) := ⟨j, by ring⟩
  have hodd : (-t) ^ (2 * j + 1) = -(t ^ (2 * j + 1)) := by
    rw [neg_pow, hoddN.neg_one_pow]
    ring
  rw [hodd]
  ring

/-- For rational inputs of absolute value at most `1 / 2`, the arctangent partial sum has error
bounded by the absolute first omitted term. -/
theorem rational_arctan_series_explicit_remainder (x : ℚ) (L : ℕ)
    (_hx : |(x : ℝ)| ≤ 1 / 2) :
    |((atanRatSeries x L : ℚ) : ℝ) - Real.arctan (x : ℝ)|
      ≤ |(x : ℝ)| ^ (2 * L + 1) / (2 * (L : ℝ) + 1) := by
  rw [atanRatSeries_cast]
  rcases le_or_gt 0 (x : ℝ) with hpos | hneg
  · rw [abs_of_nonneg hpos, abs_sub_comm]
    exact arctan_series_remainder_nonneg L _ hpos
  · have hu : 0 ≤ -((x : ℝ)) := by linarith
    have heq : atanPoly L ((x : ℝ)) - Real.arctan ((x : ℝ))
        = Real.arctan (-((x : ℝ))) - atanPoly L (-((x : ℝ))) := by
      rw [atanPoly_neg, Real.arctan_neg]
      ring
    have habs : |((x : ℝ))| ^ (2 * L + 1) = (-(x : ℝ)) ^ (2 * L + 1) := by
      rw [show |((x : ℝ))| = -((x : ℝ)) from abs_of_neg hneg]
    rw [heq, habs]
    exact arctan_series_remainder_nonneg L _ hu

/-- Machin's identity expresses π as `16 * arctan(1 / 5) - 4 * arctan(1 / 239)`. -/
theorem rational_machin_pi_identity :
    16 * Real.arctan ((1 / 5 : ℝ)) - 4 * Real.arctan ((1 / 239 : ℝ)) = Real.pi := by
  have h1 : Real.arctan ((1 / 5 : ℝ)) + Real.arctan ((1 / 5 : ℝ))
      = Real.arctan ((5 / 12 : ℝ)) := by
    rw [Real.arctan_add (by norm_num : ((1 / 5 : ℝ)) * ((1 / 5 : ℝ)) < 1)]
    congr 1
    norm_num
  have h2 : Real.arctan ((5 / 12 : ℝ)) + Real.arctan ((5 / 12 : ℝ))
      = Real.arctan ((120 / 119 : ℝ)) := by
    rw [Real.arctan_add (by norm_num : ((5 / 12 : ℝ)) * ((5 / 12 : ℝ)) < 1)]
    congr 1
    norm_num

  have h3 : Real.arctan ((120 / 119 : ℝ)) - Real.arctan ((1 / 239 : ℝ))
      = Real.arctan ((1 : ℝ)) := by
    have ht : Real.arctan ((1 / 239 : ℝ))
        + Real.arctan (((120 / 119 : ℝ) - (1 / 239 : ℝ))
          / (1 + (120 / 119 : ℝ) * (1 / 239 : ℝ)))
        = Real.arctan ((120 / 119 : ℝ)) := by
      rw [Real.arctan_add
        (by norm_num : ((1 / 239 : ℝ)) * (((120 / 119 : ℝ) - (1 / 239 : ℝ))
          / (1 + (120 / 119 : ℝ) * (1 / 239 : ℝ))) < 1)]
      congr 1
      norm_num
    have hratio : ((120 / 119 : ℝ) - (1 / 239 : ℝ))
        / (1 + (120 / 119 : ℝ) * (1 / 239 : ℝ)) = 1 := by
      norm_num
    rw [hratio] at ht
    linarith [Real.arctan_one]
  have h4 : 4 * Real.arctan ((1 / 5 : ℝ)) = Real.arctan ((120 / 119 : ℝ)) := by
    have h41 : 2 * Real.arctan ((1 / 5 : ℝ)) = Real.arctan ((5 / 12 : ℝ)) := by
      rw [two_mul, h1]
    have h42 : 2 * Real.arctan ((5 / 12 : ℝ)) = Real.arctan ((120 / 119 : ℝ)) := by
      rw [two_mul, h2]
    rw [show (4 : ℝ) * Real.arctan ((1 / 5 : ℝ))
        = 2 * (2 * Real.arctan ((1 / 5 : ℝ))) from by ring, h41, h42]
  have h5 : 4 * (Real.arctan ((120 / 119 : ℝ)) - Real.arctan ((1 / 239 : ℝ))) = Real.pi := by
    rw [h3, Real.arctan_one]
    ring
  have hsplit : 16 * Real.arctan ((1 / 5 : ℝ)) - 4 * Real.arctan ((1 / 239 : ℝ))
      = 4 * (4 * Real.arctan ((1 / 5 : ℝ)) - Real.arctan ((1 / 239 : ℝ))) := by ring
  rw [hsplit, h4]
  linarith [h5]

/-- The rational Machin approximation using `k + 3` terms of each arctangent series. -/
def piRatApprox (k : ℕ) : ℚ :=
  16 * atanRatSeries ((1 / 5 : ℚ)) (k + 3) - 4 * atanRatSeries ((1 / 239 : ℚ)) (k + 3)

/-- The rational Machin approximation has error at most `20 / 5^(2 * k + 7)`. -/
private theorem piRatApprox_error_le (k : ℕ) :
    |((piRatApprox k : ℚ) : ℝ) - Real.pi| ≤ 20 / ((5 : ℝ) ^ (2 * k + 7)) := by
  have hL : 2 * (k + 3) + 1 = 2 * k + 7 := by omega
  have hA := rational_arctan_series_explicit_remainder ((1 / 5 : ℚ)) (k + 3) (by norm_num)
  have hB := rational_arctan_series_explicit_remainder ((1 / 239 : ℚ)) (k + 3) (by norm_num)
  rw [hL] at hA hB
  have hcA : (((1 / 5 : ℚ) : ℝ)) = ((1 / 5 : ℝ)) := by norm_num
  have hcB : (((1 / 239 : ℚ) : ℝ)) = ((1 / 239 : ℝ)) := by norm_num
  rw [hcA] at hA
  rw [hcB] at hB
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 5)] at hA
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 239)] at hB
  have hA2 : |(((atanRatSeries ((1 / 5 : ℚ)) (k + 3) : ℚ) : ℝ))
        - Real.arctan ((1 / 5 : ℝ))| ≤ ((1 / 5 : ℝ) ^ (2 * k + 7)) :=
    hA.trans (div_le_self (pow_nonneg (by norm_num) _)
      (by exact_mod_cast (show (1 : ℕ) ≤ 2 * k + 7 by omega)))
  have hB2 : |(((atanRatSeries ((1 / 239 : ℚ)) (k + 3) : ℚ) : ℝ))
        - Real.arctan ((1 / 239 : ℝ))| ≤ ((1 / 239 : ℝ) ^ (2 * k + 7)) :=
    hB.trans (div_le_self (pow_nonneg (by norm_num) _)
      (by exact_mod_cast (show (1 : ℕ) ≤ 2 * k + 7 by omega)))
  have hineq : ((piRatApprox k : ℚ) : ℝ) - Real.pi
      = 16 * ((((atanRatSeries ((1 / 5 : ℚ)) (k + 3) : ℚ) : ℝ)) - Real.arctan ((1 / 5 : ℝ)))
        - 4 * ((((atanRatSeries ((1 / 239 : ℚ)) (k + 3) : ℚ) : ℝ))
          - Real.arctan ((1 / 239 : ℝ))) := by
    have hpi := rational_machin_pi_identity
    unfold piRatApprox
    push_cast at hpi ⊢
    linarith [hpi]
  have hX : |(16 : ℝ) * ((((atanRatSeries ((1 / 5 : ℚ)) (k + 3) : ℚ) : ℝ))
        - Real.arctan ((1 / 5 : ℝ)))|
      ≤ 16 * ((1 / 5 : ℝ) ^ (2 * k + 7)) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 16)]
    exact mul_le_mul_of_nonneg_left hA2 (by norm_num : (0 : ℝ) ≤ 16)
  have hY : |(4 : ℝ) * ((((atanRatSeries ((1 / 239 : ℚ)) (k + 3) : ℚ) : ℝ))
        - Real.arctan ((1 / 239 : ℝ)))|
      ≤ 4 * ((1 / 239 : ℝ) ^ (2 * k + 7)) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    exact mul_le_mul_of_nonneg_left hB2 (by norm_num : (0 : ℝ) ≤ 4)
  have htri : |16 * ((((atanRatSeries ((1 / 5 : ℚ)) (k + 3) : ℚ) : ℝ))
        - Real.arctan ((1 / 5 : ℝ)))
      - 4 * ((((atanRatSeries ((1 / 239 : ℚ)) (k + 3) : ℚ) : ℝ))
        - Real.arctan ((1 / 239 : ℝ)))|
      ≤ 16 * ((1 / 5 : ℝ) ^ (2 * k + 7)) + 4 * ((1 / 239 : ℝ) ^ (2 * k + 7)) :=
    (abs_sub _ _).trans (add_le_add hX hY)
  rw [hineq]
  refine htri.trans ?_
  have h239 : (1 / 239 : ℝ) ^ (2 * k + 7) ≤ 1 / ((5 : ℝ) ^ (2 * k + 7)) := by
    rw [div_pow, one_pow]
    exact one_div_le_one_div_of_le (by positivity) (by gcongr; norm_num)
  have hfive : ((1 / 5 : ℝ) ^ (2 * k + 7)) = 1 / ((5 : ℝ) ^ (2 * k + 7)) := by
    rw [div_pow, one_pow]
  calc 16 * ((1 / 5 : ℝ) ^ (2 * k + 7)) + 4 * ((1 / 239 : ℝ) ^ (2 * k + 7))
      ≤ 16 * (1 / ((5 : ℝ) ^ (2 * k + 7))) + 4 * (1 / ((5 : ℝ) ^ (2 * k + 7))) :=
        add_le_add (mul_le_mul_of_nonneg_left hfive.le (by norm_num : (0 : ℝ) ≤ 16))
          (mul_le_mul_of_nonneg_left h239 (by norm_num : (0 : ℝ) ≤ 4))
    _ = 20 / ((5 : ℝ) ^ (2 * k + 7)) := by ring

/-- The power of five dominates `20 * 2^(k + 2)`, as needed for the dyadic precision estimate. -/
private theorem twenty_two_pow_le (k : ℕ) :
    (20 : ℝ) * ((2 : ℝ) ^ (k + 2)) ≤ ((5 : ℝ) ^ (2 * k + 7)) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      have h2 : ((2 : ℝ) ^ (k + 1 + 2)) = 2 * ((2 : ℝ) ^ (k + 2)) := by
        rw [show k + 1 + 2 = k + 2 + 1 from by omega, pow_succ]
        ring
      have h5 : ((5 : ℝ) ^ (2 * (k + 1) + 7)) = 25 * ((5 : ℝ) ^ (2 * k + 7)) := by
        rw [show 2 * (k + 1) + 7 = 2 * k + 7 + 2 from by omega, pow_add,
          show (5 : ℝ) ^ 2 = 25 from by norm_num]
        ring
      rw [h2, h5]
      nlinarith [ih, pow_nonneg (by norm_num : (0 : ℝ) ≤ 5) (2 * k + 7)]

/-- Machin's identity holds, and each computed rational approximation lies strictly between zero
and four with error at most `2^(-(k + 2))`. -/
theorem rational_machin_pi_computed_precision :
    16 * Real.arctan ((1 / 5 : ℝ)) - 4 * Real.arctan ((1 / 239 : ℝ)) = Real.pi ∧
    ∀ k : ℕ, 0 < piRatApprox k ∧ piRatApprox k < 4 ∧
      |((piRatApprox k : ℚ) : ℝ) - Real.pi| ≤ ((2 : ℝ) ⁻¹) ^ (k + 2) := by
  refine ⟨rational_machin_pi_identity, fun k => ?_⟩
  have herr := piRatApprox_error_le k

  have h57 : ((5 : ℝ) ^ 7) ≤ ((5 : ℝ) ^ (2 * k + 7)) := by
    have h1 : ((5 : ℕ) ^ 7) ≤ ((5 : ℕ) ^ (2 * k + 7)) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    exact_mod_cast h1
  have herr' : |((piRatApprox k : ℚ) : ℝ) - Real.pi| ≤ 20 / ((5 : ℝ) ^ 7) := by
    have h1 : 1 / ((5 : ℝ) ^ (2 * k + 7)) ≤ 1 / ((5 : ℝ) ^ 7) :=
      one_div_le_one_div_of_le (by positivity) h57
    simp only [← inv_eq_one_div] at h1
    refine herr.trans ?_
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 20)
  rw [show ((5 : ℝ) ^ 7) = 78125 from by norm_num] at herr'
  have hsmall : (20 : ℝ) / 78125 < 1 / 300 := by norm_num

  have hA1 := rational_arctan_series_explicit_remainder ((1 / 5 : ℚ)) 1 (by norm_num)
  have hB1 := rational_arctan_series_explicit_remainder ((1 / 239 : ℚ)) 1 (by norm_num)
  rw [atanRatSeries_cast, atanPoly_one] at hA1 hB1
  push_cast at hA1 hB1
  have hA1abs := abs_le.mp hA1
  have hB1abs := abs_le.mp hB1

  have hpiup : Real.pi ≤ 16 * ((1 / 5 : ℝ) + (1 / 5 : ℝ) ^ 3 / 3)
      - 4 * ((1 / 239 : ℝ) - (1 / 239 : ℝ) ^ 3 / 3) := by
    have hid := rational_machin_pi_identity
    have hAup : Real.arctan ((1 / 5 : ℝ)) ≤ (1 / 5 : ℝ) + (1 / 5 : ℝ) ^ 3 / 3 := by
      linarith [hA1abs.1]
    have hBlow : Real.arctan ((1 / 239 : ℝ)) ≥ (1 / 239 : ℝ) - (1 / 239 : ℝ) ^ 3 / 3 := by
      linarith [hB1abs.2]
    nlinarith [hid, hAup, hBlow]
  have hnum : 16 * ((1 / 5 : ℝ) + (1 / 5 : ℝ) ^ 3 / 3)
      - 4 * ((1 / 239 : ℝ) - (1 / 239 : ℝ) ^ 3 / 3) < 4 - 1 / 300 := by norm_num
  refine ⟨?_, ?_, ?_⟩
  · have h1 := (abs_le.mp herr').1
    have hposR : (0 : ℝ) < ((piRatApprox k : ℚ) : ℝ) := by
      have h3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
      linarith
    exact Rat.cast_pos.mp hposR
  · have h1 := (abs_le.mp herr').2
    have hltR : ((piRatApprox k : ℚ) : ℝ) < 4 := by
      linarith [hpiup, hnum]
    exact Rat.cast_lt.mp hltR
  · refine herr.trans ?_
    rw [show ((2 : ℝ) ⁻¹) ^ (k + 2) = 1 / ((2 : ℝ) ^ (k + 2)) from by
        rw [inv_eq_one_div, one_div_pow],
      div_le_div_iff₀ (by positivity) (by positivity)]
    linarith [twenty_two_pow_le k]

end Qatlib.Concepts.AmplitudeCore.PreparedReadout
