/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PolyRotation.PolyRotationTaylorBiasStat
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Choose.Central

/-!
# Taylor bias of polynomial payoff rotations

This module proves a uniform remainder bound for the truncated arcsine series by studying
normalized residuals and their derivatives. It transfers the remainder estimate to the
squared-sine payoff in `riskPolyRotationTaylorBias`.

The polynomial payoff-rotation setting is described in [WoernerEgger2019].

## Main statements

* `arcPartial_tail_bound`: For `|x| ≤ 1`, the arcsine partial-sum error is at most
  `riskArcsinTail u * |x| ^ (2 * u + 3)`.
* `riskPolyRotationTaylorBias`: For `0 < c ≤ 1` and `y ∈ [0, 1]`, the polynomial rotation
  probability differs from its affine target by at most `riskArcsinTail u * c ^ (2 * u + 3) /
  2`; see [WoernerEgger2019].

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib.Concepts.RiskEstimation.PolyReadout

namespace Qatlib.Concepts.RiskEstimation.PolyRotation

open Set
open scoped Classical BigOperators Topology

/-- If a continuous function vanishes at zero and its derivative divided by `x ^ n` is monotone
on `(0, 1)`, then the function divided by `x ^ (n + 1)` is monotone there. -/
private theorem quotient_power_monotone (n : ℕ) (f f' : ℝ → ℝ)
    (hc : ContinuousOn f (Ico 0 1)) (hzero : f 0 = 0)
    (hd : ∀ x ∈ Ioo 0 1, HasDerivAt f (f' x) x)
    (hm : MonotoneOn (fun x => f' x / x ^ n) (Ioo 0 1)) :
    MonotoneOn (fun x => f x / x ^ (n + 1)) (Ioo 0 1) := by
  have hcrit (x : ℝ) (hx : x ∈ Ioo 0 1) : (n + 1 : ℝ) * f x ≤ x * f' x := by
    have hcont : ContinuousOn f (Icc 0 x) := hc.mono (fun t ht => ⟨ht.1, ht.2.trans_lt hx.2⟩)
    obtain ⟨t, ht, he⟩ := exists_ratio_hasDerivAt_eq_ratio_slope f f' hx.1 hcont
      (fun t ht => hd t ⟨ht.1, ht.2.trans hx.2⟩)
      (fun t : ℝ => t ^ (n + 1)) (fun t : ℝ => (n + 1 : ℝ) * t ^ n)
      (continuous_id.pow (n + 1)).continuousOn
      (fun t _ => by simpa only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] using! hasDerivAt_pow (n + 1) t)
    simp only [zero_pow (Nat.succ_ne_zero n), hzero, sub_zero] at he
    have hb := hm ⟨ht.1, ht.2.trans hx.2⟩ hx ht.2.le
    have hb' := (div_le_div_iff₀ (pow_pos ht.1 n) (pow_pos hx.1 n)).mp hb
    have hh : ((n + 1 : ℝ) * f x) * t ^ n ≤ (x * f' x) * t ^ n := by
      have hmul := mul_le_mul_of_nonneg_left hb' hx.1.le
      rw [pow_succ] at he
      nlinarith
    exact (mul_le_mul_iff_left₀ (pow_pos ht.1 n)).mp hh
  have hq (x : ℝ) (hx : x ∈ Ioo 0 1) :
      HasDerivAt (fun x => f x / x ^ (n + 1))
        ((f' x * x ^ (n + 1) - f x * ((n + 1 : ℝ) * x ^ n)) / (x ^ (n + 1)) ^ 2) x := by
    convert! (hd x hx).div (hasDerivAt_pow (n + 1) x) (pow_ne_zero _ hx.1.ne') using 1
    all_goals simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  apply monotoneOn_of_deriv_nonneg (convex_Ioo 0 1)
  · exact (hc.mono (fun _ hx => ⟨hx.1.le, hx.2⟩)).div
      (continuous_id.pow (n + 1)).continuousOn (fun _ hx => pow_ne_zero _ hx.1.ne')
  · rw [isOpen_Ioo.interior_eq]
    exact fun x hx => (hq x hx).differentiableAt.differentiableWithinAt
  · rw [isOpen_Ioo.interior_eq]
    intro x hx
    rw [(hq x hx).deriv]
    have hn : 0 ≤ f' x * x ^ (n + 1) - f x * ((n + 1 : ℝ) * x ^ n) := by
      have hh := mul_nonneg (pow_nonneg hx.1.le n) (sub_nonneg.mpr (hcrit x hx))
      rw [pow_succ]
      nlinarith
    exact div_nonneg hn (sq_nonneg _)

/-- The normalized central-binomial coefficient `Nat.centralBinom j / 4 ^ j`. -/
private noncomputable def rootCoeff (j : ℕ) : ℝ := (Nat.centralBinom j : ℝ) / 4 ^ j

/-- The normalized central-binomial coefficient is nonnegative. -/
private theorem rootCoeff_nonneg (j : ℕ) : 0 ≤ rootCoeff j := by unfold rootCoeff; positivity

/-- The normalized coefficients satisfy `(2 * j + 2) * rootCoeff (j + 1) = (2 * j + 1) *
rootCoeff j`. -/
private theorem rootCoeff_recurrence (j : ℕ) :
    (2 * j + 2 : ℝ) * rootCoeff (j + 1) = (2 * j + 1) * rootCoeff j := by
  have h := congrArg (fun n : ℕ => (n : ℝ)) (Nat.succ_mul_centralBinom_succ j)
  push_cast at h
  unfold rootCoeff
  rw [pow_succ]
  field_simp
  nlinarith

/-- Multiplying the `j`th arcsine coefficient by `2 * j + 1` gives `rootCoeff j`. -/
private theorem arcsinCoeff_derivative (j : ℕ) :
    (2 * j + 1 : ℝ) * riskArcsinCoeff j = rootCoeff j := by
  unfold riskArcsinCoeff rootCoeff
  rw [Nat.centralBinom_eq_two_mul_choose]
  field_simp

/-- The odd arcsine-series partial sum through degree `2 * u + 1`. -/
private noncomputable def arcPartial (u : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (u + 1), riskArcsinCoeff j * x ^ (2 * j + 1)

/-- The even inverse-square-root-series partial sum through degree `2 * u`. -/
private noncomputable def rootPartial (u : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (u + 1), rootCoeff j * x ^ (2 * j)

/-- The derivative of the arcsine partial sum is the corresponding root partial sum. -/
private theorem arcPartial_deriv (u : ℕ) (x : ℝ) :
    HasDerivAt (arcPartial u) (rootPartial u x) x := by
  have h := HasDerivAt.fun_sum (u := Finset.range (u + 1))
    (fun j _ => (hasDerivAt_pow (2 * j + 1) x).const_mul (riskArcsinCoeff j))
  convert! h using 1
  simp only [rootPartial, Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro j _
  rw [← arcsinCoeff_derivative]
  push_cast
  ring

/-- The derivative of the root partial sum satisfies the stated identity after multiplication by
`1 - x²`. -/
private theorem rootPartial_deriv_equation (u : ℕ) (x : ℝ) :
    ∃ q : ℝ, HasDerivAt (rootPartial u) q x ∧
      (1 - x ^ 2) * q = x * rootPartial u x - (2 * u + 1) * rootCoeff u * x ^ (2 * u + 1) := by
  induction u with
  | zero =>
    refine ⟨0, ?_, ?_⟩
    · have hfun : rootPartial 0 = fun _ : ℝ => 1 := by funext t; simp [rootPartial, rootCoeff]
      rw [hfun]
      exact hasDerivAt_const x (1 : ℝ)
    · simp [rootPartial, rootCoeff]
  | succ u ih =>
    obtain ⟨q, hq, he⟩ := ih
    have hfun : rootPartial (u + 1) = fun t => rootPartial u t + rootCoeff (u + 1) * t ^ (2 * u + 2) := by
      funext t
      simp [rootPartial, Finset.sum_range_succ, show 2 * (u + 1) = 2 * u + 2 by omega]
    have hd := hq.add ((hasDerivAt_pow (2 * u + 2) x).const_mul (rootCoeff (u + 1)))
    simp only [Pi.add_def] at hd
    rw [← hfun] at hd
    refine ⟨q + rootCoeff (u + 1) * ((2 * u + 2 : ℝ) * x ^ (2 * u + 1)), ?_, ?_⟩
    · simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat,
        show 2 * u + 2 - 1 = 2 * u + 1 by omega] using! hd
    · rw [hfun]
      have hr := rootCoeff_recurrence u
      have hpow : x ^ (2 * (u + 1) + 1) = x ^ (2 * u + 1) * x ^ 2 := by
        rw [← pow_add]
        congr 1
      have hpow' : x * x ^ (2 * u + 2) = x ^ (2 * u + 1) * x ^ 2 := by
        rw [← pow_succ', ← pow_add]
      rw [hpow]
      push_cast
      linear_combination he + x ^ (2 * u + 1) * hr - rootCoeff (u + 1) * hpow'

/-- The root partial sum takes value one at zero. -/
private theorem rootPartial_zero (u : ℕ) : rootPartial u 0 = 1 := by
  unfold rootPartial
  rw [Finset.sum_eq_single 0]
  · simp [rootCoeff]
  · intro j _ hj
    have he : 2 * j ≠ 0 := by omega
    simp [zero_pow he]
  · simp

/-- The square root of `1 - x²` is positive for `x ∈ (0, 1)`. -/
private theorem density_pos (x : ℝ) (hx : x ∈ Ioo 0 1) : 0 < Real.sqrt (1 - x ^ 2) :=
  Real.sqrt_pos.mpr (by nlinarith [hx.1, hx.2])

/-- On `(0, 1)`, the derivative of `sqrt (1 - x²)` is `-x / sqrt (1 - x²)`. -/
private theorem density_deriv (x : ℝ) (hx : x ∈ Ioo 0 1) :
    HasDerivAt (fun t : ℝ => Real.sqrt (1 - t ^ 2)) (-x / Real.sqrt (1 - x ^ 2)) x := by
  have hD : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have hS := density_pos x hx
  convert! (Real.hasDerivAt_sqrt hD.ne').comp x
    ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_pow 2 x)) using 1
  all_goals simp only [Nat.cast_ofNat, zero_sub]
  all_goals field_simp [hS.ne']
  all_goals ring

/-- The function `1 / sqrt (1 - x²)` is monotone on `(0, 1)`. -/
private theorem inverse_density_monotone :
    MonotoneOn (fun x : ℝ => 1 / Real.sqrt (1 - x ^ 2)) (Ioo 0 1) := by
  intro x hx y hy hxy
  apply div_le_div_of_nonneg_left (by norm_num) (density_pos y hy)
  apply Real.sqrt_le_sqrt
  nlinarith [hx.1, hy.1]

/-- The residual `1 - sqrt (1 - x²) * rootPartial u x`. -/
private noncomputable def rootResidual (u : ℕ) (x : ℝ) : ℝ :=
  1 - Real.sqrt (1 - x ^ 2) * rootPartial u x

/-- The explicit slope `(2 * u + 1) * rootCoeff u * x ^ (2 * u + 1) / sqrt (1 - x²)` of the root
residual on `(0, 1)`. -/
private noncomputable def rootResidualSlope (u : ℕ) (x : ℝ) : ℝ :=
  (2 * u + 1 : ℝ) * rootCoeff u * x ^ (2 * u + 1) / Real.sqrt (1 - x ^ 2)

/-- The difference between arcsine and its odd partial sum. -/
private noncomputable def arcResidual (u : ℕ) (x : ℝ) : ℝ := Real.arcsin x - arcPartial u x

/-- The explicit slope `rootResidual u x / sqrt (1 - x²)` of the arcsine residual on `(0, 1)`. -/
private noncomputable def arcResidualSlope (u : ℕ) (x : ℝ) : ℝ :=
  rootResidual u x / Real.sqrt (1 - x ^ 2)

/-- The root residual is continuous on the real line. -/
private theorem rootResidual_continuous (u : ℕ) : Continuous (rootResidual u) := by
  unfold rootResidual rootPartial
  fun_prop

/-- The arcsine residual is continuous on the real line. -/
private theorem arcResidual_continuous (u : ℕ) : Continuous (arcResidual u) := by
  unfold arcResidual arcPartial
  fun_prop

/-- The root residual vanishes at zero. -/
private theorem rootResidual_zero (u : ℕ) : rootResidual u 0 = 0 := by
  simp [rootResidual, rootPartial_zero]

/-- The arcsine residual vanishes at zero. -/
private theorem arcResidual_zero (u : ℕ) : arcResidual u 0 = 0 := by
  simp [arcResidual, arcPartial]

/-- The derivative of the root residual on `(0, 1)` equals `rootResidualSlope`. -/
private theorem rootResidual_deriv (u : ℕ) (x : ℝ) (hx : x ∈ Ioo 0 1) :
    HasDerivAt (rootResidual u) (rootResidualSlope u x) x := by
  obtain ⟨q, hq, he⟩ := rootPartial_deriv_equation u x
  have hS := density_pos x hx
  have hs := Real.sq_sqrt (show 0 ≤ 1 - x ^ 2 by nlinarith [hx.1, hx.2])
  convert! (hasDerivAt_const x (1 : ℝ)).sub ((density_deriv x hx).mul hq) using 1
  · dsimp [rootResidualSlope]
    field_simp [hS.ne']
    nlinarith [congrArg (fun t : ℝ => t * q) hs]

/-- The derivative of the arcsine residual on `(0, 1)` equals `arcResidualSlope`. -/
private theorem arcResidual_deriv (u : ℕ) (x : ℝ) (hx : x ∈ Ioo 0 1) :
    HasDerivAt (arcResidual u) (arcResidualSlope u x) x := by
  have hS := density_pos x hx
  convert! (Real.hasDerivAt_arcsin (by linarith [hx.1]) hx.2.ne).sub (arcPartial_deriv u x) using 1
  · dsimp [arcResidualSlope, rootResidual]
    field_simp [hS.ne']

/-- The root residual slope divided by `x ^ (2 * u + 1)` is monotone on `(0, 1)`. -/
private theorem rootSlope_ratio_monotone (u : ℕ) :
    MonotoneOn (fun x => rootResidualSlope u x / x ^ (2 * u + 1)) (Ioo 0 1) := by
  have he (x : ℝ) (hx : x ∈ Ioo 0 1) :
      rootResidualSlope u x / x ^ (2 * u + 1) =
        ((2 * u + 1 : ℝ) * rootCoeff u) * (1 / Real.sqrt (1 - x ^ 2)) := by
    unfold rootResidualSlope
    field_simp [pow_ne_zero _ hx.1.ne']
  intro x hx y hy hxy
  (try dsimp only)
  rw [he x hx, he y hy]
  exact mul_le_mul_of_nonneg_left (inverse_density_monotone hx hy hxy)
    (mul_nonneg (by positivity) (rootCoeff_nonneg u))

/-- The root residual divided by `x ^ (2 * u + 2)` is monotone on `(0, 1)`. -/
private theorem rootResidual_ratio_monotone (u : ℕ) :
    MonotoneOn (fun x => rootResidual u x / x ^ (2 * u + 2)) (Ioo 0 1) := by
  simpa only [show 2 * u + 1 + 1 = 2 * u + 2 by omega] using!
    quotient_power_monotone (2 * u + 1) (rootResidual u) (rootResidualSlope u)
      (rootResidual_continuous u).continuousOn (rootResidual_zero u)
      (rootResidual_deriv u) (rootSlope_ratio_monotone u)

/-- A function continuous on `[0, 1)`, vanishing at zero, and having nonnegative derivative on
`(0, 1)` is nonnegative at every point of `(0, 1)`. -/
private theorem primitive_nonneg (f f' : ℝ → ℝ) (hc : ContinuousOn f (Ico 0 1)) (hzero : f 0 = 0)
    (hd : ∀ x ∈ Ioo 0 1, HasDerivAt f (f' x) x)
    (hp : ∀ x ∈ Ioo 0 1, 0 ≤ f' x) (x : ℝ) (hx : x ∈ Ioo 0 1) : 0 ≤ f x := by
  obtain ⟨t, ht, he⟩ := exists_hasDerivAt_eq_slope f f' hx.1
    (hc.mono (fun t ht => ⟨ht.1, ht.2.trans_lt hx.2⟩))
    (fun t ht => hd t ⟨ht.1, ht.2.trans hx.2⟩)
  simp only [hzero, sub_zero] at he
  have hpt := hp t ⟨ht.1, ht.2.trans hx.2⟩
  field_simp [hx.1.ne'] at he
  rw [← he]
  exact mul_nonneg hpt hx.1.le

/-- The root residual is nonnegative on `(0, 1)`. -/
private theorem rootResidual_nonneg (u : ℕ) (x : ℝ) (hx : x ∈ Ioo 0 1) : 0 ≤ rootResidual u x :=
  primitive_nonneg (rootResidual u) (rootResidualSlope u) (rootResidual_continuous u).continuousOn
    (rootResidual_zero u) (rootResidual_deriv u)
    (fun t ht => by
      unfold rootResidualSlope
      exact div_nonneg
        (mul_nonneg (mul_nonneg (by positivity) (rootCoeff_nonneg u)) (pow_nonneg ht.1.le _))
        (density_pos t ht).le) x hx

/-- The arcsine residual slope divided by `x ^ (2 * u + 2)` is monotone on `(0, 1)`. -/
private theorem arcSlope_ratio_monotone (u : ℕ) :
    MonotoneOn (fun x => arcResidualSlope u x / x ^ (2 * u + 2)) (Ioo 0 1) := by
  intro x hx y hy hxy
  have hm := rootResidual_ratio_monotone u hx hy hxy
  have hi := inverse_density_monotone hx hy hxy
  have hp : 0 ≤ rootResidual u y / y ^ (2 * u + 2) :=
    div_nonneg (rootResidual_nonneg u y hy) (pow_nonneg hy.1.le _)
  have hh := mul_le_mul hm hi (by positivity) hp
  simpa only [arcResidualSlope, div_eq_mul_inv, one_mul, mul_assoc, mul_comm, mul_left_comm] using!
      hh

/-- The arcsine residual divided by `x ^ (2 * u + 3)` is monotone on `(0, 1)`. -/
private theorem arcResidual_ratio_monotone (u : ℕ) :
    MonotoneOn (fun x => arcResidual u x / x ^ (2 * u + 3)) (Ioo 0 1) := by
  simpa only [show 2 * u + 2 + 1 = 2 * u + 3 by omega] using!
    quotient_power_monotone (2 * u + 2) (arcResidual u) (arcResidualSlope u)
      (arcResidual_continuous u).continuousOn (arcResidual_zero u)
      (arcResidual_deriv u) (arcSlope_ratio_monotone u)

/-- The arcsine residual is nonnegative on `(0, 1)`. -/
private theorem arcResidual_nonneg (u : ℕ) (x : ℝ) (hx : x ∈ Ioo 0 1) : 0 ≤ arcResidual u x :=
  primitive_nonneg (arcResidual u) (arcResidualSlope u) (arcResidual_continuous u).continuousOn
    (arcResidual_zero u) (arcResidual_deriv u)
    (fun t ht => div_nonneg (rootResidual_nonneg u t ht) (density_pos t ht).le) x hx

/-- The arcsine residual at one equals `riskArcsinTail u`. -/
private theorem arcResidual_one (u : ℕ) : arcResidual u 1 = riskArcsinTail u := by
  simp [arcResidual, arcPartial, riskArcsinTail]

/-- On `(0, 1)`, the normalized arcsine residual is bounded above by `riskArcsinTail u`. -/
private theorem arcResidual_ratio_le_tail (u : ℕ) (x : ℝ) (hx : x ∈ Ioo 0 1) :
    arcResidual u x / x ^ (2 * u + 3) ≤ riskArcsinTail u := by
  have hc : ContinuousAt (fun t : ℝ => arcResidual u t / t ^ (2 * u + 3)) 1 :=
    (arcResidual_continuous u).continuousAt.div (continuous_id.pow _).continuousAt (by simp)
  have ht : Filter.Tendsto (fun t : ℝ => arcResidual u t / t ^ (2 * u + 3))
      (𝓝[<] 1) (𝓝 (riskArcsinTail u)) := by
    simpa only [one_pow, div_one, arcResidual_one] using!
      (hc.tendsto.mono_left nhdsWithin_le_nhds)
  apply ge_of_tendsto ht
  have hgt : ∀ᶠ t : ℝ in 𝓝[<] 1, x ≤ t :=
    (show ∀ᶠ t : ℝ in 𝓝 1, x ≤ t from Ici_mem_nhds hx.2).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hgt] with t ht1 hxt
  exact arcResidual_ratio_monotone u hx ⟨lt_of_lt_of_le hx.1 hxt, ht1⟩ hxt

/-- The arcsine tail constant is nonnegative. -/
theorem riskArcsinTail_nonneg (u : ℕ) : 0 ≤ riskArcsinTail u := by
  have hx : (1 / 2 : ℝ) ∈ Ioo 0 1 := by constructor <;> norm_num
  exact (div_nonneg (arcResidual_nonneg u _ hx) (by positivity)).trans
    (arcResidual_ratio_le_tail u _ hx)

/-- The arcsine partial sum is an odd function. -/
private theorem arcPartial_neg (u : ℕ) (x : ℝ) : arcPartial u (-x) = -arcPartial u x := by
  unfold arcPartial
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have ho : Odd (2 * j + 1) := ⟨j, by omega⟩
  rw [ho.neg_pow]
  ring

/-- For `x ∈ [0, 1]`, the arcsine partial-sum error is at most `riskArcsinTail u * x ^ (2 * u +
3)`. -/
private theorem arcPartial_tail_positive (u : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |arcPartial u x - Real.arcsin x| ≤ riskArcsinTail u * x ^ (2 * u + 3) := by
  by_cases hxz : x = 0
  · subst x
    simp [arcPartial]
  by_cases hxo : x = 1
  · subst x
    have he := arcResidual_one u
    rw [one_pow, mul_one, abs_sub_comm, ← arcResidual, he,
      abs_of_nonneg (riskArcsinTail_nonneg u)]
  have hx : x ∈ Ioo 0 1 := ⟨lt_of_le_of_ne hx0 (Ne.symm hxz), lt_of_le_of_ne hx1 hxo⟩
  rw [abs_sub_comm, ← arcResidual, abs_of_nonneg (arcResidual_nonneg u x hx)]
  exact (div_le_iff₀ (pow_pos hx.1 _)).mp (arcResidual_ratio_le_tail u x hx)

/-- For `|x| ≤ 1`, the arcsine partial-sum error is at most `riskArcsinTail u * |x| ^ (2 * u +
3)`. -/
private theorem arcPartial_tail_bound (u : ℕ) (x : ℝ) (hx : |x| ≤ 1) :
    |arcPartial u x - Real.arcsin x| ≤ riskArcsinTail u * |x| ^ (2 * u + 3) := by
  by_cases hx0 : 0 ≤ x
  · simpa only [abs_of_nonneg hx0] using!
      arcPartial_tail_positive u x hx0 ((le_abs_self x).trans hx)
  · have hn : x < 0 := lt_of_not_ge hx0
    have h := arcPartial_tail_positive u (-x) (neg_nonneg.mpr hn.le) (by rwa [abs_of_neg hn] at hx)
    rw [arcPartial_neg, Real.arcsin_neg, neg_sub_neg, abs_sub_comm] at h
    rw [abs_of_neg hn]
    exact h

/-- The shifted squared sine satisfies `sin (a + π / 4)² = (1 + sin (2 * a)) / 2`. -/
private theorem sin_square_quarter_shift (a : ℝ) :
    Real.sin (a + Real.pi / 4) ^ 2 = (1 + Real.sin (2 * a)) / 2 := by
  rw [Real.sin_sq_eq_half_sub, show 2 * (a + Real.pi / 4) = 2 * a + Real.pi / 2 by ring,
    Real.cos_add_pi_div_two]
  ring

/-- Twice the scaled payoff Taylor polynomial equals the arcsine partial sum at `2 * c * (y - 1
/ 2)`. -/
private theorem riskSinTaylor_arcPartial (u : ℕ) (c y : ℝ) :
    2 * (c * riskSinTaylor u c y) = arcPartial u (2 * c * (y - 1 / 2)) := by
  unfold riskSinTaylor arcPartial
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold riskArcsinCoeff
  have hfour : (4 : ℝ) ^ j = (2 : ℝ) ^ (2 * j) := by rw [pow_mul]; norm_num
  rw [mul_pow, mul_pow, pow_succ, pow_succ, ← hfour]
  field_simp
  ring

/-- For `0 < c ≤ 1` and `y ∈ [0, 1]`, the polynomial rotation probability differs from its
affine target by at most `riskArcsinTail u * c ^ (2 * u + 3) / 2`; see [WoernerEgger2019]. -/
theorem riskPolyRotationTaylorBias : PolyRotationTaylorBias := by
  intro u c y hc hc1 hy0 hy1
  let w := 2 * c * (y - 1 / 2)
  have hwc : |w| ≤ c := by
    apply abs_le.mpr
    dsimp [w]
    constructor <;> nlinarith
  have hw : |w| ≤ 1 := hwc.trans hc1
  have happrox := arcPartial_tail_bound u w hw
  have hsin := Real.abs_sin_sub_sin_le (arcPartial u w) (Real.arcsin w)
  rw [Real.sin_arcsin (by linarith [(abs_le.mp hw).1]) (by linarith [(abs_le.mp hw).2])] at hsin
  have he : Real.sin (c * riskSinTaylor u c y + Real.pi / 4) ^ 2 - (c * (y - 1 / 2) + 1 / 2) =
      (Real.sin (arcPartial u w) - w) / 2 := by
    rw [sin_square_quarter_shift, riskSinTaylor_arcPartial]
    dsimp only [w]
    ring
  rw [he, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hp := pow_le_pow_left₀ (abs_nonneg w) hwc (2 * u + 3)
  have hm := mul_le_mul_of_nonneg_left hp (riskArcsinTail_nonneg u)
  linarith

end Qatlib.Concepts.RiskEstimation.PolyRotation
