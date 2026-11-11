/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductEtaRecordStat
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# A certified scalar maximum for multiproduct bounds

This module certifies `EtaMaxProperty (311 / 1000)` and proves `multiproductEtaRecord`. An
entropy expression and a degree-eight polynomial lower bound reduce the scalar ratio estimate to
explicit polynomial and exponential inequalities. See [ChildsWiebe2012] for the multiproduct and
linear-combination simulation framework.

## Main statements

* `multiproduct_entropy_lower`: For 0 ≤ x < 1, the polynomial x² + x⁴ / 6 + x⁶ / 15 + x⁸ / 28 is
  at most `etaEntropy x`.
* `multiproduct_eta_max_311`: The constant 311 / 1000 satisfies `EtaMaxProperty`.
* `multiproductEtaRecord`: Establishes the existence of 0.305 < η < 0.312 satisfying
  `EtaMaxProperty`, using η = 311 / 1000.

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

set_option warningAsError false
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace Qatlib.Papers.HamLCUSim12.Multiproduct

/-- The scalar function (1 + x) log(1 + x) + (1 − x) log(1 − x) used to bound the multiproduct
ratio. -/
private def etaEntropy (x : ℝ) : ℝ :=
  (1+x)*Real.log (1+x)+(1-x)*Real.log (1-x)
/-- The polynomial x² + x⁴ / 6 + x⁶ / 15 + x⁸ / 28 approximating `etaEntropy` from below on [0,
1). -/
private def etaEntropyPoly (x : ℝ) : ℝ := x^2+x^4/6+x^6/15+x^8/28
/-- The difference log(1 + x) − log(1 − x) minus the polynomial 2x + 2x³ / 3 + 2x⁵ / 5 + 2x⁷ /
7. -/
private def etaLogRemainder (x : ℝ) : ℝ :=
  Real.log (1+x)-Real.log (1-x)-(2*x+2*x^3/3+2*x^5/5+2*x^7/7)

/-- For 0 ≤ x < 1, the derivative of `etaLogRemainder` at x is 2x⁸ / (1 − x²). -/
private theorem eta_log_remainder_deriv (x : ℝ) (hx : 0 ≤ x) (hx1 : x < 1) :
    HasDerivAt etaLogRemainder (2*x^8/(1-x^2)) x := by
  have hp : 1+x ≠ 0 := by linarith
  have hm : 1-x ≠ 0 := by linarith
  convert! ((((hasDerivAt_id x).const_add 1).log hp).sub
    (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).log hm)).sub
    ((((hasDerivAt_id x).const_mul 2).add (((hasDerivAt_id x).pow 3).const_mul 2 |>.div_const 3)).add
      (((hasDerivAt_id x).pow 5).const_mul 2 |>.div_const 5) |>.add
      (((hasDerivAt_id x).pow 7).const_mul 2 |>.div_const 7)) using 1
  try dsimp [etaLogRemainder]
  have hn : 1-x^2 ≠ 0 := by nlinarith
  (try field_simp)
  ring

/-- The logarithmic remainder `etaLogRemainder` is nonnegative on [0, 1). -/
private theorem eta_log_remainder_nonneg (x : ℝ) (hx : 0 ≤ x) (hx1 : x < 1) :
    0 ≤ etaLogRemainder x := by
  have hd (u : ℝ) (hu : u ∈ Set.Icc 0 x) :=
    eta_log_remainder_deriv u hu.1 (hu.2.trans_lt hx1)
  have hmono : MonotoneOn etaLogRemainder (Set.Icc 0 x) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact continuousOn_of_forall_continuousAt (fun u hu => (hd u hu).continuousAt)
    · exact fun u hu => (hd u (interior_subset hu)).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [(hd u (interior_subset hu)).deriv]
      have hu0 := (interior_subset hu).1
      have hu1 := (interior_subset hu).2.trans_lt hx1
      apply div_nonneg (by positivity)
      nlinarith
  have he := hmono ⟨le_rfl, hx⟩ ⟨hx, le_rfl⟩ hx
  simpa [etaLogRemainder] using he

/-- For 0 ≤ x < 1, the derivative of `etaEntropy` is log(1 + x) − log(1 − x). -/
private theorem eta_entropy_deriv (x : ℝ) (hx : 0 ≤ x) (hx1 : x < 1) :
    HasDerivAt etaEntropy (Real.log (1+x)-Real.log (1-x)) x := by
  have hp : 1+x ≠ 0 := by linarith
  have hm : 1-x ≠ 0 := by linarith
  let dp := (hasDerivAt_id x).const_add 1
  let dm := (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)
  convert! (dp.mul (dp.log hp)).add (dm.mul (dm.log hm)) using 1
  try dsimp [etaEntropy, dp, dm]
  (try field_simp)
  ring

/-- The derivative of `etaEntropyPoly` at x is 2x + 2x³ / 3 + 2x⁵ / 5 + 2x⁷ / 7. -/
private theorem eta_entropy_poly_deriv (x : ℝ) :
    HasDerivAt etaEntropyPoly (2*x+2*x^3/3+2*x^5/5+2*x^7/7) x := by
  convert! ((((hasDerivAt_id x).pow 2).add (((hasDerivAt_id x).pow 4).div_const 6)).add
    (((hasDerivAt_id x).pow 6).div_const 15)).add (((hasDerivAt_id x).pow 8).div_const 28) using 1
  try dsimp [etaEntropyPoly]
  ring

/-- For 0 ≤ x < 1, the polynomial x² + x⁴ / 6 + x⁶ / 15 + x⁸ / 28 is at most `etaEntropy x`. -/
theorem multiproduct_entropy_lower (x : ℝ) (hx : 0 ≤ x) (hx1 : x < 1) :
    x^2+x^4/6+x^6/15+x^8/28 ≤ etaEntropy x := by
  let R := fun u => etaEntropy u-etaEntropyPoly u
  have hd (u : ℝ) (hu : u ∈ Set.Icc 0 x) : HasDerivAt R (etaLogRemainder u) u := by
    exact (eta_entropy_deriv u hu.1 (hu.2.trans_lt hx1)).sub (eta_entropy_poly_deriv u)
  have hmono : MonotoneOn R (Set.Icc 0 x) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact continuousOn_of_forall_continuousAt (fun u hu => (hd u hu).continuousAt)
    · exact fun u hu => (hd u (interior_subset hu)).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [(hd u (interior_subset hu)).deriv]
      exact eta_log_remainder_nonneg u (interior_subset hu).1 ((interior_subset hu).2.trans_lt hx1)
  have he := hmono ⟨le_rfl, hx⟩ ⟨hx, le_rfl⟩ hx
  simpa [R, etaEntropy, etaEntropyPoly] using he

/-- For y ≥ 0, certifies (1000 / 311)y ≤ (2293 / 1000)(1 + y + y² / 6 + y³ / 15 + y⁴ / 28 − 83 /
100). -/
private theorem eta_polynomial_certificate (y : ℝ) (hy : 0 ≤ y) :
    (1000/311 : ℝ)*y ≤ (2293/1000 : ℝ)*(1+(y+y^2/6+y^3/15+y^4/28)-83/100) := by
  let z := y-18/25
  let A : ℝ := 19153429/26250000
  let B : ℝ := -411944969/34015625000
  let C : ℝ := 9652293853/3401562500000
  have hq : 0 ≤ A*z^2+B*z+C := by
    dsimp [A, B, C]
    nlinarith only [sq_nonneg z, sq_nonneg (z+B)]
  have hr : 0 ≤ (2293/1000 : ℝ)*(y*z^2/15+(y^2+2*(18/25)*y)*z^2/28) := by positivity
  have he : (2293/1000 : ℝ)*(1+(y+y^2/6+y^3/15+y^4/28)-83/100)-(1000/311)*y =
      A*z^2+B*z+C+(2293/1000)*(y*z^2/15+(y^2+2*(18/25)*y)*z^2/28) := by
    dsimp [A, B, C, z]
    ring
  apply sub_nonneg.mp
  rw [he]
  exact add_nonneg hq hr

/-- The exponential at 83 / 100 is at least 2293 / 1000. -/
private theorem eta_exp_anchor : (2293/1000 : ℝ) ≤ Real.exp (83/100) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 83/100) 8
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith only [h]

/-- The constant 311 / 1000 satisfies `EtaMaxProperty`. -/
theorem multiproduct_eta_max_311 : EtaMaxProperty (311/1000) := by
  intro x hx hx1
  have hp : 0 < 1+x := by linarith
  have hm : 0 < 1-x := by linarith
  have hd : (1+x)^((1+x : ℝ))*(1-x)^((1-x : ℝ)) = Real.exp (etaEntropy x) := by
    rw [Real.rpow_def_of_pos hp, Real.rpow_def_of_pos hm, ← Real.exp_add]
    dsimp [etaEntropy]
    congr 1
    ring
  rw [hd]
  have hP : 0 ≤ etaEntropyPoly x := by dsimp [etaEntropyPoly]; positivity
  have hfactor : 0 ≤ 1+etaEntropyPoly x-83/100 := by linarith
  have ht : (2293/1000 : ℝ)*(1+etaEntropyPoly x-83/100) ≤ Real.exp (etaEntropyPoly x) := by
    calc
      _ ≤ Real.exp (83/100)*(1+etaEntropyPoly x-83/100) :=
        mul_le_mul_of_nonneg_right eta_exp_anchor hfactor
      _ ≤ Real.exp (83/100)*Real.exp (etaEntropyPoly x-83/100) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        convert! Real.add_one_le_exp (etaEntropyPoly x-83/100) using 1
        ring
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hpoly := eta_polynomial_certificate (x^2) (sq_nonneg x)
  have hpoly' : (1000/311 : ℝ)*x^2 ≤ (2293/1000 : ℝ)*(1+etaEntropyPoly x-83/100) := by
    convert! hpoly using 1
    dsimp [etaEntropyPoly]
    ring
  have he : (1000/311 : ℝ)*x^2 ≤ Real.exp (etaEntropy x) :=
    (hpoly'.trans ht).trans (Real.exp_le_exp.mpr (multiproduct_entropy_lower x hx hx1))
  apply (div_le_iff₀ (Real.exp_pos _)).2
  nlinarith only [he]

/-- Establishes the existence of 0.305 < η < 0.312 satisfying `EtaMaxProperty`, using η = 311 /
1000. See [ChildsWiebe2012]. -/
theorem multiproductEtaRecord : MultiproductEtaRecord := by
  refine ⟨311/1000, ?_, ?_, multiproduct_eta_max_311⟩ <;> norm_num

end Qatlib.Papers.HamLCUSim12.Multiproduct
