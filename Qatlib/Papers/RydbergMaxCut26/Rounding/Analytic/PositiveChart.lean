/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# A change of variables for the positive half-line

The rational map `positiveChart c` sends the open unit interval bijectively onto the positive
half-line when `c > 0`. Its derivative supplies a change-of-variables formula used to obtain the
Euler representation of the Gaussian rounding kernel. See [CrostaSaubanereHuber2026].

## Main statements

* `positiveChart_image`: identifies the image of the open unit interval.
* `positiveChart_integral`: gives the integral substitution with its explicit derivative.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical
open MeasureTheory Set Real

namespace Qatlib.Papers.RydbergMaxCut26.Rounding.Laplace

/-- The rational substitution `c * u² / (1 - u²)`. -/
def positiveChart (c u : ℝ) : ℝ := c*u^2/(1-u^2)

/-- The denominator `1 - u²` is positive on the open unit interval. -/
theorem chart_den_pos {u : ℝ} (hu : u∈Ioo (0:ℝ) 1) : 0<1-u^2 := by
  nlinarith [hu.1,hu.2]

/-- On the open unit interval, `positiveChart c` has derivative `2 * c * u / (1 - u²)²`. -/
theorem positiveChart_deriv (c u : ℝ) (hu : u∈Ioo (0:ℝ) 1) :
    HasDerivAt (positiveChart c) (2*c*u/(1-u^2)^2) u := by
  have hd := ((hasDerivAt_pow 2 u).const_mul c).div
    ((hasDerivAt_const u (1:ℝ)).sub (hasDerivAt_pow 2 u)) (chart_den_pos hu).ne'
  convert! hd using 1
  try dsimp
  (try field_simp [(chart_den_pos hu).ne'])
  ring

/-- For positive `c`, `positiveChart c` is injective on the open unit interval. -/
theorem positiveChart_inj {c : ℝ} (hc : 0<c) : InjOn (positiveChart c) (Ioo (0:ℝ) 1) := by
  intro x hx y hy he
  have hdx := (chart_den_pos hx).ne'
  have hdy := (chart_den_pos hy).ne'
  have he' : c*x^2*(1-y^2)=c*y^2*(1-x^2) := (div_eq_div_iff hdx hdy).mp he
  have hz : c*(x^2-y^2)=0 := by
    calc
      _ = c*x^2*(1-y^2)-c*y^2*(1-x^2) := by ring
      _ = 0 := sub_eq_zero.mpr he'
  have hs := (mul_eq_zero.mp hz).resolve_left hc.ne'
  nlinarith [hx.1,hy.1]

/-- For positive `c`, the image of the open unit interval under `positiveChart c` is the
positive half-line. -/
theorem positiveChart_image {c : ℝ} (hc : 0<c) : positiveChart c '' Ioo (0:ℝ) 1=Ioi 0 := by
  ext x
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact div_pos (mul_pos hc (sq_pos_of_pos hu.1)) (chart_den_pos hu)
  · intro hx
    have hx' : 0<x := hx
    have hcx : 0<c+x := add_pos hc hx'
    have hfrac : 0<x/(c+x) := div_pos hx' hcx
    have hu0 : 0<Real.sqrt (x/(c+x)) := Real.sqrt_pos.mpr hfrac
    have hlt : x/(c+x)<1 := (div_lt_one hcx).mpr (by linarith)
    have hu1 : Real.sqrt (x/(c+x))<1 := by
      nlinarith [Real.sq_sqrt hfrac.le,Real.sqrt_nonneg (x/(c+x))]
    refine ⟨Real.sqrt (x/(c+x)),⟨hu0,hu1⟩,?_⟩
    unfold positiveChart
    rw [Real.sq_sqrt hfrac.le]
    field_simp
    simp [hc.ne']

/-- For positive `c`, integration over the positive half-line can be rewritten on the open unit
interval using `positiveChart c` and the Jacobian `2 * c * u / (1 - u²)²`. -/
theorem positiveChart_integral {c : ℝ} (hc : 0<c) (f : ℝ→ℝ) :
    (∫ x in Ioi (0:ℝ),f x)=
      ∫ u in Ioo (0:ℝ) 1,(2*c*u/(1-u^2)^2)*f (positiveChart c u) := by
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun u hu => (positiveChart_deriv c u hu).hasDerivWithinAt) (positiveChart_inj hc) f
  rw [positiveChart_image hc] at h
  rw [h]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u hu
  (try dsimp only)
  have hu0 := hu.1
  have hd := chart_den_pos hu
  rw [abs_of_pos (by positivity : 0<2*c*u/(1-u^2)^2),smul_eq_mul]

end Qatlib.Papers.RydbergMaxCut26.Rounding.Laplace
