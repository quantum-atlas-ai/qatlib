/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Entropy estimates for central-difference weights

`centralDiffBinaryEntropy` is the logarithmic expression used to control central-difference
binomial ratios. Polynomial lower bounds for it and an upper bound for the logarithm imply
`centralDiff_entropy_exponent`, the uniform negative exponent estimate. See
[GilyenArunachalamWiebe2019] for background.

## Main statements

* `centralDiff_entropy_lower`: For `0 ≤ y < 1`, `cdEven y` is a lower bound for
  `centralDiffBinaryEntropy y`.
* `centralDiff_entropy_exponent`: For `0 < y < 1`, `2 * log y - centralDiffBinaryEntropy y` is
  at most negative seven sixths.

## References

* [Gilyen, Arunachalam, and Wiebe, 2019][GilyenArunachalamWiebe2019]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Qatlib.Concepts.GradientOracle.CentralDiff

/-- A function with the specified nonnegative derivative throughout a closed interval has its
value at the left endpoint at most its value at the right endpoint. -/
private theorem cd_increasing_endpoints (f f' : ℝ → ℝ) (a b : ℝ) (hab : a≤b)
    (hd : ∀ u∈Set.Icc a b,HasDerivAt f (f' u) u)
    (hs : ∀ u∈Set.Icc a b,0≤f' u) : f a≤f b := by
  have hc : ContinuousOn f (Set.Icc a b) := fun u hu => (hd u hu).continuousAt.continuousWithinAt
  have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) hc
    (fun u hu => (hd u (interior_subset hu)).hasDerivWithinAt)
    (fun u hu => hs u (interior_subset hu))
  exact hm ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab

/-- The odd polynomial `2 * y + (2 / 3) * y ^ 3 + (2 / 5) * y ^ 5 + (2 / 7) * y ^ 7`. -/
private def cdOdd (y : ℝ) : ℝ := 2*y+(2/3)*y^3+(2/5)*y^5+(2/7)*y^7
/-- The even polynomial `y ^ 2 + y ^ 4 / 6 + y ^ 6 / 15 + y ^ 8 / 28`. -/
private def cdEven (y : ℝ) : ℝ := y^2+y^4/6+y^6/15+y^8/28
/-- The logarithmic expression `(1 + y) * log (1 + y) + (1 - y) * log (1 - y)`. -/
def centralDiffBinaryEntropy (y : ℝ) : ℝ := (1+y)*Real.log (1+y)+(1-y)*Real.log (1-y)

/-- The derivative of `cdOdd` is `2 + 2 * y ^ 2 + 2 * y ^ 4 + 2 * y ^ 6`. -/
private theorem cdOdd_deriv (y : ℝ) :
    HasDerivAt cdOdd (2+2*y^2+2*y^4+2*y^6) y := by
  have h := ((((hasDerivAt_id y).const_mul 2).add (((hasDerivAt_id y).pow 3).const_mul (2/3))).add
    (((hasDerivAt_id y).pow 5).const_mul (2/5))).add (((hasDerivAt_id y).pow 7).const_mul (2/7))
  convert! h using 1
  try simp only [id_eq]
  ring

/-- The derivative of `cdEven` is `cdOdd`. -/
private theorem cdEven_deriv (y : ℝ) : HasDerivAt cdEven (cdOdd y) y := by
  have h := (((((hasDerivAt_id y).pow 2).add (((hasDerivAt_id y).pow 4).const_mul (1/6))).add
    (((hasDerivAt_id y).pow 6).const_mul (1/15))).add (((hasDerivAt_id y).pow 8).const_mul (1/28)))
  convert! h using 1
  · ext u; dsimp [cdEven]; ring
  · (try dsimp [cdOdd]); ring

/-- For `0 ≤ y < 1`, the polynomial `cdOdd y` bounds `log (1 + y) - log (1 - y)` from below. -/
theorem centralDiff_log_ratio_lower (y : ℝ) (hy : 0≤y) (hy1 : y<1) :
    cdOdd y≤Real.log (1+y)-Real.log (1-y) := by
  let F := fun u : ℝ => Real.log (1+u)-Real.log (1-u)-cdOdd u
  have hd (u : ℝ) (hu : u∈Set.Icc 0 y) : HasDerivAt F (2*u^8/(1-u^2)) u := by
    have hp : 0<1+u := by linarith [hu.1]
    have hm : 0<1-u := by linarith [hu.2]
    have hden : 0<1-u^2 := by nlinarith [hu.1,hu.2]
    have h := (((hasDerivAt_id u).const_add 1).log hp.ne').sub
      (((hasDerivAt_id u).const_sub 1).log hm.ne')
    have h' := h.sub (cdOdd_deriv u)
    convert! h' using 1
    try simp only [id_eq]
    field_simp
    ring
  have hs (u : ℝ) (hu : u∈Set.Icc 0 y) : 0≤2*u^8/(1-u^2) := by
    have hp : 0<1-u^2 := by nlinarith [hu.1,hu.2]
    exact div_nonneg (by positivity) hp.le
  have h := cd_increasing_endpoints F (fun u => 2*u^8/(1-u^2)) 0 y hy hd hs
  have hzero : F 0=0 := by norm_num [F,cdOdd]
  rw [hzero] at h
  dsimp [F] at h
  linarith

/-- For `0 ≤ y < 1`, `cdEven y` is a lower bound for `centralDiffBinaryEntropy y`. -/
theorem centralDiff_entropy_lower (y : ℝ) (hy : 0≤y) (hy1 : y<1) :
    cdEven y≤centralDiffBinaryEntropy y := by
  let F := fun u : ℝ => centralDiffBinaryEntropy u-cdEven u
  have hd (u : ℝ) (hu : u∈Set.Icc 0 y) :
      HasDerivAt F (Real.log (1+u)-Real.log (1-u)-cdOdd u) u := by
    have hp : 0<1+u := by linarith [hu.1]
    have hm : 0<1-u := by linarith [hu.2]
    have hplus := ((hasDerivAt_id u).const_add 1).mul (((hasDerivAt_id u).const_add 1).log hp.ne')
    have hminus := ((hasDerivAt_id u).const_sub 1).mul (((hasDerivAt_id u).const_sub 1).log hm.ne')
    have h := (hplus.add hminus).sub (cdEven_deriv u)
    convert! h using 1
    try simp only [id_eq]
    field_simp
    ring
  have hs (u : ℝ) (hu : u∈Set.Icc 0 y) :
      0≤Real.log (1+u)-Real.log (1-u)-cdOdd u := by
    have h := centralDiff_log_ratio_lower u hu.1 (lt_of_le_of_lt hu.2 hy1)
    linarith
  have h := cd_increasing_endpoints F (fun u => Real.log (1+u)-Real.log (1-u)-cdOdd u) 0 y hy hd hs
  have hzero : F 0=0 := by norm_num [F,cdEven,centralDiffBinaryEntropy]
  rw [hzero] at h
  dsimp [F] at h
  linarith

/-- For `0 < z ≤ 1`, the logarithm is at most the negative sum of the first four powers of `1 -
z` divided by their degrees. -/
theorem centralDiff_log_upper (z : ℝ) (hz : 0<z) (hz1 : z≤1) :
    Real.log z≤-((1-z)+(1-z)^2/2+(1-z)^3/3+(1-z)^4/4) := by
  let F := fun u : ℝ => Real.log u+(1-u)+(1-u)^2/2+(1-u)^3/3+(1-u)^4/4
  have hd (u : ℝ) (hu : u∈Set.Icc z 1) : HasDerivAt F ((1-u)^4/u) u := by
    have hp : 0<u := lt_of_lt_of_le hz hu.1
    have hsub := (hasDerivAt_id u).const_sub 1
    have h := (((((hasDerivAt_id u).log hp.ne').add hsub).add ((hsub.pow 2).const_mul (1/2))).add
      ((hsub.pow 3).const_mul (1/3))).add ((hsub.pow 4).const_mul (1/4))
    convert! h using 1
    · ext x; dsimp [F]; ring
    · try simp only [id_eq]
      field_simp
      ring
  have hs (u : ℝ) (hu : u∈Set.Icc z 1) : 0≤(1-u)^4/u :=
      div_nonneg (by positivity) (le_trans hz.le hu.1)
  have h := cd_increasing_endpoints F (fun u => (1-u)^4/u) z 1 hz1 hd hs
  have h1 : F 1=0 := by norm_num [F]
  rw [h1] at h
  dsimp [F] at h
  linarith

/-- For `0 ≤ z ≤ 1`, the stated polynomial combining powers of `z` and `1 - z` is at least one
sixth. -/
private theorem centralDiff_entropy_polynomial (z : ℝ) (_hz : 0≤z) (hz1 : z≤1) :
    (1-z)^2/2+(1-z)^3/3+(1-z)^4/4+z^2/6+z^3/15+z^4/28≥(1/6 : ℝ) := by
  let t := z-2/3
  let B := (83/210 : ℝ)-(53/105)*t+(2/7)*t^2
  have hB : 0≤B := by dsimp [B,t]; nlinarith [sq_nonneg (z-2/3)]
  have he : (1-z)^2/2+(1-z)^3/3+(1-z)^4/4+z^2/6+z^3/15+z^4/28-1/6=
      t^2*B+(t-121/1890)^2+986/893025 := by dsimp [B,t]; ring
  have hp := mul_nonneg (sq_nonneg t) hB
  nlinarith [sq_nonneg (t-121/1890)]

/-- For `0 < y < 1`, `2 * log y - centralDiffBinaryEntropy y` is at most negative seven sixths. -/
theorem centralDiff_entropy_exponent (y : ℝ) (hy : 0<y) (hy1 : y<1) :
    2*Real.log y-centralDiffBinaryEntropy y≤-(7/6 : ℝ) := by
  have hz : 0<y^2 := sq_pos_of_pos hy
  have hz1 : y^2≤1 := by nlinarith
  have hl := centralDiff_log_upper (y^2) hz hz1
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have he := centralDiff_entropy_lower y hy.le hy1
  have hp := centralDiff_entropy_polynomial (y^2) hz.le hz1
  dsimp [cdEven] at he
  nlinarith

/-- The natural logarithm of two is at least two thirds. -/
theorem centralDiff_log_two_lower : (2/3 : ℝ)≤Real.log 2 := by
  have h := centralDiff_log_ratio_lower (1/3 : ℝ) (by norm_num) (by norm_num)
  have he : Real.log (1+(1/3 : ℝ))-Real.log (1-(1/3 : ℝ))=Real.log 2 := by
    rw [← Real.log_div (by norm_num : (1+(1/3 : ℝ))≠0) (by norm_num : (1-(1/3 : ℝ))≠0)]
    norm_num
  rw [he] at h
  norm_num [cdOdd] at h
  linarith

end Qatlib.Concepts.GradientOracle.CentralDiff
