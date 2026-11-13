/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CryptoDisting99.Equivalence.Defs
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# A square-root upper bound for binary entropy

The auxiliary function `entropyAux` and its derivative establish a square-root upper bound for
binary entropy on the unit interval. The final bound `binaryEntropy_le_two_sqrt` uses entropy in
bits and supplies an analytic comparison relevant to Proposition 5 and the distinguishability
bounds of [FuchsVanDeGraaf1999].

## Main statements

* `binEntropy_le_log_four_mul_sqrt`: the natural-log entropy bound.
* `binaryEntropy_le_two_sqrt`: binary entropy in bits is at most `2 * √(r * (1 - r))`.

## References

* [Fuchs and van de Graaf, 1999][FuchsVanDeGraaf1999]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CryptoDisting99.Equivalence

open Real
open scoped BigOperators

/-- For `z ∈ [0, 1]`, the expression `z * log z + (1 - z) * log (1 + z)` is nonpositive. -/
lemma phi_nonpos {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    z * Real.log z + (1 - z) * Real.log (1 + z) ≤ 0 := by
  rcases eq_or_lt_of_le hz0 with h | h
  · subst h; simp
  · have h1 : Real.log z ≤ z - 1 := Real.log_le_sub_one_of_pos h
    have h2 : Real.log (1 + z) ≤ z := by
      have h3 := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < 1 + z)
      linarith
    have hz1' : (0:ℝ) ≤ 1 - z := by linarith
    have ha : z * Real.log z ≤ z * (z - 1) := mul_le_mul_of_nonneg_left h1 hz0
    have hb : (1 - z) * Real.log (1 + z) ≤ (1 - z) * z :=
      mul_le_mul_of_nonneg_left h2 hz1'
    nlinarith

/-- Defines the entropy comparison function `-2 * y * log y + (y + y⁻¹) * log (1 + y ^ 2) - log
4`. -/
def entropyAux (y : ℝ) : ℝ :=
  -2 * y * Real.log y + (y + y⁻¹) * Real.log (1 + y^2) - Real.log 4

/-- For positive `y`, computes the derivative of `entropyAux` as `log (1 + y ^ 2) * (1 - 1 / y ^
2) - 2 * log y`. -/
lemma entropyAux_hasDerivAt {y : ℝ} (hy : 0 < y) :
    HasDerivAt entropyAux
      (Real.log (1 + y^2) * (1 - 1/y^2) - 2 * Real.log y) y := by
  unfold entropyAux
  have hd1 : HasDerivAt (fun y : ℝ => y * Real.log y) (Real.log y + 1) y := by
    have h := (hasDerivAt_id y).mul (Real.hasDerivAt_log hy.ne')
    simp only [id, one_mul] at h
    convert! h using 1
    field_simp
  have h1 : HasDerivAt (fun y : ℝ => -2 * y * Real.log y) (-2 * (Real.log y + 1)) y := by
    have h := hd1.const_mul (-2)
    convert! h using 1
    funext z; ring
  have hinv : HasDerivAt (fun y : ℝ => y⁻¹) (-(y^2)⁻¹) y := hasDerivAt_inv hy.ne'
  have hsum : HasDerivAt (fun y : ℝ => y + y⁻¹) (1 - (y^2)⁻¹) y := by
    have h := (hasDerivAt_id y).add hinv
    simpa using! h
  have hinner : HasDerivAt (fun y : ℝ => 1 + y^2) (2*y) y := by
    have h := (hasDerivAt_id y).pow 2
    simpa using! h
  have hlog : HasDerivAt (fun y : ℝ => Real.log (1 + y^2)) (2*y/(1+y^2)) y := by
    have hpos : (1 + y^2) ≠ 0 := by positivity
    have h := (Real.hasDerivAt_log hpos).comp y hinner
    convert! h using 1
    field_simp
  have h2 : HasDerivAt (fun y : ℝ => (y + y⁻¹) * Real.log (1 + y^2))
      ((1 - (y^2)⁻¹) * Real.log (1 + y^2) + (y + y⁻¹) * (2*y/(1+y^2))) y :=
    hsum.mul hlog
  have hc : HasDerivAt (fun _ : ℝ => Real.log 4) 0 y := hasDerivAt_const _ _
  have hall := (h1.add h2).sub hc
  convert! hall using 1
  have hy2 : y ≠ 0 := hy.ne'
  field_simp
  ring

/-- For `0 < x ≤ 1`, the displayed derivative expression for `entropyAux` is nonnegative. -/
lemma entropyAux_deriv_nonneg {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    0 ≤ Real.log (1 + x^2) * (1 - 1/x^2) - 2 * Real.log x := by
  have hz0 : 0 ≤ x^2 := by positivity
  have hz1 : x^2 ≤ 1 := by nlinarith
  have hphi := phi_nonpos hz0 hz1
  have hlogx2 : Real.log (x^2) = 2 * Real.log x := by
    rw [Real.log_pow]; push_cast; ring
  rw [hlogx2] at hphi
  have key : 0 ≤ (x^2 - 1) * Real.log (1 + x^2) - 2 * x^2 * Real.log x := by linarith
  have hstep : Real.log (1 + x^2) * (1 - 1/x^2) - 2 * Real.log x
      = (1/x^2) * ((x^2 - 1) * Real.log (1 + x^2) - 2 * x^2 * Real.log x) := by
    field_simp
  rw [hstep]
  exact mul_nonneg (by positivity) key

/-- The entropy auxiliary function vanishes at one. -/
lemma entropyAux_one : entropyAux 1 = 0 := by
  unfold entropyAux
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
    push_cast; ring
  rw [h4]; norm_num

/-- The entropy auxiliary function is continuous on the positive real half-line. -/
lemma entropyAux_continuous : ContinuousOn entropyAux (Set.Ioi 0) := by
  unfold entropyAux
  have hid : ContinuousOn (fun y : ℝ => y) (Set.Ioi 0) := continuousOn_id
  have hlog : ContinuousOn Real.log (Set.Ioi 0) :=
    Real.continuousOn_log.mono (fun x hx => by simpa using hx.ne')
  have hinv : ContinuousOn (fun y : ℝ => y⁻¹) (Set.Ioi 0) :=
    continuousOn_id.inv₀ (fun x hx => hx.ne')
  have hc2 : ContinuousOn (fun _ : ℝ => (-2:ℝ)) (Set.Ioi 0) := continuousOn_const
  have h1 : ContinuousOn (fun y : ℝ => (-2) * (y * Real.log y)) (Set.Ioi 0) := by
    simpa only [Pi.mul_apply, mul_assoc] using! (hc2.mul hid).mul hlog
  have h2inner : ContinuousOn (fun y : ℝ => Real.log (1 + y^2)) (Set.Ioi 0) :=
    hlog.comp (continuousOn_const.add (hid.pow 2))
      (fun x hx => by simp only [Set.mem_Ioi]; positivity)
  have h2 : ContinuousOn (fun y : ℝ => (y + y⁻¹) * Real.log (1 + y^2)) (Set.Ioi 0) :=
    (hid.add hinv).mul h2inner
  have h3 : ContinuousOn (fun _ : ℝ => Real.log 4) (Set.Ioi 0) := continuousOn_const
  refine ((h1.add h2).sub h3).congr (fun y hy => ?_)
  dsimp
  ring

/-- The entropy auxiliary function is nonpositive for `0 < y ≤ 1`. -/
lemma entropyAux_nonpos {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) : entropyAux y ≤ 0 := by
  have hmono : MonotoneOn entropyAux (Set.Ioc 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioc 0 1)
    · exact entropyAux_continuous.mono Set.Ioc_subset_Ioi_self
    · intro x hx
      rw [interior_Ioc] at hx
      exact (entropyAux_hasDerivAt hx.1).hasDerivWithinAt
    · intro x hx
      rw [interior_Ioc] at hx
      exact entropyAux_deriv_nonneg hx.1 (le_of_lt hx.2)
  have h := hmono (Set.mem_Ioc.mpr ⟨hy0, hy1⟩)
    (Set.mem_Ioc.mpr ⟨by norm_num, le_refl 1⟩) hy1
  rwa [entropyAux_one] at h

/-- For positive `y`, rewrites binary entropy at `y ^ 2 / (1 + y ^ 2)` using `log (1 + y ^ 2)`
and `log y`. -/
lemma binEntropy_subst {y : ℝ} (hy0 : 0 < y) :
    Real.binEntropy (y^2/(1+y^2)) =
      Real.log (1+y^2) - 2*(y^2/(1+y^2))*Real.log y := by
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  unfold Real.negMulLog
  have h1py : (0:ℝ) < 1 + y^2 := by positivity
  have h1m : 1 - y^2/(1+y^2) = 1/(1+y^2) := by field_simp; ring
  rw [h1m]
  have hlogr : Real.log (y^2/(1+y^2)) = 2*Real.log y - Real.log (1+y^2) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow]
    push_cast; ring
  have hlog1 : Real.log (1/(1+y^2)) = -Real.log (1+y^2) := by
    rw [Real.log_div one_ne_zero h1py.ne']; simp
  rw [hlogr, hlog1]
  field_simp
  ring

/-- For positive `y`, the square root of `r * (1 - r)` at `r = y ^ 2 / (1 + y ^ 2)` equals `y /
(1 + y ^ 2)`. -/
lemma sqrt_subst {y : ℝ} (hy0 : 0 < y) :
    Real.sqrt ((y^2/(1+y^2)) * (1 - y^2/(1+y^2))) = y/(1+y^2) := by
  have hsq : (y^2/(1+y^2)) * (1 - y^2/(1+y^2)) = (y/(1+y^2))^2 := by
    field_simp
    ring
  rw [hsq, Real.sqrt_sq (by positivity)]

/-- For `0 < y ≤ 1`, bounds natural-log binary entropy at `y ^ 2 / (1 + y ^ 2)` by `log 4` times
the corresponding square-root expression. -/
lemma binEntropy_le_of_aux {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) :
    Real.binEntropy (y^2/(1+y^2)) ≤
      Real.log 4 * Real.sqrt ((y^2/(1+y^2)) * (1 - y^2/(1+y^2))) := by
  have h1py : (0:ℝ) < 1 + y^2 := by positivity
  have hH := entropyAux_nonpos hy0 hy1
  have step : y * entropyAux y =
      -2*y^2*Real.log y + (y^2+1)*Real.log (1+y^2) - y*Real.log 4 := by
    unfold entropyAux
    field_simp
  have hHy : y * entropyAux y ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt hy0) hH
  rw [step] at hHy
  rw [binEntropy_subst hy0, sqrt_subst hy0]
  have key : Real.log (1+y^2) - 2*(y^2/(1+y^2))*Real.log y ≤
      Real.log 4 * (y/(1+y^2)) := by
    rw [show Real.log 4 * (y/(1+y^2)) = Real.log 4 * y/(1+y^2) by ring]
    rw [le_div_iff₀ h1py]
    have hX : (Real.log (1+y^2) - 2*(y^2/(1+y^2))*Real.log y) * (1+y^2)
        = Real.log (1+y^2)*(1+y^2) - 2*y^2*Real.log y := by
      field_simp
    rw [hX]
    linarith
  exact key

/-- For `r ∈ [0, 1 / 2]`, natural-log binary entropy is at most `log 4 * √(r * (1 - r))`. -/
lemma binEntropy_le_log_four_mul_sqrt_of_le_half {r : ℝ} (hr0 : 0 ≤ r)
    (hrh : r ≤ 1/2) :
    Real.binEntropy r ≤ Real.log 4 * Real.sqrt (r * (1 - r)) := by
  rcases eq_or_lt_of_le hr0 with h | h
  · subst h; simp
  · have hr1 : r < 1 := by linarith
    have h1m : 0 < 1 - r := by linarith
    have hq : 0 < r/(1-r) := by positivity
    set y := Real.sqrt (r/(1-r)) with hydef
    have hy0 : 0 < y := Real.sqrt_pos.mpr hq
    have hy1 : y ≤ 1 := by
      rw [hydef]
      have hle : r/(1-r) ≤ 1 := by rw [div_le_one h1m]; linarith
      calc Real.sqrt (r/(1-r)) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hle
        _ = 1 := Real.sqrt_one
    have hysq : y^2 = r/(1-r) := by
      rw [hydef, sq]; exact Real.mul_self_sqrt hq.le
    have hreq : r = y^2/(1+y^2) := by
      rw [hysq]
      field_simp
      ring
    rw [hreq]
    exact binEntropy_le_of_aux hy0 hy1

/-- For `r ∈ [0, 1]`, natural-log binary entropy is at most `log 4 * √(r * (1 - r))`. -/
theorem binEntropy_le_log_four_mul_sqrt {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Real.binEntropy r ≤ Real.log 4 * Real.sqrt (r * (1 - r)) := by
  rcases le_total r (1/2) with h | h
  · exact binEntropy_le_log_four_mul_sqrt_of_le_half hr0 h
  · have h1r0 : 0 ≤ 1 - r := by linarith
    have h1rh : 1 - r ≤ 1/2 := by linarith
    have hrec := binEntropy_le_log_four_mul_sqrt_of_le_half h1r0 h1rh
    have harg : (1-r)*(1-(1-r)) = r*(1-r) := by ring
    rw [harg, Real.binEntropy_one_sub r] at hrec
    exact hrec

/-- For `r ∈ [0, 1]`, binary entropy in bits is at most `2 * √(r * (1 - r))`. -/
theorem binaryEntropy_le_two_sqrt {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    binaryEntropy r ≤ 2 * Real.sqrt (r * (1 - r)) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbase : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
    push_cast; ring
  have h := binEntropy_le_log_four_mul_sqrt hr0 hr1
  unfold binaryEntropy
  have hcoef : (Real.log 2)⁻¹ * Real.log 4 = 2 := by
    rw [hbase]; field_simp
  calc (Real.log 2)⁻¹ * Real.binEntropy r
      ≤ (Real.log 2)⁻¹ * (Real.log 4 * Real.sqrt (r * (1 - r))) :=
        mul_le_mul_of_nonneg_left h (le_of_lt (inv_pos.mpr hlog2))
    _ = 2 * Real.sqrt (r * (1 - r)) := by rw [← mul_assoc, hcoef]

end Qatlib.Papers.CryptoDisting99.Equivalence
