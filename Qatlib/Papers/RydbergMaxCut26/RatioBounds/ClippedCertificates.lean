/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.RatioBounds.RationalSOS
import Qatlib.Papers.RydbergMaxCut26.MainResults.MeasureHybrid

/-!
# Clipped scalar certificates and weighted energy transfer

`clipped_651` and `clipped_614` extend the scalar approximation certificates to clipped
denominators using the kernel identity and the upper bound `k ≤ 1`. `weighted_energy` sums these
inequalities with nonnegative edge weights and combines candidate upper bounds with a
comparison-energy lower bound; the final lemmas translate energy bounds into ratios or weaker
constants.

These results support the development of [CrostaSaubanereHuber2026].

## Main statements

* `clipped_651` and `clipped_614`: certify the ideal and robust factors.
* `weighted_energy`: transfers edge certificates to a global energy bound.
* `ratio_of_energy`: handles division by a negative optimum.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Matrix Qatlib MeasureTheory
open Qatlib.Foundations.PureStateMath
open scoped Classical ComplexOrder
namespace Qatlib.Papers.RydbergMaxCut26.RatioBounds.Clipped
open Qatlib.Papers.RydbergMaxCut26.RatioBounds.SOS
open Qatlib.Papers.RydbergMaxCut26.RatioBounds.Hypergeom

/-- If `t ≥ -1`, `k ≤ 1`, and `k = kernelConstant * Fhat t`, then 651/1000 times the clipped
denominator `max (1-3*t) 0` is bounded by the mixture with weights 345/1000 and 655/1000.
This supplies the clipped ideal certificate for [CrostaSaubanereHuber2026]. -/
theorem clipped_651 (t k : ℝ) (ht : -1 ≤ t) (hk : k ≤ 1)
    (hkernel : k=kernelConstant*Qatlib.Papers.RydbergMaxCut26.RatioBounds.Core.Fhat t) :
    (651/1000:ℝ)*max (1-3*t) 0 ≤
      (345/1000:ℝ)*(-4*min t 0)+(655/1000:ℝ)*(1-k) := by
  by_cases hsmall : t < 1/3
  · have hn := hnum_651 t ⟨ht,hsmall⟩
    rw [max_eq_left (by linarith : 0 ≤ 1-3*t)]
    rw [hkernel]
    have hm := min_le_left t 0
    linarith
  · have ht0 : 0 ≤ t := by linarith
    rw [max_eq_right (by linarith : 1-3*t ≤ 0),min_eq_right ht0]
    nlinarith

/-- If `t ≥ -1`, `k ≤ 1`, and `k = kernelConstant * Fhat t`, then 614/1000 times `max
(1-(3/(89/100))*t) 0` is bounded by the mixture with weights 153/400 and 247/400, giving the
robust scalar certificate of [CrostaSaubanereHuber2026]. -/
theorem clipped_614 (t k : ℝ) (ht : -1 ≤ t) (hk : k ≤ 1)
    (hkernel : k=kernelConstant*Qatlib.Papers.RydbergMaxCut26.RatioBounds.Core.Fhat t) :
    (614/1000:ℝ)*max (1-(3/(89/100:ℝ))*t) 0 ≤
      (153/400:ℝ)*(-4*min t 0)+(247/400:ℝ)*(1-k) := by
  by_cases hsmall : t < (89/100:ℝ)/3
  · have hn := hnum_614 t ⟨ht,hsmall⟩
    rw [max_eq_left (by linarith : 0 ≤ 1-(3/(89/100:ℝ))*t)]
    rw [hkernel]
    have hm := min_le_left t 0
    linarith
  · have ht0 : 0 ≤ t := by linarith
    rw [max_eq_right (by linarith : 1-(3/(89/100:ℝ))*t ≤ 0),min_eq_right ht0]
    nlinarith

/-- Nonnegative edge weights and the stated edgewise certificate, candidate bounds, and
comparison lower bound imply `p*ER + (1-p)*EP ≤ κ*EQ` when `κ` and `p` are nonnegative. -/
theorem weighted_energy {E : Type*} [Fintype E] (w t k : E → ℝ)
    (hw : ∀ e,0 ≤ w e) (η κ p ER EP EQ : ℝ) (hκ : 0 ≤ κ) (hp : 0 ≤ p)
    (hedge : ∀ e,κ*max (1-(3/η)*t e) 0 ≤ p*(-4*min (t e) 0)+(1-p)*(1-k e))
    (hR : ER ≤ ∑ e,w e*min (t e) 0)
    (hP : EP=-(1/4:ℝ)*∑ e,w e*(1-k e))
    (hQ : -(1/4:ℝ)*∑ e,w e*max (1-(3/η)*t e) 0 ≤ EQ) :
    p*ER+(1-p)*EP ≤ κ*EQ := by
  have hs := Finset.sum_le_sum (fun e (_ : e∈Finset.univ) =>
    mul_le_mul_of_nonneg_left (hedge e) (hw e))
  have he (e : E) : w e*(p*(-4*min (t e) 0)+(1-p)*(1-k e))=
      -4*p*(w e*min (t e) 0)+(1-p)*(w e*(1-k e)) := by ring
  have hd (e : E) : w e*(κ*max (1-(3/η)*t e) 0)=κ*(w e*max (1-(3/η)*t e) 0) := by ring
  simp_rw [he,hd] at hs
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,← Finset.mul_sum] at hs
  have hr := mul_le_mul_of_nonneg_left hR hp
  have hq := mul_le_mul_of_nonneg_left hQ hκ
  rw [hP]
  nlinarith

/-- If `Eopt < 0` and `Eout ≤ κ*Eopt`, division by the negative optimum gives `κ ≤ Eout/Eopt`. -/
theorem ratio_of_energy (Eout Eopt κ : ℝ) (hopt : Eopt < 0) (h : Eout ≤ κ*Eopt) :
    κ ≤ Eout/Eopt := (le_div_iff_of_neg hopt).mpr h

/-- If `Eopt ≤ 0`, an energy bound with factor `κ` implies the corresponding bound with any
smaller factor `c`. -/
theorem weaken_energy (Eout Eopt κ c : ℝ) (hopt : Eopt ≤ 0) (h : Eout ≤ κ*Eopt)
    (hc : c ≤ κ) : Eout ≤ c*Eopt :=
  h.trans (mul_le_mul_of_nonpos_right hc hopt)
end Qatlib.Papers.RydbergMaxCut26.RatioBounds.Clipped
