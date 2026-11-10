/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.RatioBounds.RationalSOS
import Qatlib.Papers.RydbergMaxCut26.MainResults.MeasureHybrid
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Matrix Qatlib MeasureTheory
open Qatlib.Foundations.PureStateMath
open scoped Classical ComplexOrder
namespace Qatlib.Papers.RydbergMaxCut26.RatioBounds.Clipped
open Qatlib.Papers.RydbergMaxCut26.RatioBounds.SOS
open Qatlib.Papers.RydbergMaxCut26.RatioBounds.Hypergeom

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

theorem ratio_of_energy (Eout Eopt κ : ℝ) (hopt : Eopt < 0) (h : Eout ≤ κ*Eopt) :
    κ ≤ Eout/Eopt := (le_div_iff_of_neg hopt).mpr h

theorem weaken_energy (Eout Eopt κ c : ℝ) (hopt : Eopt ≤ 0) (h : Eout ≤ κ*Eopt)
    (hc : c ≤ κ) : Eout ≤ c*Eopt :=
  h.trans (mul_le_mul_of_nonpos_right hc hopt)
end Qatlib.Papers.RydbergMaxCut26.RatioBounds.Clipped
