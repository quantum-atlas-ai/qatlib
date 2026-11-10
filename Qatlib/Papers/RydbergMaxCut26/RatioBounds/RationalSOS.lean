/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.RatioBounds.Hypergeometric
import Qatlib.Papers.RydbergMaxCut26.RatioBounds.ConditionalRatio
set_option warningAsError false
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Qatlib.Papers.RydbergMaxCut26.RatioBounds.SOS

open Qatlib.Papers.RydbergMaxCut26.RatioBounds.Core

noncomputable def kernelConstant : ℝ := 8/(3*Real.pi)

theorem cubic_651 (t : ℝ) (ht : t≤0) :
    (651/1000:ℝ)*(1-3*t)≤(345/1000:ℝ)*(-4*t)+
      (655/1000:ℝ)*(1-(28/33:ℝ)*(t*(1+t^2/10))) := by
  have hs : 0≤(t+13/40)^2*(-t+13/20) := mul_nonneg (sq_nonneg _) (by linarith)
  nlinarith [hs]

theorem cubic_614 (t : ℝ) (ht : t≤0) :
    (614/1000:ℝ)*(1-(3/(89/100:ℝ))*t)≤(153/400:ℝ)*(-4*t)+
      (247/400:ℝ)*(1-(28/33:ℝ)*(t*(1+t^2/10))) := by
  have hs : 0≤(t+8/25)^2*(-t+16/25) := mul_nonneg (sq_nonneg _) (by linarith)
  nlinarith [hs]

theorem negative_kernel (t : ℝ) (htlo : -1≤t) (ht0 : t≤0) :
    kernelConstant*Fhat t≤(28/33:ℝ)*(t*(1+t^2/10)) := by
  have hf : Fhat t≤t*(1+t^2/10) :=
      Qatlib.Papers.RydbergMaxCut26.RatioBounds.Hypergeom.fhat_negative htlo ht0
  have hp : t*(1+t^2/10)≤0 := mul_nonpos_of_nonpos_of_nonneg ht0 (by positivity)
  have hfn : Fhat t≤0 := hf.trans hp
  have hc := Qatlib.Papers.RydbergMaxCut26.RatioBounds.Hypergeom.rounding_constant_bounds.1
  exact (mul_le_mul_of_nonpos_right hc hfn).trans (mul_le_mul_of_nonneg_left hf (by norm_num))

theorem positive_kernel (t : ℝ) (ht0 : 0≤t) (ht1 : t≤1/3) :
    kernelConstant*Fhat t≤((400/471:ℝ)*(81/80))*t := by
  have hf : Fhat t≤(81/80:ℝ)*t :=
      Qatlib.Papers.RydbergMaxCut26.RatioBounds.Hypergeom.fhat_positive ht0 ht1
  have hhyper :=
      Qatlib.Papers.RydbergMaxCut26.RatioBounds.Hypergeom.hyper_lower (sq_nonneg t)
      (by nlinarith : t^2≤1)
  have hfn : 0≤Fhat t := mul_nonneg ht0 (by nlinarith [sq_nonneg t])
  have hc := Qatlib.Papers.RydbergMaxCut26.RatioBounds.Hypergeom.rounding_constant_bounds.2
  have h := (mul_le_mul_of_nonneg_right hc hfn).trans (mul_le_mul_of_nonneg_left hf (by norm_num))
  simpa only [mul_assoc] using! h

theorem hnum_651 (t : ℝ) (ht : t∈Set.Ico (-1:ℝ) (1/3)) :
    (651/1000:ℝ)*(1-3*t)≤(345/1000:ℝ)*(-4*t)+
      (655/1000:ℝ)*(1-kernelConstant*Fhat t) := by
  by_cases ht0 : t≤0
  · have hker := negative_kernel t ht.1 ht0
    have hcub := cubic_651 t ht0
    nlinarith
  · have hpos : 0≤t := (lt_of_not_ge ht0).le
    have hker := positive_kernel t hpos ht.2.le
    nlinarith

theorem hnum_614 (t : ℝ) (ht : t∈Set.Ico (-1:ℝ) ((89/100:ℝ)/3)) :
    (614/1000:ℝ)*(1-(3/(89/100:ℝ))*t)≤(153/400:ℝ)*(-4*t)+
      (247/400:ℝ)*(1-kernelConstant*Fhat t) := by
  by_cases ht0 : t≤0
  · have hker := negative_kernel t ht.1 ht0
    have hcub := cubic_614 t ht0
    nlinarith
  · have hpos : 0≤t := (lt_of_not_ge ht0).le
    have hsmall : t≤1/3 := by linarith [ht.2]
    have hker := positive_kernel t hpos hsmall
    nlinarith
end Qatlib.Papers.RydbergMaxCut26.RatioBounds.SOS
