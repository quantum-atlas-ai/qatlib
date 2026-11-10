/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.Rounding.Analytic.PositiveChart
import Qatlib.Papers.RydbergMaxCut26.Rounding.Analytic.LaplaceNorm
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical
open MeasureTheory Set Real

namespace Qatlib.Papers.RydbergMaxCut26.Rounding.Laplace

def halfAffine (A B a : ℝ) : ℝ :=
  1/(Real.sqrt a*(A+B*a)^2*Real.sqrt (A+B*a))

theorem halfAffine_chart (A B u : ℝ) (hA : 0<A) (hB : 0<B) (hu : u∈Ioo (0:ℝ) 1) :
    (2*(A/B)*u/(1-u^2)^2)*halfAffine A B (positiveChart (A/B) u)=
      (2/(A^2*Real.sqrt B))*(1-u^2) := by
  have hq := chart_den_pos hu
  have hs : Real.sqrt (positiveChart (A/B) u)=
      Real.sqrt A*u/(Real.sqrt B*Real.sqrt (1-u^2)) := by
    rw [positiveChart,Real.sqrt_div (mul_nonneg (div_nonneg hA.le hB.le) (sq_nonneg u)),
      Real.sqrt_mul (div_nonneg hA.le hB.le),Real.sqrt_div hA.le,Real.sqrt_sq hu.1.le]
    ring
  have he : A+B*positiveChart (A/B) u=A/(1-u^2) := by
    unfold positiveChart
    field_simp
    ring
  rw [halfAffine,hs,he,Real.sqrt_div hA.le]
  have hsA := (Real.sqrt_pos.mpr hA).ne'
  have hsB := (Real.sqrt_pos.mpr hB).ne'
  have hsq := (Real.sqrt_pos.mpr hq).ne'
  field_simp [hu.1.ne']
  rw [Real.sq_sqrt hq.le,Real.sq_sqrt hA.le,Real.sq_sqrt hB.le]
  ring

theorem halfAffine_integral (A B : ℝ) (hA : 0<A) (hB : 0<B) :
    (∫ a in Ioi (0:ℝ),halfAffine A B a)=4/(3*A^2*Real.sqrt B) := by
  rw [positiveChart_integral (div_pos hA hB)]
  have he : (∫ u in Ioo (0:ℝ) 1,(2*(A/B)*u/(1-u^2)^2)*halfAffine A B (positiveChart (A/B) u))=
      ∫ u in Ioo (0:ℝ) 1,(2/(A^2*Real.sqrt B))*(1-u^2) :=
    setIntegral_congr_fun measurableSet_Ioo (fun u hu => halfAffine_chart A B u hA hB hu)
  rw [he,integral_const_mul,← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
  rw [intervalIntegral.integral_sub (intervalIntegrable_const (c:=(1:ℝ))) ((continuous_pow 2).intervalIntegrable 0 1),intervalIntegral.integral_const,integral_pow]
  norm_num
  ring

end Qatlib.Papers.RydbergMaxCut26.Rounding.Laplace
