/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.Rounding.Analytic.ActualGaussianKernel
import Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianSymmetry
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
open scoped Classical
open MeasureTheory ProbabilityTheory Set Real

namespace Qatlib.Papers.RydbergMaxCut26.Rounding.Laplace
open Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianPair

theorem actualKernel_hypergeom_closed (t : ℝ) (ht : |t|≤1) :
    actualKernel t=(8/(3*Real.pi))*t*₂F₁ (1/2:ℝ) (1/2) (5/2) (t^2) := by
  by_cases hi : |t|<1
  · exact actualKernel_hypergeom t hi
  have he : |t|=1 := le_antisymm ht (le_of_not_gt hi)
  rcases (abs_eq (by norm_num : (0:ℝ)≤1)).mp he with h|h
  · subst t
    rw [actualKernel_one]
    norm_num only [one_pow,Qatlib.Papers.RydbergMaxCut26.RatioBounds.Euler.gauss_endpoint_one]
    field_simp
  · subst t
    rw [actualKernel_neg_one]
    norm_num only [neg_sq,one_pow,Qatlib.Papers.RydbergMaxCut26.RatioBounds.Euler.gauss_endpoint_one]
    field_simp

theorem roundedLaw_hypergeom (t : ℝ) (ht : |t|≤1) :
    (∫ p,inner ℝ p.1 p.2 ∂roundedLaw t)=
      (8/(3*Real.pi))*t*₂F₁ (1/2:ℝ) (1/2) (5/2) (t^2) := by
  rw [roundedLaw_expect,actualKernel_hypergeom_closed t ht]

end Qatlib.Papers.RydbergMaxCut26.Rounding.Laplace
