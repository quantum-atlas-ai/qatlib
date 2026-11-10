/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false

namespace CBMD

open MeasureTheory
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem dyson_generator_real_inner
    (H L : E →L[ℂ] E) (hH : H.IsSymmetric) (hL : L.IsSymmetric) (z : ℂ) (v : E) :
    (inner ℂ v ((-Complex.I) • (H v + z • L v))).re =
      z.im * (inner ℂ v (L v)).re := by
  have hHi := hH.im_inner_self_apply v
  have hLi := hL.im_inner_self_apply v
  change (inner ℂ v (H v)).im = 0 at hHi
  change (inner ℂ v (L v)).im = 0 at hLi
  simp [inner_smul_right, inner_add_right, Complex.mul_re, Complex.mul_im,
    hHi, hLi]

theorem dyson_generator_energy_le
    (H L : E →L[ℂ] E) (hH : H.IsSymmetric) (hL : L.IsPositive) (z : ℂ) (v : E) :
    (inner ℂ v ((-Complex.I) • (H v + z • L v))).re ≤
      max z.im 0 * ‖L‖ * ‖v‖ ^ 2 := by
  rw [dyson_generator_real_inner H L hH hL.isSymmetric z v]
  have hq : 0 ≤ (inner ℂ v (L v)).re := hL.re_inner_nonneg_right v
  have hupper : (inner ℂ v (L v)).re ≤ ‖L‖ * ‖v‖ ^ 2 := by
    calc
      _ ≤ ‖v‖ * ‖L v‖ := re_inner_le_norm (𝕜 := ℂ) v (L v)
      _ ≤ ‖v‖ * (‖L‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left (L.le_opNorm v) (norm_nonneg _)
      _ = _ := by ring
  calc
    _ ≤ max z.im 0 * (inner ℂ v (L v)).re :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hq
    _ ≤ max z.im 0 * (‖L‖ * ‖v‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hupper (le_max_right _ _)
    _ = _ := by ring

theorem dyson_trajectory_norm_le
    (H L : ℝ → E →L[ℂ] E) (hL : Continuous L)
    (hHsym : ∀ u, (H u).IsSymmetric) (hLpos : ∀ u, (L u).IsPositive)
    (z : ℂ) (v : ℝ → E)
    (hv : ∀ u, HasDerivAt v ((-Complex.I) • (H u (v u) + z • L u (v u))) u)
    (s t : ℝ) (hst : s ≤ t) :
    ‖v t‖ ≤ Real.exp (max z.im 0 * ∫ u in s..t, ‖L u‖) * ‖v s‖ := by
  letI := InnerProductSpace.rclikeToReal ℂ E
  let c : ℝ := max z.im 0
  let R : ℝ → ℝ := fun r => ∫ u in s..r, ‖L u‖
  have hR (u : ℝ) : HasDerivAt R ‖L u‖ u :=
    intervalIntegral.integral_hasDerivAt_right (hL.norm.intervalIntegrable _ _)
      hL.norm.aestronglyMeasurable.stronglyMeasurableAtFilter hL.norm.continuousAt
  have hsq (u : ℝ) : HasDerivAt (fun r => ‖v r‖ ^ 2)
      (2 * (inner ℂ (v u) ((-Complex.I) • (H u (v u) + z • L u (v u)))).re) u := by
    simpa only [real_inner_eq_re_inner (𝕜 := ℂ)] using! (hv u).norm_sq
  let f : ℝ → ℝ := fun r => Real.exp (-2 * c * R r) * ‖v r‖ ^ 2
  have hd (u : ℝ) : HasDerivAt f
      (Real.exp (-2 * c * R u) * (-2 * c * ‖L u‖) * ‖v u‖ ^ 2 +
        Real.exp (-2 * c * R u) *
          (2 * (inner ℂ (v u) ((-Complex.I) • (H u (v u) + z • L u (v u)))).re)) u := by
    exact (((hR u).const_mul (-2 * c)).exp).mul (hsq u)
  have hd₀ (u : ℝ) :
      Real.exp (-2 * c * R u) * (-2 * c * ‖L u‖) * ‖v u‖ ^ 2 +
        Real.exp (-2 * c * R u) *
          (2 * (inner ℂ (v u) ((-Complex.I) • (H u (v u) + z • L u (v u)))).re) ≤ 0 := by
    have he := dyson_generator_energy_le (H u) (L u) (hHsym u) (hLpos u) z (v u)
    have hh := mul_le_mul_of_nonneg_left he (Real.exp_pos (-2 * c * R u)).le
    dsimp only [c] at *
    nlinarith
  have hm : Antitone f := antitone_of_hasDerivAt_nonpos hd hd₀
  have hb := hm hst
  have hfs : f s = ‖v s‖ ^ 2 := by simp [f, R]
  rw [hfs] at hb
  have hexp : Real.exp (-2 * c * R t) = Real.exp (-c * R t) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  change Real.exp (-2 * c * R t) * ‖v t‖ ^ 2 ≤ ‖v s‖ ^ 2 at hb
  rw [hexp, ← mul_pow] at hb
  have hroot := (sq_le_sq₀ (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
    (norm_nonneg _)).mp hb
  have hh := mul_le_mul_of_nonneg_left hroot (Real.exp_pos (c * R t)).le
  rw [← mul_assoc, ← Real.exp_add,
    show c * R t + -c * R t = 0 by ring, Real.exp_zero, one_mul] at hh
  exact hh

end CBMD

end Qatlib.Foundations.CbmdAnalysis.Core
