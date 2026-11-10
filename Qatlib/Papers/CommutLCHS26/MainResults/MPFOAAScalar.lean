/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.MPFOAASine
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.MeanValue
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.MPFOAAScalar

open Set
open scoped NNReal
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open MPFOAASine

def poly (n : ℕ) : Polynomial ℂ := responseP (-Complex.I) (List.replicate (2 * n + 1) Complex.I)

theorem eval_real (n : ℕ) (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    (poly n).eval (x : ℂ) = (Real.sin (((2 * n + 1 : ℕ) : ℝ) * Real.arcsin x) : ℂ) := by
  have h := (sine_response n (Real.arcsin x)).1
  rwa [Real.sin_arcsin hx.1 hx.2] at h

theorem arcsin_derivative_bound (x : ℝ) (hx : x ∈ Icc (-(3 / 5) : ℝ) (3 / 5)) :
    ‖1 / Real.sqrt (1 - x ^ 2)‖ ≤ 5 / 4 := by
  have hs : (4 / 5 : ℝ) ≤ Real.sqrt (1 - x ^ 2) := by
    apply (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 4 / 5)
      (by nlinarith [hx.1, hx.2] : 0 ≤ 1 - x ^ 2)).mpr
    nlinarith [hx.1, hx.2]
  have hp : 0 < Real.sqrt (1 - x ^ 2) := by linarith
  rw [Real.norm_eq_abs, abs_of_pos (div_pos one_pos hp)]
  apply (div_le_iff₀ hp).mpr
  linarith

theorem arcsin_sub_bound (x y : ℝ) (hx : x ∈ Icc (-(3 / 5) : ℝ) (3 / 5))
    (hy : y ∈ Icc (-(3 / 5) : ℝ) (3 / 5)) :
    |Real.arcsin x - Real.arcsin y| ≤ (5 / 4 : ℝ) * |x - y| := by
  have hd (z : ℝ) (hz : z ∈ Icc (-(3 / 5) : ℝ) (3 / 5)) :
      HasDerivWithinAt Real.arcsin (1 / Real.sqrt (1 - z ^ 2)) (Icc (-(3 / 5) : ℝ) (3 / 5)) z :=
    (Real.hasDerivAt_arcsin (by intro h; subst z; norm_num at hz)
      (by intro h; subst z; norm_num at hz)).hasDerivWithinAt
  simpa only [Real.norm_eq_abs] using (convex_Icc (-(3 / 5) : ℝ) (3 / 5)).norm_image_sub_le_of_norm_hasDerivWithin_le
    hd arcsin_derivative_bound hy hx

theorem eval_sub_bound (n : ℕ) (x y : ℝ) (hx : x ∈ Icc (-(3 / 5) : ℝ) (3 / 5))
    (hy : y ∈ Icc (-(3 / 5) : ℝ) (3 / 5)) :
    ‖(poly n).eval (x : ℂ) - (poly n).eval (y : ℂ)‖ ≤
      ((5 / 4 : ℝ) * ((2 * n + 1 : ℕ) : ℝ)) * |x - y| := by
  rw [eval_real n x (by constructor <;> linarith [hx.1, hx.2]),
    eval_real n y (by constructor <;> linarith [hy.1, hy.2]), ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ |(((2 * n + 1 : ℕ) : ℝ) * Real.arcsin x) -
        (((2 * n + 1 : ℕ) : ℝ) * Real.arcsin y)| := Real.abs_sin_sub_sin_le _ _
    _ = ((2 * n + 1 : ℕ) : ℝ) * |Real.arcsin x - Real.arcsin y| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    _ ≤ ((2 * n + 1 : ℕ) : ℝ) * ((5 / 4 : ℝ) * |x - y|) :=
      mul_le_mul_of_nonneg_left (arcsin_sub_bound x y hx hy) (Nat.cast_nonneg _)
    _ = _ := by ring

theorem eval_lipschitz (n : ℕ) :
    LipschitzOnWith (⟨(5 / 4 : ℝ) * ((2 * n + 1 : ℕ) : ℝ), by positivity⟩ : ℝ≥0)
      (fun x : ℝ => (poly n).eval (x : ℂ)) (Icc (-(3 / 5) : ℝ) (3 / 5)) := by
  rw [lipschitzOnWith_iff_norm_sub_le]
  intro x hx y hy
  simpa only [Real.norm_eq_abs] using! eval_sub_bound n x y hx hy

end Qatlib.Papers.CommutLCHS26.MainResults.MPFOAAScalar
