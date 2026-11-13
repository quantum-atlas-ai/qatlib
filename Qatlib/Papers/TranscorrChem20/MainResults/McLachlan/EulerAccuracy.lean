/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TranscorrChem20.MainResults.McLachlan.Basic
import Qatlib.Concepts.ImaginaryFlow.LeastSquares.EulerError

/-!
# Euler accuracy and a cutoff-rate example

This module bounds the local Euler error of a twice continuously differentiable parameter curve
by a constant times the squared step. It also defines `scalarCutoffRate` and gives explicit
coefficients for which thresholding leaves a nonzero normal-equation residual. See
[McArdleTew2020].

## Main statements

* `parameter_euler_local_error`: Quadratic error bound on a compact interval.
* `cutoff_need_not_solve_normal_equation`: A scalar thresholding example with residual one.

## References

* [McArdle and Tew, 2020][McArdleTew2020]
-/

set_option autoImplicit false
noncomputable section
open Set
open Qatlib.Concepts.ImaginaryFlow.LeastSquares

namespace Qatlib.Papers.TranscorrChem20.MainResults.McLachlan

/-- A parameter curve that is twice continuously differentiable on a nontrivial compact interval
has a uniform quadratic error bound relative to its Euler approximation at the left
endpoint. See [McArdleTew2020]. -/
theorem parameter_euler_local_error {n : ℕ} (Θ : ℝ → (Fin n → ℝ)) (a b : ℝ)
    (hab : a < b) (hΘ : ContDiffOn ℝ 2 Θ (Icc a b)) (rate : Fin n → ℝ)
    (hRate : HasDerivAt Θ rate a) :
    ∃ C : ℝ, ∀ x ∈ Icc a b, ‖Θ x - (Θ a + (x-a) • rate)‖ ≤ C * (x-a)^2 :=
  curve_euler_error Θ a b hab hΘ rate hRate

/-- The scalar rate `-c / a` when `|a|` exceeds the threshold, and zero otherwise. -/
def scalarCutoffRate (threshold a c : ℝ) : ℝ :=
  if threshold < |a| then - c / a else 0

/-- For coefficient `1/10000000` and threshold `1/1000000`, the cutoff rate with forcing one
leaves normal-equation residual one. See [McArdleTew2020]. -/
theorem cutoff_need_not_solve_normal_equation :
    let a : ℝ := 1/10000000
    let threshold : ℝ := 1/1000000
    a * scalarCutoffRate threshold a 1 + 1 = 1 := by
  norm_num [scalarCutoffRate]

end Qatlib.Papers.TranscorrChem20.MainResults.McLachlan
