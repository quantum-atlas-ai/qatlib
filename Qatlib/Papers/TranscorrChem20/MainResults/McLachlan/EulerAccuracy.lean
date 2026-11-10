/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TranscorrChem20.MainResults.McLachlan.Basic
import Qatlib.Concepts.ImaginaryFlow.LeastSquares.EulerError
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Set
open Qatlib.Concepts.ImaginaryFlow.LeastSquares

namespace Qatlib.Papers.TranscorrChem20.MainResults.McLachlan

theorem parameter_euler_local_error {n : ℕ} (Θ : ℝ → (Fin n → ℝ)) (a b : ℝ)
    (hab : a < b) (hΘ : ContDiffOn ℝ 2 Θ (Icc a b)) (rate : Fin n → ℝ)
    (hRate : HasDerivAt Θ rate a) :
    ∃ C : ℝ, ∀ x ∈ Icc a b, ‖Θ x - (Θ a + (x-a) • rate)‖ ≤ C * (x-a)^2 :=
  curve_euler_error Θ a b hab hΘ rate hRate

def scalarCutoffRate (threshold a c : ℝ) : ℝ :=
  if threshold < |a| then - c / a else 0

theorem cutoff_need_not_solve_normal_equation :
    let a : ℝ := 1/10000000
    let threshold : ℝ := 1/1000000
    a * scalarCutoffRate threshold a 1 + 1 = 1 := by
  norm_num [scalarCutoffRate]

end Qatlib.Papers.TranscorrChem20.MainResults.McLachlan
