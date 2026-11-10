/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

set_option autoImplicit false
namespace Qatlib.Papers.QAlgorithms97.MainResults.PhaseEstimation

theorem appendixC_counter_grid :
    (0 : ℝ) < 1 / 4 ∧ (1 / 4 : ℝ) ≤ 1 / (2 : ℝ) ^ (1 + 1) ∧
      (∀ a : Fin 2, (a.val : ℝ) / 2 ≠ (1 / 4 : ℝ)) ∧
      (∀ a : Fin 2, |(1 / 4 : ℝ) - 0| ≤ |(1 / 4 : ℝ) - a.val / 2|) ∧
      (-(2 : ℤ) ^ (1 - 1) ≤ 0 ∧ (0 : ℤ) < 2 ^ (1 - 1)) := by
  norm_num

theorem appendixC_printed_chord_counter :
    ¬ ‖(1 : ℂ) - Complex.exp (2 * Real.pi * Complex.I * (1 / 4 : ℂ))‖ ≤
      4 * (1 / 4 : ℝ) := by
  have he : Complex.exp (2 * Real.pi * Complex.I * (1 / 4 : ℂ)) = Complex.I := by
    convert Complex.exp_pi_div_two_mul_I using 1
    congr 1
    ring
  rw [he]
  have hs : ‖(1 : ℂ) - Complex.I‖ ^ 2 = 2 := by
    rw [Complex.sq_norm]
    norm_num [Complex.normSq_apply]
  have hn := norm_nonneg ((1 : ℂ) - Complex.I)
  norm_num only [show 4 * (1 / 4 : ℝ) = 1 by norm_num]
  nlinarith

end Qatlib.Papers.QAlgorithms97.MainResults.PhaseEstimation
