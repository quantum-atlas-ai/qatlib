/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Qatlib.Papers.UniversalWalk08.MainResults.ScatteringDefs

set_option autoImplicit false

noncomputable def scatteringPhase (k x t : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((k : ℂ) * (x : ℂ)) -
    2 * Complex.I * (t : ℂ) * (Real.cos k : ℂ))

noncomputable def scatteringAmplitude {n : ℕ} (T : Fin (2 ^ n) → ℝ → ℂ)
    (x t : ℝ) (s : Fin (2 ^ n)) : ℂ :=
  (1 / (2 * (Real.pi : ℂ))) *
    ∫ k in (-Real.pi)..0, scatteringPhase k x t * T s k

@[simp]
theorem scatteringPhase_zero_zero (k : ℝ) : scatteringPhase k 0 0 = 1 := by
  simp [scatteringPhase]

@[simp]
theorem scatteringAmplitude_zero {n : ℕ} (x t : ℝ) (s : Fin (2 ^ n)) :
    scatteringAmplitude (n := n) (fun _ _ => 0) x t s = 0 := by
  simp [scatteringAmplitude]

theorem scatteringPhase_eq_exp_ofReal_mul_I (k x t : ℝ) :
    scatteringPhase k x t =
      Complex.exp (((k * x - 2 * t * Real.cos k : ℝ) : ℂ) * Complex.I) := by
  unfold scatteringPhase
  congr 1
  push_cast
  ring

theorem norm_scatteringPhase (k x t : ℝ) : ‖scatteringPhase k x t‖ = 1 := by
  rw [scatteringPhase_eq_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I]

theorem normSq_scatteringPhase (k x t : ℝ) :
    Complex.normSq (scatteringPhase k x t) = 1 := by
  rw [Complex.normSq_eq_norm_sq, norm_scatteringPhase]
  norm_num

end Qatlib.Papers.UniversalWalk08.MainResults.ScatteringDefs
