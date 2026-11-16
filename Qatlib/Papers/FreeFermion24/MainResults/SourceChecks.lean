/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.FreeFermion24.MainResults.SourceModel
public import Mathlib.Tactic.NormNum

@[expose] public section


set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.FreeFermion24.MainResults.SourceChecks

open Qatlib.Papers.FreeFermion24.MainResults.Model

/-- The legacy Green function has a nonzero imaginary component at the origin. -/
theorem green_origin : gDeltaBetaOmega 1 1 1 0 0 = -(Complex.I / 8) := by
  norm_num [gDeltaBetaOmega, Complex.inv_def]
  ring

/-- A real scalar cannot approximate the legacy Green function at the origin arbitrarily well. -/
theorem green_real_gap (a : ℝ) :
    (1 / 8 : ℝ) ≤ ‖gDeltaBetaOmega 1 1 1 0 0 - (a : ℂ)‖ := by
  rw [green_origin]
  have h := Complex.abs_im_le_norm (-(Complex.I / 8) - (a : ℂ))
  norm_num at h ⊢
  exact h

/-- Real-coefficient polynomial approximants fail the required small error already at zero. -/
theorem green_poly_gap (p : Polynomial ℝ) :
    ¬ ‖gDeltaBetaOmega 1 1 1 0 0 - ((p.eval 0 : ℝ) : ℂ)‖ ≤ 1 / 16 := by
  have h := green_real_gap (p.eval 0)
  linarith

end Qatlib.Papers.FreeFermion24.MainResults.SourceChecks
