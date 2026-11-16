/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic

@[expose] public section


set_option autoImplicit false

namespace Qatlib.Papers.NoncommGibbs23.MainResults

/-- Multiplying an explicitly assumed scalar factorization by its nonzero
Fourier normalization recovers the unnormalized kernel. -/
theorem corollaryA1_factorizedTimeDomain (fhat : ℝ → ℝ → ℂ) (fp fm : ℝ → ℂ)
    (hfac : ∀ ν1 ν2 : ℝ,
      (1 / (2 * Real.pi) : ℂ) * fhat ν1 ν2 = fp (ν1 + ν2) * fm (ν1 - ν2)) :
    ∀ ν1 ν2 : ℝ, fhat ν1 ν2 = (2 * Real.pi : ℂ) * (fp (ν1 + ν2) * fm (ν1 - ν2)) := by
  intro ν1 ν2
  rw [← hfac]
  field_simp

end Qatlib.Papers.NoncommGibbs23.MainResults
