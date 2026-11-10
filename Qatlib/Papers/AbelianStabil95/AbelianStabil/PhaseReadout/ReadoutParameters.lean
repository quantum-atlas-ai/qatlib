/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
namespace Qatlib.Papers.AbelianStabil95.AbelianStabil.PhaseReadout

def bisectRange (l : ℕ) : ℕ := 2 ^ l - 1

theorem bisectRange_succ (l : ℕ) : bisectRange l + 1 = 2 ^ l := by
  unfold bisectRange
  have h : 0 < 2 ^ l := by positivity
  omega

theorem bisectPrecision_pos (l : ℕ) : (0 : ℝ) < (2 : ℝ) ^ (-(l : ℤ) - 2) := by
  positivity

end Qatlib.Papers.AbelianStabil95.AbelianStabil.PhaseReadout
