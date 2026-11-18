/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

import Qatlib.Foundations.ScaledSqrt.SqrtBounds.RootCountOrder

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Foundations.ScaledSqrt.SqrtBounds

/-- A plain module consumer can apply the order theorem without private imports. -/
theorem rootCount_order_consumer (half : ℕ) {p q : ℚ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    rootCount half p ≤ rootCount half q :=
  rootCount_mono half hp hpq

/-- The interface includes a zero lower input. -/
theorem rootCount_zero_input_consumer (half : ℕ) :
    rootCount half 0 ≤ rootCount half 1 :=
  rootCount_mono half (by decide) (by decide)

/-- A plain definition consumes the count interface without a noncomputable section. -/
def executableCount : ℕ := rootCount 8 (1 / 4)

/-- The public bound includes zero scale without unfolding implementation details. -/
theorem rootCount_zero_scale_consumer : rootCount 0 (1 / 4) = 0 := by
  exact Nat.eq_zero_of_le_zero (rootCount_le_half 0 (1 / 4) (by norm_num) (by norm_num))
