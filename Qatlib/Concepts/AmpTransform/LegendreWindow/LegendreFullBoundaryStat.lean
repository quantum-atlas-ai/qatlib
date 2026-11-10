/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.NumberTheory.DiophantineApproximation.Basic
set_option autoImplicit false
open scoped Classical BigOperators
namespace Qatlib.Concepts.AmpTransform.LegendreWindow

def LegendreFullBoundary : Prop :=
  ∀ (N P y : ℕ), 0 < N → 0 < P → P ^ 2 ≤ N → 0 < y → y < N →
    let r := (P * y) % N
    let d := min r (N - r)
    let a := (P * y) / N + if r ≤ N - r then 0 else 1
    d ≤ P / 2 →
    ∃ u b : ℕ, 0 < b ∧ Nat.Coprime u b ∧ b ∣ P ∧
      ((u : ℚ) / b = (a : ℚ) / P) ∧
      ∃ n : ℕ, (u : ℚ) / b = ((y : ℝ) / N).convergent n

end Qatlib.Concepts.AmpTransform.LegendreWindow
