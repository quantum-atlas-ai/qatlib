/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Qatlib.Concepts.SearchStopping.GroverSuccess

open scoped BigOperators

def Lemma1Restricted : Prop :=
  (∀ (α β : ℝ) (m : ℕ), 0 < m → Real.sin β ≠ 0 →
    (∑ j ∈ Finset.range m, Real.cos (α + 2 * β * j)) =
      Real.sin (m * β) * Real.cos (α + ((m : ℝ) - 1) * β) / Real.sin β) ∧
  (∀ (α : ℝ) (m : ℕ), 0 < m → Real.sin α ≠ 0 →
    (∑ j ∈ Finset.range m, Real.cos ((2 * j + 1) * α)) =
      Real.sin (2 * m * α) / (2 * Real.sin α))

end Qatlib.Concepts.SearchStopping.GroverSuccess
