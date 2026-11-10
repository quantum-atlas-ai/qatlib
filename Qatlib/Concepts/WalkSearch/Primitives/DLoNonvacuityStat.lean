/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic

namespace Qatlib.Concepts.WalkSearch.Primitives

def DLoNonvacuity : Prop :=
  (∀ (δ : ℝ), 0 < δ → δ < 1 →
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → 1 ≤ Nat.floor ((n:ℝ)^(1-δ)/10)) ∧
  (∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → 1 ≤ Nat.floor ((n:ℝ)^((6:ℝ)/7)/10))

end Qatlib.Concepts.WalkSearch.Primitives
