/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic

/-!
# Nonvacuity of low-degree cutoffs

Defines `DLoNonvacuity`, the eventual positivity requirement for the floored low-degree cutoffs
used in the classification analysis. It covers exponents `1 - δ` for `0 < δ < 1` and the fixed
exponent `6 / 7`; see [Ambainis2005] for the surrounding graph-search setting.

## Main statements

* `DLoNonvacuity`: The conjunction asserting eventual positivity of `Nat.floor ((n : ℝ) ^ (1 -
  δ) / 10)` for each `0 < δ < 1` and of the analogous cutoff with exponent `6 / 7`.

## References

* [Ambainis, 2005][Ambainis2005]
-/

namespace Qatlib.Concepts.WalkSearch.Primitives

/-- The conjunction asserting eventual positivity of `Nat.floor ((n : ℝ) ^ (1 - δ) / 10)` for
each `0 < δ < 1` and of the analogous cutoff with exponent `6 / 7`. -/
def DLoNonvacuity : Prop :=
  (∀ (δ : ℝ), 0 < δ → δ < 1 →
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → 1 ≤ Nat.floor ((n:ℝ)^(1-δ)/10)) ∧
  (∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → 1 ≤ Nat.floor ((n:ℝ)^((6:ℝ)/7)/10))

end Qatlib.Concepts.WalkSearch.Primitives
