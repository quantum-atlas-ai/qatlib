/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.ResourceBounds.LogBudgets
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Conditional resource formulas for quantum preimage search

This module defines the real-valued resource expressions used in the conditional preimage-search
estimates of [AmyEtAl2017]. `ledgerIterations` records the floored Grover iteration estimate,
`surfaceCodeCycles` converts iteration count and T-depth into cycles, and `totalCost` combines a
qubit count with a cycle count.

The identity `overhead_eq` expresses the logarithmic overhead using the denominator eight.

## Main statements

* `ledgerIterations`: The real-valued integer floor of `(π / 4) * 2 ^ k`, used as the iteration
  ledger.
* `totalCost`: The product `(n + Φ * nDist) * σ` of the combined qubit count and the cycle
  count.
* `overhead_eq`: The overhead equals `(log2 total - k) / 8`.

## References

* [Amy et al., 2017][AmyEtAl2017]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QPreimage16.ConditionalCost

open Qatlib.Foundations.ResourceBounds.LogBudgets

/-- The real-valued integer floor of `(π / 4) * 2 ^ k`, used as the iteration ledger. -/
noncomputable def ledgerIterations (k : ℕ) : ℝ :=
  ((Int.floor ((Real.pi / 4) * (2 : ℝ) ^ k) : ℤ) : ℝ)

/-- The cycle expression `iters * 530 * (2 * tDepth)` for the conditional surface-code cost
model. -/
noncomputable def surfaceCodeCycles (iters tDepth : ℝ) : ℝ :=
  iters * 530 * (2 * tDepth)

/-- The product `(n + Φ * nDist) * σ` of the combined qubit count and the cycle count. -/
noncomputable def totalCost (n Φ nDist σ : ℝ) : ℝ := (n + Φ * nDist) * σ

/-- The logarithmic overhead `(log2 total - k) / log2 256` relative to exponent `k`. -/
noncomputable def overhead (total : ℝ) (k : ℕ) : ℝ := (log2 total - k) / log2 256

/-- The base-two logarithm of 256 is eight. -/
theorem log2_256 : log2 256 = 8 := by
  unfold log2
  have h : (256 : ℝ) = 2 ^ (8 : ℕ) := by norm_num
  rw [h, Real.logb_pow]
  rw [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
  norm_num

/-- The overhead equals `(log2 total - k) / 8`. -/
theorem overhead_eq (total : ℝ) (k : ℕ) :
    overhead total k = (log2 total - k) / 8 := by
  unfold overhead
  rw [log2_256]

end Qatlib.Papers.QPreimage16.ConditionalCost
