/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.Achievability.TrigApproximation

/-!
# Taylor Truncation Contract

`Theorem1TaylorTruncation` specifies a natural cutoff controlling the exponential Taylor error
for any real simulation parameter `τ` and any positive tolerance `ε`. This contract supplies the
scalar approximation budget for the encoded Hamiltonian simulation construction in the setting
of [LowChuang2019].

Its degree bound uses `log (8 / min ε 1)`, so tolerances above one cannot make the allowed
natural degree negative. The remaining requirements are `2 * |τ| ≤ n + 1` and
`exponentialTaylorError τ n ≤ ε`.

## Main statements

- `Theorem1TaylorTruncation` defines the corrected scalar cutoff and degree guarantee.

## References

- [Low and Chuang, 2019][LowChuang2019].
-/

open Qatlib.Concepts.QspSimulation.Achievability

namespace Qatlib.Concepts.SignalPrimitive.MainResults

/-- The Taylor cutoff contract requiring `2 * |τ| ≤ n + 1`, error at most `ε`, and `n ≤ 4 * |τ|
+ 8 * log (8 / min ε 1) + 8` for every real `τ` and positive `ε`. -/
def Theorem1TaylorTruncation : Prop :=
  ∀ (τ ε : ℝ), 0 < ε → ∃ n : ℕ,
    2 * |τ| ≤ (n : ℝ) + 1 ∧
    Qatlib.Concepts.QspSimulation.Achievability.exponentialTaylorError τ n ≤ ε ∧
    (n : ℝ) ≤ 4 * |τ| + 8 * Real.log (8 / min ε 1) + 8

end Qatlib.Concepts.SignalPrimitive.MainResults
