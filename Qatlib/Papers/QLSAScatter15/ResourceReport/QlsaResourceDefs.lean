/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic

/-!
# QLSA resource ledger definitions

`QlsaResourceLedger` stores width, depth, and gate counts with and without oracles. The value
`tableII` records the six estimates, and `OrderOfMagnitude` specifies the decimal interval used
in their verification. See [SchererEtAl2017] for the paper context.

## Main statements

* `OrderOfMagnitude`: The decimal interval condition `10^k ≤ x < 10^(k + 1)`.
* `QlsaResourceLedger`: A record of circuit width, depth, and gate count, each measured both
  excluding and including oracles.
* `tableII`: The resource ledger recording the six Table II estimates of [SchererEtAl2017].

## References

* [Scherer et al., 2017][SchererEtAl2017]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QLSAScatter15.ResourceReport

/-- The decimal interval condition `10^k ≤ x < 10^(k + 1)`. -/
def OrderOfMagnitude (k x : ℕ) : Prop := 10 ^ k ≤ x ∧ x < 10 ^ (k + 1)

/-- A record of circuit width, depth, and gate count, each measured both excluding and including
oracles. -/
structure QlsaResourceLedger where
  circuitWidthExclOracles : ℕ
  circuitDepthExclOracles : ℕ
  gateCountExclOracles : ℕ
  circuitWidthInclOracles : ℕ
  circuitDepthInclOracles : ℕ
  gateCountInclOracles : ℕ
  deriving Repr, DecidableEq

/-- The resource ledger recording the six Table II estimates of [SchererEtAl2017]. -/
def tableII : QlsaResourceLedger where
  circuitWidthExclOracles := 341
  circuitDepthExclOracles := 33 * 10 ^ 24
  gateCountExclOracles := 334 * 10 ^ 23
  circuitWidthInclOracles := 3 * 10 ^ 8
  circuitDepthInclOracles := 18 * 10 ^ 28
  gateCountInclOracles := 237 * 10 ^ 27

end Qatlib.Papers.QLSAScatter15.ResourceReport
