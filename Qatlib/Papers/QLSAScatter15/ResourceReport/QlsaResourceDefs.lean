/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QLSAScatter15.ResourceReport

def OrderOfMagnitude (k x : ℕ) : Prop := 10 ^ k ≤ x ∧ x < 10 ^ (k + 1)

structure QlsaResourceLedger where
  circuitWidthExclOracles : ℕ
  circuitDepthExclOracles : ℕ
  gateCountExclOracles : ℕ
  circuitWidthInclOracles : ℕ
  circuitDepthInclOracles : ℕ
  gateCountInclOracles : ℕ
  deriving Repr, DecidableEq

def tableII : QlsaResourceLedger where
  circuitWidthExclOracles := 341
  circuitDepthExclOracles := 33 * 10 ^ 24
  gateCountExclOracles := 334 * 10 ^ 23
  circuitWidthInclOracles := 3 * 10 ^ 8
  circuitDepthInclOracles := 18 * 10 ^ 28
  gateCountInclOracles := 237 * 10 ^ 27

end Qatlib.Papers.QLSAScatter15.ResourceReport
