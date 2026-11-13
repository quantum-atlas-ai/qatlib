/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLinearODE17.EndToEnd.LinearDifferentialConstruction

/-!
# Source-access and dyadic ledgers for the ODE solver

This module defines `SourceAccessLedger` and its explicit construction, together with
repetition-based query and gate ledgers. It also defines the dyadic truncation magnitude and
error budget used to represent real inputs at finite precision in the ODE construction
associated with [BerryEtAl2017ODE].

## Main statements

* `sourceAccessLedger`: The explicit source-access resource record.
* `amplifiedQueryCount`: The repeated query count.
* `dyadicMagnitude`: Magnitude truncation on a dyadic grid.

## References

* [Berry et al., 2017][BerryEtAl2017ODE]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QLinearODE17.EndToEnd

open Qatlib.Papers.QLinearODE17.EndToEnd

/-- A record of controlled preparations, oracle calls, classical bits, and peak workspace. -/
structure SourceAccessLedger where

  controlledPreparations : ℕ

  oracleCalls : ℕ

  classicalBits : ℕ

  peakWorkspace : ℕ
  deriving DecidableEq, Repr

/-- The source-access ledger with (m + 1)ρ controlled preparations, m + 1 oracle calls, and the
supplied classical-bit and workspace counts. -/
def sourceAccessLedger (m ρ : ℕ) (bits workspace : ℕ) : SourceAccessLedger where
  controlledPreparations := (m + 1) * ρ
  oracleCalls := m + 1
  classicalBits := bits
  peakWorkspace := workspace

/-- The query ledger for `r` repetitions of a procedure with `nq` queries, defined as `r * nq`. -/
def amplifiedQueryCount (r nq : ℕ) : ℕ := r * nq

/-- The gate ledger for `r` repetitions of a procedure with `g` gates, defined as `r * g`. -/
def amplifiedGateCount (r g : ℕ) : ℕ := r * g

/-- The magnitude |x| truncated downward to the grid with spacing 2^(-bits). -/
noncomputable def dyadicMagnitude (x : ℝ) (bits : ℕ) : ℝ :=
  (Nat.floor (|x| * 2 ^ bits) : ℝ) / 2 ^ bits

/-- The dyadic error budget 2^(-bits). -/
noncomputable def finiteDigitErrorBudget (bits : ℕ) : ℝ := 1 / 2 ^ bits

end Qatlib.Papers.QLinearODE17.EndToEnd
