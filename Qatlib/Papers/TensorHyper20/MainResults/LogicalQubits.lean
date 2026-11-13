/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Log
import Qatlib.Papers.TensorHyper20.MainResults.Definitions

/-!
# Logical-qubit accounting identity

Relates the componentwise logical-qubit count `logicalQubitsParts` to the compact formula
`logicalQubitsFormula` used for tensor hypercontraction in [LeeEtAl2021]. The condition `1 ≤ I`
ensures that the natural-number subtraction in the phase-estimation register contribution
simplifies correctly.

## Main statements

* `eq46_logical_qubits`: identifies the componentwise and compact counts for `I ≥ 1`.

## References

* [Lee et al., 2021][LeeEtAl2021]
-/

set_option autoImplicit false

namespace Qatlib.Papers.TensorHyper20.MainResults.LogicalQubits

open Qatlib.Papers.TensorHyper20.MainResults

/-- For `I ≥ 1`, the sum of logical-qubit register contributions equals the compact
logical-qubit formula. See [LeeEtAl2021]. -/
theorem eq46_logical_qubits (N M I i d ℵ m ks1 : ℕ) (hI : 1 ≤ I) :
    logicalQubitsParts N M I i d ℵ m ks1
      = logicalQubitsFormula N M I i d ℵ m ks1 := by
  unfold logicalQubitsParts logicalQubitsFormula
  have hL : 1 ≤ Nat.clog 2 (I + 1) := Nat.clog_pos (by norm_num) (by omega)
  omega

end Qatlib.Papers.TensorHyper20.MainResults.LogicalQubits
