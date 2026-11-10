/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Log
import Qatlib.Papers.TensorHyper20.MainResults.Definitions
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.TensorHyper20.MainResults.LogicalQubits

open Qatlib.Papers.TensorHyper20.MainResults

theorem eq46_logical_qubits (N M I i d ℵ m ks1 : ℕ) (hI : 1 ≤ I) :
    logicalQubitsParts N M I i d ℵ m ks1
      = logicalQubitsFormula N M I i d ℵ m ks1 := by
  unfold logicalQubitsParts logicalQubitsFormula
  have hL : 1 ≤ Nat.clog 2 (I + 1) := Nat.clog_pos (by norm_num) (by omega)
  omega

end Qatlib.Papers.TensorHyper20.MainResults.LogicalQubits
