/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MolGeometry09.MainResults.HouseholderIteration

/-!
# Householder derivative-query ledger as a finite power sum

The order-`l` Householder ledger is the sum of the derivative costs `2^m`
for orders `m + 1`. The underlying circuit and derivative ledger are in Qatlib.
-/

set_option autoImplicit false

namespace Qatlib.Papers.MolGeometry09.MainResults.HouseholderIteration

open Qatlib.Papers.MolGeometry09.MainResults.HouseholderIteration
open Qatlib.Papers.MolGeometry09.MainResults.DerivativeQueryLedger
open scoped BigOperators

/-- The ledger sum is `Σ_{m=0}^{l} 2^m`: the order-`m+1` derivative costs `2^m`
(arXiv:0908.1921v1, p. 5). -/
theorem householder_ledger_eq_pow_sum (d M l : ℕ) (hM : 0 < M) :
    householderIterationQueries d M l =
      ∑ m ∈ Finset.range (l + 1), 2 ^ m := by
  unfold householderIterationQueries
  apply Finset.sum_congr rfl
  intro m _
  rw [nth_derivative_query_count d M (m + 1) hM (Nat.succ_le_succ (Nat.zero_le m))]
  simp

end Qatlib.Papers.MolGeometry09.MainResults.HouseholderIteration
