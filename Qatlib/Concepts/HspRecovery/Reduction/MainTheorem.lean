/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.DescentQueryGrowthDihe
import Qatlib.Concepts.HspRecovery.SieveAlgorithm.DihedralSieveAlgorithmDihe

/-!
# Power-of-two dihedral recovery statements

This module exposes the query growth and `DihedralSieveAlgorithm` results for the power-of-two
dihedral construction. `theorem11_powerTwo_instance` packages the two guarantees in one
conjunction.

These are the formalized power-of-two recovery statements associated with the dihedral sieve of
[Kuperberg2005].

## Main statements

* `theorem11_query_growth`: bounds the query budget by an exponential in the square root.
* `theorem11_powerTwo_parity_recovery`: establishes `DihedralSieveAlgorithm`.
* `theorem11_powerTwo_instance`: combines the two results.

## References

* [Kuperberg, 2005][Kuperberg2005]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.HspRecovery.ReductionCore.MainTheorem

open Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib.Concepts.HspRecovery.SieveAlgorithm

/-- Positive real constants bound the power-of-two query budget by `C * 2^(c * sqrt n)` for all
natural `n`. This is the query growth statement associated with [Kuperberg, Theorem
1.1][Kuperberg2005]. -/
theorem theorem11_query_growth :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ n : ℕ,
      (sourcePowerTwoQueryBudget n : ℝ) ≤ C * (2 : ℝ) ^ (c * Real.sqrt (n : ℝ)) :=
  sourceDescentQueryGrowth

/-- The power-of-two parity recovery construction satisfies `DihedralSieveAlgorithm`, in the
setting of [Kuperberg, Theorem 1.1][Kuperberg2005]. -/
theorem theorem11_powerTwo_parity_recovery :
    DihedralSieveAlgorithm :=
  dihedralSieveAlgorithm

/-- The power-of-two construction satisfies both the subexponential query growth bound and
`DihedralSieveAlgorithm`. See [Kuperberg2005]. -/
theorem theorem11_powerTwo_instance :
    (∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ n : ℕ,
      (sourcePowerTwoQueryBudget n : ℝ) ≤ C * (2 : ℝ) ^ (c * Real.sqrt (n : ℝ))) ∧
    DihedralSieveAlgorithm :=
  ⟨theorem11_query_growth, theorem11_powerTwo_parity_recovery⟩

end Qatlib.Concepts.HspRecovery.ReductionCore.MainTheorem
