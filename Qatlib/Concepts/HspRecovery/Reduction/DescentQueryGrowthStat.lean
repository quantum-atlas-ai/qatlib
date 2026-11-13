/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.PowerTwoSlopeProgram

/-!
# Statement of descent query growth

`SourceDescentQueryGrowth` expresses a subexponential bound for `sourcePowerTwoQueryBudget`:
positive constants bound it by an exponential in the square root of the input parameter. This is
the query growth form associated with the dihedral sieve of [Kuperberg2005].

## Main statements

* `SourceDescentQueryGrowth`: states the bound with explicit existential quantifiers over
  positive constants.

## References

* [Kuperberg, 2005][Kuperberg2005]
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
namespace Qatlib.Concepts.HspRecovery.ReductionCore

/-- The proposition that positive real constants `C` and `c` bound `sourcePowerTwoQueryBudget n`
by `C * 2^(c * sqrt n)` for every natural number `n`. -/
def SourceDescentQueryGrowth : Prop := by
  classical
  exact
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ n : ℕ,
    (sourcePowerTwoQueryBudget n : ℝ) ≤ C * (2 : ℝ) ^ (c * Real.sqrt n)

end Qatlib.Concepts.HspRecovery.ReductionCore
