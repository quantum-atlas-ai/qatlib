/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabaticEvol00.MainResults.AdiabaticDefs

/-!
# Runtime scaling from an assumed overconstrained gap bound

This module applies the general power-law runtime estimate to a quadratic energy bound and a gap
lower bound proportional to `n ^ (7 / 10)`. The theorem `overconstrained_time` yields an upper
bound proportional to `n ^ (3 / 5)` for `E / g ^ 2`, conditional on those input bounds. The
mathematical context is [FarhiEtAl2000].

## Main statements

* `overconstrained_time`: For positive `n` and `c`, a nonnegative energy at most `C * n ^ 2` and
  a gap at least `c * n ^ (7 / 10)` imply `E / g ^ 2 ≤ (C / c ^ 2) * n ^ (3 / 5)`.
* `overconstrained_time_exponent`: Substituting `p = 7 / 10` in `2 - 2 * p` gives `3 / 5`.

## References

* [Farhi et al., 2000][FarhiEtAl2000]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AdiabaticEvol00.MainResults.OverconstrainedGap

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.AdiabaticEvol00.MainResults
open scoped Matrix.Norms.L2Operator ComplexOrder BigOperators

/-- For positive `n` and `c`, a nonnegative energy at most `C * n ^ 2` and a gap at least `c * n
^ (7 / 10)` imply `E / g ^ 2 ≤ (C / c ^ 2) * n ^ (3 / 5)` [FarhiEtAl2000]. -/
theorem overconstrained_time {E g c C : ℝ} {n : ℕ}
    (hn : 0 < (n : ℝ)) (hc : 0 < c)
    (hE : E ≤ C * (n : ℝ) ^ 2) (hgap : c * (n : ℝ) ^ (7 / 10 : ℝ) ≤ g)
    (hE0 : 0 ≤ E) :
    E / g ^ 2 ≤ (C / c ^ 2) * (n : ℝ) ^ (3 / 5 : ℝ) := by
  have h := time_bound_power (a := 2) (q := (7 / 10 : ℝ)) hn hc
    (by simpa using hE) hgap hE0
  have hexp : (2 : ℝ) - 2 * (7 / 10 : ℝ) = 3 / 5 := by norm_num
  rw [hexp] at h
  exact h

/-- Substituting `p = 7 / 10` in `2 - 2 * p` gives `3 / 5` [FarhiEtAl2000]. -/
theorem overconstrained_time_exponent (p : ℝ) (hp : p = 7 / 10) : 2 - 2 * p = 3 / 5 := by
  subst hp; norm_num

end Qatlib.Papers.AdiabaticEvol00.MainResults.OverconstrainedGap
