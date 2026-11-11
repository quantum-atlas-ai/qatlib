/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabaticEvol00.MainResults.AdiabaticDefs

/-!
# Runtime scaling from an assumed bush gap bound

This module defines the scalar energy scale `bushMaxEigB` and bounds it linearly in the number
of bits. The theorem `bush_time_seven_quarters` converts an assumed gap lower bound proportional
to `n ^ (-(3 / 8))` and a linear energy bound into an upper bound proportional to `n ^ (7 / 4)`
for the runtime ratio. The mathematical context is [FarhiEtAl2000].

## Main statements

* `bushMaxEigB_linear`: For `n ≥ 1`, the scalar bush-driver energy scale `2 * n + 1` is at most
  `3 * n`.
* `bush_time_seven_quarters`: A nonnegative energy bounded by `C * n` and a gap at least `c * n
  ^ (-(3 / 8))` give `E / g ^ 2 ≤ (C / c ^ 2) * n ^ (7 / 4)` for positive `n` and `c`.

## References

* [Farhi et al., 2000][FarhiEtAl2000]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AdiabaticEvol00.MainResults.BushGap

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.AdiabaticEvol00.MainResults
open scoped Matrix.Norms.L2Operator ComplexOrder BigOperators

/-- The scalar `2 * n + 1`, used as the bush-driver energy scale. -/
def bushMaxEigB (n : ℕ) : ℝ := 2 * (n : ℝ) + 1

/-- For `n ≥ 1`, the scalar bush-driver energy scale `2 * n + 1` is at most `3 * n`
[FarhiEtAl2000]. -/
theorem bushMaxEigB_linear (n : ℕ) (hn : 1 ≤ n) : bushMaxEigB n ≤ 3 * (n : ℝ) := by
  unfold bushMaxEigB
  have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  linarith

/-- A nonnegative energy bounded by `C * n` and a gap at least `c * n ^ (-(3 / 8))` give `E / g
^ 2 ≤ (C / c ^ 2) * n ^ (7 / 4)` for positive `n` and `c` [FarhiEtAl2000]. -/
theorem bush_time_seven_quarters {E g c C : ℝ} {n : ℕ}
    (hn : 0 < (n : ℝ)) (hc : 0 < c)
    (hE : E ≤ C * (n : ℝ)) (hgap : c * (n : ℝ) ^ (-(3 / 8 : ℝ)) ≤ g)
    (hE0 : 0 ≤ E) :
    E / g ^ 2 ≤ (C / c ^ 2) * (n : ℝ) ^ (7 / 4 : ℝ) := by
  have h := time_bound_power (a := 1) (q := -(3 / 8 : ℝ)) hn hc
    (by simpa using hE) hgap hE0
  have hexp : (1 : ℝ) - 2 * (-(3 / 8 : ℝ)) = 7 / 4 := by norm_num
  rw [hexp] at h
  exact h

/-- Substituting `p = 3 / 8` in `1 + 2 * p` gives `7 / 4` [FarhiEtAl2000]. -/
theorem bush_time_exponent (p : ℝ) (hp : p = 3 / 8) : 1 + 2 * p = 7 / 4 := by
  subst hp; norm_num

end Qatlib.Papers.AdiabaticEvol00.MainResults.BushGap
