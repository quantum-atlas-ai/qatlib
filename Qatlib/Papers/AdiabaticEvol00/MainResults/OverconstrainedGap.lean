/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabaticEvol00.MainResults.AdiabaticDefs

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AdiabaticEvol00.MainResults.OverconstrainedGap

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.AdiabaticEvol00.MainResults
open scoped Matrix.Norms.L2Operator ComplexOrder BigOperators

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

theorem overconstrained_time_exponent (p : ℝ) (hp : p = 7 / 10) : 2 - 2 * p = 3 / 5 := by
  subst hp; norm_num

end Qatlib.Papers.AdiabaticEvol00.MainResults.OverconstrainedGap
