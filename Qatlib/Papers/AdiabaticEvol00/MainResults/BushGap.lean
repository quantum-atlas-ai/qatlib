/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabaticEvol00.MainResults.AdiabaticDefs

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AdiabaticEvol00.MainResults.BushGap

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.AdiabaticEvol00.MainResults
open scoped Matrix.Norms.L2Operator ComplexOrder BigOperators

def bushMaxEigB (n : ℕ) : ℝ := 2 * (n : ℝ) + 1

theorem bushMaxEigB_linear (n : ℕ) (hn : 1 ≤ n) : bushMaxEigB n ≤ 3 * (n : ℝ) := by
  unfold bushMaxEigB
  have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  linarith

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

theorem bush_time_exponent (p : ℝ) (hp : p = 3 / 8) : 1 + 2 * p = 7 / 4 := by
  subst hp; norm_num

end Qatlib.Papers.AdiabaticEvol00.MainResults.BushGap
