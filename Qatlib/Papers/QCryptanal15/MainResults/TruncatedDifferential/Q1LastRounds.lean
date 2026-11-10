/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCryptanal15.MainResults.Complexity.GroverBudget
import Qatlib.Papers.QCryptanal15.MainResults.TruncatedDifferential.Q2Distinguisher
import Qatlib.Papers.QCryptanal15.MainResults.SimpleDifferential.Q1LastRounds
set_option warningAsError false

set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace Qatlib.Papers.QCryptanal15.MainResults.TruncatedDifferential

open Complexity
open Qatlib.Papers.QCryptanal15.MainResults.SimpleDifferential

noncomputable def q1TruncatedData (hT Δin : ℝ) : ℝ :=
  max (pow2 ((hT + 1) / 2)) (pow2 (hT - Δin + 1))

noncomputable def classicalTruncatedData (hT Δin : ℝ) : ℝ :=
  max (pow2 ((hT + 1) / 2)) (pow2 (hT - Δin + 1))

noncomputable def q1TruncatedMarkedFraction (hT Δfin n : ℝ) : ℝ :=
  pow2 (-(hT + Δfin - n))

noncomputable def q1TruncatedLastRoundsCost (hT Δin Δfin n k hout Cstar : ℝ) : ℝ :=
  q1TruncatedData hT Δin +
    pow2 ((hT + Δfin - n) / 2) * lastRoundsCheckingCost k hout Cstar

theorem q1_truncated_data_eq_classical (hT Δin : ℝ) :
    q1TruncatedData hT Δin = classicalTruncatedData hT Δin := rfl

theorem q1_truncated_data (hT Δin : ℝ) :
    q1TruncatedData hT Δin =
      max (pow2 ((hT + 1) / 2)) (pow2 (hT - Δin + 1)) := rfl

theorem q1_truncated_marked_fraction (hT Δfin n : ℝ) :
    q1TruncatedMarkedFraction hT Δfin n = pow2 (-hT - Δfin + n) := by
  unfold q1TruncatedMarkedFraction
  congr 1
  ring

theorem q1_truncated_filter_iterations (hT Δfin n : ℝ) :
    (Real.sqrt (q1TruncatedMarkedFraction hT Δfin n))⁻¹ =
      pow2 ((hT + Δfin - n) / 2) := by
  unfold q1TruncatedMarkedFraction
  exact inv_sqrt_pow2_neg (hT + Δfin - n)

theorem q1_truncated_lastrounds_cost (hT Δin Δfin n k hout Cstar : ℝ) :
    q1TruncatedLastRoundsCost hT Δin Δfin n k hout Cstar =
      q1TruncatedData hT Δin +
        (Real.sqrt (q1TruncatedMarkedFraction hT Δfin n))⁻¹ *
          lastRoundsCheckingCost k hout Cstar := by
  unfold q1TruncatedLastRoundsCost
  rw [q1_truncated_filter_iterations]

theorem q1_truncated_time_ge_data (hT Δin Δfin n k hout Cstar : ℝ)
    (hCstar : 0 ≤ Cstar) :
    q1TruncatedData hT Δin ≤
      q1TruncatedLastRoundsCost hT Δin Δfin n k hout Cstar := by
  unfold q1TruncatedLastRoundsCost lastRoundsCheckingCost
  have hcheck : 0 ≤ Cstar + pow2 ((k - hout) / 2) := by
    have := pow2_nonneg ((k - hout) / 2)
    linarith
  have hiter : 0 ≤ pow2 ((hT + Δfin - n) / 2) := pow2_nonneg _
  have : 0 ≤ pow2 ((hT + Δfin - n) / 2) * (Cstar + pow2 ((k - hout) / 2)) :=
    mul_nonneg hiter hcheck
  linarith

theorem q1_truncated_grover_budget (hT Δfin n : ℝ) :
    Real.pi / (4 * Real.sqrt (q1TruncatedMarkedFraction hT Δfin n)) + 1 =
      Real.pi / 4 * pow2 ((hT + Δfin - n) / 2) + 1 := by
  unfold q1TruncatedMarkedFraction
  exact amplification_budget_pow2 (hT + Δfin - n)

end Qatlib.Papers.QCryptanal15.MainResults.TruncatedDifferential
