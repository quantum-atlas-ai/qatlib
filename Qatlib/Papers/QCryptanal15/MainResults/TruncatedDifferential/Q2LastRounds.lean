/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCryptanal15.MainResults.Complexity.GroverBudget
import Qatlib.Papers.QCryptanal15.MainResults.TruncatedDifferential.Q2Distinguisher
import Qatlib.Papers.QCryptanal15.MainResults.SimpleDifferential.Q2LastRounds
set_option warningAsError false

set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace Qatlib.Papers.QCryptanal15.MainResults.TruncatedDifferential

open Complexity
open Qatlib.Papers.QCryptanal15.MainResults.SimpleDifferential

noncomputable def q2TruncatedLastRoundsFirstTerm (hT Δin Δfin n : ℝ) : ℝ :=
  pow2 ((hT + 1) / 2) * max (pow2 (-(Δin / 3))) (pow2 (-((n + 1 - Δfin) / 6)))

noncomputable def q2TruncatedLastRoundsSecondFactor (hT Δin Δfin n : ℝ) : ℝ :=
  max (pow2 ((hT + Δfin - n) / 2)) (pow2 ((hT + 1) / 2 - Δin))

noncomputable def q2TruncatedLastRoundsCost (hT Δin Δfin n k hout Cstar : ℝ) : ℝ :=
  q2TruncatedLastRoundsFirstTerm hT Δin Δfin n +
    q2TruncatedLastRoundsSecondFactor hT Δin Δfin n *
      lastRoundsCheckingCost k hout Cstar

noncomputable def q2TruncatedBranchAmbainis (hT Δin k hout Cstar : ℝ) : ℝ :=
  pow2 ((hT + 1) / 2 - Δin / 3) +
    pow2 ((hT + 1) / 2 - Δin) * lastRoundsCheckingCost k hout Cstar

noncomputable def q2TruncatedBranchGrover (hT Δfin n k hout Cstar : ℝ) : ℝ :=
  pow2 ((hT + 1) / 2 - (n + 1 - Δfin) / 6) +
    pow2 ((hT + Δfin - n) / 2) * lastRoundsCheckingCost k hout Cstar

noncomputable def q2TruncatedBranchSingle (hT Δfin n k hout Cstar : ℝ) : ℝ :=
  pow2 (hT / 2 - (n - Δfin) / 6) +
    pow2 ((hT + Δfin - n) / 2) * lastRoundsCheckingCost k hout Cstar

theorem q2_truncated_branch_ambainis_le (hT Δin Δfin n k hout Cstar : ℝ)
    (hCstar : 0 ≤ Cstar) :
    q2TruncatedBranchAmbainis hT Δin k hout Cstar ≤
      q2TruncatedLastRoundsCost hT Δin Δfin n k hout Cstar := by
  unfold q2TruncatedBranchAmbainis q2TruncatedLastRoundsCost
    q2TruncatedLastRoundsFirstTerm q2TruncatedLastRoundsSecondFactor
    lastRoundsCheckingCost
  have hcheck : 0 ≤ Cstar + pow2 ((k - hout) / 2) := by
    have := pow2_nonneg ((k - hout) / 2)
    linarith
  have hfirst : pow2 ((hT + 1) / 2 - Δin / 3) ≤
      pow2 ((hT + 1) / 2) * max (pow2 (-(Δin / 3))) (pow2 (-((n + 1 - Δfin) / 6))) := by
    have hsplit : pow2 ((hT + 1) / 2 - Δin / 3) =
        pow2 ((hT + 1) / 2) * pow2 (-(Δin / 3)) := by
      rw [sub_eq_add_neg, pow2_add]
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) (pow2_nonneg _)
  have hsecond : pow2 ((hT + 1) / 2 - Δin) * (Cstar + pow2 ((k - hout) / 2)) ≤
      max (pow2 ((hT + Δfin - n) / 2)) (pow2 ((hT + 1) / 2 - Δin)) *
        (Cstar + pow2 ((k - hout) / 2)) :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hcheck
  linarith

theorem q2_truncated_branch_grover_le (hT Δin Δfin n k hout Cstar : ℝ)
    (hCstar : 0 ≤ Cstar) :
    q2TruncatedBranchGrover hT Δfin n k hout Cstar ≤
      q2TruncatedLastRoundsCost hT Δin Δfin n k hout Cstar := by
  unfold q2TruncatedBranchGrover q2TruncatedLastRoundsCost
    q2TruncatedLastRoundsFirstTerm q2TruncatedLastRoundsSecondFactor
    lastRoundsCheckingCost
  have hcheck : 0 ≤ Cstar + pow2 ((k - hout) / 2) := by
    have := pow2_nonneg ((k - hout) / 2)
    linarith
  have hfirst : pow2 ((hT + 1) / 2 - (n + 1 - Δfin) / 6) ≤
      pow2 ((hT + 1) / 2) * max (pow2 (-(Δin / 3))) (pow2 (-((n + 1 - Δfin) / 6))) := by
    have hsplit : pow2 ((hT + 1) / 2 - (n + 1 - Δfin) / 6) =
        pow2 ((hT + 1) / 2) * pow2 (-((n + 1 - Δfin) / 6)) := by
      rw [sub_eq_add_neg, pow2_add]
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) (pow2_nonneg _)
  have hsecond : pow2 ((hT + Δfin - n) / 2) * (Cstar + pow2 ((k - hout) / 2)) ≤
      max (pow2 ((hT + Δfin - n) / 2)) (pow2 ((hT + 1) / 2 - Δin)) *
        (Cstar + pow2 ((k - hout) / 2)) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hcheck
  linarith

theorem q2_truncated_branch_single_le_grover (hT Δfin n k hout Cstar : ℝ) :
    q2TruncatedBranchSingle hT Δfin n k hout Cstar ≤
      q2TruncatedBranchGrover hT Δfin n k hout Cstar := by
  unfold q2TruncatedBranchSingle q2TruncatedBranchGrover
  have hexp : hT / 2 - (n - Δfin) / 6 ≤ (hT + 1) / 2 - (n + 1 - Δfin) / 6 := by
    linarith
  have hfirst := pow2_le_pow2 hexp
  exact add_le_add_left hfirst _

theorem q2_truncated_lastrounds_bounds_branches (hT Δin Δfin n k hout Cstar : ℝ)
    (hCstar : 0 ≤ Cstar) :
    q2TruncatedBranchSingle hT Δfin n k hout Cstar ≤
        q2TruncatedLastRoundsCost hT Δin Δfin n k hout Cstar ∧
      q2TruncatedBranchGrover hT Δfin n k hout Cstar ≤
        q2TruncatedLastRoundsCost hT Δin Δfin n k hout Cstar ∧
      q2TruncatedBranchAmbainis hT Δin k hout Cstar ≤
        q2TruncatedLastRoundsCost hT Δin Δfin n k hout Cstar := by
  refine ⟨?_, q2_truncated_branch_grover_le hT Δin Δfin n k hout Cstar hCstar,
    q2_truncated_branch_ambainis_le hT Δin Δfin n k hout Cstar hCstar⟩
  exact le_trans (q2_truncated_branch_single_le_grover hT Δfin n k hout Cstar)
    (q2_truncated_branch_grover_le hT Δin Δfin n k hout Cstar hCstar)

theorem q2_truncated_grover_budget (hT Δfin n : ℝ) :
    Real.pi / (4 * Real.sqrt (pow2 (-(hT + Δfin - n)))) + 1 =
      Real.pi / 4 * pow2 ((hT + Δfin - n) / 2) + 1 :=
  amplification_budget_pow2 (hT + Δfin - n)

end Qatlib.Papers.QCryptanal15.MainResults.TruncatedDifferential
