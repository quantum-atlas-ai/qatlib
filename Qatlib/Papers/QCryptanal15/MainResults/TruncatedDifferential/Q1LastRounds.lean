/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCryptanal15.MainResults.Complexity.GroverBudget
import Qatlib.Papers.QCryptanal15.MainResults.TruncatedDifferential.Q2Distinguisher
import Qatlib.Papers.QCryptanal15.MainResults.SimpleDifferential.Q1LastRounds

/-!
# Q1 truncated-differential last-round costs

`q1TruncatedData` is the maximum of two classical data scales. The Q1 cost expression adds
filtered last-round checking; the module rewrites the marked fraction and filtering factor and
proves the total dominates the data cost. The mathematical context is [KaplanEtAl2015].

## Main statements

* `q1_truncated_data_eq_classical`: The Q1 and classical truncated-differential data expressions
  are equal.
* `q1_truncated_lastrounds_cost`: The Q1 last-round expression is its data cost plus the
  reciprocal square root of the filtering fraction times checking cost.

## References

* [Kaplan et al., 2015][KaplanEtAl2015]
-/

set_option warningAsError false

set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace Qatlib.Papers.QCryptanal15.MainResults.TruncatedDifferential

open Complexity
open Qatlib.Papers.QCryptanal15.MainResults.SimpleDifferential

/-- The Q1 truncated-differential data expression `max (2^((hT+1)/2)) (2^(hT-Δin+1))`. -/
noncomputable def q1TruncatedData (hT Δin : ℝ) : ℝ :=
  max (pow2 ((hT + 1) / 2)) (pow2 (hT - Δin + 1))

/-- The classical truncated-differential data expression `max (2^((hT+1)/2)) (2^(hT-Δin+1))`. -/
noncomputable def classicalTruncatedData (hT Δin : ℝ) : ℝ :=
  max (pow2 ((hT + 1) / 2)) (pow2 (hT - Δin + 1))

/-- The Q1 truncated-differential filtering fraction expression `2^(-(hT+Δfin-n))`. -/
noncomputable def q1TruncatedMarkedFraction (hT Δfin n : ℝ) : ℝ :=
  pow2 (-(hT + Δfin - n))

/-- The Q1 truncated-differential last-round cost expression combining data with filtered
checking cost. -/
noncomputable def q1TruncatedLastRoundsCost (hT Δin Δfin n k hout Cstar : ℝ) : ℝ :=
  q1TruncatedData hT Δin +
    pow2 ((hT + Δfin - n) / 2) * lastRoundsCheckingCost k hout Cstar

/-- The Q1 and classical truncated-differential data expressions are equal. See
[KaplanEtAl2015]. -/
theorem q1_truncated_data_eq_classical (hT Δin : ℝ) :
    q1TruncatedData hT Δin = classicalTruncatedData hT Δin := rfl

/-- The Q1 data expression is the maximum of the stated square-root and structure-limited
exponential scales. See [KaplanEtAl2015]. -/
theorem q1_truncated_data (hT Δin : ℝ) :
    q1TruncatedData hT Δin =
      max (pow2 ((hT + 1) / 2)) (pow2 (hT - Δin + 1)) := rfl

/-- The filtering fraction expression can be written as `2^(-hT-Δfin+n)`. -/
theorem q1_truncated_marked_fraction (hT Δfin n : ℝ) :
    q1TruncatedMarkedFraction hT Δfin n = pow2 (-hT - Δfin + n) := by
  unfold q1TruncatedMarkedFraction
  congr 1
  ring

/-- The reciprocal square root of the Q1 truncated filtering fraction is `2^((hT+Δfin-n)/2)`.
See [KaplanEtAl2015]. -/
theorem q1_truncated_filter_iterations (hT Δfin n : ℝ) :
    (Real.sqrt (q1TruncatedMarkedFraction hT Δfin n))⁻¹ =
      pow2 ((hT + Δfin - n) / 2) := by
  unfold q1TruncatedMarkedFraction
  exact inv_sqrt_pow2_neg (hT + Δfin - n)

/-- The Q1 last-round expression is its data cost plus the reciprocal square root of the
filtering fraction times checking cost. See [KaplanEtAl2015]. -/
theorem q1_truncated_lastrounds_cost (hT Δin Δfin n k hout Cstar : ℝ) :
    q1TruncatedLastRoundsCost hT Δin Δfin n k hout Cstar =
      q1TruncatedData hT Δin +
        (Real.sqrt (q1TruncatedMarkedFraction hT Δfin n))⁻¹ *
          lastRoundsCheckingCost k hout Cstar := by
  unfold q1TruncatedLastRoundsCost
  rw [q1_truncated_filter_iterations]

/-- For nonnegative `Cstar`, the Q1 truncated last-round cost is at least its data expression. -/
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

/-- The Q1 truncated filtering budget equals `(π/4) * 2^((hT+Δfin-n)/2) + 1`. See
[KaplanEtAl2015]. -/
theorem q1_truncated_grover_budget (hT Δfin n : ℝ) :
    Real.pi / (4 * Real.sqrt (q1TruncatedMarkedFraction hT Δfin n)) + 1 =
      Real.pi / 4 * pow2 ((hT + Δfin - n) / 2) + 1 := by
  unfold q1TruncatedMarkedFraction
  exact amplification_budget_pow2 (hT + Δfin - n)

end Qatlib.Papers.QCryptanal15.MainResults.TruncatedDifferential
