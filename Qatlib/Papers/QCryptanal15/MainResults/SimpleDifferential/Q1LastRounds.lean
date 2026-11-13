/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCryptanal15.MainResults.Complexity.GroverBudget
import Qatlib.Papers.QCryptanal15.MainResults.SimpleDifferential.Q2LastRounds

/-!
# Q1 simple-differential last-round costs

`q1SimpleLastRoundsData` retains the classical distinguisher data scale. The last-round cost
formula combines it with a square-root filtering factor and `lastRoundsCheckingCost`, with a
lower bound by data and an explicit amplification-budget identity. The mathematical context is
[KaplanEtAl2015].

## Main statements

* `q1_simple_lastrounds_cost`: The Q1 last-round cost splits into its data expression and the
  square-root filtering factor times checking cost.
* `q1_simple_lastrounds_time_ge_data`: For nonnegative `Cstar`, the Q1 last-round cost is at
  least the data expression.

## References

* [Kaplan et al., 2015][KaplanEtAl2015]
-/

set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace Qatlib.Papers.QCryptanal15.MainResults.SimpleDifferential

open Complexity

/-- The Q1 simple-differential last-round data expression `2^(hS+1)`. -/
noncomputable def q1SimpleLastRoundsData (hS : ℝ) : ℝ := pow2 (hS + 1)

/-- The Q1 cost expression combining classical data with the square-root filtering factor times
the last-round checking cost. -/
noncomputable def q1SimpleLastRoundsCost (hS Δfin n k hout Cstar : ℝ) : ℝ :=
  pow2 (hS + 1) +
    pow2 ((hS + Δfin - n) / 2) * lastRoundsCheckingCost k hout Cstar

/-- The classical last-round cost expression combining data, a full filtering factor, and
classical residual key checking. -/
noncomputable def classicalSimpleLastRoundsCost (hS Δfin n k hout C : ℝ) : ℝ :=
  pow2 (hS + 1) + pow2 (hS + Δfin - n) * (C + pow2 (k - hout))

/-- The Q1 last-round data expression equals the classical simple-differential distinguisher
cost. See [KaplanEtAl2015]. -/
theorem q1_simple_lastrounds_data_eq_classical (hS : ℝ) :
    q1SimpleLastRoundsData hS = classicalSimpleDistinguisherCost hS := rfl

/-- Squaring the Q1 filtering factor yields `2^(hS+Δfin-n)`. See [KaplanEtAl2015]. -/
theorem q1_simple_lastrounds_second_term_sqrt (hS Δfin n : ℝ) :
    pow2 ((hS + Δfin - n) / 2) ^ 2 = pow2 (hS + Δfin - n) :=
  pow2_half_sq (hS + Δfin - n)

/-- The Q1 last-round cost splits into its data expression and the square-root filtering factor
times checking cost. See [KaplanEtAl2015]. -/
theorem q1_simple_lastrounds_cost (hS Δfin n k hout Cstar : ℝ) :
    q1SimpleLastRoundsCost hS Δfin n k hout Cstar =
      q1SimpleLastRoundsData hS +
        pow2 ((hS + Δfin - n) / 2) * lastRoundsCheckingCost k hout Cstar := rfl

/-- For nonnegative `Cstar`, the Q1 last-round cost is at least the data expression. -/
theorem q1_simple_lastrounds_time_ge_data (hS Δfin n k hout Cstar : ℝ)
    (hCstar : 0 ≤ Cstar) :
    q1SimpleLastRoundsData hS ≤ q1SimpleLastRoundsCost hS Δfin n k hout Cstar := by
  unfold q1SimpleLastRoundsCost q1SimpleLastRoundsData lastRoundsCheckingCost
  have hcheck : 0 ≤ Cstar + pow2 ((k - hout) / 2) := by
    have := pow2_nonneg ((k - hout) / 2)
    linarith
  have hiter : 0 ≤ pow2 ((hS + Δfin - n) / 2) := pow2_nonneg _
  have : 0 ≤ pow2 ((hS + Δfin - n) / 2) * (Cstar + pow2 ((k - hout) / 2)) :=
    mul_nonneg hiter hcheck
  linarith

/-- The amplification budget for filtering exponent `hS+Δfin-n` equals `(π/4) *
2^((hS+Δfin-n)/2) + 1`. See [KaplanEtAl2015]. -/
theorem q1_simple_lastrounds_grover_budget (hS Δfin n : ℝ) :
    Real.pi / (4 * Real.sqrt (pow2 (-(hS + Δfin - n)))) + 1 =
      Real.pi / 4 * pow2 ((hS + Δfin - n) / 2) + 1 :=
  amplification_budget_pow2 (hS + Δfin - n)

end Qatlib.Papers.QCryptanal15.MainResults.SimpleDifferential
