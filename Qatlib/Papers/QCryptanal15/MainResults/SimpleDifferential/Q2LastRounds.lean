/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCryptanal15.MainResults.Complexity.GroverBudget
import Qatlib.Papers.QCryptanal15.MainResults.SimpleDifferential.Q2Distinguisher

/-!
# Q2 simple-differential last-round costs

`q2SimpleLastRoundsMarkedFraction` and `lastRoundsCheckingCost` describe the filtering and
residual key-search expressions. The Q2 total cost splits into distinguisher data and
inverse-square-root filtering times checking cost. The mathematical context is [KaplanEtAl2015].

## Main statements

* `q2_simple_lastrounds_cost`: The Q2 last-round cost is the data expression plus the reciprocal
  square root of the marked fraction times checking cost.
* `q2_simple_lastrounds_grover_budget`: The amplification budget associated with the last-round
  marked fraction equals `(π/4) * 2^((hS+Δfin-n)/2) + 1`.

## References

* [Kaplan et al., 2015][KaplanEtAl2015]
-/

set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace Qatlib.Papers.QCryptanal15.MainResults.SimpleDifferential

open Complexity

/-- The Q2 last-round marked-fraction expression `2^(-(hS+Δfin-n))`. -/
noncomputable def q2SimpleLastRoundsMarkedFraction (hS Δfin n : ℝ) : ℝ :=
  pow2 (-(hS + Δfin - n))

/-- The checking-cost expression `Cstar + 2^((k-hout)/2)`. -/
noncomputable def lastRoundsCheckingCost (k hout Cstar : ℝ) : ℝ :=
  Cstar + pow2 ((k - hout) / 2)

/-- The Q2 simple-differential last-round data expression `2^(hS/2+1)`. -/
noncomputable def q2SimpleLastRoundsData (hS : ℝ) : ℝ := pow2 (hS / 2 + 1)

/-- The Q2 last-round cost expression combining data with a square-root filtering factor times
the checking cost. -/
noncomputable def q2SimpleLastRoundsCost (hS Δfin n k hout Cstar : ℝ) : ℝ :=
  pow2 (hS / 2 + 1) +
    pow2 ((hS + Δfin - n) / 2) * lastRoundsCheckingCost k hout Cstar

/-- The last-round marked fraction can be written as `2^(-hS-Δfin+n)`. See [KaplanEtAl2015]. -/
theorem q2_simple_lastrounds_marked_fraction (hS Δfin n : ℝ) :
    q2SimpleLastRoundsMarkedFraction hS Δfin n = pow2 (-hS - Δfin + n) := by
  unfold q2SimpleLastRoundsMarkedFraction
  congr 1
  ring

/-- The reciprocal square root of the last-round marked fraction is `2^((hS+Δfin-n)/2)`. See
[KaplanEtAl2015]. -/
theorem q2_simple_lastrounds_filter_iterations (hS Δfin n : ℝ) :
    (Real.sqrt (q2SimpleLastRoundsMarkedFraction hS Δfin n))⁻¹ =
      pow2 ((hS + Δfin - n) / 2) := by
  unfold q2SimpleLastRoundsMarkedFraction
  exact inv_sqrt_pow2_neg (hS + Δfin - n)

/-- The Q2 last-round cost is the data expression plus the reciprocal square root of the marked
fraction times checking cost. See [KaplanEtAl2015]. -/
theorem q2_simple_lastrounds_cost (hS Δfin n k hout Cstar : ℝ) :
    q2SimpleLastRoundsCost hS Δfin n k hout Cstar =
      q2SimpleLastRoundsData hS +
        (Real.sqrt (q2SimpleLastRoundsMarkedFraction hS Δfin n))⁻¹ *
          lastRoundsCheckingCost k hout Cstar := by
  unfold q2SimpleLastRoundsCost q2SimpleLastRoundsData
  rw [q2_simple_lastrounds_filter_iterations]

/-- The Q2 last-round data expression equals the Q2 simple-differential distinguisher cost. -/
theorem q2_simple_lastrounds_data_eq_distinguisher (hS : ℝ) :
    q2SimpleLastRoundsData hS = q2SimpleDistinguisherCost hS := rfl

/-- For nonnegative `Cstar`, the Q2 last-round cost is at least its data expression. See
[KaplanEtAl2015]. -/
theorem q2_simple_lastrounds_time_ge_data (hS Δfin n k hout Cstar : ℝ)
    (hCstar : 0 ≤ Cstar) :
    q2SimpleLastRoundsData hS ≤ q2SimpleLastRoundsCost hS Δfin n k hout Cstar := by
  unfold q2SimpleLastRoundsCost q2SimpleLastRoundsData lastRoundsCheckingCost
  have hcheck : 0 ≤ Cstar + pow2 ((k - hout) / 2) := by
    have := pow2_nonneg ((k - hout) / 2)
    linarith
  have hiter : 0 ≤ pow2 ((hS + Δfin - n) / 2) := pow2_nonneg _
  have : 0 ≤ pow2 ((hS + Δfin - n) / 2) * (Cstar + pow2 ((k - hout) / 2)) :=
    mul_nonneg hiter hcheck
  linarith

/-- The amplification budget associated with the last-round marked fraction equals `(π/4) *
2^((hS+Δfin-n)/2) + 1`. See [KaplanEtAl2015]. -/
theorem q2_simple_lastrounds_grover_budget (hS Δfin n : ℝ) :
    Real.pi / (4 * Real.sqrt (q2SimpleLastRoundsMarkedFraction hS Δfin n)) + 1 =
      Real.pi / 4 * pow2 ((hS + Δfin - n) / 2) + 1 := by
  unfold q2SimpleLastRoundsMarkedFraction
  exact amplification_budget_pow2 (hS + Δfin - n)

end Qatlib.Papers.QCryptanal15.MainResults.SimpleDifferential
