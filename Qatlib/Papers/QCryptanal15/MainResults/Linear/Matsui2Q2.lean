/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCryptanal15.MainResults.Complexity.GroverBudget
import Qatlib.Papers.QCryptanal15.MainResults.Linear.Matsui2Q1

/-!
# Matsui Algorithm 2 in the Q2 model

`matsui2Q2Data` and `matsui2Q2Time` encode the Q2 cost expressions. `matsui2_q2_cost` separates
data from residual search, and `matsui2_q2_time_le_q1_time` compares the Q2 and Q1 formulas. The
mathematical context is [KaplanEtAl2015].

## Main statements

* `matsui2_q2_cost`: The Q2 time expression is its data cost plus the square root of the
  residual key-space scale.
* `matsui2_q2_time_le_q1_time`: The Q2 time expression is no greater than the Q1 time
  expression.

## References

* [Kaplan et al., 2015][KaplanEtAl2015]
-/

set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace Qatlib.Papers.QCryptanal15.MainResults.Linear

open Complexity

/-- The Q2 data cost expression `2^(kout/2)/ε` for Matsui Algorithm 2. -/
noncomputable def matsui2Q2Data (kout ε : ℝ) : ℝ := pow2 (kout / 2) / ε

/-- The Q2 time expression `2^(kout/2)/ε + 2^((k-kout)/2)` for Matsui Algorithm 2. -/
noncomputable def matsui2Q2Time (kout ε k : ℝ) : ℝ :=
  pow2 (kout / 2) / ε + pow2 ((k - kout) / 2)

/-- For nonzero `ε`, the Q2 data expression is `sqrt (2^kout) * (1/ε)`. See [KaplanEtAl2015]. -/
theorem matsui2_q2_data_grover (kout ε : ℝ) (hε : ε ≠ 0) :
    matsui2Q2Data kout ε = Real.sqrt (pow2 kout) * (1 / ε) := by
  unfold matsui2Q2Data
  rw [sqrt_pow2]
  field_simp

/-- The Q2 time expression is its data cost plus the square root of the residual key-space
scale. See [KaplanEtAl2015]. -/
theorem matsui2_q2_cost (kout ε k : ℝ) :
    matsui2Q2Time kout ε k = matsui2Q2Data kout ε + Real.sqrt (pow2 (k - kout)) := by
  unfold matsui2Q2Time matsui2Q2Data
  rw [sqrt_pow2]

/-- The Q2 time expression is at least its data cost. -/
theorem matsui2_q2_time_ge_data (kout ε k : ℝ) :
    matsui2Q2Data kout ε ≤ matsui2Q2Time kout ε k := by
  unfold matsui2Q2Time
  exact le_add_of_nonneg_right (pow2_nonneg _)

/-- The Q2 time expression is no greater than the Q1 time expression. See [KaplanEtAl2015]. -/
theorem matsui2_q2_time_le_q1_time (kout ε k : ℝ) :
    matsui2Q2Time kout ε k ≤ matsui2Q1Time kout ε k := by
  unfold matsui2Q2Time matsui2Q1Time
  have h : 0 ≤ 1 / ε ^ 2 := div_nonneg zero_le_one (sq_nonneg ε)
  linarith

/-- The data-search amplification budget is `(π/4) * 2^(kout/2) + 1`. See [KaplanEtAl2015]. -/
theorem matsui2_q2_data_grover_budget (kout : ℝ) :
    Real.pi / (4 * Real.sqrt (pow2 (-kout))) + 1 =
      Real.pi / 4 * pow2 (kout / 2) + 1 :=
  amplification_budget_pow2 kout

end Qatlib.Papers.QCryptanal15.MainResults.Linear
