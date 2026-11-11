/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCryptanal15.MainResults.Complexity.Core
import Qatlib.Papers.QCryptanal15.MainResults.Complexity.GroverBudget

/-!
# Matsui Algorithm 2 in the Q1 model

`matsui2Q1Time` combines classical data acquisition with two quantum key-search terms. The
module rewrites the terms as square roots, bounds time below by data for positive bias, and
evaluates both amplification budgets. The mathematical context is [KaplanEtAl2015].

## Main statements

* `matsui2_q1_cost`: For nonzero `ε`, the Q1 time expression splits into classical data and the
  two stated square-root search terms.
* `matsui2_q1_time_ge_data`: For positive `ε`, the Q1 time expression is at least its data cost.

## References

* [Kaplan et al., 2015][KaplanEtAl2015]
-/

set_option warningAsError false

set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace Qatlib.Papers.QCryptanal15.MainResults.Linear

open Complexity

/-- The Q1 data cost expression `1/ε²` for Matsui Algorithm 2. -/
noncomputable def matsui2Q1Data (ε : ℝ) : ℝ := 1 / ε ^ 2

/-- The Q1 time expression `1/ε² + 2^(kout/2)/ε + 2^((k-kout)/2)` for Matsui Algorithm 2. -/
noncomputable def matsui2Q1Time (kout ε k : ℝ) : ℝ :=
  1 / ε ^ 2 + pow2 (kout / 2) / ε + pow2 ((k - kout) / 2)

/-- For nonzero `ε`, the first search term is the square root of `2^kout` multiplied by `1/ε`.
See [KaplanEtAl2015]. -/
theorem matsui2_q1_first_grover_cost (kout ε : ℝ) (hε : ε ≠ 0) :
    pow2 (kout / 2) / ε = Real.sqrt (pow2 kout) * (1 / ε) := by
  rw [sqrt_pow2]
  field_simp

/-- For nonzero `ε`, the Q1 time expression splits into classical data and the two stated
square-root search terms. See [KaplanEtAl2015]. -/
theorem matsui2_q1_cost (kout ε k : ℝ) (hε : ε ≠ 0) :
    matsui2Q1Time kout ε k =
      1 / ε ^ 2 + Real.sqrt (pow2 kout) * (1 / ε) + Real.sqrt (pow2 (k - kout)) := by
  unfold matsui2Q1Time
  rw [matsui2_q1_first_grover_cost kout ε hε]
  exact congrArg (fun x => 1 / ε ^ 2 + Real.sqrt (pow2 kout) * (1 / ε) + x)
    (sqrt_pow2 (k - kout)).symm

/-- For positive `ε`, the Q1 time expression is at least its data cost. See [KaplanEtAl2015]. -/
theorem matsui2_q1_time_ge_data (kout ε k : ℝ) (hε : 0 < ε) :
    matsui2Q1Data ε ≤ matsui2Q1Time kout ε k := by
  unfold matsui2Q1Data matsui2Q1Time
  have h1 : 0 ≤ pow2 (kout / 2) / ε := div_nonneg (pow2_nonneg _) hε.le
  have h2 : 0 ≤ pow2 ((k - kout) / 2) := pow2_nonneg _
  linarith

/-- The amplification budget for the first key-search scale is `(π/4) * 2^(kout/2) + 1`. See
[KaplanEtAl2015]. -/
theorem matsui2_q1_first_grover_budget (kout : ℝ) :
    Real.pi / (4 * Real.sqrt (pow2 (-kout))) + 1 =
      Real.pi / 4 * pow2 (kout / 2) + 1 :=
  amplification_budget_pow2 kout

/-- The amplification budget for the residual key-search scale is `(π/4) * 2^((k-kout)/2) + 1`.
See [KaplanEtAl2015]. -/
theorem matsui2_q1_second_grover_budget (k kout : ℝ) :
    Real.pi / (4 * Real.sqrt (pow2 (-(k - kout)))) + 1 =
      Real.pi / 4 * pow2 ((k - kout) / 2) + 1 :=
  amplification_budget_pow2 (k - kout)

end Qatlib.Papers.QCryptanal15.MainResults.Linear
