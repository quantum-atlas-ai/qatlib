/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCryptanal15.MainResults.Complexity.GroverBudget
import Qatlib.Papers.QCryptanal15.MainResults.Linear.Matsui1Q1
import Qatlib.Papers.QCryptanal15.MainResults.Linear.Q2Distinguisher

/-!
# Matsui Algorithm 1 in the Q2 model

`matsui1Q2Data` replaces the inverse-square bias dependence by an inverse-linear counting cost.
`matsui1_q2_cost` separates this data expression from residual key search, and the remaining
results compare Q1 data and give the search budget. The mathematical context is
[KaplanEtAl2015].

## Main statements

* `matsui1_q2_data_eq_epsilon_mul_q1`: For nonzero `ε`, the Q2 data expression equals `ε` times
  the Q1 data expression.
* `matsui1_q2_cost`: The Q2 time expression is its data cost plus the square root of the
  residual key-space scale.

## References

* [Kaplan et al., 2015][KaplanEtAl2015]
-/

set_option warningAsError false

set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace Qatlib.Papers.QCryptanal15.MainResults.Linear

open Complexity

/-- The Q2 data cost expression `ℓ/ε` for Matsui Algorithm 1. -/
noncomputable def matsui1Q2Data (ℓ ε : ℝ) : ℝ := ℓ / ε

/-- The Q2 time cost expression `ℓ/ε + 2^((k-ℓ)/2)` for Matsui Algorithm 1. -/
noncomputable def matsui1Q2Time (ℓ ε k : ℝ) : ℝ := ℓ / ε + pow2 ((k - ℓ) / 2)

/-- The Q2 data expression is `ℓ` times the Q2 linear-distinguisher cost. See [KaplanEtAl2015]. -/
theorem matsui1_q2_data_is_linear_counting (ℓ ε : ℝ) :
    matsui1Q2Data ℓ ε = ℓ * q2LinearDistinguisherCost ε := by
  unfold matsui1Q2Data q2LinearDistinguisherCost
  ring

/-- For nonzero `ε`, the Q2 data expression equals `ε` times the Q1 data expression. See
[KaplanEtAl2015]. -/
theorem matsui1_q2_data_eq_epsilon_mul_q1 (ℓ ε : ℝ) (hε : ε ≠ 0) :
    matsui1Q2Data ℓ ε = ε * matsui1Q1Data ℓ ε := by
  unfold matsui1Q2Data matsui1Q1Data
  field_simp

/-- The Q2 time expression is its data cost plus the square root of the residual key-space
scale. See [KaplanEtAl2015]. -/
theorem matsui1_q2_cost (ℓ ε k : ℝ) :
    matsui1Q2Time ℓ ε k = matsui1Q2Data ℓ ε + Real.sqrt (pow2 (k - ℓ)) := by
  unfold matsui1Q2Time matsui1Q2Data
  rw [sqrt_pow2]

/-- The Q2 time expression is at least its data cost. -/
theorem matsui1_q2_time_ge_data (ℓ ε k : ℝ) :
    matsui1Q2Data ℓ ε ≤ matsui1Q2Time ℓ ε k := by
  unfold matsui1Q2Time
  exact le_add_of_nonneg_right (pow2_nonneg _)

/-- The residual key-search amplification budget is `(π/4) * 2^((k-ℓ)/2) + 1`. See
[KaplanEtAl2015]. -/
theorem matsui1_q2_grover_budget (k ℓ : ℝ) :
    Real.pi / (4 * Real.sqrt (pow2 (-(k - ℓ)))) + 1 =
      Real.pi / 4 * pow2 ((k - ℓ) / 2) + 1 :=
  amplification_budget_pow2 (k - ℓ)

end Qatlib.Papers.QCryptanal15.MainResults.Linear
