/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCryptanal15.MainResults.Complexity.Core
import Qatlib.Papers.QCryptanal15.MainResults.Complexity.GroverBudget

/-!
# Matsui Algorithm 1 in the Q1 model

`matsui1Q1Data` and `matsui1Q1Time` specify the data and time cost expressions for Matsui
Algorithm 1 with classical data access. The identities isolate the square-root residual key
search and its explicit amplification budget. The mathematical context is [KaplanEtAl2015].

## Main statements

* `matsui1_q1_cost`: The Q1 time expression is the data cost plus the square root of the
  residual key-space scale.
* `matsui1_q1_grover_budget`: The amplification budget for marked scale `2^(-(k-ℓ))` equals
  `(π/4) * 2^((k-ℓ)/2) + 1`.

## References

* [Kaplan et al., 2015][KaplanEtAl2015]
-/

set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace Qatlib.Papers.QCryptanal15.MainResults.Linear

open Complexity

/-- The Q1 data cost expression `ℓ/ε²` for Matsui Algorithm 1. -/
noncomputable def matsui1Q1Data (ℓ ε : ℝ) : ℝ := ℓ / ε ^ 2

/-- The Q1 time cost expression `ℓ/ε² + 2^((k-ℓ)/2)` for Matsui Algorithm 1. -/
noncomputable def matsui1Q1Time (ℓ ε k : ℝ) : ℝ := ℓ / ε ^ 2 + pow2 ((k - ℓ) / 2)

/-- The square root of the residual key-space scale `2^(k-ℓ)` is `2^((k-ℓ)/2)`. See
[KaplanEtAl2015]. -/
theorem matsui1_q1_key_search_iterations (k ℓ : ℝ) :
    Real.sqrt (pow2 (k - ℓ)) = pow2 ((k - ℓ) / 2) := sqrt_pow2 (k - ℓ)

/-- The Q1 time expression is the data cost plus the square root of the residual key-space
scale. See [KaplanEtAl2015]. -/
theorem matsui1_q1_cost (ℓ ε k : ℝ) :
    matsui1Q1Time ℓ ε k = matsui1Q1Data ℓ ε + Real.sqrt (pow2 (k - ℓ)) := by
  unfold matsui1Q1Time matsui1Q1Data
  rw [sqrt_pow2]

/-- Squaring the residual quantum key-search term gives the classical residual key-space scale.
See [KaplanEtAl2015]. -/
theorem matsui1_q1_classical_final_term (k ℓ : ℝ) :
    pow2 ((k - ℓ) / 2) ^ 2 = pow2 (k - ℓ) := pow2_half_sq (k - ℓ)

/-- The Q1 time expression is at least its data cost. -/
theorem matsui1_q1_time_ge_data (ℓ ε k : ℝ) :
    matsui1Q1Data ℓ ε ≤ matsui1Q1Time ℓ ε k := by
  unfold matsui1Q1Time
  exact le_add_of_nonneg_right (pow2_nonneg _)

/-- The amplification budget for marked scale `2^(-(k-ℓ))` equals `(π/4) * 2^((k-ℓ)/2) + 1`. See
[KaplanEtAl2015]. -/
theorem matsui1_q1_grover_budget (k ℓ : ℝ) :
    Real.pi / (4 * Real.sqrt (pow2 (-(k - ℓ)))) + 1 =
      Real.pi / 4 * pow2 ((k - ℓ) / 2) + 1 :=
  amplification_budget_pow2 (k - ℓ)

end Qatlib.Papers.QCryptanal15.MainResults.Linear
