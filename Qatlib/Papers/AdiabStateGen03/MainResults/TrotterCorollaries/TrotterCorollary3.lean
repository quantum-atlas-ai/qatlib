/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabStateGen03.MainResults.Defs
import Qatlib.Papers.AdiabStateGen03.MainResults.TrotterCorollaries.PowerAccumulation
import Qatlib.Papers.AdiabStateGen03.MainResults.TrotterCorollaries.TrotterStep
import Mathlib.Tactic.Abel

/-!
# Trotter error with a target-time remainder

This module combines a single-step approximation estimate with a bound on the difference between
the total step time and the target evolution time. The theorem
`trotter_three_error_decomposition` separates the accumulated error and the time remainder;
`trotter_corollary_three_of_step` substitutes the specified bounds for these two terms. The
mathematical context is [AharonovTaShma2007].

## Main statements

* `trotter_three_error_decomposition`: Under contraction bounds, an assumed step error `B` and a
  target-time remainder error `B₂` give total error at most `N * B + B₂`.
* `trotter_corollary_three_of_step`: The supplied step and time-remainder estimates yield total
  error at most `C₁ * N * M * Λ * δ + C₂ * M * Λ ^ 3 * t * δ ^ 2` under contraction bounds.

## References

* [Aharonov and Ta‐Shma, 2007][AharonovTaShma2007]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder InnerProductSpace BigOperators

namespace Qatlib.Papers.AdiabStateGen03.MainResults.TrotterCorollaries

/-- Under contraction bounds, an assumed step error `B` and a target-time remainder error `B₂`
give total error at most `N * B + B₂` [AharonovTaShma2007]. -/
theorem trotter_three_error_decomposition {n M : ℕ} (Hs : Fin M → Ham n) (H : Ham n)
    (δ B B₂ : ℝ) (N : ℕ) (t : ℝ)
    (hstep : ‖trotterStep Hs δ - timeEvolution H (2 * δ)‖ ≤ B)
    (hU : ‖trotterStep Hs δ‖ ≤ 1) (hV : ‖timeEvolution H (2 * δ)‖ ≤ 1)
    (hfloor : ‖timeEvolution H ((N : ℝ) * (2 * δ)) - timeEvolution H t‖ ≤ B₂) :
    ‖trotterStep Hs δ ^ N - timeEvolution H t‖ ≤ (N : ℝ) * B + B₂ := by
  have hpow : timeEvolution H (2 * δ) ^ N = timeEvolution H ((N : ℝ) * (2 * δ)) :=
    timeEvolution_pow_nat H (2 * δ) N
  have h1 : ‖trotterStep Hs δ ^ N - timeEvolution H (2 * δ) ^ N‖ ≤ (N : ℝ) * B :=
    (norm_pow_sub_pow_le_of_norm_le_one _ _ hU hV N).trans
      (mul_le_mul_of_nonneg_left hstep (Nat.cast_nonneg N))
  have h2 : ‖timeEvolution H (2 * δ) ^ N - timeEvolution H t‖ ≤ B₂ := by
    rw [hpow]
    exact hfloor
  have hsplit : trotterStep Hs δ ^ N - timeEvolution H t
      = (trotterStep Hs δ ^ N - timeEvolution H (2 * δ) ^ N)
        + (timeEvolution H (2 * δ) ^ N - timeEvolution H t) := by
    abel
  calc ‖trotterStep Hs δ ^ N - timeEvolution H t‖
      = ‖(trotterStep Hs δ ^ N - timeEvolution H (2 * δ) ^ N)
          + (timeEvolution H (2 * δ) ^ N - timeEvolution H t)‖ := by rw [hsplit]
    _ ≤ ‖trotterStep Hs δ ^ N - timeEvolution H (2 * δ) ^ N‖
          + ‖timeEvolution H (2 * δ) ^ N - timeEvolution H t‖ := norm_add_le _ _
    _ ≤ (N : ℝ) * B + B₂ := add_le_add h1 h2

/-- The supplied step and time-remainder estimates yield total error at most `C₁ * N * M * Λ * δ
+ C₂ * M * Λ ^ 3 * t * δ ^ 2` under contraction bounds [AharonovTaShma2007]. -/
theorem trotter_corollary_three_of_step {n M : ℕ} (Hs : Fin M → Ham n) (H : Ham n)
    (Λ δ t C₁ C₂ : ℝ) (N : ℕ)
    (hstep : ‖trotterStep Hs δ - timeEvolution H (2 * δ)‖ ≤ C₁ * (M : ℝ) * Λ * δ)
    (hU : ‖trotterStep Hs δ‖ ≤ 1) (hV : ‖timeEvolution H (2 * δ)‖ ≤ 1)
    (hfloor : ‖timeEvolution H ((N : ℝ) * (2 * δ)) - timeEvolution H t‖
      ≤ C₂ * (M : ℝ) * Λ ^ 3 * t * δ ^ 2) :
    ‖trotterStep Hs δ ^ N - timeEvolution H t‖
      ≤ C₁ * (N : ℝ) * (M : ℝ) * Λ * δ + C₂ * (M : ℝ) * Λ ^ 3 * t * δ ^ 2 := by
  have h := trotter_three_error_decomposition Hs H δ
    (C₁ * (M : ℝ) * Λ * δ) (C₂ * (M : ℝ) * Λ ^ 3 * t * δ ^ 2) N t hstep hU hV hfloor
  calc ‖trotterStep Hs δ ^ N - timeEvolution H t‖
      ≤ (N : ℝ) * (C₁ * (M : ℝ) * Λ * δ)
          + C₂ * (M : ℝ) * Λ ^ 3 * t * δ ^ 2 := h
    _ = C₁ * (N : ℝ) * (M : ℝ) * Λ * δ
          + C₂ * (M : ℝ) * Λ ^ 3 * t * δ ^ 2 := by ring

end Qatlib.Papers.AdiabStateGen03.MainResults.TrotterCorollaries
