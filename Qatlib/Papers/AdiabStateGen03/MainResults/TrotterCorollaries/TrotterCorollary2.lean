/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabStateGen03.MainResults.Defs
import Qatlib.Papers.AdiabStateGen03.MainResults.TrotterCorollaries.PowerAccumulation
import Qatlib.Papers.AdiabStateGen03.MainResults.TrotterCorollaries.TrotterStep

/-!
# Trotter error at an exact step count

This module derives accumulated Trotter error bounds from an assumed cubic single-step estimate
and contraction bounds. The theorem `trotter_accumulation_two` controls an arbitrary number of
steps, while `trotter_corollary_two_of_step` expresses the result at a target time exactly equal
to the total step duration. The mathematical context is [AharonovTaShma2007].

## Main statements

* `trotter_accumulation_two`: An assumed cubic Trotter step error accumulates at most linearly
  over `N` steps when both step operators have norm at most one.
* `trotter_corollary_two_of_step`: When `N * (2 * δ) = t`, the assumed cubic step estimate and
  contraction bounds give total error at most `C * N * M * (δ * Λ) ^ 3` at time `t`.

## References

* [Aharonov and Ta‐Shma, 2007][AharonovTaShma2007]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder InnerProductSpace BigOperators

namespace Qatlib.Papers.AdiabStateGen03.MainResults.TrotterCorollaries

/-- An assumed cubic Trotter step error accumulates at most linearly over `N` steps when both
step operators have norm at most one [AharonovTaShma2007]. -/
theorem trotter_accumulation_two {n M : ℕ} (Hs : Fin M → Ham n) (H : Ham n)
    (Λ δ C : ℝ) (N : ℕ)
    (hstep : ‖trotterStep Hs δ - timeEvolution H (2 * δ)‖ ≤ C * (M : ℝ) * (δ * Λ) ^ 3)
    (hU : ‖trotterStep Hs δ‖ ≤ 1) (hV : ‖timeEvolution H (2 * δ)‖ ≤ 1) :
    ‖trotterStep Hs δ ^ N - timeEvolution H ((N : ℝ) * (2 * δ))‖
      ≤ (N : ℝ) * (C * (M : ℝ) * (δ * Λ) ^ 3) := by
  have hpow : timeEvolution H (2 * δ) ^ N = timeEvolution H ((N : ℝ) * (2 * δ)) :=
    timeEvolution_pow_nat H (2 * δ) N
  rw [← hpow]
  calc ‖trotterStep Hs δ ^ N - timeEvolution H (2 * δ) ^ N‖
      ≤ (N : ℝ) * ‖trotterStep Hs δ - timeEvolution H (2 * δ)‖ :=
        norm_pow_sub_pow_le_of_norm_le_one _ _ hU hV N
    _ ≤ (N : ℝ) * (C * (M : ℝ) * (δ * Λ) ^ 3) :=
        mul_le_mul_of_nonneg_left hstep (Nat.cast_nonneg N)

/-- When `N * (2 * δ) = t`, the assumed cubic step estimate and contraction bounds give total
error at most `C * N * M * (δ * Λ) ^ 3` at time `t` [AharonovTaShma2007]. -/
theorem trotter_corollary_two_of_step {n M : ℕ} (Hs : Fin M → Ham n) (H : Ham n)
    (Λ δ t C : ℝ) (N : ℕ)
    (hstep : ‖trotterStep Hs δ - timeEvolution H (2 * δ)‖ ≤ C * (M : ℝ) * (δ * Λ) ^ 3)
    (hU : ‖trotterStep Hs δ‖ ≤ 1) (hV : ‖timeEvolution H (2 * δ)‖ ≤ 1)
    (hN : (N : ℝ) * (2 * δ) = t) :
    ‖trotterStep Hs δ ^ N - timeEvolution H t‖
      ≤ C * (N : ℝ) * (M : ℝ) * (δ * Λ) ^ 3 := by
  have h := trotter_accumulation_two Hs H Λ δ C N hstep hU hV
  rw [hN] at h

  calc ‖trotterStep Hs δ ^ N - timeEvolution H t‖
      ≤ (N : ℝ) * (C * (M : ℝ) * (δ * Λ) ^ 3) := h
    _ = C * (N : ℝ) * (M : ℝ) * (δ * Λ) ^ 3 := by ring

end Qatlib.Papers.AdiabStateGen03.MainResults.TrotterCorollaries
