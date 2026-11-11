/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabLimit07.MainResults.RuntimeBound

/-!
# A complement dimension consequence of the runtime bound

Rearranges a scalar runtime inequality to obtain a lower bound on the complementary eigenspace
dimension. The argument uses positivity of the configuration count, solution-set size, energy
bound, and complement dimension, together with nonnegative runtime. See [IoannouMosca2008].

## Main statements

* `complement_dim_ge`: A runtime lower bound implies the corresponding complement dimension
  lower bound.

## References

* [Ioannou and Mosca, 2008][IoannouMosca2008]
-/

set_option warningAsError false

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.AdiabLimit07.MainResults

open Matrix
open Qatlib.Foundations.PureStateMath
open scoped BigOperators Matrix

variable {n : ℕ}

/-- Under the stated positivity assumptions and `T ≥ 0`, a runtime lower bound yields `(c * sqrt
N - cardP0 / sqrt N) / (2 * cardP0 * maxF * T) ≤ compDim` [IoannouMosca2008]. -/
theorem complement_dim_ge {c cardP0 maxF compDim T N : ℝ}
    (hN : 0 < N) (hT : 0 ≤ T) (hcard : 0 < cardP0) (hmaxF : 0 < maxF)
    (hcomp : 0 < compDim)
    (h : (c * Real.sqrt N - cardP0 / Real.sqrt N)
            / (2 * cardP0 * maxF * compDim) ≤ T) :
    (c * Real.sqrt N - cardP0 / Real.sqrt N) / (2 * cardP0 * maxF * T) ≤ compDim := by
  have hD : 0 < 2 * cardP0 * maxF := by positivity
  have hden : 0 < 2 * cardP0 * maxF * compDim := by positivity
  have hmain : c * Real.sqrt N - cardP0 / Real.sqrt N
      ≤ T * (2 * cardP0 * maxF * compDim) := (div_le_iff₀ hden).mp h
  by_cases hT0 : T = 0
  · rw [hT0]
    simp only [mul_zero, div_zero]
    exact le_of_lt hcomp
  · have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hT0)
    rw [div_le_iff₀ (by positivity : 0 < 2 * cardP0 * maxF * T)]
    nlinarith [hmain]

end Qatlib.Papers.AdiabLimit07.MainResults
