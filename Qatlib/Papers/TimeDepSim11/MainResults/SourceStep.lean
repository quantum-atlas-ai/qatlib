/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.TimeDepSim11.MainResults.TrotterTotalError

@[expose] public section

/-!
# Error budget at the source Trotter step size

Compose the finite sum for the segment error with the segment count and
the step size chosen on pp. 2–3 of arXiv:1102.1360v1.
-/

set_option autoImplicit false

open scoped BigOperators
open Qatlib.Papers.TimeDepSim11.MainResults.TrotterTotalError

namespace Qatlib.Papers.TimeDepSim11.MainResults

/-- At the paper's positive step size, the accumulated finite Trotter error bound is
at most half the desired tolerance. -/
theorem trotter_total_error_at_source_dt (ε T cmax L : ℝ) (M : ℕ)
    (hε : 0 < ε) (hT : 0 < T) (hcmax : 0 < cmax) (hL : 0 < L) :
    let dt := ε / (T * cmax ^ 2 * L ^ 2)
    (T / dt) * ((1 / 2) * cmax ^ 2 * dt ^ 2 *
      (∑ i ∈ Finset.range M, (2 : ℝ) ^ (i + 1) * (L / (2 : ℝ) ^ (i + 1)) ^ 2)) ≤ ε / 2 := by
  let dt := ε / (T * cmax ^ 2 * L ^ 2)
  have hdt : 0 < dt := div_pos hε (by positivity)
  change (T / dt) * _ ≤ ε / 2
  calc
    _ ≤ (T / dt) * ((1 / 2) * cmax ^ 2 * L ^ 2 * dt ^ 2) :=
      mul_le_mul_of_nonneg_left (trotter_step_error_bound cmax L dt M hcmax.le)
        (div_nonneg hT.le hdt.le)
    _ = ε / 2 := trotter_dt_choice_half_epsilon ε T cmax L hε hT hcmax hL

end Qatlib.Papers.TimeDepSim11.MainResults
