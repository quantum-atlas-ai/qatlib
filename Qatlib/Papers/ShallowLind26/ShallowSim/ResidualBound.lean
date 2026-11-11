/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Residual-based implementation bound (Proposition 4.12)

Shen--Wu--Yuan--Zhang, fixed arXiv:2610.05362v1, Proposition 4.12, page 24.

Let `Y` be an isometry from the input space into the physical data space.  The
finite implementation `F E_sig` differs from the ideal map `E_sig V` by the two
residuals

`F E_sig Y - E_sig V Y = R_{q,+} Y - R_{q,-} Y`

(one residual for the forward comparison and one for the backward comparison).
If `‖R_{q,+} Y‖ ≤ r_+` and `‖R_{q,-} Y‖ ≤ r_-`, the triangle inequality gives

`‖F E_sig Y - E_sig V Y‖ ≤ r_+ + r_-`.

If a full-comparison implementation additionally carries a terminal error
`‖F̂ - F‖ ≤ η_term`, the same argument adds `η_term`.

We formalize the triangle-inequality core in an arbitrary seminormed additive
group; this is the step that the source applies uniformly to all references,
because the norm is the reference-extended operator norm and the residuals are
bounded on the same input domain.
-/

namespace Qatlib.Papers.ShallowLind26.ShallowSim.ResidualBound

set_option autoImplicit false

variable {E : Type*} [SeminormedAddCommGroup E]

/-- **Proposition 4.12, residual bound.**  A difference of two residuals is
bounded by the sum of their bounds. -/
theorem residual_bound (x a b : E) (rplus rminus : ℝ)
    (hx : x = a - b) (ha : ‖a‖ ≤ rplus) (hb : ‖b‖ ≤ rminus) :
    ‖x‖ ≤ rplus + rminus := by
  subst hx
  calc ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le a b
    _ ≤ rplus + rminus := add_le_add ha hb

/-- **Proposition 4.12, with terminal implementation error.**  An additional
full-comparison error `η_term` raises the bound by exactly `η_term`. -/
theorem residual_bound_terminal (x a b c : E) (rplus rminus eta : ℝ)
    (hx : x = (a - b) + c) (ha : ‖a‖ ≤ rplus) (hb : ‖b‖ ≤ rminus)
    (hc : ‖c‖ ≤ eta) :
    ‖x‖ ≤ rplus + rminus + eta := by
  subst hx
  calc ‖(a - b) + c‖ ≤ ‖a - b‖ + ‖c‖ := norm_add_le (a - b) c
    _ ≤ (rplus + rminus) + eta :=
        add_le_add (residual_bound (a - b) a b rplus rminus rfl ha hb) hc
    _ = rplus + rminus + eta := by ring

/-- The bound is unchanged by an untouched reference: the residual hypotheses
are stated in the same group, so any reference extension satisfying them is
covered.  This records that the statement is reference-uniform. -/
theorem residual_bound_reference (x a b : E) (rplus rminus : ℝ)
    (hx : x = a - b) (ha : ‖a‖ ≤ rplus) (hb : ‖b‖ ≤ rminus) :
    ‖x‖ ≤ rplus + rminus :=
  residual_bound x a b rplus rminus hx ha hb

end Qatlib.Papers.ShallowLind26.ShallowSim.ResidualBound
