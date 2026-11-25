/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Basic.Real.Basic

@[expose] public section

/-!
# Effective depth and coherence budget

Equations (41) and (42) of Goh and Müller (arXiv:2609.35131v1) use the
maximum graph degree to estimate the depth per layer. With a positive gate
count and gate duration, their proxy gives an exact algebraic threshold.
-/

set_option autoImplicit false

namespace Qatlib.Papers.OverlapGapGoh26.Resources

/-- The paper's effective depth per layer, in two-qubit gate time steps. -/
noncomputable def effectiveDepth (gateCount maxDegree : ℕ) : ℝ :=
  (gateCount : ℝ) / ((maxDegree : ℝ) + 1)

/-- The paper's coherence-limited layer count with the degree factor moved to the numerator. -/
theorem coherence_depth_eq (T₂ gateTime : ℝ) (gateCount maxDegree : ℕ) :
    T₂ / (effectiveDepth gateCount maxDegree * gateTime) =
      T₂ * ((maxDegree : ℝ) + 1) / ((gateCount : ℝ) * gateTime) := by
  unfold effectiveDepth
  rw [div_mul_eq_mul_div, div_div_eq_mul_div]

/-- With positive gate count and duration, the proxy reaches its coherence budget strictly
before a given target layer count exactly when the corresponding runtime inequality holds. -/
theorem coherence_lt_target_iff (T₂ gateTime target : ℝ) {gateCount : ℕ} (maxDegree : ℕ)
    (hcount : 0 < gateCount) (htime : 0 < gateTime) :
    T₂ / (effectiveDepth gateCount maxDegree * gateTime) < target ↔
      T₂ * ((maxDegree : ℝ) + 1) < target * ((gateCount : ℝ) * gateTime) := by
  rw [coherence_depth_eq, div_lt_iff₀ (mul_pos (Nat.cast_pos.mpr hcount) htime)]

end Qatlib.Papers.OverlapGapGoh26.Resources
