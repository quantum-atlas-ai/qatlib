/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SparseHamSim13.MainResults.BoundProbe

@[expose] public section

/-!
# Weighted segment cost and a positive logarithmic budget

The finite-segment model maps each continuous evolution to a fractional
query of the same generator with a negated angle. The weight of a segment
is its duration times the generator's maximum entry norm. Unit segment
weights recover elapsed time. A separate logarithmic inequality gives a
positive query budget in a sufficient small-error regime.
-/

set_option autoImplicit false

open Qatlib.Papers.SparseHamSim13.MainResults
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.SparseHamSim13.MainResults

/-- The modeled fractional word charges each nonnegative segment duration
times the segment generator's maximum entry norm. -/
theorem frac_cost_continuous_embed {n : ℕ} (P : ContinuousProgram n) :
    fracCost (P.segments.map (fun p => FracStep.query p.1 (-p.2))) =
      (P.segments.map (fun p => p.2 * matMaxEntry p.1)).sum := by
  have hcost (segments : List (Matrix (Reg n) (Reg n) ℂ × ℝ))
      (hd : ∀ p ∈ segments, 0 ≤ p.2) :
      fracCost (segments.map (fun p => FracStep.query p.1 (-p.2))) =
        (segments.map (fun p => p.2 * matMaxEntry p.1)).sum := by
    induction segments with
    | nil => rfl
    | cons p tail ih =>
      have hp := hd p (by simp)
      have ht := ih (fun q hq => hd q (List.mem_cons_of_mem p hq))
      simp [fracCost, abs_of_nonneg hp, ht]
  exact hcost P.segments P.duration_nonneg

/-- For unit max-entry norms the identical fractional embedding also
charges exactly the elapsed time. -/
theorem frac_cost_eq_time_of_unit_weights {n : ℕ} (P : ContinuousProgram n)
    (hnorm : ∀ p ∈ P.segments, matMaxEntry p.1 = 1) :
    fracCost (P.segments.map (fun p => FracStep.query p.1 (-p.2))) = P.totalTime := by
  rw [frac_cost_continuous_embed, ContinuousProgram.totalTime]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  rw [hnorm p hp, mul_one]

/-- The displayed query-budget expression is positive when the ratio
`τ / ε` is at least `exp (exp 1)`. -/
theorem query_bound_pos_of_regime {τ ε : ℝ} (hε : 0 < ε)
    (hreg : Real.exp (Real.exp 1) * ε ≤ τ) : 0 < queryBound τ ε := by
  have hstrict : Real.exp 1 < Real.exp (Real.exp 1) :=
    Real.exp_lt_exp.mpr (Real.one_lt_exp_iff.mpr zero_lt_one)
  exact queryBound_pos hε (hstrict.trans_le ((le_div_iff₀ hε).mpr hreg))

end Qatlib.Papers.SparseHamSim13.MainResults
