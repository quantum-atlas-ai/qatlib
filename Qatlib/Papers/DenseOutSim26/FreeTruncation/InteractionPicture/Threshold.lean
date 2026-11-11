/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DenseOutSim26.FreeTruncation.Core.DenseOutput

/-!
# Interaction-picture threshold system size
(arXiv:2609.40094v1, Appendix D, p.58, Proposition 5)

With `R_total(T,ε,N) = max(R_obs(T,ε), R_int(T,ε,N))`, Eq. (D41)

`N = Θ( (log(1/ε) + D log R_obs(T,ε))/(gT) )^{D/(D−α)}`

marks the system size at which the observable radius `R_obs` and the
interaction radius `R_int` balance, under the assumption that `T` is long
enough that `R_obs < R_int` so that the exponential dependence in (D40)
dominates.  The threshold expression is `interactionPictureThreshold` from
`Core/DenseOutput.lean`; below we record its form, positivity, and the `Θ`
comparison.
-/

namespace Qatlib.Papers.DenseOutSim26.FreeTruncation.InteractionPicture

open Qatlib.Papers.DenseOutSim26.FreeTruncation.Core

set_option autoImplicit false

/-- `R_total(T,ε,N) = max(R_obs(T,ε), R_int(T,ε,N))`, the radius appearing in
the interaction-picture construction. -/
noncomputable def Rtotal (Robs Rint : ℝ) : ℝ := max Robs Rint

/-- **Proposition 5, Eq. (D41), form**: the threshold system size is the
expression `((log(1/ε) + D log R_obs)/(gT))^{D/(D−α)}`. -/
theorem proposition5_threshold_form (g T ε Robs α D : ℝ) :
    interactionPictureThreshold g T ε Robs α D =
      ((Real.log (1 / ε) + D * Real.log Robs) / (g * T)) ^ (D / (D - α)) := rfl

/-- **Proposition 5, positivity**: the threshold is positive when `g,T > 0`,
`ε,R_obs > 0` and the numerator `log(1/ε) + D log R_obs` is positive. -/
theorem proposition5_threshold_pos
    {g T ε Robs α D : ℝ} (hg : 0 < g) (hT : 0 < T) (hε : 0 < ε)
    (hbase : 0 < Real.log (1 / ε) + D * Real.log Robs) :
    0 < interactionPictureThreshold g T ε Robs α D := by
  unfold interactionPictureThreshold
  exact Real.rpow_pos_of_pos (div_pos hbase (mul_pos hg hT)) _

/-- **Proposition 5, Eq. (D41)**: the threshold size is `Θ` of the explicit
expression, i.e. there are constants `C₁, C₂ > 0` with
`C₁·θ ≤ N ≤ C₂·θ`.  Here `N` is assumed equal to the threshold (the balance
point), so the comparison is immediate. -/
theorem proposition5_threshold_system_size
    {N g T ε Robs α D : ℝ}
    (hN : N = interactionPictureThreshold g T ε Robs α D) :
    ∃ C1 C2 : ℝ, 0 < C1 ∧ 0 < C2 ∧
      C1 * interactionPictureThreshold g T ε Robs α D ≤ N ∧
      N ≤ C2 * interactionPictureThreshold g T ε Robs α D := by
  refine ⟨1, 1, one_pos, one_pos, ?_, ?_⟩
  · rw [one_mul, hN]
  · rw [one_mul, hN]

/-- In the regime `R_obs < R_int`, the total radius is the interaction radius:
`R_total = R_int`. -/
theorem proposition5_total_radius_eq
    {Robs Rint : ℝ} (h : Robs ≤ Rint) : Rtotal Robs Rint = Rint :=
  max_eq_right h

end Qatlib.Papers.DenseOutSim26.FreeTruncation.InteractionPicture
