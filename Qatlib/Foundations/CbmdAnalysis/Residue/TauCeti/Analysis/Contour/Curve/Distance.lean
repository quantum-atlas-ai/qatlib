/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.Compact

/-!
# Distance bounds for compact curve traces

This module proves uniform separation of a continuous compact curve from an avoided point and
from a small neighborhood of that point. It also gives closedness of distance cutoff sets and
existence of points off the trace, providing geometric tools for the contour analysis supporting
[WangEtAl2026].

## Main statements

* `exists_ball_dist_curve_lower_bound`: uniform separation from a neighborhood.
* `isClosed_setOfPred_mem_uIcc_norm_sub_le`: closedness of a norm cutoff set.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

open Set

namespace TauCeti.Contour

variable {E : Type*}

section Normed

variable [NormedAddCommGroup E]

/-- A continuous curve on a compact parameter interval avoiding `w` stays a positive uniform
distance from `w`. -/
theorem exists_curve_dist_lower_bound {γ : ℝ → E} {w : E} {a b : ℝ}
    (hγ : ContinuousOn γ (uIcc a b)) (h_avoid : ∀ t ∈ uIcc a b, γ t ≠ w) :
    ∃ ρ > 0, ∀ t ∈ uIcc a b, ρ ≤ ‖γ t - w‖ := by
  have h_image_compact : IsCompact (γ '' uIcc a b) := isCompact_uIcc.image_of_continuousOn hγ
  have h_image_nonempty : (γ '' uIcc a b).Nonempty := ⟨γ a, mem_image_of_mem _ left_mem_uIcc⟩
  have h_w_not_mem : w ∉ γ '' uIcc a b := fun ⟨t, ht, heq⟩ ↦ h_avoid t ht heq
  refine ⟨Metric.infDist w (γ '' uIcc a b),
    (h_image_compact.isClosed.notMem_iff_infDist_pos h_image_nonempty).mp h_w_not_mem,
    fun t ht ↦ ?_⟩
  rw [← dist_eq_norm, dist_comm]
  exact Metric.infDist_le_dist_of_mem (mem_image_of_mem γ ht)

/-- A continuous curve avoiding `w₀` stays uniformly separated from every point in a
sufficiently small ball about `w₀`. -/
theorem exists_ball_dist_curve_lower_bound {γ : ℝ → E} {w₀ : E} {a b : ℝ}
    (hγ : ContinuousOn γ (uIcc a b)) (h_avoid : ∀ t ∈ uIcc a b, γ t ≠ w₀) :
    ∃ ε > 0, ∀ w ∈ Metric.ball w₀ ε, ∀ t ∈ uIcc a b, ε ≤ ‖γ t - w‖ := by
  obtain ⟨ρ, hρ_pos, h_dist_lb⟩ := exists_curve_dist_lower_bound hγ h_avoid
  refine ⟨ρ / 2, half_pos hρ_pos, fun w hw t ht ↦ ?_⟩
  have h := h_dist_lb t ht
  rw [Metric.mem_ball] at hw
  rw [← dist_eq_norm] at h ⊢
  linarith [dist_triangle (γ t) w w₀]

end Normed

/-- In a noncompact preconnected Hausdorff space, an open set containing a compact curve trace
contains a point outside that trace. -/
theorem exists_mem_off_curve [TopologicalSpace E] [T2Space E] [PreconnectedSpace E]
    [NoncompactSpace E] {γ : ℝ → E} {Ω : Set E} {a b : ℝ} (hΩ : IsOpen Ω)
    (hγ : ContinuousOn γ (uIcc a b)) (hγΩ : ∀ t ∈ uIcc a b, γ t ∈ Ω) :
    ∃ w₀ ∈ Ω, ∀ t ∈ uIcc a b, γ t ≠ w₀ := by
  by_contra! hcon
  have hcompact : IsCompact Ω := by
    rw [← (image_subset_iff.mpr hγΩ).antisymm hcon]
    exact isCompact_uIcc.image_of_continuousOn hγ
  have huniv : Ω = univ := IsClopen.eq_univ ⟨hcompact.isClosed, hΩ⟩ ⟨γ a, hγΩ a left_mem_uIcc⟩
  exact noncompact_univ E (huniv ▸ hcompact)

/-- The parameters in an unordered closed interval whose curve values are within distance `ε` of
`s` form a closed set. -/
theorem isClosed_setOfPred_mem_uIcc_dist_le [PseudoMetricSpace E] {γ : ℝ → E}
    {a b : ℝ} (hγ_cont : ContinuousOn γ (uIcc a b)) (s : E) (ε : ℝ) :
    IsClosed {t ∈ uIcc a b | dist (γ t) s ≤ ε} :=
  isCompact_uIcc.isClosed.isClosed_le
    ((continuous_id.dist continuous_const).comp_continuousOn hγ_cont) continuousOn_const

/-- The parameters in an unordered closed interval satisfying `‖γ t - s‖ ≤ ε` form a closed set. -/
theorem isClosed_setOfPred_mem_uIcc_norm_sub_le [SeminormedAddCommGroup E]
    {γ : ℝ → E} {a b : ℝ} (hγ_cont : ContinuousOn γ (uIcc a b)) (s : E) (ε : ℝ) :
    IsClosed {t ∈ uIcc a b | ‖γ t - s‖ ≤ ε} := by
  simpa [dist_eq_norm] using isClosed_setOfPred_mem_uIcc_dist_le hγ_cont s ε

end TauCeti.Contour

end
end Qatlib.Foundations.CbmdAnalysis.Residue
