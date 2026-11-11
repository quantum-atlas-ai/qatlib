/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Calculus.OneSidedDerivLimit
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Monotonicity of distance near crossings

This module uses nonzero one-sided derivative limits to control the inner product between a
crossing chord and its derivative. It deduces local strict monotonicity of distance on either
side, supporting the truncation windows used in the contour analysis for [WangEtAl2026].

## Main statements

* `exists_strictMonoOn_norm_sub_right`: strict distance increase to the right.
* `exists_strictAntiOn_norm_sub_left`: strict distance decrease to the left.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

noncomputable section

namespace TauCeti.Contour

open Filter Set Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Near a crossing with nonzero limiting tangent, the chord-derivative inner product differs
from `(t - t₀) * ‖L‖²` by at most half its absolute leading scale. -/
private theorem abs_inner_chord_deriv_sub_le {γ : ℝ → F} {t₀ : ℝ} {s : F} (h_at : γ t₀ = s)
    {L : F} (hL : L ≠ 0) {u : Set ℝ} (h_deriv : HasDerivWithinAt γ L u t₀)
    (hL_tendsto : Tendsto (deriv γ) (𝓝[u] t₀) (𝓝 L)) :
    ∀ᶠ t in 𝓝[u] t₀,
      |inner ℝ (γ t - s) (deriv γ t) - (t - t₀) * ‖L‖ ^ 2| ≤ |t - t₀| * ‖L‖ ^ 2 / 2 := by
  have hr := hasDerivWithinAt_iff_isLittleO.mp h_deriv
  set η : ℝ := ‖L‖ / 8 with hη_def
  have hL_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  have hη_pos : 0 < η := by rw [hη_def]; positivity
  have h_deriv_close : ∀ᶠ t in 𝓝[u] t₀, ‖deriv γ t - L‖ < η := by
    filter_upwards [(Metric.tendsto_nhds.mp hL_tendsto) η hη_pos] with t ht
    rwa [dist_eq_norm] at ht
  filter_upwards [hr.def hη_pos, h_deriv_close] with t h_chord_t h_dclose_t
  set R : F := γ t - γ t₀ - (t - t₀) • L with hR_def
  set D : F := deriv γ t - L with hD_def
  have hR_norm : ‖R‖ ≤ η * |t - t₀| := by rwa [Real.norm_eq_abs] at h_chord_t
  have hD_norm : ‖D‖ ≤ η := h_dclose_t.le
  have h_err_LD : |inner ℝ L D| ≤ ‖L‖ * η :=
    (abs_real_inner_le_norm L D).trans
      (mul_le_mul_of_nonneg_left hD_norm (norm_nonneg _))
  have h_err_RL : |inner ℝ R L| ≤ η * |t - t₀| * ‖L‖ :=
    (abs_real_inner_le_norm R L).trans
      (mul_le_mul_of_nonneg_right hR_norm (norm_nonneg _))
  have h_err_RD : |inner ℝ R D| ≤ η * |t - t₀| * η :=
    (abs_real_inner_le_norm R D).trans
      (mul_le_mul hR_norm hD_norm (norm_nonneg _) (by positivity))
  have h_err_tLD : |(t - t₀) * inner ℝ L D| ≤ |t - t₀| * (‖L‖ * η) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left h_err_LD (abs_nonneg _)
  have h_expand : inner ℝ (γ t - s) (deriv γ t) - (t - t₀) * ‖L‖ ^ 2 =
      (t - t₀) * inner ℝ L D + inner ℝ R L + inner ℝ R D := by
    rw [show γ t - s = (t - t₀) • L + R by rw [hR_def, h_at]; abel,
      show deriv γ t = L + D by rw [hD_def]; abel,
      inner_add_left, inner_add_right, inner_add_right,
      real_inner_smul_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    ring
  have h_eta_bound : 2 * η * ‖L‖ + η ^ 2 ≤ ‖L‖ ^ 2 / 2 := by
    rw [hη_def]
    nlinarith [hL_pos]
  rw [h_expand]
  calc |(t - t₀) * inner ℝ L D + inner ℝ R L + inner ℝ R D|
      ≤ |(t - t₀) * inner ℝ L D| + |inner ℝ R L| + |inner ℝ R D| := abs_add_three _ _ _
    _ ≤ |t - t₀| * (‖L‖ * η) + η * |t - t₀| * ‖L‖ + η * |t - t₀| * η := by gcongr
    _ ≤ |t - t₀| * ‖L‖ ^ 2 / 2 := by
        nlinarith [mul_le_mul_of_nonneg_left h_eta_bound (abs_nonneg (t - t₀))]

/-- A nonzero right-hand derivative limit at a continuous crossing makes distance from the
crossing point strictly increasing on a sufficiently small right interval. -/
theorem exists_strictMonoOn_norm_sub_right {γ : ℝ → F} {t₀ : ℝ} {s : F} (h_at : γ t₀ = s)
    {L : F} (hL : L ≠ 0) (hL_right : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L))
    (hγ_cont : ContinuousWithinAt γ (Ici t₀) t₀) :
    ∃ r > 0, StrictMonoOn (fun t => ‖γ t - s‖) (Icc t₀ (t₀ + r)) := by
  have h_ne := hL_right.eventually_ne hL
  have h_deriv := hasDerivWithinAt_Ioi_of_tendsto_deriv_of_ne_zero hγ_cont hL hL_right
  have h_combined : ∀ᶠ t in 𝓝[>] t₀, DifferentiableAt ℝ γ t ∧
      (t - t₀) * ‖L‖ ^ 2 / 2 ≤ inner ℝ (γ t - s) (deriv γ t) := by
    filter_upwards [h_ne, abs_inner_chord_deriv_sub_le h_at hL h_deriv hL_right,
      self_mem_nhdsWithin] with t h_ne_t h_abs ht
    rw [abs_of_pos (show 0 < t - t₀ from sub_pos.mpr ht)] at h_abs
    exact ⟨differentiableAt_of_deriv_ne_zero h_ne_t, by linarith [(abs_le.mp h_abs).1]⟩
  obtain ⟨c, hc, hr_data⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp h_combined
  refine ⟨c - t₀, sub_pos.mpr hc, ?_⟩
  rw [add_sub_cancel]
  have h_γ_continuousOn : ContinuousOn γ (Icc t₀ c) := fun t ht => by
    rcases eq_or_lt_of_le ht.1 with rfl | h_gt
    · exact hγ_cont.mono Icc_subset_Ici_self
    · exact (hr_data ⟨h_gt, ht.2⟩).1.continuousAt.continuousWithinAt
  have h_f_strictMono : StrictMonoOn (fun t => ‖γ t - s‖ ^ 2) (Icc t₀ c) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _)
      (f' := fun t => 2 * inner ℝ (γ t - s) (deriv γ t))
      (fun t ht => (((h_γ_continuousOn t ht).sub continuousWithinAt_const).norm).pow 2)
    · intro t ht
      rw [interior_Icc] at ht
      exact (((hr_data ⟨ht.1, ht.2.le⟩).1.hasDerivAt.sub_const s).norm_sq).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have hL_sq_pos : 0 < ‖L‖ ^ 2 := by positivity
      linarith [(hr_data ⟨ht.1, ht.2.le⟩).2, mul_pos (sub_pos.mpr ht.1) hL_sq_pos]
  exact fun a ha b hb hab =>
    lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) (h_f_strictMono ha hb hab)

/-- A nonzero left-hand derivative limit at a continuous crossing makes distance from the
crossing point strictly decreasing on a sufficiently small left interval. -/
theorem exists_strictAntiOn_norm_sub_left {γ : ℝ → F} {t₀ : ℝ} {s : F} (h_at : γ t₀ = s)
    {L : F} (hL : L ≠ 0) (hL_left : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L))
    (hγ_cont : ContinuousWithinAt γ (Iic t₀) t₀) :
    ∃ r > 0, StrictAntiOn (fun t => ‖γ t - s‖) (Icc (t₀ - r) t₀) := by
  have hL_right : Tendsto (deriv fun t => γ (-t)) (𝓝[>] (-t₀)) (𝓝 (-L)) :=
    (hL_left.comp tendsto_neg_nhdsGT_neg).neg.congr fun t => (deriv_comp_neg ..).symm
  have hγ_cont' : ContinuousWithinAt (fun t => γ (-t)) (Ici (-t₀)) (-t₀) :=
    hγ_cont.comp_of_eq continuous_neg.continuousWithinAt (fun x ht => show -x ≤ t₀ from neg_le_of_neg_le ht) (neg_neg t₀)
  obtain ⟨r, hr, hmono⟩ := exists_strictMonoOn_norm_sub_right (γ := fun t => γ (-t))
    (by simpa using h_at) (neg_ne_zero.mpr hL) hL_right hγ_cont'
  refine ⟨r, hr, fun a ha b hb hab => ?_⟩
  simpa using hmono ⟨neg_le_neg hb.2, by linarith [hb.1]⟩ ⟨neg_le_neg ha.2, by linarith [ha.1]⟩
    (neg_lt_neg hab)

end TauCeti.Contour

end

end
end Qatlib.Foundations.CbmdAnalysis.Residue
