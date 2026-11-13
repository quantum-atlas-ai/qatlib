/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Qatlib Contributors

Adapted from https://github.com/TauCetiProject/TauCeti@3780371c
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Chord.TangentBound
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.RegularityConditions
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Flatness forces tangent alignment

Shows that a flatness direction is collinear with an existing nonzero one-sided derivative. The
resulting `FlatOfOrder.tangentDeviation_isLittleO_right` and left-hand counterpart control
transverse displacement relative to the actual tangent.

These geometric estimates support the treatment of contour crossings in the analysis associated
with [WangEtAl2026].

## Main statements

* `FlatOfOrder.tangentDeviation_isLittleO_right`: Order-`n` flatness with `n ≥ 1` controls the
  right-hand tangent deviation by little-o of the `n`th power of the chord length, for a nonzero
  right derivative.
* `FlatOfOrder.tangentDeviation_isLittleO_left`: Order-`n` flatness with `n ≥ 1` controls the
  left-hand tangent deviation by little-o of the `n`th power of the chord length, for a nonzero
  left derivative.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

noncomputable section

namespace TauCeti.Contour

open Asymptotics Filter Set Topology

/-- For a curve with a right derivative and `n ≥ 1`, the `n`th power of its chord length is
eventually bounded by a positive constant times the parameter displacement. -/
private theorem eventually_norm_sub_pow_le_of_hasDerivWithinAt {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} {n : ℕ}
    (hn : 1 ≤ n) (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t in 𝓝[>] t₀, ‖γ t - γ t₀‖ ^ n ≤ C * (t - t₀) := by
  obtain ⟨c, hc, hbound⟩ := (h_deriv.hasFDerivWithinAt.isBigO_sub).exists_pos
  refine ⟨c ^ n, by positivity, ?_⟩
  have h_small : ∀ᶠ t in 𝓝[>] t₀, t - t₀ ≤ 1 := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds
      (eventually_le_nhds (by linarith : t₀ < t₀ + 1))] with t ht
    linarith
  filter_upwards [hbound.bound, h_small, self_mem_nhdsWithin] with t hb hs ht
  have ht' : 0 < t - t₀ := sub_pos.mpr ht
  rw [Real.norm_of_nonneg ht'.le] at hb
  calc ‖γ t - γ t₀‖ ^ n ≤ (c * (t - t₀)) ^ n := by gcongr
    _ = c ^ n * (t - t₀) ^ n := by rw [mul_pow]
    _ ≤ c ^ n * (t - t₀) := by
        gcongr
        exact pow_le_of_le_one ht'.le hs (by omega : n ≠ 0)

/-- Bounds the transverse component of a candidate tangent times the positive parameter
displacement by the curve's transverse displacement and linearization error. -/
private theorem abs_im_mul_conj_div_mul_le_of_sub_smul {γ : ℝ → ℂ} {t₀ : ℝ} {v L : ℂ} {t : ℝ}
    (hv : v ≠ 0) (ht' : 0 < t - t₀) :
    |(L * starRingEnd ℂ v).im| / ‖v‖ * (t - t₀) ≤
      |((γ t - γ t₀) * star v).im| / ‖v‖ + ‖γ t - γ t₀ - (t - t₀) • L‖ := by
  rw [Complex.star_def, ← norm_tangentDeviation hv, ← norm_tangentDeviation hv]
  have hstep : ‖tangentDeviation L v‖ * (t - t₀) =
      ‖tangentDeviation ((t - t₀) • L) v‖ := by
    rw [tangentDeviation_real_smul, norm_smul, Real.norm_of_nonneg ht'.le]; ring
  have hdev : tangentDeviation ((t - t₀) • L) v =
      tangentDeviation (γ t - γ t₀) v - tangentDeviation (γ t - γ t₀ - (t - t₀) • L) v :=
    (congrArg (tangentDeviation · v) (by abel : ((t - t₀) • L : ℂ) =
      (γ t - γ t₀) - (γ t - γ t₀ - (t - t₀) • L))).trans (tangentDeviation_sub _ _ _)
  rw [hstep, hdev]
  refine (norm_sub_le _ _).trans ?_
  gcongr
  exact norm_tangentDeviation_le _ _

/-- A right-hand flatness estimate of positive order bounds the normalized transverse component
of the derivative by every positive `ε`. -/
private theorem abs_im_mul_conj_div_le_of_isLittleO {γ : ℝ → ℂ} {t₀ : ℝ} {v L : ℂ} {n : ℕ}
    (hv : v ≠ 0) (hn : 1 ≤ n) (h_dev : (fun t => |((γ t - γ t₀) * star v).im| / ‖v‖) =o[𝓝[>] t₀]
      fun t => ‖γ t - γ t₀‖ ^ n)
    (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) {ε : ℝ} (hε : 0 < ε) :
    |(L * starRingEnd ℂ v).im| / ‖v‖ ≤ ε := by
  set c : ℝ := |(L * starRingEnd ℂ v).im| / ‖v‖ with _
  have herr : (fun t => γ t - γ t₀ - (t - t₀) • L) =o[𝓝[>] t₀] (fun t => t - t₀) :=
    hasDerivWithinAt_iff_isLittleO.mp h_deriv
  obtain ⟨C, hC, h_pow⟩ := eventually_norm_sub_pow_le_of_hasDerivWithinAt hn h_deriv
  set ε' : ℝ := ε / (2 * C) with hε'_def
  have hε' : 0 < ε' := by positivity
  have h_dev_bound := (isLittleO_iff.mp h_dev) hε'
  have h_err_bound := (isLittleO_iff.mp herr) (c := ε / 2) (by positivity)
  have h_all : ∀ᶠ t in 𝓝[>] t₀, c * (t - t₀) ≤ ε * (t - t₀) := by
    filter_upwards [h_dev_bound, h_err_bound, h_pow, self_mem_nhdsWithin] with t hd he hp ht
    have ht' : 0 < t - t₀ := sub_pos.mpr ht
    have h_tri := abs_im_mul_conj_div_mul_le_of_sub_smul (γ := γ) (L := L) hv ht'
    rw [Real.norm_eq_abs, abs_of_pos ht'] at he
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hd
    have hd' : |((γ t - γ t₀) * star v).im| / ‖v‖ ≤ ε' * (C * (t - t₀)) := by
      calc |((γ t - γ t₀) * star v).im| / ‖v‖ ≤ ε' * ‖γ t - γ t₀‖ ^ n := by
            simpa [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) n)] using hd
        _ ≤ ε' * (C * (t - t₀)) := by gcongr
    have hε'_eq : ε' * C = ε / 2 := by
      rw [hε'_def]
      field_simp
    calc c * (t - t₀) ≤ |((γ t - γ t₀) * star v).im| / ‖v‖ +
          ‖γ t - γ t₀ - (t - t₀) • L‖ := h_tri
      _ ≤ ε' * (C * (t - t₀)) + ε / 2 * (t - t₀) := by
          gcongr
      _ = ε * (t - t₀) := by rw [← mul_assoc, hε'_eq]; ring
  obtain ⟨t, hct, ht⟩ := (h_all.and self_mem_nhdsWithin).exists
  exact le_of_mul_le_mul_right hct (sub_pos.mpr ht)

/-- A right derivative is collinear with any nonzero direction satisfying the stated right-hand
flatness estimate of positive order. -/
private theorem im_mul_conj_eq_zero_of_flat_right {γ : ℝ → ℂ} {t₀ : ℝ} {v L : ℂ} {n : ℕ}
    (hv : v ≠ 0) (hn : 1 ≤ n) (h_dev : (fun t => |((γ t - γ t₀) * star v).im| / ‖v‖) =o[𝓝[>] t₀]
      fun t => ‖γ t - γ t₀‖ ^ n)
    (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) :
    (L * starRingEnd ℂ v).im = 0 := by
  have hv_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set c : ℝ := |(L * starRingEnd ℂ v).im| / ‖v‖ with hc_def
  have hc_nonneg : 0 ≤ c := by positivity
  have hc_le : ∀ ε : ℝ, 0 < ε → c ≤ ε :=
    fun ε hε => abs_im_mul_conj_div_le_of_isLittleO hv hn h_dev h_deriv hε
  rcases eq_or_lt_of_le hc_nonneg with h0 | hpos
  · have h' : |(L * starRingEnd ℂ v).im| / ‖v‖ = 0 := by rw [← hc_def, ← h0]
    exact abs_eq_zero.mp ((div_eq_zero_iff.mp h').resolve_right hv_pos.ne')
  · exact absurd (hc_le (c / 2) (by linarith)) (by linarith)

/-- A left derivative is collinear with any nonzero direction satisfying the stated left-hand
flatness estimate of positive order. -/
private theorem im_mul_conj_eq_zero_of_flat_left {γ : ℝ → ℂ} {t₀ : ℝ} {v L : ℂ} {n : ℕ}
    (hv : v ≠ 0) (hn : 1 ≤ n) (h_dev : (fun t => |((γ t - γ t₀) * star v).im| / ‖v‖) =o[𝓝[<] t₀]
      fun t => ‖γ t - γ t₀‖ ^ n)
    (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) :
    (L * starRingEnd ℂ v).im = 0 := by
  have ht₀ : 2 * t₀ - t₀ = t₀ := by ring
  have hσ : Tendsto (fun t => 2 * t₀ - t) (𝓝[>] t₀) (𝓝[<] t₀) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun t : ℝ => 2 * t₀ - t) (𝓝 t₀) (𝓝 (2 * t₀ - t₀)) :=
        tendsto_const_nhds.sub tendsto_id
      rw [ht₀] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [mem_Iio]
      linarith [mem_Ioi.mp ht]
  have h_dev' : (fun t => |((γ (2 * t₀ - t) - γ (2 * t₀ - t₀)) * star v).im| / ‖v‖)
      =o[𝓝[>] t₀] fun t => ‖γ (2 * t₀ - t) - γ (2 * t₀ - t₀)‖ ^ n := by
    rw [ht₀]
    exact h_dev.comp_tendsto hσ
  have h_deriv' : HasDerivWithinAt (fun t => γ (2 * t₀ - t)) (-L) (Ioi t₀) t₀ := by
    have hg : HasDerivWithinAt γ L (Iio t₀) (2 * t₀ - t₀) := by
      rw [ht₀]
      exact h_deriv
    have hh : HasDerivWithinAt (fun t : ℝ => 2 * t₀ - t) (-1) (Ioi t₀) t₀ :=
      (hasDerivWithinAt_id t₀ (Ioi t₀)).const_sub (2 * t₀)
    have h := hg.scomp t₀ hh fun t ht => by
      simp only [mem_Iio]
      linarith [mem_Ioi.mp ht]
    rw [neg_one_smul] at h
    exact h
  have h_im := im_mul_conj_eq_zero_of_flat_right hv hn h_dev' h_deriv'
  rw [neg_mul, Complex.neg_im, neg_eq_zero] at h_im
  exact h_im

/-- Transfers a transverse little-o estimate from a nonzero direction to a collinear nonzero
tangent direction. -/
private theorem tangentDeviation_isLittleO_of_im_mul_conj_eq_zero {γ : ℝ → ℂ} {t₀ : ℝ}
    {v L : ℂ} {n : ℕ} {l : Filter ℝ} (hv : v ≠ 0) (hL : L ≠ 0) (h_im : (L * starRingEnd ℂ v).im = 0)
    (h_dev : (fun t => |((γ t - γ t₀) * star v).im| / ‖v‖) =o[l]
      fun t => ‖γ t - γ t₀‖ ^ n) :
    (fun t => ‖tangentDeviation (γ t - γ t₀) L‖) =o[l]
      fun t => ‖γ t - γ t₀‖ ^ n := by
  obtain ⟨cc, hcc⟩ := (im_mul_conj_eq_zero_iff_exists_real_smul hv).1 h_im
  have hcc_ne : cc ≠ 0 := fun h0 => hL (by rw [hcc, h0, zero_smul])
  have hkey : ∀ t, ‖tangentDeviation (γ t - γ t₀) L‖ =
      |((γ t - γ t₀) * star v).im| / ‖v‖ := fun t => by
    rw [hcc, tangentDeviation_real_smul_right hcc_ne, norm_tangentDeviation hv,
      Complex.star_def]
  exact h_dev.congr' (Filter.Eventually.of_forall fun t => (hkey t).symm) Filter.EventuallyEq.rfl

/-- Order-`n` flatness with `n ≥ 1` controls the right-hand tangent deviation by little-o of the
`n`th power of the chord length, for a nonzero right derivative. -/
theorem FlatOfOrder.tangentDeviation_isLittleO_right {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} {n : ℕ}
    (hflat : FlatOfOrder γ t₀ n) (hn : 1 ≤ n) (hL : L ≠ 0)
    (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) :
    (fun t => ‖tangentDeviation (γ t - γ t₀) L‖) =o[𝓝[>] t₀]
      fun t => ‖γ t - γ t₀‖ ^ n := by
  obtain ⟨vp, vm, hvp, _, hr, -⟩ := flatOfOrder_iff.mp hflat
  exact tangentDeviation_isLittleO_of_im_mul_conj_eq_zero hvp hL
    (im_mul_conj_eq_zero_of_flat_right hvp hn hr h_deriv) hr

/-- Order-`n` flatness with `n ≥ 1` controls the left-hand tangent deviation by little-o of the
`n`th power of the chord length, for a nonzero left derivative. -/
theorem FlatOfOrder.tangentDeviation_isLittleO_left {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} {n : ℕ}
    (hflat : FlatOfOrder γ t₀ n) (hn : 1 ≤ n) (hL : L ≠ 0)
    (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) :
    (fun t => ‖tangentDeviation (γ t - γ t₀) L‖) =o[𝓝[<] t₀]
      fun t => ‖γ t - γ t₀‖ ^ n := by
  obtain ⟨vp, vm, _, hvm, -, hl⟩ := flatOfOrder_iff.mp hflat
  exact tangentDeviation_isLittleO_of_im_mul_conj_eq_zero hvm hL
    (im_mul_conj_eq_zero_of_flat_left hvm hn hl h_deriv) hl

end TauCeti.Contour

end

end
end Qatlib.Foundations.CbmdAnalysis.Residue
