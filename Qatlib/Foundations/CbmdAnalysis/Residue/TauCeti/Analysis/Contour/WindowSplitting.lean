/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Cauchy.PrincipalValue.Basic
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Crossing.Monotonicity
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Crossing.Windows
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Curve.Distance
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.ExitTime

/-!
# Splitting truncated contour integrals at exit times

Constructs radius-dependent exit times on both sides of a unique contour crossing with nonzero
one-sided derivative limits. Radial monotonicity and integrability then split the truncated
contour integral into ordinary integrals outside the exit times.

`exists_exit_times_truncated_integral_split` supports the local principal-value analysis
associated with [WangEtAl2026].

## Main statements

* `exists_exit_times_truncated_integral_split`: At a unique crossing with nonzero one-sided
  derivative limits, constructs equal-radius exit times tending to the crossing and an eventual
  splitting of the truncated integral into the two outer integrals.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

noncomputable section

namespace TauCeti.Contour

open Filter MeasureTheory Set Topology

/-- Radial truncation leaves the integral unchanged when the curve is almost everywhere farther
than `ε` from the reference point. -/
private theorem integral_truncated_eq_of_ae_gt {γ : ℝ → ℂ} {g : ℂ → ℂ} {s : ℂ} {l u ε : ℝ}
    (hlu : l ≤ u) (h_gt : ∀ᵐ t ∂MeasureTheory.volume, t ∈ Ioc l u → ε < ‖γ t - s‖) :
    ∫ t in l..u, (if ‖γ t - s‖ > ε then g (γ t) * deriv γ t else 0) =
      ∫ t in l..u, g (γ t) * deriv γ t := by
  refine intervalIntegral.integral_congr_ae ?_
  rw [uIoc_of_le hlu]
  filter_upwards [h_gt] with t ht htm
  rw [if_pos (ht htm)]

/-- A continuous curve with nonzero one-sided derivative limits at a crossing has a smaller
parameter window where distance from the crossing is strictly increasing to the right and
strictly decreasing to the left. -/
private theorem exists_monotone_leave_radius {γ : ℝ → ℂ} {s : ℂ} {t₀ r : ℝ}
    {L_R L_L : ℂ} (hr_pos : 0 < r) (h_at : γ t₀ = s)
    (hγ_cont : ContinuousOn γ (Icc (t₀ - r) (t₀ + r))) (hL_R : L_R ≠ 0) (hL_L : L_L ≠ 0)
    (h_tendsto_R : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L_R))
    (h_tendsto_L : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L_L)) :
    ∃ ρ > 0, ρ ≤ r ∧
      StrictMonoOn (fun t => ‖γ t - s‖) (Icc t₀ (t₀ + ρ)) ∧
      StrictAntiOn (fun t => ‖γ t - s‖) (Icc (t₀ - ρ) t₀) ∧
      (∀ t ∈ Ioc t₀ (t₀ + ρ), γ t ≠ s) ∧
      (∀ t ∈ Ico (t₀ - ρ) t₀, γ t ≠ s) := by
  have hγ_at : ContinuousAt γ t₀ :=
    hγ_cont.continuousAt (Icc_mem_nhds (by linarith) (by linarith))
  obtain ⟨r_R, hr_R_pos, hmono_raw⟩ :=
    exists_strictMonoOn_norm_sub_right h_at hL_R h_tendsto_R hγ_at.continuousWithinAt
  obtain ⟨r_L, hr_L_pos, hanti_raw⟩ :=
    exists_strictAntiOn_norm_sub_left h_at hL_L h_tendsto_L hγ_at.continuousWithinAt
  set ρ : ℝ := min r (min r_R r_L) with _
  have hρ_pos : 0 < ρ := lt_min hr_pos (lt_min hr_R_pos hr_L_pos)
  have hρ_R : ρ ≤ r_R := (min_le_right _ _).trans (min_le_left _ _)
  have hρ_L : ρ ≤ r_L := (min_le_right _ _).trans (min_le_right _ _)
  have hmono : StrictMonoOn (fun t => ‖γ t - s‖) (Icc t₀ (t₀ + ρ)) :=
    hmono_raw.mono (Icc_subset_Icc le_rfl (by linarith))
  have hanti : StrictAntiOn (fun t => ‖γ t - s‖) (Icc (t₀ - ρ) t₀) :=
    hanti_raw.mono (Icc_subset_Icc (by linarith) le_rfl)
  refine ⟨ρ, hρ_pos, min_le_left _ _, hmono, hanti, ?_, ?_⟩
  · intro t ht heq
    have h_strict : ‖γ t₀ - s‖ < ‖γ t - s‖ :=
      hmono ⟨le_rfl, by linarith [ht.1]⟩ ⟨ht.1.le, ht.2⟩ ht.1
    rw [h_at, heq, sub_self, norm_zero] at h_strict
    exact absurd h_strict (lt_irrefl 0)
  · intro t ht heq
    have h_strict : ‖γ t₀ - s‖ < ‖γ t - s‖ :=
      hanti ⟨ht.1, ht.2.le⟩ ⟨by linarith [ht.2], le_rfl⟩ ht.2
    rw [h_at, heq, sub_self, norm_zero] at h_strict
    exact absurd h_strict (lt_irrefl 0)

/-- The radially truncated integral vanishes between two radius-`ε` exit points when distance is
monotone on either side of the crossing. -/
private theorem integral_truncated_eq_zero_between_exits {γ : ℝ → ℂ} {g : ℂ → ℂ} {s : ℂ}
    {t₀ ρ ε cₗ cᵣ : ℝ} (hmono : MonotoneOn (fun t => ‖γ t - s‖) (Icc t₀ (t₀ + ρ)))
    (hanti : AntitoneOn (fun t => ‖γ t - s‖) (Icc (t₀ - ρ) t₀))
    (hcₗ : cₗ ∈ Ioo (t₀ - ρ) t₀) (hcᵣ : cᵣ ∈ Ioo t₀ (t₀ + ρ))
    (hεₗ : ‖γ cₗ - s‖ = ε) (hεᵣ : ‖γ cᵣ - s‖ = ε) :
    ∫ u in cₗ..cᵣ, (if ‖γ u - s‖ > ε then g (γ u) * deriv γ u else 0) = 0 := by
  refine (intervalIntegrable_truncated_and_integral_truncated_eq_zero_of_norm_le
    (g := fun t => g (γ t) * deriv γ t) (Filter.Eventually.of_forall fun t ht => ?_)).2
  rw [uIoc_of_le (le_of_lt (hcₗ.2.trans hcᵣ.1))] at ht
  rcases lt_trichotomy t t₀ with h_lt | h_eq | h_ge
  · have h_bd : ‖γ t - s‖ ≤ ‖γ cₗ - s‖ :=
      hanti ⟨hcₗ.1.le, hcₗ.2.le⟩ ⟨le_trans hcₗ.1.le ht.1.le, h_lt.le⟩ ht.1.le
    rwa [hεₗ] at h_bd
  · rw [h_eq]
    have h_bd : ‖γ t₀ - s‖ ≤ ‖γ cₗ - s‖ :=
      hanti ⟨hcₗ.1.le, hcₗ.2.le⟩ ⟨by linarith [hcₗ.1, hcₗ.2], le_rfl⟩ hcₗ.2.le
    rwa [hεₗ] at h_bd
  · have h_bd : ‖γ t - s‖ ≤ ‖γ cᵣ - s‖ :=
      hmono ⟨h_ge.le, le_trans ht.2 hcᵣ.2.le⟩ ⟨hcᵣ.1.le, hcᵣ.2.le⟩ ht.2
    rwa [hεᵣ] at h_bd

/-- On the interval ending at a left exit point, radial truncation leaves the integral unchanged
under strict radial decrease near the crossing and a larger distance bound farther away. -/
private theorem integral_truncated_eq_of_left_exit {γ : ℝ → ℂ} {g : ℂ → ℂ} {s : ℂ}
    {t₀ ρ l m ε cₗ : ℝ} (h_lb : l ≤ cₗ) (hcₗ : cₗ ∈ Ioo (t₀ - ρ) t₀)
    (hεₗ : ‖γ cₗ - s‖ = ε) (hεm : ε < m)
    (hanti : StrictAntiOn (fun t => ‖γ t - s‖) (Icc (t₀ - ρ) t₀))
    (h_far : ∀ t ∈ Icc l (t₀ - ρ), m ≤ ‖γ t - s‖) :
    ∫ u in l..cₗ, (if ‖γ u - s‖ > ε then g (γ u) * deriv γ u else 0) =
      ∫ u in l..cₗ, g (γ u) * deriv γ u := by
  refine integral_truncated_eq_of_ae_gt h_lb ?_
  filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr
    (MeasureTheory.measure_singleton cₗ)] with t h_ne ht
  have h_t_lt : t < cₗ := lt_of_le_of_ne ht.2 h_ne
  rcases lt_or_ge t (t₀ - ρ) with h_lt | h_ge
  · exact lt_of_lt_of_le hεm (h_far t ⟨ht.1.le, h_lt.le⟩)
  · have h_bd : ‖γ cₗ - s‖ < ‖γ t - s‖ :=
      hanti ⟨h_ge, by linarith [hcₗ.2, h_t_lt]⟩ ⟨hcₗ.1.le, hcₗ.2.le⟩ h_t_lt
    rwa [hεₗ] at h_bd

/-- On the interval starting at a right exit point, radial truncation leaves the integral
unchanged under strict radial increase near the crossing and a larger distance bound farther
away. -/
private theorem integral_truncated_eq_of_right_exit {γ : ℝ → ℂ} {g : ℂ → ℂ} {s : ℂ}
    {t₀ ρ u m ε cᵣ : ℝ} (h_ub : cᵣ ≤ u) (hcᵣ : cᵣ ∈ Ioo t₀ (t₀ + ρ))
    (hεᵣ : ‖γ cᵣ - s‖ = ε) (hεm : ε < m)
    (hmono : StrictMonoOn (fun t => ‖γ t - s‖) (Icc t₀ (t₀ + ρ)))
    (h_far : ∀ t ∈ Icc (t₀ + ρ) u, m ≤ ‖γ t - s‖) :
    ∫ v in cᵣ..u, (if ‖γ v - s‖ > ε then g (γ v) * deriv γ v else 0) =
      ∫ v in cᵣ..u, g (γ v) * deriv γ v := by
  refine integral_truncated_eq_of_ae_gt h_ub (Eventually.of_forall fun t ht => ?_)
  rcases le_or_gt t (t₀ + ρ) with h_le | h_gt
  · have h_bd : ‖γ cᵣ - s‖ < ‖γ t - s‖ :=
      hmono ⟨hcᵣ.1.le, hcᵣ.2.le⟩ ⟨by linarith [hcᵣ.1, ht.1], h_le⟩ ht.1
    rwa [hεᵣ] at h_bd
  · exact lt_of_lt_of_le hεm (h_far t ⟨h_gt.le, ht.2⟩)

/-- Splits an integrable radially truncated integral into two untruncated outer integrals at
exit points, using radial monotonicity and distance bounds away from the crossing. -/
private theorem integral_truncated_eq_add_of_exit_points {γ : ℝ → ℂ} {g : ℂ → ℂ} {s : ℂ}
    {t₀ ρ l u m ε cₗ cᵣ : ℝ} (h_lb : l ≤ cₗ) (h_ub : cᵣ ≤ u)
    (hmono : StrictMonoOn (fun t => ‖γ t - s‖) (Icc t₀ (t₀ + ρ)))
    (hanti : StrictAntiOn (fun t => ‖γ t - s‖) (Icc (t₀ - ρ) t₀))
    (h_far_L : ∀ t ∈ Icc l (t₀ - ρ), m ≤ ‖γ t - s‖)
    (h_far_R : ∀ t ∈ Icc (t₀ + ρ) u, m ≤ ‖γ t - s‖)
    (hcₗ : cₗ ∈ Ioo (t₀ - ρ) t₀) (hcᵣ : cᵣ ∈ Ioo t₀ (t₀ + ρ))
    (hεₗ : ‖γ cₗ - s‖ = ε) (hεᵣ : ‖γ cᵣ - s‖ = ε) (hεm : ε < m)
    (h_int_left : IntervalIntegrable
      (fun t => if ‖γ t - s‖ > ε then g (γ t) * deriv γ t else 0)
      MeasureTheory.volume l cₗ)
    (h_int_mid : IntervalIntegrable
      (fun t => if ‖γ t - s‖ > ε then g (γ t) * deriv γ t else 0) MeasureTheory.volume cₗ cᵣ)
    (h_int_right : IntervalIntegrable
      (fun t => if ‖γ t - s‖ > ε then g (γ t) * deriv γ t else 0)
      MeasureTheory.volume cᵣ u) :
    ∫ v in l..u, (if ‖γ v - s‖ > ε then g (γ v) * deriv γ v else 0) =
      (∫ v in l..cₗ, g (γ v) * deriv γ v) +
        (∫ v in cᵣ..u, g (γ v) * deriv γ v) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (h_int_left.trans h_int_mid) h_int_right,
    ← intervalIntegral.integral_add_adjacent_intervals h_int_left h_int_mid,
    integral_truncated_eq_zero_between_exits hmono.monotoneOn hanti.antitoneOn hcₗ hcᵣ hεₗ hεᵣ,
    add_zero,
    integral_truncated_eq_of_left_exit h_lb hcₗ hεₗ hεm hanti h_far_L,
    integral_truncated_eq_of_right_exit h_ub hcᵣ hεᵣ hεm hmono h_far_R]

/-- At a unique crossing with nonzero one-sided derivative limits, constructs equal-radius exit
times tending to the crossing and an eventual splitting of the truncated integral into the
two outer integrals. -/
theorem exists_exit_times_truncated_integral_split {γ : ℝ → ℂ} {s : ℂ} {l t₀ u : ℝ}
    {L_R L_L : ℂ} (hlt : l < t₀) (htu : t₀ < u) (h_at : γ t₀ = s)
    (hγ_cont : ContinuousOn γ (Icc l u)) (hL_R : L_R ≠ 0) (hL_L : L_L ≠ 0)
    (h_tendsto_R : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L_R))
    (h_tendsto_L : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L_L))
    (h_unique : ∀ t ∈ Icc l u, γ t = s → t = t₀) (g : ℂ → ℂ)
    (h_int : ∀ ε : ℝ, 0 < ε → ∀ a b : ℝ, l ≤ a → a ≤ b → b ≤ u →
      IntervalIntegrable (fun t => if ‖γ t - s‖ > ε then g (γ t) * deriv γ t else 0)
        MeasureTheory.volume a b) :
    ∃ τL τR : ℝ → ℝ,
      Tendsto τL (𝓝[>] (0 : ℝ)) (𝓝[<] t₀) ∧
      Tendsto τR (𝓝[>] (0 : ℝ)) (𝓝[>] t₀) ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖γ (τL ε) - s‖ = ε) ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖γ (τR ε) - s‖ = ε) ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), τL ε ∈ Ioo l t₀) ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), τR ε ∈ Ioo t₀ u) ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ),
        ∫ v in l..u, (if ‖γ v - s‖ > ε then g (γ v) * deriv γ v else 0) =
          (∫ v in l..(τL ε), g (γ v) * deriv γ v) +
          (∫ v in (τR ε)..u, g (γ v) * deriv γ v)) := by
  classical
  let r := min (t₀ - l) (u - t₀)
  have hr_pos : 0 < r := lt_min (sub_pos.mpr hlt) (sub_pos.mpr htu)
  have hlr : l ≤ t₀ - r := by
    dsimp [r]
    linarith [min_le_left (t₀ - l) (u - t₀)]
  have hru : t₀ + r ≤ u := by
    dsimp [r]
    linarith [min_le_right (t₀ - l) (u - t₀)]
  have hγ_cont' : ContinuousOn γ (Icc (t₀ - r) (t₀ + r)) :=
    hγ_cont.mono (Icc_subset_Icc hlr hru)
  obtain ⟨ρ, hρ_pos, hρ_le_r, hmono, hanti, h_leave_R, h_leave_L⟩ :=
    exists_monotone_leave_radius hr_pos h_at hγ_cont' hL_R hL_L h_tendsto_R h_tendsto_L
  have hγ_cont_R : ContinuousOn γ (Icc t₀ (t₀ + ρ)) :=
    hγ_cont.mono (Icc_subset_Icc hlt.le (by linarith [hρ_le_r, hru]))
  have hγ_cont_L : ContinuousOn γ (Icc (t₀ - ρ) t₀) :=
    hγ_cont.mono (Icc_subset_Icc (by linarith [hρ_le_r, hlr]) htu.le)
  set τL := firstExitTimeLeft γ t₀ ρ s with _
  set τR := firstExitTimeRight γ t₀ ρ s with _
  have h_toL : Tendsto τL (𝓝[>] (0 : ℝ)) (𝓝[<] t₀) :=
    firstExitTimeLeft_tendsto hρ_pos hγ_cont_L h_at h_leave_L
  have h_toR : Tendsto τR (𝓝[>] (0 : ℝ)) (𝓝[>] t₀) :=
    firstExitTimeRight_tendsto hρ_pos hγ_cont_R h_at h_leave_R
  have h_radL : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖γ (τL ε) - s‖ = ε :=
    eventually_norm_at_firstExitTimeLeft_eq hρ_pos.le hγ_cont_L h_at
      (h_leave_L _ ⟨le_rfl, by linarith⟩)
  have h_radR : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖γ (τR ε) - s‖ = ε :=
    eventually_norm_at_firstExitTimeRight_eq hρ_pos.le hγ_cont_R h_at
      (h_leave_R _ ⟨by linarith, le_rfl⟩)
  have h_memL : ∀ᶠ ε in 𝓝[>] (0 : ℝ), τL ε ∈ Ioo (t₀ - ρ) t₀ :=
    h_toL (Ioo_mem_nhdsLT (by linarith))
  have h_memR : ∀ᶠ ε in 𝓝[>] (0 : ℝ), τR ε ∈ Ioo t₀ (t₀ + ρ) :=
    h_toR (Ioo_mem_nhdsGT (by linarith))
  refine ⟨τL, τR, h_toL, h_toR, h_radL, h_radR,
    h_memL.mono fun ε hε => ⟨by linarith [hε.1], hε.2⟩,
    h_memR.mono fun ε hε => ⟨hε.1, by linarith [hε.2]⟩, ?_⟩
  obtain ⟨mL, hmL_pos, h_far_L⟩ := exists_curve_dist_lower_bound
    (a := l) (b := t₀ - ρ) (w := s)
    (hγ_cont.mono (by rw [uIcc_of_le (by linarith)]; exact Icc_subset_Icc le_rfl (by linarith)))
    (fun t ht h_eq => by
      rw [uIcc_of_le (by linarith)] at ht
      have ht_eq := h_unique t ⟨ht.1, by linarith [ht.2, hρ_pos, htu]⟩ h_eq
      linarith [ht.2])
  obtain ⟨mR, hmR_pos, h_far_R⟩ := exists_curve_dist_lower_bound
    (a := t₀ + ρ) (b := u) (w := s)
    (hγ_cont.mono (by rw [uIcc_of_le (by linarith)]; exact Icc_subset_Icc (by linarith) le_rfl))
    (fun t ht h_eq => by
      rw [uIcc_of_le (by linarith)] at ht
      have ht_eq := h_unique t ⟨by linarith [ht.1, hρ_pos, hlt], ht.2⟩ h_eq
      linarith [ht.1])
  let m := min mL mR
  have hm_pos : 0 < m := lt_min hmL_pos hmR_pos
  filter_upwards [h_radL, h_radR, h_memL, h_memR, Ioo_mem_nhdsGT hm_pos]
    with ε hεL hεR hτL hτR hεm
  have h_lb : l ≤ τL ε := by linarith [hτL.1, hρ_le_r, hlr]
  have h_mid_le : τL ε ≤ τR ε := by linarith [hτL.2, hτR.1]
  have h_ub : τR ε ≤ u := by linarith [hτR.2, hρ_le_r, hru]
  exact integral_truncated_eq_add_of_exit_points h_lb h_ub hmono hanti
    (fun t ht => (min_le_left mL mR).trans (h_far_L t (by rwa [uIcc_of_le (by linarith)])))
    (fun t ht => (min_le_right mL mR).trans (h_far_R t (by rwa [uIcc_of_le (by linarith)])))
    hτL hτR hεL hεR hεm.2
    (h_int ε hεm.1 l (τL ε) le_rfl h_lb (by linarith [hτL.2, htu]))
    (h_int ε hεm.1 (τL ε) (τR ε) h_lb h_mid_le h_ub)
    (h_int ε hεm.1 (τR ε) u (h_lb.trans h_mid_le) h_ub le_rfl)

end TauCeti.Contour

end

end
end Qatlib.Foundations.CbmdAnalysis.Residue
