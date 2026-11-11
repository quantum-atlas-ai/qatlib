/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Mathlib.Topology.MetricSpace.Bounded
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Winding.LocallyConstant
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Winding.Vanishing
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Topology.FilledHull
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.Basic

/-!
# Winding numbers on unbounded complementary components

Proves vanishing winding numbers on unbounded connected components of a curve's complement. For
closed piecewise C1 curves, an avoiding ray implies vanishing, and containment in a set
containing its filled hull implies null homology.

These geometric criteria support residue arguments associated with [WangEtAl2026].

## Main statements

* `windingNumber_eq_zero_of_unbounded_component`: The winding number of a closed continuous
  curve vanishes at points in unbounded complementary components, under the stated
  countable-exception differentiability and derivative integrability hypotheses.
* `IsPiecewiseC1On.windingNumber_eq_zero_of_ray`: The winding number of a closed piecewise C1
  curve about `w` is zero if a ray from `w` in a nonzero direction avoids the image.
* `IsPiecewiseC1On.isNullHomologous_of_filledHull_subset`: A closed piecewise C1 curve contained
  in a set that contains its filled hull is null homologous in that set.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

open Bornology Complex MeasureTheory _root_.Set

open scoped Topology

namespace TauCeti.Contour

/-- For a continuous curve with interval-integrable derivative and integer winding numbers off
its image, the winding number vanishes on every unbounded connected component of the
complement. -/
theorem _root_.Qatlib.Foundations.CbmdAnalysis.Residue.ContinuousOn.windingNumber_eq_zero_of_unbounded_component_of_integer
    {γ : ℝ → ℂ} {a b : ℝ} (hγ : ContinuousOn γ (uIcc a b))
    (hderiv : IntervalIntegrable (deriv γ) volume a b)
    (hint : ∀ z, z ∉ γ '' uIcc a b → ∃ n : ℤ, windingNumber γ a b z = n)
    {z : ℂ} (hz : ¬IsBounded (connectedComponentIn ((γ '' uIcc a b)ᶜ) z)) :
    windingNumber γ a b z = 0 := by
  obtain ⟨K, hK, hKgood⟩ := Filter.mem_cocompact.mp
    (ContinuousOn.windingNumber_eventually_zero_cocompact_of_integer hγ hderiv hint)
  have hnot : ¬connectedComponentIn ((γ '' uIcc a b)ᶜ) z ⊆ K :=
    fun hsubset ↦ hz (hK.isBounded.subset hsubset)
  obtain ⟨w, hw, hwK⟩ := Set.not_subset.mp hnot
  exact (ContinuousOn.windingNumber_eq_of_mem_connectedComponentIn_of_integer hγ hderiv hint hw).symm.trans
    (hKgood hwK).2

/-- The winding number of a closed continuous curve vanishes at points in unbounded
complementary components, under the stated countable-exception differentiability and
derivative integrability hypotheses. -/
theorem windingNumber_eq_zero_of_unbounded_component {γ : ℝ → ℂ} {a b : ℝ} {P : Set ℝ}
    (hclosed : γ a = γ b) (hP : P.Countable) (hγ_cont : ContinuousOn γ (uIcc a b))
    (hγ_diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t)
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b)
    {w : ℂ} (hcomp : ¬IsBounded (connectedComponentIn ((γ '' uIcc a b)ᶜ) w)) :
    windingNumber γ a b w = 0 := by
  have hac := ContinuousOn.absolutelyContinuousOnInterval_of_hasDerivAt_off_countable hγ_cont hP
    (fun t ht ↦ (hγ_diff t ht).hasDerivAt) hderiv_int
  exact ContinuousOn.windingNumber_eq_zero_of_unbounded_component_of_integer hγ_cont hderiv_int
    (fun _ hz ↦ AbsolutelyContinuousOnInterval.exists_int_windingNumber hac hclosed hz) hcomp

/-- The winding number of a closed piecewise C1 curve vanishes at points in unbounded connected
components of its image complement. -/
theorem _root_.Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.IsPiecewiseC1On.windingNumber_eq_zero_of_unbounded_component
    {γ : ℝ → ℂ} {a b : ℝ} (hγ : IsPiecewiseC1On γ a b) (hclosed : γ a = γ b)
    {w : ℂ} (hcomp : ¬IsBounded (connectedComponentIn ((γ '' uIcc a b)ᶜ) w)) :
    windingNumber γ a b w = 0 := by
  obtain ⟨P, hP, hγ_diff⟩ := hγ.exists_countable_differentiableAt
  exact TauCeti.Contour.windingNumber_eq_zero_of_unbounded_component hclosed hP
    hγ.continuousOn hγ_diff hγ.intervalIntegrable_deriv hcomp

/-- The winding number of a closed piecewise C1 curve about `w` is zero if a ray from `w` in a
nonzero direction avoids the image. -/
theorem _root_.Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.IsPiecewiseC1On.windingNumber_eq_zero_of_ray {γ : ℝ → ℂ} {a b : ℝ}
    (hγ : IsPiecewiseC1On γ a b) (hclosed : γ a = γ b) {w v : ℂ} (hv : v ≠ 0)
    (hray : ∀ c : ℝ, 0 ≤ c → w + (c : ℂ) * v ∉ γ '' uIcc a b) :
    windingNumber γ a b w = 0 := by
  have hAconn : IsPreconnected ((fun c : ℝ => w + (c : ℂ) * v) '' Ici 0) :=
    isPreconnected_Ici.image (fun c : ℝ => w + (c : ℂ) * v)
      (Continuous.continuousOn (by fun_prop))
  have hzero : (0 : ℝ) ∈ Ici (0 : ℝ) := Set.mem_Ici.mpr le_rfl
  have hAmem : w ∈ (fun c : ℝ => w + (c : ℂ) * v) '' Ici 0 := ⟨0, hzero, by simp⟩
  have hAsub : (fun c : ℝ => w + (c : ℂ) * v) '' Ici 0 ⊆ (γ '' uIcc a b)ᶜ := by
    rintro _ ⟨c, hc, rfl⟩
    exact hray c hc
  refine hγ.windingNumber_eq_zero_of_unbounded_component hclosed fun hbdd => ?_
  have hsub := hAconn.subset_connectedComponentIn hAmem hAsub
  obtain ⟨r, hr⟩ := (hbdd.subset hsub).subset_closedBall 0
  have hwr : ‖w‖ ≤ r := by simpa using Metric.mem_closedBall.mp (hr ⟨0, hzero, by simp⟩)
  have hrnn : (0 : ℝ) ≤ r := le_trans (norm_nonneg w) hwr
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv

  set c : ℝ := (r + ‖w‖ + 1) / ‖v‖ with hc_def
  have hcnn : 0 ≤ c := by positivity
  have hnorm : ‖(c : ℂ) * v‖ = r + ‖w‖ + 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcnn, hc_def,
      div_mul_cancel₀ _ hvpos.ne']
  have hle : ‖w + (c : ℂ) * v‖ ≤ r := by
    simpa using Metric.mem_closedBall.mp (hr ⟨c, hcnn, rfl⟩)
  have hge : ‖(c : ℂ) * v‖ ≤ ‖w + (c : ℂ) * v‖ + ‖w‖ := by
    simpa using norm_sub_le (w + (c : ℂ) * v) w
  rw [hnorm] at hge
  linarith

/-- A closed piecewise C1 curve contained in a set that contains its filled hull is null
homologous in that set. -/
theorem _root_.Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.IsPiecewiseC1On.isNullHomologous_of_filledHull_subset
    {γ : ℝ → ℂ} {a b : ℝ} {U : Set ℂ} (hγ : IsPiecewiseC1On γ a b) (hclosed : γ a = γ b)
    (hγU : MapsTo γ (uIcc a b) U)
    (hU : filledHull U ⊆ U) : IsNullHomologous γ a b U := by
  rw [isNullHomologous_iff]
  intro w hw
  refine hγ.windingNumber_eq_zero_of_unbounded_component hclosed fun hbdd => hw (hU ?_)
  refine (mem_filledHull_iff (K := U)).2 (hbdd.subset (connectedComponentIn_mono w ?_))
  rintro _ hx ⟨t, ht, rfl⟩
  exact hx (hγU ht)

end TauCeti.Contour

end
end Qatlib.Foundations.CbmdAnalysis.Residue
