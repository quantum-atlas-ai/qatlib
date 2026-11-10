/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Winding.Number.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Calculus.ContDiff.PiecewiseC1On
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Curve.Distance
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Winding.Continuity
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.Basic
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

open Complex MeasureTheory Set

open scoped Topology

namespace TauCeti.Contour

attribute [local irreducible] windingNumber

theorem eq_of_dist_intCast_lt_one {m n : ℤ} (h : dist (m : ℂ) (n : ℂ) < 1) : m = n := by
  by_contra hne
  have : (1 : ℝ) ≤ dist (m : ℂ) (n : ℂ) := by
    rw [Complex.isometry_intCast.dist_eq]; exact Int.pairwise_one_le_dist hne
  linarith

theorem _root_.Qatlib.Foundations.CbmdAnalysis.Residue.ContinuousOn.isLocallyConstant_windingNumber_of_integer {γ : ℝ → ℂ} {a b : ℝ}
    (hγ_cont : ContinuousOn γ (uIcc a b))
    (hderiv_int : IntervalIntegrable (deriv γ) volume a b)
    (hint : ∀ z, z ∉ γ '' uIcc a b → ∃ n : ℤ, windingNumber γ a b z = n) :
    IsLocallyConstant
      (fun z : {z : ℂ // z ∉ γ '' uIcc a b} ↦ windingNumber γ a b z.1) := by
  classical
  choose n hn using fun z : {z : ℂ // z ∉ γ '' uIcc a b} ↦ hint z.1 z.2
  have hc : Continuous
      (fun z : {z : ℂ // z ∉ γ '' uIcc a b} ↦ windingNumber γ a b z.1) := by
    refine continuous_iff_continuousAt.mpr fun z ↦ ?_
    have havoid : ∀ t ∈ uIcc a b, γ t ≠ z.1 := by
      simpa only [mem_image, not_exists, not_and] using z.2
    exact (continuousAt_windingNumber_of_avoidance hγ_cont havoid
      (intervalIntegrable_inv_sub_mul_deriv hγ_cont havoid hderiv_int)).comp
        continuous_subtype_val.continuousAt
  have hncont : Continuous n := Complex.isClosedEmbedding_intCast.isEmbedding.continuous_iff.mpr
    (by simpa only [Function.comp_def, ← hn] using hc)
  simpa only [Function.comp_def, ← hn] using
    ((IsLocallyConstant.iff_continuous n).mpr hncont).comp (fun k : ℤ ↦ (k : ℂ))

theorem isLocallyConstant_windingNumber_of_closed {γ : ℝ → ℂ} {a b : ℝ} {P : Set ℝ}
    (hclosed : γ a = γ b) (hP : P.Countable) (hγ_cont : ContinuousOn γ (uIcc a b))
    (hγ_diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t)
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b) :
    IsLocallyConstant
      (fun w : {w : ℂ // ∀ t ∈ uIcc a b, γ t ≠ w} ↦ windingNumber γ a b w.1) := by
  have hac := ContinuousOn.absolutelyContinuousOnInterval_of_hasDerivAt_off_countable hγ_cont hP
    (fun t ht ↦ (hγ_diff t ht).hasDerivAt) hderiv_int
  have h := ContinuousOn.isLocallyConstant_windingNumber_of_integer (γ := γ) (a := a) (b := b) hγ_cont hderiv_int
    (fun _ hz ↦ AbsolutelyContinuousOnInterval.exists_int_windingNumber (γ := γ) (a := a) (b := b) hac hclosed hz)

  exact h.comp_continuous (g := fun z : {z : ℂ // z ∉ γ '' uIcc a b} ↦ windingNumber γ a b z.1) (continuous_subtype_val.subtype_mk
    (fun z ↦ by simpa only [mem_image, not_exists, not_and] using z.2))

theorem _root_.Qatlib.Foundations.CbmdAnalysis.Residue.ContinuousOn.windingNumber_eq_of_mem_connectedComponentIn_of_integer
    {γ : ℝ → ℂ} {a b : ℝ} (hγ : ContinuousOn γ (uIcc a b))
    (hderiv : IntervalIntegrable (deriv γ) volume a b)
    (hint : ∀ z, z ∉ γ '' uIcc a b → ∃ n : ℤ, windingNumber γ a b z = n)
    {z w : ℂ} (hw : w ∈ connectedComponentIn ((γ '' uIcc a b)ᶜ) z) :
    windingNumber γ a b w = windingNumber γ a b z := by
  have hz : z ∈ (γ '' uIcc a b)ᶜ := by
    by_contra hz
    rw [connectedComponentIn_eq_empty hz] at hw
    exact hw
  rw [connectedComponentIn_eq_image hz] at hw
  obtain ⟨w, hw, rfl⟩ := hw
  exact (ContinuousOn.isLocallyConstant_windingNumber_of_integer (γ := γ) (a := a) (b := b) hγ hderiv hint).apply_eq_of_isPreconnected
    (f := fun w : {w : ℂ // w ∈ (γ '' uIcc a b)ᶜ} ↦ windingNumber γ a b w.1)
    isPreconnected_connectedComponent hw mem_connectedComponent

theorem windingNumber_eq_of_mem_connectedComponentIn {γ : ℝ → ℂ} {a b : ℝ} {P : Set ℝ}
    (hclosed : γ a = γ b) (hP : P.Countable) (hγ_cont : ContinuousOn γ (uIcc a b))
    (hγ_diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t)
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b)
    {w₀ w₁ : ℂ} (hw₁ : w₁ ∈ connectedComponentIn ((γ '' uIcc a b)ᶜ) w₀) :
    windingNumber γ a b w₁ = windingNumber γ a b w₀ := by
  have hac := ContinuousOn.absolutelyContinuousOnInterval_of_hasDerivAt_off_countable hγ_cont hP
    (fun t ht ↦ (hγ_diff t ht).hasDerivAt) hderiv_int
  exact ContinuousOn.windingNumber_eq_of_mem_connectedComponentIn_of_integer hγ_cont hderiv_int
    (fun _ hz ↦ AbsolutelyContinuousOnInterval.exists_int_windingNumber (γ := γ) (a := a) (b := b) hac hclosed hz) hw₁

theorem _root_.Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.IsPiecewiseC1On.windingNumber_eq_of_mem_connectedComponentIn
    {γ : ℝ → ℂ} {a b : ℝ} (hγ : IsPiecewiseC1On γ a b) (hclosed : γ a = γ b)
    {w₀ w₁ : ℂ} (hw₁ : w₁ ∈ connectedComponentIn ((γ '' uIcc a b)ᶜ) w₀) :
    windingNumber γ a b w₁ = windingNumber γ a b w₀ := by
  obtain ⟨P, hP, hγ_diff⟩ := hγ.exists_countable_differentiableAt
  exact TauCeti.Contour.windingNumber_eq_of_mem_connectedComponentIn hclosed hP
    hγ.continuousOn hγ_diff hγ.intervalIntegrable_deriv hw₁

theorem exists_ball_windingNumber_zero {γ : ℝ → ℂ} {w : ℂ} {a b : ℝ} {P : Set ℝ}
    (hclosed : γ a = γ b) (hP : P.Countable) (hγ_cont : ContinuousOn γ (uIcc a b))
    (hγ_diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t)
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b)
    (hoff : ∀ t ∈ uIcc a b, γ t ≠ w) (hw_zero : windingNumber γ a b w = 0) :
    ∃ ε > 0, ∀ w' ∈ Metric.ball w ε,
      (∀ t ∈ uIcc a b, γ t ≠ w') ∧ windingNumber γ a b w' = 0 := by
  obtain ⟨ε₁, hε₁, h_dist⟩ := exists_ball_dist_curve_lower_bound hγ_cont hoff

  have hSopen : IsOpen {z : ℂ | ∀ t ∈ uIcc a b, γ t ≠ z} := by
    have hset : {z : ℂ | ∀ t ∈ uIcc a b, γ t ≠ z} = (γ '' uIcc a b)ᶜ := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_image, not_exists, not_and, ne_eq]
    rw [hset]
    exact (isCompact_uIcc.image_of_continuousOn hγ_cont).isClosed.isOpen_compl

  have hlc := isLocallyConstant_windingNumber_of_closed hclosed hP hγ_cont hγ_diff hderiv_int
  obtain ⟨V, hV_open, hwV, hV_const⟩ := hlc.exists_open ⟨w, hoff⟩
  have hVℂ : IsOpen (Subtype.val '' V) := hSopen.isOpenMap_subtype_val V hV_open
  obtain ⟨ε₂, hε₂, hball₂⟩ := Metric.isOpen_iff.mp hVℂ w ⟨⟨w, hoff⟩, hwV, rfl⟩
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun w' hw' ↦ ⟨fun t ht ↦ ?_, ?_⟩⟩
  · exact sub_ne_zero.mp (norm_pos_iff.mp (lt_of_lt_of_le hε₁
      (h_dist w' (Metric.ball_subset_ball (min_le_left _ _) hw') t ht)))
  · obtain ⟨p, hpV, hpeq⟩ := hball₂ (Metric.ball_subset_ball (min_le_right _ _) hw')
    rw [← hpeq, hV_const p hpV]
    exact hw_zero

end TauCeti.Contour

end
end Qatlib.Foundations.CbmdAnalysis.Residue
