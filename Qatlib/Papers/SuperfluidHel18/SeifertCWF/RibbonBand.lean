/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.SeifertCWF.RibbonGaussLimit

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# A symmetric parameter band for the ribbon Gauss integral

[Kedia2018SuperfluidHelicity], Section IV and Eq. (5),
[DOI](https://doi.org/10.1103/PhysRevFluids.3.104702).
The near part of the core–offset Gauss integral can be written using
a signed parameter difference on one symmetric interval. The periodic
translation accounts for both endpoint corners of the parameter square.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SuperfluidHel18.SeifertCWF

open Qatlib.Papers.SuperfluidHel18.CenterlineCL
open MeasureTheory Set
open scoped Real

/-- A signed difference lies in the band if an integer period translate lies there. -/
private def inPeriodicBand (δ h : ℝ) : Prop :=
  ∃ n : ℤ, |h + (n : ℝ) * (2 * π)| < δ

/-- Adding a full period preserves membership in the band. -/
private theorem inPeriodicBand_add_period (δ h : ℝ) :
    inPeriodicBand δ (h + 2 * π) ↔ inPeriodicBand δ h := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n + 1, ?_⟩
    push_cast
    rwa [show h + ((n : ℝ) + 1) * (2 * π) =
      h + 2 * π + (n : ℝ) * (2 * π) by ring]
  · rintro ⟨n, hn⟩
    refine ⟨n - 1, ?_⟩
    push_cast
    rwa [show h + 2 * π + ((n : ℝ) - 1) * (2 * π) =
      h + (n : ℝ) * (2 * π) by ring]

/-- For differences of parameters in one period, only the two adjacent periodic
copies and the unshifted difference meet a band of width at most half a period. -/
private theorem inPeriodicBand_iff {δ h : ℝ} (hδ : δ ≤ π) (hh : |h| ≤ 2 * π) :
    inPeriodicBand δ h ↔ min |h| (2 * π - |h|) < δ := by
  have hp := Real.pi_pos
  have hh' := abs_le.mp hh
  rw [min_lt_iff]
  constructor
  · rintro ⟨n, hn⟩
    have hn' := abs_lt.mp hn
    have hnlo : ¬ n ≤ -2 := by
      intro hl
      have hl' : (n : ℝ) ≤ -2 := by exact_mod_cast hl
      have hz := mul_le_mul_of_nonneg_right hl' Real.two_pi_pos.le
      linarith [hn'.1, hh'.2]
    have hnhi : ¬ (2 : ℤ) ≤ n := by
      intro hu
      have hu' : (2 : ℝ) ≤ n := by exact_mod_cast hu
      have hz := mul_le_mul_of_nonneg_right hu' Real.two_pi_pos.le
      linarith [hn'.2, hh'.1]
    have hcases : n = -1 ∨ n = 0 ∨ n = 1 := by omega
    rcases hcases with rfl | rfl | rfl
    · right
      norm_num at hn'
      have hhpos : 0 ≤ h := by linarith [hn'.1]
      rw [abs_of_nonneg hhpos]
      linarith [hn'.1]
    · left
      simpa using hn
    · right
      norm_num at hn'
      have hhneg : h ≤ 0 := by linarith [hn'.2]
      rw [abs_of_nonpos hhneg]
      linarith [hn'.2]
  · rintro (hsmall | hwrap)
    · exact ⟨0, by simpa using hsmall⟩
    · rcases le_total 0 h with hhpos | hhneg
      · refine ⟨-1, ?_⟩
        rw [abs_of_nonneg hhpos] at hwrap
        norm_num
        rw [abs_of_nonpos (by linarith [hh'.2] : h + -(2 * π) ≤ 0)]
        linarith
      · refine ⟨1, ?_⟩
        rw [abs_of_nonpos hhneg] at hwrap
        norm_num
        rw [abs_of_nonneg (by linarith [hh'.1] : 0 ≤ h + 2 * π)]
        linarith

/-- On the centered period, the periodic band is the ordinary open interval. -/
private theorem inPeriodicBand_iff_mem_Ioo {δ h : ℝ} (hδ : δ ≤ π)
    (hh : h ∈ Icc (-π) π) : inPeriodicBand δ h ↔ h ∈ Ioo (-δ) δ := by
  have ha : |h| ≤ π := abs_le.mpr hh
  have hp := Real.pi_pos
  rw [inPeriodicBand_iff hδ (by linarith), min_eq_left (by linarith)]
  exact abs_lt

/-- Fubini and periodic translation express the complete circular near band
as an ordinary symmetric integral of signed differences at every base point. -/
theorem circularRibbonNear_eq_intervalIntegral {γ N : ℝ → Fin 3 → ℝ}
    (hγ : ContDiff ℝ 1 γ) (hN : ContDiff ℝ 1 N)
    (hpγ : Function.Periodic γ (2 * π)) {a δ : ℝ}
    (hdisj : ∀ s t, γ s ≠ normalRibbonPoint γ N a t) (hδ : 0 < δ) (hδπ : δ ≤ π) :
    circularRibbonNear γ N δ a =
      ∫ s in 0..(2 * π), ∫ h in -δ..δ, gaussKernel γ (normalRibbonPoint γ N a) (s + h) s := by
  classical
  let U : Set (ℝ × ℝ) := {p | circularParameterGap p.1 p.2 < δ}
  let G (p : ℝ × ℝ) := gaussKernel γ (normalRibbonPoint γ N a) p.1 p.2
  have hgap : Continuous (fun p : ℝ × ℝ => circularParameterGap p.1 p.2) := by
    unfold circularParameterGap
    fun_prop
  have hU : MeasurableSet U := (isOpen_lt hgap continuous_const).measurableSet
  have hc : ContDiff ℝ 1 (normalRibbonPoint γ N a) := hγ.add (hN.const_smul a)
  have hi : Integrable (U.indicator G) gaussMeasure :=
    (integrable_gaussKernel γ (normalRibbonPoint γ N a) hγ hc hdisj).indicator hU
  change (∫ p in U, G p ∂gaussMeasure) = _
  rw [← integral_indicator hU]
  unfold gaussMeasure at hi ⊢
  rw [integral_prod_symm _ hi, intervalIntegral.integral_of_le Real.two_pi_pos.le,
    integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro s hs
  let f (h : ℝ) := if inPeriodicBand δ h then G (s + h, s) else 0
  have hP : Function.Periodic f (2 * π) := by
    intro h
    have hd := periodic_deriv_curve hpγ (hγ.differentiable (by norm_num))
    simp only [f, inPeriodicBand_add_period, G, ← add_assoc s h, gaussKernel,
      hpγ (s + h), hd (s + h)]
  have hshift : (∫ h in -s..(2 * π - s), f h) = ∫ h in -π..π, f h := by
    convert hP.intervalIntegral_add_eq (-s) (-π) using 2 <;> ring
  change (∫ t in Icc 0 (2 * π), U.indicator G (t, s)) = _
  calc
    _ = ∫ t in 0..(2 * π), f (t - s) := by
      rw [intervalIntegral.integral_of_le Real.two_pi_pos.le, ← integral_Icc_eq_integral_Ioc]
      apply setIntegral_congr_fun measurableSet_Icc
      intro t ht
      have hg : |t - s| ≤ 2 * π :=
        abs_le.mpr ⟨by linarith [hs.2, ht.1], by linarith [hs.1, ht.2]⟩
      have heq : inPeriodicBand δ (t - s) ↔ (t, s) ∈ U := by
        change inPeriodicBand δ (t - s) ↔ circularParameterGap t s < δ
        rw [inPeriodicBand_iff hδπ hg, circularParameterGap, abs_sub_comm s t]
      simp only [f, heq, indicator, show s + (t - s) = t by ring]
    _ = ∫ h in -s..(2 * π - s), f h := by
      simpa only [sub_eq_add_neg, zero_add] using
        (intervalIntegral.integral_comp_add_right f (a := 0) (b := 2 * π) (-s))
    _ = ∫ h in -π..π, f h := hshift
    _ = ∫ h in -δ..δ, G (s + h, s) := by
      have hp := Real.pi_pos
      have hsupp : EqOn f ((Ioo (-δ) δ).indicator fun h => G (s + h, s)) (Icc (-π) π) := by
        intro h hh
        simp only [f, inPeriodicBand_iff_mem_Ioo hδπ hh, indicator]
      have hsub : Ioo (-δ) δ ⊆ Icc (-π) π := by
        intro h hh
        exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
      rw [intervalIntegral.integral_of_le (by linarith : -π ≤ π), ← integral_Icc_eq_integral_Ioc,
        setIntegral_congr_fun measurableSet_Icc hsupp, setIntegral_indicator measurableSet_Ioo,
        inter_eq_right.mpr hsub, ← integral_Ioc_eq_integral_Ioo,
        intervalIntegral.integral_of_le (by linarith : -δ ≤ δ)]

end Qatlib.Papers.SuperfluidHel18.SeifertCWF
