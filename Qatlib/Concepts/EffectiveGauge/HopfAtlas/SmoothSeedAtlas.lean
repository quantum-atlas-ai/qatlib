/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.CoarseSeedAtlas
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SeedChartTransfer
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.GaugeCoordinates
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option backward.isDefEq.respectTransparency false

/-!
# Smooth Seed Atlas

Hopf Atlas constructions for Effective Gauge.
Defines `seedChartDomain`, `quaternionFromComponents`.
Proves `quaternionMk_contDiffOn`, `northSeed_contDiffOn`, `southSeed_contDiffOn`.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped Quaternion ContDiff
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.SpectralH1 Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Definition of seed Chart Domain in the Hopf Atlas construction. -/
def seedChartDomain (chart : SeedChart) : Set ℍ := {s | SeedChartValid chart s}

/-- Definition of quaternion From Components in the Hopf Atlas construction. -/
def quaternionFromComponents (a b c d : ℝ) : ℍ := ⟨a,b,c,d⟩

/-- Original `quaternionMk_contDiffOn` guarantee for the `SmoothSeedAtlas` construction; the complete source hypotheses are retained. -/
private theorem quaternionMk_contDiffOn (S : Set ℍ) (f0 f1 f2 f3 : ℍ → ℝ)
    (h0 : ContDiffOn ℝ ∞ f0 S) (h1 : ContDiffOn ℝ ∞ f1 S)
    (h2 : ContDiffOn ℝ ∞ f2 S) (h3 : ContDiffOn ℝ ∞ f3 S) :
    ContDiffOn ℝ ∞ (fun x => quaternionFromComponents (f0 x) (f1 x) (f2 x) (f3 x)) S := by
  let e0 : ℝ →L[ℝ] ℍ := ContinuousLinearMap.toSpanSingleton ℝ (1 : ℍ)
  let e1 : ℝ →L[ℝ] ℍ := ContinuousLinearMap.toSpanSingleton ℝ (⟨0,1,0,0⟩ : ℍ)
  let e2 : ℝ →L[ℝ] ℍ := ContinuousLinearMap.toSpanSingleton ℝ (⟨0,0,1,0⟩ : ℍ)
  let e3 : ℝ →L[ℝ] ℍ := ContinuousLinearMap.toSpanSingleton ℝ (⟨0,0,0,1⟩ : ℍ)
  have h := (((e0.contDiff.comp_contDiffOn h0).add (e1.contDiff.comp_contDiffOn h1)).add
    (e2.contDiff.comp_contDiffOn h2)).add (e3.contDiff.comp_contDiffOn h3)
  convert h using 1
  funext x
  ext <;> simp [quaternionFromComponents,e0,e1,e2,e3]

/-- Original `northSeed_contDiffOn` guarantee for the `SmoothSeedAtlas` construction; the complete source hypotheses are retained. -/
theorem northSeed_contDiffOn : ContDiffOn ℝ ∞ northSeed (seedChartDomain .north) := by
  have hI : ContDiff ℝ ∞ (fun s : ℍ => s.imI) := (quaternionCoordinateCLM 1).contDiff
  have hJ : ContDiff ℝ ∞ (fun s : ℍ => s.imJ) := (quaternionCoordinateCLM 2).contDiff
  have hK : ContDiff ℝ ∞ (fun s : ℍ => s.imK) := (quaternionCoordinateCLM 3).contDiff
  have hpos (s : ℍ) (hs : s∈seedChartDomain .north) : 0<(1+s.imI)/2 := by
    change -(1/2 : ℝ)<s.imI at hs
    linarith
  have hroot : ContDiffOn ℝ ∞ (fun s : ℍ => Real.sqrt ((1+s.imI)/2)) (seedChartDomain .north) :=
    ((contDiff_const.add hI).div_const 2).contDiffOn.sqrt (fun s hs => (hpos s hs).ne')
  have hden (s : ℍ) (hs : s∈seedChartDomain .north) : 2*Real.sqrt ((1+s.imI)/2)≠0 := by
    exact mul_ne_zero (by norm_num) (Real.sqrt_pos.mpr (hpos s hs)).ne'
  exact quaternionMk_contDiffOn _ _ _ _ _ hroot contDiffOn_const
    (hK.contDiffOn.div (contDiffOn_const.mul hroot) hden)
    (hJ.contDiffOn.neg.div (contDiffOn_const.mul hroot) hden)

/-- Original `southSeed_contDiffOn` guarantee for the `SmoothSeedAtlas` construction; the complete source hypotheses are retained. -/
theorem southSeed_contDiffOn : ContDiffOn ℝ ∞ southSeed (seedChartDomain .south) := by
  have hI : ContDiff ℝ ∞ (fun s : ℍ => s.imI) := (quaternionCoordinateCLM 1).contDiff
  have hJ : ContDiff ℝ ∞ (fun s : ℍ => s.imJ) := (quaternionCoordinateCLM 2).contDiff
  have hK : ContDiff ℝ ∞ (fun s : ℍ => s.imK) := (quaternionCoordinateCLM 3).contDiff
  have hpos (s : ℍ) (hs : s∈seedChartDomain .south) : 0<(1-s.imI)/2 := by
    change s.imI<(1/2 : ℝ) at hs
    linarith
  have hroot : ContDiffOn ℝ ∞ (fun s : ℍ => Real.sqrt ((1-s.imI)/2)) (seedChartDomain .south) :=
    ((contDiff_const.sub hI).div_const 2).contDiffOn.sqrt (fun s hs => (hpos s hs).ne')
  have hden (s : ℍ) (hs : s∈seedChartDomain .south) : 2*Real.sqrt ((1-s.imI)/2)≠0 := by
    exact mul_ne_zero (by norm_num) (Real.sqrt_pos.mpr (hpos s hs)).ne'
  exact quaternionMk_contDiffOn _ _ _ _ _
    (hK.contDiffOn.div (contDiffOn_const.mul hroot) hden)
    (hJ.contDiffOn.div (contDiffOn_const.mul hroot) hden) hroot contDiffOn_const

/-- Original `exactChartSeed_contDiffOn` guarantee for the `SmoothSeedAtlas` construction; the complete source hypotheses are retained. -/
theorem exactChartSeed_contDiffOn (chart : SeedChart) :
    ContDiffOn ℝ ∞ (exactChartSeed chart) (seedChartDomain chart) := by
  cases chart with
  | north => exact northSeed_contDiffOn
  | south => exact southSeed_contDiffOn

/-- Smooth dependence on the spin on the actual open overlap, distinct
from smoothness of a fixed transferred spatial field. -/
theorem seedChartTransition_contDiffOn (a b : SeedChart) :
    ContDiffOn ℝ ∞ (seedChartTransition a b) (seedChartDomain a∩seedChartDomain b) := by
  have ha := (exactChartSeed_contDiffOn a).mono (inter_subset_left : seedChartDomain a∩seedChartDomain b ⊆ _)
  have hb := (exactChartSeed_contDiffOn b).mono (inter_subset_right : seedChartDomain a∩seedChartDomain b ⊆ _)
  have hstar : ContDiff ℝ ∞ (fun s : ℍ => star s) := by
    rw [← contDiffOn_univ]
    have h := quaternionMk_contDiffOn (univ : Set ℍ)
      (fun s : ℍ => s.re) (fun s : ℍ => -s.imI) (fun s : ℍ => -s.imJ) (fun s : ℍ => -s.imK)
      (quaternionCoordinateCLM 0).contDiff.contDiffOn (quaternionCoordinateCLM 1).contDiff.neg.contDiffOn
      (quaternionCoordinateCLM 2).contDiff.neg.contDiffOn (quaternionCoordinateCLM 3).contDiff.neg.contDiffOn
    convert h using 1
    funext s
    ext <;> simp [quaternionFromComponents]
  exact hb.mul (hstar.comp_contDiffOn ha)

/-- Original `isOpen_seedChartDomain` guarantee for the `SmoothSeedAtlas` construction; the complete source hypotheses are retained. -/
theorem isOpen_seedChartDomain (chart : SeedChart) : IsOpen (seedChartDomain chart) := by
  have hI : Continuous (fun s : ℍ => s.imI) := (quaternionCoordinateCLM 1).continuous
  cases chart with
  | north =>
    change IsOpen {s : ℍ | -(1/2 : ℝ)<s.imI}
    exact isOpen_lt continuous_const hI
  | south =>
    change IsOpen {s : ℍ | s.imI<(1/2 : ℝ)}
    exact isOpen_lt hI continuous_const

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
