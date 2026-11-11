/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.PhysicalLine

/-! # A fixed initial chart selected by a single coarse rational source query -/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Constructors for Seed Chart in the Hopf Atlas construction. -/
inductive SeedChart where
  | north
  | south
  deriving DecidableEq, Repr

/-- Definition of choose Seed Chart in the Hopf Atlas construction. -/
def chooseSeedChart (a : Fin 3 → ℚ) : SeedChart :=
  if -(1/2 : ℚ)<a 0-1/16 then .north else .south

/-- Definition of origin Spin Samples in the Hopf Atlas construction. -/
def originSpinSamples (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample) (b : ℕ) : Fin 3 → ℚ :=
  (source (0,b)).1

/-- Definition of chosen Origin Chart in the Hopf Atlas construction. -/
def chosenOriginChart (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample) : SeedChart :=
  chooseSeedChart (originSpinSamples source 4)

noncomputable section
open scoped Quaternion

/-- Definition of exact Chart Seed in the Hopf Atlas construction. -/
def exactChartSeed (chart : SeedChart) (s : ℍ) : ℍ :=
  match chart with
  | .north => northSeed s
  | .south => southSeed s

/-- Definition of chosen Origin Seed in the Hopf Atlas construction. -/
def chosenOriginSeed (v : SpatialPoint → SpatialPoint)
    (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample) : ℍ :=
  exactChartSeed (chosenOriginChart source) (sourceQuaternion v 0)

/-- Original `chooseSeedChart_valid` guarantee for the `SeedChart` construction; the complete source hypotheses are retained. -/
theorem chooseSeedChart_valid (a : Fin 3 → ℚ) (s : ℍ) (he : |(a 0 : ℝ)-s.imI| ≤ (1/16 : ℝ)) :
    match chooseSeedChart a with
    | .north => -(1/2 : ℝ)<s.imI
    | .south => s.imI<(1/2 : ℝ) := by
  unfold chooseSeedChart
  split_ifs with h
  · have hr : ((-(1/2 : ℚ) : ℚ) : ℝ)<((a 0-1/16 : ℚ) : ℝ) := Rat.cast_lt.mpr h
    push_cast at hr
    have h1 := (abs_le.mp he).2
    dsimp
    linarith
  · have hr : ((a 0-1/16 : ℚ) : ℝ) ≤ ((-(1/2 : ℚ) : ℚ) : ℝ) := Rat.cast_le.mpr (le_of_not_gt h)
    push_cast at hr
    have h1 := (abs_le.mp he).1
    dsimp
    linarith

/-- Original `exactChartSeed_spec` guarantee for the `SeedChart` construction; the complete source hypotheses are retained. -/
theorem exactChartSeed_spec (chart : SeedChart) (s : ℍ) (hr : s.re=0) (hn : ‖s‖=1)
    (hc : match chart with
      | .north => -(1/2 : ℝ)<s.imI
      | .south => s.imI<(1/2 : ℝ)) :
    ‖exactChartSeed chart s‖=1 ∧ hopf (exactChartSeed chart s)=s ∧
      (match chart with
      | .north => (1/2 : ℝ)<(exactChartSeed chart s).re
      | .south => (1/2 : ℝ)<(exactChartSeed chart s).imJ) := by
  cases chart with
  | north => exact ⟨northSeed_norm s hr hn hc,northSeed_hopf s hr hn hc,northSeed_margin s hc⟩
  | south => exact ⟨southSeed_norm s hr hn hc,southSeed_hopf s hr hn hc,southSeed_margin s hc⟩

/-- Original `originSpinSamples_error` guarantee for the `SeedChart` construction; the complete source hypotheses are retained. -/
theorem originSpinSamples_error (v : SpatialPoint → SpatialPoint)
    (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample) (hsource : OriginalSpinSourceAccurate v source) (b : ℕ) :
    ∀ j, |(originSpinSamples source b j : ℝ)-v 0 j| ≤ (2^b : ℝ)⁻¹ := by
  have h := (hsource 0 b (fun _ => ⟨by simp,by simpa using physicalPeriod_pos.le⟩)).1
  have he : rationalSpatialPoint (0 : Fin 3 → ℚ)=0 := by ext j; simp [rationalSpatialPoint]
  rw [he] at h
  exact h

/-- Original `chosenOriginChart_valid` guarantee for the `SeedChart` construction; the complete source hypotheses are retained. -/
theorem chosenOriginChart_valid (v : SpatialPoint → SpatialPoint)
    (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample) (hsource : OriginalSpinSourceAccurate v source) :
    match chosenOriginChart source with
    | .north => -(1/2 : ℝ)<(sourceQuaternion v 0).imI
    | .south => (sourceQuaternion v 0).imI<(1/2 : ℝ) := by
  apply chooseSeedChart_valid
  simpa only [sourceQuaternion,spinOfVector,show (2^4 : ℝ)⁻¹=(1/16 : ℝ) by norm_num] using originSpinSamples_error v source hsource 4 0

/-- One chart and one exact seed are fixed independently of all requested
accuracies. The seed is produced from the original source value at zero. -/
theorem chosenOriginSeed_spec (v : SpatialPoint → SpatialPoint) (hu : ∀ w, ‖v w‖=1)
    (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample) (hsource : OriginalSpinSourceAccurate v source) :
    ‖chosenOriginSeed v source‖=1 ∧ hopf (chosenOriginSeed v source)=sourceQuaternion v 0 ∧
      (match chosenOriginChart source with
      | .north => (1/2 : ℝ)<(chosenOriginSeed v source).re
      | .south => (1/2 : ℝ)<(chosenOriginSeed v source).imJ) := by
  have hn : ‖sourceQuaternion v 0‖=1 := (spinOfVector_norm _).trans (hu 0)
  have hc := chosenOriginChart_valid v source hsource
  cases hchart : chosenOriginChart source with
  | north =>
    simp only [hchart] at hc
    simpa only [chosenOriginSeed,hchart] using exactChartSeed_spec .north (sourceQuaternion v 0) rfl hn hc
  | south =>
    simp only [hchart] at hc
    simpa only [chosenOriginSeed,hchart] using exactChartSeed_spec .south (sourceQuaternion v 0) rfl hn hc

end
end Qatlib.Concepts.EffectiveGauge.HopfAtlas
