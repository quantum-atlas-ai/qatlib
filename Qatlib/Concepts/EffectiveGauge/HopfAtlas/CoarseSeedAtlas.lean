/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SeedChart

/-!
# Coarse Seed Atlas

Hopf Atlas constructions for Effective Gauge.
Defines `seedChartAccepted`, `SeedChartValid`.
Proves `seedChartAccepted_choose`, `seedChartAccepted_valid`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Finite, positive-margin admission test. A rejected alternate chart is not
claimed mathematically invalid: it is merely uncertified by this answer. -/
def seedChartAccepted (sample : Fin 3 → ℚ) (chart : SeedChart) : Bool :=
  match chart with
  | .north => decide (-(1/2 : ℚ)<sample 0-1/16)
  | .south => decide (sample 0+1/16<(1/2 : ℚ))

/-- Original `seedChartAccepted_choose` guarantee for the `CoarseSeedAtlas` construction; the complete source hypotheses are retained. -/
theorem seedChartAccepted_choose (sample : Fin 3 → ℚ) :
    seedChartAccepted sample (chooseSeedChart sample)=true := by
  unfold chooseSeedChart
  split_ifs with h
  · simp only [seedChartAccepted,decide_eq_true_eq]
    exact h
  · simp only [seedChartAccepted,decide_eq_true_eq]
    have hh := le_of_not_gt h
    linarith

noncomputable section
open scoped Quaternion

/-- Definition of Seed Chart Valid in the Hopf Atlas construction. -/
def SeedChartValid (chart : SeedChart) (s : ℍ) : Prop :=
  match chart with
  | .north => -(1/2 : ℝ)<s.imI
  | .south => s.imI<(1/2 : ℝ)

/-- Original `seedChartAccepted_valid` guarantee for the `CoarseSeedAtlas` construction; the complete source hypotheses are retained. -/
theorem seedChartAccepted_valid (sample : Fin 3 → ℚ) (s : ℍ)
    (he : |(sample 0 : ℝ)-s.imI| ≤ (1/16 : ℝ))
    (chart : SeedChart) (hchart : seedChartAccepted sample chart=true) :
    SeedChartValid chart s := by
  cases chart with
  | north =>
    have hq : -(1/2 : ℚ)<sample 0-1/16 := of_decide_eq_true hchart
    have hr : ((-(1/2 : ℚ) : ℚ) : ℝ)<((sample 0-1/16 : ℚ) : ℝ) := Rat.cast_lt.mpr hq
    push_cast at hr
    have hh := (abs_le.mp he).2
    change -(1/2 : ℝ)<s.imI
    linarith
  | south =>
    have hq : sample 0+1/16<(1/2 : ℚ) := of_decide_eq_true hchart
    have hr : ((sample 0+1/16 : ℚ) : ℝ)<(((1/2 : ℚ) : ℚ) : ℝ) := Rat.cast_lt.mpr hq
    push_cast at hr
    have hh := (abs_le.mp he).1
    change s.imI<(1/2 : ℝ)
    linarith

end
end Qatlib.Concepts.EffectiveGauge.HopfAtlas
