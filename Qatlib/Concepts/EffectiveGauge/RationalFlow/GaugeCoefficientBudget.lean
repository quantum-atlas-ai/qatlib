/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.EffectiveGauge.RationalFlow.GaugeSpectralPlan

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Gauge Coefficient Budget

Rational Flow constructions for Effective Gauge.
Proves `finiteGaugeCoefficientAccuracy_pos`, `finiteGaugeCoefficientMesh_spec`, `finiteGaugeModeAccuracy_spec`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Every output cutoff has a positive per-coefficient accuracy when the target tolerance is
positive. -/
theorem finiteGaugeCoefficientAccuracy_pos (N : ℕ) (tolerance : ℚ) (ht : 0<tolerance) :
    0<finiteGaugeCoefficientAccuracy N tolerance := by
  have hJ : (0 : ℚ)<finitePoissonFrequencyCount N := by
    exact_mod_cast finitePoissonFrequencyCount_pos N
  exact div_pos ht (by positivity)

/-- At positive coefficient accuracy the selected mesh is positive and its quadrature bound
`3 * (P1 + 7 * N) / mesh` is at most one quarter of that accuracy. -/
theorem finiteGaugeCoefficientMesh_spec (P1 : ℚ) (N : ℕ)
    (accuracy : ℚ) (ha : 0<accuracy) :
    0<finiteGaugeCoefficientMesh P1 N accuracy ∧
      3*(P1+7*(N : ℚ))/(finiteGaugeCoefficientMesh P1 N accuracy : ℚ) ≤ accuracy/4 := by
  let M := finiteGaugeCoefficientMesh P1 N accuracy
  have hM : 0<M := lt_of_lt_of_le (by decide : 0<1) (le_max_left _ _)
  have hMR : (0 : ℚ)<M := Nat.cast_pos.mpr hM
  have hceil : 12*(P1+7*(N : ℚ))/accuracy ≤ (M : ℚ) := by
    apply (Nat.le_ceil _).trans
    dsimp only [M,finiteGaugeCoefficientMesh]
    exact_mod_cast le_max_right 1 (Nat.ceil (12*(P1+7*(N : ℚ))/accuracy))
  have hmul := (div_le_iff₀ ha).mp hceil
  refine ⟨hM,(div_le_iff₀ hMR).mpr ?_⟩
  nlinarith

/-- For positive coefficient accuracy the mode accuracy lies in `(0, 1]`. Adding the sample accuracy
to the mode accuracy times one plus the sample accuracy gives exactly half the coefficient accuracy. -/
theorem finiteGaugeModeAccuracy_spec (accuracy : ℚ) (ha : 0<accuracy) :
    0<finiteGaugeModeAccuracy accuracy ∧ finiteGaugeModeAccuracy accuracy ≤ 1 ∧
      finiteGaugeSampleAccuracy accuracy+(1+finiteGaugeSampleAccuracy accuracy)*
        finiteGaugeModeAccuracy accuracy=accuracy/2 := by
  have hs : 0<finiteGaugeSampleAccuracy accuracy := div_pos ha (by norm_num)
  have hden : 0<4*(1+finiteGaugeSampleAccuracy accuracy) := by positivity
  refine ⟨div_pos ha hden,?_,?_⟩
  · apply (div_le_iff₀ hden).mpr
    dsimp only [finiteGaugeSampleAccuracy]
    linarith
  · dsimp only [finiteGaugeModeAccuracy,finiteGaugeSampleAccuracy]
    field_simp
    ring

/-- For positive coefficient accuracy the selected period accuracy is positive and its product with
`3 * N` is at most half the mode accuracy. -/
theorem finiteGaugeModePeriodAccuracy_spec (N : ℕ) (accuracy : ℚ) (ha : 0<accuracy) :
    0<finiteGaugeModePeriodAccuracy N accuracy ∧
      3*(N : ℚ)*finiteGaugeModePeriodAccuracy N accuracy ≤ finiteGaugeModeAccuracy accuracy/2 := by
  have hd := finiteGaugeModeAccuracy_spec accuracy ha
  have hden : (0 : ℚ)<12*((N : ℚ)+1) := by positivity
  refine ⟨div_pos hd.1 hden,?_⟩
  dsimp only [finiteGaugeModePeriodAccuracy]
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hden).mpr
  have hn : (0 : ℚ) ≤ N := Nat.cast_nonneg _
  nlinarith [mul_nonneg hd.1.le hn]

/-- At positive coefficient accuracy the sum of the mesh quadrature bound and the sample-mode
product error bound is at most that accuracy. -/
theorem finiteGaugeCoefficientSampling_budget (P1 : ℚ) (N : ℕ)
    (accuracy : ℚ) (ha : 0<accuracy) :
    3*(P1+7*(N : ℚ))/(finiteGaugeCoefficientMesh P1 N accuracy : ℚ)+
      (finiteGaugeSampleAccuracy accuracy+(1+finiteGaugeSampleAccuracy accuracy)*
        finiteGaugeModeAccuracy accuracy) ≤ accuracy := by
  rw [(finiteGaugeModeAccuracy_spec accuracy ha).2.2]
  linarith [(finiteGaugeCoefficientMesh_spec P1 N accuracy ha).2]

end Qatlib.Concepts.EffectiveGauge.RationalFlow
