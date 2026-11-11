/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.GaugeSpectralPlan

set_option backward.isDefEq.respectTransparency false

/-!
# Gauge Spectral Budget

Rational Flow constructions for Effective Gauge.
Proves `finiteGaugeOutputCutoff_spec`, `finiteGaugeCutoff_H1_tail_budget`, `finiteGaugeCoefficient_H1_budget`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Original `finiteGaugeOutputCutoff_spec` guarantee for the `GaugeSpectralBudget` construction; the complete source hypotheses are retained. -/
theorem finiteGaugeOutputCutoff_spec (M3 tolerance : ℚ) (ht : 0<tolerance) :
    0<finiteGaugeOutputCutoff M3 tolerance ∧
      16*|M3| ≤ tolerance*(finiteGaugeOutputCutoff M3 tolerance : ℚ) := by
  have hN : 0<finiteGaugeOutputCutoff M3 tolerance := lt_of_lt_of_le (by decide : 0<1) (le_max_left _ _)
  have hceil : 16*|M3|/tolerance ≤ (finiteGaugeOutputCutoff M3 tolerance : ℚ) := by
    apply (Nat.le_ceil _).trans
    dsimp only [finiteGaugeOutputCutoff]
    exact_mod_cast (le_max_right 1 (Nat.ceil (16*|M3|/tolerance)))
  exact ⟨hN,by nlinarith [(div_le_iff₀ ht).mp hceil]⟩

/-- Original `finiteGaugeCutoff_H1_tail_budget` guarantee for the `GaugeSpectralBudget` construction; the complete source hypotheses are retained. -/
theorem finiteGaugeCutoff_H1_tail_budget (M3 tolerance : ℚ) (hM : 0 ≤ M3) (ht : 0<tolerance) :
    48*M3^2/((finiteGaugeOutputCutoff M3 tolerance : ℚ)+1)^4 ≤ 3*tolerance^2/16 := by
  let N := finiteGaugeOutputCutoff M3 tolerance
  have hs := finiteGaugeOutputCutoff_spec M3 tolerance ht
  have hcut : 16*M3 ≤ tolerance*(N : ℚ) := by simpa only [abs_of_nonneg hM] using hs.2
  have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg _
  have hsq := (sq_le_sq₀ (by positivity : (0 : ℚ) ≤ 16*M3)
    (by positivity : (0 : ℚ) ≤ tolerance*(N : ℚ))).mpr hcut
  have hden : (N : ℚ)^2 ≤ ((N : ℚ)+1)^4 := by
    have hle : (N : ℚ) ≤ (N : ℚ)+1 := by linarith
    exact ((sq_le_sq₀ hN (by positivity)).mpr hle).trans
      (pow_le_pow_right₀ (by linarith : (1 : ℚ) ≤ (N : ℚ)+1) (by decide : 2 ≤ 4))
  apply (div_le_iff₀ (by positivity : (0 : ℚ)<((N : ℚ)+1)^4)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hden (sq_nonneg tolerance)]

/-- Original `finiteGaugeCoefficient_H1_budget` guarantee for the `GaugeSpectralBudget` construction; the complete source hypotheses are retained. -/
theorem finiteGaugeCoefficient_H1_budget (N : ℕ) (tolerance : ℚ) :
    4*343*(finitePoissonFrequencyCount N : ℚ)*(1+3*(N : ℚ)^2)*
      (finiteGaugeCoefficientAccuracy N tolerance)^2 ≤ 4116*tolerance^2/262144 := by
  let J : ℚ := finitePoissonFrequencyCount N
  let delta := finiteGaugeCoefficientAccuracy N tolerance
  have hJ : 0<J := by
    change (0 : ℚ)<finitePoissonFrequencyCount N
    exact_mod_cast finitePoissonFrequencyCount_pos N
  have hJ1 : 1 ≤ J := by
    change (1 : ℚ) ≤ finitePoissonFrequencyCount N
    exact_mod_cast (Nat.succ_le_iff.mpr (finitePoissonFrequencyCount_pos N))
  have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg _
  have hNp : 0<(N : ℚ)+1 := by positivity
  have hweight : 1+3*(N : ℚ)^2 ≤ 3*((N : ℚ)+1)^2 := by nlinarith
  have hnum := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hweight (by positivity : (0 : ℚ) ≤ 4*343*J)) (sq_nonneg delta)
  have hid : 4*343*J*(3*((N : ℚ)+1)^2)*delta^2=4116*tolerance^2/(262144*J) := by
    dsimp only [delta,finiteGaugeCoefficientAccuracy]
    change 4*343*J*(3*((N : ℚ)+1)^2)*(tolerance/(512*J*((N : ℚ)+1)))^2=4116*tolerance^2/(262144*J)
    field_simp [hJ.ne',hNp.ne']
    ring
  exact (hnum.trans_eq hid).trans (div_le_div₀ (by positivity) le_rfl (by norm_num) (by nlinarith))

/-- Directly add the disjoint inside/outside spectral energies. These
rational budgets leave the exact physical H1 norm at most eps/2. -/
theorem finiteGaugeSpectral_H1_budget (M3 tolerance : ℚ) (hM : 0 ≤ M3) (ht : 0<tolerance) :
    let N := finiteGaugeOutputCutoff M3 tolerance
    48*M3^2/((N : ℚ)+1)^4+4*343*(finitePoissonFrequencyCount N : ℚ)*(1+3*(N : ℚ)^2)*
      (finiteGaugeCoefficientAccuracy N tolerance)^2 ≤ tolerance^2/4 := by
  dsimp only
  have htail := finiteGaugeCutoff_H1_tail_budget M3 tolerance hM ht
  have hnum := finiteGaugeCoefficient_H1_budget (finiteGaugeOutputCutoff M3 tolerance) tolerance
  nlinarith [sq_nonneg tolerance]

end Qatlib.Concepts.EffectiveGauge.RationalFlow
