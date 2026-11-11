/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.ConstantGaugeEnergy

set_option backward.isDefEq.respectTransparency false

/-!
# Seed Transfer Budget

Rational Flow constructions for Effective Gauge.
Defines `seedTransferArtifactAccuracy`.
Proves `seedTransferArtifactAccuracy_spec`, `seedTransferArtifactAccuracy_budget`, `seedTransferArtifact_H1_bound`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.SpectralH1 Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Definition of seed Transfer Artifact Accuracy in the Rational Flow construction. -/
def seedTransferArtifactAccuracy (M tolerance : ℚ) : ℚ :=
  min (1/2) (tolerance/(256*(|M|+1)))

/-- Original `seedTransferArtifactAccuracy_spec` guarantee for the `SeedTransferBudget` construction; the complete source hypotheses are retained. -/
theorem seedTransferArtifactAccuracy_spec (M tolerance : ℚ) (ht : 0<tolerance) :
    0<seedTransferArtifactAccuracy M tolerance ∧ seedTransferArtifactAccuracy M tolerance ≤ 1/2 ∧
      seedTransferArtifactAccuracy M tolerance*(|M|+1) ≤ tolerance/256 := by
  have hden : 0<256*(|M|+1) := by positivity
  refine ⟨lt_min (by norm_num) (div_pos ht hden),min_le_left _ _,?_⟩
  have h := (le_div_iff₀ hden).mp (min_le_right (1/2 : ℚ) (tolerance/(256*(|M|+1))))
  change min (1/2 : ℚ) (tolerance/(256*(|M|+1)))*(|M|+1) ≤ tolerance/256
  linarith

noncomputable section
open scoped Quaternion ContDiff

/-- Original `seedTransferArtifactAccuracy_budget` guarantee for the `SeedTransferBudget` construction; the complete source hypotheses are retained. -/
theorem seedTransferArtifactAccuracy_budget (M tolerance : ℚ) (ht : 0<tolerance) :
    (seedTransferArtifactAccuracy M tolerance : ℝ)^2*(343*(1+3*|(M : ℝ)|^2)) ≤ (tolerance : ℝ)^2/32 := by
  let delta : ℝ := seedTransferArtifactAccuracy M tolerance
  let A : ℝ := |(M : ℝ)|
  have hs := seedTransferArtifactAccuracy_spec M tolerance ht
  have hd : 0 ≤ delta := (Rat.cast_pos.mpr hs.1).le
  have htR : (0 : ℝ)<(tolerance : ℝ) := Rat.cast_pos.mpr ht
  have hmul : delta*(A+1) ≤ (tolerance : ℝ)/256 := by
    dsimp only [delta,A]
    exact_mod_cast hs.2.2
  have hsquare : (delta*(A+1))^2 ≤ ((tolerance : ℝ)/256)^2 :=
    (sq_le_sq₀ (by dsimp [A]; positivity) (by positivity)).mpr hmul
  have hfactor : 343*(1+3*A^2) ≤ 1029*(A+1)^2 := by
    have hA : 0 ≤ A := abs_nonneg _
    nlinarith
  have hprod := mul_le_mul_of_nonneg_left hfactor (sq_nonneg delta)
  change delta^2*(343*(1+3*A^2)) ≤ _
  nlinarith

/-- The chosen transfer tolerance controls this same approximate left action
on a smooth finite field, including its ordinary physical derivative energy. -/
theorem seedTransferArtifact_H1_bound (M tolerance : ℚ) (ht : 0<tolerance)
    (A C : ℍ) (hC : ‖C‖=1)
    (hAC : ‖A-C‖ ≤ (seedTransferArtifactAccuracy M tolerance : ℝ))
    (F Q : QuaternionField) (hF : ContDiff ℝ ∞ F) (hQ : ContDiff ℝ ∞ Q)
    (herror : physicalFieldH1Energy (fun X => F X-Q X) ≤ ((tolerance : ℝ)/8)^2/4)
    (henergy : physicalFieldH1Energy Q ≤ 343*(1+3*|(M : ℝ)|^2)) :
    physicalFieldH1Energy (fun X => A*F X-C*Q X) ≤ (tolerance : ℝ)^2/4 := by
  let delta : ℝ := seedTransferArtifactAccuracy M tolerance
  have hs := seedTransferArtifactAccuracy_spec M tolerance ht
  have hd : 0 ≤ delta := (Rat.cast_pos.mpr hs.1).le
  have hd1 : delta ≤ 1/2 := by
    have hh : (seedTransferArtifactAccuracy M tolerance : ℝ) ≤ ((1/2 : ℚ) : ℝ) := Rat.cast_le.mpr hs.2.1
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using hh
  have hA : ‖A‖ ≤ 2 := by
    have h := norm_le_norm_sub_add A C
    rw [hC] at h
    linarith
  have hAsq : ‖A‖^2 ≤ (4 : ℝ) := by nlinarith [norm_nonneg A]
  have hACsq : ‖A-C‖^2 ≤ delta^2 := (sq_le_sq₀ (norm_nonneg _) hd).mpr hAC
  have hE0 := physicalFieldH1Energy_nonneg (fun X => F X-Q X)
  have hQ0 := physicalFieldH1Energy_nonneg Q
  have hfirst : 2*‖A‖^2*physicalFieldH1Energy (fun X => F X-Q X) ≤
      8*physicalFieldH1Energy (fun X => F X-Q X) := by nlinarith
  have hsecond : 2*‖A-C‖^2*physicalFieldH1Energy Q ≤
      2*delta^2*(343*(1+3*|(M : ℝ)|^2)) := by
    calc
      _ ≤ 2*delta^2*physicalFieldH1Energy Q := by gcongr
      _ ≤ _ := by gcongr
  have hbound := physicalFieldH1Energy_transfer_error A C F Q hF hQ
  have hbudget := seedTransferArtifactAccuracy_budget M tolerance ht
  change delta^2*(343*(1+3*|(M : ℝ)|^2)) ≤ _ at hbudget
  nlinarith

end
end Qatlib.Concepts.EffectiveGauge.RationalFlow
