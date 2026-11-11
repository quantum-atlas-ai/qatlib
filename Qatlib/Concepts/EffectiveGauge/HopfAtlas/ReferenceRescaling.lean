/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SourcePhaseLog

set_option backward.isDefEq.respectTransparency false

/-!
# The actual rational unit collar names one fixed physical reference

Different admissible collar widths can define different reference fields.
The source program's chosen unit width eta names the physical target with
width (2*pi)*eta. No equality with a reference using mu/2 is asserted.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Definition of reference Unit Collar in the Hopf Atlas construction. -/
def referenceUnitCollar (mu : ℚ) : ℚ := min (1/8) (mu/14)

/-- Original `referenceUnitCollar_spec` guarantee for the `ReferenceRescaling` construction; the complete source hypotheses are retained. -/
theorem referenceUnitCollar_spec (mu : ℚ) (hm : 0<mu) :
    0<referenceUnitCollar mu ∧ referenceUnitCollar mu ≤ 1/8 ∧ 7*referenceUnitCollar mu ≤ mu/2 := by
  refine ⟨lt_min (by norm_num) (by positivity),min_le_left _ _,?_⟩
  have h := min_le_right (1/8 : ℚ) (mu/14)
  dsimp only [referenceUnitCollar]
  linarith

noncomputable section
open scoped Quaternion ContDiff
open Set

/-- Original `constantCollar_mono` guarantee for the `ReferenceRescaling` construction; the complete source hypotheses are retained. -/
theorem constantCollar_mono {f : QuaternionField} {eta delta : ℝ} {c : ℍ}
    (hf : HasConstantCollar f eta c) (h : delta ≤ eta) : HasConstantCollar f delta c := by
  intro x hx hb
  apply hf x hx
  rcases hb with ⟨j,hj⟩
  exact ⟨j,hj.elim (fun hj => Or.inl (hj.trans h)) (fun hj => Or.inr (by linarith))⟩

/-- Original `support_rescaled_collar` guarantee for the `ReferenceRescaling` construction; the complete source hypotheses are retained. -/
theorem support_rescaled_collar (v : SpatialPoint → SpatialPoint) (B : Set SpatialPoint)
    (hB : ∀ x ∈ B, InFundamentalCube x) (mu : ℝ) (hm : 0<mu)
    (hg : ∀ x ∈ B, ∀ a, OnCubeBoundary a → mu ≤ ‖x-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a ∉ B → b ∉ B → v a=v b)
    (eta : ℚ) (he : 0 ≤ eta) (hmargin : 7*(eta : ℝ) ≤ mu/2) :
    HasConstantCollar (sourceQuaternion v) (physicalPeriod*(eta : ℝ)) (sourceQuaternion v 0) := by
  apply constantCollar_mono (support_background_collar v B hB mu hm hg hoff)
  have hL : physicalPeriod ≤ (7 : ℝ) := by dsimp [physicalPeriod]; linarith [Real.pi_lt_d2]
  have heR : (0 : ℝ) ≤ eta := by exact_mod_cast he
  exact (mul_le_mul_of_nonneg_right hL heR).trans hmargin

/-- Original `gluingCutoff_scaled` guarantee for the `ReferenceRescaling` construction; the complete source hypotheses are retained. -/
theorem gluingCutoff_scaled (eta x : ℝ) (he : 0<eta) (he1 : eta ≤ 1/2) :
    gluingCutoff (physicalPeriod*eta) (physicalPeriod*x)=
      Real.smoothTransition ((x-(1-eta/2))/(eta/4)) := by
  rw [gluingCutoff_eq_backend (by nlinarith [physicalPeriod_pos])]
  congr 1
  field_simp [physicalPeriod_pos.ne',he.ne']

/-- This exact field keeps the source callback and its fixed coarse chart.
Its collar is the actual unit width chosen for the finite value program. -/
def sourcePeriodicReference (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ w, ‖v w‖=1) (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample)
    (hs : OriginalSpinSourceAccurate v source) (m1 m2 eta : ℚ) : QuaternionField :=
  periodicReference v hv (rescaledOriginSeed v source m1 m2)
    (rescaledOriginSeed_spec v hu source hs m1 m2).1 (physicalPeriod*(eta : ℝ))

/-- Original `sourcePeriodicReference_spec` guarantee for the `ReferenceRescaling` construction; the complete source hypotheses are retained. -/
theorem sourcePeriodicReference_spec (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ w, ‖v w‖=1) (hp : IsPeriodicField v)
    (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample) (hs : OriginalSpinSourceAccurate v source)
    (m1 m2 eta : ℚ) (he : 0<eta) (B : Set SpatialPoint)
    (hB : ∀ w ∈ B, InFundamentalCube w) (mu : ℝ) (hm : 0<mu)
    (hg : ∀ w ∈ B, ∀ a, OnCubeBoundary a → mu ≤ ‖w-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a ∉ B → b ∉ B → v a=v b)
    (hmargin : 7*(eta : ℝ) ≤ mu/2) :
    IsPeriodicField (sourcePeriodicReference v hv hu source hs m1 m2 eta) ∧
      IsSmoothUnitLift (sourceQuaternion v) (sourcePeriodicReference v hv hu source hs m1 m2 eta) ∧
      sourcePeriodicReference v hv hu source hs m1 m2 eta 0=rescaledOriginSeed v source m1 m2 := by
  have hc := support_rescaled_collar v B hB mu hm hg hoff eta he.le hmargin
  have heR : 0<(eta : ℝ) := by exact_mod_cast he
  have hpos := mul_pos physicalPeriod_pos heR
  have hseed := rescaledOriginSeed_spec v hu source hs m1 m2
  have hspec := periodicReference_spec v hv hu _ hseed.1 (spin_field_periodic hp) _ hpos _ hc hseed.2.1
  exact ⟨hspec.1,hspec.2,periodicReference_origin v hv hu _ hseed.1 (spin_field_periodic hp) _ hpos _ hc hseed.2.1⟩

/-- On the closed cube, including its upper faces, the periodic target is the
same corrected field. This is needed before comparing finite point values. -/
theorem periodicReference_eq_corrected_on_cube (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ w, ‖v w‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1) (hp : IsPeriodicField (sourceQuaternion v))
    (eta : ℝ) (he : 0<eta) (sc : ℍ) (hc : HasConstantCollar (sourceQuaternion v) eta sc)
    (hi : hopf q₀=sc) (x : SpatialPoint) (hx : InFundamentalCube x) :
    periodicReference v hv q₀ h₀ eta x=correctedReference v hv q₀ h₀ eta x :=
  periodicExtension_eq_on_cube _ _ (gluingWidth_pos he) q₀
    (correctedReference_collar v hv hu q₀ h₀ hp eta he sc hc hi) x hx

end
end Qatlib.Concepts.EffectiveGauge.HopfAtlas
