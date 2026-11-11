/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.ReferenceRescaling

set_option backward.isDefEq.respectTransparency false

/-! # The supplied zero first-derivative bound certifies the reference shortcut -/

set_option autoImplicit false
noncomputable section
open scoped Quaternion ContDiff
open Set
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Original `raw_eq_initial_of_zero_x` guarantee for the `ZeroReference` construction; the complete source hypotheses are retained. -/
theorem raw_eq_initial_of_zero_x (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ w, ‖v w‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1)
    (hz : ∀ w, InFundamentalCube w → sourceXDerivative v w=0)
    (x : SpatialPoint) (hx : InFundamentalCube x) : sourceLiftSpatialExtension v hv q₀ h₀ x=q₀ := by
  change sourceLiftExtension v hv q₀ h₀ ((sourcePositionInverse x).1,x 0)=q₀
  apply sourceLiftExtension_eq_initial_of_generator_zero v hv hu q₀ h₀ _ _ (hx 0)
  intro t ht
  let w := sourcePosition ((sourcePositionInverse x).1,x 0*t)
  have hw : InFundamentalCube w := by
    intro j
    fin_cases j
    · change 0 ≤ x 0*t ∧ x 0*t ≤ physicalPeriod
      refine ⟨mul_nonneg (hx 0).1 ht.1,?_⟩
      exact (mul_le_mul_of_nonneg_left ht.2 (hx 0).1).trans (by simpa only [mul_one] using (hx 0).2)
    · exact hx 1
    · exact hx 2
  change (x 0) • sourceHorizontalQuaternion v w=0
  simp only [sourceHorizontalQuaternion,horizontalCoefficient,hz w hw,mul_zero,smul_zero]

/-- Original `periodicReference_eq_initial_of_zero_x` guarantee for the `ZeroReference` construction; the complete source hypotheses are retained. -/
theorem periodicReference_eq_initial_of_zero_x (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ w, ‖v w‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1) (hp : IsPeriodicField (sourceQuaternion v))
    (eta : ℝ) (he : 0<eta) (sc : ℍ) (hc : HasConstantCollar (sourceQuaternion v) eta sc) (hi : hopf q₀=sc)
    (hz : ∀ w, InFundamentalCube w → sourceXDerivative v w=0)
    (x : SpatialPoint) (hx : InFundamentalCube x) : periodicReference v hv q₀ h₀ eta x=q₀ := by
  have hraw := raw_eq_initial_of_zero_x v hv hu q₀ h₀ hz
  have hh := sourceLiftSpatialExtension_isSmoothUnitLift v hv hu q₀ h₀ hp eta he sc hc hi
  have hfull : HasConstantCollar (sourceQuaternion v) physicalPeriod sc := by
    intro w hw _
    have hf := (hh.2 w).2
    rw [hraw w hw,hi] at hf
    exact hf.symm
  have hpcoord : ∀ j, 0 ≤ transverseProjection x j ∧ transverseProjection x j ≤ physicalPeriod := by
    intro j
    fin_cases j
    · exact hx 1
    · exact hx 2
  have hphase := terminalRealPhase_boundary_zero v hv hu q₀ h₀ hp physicalPeriod physicalPeriod_pos sc hfull hi
    (transverseProjection x) hpcoord ⟨0,Or.inl (hpcoord 0).2⟩
  rw [periodicReference_eq_corrected_on_cube v hv hu q₀ h₀ hp eta he sc hc hi x hx]
  simp [correctedReference,hphase,hraw x hx,phase]

/-- An input first-bound of zero is used as a mathematical promise about the
original spin derivatives. No comparison of sampled spin values is involved. -/
theorem sourcePeriodicReference_zero_first (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ w, ‖v w‖=1) (hp : IsPeriodicField v)
    (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample) (hs : OriginalSpinSourceAccurate v source)
    (m2 eta : ℚ) (hb : SourceRescalingBounds v 0 (m2 : ℝ)) (he : 0<eta)
    (B : Set SpatialPoint) (hB : ∀ w ∈ B, InFundamentalCube w) (mu : ℝ) (hm : 0<mu)
    (hg : ∀ w ∈ B, ∀ a, OnCubeBoundary a → mu ≤ ‖w-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a ∉ B → b ∉ B → v a=v b)
    (hmargin : 7*(eta : ℝ) ≤ mu/2) (x : SpatialPoint) (hx : InFundamentalCube x) :
    sourcePeriodicReference v hv hu source hs 0 m2 eta x=rescaledOriginSeed v source 0 m2 := by
  have hc := support_rescaled_collar v B hB mu hm hg hoff eta he.le hmargin
  apply periodicReference_eq_initial_of_zero_x v hv hu _ _ (spin_field_periodic hp) _
    (mul_pos physicalPeriod_pos (by exact_mod_cast he)) _ hc (rescaledOriginSeed_spec v hu source hs 0 m2).2.1 _ x hx
  intro w hw
  have hd : fderiv ℝ v w (EuclideanSpace.single 0 1)=0 := norm_le_zero_iff.mp (hb.1 w hw 0)
  rw [sourceXDerivative_eq_spin v hv,hd]
  rfl

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
