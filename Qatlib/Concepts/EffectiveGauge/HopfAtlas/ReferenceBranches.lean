/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.EffectiveGauge.HopfAtlas.ReferenceRescaling

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Exact branch formulas for the finite reference-value program

These formulas identify a single periodic target with the actual unit
collar. The transition formula retains the same real terminal phase.
They do not yet certify the rational exp/cutoff/cis implementations.
-/

set_option autoImplicit false
noncomputable section
open scoped Quaternion ContDiff
open Set
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- A point with each coordinate in `[0, 1]` lies in the fundamental cube after multiplication by
the physical period. -/
theorem scaledUnitPoint_cube (u : SpatialPoint) (hu : ∀ j, u j ∈ Icc 0 1) :
    InFundamentalCube (physicalPeriod • u) := by
  intro j
  change 0 ≤ physicalPeriod*u j ∧ physicalPeriod*u j ≤ physicalPeriod
  exact ⟨mul_nonneg physicalPeriod_pos.le (hu j).1,
    by simpa only [mul_one] using mul_le_mul_of_nonneg_left (hu j).2 physicalPeriod_pos.le⟩

/-- Quaternion phase converts addition of real angles into quaternion multiplication. -/
theorem phase_add (a b : ℝ) : phase (a+b)=phase a*phase b := by
  apply Quaternion.ext
  · simp [phase,iAxis,Real.cos_add]
  · simp [phase,iAxis,Real.sin_add]
    ring
  · simp [phase,iAxis]
  · simp [phase,iAxis]

/-- When `eta ≤ 1/2`, the physical gluing width at scale `physicalPeriod * eta` is
`physicalPeriod * eta / 4`. -/
private theorem scaled_width (eta : ℝ) (he1 : eta ≤ 1/2) :
    gluingWidth (physicalPeriod*eta)=physicalPeriod*eta/4 :=
  gluingWidth_eq_quarter (by nlinarith [physicalPeriod_pos])

/-- For a smooth unit source with a constant physical collar and a unit seed, the raw spatial lift
on the rear collar of the fundamental cube equals the corresponding transverse transport path at
its terminal time. -/
private theorem raw_end_on_collar (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ w, ‖v w‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1) (eta : ℝ) (sc : ℍ)
    (hc : HasConstantCollar (sourceQuaternion v) eta sc) (x : SpatialPoint)
    (hx : InFundamentalCube x) (hnear : physicalPeriod-eta ≤ x 0) :
    sourceLiftSpatialExtension v hv q₀ h₀ x=
      sourceLiftPaths v hv q₀ h₀ (transverseProjection x) transportFinish := by
  have hconst : ∀ t ∈ Icc (x 0) physicalPeriod,
      sourceQuaternion v (sourcePosition (transverseProjection x,t))=sc := by
    intro t ht
    apply hc _ ?_ ⟨0,Or.inr (hnear.trans ht.1)⟩
    intro j
    fin_cases j
    · exact ⟨(hx 0).1.trans ht.1,ht.2⟩
    · exact hx 1
    · exact hx 2
  have hpath := sourceLiftPaths_eq_of_source_constant v hv hu q₀ h₀ _
    ⟨x 0,hx 0⟩ transportFinish (hx 0).2 sc hconst
  change sourceLiftExtension v hv q₀ h₀ ((sourcePositionInverse x).1,x 0)=_
  rw [sourceLiftExtension_eq v hv hu q₀ h₀ _ ⟨x 0,hx 0⟩]
  exact hpath.symm

/-- For a smooth periodic unit source with a constant collar and a unit seed lying over its collar
spin, the periodic reference agrees with the raw lift at scaled unit-cube points with longitudinal
coordinate at most `1 - eta / 2`. This branch formula assumes `0 < eta ≤ 1/2`. -/
theorem unitReference_front (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ w, ‖v w‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1) (hp : IsPeriodicField (sourceQuaternion v))
    (eta : ℝ) (he : 0<eta) (he1 : eta ≤ 1/2) (sc : ℍ)
    (hc : HasConstantCollar (sourceQuaternion v) (physicalPeriod*eta) sc) (hi : hopf q₀=sc)
    (u : SpatialPoint) (hx : ∀ j, u j ∈ Icc 0 1) (hfront : u 0 ≤ 1-eta/2) :
    periodicReference v hv q₀ h₀ (physicalPeriod*eta) (physicalPeriod • u)=
      sourceLiftSpatialExtension v hv q₀ h₀ (physicalPeriod • u) := by
  rw [periodicReference_eq_corrected_on_cube v hv hu q₀ h₀ hp _ (mul_pos physicalPeriod_pos he) sc hc hi _ (scaledUnitPoint_cube u hx)]
  have hz : gluingCutoff (physicalPeriod*eta) ((physicalPeriod • u) 0)=0 := by
    rw [show (physicalPeriod • u) 0=physicalPeriod*(u 0) by rfl,gluingCutoff_scaled eta (u 0) he he1]
    exact Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))
  unfold correctedReference
  rw [hz,zero_mul]
  simp [phase]

/-- For a smooth periodic unit source with a constant collar and a unit seed lying over its collar
spin, the periodic reference equals that seed at scaled unit-cube points with first coordinate at
least `1 - eta / 4`, when `0 < eta ≤ 1/2`. -/
theorem unitReference_back (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ w, ‖v w‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1) (hp : IsPeriodicField (sourceQuaternion v))
    (eta : ℝ) (he : 0<eta) (he1 : eta ≤ 1/2) (sc : ℍ)
    (hc : HasConstantCollar (sourceQuaternion v) (physicalPeriod*eta) sc) (hi : hopf q₀=sc)
    (u : SpatialPoint) (hx : ∀ j, u j ∈ Icc 0 1) (hback : 1-eta/4 ≤ u 0) :
    periodicReference v hv q₀ h₀ (physicalPeriod*eta) (physicalPeriod • u)=q₀ := by
  rw [periodicReference_eq_corrected_on_cube v hv hu q₀ h₀ hp _ (mul_pos physicalPeriod_pos he) sc hc hi _ (scaledUnitPoint_cube u hx)]
  apply correctedReference_right_collar v hv hu q₀ h₀ hp _ (mul_pos physicalPeriod_pos he) sc hc hi _ (scaledUnitPoint_cube u hx)
  rw [scaled_width eta he1]
  change physicalPeriod-physicalPeriod*eta/4 ≤ physicalPeriod*(u 0)
  nlinarith [physicalPeriod_pos]

/-- For a smooth periodic unit source with a constant collar of width `physicalPeriod * eta`, the
periodic reference equals the given unit seed over the collar spin at any scaled unit-cube point
within normalized distance `eta` of a transverse face. Here `eta` is positive. -/
theorem unitReference_transverse (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ w, ‖v w‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1) (hp : IsPeriodicField (sourceQuaternion v))
    (eta : ℝ) (he : 0<eta) (sc : ℍ)
    (hc : HasConstantCollar (sourceQuaternion v) (physicalPeriod*eta) sc) (hi : hopf q₀=sc)
    (u : SpatialPoint) (hx : ∀ j, u j ∈ Icc 0 1)
    (hb : u 1 ≤ eta ∨ 1-eta ≤ u 1 ∨ u 2 ≤ eta ∨ 1-eta ≤ u 2) :
    periodicReference v hv q₀ h₀ (physicalPeriod*eta) (physicalPeriod • u)=q₀ := by
  rw [periodicReference_eq_corrected_on_cube v hv hu q₀ h₀ hp _ (mul_pos physicalPeriod_pos he) sc hc hi _ (scaledUnitPoint_cube u hx)]
  apply correctedReference_transverse_collar v hv hu q₀ h₀ hp _ (mul_pos physicalPeriod_pos he) sc hc hi _ (scaledUnitPoint_cube u hx)
  rcases hb with h | h | h | h
  · exact ⟨0,Or.inl (mul_le_mul_of_nonneg_left h physicalPeriod_pos.le)⟩
  · refine ⟨0,Or.inr ?_⟩
    change physicalPeriod-physicalPeriod*eta ≤ physicalPeriod*(u 1)
    nlinarith [physicalPeriod_pos]
  · exact ⟨1,Or.inl (mul_le_mul_of_nonneg_left h physicalPeriod_pos.le)⟩
  · refine ⟨1,Or.inr ?_⟩
    change physicalPeriod-physicalPeriod*eta ≤ physicalPeriod*(u 2)
    nlinarith [physicalPeriod_pos]

/-- At every actual transition point the exact value is exp(i*(1-rho)*lambda)
times the fixed initial seed. Lambda is the same real integral as before. -/
theorem unitReference_transition (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ w, ‖v w‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1) (hp : IsPeriodicField (sourceQuaternion v))
    (eta : ℝ) (he : 0<eta) (he1 : eta ≤ 1/2) (sc : ℍ)
    (hc : HasConstantCollar (sourceQuaternion v) (physicalPeriod*eta) sc) (hi : hopf q₀=sc)
    (u : SpatialPoint) (hx : ∀ j, u j ∈ Icc 0 1) (ht : 1-eta/2 ≤ u 0) :
    periodicReference v hv q₀ h₀ (physicalPeriod*eta) (physicalPeriod • u)=
      phase ((1-Real.smoothTransition ((u 0-(1-eta/2))/(eta/4)))*
        terminalRealPhase v hv q₀ h₀ (transverseProjection (physicalPeriod • u)))*q₀ := by
  let p := transverseProjection (physicalPeriod • u)
  let lambda := terminalRealPhase v hv q₀ h₀ p
  have hphase : phase lambda=terminalRatio v hv q₀ h₀ p := by
    simpa only [transversePair_eta] using terminalRealPhase_reconstruct v hv hu q₀ h₀ hp _
      (mul_pos physicalPeriod_pos he) sc hc hi (p 0) (p 1) (scaledUnitPoint_cube u hx 2)
  have hraw : sourceLiftSpatialExtension v hv q₀ h₀ (physicalPeriod • u)=phase lambda*q₀ := by
    have hfinish := raw_end_on_collar v hv hu q₀ h₀ (physicalPeriod*eta) sc hc (physicalPeriod • u)
      (scaledUnitPoint_cube u hx) (by change physicalPeriod-physicalPeriod*eta ≤ physicalPeriod*(u 0); nlinarith [physicalPeriod_pos])
    calc
      _ = sourceLiftPaths v hv q₀ h₀ p transportFinish := hfinish
      _ = (sourceLiftPaths v hv q₀ h₀ p transportFinish*star q₀)*q₀ := by
        rw [mul_assoc,Quaternion.star_mul_self,(normSq_eq_one_iff _).mpr h₀]
        simp
      _ = phase lambda*q₀ := by rw [hphase]; rfl
  rw [periodicReference_eq_corrected_on_cube v hv hu q₀ h₀ hp _ (mul_pos physicalPeriod_pos he) sc hc hi _ (scaledUnitPoint_cube u hx)]
  unfold correctedReference
  rw [hraw,← mul_assoc,← phase_add]
  change phase (-(gluingCutoff (physicalPeriod*eta) (physicalPeriod*(u 0))*lambda)+lambda)*q₀=_
  rw [gluingCutoff_scaled eta (u 0) he he1]
  congr 2
  dsimp [lambda,p]
  ring

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
