/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.CircleLogReconstruction
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# A concrete smooth correction which is constant at all six physical faces

The flat step is the same exp(-1/t) ratio used by the effective backend.
A safely reduced collar width gives a positive gluing margin for any
positive input collar. This module does not yet periodize the field.
-/

set_option autoImplicit false
noncomputable section
open scoped Quaternion RealInnerProductSpace Topology ContDiff
open Set
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Definition of gluing Width in the Hopf Atlas construction. -/
def gluingWidth (eta : ℝ) : ℝ := min (eta/4) (physicalPeriod/8)

/-- Original `gluingWidth_pos` guarantee for the `CollarGluing` construction; the complete source hypotheses are retained. -/
theorem gluingWidth_pos {eta : ℝ} (he : 0<eta) : 0<gluingWidth eta :=
  lt_min (div_pos he (by norm_num)) (div_pos physicalPeriod_pos (by norm_num))

/-- Original `gluingWidth_le_eta` guarantee for the `CollarGluing` construction; the complete source hypotheses are retained. -/
theorem gluingWidth_le_eta {eta : ℝ} (he : 0<eta) : gluingWidth eta ≤ eta := by
  have h := min_le_left (eta/4) (physicalPeriod/8)
  dsimp [gluingWidth]
  linarith

/-- Original `gluingWidth_le_period` guarantee for the `CollarGluing` construction; the complete source hypotheses are retained. -/
theorem gluingWidth_le_period (eta : ℝ) : gluingWidth eta ≤ physicalPeriod/8 := min_le_right _ _

/-- Original `gluingWidth_eq_quarter` guarantee for the `CollarGluing` construction; the complete source hypotheses are retained. -/
theorem gluingWidth_eq_quarter {eta : ℝ} (he : eta ≤ physicalPeriod/2) : gluingWidth eta=eta/4 := by
  apply min_eq_left
  linarith

/-- Definition of gluing Cutoff in the Hopf Atlas construction. -/
def gluingCutoff (eta x : ℝ) : ℝ :=
  Real.smoothTransition ((x-(physicalPeriod-2*gluingWidth eta))/gluingWidth eta)

/-- Original `contDiff_gluingCutoff` guarantee for the `CollarGluing` construction; the complete source hypotheses are retained. -/
theorem contDiff_gluingCutoff (eta : ℝ) : ContDiff ℝ ∞ (gluingCutoff eta) :=
  (Real.smoothTransition.contDiff (n := ⊤)).comp ((contDiff_id.sub contDiff_const).div_const _)

/-- Original `gluingCutoff_zero` guarantee for the `CollarGluing` construction; the complete source hypotheses are retained. -/
theorem gluingCutoff_zero {eta x : ℝ} (he : 0<eta) (hx : x ≤ physicalPeriod-2*gluingWidth eta) :
    gluingCutoff eta x=0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) (gluingWidth_pos he).le

/-- Original `gluingCutoff_one` guarantee for the `CollarGluing` construction; the complete source hypotheses are retained. -/
theorem gluingCutoff_one {eta x : ℝ} (he : 0<eta) (hx : physicalPeriod-gluingWidth eta ≤ x) :
    gluingCutoff eta x=1 := by
  apply Real.smoothTransition.one_of_one_le
  apply (le_div_iff₀ (gluingWidth_pos he)).mpr
  linarith

/-- Original `gluingCutoff_eq_backend` guarantee for the `CollarGluing` construction; the complete source hypotheses are retained. -/
theorem gluingCutoff_eq_backend {eta : ℝ} (he : eta ≤ physicalPeriod/2) (x : ℝ) :
    gluingCutoff eta x=Real.smoothTransition ((x-(physicalPeriod-eta/2))/(eta/4)) := by
  unfold gluingCutoff
  rw [gluingWidth_eq_quarter he]
  congr 2
  ring

/-- Definition of transverse Projection in the Hopf Atlas construction. -/
def transverseProjection : SpatialPoint →L[ℝ] TransversePoint :=
  (ContinuousLinearMap.fst ℝ TransversePoint ℝ).comp sourcePositionInverse

/-- Definition of corrected Reference in the Hopf Atlas construction. -/
def correctedReference (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (q₀ : ℍ) (h₀ : ‖q₀‖=1) (eta : ℝ) (x : SpatialPoint) : ℍ :=
  phase (-(gluingCutoff eta (x 0)*terminalRealPhase v hv q₀ h₀ (transverseProjection x)))*
    sourceLiftSpatialExtension v hv q₀ h₀ x

/-- Original `contDiff_correctedReference` guarantee for the `CollarGluing` construction; the complete source hypotheses are retained. -/
theorem contDiff_correctedReference (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (q₀ : ℍ) (h₀ : ‖q₀‖=1) (eta : ℝ) : ContDiff ℝ ∞ (correctedReference v hv q₀ h₀ eta) := by
  have hx : ContDiff ℝ ∞ (EuclideanSpace.proj (0 : Fin 3) : SpatialPoint → ℝ) := by
    exact ContinuousLinearMap.contDiff _
  exact (contDiff_phase.comp (((contDiff_gluingCutoff eta).comp hx).mul
    ((contDiff_terminalRealPhase v hv q₀ h₀).comp transverseProjection.contDiff)).neg).mul
      (contDiff_sourceLiftSpatialExtension v hv q₀ h₀)

/-- Original `correctedReference_isSmoothUnitLift` guarantee for the `CollarGluing` construction; the complete source hypotheses are retained. -/
theorem correctedReference_isSmoothUnitLift (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ x, ‖v x‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1)
    (hp : IsPeriodicField (sourceQuaternion v)) (eta : ℝ) (he : 0<eta) (sc : ℍ)
    (hc : HasConstantCollar (sourceQuaternion v) eta sc) (hi : hopf q₀=sc) :
    IsSmoothUnitLift (sourceQuaternion v) (correctedReference v hv q₀ h₀ eta) := by
  have h := sourceLiftSpatialExtension_isSmoothUnitLift v hv hu q₀ h₀ hp eta he sc hc hi
  refine ⟨contDiff_correctedReference v hv q₀ h₀ eta, fun x => ?_⟩
  exact ⟨by simp [correctedReference,norm_mul,phase_norm,(h.2 x).1],
    (hopf_phase _ _).trans (h.2 x).2⟩

/-- Original `phase_neg_star` guarantee for the `CollarGluing` construction; the complete source hypotheses are retained. -/
private theorem phase_neg_star (t : ℝ) : phase (-t)=star (phase t) := by
  ext <;> simp [phase,iAxis]

/-- Original `cube_transverse` guarantee for the `CollarGluing` construction; the complete source hypotheses are retained. -/
private theorem cube_transverse {x : SpatialPoint} (hx : InFundamentalCube x) :
    ∀ j, 0 ≤ transverseProjection x j ∧ transverseProjection x j ≤ physicalPeriod := by
  intro j
  fin_cases j
  · exact hx 1
  · exact hx 2

/-- Original `cube_line` guarantee for the `CollarGluing` construction; the complete source hypotheses are retained. -/
private theorem cube_line (p : TransversePoint) (hp : ∀ j, 0 ≤ p j ∧ p j ≤ physicalPeriod)
    (u : ℝ) (hu : 0 ≤ u ∧ u ≤ physicalPeriod) : InFundamentalCube (sourcePosition (p,u)) := by
  intro j
  fin_cases j
  · exact hu
  · exact hp 0
  · exact hp 1

/-- Original `raw_eq_path` guarantee for the `CollarGluing` construction; the complete source hypotheses are retained. -/
private theorem raw_eq_path (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ x, ‖v x‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1) (x : SpatialPoint) (hx : 0 ≤ x 0 ∧ x 0 ≤ physicalPeriod) :
    sourceLiftSpatialExtension v hv q₀ h₀ x=sourceLiftPaths v hv q₀ h₀ (transverseProjection x) ⟨x 0,hx⟩ :=
  sourceLiftExtension_eq v hv hu q₀ h₀ (transverseProjection x) ⟨x 0,hx⟩

/-- Original `raw_initial_of_constant` guarantee for the `CollarGluing` construction; the complete source hypotheses are retained. -/
private theorem raw_initial_of_constant (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ x, ‖v x‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1) (x : SpatialPoint) (hx : 0 ≤ x 0 ∧ x 0 ≤ physicalPeriod)
    (sc : ℍ) (hs : ∀ u ∈ Icc (0 : ℝ) (x 0), sourceQuaternion v (sourcePosition (transverseProjection x,u))=sc) :
    sourceLiftSpatialExtension v hv q₀ h₀ x=q₀ := by
  rw [raw_eq_path v hv hu q₀ h₀ x hx,
    sourceLiftPaths_eq_of_source_constant v hv hu q₀ h₀ _ transportStart ⟨x 0,hx⟩ hx.1 sc hs]
  exact pathTransport_start q₀ h₀ _

/-- Original `correctedReference_left_collar` guarantee for the `CollarGluing` construction; the complete source hypotheses are retained. -/
theorem correctedReference_left_collar (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ x, ‖v x‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1) (eta : ℝ) (he : 0<eta) (sc : ℍ)
    (hc : HasConstantCollar (sourceQuaternion v) eta sc) (x : SpatialPoint)
    (hx : InFundamentalCube x) (hleft : x 0 ≤ gluingWidth eta) : correctedReference v hv q₀ h₀ eta x=q₀ := by
  have hcut : gluingCutoff eta (x 0)=0 := gluingCutoff_zero he (by
    have h := gluingWidth_le_period eta
    linarith [physicalPeriod_pos])
  have hraw : sourceLiftSpatialExtension v hv q₀ h₀ x=q₀ := by
    apply raw_initial_of_constant v hv hu q₀ h₀ x (hx 0) sc
    intro u hu'
    exact hc _ (cube_line _ (cube_transverse hx) u ⟨hu'.1,hu'.2.trans (hx 0).2⟩)
      ⟨0,Or.inl (hu'.2.trans (hleft.trans (gluingWidth_le_eta he)))⟩
  simp [correctedReference,hcut,hraw,phase]

/-- Original `correctedReference_right_collar` guarantee for the `CollarGluing` construction; the complete source hypotheses are retained. -/
theorem correctedReference_right_collar (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ x, ‖v x‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1)
    (hp : IsPeriodicField (sourceQuaternion v)) (eta : ℝ) (he : 0<eta) (sc : ℍ)
    (hc : HasConstantCollar (sourceQuaternion v) eta sc) (hi : hopf q₀=sc) (x : SpatialPoint)
    (hx : InFundamentalCube x) (hright : physicalPeriod-gluingWidth eta ≤ x 0) :
    correctedReference v hv q₀ h₀ eta x=q₀ := by
  let p := transverseProjection x
  have hconst : ∀ u ∈ Icc (x 0) physicalPeriod, sourceQuaternion v (sourcePosition (p,u))=sc := by
    intro u hu'
    apply hc _ (cube_line p (cube_transverse hx) u ⟨(hx 0).1.trans hu'.1,hu'.2⟩)
    exact ⟨0,Or.inr ((sub_le_sub_left (gluingWidth_le_eta he) physicalPeriod).trans (hright.trans hu'.1))⟩
  have hpath := sourceLiftPaths_eq_of_source_constant v hv hu q₀ h₀ p ⟨x 0,hx 0⟩ transportFinish (hx 0).2 sc hconst
  have hraw : sourceLiftSpatialExtension v hv q₀ h₀ x=sourceLiftPaths v hv q₀ h₀ p transportFinish := by
    rw [raw_eq_path v hv hu q₀ h₀ x (hx 0)]
    exact hpath.symm
  have hphase : phase (terminalRealPhase v hv q₀ h₀ p)=terminalRatio v hv q₀ h₀ p := by
    simpa only [transversePair_eta] using terminalRealPhase_reconstruct v hv hu q₀ h₀ hp eta he sc hc hi
      (p 0) (p 1) (cube_transverse hx 1)
  change phase (-(gluingCutoff eta (x 0)*terminalRealPhase v hv q₀ h₀ p))*
    sourceLiftSpatialExtension v hv q₀ h₀ x=q₀
  rw [gluingCutoff_one he hright,one_mul,phase_neg_star,hphase,hraw]
  change star (sourceLiftPaths v hv q₀ h₀ p transportFinish*star q₀)*
    sourceLiftPaths v hv q₀ h₀ p transportFinish=q₀
  have hn : ‖sourceLiftPaths v hv q₀ h₀ p transportFinish‖=1 := pathTransport_unit q₀ h₀ _ transportFinish
  rw [star_mul,star_star,mul_assoc,Quaternion.star_mul_self,(normSq_eq_one_iff _).mpr hn]
  simp

/-- Original `correctedReference_transverse_collar` guarantee for the `CollarGluing` construction; the complete source hypotheses are retained. -/
theorem correctedReference_transverse_collar (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ x, ‖v x‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1)
    (hp : IsPeriodicField (sourceQuaternion v)) (eta : ℝ) (he : 0<eta) (sc : ℍ)
    (hc : HasConstantCollar (sourceQuaternion v) eta sc) (hi : hopf q₀=sc) (x : SpatialPoint)
    (hx : InFundamentalCube x)
    (hb : ∃ j, transverseProjection x j ≤ eta ∨ physicalPeriod-eta ≤ transverseProjection x j) :
    correctedReference v hv q₀ h₀ eta x=q₀ := by
  have ht := terminalRealPhase_boundary_zero v hv hu q₀ h₀ hp eta he sc hc hi _ (cube_transverse hx) hb
  have hraw : sourceLiftSpatialExtension v hv q₀ h₀ x=q₀ := by
    apply raw_initial_of_constant v hv hu q₀ h₀ x (hx 0) sc
    intro u hu'
    apply hc _ (cube_line _ (cube_transverse hx) u ⟨hu'.1,hu'.2.trans (hx 0).2⟩)
    rcases hb with ⟨j,hj⟩
    fin_cases j
    · exact ⟨1,hj⟩
    · exact ⟨2,hj⟩
  simp [correctedReference,ht,hraw,phase]

/-- Original `correctedReference_collar` guarantee for the `CollarGluing` construction; the complete source hypotheses are retained. -/
theorem correctedReference_collar (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ x, ‖v x‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1)
    (hp : IsPeriodicField (sourceQuaternion v)) (eta : ℝ) (he : 0<eta) (sc : ℍ)
    (hc : HasConstantCollar (sourceQuaternion v) eta sc) (hi : hopf q₀=sc) :
    HasConstantCollar (correctedReference v hv q₀ h₀ eta) (gluingWidth eta) q₀ := by
  intro x hx hb
  rcases hb with ⟨j,hj⟩
  fin_cases j
  · rcases hj with hj | hj
    · exact correctedReference_left_collar v hv hu q₀ h₀ eta he sc hc x hx hj
    · exact correctedReference_right_collar v hv hu q₀ h₀ hp eta he sc hc hi x hx hj
  · apply correctedReference_transverse_collar v hv hu q₀ h₀ hp eta he sc hc hi x hx
    refine ⟨0,?_⟩
    exact hj.elim (fun h => Or.inl (h.trans (gluingWidth_le_eta he)))
      (fun h => Or.inr ((sub_le_sub_left (gluingWidth_le_eta he) physicalPeriod).trans h))
  · apply correctedReference_transverse_collar v hv hu q₀ h₀ hp eta he sc hc hi x hx
    refine ⟨1,?_⟩
    exact hj.elim (fun h => Or.inl (h.trans (gluingWidth_le_eta he)))
      (fun h => Or.inr ((sub_le_sub_left (gluingWidth_le_eta he) physicalPeriod).trans h))

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
