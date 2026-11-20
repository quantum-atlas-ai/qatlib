/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.EffectiveGauge.HopfAtlas.MixedTime

@[expose] public section

/-!
# The actual terminal phase and its transverse boundary values

Equal Hopf images of unit quaternions give a left complex-phase ratio.
The terminal ratio is built from the source transport. Its boundary value
is proved from the original source collar, not assumed for the lift.
-/

set_option autoImplicit false
noncomputable section
open scoped Quaternion RealInnerProductSpace Topology ContDiff
open Set
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Definition of Is Circle Quaternion in the Hopf Atlas construction. -/
def IsCircleQuaternion (q : ℍ) : Prop := ‖q‖=1 ∧ q.imJ=0 ∧ q.imK=0

/-- Definition of fibre Ratio in the Hopf Atlas construction. -/
def fibreRatio (q r : ℍ) : ℍ := q*star r

/-- The fibre ratio `q * star r` of two unit quaternions has unit norm. -/
theorem fibreRatio_norm (q r : ℍ) (hq : ‖q‖=1) (hr : ‖r‖=1) : ‖fibreRatio q r‖=1 := by
  simp [fibreRatio, norm_mul, norm_star, hq, hr]

/-- The fibre ratio of two unit quaternions with the same Hopf image commutes with `iAxis`. -/
theorem fibreRatio_axis (q r : ℍ) (hq : ‖q‖=1) (hr : ‖r‖=1) (hh : hopf q=hopf r) :
    iAxis*fibreRatio q r=fibreRatio q r*iAxis := by
  have hqu : q*star q=1 := by
    rw [Quaternion.self_mul_star, (normSq_eq_one_iff _).mpr hq]; rfl
  have hru : r*star r=1 := by
    rw [Quaternion.self_mul_star, (normSq_eq_one_iff _).mpr hr]; rfl
  calc
    _ = (q*star q)*iAxis*(q*star r) := by rw [hqu, one_mul]; rfl
    _ = q*hopf q*star r := by simp only [hopf, mul_assoc]
    _ = q*hopf r*star r := by rw [hh]
    _ = (q*star r)*iAxis*(r*star r) := by simp only [hopf, mul_assoc]
    _ = _ := by rw [hru, mul_one]; rfl

/-- A quaternion that commutes with `iAxis` has zero `j` and `k` components. -/
theorem axis_commute_coordinates (q : ℍ) (h : iAxis*q=q*iAxis) : q.imJ=0 ∧ q.imK=0 := by
  have hj := congrArg (fun r : ℍ => r.imJ) h
  have hk := congrArg (fun r : ℍ => r.imK) h
  simp [iAxis] at hj hk
  constructor <;> linarith

/-- Two unit quaternions with the same Hopf image have a fibre ratio in the quaternion unit circle
in the real-`i` plane. -/
theorem fibreRatio_circle (q r : ℍ) (hq : ‖q‖=1) (hr : ‖r‖=1) (hh : hopf q=hopf r) :
    IsCircleQuaternion (fibreRatio q r) :=
  ⟨fibreRatio_norm q r hq hr, axis_commute_coordinates _ (fibreRatio_axis q r hq hr hh)⟩

/-- Constancy of the actual source on a physical time subinterval forces
constancy of the constructed horizontal path on that interval. -/
theorem sourceLiftPaths_eq_of_source_constant (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ x, ‖v x‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1) (p : TransversePoint)
    (a b : TransportTime) (hab : (a : ℝ) ≤ b) (sc : ℍ)
    (hs : ∀ u ∈ Icc (a : ℝ) b, sourceQuaternion v (sourcePosition (p,u))=sc) :
    sourceLiftPaths v hv q₀ h₀ p b=sourceLiftPaths v hv q₀ h₀ p a := by
  rcases hab.eq_or_lt with he | hlt
  · have he' : a=b := Subtype.ext he
    rw [he']
  let q := extendPath (sourceLiftPaths v hv q₀ h₀ p)
  have hsub : Icc (a : ℝ) b ⊆ Icc 0 physicalPeriod :=
    fun _ ht => ⟨a.2.1.trans ht.1, ht.2.trans b.2.2⟩
  have hds : ∀ u ∈ Icc (a : ℝ) b, sourceXDerivative v (sourcePosition (p,u))=0 := by
    intro u ht
    have hc : HasDerivWithinAt (fun z : ℝ => sourceQuaternion v (sourcePosition (p,z))) 0
        (Icc (a : ℝ) b) u :=
      (hasDerivAt_const u sc).hasDerivWithinAt.congr_of_mem hs ht
    exact UniqueDiffWithinAt.eq_deriv (Icc (a : ℝ) b) (uniqueDiffOn_Icc hlt u ht)
      (sourceCurve_hasDerivAt hv p u).hasDerivWithinAt hc
  have hq : ∀ u ∈ Icc (a : ℝ) b, HasDerivWithinAt q (q u*(0 : ℍ)) (Icc (a : ℝ) b) u := by
    intro u ht
    have h := (sourceLiftPaths_hasDerivWithinAt v hv hu q₀ h₀ p u (hsub ht)).mono hsub
    simpa only [sourceHorizontalQuaternion, horizontalCoefficient, hds u ht, mul_zero, smul_zero] using h
  have hn : ∀ u ∈ Icc (a : ℝ) b, ‖q u‖=1 := by
    intro u ht
    simpa only [q, sourceLiftPaths, extendPath_on _ u (hsub ht)] using
      pathTransport_unit q₀ h₀ (horizontalCoefficientPaths v hv p) ⟨u,hsub ht⟩
  have hr : ∀ u ∈ Icc (a : ℝ) b,
      HasDerivWithinAt (fun _ : ℝ => q a) (q a*(0 : ℍ)) (Icc (a : ℝ) b) u := by
    intro u _
    simpa only [mul_zero] using (hasDerivAt_const u (q a)).hasDerivWithinAt
  have h := unit_transport_stability hab (k := fun _ => (0 : ℍ)) (l := fun _ => (0 : ℍ))
    continuousOn_const continuousOn_const hq hr (fun _ _ => rfl) hn
    (fun _ _ => hn a ⟨le_rfl,hab⟩) rfl (E := 0) (by intro u _; simp)
  have he : q a=q b := sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (by simpa using h) (norm_nonneg _)))
  simpa only [q, extendPath_coe] using he.symm

/-- Definition of terminal Ratio in the Hopf Atlas construction. -/
def terminalRatio (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (q₀ : ℍ) (h₀ : ‖q₀‖=1) (p : TransversePoint) : ℍ :=
  fibreRatio (sourceLiftPaths v hv q₀ h₀ p transportFinish) q₀

/-- The terminal ratio as a function of the two transverse coordinates is smooth for a smooth
source field and a unit seed. -/
theorem contDiff_terminalRatio (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (q₀ : ℍ) (h₀ : ‖q₀‖=1) : ContDiff ℝ ∞ (terminalRatio v hv q₀ h₀) := by
  have he : ContDiff ℝ ∞ (ContinuousMap.evalCLM ℝ transportFinish : QuaternionPath → ℍ) := by
    exact ContinuousLinearMap.contDiff _
  exact (he.comp (contDiff_sourceLiftPaths v hv q₀ h₀)).mul contDiff_const

/-- A periodic quaternion field with constant value `sc` on a positive-width collar equals `sc` on
the final longitudinal face for every transverse address. -/
theorem collar_final_face (s : QuaternionField) (hp : IsPeriodicField s)
    (eta : ℝ) (he : 0<eta) (sc : ℍ) (hc : HasConstantCollar s eta sc)
    (p : TransversePoint) : s (sourcePosition (p,physicalPeriod))=sc := by
  have hpos : sourcePosition (p,physicalPeriod)=sourcePosition (p,0)+latticeShift ![1,0,0] := by
    change (WithLp.toLp 2 ![physicalPeriod,p 0,p 1] : SpatialPoint)=
      WithLp.toLp 2 ![0,p 0,p 1]+latticeShift ![1,0,0]
    ext j
    fin_cases j <;> simp [latticeShift]
  rw [hpos, hp]
  exact collar_initial_face s hp eta he sc hc p

/-- For a smooth unit source with periodic spin and a positive-width constant collar, a unit seed
over the collar spin yields a unit-circle terminal ratio at every transverse point. -/
theorem terminalRatio_circle (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ x, ‖v x‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1)
    (hp : IsPeriodicField (sourceQuaternion v)) (eta : ℝ) (he : 0<eta) (sc : ℍ)
    (hc : HasConstantCollar (sourceQuaternion v) eta sc) (hi : hopf q₀=sc) (p : TransversePoint) :
    IsCircleQuaternion (terminalRatio v hv q₀ h₀ p) := by
  apply fibreRatio_circle _ q₀ (pathTransport_unit q₀ h₀ _ transportFinish) h₀
  exact (sourceLiftPaths_hopf v hv hu q₀ h₀ p
    (hi.trans (collar_initial_face _ hp eta he sc hc p).symm) transportFinish).trans
      ((collar_final_face _ hp eta he sc hc p).trans hi.symm)

/-- For a smooth unit source with a constant collar and a unit seed, the terminal ratio is one at
each point of the transverse physical square with at least one coordinate in the collar. -/
theorem terminalRatio_boundary (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ x, ‖v x‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1) (eta : ℝ) (sc : ℍ)
    (hc : HasConstantCollar (sourceQuaternion v) eta sc) (p : TransversePoint)
    (hsq : ∀ j, 0 ≤ p j ∧ p j ≤ physicalPeriod)
    (hb : ∃ j, p j ≤ eta ∨ physicalPeriod-eta ≤ p j) : terminalRatio v hv q₀ h₀ p=1 := by
  have hs : ∀ u ∈ Icc (0 : ℝ) physicalPeriod, sourceQuaternion v (sourcePosition (p,u))=sc := by
    intro u ht
    apply hc
    · intro j
      fin_cases j
      · exact ht
      · exact hsq 0
      · exact hsq 1
    · rcases hb with ⟨j,hj⟩
      fin_cases j
      · exact ⟨1,hj⟩
      · exact ⟨2,hj⟩
  have h := sourceLiftPaths_eq_of_source_constant v hv hu q₀ h₀ p transportStart transportFinish
    physicalPeriod_pos.le sc hs
  have hstart : sourceLiftPaths v hv q₀ h₀ p transportStart=q₀ := pathTransport_start q₀ h₀ _
  change sourceLiftPaths v hv q₀ h₀ p transportFinish*star q₀=1
  rw [h,hstart,Quaternion.self_mul_star,(normSq_eq_one_iff _).mpr h₀]
  rfl

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
