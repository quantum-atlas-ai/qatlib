/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.Model
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! # Gauge covariance for actual derivatives, including nonunit inputs -/

set_option autoImplicit false
noncomputable section
open scoped Quaternion RealInnerProductSpace ContDiff

namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Original `contDiff_phase` guarantee for the `Gauge` construction; the complete source hypotheses are retained. -/
theorem contDiff_phase : ContDiff ℝ ∞ phase := by
  have hc : ContDiff ℝ ∞ (fun t : ℝ => Real.cos t • (1 : ℍ)) :=
    Real.contDiff_cos.smul contDiff_const
  have hs : ContDiff ℝ ∞ (fun t : ℝ => Real.sin t • iAxis) :=
    Real.contDiff_sin.smul contDiff_const
  exact hc.add hs

/-- Original `phase_hasDerivAt` guarantee for the `Gauge` construction; the complete source hypotheses are retained. -/
theorem phase_hasDerivAt (t : ℝ) : HasDerivAt phase (iAxis*phase t) t := by
  apply (((Real.hasDerivAt_cos t).smul_const (1 : ℍ)).add
      ((Real.hasDerivAt_sin t).smul_const iAxis)).congr_deriv
  apply Quaternion.ext <;> simp [iAxis, phase]

/-- Original `gauge_hasDerivAt` guarantee for the `Gauge` construction; the complete source hypotheses are retained. -/
theorem gauge_hasDerivAt {q : ℝ → ℍ} {theta : ℝ → ℝ} {v : ℍ} {a t : ℝ}
    (hq : HasDerivAt q v t) (ht : HasDerivAt theta a t) :
    HasDerivAt (fun u => phase (theta u)*q u)
      (phase (theta t)*(v+a • (iAxis*q t))) t := by
  have hp := (phase_hasDerivAt (theta t)).scomp t ht
  have hh := hp.mul hq
  apply hh.congr_deriv
  apply Quaternion.ext <;> simp [Function.comp_def, phase, iAxis] <;> ring

/-- Definition of curve Connection in the Hopf Atlas construction. -/
def curveConnection (q : ℝ → ℍ) (t : ℝ) : ℝ :=
  connectionValue (q t) (deriv q t)

/-- Original `curve_connection_gauge` guarantee for the `Gauge` construction; the complete source hypotheses are retained. -/
theorem curve_connection_gauge {q : ℝ → ℍ} {theta : ℝ → ℝ} {v : ℍ} {a t : ℝ}
    (hq : HasDerivAt q v t) (ht : HasDerivAt theta a t) :
    curveConnection (fun u => phase (theta u)*q u) t =
      curveConnection q t+a*Quaternion.normSq (q t) := by
  unfold curveConnection
  rw [(gauge_hasDerivAt hq ht).deriv, hq.deriv]
  exact connectionValue_gauge (theta t) a (q t) v

/-- Original `curve_connection_gauge_unit` guarantee for the `Gauge` construction; the complete source hypotheses are retained. -/
theorem curve_connection_gauge_unit {q : ℝ → ℍ} {theta : ℝ → ℝ} {v : ℍ} {a t : ℝ}
    (hq : HasDerivAt q v t) (ht : HasDerivAt theta a t) (hu : ‖q t‖ = 1) :
    curveConnection (fun u => phase (theta u)*q u) t = curveConnection q t+a := by
  rw [curve_connection_gauge hq ht, (normSq_eq_one_iff _).mpr hu, mul_one]

/-- Original `line_hasDerivAt` guarantee for the `Gauge` construction; the complete source hypotheses are retained. -/
private theorem line_hasDerivAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : SpatialPoint → F} {x : SpatialPoint} (hf : DifferentiableAt ℝ f x)
    (v : SpatialPoint) : HasDerivAt (fun t : ℝ => f (x+t • v)) (fderiv ℝ f x v) 0 := by
  have hl : HasDerivAt (fun t : ℝ => x+t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hf0 : HasFDerivAt f (fderiv ℝ f x) (x+(0 : ℝ) • v) := by
    simpa using hf.hasFDerivAt
  simpa only [Function.comp_def] using hf0.comp_hasDerivAt (0 : ℝ) hl

/-- Actual spatial Fréchet derivatives, with no assumed derivative oracle. -/
theorem connection_gauge {q : QuaternionField} {theta : SpatialPoint → ℝ} {x : SpatialPoint}
    (hq : DifferentiableAt ℝ q x) (ht : DifferentiableAt ℝ theta x) (j : Fin 3) :
    connection (fun y => phase (theta y)*q y) x j =
      connection q x j+(fderiv ℝ theta x (EuclideanSpace.single j 1))*Quaternion.normSq (q x) := by
  let v : SpatialPoint := EuclideanSpace.single j 1
  have hg : DifferentiableAt ℝ (fun y => phase (theta y)*q y) x :=
    ((phase_hasDerivAt (theta x)).differentiableAt.comp x ht).mul hq
  have h := curve_connection_gauge (line_hasDerivAt hq v) (line_hasDerivAt ht v)
  unfold curveConnection at h
  rw [(line_hasDerivAt hg v).deriv, (line_hasDerivAt hq v).deriv] at h
  simpa [connection, spatialPartial, v] using h

/-- Original `connection_gauge_unit` guarantee for the `Gauge` construction; the complete source hypotheses are retained. -/
theorem connection_gauge_unit {q : QuaternionField} {theta : SpatialPoint → ℝ} {x : SpatialPoint}
    (hq : DifferentiableAt ℝ q x) (ht : DifferentiableAt ℝ theta x) (hu : ‖q x‖ = 1)
    (j : Fin 3) :
    connection (fun y => phase (theta y)*q y) x j =
      connection q x j+fderiv ℝ theta x (EuclideanSpace.single j 1) := by
  rw [connection_gauge hq ht, (normSq_eq_one_iff _).mpr hu, mul_one]

/-- Original `velocity_gauge_unit` guarantee for the `Gauge` construction; the complete source hypotheses are retained. -/
theorem velocity_gauge_unit {q : QuaternionField} {theta : SpatialPoint → ℝ} {x : SpatialPoint}
    (hq : DifferentiableAt ℝ q x) (ht : DifferentiableAt ℝ theta x) (hu : ‖q x‖ = 1)
    (hbar : ℝ) (j : Fin 3) :
    velocity hbar (fun y => phase (theta y)*q y) x j =
      velocity hbar q x j+hbar*(fderiv ℝ theta x (EuclideanSpace.single j 1)) := by
  change hbar*connection (fun y => phase (theta y)*q y) x j =
    hbar*connection q x j+_
  rw [connection_gauge_unit hq ht hu]
  ring

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
