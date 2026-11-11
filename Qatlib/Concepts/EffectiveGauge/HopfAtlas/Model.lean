/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Quaternion
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Native fields and conventions for the periodic Clebsch gauge

The spatial derivative is the actual real Fréchet derivative on Euclidean
three-space. Smoothness is C-infinity, not the analytic `omega` order.
These definitions do not supply a reference lift or solve the gauge problem.
-/

set_option autoImplicit false
noncomputable section
open scoped Quaternion RealInnerProductSpace ContDiff

namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Abbreviation for Spatial Point in the Hopf Atlas construction. -/
abbrev SpatialPoint := EuclideanSpace ℝ (Fin 3)
/-- Abbreviation for Quaternion Field in the Hopf Atlas construction. -/
abbrev QuaternionField := SpatialPoint → ℍ

/-- Definition of physical Period in the Hopf Atlas construction. -/
def physicalPeriod : ℝ := 2 * Real.pi

/-- Definition of i Axis in the Hopf Atlas construction. -/
def iAxis : ℍ := ⟨0, 1, 0, 0⟩

/-- Definition of hopf in the Hopf Atlas construction. -/
def hopf (q : ℍ) : ℍ := star q * iAxis * q

/-- Definition of phase in the Hopf Atlas construction. -/
def phase (t : ℝ) : ℍ := Real.cos t • (1 : ℍ) + Real.sin t • iAxis

/-- Definition of connection Value in the Hopf Atlas construction. -/
def connectionValue (q v : ℍ) : ℝ := inner ℝ (iAxis * q) v

/-- Definition of lattice Shift in the Hopf Atlas construction. -/
def latticeShift (n : Fin 3 → ℤ) : SpatialPoint :=
  WithLp.toLp 2 (fun j => physicalPeriod * (n j : ℝ))

/-- Definition of Is Periodic Field in the Hopf Atlas construction. -/
def IsPeriodicField {F : Type*} (f : SpatialPoint → F) : Prop :=
  ∀ x n, f (x + latticeShift n) = f x

/-- Definition of In Fundamental Cube in the Hopf Atlas construction. -/
def InFundamentalCube (x : SpatialPoint) : Prop :=
  ∀ j, 0 ≤ x j ∧ x j ≤ physicalPeriod

/-- The collar condition is only imposed inside one fundamental cube. -/
def HasConstantCollar (s : QuaternionField) (eta : ℝ) (sc : ℍ) : Prop :=
  ∀ x, InFundamentalCube x →
    (∃ j, x j ≤ eta ∨ physicalPeriod - eta ≤ x j) → s x = sc

/-- Definition of Is Smooth Spin in the Hopf Atlas construction. -/
def IsSmoothSpin (s : QuaternionField) : Prop :=
  ContDiff ℝ ∞ s ∧ ∀ x, (s x).re = 0 ∧ ‖s x‖ = 1

/-- Definition of Is Smooth Unit Lift in the Hopf Atlas construction. -/
def IsSmoothUnitLift (s q : QuaternionField) : Prop :=
  ContDiff ℝ ∞ q ∧ ∀ x, ‖q x‖ = 1 ∧ hopf (q x) = s x

/-- Definition of spatial Partial in the Hopf Atlas construction. -/
def spatialPartial (q : QuaternionField) (x : SpatialPoint) (j : Fin 3) : ℍ :=
  fderiv ℝ q x (EuclideanSpace.single j 1)

/-- Definition of connection in the Hopf Atlas construction. -/
def connection (q : QuaternionField) (x : SpatialPoint) (j : Fin 3) : ℝ :=
  connectionValue (q x) (spatialPartial q x j)

/-- Definition of velocity in the Hopf Atlas construction. -/
def velocity (hbar : ℝ) (q : QuaternionField) (x : SpatialPoint) : SpatialPoint :=
  WithLp.toLp 2 (fun j => hbar * connection q x j)

/-- Definition of divergence in the Hopf Atlas construction. -/
def divergence (u : SpatialPoint → SpatialPoint) (x : SpatialPoint) : ℝ :=
  ∑ j, fderiv ℝ (fun y => u y j) x (EuclideanSpace.single j 1)

/-- Definition of Is Solenoidal in the Hopf Atlas construction. -/
def IsSolenoidal (q : QuaternionField) : Prop :=
  ∀ x, divergence (velocity 1 q) x = 0

/-- Original `normSq_eq_one_iff` guarantee for the `Model` construction; the complete source hypotheses are retained. -/
theorem normSq_eq_one_iff (q : ℍ) : Quaternion.normSq q = 1 ↔ ‖q‖ = 1 := by
  rw [Quaternion.normSq_eq_norm_mul_self]
  constructor
  · intro h
    nlinarith [norm_nonneg q]
  · intro h
    rw [h]
    norm_num

/-- Original `norm_iAxis` guarantee for the `Model` construction; the complete source hypotheses are retained. -/
@[simp] theorem norm_iAxis : ‖iAxis‖ = 1 := by
  apply (normSq_eq_one_iff _).mp
  simp [iAxis, Quaternion.normSq_def']

/-- Original `hopf_re` guarantee for the `Model` construction; the complete source hypotheses are retained. -/
theorem hopf_re (q : ℍ) : (hopf q).re = 0 := by
  simp [hopf, iAxis]
  ring

/-- Original `hopf_imI` guarantee for the `Model` construction; the complete source hypotheses are retained. -/
theorem hopf_imI (q : ℍ) :
    (hopf q).imI = q.re^2 + q.imI^2 - q.imJ^2 - q.imK^2 := by
  simp [hopf, iAxis]
  ring

/-- Original `hopf_imJ` guarantee for the `Model` construction; the complete source hypotheses are retained. -/
theorem hopf_imJ (q : ℍ) : (hopf q).imJ = 2*(q.imI*q.imJ-q.re*q.imK) := by
  simp [hopf, iAxis]
  ring

/-- Original `hopf_imK` guarantee for the `Model` construction; the complete source hypotheses are retained. -/
theorem hopf_imK (q : ℍ) : (hopf q).imK = 2*(q.re*q.imJ+q.imI*q.imK) := by
  simp [hopf, iAxis]
  ring

/-- Original `hopf_norm` guarantee for the `Model` construction; the complete source hypotheses are retained. -/
theorem hopf_norm (q : ℍ) : ‖hopf q‖ = ‖q‖^2 := by
  simp [hopf, norm_mul, norm_star, pow_two]

/-- Original `phase_normSq` guarantee for the `Model` construction; the complete source hypotheses are retained. -/
theorem phase_normSq (t : ℝ) : Quaternion.normSq (phase t) = 1 := by
  simp [phase, iAxis, Quaternion.normSq_def']

/-- Original `phase_norm` guarantee for the `Model` construction; the complete source hypotheses are retained. -/
@[simp] theorem phase_norm (t : ℝ) : ‖phase t‖ = 1 :=
  (normSq_eq_one_iff _).mp (phase_normSq t)

/-- Original `phase_axis` guarantee for the `Model` construction; the complete source hypotheses are retained. -/
theorem phase_axis (t : ℝ) : star (phase t)*iAxis*phase t = iAxis := by
  have h := Real.cos_sq_add_sin_sq t
  ext <;> simp [phase, iAxis] <;> nlinarith

/-- Original `hopf_phase` guarantee for the `Model` construction; the complete source hypotheses are retained. -/
theorem hopf_phase (t : ℝ) (q : ℍ) : hopf (phase t*q) = hopf q := by
  unfold hopf
  rw [star_mul]
  calc
    (star q*star (phase t))*iAxis*(phase t*q) =
        star q*(star (phase t)*iAxis*phase t)*q := by simp only [mul_assoc]
    _ = star q*iAxis*q := by rw [phase_axis]

/-- Original `connectionValue_eq` guarantee for the `Model` construction; the complete source hypotheses are retained. -/
theorem connectionValue_eq (q v : ℍ) : connectionValue q v =
    q.re*v.imI-q.imI*v.re+q.imJ*v.imK-q.imK*v.imJ := by
  simp [connectionValue, Quaternion.inner_def, iAxis]
  ring

/-- Tangent algebra underlying the actual derivative gauge law. -/
theorem connectionValue_gauge (t a : ℝ) (q v : ℍ) :
    connectionValue (phase t*q) (phase t*(v+a • (iAxis*q))) =
      connectionValue q v+a*Quaternion.normSq q := by
  calc
    _ = (Real.cos t^2+Real.sin t^2)*(connectionValue q v+a*Quaternion.normSq q) := by
      simp [connectionValue, Quaternion.inner_def, phase, iAxis, Quaternion.normSq_def',
        -Real.cos_sq_add_sin_sq, -Real.sin_sq_add_cos_sq]
      ring
    _ = _ := by rw [Real.cos_sq_add_sin_sq]; simp

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
