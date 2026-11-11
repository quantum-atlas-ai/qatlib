/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.PeriodicExtension

/-!
# From the original separated support region to a source-generated reference

The input support is only used inside the fundamental cube. A positive
Euclidean separation from every cube face yields the collar promise;
the constant background is the actual source value at the origin.
The theorem works for a general support set, including the given closed ball.
-/

set_option autoImplicit false
noncomputable section
open scoped Quaternion RealInnerProductSpace Topology ContDiff
open Set
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Definition of On Cube Boundary in the Hopf Atlas construction. -/
def OnCubeBoundary (x : SpatialPoint) : Prop :=
  InFundamentalCube x ∧ ∃ j, x j=0 ∨ x j=physicalPeriod

/-- Definition of cube Face Point in the Hopf Atlas construction. -/
private def cubeFacePoint (x : SpatialPoint) (j : Fin 3) (t : ℝ) : SpatialPoint :=
  WithLp.toLp 2 (Function.update x.ofLp j t)

/-- Original `cubeFacePoint_cube` guarantee for the `SupportGeometry` construction; the complete source hypotheses are retained. -/
private theorem cubeFacePoint_cube (x : SpatialPoint) (hx : InFundamentalCube x) (j : Fin 3)
    (t : ℝ) (ht : 0 ≤ t ∧ t ≤ physicalPeriod) : InFundamentalCube (cubeFacePoint x j t) := by
  intro i
  by_cases hi : i=j
  · subst i; simpa [cubeFacePoint] using ht
  · simpa [cubeFacePoint,hi] using hx i

/-- Original `cubeFacePoint_norm` guarantee for the `SupportGeometry` construction; the complete source hypotheses are retained. -/
private theorem cubeFacePoint_norm (x : SpatialPoint) (j : Fin 3) (t : ℝ) :
    ‖x-cubeFacePoint x j t‖=|x j-t| := by
  have h : x-cubeFacePoint x j t=EuclideanSpace.single j (x j-t) := by
    ext i
    by_cases hi : i=j
    · subst i; simp [cubeFacePoint]
    · simp [cubeFacePoint,hi]
  rw [h]
  simp

/-- Original `support_coordinate_margin` guarantee for the `SupportGeometry` construction; the complete source hypotheses are retained. -/
theorem support_coordinate_margin (B : Set SpatialPoint)
    (hB : ∀ x ∈ B, InFundamentalCube x) (mu : ℝ)
    (hgap : ∀ x ∈ B, ∀ z, OnCubeBoundary z → mu ≤ ‖x-z‖) :
    ∀ x ∈ B, ∀ j, mu ≤ x j ∧ x j ≤ physicalPeriod-mu := by
  intro x hx j
  have hlow := hgap x hx (cubeFacePoint x j 0)
    ⟨cubeFacePoint_cube x (hB x hx) j 0 ⟨le_rfl,physicalPeriod_pos.le⟩,
      j,Or.inl (by simp [cubeFacePoint])⟩
  have hhigh := hgap x hx (cubeFacePoint x j physicalPeriod)
    ⟨cubeFacePoint_cube x (hB x hx) j physicalPeriod ⟨physicalPeriod_pos.le,le_rfl⟩,
      j,Or.inr (by simp [cubeFacePoint])⟩
  rw [cubeFacePoint_norm,sub_zero,abs_of_nonneg (hB x hx j).1] at hlow
  rw [cubeFacePoint_norm,abs_of_nonpos (sub_nonpos.mpr (hB x hx j).2)] at hhigh
  exact ⟨hlow,by linarith⟩

/-- Original `support_background_collar` guarantee for the `SupportGeometry` construction; the complete source hypotheses are retained. -/
theorem support_background_collar (v : SpatialPoint → SpatialPoint) (B : Set SpatialPoint)
    (hB : ∀ x ∈ B, InFundamentalCube x) (mu : ℝ) (hm : 0<mu)
    (hgap : ∀ x ∈ B, ∀ z, OnCubeBoundary z → mu ≤ ‖x-z‖)
    (hoff : ∀ x y, InFundamentalCube x → InFundamentalCube y → x ∉ B → y ∉ B → v x=v y) :
    HasConstantCollar (sourceQuaternion v) (mu/2) (sourceQuaternion v 0) := by
  have hbox := support_coordinate_margin B hB mu hgap
  have hz : (0 : SpatialPoint) ∉ B := by
    intro h
    have hh := (hbox 0 h 0).1
    change mu ≤ 0 at hh
    linarith
  intro x hx hb
  have hxb : x ∉ B := by
    intro h
    rcases hb with ⟨j,hj⟩
    have hh := hbox x h j
    rcases hj with hj | hj <;> linarith
  exact congrArg spinOfVector (hoff x 0 hx (fun _ => ⟨le_rfl,physicalPeriod_pos.le⟩) hxb hz)

/-- A periodic smooth unit Hopf reference is constructed from the original
source, support separation and constancy promise. No lift or background
value is an input, and both initial charts remain available. -/
theorem exists_periodicReference_from_support (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v) (B : Set SpatialPoint)
    (hB : ∀ x ∈ B, InFundamentalCube x) (mu : ℝ) (hm : 0<mu)
    (hgap : ∀ x ∈ B, ∀ z, OnCubeBoundary z → mu ≤ ‖x-z‖)
    (hoff : ∀ x y, InFundamentalCube x → InFundamentalCube y → x ∉ B → y ∉ B → v x=v y) :
    ∃ q : QuaternionField, IsPeriodicField q ∧ IsSmoothUnitLift (sourceQuaternion v) q ∧
      ((q 0=northSeed (sourceQuaternion v 0) ∧ (1/2 : ℝ)<(q 0).re) ∨
       (q 0=southSeed (sourceQuaternion v 0) ∧ (1/2 : ℝ)<(q 0).imJ)) := by
  let sc := sourceQuaternion v 0
  have hsc : ‖sc‖=1 := (spinOfVector_norm (v 0)).trans (hu 0)
  have hc := support_background_collar v B hB mu hm hgap hoff
  have hmu : 0<mu/2 := half_pos hm
  have hpq : IsPeriodicField (sourceQuaternion v) := spin_field_periodic hp
  rcases chart_cover sc with hn | hs
  · have hnq : ‖northSeed sc‖=1 := northSeed_norm sc rfl hsc hn
    have hi := northSeed_hopf sc rfl hsc hn
    have hspec := periodicReference_spec v hv hu (northSeed sc) hnq hpq (mu/2) hmu sc hc hi
    have hzero := periodicReference_origin v hv hu (northSeed sc) hnq hpq (mu/2) hmu sc hc hi
    refine ⟨periodicReference v hv (northSeed sc) hnq (mu/2),hspec.1,hspec.2,Or.inl ⟨hzero,?_⟩⟩
    rw [hzero]
    exact northSeed_margin sc hn
  · have hnq : ‖southSeed sc‖=1 := southSeed_norm sc rfl hsc hs
    have hi := southSeed_hopf sc rfl hsc hs
    have hspec := periodicReference_spec v hv hu (southSeed sc) hnq hpq (mu/2) hmu sc hc hi
    have hzero := periodicReference_origin v hv hu (southSeed sc) hnq hpq (mu/2) hmu sc hc hi
    refine ⟨periodicReference v hv (southSeed sc) hnq (mu/2),hspec.1,hspec.2,Or.inr ⟨hzero,?_⟩⟩
    rw [hzero]
    exact southSeed_margin sc hs

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
