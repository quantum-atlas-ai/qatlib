/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.ReferenceValue
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

set_option backward.isDefEq.respectTransparency false

/-!
# Original spin curvature with the actual left-phase convention

The scalar density is a quaternion expression for one half of the vector
triple product. Unit and tangent hypotheses are used only for the exact
lift identity; noisy source packets will be controlled separately.
-/

set_option autoImplicit false
noncomputable section
open scoped Quaternion RealInnerProductSpace ContDiff
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Definition of hopf Differential in the Hopf Atlas construction. -/
def hopfDifferential (q v : ℍ) : ℍ := star v*iAxis*q+star q*iAxis*v

/-- Definition of spin Curvature Value in the Hopf Atlas construction. -/
def spinCurvatureValue (s ds dt : ℍ) : ℝ := -((s*ds*dt).re)/2

/-- Stability for raw, nonunit and nontangent packets. Coordinate errors
in three dimensions may be bounded by `2*e` in this Euclidean norm. -/
theorem spinCurvatureValue_packet_error (s ds dt a b c : ℍ) (M e : ℝ)
    (hM : 0 ≤ M) (he : 0 ≤ e) (he1 : e ≤ 1/64)
    (hs : ‖s‖=1) (hds : ‖ds‖ ≤ M) (hdt : ‖dt‖ ≤ M)
    (ha : ‖a-s‖ ≤ 2*e) (hb : ‖b-ds‖ ≤ 2*e) (hc : ‖c-dt‖ ≤ 2*e) :
    |spinCurvatureValue a b c-spinCurvatureValue s ds dt| ≤ 2*e*(M+1)^2 := by
  have hre (q : ℍ) : |q.re| ≤ ‖q‖ := by
    simpa [Quaternion.inner_def] using abs_real_inner_le_norm q (1 : ℍ)
  have hbn : ‖b‖ ≤ M+1 := by
    have h := norm_add_le (b-ds) ds
    rw [sub_add_cancel] at h
    linarith
  have hcn : ‖c‖ ≤ M+1 := by
    have h := norm_add_le (c-dt) dt
    rw [sub_add_cancel] at h
    linarith
  have hid : a*b*c-s*ds*dt=(a-s)*b*c+s*(b-ds)*c+s*ds*(c-dt) := by noncomm_ring
  have hn : ‖a*b*c-s*ds*dt‖ ≤
      2*e*(M+1)*(M+1)+2*e*(M+1)+2*e*M := by
    calc
      _ ≤ ‖(a-s)*b*c‖+‖s*(b-ds)*c‖+‖s*ds*(c-dt)‖ := by
        rw [hid]
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ = ‖a-s‖*‖b‖*‖c‖+‖s‖*‖b-ds‖*‖c‖+‖s‖*‖ds‖*‖c-dt‖ := by simp only [norm_mul]
      _ ≤ (2*e)*(M+1)*(M+1)+1*(2*e)*(M+1)+1*M*(2*e) := by
        gcongr <;> exact le_of_eq hs
      _ = _ := by ring
  have hr : |spinCurvatureValue a b c-spinCurvatureValue s ds dt|=
      |(a*b*c-s*ds*dt).re|/2 := by
    simp only [spinCurvatureValue,Quaternion.re_sub]
    rw [show -(a*b*c).re/2-(-(s*ds*dt).re/2)=-((a*b*c).re-(s*ds*dt).re)/2 by ring,
      abs_div,abs_neg]
    norm_num
  rw [hr]
  have h := (hre (a*b*c-s*ds*dt)).trans hn
  nlinarith [mul_nonneg he (sq_nonneg M)]

/-- Original `spinCurvatureValue_components` guarantee for the `SourceCurvature` construction; the complete source hypotheses are retained. -/
theorem spinCurvatureValue_components (s a b : SpatialPoint) :
    spinCurvatureValue (spinOfVector s) (spinOfVector a) (spinOfVector b)=
      (s 0*(a 1*b 2-a 2*b 1)+s 1*(a 2*b 0-a 0*b 2)+s 2*(a 0*b 1-a 1*b 0))/2 := by
  simp [spinCurvatureValue,spinOfVector]
  ring

/-- Definition of source Curvature in the Hopf Atlas construction. -/
def sourceCurvature (v : SpatialPoint → SpatialPoint) (x : SpatialPoint) (i j : Fin 3) : ℝ :=
  spinCurvatureValue (spinOfVector (v x))
    (spinOfVector (fderiv ℝ v x (EuclideanSpace.single i 1)))
    (spinOfVector (fderiv ℝ v x (EuclideanSpace.single j 1)))

/-- Definition of connection Curvature in the Hopf Atlas construction. -/
def connectionCurvature (q : QuaternionField) (x : SpatialPoint) (i j : Fin 3) : ℝ :=
  fderiv ℝ (fun y => connection q y j) x (EuclideanSpace.single i 1)-
    fderiv ℝ (fun y => connection q y i) x (EuclideanSpace.single j 1)

set_option maxHeartbeats 800000 in
/-- Exact polynomial identity before unit/tangent specialization. The normal
terms are explicit, so they cannot silently be dropped for noisy samples. -/
theorem hopf_curvature_algebra (q v w : ℍ) :
    spinCurvatureValue (hopf q) (hopfDifferential q v) (hopfDifferential q w)=
      2*(Quaternion.normSq q)^2*inner ℝ (iAxis*v) w+
      2*Quaternion.normSq q*(inner ℝ q w*connectionValue q v-inner ℝ q v*connectionValue q w) := by
  simp [spinCurvatureValue,hopf,hopfDifferential,Quaternion.normSq_def',Quaternion.inner_def,connectionValue,iAxis]
  ring

/-- Original `hopf_curvature_tangent` guarantee for the `SourceCurvature` construction; the complete source hypotheses are retained. -/
theorem hopf_curvature_tangent (q v w : ℍ) (hn : ‖q‖=1)
    (hv : inner ℝ q v=0) (hw : inner ℝ q w=0) :
    spinCurvatureValue (hopf q) (hopfDifferential q v) (hopfDifferential q w)=2*inner ℝ (iAxis*v) w := by
  rw [hopf_curvature_algebra,(normSq_eq_one_iff q).mpr hn,hv,hw]
  ring


/-- Quaternion conjugation commutes with real scalar multiplication. -/
local instance : StarModule ℝ ℍ where
  star_smul r q := by ext <;> simp

/-- Original `actual_hopf_derivative` guarantee for the `SourceCurvature` construction; the complete source hypotheses are retained. -/
private theorem actual_hopf_derivative (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (x : SpatialPoint) (h : SpatialPoint) :
    fderiv ℝ (fun y => hopf (q y)) x h=hopfDifferential (q x) (fderiv ℝ q x h) := by
  have hd := (hq.differentiable (by simp) x).hasFDerivAt
  change fderiv ℝ (fun y => star (q y)*iAxis*q y) x h=_
  have hprod := (hd.star.mul_const' iAxis).mul' hd
  change HasFDerivAt (fun y : SpatialPoint => star (q y)*iAxis*q y) _ x at hprod
  rw [hprod.fderiv]
  simp [hopfDifferential,add_comm]

/-- Original `actual_unit_tangent` guarantee for the `SourceCurvature` construction; the complete source hypotheses are retained. -/
private theorem actual_unit_tangent (q : QuaternionField) (hq : ContDiff ℝ ∞ q) (hu : ∀ y, ‖q y‖=1)
    (x h : SpatialPoint) : inner ℝ (q x) (fderiv ℝ q x h)=0 := by
  have hd := (hq.differentiable (by simp) x).hasFDerivAt
  have hi := hd.inner ℝ hd
  have heq : (fun y => inner ℝ (q y) (q y))=(fun _ : SpatialPoint => (1 : ℝ)) := by
    funext y
    rw [real_inner_self_eq_norm_sq,hu y]
    norm_num
  rw [heq] at hi
  have he := congrArg (fun f : SpatialPoint →L[ℝ] ℝ => f h) (hi.unique (hasFDerivAt_const (1 : ℝ) x))
  have hs : inner ℝ (q x) (fderiv ℝ q x h)+inner ℝ (fderiv ℝ q x h) (q x)=0 := by simpa using he
  have hcomm := real_inner_comm (q x) (fderiv ℝ q x h)
  linarith

/-- Original `actual_connection_derivative` guarantee for the `SourceCurvature` construction; the complete source hypotheses are retained. -/
private theorem actual_connection_derivative (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (x : SpatialPoint) (i j : Fin 3) :
    fderiv ℝ (fun y => connection q y j) x (EuclideanSpace.single i 1)=
      inner ℝ (iAxis*q x) (fderiv ℝ (fderiv ℝ q) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))+
      inner ℝ (iAxis*spatialPartial q x i) (spatialPartial q x j) := by
  have hd := (hq.differentiable (by simp) x).hasFDerivAt
  have hdd := ((hq.fderiv_right (m := ∞) (by rfl)).differentiable (by simp) x).hasFDerivAt
  have hj := hdd.clm_apply (hasFDerivAt_const (EuclideanSpace.single j (1 : ℝ)) x)
  have hi := (hd.const_mul iAxis).inner ℝ hj
  change fderiv ℝ (fun y => inner ℝ (iAxis*q y) (fderiv ℝ q y (EuclideanSpace.single j 1))) x _=_
  rw [hi.fderiv]
  simp [spatialPartial]

/-- Original `connectionCurvature_eq_tangent` guarantee for the `SourceCurvature` construction; the complete source hypotheses are retained. -/
theorem connectionCurvature_eq_tangent (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (x : SpatialPoint) (i j : Fin 3) :
    connectionCurvature q x i j=2*inner ℝ (iAxis*spatialPartial q x i) (spatialPartial q x j) := by
  have htwo : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) := by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top
  have hsym := (hq.contDiffAt (x := x)).isSymmSndFDerivAt htwo
  have hskew : inner ℝ (iAxis*spatialPartial q x j) (spatialPartial q x i)=
      -inner ℝ (iAxis*spatialPartial q x i) (spatialPartial q x j) := by
    simp [Quaternion.inner_def,iAxis]
    ring
  rw [connectionCurvature,actual_connection_derivative q hq,actual_connection_derivative q hq,
    hsym (EuclideanSpace.single i 1) (EuclideanSpace.single j 1),hskew]
  ring

/-- The actual connection curvature of a smooth unit lift equals the density
of its original spin. No curvature equality is assumed by the consumer. -/
theorem connectionCurvature_eq_source (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (q : QuaternionField) (hq : ContDiff ℝ ∞ q) (hu : ∀ y, ‖q y‖=1)
    (hh : ∀ y, hopf (q y)=spinOfVector (v y)) (x : SpatialPoint) (i j : Fin 3) :
    connectionCurvature q x i j=sourceCurvature v x i j := by
  have heq : (fun y => hopf (q y))=(fun y => spinOfVector (v y)) := funext hh
  have hd (k : Fin 3) : hopfDifferential (q x) (spatialPartial q x k)=
      spinOfVector (fderiv ℝ v x (EuclideanSpace.single k 1)) := by
    change hopfDifferential (q x) (fderiv ℝ q x (EuclideanSpace.single k 1))=_
    rw [← actual_hopf_derivative q hq,heq]
    have h := spinEmbedding.toContinuousLinearMap.hasFDerivAt.comp x (hv.differentiable (by simp) x).hasFDerivAt
    change (fderiv ℝ (spinEmbedding.toContinuousLinearMap ∘ v) x) _=_
    rw [h.fderiv]
    rfl
  have ha := hopf_curvature_tangent (q x) (spatialPartial q x i) (spatialPartial q x j) (hu x)
    (actual_unit_tangent q hq hu x _) (actual_unit_tangent q hq hu x _)
  rw [connectionCurvature_eq_tangent q hq,← ha,hh x,hd i,hd j]
  rfl

/-- The lift here is produced from the original source; it is not a supplied
reference oracle. This closes the exact source-curvature identity used by
source-only mean integration of the same periodic reference. -/
theorem sourcePeriodicReference_curvature (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ w, ‖v w‖=1) (hp : IsPeriodicField v)
    (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample) (hs : OriginalSpinSourceAccurate v source)
    (m1 m2 eta : ℚ) (he : 0<eta) (B : Set SpatialPoint)
    (hB : ∀ w ∈ B, InFundamentalCube w) (mu : ℝ) (hm : 0<mu)
    (hg : ∀ w ∈ B, ∀ a, OnCubeBoundary a → mu ≤ ‖w-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a ∉ B → b ∉ B → v a=v b)
    (hmargin : 7*(eta : ℝ) ≤ mu/2) (x : SpatialPoint) (i j : Fin 3) :
    connectionCurvature (sourcePeriodicReference v hv hu source hs m1 m2 eta) x i j=sourceCurvature v x i j := by
  have h := (sourcePeriodicReference_spec v hv hu hp source hs m1 m2 eta he B hB mu hm hg hoff hmargin).2.1
  exact connectionCurvature_eq_source v hv _ h.1 (fun y => (h.2 y).1) (fun y => (h.2 y).2) x i j

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
