/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SourceCurvature
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

set_option backward.isDefEq.respectTransparency false

/-!
# The physical mean of the constructed reference from source curvature

The coordinate integral is identified with the actual Euclidean volume
integral. Boundary connections are derived from full ambient seam collars.
No mean, lift or integration-by-parts identity is an original input.
-/

set_option autoImplicit false
noncomputable section
open scoped Quaternion ContDiff Topology
open Set MeasureTheory
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Abbreviation for Coordinate Point in the Rational Flow construction. -/
private abbrev CoordinatePoint := Fin 3 → ℝ
/-- Definition of coordinate Top in the Rational Flow construction. -/
private def coordinateTop : CoordinatePoint := fun _ => physicalPeriod

/-- Definition of physical Cube Integral in the Rational Flow construction. -/
def physicalCubeIntegral (f : SpatialPoint → ℝ) : ℝ :=
  ∫ x in Icc (0 : CoordinatePoint) coordinateTop, f (WithLp.toLp 2 x)

/-- The coordinate box integral uses exactly the Euclidean Lebesgue volume. -/
theorem physicalCubeIntegral_eq_volume (f : SpatialPoint → ℝ) :
    physicalCubeIntegral f=∫ x in {x | InFundamentalCube x}, f x := by
  have hset : (WithLp.toLp 2 : CoordinatePoint → SpatialPoint) ⁻¹'
      {x | InFundamentalCube x}=Icc (0 : CoordinatePoint) coordinateTop := by
    ext x
    simp only [mem_preimage,mem_setOf_eq,InFundamentalCube,mem_Icc,Pi.le_def,coordinateTop]
    constructor
    · intro h
      exact ⟨fun i => (h i).1,fun i => (h i).2⟩
    · rintro ⟨h0,hL⟩ i
      exact ⟨h0 i,hL i⟩
  simpa only [hset,physicalCubeIntegral] using
    (PiLp.volume_preserving_toLp (Fin 3)).setIntegral_preimage_emb
      (MeasurableEquiv.toLp 2 CoordinatePoint).measurableEmbedding f {x | InFundamentalCube x}

/-- Original `scalar_partial_integral_zero` guarantee for the `MeanIntegral` construction; the complete source hypotheses are retained. -/
private theorem scalar_partial_integral_zero (f : CoordinatePoint → ℝ) (hf : ContDiff ℝ ∞ f)
    (hb : ∀ x ∈ Icc (0 : CoordinatePoint) coordinateTop,
      (∃ j, x j=0 ∨ x j=physicalPeriod) → f x=0) (i : Fin 3) :
    (∫ x in Icc (0 : CoordinatePoint) coordinateTop,
      fderiv ℝ f x (Pi.single i 1))=0 := by
  let fs : Fin 3 → CoordinatePoint → ℝ := fun j => if j=i then f else fun _ => 0
  let dfs : Fin 3 → CoordinatePoint → CoordinatePoint →L[ℝ] ℝ :=
    fun j => if j=i then fderiv ℝ f else fun _ => 0
  have hc (j : Fin 3) : ContinuousOn (fs j) (Icc (0 : CoordinatePoint) coordinateTop) := by
    by_cases h : j=i
    · simpa [fs,h] using hf.continuous.continuousOn
    · simp only [fs,h,ite_false]
      exact continuousOn_const
  have hd (x : CoordinatePoint) (j : Fin 3) : HasFDerivAt (fs j) (dfs j x) x := by
    by_cases h : j=i
    · simpa [fs,dfs,h] using (hf.differentiable (by simp) x).hasFDerivAt
    · simpa [fs,dfs,h] using hasFDerivAt_const (0 : ℝ) x
  have heq (x : CoordinatePoint) : (∑ j : Fin 3, dfs j x (Pi.single j 1))=
      fderiv ℝ f x (Pi.single i 1) := by
    have heach (j : Fin 3) : dfs j x (Pi.single j 1)=
        if j=i then fderiv ℝ f x (Pi.single j 1) else 0 := by
      by_cases h : j=i <;> simp [dfs,h]
    simp_rw [heach]
    simp
  have hi : IntegrableOn (fun x => ∑ j : Fin 3, dfs j x (Pi.single j 1))
      (Icc (0 : CoordinatePoint) coordinateTop) := by
    simp only [heq]
    exact (((hf.fderiv_right (m := ∞) (by rfl)).continuous).clm_apply continuous_const).integrableOn_Icc
  have hdiv := integral_divergence_of_hasFDerivAt_off_countable' (0 : CoordinatePoint) coordinateTop
    (by intro j; exact physicalPeriod_pos.le) fs dfs ∅ countable_empty hc (fun x _ j => hd x j) hi
  have hface (j : Fin 3) (t : ℝ) (ht : t=0 ∨ t=physicalPeriod) :
      ∫ y in Icc ((0 : CoordinatePoint) ∘ j.succAbove) (coordinateTop ∘ j.succAbove),
        fs j (j.insertNth t y)=0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro y hy
    have hbox : j.insertNth t y ∈ Icc (0 : CoordinatePoint) coordinateTop := by
      constructor <;> rw [Pi.le_def,Fin.forall_iff_succAbove j]
      · constructor
        · simp only [Pi.zero_apply,Fin.insertNth_apply_same]
          rcases ht with rfl | rfl
          · exact le_rfl
          · exact physicalPeriod_pos.le
        · intro k
          simpa using hy.1 k
      · constructor
        · simp only [coordinateTop,Fin.insertNth_apply_same]
          rcases ht with rfl | rfl
          · exact physicalPeriod_pos.le
          · exact le_rfl
        · intro k
          simpa [coordinateTop] using hy.2 k
    have hzero := hb _ hbox ⟨j,by simpa using ht⟩
    by_cases hji : j=i
    · simpa [fs,hji] using hzero
    · simp [fs,hji]
  have hfront (j : Fin 3) :
      ∫ y in Icc ((0 : CoordinatePoint) ∘ j.succAbove) (coordinateTop ∘ j.succAbove),
        fs j (j.insertNth (coordinateTop j) y)=0 := hface j physicalPeriod (Or.inr rfl)
  have hback (j : Fin 3) :
      ∫ y in Icc ((0 : CoordinatePoint) ∘ j.succAbove) (coordinateTop ∘ j.succAbove),
        fs j (j.insertNth ((0 : CoordinatePoint) j) y)=0 := hface j 0 (Or.inl rfl)
  simpa only [heq,hfront,hback,
    sub_self,Finset.sum_const_zero] using hdiv

/-- Original `cube_integrable` guarantee for the `MeanIntegral` construction; the complete source hypotheses are retained. -/
private theorem cube_integrable (f : SpatialPoint → ℝ) (hf : Continuous f) :
    IntegrableOn (fun x : CoordinatePoint => f (WithLp.toLp 2 x))
      (Icc (0 : CoordinatePoint) coordinateTop) :=
  (hf.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.continuous).integrableOn_Icc

/-- Original `physicalCubeIntegral_partial_zero` guarantee for the `MeanIntegral` construction; the complete source hypotheses are retained. -/
theorem physicalCubeIntegral_partial_zero (f : SpatialPoint → ℝ) (hf : ContDiff ℝ ∞ f)
    (hb : ∀ x, OnCubeBoundary x → f x=0) (i : Fin 3) :
    physicalCubeIntegral (fun x => fderiv ℝ f x (EuclideanSpace.single i 1))=0 := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  have hc : ContDiff ℝ ∞ (fun x : CoordinatePoint => f (e x)) := hf.comp e.contDiff
  have hbd (x : CoordinatePoint) (hx : x ∈ Icc (0 : CoordinatePoint) coordinateTop)
      (hj : ∃ j, x j=0 ∨ x j=physicalPeriod) : f (e x)=0 :=
    hb (e x) ⟨fun j => ⟨hx.1 j,hx.2 j⟩,hj⟩
  have hder (x : CoordinatePoint) :
      fderiv ℝ (fun y => f (e y)) x (Pi.single i 1)=
        fderiv ℝ f (e x) (EuclideanSpace.single i 1) := by
    have hd := (hf.differentiable (by simp) (e x)).hasFDerivAt.comp x e.hasFDerivAt
    change fderiv ℝ (f ∘ e) x (Pi.single i 1)=_
    rw [hd.fderiv]
    rfl
  have h := scalar_partial_integral_zero (fun x => f (e x)) hc hbd i
  simp only [hder] at h
  exact h

/-- Original `contDiff_connection` guarantee for the `MeanIntegral` construction; the complete source hypotheses are retained. -/
theorem contDiff_connection (q : QuaternionField) (hq : ContDiff ℝ ∞ q) (j : Fin 3) :
    ContDiff ℝ ∞ (fun x => connection q x j) := by
  exact (contDiff_const.mul hq).inner ℝ
    ((hq.fderiv_right (m := ∞) (by rfl)).clm_apply contDiff_const)

/-- All ordinary partials vanish at every physical face. The argument uses
ambient neighbourhood constancy, not merely constancy restricted to a face. -/
theorem periodicReference_connection_boundary_zero (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (q₀ : Quaternion ℝ) (h₀ : ‖q₀‖=1)
    (hp : IsPeriodicField (sourceQuaternion v)) (eta : ℝ) (he : 0<eta) (sc : Quaternion ℝ)
    (hc : HasConstantCollar (sourceQuaternion v) eta sc) (hi : hopf q₀=sc)
    (x : SpatialPoint) (hx : OnCubeBoundary x) (j : Fin 3) :
    connection (periodicReference v hv q₀ h₀ eta) x j=0 := by
  have hseam : ∃ k, wrapCoordinate (x k)=0 := by
    rcases hx.2 with ⟨k,hk⟩
    refine ⟨k,?_⟩
    rcases hk with hk | hk <;> rw [hk]
    · simp [wrapCoordinate]
    · simp [wrapCoordinate,physicalPeriod_pos.ne']
  have heq := periodicExtension_eventually_constant_of_seam
    (correctedReference v hv q₀ h₀ eta) (gluingWidth eta) (gluingWidth_pos he)
    (gluingWidth_le_period eta) q₀ (correctedReference_collar v hv hu q₀ h₀ hp eta he sc hc hi) x hseam
  have hder : fderiv ℝ (periodicReference v hv q₀ h₀ eta) x=0 := by
    simpa only [periodicReference,fderiv_const_apply] using heq.fderiv_eq (𝕜 := ℝ)
  simp [connection,connectionValue,spatialPartial,hder]

/-- Definition of physical Cube Mean in the Rational Flow construction. -/
def physicalCubeMean (f : SpatialPoint → ℝ) : ℝ := physicalCubeIntegral f/physicalPeriod^3

/-- Original `physicalCubeIntegral_one` guarantee for the `MeanIntegral` construction; the complete source hypotheses are retained. -/
theorem physicalCubeIntegral_one : physicalCubeIntegral (fun _ => 1)=physicalPeriod^3 := by
  simp [physicalCubeIntegral,Measure.real,Real.volume_Icc_pi,coordinateTop,
    physicalPeriod_pos.le,pow_succ]

/-- Original `physicalCubeMean_const` guarantee for the `MeanIntegral` construction; the complete source hypotheses are retained. -/
theorem physicalCubeMean_const (c : ℝ) : physicalCubeMean (fun _ => c)=c := by
  have hc : physicalCubeIntegral (fun _ => c)=c*physicalCubeIntegral (fun _ => 1) := by
    simp [physicalCubeIntegral,mul_comm]
  rw [physicalCubeMean,hc,physicalCubeIntegral_one]
  field_simp [physicalPeriod_pos.ne']

/-- Original `cubeIntegral_add` guarantee for the `MeanIntegral` construction; the complete source hypotheses are retained. -/
private theorem cubeIntegral_add (f g : SpatialPoint → ℝ) (hf : Continuous f) (hg : Continuous g) :
    physicalCubeIntegral (fun x => f x+g x)=physicalCubeIntegral f+physicalCubeIntegral g :=
  integral_add (cube_integrable f hf) (cube_integrable g hg)

/-- Original `cubeIntegral_sub` guarantee for the `MeanIntegral` construction; the complete source hypotheses are retained. -/
private theorem cubeIntegral_sub (f g : SpatialPoint → ℝ) (hf : Continuous f) (hg : Continuous g) :
    physicalCubeIntegral (fun x => f x-g x)=physicalCubeIntegral f-physicalCubeIntegral g :=
  integral_sub (cube_integrable f hf) (cube_integrable g hg)

/-- Original `coordinate_mul_partial` guarantee for the `MeanIntegral` construction; the complete source hypotheses are retained. -/
private theorem coordinate_mul_partial (f : SpatialPoint → ℝ) (hf : ContDiff ℝ ∞ f)
    (x : SpatialPoint) (i j : Fin 3) :
    fderiv ℝ (fun y => y i*f y) x (EuclideanSpace.single j 1)=
      (if i=j then 1 else 0)*f x+x i*fderiv ℝ f x (EuclideanSpace.single j 1) := by
  have hd := (EuclideanSpace.proj i : SpatialPoint →L[ℝ] ℝ).hasFDerivAt.mul
    (hf.differentiable (by simp) x).hasFDerivAt
  change HasFDerivAt (fun y : SpatialPoint => y i*f y) _ x at hd
  rw [hd.fderiv]
  simp [add_comm]

/-- Integration by parts for the actual connection of any smooth field
whose full connection vanishes on the six physical faces. -/
theorem physicalCubeMean_connection_curvature (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hb : ∀ x, OnCubeBoundary x → ∀ k, connection q x k=0)
    (i j : Fin 3) (hij : i≠j) :
    physicalCubeMean (fun x => connection q x j)=
      -physicalCubeMean (fun x => x i*connectionCurvature q x i j) := by
  have hcont (k : Fin 3) := contDiff_connection q hq k
  have hcoord : ContDiff ℝ ∞ (fun x : SpatialPoint => x i) :=
    (EuclideanSpace.proj i : SpatialPoint →L[ℝ] ℝ).contDiff
  have hleft := physicalCubeIntegral_partial_zero (fun x => x i*connection q x j)
    (hcoord.mul (hcont j)) (fun x hx => by simp only [hb x hx j,mul_zero]) i
  have hright := physicalCubeIntegral_partial_zero (fun x => x i*connection q x i)
    (hcoord.mul (hcont i)) (fun x hx => by simp only [hb x hx i,mul_zero]) j
  simp only [coordinate_mul_partial _ (hcont j),ite_true,one_mul] at hleft
  simp only [coordinate_mul_partial _ (hcont i),hij,ite_false,zero_mul,zero_add] at hright
  have hdcont (k l : Fin 3) : Continuous
      (fun x => fderiv ℝ (fun y => connection q y k) x (EuclideanSpace.single l 1)) :=
    ((hcont k).fderiv_right (m := ∞) (by rfl)).continuous.clm_apply continuous_const
  have hxcont : Continuous (fun x : SpatialPoint => x i) := hcoord.continuous
  rw [cubeIntegral_add (fun x => connection q x j)
    (fun x => x i*fderiv ℝ (fun y => connection q y j) x (EuclideanSpace.single i 1))
    (hcont j).continuous (hxcont.mul (hdcont j i))] at hleft
  have hdistrib : (fun x => x i*connectionCurvature q x i j)=
      (fun x => x i*fderiv ℝ (fun y => connection q y j) x (EuclideanSpace.single i 1)-
        x i*fderiv ℝ (fun y => connection q y i) x (EuclideanSpace.single j 1)) := by
    funext x
    simp only [connectionCurvature,mul_sub]
  rw [physicalCubeMean,physicalCubeMean,hdistrib,
    cubeIntegral_sub
      (fun x => x i*fderiv ℝ (fun y => connection q y j) x (EuclideanSpace.single i 1))
      (fun x => x i*fderiv ℝ (fun y => connection q y i) x (EuclideanSpace.single j 1))
      (hxcont.mul (hdcont j i)) (hxcont.mul (hdcont i j)),hright,sub_zero]
  have heq : physicalCubeIntegral (fun x => connection q x j)=
      -physicalCubeIntegral (fun x => x i*fderiv ℝ (fun y => connection q y j) x (EuclideanSpace.single i 1)) := by
    linarith
  rw [heq,neg_div]

/-- The reference mean is an integral of the original spin alone. The
reference, its smoothness and its zero boundary connection are all produced
from the original source and support geometry. -/
theorem sourcePeriodicReference_mean (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ w, ‖v w‖=1) (hp : IsPeriodicField v)
    (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample) (hs : OriginalSpinSourceAccurate v source)
    (m1 m2 eta : ℚ) (he : 0<eta) (B : Set SpatialPoint)
    (hB : ∀ w ∈ B, InFundamentalCube w) (mu : ℝ) (hm : 0<mu)
    (hg : ∀ w ∈ B, ∀ a, OnCubeBoundary a → mu ≤ ‖w-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a ∉ B → b ∉ B → v a=v b)
    (hmargin : 7*(eta : ℝ) ≤ mu/2) (i j : Fin 3) (hij : i≠j) :
    physicalCubeMean (fun x => connection (sourcePeriodicReference v hv hu source hs m1 m2 eta) x j)=
      -physicalCubeMean (fun x => x i*sourceCurvature v x i j) := by
  have hspec := sourcePeriodicReference_spec v hv hu hp source hs m1 m2 eta he B hB mu hm hg hoff hmargin
  have hc := support_rescaled_collar v B hB mu hm hg hoff eta he.le hmargin
  have hseed := rescaledOriginSeed_spec v hu source hs m1 m2
  have heR : 0<(eta : ℝ) := by exact_mod_cast he
  have hb (x : SpatialPoint) (hx : OnCubeBoundary x) (k : Fin 3) :
      connection (sourcePeriodicReference v hv hu source hs m1 m2 eta) x k=0 :=
    periodicReference_connection_boundary_zero v hv hu _ hseed.1 (spin_field_periodic hp)
      _ (mul_pos physicalPeriod_pos heR) _ hc hseed.2.1 x hx k
  have h := physicalCubeMean_connection_curvature _ hspec.2.1.1 hb i j hij
  simp_rw [sourcePeriodicReference_curvature v hv hu hp source hs m1 m2 eta he B hB mu hm hg hoff hmargin] at h
  exact h

/-- Definition of unit Cube Integral in the Rational Flow construction. -/
def unitCubeIntegral (f : SpatialPoint → ℝ) : ℝ :=
  ∫ u in Icc (0 : CoordinatePoint) (fun _ => (1 : ℝ)), f (WithLp.toLp 2 u)

/-- The exact physical-to-unit change of variables includes the full volume
factor. It holds for the actual Lebesgue integral, including its zero
convention for nonintegrable functions. -/
theorem physicalCubeMean_scale (f : SpatialPoint → ℝ) :
    physicalCubeMean f=unitCubeIntegral (fun u => f (physicalPeriod • u)) := by
  let Q := Icc (0 : CoordinatePoint) coordinateTop
  let U := Icc (0 : CoordinatePoint) (fun _ => (1 : ℝ))
  have hmem (u : CoordinatePoint) : physicalPeriod • u ∈ Q ↔ u ∈ U := by
    change (0 ≤ physicalPeriod • u ∧ physicalPeriod • u ≤ coordinateTop) ↔ (0 ≤ u ∧ u ≤ fun _ => 1)
    constructor
    · rintro ⟨h0,hL⟩
      constructor <;> intro k
      · exact (mul_nonneg_iff_of_pos_left physicalPeriod_pos).mp (h0 k)
      · exact (mul_le_mul_iff_right₀ physicalPeriod_pos).mp (by simpa [coordinateTop] using hL k)
    · rintro ⟨h0,h1⟩
      constructor <;> intro k
      · exact mul_nonneg physicalPeriod_pos.le (h0 k)
      · exact (mul_le_mul_of_nonneg_left (h1 k) physicalPeriod_pos.le).trans_eq (mul_one _)
  have hfun : (fun u : CoordinatePoint =>
      Q.indicator (fun x => f (WithLp.toLp 2 x)) (physicalPeriod • u))=
      U.indicator (fun u => f (physicalPeriod • WithLp.toLp 2 u)) := by
    funext u
    by_cases hu : u ∈ U
    · simp only [indicator_of_mem hu,indicator_of_mem ((hmem u).mpr hu)]
      rfl
    · simp only [indicator_of_notMem hu,indicator_of_notMem ((not_congr (hmem u)).mpr hu)]
  have hs := Measure.integral_comp_smul_of_nonneg volume
    (Q.indicator (fun x => f (WithLp.toLp 2 x))) physicalPeriod (hR := physicalPeriod_pos.le)
  rw [hfun,integral_indicator measurableSet_Icc,integral_indicator measurableSet_Icc] at hs
  simpa only [physicalCubeMean,physicalCubeIntegral,unitCubeIntegral,
    Module.finrank_pi_fintype,Module.finrank_self,Finset.sum_const,Finset.card_univ,Fintype.card_fin,one_mul,
    nsmul_eq_mul,Nat.cast_ofNat,mul_one,smul_eq_mul,div_eq_mul_inv,mul_comm,Q,U] using hs.symm

/-- Definition of unit Coordinate Spin in the Rational Flow construction. -/
def unitCoordinateSpin (v : SpatialPoint → SpatialPoint) : SpatialPoint → SpatialPoint :=
  fun u => v (physicalPeriod • u)

/-- Original `sourceCurvature_unitCoordinateSpin` guarantee for the `MeanIntegral` construction; the complete source hypotheses are retained. -/
theorem sourceCurvature_unitCoordinateSpin (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (u : SpatialPoint) (i j : Fin 3) :
    sourceCurvature (unitCoordinateSpin v) u i j=
      physicalPeriod^2*sourceCurvature v (physicalPeriod • u) i j := by
  have hd (k : Fin 3) :
      fderiv ℝ (unitCoordinateSpin v) u (EuclideanSpace.single k 1)=
        physicalPeriod • fderiv ℝ v (physicalPeriod • u) (EuclideanSpace.single k 1) := by
    have h := (hv.differentiable (by simp) (physicalPeriod • u)).hasFDerivAt.comp u
      ((hasFDerivAt_id u).const_smul physicalPeriod)
    change HasFDerivAt (unitCoordinateSpin v) _ u at h
    rw [h.fderiv]
    simp
  simp only [sourceCurvature,hd,spinCurvatureValue_components]
  simp only [unitCoordinateSpin,PiLp.smul_apply,smul_eq_mul]
  ring

/-- This is exactly the unit-coordinate curvature moment targeted by the
source-only finite mean producer. Division by the physical period remains. -/
theorem sourcePeriodicReference_unit_mean (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ w, ‖v w‖=1) (hp : IsPeriodicField v)
    (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample) (hs : OriginalSpinSourceAccurate v source)
    (m1 m2 eta : ℚ) (he : 0<eta) (B : Set SpatialPoint)
    (hB : ∀ w ∈ B, InFundamentalCube w) (mu : ℝ) (hm : 0<mu)
    (hg : ∀ w ∈ B, ∀ a, OnCubeBoundary a → mu ≤ ‖w-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a ∉ B → b ∉ B → v a=v b)
    (hmargin : 7*(eta : ℝ) ≤ mu/2) (i j : Fin 3) (hij : i≠j) :
    physicalCubeMean (fun x => connection (sourcePeriodicReference v hv hu source hs m1 m2 eta) x j)=
      -(unitCubeIntegral (fun u => u i*sourceCurvature (unitCoordinateSpin v) u i j))/physicalPeriod := by
  rw [sourcePeriodicReference_mean v hv hu hp source hs m1 m2 eta he B hB mu hm hg hoff hmargin i j hij,
    physicalCubeMean_scale]
  have hpoint (u : SpatialPoint) :
      (physicalPeriod • u) i*sourceCurvature v (physicalPeriod • u) i j=
        (u i*sourceCurvature (unitCoordinateSpin v) u i j)/physicalPeriod := by
    rw [sourceCurvature_unitCoordinateSpin v hv]
    change physicalPeriod*u i*_=_
    field_simp [physicalPeriod_pos.ne']
  simp_rw [hpoint]
  simp only [unitCubeIntegral,integral_div,neg_div]

end Qatlib.Concepts.EffectiveGauge.RationalFlow
