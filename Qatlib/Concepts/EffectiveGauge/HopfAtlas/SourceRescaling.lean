/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.PeriodApproximation
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.PhysicalLine

/-!
# Original rational source queries approximate fixed physical period samples

The target coordinates use the exact 2π, independently of precision. The
program calls the original source only at the short dyadic lower-period
coordinates and accounts for both position and derivative-scaling errors.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Definition of rescale Source Overhead in the Hopf Atlas construction. -/
def rescaleSourceOverhead (m1 m2 : ℚ) : ℕ := Nat.clog 2 (Nat.ceil (128*(m1+m2+1)))

/-- Definition of rescale Source Query in the Hopf Atlas construction. -/
def rescaleSourceQuery (m1 m2 : ℚ) (label : (Fin 3 → ℚ) × ℕ) : (Fin 3 → ℚ) × ℕ :=
  let b := label.2+rescaleSourceOverhead m1 m2
  let length := periodLower b
  (fun j => length*label.1 j,b)

/-- Definition of rescaled Spin Samples in the Hopf Atlas construction. -/
def rescaledSpinSamples (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample)
    (m1 m2 : ℚ) (label : (Fin 3 → ℚ) × ℕ) : RationalSpinSample :=
  let b := label.2+rescaleSourceOverhead m1 m2
  let length := periodLower b
  let answer := source (fun j => length*label.1 j,b)
  (answer.1,fun j => length*answer.2 j)

/-- Definition of rescaled Charged Samples in the Hopf Atlas construction. -/
def rescaledChargedSamples (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample × ℕ)
    (m1 m2 : ℚ) (label : (Fin 3 → ℚ) × ℕ) : RationalSpinSample × ℕ :=
  let b := label.2+rescaleSourceOverhead m1 m2
  let length := periodLower b
  let answer := source (fun j => length*label.1 j,b)
  ((answer.1.1,fun j => length*answer.1.2 j),answer.2)

/-- Original `rescaledChargedSamples_value` guarantee for the `SourceRescaling` construction; the complete source hypotheses are retained. -/
theorem rescaledChargedSamples_value (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample × ℕ)
    (m1 m2 : ℚ) (label : (Fin 3 → ℚ) × ℕ) :
    (rescaledChargedSamples source m1 m2 label).1=rescaledSpinSamples (fun q => (source q).1) m1 m2 label := rfl

/-- Original `rescaledChargedSamples_fee` guarantee for the `SourceRescaling` construction; the complete source hypotheses are retained. -/
theorem rescaledChargedSamples_fee (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample × ℕ)
    (m1 m2 : ℚ) (label : (Fin 3 → ℚ) × ℕ) :
    (rescaledChargedSamples source m1 m2 label).2=(source (rescaleSourceQuery m1 m2 label)).2 := rfl

/-- Original `rescaleSourceOverhead_bound` guarantee for the `SourceRescaling` construction; the complete source hypotheses are retained. -/
theorem rescaleSourceOverhead_bound (m1 m2 : ℚ) : 128*(m1+m2+1) ≤ (2^rescaleSourceOverhead m1 m2 : ℚ) := by
  have h : Nat.ceil (128*(m1+m2+1)) ≤ 2^rescaleSourceOverhead m1 m2 := Nat.le_pow_clog (by decide) _
  exact (Nat.le_ceil _).trans (by exact_mod_cast h)

/-- Original `rescaleSourceOverhead_budget` guarantee for the `SourceRescaling` construction; the complete source hypotheses are retained. -/
theorem rescaleSourceOverhead_budget (m1 m2 : ℚ) (b : ℕ) :
    (128*(m1+m2+1))*(2^(b+rescaleSourceOverhead m1 m2) : ℚ)⁻¹ ≤ (2^b : ℚ)⁻¹ := by
  have h := rescaleSourceOverhead_bound m1 m2
  have ho : (0 : ℚ)<2^rescaleSourceOverhead m1 m2 := by positivity
  have hm : (128*(m1+m2+1))*(2^rescaleSourceOverhead m1 m2 : ℚ)⁻¹ ≤ 1 := by
    simpa only [div_eq_mul_inv] using (div_le_one ho).mpr h
  rw [pow_add,mul_inv_rev,← mul_assoc]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hm (by positivity : (0 : ℚ) ≤ (2^b : ℚ)⁻¹)

noncomputable section
open scoped Quaternion ContDiff BigOperators
open Set

/-- Definition of source Physical Dx in the Hopf Atlas construction. -/
def sourcePhysicalDx (v : SpatialPoint → SpatialPoint) (x : SpatialPoint) : SpatialPoint :=
  fderiv ℝ v x (EuclideanSpace.single 0 1)

/-- These are actual derivatives of the original source. Mixed x/y and x/z
derivatives are necessary because all three coordinates are rescaled. -/
def SourceRescalingBounds (v : SpatialPoint → SpatialPoint) (m1 m2 : ℝ) : Prop :=
  (∀ x, InFundamentalCube x → ∀ j, ‖fderiv ℝ v x (EuclideanSpace.single j 1)‖ ≤ m1) ∧
  (∀ x, InFundamentalCube x → ∀ j, ‖fderiv ℝ (sourcePhysicalDx v) x (EuclideanSpace.single j 1)‖ ≤ m2)

/-- The actual physical derivative in an arbitrary original coordinate direction. -/
def sourcePhysicalPartial (v : SpatialPoint → SpatialPoint) (i : Fin 3) (x : SpatialPoint) : SpatialPoint :=
  fderiv ℝ v x (EuclideanSpace.single i 1)

/-- The directional pair is a projection of the original source data, rather
than a new coefficient or lift oracle. -/
def OriginalDirectionalSpinSourceAccurate (v : SpatialPoint → SpatialPoint) (i : Fin 3)
    (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample) : Prop :=
  ∀ (a : Fin 3 → ℚ) (b : ℕ), (∀ j, 0 ≤ (a j : ℝ) ∧ (a j : ℝ) ≤ physicalPeriod) →
    (∀ j, |((source (a,b)).1 j : ℝ)-v (rationalSpatialPoint a) j| ≤ (2^b : ℝ)⁻¹) ∧
    (∀ j, |((source (a,b)).2 j : ℝ)-sourcePhysicalPartial v i (rationalSpatialPoint a) j| ≤
      (2^b : ℝ)⁻¹)

/-- A directional adapter needs every spatial variation of that derivative. -/
def SourceDirectionalRescalingBounds (v : SpatialPoint → SpatialPoint) (i : Fin 3) (m1 m2 : ℝ) : Prop :=
  (∀ x, InFundamentalCube x → ∀ j, ‖fderiv ℝ v x (EuclideanSpace.single j 1)‖ ≤ m1) ∧
  (∀ x, InFundamentalCube x → ∀ j,
    ‖fderiv ℝ (sourcePhysicalPartial v i) x (EuclideanSpace.single j 1)‖ ≤ m2)

/-- Unlike the legacy Dx-only interface, this controls all ordered second partials. -/
def SourceAllRescalingBounds (v : SpatialPoint → SpatialPoint) (m1 m2 : ℝ) : Prop :=
  (∀ x, InFundamentalCube x → ∀ j, ‖fderiv ℝ v x (EuclideanSpace.single j 1)‖ ≤ m1) ∧
  (∀ i x, InFundamentalCube x → ∀ j,
    ‖fderiv ℝ (sourcePhysicalPartial v i) x (EuclideanSpace.single j 1)‖ ≤ m2)

/-- The all-direction hypothesis implies each genuine directional adapter contract. -/
theorem SourceAllRescalingBounds.directional (v : SpatialPoint → SpatialPoint) (m1 m2 : ℝ)
    (h : SourceAllRescalingBounds v m1 m2) (i : Fin 3) :
    SourceDirectionalRescalingBounds v i m1 m2 := ⟨h.1,h.2 i⟩

/-- Preserve consumption of the original Dx-only API without strengthening its type. -/
theorem SourceAllRescalingBounds.legacy (v : SpatialPoint → SpatialPoint) (m1 m2 : ℝ)
    (h : SourceAllRescalingBounds v m1 m2) : SourceRescalingBounds v m1 m2 := ⟨h.1,h.2 0⟩

/-- Original `cube_convex` guarantee for the `SourceRescaling` construction; the complete source hypotheses are retained. -/
private theorem cube_convex : Convex ℝ {x : SpatialPoint | InFundamentalCube x} := by
  intro a ha b hb r s hr hs hrs i
  change 0 ≤ r*a i+s*b i ∧ r*a i+s*b i ≤ physicalPeriod
  constructor
  · nlinarith [mul_nonneg hr (ha i).1,mul_nonneg hs (hb i).1]
  · have hscale : r*physicalPeriod+s*physicalPeriod=physicalPeriod := by rw [← add_mul,hrs,one_mul]
    nlinarith [mul_nonneg hr (sub_nonneg.mpr (ha i).2),mul_nonneg hs (sub_nonneg.mpr (hb i).2)]

/-- Original `clm_axes_bound` guarantee for the `SourceRescaling` construction; the complete source hypotheses are retained. -/
private theorem clm_axes_bound (D : SpatialPoint →L[ℝ] SpatialPoint) (C : ℝ) (hC : 0 ≤ C)
    (hD : ∀ i, ‖D (EuclideanSpace.single i 1)‖ ≤ C) : ‖D‖ ≤ 3*C := by
  apply D.opNorm_le_bound (by positivity)
  intro z
  have he : z=∑ i : Fin 3, (z i) • EuclideanSpace.single i (1 : ℝ) := by
    ext i
    fin_cases i <;> simp [Fin.sum_univ_three]
  have hd : D z=∑ i : Fin 3, (z i) • D (EuclideanSpace.single i 1) := by
    conv_lhs => rw [he]
    simp only [map_sum,map_smul]
  calc
    _ = ‖∑ i : Fin 3, (z i) • D (EuclideanSpace.single i 1)‖ := congrArg norm hd
    _ ≤ ∑ i : Fin 3, ‖(z i) • D (EuclideanSpace.single i 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, ‖z‖*C := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul (PiLp.norm_apply_le z i) (hD i) (norm_nonneg _) (norm_nonneg _)
    _ = (3*C)*‖z‖ := by rw [Fin.sum_univ_three]; ring

/-- Original `source_cube_lipschitz` guarantee for the `SourceRescaling` construction; the complete source hypotheses are retained. -/
private theorem source_cube_lipschitz (f : SpatialPoint → SpatialPoint) (hf : ContDiff ℝ ∞ f)
    (C : ℝ) (hC : 0 ≤ C)
    (hD : ∀ x, InFundamentalCube x → ∀ i, ‖fderiv ℝ f x (EuclideanSpace.single i 1)‖ ≤ C)
    (a b : SpatialPoint) (ha : InFundamentalCube a) (hb : InFundamentalCube b) :
    ‖f b-f a‖ ≤ (3*C)*‖b-a‖ :=
  Convex.norm_image_sub_le_of_norm_fderiv_le (fun x _ => hf.differentiable (by simp) x)
    (fun x hx => clm_axes_bound _ C hC (hD x hx)) cube_convex ha hb

/-- Original `vector_coords_bound` guarantee for the `SourceRescaling` construction; the complete source hypotheses are retained. -/
private theorem vector_coords_bound (z : SpatialPoint) (e : ℝ) (he : 0 ≤ e)
    (hz : ∀ i, |z i| ≤ e) : ‖z‖ ≤ 2*e := by
  have h := pure_coordinate_norm_le (spinOfVector z) rfl e he (hz 0) (hz 1) (hz 2)
  rw [spinOfVector_norm] at h
  linarith

/-- Original `scaled_unit_in_cube` guarantee for the `SourceRescaling` construction; the complete source hypotheses are retained. -/
private theorem scaled_unit_in_cube (a : Fin 3 → ℚ) (ha : ∀ i, (a i : ℝ) ∈ Icc 0 1)
    (r : ℝ) (hr : 0 ≤ r ∧ r ≤ physicalPeriod) : InFundamentalCube (r • rationalSpatialPoint a) := by
  intro i
  change 0 ≤ r*(a i : ℝ) ∧ r*(a i : ℝ) ≤ physicalPeriod
  exact ⟨mul_nonneg hr.1 (ha i).1,(mul_le_mul_of_nonneg_left (ha i).2 hr.1).trans (by simpa using hr.2)⟩

/-- Original `rescaleSourceQuery_cast` guarantee for the `SourceRescaling` construction; the complete source hypotheses are retained. -/
theorem rescaleSourceQuery_cast (m1 m2 : ℚ) (a : Fin 3 → ℚ) (b : ℕ) :
    rationalSpatialPoint (rescaleSourceQuery m1 m2 (a,b)).1=
      (periodLower (b+rescaleSourceOverhead m1 m2) : ℝ) • rationalSpatialPoint a := by
  ext i
  change ((periodLower (b+rescaleSourceOverhead m1 m2)*a i : ℚ) : ℝ)=_
  exact Rat.cast_mul _ _

/-- Original `rescaleSourceQuery_legal` guarantee for the `SourceRescaling` construction; the complete source hypotheses are retained. -/
theorem rescaleSourceQuery_legal (m1 m2 : ℚ) (a : Fin 3 → ℚ) (b : ℕ)
    (ha : ∀ i, (a i : ℝ) ∈ Icc 0 1) :
    ∀ i, 0 ≤ ((rescaleSourceQuery m1 m2 (a,b)).1 i : ℝ) ∧
      ((rescaleSourceQuery m1 m2 (a,b)).1 i : ℝ) ≤ physicalPeriod := by
  have hl := periodLower_spec (b+rescaleSourceOverhead m1 m2)
  have h := scaled_unit_in_cube a ha _ ⟨by linarith,hl.2.1⟩
  rw [← rescaleSourceQuery_cast] at h
  exact h

/-- The output is accurate at the exact 2π-scaled point, not the moving dyadic
query point. All needed moduli are actual first and mixed second derivatives
of the original source; no lift or nonrational source oracle is assumed. -/
theorem rescaledDirectionalSpinSamples_error (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (direction : Fin 3)
    (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample)
    (hs : OriginalDirectionalSpinSourceAccurate v direction source)
    (m1 m2 : ℚ) (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2)
    (hbounds : SourceDirectionalRescalingBounds v direction (m1 : ℝ) (m2 : ℝ))
    (a : Fin 3 → ℚ) (ha : ∀ i, (a i : ℝ) ∈ Icc 0 1) (b : ℕ) :
    (∀ j, |((rescaledSpinSamples source m1 m2 (a,b)).1 j : ℝ)-
      v (physicalPeriod • rationalSpatialPoint a) j| ≤ (2^b : ℝ)⁻¹) ∧
    (∀ j, |((rescaledSpinSamples source m1 m2 (a,b)).2 j : ℝ)-
      (physicalPeriod • sourcePhysicalPartial v direction (physicalPeriod • rationalSpatialPoint a)) j| ≤ (2^b : ℝ)⁻¹) := by
  let n := b+rescaleSourceOverhead m1 m2
  let length : ℝ := (periodLower n : ℝ)
  let u := rationalSpatialPoint a
  let p := length • u
  let t := physicalPeriod • u
  let data := source (rescaleSourceQuery m1 m2 (a,b))
  let e : ℝ := (2^n : ℝ)⁻¹
  have he : 0 ≤ e := by positivity
  have hm1R : (0 : ℝ) ≤ m1 := by exact_mod_cast hm1
  have hm2R : (0 : ℝ) ≤ m2 := by exact_mod_cast hm2
  have hl := periodLower_spec n
  have hlen : 0 ≤ length := by dsimp [length]; linarith [hl.1]
  have hlen7 : length ≤ 7 := hl.2.2.2.le
  have hlenL : length ≤ physicalPeriod := hl.2.1
  have hdelta : physicalPeriod-length ≤ e := hl.2.2.1
  have hpc : InFundamentalCube p := scaled_unit_in_cube a ha length ⟨hlen,hlenL⟩
  have htc : InFundamentalCube t := scaled_unit_in_cube a ha physicalPeriod ⟨physicalPeriod_pos.le,le_rfl⟩
  have hd := hs (rescaleSourceQuery m1 m2 (a,b)).1 n (rescaleSourceQuery_legal m1 m2 a b ha)
  rw [rescaleSourceQuery_cast] at hd
  have hsdata : ∀ j, |(data.1 j : ℝ)-v p j| ≤ e := hd.1
  have hddata : ∀ j, |(data.2 j : ℝ)-sourcePhysicalPartial v direction p j| ≤ e := hd.2
  have hsn : ‖rationalSpatialPoint data.1-v p‖ ≤ 2*e :=
    vector_coords_bound _ e he hsdata
  have hdn : ‖rationalSpatialPoint data.2-sourcePhysicalPartial v direction p‖ ≤ 2*e :=
    vector_coords_bound _ e he hddata
  have hu : ‖u‖ ≤ 2 := by
    have h := vector_coords_bound u 1 (by norm_num) (fun i => by
      change |(a i : ℝ)| ≤ 1
      rw [abs_of_nonneg (ha i).1]
      exact (ha i).2)
    simpa only [mul_one] using h
  have hdist : ‖p-t‖ ≤ 2*e := by
    calc
      _ = |length-physicalPeriod| * ‖u‖ := by
        dsimp only [p,t]
        rw [← sub_smul,norm_smul,Real.norm_eq_abs]
      _ = (physicalPeriod-length)*‖u‖ := by rw [abs_of_nonpos (sub_nonpos.mpr hlenL),neg_sub]
      _ ≤ e*2 := mul_le_mul hdelta hu (norm_nonneg _) he
      _ = _ := by ring
  have hvar : ‖v p-v t‖ ≤ 6*(m1 : ℝ)*e := by
    have h := (source_cube_lipschitz v hv (m1 : ℝ) hm1R hbounds.1 t p htc hpc).trans
      (mul_le_mul_of_nonneg_left hdist (by positivity : (0 : ℝ) ≤ 3*(m1 : ℝ)))
    nlinarith
  have hdx : ContDiff ℝ ∞ (sourcePhysicalPartial v direction) :=
    (hv.fderiv_right (m := ∞) (by rfl)).clm_apply contDiff_const
  have hdvar : ‖sourcePhysicalPartial v direction p-sourcePhysicalPartial v direction t‖ ≤ 6*(m2 : ℝ)*e := by
    have h := (source_cube_lipschitz _ hdx (m2 : ℝ) hm2R hbounds.2 t p htc hpc).trans
      (mul_le_mul_of_nonneg_left hdist (by positivity : (0 : ℝ) ≤ 3*(m2 : ℝ)))
    nlinarith
  have hdt : ‖sourcePhysicalPartial v direction t‖ ≤ (m1 : ℝ) := hbounds.1 t htc direction
  have hbudget : 128*((m1 : ℝ)+(m2 : ℝ)+1)*e ≤ (2^b : ℝ)⁻¹ := by
    have h : (((128*(m1+m2+1))*(2^n : ℚ)⁻¹ : ℚ) : ℝ) ≤ (((2^b : ℚ)⁻¹ : ℚ) : ℝ) :=
      Rat.cast_le.mpr (rescaleSourceOverhead_budget m1 m2 b)
    push_cast at h
    exact h
  have hvtotal : ‖rationalSpatialPoint data.1-v t‖ ≤ (2^b : ℝ)⁻¹ := by
    calc
      _ ≤ ‖rationalSpatialPoint data.1-v p‖+‖v p-v t‖ := by
        simpa only [dist_eq_norm] using dist_triangle (rationalSpatialPoint data.1) (v p) (v t)
      _ ≤ 2*e+6*(m1 : ℝ)*e := add_le_add hsn hvar
      _ ≤ 128*((m1 : ℝ)+(m2 : ℝ)+1)*e := by
        nlinarith [mul_nonneg hm1R he,mul_nonneg hm2R he]
      _ ≤ _ := hbudget
  have hdtotal : ‖length • rationalSpatialPoint data.2-physicalPeriod • sourcePhysicalPartial v direction t‖ ≤ (2^b : ℝ)⁻¹ := by
    have hid : length • rationalSpatialPoint data.2-physicalPeriod • sourcePhysicalPartial v direction t=
        length • (rationalSpatialPoint data.2-sourcePhysicalPartial v direction p)+
        length • (sourcePhysicalPartial v direction p-sourcePhysicalPartial v direction t)+(length-physicalPeriod) • sourcePhysicalPartial v direction t := by module
    calc
      _ ≤ ‖length • (rationalSpatialPoint data.2-sourcePhysicalPartial v direction p)‖+
          ‖length • (sourcePhysicalPartial v direction p-sourcePhysicalPartial v direction t)‖+
          ‖(length-physicalPeriod) • sourcePhysicalPartial v direction t‖ := by
        rw [hid]
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
      _ = length*‖rationalSpatialPoint data.2-sourcePhysicalPartial v direction p‖+
          length*‖sourcePhysicalPartial v direction p-sourcePhysicalPartial v direction t‖+(physicalPeriod-length)*‖sourcePhysicalPartial v direction t‖ := by
        simp only [norm_smul,Real.norm_eq_abs,
          abs_of_nonneg hlen,abs_of_nonpos (sub_nonpos.mpr hlenL),neg_sub]
      _ ≤ 7*(2*e)+7*(6*(m2 : ℝ)*e)+e*(m1 : ℝ) := add_le_add
        (add_le_add (mul_le_mul hlen7 hdn (norm_nonneg _) (by norm_num))
          (mul_le_mul hlen7 hdvar (norm_nonneg _) (by norm_num)))
        (mul_le_mul hdelta hdt (norm_nonneg _) he)
      _ ≤ 128*((m1 : ℝ)+(m2 : ℝ)+1)*e := by
        nlinarith [mul_nonneg hm1R he,mul_nonneg hm2R he]
      _ ≤ _ := hbudget
  constructor
  · intro j
    change |(data.1 j : ℝ)-v t j| ≤ _
    have hc : |(data.1 j : ℝ)-v t j| ≤ ‖rationalSpatialPoint data.1-v t‖ := by
      simpa [Real.norm_eq_abs,PiLp.sub_apply,PiLp.smul_apply,rationalSpatialPoint] using PiLp.norm_apply_le (rationalSpatialPoint data.1-v t) j
    exact hc.trans hvtotal
  · intro j
    change |((periodLower n*data.2 j : ℚ) : ℝ)-physicalPeriod*(sourcePhysicalPartial v direction t) j| ≤ _
    rw [Rat.cast_mul]
    have hc : |length*(data.2 j : ℝ)-physicalPeriod*(sourcePhysicalPartial v direction t) j| ≤
        ‖length • rationalSpatialPoint data.2-physicalPeriod • sourcePhysicalPartial v direction t‖ := by
      simpa [Real.norm_eq_abs,PiLp.sub_apply,PiLp.smul_apply,rationalSpatialPoint] using PiLp.norm_apply_le
        (length • rationalSpatialPoint data.2-physicalPeriod • sourcePhysicalPartial v direction t) j
    exact hc.trans hdtotal

/-- The historical Dx theorem keeps its full original type and follows by
specializing the arbitrary-direction adapter. -/
theorem rescaledSpinSamples_error (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (source : (Fin 3 → ℚ) × ℕ → RationalSpinSample) (hs : OriginalSpinSourceAccurate v source)
    (m1 m2 : ℚ) (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2)
    (hbounds : SourceRescalingBounds v (m1 : ℝ) (m2 : ℝ))
    (a : Fin 3 → ℚ) (ha : ∀ i, (a i : ℝ) ∈ Icc 0 1) (b : ℕ) :
    (∀ j, |((rescaledSpinSamples source m1 m2 (a,b)).1 j : ℝ)-
      v (physicalPeriod • rationalSpatialPoint a) j| ≤ (2^b : ℝ)⁻¹) ∧
    (∀ j, |((rescaledSpinSamples source m1 m2 (a,b)).2 j : ℝ)-
      (physicalPeriod • sourcePhysicalDx v (physicalPeriod • rationalSpatialPoint a)) j| ≤ (2^b : ℝ)⁻¹) := by
  exact rescaledDirectionalSpinSamples_error v hv 0 source hs m1 m2 hm1 hm2 hbounds a ha b

end
end Qatlib.Concepts.EffectiveGauge.HopfAtlas
