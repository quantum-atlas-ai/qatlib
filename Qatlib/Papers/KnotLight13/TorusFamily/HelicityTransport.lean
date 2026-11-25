/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanRayDifferential
public import Qatlib.Papers.KnotLight13.TorusFamily.InitialHelicityDensity
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Conservation of the whole-space Bateman helicities

[Kedia2013TyingKnots], equation (6) and the conserved quantities on page 150404-3,
[DOI](https://doi.org/10.1103/physrevlett.111.150404).
Oriented determinants of the real and imaginary scalar differentials
give the spatial transport laws for the electric and magnetic vectors
and for helicity density. The explicit initial decay gives absolute
integrability of each helicity at every real time.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.TorusFamily

open Qatlib.Papers.KnottedLight08.HopfField (cross3 dot3)
open Qatlib.Papers.KnotLight13.TorusFamily (rationalAlpha rationalBeta complex_rational_pair_unit)
open Filter MeasureTheory Module Set
open scoped BigOperators

local notation "HelicitySpace" => ℝ × ℝ × ℝ

/-- The real determinant of the three rows of spatial covectors. -/
private noncomputable def covectorDet (a : Fin 3 → HelicitySpace →L[ℝ] ℝ) : ℝ :=
  Matrix.det (Matrix.of fun i j => a i (batemanCartesianBasis j))

/-- Composing the three covectors with a spatial derivative multiplies
their determinant by its real Jacobian. -/
private theorem covectorDet_comp (a : Fin 3 → HelicitySpace →L[ℝ] ℝ) (D : HelicitySpace →L[ℝ] HelicitySpace) :
    covectorDet (fun i => (a i).comp D) = LinearMap.det D.toLinearMap * covectorDet a := by
  let A : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun i j => a i (batemanCartesianBasis j)
  let B := LinearMap.toMatrix batemanCartesianBasis batemanCartesianBasis D.toLinearMap
  have hAB : (Matrix.of fun i j => ((a i).comp D) (batemanCartesianBasis j)) = A * B := by
    ext i j
    change a i (D (batemanCartesianBasis j)) = _
    conv_lhs => rw [← batemanCartesianBasis.sum_repr (D (batemanCartesianBasis j)), map_sum]
    simp [Matrix.mul_apply, A, B, LinearMap.toMatrix_apply, map_smul, smul_eq_mul, mul_comm]
  unfold covectorDet
  rw [hAB, Matrix.det_mul, LinearMap.det_toMatrix]
  ac_rfl

/-- The electric helicity density written as real coordinate determinants. -/
private theorem bateman_helicity_determinants (p q : ℕ) (t : ℝ) (s : HelicitySpace) :
    let a := batemanAlphaPower p t s
    let da := fderiv ℝ (batemanAlphaPower p t) s
    let db := fderiv ℝ (batemanBetaPower q t) s
    let br := Complex.reCLM.comp db
    let bi := Complex.imCLM.comp db
    batemanElectricHelicityDensity p q t s =
      a.im * covectorDet ![br, Complex.reCLM.comp da, bi] -
      a.re * covectorDet ![br, Complex.imCLM.comp da, bi] := by
  rcases s with ⟨x, y, z⟩
  let s : HelicitySpace := (x, y, z)
  let a := batemanAlphaPower p t s
  let da := fderiv ℝ (batemanAlphaPower p t) s
  let db := fderiv ℝ (batemanBetaPower q t) s
  change batemanElectricHelicityDensity p q t (x, y, z) =
    a.im * covectorDet ![Complex.reCLM.comp db, Complex.reCLM.comp da, Complex.imCLM.comp db] -
    a.re * covectorDet ![Complex.reCLM.comp db, Complex.imCLM.comp da, Complex.imCLM.comp db]
  have hf : rationalPowerField p q x y z t =
      cross3 (fun j => da (batemanAxis j)) (fun j => db (batemanAxis j)) := by
    simp only [da, db, s, fderiv_batemanAlphaPower_axis, fderiv_batemanBetaPower_axis, rationalPowerField]
  have hP : ∀ j : Fin 3, batemanPotential p q t (x, y, z) (batemanAxis j) = a * db (batemanAxis j) := by
    intro j
    rfl
  unfold batemanElectricHelicityDensity
  simp only [hP, hf]
  simp [dot3, cross3, covectorDet, Matrix.det_fin_three, batemanCartesianBasis_apply,
    Complex.mul_re, Complex.sub_re, sub_mul]
  ring

/-- A smooth scalar which is constant along each Bateman ray has initial
differential equal to the spatial pullback of its later differential. -/
private theorem differential_transport (f : HelicitySpace → ℂ) (f₀ : HelicitySpace → ℂ)
    (t : ℝ) (s : HelicitySpace) (hf : Differentiable ℝ f)
    (h : ∀ x, f (batemanRay t x) = f₀ x) :
    (fderiv ℝ f (batemanRay t s)).comp (fderiv ℝ (batemanRay t) s) = fderiv ℝ f₀ s := by
  have hcomp : f ∘ batemanRay t = f₀ := funext h
  have hRay := (contDiff_bateman_ray t).differentiable (by simp) s
  have hD := ((hf _).hasFDerivAt.comp s hRay.hasFDerivAt).fderiv
  rw [hcomp] at hD
  exact hD.symm

/-- Both powered scalar differentials are pulled back by the same spatial ray. -/
private theorem batemanDifferentialPullback (p q : ℕ) (t : ℝ) (s : HelicitySpace) :
    let D := fderiv ℝ (batemanRay t) s
    let y := batemanRay t s
    (fderiv ℝ (batemanAlphaPower p t) y).comp D = fderiv ℝ (batemanAlphaPower p 0) s ∧
    (fderiv ℝ (batemanBetaPower q t) y).comp D = fderiv ℝ (batemanBetaPower q 0) s := by
  exact ⟨differential_transport _ _ _ _ ((contDiff_batemanAlphaPower p t).differentiable (by simp))
      (fun x => congrArg (fun w : ℂ × ℂ => w.1 ^ p) (batemanPairAt_batemanRay t x)),
    differential_transport _ _ _ _ ((contDiff_batemanBetaPower q t).differentiable (by simp))
      (fun x => congrArg (fun w : ℂ × ℂ => w.2 ^ q) (batemanPairAt_batemanRay t x))⟩

/-- The real electric vector of the powered Bateman field on a physical slice. -/
noncomputable def batemanElectricVector (p q : ℕ) (t : ℝ) (s : HelicitySpace) : HelicitySpace :=
  batemanCartesianCoordinates.symm fun j => (rationalPowerField p q s.1 s.2.1 s.2.2 t j).re

/-- The real magnetic vector of the powered Bateman field on a physical slice. -/
noncomputable def batemanMagneticVector (p q : ℕ) (t : ℝ) (s : HelicitySpace) : HelicitySpace :=
  batemanCartesianCoordinates.symm fun j => (rationalPowerField p q s.1 s.2.1 s.2.2 t j).im

/-- Pairing the physical vectors with a real spatial covector amounts to
augmenting the real and imaginary parts of the wedge by that covector. -/
private theorem batemanVectorDeterminants (p q : ℕ) (t : ℝ) (s : HelicitySpace)
    (c : HelicitySpace →L[ℝ] ℝ) :
    let da := fderiv ℝ (batemanAlphaPower p t) s
    let db := fderiv ℝ (batemanBetaPower q t) s
    let ar := Complex.reCLM.comp da
    let ai := Complex.imCLM.comp da
    let br := Complex.reCLM.comp db
    let bi := Complex.imCLM.comp db
    c (batemanElectricVector p q t s) = covectorDet ![c, ar, br] - covectorDet ![c, ai, bi] ∧
    c (batemanMagneticVector p q t s) = covectorDet ![c, ar, bi] + covectorDet ![c, ai, br] := by
  rcases s with ⟨x, y, z⟩
  have hc (v : Fin 3 → ℝ) :
      c (batemanCartesianCoordinates.symm v) =
        c (batemanAxis 0) * v 0 + c (batemanAxis 1) * v 1 + c (batemanAxis 2) * v 2 := by
    have hv : batemanCartesianCoordinates.symm v =
        v 0 • batemanAxis 0 + v 1 • batemanAxis 1 + v 2 • batemanAxis 2 := by
      change (v 0, v 1, v 2) = _
      simp [batemanAxis, Prod.smul_mk, Prod.mk_add_mk]
    rw [hv]
    simp [mul_comm]
  constructor <;>
    simp [batemanElectricVector, batemanMagneticVector, hc, rationalPowerField, cross3,
      covectorDet, Matrix.det_fin_three, batemanCartesianBasis_apply, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, fderiv_batemanAlphaPower_axis, fderiv_batemanBetaPower_axis] <;>
    ring

/-- Under the derivative of the physical ray map, the actual electric
and magnetic vectors are transported with the same positive spatial
Jacobian. This is an identity on the entire space, including field zeros. -/
theorem batemanRay_transports_vectors (p q : ℕ) (t : ℝ) (s : HelicitySpace) :
    let D := fderiv ℝ (batemanRay t) s
    let y := batemanRay t s
    D (batemanElectricVector p q 0 s) = LinearMap.det D.toLinearMap • batemanElectricVector p q t y ∧
    D (batemanMagneticVector p q 0 s) = LinearMap.det D.toLinearMap • batemanMagneticVector p q t y := by
  let D := fderiv ℝ (batemanRay t) s
  let y := batemanRay t s
  obtain ⟨ha, hb⟩ := batemanDifferentialPullback p q t s
  have hdet (c : HelicitySpace →L[ℝ] ℝ) (L M : ℂ →L[ℝ] ℝ) :
      covectorDet ![c.comp D, L.comp (fderiv ℝ (batemanAlphaPower p 0) s),
        M.comp (fderiv ℝ (batemanBetaPower q 0) s)] =
      LinearMap.det D.toLinearMap * covectorDet ![c, L.comp (fderiv ℝ (batemanAlphaPower p t) y),
        M.comp (fderiv ℝ (batemanBetaPower q t) y)] := by
    rw [← covectorDet_comp]
    congr 1
    funext j
    fin_cases j
    · rfl
    · exact congrArg (fun L' => L.comp L') ha.symm
    · exact congrArg (fun M' => M.comp M') hb.symm
  have h (c : HelicitySpace →L[ℝ] ℝ) :
      c (D (batemanElectricVector p q 0 s)) =
        c (LinearMap.det D.toLinearMap • batemanElectricVector p q t y) ∧
      c (D (batemanMagneticVector p q 0 s)) =
        c (LinearMap.det D.toLinearMap • batemanMagneticVector p q t y) := by
    obtain ⟨he₀, hm₀⟩ := batemanVectorDeterminants p q 0 s (c.comp D)
    obtain ⟨he, hm⟩ := batemanVectorDeterminants p q t y c
    constructor
    · change (c.comp D) (batemanElectricVector p q 0 s) = _
      rw [he₀, hdet, hdet, map_smul, he, smul_eq_mul, mul_sub]
    · change (c.comp D) (batemanMagneticVector p q 0 s) = _
      rw [hm₀, hdet, hdet, map_smul, hm, smul_eq_mul, mul_add]
  let xCoord := ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)
  let yzCoord := ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)
  let yCoord := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp yzCoord
  let zCoord := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp yzCoord
  exact ⟨Prod.ext (h xCoord).1 (Prod.ext (h yCoord).1 (h zCoord).1),
    Prod.ext (h xCoord).2 (Prod.ext (h yCoord).2 (h zCoord).2)⟩

/-- An oriented parametrization of a field line is tangent to the
field with positive speed at each parameter value in its domain. -/
def IsOrientedFieldLine (V : HelicitySpace → HelicitySpace) (γ : ℝ → HelicitySpace)
    (I : Set ℝ) : Prop :=
  ∀ u ∈ I, ∃ speed : ℝ, 0 < speed ∧ HasDerivAt γ (speed • V (γ u)) u

/-- The cofactor transformation with positive determinant preserves
oriented field-line parametrizations in both directions. -/
private theorem orientedFieldLine_ray_iff (t : ℝ) (V W : HelicitySpace → HelicitySpace)
    (hV : ∀ s, let D := fderiv ℝ (batemanRay t) s
      D (V s) = LinearMap.det D.toLinearMap • W (batemanRay t s))
    (γ : ℝ → HelicitySpace) (I : Set ℝ) :
    IsOrientedFieldLine W (batemanRay t ∘ γ) I ↔ IsOrientedFieldLine V γ I := by
  have h (u speed : ℝ) :
      let J := LinearMap.det (fderiv ℝ (batemanRay t) (γ u)).toLinearMap
      HasDerivAt (batemanRay t ∘ γ) ((speed * J) • W (batemanRay t (γ u))) u ↔
        HasDerivAt γ (speed • V (γ u)) u := by
    let D := fderiv ℝ (batemanRay t) (γ u)
    let inv := fun s : HelicitySpace => (batemanSliceHomeomorph t).symm s
    let E := fderiv ℝ inv (batemanRay t (γ u))
    have hD : HasFDerivAt (batemanRay t) D (γ u) :=
      ((contDiff_bateman_ray t).differentiable (by simp) _).hasFDerivAt
    have hE : HasFDerivAt inv E (batemanRay t (γ u)) :=
      ((contDiff_bateman_slice_inverse t).differentiable (by simp) _).hasFDerivAt
    have hVel : D (speed • V (γ u)) =
        (speed * LinearMap.det D.toLinearMap) • W (batemanRay t (γ u)) := by
      rw [map_smul, hV, mul_smul]
    constructor
    · intro hu
      have hcomp : inv ∘ (batemanRay t ∘ γ) = γ :=
        funext fun u => (batemanSliceHomeomorph t).symm_apply_apply (γ u)
      rw [← hVel] at hu
      have hderiv := hE.comp_hasDerivAt u hu
      change HasDerivAt (inv ∘ (batemanRay t ∘ γ)) ((E.comp D) (speed • V (γ u))) u at hderiv
      rwa [hcomp, fderiv_bateman_ray_inverse_comp, ContinuousLinearMap.id_apply] at hderiv
    · intro hu
      simpa only [hVel] using hD.comp_hasDerivAt u hu
  constructor
  · intro hγ u hu
    let J := LinearMap.det (fderiv ℝ (batemanRay t) (γ u)).toLinearMap
    have hJ : 0 < J := det_bateman_ray_pos t (γ u)
    obtain ⟨speed, hp, hspeed⟩ := hγ u hu
    refine ⟨speed / J, div_pos hp hJ, (h u (speed / J)).mp ?_⟩
    change HasDerivAt (batemanRay t ∘ γ) ((speed / J * J) • W (batemanRay t (γ u))) u
    rwa [div_mul_cancel₀ speed hJ.ne']
  · intro hγ u hu
    obtain ⟨speed, hp, hspeed⟩ := hγ u hu
    exact ⟨_, mul_pos hp (det_bateman_ray_pos t (γ u)), (h u speed).mpr hspeed⟩

/-- The ray map transports whole oriented electric and magnetic
field-line parametrizations on any parameter domain. -/
theorem batemanRay_orientedFieldLines_iff (p q : ℕ) (t : ℝ) (γ : ℝ → HelicitySpace) (I : Set ℝ) :
    (IsOrientedFieldLine (batemanElectricVector p q t) (batemanRay t ∘ γ) I ↔
      IsOrientedFieldLine (batemanElectricVector p q 0) γ I) ∧
    (IsOrientedFieldLine (batemanMagneticVector p q t) (batemanRay t ∘ γ) I ↔
      IsOrientedFieldLine (batemanMagneticVector p q 0) γ I) :=
  ⟨orientedFieldLine_ray_iff t _ _ (fun s => (batemanRay_transports_vectors p q t s).1) γ I,
    orientedFieldLine_ray_iff t _ _ (fun s => (batemanRay_transports_vectors p q t s).2) γ I⟩

/-- The electric helicity density pulls back to the initial helicity
density with the signed spatial Jacobian of the physical ray. -/
theorem batemanElectricHelicityDensity_jacobian (p q : ℕ) (t : ℝ) (s : HelicitySpace) :
    LinearMap.det (fderiv ℝ (batemanRay t) s).toLinearMap *
      batemanElectricHelicityDensity p q t (batemanRay t s) =
      batemanElectricHelicityDensity p q 0 s := by
  let y := batemanRay t s
  let D := fderiv ℝ (batemanRay t) s
  let a := batemanAlphaPower p t y
  let da := fderiv ℝ (batemanAlphaPower p t) y
  let db := fderiv ℝ (batemanBetaPower q t) y
  let a₀ := batemanAlphaPower p 0 s
  let da₀ := fderiv ℝ (batemanAlphaPower p 0) s
  let db₀ := fderiv ℝ (batemanBetaPower q 0) s
  let br := Complex.reCLM.comp db
  let bi := Complex.imCLM.comp db
  let br₀ := Complex.reCLM.comp db₀
  let bi₀ := Complex.imCLM.comp db₀
  have ha (x : HelicitySpace) : batemanAlphaPower p t (batemanRay t x) = batemanAlphaPower p 0 x :=
    congrArg (fun w : ℂ × ℂ => w.1 ^ p) (batemanPairAt_batemanRay t x)
  obtain ⟨hdA, hdB⟩ := batemanDifferentialPullback p q t s
  have hdet (L : ℂ →L[ℝ] ℝ) :
      covectorDet ![br₀, L.comp da₀, bi₀] =
        LinearMap.det D.toLinearMap * covectorDet ![br, L.comp da, bi] := by
    rw [← covectorDet_comp]
    congr 1
    funext j
    fin_cases j
    · change Complex.reCLM.comp db₀ = (Complex.reCLM.comp db).comp D
      rw [ContinuousLinearMap.comp_assoc, hdB]
    · change L.comp da₀ = (L.comp da).comp D
      rw [ContinuousLinearMap.comp_assoc, hdA]
    · change Complex.imCLM.comp db₀ = (Complex.imCLM.comp db).comp D
      rw [ContinuousLinearMap.comp_assoc, hdB]
  rw [bateman_helicity_determinants p q t, bateman_helicity_determinants p q 0]
  change LinearMap.det D.toLinearMap *
      (a.im * covectorDet ![br, Complex.reCLM.comp da, bi] -
       a.re * covectorDet ![br, Complex.imCLM.comp da, bi]) =
    a₀.im * covectorDet ![br₀, Complex.reCLM.comp da₀, bi₀] -
      a₀.re * covectorDet ![br₀, Complex.imCLM.comp da₀, bi₀]
  have ha₀ : a = a₀ := ha s
  rw [ha₀, hdet, hdet]
  ring

/-- On triples the square of the product norm is bounded by the sum of
the three coordinate squares used in the stereographic radius. -/
private theorem norm_sq_le_cartesian_radius (x y z : ℝ) :
    ‖(x, y, z)‖ ^ 2 ≤ x ^ 2 + y ^ 2 + z ^ 2 := by
  simp only [Prod.norm_def, Real.norm_eq_abs, max_def]
  repeat' split
  all_goals
    rw [sq_abs]
    nlinarith only [sq_nonneg x, sq_nonneg y, sq_nonneg z]

/-- Product Lebesgue volume is the additive Haar measure on physical triples. -/
private theorem helicitySpace_volume_isAddHaarMeasure : (volume : Measure HelicitySpace).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod ℝ (ℝ × ℝ), Measure.volume_eq_prod ℝ ℝ]
  infer_instance

/-- The initial electric helicity density is absolutely integrable over
all of three-space, using its (O(|x|^{-6})) bound. -/
theorem integrable_batemanElectricHelicityDensity_zero (p q : ℕ) :
    Integrable (batemanElectricHelicityDensity p q 0) := by
  have := helicitySpace_volume_isAddHaarMeasure
  have hdim : (Module.finrank ℝ HelicitySpace : ℝ) < 6 := by
    simp only [Module.finrank_prod, Module.finrank_self]
    norm_num
  have hweight : Integrable (fun s : HelicitySpace => ((1 + ‖s‖ ^ 2) ^ 3)⁻¹) := by
    convert integrable_rpow_neg_one_add_norm_sq
      (μ := (volume : Measure HelicitySpace)) hdim using 2
    rw [show (-6 : ℝ) / 2 = -(3 : ℝ) by norm_num, Real.rpow_neg (by positivity)]
    norm_num
  have hc : Continuous (batemanElectricHelicityDensity p q 0) := by
    have hcoords : Continuous (fun s : HelicitySpace => (s.1, s.2.1, s.2.2, (0 : ℝ))) := by fun_prop
    have hA := Complex.continuous_normSq.comp (contDiff_rationalAlpha.continuous.comp hcoords)
    have hB := Complex.continuous_normSq.comp (contDiff_rationalBeta.continuous.comp hcoords)
    refine Continuous.congr (f := fun s : HelicitySpace => 8 * (p : ℝ) * (q : ℝ) ^ 2 *
      Complex.normSq (rationalAlpha s.1 s.2.1 s.2.2 0) ^ p *
      Complex.normSq (rationalBeta s.1 s.2.1 s.2.2 0) ^ (q - 1) /
      (s.1 ^ 2 + s.2.1 ^ 2 + s.2.2 ^ 2 + 1) ^ 3) ?_ ?_
    · exact ((continuous_const.mul (hA.pow p)).mul (hB.pow (q - 1))).div
        (by fun_prop) (fun _ => by positivity)
    · rintro ⟨x, y, z⟩
      exact (batemanElectricHelicityDensity_zero_time p q x y z).symm
  refine (hweight.const_mul (8 * (p : ℝ) * (q : ℝ) ^ 2)).mono' hc.aestronglyMeasurable
    (Eventually.of_forall ?_)
  rintro ⟨x, y, z⟩
  change ‖batemanElectricHelicityDensity p q 0 (x, y, z)‖ ≤ _
  rw [Real.norm_eq_abs]
  have hnonneg : 0 ≤ batemanElectricHelicityDensity p q 0 (x, y, z) := by
    rw [batemanElectricHelicityDensity_zero_time]
    exact div_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (pow_nonneg (Complex.normSq_nonneg _) _)) (pow_nonneg (Complex.normSq_nonneg _) _))
      (by positivity)
  rw [abs_of_nonneg hnonneg, batemanElectricHelicityDensity_zero_time]
  let d := x ^ 2 + y ^ 2 + z ^ 2 + 1
  let a := Complex.normSq (rationalAlpha x y z 0)
  let b := Complex.normSq (rationalBeta x y z 0)
  have hu : a + b = 1 := complex_rational_pair_unit x y z 0
  have ha : 0 ≤ a := Complex.normSq_nonneg _
  have hb : 0 ≤ b := Complex.normSq_nonneg _
  have ha₁ : a ^ p ≤ 1 := pow_le_one₀ ha (by linarith only [hu, hb])
  have hb₁ : b ^ (q - 1) ≤ 1 := pow_le_one₀ hb (by linarith only [hu, ha])
  have hD : (1 + ‖(x, y, z)‖ ^ 2) ^ 3 ≤ d ^ 3 := by
    apply pow_le_pow_left₀ (by positivity)
    unfold d
    linarith only [norm_sq_le_cartesian_radius x y z]
  have hcoeff : 0 ≤ 8 * (p : ℝ) * (q : ℝ) ^ 2 := by positivity
  change 8 * (p : ℝ) * (q : ℝ) ^ 2 * a ^ p * b ^ (q - 1) / d ^ 3 ≤
    8 * (p : ℝ) * (q : ℝ) ^ 2 * ((1 + ‖(x, y, z)‖ ^ 2) ^ 3)⁻¹
  calc
    _ ≤ (8 * (p : ℝ) * (q : ℝ) ^ 2 * 1 * 1) / d ^ 3 := by
      gcongr
    _ = 8 * (p : ℝ) * (q : ℝ) ^ 2 * (d ^ 3)⁻¹ := by simp [div_eq_mul_inv]
    _ ≤ _ := mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hD) hcoeff

/-- A density pulled back by the positive Bateman Jacobian has the
same integrability and total mass as its initial density. -/
theorem integrable_and_integral_of_batemanRay (t : ℝ) (g g₀ : HelicitySpace → ℝ)
    (h : ∀ x, LinearMap.det (fderiv ℝ (batemanRay t) x).toLinearMap *
      g (batemanRay t x) = g₀ x) (hi : Integrable g₀) :
    Integrable g ∧ (∫ x : HelicitySpace, g x) = ∫ x : HelicitySpace, g₀ x := by
  let f := batemanRay t
  let D := fderiv ℝ f
  have hsurj : f '' (univ : Set HelicitySpace) = univ := by
    rw [image_univ]
    exact (batemanSliceHomeomorph t).surjective.range_eq
  have hinj : InjOn f univ := (batemanSliceHomeomorph t).injective.injOn
  have hD : ∀ x ∈ univ, HasFDerivWithinAt f (D x) univ x :=
    fun x _ => ((contDiff_bateman_ray t).differentiable (by simp) x).hasFDerivAt.hasFDerivWithinAt
  have hweight (x : HelicitySpace) :
      |LinearMap.det (D x).toLinearMap| • g (f x) = g₀ x := by
    rw [abs_of_pos (det_bateman_ray_pos t x), smul_eq_mul, h x]
  have := helicitySpace_volume_isAddHaarMeasure
  constructor
  · have h := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume MeasurableSet.univ hD hinj g
    rw [hsurj, integrableOn_univ, integrableOn_univ] at h
    exact h.mpr (hi.congr
      (Eventually.of_forall fun x => (hweight x).symm))
  · have h := integral_image_eq_integral_abs_det_fderiv_smul volume MeasurableSet.univ hD hinj g
    rw [hsurj, setIntegral_univ, setIntegral_univ] at h
    rw [h, integral_congr_ae (Eventually.of_forall hweight)]

/-- The electric helicity is an absolutely convergent whole-space
integral at every real time and equals its initial value. -/
theorem integrable_and_conserved_batemanElectricHelicity (p q : ℕ) (t : ℝ) :
    Integrable (batemanElectricHelicityDensity p q t) ∧
      (∫ x : HelicitySpace, batemanElectricHelicityDensity p q t x) =
        ∫ x : HelicitySpace, batemanElectricHelicityDensity p q 0 x :=
  integrable_and_integral_of_batemanRay t _ _ (batemanElectricHelicityDensity_jacobian p q t)
    (integrable_batemanElectricHelicityDensity_zero p q)

/-- The real magnetic helicity is also absolutely convergent and at
every time is equal to the initial electric helicity in the Bateman gauge. -/
theorem integrable_and_conserved_batemanMagneticHelicity (p q : ℕ) (t : ℝ) :
    Integrable (batemanMagneticHelicityDensity p q t) ∧
      (∫ x : HelicitySpace, batemanMagneticHelicityDensity p q t x) =
        ∫ x : HelicitySpace, batemanElectricHelicityDensity p q 0 x := by
  have h : batemanElectricHelicityDensity p q t = batemanMagneticHelicityDensity p q t :=
    funext (bateman_electric_helicity_eq_magnetic p q t)
  simpa only [← h] using integrable_and_conserved_batemanElectricHelicity p q t

end Qatlib.Papers.KnotLight13.TorusFamily
