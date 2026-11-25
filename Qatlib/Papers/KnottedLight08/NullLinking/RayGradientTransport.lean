/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.NullLinking.ReflectedRayDifferential
public import Qatlib.Papers.KnottedLight08.HopfField.RanadaBateman

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Transport of the magnetic vector field by the reflected rays

[IrvineBouwmeester2008KnottedLight], Eq. (2) and Fig. 1,
[DOI](https://doi.org/10.1038/nphys1056).
The two Bateman gradients transform as covectors under the spatial ray
map. Their cross product and its real part therefore obey the cofactor
law. In the exact Rañada normalization the spatial differential sends
the initial magnetic vector to the new magnetic vector times the
positive determinant of the reflected ray map.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.NullLinking

open Module
open Qatlib.Papers.KnottedLight08.HopfField (cross3 squaredLength dot3)
open Qatlib.Papers.KnotLight13.TorusFamily (rationalAlpha rationalBeta)
open Qatlib.Papers.KnotLight13.TorusFamily
open Qatlib.Papers.KnottedLight08.HopfField
open scoped ComplexConjugate

/-- The linear identification of physical triples with their three
Cartesian coordinates. -/
def cartesianCoordinates : (ℝ × ℝ × ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ) where
  toFun s := ![s.1, s.2.1, s.2.2]
  invFun v := (v 0, v 1, v 2)
  left_inv := by rintro ⟨x, y, z⟩; rfl
  right_inv := by
    intro v
    funext i
    fin_cases i <;> rfl
  map_add' := by
    intro a b
    funext i
    fin_cases i <;> rfl
  map_smul' := by
    intro a b
    funext i
    fin_cases i <;> rfl

/-- The coordinate basis of physical triples. -/
noncomputable def cartesianBasis : Basis (Fin 3) ℝ (ℝ × ℝ × ℝ) :=
  (Pi.basisFun ℝ (Fin 3)).map cartesianCoordinates.symm

/-- Basis coordinates are the literal Cartesian entries. -/
private theorem cartesian_basis_repr (x : ℝ × ℝ × ℝ) (j : Fin 3) :
    cartesianBasis.repr x j = cartesianCoordinates x j := by
  change (Pi.basisFun ℝ (Fin 3)).repr (cartesianCoordinates x) j = _
  exact Pi.basisFun_repr ℝ (Fin 3) (cartesianCoordinates x) j

/-- The three basis vectors are the coordinate directions. -/
private theorem cartesian_basis_eq (j : Fin 3) :
    cartesianBasis j = (![(1, 0, 0), (0, 1, 0), (0, 0, 1)] : Fin 3 → ℝ × ℝ × ℝ) j := by
  fin_cases j <;>
    simp [cartesianBasis, Basis.map_apply, Pi.basisFun_apply, cartesianCoordinates]

/-- A complex-valued linear form on physical space is the sum of its
coordinate values times the input coordinates. -/
private theorem clm_eq_sum_cartesian (L : (ℝ × ℝ × ℝ) →L[ℝ] ℂ) (x : ℝ × ℝ × ℝ) :
    L x = ∑ i : Fin 3, (cartesianCoordinates x i : ℂ) * L (cartesianBasis i) := by
  conv_lhs => rw [← cartesianBasis.sum_repr x, map_sum]
  simp only [map_smul, cartesian_basis_repr, Complex.real_smul]

/-- The spatial Jacobian of the ray in the physical Cartesian basis. -/
noncomputable def rayJacobian (t : ℝ) (x : ℝ × ℝ × ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  LinearMap.toMatrix cartesianBasis cartesianBasis (fderiv ℝ (batemanRay t) x).toLinearMap

/-- The ray Jacobian has the determinant of the spatial differential. -/
theorem det_ray_jacobian (t : ℝ) (x : ℝ × ℝ × ℝ) :
    Matrix.det (rayJacobian t x) = LinearMap.det (fderiv ℝ (batemanRay t) x).toLinearMap :=
  LinearMap.det_toMatrix _ _

/-- A Jacobian column is the spatial derivative along its coordinate
direction. -/
private theorem ray_jacobian_apply (t : ℝ) (x : ℝ × ℝ × ℝ) (i j : Fin 3) :
    rayJacobian t x i j = cartesianCoordinates ((fderiv ℝ (batemanRay t) x) (cartesianBasis j)) i := by
  rw [rayJacobian, LinearMap.toMatrix_apply, cartesian_basis_repr]
  rfl

/-- A Cartesian slice in the chosen coordinate with the other
coordinates held fixed. -/
private def spatialCoordinateSection (x : ℝ × ℝ × ℝ) (j : Fin 3) (u : ℝ) : ℝ × ℝ × ℝ :=
  ![(u, x.2.1, x.2.2), (x.1, u, x.2.2), (x.1, x.2.1, u)] j

/-- At the base coordinate a coordinate section gives the base point. -/
private theorem spatial_coordinate_section_at (x : ℝ × ℝ × ℝ) (j : Fin 3) :
    spatialCoordinateSection x j (cartesianCoordinates x j) = x := by
  rcases x with ⟨x, y, z⟩
  fin_cases j <;> rfl

/-- The coordinate section has the corresponding unit vector as derivative. -/
private theorem hasDerivAt_spatial_coordinate_section (x : ℝ × ℝ × ℝ) (j : Fin 3) :
    HasDerivAt (spatialCoordinateSection x j) (cartesianBasis j) (cartesianCoordinates x j) := by
  rcases x with ⟨x, y, z⟩
  rw [cartesian_basis_eq]
  fin_cases j
  · exact (hasDerivAt_id x).prodMk (hasDerivAt_const x (y, z))
  · exact (hasDerivAt_const y x).prodMk ((hasDerivAt_id y).prodMk (hasDerivAt_const y z))
  · exact (hasDerivAt_const z x).prodMk ((hasDerivAt_const z y).prodMk (hasDerivAt_id z))

/-- The first Bateman coordinate on a physical time slice. -/
private noncomputable def alphaSlice (t : ℝ) (x : ℝ × ℝ × ℝ) : ℂ :=
  rationalAlpha x.1 x.2.1 x.2.2 t

/-- The second Bateman coordinate on a physical time slice. -/
private noncomputable def betaSlice (t : ℝ) (x : ℝ × ℝ × ℝ) : ℂ :=
  rationalBeta x.1 x.2.1 x.2.2 t

set_option maxHeartbeats 600000 in
/-- The first Bateman coordinate is smooth on each physical slice. -/
private theorem contDiff_alpha_slice (t : ℝ) : ContDiff ℝ ⊤ (alphaSlice t) := by
  have hi : ContDiff ℝ ⊤ (fun x : ℝ × ℝ × ℝ => (x.1, x.2.1, x.2.2, t)) := by fun_prop
  have h := contDiff_rationalAlpha.comp hi
  change ContDiff ℝ ⊤ (alphaSlice t) at h
  exact h

/-- The second Bateman coordinate is smooth on each physical slice. -/
private theorem contDiff_beta_slice (t : ℝ) : ContDiff ℝ ⊤ (betaSlice t) := by
  have hi : ContDiff ℝ ⊤ (fun x : ℝ × ℝ × ℝ => (x.1, x.2.1, x.2.2, t)) := by fun_prop
  unfold betaSlice
  exact contDiff_rationalBeta.comp hi

/-- Evaluating the Fréchet derivative on the unit vector gives the
actual one-variable coordinate derivative. -/
private theorem fderiv_on_cartesian_basis (f : (ℝ × ℝ × ℝ) → ℂ)
    (x : ℝ × ℝ × ℝ) (j : Fin 3) (hf : DifferentiableAt ℝ f x) :
    fderiv ℝ f x (cartesianBasis j) =
      deriv (fun u => f (spatialCoordinateSection x j u)) (cartesianCoordinates x j) := by
  have h : HasFDerivAt f (fderiv ℝ f x) (spatialCoordinateSection x j (cartesianCoordinates x j)) := by
    rw [spatial_coordinate_section_at]
    exact hf.hasFDerivAt
  exact (h.comp_hasDerivAt _ (hasDerivAt_spatial_coordinate_section x j)).deriv.symm

/-- The actual differential of the first Bateman coordinate agrees
with the previously computed rational gradient. -/
private theorem fderiv_alpha_basis (t : ℝ) (x : ℝ × ℝ × ℝ) (j : Fin 3) :
    fderiv ℝ (alphaSlice t) x (cartesianBasis j) = alphaGradient x.1 x.2.1 x.2.2 t j := by
  rw [fderiv_on_cartesian_basis (alphaSlice t) x j ((contDiff_alpha_slice t).differentiable (by simp) x)]
  rcases x with ⟨x, y, z⟩
  fin_cases j
  · exact (hasDerivAt_rationalAlpha_x x y z t).deriv
  · exact (hasDerivAt_rationalAlpha_y x y z t).deriv
  · exact (hasDerivAt_rationalAlpha_z x y z t).deriv

/-- The actual differential of the second Bateman coordinate agrees
with the previously computed rational gradient. -/
private theorem fderiv_beta_basis (t : ℝ) (x : ℝ × ℝ × ℝ) (j : Fin 3) :
    fderiv ℝ (betaSlice t) x (cartesianBasis j) = betaGradient x.1 x.2.1 x.2.2 t j := by
  rw [fderiv_on_cartesian_basis (betaSlice t) x j ((contDiff_beta_slice t).differentiable (by simp) x)]
  rcases x with ⟨x, y, z⟩
  fin_cases j
  · exact (hasDerivAt_rationalBeta_x x y z t).deriv
  · exact (hasDerivAt_rationalBeta_y x y z t).deriv
  · exact (hasDerivAt_rationalBeta_z x y z t).deriv

/-- The chain rule on an invariant scalar gives the transposed
Jacobian action on its coordinate derivative. -/
private theorem fderiv_of_ray_invariant (t : ℝ) (x : ℝ × ℝ × ℝ)
    (f g : (ℝ × ℝ × ℝ) → ℂ) (hf : DifferentiableAt ℝ f (batemanRay t x))
    (he : (f ∘ batemanRay t) = g) (j : Fin 3) :
    fderiv ℝ g x (cartesianBasis j) =
      ∑ i : Fin 3, (rayJacobian t x i j : ℂ) * fderiv ℝ f (batemanRay t x) (cartesianBasis i) := by
  have hR := ((contDiff_bateman_ray t).differentiable (by simp) x).hasFDerivAt
  have h := (hf.hasFDerivAt.comp x hR).fderiv
  rw [he] at h
  rw [h, ContinuousLinearMap.comp_apply, clm_eq_sum_cartesian]
  simp only [ray_jacobian_apply]

/-- Both Bateman gradients are pulled back by the same transposed
spatial Jacobian. -/
private theorem ray_pulls_back_gradients (t : ℝ) (x : ℝ × ℝ × ℝ) :
    let y := batemanRay t x
    let M := (rayJacobian t x).map Complex.ofRealHom
    alphaGradient x.1 x.2.1 x.2.2 0 = M.transpose.mulVec (alphaGradient y.1 y.2.1 y.2.2 t) ∧
    betaGradient x.1 x.2.1 x.2.2 0 = M.transpose.mulVec (betaGradient y.1 y.2.1 y.2.2 t) := by
  have ha : alphaSlice t ∘ batemanRay t = alphaSlice 0 :=
    funext fun s => congrArg Prod.fst (batemanPairAt_batemanRay t s)
  have hb : betaSlice t ∘ batemanRay t = betaSlice 0 :=
    funext fun s => congrArg Prod.snd (batemanPairAt_batemanRay t s)
  let y := batemanRay t x
  constructor
  · funext j
    have h := fderiv_of_ray_invariant t x (alphaSlice t) (alphaSlice 0)
      ((contDiff_alpha_slice t).differentiable (by simp) y) ha j
    simpa only [Matrix.mulVec, Matrix.transpose_apply, Matrix.map_apply, Complex.ofRealHom_eq_coe,
      dotProduct, fderiv_alpha_basis] using h
  · funext j
    have h := fderiv_of_ray_invariant t x (betaSlice t) (betaSlice 0)
      ((contDiff_beta_slice t).differentiable (by simp) y) hb j
    simpa only [Matrix.mulVec, Matrix.transpose_apply, Matrix.map_apply, Complex.ofRealHom_eq_coe,
      dotProduct, fderiv_beta_basis] using h

/-- The rational Bateman field obeys the spatial cofactor law along its rays. -/
theorem ray_transports_rational_field (t : ℝ) (x : ℝ × ℝ × ℝ) (j : Fin 3) :
    let y := batemanRay t x
    let J := rayJacobian t x
    ((J.map Complex.ofRealHom).mulVec (rationalField x.1 x.2.1 x.2.2 0)) j =
      ((Matrix.det J : ℝ) : ℂ) * rationalField y.1 y.2.1 y.2.2 t j := by
  obtain ⟨ha, hb⟩ := ray_pulls_back_gradients t x
  dsimp only
  have hdet : Matrix.det ((rayJacobian t x).map Complex.ofRealHom) =
      ((Matrix.det (rayJacobian t x) : ℝ) : ℂ) :=
    (Complex.ofRealHom.map_det (rayJacobian t x)).symm
  rw [rationalField, ha, hb, mulVec_cross_of_transposed_covectors, hdet]
  rfl

/-- The real magnetic vector of the actual Rañada field. -/
noncomputable def ranadaMagneticVector (t : ℝ) (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  cartesianCoordinates.symm (fun j => (ranadaB x.1 x.2.1 x.2.2 t j).re)

/-- Under the exact field normalization the Rañada magnetic components
are the real Bateman components at reflected time times (1/(2π)). -/
private theorem ranada_b_eq_scaled_reflected_re (x y z t : ℝ) (j : Fin 3) :
    (ranadaB x y z t j).re = (1 / (2 * Real.pi)) * (rationalField x y z (-t) j).re := by
  have h := congrArg Complex.im (ranadaField_eq_bateman x y z t j)
  have hκ : (Complex.I / (2 * (Real.pi : ℂ))) =
      Complex.I * ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hκ] at h
  simpa only [ranadaField, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    ranadaE_im, Complex.ofReal_im, Complex.ofReal_re, zero_mul, one_mul, zero_add,
    neg_zero, Complex.conj_re, Complex.mul_re, sub_zero] using h

/-- The actual magnetic vector is nowhere zero, since the real
Bateman field has strictly positive squared length. -/
theorem ranada_magnetic_vector_ne_zero (t : ℝ) (x : ℝ × ℝ × ℝ) :
    ranadaMagneticVector t x ≠ 0 := by
  have hPos := rational_electric_length_pos x.1 x.2.1 x.2.2 (-t)
  intro h0
  have hfun : (fun j => (ranadaB x.1 x.2.1 x.2.2 t j).re) = 0 := by
    have h := congrArg cartesianCoordinates h0
    simpa only [ranadaMagneticVector, LinearEquiv.apply_symm_apply, map_zero] using h
  have hRe (j : Fin 3) : (rationalField x.1 x.2.1 x.2.2 (-t) j).re = 0 := by
    have h := congrFun hfun j
    rw [Pi.zero_apply, ranada_b_eq_scaled_reflected_re] at h
    exact (mul_eq_zero.mp h).resolve_left (by positivity)
  simp [electricField, squaredLength, dot3, hRe] at hPos

/-- The reflected ray differential pushes the actual initial magnetic
vector to the actual vector at time `t`, multiplied by the positive
spatial Jacobian determinant. -/
theorem reflected_ray_transports_magnetic_vector (t : ℝ) (x : ℝ × ℝ × ℝ) :
    let y := batemanRay (-t) x
    let D := fderiv ℝ (batemanRay (-t)) x
    D (ranadaMagneticVector 0 x) = LinearMap.det D.toLinearMap • ranadaMagneticVector t y := by
  let y := batemanRay (-t) x
  let D := fderiv ℝ (batemanRay (-t)) x
  let J := rayJacobian (-t) x
  have hCoords (s : ℝ × ℝ × ℝ) (v : ℝ) :
      cartesianCoordinates (ranadaMagneticVector v s) =
        (fun j => (ranadaB s.1 s.2.1 s.2.2 v j).re) :=
    cartesianCoordinates.apply_symm_apply _
  have hRepr (s : ℝ × ℝ × ℝ) :
      (cartesianBasis.repr s : Fin 3 → ℝ) = cartesianCoordinates s :=
    funext (cartesian_basis_repr s)
  have hMatrix : J.mulVec (cartesianCoordinates (ranadaMagneticVector 0 x)) =
      cartesianCoordinates (D (ranadaMagneticVector 0 x)) := by
    simpa only [J, D, rayJacobian, hRepr, ContinuousLinearMap.coe_coe] using
      LinearMap.toMatrix_mulVec_repr cartesianBasis cartesianBasis D.toLinearMap
        (ranadaMagneticVector 0 x)
  apply cartesianCoordinates.injective
  change cartesianCoordinates (D (ranadaMagneticVector 0 x)) =
    cartesianCoordinates (LinearMap.det D.toLinearMap • ranadaMagneticVector t y)
  rw [← hMatrix, map_smul, hCoords, hCoords, ← det_ray_jacobian]
  funext j
  have h := congrArg Complex.re (ray_transports_rational_field (-t) x j)
  have h' : (J.mulVec (fun i => (rationalField x.1 x.2.1 x.2.2 0 i).re)) j =
      Matrix.det J * (rationalField y.1 y.2.1 y.2.2 (-t) j).re := by
    simpa only [J, y, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Complex.add_re, Complex.mul_re,
      Matrix.map_apply, Complex.ofRealHom_eq_coe, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] using h
  simp only [ranada_b_eq_scaled_reflected_re, neg_zero, Pi.smul_apply, smul_eq_mul]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h' ⊢
  linear_combination (1 / (2 * Real.pi)) * h'

end Qatlib.Papers.KnottedLight08.NullLinking
