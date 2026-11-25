/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.HelicitySpec.Balance
public import Qatlib.Papers.KnottedLight08.HopfField.RanadaScalars
public import Qatlib.Papers.KnottedLight08.HopfField.RanadaInitialHelicity
public import Qatlib.Papers.KnottedLight08.HopfField.RanadaCurl
public import Qatlib.Papers.KnottedLight08.HopfField.RanadaEnergy
public import Qatlib.Papers.KnottedLight08.NullLinking.ElectricLinking
public import Qatlib.Papers.KnottedLight08.NullLinking.CompactifiedAxes
public import Qatlib.Papers.KnottedLight08.NullLinking.PoleDiskCrossing
public import Qatlib.Papers.KnottedLight08.NullLinking.UnifiedLinking
public import Qatlib.Papers.KnottedLight08.NullLinking.HopfLinkWinding
public import Qatlib.Papers.KnottedLight08.CurlEigenstate.CKEigenstates
public import Qatlib.Papers.KnottedLight08.CurlEigenstate.HopfSpectrum
public import Qatlib.Papers.KnottedLight08.CurlEigenstate.CKRadialOrigin
public import Qatlib.Papers.KnottedLight08.CurlEigenstate.HopfArticleSpectrum
public import Qatlib.Papers.KnottedLight08.CurlEigenstate.HopfFourierSpectrum
public import Qatlib.Papers.KnottedLight08.CurlEigenstate.HopfPotentialSpace
public import Qatlib.Papers.KnottedLight08.CurlEigenstate.HopfPotentialCurl
public import Qatlib.Papers.KnottedLight08.HelicitySpec.CKPairing
public import Qatlib.Papers.KnottedLight08.HelicitySpec.HopfAzimuthal

/-! Regression consumers for null invariants, Hopf coordinates and helicity balance. -/

@[expose] public section
set_option autoImplicit false

open MeasureTheory
open Qatlib.Papers.KnottedLight08.HopfField
open Qatlib.Papers.KnottedLight08.HelicitySpec
open Qatlib.Papers.KnottedLight08.HopfField
open Qatlib.Papers.KnottedLight08.NullLinking
open Qatlib.Papers.SuperfluidHel18.CenterlineCL (gaussLinking)
open Qatlib.Papers.KnotLight13.TorusFamily
  (Spacetime cartesianCurl cartesianDivergence spaceTimePartial batemanRay)

example : dot3 (riemannSilberstein ![1, 0, 0] ![0, 1, 0])
    (riemannSilberstein ![1, 0, 0] ![0, 1, 0]) = 0 := by
  apply (null_iff _ _).mpr
  norm_num [dot3, squaredLength]

example : dot3 (riemannSilberstein ![1, 0, 0] ![1, 0, 0])
    (riemannSilberstein ![1, 0, 0] ![1, 0, 0]) ≠ 0 := by
  intro h
  have horth := ((null_iff _ _).mp h).1
  norm_num [dot3] at horth

example (x y z : ℝ) : squaredLength (hopf (stereo x y z)) = 1 :=
  hopf_unit _ (stereo_unit x y z)

example (q : Fin 4 → ℝ) : hopf (phaseRotate (3 / 5) (4 / 5) q) = hopf q :=
  hopf_phase_invariant _ _ q (by norm_num)

example : ((Complex.I, 0) : ℂ × ℂ) ∈ unitHopfFiber (1, 0) := by
  apply (mem_unitHopfFiber_iff _ _ (by simp)).2
  exact ⟨Complex.I, by simp, by simp [phaseOrbit]⟩

example : ((0, 1) : ℂ × ℂ) ∉ unitHopfFiber (1, 0) := by
  simp [unitHopfFiber]

/-- A point of the finite magnetic circle of value one lies in the
genuine affine chart and satisfies the printed scalar equation. -/
example : etaDen 1 (-1) 1 0 ≠ 0 ∧ ranadaEta 1 (-1) 1 0 = 1 := by
  have h := (ranadaEta_initial_fiber_iff 1 0 1 (-1) 1 (by norm_num)).2 (by norm_num)
  simpa using h

/-- The coordinate Hopf circles have determinant winding one. -/
example : hopfDeterminantWinding (1, 0) (0, 1) = 1 :=
  hopf_determinant_winding_eq_one _ _ (by simp) (by simp [unitHopfFiber])

#print axioms Qatlib.Papers.KnottedLight08.NullLinking.initialMagneticFiber_isCompact
#print axioms Qatlib.Papers.KnottedLight08.NullLinking.hopf_determinant_winding_eq_one

example (A B : Fin 3 → ℝ) :
    dot3 (dualRotation A) (dualRotation B) = dot3 A B := dual_pairing A B

example : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 0 ∧
    HasDerivAt (fun _ : ℝ => (2 : ℝ)) 0 0 ∧ (1 : ℝ) ≠ 2 := by
  exact ⟨hasDerivAt_const 0 1, hasDerivAt_const 0 2, by norm_num⟩

example (t : ℝ) : (7 : ℝ) = (7 : ℝ) :=
  null_magnetic_conserved (fun _ => 7) (fun _ => 0)
    (fun x => by simpa using (hasDerivAt_const x (7 : ℝ)))
    (fun _ => rfl) 0 t

example (s t : ℝ) : 2 * s + (3 - 2 * s) = 2 * t + (3 - 2 * t) := by
  apply total_helicity_conserved (fun x => 2 * x) (fun x => 3 - 2 * x) (fun _ => -1)
  · intro x
    simpa using (hasDerivAt_id x).const_mul 2
  · intro x
    simpa using HasDerivAt.fun_sub (hasDerivAt_const x (3 : ℝ))
      ((hasDerivAt_id x).const_mul 2)

/-! Regression consumers for the exact Rañada scalars (equation (2)). -/

open scoped ComplexConjugate

example : ranadaEta 0 0 0 0 = 0 := by
  norm_num [ranadaEta, ranadaQ, ranadaR, ranadaP, ranadaS, ranadaA]

example : ranadaZeta 0 0 0 0 = 0 := by
  norm_num [ranadaZeta, ranadaQ, ranadaP, ranadaR, ranadaS, ranadaA]

/-- The exact printed value `-(2 + 4i)/5` of the magnetic scalar at `(1, 1, 0, 0)`. -/
example : ranadaEta 1 1 0 0 = -(((2 : ℝ) : ℂ) + Complex.I * ((4 : ℝ) : ℂ)) / 5 := by
  have hd : ((ranadaP 1 1 0 0 : ℂ) + Complex.I * (ranadaS 1 1 0 0)) ≠ 0 := by
    intro h0
    rw [ofReal_add_iMul_eq_zero_iff] at h0
    norm_num [ranadaP, ranadaS, ranadaA] at h0
  have hcross : (5 : ℂ) * ((ranadaQ 1 1 0 0 : ℂ) + Complex.I * (ranadaR 1 1 0 0))
      = -(((2 : ℝ) : ℂ) + Complex.I * ((4 : ℝ) : ℂ)) *
        ((ranadaP 1 1 0 0 : ℂ) + Complex.I * (ranadaS 1 1 0 0)) := by
    rw [Complex.ext_iff]
    constructor <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.neg_re, Complex.neg_im] <;>
      norm_num [ranadaQ, ranadaR, ranadaP, ranadaS, ranadaA]
  rw [ranadaEta, div_eq_iff hd]
  linear_combination hcross / 5

/-- The exact printed value `-(4 + 2i)/5` of the electric scalar at `(1, 1, 0, 0)`. -/
example : ranadaZeta 1 1 0 0 = -(((4 : ℝ) : ℂ) + Complex.I * ((2 : ℝ) : ℂ)) / 5 := by
  have hd : ((ranadaR 1 1 0 0 : ℂ) + Complex.I * (ranadaS 1 1 0 0)) ≠ 0 := by
    intro h0
    rw [ofReal_add_iMul_eq_zero_iff] at h0
    norm_num [ranadaR, ranadaS, ranadaA] at h0
  have hcross : (5 : ℂ) * ((ranadaP 1 1 0 0 : ℂ) + Complex.I * (ranadaQ 1 1 0 0))
      = -(((4 : ℝ) : ℂ) + Complex.I * ((2 : ℝ) : ℂ)) *
        ((ranadaR 1 1 0 0 : ℂ) + Complex.I * (ranadaS 1 1 0 0)) := by
    rw [Complex.ext_iff]
    constructor <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.neg_re, Complex.neg_im] <;>
      norm_num [ranadaQ, ranadaR, ranadaP, ranadaS, ranadaA]
  rw [ranadaZeta, div_eq_iff hd]
  linear_combination hcross / 5

/-- The point `(0, 1, 0)` at `t = 0` is a genuine pole of the magnetic scalar. -/
example : ranadaP 0 1 0 0 + Complex.I * ranadaS 0 1 0 0 = 0 ∧
    ranadaQ 0 1 0 0 + Complex.I * ranadaR 0 1 0 0 ≠ 0 := by
  refine ⟨(ranadaEta_den_zero_t_zero_iff 0 1 0).mpr ⟨rfl, by norm_num⟩, ?_⟩
  norm_num [ranadaQ, ranadaR, ranadaA]

/-- The point `(1, 0, 0)` at `t = 0` is a genuine pole of the electric scalar. -/
example : ranadaR 1 0 0 0 + Complex.I * ranadaS 1 0 0 0 = 0 ∧
    ranadaP 1 0 0 0 + Complex.I * ranadaQ 1 0 0 0 ≠ 0 := by
  refine ⟨(ranadaZeta_den_zero_t_zero_iff 1 0 0).mpr ⟨rfl, by norm_num⟩, ?_⟩
  norm_num [ranadaQ, ranadaR, ranadaP, ranadaS, ranadaA]

/-- The quaternionic coordinate stays nonzero on both lightlike pole lines. -/
example (t : ℝ) : 0 < ranadaP 0 0 (t + 1) t ^ 2 + ranadaQ 0 0 (t + 1) t ^ 2 +
    ranadaR 0 0 (t + 1) t ^ 2 + ranadaS 0 0 (t + 1) t ^ 2 :=
  ranadaNormSq_pos 0 0 (t + 1) t

example : ranadaP 0 0 (3 - 1) 3 = 0 ∧ ranadaQ 0 0 (3 - 1) 3 ≠ 0 :=
  ⟨(ranada_pole_pastLine 3).1, (ranada_pole_pastLine 3).2.2.2⟩

/-! Regression consumers for the density chart transitions and the global fields. -/

/-- The source-free Maxwell equations apply to the homogeneous field at the
magnetic scalar's genuine pole on the initial circle. -/
example :
    cartesianCurl ranadaFieldAt (0, 1, 0, 0) 2 =
        Complex.I * spaceTimePartial (fun s => ranadaFieldAt s 2) (0, 1, 0, 0) 3 ∧
      cartesianDivergence ranadaFieldAt (0, 1, 0, 0) = 0 :=
  ⟨maxwell_ranadaField 0 1 0 0 2, ranadaField_divergence_free 0 1 0 0⟩

#print axioms Qatlib.Papers.KnottedLight08.HopfField.ranadaField_eq_bateman
#print axioms Qatlib.Papers.KnottedLight08.HopfField.maxwell_ranadaField
#print axioms Qatlib.Papers.KnottedLight08.HopfField.ranadaField_divergence_free

/-- Holomorphic reciprocation preserves the density for concrete data. -/
example (dw : Fin 3 → ℂ) : density (1 / (1 : ℂ)) (fun j => -(dw j) / 1 ^ 2) = density 1 dw :=
  density_recip 1 dw one_ne_zero

/-- Conjugated reciprocation flips the orientation for concrete data. -/
example (dw : Fin 3 → ℂ) (j : Fin 3) :
    density ((conj (1 : ℂ))⁻¹) (fun k => -(conj (dw k)) / (conj 1) ^ 2) j
      = -density 1 dw j := by
  have h := density_conjRecip (1 : ℂ) dw one_ne_zero
  exact congrFun h j

/-- Both global fields take real values at the pole circles of the scalars. -/
example : (ranadaB 0 1 0 0 0).im = 0 ∧ (ranadaE 1 0 0 0 0).im = 0 :=
  ⟨ranadaB_im 0 1 0 0 0, ranadaE_im 1 0 0 0 0⟩

/-- The denominators of both fields never vanish, including on the pole
circles. -/
example : etaSumSq 0 1 0 0 ≠ 0 ∧ zetaSumSq 1 0 0 0 ≠ 0 :=
  ⟨etaSumSq_ne_zero 0 1 0 0, zetaSumSq_ne_zero 1 0 0 0⟩

/-- Where the magnetic scalar is finite at a pole of the electric one, the
global magnetic field is the printed density. -/
example : ranadaB 1 0 0 0 = density (ranadaEta 1 0 0 0) (etaGrad 1 0 0 0) := by
  have hd : etaDen 1 0 0 0 ≠ 0 := by
    intro h0
    have h2 := (ranadaEta_den_zero_t_zero_iff 1 0 0).mp h0
    norm_num at h2
  exact (ranadaB_eq_density hd).symm

/-- Around genuine poles of the magnetic scalar the same field is the density
of the reciprocal chart (smooth gluing at the pole `(0, 1, 0)` at `t = 0`). -/
example : etaDen 0 1 0 0 = 0 ∧
    density (etaRecip 0 1 0 0) (etaRecipGrad 0 1 0 0) = ranadaB 0 1 0 0 := by
  refine ⟨by norm_num [etaDen, ranadaP, ranadaS, ranadaA], ?_⟩
  refine ranadaB_eq_density_recip ?_
  intro h0
  rw [etaNum, ofReal_add_iMul_eq_zero_iff] at h0
  norm_num [ranadaQ, ranadaR, ranadaA] at h0

/-! Regression consumers for the pointwise null invariants. -/

/-- The Hopf electric and magnetic fields are pointwise orthogonal. -/
example (x y z t : ℝ) : dot3 (ranadaE x y z t) (ranadaB x y z t) = 0 :=
  Qatlib.Papers.KnottedLight08.NullLinking.ranadaE_dot_ranadaB x y z t

/-- The Hopf electric and magnetic fields have equal bilinear squares. -/
example (x y z t : ℝ) :
    dot3 (ranadaE x y z t) (ranadaE x y z t) = dot3 (ranadaB x y z t) (ranadaB x y z t) :=
  Qatlib.Papers.KnottedLight08.NullLinking.ranadaE_sq_eq_ranadaB_sq x y z t

/-- The electric field at the spacetime origin is `(0, 2/π, 0)`. -/
example : ranadaE 0 0 0 0 0 = 0 ∧ ranadaE 0 0 0 0 1 = ((2 / Real.pi : ℝ) : ℂ) ∧
    ranadaE 0 0 0 0 2 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [ranadaE, zetaSumSq, zetaNum, zetaDen, ranadaP, ranadaQ, ranadaR, ranadaS,
      ranadaA, zetaHomog, zetaNumGrad, zetaDenGrad, zetaNumX, zetaNumY, zetaNumZ, zetaDenX,
      zetaDenY, zetaDenZ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons, cross3, conj_add', conj_mul', Complex.conj_ofReal,
      Complex.conj_I]
    norm_num [Complex.I_mul_I, Complex.conj_ofNat, Complex.conj_ofReal]
  · simp only [ranadaE, zetaSumSq, zetaNum, zetaDen, ranadaP, ranadaQ, ranadaR, ranadaS,
      ranadaA, zetaHomog, zetaNumGrad, zetaDenGrad, zetaNumX, zetaNumY, zetaNumZ, zetaDenX,
      zetaDenY, zetaDenZ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons, cross3, conj_add', conj_mul', Complex.conj_ofReal,
      Complex.conj_I]
    norm_num [Complex.I_mul_I, Complex.conj_ofNat, Complex.conj_ofReal]
    try field_simp
    try norm_num [Complex.I_mul_I, Complex.conj_ofNat, Complex.conj_ofReal]
  · simp only [ranadaE, zetaSumSq, zetaNum, zetaDen, ranadaP, ranadaQ, ranadaR, ranadaS,
      ranadaA, zetaHomog, zetaNumGrad, zetaDenGrad, zetaNumX, zetaNumY, zetaNumZ, zetaDenX,
      zetaDenY, zetaDenZ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons, cross3, conj_add', conj_mul', Complex.conj_ofReal,
      Complex.conj_I]
    norm_num [Complex.I_mul_I, Complex.conj_ofNat, Complex.conj_ofReal]

/-- The magnetic field at the spacetime origin is `(-2/π, 0, 0)`. -/
example : ranadaB 0 0 0 0 0 = ((-2 / Real.pi : ℝ) : ℂ) ∧ ranadaB 0 0 0 0 1 = 0 ∧
    ranadaB 0 0 0 0 2 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [ranadaB, etaSumSq, etaNum, etaDen, ranadaP, ranadaQ, ranadaR, ranadaS,
      ranadaA, etaHomog, etaNumGrad, etaDenGrad, etaNumX, etaNumY, etaNumZ, etaDenX, etaDenY,
      etaDenZ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons, cross3, conj_add', conj_mul', Complex.conj_ofReal,
      Complex.conj_I]
    norm_num [Complex.I_mul_I, Complex.conj_ofNat, Complex.conj_ofReal]
    try field_simp
    try norm_num [Complex.I_mul_I, Complex.conj_ofNat, Complex.conj_ofReal]
  · simp only [ranadaB, etaSumSq, etaNum, etaDen, ranadaP, ranadaQ, ranadaR, ranadaS,
      ranadaA, etaHomog, etaNumGrad, etaDenGrad, etaNumX, etaNumY, etaNumZ, etaDenX, etaDenY,
      etaDenZ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons, cross3, conj_add', conj_mul', Complex.conj_ofReal,
      Complex.conj_I]
    norm_num [Complex.I_mul_I, Complex.conj_ofNat, Complex.conj_ofReal]
  · simp only [ranadaB, etaSumSq, etaNum, etaDen, ranadaP, ranadaQ, ranadaR, ranadaS,
      ranadaA, etaHomog, etaNumGrad, etaDenGrad, etaNumX, etaNumY, etaNumZ, etaDenX, etaDenY,
      etaDenZ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons, cross3, conj_add', conj_mul', Complex.conj_ofReal,
      Complex.conj_I]
    norm_num [Complex.I_mul_I, Complex.conj_ofNat, Complex.conj_ofReal]

/-- At the magnetic chart pole `(0,1,0)` the smooth potential has a
nonzero third curl component, with the magnetic sign of Eq. (2). -/
example : (cartesianCurl (fun s j => (ranadaInitialPotential s.1 s.2.1 s.2.2.1 j : ℂ))
    (0, 1, 0, 0) 2).re = -1 / (2 * Real.pi) := by
  rw [curl_ranada_initial_potential, ranada_b_initial_re]
  norm_num [hopfScale, initialMagneticDirection]
  ring

/-- The full initial helicity is an absolutely convergent integral
with its literal field normalization. -/
example : Integrable ranadaInitialHelicityDensity ∧
    (∫ s : EuclideanSpace ℝ (Fin 3), ranadaInitialHelicityDensity s) = 1 / 4 :=
  ⟨integrable_ranada_initial_helicity, integral_ranada_initial_helicity⟩

/-- The squared third complex field component is integrable at a
nonzero time. -/
example : Integrable (fun s : EuclideanSpace ℝ (Fin 3) =>
    Complex.normSq (ranadaField (s 0) (s 1) (s 2) 1 2)) :=
  integrable_normSq_ranada_field 1 2

#print axioms curl_ranada_initial_potential
#print axioms tendsto_ranada_field_spatial_infinity
#print axioms integrable_ranada_energy
#print axioms integral_ranada_initial_helicity

/-- The finite fiber at scalar value one has nonzero derivative in the
negative first-coordinate direction at angle zero. -/
example : HasDerivAt (fun θ : ℝ => initialMagneticCircle 1 0 θ 0) (-1) 0 := by
  have h := hasDerivAt_initial_magnetic_circle 1 0 0 0
  norm_num [initialMagneticCircleTangent, planeDisplacement] at h
  exact h

/-- A finite nonzero magnetic fiber is still traced by the transported
circle at a nonzero time. -/
example : magneticCircleAt 1 0 1 0 ∈ magneticFiberAt 1 1 := by
  have h : magneticCircleAt 1 0 1 0 ∈ Set.range (magneticCircleAt 1 0 1) := ⟨0, rfl⟩
  rw [range_magnetic_circle_at 1 0 1 (by norm_num)] at h
  simpa using h

/-- The concrete initial pole `(0,1,0)` remains a pole at the point
`(-1,1,0)` of the time-one slice. -/
example : etaDen (-1) 1 0 1 = 0 := by
  have h : magneticPoleCircleAt 1 0 ∈ Set.range (magneticPoleCircleAt 1) := ⟨0, rfl⟩
  rw [range_magnetic_pole_circle_at] at h
  norm_num [magneticPoleCircleAt, batemanRay] at h
  exact h

#print axioms ranada_b_along_initial_magnetic_circle
#print axioms range_magnetic_circle_at
#print axioms range_magnetic_pole_circle_at
#print axioms ranada_b_along_initial_magnetic_pole_circle

/-- The transported finite magnetic line is regular at a negative time. -/
example : deriv (magneticCircleAt 1 0 (-1)) 0 ≠ 0 := by
  obtain ⟨_, _, hne, h⟩ := hasDerivAt_magnetic_circle_at 1 0 (-1) 0 (by norm_num)
  rw [h.deriv]
  exact hne

/-- The nonzero tangent of the transported pole is positively aligned
with the actual magnetic field at time one. -/
example : ∃ μ : ℝ, 0 < μ ∧
    (μ • ranadaMagneticVector 1 (magneticPoleCircleAt 1 0)) ≠ 0 ∧
    HasDerivAt (magneticPoleCircleAt 1)
      (μ • ranadaMagneticVector 1 (magneticPoleCircleAt 1 0)) 0 :=
  hasDerivAt_magnetic_pole_circle_at 1 0

#print axioms Qatlib.Papers.KnotLight13.TorusFamily.det_bateman_ray_pos
#print axioms reflected_ray_transports_magnetic_vector
#print axioms hasDerivAt_magnetic_circle_at
#print axioms hasDerivAt_magnetic_pole_circle_at

/-- The actual Gauss integral of two disjoint finite fibers agrees on
two opposite nonzero time slices. -/
example : gaussLinking (cartesianCoordinates ∘ magneticCircleAt 1 0 (-1))
        (cartesianCoordinates ∘ magneticCircleAt (-1) 0 (-1)) =
      gaussLinking (cartesianCoordinates ∘ magneticCircleAt 1 0 1)
        (cartesianCoordinates ∘ magneticCircleAt (-1) 0 1) := by
  apply gaussLinking_magnetic_circles_eq <;> norm_num

/-- The projective pole has a conserved Gauss integral with a finite
fiber even across slices with a vanishing affine denominator on the pole. -/
example : gaussLinking (cartesianCoordinates ∘ magneticCircleAt 1 0 0)
        (cartesianCoordinates ∘ magneticPoleCircleAt 0) =
      gaussLinking (cartesianCoordinates ∘ magneticCircleAt 1 0 1)
        (cartesianCoordinates ∘ magneticPoleCircleAt 1) := by
  apply gaussLinking_magnetic_circle_pole_eq
  norm_num

#print axioms gaussLinking_magnetic_circles_eq
#print axioms gaussLinking_magnetic_circle_pole_eq

/-- The real-label circle deforms to larger circles with the same
Gauss integral against the initial pole. -/
example : gaussLinking (realLabelMagneticCircle 2) (cartesianCoordinates ∘ magneticPoleCircleAt 0) =
    gaussLinking (realLabelMagneticCircle 1) (cartesianCoordinates ∘ magneticPoleCircleAt 0) :=
  gaussLinking_real_label_pole_eq (by norm_num) (by norm_num)

/-- The axis limit has positive Gauss density at the disk crossing. -/
example : rescaledMagneticGaussKernel 0 0 0 = 1 / (4 * Real.pi) := by
  rw [rescaledMagneticGaussKernel_zero]
  norm_num

/-- The concrete circle with label one crosses the open pole disk
with the orientation of the magnetic field. -/
example : ∃! θ : ℝ, θ ∈ Set.Ico 0 (2 * Real.pi) ∧ initialMagneticCircle 1 0 θ 0 = 0 ∧
    initialMagneticCircle 1 0 θ 1 ^ 2 + initialMagneticCircle 1 0 θ 2 ^ 2 < 1 ∧
    0 < -deriv (fun s => initialMagneticCircle 1 0 s 0) θ :=
  initial_magnetic_circle_pole_disk_positive_crossing 1 0 (by norm_num)

#print axioms initial_magnetic_circle_pole_disk_positive_crossing
#print axioms gaussLinking_real_label_pole_eq
#print axioms le_rescaledMagneticCircle_pole_chord
#print axioms tendsto_rescaledMagneticGaussKernel

/-- Two distinct finite magnetic labels with equal moduli have
positive linking value on a nonzero time slice. -/
example : gaussLinking (cartesianCoordinates ∘ magneticCircleAt 1 0 2)
    (cartesianCoordinates ∘ magneticCircleAt 0 1 2) = 1 := by
  apply gaussLinking_magnetic_circles_eq_one
  · norm_num
  · norm_num
  · intro h
    have he := congrArg Complex.re h
    norm_num at he

/-- The transported electric pole is the entire zero set of the
electric denominator on a negative-time slice. -/
example : Set.range (electricPoleCircleAt (-1)) =
    {s : ℝ × ℝ × ℝ | zetaDen s.1 s.2.1 s.2.2 (-1) = 0} :=
  range_electric_pole_circle_at (-1)

/-- The electric linking value uses the original positive orientation
of the field line's parameter after the proper rotation. -/
example : gaussLinking (cartesianCoordinates ∘ electricCircleAt 0 (-1) (-2))
    (cartesianCoordinates ∘ electricPoleCircleAt (-2)) = 1 :=
  gaussLinking_electric_circle_pole_eq_one 0 (-1) (-2) (by norm_num)

/-- The true electric tangent remains nonzero at a point of the
transported electric pole. -/
example : deriv (electricPoleCircleAt (-2)) 0 ≠ 0 := by
  obtain ⟨_, _, hn, h⟩ := hasDerivAt_electric_pole_circle_at (-2) 0
  rw [h.deriv]
  exact hn

#print axioms tendsto_truncatedMagneticGaussIntegral
#print axioms gaussLinking_magnetic_circle_pole_eq_one
#print axioms gaussLinking_magnetic_circles_eq_one
#print axioms ranadaB_quarterTurn_eq_ranadaE
#print axioms hasDerivAt_electric_circle_at
#print axioms hasDerivAt_electric_pole_circle_at
#print axioms gaussLinking_electric_circle_pole_eq_one
#print axioms gaussLinking_electric_circles_eq_one

/-- The actual zero-label electric axis on a nonzero slice closes
to a circle in the one-point compactification. -/
example : Nonempty (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ
    closure (((↑) : ℝ × ℝ × ℝ → OnePoint (ℝ × ℝ × ℝ)) '' electricFiberAt 1 0)) :=
  ⟨compactifiedElectricZeroFiberHomeo 1⟩

#print axioms compactifiedMagneticZeroFiberHomeo
#print axioms compactifiedElectricZeroFiberHomeo

/-- The compactified magnetic zero-label representative links once with a
finite nonzero magnetic fiber. -/
example : gaussLinking (cartesianCoordinates ∘ magneticCircleAt 1 0 1)
    (magneticZeroCompactifiedRepresentative 1) = 1 := by
  exact gaussLinking_magnetic_circle_compactified_zero_eq_one 1 0 1 (by norm_num)

/-- The compactified electric zero-label representative links once with a
finite nonzero electric fiber. -/
example : gaussLinking (cartesianCoordinates ∘ electricCircleAt 1 0 1)
    (electricZeroCompactifiedRepresentative 1) = 1 := by
  exact gaussLinking_electric_circle_compactified_zero_eq_one 1 0 1 (by norm_num)

#print axioms magnetic_zero_compactified_circle_bridge
#print axioms electric_zero_compactified_circle_bridge
#print axioms gaussLinking_magnetic_circle_compactified_zero_eq_one
#print axioms gaussLinking_electric_circle_compactified_zero_eq_one

/-- On a nonzero slice the smooth spatial covector has the actual magnetic
curl, and its whole-space pairing is the positive normalized helicity. -/
example :
    (∀ x, spatialCovectorCurl (ranadaMagneticCovector 1) x = ranadaMagneticVector 1 x) ∧
    Integrable (ranadaMagneticHelicityDensity 1) ∧
    (∫ x : ℝ × ℝ × ℝ, ranadaMagneticHelicityDensity 1 x) = 1 / 4 :=
  ⟨spatialCovectorCurl_ranadaMagnetic 1, integrable_and_integral_ranadaMagneticHelicityDensity 1⟩

#print axioms spatialCovectorCurl_ranadaMagnetic
#print axioms integrable_and_integral_ranadaMagneticHelicityDensity

/-- At negative time the rotated electric gauge has the actual electric curl
and the same positive whole-space helicity. -/
example :
    (∀ x, spatialCovectorCurl (ranadaElectricCovector (-2)) x = ranadaElectricVector (-2) x) ∧
    Integrable (ranadaElectricHelicityDensity (-2)) ∧
    (∫ x : ℝ × ℝ × ℝ, ranadaElectricHelicityDensity (-2) x) = 1 / 4 :=
  ⟨spatialCovectorCurl_ranadaElectric (-2),
    integrable_and_integral_ranadaElectricHelicityDensity (-2)⟩

#print axioms spatialCovectorCurl_ranadaElectric
#print axioms integrable_and_integral_ranadaElectricHelicityDensity

/-! Regression consumers for the CK curl eigenstates and the Hopf pulse spectrum. -/

open Qatlib.Papers.KnottedLight08.CurlEigenstate

/-- The dipole mode and its curl are related by the first curl identity away
from the center. -/
example (k : ℝ) (s : Spacetime) (hr : ckRadius s.1 s.2.1 s.2.2.1 ≠ 0) :
    cartesianCurl (ckMultipoleField k) s = ckCurlMultipoleField k s :=
  cartesianCurl_ckMultipoleField k s hr

/-- The second curl restores `k²` times the dipole mode, the Helmholtz
identity behind the eigenstate structure. -/
example (k : ℝ) (s : Spacetime) (hr : ckRadius s.1 s.2.1 s.2.2.1 ≠ 0) :
    cartesianCurl (ckCurlMultipoleField k) s
      = fun j => ((k ^ 2 : ℝ) : ℂ) * ckMultipoleField k s j :=
  cartesianCurl_ckCurlMultipoleField k s hr

/-- The TM mode is `i/k` times the curl of the TE mode. -/
example (k : ℝ) (hk : k ≠ 0) (s : Spacetime)
    (hr : ckRadius s.1 s.2.1 s.2.2.1 ≠ 0) (j : Fin 3) :
    ckTMMode k s j = Complex.I / (k : ℂ) * cartesianCurl (ckTEMode k) s j :=
  ckTMMode_eq_scaled_curl_ckTEMode k hk s hr j

/-- The positive relative phase has curl eigenvalue `-3` at wavenumber `3`. -/
example (s : Spacetime) (hr : ckRadius s.1 s.2.1 s.2.2.1 ≠ 0) :
    cartesianCurl (fun s' j => ckTEMode 3 s' j + Complex.I * ckTMMode 3 s' j) s
      = fun j => -(3 : ℂ) * (ckTEMode 3 s j + Complex.I * ckTMMode 3 s j) :=
  cartesianCurl_eigenCombinationPlus 3 (by norm_num) s hr

/-- The negative relative phase gives curl eigenvalue `k` at any nonzero wavenumber. -/
example (k : ℝ) (hk : k ≠ 0) (s : Spacetime)
    (hr : ckRadius s.1 s.2.1 s.2.2.1 ≠ 0) :
    cartesianCurl (fun s' j => ckTEMode k s' j - Complex.I * ckTMMode k s' j) s
      = fun j => (k : ℂ) * (ckTEMode k s j - Complex.I * ckTMMode k s j) :=
  cartesianCurl_eigenCombinationMinus k hk s hr

/-- The Beltrami field is force-free: it is parallel to its own curl. -/
example (k : ℝ) (s : Spacetime) (hr : ckRadius s.1 s.2.1 s.2.2.1 ≠ 0) :
    cross3 (ckBeltramiPlus k s) (cartesianCurl (ckBeltramiPlus k) s) = 0 :=
  forceFree_ckBeltramiPlus k s hr

/-- The dipole mode is nonzero at `(0, 0, π/2)`. -/
example : ckMultipoleField 1 (0, 0, Real.pi / 2, 0) 0 ≠ 0 :=
  ckMultipoleField_one_pi_half_ne_zero

/-- At that point the first component has the explicit value `4/π²`. -/
example : ckMultipoleField 1 (0, 0, Real.pi / 2, 0) 0 = (4 : ℂ) / Real.pi ^ 2 := by
  rw [ckMultipoleField_one_pi_half]
  rfl

#print axioms Qatlib.Papers.KnottedLight08.CurlEigenstate.cartesianCurl_ckMultipoleField
#print axioms Qatlib.Papers.KnottedLight08.CurlEigenstate.cartesianCurl_ckCurlMultipoleField
#print axioms Qatlib.Papers.KnottedLight08.CurlEigenstate.cartesianCurl_eigenCombinationPlus
#print axioms Qatlib.Papers.KnottedLight08.CurlEigenstate.cartesianCurl_eigenCombinationMinus
#print axioms Qatlib.Papers.KnottedLight08.CurlEigenstate.forceFree_ckBeltramiPlus

/-- The Laplace–sine transform of the pulse weight at unit radius. -/
example : ∫ k in Set.Ioi 0, Real.exp (-k) * Real.sin (1 * k) = 1 / 2 := by
  rw [integral_exp_mul_sin 1]
  norm_num

/-- Dividing by the radius gives the Lorentzian spectral kernel at `r = 1`. -/
example : (∫ k in Set.Ioi 0, Real.exp (-k) * Real.sin (1 * k)) / 1 = 1 / 2 := by
  rw [hopfSpectralKernel (r := 1) one_ne_zero]
  norm_num

/-- The spectral kernel has no radial zeros. -/
example (r : ℝ) : 1 / (1 + r ^ 2) ≠ 0 := hopfKernel_ne_zero r

/-- The spectral weight `k³ e^{-k}` has total mass `6`. -/
example : ∫ k in Set.Ioi 0, Real.exp (-k) * k ^ 3 = 6 := hopfSpectralWeightIntegral

/-- The transverse second derivative of the Lorentzian kernel in closed form. -/
example (x y z : ℝ) :
    deriv (fun yy => deriv (fun yy' => 1 / (1 + x ^ 2 + yy' ^ 2 + z ^ 2)) yy) y
      + deriv (fun zz => deriv (fun zz' => 1 / (1 + x ^ 2 + y ^ 2 + zz' ^ 2)) zz) z
      = -4 * (1 + x ^ 2 - y ^ 2 - z ^ 2) / (1 + x ^ 2 + y ^ 2 + z ^ 2) ^ 3 :=
  lorentzian_lap_yz x y z

/-- The squared modulus of the magnetic letter pair at `(1, 0, 0, 0)` is one. -/
example : etaSumSq 1 0 0 0 = ((1 : ℝ) : ℂ) := by
  rw [Qatlib.Papers.KnottedLight08.CurlEigenstate.etaSumSq_t_zero]
  norm_num

/-- The `1/(4πi)` prefactor turns the cross product's `2i` into `1/(2π)`. -/
example (c : ℂ) : (1 / (4 * Real.pi * Complex.I)) * (2 * Complex.I * c) = c / (2 * Real.pi) :=
  half_prefactor_cancel c

/-- The `t = 0` magnetic `x`-component equals the transverse second derivative
of the Lorentzian spectral kernel scaled by `1/(2π)`. -/
example (x y z : ℝ) :
    ranadaB x y z 0 0 = ((1 / (2 * Real.pi)
        * (deriv (fun yy => deriv (fun yy' => 1 / (1 + x ^ 2 + yy' ^ 2 + z ^ 2)) yy) y
          + deriv (fun zz => deriv (fun zz' => 1 / (1 + x ^ 2 + y ^ 2 + zz' ^ 2)) zz) z)
        : ℝ) : ℂ) :=
  ranadaB_initial_spectral x y z

/-- The spectral reconstruction reproduces the library's origin value `-2/π`,
cross-checking the direct expansion above. -/
example : ranadaB 0 0 0 0 0 = ((-2 / Real.pi : ℝ) : ℂ) := by
  rw [ranadaB_initial_zero 0 0 0]
  norm_num

#print axioms Qatlib.Papers.KnottedLight08.CurlEigenstate.integral_exp_mul_sin
#print axioms Qatlib.Papers.KnottedLight08.CurlEigenstate.ranadaB_initial_zero
#print axioms Qatlib.Papers.KnottedLight08.CurlEigenstate.ranadaB_initial_spectral

/-- At time one the sinc-regularized integral at the spatial origin is `-i/2`. -/
example :
    (∫ k in Set.Ioi (0 : ℝ), Complex.exp (-(1 + Complex.I) * (k : ℂ)) * (k : ℂ))
      = -(Complex.I / 2) := by
  have h :
      (∫ k in Set.Ioi (0 : ℝ), Complex.exp (-(1 + Complex.I) * (k : ℂ)) * (k : ℂ))
        = 1 / (1 + Complex.I) ^ 2 := by
    simpa only [zero_mul, Real.sinc_zero, mul_one, Complex.ofReal_one, Complex.ofReal_zero,
      show (0 : ℂ) ^ 2 = 0 by norm_num, add_zero] using integral_hopf_time_radial 0 1
  rw [h, show (1 + Complex.I) ^ 2 = 2 * Complex.I from by linear_combination Complex.I_mul_I]
  apply (div_eq_iff (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) Complex.I_ne_zero)).2
  linear_combination Complex.I_mul_I

/-- At a nonzero spatial point and time, the spectral reconstruction gives
an explicit nonzero Rañada field component. -/
private theorem ranadaField_at_sample : ranadaField 1 0 0 1 0 = -(2 * Complex.I) /
      ((Real.pi : ℂ) * (1 + 2 * Complex.I) ^ 2) := by
  let w : ℂ := 1 + 2 * Complex.I
  have hw : w ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    norm_num [w, Complex.add_re, Complex.mul_re] at hr
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hg : (Complex.I * (1 + Complex.I)) ^ 2 = -(2 * Complex.I) := by
    rw [mul_pow, Complex.I_sq]
    linear_combination -Complex.I_mul_I
  rw [ranadaField_eq_hopf_null_secondDerivatives]
  norm_num [second_deriv_hopfKernelNullSection,
    Qatlib.Papers.KnotLight13.TorusFamily.complexDenominator,
    Qatlib.Papers.KnotLight13.TorusFamily.radialAux]
  rw [mul_comm Complex.I (2 : ℂ)]
  change Complex.I / (4 * (Real.pi : ℂ)) *
    (8 * (Complex.I * (1 + Complex.I)) ^ 2 / w ^ 3 - 8 / w ^ 3) =
      -(2 * Complex.I) / ((Real.pi : ℂ) * w ^ 2)
  rw [hg]
  field_simp [hw, hπ]
  dsimp [w]
  ring

#print axioms Qatlib.Papers.KnottedLight08.CurlEigenstate.integral_hopf_time_radial
#print axioms Qatlib.Papers.KnottedLight08.CurlEigenstate.hopfKernelNullSection_zero_eq_integral
#print axioms Qatlib.Papers.KnottedLight08.CurlEigenstate.ranadaField_eq_hopf_null_secondDerivatives

/-- The actual CK superposition at the same nonzero spacetime point
converges absolutely and gives the nonzero field value. -/
example :
    let U := fun k : ℝ => Complex.exp (-(1 + Complex.I) * (k : ℂ)) * hopfDipoleMode k 1 0 0 0
    MeasureTheory.IntegrableOn U (Set.Ioi 0) ∧
      (1 / (2 * (Real.pi : ℂ))) * (∫ k in Set.Ioi (0 : ℝ), U k) =
        -(2 * Complex.I) / ((Real.pi : ℂ) * (1 + 2 * Complex.I) ^ 2) := by
  obtain ⟨hInt, h⟩ := ranadaField_eq_hopf_dipole_superposition 1 0 0 1 0
  simp only [Complex.ofReal_one, mul_one] at hInt h
  exact ⟨hInt, h.symm.trans ranadaField_at_sample⟩

#print axioms Qatlib.Papers.KnottedLight08.CurlEigenstate.hopf_dipole_radial_integrals
#print axioms Qatlib.Papers.KnottedLight08.CurlEigenstate.ranadaField_eq_hopf_dipole_superposition

/-- The published potential's positive-frequency Maxwell multiplier gives
the exact article-normalized Rañada component at a nonzero spacetime point. -/
example :
    (∫ k in Set.Ioi (0 : ℝ), (2 * Complex.I * (k : ℂ)) * hopfArticlePotential k 1 0 0 1 0) =
      (4 * Complex.I) / ((Real.pi : ℂ) * (1 + 2 * Complex.I) ^ 2) := by
  have hr : ckRadius 1 0 0 ≠ 0 := by norm_num [ckRadius]
  rw [(integral_hopfArticleMaxwell hr 1 0).2, ranadaField_at_sample]
  ring

/-- The total angular Fourier weight on the north axis is nonzero. -/
example : (∑ j : Fin 3, (‖hopfMagneticFourierPoly 1 0 0 1 j‖ ^ 2 +
    ‖hopfElectricFourierPoly 1 0 0 1 j‖ ^ 2)) = 4 := by
  calc
    _ = 2 * (1 + (1 : ℝ) ^ 2) := hopfFourier_angular_sq 0 0 1 (by norm_num)
    _ = _ := by norm_num

#print axioms Qatlib.Papers.KnottedLight08.CurlEigenstate.tendsto_ckKernel_div_cube
#print axioms Qatlib.Papers.KnottedLight08.CurlEigenstate.integral_hopfArticleMaxwell
#print axioms Qatlib.Papers.KnottedLight08.CurlEigenstate.hopfFourier_eq_frequencyFactor
#print axioms Qatlib.Papers.KnottedLight08.CurlEigenstate.hopfFourier_angular_sq

/-- The time derivative of the integrated CK potential is the explicit
nonzero Rañada component at the chosen off-axis spacetime point. -/
example : deriv (fun t => hopfPositivePotential 1 0 0 t 0) 1 =
    -(2 * Complex.I) / ((Real.pi : ℂ) * (1 + 2 * Complex.I) ^ 2) := by
  rw [(hasDerivAt_hopfPositivePotential_time 1 0 0 1 0).deriv, ranadaField_at_sample]

/-- The extended mode has a nonzero Cartesian curl at the origin. -/
example : cartesianCurl (fun p => hopfDipoleMode 1 p.1 p.2.1 p.2.2.1) (0, 0, 0, 0) 1 =
    (2 : ℂ) / 3 := by
  rw [cartesianCurl_hopfDipoleMode]
  norm_num [hopfDipoleMode, ckRadius, ckConstantCurl]

/-- The integrated potential retains the curl phase at a nonzero
off-axis point of the actual Hopf field. -/
example : cartesianCurl (fun p => hopfPositivePotential p.1 p.2.1 p.2.2.1 p.2.2.2)
    (1, 0, 0, 1) 0 =
      Complex.I * (-(2 * Complex.I) / ((Real.pi : ℂ) * (1 + 2 * Complex.I) ^ 2)) := by
  rw [cartesianCurl_hopfPositivePotential]
  simp only [ranadaField_at_sample]

open Qatlib.Papers.KnottedLight08.HelicitySpec

/-- A quarter turn sends the exact off-axis first component to the
second component with the azimuthal phase of the Hopf dipole. -/
example : ranadaField 0 1 0 1 1 =
    (2 : ℂ) / ((Real.pi : ℂ) * (1 + 2 * Complex.I) ^ 2) := by
  calc
    _ = Complex.I * ranadaField 1 0 0 1 0 := by
      simpa [vectorQuarterTurn] using ranadaField_quarterTurn 1 0 0 1 1
    _ = _ := by
      rw [ranadaField_at_sample, ← mul_div_assoc]
      congr 1
      linear_combination -2 * Complex.I_mul_I

/-- Opposite nonzero azimuthal coefficients create an oscillation
that changes the modal helicity between two exact times. -/
example : ckSpectralHelicityAt (fun _ => 1) (fun _ => 0) 1 1 0 = 0 ∧
    ckSpectralHelicityAt (fun _ => 1) (fun _ => 0) 1 1 (Real.pi / 2) = 2 := by
  constructor
  · norm_num [ckSpectralHelicityAt, ckSignedModeNorm, ckOppositeModeProduct]
  · have hPhase : -(2 : ℂ) * Complex.I * ((1 : ℝ) : ℂ) * ((Real.pi / 2 : ℝ) : ℂ) =
        -((Real.pi : ℂ) * Complex.I) := by
      push_cast
      ring
    simp only [ckSpectralHelicityAt, hPhase, Complex.exp_neg_pi_mul_I]
    norm_num [ckSignedModeNorm, ckOppositeModeProduct]

#print axioms Qatlib.Papers.KnottedLight08.CurlEigenstate.integrableOn_hopfPotentialDensity
#print axioms Qatlib.Papers.KnottedLight08.CurlEigenstate.deriv_hopfVectorPotential_time
#print axioms Qatlib.Papers.KnottedLight08.CurlEigenstate.continuous_hopfDipoleMode
#print axioms Qatlib.Papers.KnottedLight08.CurlEigenstate.continuous_hopfPositivePotential
#print axioms Qatlib.Papers.KnottedLight08.CurlEigenstate.cartesianCurl_hopfDipoleMode
#print axioms Qatlib.Papers.KnottedLight08.CurlEigenstate.cartesianCurl_hopfVectorPotential
#print axioms Qatlib.Papers.KnottedLight08.CurlEigenstate.cartesianDivergence_hopfDipoleMode
#print axioms Qatlib.Papers.KnottedLight08.CurlEigenstate.cartesianDivergence_hopfVectorPotential
#print axioms Qatlib.Papers.KnottedLight08.HelicitySpec.integrableOn_ckSpectralHelicity
#print axioms Qatlib.Papers.KnottedLight08.HelicitySpec.ckSpectralHelicity_eq_signed_of_unpaired
#print axioms Qatlib.Papers.KnottedLight08.HelicitySpec.integrable_hopf_sameSignPairing
#print axioms Qatlib.Papers.KnottedLight08.HelicitySpec.integral_hopf_sameSignPairing
#print axioms Qatlib.Papers.KnottedLight08.HelicitySpec.integrable_and_integral_hopfVectorPotential_curl
