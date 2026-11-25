/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.CurlEigenstate.HopfPotentialCurl
public import Qatlib.Papers.KnottedLight08.CurlEigenstate.CKRegularMode

import Qatlib.Papers.KnottedLight08.CurlEigenstate.HopfModeBound
import Qatlib.Papers.KnottedLight08.CurlEigenstate.HopfPotentialSpace
import Qatlib.Papers.KnottedLight08.HopfField.RanadaEnergy
import Qatlib.Papers.KnottedLight08.HopfField.RanadaHelicity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Azimuthal symmetry of the actual Hopf pulse

A quarter turn about the third axis multiplies the positive-frequency
dipole by its azimuthal phase and rotates its vector components.
This gives the same symmetry for the reconstructed vector potential
and Rañada field.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.HelicitySpec

open MeasureTheory Set
open Qatlib.Papers.KnottedLight08.CurlEigenstate
open Qatlib.Papers.KnottedLight08.HopfField
open Qatlib.Papers.KnotLight13.TorusFamily (cartesianCurl)
open scoped BigOperators ComplexConjugate

/-- The Cartesian action of a positive quarter turn about the third axis. -/
def vectorQuarterTurn (v : Fin 3 → ℂ) : Fin 3 → ℂ := ![-v 1, v 0, v 2]

/-- The actual regular CK dipole acquires phase `i` under a positive
spatial quarter turn, including at the origin. -/
theorem hopfDipoleMode_quarterTurn (k x y z : ℝ) (j : Fin 3) :
    hopfDipoleMode k (-y) x z j =
      Complex.I * vectorQuarterTurn (hopfDipoleMode k x y z) j := by
  have hr : ckRadius (-y) x z = ckRadius x y z := by
    unfold ckRadius
    congr 1
    ring
  have hA (l : Fin 3) : ckAngular (-y) x z l =
      Complex.I * vectorQuarterTurn (ckAngular x y z) l := by
    fin_cases l <;> simp [ckAngular, vectorQuarterTurn] <;>
      ring_nf <;> simp [Complex.I_sq]
  have hB (l : Fin 3) : ckCurlAngular (-y) x z l =
      Complex.I * vectorQuarterTurn (ckCurlAngular x y z) l := by
    fin_cases l <;> simp [ckCurlAngular, vectorQuarterTurn] <;>
      ring_nf <;> simp [Complex.I_sq]
    rw [sub_eq_add_neg]
  have hC (l : Fin 3) : ckConstantCurl l =
      Complex.I * vectorQuarterTurn ckConstantCurl l := by
    fin_cases l <;> simp [ckConstantCurl, vectorQuarterTurn] <;>
      ring_nf
    simp [Complex.I_sq]
  rw [hopfDipoleMode_eq_regular, hr, hA, hB, hC]
  fin_cases j <;> simp [vectorQuarterTurn, hopfDipoleMode_eq_regular] <;> ring

/-- The positive-frequency vector potential inherits the exact
azimuthal phase of the dipole modes under spatial rotation. -/
theorem hopfPositivePotential_quarterTurn (x y z t : ℝ) (j : Fin 3) :
    hopfPositivePotential (-y) x z t j =
      Complex.I * vectorQuarterTurn (hopfPositivePotential x y z t) j := by
  have h (k : ℝ) : hopfPotentialDensity (-y) x z t j k =
      Complex.I * vectorQuarterTurn (fun l => hopfPotentialDensity x y z t l k) j := by
    rw [hopfPotentialDensity, hopfDipoleMode_quarterTurn]
    fin_cases j <;> simp [vectorQuarterTurn, hopfPotentialDensity] <;> ring
  rw [hopfPositivePotential, setIntegral_congr_fun measurableSet_Ioi (fun k _ => h k),
    integral_const_mul]
  fin_cases j <;> simp [vectorQuarterTurn, hopfPositivePotential, integral_neg]

/-- The Rañada complex field has the same azimuthal character
through the convergent positive-frequency dipole reconstruction. -/
theorem ranadaField_quarterTurn (x y z t : ℝ) (j : Fin 3) :
    ranadaField (-y) x z t j = Complex.I * vectorQuarterTurn (ranadaField x y z t) j := by
  let E := fun k : ℝ => Complex.exp (-(1 + Complex.I * (t : ℂ)) * (k : ℂ))
  let c := (1 : ℂ) / (2 * (Real.pi : ℂ))
  have hleft : ranadaField (-y) x z t j =
      c * ∫ k in Ioi (0 : ℝ), E k * hopfDipoleMode k (-y) x z j :=
    (ranadaField_eq_hopf_dipole_superposition (-y) x z t j).2
  have hright (l : Fin 3) : ranadaField x y z t l =
      c * ∫ k in Ioi (0 : ℝ), E k * hopfDipoleMode k x y z l :=
    (ranadaField_eq_hopf_dipole_superposition x y z t l).2
  have h (k : ℝ) : E k * hopfDipoleMode k (-y) x z j =
      Complex.I * vectorQuarterTurn (fun l => E k * hopfDipoleMode k x y z l) j := by
    rw [hopfDipoleMode_quarterTurn]
    fin_cases j <;> simp [vectorQuarterTurn] <;> ring
  rw [hleft, setIntegral_congr_fun measurableSet_Ioi (fun k _ => h k), integral_const_mul]
  fin_cases j <;> simp [vectorQuarterTurn, hright, integral_neg] <;> ring

/-- The same-sign azimuthal pairing of the actual positive-frequency
potential and field changes sign under a quarter turn. -/
theorem hopf_sameSignPairing_quarterTurn (x y z t : ℝ) :
    (∑ j : Fin 3, hopfPositivePotential (-y) x z t j * ranadaField (-y) x z t j) =
      -(∑ j : Fin 3, hopfPositivePotential x y z t j * ranadaField x y z t j) := by
  simp_rw [hopfPositivePotential_quarterTurn, ranadaField_quarterTurn]
  simp [Fin.sum_univ_three, vectorQuarterTurn]
  ring_nf
  simp [Complex.I_sq]
  ring

/-- The spatial quarter turn used for integration in Cartesian coordinates. -/
private def spatialQuarterTurn : (ℝ × ℝ × ℝ) ≃ᵐ (ℝ × ℝ × ℝ) where
  toFun p := (-p.2.1, p.1, p.2.2)
  invFun p := (p.2.1, -p.1, p.2.2)
  left_inv p := by simp
  right_inv p := by simp
  measurable_toFun := by
    change Measurable (fun p : ℝ × ℝ × ℝ => (-p.2.1, p.1, p.2.2))
    fun_prop
  measurable_invFun := by
    change Measurable (fun p : ℝ × ℝ × ℝ => (p.2.1, -p.1, p.2.2))
    fun_prop

/-- The spatial quarter turn preserves the ordinary Cartesian volume. -/
private theorem measurePreserving_spatialQuarterTurn :
    MeasurePreserving spatialQuarterTurn volume volume := by
  have hneg : MeasurePreserving (fun r : ℝ => -r) volume volume :=
    Measure.measurePreserving_neg volume
  have hswap : MeasurePreserving (@Prod.swap ℝ ℝ) volume volume := Measure.measurePreserving_swap
  have hplane := (hneg.prod (MeasurePreserving.id (volume : Measure ℝ))).comp hswap
  have hflat := hplane.prod (MeasurePreserving.id (volume : Measure ℝ))
  have hassoc : MeasurePreserving (MeasurableEquiv.prodAssoc : (ℝ × ℝ) × ℝ ≃ᵐ ℝ × ℝ × ℝ)
      volume volume := volume_preserving_prodAssoc
  exact (hassoc.comp hflat).comp (MeasurePreserving.symm _ hassoc)

/-- Azimuthal symmetry cancels the same-sign pairing of the actual
Hopf potential and field in the Cartesian spatial integral. -/
theorem integral_hopf_sameSignPairing (t : ℝ) :
    (∫ p : ℝ × ℝ × ℝ, ∑ j : Fin 3,
      hopfPositivePotential p.1 p.2.1 p.2.2 t j * ranadaField p.1 p.2.1 p.2.2 t j) = 0 := by
  let P := fun p : ℝ × ℝ × ℝ => ∑ j : Fin 3,
    hopfPositivePotential p.1 p.2.1 p.2.2 t j * ranadaField p.1 p.2.1 p.2.2 t j
  have hP (p : ℝ × ℝ × ℝ) : P (spatialQuarterTurn p) = -P p :=
    hopf_sameSignPairing_quarterTurn p.1 p.2.1 p.2.2 t
  have h := measurePreserving_spatialQuarterTurn.integral_comp' P
  simp_rw [hP, integral_neg] at h
  change (∫ p, P p) = 0
  linear_combination -(1 / 2 : ℂ) * h

/-- A bounded Hopf potential component multiplies an integrable
component to an integrable product on Cartesian space. -/
private theorem integrable_hopfPotential_mul (t : ℝ) (j : Fin 3)
    (G : (ℝ × ℝ × ℝ) → ℂ) (hG : Integrable G) :
    Integrable (fun p : ℝ × ℝ × ℝ => hopfPositivePotential p.1 p.2.1 p.2.2 t j * G p) := by
  obtain ⟨C, hC⟩ := exists_hopfPositivePotential_bound
  have hp : Continuous (fun p : ℝ × ℝ × ℝ => (p.1, p.2.1, p.2.2, t)) := by fun_prop
  have hA : AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => hopfPositivePotential p.1 p.2.1 p.2.2 t j) volume := by
    simpa only [Function.comp_def] using
      ((continuous_hopfPositivePotential j).comp hp).aestronglyMeasurable (μ := volume)
  refine (hG.norm.const_mul C).mono' (hA.mul hG.aestronglyMeasurable) ?_
  filter_upwards with p
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hC p.1 p.2.1 p.2.2 t j) (norm_nonneg _)

/-- Absolute integrability transfers to the Cartesian product
coordinates through the volume-preserving coordinate map. -/
private theorem integrable_cartesian_ranadaField (t : ℝ) (j : Fin 3) :
    Integrable (fun p : ℝ × ℝ × ℝ => ranadaField p.1 p.2.1 p.2.2 t j) := by
  convert measurePreserving_spatialEuclidean.integrable_comp_of_integrable
    (integrable_ranada_field t j) using 1
  funext p
  rcases p with ⟨x, y, z⟩
  rfl

/-- Absolute integrability of the same-sign pairing of the actual Hopf fields. -/
theorem integrable_hopf_sameSignPairing (t : ℝ) :
    Integrable (fun p : ℝ × ℝ × ℝ => ∑ j : Fin 3,
      hopfPositivePotential p.1 p.2.1 p.2.2 t j * ranadaField p.1 p.2.1 p.2.2 t j) := by
  exact integrable_finsetSum _ fun j _ =>
    integrable_hopfPotential_mul t j _ (integrable_cartesian_ranadaField t j)

/-- Absolute integrability of the opposite-sign pairing of the actual Hopf fields. -/
theorem integrable_hopf_mixedPairing (t : ℝ) :
    Integrable (fun p : ℝ × ℝ × ℝ => ∑ j : Fin 3,
      hopfPositivePotential p.1 p.2.1 p.2.2 t j * conj (ranadaField p.1 p.2.1 p.2.2 t j)) := by
  exact integrable_finsetSum _ fun j _ => integrable_hopfPotential_mul t j _
    (Complex.conjCLE.toContinuousLinearMap.integrable_comp (integrable_cartesian_ranadaField t j))

/-- The dot product of the article's real Coulomb potential and its curl. -/
noncomputable def hopfSpatialHelicityDensity (t : ℝ) (p : ℝ × ℝ × ℝ) : ℝ :=
  ∑ j : Fin 3, hopfVectorPotential p.1 p.2.1 p.2.2 t j *
    (cartesianCurl (fun s l => (hopfVectorPotential s.1 s.2.1 s.2.2.1 s.2.2.2 l : ℂ))
      (p.1, p.2.1, p.2.2, t) j).re

/-- The spatial helicity density in the article's Coulomb gauge is absolutely
integrable. Its integral is twice the imaginary part of the integrated
opposite-sign pairing of the actual complex fields. -/
theorem integrable_and_integral_hopfVectorPotential_curl (t : ℝ) :
    Integrable (hopfSpatialHelicityDensity t) ∧
      (∫ p, hopfSpatialHelicityDensity t p) =
        2 * (∫ p : ℝ × ℝ × ℝ, ∑ j : Fin 3,
          hopfPositivePotential p.1 p.2.1 p.2.2 t j *
            conj (ranadaField p.1 p.2.1 p.2.2 t j)).im := by
  let M := fun p : ℝ × ℝ × ℝ => ∑ j : Fin 3,
    hopfPositivePotential p.1 p.2.1 p.2.2 t j * conj (ranadaField p.1 p.2.1 p.2.2 t j)
  let P := fun p : ℝ × ℝ × ℝ => ∑ j : Fin 3,
    hopfPositivePotential p.1 p.2.1 p.2.2 t j * ranadaField p.1 p.2.1 p.2.2 t j
  have hM : Integrable M := integrable_hopf_mixedPairing t
  have hP : Integrable P := integrable_hopf_sameSignPairing t
  have hparts (p : ℝ × ℝ × ℝ) : hopfSpatialHelicityDensity t p = 2 * ((M p).im - (P p).im) := by
    unfold hopfSpatialHelicityDensity
    simp_rw [cartesianCurl_hopfVectorPotential, Complex.ofReal_re]
    simp only [M, P, hopfVectorPotential, Fin.sum_univ_three, Complex.add_im, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, ranadaField, Complex.I_re, Complex.I_im, ranadaE_im,
      zero_mul, one_mul, zero_add]
    ring
  have hMi : Integrable (fun p => (M p).im) := Complex.imCLM.integrable_comp hM
  have hPi : Integrable (fun p => (P p).im) := Complex.imCLM.integrable_comp hP
  refine ⟨((hMi.sub hPi).const_mul (2 : ℝ)).congr
    (Filter.Eventually.of_forall fun p => (hparts p).symm), ?_⟩
  simp_rw [hparts]
  change (∫ p, 2 * ((M p).im - (P p).im)) = 2 * (∫ p, M p).im
  rw [integral_const_mul, integral_sub hMi hPi]
  change 2 * ((∫ p, RCLike.im (M p)) - ∫ p, RCLike.im (P p)) = _
  rw [integral_im hM, integral_im hP]
  have hzero : (∫ p, P p) = 0 := integral_hopf_sameSignPairing t
  simp [hzero]

end Qatlib.Papers.KnottedLight08.HelicitySpec
