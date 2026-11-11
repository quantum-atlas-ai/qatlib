/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianMatrix
import Qatlib.Papers.RydbergMaxCut26.Rounding.PhysicalRounding

/-!
# Gaussian laws for physical fit vectors

The map `physicalFitEuclidean` packages the physical Gram construction as unit Euclidean
vectors. Its Gaussian projections agree coordinatewise with `physicalRound`, yielding measurable
rounded vectors, almost-sure unit norm at every site, and integrable pairwise dot products. See
[CrostaSaubanereHuber2026].

## Main statements

* `physicalProjection_law`: identifies each physical projection with the standard Gaussian law.
* `physicalRound_unit_ae`: establishes unit squared norm simultaneously at all sites almost
  surely.
* `physical_dot_integrable`: proves integrability of rounded pairwise dot products.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open scoped Classical ComplexOrder
open MeasureTheory ProbabilityTheory Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Bloch Qatlib.Papers.RydbergMaxCut26.MomentSdp.Gram
open Qatlib.Papers.RydbergMaxCut26.Rounding.Projection
open Qatlib.Papers.RydbergMaxCut26.Rounding.Physical

namespace Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianPhysical
open Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianPair
open Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianMatrix

/-- The Euclidean normalization `unitVector` agrees coordinatewise with `Projection.normalize`. -/
theorem unitVector_coordinates (x : V) (a : Fin 3) :
    unitVector x a=Qatlib.Papers.RydbergMaxCut26.Rounding.Projection.normalize (fun b => x b) a := by
  change ‖x‖⁻¹*x a=x a/Real.sqrt (∑ b : Fin 3,x b^2)
  rw [EuclideanSpace.norm_eq]
  simp only [Real.norm_eq_abs,sq_abs]
  rw [div_eq_mul_inv,mul_comm]

/-- The coordinate squared norm of a Euclidean vector equals the square of its Euclidean norm. -/
theorem physical_sqnorm_coordinates (x : V) : sqnorm (fun a => x a)=‖x‖^2 :=
  (EuclideanSpace.real_norm_sq_eq x).symm

/-- The Euclidean-space representation of the physical fit vector associated with a site of a
density matrix. -/
def physicalFitEuclidean (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1) (i : Fin n) :
    Row (Fin 2 × MomentIndex n) := WithLp.toLp 2 (physicalFit n ρ hρ htr i)

/-- Every Euclidean physical fit vector has norm one. -/
theorem physicalFitEuclidean_unit (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1) (i : Fin n) :
    ‖physicalFitEuclidean n ρ hρ htr i‖=1 := by
  have h : ‖physicalFitEuclidean n ρ hρ htr i‖^2=1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact physical_fit_unit n ρ hρ htr i
  nlinarith [norm_nonneg (physicalFitEuclidean n ρ hρ htr i)]

/-- The physically rounded vector at a site consists of the coordinates of its normalized raw
Gaussian projection. -/
theorem physicalRound_coordinates (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1)
    (R : Fin 3 → Fin 2 × MomentIndex n → ℝ) (i : Fin n) :
    physicalRound n ρ hρ htr R i=fun a => unitVector (rawProject (physicalFitEuclidean n ρ hρ htr i) R) a := by
  funext a
  have h := unitVector_coordinates (rawProject (physicalFitEuclidean n ρ hρ htr i) R) a
  simpa only [physicalRound,roundVector,physicalFit,physicalFitEuclidean,rawProject] using! h.symm

/-- The raw Gaussian projection of a physical fit vector has the standard three-dimensional
Gaussian law. -/
theorem physicalProjection_law (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1) (i : Fin n) :
    MeasurePreserving (rawProject (physicalFitEuclidean n ρ hρ htr i)) (rawMatrixLaw (Fin 2 × MomentIndex n)) gamma :=
  rawProject_unit_law _ (physicalFitEuclidean_unit n ρ hρ htr i)

/-- The raw Gaussian projection of each physical fit vector is nonzero almost surely. -/
theorem physicalProjection_ne_zero (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1) (i : Fin n) :
    ∀ᵐ R ∂rawMatrixLaw (Fin 2 × MomentIndex n),rawProject (physicalFitEuclidean n ρ hρ htr i) R≠0 :=
  (physicalProjection_law n ρ hρ htr i).quasiMeasurePreserving.ae (gamma_ae_ne 0)

/-- Almost surely under the raw Gaussian matrix law, all physically rounded site vectors have
squared norm one. -/
theorem physicalRound_unit_ae (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    ∀ᵐ R ∂rawMatrixLaw (Fin 2 × MomentIndex n),∀ i : Fin n,sqnorm (physicalRound n ρ hρ htr R i)=1 := by
  apply ae_all_iff.mpr
  intro i
  filter_upwards [physicalProjection_ne_zero n ρ hρ htr i] with R hR
  rw [physicalRound_coordinates,physical_sqnorm_coordinates,norm_unitVector _ hR]
  norm_num

/-- The coordinate dot product of two physically rounded vectors equals the Euclidean inner
product of their normalized raw projections. -/
theorem physical_dot_eq (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1)
    (i j : Fin n) (R : Fin 3 → Fin 2 × MomentIndex n → ℝ) :
    (∑ a : Fin 3,physicalRound n ρ hρ htr R i a*physicalRound n ρ hρ htr R j a)=
      inner ℝ (unitVector (rawProject (physicalFitEuclidean n ρ hρ htr i) R))
        (unitVector (rawProject (physicalFitEuclidean n ρ hρ htr j) R)) := by
  rw [physicalRound_coordinates,physicalRound_coordinates]
  simp [PiLp.inner_apply,mul_comm]

/-- The physically rounded vector at each site is a measurable function of the raw Gaussian
matrix. -/
theorem physicalRound_measurable (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1) (i : Fin n) :
    Measurable (fun R : Fin 3 → Fin 2 × MomentIndex n → ℝ => physicalRound n ρ hρ htr R i) := by
  have h : Measurable (fun R : Fin 3 → Fin 2 × MomentIndex n → ℝ => unitVector (rawProject (physicalFitEuclidean n ρ hρ htr i) R)) :=
    unitVector_measurable.comp (physicalProjection_law n ρ hρ htr i).measurable
  apply measurable_pi_iff.mpr
  intro a
  have ha : Measurable (fun v : V => v a) := by fun_prop
  simpa only [physicalRound_coordinates] using! ha.comp h

/-- The dot product of two physically rounded site vectors is integrable under the raw Gaussian
matrix law. -/
theorem physical_dot_integrable (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1) (i j : Fin n) :
    Integrable (fun R : Fin 3 → Fin 2 × MomentIndex n → ℝ =>
      ∑ a : Fin 3,physicalRound n ρ hρ htr R i a*physicalRound n ρ hρ htr R j a) (rawMatrixLaw (Fin 2 × MomentIndex n)) := by
  have hm : Measurable (fun R : Fin 3 → Fin 2 × MomentIndex n → ℝ =>
      inner ℝ (unitVector (rawProject (physicalFitEuclidean n ρ hρ htr i) R))
        (unitVector (rawProject (physicalFitEuclidean n ρ hρ htr j) R))) :=
    (unitVector_measurable.comp (physicalProjection_law n ρ hρ htr i).measurable).inner
      (unitVector_measurable.comp (physicalProjection_law n ρ hρ htr j).measurable)
  have hi : Integrable (fun R : Fin 3 → Fin 2 × MomentIndex n → ℝ =>
      inner ℝ (unitVector (rawProject (physicalFitEuclidean n ρ hρ htr i) R))
        (unitVector (rawProject (physicalFitEuclidean n ρ hρ htr j) R))) (rawMatrixLaw (Fin 2 × MomentIndex n)) :=
    (integrable_const (1:ℝ)).mono' hm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun R => unit_inner_bound _ _))
  exact hi.congr (Filter.Eventually.of_forall (fun R => (physical_dot_eq n ρ hρ htr i j R).symm))

end Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianPhysical
