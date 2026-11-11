/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianCore

/-!
# Gaussian matrices and three-dimensional projections

The laws `matrixLaw` and `rawMatrixLaw` represent three independent Gaussian rows in Euclidean
and scalar coordinates. The projection maps `project` and `rawProject` send a fixed unit input
to a standard three-dimensional Gaussian vector, giving almost-sure normalization and integrable
rounded correlations. See [CrostaSaubanereHuber2026].

## Main statements

* `row_projection_covariance`: identifies covariance of row projections with the input inner
  product.
* `rawProject_unit_law`: gives the standard Gaussian law of a projected unit vector.
* `rawProject_normalized_unit`: establishes almost-sure unit norm after normalization.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory

namespace Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianMatrix
open Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianPair

/-- The real Euclidean space indexed by `I`. -/
abbrev Row (I : Type) := EuclideanSpace ℝ I

/-- A collection of three Euclidean rows indexed by `I`. -/
abbrev Rows (I : Type) := Fin 3 → Row I

/-- The law of three independent standard Gaussian Euclidean rows. -/
abbrev matrixLaw (I : Type) [Fintype I] : Measure (Rows I) :=
  Measure.pi (fun _ : Fin 3 => stdGaussian (Row I))

/-- The law of a three-row matrix whose scalar entries are independent standard real Gaussians. -/
abbrev rawMatrixLaw (I : Type) [Fintype I] : Measure (Fin 3 → I → ℝ) :=
  Measure.pi (fun _ : Fin 3 => Measure.pi (fun _ : I => gaussianReal 0 1))

/-- The conversion of each scalar row to its Euclidean-space representation. -/
def toRows {I : Type} (R : Fin 3 → I → ℝ) : Rows I := fun r => WithLp.toLp 2 (R r)

/-- Converting scalar Gaussian rows to Euclidean rows transports `rawMatrixLaw` to `matrixLaw`. -/
theorem raw_to_rows_preserving {I : Type} [Fintype I] :
    MeasurePreserving (toRows (I:=I)) (rawMatrixLaw I) (matrixLaw I) := by
  exact measurePreserving_pi _ _ (fun _ : Fin 3 =>
    (⟨by fun_prop,map_pi_eq_stdGaussian⟩ : MeasurePreserving (WithLp.toLp 2)
      (Measure.pi (fun _ : I => gaussianReal 0 1)) (stdGaussian (Row I))))

/-- The inner product of a fixed unit vector with a standard Gaussian row has the standard real
Gaussian law. -/
theorem row_unit_projection {I : Type} [Fintype I] (u : Row I) (hu : ‖u‖=1) :
    MeasurePreserving (fun x : Row I => inner ℝ u x) (stdGaussian (Row I)) (gaussianReal 0 1) := by
  refine ⟨by fun_prop,?_⟩
  change (stdGaussian (Row I)).map (innerSL ℝ u)=_
  rw [IsGaussian.map_eq_gaussianReal,integral_strongDual_stdGaussian,variance_dual_stdGaussian,innerSL_apply_norm,hu]
  norm_num

/-- The three-dimensional vector of inner products of `u` with the matrix rows. -/
def project {I : Type} [Fintype I] (u : Row I) (R : Rows I) : V :=
  WithLp.toLp 2 (fun r : Fin 3 => inner ℝ u (R r))

/-- The matrix projection of a fixed input vector is measurable. -/
theorem project_measurable {I : Type} [Fintype I] (u : Row I) : Measurable (project u) := by
  unfold project
  fun_prop

/-- The projection of a unit vector under `matrixLaw` has the standard three-dimensional
Gaussian law. -/
theorem project_unit_law {I : Type} [Fintype I] (u : Row I) (hu : ‖u‖=1) :
    MeasurePreserving (project u) (matrixLaw I) gamma := by
  have hp := measurePreserving_pi (fun _ : Fin 3 => stdGaussian (Row I))
    (fun _ : Fin 3 => gaussianReal 0 1) (fun _ => row_unit_projection u hu)
  have ht : MeasurePreserving (WithLp.toLp 2 : (Fin 3 → ℝ) → V)
      (Measure.pi (fun _ : Fin 3 => gaussianReal 0 1)) gamma := ⟨by fun_prop,gamma_from_iid⟩
  exact ht.comp hp

/-- The Gaussian matrix projection of a unit vector is nonzero almost surely. -/
theorem project_unit_ne_zero {I : Type} [Fintype I] (u : Row I) (hu : ‖u‖=1) :
    ∀ᵐ R ∂matrixLaw I,project u R≠0 :=
  (project_unit_law u hu).quasiMeasurePreserving.ae (gamma_ae_ne 0)

/-- The normalized Gaussian matrix projection of a unit vector has norm one almost surely. -/
theorem project_normalized_unit {I : Type} [Fintype I] (u : Row I) (hu : ‖u‖=1) :
    ∀ᵐ R ∂matrixLaw I,‖unitVector (project u R)‖=1 := by
  filter_upwards [project_unit_ne_zero u hu] with R hR
  exact norm_unitVector _ hR

/-- The covariance of two projections of a standard Gaussian row equals the inner product of
their input vectors. -/
theorem row_projection_covariance {I : Type} [Fintype I] (u v : Row I) :
    cov[fun x : Row I => inner ℝ u x,fun x : Row I => inner ℝ v x;stdGaussian (Row I)]=inner ℝ u v := by
  rw [← covarianceBilin_apply_eq_cov (IsGaussian.memLp_two_id (μ:=stdGaussian (Row I))) u v,covarianceBilin_stdGaussian]
  rfl

/-- Each coordinate of `project u R` is the sum of the row entries multiplied by the coordinates
of `u`. -/
theorem project_apply {I : Type} [Fintype I] (u : Row I) (R : Rows I) (r : Fin 3) :
    project u R r=∑ i : I,R r i*u i := by
  simp [project,PiLp.inner_apply,mul_comm]

/-- The normalized projected inner product of two fixed vectors is integrable under the Gaussian
matrix law. -/
theorem projected_correlation_integrable {I : Type} [Fintype I] (u v : Row I) :
    Integrable (fun R : Rows I => inner ℝ (unitVector (project u R)) (unitVector (project v R))) (matrixLaw I) := by
  have hm : Measurable (fun R : Rows I => inner ℝ (unitVector (project u R)) (unitVector (project v R))) :=
    (unitVector_measurable.comp (project_measurable u)).inner (unitVector_measurable.comp (project_measurable v))
  exact (integrable_const (1:ℝ)).mono' hm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun R => unit_inner_bound (project u R) (project v R)))

/-- The three-dimensional matrix-vector product in scalar row coordinates. -/
def rawProject {I : Type} [Fintype I] (u : Row I) (R : Fin 3 → I → ℝ) : V :=
  WithLp.toLp 2 (fun r => ∑ i : I,R r i*u i)

/-- Projecting after converting scalar rows to Euclidean rows equals `rawProject`. -/
theorem rawProject_eq {I : Type} [Fintype I] (u : Row I) (R : Fin 3 → I → ℝ) :
    project u (toRows R)=rawProject u R := by
  apply (WithLp.equiv 2 (Fin 3 → ℝ)).injective
  funext r
  exact project_apply u (toRows R) r

/-- The raw Gaussian matrix projection of a unit vector has the standard three-dimensional
Gaussian law. -/
theorem rawProject_unit_law {I : Type} [Fintype I] (u : Row I) (hu : ‖u‖=1) :
    MeasurePreserving (rawProject u) (rawMatrixLaw I) gamma := by
  have h := (project_unit_law u hu).comp (raw_to_rows_preserving (I:=I))
  have he : (project u ∘ toRows (I:=I))=rawProject u := funext (rawProject_eq u)
  rwa [he] at h

/-- The normalized raw Gaussian matrix projection of a unit vector has norm one almost surely. -/
theorem rawProject_normalized_unit {I : Type} [Fintype I] (u : Row I) (hu : ‖u‖=1) :
    ∀ᵐ R ∂rawMatrixLaw I,‖unitVector (rawProject u R)‖=1 := by
  filter_upwards [(rawProject_unit_law u hu).quasiMeasurePreserving.ae (gamma_ae_ne 0)] with R hR
  exact norm_unitVector _ hR

end Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianMatrix
