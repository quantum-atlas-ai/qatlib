/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianCore
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory

namespace Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianMatrix
open Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianPair

abbrev Row (I : Type) := EuclideanSpace ℝ I

abbrev Rows (I : Type) := Fin 3 → Row I

abbrev matrixLaw (I : Type) [Fintype I] : Measure (Rows I) :=
  Measure.pi (fun _ : Fin 3 => stdGaussian (Row I))

abbrev rawMatrixLaw (I : Type) [Fintype I] : Measure (Fin 3 → I → ℝ) :=
  Measure.pi (fun _ : Fin 3 => Measure.pi (fun _ : I => gaussianReal 0 1))

def toRows {I : Type} (R : Fin 3 → I → ℝ) : Rows I := fun r => WithLp.toLp 2 (R r)

theorem raw_to_rows_preserving {I : Type} [Fintype I] :
    MeasurePreserving (toRows (I:=I)) (rawMatrixLaw I) (matrixLaw I) := by
  exact measurePreserving_pi _ _ (fun _ : Fin 3 =>
    (⟨by fun_prop,map_pi_eq_stdGaussian⟩ : MeasurePreserving (WithLp.toLp 2)
      (Measure.pi (fun _ : I => gaussianReal 0 1)) (stdGaussian (Row I))))

theorem row_unit_projection {I : Type} [Fintype I] (u : Row I) (hu : ‖u‖=1) :
    MeasurePreserving (fun x : Row I => inner ℝ u x) (stdGaussian (Row I)) (gaussianReal 0 1) := by
  refine ⟨by fun_prop,?_⟩
  change (stdGaussian (Row I)).map (innerSL ℝ u)=_
  rw [IsGaussian.map_eq_gaussianReal,integral_strongDual_stdGaussian,variance_dual_stdGaussian,innerSL_apply_norm,hu]
  norm_num

def project {I : Type} [Fintype I] (u : Row I) (R : Rows I) : V :=
  WithLp.toLp 2 (fun r : Fin 3 => inner ℝ u (R r))

theorem project_measurable {I : Type} [Fintype I] (u : Row I) : Measurable (project u) := by
  unfold project
  fun_prop

theorem project_unit_law {I : Type} [Fintype I] (u : Row I) (hu : ‖u‖=1) :
    MeasurePreserving (project u) (matrixLaw I) gamma := by
  have hp := measurePreserving_pi (fun _ : Fin 3 => stdGaussian (Row I))
    (fun _ : Fin 3 => gaussianReal 0 1) (fun _ => row_unit_projection u hu)
  have ht : MeasurePreserving (WithLp.toLp 2 : (Fin 3 → ℝ) → V)
      (Measure.pi (fun _ : Fin 3 => gaussianReal 0 1)) gamma := ⟨by fun_prop,gamma_from_iid⟩
  exact ht.comp hp

theorem project_unit_ne_zero {I : Type} [Fintype I] (u : Row I) (hu : ‖u‖=1) :
    ∀ᵐ R ∂matrixLaw I,project u R≠0 :=
  (project_unit_law u hu).quasiMeasurePreserving.ae (gamma_ae_ne 0)

theorem project_normalized_unit {I : Type} [Fintype I] (u : Row I) (hu : ‖u‖=1) :
    ∀ᵐ R ∂matrixLaw I,‖unitVector (project u R)‖=1 := by
  filter_upwards [project_unit_ne_zero u hu] with R hR
  exact norm_unitVector _ hR

theorem row_projection_covariance {I : Type} [Fintype I] (u v : Row I) :
    cov[fun x : Row I => inner ℝ u x,fun x : Row I => inner ℝ v x;stdGaussian (Row I)]=inner ℝ u v := by
  rw [← covarianceBilin_apply_eq_cov (IsGaussian.memLp_two_id (μ:=stdGaussian (Row I))) u v,covarianceBilin_stdGaussian]
  rfl

theorem project_apply {I : Type} [Fintype I] (u : Row I) (R : Rows I) (r : Fin 3) :
    project u R r=∑ i : I,R r i*u i := by
  simp [project,PiLp.inner_apply,mul_comm]

theorem projected_correlation_integrable {I : Type} [Fintype I] (u v : Row I) :
    Integrable (fun R : Rows I => inner ℝ (unitVector (project u R)) (unitVector (project v R))) (matrixLaw I) := by
  have hm : Measurable (fun R : Rows I => inner ℝ (unitVector (project u R)) (unitVector (project v R))) :=
    (unitVector_measurable.comp (project_measurable u)).inner (unitVector_measurable.comp (project_measurable v))
  exact (integrable_const (1:ℝ)).mono' hm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun R => unit_inner_bound (project u R) (project v R)))

def rawProject {I : Type} [Fintype I] (u : Row I) (R : Fin 3 → I → ℝ) : V :=
  WithLp.toLp 2 (fun r => ∑ i : I,R r i*u i)

theorem rawProject_eq {I : Type} [Fintype I] (u : Row I) (R : Fin 3 → I → ℝ) :
    project u (toRows R)=rawProject u R := by
  apply (WithLp.equiv 2 (Fin 3 → ℝ)).injective
  funext r
  exact project_apply u (toRows R) r

theorem rawProject_unit_law {I : Type} [Fintype I] (u : Row I) (hu : ‖u‖=1) :
    MeasurePreserving (rawProject u) (rawMatrixLaw I) gamma := by
  have h := (project_unit_law u hu).comp (raw_to_rows_preserving (I:=I))
  have he : (project u ∘ toRows (I:=I))=rawProject u := funext (rawProject_eq u)
  rwa [he] at h

theorem rawProject_normalized_unit {I : Type} [Fintype I] (u : Row I) (hu : ‖u‖=1) :
    ∀ᵐ R ∂rawMatrixLaw I,‖unitVector (rawProject u R)‖=1 := by
  filter_upwards [(rawProject_unit_law u hu).quasiMeasurePreserving.ae (gamma_ae_ne 0)] with R hR
  exact norm_unitVector _ hR

end Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianMatrix
