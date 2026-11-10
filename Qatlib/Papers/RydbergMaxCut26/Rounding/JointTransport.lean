/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.Rounding.OrthogonalResidual
import Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianEndpoints
import Qatlib.Papers.RydbergMaxCut26.Rounding.Analytic.PairGaussianLaw
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory
open Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianPair
open Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianMatrix
open Qatlib.Papers.RydbergMaxCut26.Rounding.Laplace

namespace Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianJoint

def rowPairLinear {I : Type} [Fintype I] (u v : Row I) : Row I →L[ℝ] ℝ×ℝ :=
  (innerSL ℝ u).prod (innerSL ℝ v)

theorem row_pair_gaussian {I : Type} [Fintype I] (u v : Row I) :
    HasGaussianLaw (fun x : Row I => (inner ℝ u x,inner ℝ v x)) (stdGaussian (Row I)) := by
  exact (IsGaussian.hasGaussianLaw_id (μ:=stdGaussian (Row I))).map_fun (rowPairLinear u v)

theorem row_pair_independent {I : Type} [Fintype I] (u v : Row I) (horth : inner ℝ u v=0) :
    IndepFun (fun x : Row I => inner ℝ u x) (fun x : Row I => inner ℝ v x) (stdGaussian (Row I)) := by
  apply (row_pair_gaussian u v).indepFun_of_covariance_eq_zero
  rw [row_projection_covariance,horth]

theorem row_pair_preserving {I : Type} [Fintype I] (u v : Row I)
    (hu : ‖u‖=1) (hv : ‖v‖=1) (horth : inner ℝ u v=0) :
    MeasurePreserving (fun x : Row I => (inner ℝ u x,inner ℝ v x))
      (stdGaussian (Row I)) ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  refine ⟨by fun_prop,?_⟩
  have h := (row_pair_independent u v horth).map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)
  rw [(row_unit_projection u hu).map_eq,(row_unit_projection v hv).map_eq] at h
  exact h

def orthogonalRowPairs {I : Type} [Fintype I] (u v : Row I) (R : Rows I) : Fin 3→ℝ×ℝ :=
  fun r => (inner ℝ u (R r),inner ℝ v (R r))

theorem orthogonal_row_pairs_preserving {I : Type} [Fintype I] (u v : Row I)
    (hu : ‖u‖=1) (hv : ‖v‖=1) (horth : inner ℝ u v=0) :
    MeasurePreserving (orthogonalRowPairs u v) (matrixLaw I) pairRowsLaw :=
  measurePreserving_pi _ _ (fun _ : Fin 3 => row_pair_preserving u v hu hv horth)

theorem orthogonal_projects_preserving {I : Type} [Fintype I] (u v : Row I)
    (hu : ‖u‖=1) (hv : ‖v‖=1) (horth : inner ℝ u v=0) :
    MeasurePreserving (fun R : Rows I => (project u R,project v R)) (matrixLaw I) sourceLaw := by
  exact packPair_preserving.comp (orthogonal_row_pairs_preserving u v hu hv horth)

theorem orthogonal_projects_independent {I : Type} [Fintype I] (u v : Row I)
    (hu : ‖u‖=1) (hv : ‖v‖=1) (horth : inner ℝ u v=0) :
    IndepFun (project u) (project v) (matrixLaw I) := by
  apply (indepFun_iff_map_prod_eq_prod_map_map (project_measurable u).aemeasurable (project_measurable v).aemeasurable).mpr
  rw [(orthogonal_projects_preserving u v hu hv horth).map_eq,
    (project_unit_law u hu).map_eq,(project_unit_law v hv).map_eq]

theorem residual_projects_preserving {I : Type} [Fintype I] (u v : Row I)
    (hu : ‖u‖=1) (hv : ‖v‖=1) (ht : |inner ℝ u v|<1) :
    MeasurePreserving (fun R : Rows I => (project u R,project (residualDirection u v) R))
      (matrixLaw I) sourceLaw :=
  orthogonal_projects_preserving u (residualDirection u v) hu
    (residual_geometry u v hu hv ht).1 (residual_geometry u v hu hv ht).2.1

theorem actual_pair_correlated_preserving {I : Type} [Fintype I] (u v : Row I)
    (hu : ‖u‖=1) (hv : ‖v‖=1) (ht : |inner ℝ u v|<1) :
    MeasurePreserving (fun R : Rows I => (project u R,project v R))
      (matrixLaw I) (correlatedLaw (inner ℝ u v)) := by
  have hp : MeasurePreserving (pairLinear (inner ℝ u v)) sourceLaw (correlatedLaw (inner ℝ u v)) :=
      ⟨by fun_prop,rfl⟩
  have h := hp.comp (residual_projects_preserving u v hu hv ht)
  have he : pairLinear (inner ℝ u v) ∘
      (fun R : Rows I => (project u R,project (residualDirection u v) R))=
      (fun R : Rows I => (project u R,project v R)) := by
    funext R
    apply Prod.ext
    · rfl
    · exact (project_reconstruction u v hu hv ht R).symm
  rwa [he] at h

theorem actual_raw_pair_correlated_preserving {I : Type} [Fintype I] (u v : Row I)
    (hu : ‖u‖=1) (hv : ‖v‖=1) (ht : |inner ℝ u v|<1) :
    MeasurePreserving (fun R : Fin 3→I→ℝ => (rawProject u R,rawProject v R))
      (rawMatrixLaw I) (correlatedLaw (inner ℝ u v)) := by
  have h := (actual_pair_correlated_preserving u v hu hv ht).comp (raw_to_rows_preserving (I:=I))
  have he : (fun R : Rows I => (project u R,project v R)) ∘ toRows=
      (fun R : Fin 3→I→ℝ => (rawProject u R,rawProject v R)) := by
    funext R
    simp only [Function.comp_apply,rawProject_eq]
  rwa [he] at h

theorem matrixExpectation_eq_actualKernel {I : Type} [Fintype I] (u v : Row I)
    (hu : ‖u‖=1) (hv : ‖v‖=1) (ht : |inner ℝ u v|<1) :
    matrixExpectation u v=actualKernel (inner ℝ u v) := by
  have hp := residual_projects_preserving u v hu hv ht
  have h :=
      integral_map (μ:=matrixLaw I) hp.measurable.aemeasurable
      (pairCorrelation_measurable (inner ℝ u v)).aestronglyMeasurable
  rw [hp.map_eq] at h
  have he : (fun R : Rows I => pairCorrelation (inner ℝ u v) (project u R,project (residualDirection u v) R))=
      matrixCorrelation u v := by
    funext R
    unfold pairCorrelation matrixCorrelation
    rw [← project_reconstruction u v hu hv ht R]
  rw [he] at h
  exact h.symm

theorem rawExpectation_eq_actualKernel {I : Type} [Fintype I] (u v : Row I)
    (hu : ‖u‖=1) (hv : ‖v‖=1) (ht : |inner ℝ u v|<1) :
    rawExpectation u v=actualKernel (inner ℝ u v) :=
  (rawExpectation_eq u v).trans (matrixExpectation_eq_actualKernel u v hu hv ht)

end Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianJoint
