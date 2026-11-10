/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianMatrix
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
open MeasureTheory ProbabilityTheory

namespace Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianMatrix
open Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianPair

def matrixCorrelation {I : Type} [Fintype I] (u v : Row I) (R : Rows I) : ℝ :=
  inner ℝ (unitVector (project u R)) (unitVector (project v R))

theorem matrixCorrelation_measurable {I : Type} [Fintype I] (u v : Row I) : Measurable (matrixCorrelation u v) :=
  (unitVector_measurable.comp (project_measurable u)).inner (unitVector_measurable.comp (project_measurable v))

def matrixExpectation {I : Type} [Fintype I] (u v : Row I) : ℝ :=
  ∫ R,matrixCorrelation u v R ∂matrixLaw I

theorem project_neg {I : Type} [Fintype I] (u : Row I) (R : Rows I) : project (-u) R= -project u R := by
  apply (WithLp.equiv 2 (Fin 3 → ℝ)).injective
  funext r
  simp [project,inner_neg_left]

theorem matrixExpectation_self {I : Type} [Fintype I] (u : Row I) (hu : ‖u‖=1) : matrixExpectation u u=1 := by
  have h : matrixCorrelation u u =ᵐ[matrixLaw I] (fun _ => (1:ℝ)) := by
    filter_upwards [project_normalized_unit u hu] with R hR
    simp only [matrixCorrelation,real_inner_self_eq_norm_sq,hR,one_pow]
  rw [matrixExpectation,integral_congr_ae h]
  simp

theorem matrixExpectation_neg {I : Type} [Fintype I] (u : Row I) (hu : ‖u‖=1) : matrixExpectation u (-u)= -1 := by
  have h : matrixCorrelation u (-u)=(fun R => -matrixCorrelation u u R) := by
    funext R
    simp only [matrixCorrelation,project_neg,unitVector_neg,inner_neg_right]
  rw [matrixExpectation,h,integral_neg]
  exact congrArg Neg.neg (matrixExpectation_self u hu)

def axisReflection {I : Type} [Fintype I] (u : Row I) : Row I ≃ₗᵢ[ℝ] Row I :=
  (Submodule.span ℝ {u}).reflection

theorem axisReflection_self {I : Type} [Fintype I] (u : Row I) : axisReflection u u=u :=
  Submodule.reflection_mem_subspace_eq_self (Submodule.mem_span_singleton_self u)

theorem axisReflection_orthogonal {I : Type} [Fintype I] (u v : Row I) (h : inner ℝ u v=0) : axisReflection u v= -v :=
  Submodule.reflection_mem_subspace_orthogonalComplement_eq_neg
    (Submodule.mem_orthogonal_singleton_iff_inner_right.mpr h)

def reflectRows {I : Type} [Fintype I] (u : Row I) (R : Rows I) : Rows I :=
    fun r => axisReflection u (R r)

theorem reflectRows_preserving {I : Type} [Fintype I] (u : Row I) :
    MeasurePreserving (reflectRows u) (matrixLaw I) (matrixLaw I) := by
  exact measurePreserving_pi _ _ (fun _ : Fin 3 =>
    (⟨by fun_prop,stdGaussian_map (axisReflection u)⟩ :
      MeasurePreserving (axisReflection u) (stdGaussian (Row I)) (stdGaussian (Row I))))

theorem project_reflect_self {I : Type} [Fintype I] (u : Row I) (R : Rows I) :
    project u (reflectRows u R)=project u R := by
  apply (WithLp.equiv 2 (Fin 3 → ℝ)).injective
  funext r
  have h := (axisReflection u).inner_map_map u (R r)
  simpa only [axisReflection_self] using! h

theorem project_reflect_orthogonal {I : Type} [Fintype I] (u v : Row I) (h : inner ℝ u v=0) (R : Rows I) :
    project v (reflectRows u R)= -project v R := by
  apply (WithLp.equiv 2 (Fin 3 → ℝ)).injective
  funext r
  have he := (axisReflection u).inner_map_map v (R r)
  rw [axisReflection_orthogonal u v h,inner_neg_left] at he
  change inner ℝ v (axisReflection u (R r))= -inner ℝ v (R r)
  linarith

theorem matrixExpectation_orthogonal {I : Type} [Fintype I] (u v : Row I) (h : inner ℝ u v=0) : matrixExpectation u v=0 := by
  have hp (R : Rows I) : matrixCorrelation u v (reflectRows u R)= -matrixCorrelation u v R := by
    simp only [matrixCorrelation,project_reflect_self,project_reflect_orthogonal u v h,unitVector_neg,inner_neg_right]
  have he := integral_map (μ:=matrixLaw I) (reflectRows_preserving u).measurable.aemeasurable
    (matrixCorrelation_measurable u v).aestronglyMeasurable
  rw [(reflectRows_preserving u).map_eq] at he
  have hf :
      (fun R => matrixCorrelation u v (reflectRows u R))=fun R => -matrixCorrelation u v R := funext hp
  rw [hf,integral_neg] at he
  change matrixExpectation u v= -matrixExpectation u v at he
  linarith

def rawExpectation {I : Type} [Fintype I] (u v : Row I) : ℝ :=
  ∫ R,inner ℝ (unitVector (rawProject u R)) (unitVector (rawProject v R)) ∂rawMatrixLaw I

theorem rawExpectation_eq {I : Type} [Fintype I] (u v : Row I) : rawExpectation u v=matrixExpectation u v := by
  have h := integral_map (μ:=rawMatrixLaw I) (raw_to_rows_preserving (I:=I)).measurable.aemeasurable
    (matrixCorrelation_measurable u v).aestronglyMeasurable
  rw [(raw_to_rows_preserving (I:=I)).map_eq] at h
  simp only [matrixCorrelation,rawProject_eq] at h
  exact h.symm

theorem raw_three_cases {I : Type} [Fintype I] (u v : Row I) (hu : ‖u‖=1) (horth : inner ℝ u v=0) :
    rawExpectation u u=1 ∧ rawExpectation u (-u)= -1 ∧ rawExpectation u v=0 := by
  simp only [rawExpectation_eq,matrixExpectation_self u hu,matrixExpectation_neg u hu,matrixExpectation_orthogonal u v horth,and_self]

end Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianMatrix
