/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Assumption21
import Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Qatlib.Foundations.MatrixAlgebra.TensorDiff
open Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Program
open Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Regularity
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation

namespace Qatlib.Papers.OverlapGapGoh26.AmpDynamics.CostConvention

def minimizationF (s h : ℝ) {t : ℕ} (u : Fin (t+1) → ℝ) : ℝ :=
  -h+u 0*s^2*(1-s)

theorem tensor_energy_neg {q N : ℕ} (J : Tensor q N) (z : Fin N → ℝ) :
    tensorEnergy (-J) z= -tensorEnergy J z := by
  simp [tensorEnergy,Finset.sum_neg_distrib]

theorem interaction_neg {r N : ℕ} (J : Fin N → (Fin r → Fin N) → ℝ)
    (z : Fin N → ℝ) (i : Fin N) : interaction (-J) z i= -interaction J z i := by
  simp [interaction,Finset.sum_neg_distrib]

theorem actual_maximizing_step_as_minimization {r N t : ℕ} (M : ℝ)
    (J : Tensor (r+1) N) (s : ℕ → ℝ) (U : Fin (t+1) → Fin N → ℝ) (i : Fin N) :
    ampNext M (rowTensor J) s t U i=
      clip M (minimizationF (s t) (interaction (rowTensor (-J)) (spinReadout s t U) i)
        (fun a => U a i)) := by
  have hj : rowTensor (-J)= -(rowTensor J) := rfl
  rw [hj,interaction_neg]
  simp [ampNext,minimizationF,FCoord]

theorem minimizationF_lipschitz_l2 (s : ℝ) (hs : s∈Set.Icc (0:ℝ) 1) {t : ℕ}
    (h h' : ℝ) (u v : Fin (t+1) → ℝ) :
    |minimizationF s h u-minimizationF s h' v|≤(1+4/27)*
      Real.sqrt ((h-h')^2+∑ a,(u a-v a)^2) := by
  have he : (-h- -h')^2=(h-h')^2 := by ring
  simpa only [FCoord,minimizationF,he] using FCoord_lipschitz_l2 s hs (-h) (-h') u v

theorem gaussian_tensor_neg_preserving (r N : ℕ) :
    MeasureTheory.MeasurePreserving (fun A : Tensor (r+1) N => -A)
      (gaussianTensorLaw r N) (gaussianTensorLaw r N) := by
  refine ⟨by fun_prop,?_⟩
  change (MeasureTheory.Measure.pi (fun _ : Fin (r+1) → Fin N =>
    ProbabilityTheory.gaussianReal 0 (((N:NNReal)^r)⁻¹))).map (fun A => fun k => -A k)=_
  rw [MeasureTheory.Measure.pi_map_pi (f:=fun _ (x : ℝ) => -x) (fun _ => by fun_prop)]
  simp_rw [ProbabilityTheory.gaussianReal_map_neg,neg_zero]
  rfl

theorem joint_tensor_neg_preserving (M : ℝ) (v : NNReal) (r N : ℕ) :
    MeasureTheory.MeasurePreserving (fun w : (Tensor (r+1) N×Tensor (r+1) N)×(Fin N → ℝ) =>
      ((-w.1.1,-w.1.2),w.2)) (jointLaw M v r N) (jointLaw M v r N) :=
  ((gaussian_tensor_neg_preserving r N).prod (gaussian_tensor_neg_preserving r N)).prod
    (MeasureTheory.MeasurePreserving.id _)

end Qatlib.Papers.OverlapGapGoh26.AmpDynamics.CostConvention
