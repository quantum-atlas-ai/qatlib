/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Assumption21
import Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation

/-!
# Maximization and minimization sign conventions

Relates the maximizing AMP update to a minimization update by negating the interaction tensor.
The energy and contraction sign identities, together with Gaussian-law invariance, make this
convention change explicit in the setting of [GohMuller2026].

## Main statements

* `actual_maximizing_step_as_minimization`: rewrites the clipped update using the negated
  tensor.
* `joint_tensor_neg_preserving`: preserves the joint law when both tensor coordinates are
  negated.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Qatlib.Foundations.MatrixAlgebra.TensorDiff
open Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Program
open Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Regularity
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation

namespace Qatlib.Papers.OverlapGapGoh26.AmpDynamics.CostConvention

/-- The affine minimization update `−h + u 0 * s ^ 2 * (1 − s)`. -/
def minimizationF (s h : ℝ) {t : ℕ} (u : Fin (t+1) → ℝ) : ℝ :=
  -h+u 0*s^2*(1-s)

/-- Negating the tensor negates its energy at every spin configuration. -/
theorem tensor_energy_neg {q N : ℕ} (J : Tensor q N) (z : Fin N → ℝ) :
    tensorEnergy (-J) z= -tensorEnergy J z := by
  simp [tensorEnergy,Finset.sum_neg_distrib]

/-- Negating the interaction tensor negates the interaction at each coordinate. -/
theorem interaction_neg {r N : ℕ} (J : Fin N → (Fin r → Fin N) → ℝ)
    (z : Fin N → ℝ) (i : Fin N) : interaction (-J) z i= -interaction J z i := by
  simp [interaction,Finset.sum_neg_distrib]

/-- The maximizing AMP step equals the clipped minimization update evaluated with the negated
tensor [GohMuller2026]. -/
theorem actual_maximizing_step_as_minimization {r N t : ℕ} (M : ℝ)
    (J : Tensor (r+1) N) (s : ℕ → ℝ) (U : Fin (t+1) → Fin N → ℝ) (i : Fin N) :
    ampNext M (rowTensor J) s t U i=
      clip M (minimizationF (s t) (interaction (rowTensor (-J)) (spinReadout s t U) i)
        (fun a => U a i)) := by
  have hj : rowTensor (-J)= -(rowTensor J) := rfl
  rw [hj,interaction_neg]
  simp [ampNext,minimizationF,FCoord]

/-- For `s ∈ [0, 1]`, the minimization coordinate map has Euclidean Lipschitz bound `1 + 4 / 27`
in the field and history variables. -/
theorem minimizationF_lipschitz_l2 (s : ℝ) (hs : s∈Set.Icc (0:ℝ) 1) {t : ℕ}
    (h h' : ℝ) (u v : Fin (t+1) → ℝ) :
    |minimizationF s h u-minimizationF s h' v|≤(1+4/27)*
      Real.sqrt ((h-h')^2+∑ a,(u a-v a)^2) := by
  have he : (-h- -h')^2=(h-h')^2 := by ring
  simpa only [FCoord,minimizationF,he] using FCoord_lipschitz_l2 s hs (-h) (-h') u v

/-- Tensor negation preserves `gaussianTensorLaw r N` [GohMuller2026]. -/
theorem gaussian_tensor_neg_preserving (r N : ℕ) :
    MeasureTheory.MeasurePreserving (fun A : Tensor (r+1) N => -A)
      (gaussianTensorLaw r N) (gaussianTensorLaw r N) := by
  refine ⟨by fun_prop,?_⟩
  change (MeasureTheory.Measure.pi (fun _ : Fin (r+1) → Fin N =>
    ProbabilityTheory.gaussianReal 0 (((N:NNReal)^r)⁻¹))).map (fun A => fun k => -A k)=_
  rw [MeasureTheory.Measure.pi_map_pi (f:=fun _ (x : ℝ) => -x) (fun _ => by fun_prop)]
  simp_rw [ProbabilityTheory.gaussianReal_map_neg,neg_zero]
  rfl

/-- Simultaneously negating both tensor coordinates and preserving the seed coordinate preserves
`jointLaw M v r N`. -/
theorem joint_tensor_neg_preserving (M : ℝ) (v : NNReal) (r N : ℕ) :
    MeasureTheory.MeasurePreserving (fun w : (Tensor (r+1) N×Tensor (r+1) N)×(Fin N → ℝ) =>
      ((-w.1.1,-w.1.2),w.2)) (jointLaw M v r N) (jointLaw M v r N) :=
  ((gaussian_tensor_neg_preserving r N).prod (gaussian_tensor_neg_preserving r N)).prod
    (MeasureTheory.MeasurePreserving.id _)

end Qatlib.Papers.OverlapGapGoh26.AmpDynamics.CostConvention
