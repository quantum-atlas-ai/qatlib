/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.AmpDynamics.FiniteAmp
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators
open Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Program Qatlib.Foundations.MatrixAlgebra.TensorDiff

namespace Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation

def rowTensor {r N : ℕ} (J : Tensor (r+1) N) : Fin N → (Fin r → Fin N) → ℝ :=
  fun i k => J (Fin.cons i k)

def interpolate {q N : ℕ} (A B : Tensor q N) (τ : ℝ) : Tensor q N :=
  fun k => Real.sqrt (1-τ)*A k+Real.sqrt τ*B k

def gaussianTensorLaw (r N : ℕ) : Measure (Tensor (r+1) N) :=
  Measure.pi (fun _ => gaussianReal 0 (((N:NNReal)^r)⁻¹))

instance gaussianTensorLaw_probability (r N : ℕ) : IsProbabilityMeasure (gaussianTensorLaw r N) := by
  unfold gaussianTensorLaw
  infer_instance

def boundedSeedLaw (M : ℝ) (N : ℕ) (v : NNReal) : Measure (Fin N → ℝ) :=
  (Measure.pi (fun _ : Fin N => gaussianReal 0 v)).map (fun seed => fun i => clip M (seed i))

theorem boundedSeedLaw_ae (M : ℝ) (hM : 0≤M) (N : ℕ) (v : NNReal) :
    ∀ᵐ seed ∂boundedSeedLaw M N v, ∀ i, seed i ∈ Set.Icc (-M) M := by
  have hc : Continuous (fun seed : Fin N → ℝ => fun i => clip M (seed i)) :=
    continuous_pi (fun i => (clip_lipschitz M).continuous.comp (continuous_apply i))
  rw [boundedSeedLaw, MeasureTheory.ae_map_iff hc.measurable.aemeasurable]
  · exact Filter.Eventually.of_forall (fun seed i => clip_mem M hM (seed i))
  · simpa [Set.pi] using MeasurableSet.pi Set.countable_univ
      (fun _ _ => (measurableSet_Icc : MeasurableSet (Set.Icc (-M) M)))

instance boundedSeedLaw_probability (M : ℝ) (N : ℕ) (v : NNReal) : IsProbabilityMeasure (boundedSeedLaw M N v) := by
  unfold boundedSeedLaw
  infer_instance

def jointLaw (M : ℝ) (v : NNReal) (r N : ℕ) :
    Measure ((Tensor (r+1) N × Tensor (r+1) N) × (Fin N → ℝ)) :=
  ((gaussianTensorLaw r N).prod (gaussianTensorLaw r N)).prod (boundedSeedLaw M N v)

theorem jointLaw_seed_independent (M : ℝ) (v : NNReal) (r N : ℕ) :
    IndepFun (fun x : (Tensor (r+1) N × Tensor (r+1) N) × (Fin N → ℝ) => x.1)
      (fun x => x.2) (jointLaw M v r N) :=
  indepFun_prod measurable_id measurable_id

def outputPath {r N : ℕ} (M : ℝ) (s : ℕ → ℝ) (T : ℕ)
    (A B : Tensor (r+1) N) (seed : Fin N → ℝ) (τ : ℝ) : EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 (ampOutput M (rowTensor (interpolate A B τ)) seed s T)

theorem continuous_outputPath {r N : ℕ} (M : ℝ) (s : ℕ → ℝ) (T : ℕ)
    (A B : Tensor (r+1) N) (seed : Fin N → ℝ) : Continuous (outputPath M s T A B seed) := by
  have hc : Continuous (fun τ : ℝ => rowTensor (interpolate A B τ)) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro k
    unfold rowTensor interpolate
    fun_prop
  exact (PiLp.continuous_toLp 2 (fun _ : Fin N => ℝ)).comp
    ((continuous_ampOutput M s T).comp (hc.prodMk continuous_const))

theorem outputPath_cube {r N : ℕ} (M : ℝ) (s : ℕ → ℝ) (T : ℕ)
    (A B : Tensor (r+1) N) (seed : Fin N → ℝ) (τ : ℝ) (i : Fin N) :
    (outputPath M s T A B seed τ).ofLp i ∈ Set.Icc (-1:ℝ) 1 := clip_mem 1 (by norm_num) _

theorem interpolate_zero {q N : ℕ} (A B : Tensor q N) : interpolate A B 0=A := by
  ext k
  simp [interpolate]

theorem interpolate_one {q N : ℕ} (A B : Tensor q N) : interpolate A B 1=B := by
  ext k
  simp [interpolate]

end Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation
