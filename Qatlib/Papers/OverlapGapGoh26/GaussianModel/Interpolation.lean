/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.AmpDynamics.FiniteAmp
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic

/-!
# Gaussian tensor interpolation and AMP output paths

`gaussianTensorLaw` gives independent centered tensor entries with variance `N⁻ʳ`, and
`jointLaw` combines two such tensors with an independent clipped Gaussian seed. `interpolate`
and `outputPath` define a continuous AMP output path with coordinates in `[-1,1]`, furnishing
the probabilistic setup used in the analysis of [GohMuller2026].

## Main statements

* `jointLaw_seed_independent`: Under `jointLaw`, the pair of Gaussian tensors is independent of
  the seed.
* `continuous_outputPath`: The AMP output path is continuous in the interpolation parameter.
* `outputPath_cube`: Every coordinate of the AMP output path belongs to `[-1,1]`.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators
open Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Program Qatlib.Foundations.MatrixAlgebra.TensorDiff

namespace Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation

/-- The row representation of a tensor, obtained by separating the first index from the
remaining `r` indices. -/
def rowTensor {r N : ℕ} (J : Tensor (r+1) N) : Fin N → (Fin r → Fin N) → ℝ :=
  fun i k => J (Fin.cons i k)

/-- The tensor interpolation `√(1-τ) A + √τ B`. -/
def interpolate {q N : ℕ} (A B : Tensor q N) (τ : ℝ) : Tensor q N :=
  fun k => Real.sqrt (1-τ)*A k+Real.sqrt τ*B k

/-- The product law of centered real Gaussian tensor entries with variance `((N:NNReal)^r)⁻¹`. -/
def gaussianTensorLaw (r N : ℕ) : Measure (Tensor (r+1) N) :=
  Measure.pi (fun _ => gaussianReal 0 (((N:NNReal)^r)⁻¹))

instance gaussianTensorLaw_probability (r N : ℕ) : IsProbabilityMeasure (gaussianTensorLaw r N) := by
  unfold gaussianTensorLaw
  infer_instance

/-- The pushforward of independent centered Gaussian seed coordinates of variance `v` by
coordinatewise clipping at `M`. -/
def boundedSeedLaw (M : ℝ) (N : ℕ) (v : NNReal) : Measure (Fin N → ℝ) :=
  (Measure.pi (fun _ : Fin N => gaussianReal 0 v)).map (fun seed => fun i => clip M (seed i))

/-- For `M ≥ 0`, every seed coordinate lies in `[-M,M]` almost surely under `boundedSeedLaw`. -/
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

/-- The product law of two independent Gaussian tensors and an independent clipped Gaussian
seed. -/
def jointLaw (M : ℝ) (v : NNReal) (r N : ℕ) :
    Measure ((Tensor (r+1) N × Tensor (r+1) N) × (Fin N → ℝ)) :=
  ((gaussianTensorLaw r N).prod (gaussianTensorLaw r N)).prod (boundedSeedLaw M N v)

/-- Under `jointLaw`, the pair of Gaussian tensors is independent of the seed. -/
theorem jointLaw_seed_independent (M : ℝ) (v : NNReal) (r N : ℕ) :
    IndepFun (fun x : (Tensor (r+1) N × Tensor (r+1) N) × (Fin N → ℝ) => x.1)
      (fun x => x.2) (jointLaw M v r N) :=
  indepFun_prod measurable_id measurable_id

/-- The Euclidean AMP output obtained from the interpolated tensor with a fixed seed. -/
def outputPath {r N : ℕ} (M : ℝ) (s : ℕ → ℝ) (T : ℕ)
    (A B : Tensor (r+1) N) (seed : Fin N → ℝ) (τ : ℝ) : EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 (ampOutput M (rowTensor (interpolate A B τ)) seed s T)

/-- The AMP output path is continuous in the interpolation parameter. -/
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

/-- Every coordinate of the AMP output path belongs to `[-1,1]`. -/
theorem outputPath_cube {r N : ℕ} (M : ℝ) (s : ℕ → ℝ) (T : ℕ)
    (A B : Tensor (r+1) N) (seed : Fin N → ℝ) (τ : ℝ) (i : Fin N) :
    (outputPath M s T A B seed τ).ofLp i ∈ Set.Icc (-1:ℝ) 1 := clip_mem 1 (by norm_num) _

/-- The tensor interpolation at parameter zero equals its first tensor. -/
theorem interpolate_zero {q N : ℕ} (A B : Tensor q N) : interpolate A B 0=A := by
  ext k
  simp [interpolate]

/-- The tensor interpolation at parameter one equals its second tensor. -/
theorem interpolate_one {q N : ℕ} (A B : Tensor q N) : interpolate A B 1=B := by
  ext k
  simp [interpolate]

end Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation
