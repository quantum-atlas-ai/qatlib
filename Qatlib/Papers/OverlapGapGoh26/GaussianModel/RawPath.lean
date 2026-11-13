/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.GaussianBounds.RawMoments
import Qatlib.Papers.OverlapGapGoh26.GaussianModel.Stationarity
import Qatlib.Foundations.ProbabilityCore.GaussPoincare.UniformRotation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Interpolated Gaussian inputs for raw dynamics

`inputPath` interpolates both tensor and seed coordinates, and `spinPath` and `energyPath`
evaluate the raw dynamics along it. The path has a Gaussian rotation representation and
stationary input marginals; `actual_raw_continuum_tail` bounds energy deviations uniformly over
the whole interpolation interval. These results support the path obstruction analysis associated
with [GohMuller2026].

## Main statements

* `inputPath_preserving`: For `τ ∈ [0,1]`, interpolating two independent standard Gaussian
  inputs preserves the standard Gaussian law.
* `actual_energy_stationary`: For each `τ ∈ [0,1]` and threshold `c`, the raw energy path has
  the same upper threshold probability as the raw energy at a single standard Gaussian input.
* `actual_raw_continuum_tail`: For positive `r` and `N`, a schedule in `[0,1]`, and `ε > 0`, the
  probability of a raw energy change of at least `ε` somewhere along the input path is at most
  `2 * rawVarianceConstant r T / (N * ε²)`.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical NNReal BigOperators
open Qatlib.Foundations.MatrixAlgebra.TensorDiff
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.RawInput
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation
open Qatlib.Papers.OverlapGapGoh26.GaussianBounds.GroundTransport
open Qatlib.Papers.OverlapGapGoh26.GaussianBounds.RawMoments
open Qatlib.Papers.OverlapGapGoh26.UniformGrid.RawEnergyNorm

namespace Qatlib.Papers.OverlapGapGoh26.GaussianModel.RawPath

/-- The combined input interpolation `√(1-τ) x + √τ y`. -/
def inputPath {r N : ℕ} (x y : Input r N) (τ : ℝ) : Input r N :=
  Real.sqrt (1-τ)•x+Real.sqrt τ•y

/-- The raw spin endpoint evaluated along the combined tensor and seed input interpolation. -/
def spinPath {r N : ℕ} (s : ℕ→ℝ) (T : ℕ) (x y : Input r N) (τ : ℝ) : EuclideanSpace ℝ (Fin N) :=
  rawSpin s T (tensorCoords (inputPath x y τ)) (seedCoords (inputPath x y τ))

/-- The raw energy density evaluated along the combined Gaussian input interpolation. -/
def energyPath {r N : ℕ} (s : ℕ→ℝ) (T : ℕ) (x y : Input r N) (τ : ℝ) : ℝ :=
  energy s T (inputPath x y τ)

/-- Extracting the scaled tensor along `inputPath` agrees with interpolating the two extracted
scaled tensors. -/
theorem source_tensor_path {r N : ℕ} (x y : Input r N) (τ : ℝ) :
    sourceTensor (tensorCoords (inputPath x y τ)).ofLp=
      interpolate (sourceTensor (tensorCoords x).ofLp) (sourceTensor (tensorCoords y).ofLp) τ := by
  funext k
  change Real.sqrt (((N:ℝ)^r)⁻¹)*(Real.sqrt (1-τ)*x (Sum.inl k)+Real.sqrt τ*y (Sum.inl k))=
    Real.sqrt (1-τ)*(Real.sqrt (((N:ℝ)^r)⁻¹)*x (Sum.inl k))+Real.sqrt τ*(Real.sqrt (((N:ℝ)^r)⁻¹)*y (Sum.inl k))
  ring

/-- The combined input path is continuous in the interpolation parameter. -/
theorem continuous_inputPath {r N : ℕ} (x y : Input r N) : Continuous (inputPath x y) := by
  unfold inputPath
  fun_prop

/-- The raw spin path is continuous in the interpolation parameter. -/
theorem continuous_spinPath {r N : ℕ} (s : ℕ→ℝ) (T : ℕ) (x y : Input r N) : Continuous (spinPath s T x y) := by
  have hc : Continuous (fun z : Input r N => rawSpin s T (tensorCoords z) (seedCoords z)) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin N => ℝ)).comp
    apply continuous_pi
    intro i
    exact (contDiff_feedback s T i 2).continuous
  exact hc.comp (continuous_inputPath x y)

/-- Every coordinate of the raw spin path has absolute value at most one. -/
theorem spinPath_cube {r N : ℕ} (s : ℕ→ℝ) (T : ℕ) (x y : Input r N) (τ : ℝ) :
    ∀ i,|spinPath s T x y τ i|≤1 := rawSpin_cube s T _ _

/-- For `τ ∈ [0,1]`, `inputPath x y τ` is the first component of the rotation of `(x,y)` by
angle `arcsin(√τ)`. -/
theorem inputPath_rotation {r N : ℕ} (x y : Input r N) (τ : ℝ) (hτ : τ∈Set.Icc (0:ℝ) 1) :
    inputPath x y τ=(ContinuousLinearMap.rotation (Real.arcsin (Real.sqrt τ)) (x,y)).1 := by
  have hs : Real.sqrt τ≤1 := by exact (Real.sqrt_le_one).mpr hτ.2
  have hlo : -1≤Real.sqrt τ := by linarith [Real.sqrt_nonneg τ]
  simp only [inputPath,ContinuousLinearMap.rotation_apply,Real.cos_arcsin,
    Real.sq_sqrt hτ.1,Real.sin_arcsin hlo hs]

/-- The angle `arcsin(√τ)` lies in `[0,π/2]` for every real `τ`. -/
theorem inputPath_angle (τ : ℝ) :
    Real.arcsin (Real.sqrt τ)∈Set.Icc (0:ℝ) (Real.pi/2) :=
  ⟨Real.arcsin_nonneg.mpr (Real.sqrt_nonneg τ),Real.arcsin_le_pi_div_two _⟩

/-- For `τ ∈ [0,1]`, interpolating two independent standard Gaussian inputs preserves the
standard Gaussian law. -/
theorem inputPath_preserving (r N : ℕ) (τ : ℝ) (hτ : τ∈Set.Icc (0:ℝ) 1) :
    MeasurePreserving (fun w : Input r N×Input r N => inputPath w.1 w.2 τ)
      ((stdGaussian (Input r N)).prod (stdGaussian (Input r N))) (stdGaussian (Input r N)) := by
  have hm := (measurePreserving_fst (μ:=stdGaussian (Input r N)) (ν:=stdGaussian (Input r N))).comp
    (Qatlib.Foundations.ProbabilityCore.GaussPoincare.Rotation.rotation_preserving (E:=Input r N) (Real.arcsin (Real.sqrt τ)))
  convert hm using 1
  funext w
  exact inputPath_rotation w.1 w.2 τ hτ

/-- For each `τ ∈ [0,1]` and threshold `c`, the raw energy path has the same upper threshold
probability as the raw energy at a single standard Gaussian input. -/
theorem actual_energy_stationary {r N : ℕ} (s : ℕ→ℝ) (T : ℕ) (τ : ℝ)
    (hτ : τ∈Set.Icc (0:ℝ) 1) (c : ℝ) :
    ((stdGaussian (Input r N)).prod (stdGaussian (Input r N))) {w | c≤energyPath s T w.1 w.2 τ}=
      (stdGaussian (Input r N)) {x | c≤energy s T x} :=
  (inputPath_preserving r N τ hτ).measure_preimage
    (measurableSet_le measurable_const (contDiff_energy s T).continuous.measurable).nullMeasurableSet

/-- For positive `r` and `N`, a schedule in `[0,1]`, and `ε > 0`, the probability of a raw
energy change of at least `ε` somewhere along the input path is at most `2 *
rawVarianceConstant r T / (N * ε²)`. See [GohMuller2026]. -/
theorem actual_raw_continuum_tail {r N T : ℕ} (hr : 0<r) (hN : 0<N) (s : ℕ→ℝ)
    (hs : ∀ j≤T,s j∈Set.Icc (0:ℝ) 1) (ε : ℝ) (hε : 0<ε) :
    ((stdGaussian (Input r N)).prod (stdGaussian (Input r N))).real
      {w | ∃ τ∈Set.Icc (0:ℝ) 1,ε≤|energyPath s T w.1 w.2 τ-energy s T w.1|}≤
      2*rawVarianceConstant r T/((N:ℝ)*ε^2) := by
  have hsub : {w : Input r N×Input r N | ∃ τ∈Set.Icc (0:ℝ) 1,ε≤|energyPath s T w.1 w.2 τ-energy s T w.1|}⊆
      {w | ∃ θ∈Set.Icc (0:ℝ) (Real.pi/2),ε≤|energy s T (ContinuousLinearMap.rotation θ w).1-energy s T w.1|} := by
    rintro w ⟨τ,hτ,h⟩
    refine ⟨Real.arcsin (Real.sqrt τ),inputPath_angle τ,?_⟩
    simpa only [energyPath,inputPath_rotation w.1 w.2 τ hτ] using h
  refine (measureReal_mono hsub).trans ?_
  refine (Qatlib.Foundations.ProbabilityCore.GaussPoincare.UniformRotation.continuum_rotation_tail
    (energy s T) ((contDiff_energy s T).of_le (by simp)) (gradient_square_integrable hr hN s hs) ε hε).trans ?_
  exact (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (actual_gradient_integral_bound hr hN s hs) (by positivity : (0:ℝ)≤Real.pi^2/4))
    (sq_nonneg ε)).trans_eq (by unfold rawVarianceConstant; ring)

end Qatlib.Papers.OverlapGapGoh26.GaussianModel.RawPath
