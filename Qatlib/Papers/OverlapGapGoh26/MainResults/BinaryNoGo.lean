/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.MainResults.RawNoGo
import Qatlib.Papers.OverlapGapGoh26.MainResults.ActualMFContract
import Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Remainder.Supremum

/-!
# Conditional binary energy obstruction for raw dynamics

`nearBinary` records when the raw energy density reaches the normalized binary maximum minus a
specified margin. Comparison with the cube maximum, a subextensive optimum gap, and the raw path
estimates give an explicit probability bound and an asymptotic obstruction conditional on the
stated model overlap gap event holding with probability tending to one. `actual_source_mf_nogo`
specializes this result to the source schedule of [GohMuller2026].

## Main statements

* `actual_raw_binary_nogo_bound`: For odd `r`, `N ≥ 2`, a schedule in `[0,1]`, `μ > 0`, and `0 <
  ν₁ < ν₂ < 1`, the probability of `nearBinary s T (μ/16)` is bounded by the displayed sum of
  model overlap gap failure, norm, fluctuation, endpoint, and optimum gap terms. See
  [GohMuller2026].
* `actual_raw_binary_nogo`: For odd `r`, fixed `T`, schedules in `[0,1]`, and the stated
  positive margin and overlap thresholds, if the model overlap gap failure probability tends to
  zero, then the probability of reaching the binary maximum minus `μ/16` tends to zero. See
  [GohMuller2026].
* `actual_source_mf_nogo`: For odd `r` and positive fixed iteration count, the source schedule
  reaches the binary maximum minus `μ/16` with probability tending to zero, provided the stated
  model overlap gap failure probability tends to zero and the margin and overlap thresholds
  satisfy the given inequalities.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Classical NNReal BigOperators Topology
open Qatlib.Foundations.MatrixAlgebra.TensorDiff
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.RawInput
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation
open Qatlib.Papers.OverlapGapGoh26.GaussianBounds.GroundTransport
open Qatlib.Papers.OverlapGapGoh26.GaussianBounds.RawMoments
open Qatlib.Papers.OverlapGapGoh26.AmpDynamics.CostConvention
open Qatlib.Papers.OverlapGapGoh26.OgpBridge.Path
open Qatlib.Papers.OverlapGapGoh26.OgpBridge.Gaussian
open Qatlib.Papers.OverlapGapGoh26.UniformGrid.GroundPath
open Qatlib.Papers.OverlapGapGoh26.MainResults.RawNoGo

namespace Qatlib.Papers.OverlapGapGoh26.MainResults.BinaryNoGo

/-- The normalized binary maximum energy, expressed as the negative binary minimum for the
negated source tensor. -/
def binaryMaximum {r N : ℕ} (x : Input r N) : ℝ :=
    -binaryGround (-(sourceTensor (tensorCoords x).ofLp))/(N:ℝ)

/-- The event that the normalized binary maximum minus the raw energy density is at most `a`. -/
def nearBinary {r N : ℕ} (s : ℕ→ℝ) (T : ℕ) (a : ℝ) : Set (Input r N) :=
  {x | binaryMaximum x-energy s T x≤a}

/-- The tensor event that the absolute difference between binary and cube minimum energies
exceeds `aN`. -/
def gapEvent (r N : ℕ) (a : ℝ) : Set (Tensor (r+1) N) :=
  {A | a*(N:ℝ)< |binaryGround A-cubeOpt A|}

/-- The input event that the binary and cube minimum energies of the negated source tensor
differ in absolute value by more than `aN`. -/
def inputGapEvent (r N : ℕ) (a : ℝ) : Set (Input r N) :=
  {x | a*(N:ℝ)< |binaryGround (-(sourceTensor (tensorCoords x).ofLp))-cubeOpt (-(sourceTensor (tensorCoords x).ofLp))|}

/-- For `N > 0`, reaching the binary maximum within `μ/16` forces either reaching the cube
maximum within `μ/8` or an input optimum gap exceeding `μN/16`. -/
theorem nearBinary_subset {r N T : ℕ} (hN : 0<N) (s : ℕ→ℝ) (μ : ℝ) :
    nearBinary (r:=r) (N:=N) s T (μ/16)⊆nearCube s T (μ/8)∪inputGapEvent r N (μ/16) := by
  intro x hx
  by_cases hbad : x∈inputGapEvent r N (μ/16)
  · exact Or.inr hbad
  · left
    have hn : (0:ℝ)<N := by exact_mod_cast hN
    have hgap : binaryGround (-(sourceTensor (tensorCoords x).ofLp))-cubeOpt (-(sourceTensor (tensorCoords x).ofLp))≤(μ/16)*(N:ℝ) :=
      (le_abs_self _).trans (le_of_not_gt hbad)
    have hd := div_le_div_of_nonneg_right hgap hn.le
    have he : maximum x-binaryMaximum x≤μ/16 := by
      rw [maximum_formula]
      unfold binaryMaximum
      convert! hd using 1 <;> field_simp
      all_goals ring
    change binaryMaximum x-energy s T x≤μ/16 at hx
    change maximum x-energy s T x≤μ/8
    linarith

/-- The standard Gaussian input probability of `inputGapEvent` is at most the Gaussian tensor
probability of `gapEvent`. -/
theorem inputGapEvent_le (r N : ℕ) (a : ℝ) :
    (stdGaussian (Input r N)).real (inputGapEvent r N a)≤(gaussianTensorLaw r N).real (gapEvent r N a) := by
  have hm := (gaussian_tensor_neg_preserving r N).comp (actual_tensor_preserving r N)
  have h :=
      Measure.le_map_apply (μ:=stdGaussian (Input r N)) hm.measurable.aemeasurable (gapEvent r N a)
  rw [hm.map_eq] at h
  exact ENNReal.toReal_mono (by finiteness) h

/-- For odd `r`, `N ≥ 2`, a schedule in `[0,1]`, `μ > 0`, and `0 < ν₁ < ν₂ < 1`, the probability
of `nearBinary s T (μ/16)` is bounded by the displayed sum of model overlap gap failure,
norm, fluctuation, endpoint, and optimum gap terms. See [GohMuller2026]. -/
theorem actual_raw_binary_nogo_bound {r N T : ℕ} (hr : Odd r) (hN : 2≤N) (s : ℕ→ℝ)
    (hs : ∀ j≤T,s j∈Set.Icc (0:ℝ) 1) (μ ν₁ ν₂ : ℝ)
    (hμ : 0<μ) (hlo : 0<ν₁) (hgap : ν₁<ν₂) (hhi : ν₂<1) :
    (stdGaussian (Input r N)).real (nearBinary s T (μ/16))≤
      ((gaussianTensorLaw r N).prod (gaussianTensorLaw r N)).real (modelOgp r N μ ν₁ ν₂)ᶜ+
        8*Real.exp (-(N:ℝ))+(2*rawVarianceConstant r T+Real.pi^2)/((N:ℝ)*(μ/8)^2)+
        Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Endpoint.endpointConstant r T/
          ((N:ℝ)*(overlapTolerance r μ ν₁)^2)+(gaussianTensorLaw r N).real (gapEvent r N (μ/16)) := by
  have hn : 0<N := by omega
  exact ((measureReal_mono (nearBinary_subset (T:=T) hn s μ)).trans (measureReal_union_le _ _)).trans
    (add_le_add (actual_raw_cube_nogo_bound hr hN s hs μ ν₁ ν₂ hμ hlo hgap hhi) (inputGapEvent_le r N (μ/16)))

/-- For odd `r`, fixed `T`, schedules in `[0,1]`, and the stated positive margin and overlap
thresholds, if the model overlap gap failure probability tends to zero, then the probability
of reaching the binary maximum minus `μ/16` tends to zero. See [GohMuller2026]. -/
theorem actual_raw_binary_nogo {r : ℕ} (hr : Odd r) (T : ℕ) (s : ℕ→ℕ→ℝ)
    (hs : ∀ N j,j≤T→s N j∈Set.Icc (0:ℝ) 1) (μ ν₁ ν₂ : ℝ)
    (hμ : 0<μ) (hlo : 0<ν₁) (hgap : ν₁<ν₂) (hhi : ν₂<1)
    (hogp : Tendsto (fun N : ℕ => ((gaussianTensorLaw r N).prod (gaussianTensorLaw r N)).real
      (modelOgp r N μ ν₁ ν₂)ᶜ) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (stdGaussian (Input r N)).real (nearBinary (s N) T (μ/16))) atTop (𝓝 0) := by
  have he : Tendsto (fun N : ℕ => 8*Real.exp (-(N:ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using!
        (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop).const_mul (8:ℝ)
  have hc : Tendsto (fun N : ℕ => (2*rawVarianceConstant r T+Real.pi^2)/((N:ℝ)*(μ/8)^2)) atTop (𝓝 0) := by
    convert! tendsto_const_div_atTop_nhds_zero_nat ((2*rawVarianceConstant r T+Real.pi^2)/(μ/8)^2) using 1
    ext N
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hd : Tendsto (fun N : ℕ => Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Endpoint.endpointConstant r T/
      ((N:ℝ)*(overlapTolerance r μ ν₁)^2)) atTop (𝓝 0) := by
    convert! tendsto_const_div_atTop_nhds_zero_nat
      (Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Endpoint.endpointConstant r T/(overlapTolerance r μ ν₁)^2) using 1
    ext N
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hg : Tendsto (fun N : ℕ => (gaussianTensorLaw r N).real (gapEvent r N (μ/16))) atTop (𝓝 0) :=
    Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Remainder.actual_absolute_optimum_gap_subextensive r (μ/16) (by positivity)
  have hall := (((hogp.add he).add hc).add hd).add hg
  simp only [zero_add] at hall
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => measureReal_nonneg)) _ hall
  filter_upwards [eventually_ge_atTop 2] with N hN
  exact actual_raw_binary_nogo_bound hr hN (s N) (hs N) μ ν₁ ν₂ hμ hlo hgap hhi

/-- For odd `r` and positive fixed iteration count, the source schedule reaches the binary
maximum minus `μ/16` with probability tending to zero, provided the stated model overlap gap
failure probability tends to zero and the margin and overlap thresholds satisfy the given
inequalities. See [GohMuller2026]. -/
theorem actual_source_mf_nogo {r : ℕ} (hr : Odd r) (T : ℕ) (hT : 0<T)
    (μ ν₁ ν₂ : ℝ) (hμ : 0<μ) (hlo : 0<ν₁) (hgap : ν₁<ν₂) (hhi : ν₂<1)
    (hogp : Tendsto (fun N : ℕ => ((gaussianTensorLaw r N).prod (gaussianTensorLaw r N)).real
      (modelOgp r N μ ν₁ ν₂)ᶜ) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (stdGaussian (Input r N)).real
      (nearBinary (Qatlib.Papers.OverlapGapGoh26.MainResults.ActualMF.sourceSchedule T) T (μ/16))) atTop (𝓝 0) :=
  actual_raw_binary_nogo hr T (fun _ => Qatlib.Papers.OverlapGapGoh26.MainResults.ActualMF.sourceSchedule T)
    (fun _ j hj => Qatlib.Papers.OverlapGapGoh26.MainResults.ActualMF.source_schedule_range T hT j hj)
    μ ν₁ ν₂ hμ hlo hgap hhi hogp

end Qatlib.Papers.OverlapGapGoh26.MainResults.BinaryNoGo
