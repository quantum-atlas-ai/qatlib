/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Endpoint.GaussianMean
import Qatlib.Papers.OverlapGapGoh26.GaussianBounds.RawMoments
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Scalar tests of Gaussian spin endpoints

`test` is the normalized inner product of a fixed vector with the endpoint `spin`. The module
proves smoothness, square integrability, and explicit difference and derivative bounds for these
scalar observables; odd interaction degree gives zero Gaussian mean. These estimates support the
endpoint analysis associated with [GohMuller2026].

## Main statements

* `test`: The normalized scalar endpoint observable `⟪v, spin s T x⟫ / N`.
* `test_mean_zero`: For odd interaction degree `r`, the scalar endpoint observable has zero mean
  under the standard Gaussian input law.
* `test_fderiv_bound`: For positive `r` and `N`, a schedule in `[0,1]`, and `‖v‖ ≤ √N`, the
  derivative norm of the scalar endpoint test is at most `4√T (2 + 2 normScale x r √T)^T / √N`.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators RealInnerProductSpace
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.RawInput
open Qatlib.Papers.OverlapGapGoh26.AmpDynamics.NormStability
open Qatlib.Papers.OverlapGapGoh26.UniformGrid.RawEnergyNorm
open Qatlib.Papers.OverlapGapGoh26.GaussianBounds.RawMoments
namespace Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Endpoint

/-- The endpoint spin map is infinitely differentiable as a function of its Gaussian input. -/
theorem spin_smooth {r N : ℕ} (s : ℕ→ℝ) (T : ℕ) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (spin (r:=r) (N:=N) s T) := by
  apply (contDiff_piLp (p:=2)).mpr
  intro i
  exact spin_component_smooth s T i

/-- The Euclidean norm of the endpoint spin is at most `√N`. -/
theorem spin_norm_le {r N : ℕ} (s : ℕ→ℝ) (T : ℕ) (x : Input r N) :
    ‖spin s T x‖≤Real.sqrt (N:ℝ) :=
  cube_spin_norm _ (rawSpin_cube s T (tensorCoords x) (seedCoords x))

/-- The normalized scalar endpoint observable `⟪v, spin s T x⟫ / N`. -/
def test {r N : ℕ} (s : ℕ→ℝ) (T : ℕ) (v : EuclideanSpace ℝ (Fin N)) (x : Input r N) : ℝ :=
  inner ℝ v (spin s T x)/(N:ℝ)

/-- The normalized scalar endpoint observable is infinitely differentiable in the Gaussian
input. -/
theorem test_smooth {r N : ℕ} (s : ℕ→ℝ) (T : ℕ) (v : EuclideanSpace ℝ (Fin N)) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (test (r:=r) s T v) := by
  exact (((innerSL ℝ v).contDiff).comp (spin_smooth s T)).div_const _

/-- The scalar endpoint observable belongs to `L²` of the standard Gaussian input law. -/
theorem test_memLp {r N : ℕ} (s : ℕ→ℝ) (T : ℕ) (v : EuclideanSpace ℝ (Fin N)) :
    MemLp (test (r:=r) s T v) 2 (stdGaussian (Input r N)) := by
  apply MemLp.of_bound (test_smooth s T v).continuous.aestronglyMeasurable
      (‖v‖*Real.sqrt (N:ℝ)/|(N:ℝ)|)
  apply Filter.Eventually.of_forall
  intro x
  rw [test,Real.norm_eq_abs,abs_div]
  exact div_le_div_of_nonneg_right ((abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_left (spin_norm_le s T x) (norm_nonneg _))) (abs_nonneg _)

/-- For odd interaction degree `r`, the scalar endpoint observable has zero mean under the
standard Gaussian input law. -/
theorem test_mean_zero {r N : ℕ} (hr : Odd r) (s : ℕ→ℝ) (T : ℕ)
    (v : EuclideanSpace ℝ (Fin N)) :
    (∫ x:Input r N,test s T v x ∂stdGaussian (Input r N))=0 := by
  have he := (seedReflection_preserving r N).integral_comp
    (seedReflection r N).toHomeomorph.measurableEmbedding (test s T v)
  have ho (x:Input r N) : test s T v (seedReflection r N x)= -test s T v x := by
    rw [test,spin_reflection hr,inner_neg_right,neg_div]
    rfl
  simp_rw [ho] at he
  rw [integral_neg] at he
  linarith

/-- For positive `r` and `N`, a schedule in `[0,1]`, and `‖v‖ ≤ √N`, the difference of scalar
endpoint tests is bounded by the displayed coefficient depending on `normScale y` times
`‖x-y‖`. -/
theorem test_difference {r N T : ℕ} (hr : 0<r) (hN : 0<N) (s : ℕ→ℝ)
    (hs : ∀ j≤T,s j∈Set.Icc (0:ℝ) 1) (v : EuclideanSpace ℝ (Fin N))
    (hv : ‖v‖≤Real.sqrt (N:ℝ)) (x y : Input r N) :
    |test s T v x-test s T v y|≤
      (4*Real.sqrt (T:ℝ)*(2+2*normScale y*(r:ℝ)*Real.sqrt (T:ℝ))^T/Real.sqrt (N:ℝ))*‖x-y‖ := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hK : 0≤normScale y := by unfold normScale;positivity
  have hspin := actual_raw_spin_norm hr hN s hs (tensorCoords x) (tensorCoords y)
    (seedCoords x) (seedCoords y) (normScale y) le_rfl
  have hsplit := input_split_le x y
  have hsp : ‖spin s T x-spin s T y‖≤
      (4*Real.sqrt (T:ℝ)*(2+2*normScale y*(r:ℝ)*Real.sqrt (T:ℝ))^T)*‖x-y‖ := by
    exact hspin.trans ((mul_le_mul_of_nonneg_left hsplit (by positivity)).trans_eq (by ring))
  rw [test,test,← sub_div,← inner_sub_right,abs_div,abs_of_pos hn]
  calc
    _ ≤ ‖v‖*‖spin s T x-spin s T y‖/(N:ℝ) :=
      div_le_div_of_nonneg_right (abs_real_inner_le_norm _ _) hn.le
    _ ≤ Real.sqrt (N:ℝ)*((4*Real.sqrt (T:ℝ)*(2+2*normScale y*(r:ℝ)*Real.sqrt (T:ℝ))^T)*‖x-y‖)/(N:ℝ) := by gcongr
    _ = _ := by
      have hsN : Real.sqrt (N:ℝ)≠0 := (Real.sqrt_pos.mpr hn).ne'
      rw [div_mul_eq_mul_div]
      apply (div_eq_div_iff hn.ne' hsN).mpr
      calc
        _ = (4*Real.sqrt (T:ℝ)*(2+2*normScale y*(r:ℝ)*Real.sqrt (T:ℝ))^T*‖x-y‖)*(Real.sqrt (N:ℝ))^2 := by ring
        _ = _ := by rw [Real.sq_sqrt hn.le]

/-- For positive `r` and `N`, a schedule in `[0,1]`, and `‖v‖ ≤ √N`, the derivative norm of the
scalar endpoint test is at most `4√T (2 + 2 normScale x r √T)^T / √N`. -/
theorem test_fderiv_bound {r N T : ℕ} (hr : 0<r) (hN : 0<N) (s : ℕ→ℝ)
    (hs : ∀ j≤T,s j∈Set.Icc (0:ℝ) 1) (v : EuclideanSpace ℝ (Fin N))
    (hv : ‖v‖≤Real.sqrt (N:ℝ)) (x : Input r N) :
    ‖fderiv ℝ (test (r:=r) s T v) x‖≤
      4*Real.sqrt (T:ℝ)*(2+2*normScale x*(r:ℝ)*Real.sqrt (T:ℝ))^T/Real.sqrt (N:ℝ) := by
  have hK : 0≤normScale x := by unfold normScale;positivity
  apply norm_fderiv_le_of_lip' ℝ (by positivity)
  exact Filter.Eventually.of_forall (fun y=>by
    simpa only [Real.norm_eq_abs] using test_difference hr hN s hs v hv y x)
end Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Endpoint
