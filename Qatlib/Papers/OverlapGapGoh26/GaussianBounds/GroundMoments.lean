/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.GaussianBounds.ActualGround
import Qatlib.Papers.OverlapGapGoh26.GaussianBounds.LipschitzMoments
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Gaussian moments of the binary ground energy density

`actualGroundDensity` represents the normalized binary ground energy in standard Euclidean
Gaussian coordinates. Its Lipschitz constant is `1/√N`, yielding membership in every finite
Gaussian `Lᵖ` space and integrability in both Euclidean and product coordinates. These results
justify ground energy averages for the Gaussian model associated with [GohMuller2026].

## Main statements

* `actualGroundDensity_lipschitz`: For `N > 0`, `actualGroundDensity` is Lipschitz with constant
  `densityLip N`.
* `actualGroundDensity_memLp`: For `N > 0`, `actualGroundDensity` belongs to every finite `Lᵖ`
  space of the standard Gaussian measure.
* `actual_raw_ground_density_integrable`: For `N > 0`, the binary ground energy density of
  `sourceTensor G` is integrable under the product of standard real Gaussian coordinate laws.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal ENNReal RealInnerProductSpace
open Qatlib.Foundations.MatrixAlgebra.TensorDiff
open Qatlib.Papers.OverlapGapGoh26.GaussianBounds.GroundTransport
open Qatlib.Papers.OverlapGapGoh26.GaussianBounds.ActualGround
open Qatlib.Papers.OverlapGapGoh26.OgpBridge.Gaussian

open Qatlib.Papers.OverlapGapGoh26.GaussianBounds.LipschitzMoments
namespace Qatlib.Papers.OverlapGapGoh26.GaussianBounds.GroundMoments

/-- The Euclidean space of real tensor coordinates indexed by maps from `Fin (r+1)` to `Fin N`. -/
abbrev StandardTensorSpace (r N : ℕ) := EuclideanSpace ℝ (Fin (r+1)→Fin N)

/-- The binary ground energy of the scaled source tensor, divided by `N`, in Euclidean tensor
coordinates. -/
def actualGroundDensity {r N : ℕ} (G : StandardTensorSpace r N) : ℝ :=
  binaryGround (sourceTensor (WithLp.ofLp G))/(N:ℝ)

/-- The nonnegative Lipschitz constant `1/√N` for the normalized ground energy. -/
def densityLip (N : ℕ) : ℝ≥0 := ⟨1/Real.sqrt (N:ℝ),by positivity⟩

/-- For `N > 0`, `actualGroundDensity` is Lipschitz with constant `densityLip N`. See
[GohMuller2026]. -/
theorem actualGroundDensity_lipschitz {r N : ℕ} (hN : 0<N) :
    LipschitzWith (densityLip N) (actualGroundDensity (r:=r) (N:=N)) := by
  apply LipschitzWith.of_dist_le_mul
  intro G D
  have h := normalized_binary_ground_transport_sq (r:=r) hN (WithLp.ofLp G) (WithLp.ofLp D)
  have he : (∑ k,(G.ofLp k-D.ofLp k)^2)=‖G-D‖^2 :=
    (EuclideanSpace.real_norm_sq_eq (G-D)).symm
  rw [he] at h
  have hh := Real.abs_le_sqrt h
  rw [Real.sqrt_div (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)] at hh
  change |actualGroundDensity G-actualGroundDensity D|≤(1/Real.sqrt (N:ℝ))*‖G-D‖
  simpa only [actualGroundDensity,div_eq_mul_inv,mul_comm,one_mul] using hh

/-- For `N > 0`, `actualGroundDensity` belongs to every finite `Lᵖ` space of the standard
Gaussian measure. -/
theorem actualGroundDensity_memLp {r N : ℕ} (hN : 0<N) (p : ℝ≥0∞) (hp : p≠∞) :
    MemLp (actualGroundDensity (r:=r) (N:=N)) p (stdGaussian (StandardTensorSpace r N)) :=
  lipschitz_gaussian_memLp _ _ (actualGroundDensity_lipschitz hN) p hp

/-- For `N > 0`, the binary ground energy density is integrable under the standard Euclidean
Gaussian measure. -/
theorem actualGroundDensity_integrable {r N : ℕ} (hN : 0<N) :
    Integrable (actualGroundDensity (r:=r) (N:=N)) (stdGaussian (StandardTensorSpace r N)) :=
  memLp_one_iff_integrable.mp (actualGroundDensity_memLp hN 1 (by norm_num))

/-- The map `WithLp.toLp 2` sends independent standard real Gaussian tensor coordinates to the
standard Gaussian measure on `StandardTensorSpace`. -/
theorem standard_coordinates_preserving (r N : ℕ) :
    MeasurePreserving (WithLp.toLp 2 : ((Fin (r+1)→Fin N)→ℝ) → StandardTensorSpace r N)
      (Measure.pi (fun _ : Fin (r+1)→Fin N => gaussianReal 0 1)) (stdGaussian (StandardTensorSpace r N)) :=
  ⟨by fun_prop,map_pi_eq_stdGaussian⟩

/-- For `N > 0`, the binary ground energy density of `sourceTensor G` is integrable under the
product of standard real Gaussian coordinate laws. -/
theorem actual_raw_ground_density_integrable {r N : ℕ} (hN : 0<N) :
    Integrable (fun G : (Fin (r+1)→Fin N)→ℝ => binaryGround (sourceTensor G)/(N:ℝ))
      (Measure.pi (fun _ : Fin (r+1)→Fin N => gaussianReal 0 1)) :=
  (standard_coordinates_preserving r N).integrable_comp_of_integrable (actualGroundDensity_integrable hN)

end Qatlib.Papers.OverlapGapGoh26.GaussianBounds.GroundMoments
