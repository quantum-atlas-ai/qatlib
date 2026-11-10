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
set_option warningAsError false

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

abbrev StandardTensorSpace (r N : ℕ) := EuclideanSpace ℝ (Fin (r+1)→Fin N)

def actualGroundDensity {r N : ℕ} (G : StandardTensorSpace r N) : ℝ :=
  binaryGround (sourceTensor (WithLp.ofLp G))/(N:ℝ)

def densityLip (N : ℕ) : ℝ≥0 := ⟨1/Real.sqrt (N:ℝ),by positivity⟩

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

theorem actualGroundDensity_memLp {r N : ℕ} (hN : 0<N) (p : ℝ≥0∞) (hp : p≠∞) :
    MemLp (actualGroundDensity (r:=r) (N:=N)) p (stdGaussian (StandardTensorSpace r N)) :=
  lipschitz_gaussian_memLp _ _ (actualGroundDensity_lipschitz hN) p hp

theorem actualGroundDensity_integrable {r N : ℕ} (hN : 0<N) :
    Integrable (actualGroundDensity (r:=r) (N:=N)) (stdGaussian (StandardTensorSpace r N)) :=
  memLp_one_iff_integrable.mp (actualGroundDensity_memLp hN 1 (by norm_num))

theorem standard_coordinates_preserving (r N : ℕ) :
    MeasurePreserving (WithLp.toLp 2 : ((Fin (r+1)→Fin N)→ℝ) → StandardTensorSpace r N)
      (Measure.pi (fun _ : Fin (r+1)→Fin N => gaussianReal 0 1)) (stdGaussian (StandardTensorSpace r N)) :=
  ⟨by fun_prop,map_pi_eq_stdGaussian⟩

theorem actual_raw_ground_density_integrable {r N : ℕ} (hN : 0<N) :
    Integrable (fun G : (Fin (r+1)→Fin N)→ℝ => binaryGround (sourceTensor G)/(N:ℝ))
      (Measure.pi (fun _ : Fin (r+1)→Fin N => gaussianReal 0 1)) :=
  (standard_coordinates_preserving r N).integrable_comp_of_integrable (actualGroundDensity_integrable hN)

end Qatlib.Papers.OverlapGapGoh26.GaussianBounds.GroundMoments
