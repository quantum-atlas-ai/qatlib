/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation
import Mathlib.Probability.Moments.SubGaussian

/-!
# Subgaussian bounds for Gaussian tensor evaluations

`independent_linear_subgaussian` controls weighted sums of independent centered Gaussian
coordinates. The factorization `coefficient_sq_sum` identifies the parameter of
`multilinearEval` on unit slot vectors, giving two sided Gaussian tail bounds for the tensor
model used in the analysis of [GohMuller2026].

## Main statements

* `independent_linear_subgaussian`: A weighted sum of independent centered Gaussian coordinates
  of variance `v` is subgaussian with parameter `v * ∑ i, (w i)^2`.
* `unit_multilinear_subgaussian`: Evaluating a Gaussian tensor on unit slot vectors is
  subgaussian with parameter `((N:NNReal)^r)⁻¹`.
* `unit_multilinear_abs_tail`: For unit slot vectors and `ε ≥ 0`, the absolute multilinear
  evaluation has the displayed two sided Gaussian tail with parameter `((N:NNReal)^r)⁻¹`.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation
open Qatlib.Foundations.MatrixAlgebra.TensorDiff

namespace Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Linear

/-- A centered real Gaussian of variance `v` satisfies the subgaussian moment generating
function bound with parameter `v`. -/
theorem gaussian_id_subgaussian (v : NNReal) : HasSubgaussianMGF id v (gaussianReal 0 v) where
  integrable_exp_mul t := integrable_exp_mul_gaussianReal t
  mgf_le t := by rw [mgf_id_gaussianReal]; simp

/-- A weighted sum of independent centered Gaussian coordinates of variance `v` is subgaussian
with parameter `v * ∑ i, (w i)^2`. -/
theorem independent_linear_subgaussian {I : Type} [Fintype I] [DecidableEq I]
    (v : NNReal) (w : I → ℝ) :
    HasSubgaussianMGF (fun J : I → ℝ => ∑ i, w i*J i)
      (∑ i, (NNReal.mk (w i^2) (sq_nonneg (w i)))*v)
      (Measure.pi (fun _ : I => gaussianReal 0 v)) := by
  have hi : iIndepFun (fun i (J : I → ℝ) => w i*J i)
      (Measure.pi (fun _ : I => gaussianReal 0 v)) := iIndepFun_pi (fun _ => by fun_prop)
  apply HasSubgaussianMGF.sum_of_iIndepFun hi
  intro i _
  have hm := (measurePreserving_eval (fun _ : I => gaussianReal 0 v) i).map_eq
  have h := gaussian_id_subgaussian v
  rw [← hm] at h
  have hc : HasSubgaussianMGF (fun J : I → ℝ => J i) v
      (Measure.pi (fun _ : I => gaussianReal 0 v)) := by
    simpa only [Function.comp_def, id_eq] using
      (HasSubgaussianMGF.of_map (X:=id) (Y:=Function.eval i)
        (μ:=Measure.pi (fun _ : I => gaussianReal 0 v)) (c:=v)
        (measurable_pi_apply i).aemeasurable h)
  exact hc.const_mul (w i)

/-- For a subgaussian random variable with parameter `c` and `ε ≥ 0`, the probability of
absolute value at least `ε` is at most `2 exp(-ε²/(2c))`. -/
theorem subgaussian_abs_tail {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} {c : NNReal} (hX : HasSubgaussianMGF X c P)
    (ε : ℝ) (hε : 0≤ε) : P.real {ω | ε≤|X ω|}≤2*Real.exp (-ε^2/(2*c)) := by
  have hs : {ω | ε≤|X ω|}={ω | ε≤X ω} ∪ {ω | ε≤-X ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_union, le_abs]
  rw [hs]
  exact (measureReal_union_le _ _).trans
      ((add_le_add (hX.measure_ge_le hε) (hX.neg.measure_ge_le hε)).trans_eq (by ring))

/-- The multilinear contraction of a tensor with one real coordinate vector in each slot. -/
def multilinearEval {q N : ℕ} (J : Tensor q N) (z : Fin q → Fin N → ℝ) : ℝ :=
  ∑ k, J k*∏ a, z a (k a)

/-- The sum of squared tensor product coefficients equals the product of the squared Euclidean
norms of the slot vectors. -/
theorem coefficient_sq_sum {q N : ℕ} (z : Fin q → Fin N → ℝ) :
    (∑ k : Fin q → Fin N, (∏ a, z a (k a))^2)=∏ a, ∑ i, z a i^2 := by
  simp_rw [← Finset.prod_pow]
  exact (Fintype.prod_sum (fun a i => z a i^2)).symm

/-- Evaluating a Gaussian tensor on unit slot vectors is subgaussian with parameter
`((N:NNReal)^r)⁻¹`. -/
theorem unit_multilinear_subgaussian {r N : ℕ} (z : Fin (r+1) → Fin N → ℝ)
    (hz : ∀ a, ∑ i, z a i^2=1) :
    HasSubgaussianMGF (fun J : Tensor (r+1) N => multilinearEval J z)
      (((N:NNReal)^r)⁻¹) (gaussianTensorLaw r N) := by
  have h :=
      independent_linear_subgaussian (((N:NNReal)^r)⁻¹)
      (fun k : Fin (r+1) → Fin N => ∏ a, z a (k a))
  have hc : (∑ k : Fin (r+1) → Fin N,
      (NNReal.mk ((∏ a, z a (k a))^2) (sq_nonneg _))*((N:NNReal)^r)⁻¹)=((N:NNReal)^r)⁻¹ := by
    rw [← Finset.sum_mul]
    have hw : (∑ k : Fin (r+1) → Fin N, (NNReal.mk ((∏ a, z a (k a))^2) (sq_nonneg _)))=1 := by
      apply NNReal.coe_injective
      simp only [NNReal.coe_sum, NNReal.coe_mk, NNReal.coe_one]
      rw [coefficient_sq_sum]
      simp [hz]
    rw [hw, one_mul]
  rw [hc] at h
  simpa only [gaussianTensorLaw, multilinearEval, mul_comm] using h

/-- For unit slot vectors and `ε ≥ 0`, the absolute multilinear evaluation has the displayed two
sided Gaussian tail with parameter `((N:NNReal)^r)⁻¹`. -/
theorem unit_multilinear_abs_tail {r N : ℕ} (z : Fin (r+1) → Fin N → ℝ)
    (hz : ∀ a, ∑ i, z a i^2=1) (ε : ℝ) (hε : 0≤ε) :
    (gaussianTensorLaw r N).real {J | ε≤|multilinearEval J z|}≤
      2*Real.exp (-ε^2/(2*(((N:NNReal)^r)⁻¹:ℝ))) :=
  subgaussian_abs_tail (unit_multilinear_subgaussian z hz) ε hε

end Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Linear
