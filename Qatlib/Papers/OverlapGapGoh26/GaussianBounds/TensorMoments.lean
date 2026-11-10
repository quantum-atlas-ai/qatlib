/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.GaussianBounds.NormalizedNorm
import Qatlib.Foundations.ProbabilityCore.GaussPoincare.Moments
set_option warningAsError false
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical NNReal
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation
namespace Qatlib.Papers.OverlapGapGoh26.GaussianBounds.TensorMoments

def uniformMomentConstant (r p : ℕ) : ℝ :=
  Qatlib.Foundations.ProbabilityCore.GaussPoincare.Moments.shiftedConstant (2*(1+8*(r+1):ℝ)^(r+1)) p

theorem actual_normalized_moment {r N : ℕ} (hr : 0<r) (hN : 0<N) (p : ℕ) :
    Integrable (fun A=>(normalizedNorm (r:=r) (N:=N) A)^p) (gaussianTensorLaw r N) ∧
      (∫ A,(normalizedNorm (r:=r) (N:=N) A)^p ∂gaussianTensorLaw r N) ≤
        (Qatlib.Foundations.ProbabilityCore.GaussPoincare.Moments.momentCap (2*(1+8*(r+1):ℝ)^(r+1)) p).toReal := by
  exact Qatlib.Foundations.ProbabilityCore.GaussPoincare.Moments.moment_from_tail (gaussianTensorLaw r N) normalizedNorm
    (normalizedNorm_continuous r N).measurable normalizedNorm_nonneg _ (by positivity)
    (fun t ht=>normalized_tail hr hN t ht) p

theorem actual_shifted_moment {r N : ℕ} (hr : 0<r) (hN : 0<N) (p : ℕ) :
    Integrable (fun A=>(1+normalizedNorm (r:=r) (N:=N) A)^p) (gaussianTensorLaw r N) ∧
      (∫ A,(1+normalizedNorm (r:=r) (N:=N) A)^p ∂gaussianTensorLaw r N) ≤
        uniformMomentConstant r p := by
  exact Qatlib.Foundations.ProbabilityCore.GaussPoincare.Moments.shifted_moment_from_tail (gaussianTensorLaw r N) normalizedNorm
    (normalizedNorm_continuous r N).measurable normalizedNorm_nonneg _ (by positivity)
    (fun t ht=>normalized_tail hr hN t ht) p

theorem uniform_shifted_moments {r : ℕ} (hr : 0<r) (p : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ N : ℕ,0<N→
      Integrable (fun A=>(1+normalizedNorm (r:=r) (N:=N) A)^p) (gaussianTensorLaw r N) ∧
      (∫ A,(1+normalizedNorm (r:=r) (N:=N) A)^p ∂gaussianTensorLaw r N)≤C := by
  refine ⟨uniformMomentConstant r p,?_,fun N hN=>actual_shifted_moment hr hN p⟩
  unfold uniformMomentConstant Qatlib.Foundations.ProbabilityCore.GaussPoincare.Moments.shiftedConstant
  positivity

theorem actual_gradient_budget_moment {r N : ℕ} (hr : 0<r) (hN : 0<N) (T : ℕ) :
    Integrable (fun A=>(1+normalizedNorm (r:=r) (N:=N) A)^(2*T+2)) (gaussianTensorLaw r N) ∧
      (∫ A,(1+normalizedNorm (r:=r) (N:=N) A)^(2*T+2) ∂gaussianTensorLaw r N) ≤
        uniformMomentConstant r (2*T+2) := actual_shifted_moment hr hN (2*T+2)
end Qatlib.Papers.OverlapGapGoh26.GaussianBounds.TensorMoments
