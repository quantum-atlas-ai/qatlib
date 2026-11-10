/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Endpoint.Independent
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.RawInput
open Qatlib.Papers.OverlapGapGoh26.GaussianBounds.TensorMoments
namespace Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Endpoint

theorem actual_spin_integrable {r N : ℕ} (s : ℕ→ℝ) (T : ℕ) :
    Integrable (spin (r:=r) (N:=N) s T) (stdGaussian (Input r N)) := by
  apply Integrable.of_eval_piLp
  intro i
  exact (spin_component_memLp s T i).integrable (by norm_num)

theorem actual_spin_mean_zero {r N : ℕ} (hr : Odd r) (s : ℕ→ℝ) (T : ℕ) :
    (∫ x:Input r N,spin s T x ∂stdGaussian (Input r N))=0 := by
  ext i
  rw [eval_integral_piLp (fun j=>(spin_component_memLp (r:=r) s T j).integrable (by norm_num)) i,
    spin_component_mean_zero hr]
  rfl

theorem endpointConstant_nonneg (r T : ℕ) : 0≤endpointConstant r T := by
  unfold endpointConstant uniformMomentConstant
    Qatlib.Foundations.ProbabilityCore.GaussPoincare.Moments.shiftedConstant
  positivity

theorem uniform_independent_endpoint_tail {r : ℕ} (hr : Odd r) (T : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ N : ℕ,0<N→∀ s:ℕ→ℝ,
      (∀ j≤T,s j∈Set.Icc (0:ℝ) 1)→∀ δ:ℝ,0<δ→
      ((stdGaussian (Input r N)).prod (stdGaussian (Input r N))).real
        {z | δ≤|overlap s T z|}≤C/((N:ℝ)*δ^2) := by
  exact ⟨endpointConstant r T,endpointConstant_nonneg r T,
    fun N hN s hs δ hδ=>independent_endpoint_tail hr hN s hs δ hδ⟩
end Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Endpoint
