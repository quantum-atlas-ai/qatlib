/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Endpoint.Independent
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Uniform independent-endpoint tail estimates

Packages spin integrability, vanishing Gaussian mean for odd interaction degree, and the
independent-endpoint tail estimate into a form uniform in the dimension and bounded schedule.
The constants depend only on the degree and time horizon in the setting of [GohMuller2026].

## Main statements

* `actual_spin_mean_zero`: gives the vector-valued Gaussian mean.
* `uniform_independent_endpoint_tail`: provides a dimension-uniform constant in the overlap tail
  bound.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.RawInput
open Qatlib.Papers.OverlapGapGoh26.GaussianBounds.TensorMoments
namespace Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Endpoint

/-- The actual spin vector is integrable under the standard Gaussian input law. -/
theorem actual_spin_integrable {r N : ℕ} (s : ℕ→ℝ) (T : ℕ) :
    Integrable (spin (r:=r) (N:=N) s T) (stdGaussian (Input r N)) := by
  apply Integrable.of_eval_piLp
  intro i
  exact (spin_component_memLp s T i).integrable (by norm_num)

/-- For odd `r`, the actual spin vector has zero mean under the standard Gaussian input law. -/
theorem actual_spin_mean_zero {r N : ℕ} (hr : Odd r) (s : ℕ→ℝ) (T : ℕ) :
    (∫ x:Input r N,spin s T x ∂stdGaussian (Input r N))=0 := by
  ext i
  rw [eval_integral_piLp (fun j=>(spin_component_memLp (r:=r) s T j).integrable (by norm_num)) i,
    spin_component_mean_zero hr]
  rfl

/-- The endpoint constant is nonnegative. -/
theorem endpointConstant_nonneg (r T : ℕ) : 0≤endpointConstant r T := by
  unfold endpointConstant uniformMomentConstant
    Qatlib.Foundations.ProbabilityCore.GaussPoincare.Moments.shiftedConstant
  positivity

/-- For odd `r` and fixed horizon `T`, there is a nonnegative constant independent of dimension
and schedule such that the independent-endpoint overlap tail is at most `C / (N * δ ^ 2)`
for positive `N`, positive `δ`, and schedules in `[0, 1]` through `T`. -/
theorem uniform_independent_endpoint_tail {r : ℕ} (hr : Odd r) (T : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ N : ℕ,0<N→∀ s:ℕ→ℝ,
      (∀ j≤T,s j∈Set.Icc (0:ℝ) 1)→∀ δ:ℝ,0<δ→
      ((stdGaussian (Input r N)).prod (stdGaussian (Input r N))).real
        {z | δ≤|overlap s T z|}≤C/((N:ℝ)*δ^2) := by
  exact ⟨endpointConstant r T,endpointConstant_nonneg r T,
    fun N hN s hs δ hδ=>independent_endpoint_tail hr hN s hs δ hδ⟩
end Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Endpoint
