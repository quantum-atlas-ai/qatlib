/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Gaussian moments of Lipschitz functions and extensions

`lipschitz_gaussian_memLp` places real Lipschitz functions in every finite `Lᵖ` space of the
standard Gaussian measure. `same_constant_gaussian_extension` extends a real function from a
subset while preserving its Lipschitz constant and obtains the same Gaussian moment bounds,
supplying tools for the Gaussian analysis associated with [GohMuller2026].

## Main statements

* `lipschitz_gaussian_memLp`: A real Lipschitz function on `E` belongs to every finite `Lᵖ`
  space of the standard Gaussian measure.
* `same_constant_gaussian_extension`: A real function that is `K` Lipschitz on `S` has a global
  `K` Lipschitz extension agreeing with it on `S` and belonging to every finite Gaussian `Lᵖ`
  space.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal NNReal
namespace Qatlib.Papers.OverlapGapGoh26.GaussianBounds.LipschitzMoments
section GenericGaussian
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A real Lipschitz function on `E` belongs to every finite `Lᵖ` space of the standard Gaussian
measure. -/
theorem lipschitz_gaussian_memLp (K : ℝ≥0) (f : E→ℝ) (hf : LipschitzWith K f)
    (p : ℝ≥0∞) (hp : p≠∞) : MemLp f p (stdGaussian E) := by
  have hg : LipschitzWith K (fun x => f x-f 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Real.dist_eq,sub_sub_sub_cancel_right] using hf.dist_le_mul x y
  have h := hg.comp_memLp (by simp) (IsGaussian.memLp_id (stdGaussian E) p hp)
  have hc : MemLp (fun _ : E => f 0) p (stdGaussian E) := memLp_const _
  convert h.add hc using 1
  funext x
  simp

/-- A real function that is `K` Lipschitz on `S` has a global `K` Lipschitz extension agreeing
with it on `S` and belonging to every finite Gaussian `Lᵖ` space. -/
theorem same_constant_gaussian_extension (K : ℝ≥0) (f : E→ℝ) (S : Set E)
    (hf : LipschitzOnWith K f S) :
    ∃ g : E→ℝ,LipschitzWith K g ∧ Set.EqOn f g S ∧
      ∀ p : ℝ≥0∞,p≠∞→MemLp g p (stdGaussian E) := by
  obtain ⟨g,hg,heq⟩ := hf.extend_real
  exact ⟨g,hg,heq,fun p hp => lipschitz_gaussian_memLp K g hg p hp⟩
end GenericGaussian
end Qatlib.Papers.OverlapGapGoh26.GaussianBounds.LipschitzMoments
