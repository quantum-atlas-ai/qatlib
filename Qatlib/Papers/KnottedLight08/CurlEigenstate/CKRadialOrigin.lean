/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.CurlEigenstate.CKModes

import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Radial normalization at the dipole origin

The first radial numerator vanishes cubically with coefficient one
third. The leading cubic terms in the curl's second radial numerator
cancel. Both facts are derived from the differentiable sine kernel.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.CurlEigenstate

open Filter Set
open scoped Topology

/-- The radial dipole numerator divided by the cube of its argument
tends to one third at the origin. -/
theorem tendsto_ckKernel_div_cube :
    Tendsto (fun u : ℝ => ckKernel u / u ^ 3) (𝓝[≠] 0) (𝓝 (1 / 3)) := by
  have hne : ∀ᶠ u : ℝ in 𝓝[≠] 0, u ≠ 0 := self_mem_nhdsWithin
  have hf : Tendsto ckKernel (𝓝[≠] 0) (𝓝 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    simpa [ckKernel] using (hasDerivAt_ckKernel 0).continuousAt.tendsto
  have hg : Tendsto (fun u : ℝ => u ^ 3) (𝓝[≠] 0) (𝓝 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    have hc : ContinuousAt (fun u : ℝ => u ^ 3) 0 := by fun_prop
    simpa only [zero_pow (by decide : 3 ≠ 0)] using hc.tendsto
  have hsinc : Tendsto Real.sinc (𝓝[≠] 0) (𝓝 1) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    simpa only [Real.sinc_zero] using
      (Real.continuous_sinc.continuousAt : ContinuousAt Real.sinc 0).tendsto
  refine HasDerivAt.lhopital_zero_nhdsNE
    (Eventually.of_forall hasDerivAt_ckKernel)
    (g' := fun u : ℝ => 3 * u ^ 2) ?_ ?_ hf hg ?_
  · exact Eventually.of_forall fun u => by simpa using hasDerivAt_pow 3 u
  · exact hne.mono fun _ hu => mul_ne_zero (by norm_num) (pow_ne_zero 2 hu)
  · have h : Tendsto (fun u : ℝ => (1 / 3) * Real.sinc u) (𝓝[≠] 0) (𝓝 (1 / 3)) := by
      simpa only [mul_one] using hsinc.const_mul (1 / 3)
    refine (tendsto_congr' ?_).mp h
    filter_upwards [hne] with u hu
    rw [Real.sinc_of_ne_zero hu]
    field_simp [hu]

/-- The second dipole radial numerator has no surviving cubic term. -/
theorem tendsto_ckCurlNumerator_div_cube :
    Tendsto (fun u : ℝ => (u ^ 2 * Real.sin u - 3 * ckKernel u) / u ^ 3)
      (𝓝[≠] 0) (𝓝 0) := by
  have hne : ∀ᶠ u : ℝ in 𝓝[≠] 0, u ≠ 0 := self_mem_nhdsWithin
  have hsinc : Tendsto Real.sinc (𝓝[≠] 0) (𝓝 1) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    simpa only [Real.sinc_zero] using
      (Real.continuous_sinc.continuousAt : ContinuousAt Real.sinc 0).tendsto
  have h : Tendsto (fun u : ℝ => Real.sinc u - 3 * (ckKernel u / u ^ 3)) (𝓝[≠] 0) (𝓝 0) := by
    simpa using hsinc.sub (tendsto_ckKernel_div_cube.const_mul 3)
  refine (tendsto_congr' ?_).mp h
  filter_upwards [hne] with u hu
  rw [Real.sinc_of_ne_zero hu]
  field_simp [hu]

end Qatlib.Papers.KnottedLight08.CurlEigenstate
