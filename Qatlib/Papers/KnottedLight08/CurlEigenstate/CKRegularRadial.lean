/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.CurlEigenstate.CKRadialOrigin

import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Regular radial factors of the dipole curl eigenstates

The second radial numerator differentiates to `-u * g(u)`, so its
fifth-order coefficient at the origin follows from the cubic
coefficient of `g`. The two extended radial factors are continuous.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.CurlEigenstate

open Filter Set
open scoped Topology

/-- Differentiating the second radial numerator gives the first
numerator times minus the frequency-radius argument. -/
theorem hasDerivAt_ckCurlNumerator (u : ℝ) :
    HasDerivAt (fun v => v ^ 2 * Real.sin v - 3 * ckKernel v) (-u * ckKernel u) u := by
  refine HasDerivAt.congr_deriv
    (((hasDerivAt_pow 2 u).mul (Real.hasDerivAt_sin u)).sub
      ((hasDerivAt_ckKernel u).const_mul 3)) ?_
  simp only [ckKernel, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  ring

/-- The curl numerator divided by the fifth power of the argument
tends to minus one fifteenth at the origin. -/
theorem tendsto_ckCurlNumerator_div_fifth :
    Tendsto (fun u : ℝ => (u ^ 2 * Real.sin u - 3 * ckKernel u) / u ^ 5)
      (𝓝[≠] 0) (𝓝 (-(1 / 15))) := by
  have hne : ∀ᶠ u : ℝ in 𝓝[≠] 0, u ≠ 0 := self_mem_nhdsWithin
  have hf : Tendsto (fun u : ℝ => u ^ 2 * Real.sin u - 3 * ckKernel u) (𝓝[≠] 0) (𝓝 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    simpa [ckKernel] using (hasDerivAt_ckCurlNumerator 0).continuousAt.tendsto
  have hg : Tendsto (fun u : ℝ => u ^ 5) (𝓝[≠] 0) (𝓝 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    have hc : ContinuousAt (fun u : ℝ => u ^ 5) 0 := by fun_prop
    simpa only [zero_pow (by decide : 5 ≠ 0)] using hc.tendsto
  refine HasDerivAt.lhopital_zero_nhdsNE
    (Eventually.of_forall hasDerivAt_ckCurlNumerator) (g' := fun u : ℝ => 5 * u ^ 4)
    ?_ ?_ hf hg ?_
  · exact Eventually.of_forall fun u => by simpa using hasDerivAt_pow 5 u
  · exact hne.mono fun _ hu => mul_ne_zero (by norm_num) (pow_ne_zero 4 hu)
  · have h : Tendsto (fun u : ℝ => (-(1 / 5)) * (ckKernel u / u ^ 3))
        (𝓝[≠] 0) (𝓝 (-(1 / 15))) := by
      convert tendsto_ckKernel_div_cube.const_mul (-(1 / 5)) using 1
      norm_num
    refine (tendsto_congr' ?_).mp h
    filter_upwards [hne] with u hu
    field_simp [hu]

/-- The regular magnetic dipole radial factor has its cubic limit at zero. -/
noncomputable def ckRadialThree (u : ℝ) : ℝ :=
  if u = 0 then 1 / 3 else ckKernel u / u ^ 3

/-- The regular curl radial factor has its fifth-order limit at zero. -/
noncomputable def ckRadialFive (u : ℝ) : ℝ :=
  if u = 0 then -(1 / 15) else (u ^ 2 * Real.sin u - 3 * ckKernel u) / u ^ 5

/-- Replacing a function's value at the puncture by its two-sided
limit gives continuity there and preserves continuity elsewhere. -/
private theorem continuous_fill_radial_zero {f : ℝ → ℝ} {L : ℝ}
    (hlim : Tendsto f (𝓝[≠] 0) (𝓝 L)) (hf : ∀ u ≠ 0, ContinuousAt f u) :
    Continuous (fun u => if u = 0 then L else f u) := by
  apply continuous_iff_continuousAt.2
  intro u
  by_cases hu : u = 0
  · subst u
    rw [continuousAt_iff_punctured_nhds]
    have hL : (if (0 : ℝ) = 0 then L else f 0) = L := by simp
    rw [hL]
    apply hlim.congr'
    filter_upwards [show ∀ᶠ v : ℝ in 𝓝[≠] 0, v ≠ 0 from self_mem_nhdsWithin] with v hv
    simp [hv]
  · apply (hf u hu).congr
    have hn : ∀ᶠ v : ℝ in 𝓝 u, v ≠ 0 := isOpen_compl_singleton.mem_nhds hu
    filter_upwards [hn] with v hv
    simp [hv]

/-- The extended first radial factor is continuous at every argument. -/
theorem continuous_ckRadialThree : Continuous ckRadialThree := by
  apply continuous_fill_radial_zero tendsto_ckKernel_div_cube
  intro u hu
  exact (hasDerivAt_ckKernel u).continuousAt.div (by fun_prop) (pow_ne_zero 3 hu)

/-- The extended second radial factor is continuous at every argument. -/
theorem continuous_ckRadialFive : Continuous ckRadialFive := by
  apply continuous_fill_radial_zero tendsto_ckCurlNumerator_div_fifth
  intro u hu
  exact (hasDerivAt_ckCurlNumerator u).continuousAt.div (by fun_prop) (pow_ne_zero 5 hu)

end Qatlib.Papers.KnottedLight08.CurlEigenstate
