/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ImaginaryFlow.GroundLimit.SpectralDamping

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.ImaginaryFlow.GroundLimit
open Matrix NormedSpace Filter
open scoped BigOperators Topology Classical

section FiniteDamping
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def retainedGround {ι : Type*} [Fintype ι] (eig : ι → ℝ) (c : ι → ℝ)
    (v : ι → E) (i0 : ι) : E :=
  ∑ i, if eig i = eig i0 then c i • v i else 0

theorem gaugeFixedState_tendsto_groundspace {ι : Type*} [Fintype ι]
    (eig : ι → ℝ) (c : ι → ℝ) (v : ι → E) (i0 : ι)
    (hmin : ∀ i, eig i0 ≤ eig i) :
    Tendsto (gaugeFixedState eig c v i0) atTop (𝓝 (retainedGround eig c v i0)) := by
  unfold gaugeFixedState retainedGround
  apply tendsto_finsetSum
  intro i _
  by_cases hi : eig i = eig i0
  · simp only [hi, sub_self, neg_zero, zero_mul, Real.exp_zero, one_mul, if_true]
    exact tendsto_const_nhds
  · have hgap : 0 < eig i - eig i0 := sub_pos.mpr (lt_of_le_of_ne (hmin i) (Ne.symm hi))
    have hinner : Tendsto (fun t : ℝ => -(eig i - eig i0) * t) atTop atBot := by
      exact (Filter.tendsto_const_mul_atBot_of_neg (by linarith : -(eig i - eig i0) < 0)).mpr tendsto_id
    have he : Tendsto (fun t : ℝ => Real.exp (-(eig i - eig i0) * t)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp hinner
    simpa only [if_neg hi, zero_mul, zero_smul] using
      (he.mul (tendsto_const_nhds (x := c i))).smul (tendsto_const_nhds (x := v i))

theorem normalized_spectral_groundspace {ι : Type*} [Fintype ι]
    (eig : ι → ℝ) (c : ι → ℝ) (v : ι → E) (i0 : ι)
    (hmin : ∀ i, eig i0 ≤ eig i) (hr : retainedGround eig c v i0 ≠ 0) :
    Tendsto (fun t : ℝ => ‖imaginaryTimeState eig c v t‖⁻¹ • imaginaryTimeState eig c v t)
      atTop (𝓝 (‖retainedGround eig c v i0‖⁻¹ • retainedGround eig c v i0)) := by
  have h := gaugeFixedState_tendsto_groundspace eig c v i0 hmin
  have hi := h.norm.inv₀ (norm_ne_zero_iff.mpr hr)
  have hs := hi.smul h
  refine Tendsto.congr' ?_ hs
  filter_upwards with t
  rw [imaginaryTimeState_eq_exp_smul_gaugeFixed, inv_norm_smul_eq (Real.exp_pos _)]

end FiniteDamping

end Qatlib.Concepts.ImaginaryFlow.GroundLimit
