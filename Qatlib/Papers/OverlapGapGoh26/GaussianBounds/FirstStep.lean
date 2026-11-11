/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.GaussianBounds.LinearTail

/-!
# Gaussian energy bounds at the first AMP step

`cube_energy_subgaussian` bounds the subgaussian parameter of the energy of any fixed cube
vector by `N`. The explicit formula `actual_first_output` shows that the first AMP output is
independent of the coupling tensor, giving a Gaussian tail for its energy density in the model
of [GohMuller2026].

## Main statements

* `cube_energy_subgaussian`: For `N > 0`, the Gaussian tensor energy of a fixed vector in
  `[-1,1]^N` has subgaussian parameter `N`.
* `actual_first_output`: For positive interaction degree, the first AMP output is the
  coordinatewise clipped seed multiplied by the initial catalyst coefficient, with the nested
  clipping shown in the formula.
* `actual_first_amp_density_tail`: For positive `r` and `N` and `ε ≥ 0`, the absolute first step
  AMP energy density exceeds `ε` with probability at most `2 exp(-ε²N/2)`.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation
open Qatlib.Foundations.MatrixAlgebra.TensorDiff Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Linear
open Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Program

namespace Qatlib.Papers.OverlapGapGoh26.GaussianBounds.FirstStep

/-- A subgaussian moment generating function bound remains valid when its nonnegative parameter
is increased. -/
theorem subgaussian_parameter_mono {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {c d : NNReal} (h : HasSubgaussianMGF X c P) (hcd : c≤d) :
    HasSubgaussianMGF X d P where
  integrable_exp_mul := h.integrable_exp_mul
  mgf_le t := (h.mgf_le t).trans (Real.exp_le_exp.mpr (by exact_mod_cast (by gcongr : (c:ℝ)*t^2/2≤(d:ℝ)*t^2/2)))

/-- For `N > 0`, the Gaussian tensor energy of a fixed vector in `[-1,1]^N` has subgaussian
parameter `N`. -/
theorem cube_energy_subgaussian {r N : ℕ} (hN : 0<N) (u : Fin N → ℝ)
    (hu : ∀ i, u i ∈ Set.Icc (-1:ℝ) 1) :
    HasSubgaussianMGF (fun A : Tensor (r+1) N => tensorEnergy A u)
      (N:NNReal) (gaussianTensorLaw r N) := by
  let w := fun k : Fin (r+1) → Fin N => ∏ a, u (k a)
  have h := independent_linear_subgaussian (((N:NNReal)^r)⁻¹) w
  have hu2 : (∑ i, u i^2)≤(N:ℝ) := by
    calc
      _ ≤ ∑ _i : Fin N, (1:ℝ) := Finset.sum_le_sum (fun i _ => by have hi := hu i; nlinarith [hi.1,hi.2])
      _ = _ := by simp
  have hw : (∑ k, w k^2)≤(N:ℝ)^(r+1) := by
    unfold w
    rw [coefficient_sq_sum (fun _ : Fin (r+1) => u)]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_pow_left₀ (by positivity) hu2 _
  have hc : (∑ k, NNReal.mk (w k^2) (sq_nonneg _)*((N:NNReal)^r)⁻¹)≤(N:NNReal) := by
    apply NNReal.coe_le_coe.mp
    simp only [NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_inv, NNReal.coe_pow,
        NNReal.coe_natCast]
    rw [← Finset.sum_mul]
    calc
      _ ≤ (N:ℝ)^(r+1)*((N:ℝ)^r)⁻¹ := mul_le_mul_of_nonneg_right hw (by positivity)
      _ = _ := by
        rw [pow_succ]
        have hn : (N:ℝ)≠0 := by positivity
        field_simp
  have hh := subgaussian_parameter_mono h hc
  simpa only [gaussianTensorLaw, tensorEnergy, w, mul_comm] using hh

/-- For positive interaction degree, the first AMP output is the coordinatewise clipped seed
multiplied by the initial catalyst coefficient, with the nested clipping shown in the
formula. -/
theorem actual_first_output {r N : ℕ} (hr : 0<r) (M : ℝ)
    (J : Fin N → (Fin r → Fin N) → ℝ) (seed : Fin N → ℝ) (s : ℕ → ℝ) :
    ampOutput M J seed s 1=fun i => clip 1 (clip M (clip M (seed i)*(s 0)^2*(1-s 0))) := by
  ext i
  have hz : spinReadout s 0 (ampHistory M J seed s 0)=fun _ => 0 := by
    funext j
    exact fCoord_zero s 0
  change clip 1 (ampHistory M J seed s (0+1) (Fin.last (0+1)) i)=_
  rw [actual_amp_step, hz]
  have hi : (∑ k : Fin r → Fin N, J i k*∏ _a : Fin r, (0:ℝ))=0 := by
    apply Finset.sum_eq_zero
    intro k _
    have hp : (∏ _a : Fin r, (0:ℝ))=0 := by simp [Nat.ne_of_gt hr]
    rw [hp, mul_zero]
  rw [hi]
  simp only [FCoord, ampHistory, zero_add]

/-- For positive `r` and `N` and `ε ≥ 0`, the absolute first step AMP energy density exceeds `ε`
with probability at most `2 exp(-ε²N/2)`. -/
theorem actual_first_amp_density_tail {r N : ℕ} (hr : 0<r) (hN : 0<N)
    (M : ℝ) (seed : Fin N → ℝ) (s : ℕ → ℝ) (ε : ℝ) (hε : 0≤ε) :
    (gaussianTensorLaw r N).real {A | ε≤|tensorEnergy A (ampOutput M (rowTensor A) seed s 1)/(N:ℝ)|}≤
      2*Real.exp (-ε^2*(N:ℝ)/2) := by
  simp_rw [actual_first_output hr]
  let u : Fin N → ℝ := fun i => clip 1 (clip M (clip M (seed i)*(s 0)^2*(1-s 0)))
  have hu : ∀ i, u i ∈ Set.Icc (-1:ℝ) 1 := fun i => clip_mem 1 (by norm_num) _
  have ht := subgaussian_abs_tail (cube_energy_subgaussian (r:=r) hN u hu) (ε*(N:ℝ)) (by positivity)
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have he : {A : Tensor (r+1) N | ε≤|tensorEnergy A u/(N:ℝ)|}=
      {A | ε*(N:ℝ)≤|tensorEnergy A u|} := by
    ext A
    simp only [Set.mem_setOf_eq, abs_div, abs_of_pos hn, le_div_iff₀ hn]
  change (gaussianTensorLaw r N).real {A | ε≤|tensorEnergy A u/(N:ℝ)|}≤_
  rw [he]
  refine ht.trans_eq ?_
  congr 2
  simp only [NNReal.coe_natCast]
  field_simp

end Qatlib.Papers.OverlapGapGoh26.GaussianBounds.FirstStep
