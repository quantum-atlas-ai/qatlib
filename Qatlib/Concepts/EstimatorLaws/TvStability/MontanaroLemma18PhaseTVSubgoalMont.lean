/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EstimatorLaws.TvStability.MontanaroLemma18PhaseTVSubgoalStat
import Qatlib.Concepts.AEMeanReadout.AELawStability.MontanaroClaim17Mont
import Qatlib.Concepts.EstimatorLaws.TvStability.Lemma18PhaseTVAux
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.PureStateTV

/-!
# Phase-readout total-variation stability

Proves the phase-kernel stability contract underlying the Lemma 18 perturbation analysis in
[Montanaro2015]. The proof combines a circular phase-distance estimate, the Dirichlet overlap
formula, pure-state measurement stability, and the arcsine estimate for squared sine amplitudes.

## Main statements

* `montanaroLemma18PhaseTVSubgoal` bounds phase-label total variation by `π² * M / (2 * sqrt 3)`
  times the square root of the squared-sine difference.

## References

* [Montanaro, 2015][Montanaro2015]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.SpectralFilter.PhaseReadout

open Qatlib.Concepts.AEMeanReadout.AELawStability
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

namespace Qatlib.Concepts.EstimatorLaws.TvStability

open Matrix
open scoped Classical BigOperators

/-- Proves the phase-kernel total-variation bound used in the Lemma 18 stability analysis of
[Montanaro2015], for phases in `[0, π / 2]` and grid size at least one. -/
theorem montanaroLemma18PhaseTVSubgoal : MontanaroLemma18PhaseTVSubgoal := by
  intro M hM ω₁ ω₂ hω₁0 hω₁1 hω₂0 hω₂1
  have hM0 : 0 < M := by omega
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM0
  let z₀ : Fin M := ⟨0, hM0⟩
  let δ := phaseDistance ω₁ ω₂
  let F := ‖Inner (offGridPhase M ω₁) (offGridPhase M ω₂)‖
  let Δ := |(Real.sin ω₁) ^ 2 - (Real.sin ω₂) ^ 2|
  have hδnonneg : 0 ≤ δ := abs_nonneg _
  have hR : 0 ≤ (Real.pi ^ 2 / (2 * Real.sqrt 3)) * (M : ℝ) * Real.sqrt Δ := by positivity
  have hsin₁ : 0 ≤ Real.sin ω₁ := Real.sin_nonneg_of_mem_Icc ⟨hω₁0, by linarith [Real.pi_pos]⟩
  have hsin₂ : 0 ≤ Real.sin ω₂ := Real.sin_nonneg_of_mem_Icc ⟨hω₂0, by linarith [Real.pi_pos]⟩
  have h17 := montanaroClaim17 (Real.sin ω₁) (Real.sin ω₂)
    hsin₁ (Real.sin_le_one _) hsin₂ (Real.sin_le_one _)
  rw [Real.arcsin_sin (by linarith [Real.pi_pos]) hω₁1,
    Real.arcsin_sin (by linarith [Real.pi_pos]) hω₂1] at h17
  have hδangle : δ ≤ (Real.pi / 2) * Real.sqrt Δ := by
    have hd : δ ≤ |ω₁ - ω₂| := by
      simpa only [Int.cast_zero, sub_zero] using! phaseDistance_le_integer_distance ω₁ ω₂ 0
    exact hd.trans h17
  by_cases hδ0 : δ = 0
  · let c : ℤ := ⌊ω₁ - ω₂ + 1 / 2⌋
    have hd : ω₁ - ω₂ - (c : ℝ) = 0 := abs_eq_zero.mp hδ0
    have he : ω₁ = ω₂ + (c : ℝ) := by linarith
    have hk (z : Fin M) : qpeKernel M ω₁ z = qpeKernel M ω₂ z := by
      rw [he, qpeKernel_int_add]
    simp only [hk, sub_self, abs_zero, Finset.sum_const_zero, mul_zero]
    exact hR
  have hδpos : 0 < δ := lt_of_le_of_ne hδnonneg (Ne.symm hδ0)
  have htv := pureState_born_tv_le_sqrt_fidelity (QFTMatrix M)ᴴ
    (conjTranspose_mem_unitaryGroup (qftMatrix_unitary hM0))
    (offGridPhase M ω₁) (offGridPhase M ω₂)
    (offgrid_phase_kernel_formula M ω₁ z₀ hM0).2.2
    (offgrid_phase_kernel_formula M ω₂ z₀ hM0).2.2
  change (1 / 2 : ℝ) * ∑ z : Fin M,
    |‖qpeKernel M ω₁ z‖ ^ 2 - ‖qpeKernel M ω₂ z‖ ^ 2| ≤ Real.sqrt (1 - F ^ 2) at htv
  have hF : F = |Real.sin (Real.pi * M * δ)| / ((M : ℝ) * Real.sin (Real.pi * δ)) :=
    offGridPhase_inner_norm_dirichlet M hM0 ω₁ ω₂ hδpos
  have hsinδ : 0 < Real.sin (Real.pi * δ) := Real.sin_pos_of_pos_of_lt_pi
    (mul_pos Real.pi_pos hδpos) (by nlinarith [phaseDistance_le_half ω₁ ω₂, Real.pi_pos])
  have hx : 0 < Real.pi * (M : ℝ) * δ := by positivity
  have hsine : Real.sin (Real.pi * δ) ≤ Real.pi * δ := by
    exact (le_abs_self _).trans ((Real.abs_sin_le_abs (x := Real.pi * δ)).trans_eq
      (abs_of_pos (mul_pos Real.pi_pos hδpos)))
  have hden : (M : ℝ) * Real.sin (Real.pi * δ) ≤ Real.pi * M * δ := by nlinarith
  have hlower : |Real.sin (Real.pi * M * δ)| / (Real.pi * M * δ) ≤ F := by
    rw [hF]
    exact div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos hMr hsinδ) hden
  have hsq := pow_le_pow_left₀ (by positivity) hlower 2
  have hsinc := sinc_square_defect_le (Real.pi * M * δ) hx
  have habs : (|Real.sin (Real.pi * M * δ)| / (Real.pi * M * δ)) ^ 2 =
      (Real.sin (Real.pi * M * δ) / (Real.pi * M * δ)) ^ 2 := by rw [div_pow, sq_abs, ← div_pow]
  rw [habs] at hsq
  have hdefect : 1 - F ^ 2 ≤ (Real.pi * M * δ) ^ 2 / 3 := by linarith
  have hsqrt : Real.sqrt (1 - F ^ 2) ≤ (Real.pi * M * δ) / Real.sqrt 3 := by
    have h := Real.sqrt_le_sqrt hdefect
    simpa only [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_pos hx] using! h
  apply htv.trans
  calc
    _ ≤ (Real.pi * M * δ) / Real.sqrt 3 := hsqrt
    _ = (Real.pi * M / Real.sqrt 3) * δ := by ring
    _ ≤ (Real.pi * M / Real.sqrt 3) * ((Real.pi / 2) * Real.sqrt Δ) :=
      mul_le_mul_of_nonneg_left hδangle (by positivity)
    _ = _ := by ring

end Qatlib.Concepts.EstimatorLaws.TvStability
