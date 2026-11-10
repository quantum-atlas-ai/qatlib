/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EstimatorLaws.TvStability.MontanaroLemma18AELawTVSubgoalStat
import Qatlib.Concepts.AEMeanReadout.AELawStability.MontanaroClaim17Mont
import Qatlib.Concepts.EstimatorLaws.TvStability.Lemma18PhaseTVAux
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.PureStateTV
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout

open Qatlib.Concepts.AEMeanReadout.AELawStability
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

namespace Qatlib.Concepts.EstimatorLaws.TvStability
open Matrix
open scoped Classical BigOperators

private theorem phase_label_tv (M : ℕ) (hM : 2 ≤ M) (ω₁ ω₂ : ℝ) :
    (1 / 2 : ℝ) * ∑ z : Fin M,
      |‖qpeKernel M ω₁ z‖ ^ 2 - ‖qpeKernel M ω₂ z‖ ^ 2| ≤
      (Real.pi * M / Real.sqrt 3) * |ω₁ - ω₂| := by
  have hM0 : 0 < M := by omega
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM0
  let z₀ : Fin M := ⟨0, hM0⟩
  let δ := phaseDistance ω₁ ω₂
  let F := ‖Inner (offGridPhase M ω₁) (offGridPhase M ω₂)‖
  have hδnonneg : 0 ≤ δ := abs_nonneg _
  have hR : 0 ≤ (Real.pi * M / Real.sqrt 3) * |ω₁ - ω₂| := by positivity
  have hδangle : δ ≤ |ω₁ - ω₂| := by
    simpa only [Int.cast_zero, sub_zero] using! phaseDistance_le_integer_distance ω₁ ω₂ 0
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
    _ ≤ (Real.pi * M / Real.sqrt 3) * |ω₁ - ω₂| :=
      mul_le_mul_of_nonneg_left hδangle (by positivity)

private theorem ae_closed_mixture {I : Type} [Fintype I] [DecidableEq I]
    (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (μ : ℝ)
    (hμ : MeasureProb (preparedAAState A j) S = μ) (z : Fin M) :
    (aeLaw M A j S hA hM).prob z =
      (‖qpeKernel M (Real.arcsin (Real.sqrt μ) / Real.pi) z‖ ^ 2 +
        ‖qpeKernel M (-Real.arcsin (Real.sqrt μ) / Real.pi) z‖ ^ 2) / 2 := by
  have hg := prepared_aa_good_bad_geometry A j S hA
  have hμ0 : 0 ≤ μ := hμ ▸ hg.2.2.2.2.1
  have hμ1 : μ ≤ 1 := hμ ▸ hg.2.2.2.2.2
  by_cases hz : μ = 0
  · rw [hz] at hμ ⊢
    rw [aeLaw_zero_mass M hM A j S hA hμ]
    simp
  by_cases ho : μ = 1
  · rw [ho] at hμ ⊢
    rw [aeLaw_one_mass M hM A j S hA hμ]
    have hperiod : qpeKernel M (-1 / 2) z = qpeKernel M (1 / 2) z := by
      convert! qpeKernel_int_add M (1 / 2) z (-1) using 1
      norm_num
    simp only [Real.sqrt_one, Real.arcsin_one]
    rw [show (Real.pi / 2) / Real.pi = (1 / 2 : ℝ) by field_simp,
      show -(Real.pi / 2) / Real.pi = (-1 / 2 : ℝ) by field_simp, hperiod]
    ring
  have hp : 0 < μ := lt_of_le_of_ne hμ0 (Ne.symm hz)
  have hl : μ < 1 := lt_of_le_of_ne hμ1 ho
  have hr : Real.sqrt μ < 1 := by simpa using! Real.sqrt_lt_sqrt hμ0 hl
  apply prepared_ae_two_phase_distribution M hM A j S hA
    (Real.arcsin (Real.sqrt μ)) (Real.arcsin_pos.mpr (Real.sqrt_pos.mpr hp))
    (Real.arcsin_lt_pi_div_two.mpr hr)
  rw [hμ, Real.sin_arcsin (by linarith [Real.sqrt_nonneg μ]) hr.le,
    Real.sq_sqrt hμ0]

theorem montanaroLemma18AELawTVSubgoal : MontanaroLemma18AELawTVSubgoal := by
  intro I _ _ M hM A₁ A₂ j₁ j₂ S₁ S₂ hA₁ hA₂ μ₁ μ₂ hμ₁ hμ₂
  let θ₁ := Real.arcsin (Real.sqrt μ₁)
  let θ₂ := Real.arcsin (Real.sqrt μ₂)
  have hg₁ := prepared_aa_good_bad_geometry A₁ j₁ S₁ hA₁
  have hg₂ := prepared_aa_good_bad_geometry A₂ j₂ S₂ hA₂
  have h10 : 0 ≤ μ₁ := hμ₁ ▸ hg₁.2.2.2.2.1
  have h11 : μ₁ ≤ 1 := hμ₁ ▸ hg₁.2.2.2.2.2
  have h20 : 0 ≤ μ₂ := hμ₂ ▸ hg₂.2.2.2.2.1
  have h21 : μ₂ ≤ 1 := hμ₂ ▸ hg₂.2.2.2.2.2
  have hr₁ : Real.sqrt μ₁ ≤ 1 := by simpa using! Real.sqrt_le_sqrt h11
  have hr₂ : Real.sqrt μ₂ ≤ 1 := by simpa using! Real.sqrt_le_sqrt h21
  have hang := montanaroClaim17 (Real.sqrt μ₁) (Real.sqrt μ₂)
    (Real.sqrt_nonneg _) hr₁ (Real.sqrt_nonneg _) hr₂
  rw [Real.sq_sqrt h10, Real.sq_sqrt h20] at hang
  change |θ₁ - θ₂| ≤ (Real.pi / 2) * Real.sqrt |μ₁ - μ₂| at hang
  have hp := phase_label_tv M hM (θ₁ / Real.pi) (θ₂ / Real.pi)
  have hn := phase_label_tv M hM (-θ₁ / Real.pi) (-θ₂ / Real.pi)
  have hneg : |(-θ₁ / Real.pi) - (-θ₂ / Real.pi)| =
      |θ₁ / Real.pi - θ₂ / Real.pi| := by
    rw [show (-θ₁ / Real.pi) - (-θ₂ / Real.pi) =
      -(θ₁ / Real.pi - θ₂ / Real.pi) by ring, abs_neg]
  rw [hneg] at hn
  have hmix : (1 / 2 : ℝ) * ∑ z : Fin M,
      |(aeLaw M A₁ j₁ S₁ hA₁ hM).prob z - (aeLaw M A₂ j₂ S₂ hA₂ hM).prob z| ≤
      (Real.pi * M / Real.sqrt 3) * |θ₁ / Real.pi - θ₂ / Real.pi| := by
    have hpoint (z : Fin M) :
        |(aeLaw M A₁ j₁ S₁ hA₁ hM).prob z - (aeLaw M A₂ j₂ S₂ hA₂ hM).prob z| ≤
        (|‖qpeKernel M (θ₁ / Real.pi) z‖ ^ 2 - ‖qpeKernel M (θ₂ / Real.pi) z‖ ^ 2| +
          |‖qpeKernel M (-θ₁ / Real.pi) z‖ ^ 2 - ‖qpeKernel M (-θ₂ / Real.pi) z‖ ^ 2|) / 2 := by
      rw [ae_closed_mixture M hM A₁ j₁ S₁ hA₁ μ₁ hμ₁,
        ae_closed_mixture M hM A₂ j₂ S₂ hA₂ μ₂ hμ₂]
      change |(‖qpeKernel M (θ₁ / Real.pi) z‖ ^ 2 +
        ‖qpeKernel M (-θ₁ / Real.pi) z‖ ^ 2) / 2 -
        (‖qpeKernel M (θ₂ / Real.pi) z‖ ^ 2 +
        ‖qpeKernel M (-θ₂ / Real.pi) z‖ ^ 2) / 2| ≤ _
      rw [← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      apply div_le_div_of_nonneg_right _ (by norm_num)
      convert! abs_add_le
        (‖qpeKernel M (θ₁ / Real.pi) z‖ ^ 2 - ‖qpeKernel M (θ₂ / Real.pi) z‖ ^ 2)
        (‖qpeKernel M (-θ₁ / Real.pi) z‖ ^ 2 - ‖qpeKernel M (-θ₂ / Real.pi) z‖ ^ 2) using 1
      congr 1
      ring
    have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin M)))
      (fun z _ => hpoint z)
    rw [← Finset.sum_div, Finset.sum_add_distrib] at hsum
    linarith
  apply hmix.trans
  calc
    _ = ((M : ℝ) / Real.sqrt 3) * |θ₁ - θ₂| := by
      rw [← sub_div, abs_div, abs_of_pos Real.pi_pos]
      field_simp
    _ ≤ ((M : ℝ) / Real.sqrt 3) * ((Real.pi / 2) * Real.sqrt |μ₁ - μ₂|) :=
      mul_le_mul_of_nonneg_left hang (by positivity)
    _ = (Real.pi / (2 * Real.sqrt 3)) * M * Real.sqrt |μ₁ - μ₂| := by ring
    _ ≤ _ := by
      gcongr
      nlinarith [Real.pi_gt_three]

end Qatlib.Concepts.EstimatorLaws.TvStability
