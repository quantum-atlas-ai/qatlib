/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem12K2WindowStat
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.K2WindowSupport
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend

open Matrix
open scoped Classical
set_option autoImplicit false

theorem bhmt_amplitude_estimation_k2_window
    (I : Type) [Fintype I] [DecidableEq I] (M : ℕ) (A : Matrix I I ℂ)
    (j : I) (S : Finset I) (hM : 2 ≤ M) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (k : ℕ) (hk : 2 ≤ k) :
    let a := MeasureProb (preparedAAState A j) S
    ∑ z ∈ Finset.univ.filter (fun z : Fin M => |aeEstimate M z-a| ≤
        2*Real.pi*(k : ℝ)*Real.sqrt (a*(1-a))/(M : ℝ)+(k : ℝ)^2*Real.pi^2/(M : ℝ)^2),
      (aeLaw M A j S hA hM).prob z ≥ 1-1/(2*((k : ℝ)-1)) := by
  let a := MeasureProb (preparedAAState A j) S
  have hgeo := prepared_aa_good_bad_geometry A j S hA
  have ha0 : 0 ≤ a := hgeo.2.2.2.2.1
  have ha1 : a ≤ 1 := hgeo.2.2.2.2.2
  by_cases hzero : a=0
  · have hzero' : MeasureProb (preparedAAState A j) S=0 := hzero
    simp_rw [aeLaw_zero_mass M hM A j S hA hzero]
    have h := bhmt_k2_qpe_success M hM 0 k hk
    simpa [hzero'] using h
  by_cases hone : a=1
  · have hone' : MeasureProb (preparedAAState A j) S=1 := hone
    simp_rw [aeLaw_one_mass M hM A j S hA hone]
    have h := bhmt_k2_qpe_success M hM (1/2) k hk
    have hsin : (Real.sin (Real.pi*(1/2)))^2=(1 : ℝ) := by
      rw [mul_one_div, Real.sin_pi_div_two]
      norm_num
    simpa only [hone', hsin] using h
  have ha0' : 0 < a := lt_of_le_of_ne ha0 (Ne.symm hzero)
  have ha1' : a < 1 := lt_of_le_of_ne ha1 hone
  let θ := Real.arcsin (Real.sqrt a)
  have hθ0 : 0 < θ := Real.arcsin_pos.mpr (Real.sqrt_pos.mpr ha0')
  have hroot1 : Real.sqrt a < 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt ha0 ha1'
  have hθ1 : θ < Real.pi/2 := Real.arcsin_lt_pi_div_two.mpr hroot1
  have hθa : a=(Real.sin θ)^2 := by
    rw [Real.sin_arcsin (by linarith [Real.sqrt_nonneg a]) hroot1.le]
    exact (Real.sq_sqrt ha0).symm
  have hp : (Real.sin (Real.pi*(θ/Real.pi)))^2=a := by
    rw [show Real.pi*(θ/Real.pi)=θ by field_simp]
    exact hθa.symm
  have hn : (Real.sin (Real.pi*(-θ/Real.pi)))^2=a := by
    rw [show Real.pi*(-θ/Real.pi)=-θ by field_simp, Real.sin_neg, neg_sq]
    exact hθa.symm
  have hlo := bhmt_k2_qpe_success M hM (θ/Real.pi) k hk
  have hhi := bhmt_k2_qpe_success M hM (-θ/Real.pi) k hk
  dsimp only at hlo hhi
  rw [hp] at hlo
  rw [hn] at hhi
  simp_rw [prepared_ae_two_phase_distribution M hM A j S hA θ hθ0 hθ1 hθa]
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  linarith

theorem bhmt_amplitude_estimation_k2_window_contract :
    Theorem12K2WindowSpec.expected :=
  bhmt_amplitude_estimation_k2_window

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
