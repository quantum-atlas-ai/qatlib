/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Theorem3QuadraticSpeedupUnknownAQuan
import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Corollary1ExpectedSearchStat
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeCountingConsumers
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.WalkSearch.QuantumAccess

namespace Qatlib.Concepts.AEMeanReadout.RankOneSubspace

open Qatlib
open scoped ENNReal

theorem corollary1ExpectedSearch : Corollary1ExpectedSearch := by
  intro N S hN hS hS2 ε hε
  have hN0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hut' : 0 ≤ (S.card : ℝ)/(N:ℝ) := by positivity
  have h2nat : 2 * S.card ≤ N := by
    calc 2 * S.card ≤ 2 * (N / 2) := Nat.mul_le_mul_left 2 hS2
      _ = (N / 2) * 2 := Nat.mul_comm _ _
      _ ≤ N := Nat.div_mul_le_self N 2
  have h2 : 2 * (S.card : ℝ) ≤ (N:ℝ) := by exact_mod_cast h2nat
  have hut : (S.card : ℝ)/(N:ℝ) ≤ 1/2 := by
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2), div_mul_eq_mul_div, div_le_iff₀ hN0]
    linarith
  set u : ℝ := Real.sqrt ((S.card : ℝ)/(N:ℝ)) with hu
  have hu0 : 0 < u := Real.sqrt_pos_of_pos (by positivity)
  have hu1 : u ≤ 1 := Real.sqrt_le_one.2 (by linarith)
  have hθ0 : 0 < Real.arcsin u := Real.arcsin_pos.2 hu0
  have hsinsq : (Real.sin (Real.arcsin u))^2 = (S.card:ℝ)/(N:ℝ) := by
    rw [Real.sin_arcsin (by linarith) hu1, hu, Real.sq_sqrt hut']
  have hu2 : u ≤ Real.sqrt 2/2 := by
    have hkey : (Real.sqrt 2/2)^2 = 1/2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    have hsq2 : Real.sqrt (1/2) = Real.sqrt 2/2 := by
      rw [← hkey, Real.sqrt_sq (by positivity : (0:ℝ) ≤ Real.sqrt 2/2)]
    rw [← hsq2]
    exact Real.sqrt_le_sqrt hut
  have hθ4 : Real.arcsin u ≤ Real.pi/4 := by
    calc Real.arcsin u ≤ Real.arcsin (Real.sqrt 2/2) := Real.arcsin_le_arcsin hu2
      _ = Real.pi/4 := by
          rw [← Real.sin_pi_div_four,
            Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]
  have hθ1 : Real.arcsin u < Real.pi/2 := by linarith [Real.pi_pos]
  have hmass : MeasureProb (preparedAAState (QFTMatrix N) (⟨0,hN⟩ : Fin N)) S
      = (Real.sin (Real.arcsin u))^2 := by
    rw [prepared_qft_mark_mass N hN S, hsinsq]
  obtain ⟨M, J, k, hM1, hwin1, htail⟩ := exists_window_tail hθ0 hθ4 hε
  have hvalid : ∀ y : Fin N, (decide (y ∈ S) : Bool) = true ↔ y ∈ S := fun y => decide_eq_true_iff
  refine ⟨M, J + k, ?_, ?_, ?_⟩
  · have hc := geometric_search_actual_cutoff_failure_probability (QFTMatrix N)
        (qftMatrix_unitary hN) (⟨0,hN⟩ : Fin N) S (fun y => decide (y ∈ S)) M (J + k) J
        (Real.arcsin u) hvalid hθ0 hθ1 hmass hwin1
    rw [Nat.add_sub_cancel_left] at hc
    have hle1 : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (searchForSchedule (QFTMatrix N) (qftMatrix_unitary hN)
        (⟨0,hN⟩ : Fin N) S (fun y => decide (y ∈ S)) (geometricSearchSchedule M (J + k)))
        (fun tr => tr.result = none) ≤ 1 := event_le_one _ _
    have hne : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (searchForSchedule (QFTMatrix N) (qftMatrix_unitary hN)
        (⟨0,hN⟩ : Fin N) S (fun y => decide (y ∈ S)) (geometricSearchSchedule M (J + k)))
        (fun tr => tr.result = none) ≠ ⊤ := (lt_of_le_of_lt hle1 ENNReal.one_lt_top).ne
    rw [← ENNReal.ofReal_toReal hne]
    exact ENNReal.ofReal_le_ofReal (hc.trans htail)
  · have hb := geometric_search_intrinsic_expected_resource_budget (QFTMatrix N)
      (qftMatrix_unitary hN) (⟨0,hN⟩ : Fin N) S (fun y => decide (y ∈ S)) M (J + k)
      (Real.arcsin u) hvalid hθ0 hθ1 hmass hM1
    have h1u : 0 < 1/u := div_pos (by norm_num) hu0
    have hinv : Real.sqrt ((N:ℝ)/(S.card:ℝ)) = 1/u := by
      refine (sq_eq_sq₀ (Real.sqrt_nonneg _) h1u.le).mp ?_
      rw [Real.sq_sqrt (by positivity), div_pow, one_pow, hu, Real.sq_sqrt hut',
        one_div_div]
    refine le_trans (hb.1) (ENNReal.ofReal_le_ofReal ?_)
    rw [show (100:ℝ) = 2 * 50 from by norm_num]
    refine le_trans (two_div_sin_two_le (c := 50) (by norm_num) hθ0 hθ4) ?_
    rw [Real.sin_arcsin (by linarith) hu1, hinv, div_eq_mul_inv, inv_eq_one_div]
  · intro tr htr y hy
    exact (geometric_search_actual_support_soundness_and_metadata (QFTMatrix N)
      (qftMatrix_unitary hN) (⟨0,hN⟩ : Fin N) S (fun y => decide (y ∈ S)) M (J + k)
      hvalid tr htr).1 y hy

end Qatlib.Concepts.AEMeanReadout.RankOneSubspace
