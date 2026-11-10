/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Waterfill.ExactResampling.ExactResamplingUpperStat
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
open Qatlib.Concepts.Waterfill.LevelFidelity
open Qatlib.Concepts.Waterfill.LevelFidelity.WaterLevelFidelity

namespace Qatlib.Concepts.Waterfill.ExactResampling
open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped BigOperators Matrix.Norms.L2Operator

theorem exactResamplingUpper : ExactResamplingUpper := by
  intro m π σ γlo γhi hπ hσ hπnorm hσnorm hlohi hlow hwit hhigh hwit2 p hpmin hpmax
  obtain ⟨γ,hlo,hhi,heq,_hopt⟩ := sourceFidelityLevelSubgoal m π σ γlo γhi hπ hσ
    hπnorm hσnorm hlohi hlow hwit hhigh hwit2 p hpmin hpmax
  obtain ⟨i₀,hπ₀,heq₀⟩ := hwit
  have hp₀ : (0 : ℝ) < π i₀ := by exact_mod_cast hπ₀
  have hs₀ : (0 : ℝ) < σ i₀ := by exact_mod_cast hσ i₀
  have hγlo : 0 < γlo := by
    by_contra hn
    have hm := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hs₀.le
    rw [heq₀] at hm
    linarith
  have hγ : 0 ≤ γ := (hγlo.trans_le hlo).le
  have hfill : levelFill π σ γ i₀ = (π i₀ : ℝ) := by
    apply min_eq_left
    calc
      _ = γlo*(σ i₀ : ℝ) := heq₀.symm
      _ ≤ γ*(σ i₀ : ℝ) := mul_le_mul_of_nonneg_right hlo hs₀.le
  have hmass : 0 < levelMass π σ γ := by
    have hle : (levelFill π σ γ i₀)^2 ≤ levelMass π σ γ :=
      Finset.single_le_sum (fun i _ => sq_nonneg (levelFill π σ γ i)) (Finset.mem_univ i₀)
    rw [hfill] at hle
    exact (sq_pos_of_ne_zero (ne_of_gt hp₀)).trans_le hle
  refine ⟨γ,hlo,hhi,hmass,heq,?_⟩
  intro D ξ U j₀ hξ hU hsource
  have hdata : ∀ i, 0 ≤ π i ∧ 0 ≤ σ i := fun i => ⟨hπ i,(hσ i).le⟩
  have hβ : 0 < Real.sqrt (levelMass π σ γ) := Real.sqrt_pos_of_pos hmass
  have hβ1 : Real.sqrt (levelMass π σ γ) ≤ 1 :=
    Real.sqrt_le_one.mpr (resamplingLevelMass_le_one π σ γ hdata hγ hπnorm)
  have hschedule := resamplingExactSchedule _ hβ hβ1
  have ha : 0 ≤ resamplingExactScale (Real.sqrt (levelMass π σ γ)) := by
    linarith [hschedule.1]
  have hword := resamplingPaidWord_actual m D π σ γ
    (resamplingExactScale (Real.sqrt (levelMass π σ γ))) j₀
    (resamplingExactRounds (Real.sqrt (levelMass π σ γ))) hdata hγ ha hschedule.2.1
  have hout := resamplingExactOutput_actual m D π σ γ hdata hγ hπnorm hσnorm hmass
    ξ U j₀ hξ hU hsource
  refine ⟨hword.1,hout.1,hout.2.1,hout.2.2.1,?_,hout.2.2.2.2.1,hout.2.2.2.2.2.1,
    hout.2.2.2.2.2.2.1,hout.2.2.2.2.2.2.2⟩
  rw [hout.2.2.2.1,heq]
  exact mul_div_cancel_right₀ p (ne_of_gt hmass)

end Qatlib.Concepts.Waterfill.ExactResampling
