/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.RecordDrivenVariableTimeAlgorithmStat
import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.RecordDrivenCascadeAux
import Qatlib.Papers.VarTimeAmpAmp10.StopModel.AverageStopTailBoundVari
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.NormNum.RealSqrt
import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.RecordDrivenSectorTransport
import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.RecordDrivenWindowBounds
import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.RecordDrivenBornTransport
import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.RecordDrivenFinalRoundCalibration

/-!
# Verification of the record-driven variable-time algorithm

This module proves `RecordDrivenVariableTimeAlgorithm` for the record-driven construction
associated with [Ambainis2012]. The proof handles pipelines of length at most sixteen separately
from longer pipelines, combines median estimation with cascade gain bounds, and establishes the
specified good-record, success, direction, and time guarantees.

## Main statements

* `rdvt_chain_large`: live-mass and gain-product bounds for longer pipelines.
* `rdvt_chain_small`: zero prefix amplification and exact cost for short pipelines.
* `recordDrivenVariableTimeAlgorithm_answer`: verification of the full record-driven
  specification.

## References

* [Ambainis, 2012][Ambainis2012]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.PhaseGeometry.Phase

open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Papers.VarTimeAmpAmp10.StopModel

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement

set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
open Matrix
open scoped Classical BigOperators
set_option warningAsError false

variable {C : Type} [Fintype C] [DecidableEq C]

omit [DecidableEq C] in

/-- Measurement mass on any sector is nonnegative. -/
theorem rdvt_measure_nonneg (ψ : QState (VtSpace C)) (S : Finset (VtSpace C)) :
    0 ≤ MeasureProb ψ S := by
  unfold MeasureProb BornProb
  exact Finset.sum_nonneg fun p _ => pow_nonneg (norm_nonneg _) 2

set_option maxHeartbeats 4000000 in

/-- For a legal supported pipeline with more than sixteen stages, the stated success floor and
recordwise estimation bounds yield domination of original live masses, the positive-prefix
floor `1 / (7 * m)`, and the displayed product-of-gains comparison. -/
private theorem rdvt_chain_large {C : Type} [Fintype C] [DecidableEq C]
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (history : ℕ → Finset C)
    (hl : GrowingVtLegal stages history) (hm : 1 ≤ stages.length)
    (j₀ : VtSpace C) (hj : j₀.1 = vtRunningFlag) (hs : GrowingVtSupported stages history j₀)
    (hrun : MeasureProb (vtState stages stages.length (Qatlib.Foundations.PureStateMath.Ket j₀)) (runningSet C) = 0)
    (hp : ℝ) (hp0 : 0 < hp)
    (hfloor : 1/(10^12*((stages.length : ℝ))^3) ≤ hp)
    (hpdef : hp = MeasureProb (vtState stages stages.length (Qatlib.Foundations.PureStateMath.Ket j₀)) (goodSet C))
    (hm16 : 16 < stages.length)
    (ω : RecordDrivenRecord stages.length)
    (hω : ∀ i : Fin (stages.length+1),
      |vtMedianEstimate (recordDrivenResolution stages.length) (recordDrivenRepetitions stages.length) (ω i)
        - MeasureProb (dataVtWordState stages history j₀ (recordDrivenInputWord stages.length ω i)) (liveSet C)|
      ≤ dataEstimateRadius
        (MeasureProb (dataVtWordState stages history j₀ (recordDrivenInputWord stages.length ω i)) (liveSet C))
        (recordDrivenResolution stages.length)) :
    (∀ k ≤ stages.length,
      MeasureProb (vtState stages k (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C) ≤
      MeasureProb (dataVtWordState stages history j₀
        (cascadeWord (recordDrivenSchedule stages.length ω) k)) (liveSet C)) ∧
    (∀ k ≤ stages.length, 1 ≤ k →
      1/(7*((stages.length : ℝ))) ≤
      MeasureProb (dataVtWordState stages history j₀
        (cascadeWord (recordDrivenSchedule stages.length ω) k)) (liveSet C)) ∧
    (∀ i ≤ stages.length,
      (∏ k ∈ Finset.Ico i stages.length,
        ((if recordDrivenSchedule stages.length ω k = 0 then (1:ℝ)
          else 1-4/(5*((stages.length : ℝ))))
          *(((2*(recordDrivenSchedule stages.length ω k)+1 : ℕ) : ℝ)^2)))
      *MeasureProb (dataVtWordState stages history j₀
        (cascadeWord (recordDrivenSchedule stages.length ω) i)) (liveSet C)
      *MeasureProb (vtState stages stages.length (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C) ≤
      MeasureProb (dataVtWordState stages history j₀
        (cascadeWord (recordDrivenSchedule stages.length ω) stages.length)) (liveSet C)
      *MeasureProb (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C)) := by
  let m := stages.length
  have hmdef : m = stages.length := rfl
  have hm1 : 1 ≤ m := by omega
  have hm17m : 17 ≤ m := by omega
  have hpdefm :
      hp = MeasureProb (vtState stages m (Qatlib.Foundations.PureStateMath.Ket j₀))
      (goodSet C) := hpdef
  have hrunm :
      MeasureProb (vtState stages m (Qatlib.Foundations.PureStateMath.Ket j₀))
      (runningSet C) = 0 := hrun
  set sched := recordDrivenSchedule stages.length ω with hscheddef
  set s : ℕ → ℝ := fun k => MeasureProb (vtState stages k (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C) with hsdef
  set R : ℕ → ℝ := fun k => MeasureProb (dataVtWordState stages history j₀
    (cascadeWord sched k)) (liveSet C) with hRdef
  set cfmul : ℕ → ℝ := fun k =>
    (if sched k = 0 then (1:ℝ) else 1-4/(5*((m:ℝ))))*((2*(sched k)+1 : ℕ) : ℝ)^2 with hcfdef
  have hmR : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hmR0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hbridge : ∀ k ≤ m,
      MeasureProb (vtState stages m (Qatlib.Foundations.PureStateMath.Ket j₀)) (goodSet C) ≤ s k ∧
      s k ≤ MeasureProb (vtState stages m (Qatlib.Foundations.PureStateMath.Ket j₀)) (goodSet C)
        +MeasureProb (vtState stages k (Qatlib.Foundations.PureStateMath.Ket j₀)) (runningSet C) :=
    fun k hk => rdvt_sector_bridge stages history hl j₀ hs hrun k hk
  have hsm : s m = MeasureProb (vtState stages m (Qatlib.Foundations.PureStateMath.Ket j₀)) (goodSet C) := by
    have h1 := (hbridge m le_rfl).1
    have h2 := (hbridge m le_rfl).2
    rw [hrunm, _root_.add_zero] at h2
    linarith
  have hsp : ∀ k ≤ m, 0 < s k := by
    intro k hk
    have h1 := (hbridge k hk).1
    rw [← hpdefm] at h1
    exact lt_of_lt_of_le hp0 h1
  have hjlive : j₀ ∈ liveSet C := by
    simp only [liveSet, goodSet, runningSet, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact Or.inr hj
  have hket1 : ∀ S : Finset (VtSpace C), j₀ ∈ S → MeasureProb (Qatlib.Foundations.PureStateMath.Ket j₀) S = 1 := by
    intro S hS
    unfold MeasureProb BornProb
    rw [Finset.sum_eq_single_of_mem j₀ hS (fun q hq hne => by simp [Qatlib.Foundations.PureStateMath.Ket, hne])]
    simp [Qatlib.Foundations.PureStateMath.Ket]
  have hs0 : s 0 = 1 := by
    have hv : vtState stages 0 (Qatlib.Foundations.PureStateMath.Ket j₀) = Qatlib.Foundations.PureStateMath.Ket j₀ := by
      simp [vtState, vtRunMatrix]
    simp only [hsdef]
    rw [hv, hket1 _ hjlive]
  have hR0 : R 0 = 1 := by
    have hw : cascadeWord sched 0 = ([] : List DataVtStep) := rfl
    have hst : dataVtWordState stages history j₀ ([] : List DataVtStep) = Qatlib.Foundations.PureStateMath.Ket j₀ := by
      simp [dataVtWordState, dataVtWordMatrix]
    simp only [hRdef]
    rw [hw, hst, hket1 _ hjlive]
  have hRnn : ∀ k, 0 ≤ R k := by
    intro k
    simp only [hRdef]
    exact rdvt_measure_nonneg _ _
  have hsnm : ∀ k ≤ m, 0 ≤ s k := fun _ hk => (hsp _ hk).le
  have hcfnn : ∀ k, 0 ≤ cfmul k := by
    intro k
    simp only [hcfdef]
    by_cases hz : sched k = 0
    · simp [hz]
    · have hm17 : (17:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm17m
      have h1 : (0:ℝ) ≤ 1-4/(5*((m:ℝ))) := by
        have h4 : (4:ℝ)/(5*((m:ℝ))) ≤ 1 := by
          apply (div_le_one (by positivity : (0:ℝ) < 5*((m:ℝ)))).2
          nlinarith [hm17]
        linarith
      have h2 : (0:ℝ) ≤ ((2*(sched k)+1 : ℕ) : ℝ)^2 := by positivity
      rw [if_neg hz]
      exact mul_nonneg h1 h2
  have hlevel : ∀ j : ℕ, j < m →
      ∃ α : ℂ,
        R j = Complex.normSq α*s j ∧
        MeasureProb (dataVtWordState stages history j₀
          (cascadeWord sched j++[DataVtStep.stageF j])) (liveSet C)
          = Complex.normSq α*s (j+1) := by
    intro j hjm
    obtain ⟨α, h1, h2⟩ :=
      rdvt_cascade_input_live stages history hl j₀ hj hs sched j (by omega)
    exact ⟨α, h1, h2 hjm⟩
  have hmain : ∀ j : ℕ, j ≤ m →
      (∀ i ≤ j, (∏ k ∈ Finset.Ico i j, cfmul k)*R i*s j ≤ R j*s i) ∧
      (s j ≤ R j) ∧ (1 ≤ j → 1/(7*((m:ℝ))) ≤ R j) := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨fun i hi => ?_, by rw [hs0, hR0], fun hcon => absurd hcon (by omega)⟩
      have hi0 : i = 0 := by omega
      subst hi0
      rw [Finset.Ico_self, Finset.prod_empty, one_mul]
    | succ j ih =>
      intro hsucc
      have hjm : j < m := by omega
      obtain ⟨α, hRj, hAj⟩ := hlevel j hjm
      set Aj : ℝ := MeasureProb (dataVtWordState stages history j₀
        (cascadeWord sched j++[DataVtStep.stageF j])) (liveSet C) with hAjdef
      have hAjmul : Aj*s j = R j*s (j+1) := by
        rw [hAj, hRj]
        ring
      have hih := ih (by omega)
      have hsj0 : 0 < s j := hsp j (by omega)
      have hsj1 : 0 < s (j+1) := hsp (j+1) (by omega)
      have hAjnn : 0 ≤ Aj := rdvt_measure_nonneg _ _
      have hAjsucc : s (j+1) ≤ Aj := by
        have h2 : s j ≤ R j := hih.2.1
        nlinarith [hAjmul, h2, hsj0]
      have hAfloor : 1/(10^12*((m:ℝ))^3) ≤ Aj := by
        have h1 := (hbridge (j+1) (by omega)).1
        rw [← hpdefm] at h1
        exact le_trans hfloor (le_trans h1 hAjsucc)
      have hinput : recordDrivenInputWord stages.length ω ⟨j, by omega⟩
          = cascadeWord sched j++[DataVtStep.stageF j] := by
        unfold recordDrivenInputWord
        have hv : (⟨j, by omega⟩ : Fin (stages.length+1)).val = j := rfl
        rw [hv, if_pos hjm]
      have hωraw := hω ⟨j, by omega⟩
      rw [hinput] at hωraw
      have hrad := recordDriven_floor_radius m (by omega) Aj hAfloor
      have hest : |recordDrivenEstimate m (ω ⟨j, by omega⟩)-Aj| ≤ Aj/100 :=
        hωraw.trans hrad
      have hestlow : (99/100)*Aj ≤ recordDrivenEstimate m (ω ⟨j, by omega⟩) := by
        have h := (abs_le.mp hest).1
        linarith
      have hesthigh : recordDrivenEstimate m (ω ⟨j, by omega⟩) ≤ (101/100)*Aj := by
        have h := (abs_le.mp hest).2
        linarith
      have hAjlow : (100/101)*recordDrivenEstimate m (ω ⟨j, by omega⟩) ≤ Aj := by
        nlinarith [hesthigh, hAjnn]
      have hschedl : sched j
          = recordDrivenPrefixRounds stages.length (ω ⟨j, by omega⟩) := by
        simp only [hscheddef, recordDrivenSchedule, dif_pos (by omega : j < stages.length)]
      have hschedj : sched j = recordDrivenPrefixRounds m (ω ⟨j, by omega⟩) := hschedl
      obtain ⟨hcap, hcross, hmin⟩ := recordDriven_prefix_crossing m (by omega) Aj
        (ω ⟨j, by omega⟩) hAfloor hest
      rw [← hschedj] at hcross hmin
      have hcast : ((2*(sched j)+1 : ℕ) : ℝ) = 2*((sched j : ℕ):ℝ)+1 := by
        push_cast
        ring
      have hRj1state : cascadeWord sched (j+1)
          = liveAAWord (cascadeWord sched j++[DataVtStep.stageF j]) (sched j) := rfl
      have hwlegal : DataVtWordLegal stages (cascadeWord sched j++[DataVtStep.stageF j]) := by
        intro t ht
        rcases List.mem_append.mp ht with ht | ht
        · exact cascadeWord_legal stages sched j (by omega) t ht
        · obtain rfl := List.mem_singleton.mp ht
          exact hjm

      have htail : cfmul j*R j*s (j+1) ≤ R (j+1)*s j →
          (∀ i ≤ j+1, (∏ k ∈ Finset.Ico i (j+1), cfmul k)*R i*s (j+1) ≤ R (j+1)*s i) ∧
          (s (j+1) ≤ R (j+1)) := by
        intro hstepmul
        have hchain : ∀ i ≤ j+1,
            (∏ k ∈ Finset.Ico i (j+1), cfmul k)*R i*s (j+1) ≤ R (j+1)*s i := by
          intro i hi
          by_cases hij : i = j+1
          · subst hij
            rw [Finset.Ico_self, Finset.prod_empty, one_mul]
          · have hile : i ≤ j := by omega
            have hsin : (0:ℝ) ≤ s i := hsnm i (by omega)
            have hcomb : ((∏ k ∈ Finset.Ico i (j+1), cfmul k)*R i*s (j+1))*s j
                ≤ (R (j+1)*s i)*s j := by
              calc ((∏ k ∈ Finset.Ico i (j+1), cfmul k)*R i*s (j+1))*s j
                  = cfmul j*((∏ k ∈ Finset.Ico i j, cfmul k)*R i*s j)*s (j+1) := by
                    rw [Finset.prod_Ico_succ_top hile]
                    ring
                _ ≤ cfmul j*(R j*s i)*s (j+1) :=
                    mul_le_mul_of_nonneg_right
                      (mul_le_mul_of_nonneg_left (hih.1 i hile) (hcfnn j)) hsj1.le
                _ = s i*(cfmul j*R j*s (j+1)) := by ring
                _ ≤ s i*(R (j+1)*s j) := mul_le_mul_of_nonneg_left hstepmul hsin
                _ = (R (j+1)*s i)*s j := by ring
            exact le_of_mul_le_mul_right hcomb hsj0
        have hcfge : (1:ℝ) ≤ cfmul j := by
          by_cases hz : sched j = 0
          · simp only [hcfdef, hz, if_pos]
            norm_num
          · have hm17 : (17:ℝ) ≤ (m:ℝ) := by exact_mod_cast (by omega : 17 ≤ m)
            have h5 : (85:ℝ) ≤ 5*((m:ℝ)) := by nlinarith [hm17]
            have hdiv : (4:ℝ)/(5*((m:ℝ))) ≤ 4/85 := by
              apply (div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 85)).2
              nlinarith [h5]
            have hγ : (81:ℝ)/85 ≤ 1-4/(5*((m:ℝ))) := by linarith
            have hc3 : (3:ℝ) ≤ 2*((sched j : ℕ):ℝ)+1 := by
              have hs1 : 1 ≤ sched j := by omega
              have hc : (1:ℝ) ≤ ((sched j : ℕ):ℝ) := by exact_mod_cast hs1
              nlinarith [hc]
            have hNsq : (9:ℝ) ≤ (2*((sched j : ℕ):ℝ)+1)^2 := by nlinarith [hc3]
            simp only [hcfdef, if_neg hz]
            rw [hcast]
            have hNnn : (0:ℝ) ≤ 2*((sched j : ℕ):ℝ)+1 := by
              have hc1 : (1:ℝ) ≤ ((sched j : ℕ):ℝ) := by
                exact_mod_cast (by omega : 1 ≤ sched j)
              linarith
            have hγnn : (0:ℝ) ≤ 1-4/(5*((m:ℝ))) := by linarith [hγ]
            have hprod : ((81:ℝ)/85)*9
                ≤ (1-4/(5*((m:ℝ))))*(2*((sched j : ℕ):ℝ)+1)^2 :=
              mul_le_mul hγ hNsq (by norm_num) hγnn
            have h1 : (1:ℝ) ≤ ((81:ℝ)/85)*9 := by norm_num
            linarith [hprod, h1]
        have hpm : s (j+1) ≤ R (j+1) := by
          have h3 : s j*s (j+1) ≤ cfmul j*R j*s (j+1) := by
            apply mul_le_mul_of_nonneg_right _ hsj1.le
            calc s j ≤ R j := hih.2.1
              _ ≤ cfmul j*R j := by nlinarith [hcfge, hRnn j]
          nlinarith [hstepmul, h3, hsj0]
        exact ⟨hchain, hpm⟩
      have hRjlow : (100/101)*(1/(6*((m:ℝ)))) ≤ R (j+1) →
          1/(7*((m:ℝ))) ≤ R (j+1) := by
        intro hRj1low
        have hconst : (1:ℝ)/7 ≤ (100/101)*(1/6) := by norm_num
        have hpos : (0:ℝ) ≤ 1/((m:ℝ)) := by positivity
        calc 1/(7*((m:ℝ)))
            = (1/7)*(1/((m:ℝ))) := by field_simp
          _ ≤ ((100/101)*(1/6))*(1/((m:ℝ))) := mul_le_mul_of_nonneg_right hconst hpos
          _ = (100/101)*(1/(6*((m:ℝ)))) := by field_simp
          _ ≤ R (j+1) := hRj1low
      by_cases hzero : sched j = 0
      · have hW : cascadeWord sched (j+1)
            = cascadeWord sched j++[DataVtStep.stageF j] := by
          show liveAAWord (cascadeWord sched j++[DataVtStep.stageF j]) (sched j) = _
          rw [hzero]
          simp [liveAAWord]
        have hRj1 : R (j+1) = Aj := by
          simp only [hRdef]
          rw [hW]
        have hstepmul : cfmul j*R j*s (j+1) ≤ R (j+1)*s j := by
          have hcf1 : cfmul j = 1 := by
            simp only [hcfdef, hzero, if_pos]
            norm_num
          rw [hcf1, one_mul, hRj1, hAjmul]
        rw [hzero] at hcross
        have hcross1 : 1/(6*((m:ℝ))) ≤ recordDrivenEstimate m (ω ⟨j, by omega⟩) := by
          simpa using! hcross
        have hRj1low : (100/101)*(1/(6*((m:ℝ)))) ≤ R (j+1) := by
          rw [hRj1]
          calc (100/101)*(1/(6*((m:ℝ))))
              ≤ (100/101)*recordDrivenEstimate m (ω ⟨j, by omega⟩) :=
                mul_le_mul_of_nonneg_left hcross1 (by norm_num)
            _ ≤ Aj := hAjlow
        exact ⟨htail hstepmul |>.1, htail hstepmul |>.2, fun _ => hRjlow hRj1low⟩
      · have hN3 : 3 ≤ 2*(sched j)+1 := by omega
        have hsched1 : 1 ≤ sched j := by omega
        have hc1 : (1:ℝ) ≤ ((sched j : ℕ):ℝ) := by exact_mod_cast hsched1
        have hAjpos : (0:ℝ) < Aj := lt_of_lt_of_le hsj1 hAjsucc
        have hestpos : (0:ℝ) < recordDrivenEstimate m (ω ⟨j, by omega⟩) := by
          have h := (abs_le.mp hest).1
          linarith
        have hestnn : (0:ℝ) ≤ recordDrivenEstimate m (ω ⟨j, by omega⟩) := le_of_lt hestpos
        have hestlt : recordDrivenEstimate m (ω ⟨j, by omega⟩) < 1/(6*((m:ℝ))) := by
          have hprev := hmin (sched j-1) (by omega)
          have hcast2 : ((2*(sched j-1)+1 : ℕ) : ℝ) = 2*((sched j : ℕ):ℝ)-1 := by
            push_cast
            have hc : ((sched j-1:ℕ):ℝ)+1 = ((sched j : ℕ):ℝ) := by
              exact_mod_cast (show (sched j:ℕ)-1+1 = sched j by omega)
            linarith
          rw [hcast2] at hprev
          have hd1 : (1:ℝ) ≤ 2*((sched j : ℕ):ℝ)-1 := by linarith
          have hmono : (1:ℝ) ≤ (2*((sched j : ℕ):ℝ)-1)^2 := by nlinarith [hd1]
          exact lt_of_le_of_lt (le_mul_of_one_le_left hestnn hmono) hprev
        have hprev2 := hmin (sched j-1) (by omega)
        have hcast2 : ((2*(sched j-1)+1 : ℕ) : ℝ) = 2*((sched j : ℕ):ℝ)-1 := by
          push_cast
          have hc : ((sched j-1:ℕ):ℝ)+1 = ((sched j : ℕ):ℝ) := by
            exact_mod_cast (show (sched j:ℕ)-1+1 = sched j by omega)
          linarith
        rw [hcast2] at hprev2
        have hAjlt : Aj < 1 := by
          have hAj99 : Aj ≤ (100/99)*recordDrivenEstimate m (ω ⟨j, by omega⟩) := by
            have h := mul_le_mul_of_nonneg_left hestlow (by norm_num : (0:ℝ) ≤ 100/99)
            rw [show (100/99)*((99/100)*Aj) = Aj from by ring] at h
            exact h
          have hm17 : (17:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm17m
          have h6m : (1:ℝ)/(6*((m:ℝ))) ≤ 1/102 :=
            (div_le_div_iff₀ (by positivity : (0:ℝ) < 6*((m:ℝ)))
              (by norm_num : (0:ℝ) < 102)).2 (by nlinarith [hm17] : (1:ℝ)*102 ≤ 1*(6*((m:ℝ))))
          have hmul := mul_lt_mul_of_pos_left hestlt (by norm_num : (0:ℝ) < 100/99)
          have hle : (100/99)*(1/(6*((m:ℝ)))) ≤ (100/99)*(1/102) :=
              mul_le_mul_of_nonneg_left h6m (by norm_num : (0:ℝ) ≤ 100/99)
          have hconst : (100/99)*(1/102) ≤ 1 := by norm_num
          linarith
        have hborn := rdvt_live_aa_born stages history j₀ hl
          (cascadeWord sched j++[DataVtStep.stageF j]) hwlegal hAjpos hAjlt hAjdef.symm (sched j)
        have hRj1 : R (j+1) = (Real.sin ((2*((sched j : ℕ):ℝ)+1)*Real.arcsin (Real.sqrt Aj)))^2 := by
          simp only [hRdef]
          rw [hRj1state]
          exact hborn
        have hNmono : (2*((sched j : ℕ):ℝ)+1) ≤ 3*(2*((sched j : ℕ):ℝ)-1) := by
          nlinarith [hc1]
        have hn2 : (0:ℝ) ≤ 3*(2*((sched j : ℕ):ℝ)-1) := by nlinarith [hc1]
        have hn1 : (0:ℝ) ≤ 2*((sched j : ℕ):ℝ)+1 := by positivity
        have hsqle : (2*((sched j : ℕ):ℝ)+1)^2 ≤ (3*(2*((sched j : ℕ):ℝ)-1))^2 := by
          calc (2*((sched j : ℕ):ℝ)+1)^2
              = (2*((sched j : ℕ):ℝ)+1)*(2*((sched j : ℕ):ℝ)+1) := by ring
            _ ≤ (3*(2*((sched j : ℕ):ℝ)-1))*(2*((sched j : ℕ):ℝ)+1) :=
                mul_le_mul_of_nonneg_right hNmono hn1
            _ ≤ (3*(2*((sched j : ℕ):ℝ)-1))*(3*(2*((sched j : ℕ):ℝ)-1)) :=
                mul_le_mul_of_nonneg_left hNmono hn2
            _ = (3*(2*((sched j : ℕ):ℝ)-1))^2 := by ring
        have hhigh : ((2*(sched j)+1 : ℕ) : ℝ)^2*recordDrivenEstimate m (ω ⟨j, by omega⟩)
            ≤ 3/(2*((m:ℝ))) := by
          rw [hcast]
          have h1 : ((2*((sched j : ℕ):ℝ)+1)^2)*recordDrivenEstimate m (ω ⟨j, by omega⟩)
              ≤ (3*(2*((sched j : ℕ):ℝ)-1))^2*recordDrivenEstimate m (ω ⟨j, by omega⟩) :=
              mul_le_mul_of_nonneg_right hsqle hestnn
          have h2 : (3*(2*((sched j : ℕ):ℝ)-1))^2 = 9*(2*((sched j : ℕ):ℝ)-1)^2 := by ring
          have h3 : 9*((2*((sched j : ℕ):ℝ)-1)^2*recordDrivenEstimate m (ω ⟨j, by omega⟩))
              < 9*(1/(6*((m:ℝ)))) :=
              mul_lt_mul_of_pos_left hprev2 (by norm_num : (0:ℝ) < 9)
          have h4 : 9*(1/(6*((m:ℝ)))) = 3/(2*((m:ℝ))) := by
            field_simp
            ring
          rw [h2] at h1
          rw [h4] at h3
          linarith
        have hwinw := rdvt_crossing_window (a := Aj)
          (est := recordDrivenEstimate m (ω ⟨j, by omega⟩)) (n := 2*(sched j)+1) (m := m)
          hm17m (by omega : 3 ≤ 2*(sched j)+1) hest hhigh
        have hwin := rdvt_window_gain (a := Aj) (N := 2*(sched j)+1) (m := m)
          hm17m (by omega : 1 ≤ 2*(sched j)+1) hAjnn (le_of_lt hAjlt) hwinw
        rw [hcast] at hwin
        have hgain : (1-4/(5*((m:ℝ))))*((2*((sched j : ℕ):ℝ)+1)^2)*Aj ≤ R (j+1) := by
          rw [hRj1]
          exact hwin
        have hstepmul : cfmul j*R j*s (j+1) ≤ R (j+1)*s j := by
          have hcf2 : cfmul j
              = (1-4/(5*((m:ℝ))))*((2*((sched j : ℕ):ℝ)+1)^2) := by
            simp only [hcfdef, if_neg hzero, hcast]
          rw [hcf2]
          have hassoc : (1-4/(5*((m:ℝ))))*((2*((sched j : ℕ):ℝ)+1)^2)*R j*s (j+1)
              = ((1-4/(5*((m:ℝ))))*((2*((sched j : ℕ):ℝ)+1)^2))*(R j*s (j+1)) := by ring
          rw [hassoc, ← hAjmul]
          calc ((1-4/(5*((m:ℝ))))*((2*((sched j : ℕ):ℝ)+1)^2))*(Aj*s j)
              = (((1-4/(5*((m:ℝ))))*((2*((sched j : ℕ):ℝ)+1)^2))*Aj)*s j := by ring
            _ ≤ R (j+1)*s j := mul_le_mul_of_nonneg_right hgain hsj0.le
        have hm17 : (17:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm17m
        have h5 : (85:ℝ) ≤ 5*((m:ℝ)) := by
          have h := mul_le_mul_of_nonneg_left hm17 (by norm_num : (0:ℝ) ≤ 5)
          calc (85:ℝ) = 5*(17:ℝ) := by norm_num
            _ ≤ 5*((m:ℝ)) := h
        have hdiv : (4:ℝ)/(5*((m:ℝ))) ≤ 4/85 := by
          have h5m : (0:ℝ) < 5*((m:ℝ)) := by positivity
          rw [div_le_div_iff₀ h5m (by norm_num : (0:ℝ) < 85)]
          have h20 : (20:ℝ)*(17:ℝ) ≤ (20:ℝ)*((m:ℝ)) :=
            mul_le_mul_of_nonneg_left hm17 (by norm_num : (0:ℝ) ≤ 20)
          calc (4:ℝ)*85 = (20:ℝ)*(17:ℝ) := by norm_num
            _ ≤ (20:ℝ)*((m:ℝ)) := h20
            _ = 4*(5*((m:ℝ))) := by ring
        have hγ : (81:ℝ)/85 ≤ 1-4/(5*((m:ℝ))) := by
          have h01 : (1:ℝ)-4/85 = 81/85 := by norm_num
          calc (81:ℝ)/85 = (1:ℝ)-4/85 := h01.symm
            _ ≤ (1:ℝ)-4/(5*((m:ℝ))) := sub_le_sub (le_refl _) hdiv
        have hγpos : (0:ℝ) ≤ 1-4/(5*((m:ℝ))) := le_trans (by norm_num : (0:ℝ) ≤ 81/85) hγ
        have hNsqAj : (100/101)*(1/(6*((m:ℝ))))
            ≤ ((2*((sched j : ℕ):ℝ)+1)^2)*Aj := by
          have hcrossd := hcross
          rw [hcast] at hcrossd
          calc (100/101)*(1/(6*((m:ℝ))))
              ≤ (100/101)*(((2*((sched j : ℕ):ℝ)+1)^2)
                *recordDrivenEstimate m (ω ⟨j, by omega⟩)) :=
                mul_le_mul_of_nonneg_left hcrossd (by norm_num : (0:ℝ) ≤ 100/101)
            _ = ((2*((sched j : ℕ):ℝ)+1)^2)
                *((100/101)*recordDrivenEstimate m (ω ⟨j, by omega⟩)) := by ring
            _ ≤ ((2*((sched j : ℕ):ℝ)+1)^2)*Aj :=
                mul_le_mul_of_nonneg_left hAjlow
                  (by positivity : (0:ℝ) ≤ (2*((sched j : ℕ):ℝ)+1)^2)
        have hRj1low : (81/85)*((100/101)*(1/(6*((m:ℝ))))) ≤ R (j+1) := by
          calc (81/85)*((100/101)*(1/(6*((m:ℝ)))))
              ≤ (1-4/(5*((m:ℝ))))*((100/101)*(1/(6*((m:ℝ))))) :=
                mul_le_mul_of_nonneg_right hγ (by positivity : (0:ℝ) ≤ (100/101)*(1/(6*((m:ℝ)))))
            _ ≤ (1-4/(5*((m:ℝ))))*(((2*((sched j : ℕ):ℝ)+1)^2)*Aj) :=
                mul_le_mul_of_nonneg_left hNsqAj hγpos
            _ = ((1-4/(5*((m:ℝ))))*((2*((sched j : ℕ):ℝ)+1)^2))*Aj := by ring
            _ ≤ R (j+1) := hgain
        have hRjlow2 : 1/(7*((m:ℝ))) ≤ R (j+1) := by
          have hconst : (1:ℝ)/7 ≤ (81/85)*((100/101)*(1/6)) := by norm_num
          have hpos : (0:ℝ) ≤ 1/((m:ℝ)) := by positivity
          calc 1/(7*((m:ℝ)))
              = (1/7)*(1/((m:ℝ))) := by field_simp
            _ ≤ ((81/85)*((100/101)*(1/6)))*(1/((m:ℝ))) :=
                  mul_le_mul_of_nonneg_right hconst hpos
            _ = (81/85)*((100/101)*(1/(6*((m:ℝ))))) := by field_simp
            _ ≤ R (j+1) := hRj1low
        exact ⟨htail hstepmul |>.1, htail hstepmul |>.2, fun _ => hRjlow2⟩
  exact ⟨fun k hk => (hmain k hk).2.1, fun k hk => (hmain k hk).2.2,
    fun i hi => (hmain m le_rfl).1 i hi⟩

set_option maxHeartbeats 4000000 in

/-- For a legal supported pipeline of at most sixteen stages under the stated stopping and
success hypotheses, the record-driven schedule is zero, cascade live masses equal the
original live masses, and full cascade time is `2 ^ m - 1`. -/
private theorem rdvt_chain_small {C : Type} [Fintype C] [DecidableEq C]
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (history : ℕ → Finset C)
    (hl : GrowingVtLegal stages history) (_hm : 1 ≤ stages.length)
    (j₀ : VtSpace C) (hj : j₀.1 = vtRunningFlag) (hs : GrowingVtSupported stages history j₀)
    (hrun : MeasureProb (vtState stages stages.length (Qatlib.Foundations.PureStateMath.Ket j₀)) (runningSet C) = 0)
    (hp : ℝ) (hp0 : 0 < hp)
    (hpdef : hp = MeasureProb (vtState stages stages.length (Qatlib.Foundations.PureStateMath.Ket j₀)) (goodSet C))
    (hsmall : stages.length ≤ 16)
    (ω : RecordDrivenRecord stages.length) :
    (∀ k, recordDrivenSchedule stages.length ω k = 0) ∧
    (∀ k ≤ stages.length,
      MeasureProb (dataVtWordState stages history j₀
        (cascadeWord (recordDrivenSchedule stages.length ω) k)) (liveSet C)
      = MeasureProb (vtState stages k (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C)) ∧
    ((dataVtWordTime (cascadeWord (recordDrivenSchedule stages.length ω) stages.length) : ℝ)
      = (2:ℝ)^(stages.length)-1) := by
  have hsched0 : ∀ k, recordDrivenSchedule stages.length ω k = 0 := by
    intro k
    unfold recordDrivenSchedule
    by_cases hk : k < stages.length
    · rw [dif_pos hk]
      unfold recordDrivenPrefixRounds
      rw [if_pos hsmall]
    · rw [dif_neg hk]
  have hjlive : j₀ ∈ liveSet C := by
    simp only [liveSet, goodSet, runningSet, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact Or.inr hj
  have hket1 : ∀ S : Finset (VtSpace C), j₀ ∈ S → MeasureProb (Qatlib.Foundations.PureStateMath.Ket j₀) S = 1 := by
    intro S hS
    unfold MeasureProb BornProb
    rw [Finset.sum_eq_single_of_mem j₀ hS (fun q hq hne => by simp [Qatlib.Foundations.PureStateMath.Ket, hne])]
    simp [Qatlib.Foundations.PureStateMath.Ket]
  have hst0 :
      vtState stages 0
      (Qatlib.Foundations.PureStateMath.Ket j₀) = Qatlib.Foundations.PureStateMath.Ket j₀ := by simp [vtState, vtRunMatrix]
  have hstW0 : dataVtWordState stages history j₀ ([] : List DataVtStep) = Qatlib.Foundations.PureStateMath.Ket j₀ := by
    simp [dataVtWordState, dataVtWordMatrix]
  have hsp : ∀ k ≤ stages.length,
      0 < MeasureProb (vtState stages k (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C) := by
    intro k hk
    have h1 := (rdvt_sector_bridge stages history hl j₀ hs hrun k hk).1
    rw [← hpdef] at h1
    exact lt_of_lt_of_le hp0 h1
  have hR : ∀ k ≤ stages.length,
      MeasureProb (dataVtWordState stages history j₀
        (cascadeWord (recordDrivenSchedule stages.length ω) k)) (liveSet C)
      = MeasureProb (vtState stages k (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C) := by
    intro k
    induction k with
    | zero =>
      intro _
      have hw : cascadeWord (recordDrivenSchedule stages.length ω) 0
          = ([] : List DataVtStep) := rfl
      rw [hw, hstW0, hket1 _ hjlive, hst0, hket1 _ hjlive]
    | succ k ih =>
      intro hk
      have hkm : k < stages.length := by omega
      obtain ⟨α, hRj, hAj⟩ := rdvt_cascade_input_live stages history hl j₀ hj hs
        (recordDrivenSchedule stages.length ω) k (by omega)
      have hW : cascadeWord (recordDrivenSchedule stages.length ω) (k+1)
          = liveAAWord (cascadeWord (recordDrivenSchedule stages.length ω) k
              ++[DataVtStep.stageF k]) (recordDrivenSchedule stages.length ω k) := rfl
      have hLW : liveAAWord (cascadeWord (recordDrivenSchedule stages.length ω) k
          ++[DataVtStep.stageF k]) 0
          = cascadeWord (recordDrivenSchedule stages.length ω) k++[DataVtStep.stageF k] := by
        simp [liveAAWord]
      rw [hW, hsched0 k, hLW]
      have hsk :
          0 < MeasureProb (vtState stages k (Qatlib.Foundations.PureStateMath.Ket j₀))
          (liveSet C) := hsp k (by omega)
      have h2 : Complex.normSq α*(MeasureProb (vtState stages k (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C))
          = MeasureProb (vtState stages k (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C) :=
        hRj.symm.trans (ih (by omega))
      have hnm : Complex.normSq α = 1 := by nlinarith [h2, hsk]
      rw [hAj hkm, hnm, one_mul]
  refine ⟨hsched0, hR, ?_⟩
  rw [rdvt_cascade_time_unroll (recordDrivenSchedule stages.length ω) stages.length]
  have hprod1 : ∀ i ∈ Finset.Ico 0 stages.length,
      ∏ k ∈ Finset.Ico i stages.length,
        ((2*(recordDrivenSchedule stages.length ω k)+1 : ℕ) : ℝ) = 1 := by
    intro i _
    apply Finset.prod_eq_one
    intro k _
    rw [hsched0 k]
    norm_num
  rw [Finset.sum_congr rfl (fun i hi => by rw [hprod1 i hi, mul_one]),
    geom_sum_Ico (by norm_num : (2:ℝ) ≠ 1) (Nat.zero_le stages.length)]
  norm_num

/-- The sorted median of an odd family of values in `[0, 1]` also lies in `[0, 1]`. -/
private theorem rdvt_sorted_median_mem {r : ℕ} {v : Fin (2*r+1) → ℝ}
    (hb : ∀ i, v i ∈ Set.Icc (0:ℝ) 1) :
    sortedBlockMedian r v ∈ Set.Icc (0:ℝ) 1 := by
  have hlen : ((insertionSortCounted (List.ofFn v)).1).length = 2*r+1 := by
    rw [insertionSortCounted_length, List.length_ofFn]
  have hmem : (insertionSortCounted (List.ofFn v)).1.getD r 0
      ∈ (insertionSortCounted (List.ofFn v)).1 := by
    have hr : r < ((insertionSortCounted (List.ofFn v)).1).length := by omega
    rw [List.getD_eq_getElem _ _ hr]
    exact List.getElem_mem hr
  have hmem' : (insertionSortCounted (List.ofFn v)).1.getD r 0 ∈ List.ofFn v :=
    (List.Perm.mem_iff (insertionSortCounted_perm (List.ofFn v))).1 hmem
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem'
  have hfin : (insertionSortCounted (List.ofFn v)).1.getD r 0 ∈ Set.Icc (0:ℝ) 1 := hi ▸ hb i
  exact hfin

/-- Every record-driven median estimate lies in `[0, 1]`. -/
private theorem rdvt_median_range (M : ℕ) (l : RecordDrivenLabels M) :
    recordDrivenEstimate M l ∈ Set.Icc (0:ℝ) 1 := by
  show sortedBlockMedian (recordDrivenRepetitions M)
      (fun i => aeEstimate (recordDrivenResolution M) (l i)) ∈ Set.Icc (0:ℝ) 1
  apply rdvt_sorted_median_mem
  intro i
  constructor
  · exact sq_nonneg _
  · exact Real.sin_sq_le_one _

set_option maxHeartbeats 4000000 in

/-- The record-driven construction satisfies `RecordDrivenVariableTimeAlgorithm`, the stated
finite-record amplification specification associated with [Ambainis, Algorithm
3][Ambainis2012]. -/
theorem recordDrivenVariableTimeAlgorithm_answer : RecordDrivenVariableTimeAlgorithm := by
  intro C _ _ stages history hl hm j₀ hj hs m Ψ p hrun hfloor
  refine ⟨(recordDrivenLaw_probability stages history j₀ hl).1,
    (recordDrivenLaw_probability stages history j₀ hl).2,
    fun record => recordDriven_words_legal stages record,
    dataRecordGood (recordDrivenResolution stages.length) (recordDrivenRepetitions stages.length)
      (stages.length+1) stages history j₀ (recordDrivenInputWord stages.length),
    recordDriven_sharp_good_mass stages history j₀ hl hm, ?_⟩
  intro ω hω
  simp only [dataRecordGood, Finset.mem_filter, Finset.mem_univ, true_and] at hω
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hfloor
  have hWlegal : DataVtWordLegal stages
      (cascadeWord (recordDrivenSchedule m ω) m) := cascadeWord_legal stages _ m le_rfl
  have hWgl : MeasureProb (dataVtWordState stages history j₀
      (cascadeWord (recordDrivenSchedule m ω) m)) (goodSet C)
    = MeasureProb (dataVtWordState stages history j₀
      (cascadeWord (recordDrivenSchedule m ω) m)) (liveSet C) :=
    rdvt_cascade_good_eq_live stages history hl j₀ hj hs (recordDrivenSchedule m ω) hrun
  have hgp : p ≤ MeasureProb (dataVtWordState stages history j₀
      (cascadeWord (recordDrivenSchedule m ω) m)) (goodSet C) := by
    by_cases h16 : 16 < m
    · have hcl := rdvt_chain_large stages history hl hm j₀ hj hs hrun p hp0 hfloor
        (rfl : p = MeasureProb (vtState stages stages.length (Qatlib.Foundations.PureStateMath.Ket j₀)) (goodSet C)) h16 ω hω
      calc p = MeasureProb (vtState stages stages.length (Qatlib.Foundations.PureStateMath.Ket j₀)) (goodSet C) := rfl
        _ ≤ MeasureProb (vtState stages m (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C) :=
          (rdvt_sector_bridge stages history hl j₀ hs hrun m le_rfl).1
        _ ≤ MeasureProb (dataVtWordState stages history j₀
            (cascadeWord (recordDrivenSchedule m ω) m)) (liveSet C) := hcl.1 m le_rfl
        _ = MeasureProb (dataVtWordState stages history j₀
            (cascadeWord (recordDrivenSchedule m ω) m)) (goodSet C) := hWgl.symm
    · have hsmall : m ≤ 16 := by omega
      have hcs := rdvt_chain_small stages history hl hm j₀ hj hs hrun p hp0
        (rfl : p = MeasureProb (vtState stages stages.length (Qatlib.Foundations.PureStateMath.Ket j₀)) (goodSet C)) hsmall ω
      have hsm : MeasureProb (vtState stages m (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C)
          = MeasureProb (vtState stages stages.length (Qatlib.Foundations.PureStateMath.Ket j₀)) (goodSet C) := by
        have h1 := (rdvt_sector_bridge stages history hl j₀ hs hrun m le_rfl).1
        have h2 := (rdvt_sector_bridge stages history hl j₀ hs hrun m le_rfl).2
        rw [show MeasureProb (vtState stages m (Qatlib.Foundations.PureStateMath.Ket j₀)) (runningSet C) = 0 from hrun,
          _root_.add_zero] at h2
        exact le_antisymm h2 h1
      calc p = MeasureProb (vtState stages stages.length (Qatlib.Foundations.PureStateMath.Ket j₀)) (goodSet C) := rfl
        _ = MeasureProb (vtState stages m (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C) := hsm.symm
        _ = MeasureProb (dataVtWordState stages history j₀
            (cascadeWord (recordDrivenSchedule m ω) m)) (liveSet C) :=
          (hcs.2.1 m le_rfl).symm
        _ ≤ MeasureProb (dataVtWordState stages history j₀
            (cascadeWord (recordDrivenSchedule m ω) m)) (goodSet C) :=
          le_of_eq hWgl.symm
  have hAfloorG : 1/(10^12*(m:ℝ)^3) ≤ MeasureProb (dataVtWordState stages history j₀
      (cascadeWord (recordDrivenSchedule m ω) m)) (goodSet C) := le_trans hfloor hgp
  have hgp0 : 0 < MeasureProb (dataVtWordState stages history j₀
      (cascadeWord (recordDrivenSchedule m ω) m)) (goodSet C) := lt_of_lt_of_le hp0 hgp
  have hgnn : 0 ≤ MeasureProb (dataVtWordState stages history j₀
      (cascadeWord (recordDrivenSchedule m ω) m)) (goodSet C) := hgp0.le
  have hlastword : recordDrivenInputWord m ω (Fin.last m)
      = cascadeWord (recordDrivenSchedule m ω) m := by
    unfold recordDrivenInputWord
    rw [if_neg (by simp)]
  have hlast : |vtMedianEstimate (recordDrivenResolution m) (recordDrivenRepetitions m)
      (ω (Fin.last m)) - MeasureProb (dataVtWordState stages history j₀
      (recordDrivenInputWord m ω (Fin.last m))) (liveSet C)|
      ≤ dataEstimateRadius (MeasureProb (dataVtWordState stages history j₀
      (recordDrivenInputWord m ω (Fin.last m))) (liveSet C)) (recordDrivenResolution m) :=
    hω (Fin.last m)
  rw [hlastword] at hlast
  have hrad := recordDriven_floor_radius m hm (MeasureProb (dataVtWordState stages history j₀
    (cascadeWord (recordDrivenSchedule m ω) m)) (liveSet C)) (by
      rw [← hWgl]
      exact le_trans hfloor hgp)
  have hestG : |recordDrivenEstimate m (ω (Fin.last m)) - MeasureProb
      (dataVtWordState stages history j₀
      (cascadeWord (recordDrivenSchedule m ω) m)) (goodSet C)|
      ≤ MeasureProb (dataVtWordState stages history j₀
      (cascadeWord (recordDrivenSchedule m ω) m)) (goodSet C)/100 := by
    have h1 := hlast.trans hrad
    rw [← hWgl] at h1
    exact h1

  have hmdef : m = stages.length := rfl
  have hm1R : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hestle : recordDrivenEstimate m (ω (Fin.last m)) ≤ 1 :=
    (rdvt_median_range m (ω (Fin.last m))).2
  have hest98 : (99:ℝ)/100*MeasureProb (dataVtWordState stages history j₀
      (cascadeWord (recordDrivenSchedule m ω) m)) (goodSet C)
      ≤ recordDrivenEstimate m (ω (Fin.last m)) := by
    have h1 := (abs_le.mp hestG).1
    linarith
  have hgup : MeasureProb (dataVtWordState stages history j₀
      (cascadeWord (recordDrivenSchedule m ω) m)) (goodSet C) ≤ (100:ℝ)/99 := by
    linarith
  have hest0 : 0 < recordDrivenEstimate m (ω (Fin.last m)) := by
    have h1 : (0:ℝ) < (99:ℝ)/100*MeasureProb (dataVtWordState stages history j₀
      (cascadeWord (recordDrivenSchedule m ω) m)) (goodSet C) :=
      mul_pos (by norm_num) hgp0
    exact lt_of_lt_of_le h1 hest98
  have hsq0 : (Real.sin (((2*0+1 : ℕ) : ℝ)*Real.arcsin (Real.sqrt
      (recordDrivenEstimate m (ω (Fin.last m))))))^2
      = recordDrivenEstimate m (ω (Fin.last m)) := by
    have h1 : ((2*0+1 : ℕ) : ℝ) = 1 := by norm_num
    have h2 : Real.sqrt (recordDrivenEstimate m (ω (Fin.last m))) ≤ 1 :=
      (Real.sqrt_le_sqrt hestle).trans_eq (by norm_num : Real.sqrt ((1:ℝ)) = 1)
    have hs1 : (-1:ℝ) ≤ Real.sqrt (recordDrivenEstimate m (ω (Fin.last m))) := by
      have hn := Real.sqrt_nonneg (recordDrivenEstimate m (ω (Fin.last m)))
      linarith
    rw [h1, one_mul, Real.sin_arcsin hs1 h2]
    exact Real.sq_sqrt hest0.le
  have hcastd : ∀ k : ℕ, (2*((k:ℝ))+1)*Real.arcsin (Real.sqrt
      (recordDrivenEstimate m (ω (Fin.last m))))
      = ((2*k+1 : ℕ) : ℝ)*Real.arcsin (Real.sqrt
      (recordDrivenEstimate m (ω (Fin.last m)))) := by
    intro k
    push_cast
    ring
  have hex : ∃ k, k ≤ recordDrivenRoundCap m ∧ (1:ℝ)/2 ≤ (Real.sin (((2*k+1 : ℕ) : ℝ)*
      Real.arcsin (Real.sqrt (recordDrivenEstimate m (ω (Fin.last m))))))^2 := by
    by_cases hestbig : (1:ℝ)/2 ≤ recordDrivenEstimate m (ω (Fin.last m))
    · exact ⟨0, Nat.zero_le _, by rwa [hsq0]⟩
    · have hmR : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
      have hm3 : (0:ℝ) < (m:ℝ)^3 := pow_pos hmR 3
      have hD1 : (0:ℝ) < 10^12*(m:ℝ)^3 := mul_pos (by norm_num) hm3
      have hD2 : (0:ℝ) < 2*10^12*(m:ℝ)^3 := mul_pos (by norm_num) hm3
      have hestlb : 1/(2*10^12*(m:ℝ)^3) ≤ recordDrivenEstimate m (ω (Fin.last m)) := by
        have hAf := (div_le_iff₀ hD1).mp hAfloorG
        rw [div_le_iff₀ hD2]
        have hhalf : (1:ℝ)/2*MeasureProb (dataVtWordState stages history j₀
            (cascadeWord (recordDrivenSchedule m ω) m)) (goodSet C)
            ≤ (99:ℝ)/100*MeasureProb (dataVtWordState stages history j₀
            (cascadeWord (recordDrivenSchedule m ω) m)) (goodSet C) :=
          mul_le_mul_of_nonneg_right (by norm_num) hgnn
        calc (1:ℝ) ≤ MeasureProb (dataVtWordState stages history j₀
              (cascadeWord (recordDrivenSchedule m ω) m)) (goodSet C)*(10^12*(m:ℝ)^3) := hAf
          _ = (2*10^12*(m:ℝ)^3)*((1:ℝ)/2*MeasureProb (dataVtWordState stages history j₀
              (cascadeWord (recordDrivenSchedule m ω) m)) (goodSet C)) := by ring
          _ ≤ (2*10^12*(m:ℝ)^3)*((99:ℝ)/100*MeasureProb (dataVtWordState stages history j₀
              (cascadeWord (recordDrivenSchedule m ω) m)) (goodSet C)) :=
            mul_le_mul_of_nonneg_left hhalf hD2.le
          _ ≤ (2*10^12*(m:ℝ)^3)*(recordDrivenEstimate m (ω (Fin.last m))) :=
            mul_le_mul_of_nonneg_left hest98 hD2.le
          _ = recordDrivenEstimate m (ω (Fin.last m))*(2*10^12*(m:ℝ)^3) := by ring
      obtain ⟨kb, hkle, hPk⟩ := rdvt_final_crossing_exists hm
        (recordDrivenEstimate m (ω (Fin.last m))) hestlb (by linarith)
      exact ⟨kb, hkle, by rw [← hcastd kb]; exact hPk⟩
  obtain ⟨kf, hf, hkle, hP, hmin⟩ := bounded_first_crossing (recordDrivenRoundCap m)
    (fun k => (1:ℝ)/2 ≤ (Real.sin (((2*k+1 : ℕ) : ℝ)*
      Real.arcsin (Real.sqrt (recordDrivenEstimate m (ω (Fin.last m))))))^2) hex
  have hFR : recordDrivenFinalRounds m (ω (Fin.last m)) = kf := by
    unfold recordDrivenFinalRounds
    rw [hf]
    simp
  have houtW : recordDrivenOutputWord m ω
      = goodAAWord (cascadeWord (recordDrivenSchedule m ω) m) kf := by
    unfold recordDrivenOutputWord
    rw [hFR]
  have houttime : (dataVtWordTime (recordDrivenOutputWord m ω) : ℝ)
      = ((2*kf+1 : ℕ) : ℝ)*(dataVtWordTime (cascadeWord (recordDrivenSchedule m ω) m) : ℝ) := by
    rw [houtW, goodAAWord_time]
    push_cast
    ring

  have hNf : ((2*kf+1 : ℕ) : ℝ)*Real.sqrt (MeasureProb (dataVtWordState stages history j₀
      (cascadeWord (recordDrivenSchedule m ω) m)) (goodSet C)) ≤ 100/27 := by
    by_cases hk0 : kf = 0
    · rw [hk0]
      have h1 : ((2*0+1 : ℕ) : ℝ) = 1 := by norm_num
      rw [h1, one_mul]
      have hsqg2 : Real.sqrt (MeasureProb (dataVtWordState stages history j₀
          (cascadeWord (recordDrivenSchedule m ω) m)) (goodSet C)) ≤ 2 :=
        (Real.sqrt_le_sqrt hgup).trans
          ((Real.sqrt_le_sqrt (by norm_num : (100:ℝ)/99 ≤ 4)).trans_eq
            (by norm_num : Real.sqrt ((4:ℝ)) = 2))
      exact hsqg2.trans (by norm_num)
    · have hk1 : 1 ≤ kf := by omega
      have hestlt : recordDrivenEstimate m (ω (Fin.last m)) < 1/2 := by
        have hn := hmin 0 (by omega)
        have hn2 := lt_of_not_ge hn
        rw [hsq0] at hn2
        exact hn2
      have hmin' : ∀ j : ℕ, j < kf → (Real.sin ((2*((j:ℝ))+1)*Real.arcsin (Real.sqrt
          (recordDrivenEstimate m (ω (Fin.last m))))))^2 < 1/2 := by
        intro j hj
        have h2 := lt_of_not_ge (hmin j hj)
        rw [← hcastd j] at h2
        exact h2
      have hNest : (2*((kf:ℝ))+1)*Real.sqrt
          (recordDrivenEstimate m (ω (Fin.last m))) ≤ 10/3 :=
        rdvt_final_mult_bound hest0 hestlt hk1 hmin'
      have hsqg : Real.sqrt (MeasureProb (dataVtWordState stages history j₀
          (cascadeWord (recordDrivenSchedule m ω) m)) (goodSet C))
          ≤ (10:ℝ)/9*Real.sqrt (recordDrivenEstimate m (ω (Fin.last m))) := by
        have h9 : ((10:ℝ)/9*Real.sqrt (recordDrivenEstimate m (ω (Fin.last m))))^2
            = (100:ℝ)/81*recordDrivenEstimate m (ω (Fin.last m)) := by
          rw [mul_pow, Real.sq_sqrt hest0.le]
          norm_num
        have hle : MeasureProb (dataVtWordState stages history j₀
            (cascadeWord (recordDrivenSchedule m ω) m)) (goodSet C)
            ≤ ((10:ℝ)/9*Real.sqrt (recordDrivenEstimate m (ω (Fin.last m))))^2 := by
          rw [h9]
          linarith
        have hle' : (Real.sqrt (MeasureProb (dataVtWordState stages history j₀
            (cascadeWord (recordDrivenSchedule m ω) m)) (goodSet C)))^2
            ≤ ((10:ℝ)/9*Real.sqrt (recordDrivenEstimate m (ω (Fin.last m))))^2 := by
          rw [Real.sq_sqrt (rdvt_measure_nonneg _ _)]
          exact hle
        exact le_of_sq_le_sq hle'
          (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      calc ((2*kf+1 : ℕ) : ℝ)*Real.sqrt (MeasureProb (dataVtWordState stages history j₀
            (cascadeWord (recordDrivenSchedule m ω) m)) (goodSet C))
          ≤ ((2*kf+1 : ℕ) : ℝ)*((10:ℝ)/9*Real.sqrt
              (recordDrivenEstimate m (ω (Fin.last m)))) :=
            mul_le_mul_of_nonneg_left hsqg (by positivity)
        _ = (10:ℝ)/9*((2*((kf:ℝ))+1)*Real.sqrt
              (recordDrivenEstimate m (ω (Fin.last m)))) := by
            push_cast
            ring
        _ ≤ (10:ℝ)/9*(10/3) := mul_le_mul_of_nonneg_left hNest (by norm_num)
        _ = 100/27 := by norm_num

  have hlargeOT : ∀ Nf : ℕ, ((Nf : ℝ))*Real.sqrt (MeasureProb (dataVtWordState stages history j₀
      (cascadeWord (recordDrivenSchedule m ω) m)) (goodSet C)) ≤ 100/27 →
      ((Nf : ℝ))*(dataVtWordTime (cascadeWord (recordDrivenSchedule m ω) m) : ℝ) ≤
      1000*(m:ℝ)^2*(vtTmax stages + reachedTav stages history j₀/Real.sqrt p) := by
    intro Nf hNfG
    have hASTB := averageStopTailBound_answer C stages history hl j₀ hj hs hrun
    by_cases h16 : 16 < m
    · have hcl := rdvt_chain_large stages history hl hm j₀ hj hs hrun p hp0 hfloor
        (rfl : p = MeasureProb (vtState stages stages.length (Qatlib.Foundations.PureStateMath.Ket j₀)) (goodSet C)) h16 ω hω
      have hmR : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)

      have hg0m : (1:ℝ)/5 ≤ (1-4/(5*((m:ℝ))))^m := by
        have hne : (5:ℝ)*((m:ℝ)) ≠ 0 := by nlinarith [hmR]
        have hD : (0:ℝ) < 5*((m:ℝ)) := by nlinarith [hmR]
        have ha : (-2:ℝ) ≤ -4/(5*((m:ℝ))) := by
          rw [le_div_iff₀ (by nlinarith [hmR] : (0:ℝ) < 5*((m:ℝ)))]
          nlinarith [hmR]
        have hb := one_add_mul_le_pow ha m
        have hmul : (m:ℝ)*(-4/(5*((m:ℝ)))) = -4/5 := by
          field_simp
        calc (1:ℝ)/5 = 1+(m:ℝ)*(-4/(5*((m:ℝ)))) := by rw [hmul]; ring
          _ ≤ (1 + -4/(5*((m:ℝ))))^m := hb
          _ = (1-4/(5*((m:ℝ))))^m := by ring
      have hgamma : ∀ i : ℕ, i ≤ m → (1:ℝ)/5 ≤ ∏ k ∈ Finset.Ico i m,
          (if recordDrivenSchedule m ω k = 0 then (1:ℝ) else 1-4/(5*((m:ℝ)))) := by
        intro i hi
        have hD2 : (Finset.Ico i m).card ≤ m := by simp
        have hfacge : ∀ k : ℕ, (1-4/(5*((m:ℝ))))
            ≤ (if recordDrivenSchedule m ω k = 0 then (1:ℝ) else 1-4/(5*((m:ℝ)))) := by
          intro k
          by_cases h : recordDrivenSchedule m ω k = 0
          · rw [if_pos h]
            have hmR2 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
            have h4 : (0:ℝ) ≤ 4/(5*((m:ℝ))) :=
              div_nonneg (by norm_num) (by nlinarith [hmR2] : (0:ℝ) ≤ 5*((m:ℝ)))
            linarith
          · rw [if_neg h]
        have hstep1 : (1-4/(5*((m:ℝ))))^(Finset.Ico i m).card
            ≤ ∏ k ∈ Finset.Ico i m,
              (if recordDrivenSchedule m ω k = 0 then (1:ℝ) else 1-4/(5*((m:ℝ)))) := by
          rw [← Finset.prod_const]
          exact Finset.prod_le_prod₀
            (fun k _ => by
              have : (0:ℝ) < 5*((m:ℝ)) := by nlinarith [hmR]
              have : (0:ℝ) ≤ 1-4/(5*((m:ℝ))) := by
                rw [sub_nonneg, div_le_iff₀ this]
                nlinarith [hmR]
              linarith)
            (fun k _ => hfacge k)
        have hanti : ∀ a : ℝ, 0 ≤ a → a ≤ 1 → ∀ d k : ℕ, a^(k+d) ≤ a^k := by
          intro a ha0 ha1 d
          induction d with
          | zero => intro k; rw [Nat.add_zero]
          | succ d ih =>
              intro k
              have hstep : a^(k+d+1) ≤ a^(k+d) := by
                rw [pow_succ]
                calc a^(k+d)*a ≤ a^(k+d)*1 :=
                      mul_le_mul_of_nonneg_left ha1 (pow_nonneg ha0 _)
                  _ = a^(k+d) := mul_one _
              exact hstep.trans (ih k)
        have hbase0 : (0:ℝ) ≤ 1-4/(5*((m:ℝ))) := by
          have h5 : (0:ℝ) < 5*((m:ℝ)) := by nlinarith [hmR]
          rw [sub_nonneg, div_le_iff₀ h5]
          nlinarith [hmR]
        have hbase1 : 1-4/(5*((m:ℝ))) ≤ 1 := by
          have h4 : (0:ℝ) ≤ 4/(5*((m:ℝ))) :=
            div_nonneg (by norm_num) (by nlinarith [hmR] : (0:ℝ) ≤ 5*((m:ℝ)))
          linarith
        have hstep2 : (1-4/(5*((m:ℝ))))^m ≤ (1-4/(5*((m:ℝ))))^(Finset.Ico i m).card := by
          have hcard := hanti _ hbase0 hbase1 (m-(Finset.Ico i m).card) (Finset.Ico i m).card
          rwa [Nat.add_sub_cancel' hD2] at hcard
        exact hg0m.trans (hstep2.trans hstep1)

      have hkey : ∀ i ∈ Finset.Ico 0 m, (1:ℝ)/5*(∏ k ∈ Finset.Ico i m,
            ((2*(recordDrivenSchedule m ω k)+1 : ℕ) : ℝ))^2
          *MeasureProb (dataVtWordState stages history j₀
            (cascadeWord (recordDrivenSchedule m ω) i)) (liveSet C)
          *MeasureProb (vtState stages m (Qatlib.Foundations.PureStateMath.Ket j₀)) (goodSet C)
          ≤ MeasureProb (dataVtWordState stages history j₀
              (cascadeWord (recordDrivenSchedule m ω) m)) (liveSet C)
            *MeasureProb (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C) := by
        intro i hi
        have hicard : i ≤ m := (Finset.mem_Ico.mp hi).2.le
        have hch : (∏ k ∈ Finset.Ico i m, ((if recordDrivenSchedule m ω k = 0 then (1:ℝ)
              else 1-4/(5*((m:ℝ))))*(((2*(recordDrivenSchedule m ω k)+1 : ℕ) : ℝ))^2))
            *MeasureProb (dataVtWordState stages history j₀
              (cascadeWord (recordDrivenSchedule m ω) i)) (liveSet C)
            *MeasureProb (vtState stages m (Qatlib.Foundations.PureStateMath.Ket j₀)) (goodSet C)
          ≤ MeasureProb (dataVtWordState stages history j₀
              (cascadeWord (recordDrivenSchedule m ω) m)) (liveSet C)
            *MeasureProb (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C) := by
            have hsm' : MeasureProb (vtState stages m (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C)
                = MeasureProb (vtState stages m (Qatlib.Foundations.PureStateMath.Ket j₀)) (goodSet C) := by
              have h1 := (rdvt_sector_bridge stages history hl j₀ hs hrun m le_rfl).1
              have h2 := (rdvt_sector_bridge stages history hl j₀ hs hrun m le_rfl).2
              rw [show MeasureProb (vtState stages m (Qatlib.Foundations.PureStateMath.Ket j₀)) (runningSet C) = 0 from hrun,
                _root_.add_zero] at h2
              exact le_antisymm h2 h1
            have hcl' := hcl.2.2 i hicard
            have hsm2 : MeasureProb (vtState stages stages.length (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C)
                = MeasureProb (vtState stages stages.length (Qatlib.Foundations.PureStateMath.Ket j₀)) (goodSet C) := hsm'
            rw [hsm2] at hcl'
            simp only [← hmdef] at hcl'
            exact hcl'
        have hsplit : (∏ k ∈ Finset.Ico i m, ((if recordDrivenSchedule m ω k = 0 then (1:ℝ)
              else 1-4/(5*((m:ℝ))))*(((2*(recordDrivenSchedule m ω k)+1 : ℕ) : ℝ))^2))
            = (∏ k ∈ Finset.Ico i m, (if recordDrivenSchedule m ω k = 0 then (1:ℝ)
              else 1-4/(5*((m:ℝ)))))*(∏ k ∈ Finset.Ico i m,
              (((2*(recordDrivenSchedule m ω k)+1 : ℕ) : ℝ))^2) := Finset.prod_mul_distrib
        have hsplit2 : (∏ k ∈ Finset.Ico i m, (((2*(recordDrivenSchedule m ω k)+1 : ℕ) : ℝ))^2)
            = (∏ k ∈ Finset.Ico i m, ((2*(recordDrivenSchedule m ω k)+1 : ℕ) : ℝ))^2 := by
          rw [Finset.prod_pow]
        rw [hsplit, hsplit2] at hch
        have h1 : (1:ℝ)/5*(∏ k ∈ Finset.Ico i m,
            ((2*(recordDrivenSchedule m ω k)+1 : ℕ) : ℝ))^2
            ≤ (∏ k ∈ Finset.Ico i m, (if recordDrivenSchedule m ω k = 0 then (1:ℝ)
              else 1-4/(5*((m:ℝ)))))*(∏ k ∈ Finset.Ico i m,
            ((2*(recordDrivenSchedule m ω k)+1 : ℕ) : ℝ))^2 :=
          mul_le_mul_of_nonneg_right (hgamma i hicard) (sq_nonneg _)
        have h1' : (1:ℝ)/5*(∏ k ∈ Finset.Ico i m,
              ((2*(recordDrivenSchedule m ω k)+1 : ℕ) : ℝ))^2
              *MeasureProb (dataVtWordState stages history j₀
                (cascadeWord (recordDrivenSchedule m ω) i)) (liveSet C)
              *MeasureProb (vtState stages m (Qatlib.Foundations.PureStateMath.Ket j₀)) (goodSet C)
            ≤ (∏ k ∈ Finset.Ico i m, (if recordDrivenSchedule m ω k = 0 then (1:ℝ)
              else 1-4/(5*((m:ℝ)))))*(∏ k ∈ Finset.Ico i m,
              ((2*(recordDrivenSchedule m ω k)+1 : ℕ) : ℝ))^2
              *MeasureProb (dataVtWordState stages history j₀
                (cascadeWord (recordDrivenSchedule m ω) i)) (liveSet C)
              *MeasureProb (vtState stages m (Qatlib.Foundations.PureStateMath.Ket j₀)) (goodSet C) := by
          have hmul : (1:ℝ)/5*(∏ k ∈ Finset.Ico i m,
                ((2*(recordDrivenSchedule m ω k)+1 : ℕ) : ℝ))^2
                *(MeasureProb (dataVtWordState stages history j₀
                  (cascadeWord (recordDrivenSchedule m ω) i)) (liveSet C)
                *MeasureProb (vtState stages m (Qatlib.Foundations.PureStateMath.Ket j₀)) (goodSet C))
            ≤ (∏ k ∈ Finset.Ico i m, (if recordDrivenSchedule m ω k = 0 then (1:ℝ)
                else 1-4/(5*((m:ℝ)))))*(∏ k ∈ Finset.Ico i m,
                  ((2*(recordDrivenSchedule m ω k)+1 : ℕ) : ℝ))^2
                *(MeasureProb (dataVtWordState stages history j₀
                  (cascadeWord (recordDrivenSchedule m ω) i)) (liveSet C)
                *MeasureProb (vtState stages m (Qatlib.Foundations.PureStateMath.Ket j₀)) (goodSet C)) :=
            mul_le_mul_of_nonneg_right h1
              (mul_nonneg (rdvt_measure_nonneg _ _) hp0.le)
          calc (1:ℝ)/5*(∏ k ∈ Finset.Ico i m,
                ((2*(recordDrivenSchedule m ω k)+1 : ℕ) : ℝ))^2
                *MeasureProb (dataVtWordState stages history j₀
                  (cascadeWord (recordDrivenSchedule m ω) i)) (liveSet C)
                *MeasureProb (vtState stages m (Qatlib.Foundations.PureStateMath.Ket j₀)) (goodSet C)
              = (1:ℝ)/5*(∏ k ∈ Finset.Ico i m,
                  ((2*(recordDrivenSchedule m ω k)+1 : ℕ) : ℝ))^2
                  *(MeasureProb (dataVtWordState stages history j₀
                    (cascadeWord (recordDrivenSchedule m ω) i)) (liveSet C)
                  *MeasureProb (vtState stages m (Qatlib.Foundations.PureStateMath.Ket j₀)) (goodSet C)) := by ring
            _ ≤ (∏ k ∈ Finset.Ico i m, (if recordDrivenSchedule m ω k = 0 then (1:ℝ)
                  else 1-4/(5*((m:ℝ)))))*(∏ k ∈ Finset.Ico i m,
                  ((2*(recordDrivenSchedule m ω k)+1 : ℕ) : ℝ))^2
                  *(MeasureProb (dataVtWordState stages history j₀
                    (cascadeWord (recordDrivenSchedule m ω) i)) (liveSet C)
                  *MeasureProb (vtState stages m (Qatlib.Foundations.PureStateMath.Ket j₀)) (goodSet C)) := hmul
            _ = (∏ k ∈ Finset.Ico i m, (if recordDrivenSchedule m ω k = 0 then (1:ℝ)
                  else 1-4/(5*((m:ℝ)))))*(∏ k ∈ Finset.Ico i m,
                  ((2*(recordDrivenSchedule m ω k)+1 : ℕ) : ℝ))^2
                  *MeasureProb (dataVtWordState stages history j₀
                    (cascadeWord (recordDrivenSchedule m ω) i)) (liveSet C)
                  *MeasureProb (vtState stages m (Qatlib.Foundations.PureStateMath.Ket j₀)) (goodSet C) := by ring
        exact h1'.trans hch

      have hLlow : ∀ i ∈ Finset.Ico 0 m, (1:ℝ)/(7*((m:ℝ))) ≤ MeasureProb
          (dataVtWordState stages history j₀
            (cascadeWord (recordDrivenSchedule m ω) i)) (liveSet C) := by
        intro i hi
        rcases Nat.eq_zero_or_pos i with rfl | hipos
        · have h0w : cascadeWord (recordDrivenSchedule m ω) 0
              = ([] : List DataVtStep) := rfl
          have hjlive : j₀ ∈ liveSet C := by
            simp only [liveSet, Finset.mem_union]
            exact Or.inr (by simp [runningSet, hj])
          have hsw0 : dataVtWordState stages history j₀ ([] : List DataVtStep) = Qatlib.Foundations.PureStateMath.Ket j₀ := by
            simp [dataVtWordState, dataVtWordMatrix]
          have hket1 : MeasureProb (Qatlib.Foundations.PureStateMath.Ket j₀) (liveSet C) = 1 := by
            unfold MeasureProb BornProb
            rw [Finset.sum_eq_single_of_mem j₀ hjlive (fun q hq hne => by simp [Qatlib.Foundations.PureStateMath.Ket, hne])]
            simp [Qatlib.Foundations.PureStateMath.Ket]
          rw [h0w, hsw0, hket1]
          have hmR2 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
          rw [div_le_iff₀ (by nlinarith [hmR2] : (0:ℝ) < 7*((m:ℝ)))]
          have h7 : (7:ℝ)*1 ≤ 7*((m:ℝ)) := mul_le_mul_of_nonneg_left hm1R (by norm_num)
          linarith
        · exact hcl.2.1 i (Finset.mem_Ico.mp hi).2.le hipos

      have hseg : ∀ i ∈ Finset.Ico 0 m,
          ((Nf : ℝ))*(∏ k ∈ Finset.Ico i m, ((2*(recordDrivenSchedule m ω k)+1 : ℕ) : ℝ))
          ≤ 22*Real.sqrt ((m:ℝ))*(1+Real.sqrt (MeasureProb (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀))
              (runningSet C))/Real.sqrt p) := by
        intro i hi
        have hicard : i ≤ m := (Finset.mem_Ico.mp hi).2.le
        have hkeyi := hkey i hi
        have hLlowi := hLlow i hi
        have hruni :=
            rdvt_measure_nonneg (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀))
            (runningSet C)
        have hsrun : MeasureProb (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C)
            ≤ p+MeasureProb (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) (runningSet C) :=
          (rdvt_sector_bridge stages history hl j₀ hs hrun i hicard).2
        have hm7 : (0:ℝ) < 7*((m:ℝ)) := by nlinarith [hmR]

        have hB : (((Nf : ℝ))*(∏ k ∈ Finset.Ico i m,
              ((2*(recordDrivenSchedule m ω k)+1 : ℕ) : ℝ)))^2*((1:ℝ)/(7*((m:ℝ))))*p
            ≤ (50000:ℝ)/729*(p+MeasureProb (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) (runningSet C)) := by
          have hstepA : (((Nf : ℝ))*(∏ k ∈ Finset.Ico i m,
                ((2*(recordDrivenSchedule m ω k)+1 : ℕ) : ℝ)))^2*((1:ℝ)/(7*((m:ℝ))))*p
              ≤ (((Nf : ℝ))*(∏ k ∈ Finset.Ico i m,
                ((2*(recordDrivenSchedule m ω k)+1 : ℕ) : ℝ)))^2*(MeasureProb
                (dataVtWordState stages history j₀
                  (cascadeWord (recordDrivenSchedule m ω) i)) (liveSet C)*p) := by
            rw [show (((Nf : ℝ))*(∏ k ∈ Finset.Ico i m,
                ((2*(recordDrivenSchedule m ω k)+1 : ℕ) : ℝ)))^2*((1:ℝ)/(7*((m:ℝ))))*p
              = (((Nf : ℝ))*(∏ k ∈ Finset.Ico i m,
                ((2*(recordDrivenSchedule m ω k)+1 : ℕ) : ℝ)))^2*(((1:ℝ)/(7*((m:ℝ))))*p) from by
              ring]
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hLlowi hp0.le) (sq_nonneg _)
          have hstepB : (((Nf : ℝ))*(∏ k ∈ Finset.Ico i m,
                ((2*(recordDrivenSchedule m ω k)+1 : ℕ) : ℝ)))^2*(MeasureProb
                (dataVtWordState stages history j₀
                  (cascadeWord (recordDrivenSchedule m ω) i)) (liveSet C)*p)
              ≤ (50000:ℝ)/729*(MeasureProb (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C)) := by
            have hrew : (((Nf : ℝ))*(∏ k ∈ Finset.Ico i m,
                  ((2*(recordDrivenSchedule m ω k)+1 : ℕ) : ℝ)))^2*(MeasureProb
                  (dataVtWordState stages history j₀
                    (cascadeWord (recordDrivenSchedule m ω) i)) (liveSet C)*p)
                = ((Nf : ℝ))^2*((1:ℝ)/5*(∏ k ∈ Finset.Ico i m,
                    ((2*(recordDrivenSchedule m ω k)+1 : ℕ) : ℝ))^2
                  *MeasureProb (dataVtWordState stages history j₀
                    (cascadeWord (recordDrivenSchedule m ω) i)) (liveSet C)
                  *MeasureProb (vtState stages m (Qatlib.Foundations.PureStateMath.Ket j₀)) (goodSet C))*5 := by
              rw [mul_pow]; ring
            have hsqW : ((Nf : ℝ))^2*(MeasureProb (dataVtWordState stages history j₀
                  (cascadeWord (recordDrivenSchedule m ω) m)) (goodSet C))
                ≤ (100/27)^2 := by
              have h1 := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _)
                (Real.sqrt_nonneg _)) hNfG 2
              rwa [mul_pow, Real.sq_sqrt (rdvt_measure_nonneg _ _)] at h1
            calc (((Nf : ℝ))*(∏ k ∈ Finset.Ico i m,
                  ((2*(recordDrivenSchedule m ω k)+1 : ℕ) : ℝ)))^2*(MeasureProb
                  (dataVtWordState stages history j₀
                    (cascadeWord (recordDrivenSchedule m ω) i)) (liveSet C)*p)
                = ((Nf : ℝ))^2*((1:ℝ)/5*(∏ k ∈ Finset.Ico i m,
                    ((2*(recordDrivenSchedule m ω k)+1 : ℕ) : ℝ))^2
                  *MeasureProb (dataVtWordState stages history j₀
                    (cascadeWord (recordDrivenSchedule m ω) i)) (liveSet C)
                  *MeasureProb (vtState stages m (Qatlib.Foundations.PureStateMath.Ket j₀)) (goodSet C))*5 := hrew
              _ ≤ ((Nf : ℝ))^2*(MeasureProb (dataVtWordState stages history j₀
                    (cascadeWord (recordDrivenSchedule m ω) m)) (liveSet C)
                  *MeasureProb (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C))*5 :=
                  mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left hkeyi (pow_nonneg (Nat.cast_nonneg _) 2))
                    (by norm_num : (0:ℝ) ≤ 5)
              _ = 5*((Nf : ℝ))^2*(MeasureProb (dataVtWordState stages history j₀
                    (cascadeWord (recordDrivenSchedule m ω) m)) (goodSet C))
                *MeasureProb (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C) := by
                  rw [hWgl]; ring
              _ ≤ 5*((100/27)^2)*MeasureProb (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C) := by
                  have hLnn : (0:ℝ) ≤ MeasureProb (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀))
                      (liveSet C) := rdvt_measure_nonneg _ _
                  have hgrow := mul_le_mul_of_nonneg_right hsqW hLnn
                  have hfin := mul_le_mul_of_nonneg_left hgrow
                    (by norm_num : (0:ℝ) ≤ 5)
                  calc 5*((Nf : ℝ))^2*(MeasureProb (dataVtWordState stages history j₀
                        (cascadeWord (recordDrivenSchedule m ω) m)) (goodSet C))
                        *MeasureProb (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C)
                      = 5*(((Nf : ℝ))^2*(MeasureProb (dataVtWordState stages history j₀
                          (cascadeWord (recordDrivenSchedule m ω) m)) (goodSet C))
                        *MeasureProb (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C)) := by ring
                    _ ≤ 5*((100/27)^2*MeasureProb (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀))
                        (liveSet C)) := hfin
                    _ = 5*((100/27)^2)*MeasureProb (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀))
                        (liveSet C) := by ring
              _ = (50000:ℝ)/729*MeasureProb (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C) := by
                  norm_num
          exact hstepA.trans (hstepB.trans (mul_le_mul_of_nonneg_left hsrun (by norm_num)))

        have hC : (((Nf : ℝ))*(∏ k ∈ Finset.Ico i m,
              ((2*(recordDrivenSchedule m ω k)+1 : ℕ) : ℝ)))^2*p
            ≤ 484*((m:ℝ))*(p+MeasureProb (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) (runningSet C)) := by
          have hc2 : (7*((m:ℝ)))*((1:ℝ)/(7*((m:ℝ)))) = 1 := by
            rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hm7)]
          have h1' : (7*((m:ℝ)))*((((Nf : ℝ))*(∏ k ∈ Finset.Ico i m,
                ((2*(recordDrivenSchedule m ω k)+1 : ℕ) : ℝ)))^2*((1:ℝ)/(7*((m:ℝ))))*p)
              = (((Nf : ℝ))*(∏ k ∈ Finset.Ico i m,
                ((2*(recordDrivenSchedule m ω k)+1 : ℕ) : ℝ)))^2*p := by
            calc (7*((m:ℝ)))*((((Nf : ℝ))*(∏ k ∈ Finset.Ico i m,
                    ((2*(recordDrivenSchedule m ω k)+1 : ℕ) : ℝ)))^2*((1:ℝ)/(7*((m:ℝ))))*p)
                = ((7*((m:ℝ)))*((1:ℝ)/(7*((m:ℝ)))))*((((Nf : ℝ))*(∏ k ∈ Finset.Ico i m,
                    ((2*(recordDrivenSchedule m ω k)+1 : ℕ) : ℝ)))^2*p) := by ring
              _ = 1*((((Nf : ℝ))*(∏ k ∈ Finset.Ico i m,
                  ((2*(recordDrivenSchedule m ω k)+1 : ℕ) : ℝ)))^2*p) := by rw [hc2]
              _ = (((Nf : ℝ))*(∏ k ∈ Finset.Ico i m,
                  ((2*(recordDrivenSchedule m ω k)+1 : ℕ) : ℝ)))^2*p := one_mul _
          have h479 : (7:ℝ)*(50000/729) ≤ 484 := by norm_num
          have hmnng : (0:ℝ) ≤ (m:ℝ) := by nlinarith [hmR]
          calc (((Nf : ℝ))*(∏ k ∈ Finset.Ico i m,
                ((2*(recordDrivenSchedule m ω k)+1 : ℕ) : ℝ)))^2*p
              = (7*((m:ℝ)))*((((Nf : ℝ))*(∏ k ∈ Finset.Ico i m,
                  ((2*(recordDrivenSchedule m ω k)+1 : ℕ) : ℝ)))^2*((1:ℝ)/(7*((m:ℝ))))*p) :=
                h1'.symm
            _ ≤ (7*((m:ℝ)))*((50000:ℝ)/729*(p+MeasureProb (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀))
                (runningSet C))) := mul_le_mul_of_nonneg_left hB hm7.le
            _ = ((7*((m:ℝ)))*(50000/729))*(p+MeasureProb (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀))
                (runningSet C)) := by ring
            _ ≤ 484*((m:ℝ))*(p+MeasureProb (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) (runningSet C)) := by
                have h479m : (7*((m:ℝ)))*(50000/729) ≤ 484*((m:ℝ)) := by
                  rw [show (7*((m:ℝ)))*(50000/729) = (7*(50000/729))*((m:ℝ)) from by ring]
                  exact mul_le_mul_of_nonneg_right h479 hmnng
                exact mul_le_mul_of_nonneg_right h479m (add_nonneg hp0.le hruni)

        have hD : (((Nf : ℝ))*(∏ k ∈ Finset.Ico i m,
              ((2*(recordDrivenSchedule m ω k)+1 : ℕ) : ℝ)))^2
            ≤ 484*((m:ℝ))*(1+MeasureProb (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀))
              (runningSet C)/p) := by
          have hE : (p+MeasureProb (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) (runningSet C))/p
              = 1+MeasureProb (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) (runningSet C)/p := by
            rw [add_div, div_self hp0.ne']
          rw [← hE, ← mul_div_assoc, le_div_iff₀ hp0]
          exact hC

        have hnon : (0:ℝ) ≤ 22*Real.sqrt ((m:ℝ))*(1+Real.sqrt (MeasureProb
            (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) (runningSet C))/Real.sqrt p) :=
          mul_nonneg (by norm_num) (add_nonneg (by norm_num)
            (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
        refine le_of_sq_le_sq ?_ hnon
        have hsple : (1:ℝ)+MeasureProb (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) (runningSet C)/p
            ≤ (1+Real.sqrt (MeasureProb (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀))
              (runningSet C))/Real.sqrt p)^2 := by
          have hsd : Real.sqrt (MeasureProb (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) (runningSet C))
              /Real.sqrt p = Real.sqrt (MeasureProb (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀))
              (runningSet C)/p) := (Real.sqrt_div hruni p).symm
          rw [hsd]
          have ht2 : (Real.sqrt (MeasureProb (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀))
              (runningSet C)/p))^2 = MeasureProb (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀))
            (runningSet C)/p := Real.sq_sqrt (div_nonneg hruni hp0.le)
          nlinarith [Real.sqrt_nonneg (MeasureProb (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀))
            (runningSet C)/p)]
        have hsplit : (22*Real.sqrt ((m:ℝ)))^2
            = (22:ℝ)^2*((m:ℝ)) := by
          rw [mul_pow, Real.sq_sqrt (by nlinarith [hmR] : (0:ℝ) ≤ (m:ℝ))]
        have hmid : (((Nf : ℝ))*(∏ k ∈ Finset.Ico i m,
              ((2*(recordDrivenSchedule m ω k)+1 : ℕ) : ℝ)))^2
            ≤ (22*Real.sqrt ((m:ℝ)))^2*(1+MeasureProb (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀))
              (runningSet C)/p) := by
          have h22 : (22:ℝ)^2 = 484 := by norm_num
          rw [hsplit, h22]
          exact hD
        have hcomb : (22*Real.sqrt ((m:ℝ)))^2*(1+Real.sqrt (MeasureProb
            (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) (runningSet C))/Real.sqrt p)^2
            = (22*Real.sqrt ((m:ℝ))*(1+Real.sqrt (MeasureProb (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀))
              (runningSet C))/Real.sqrt p))^2 := by ring
        rw [← hcomb]
        exact hmid.trans (mul_le_mul_of_nonneg_left hsple
          (pow_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) 2))

      have hun := rdvt_cascade_time_unroll (recordDrivenSchedule m ω) m
      have hsumB := hASTB.2
      rw [Finset.range_eq_Ico] at hsumB
      have hgeom : ∑ i ∈ Finset.Ico 0 m, (2:ℝ)^i ≤ (2:ℝ)^m-1 := by
        rw [geom_sum_Ico (by norm_num : (2:ℝ) ≠ 1) (Nat.zero_le m)]
        norm_num
      have hsqrtem : Real.sqrt ((m:ℝ)) ≤ (m:ℝ) := by
        refine (Real.sqrt_le_sqrt ?_).trans_eq
          (Real.sqrt_mul_self (by nlinarith [hmR] : (0:ℝ) ≤ (m:ℝ)))
        nlinarith [hmR]
      rw [hun, Finset.mul_sum]
      have hterm : ∀ i ∈ Finset.Ico 0 m, ((2:ℝ)^i)*(((Nf : ℝ))*(∏ k ∈ Finset.Ico i m,
            ((2*(recordDrivenSchedule m ω k)+1 : ℕ) : ℝ)))
          ≤ (2:ℝ)^i*(22*Real.sqrt ((m:ℝ)))+((2:ℝ)^i*(22*Real.sqrt ((m:ℝ))))*Real.sqrt
            (MeasureProb (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) (runningSet C))/Real.sqrt p := by
        intro i hi
        have h := hseg i hi
        have h2 : (2:ℝ)^i*(22*Real.sqrt ((m:ℝ))*(1+Real.sqrt (MeasureProb
            (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) (runningSet C))/Real.sqrt p))
            = (2:ℝ)^i*(22*Real.sqrt ((m:ℝ)))+((2:ℝ)^i*(22*Real.sqrt ((m:ℝ))))*Real.sqrt
            (MeasureProb (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) (runningSet C))/Real.sqrt p := by ring
        rw [← h2]
        exact mul_le_mul_of_nonneg_left h (pow_nonneg (by norm_num) i)
      have hterm2 : ∀ i ∈ Finset.Ico 0 m, ((2:ℝ)^i)*(((Nf : ℝ))*(∏ k ∈ Finset.Ico i m,
            ((2*(recordDrivenSchedule m ω k)+1 : ℕ) : ℝ)))
          = (Nf:ℝ)*((2:ℝ)^i*(∏ k ∈ Finset.Ico i m,
            ((2*(recordDrivenSchedule m ω k)+1 : ℕ) : ℝ))) := by
        intro i _; ring
      rw [Finset.sum_congr rfl (fun i hi => (hterm2 i hi).symm)]
      have hsumA : ∑ i ∈ Finset.Ico 0 m, (2:ℝ)^i*(22*Real.sqrt ((m:ℝ)))
          = (22*Real.sqrt ((m:ℝ)))*∑ i ∈ Finset.Ico 0 m, (2:ℝ)^i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
      have hsumB' : ∑ i ∈ Finset.Ico 0 m, ((2:ℝ)^i*(22*Real.sqrt ((m:ℝ))))*Real.sqrt
            (MeasureProb (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) (runningSet C))/Real.sqrt p
          = (22*Real.sqrt ((m:ℝ))/Real.sqrt p)*(∑ i ∈ Finset.Ico 0 m, (2:ℝ)^i*Real.sqrt
            (MeasureProb (vtState stages i (Qatlib.Foundations.PureStateMath.Ket j₀)) (runningSet C))) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      have hc0 : (0:ℝ) ≤ 22*Real.sqrt ((m:ℝ))/Real.sqrt p :=
        div_nonneg (by norm_num) (Real.sqrt_nonneg _)
      have hU1 : (22*Real.sqrt ((m:ℝ)))*((2:ℝ)^m-1) ≤ 1000*((m:ℝ))^2*(2:ℝ)^m := by
        have h1 : (2:ℝ)^m-1 ≤ (2:ℝ)^m := by
          nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 2) m]
        have h2 : 22*Real.sqrt ((m:ℝ)) ≤ 1000*((m:ℝ))^2 := by nlinarith [hsqrtem, hm1R]
        calc (22*Real.sqrt ((m:ℝ)))*((2:ℝ)^m-1) ≤ (22*Real.sqrt ((m:ℝ)))*((2:ℝ)^m) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ ≤ 1000*((m:ℝ))^2*((2:ℝ)^m) := by
              rw [show 1000*((m:ℝ))^2*((2:ℝ)^m) = (1000*((m:ℝ))^2)*((2:ℝ)^m) from by ring]
              exact mul_le_mul_of_nonneg_right h2 (pow_nonneg (by norm_num) m)
      have hTavnn : (0:ℝ) ≤ reachedTav stages history j₀ := Real.sqrt_nonneg _
      have hU2 : (22*Real.sqrt ((m:ℝ))/Real.sqrt p)*(Real.sqrt ((stages.length : ℝ))
            *reachedTav stages history j₀)
          ≤ 1000*((m:ℝ))^2*(reachedTav stages history j₀/Real.sqrt p) := by
        have hmmsq : Real.sqrt ((m:ℝ))*Real.sqrt ((m:ℝ)) = (m:ℝ) :=
          Real.mul_self_sqrt (by nlinarith [hmR] : (0:ℝ) ≤ (m:ℝ))
        have hmcast : ((stages.length : ℝ)) = (m:ℝ) := by rw [hmdef]
        have ht1 : (22*Real.sqrt ((m:ℝ))/Real.sqrt p)*(Real.sqrt ((stages.length : ℝ))
            *reachedTav stages history j₀)
            = 22*((m:ℝ))*(reachedTav stages history j₀/Real.sqrt p) := by
          rw [hmcast]
          rw [show (22*Real.sqrt ((m:ℝ))/Real.sqrt p)*(Real.sqrt ((m:ℝ))
              *reachedTav stages history j₀)
              = 22*(Real.sqrt ((m:ℝ))*Real.sqrt ((m:ℝ)))*(reachedTav stages history j₀
              /Real.sqrt p) from by ring]
          rw [hmmsq]
        have h3 : 22*((m:ℝ)) ≤ 1000*((m:ℝ))^2 := by nlinarith [hm1R]
        rw [ht1]
        exact mul_le_mul_of_nonneg_right h3 (div_nonneg hTavnn (Real.sqrt_nonneg _))
      refine le_trans (Finset.sum_le_sum (fun i hi => hterm i hi)) ?_
      rw [Finset.sum_add_distrib, hsumA, hsumB']
      rw [show 1000*((m:ℝ))^2*(vtTmax stages + reachedTav stages history j₀/Real.sqrt p)
          = 1000*((m:ℝ))^2*((2:ℝ)^m)+1000*((m:ℝ))^2*(reachedTav stages history j₀
          /Real.sqrt p) from by rw [hmdef]; unfold vtTmax; ring]
      exact add_le_add
        (le_trans (mul_le_mul_of_nonneg_left hgeom (by positivity)) hU1)
        (le_trans (mul_le_mul_of_nonneg_left hsumB hc0) hU2)
    · have hsmall : m ≤ 16 := by omega
      have hcs := rdvt_chain_small stages history hl hm j₀ hj hs hrun p hp0
        (rfl : p = MeasureProb (vtState stages stages.length (Qatlib.Foundations.PureStateMath.Ket j₀)) (goodSet C)) hsmall ω
      have hsm' : MeasureProb (vtState stages m (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C)
          = MeasureProb (vtState stages stages.length (Qatlib.Foundations.PureStateMath.Ket j₀)) (goodSet C) := by
        have h1 := (rdvt_sector_bridge stages history hl j₀ hs hrun m le_rfl).1
        have h2 := (rdvt_sector_bridge stages history hl j₀ hs hrun m le_rfl).2
        rw [show MeasureProb (vtState stages m (Qatlib.Foundations.PureStateMath.Ket j₀)) (runningSet C) = 0 from hrun, _root_.add_zero] at h2
        exact le_antisymm h2 h1
      have hgp2 : p = MeasureProb (dataVtWordState stages history j₀
          (cascadeWord (recordDrivenSchedule m ω) m)) (goodSet C) := by
        calc p = MeasureProb (vtState stages m (Qatlib.Foundations.PureStateMath.Ket j₀)) (liveSet C) := hsm'.symm
          _ = MeasureProb (dataVtWordState stages history j₀
              (cascadeWord (recordDrivenSchedule m ω) m)) (liveSet C) :=
            (hcs.2.1 m le_rfl).symm
          _ = MeasureProb (dataVtWordState stages history j₀
              (cascadeWord (recordDrivenSchedule m ω) m)) (goodSet C) := hWgl.symm
      rw [← hgp2] at hNfG
      have hTm : (dataVtWordTime (cascadeWord (recordDrivenSchedule m ω) m) : ℝ)
          = (2:ℝ)^m-1 := hcs.2.2
      have hTav2 : (2:ℝ) ≤ reachedTav stages history j₀ := by
        have hjr : j₀ ∈ runningSet C := by simp [runningSet, hj]
        have hst0 :
            vtState stages 0
            (Qatlib.Foundations.PureStateMath.Ket j₀) = Qatlib.Foundations.PureStateMath.Ket j₀ := by simp [vtState, vtRunMatrix]
        have hket1 : ∀ S : Finset (VtSpace C), j₀ ∈ S → MeasureProb (Qatlib.Foundations.PureStateMath.Ket j₀) S = 1 := by
          intro S hS
          unfold MeasureProb BornProb
          rw [Finset.sum_eq_single_of_mem j₀ hS (fun q hq hne => by simp [Qatlib.Foundations.PureStateMath.Ket, hne])]
          simp [Qatlib.Foundations.PureStateMath.Ket]
        have hA0 := hASTB.1 0 (Nat.zero_le m)
        have hr0 : MeasureProb (vtState stages 0 (Qatlib.Foundations.PureStateMath.Ket j₀)) (runningSet C) = 1 := by
          rw [hst0]; exact hket1 _ hjr
        have hsumr : ∑ j ∈ Finset.range stages.length, reachedPstop stages history (Qatlib.Foundations.PureStateMath.Ket j₀) j
            = 1 := by
          have h2 : ∑ j ∈ Finset.range stages.length, reachedPstop stages history (Qatlib.Foundations.PureStateMath.Ket j₀) j
              = ∑ j ∈ Finset.range stages.length, (if 0 ≤ j then reachedPstop stages history
                (Qatlib.Foundations.PureStateMath.Ket j₀) j else 0) :=
            (Finset.sum_congr rfl fun j _ => by rw [if_pos (Nat.zero_le j)]).symm
          rw [h2, ← hA0, hr0]
        have h4 : (4:ℝ) ≤ ∑ j ∈ Finset.range stages.length,
            reachedPstop stages history (Qatlib.Foundations.PureStateMath.Ket j₀) j*(stopTime j)^2 := by
          have hterm : ∀ j ∈ Finset.range stages.length,
              reachedPstop stages history (Qatlib.Foundations.PureStateMath.Ket j₀) j*(4:ℝ)
              ≤ reachedPstop stages history (Qatlib.Foundations.PureStateMath.Ket j₀) j*(stopTime j)^2 := by
            intro j hj'
            have hs2 : (4:ℝ) ≤ (stopTime j)^2 := by
              unfold stopTime
              have h2j : (2:ℝ)^1 ≤ (2:ℝ)^(j+1) := by
                have hn : (1:ℕ) ≤ 2^j := Nat.succ_le_of_lt (Nat.two_pow_pos j)
                have h1 : (1:ℝ) ≤ (2:ℝ)^j := by exact_mod_cast hn
                calc (2:ℝ)^1 = (2:ℝ)*1 := by norm_num
                  _ ≤ (2:ℝ)*((2:ℝ)^j) := mul_le_mul_of_nonneg_left h1 (by norm_num)
                  _ = (2:ℝ)^(j+1) := by rw [pow_add]; ring
              calc (4:ℝ) = ((2:ℝ)^1)^2 := by norm_num
                _ ≤ ((2:ℝ)^(j+1))^2 := pow_le_pow_left₀
                    (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) 1) h2j 2
            exact mul_le_mul_of_nonneg_left hs2
              (reached_pstop_nonneg stages history hl _ j (Finset.mem_range.mp hj'))
          calc (4:ℝ) = 4*(1:ℝ) := by norm_num
            _ = 4*(∑ j ∈ Finset.range stages.length,
                reachedPstop stages history (Qatlib.Foundations.PureStateMath.Ket j₀) j) := by rw [hsumr]
            _ = ∑ j ∈ Finset.range stages.length,
                reachedPstop stages history (Qatlib.Foundations.PureStateMath.Ket j₀) j*(4:ℝ) := by
                  rw [Finset.mul_sum]
                  exact Finset.sum_congr rfl (fun j _ => by ring)
            _ ≤ ∑ j ∈ Finset.range stages.length,
                reachedPstop stages history (Qatlib.Foundations.PureStateMath.Ket j₀) j*(stopTime j)^2 :=
                  Finset.sum_le_sum hterm
        exact le_trans (by norm_num : (2:ℝ) ≤ Real.sqrt 4)
          (Real.sqrt_le_sqrt h4)
      have h2m540 : (2:ℝ)^m ≤ 540*((m:ℝ))^2 := by
        have hpure : ∀ k : ℕ, 1 ≤ k → k ≤ 16 → (2:ℝ)^k ≤ 540*((k:ℝ))^2 := by
          intro k hk1 hk16
          interval_cases k <;> norm_num
        exact hpure m (by omega) hsmall
      have hpinv : (0:ℝ) < Real.sqrt p := Real.sqrt_pos.mpr hp0
      have hsng : ((Nf : ℝ))*((2:ℝ)^m) = ((Nf : ℝ))*Real.sqrt p*((2:ℝ)^m/Real.sqrt p) := by
        calc ((Nf : ℝ))*((2:ℝ)^m) = ((Nf : ℝ))*(Real.sqrt p*((2:ℝ)^m/Real.sqrt p)) := by
              rw [mul_div_cancel₀ _ hpinv.ne']
          _ = ((Nf : ℝ))*Real.sqrt p*((2:ℝ)^m/Real.sqrt p) := by ring
      calc ((Nf : ℝ))*(dataVtWordTime (cascadeWord (recordDrivenSchedule m ω) m) : ℝ)
          = ((Nf : ℝ))*((2:ℝ)^m-1) := by rw [hTm]
        _ ≤ ((Nf : ℝ))*((2:ℝ)^m) := by
            apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
            nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 2) m]
        _ = ((Nf : ℝ))*Real.sqrt p*((2:ℝ)^m/Real.sqrt p) := hsng
        _ ≤ (100/27)*((2:ℝ)^m/Real.sqrt p) := by
            apply mul_le_mul_of_nonneg_right hNfG
              (div_nonneg (pow_nonneg (by norm_num) m) (Real.sqrt_nonneg _))
        _ ≤ (100/27)*(540*((m:ℝ))^2/Real.sqrt p) := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            exact div_le_div_of_nonneg_right h2m540 hpinv.le
        _ ≤ 1000*((m:ℝ))^2*(vtTmax stages + reachedTav stages history j₀/Real.sqrt p) := by
            have hTavdiv : (2:ℝ)/Real.sqrt p ≤ reachedTav stages history j₀/Real.sqrt p :=
              div_le_div_of_nonneg_right hTav2 hpinv.le
            have hvTnn : (0:ℝ) ≤ vtTmax stages := by
              unfold vtTmax; exact pow_nonneg (by norm_num) _
            have hlast : (100/27)*(540*((m:ℝ))^2/Real.sqrt p)
                ≤ 1000*((m:ℝ))^2*(reachedTav stages history j₀/Real.sqrt p) := by
              have h2m : ((m:ℝ))^2*((2:ℝ)/Real.sqrt p)
                  ≤ ((m:ℝ))^2*(reachedTav stages history j₀/Real.sqrt p) :=
                mul_le_mul_of_nonneg_left hTavdiv (by positivity : (0:ℝ) ≤ ((m:ℝ))^2)
              have hconv : (100/27)*(540*((m:ℝ))^2/Real.sqrt p)
                  = 1000*(((m:ℝ))^2*((2:ℝ)/Real.sqrt p)) := by ring
              rw [hconv]
              exact (mul_le_mul_of_nonneg_left h2m (by norm_num)).trans_eq (by ring)
            have hzero : (0:ℝ) ≤ 1000*((m:ℝ))^2*vtTmax stages :=
              mul_nonneg (by positivity) hvTnn
            rw [show 1000*((m:ℝ))^2*(vtTmax stages + reachedTav stages history j₀/Real.sqrt p)
                = 1000*((m:ℝ))^2*(reachedTav stages history j₀/Real.sqrt p)
                  +1000*((m:ℝ))^2*vtTmax stages from by rw [mul_add]; ring]
            exact hlast.trans (le_add_of_nonneg_right hzero)

  have hOT : (dataVtWordTime (recordDrivenOutputWord m ω) : ℝ) ≤
      1000*(m:ℝ)^2*(vtTmax stages + reachedTav stages history j₀/Real.sqrt p) := by
    rw [houttime]
    exact hlargeOT (2*kf+1) hNf
  have hsucc : (2:ℝ)/5 ≤ MeasureProb (dataVtWordState stages history j₀
      (recordDrivenOutputWord m ω)) (goodSet C) := by
    rw [houtW]
    by_cases hk0 : kf = 0
    · rw [hk0]
      have hgw : goodAAWord (cascadeWord (recordDrivenSchedule m ω) m) 0
          = cascadeWord (recordDrivenSchedule m ω) m := by simp [goodAAWord]
      rw [hgw]
      have hestbig : (1:ℝ)/2 ≤ recordDrivenEstimate m (ω (Fin.last m)) := by
        have hP0 := hP
        rw [hk0] at hP0
        rwa [hsq0] at hP0
      have h2 := (abs_le.mp hestG).2
      have hg50 : (50:ℝ)/101 ≤ MeasureProb (dataVtWordState stages history j₀
          (cascadeWord (recordDrivenSchedule m ω) m)) (goodSet C) := by
        rw [div_le_iff₀ (by norm_num : (0:ℝ) < 101)]
        nlinarith [h2, hestbig]
      exact le_trans (by norm_num : (2:ℝ)/5 ≤ 50/101) hg50
    · have hk1 : 1 ≤ kf := by omega
      have hestlt : recordDrivenEstimate m (ω (Fin.last m)) < 1/2 := by
        have hn := hmin 0 (by omega)
        have hn2 := lt_of_not_ge hn
        rw [hsq0] at hn2
        exact hn2
      have hglt : MeasureProb (dataVtWordState stages history j₀
          (cascadeWord (recordDrivenSchedule m ω) m)) (goodSet C) < 1 := by
        linarith
      have hborn := rdvt_good_aa_born stages history j₀ hl
        (cascadeWord (recordDrivenSchedule m ω) m) hWlegal hgp0 hglt rfl kf
      rw [hborn]
      exact rdvt_final_success hk1 hgp0 hestG hestlt
        (by rw [hcastd kf]; exact hP)
        (fun j hj => by rw [hcastd j]; exact not_le.mp (hmin j hj))
  have hrunle : MeasureProb (dataVtWordState stages history j₀ (recordDrivenOutputWord m ω))
      (runningSet C) ≤ 3/5 :=
    recordDriven_output_running_of_good stages history j₀ hl ω hsucc
  have hray : ∃ c : ℂ, Collapse (dataVtWordState stages history j₀
      (recordDrivenOutputWord m ω)) (goodSet C)
      = c • Collapse (vtState stages m (Qatlib.Foundations.PureStateMath.Ket j₀)) (goodSet C) :=
    recordDriven_good_ray stages history j₀ hl hj hs ω

  have hTmono : ∀ j ≤ m, dataVtWordTime (cascadeWord (recordDrivenSchedule m ω) j)
      ≤ dataVtWordTime (cascadeWord (recordDrivenSchedule m ω) m) := by
    have hstep : ∀ j, dataVtWordTime (cascadeWord (recordDrivenSchedule m ω) j)
        ≤ dataVtWordTime (cascadeWord (recordDrivenSchedule m ω) (j+1)) := by
      intro j
      rw [cascadeWord_time]
      have h2 : (1:ℕ) ≤ 2*recordDrivenSchedule m ω j+1 := by omega
      calc dataVtWordTime (cascadeWord (recordDrivenSchedule m ω) j)
          = 1*dataVtWordTime (cascadeWord (recordDrivenSchedule m ω) j) := (one_mul _).symm
        _ ≤ (2*recordDrivenSchedule m ω j+1)*(dataVtWordTime
            (cascadeWord (recordDrivenSchedule m ω) j)+2^j) :=
            Nat.mul_le_mul h2 (Nat.le_add_right _ _)
    intro j hj
    have hgen : ∀ k, j+k ≤ m → dataVtWordTime (cascadeWord (recordDrivenSchedule m ω) j)
        ≤ dataVtWordTime (cascadeWord (recordDrivenSchedule m ω) (j+k)) := by
      intro k
      induction k with
      | zero => intro _; rw [Nat.add_zero]
      | succ k ih =>
          intro hk
          exact (ih (by omega)).trans (hstep (j+k))
    have hfin := hgen (m-j) (by omega)
    rw [show j+(m-j) = m from Nat.add_sub_cancel' hj] at hfin
    exact hfin
  have hinT : ∀ i : Fin (m+1), dataVtWordTime (recordDrivenInputWord m ω i)
      ≤ dataVtWordTime (cascadeWord (recordDrivenSchedule m ω) m)+2^m := by
    intro i
    unfold recordDrivenInputWord
    by_cases hilt : i.val < m
    · rw [if_pos hilt, dataVtWordTime_append]
      have hsng : dataVtWordTime ([DataVtStep.stageF i.val] : List DataVtStep) = 2^i.val := by
        simp [dataVtWordTime, dataVtStepTime]
      rw [hsng]
      have h1 : dataVtWordTime (cascadeWord (recordDrivenSchedule m ω) i.val)
          ≤ dataVtWordTime (cascadeWord (recordDrivenSchedule m ω) m) :=
        hTmono i.val (Fin.is_le i)
      have h2 : (2:ℕ)^i.val ≤ 2^m := Nat.pow_le_pow_right (by omega) (Fin.is_le i)
      omega
    · rw [if_neg hilt]
      exact Nat.le_add_right _ _
  have hestT : (recordDrivenEstimateTime m ω : ℝ) ≤ ((m:ℝ)+1)*(2001*((m:ℝ)))*(3000000000*((m:ℝ))^2)
      *((dataVtWordTime (cascadeWord (recordDrivenSchedule m ω) m) : ℝ)+((2:ℝ)^m)) := by
    have hc1 : (2*recordDrivenRepetitions m+1 : ℕ) ≤ 2001*m := by
      unfold recordDrivenRepetitions
      omega
    have hm2 : (1:ℕ) ≤ m*m := by nlinarith [hm]
    have hc2 : (2*(recordDrivenResolution m-1)+1 : ℕ) ≤ 3000000000*m^2 := by
      have hm2sq : (1:ℕ) ≤ m^2 := by rw [Nat.pow_two]; exact hm2
      have h3 : (3:ℕ) ≤ 1000000000*m^2 :=
        le_trans (by norm_num : (3:ℕ) ≤ 1000000000*1)
          (Nat.mul_le_mul_left 1000000000 hm2sq)
      have hres : recordDrivenResolution m-1 = 1000000000*m^2+1 := by
        have hr : recordDrivenResolution m = 1000000000*m^2+2 := rfl
        rw [hr]
        omega
      rw [hres]
      omega
    have hnum : ∀ i : Fin (m+1),
        (((2*recordDrivenRepetitions m+1)*(2*(recordDrivenResolution m-1)+1)
          *dataVtWordTime (recordDrivenInputWord m ω i) : ℕ) : ℝ)
        ≤ (2001*((m:ℝ)))*(3000000000*((m:ℝ))^2)
          *((dataVtWordTime (cascadeWord (recordDrivenSchedule m ω) m) : ℝ)+((2:ℝ)^m)) := by
      intro i
      have hc1' : ((2*recordDrivenRepetitions m+1 : ℕ) : ℝ) ≤ 2001*((m:ℝ)) :=
        by exact_mod_cast hc1
      have hc2' : ((2*(recordDrivenResolution m-1)+1 : ℕ) : ℝ) ≤ 3000000000*((m:ℝ))^2 :=
        by exact_mod_cast hc2
      have ht' : ((dataVtWordTime (recordDrivenInputWord m ω i) : ℕ) : ℝ)
          ≤ (dataVtWordTime (cascadeWord (recordDrivenSchedule m ω) m) : ℝ)+((2:ℝ)^m) :=
        by exact_mod_cast hinT i
      calc (((2*recordDrivenRepetitions m+1)*(2*(recordDrivenResolution m-1)+1)
          *dataVtWordTime (recordDrivenInputWord m ω i) : ℕ) : ℝ)
          = ((2*recordDrivenRepetitions m+1 : ℕ) : ℝ)*((2*(recordDrivenResolution m-1)+1 : ℕ) : ℝ)
            *((dataVtWordTime (recordDrivenInputWord m ω i) : ℕ) : ℝ) := by
              push_cast; ring
        _ ≤ (2001*((m:ℝ)))*(3000000000*((m:ℝ))^2)
            *((dataVtWordTime (cascadeWord (recordDrivenSchedule m ω) m) : ℝ)+((2:ℝ)^m)) := by
              exact mul_le_mul (mul_le_mul hc1' hc2' (by positivity) (by positivity)) ht'
                (by positivity) (by positivity)
    unfold recordDrivenEstimateTime
    rw [Nat.cast_sum]
    calc ∑ i : Fin (m+1), (((2*recordDrivenRepetitions m+1)*(2*(recordDrivenResolution m-1)+1)
        *dataVtWordTime (recordDrivenInputWord m ω i) : ℕ) : ℝ)
        ≤ ∑ i : Fin (m+1), (2001*((m:ℝ)))*(3000000000*((m:ℝ))^2)
          *((dataVtWordTime (cascadeWord (recordDrivenSchedule m ω) m) : ℝ)+((2:ℝ)^m)) :=
          Finset.sum_le_sum (fun i _ => hnum i)
      _ = ((m:ℝ)+1)*(2001*((m:ℝ)))*(3000000000*((m:ℝ))^2)
          *((dataVtWordTime (cascadeWord (recordDrivenSchedule m ω) m) : ℝ)+((2:ℝ)^m)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
            ring
  have hTmU : (dataVtWordTime (cascadeWord (recordDrivenSchedule m ω) m) : ℝ)
      ≤ 1000*((m:ℝ))^2*Real.sqrt ((m:ℝ))
        *(vtTmax stages + reachedTav stages history j₀/Real.sqrt p) := by
    have h1 : ((1:ℕ):ℝ)*((dataVtWordTime (cascadeWord (recordDrivenSchedule m ω) m) : ℝ))
        ≤ 1000*((m:ℝ))^2*(vtTmax stages + reachedTav stages history j₀/Real.sqrt p) := by
      refine hlargeOT 1 ?_
      rw [Nat.cast_one, one_mul]
      have hsqg2 : Real.sqrt (MeasureProb (dataVtWordState stages history j₀
          (cascadeWord (recordDrivenSchedule m ω) m)) (goodSet C)) ≤ 2 :=
        (Real.sqrt_le_sqrt hgup).trans
          ((Real.sqrt_le_sqrt (by norm_num : (100:ℝ)/99 ≤ 4)).trans_eq
            (by norm_num : Real.sqrt ((4:ℝ)) = 2))
      exact hsqg2.trans (by norm_num)
    rw [Nat.cast_one, one_mul] at h1
    have hs1 : (1:ℝ) ≤ Real.sqrt ((m:ℝ)) := by
      have := Real.sqrt_le_sqrt (show (1:ℝ) ≤ (m:ℝ) by linarith)
      simpa using! this
    exact h1.trans (by
      have hVnn : (0:ℝ) ≤ vtTmax stages + reachedTav stages history j₀/Real.sqrt p :=
        add_nonneg (by unfold vtTmax; exact pow_nonneg (by norm_num) _)
          (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      calc 1000*((m:ℝ))^2*(vtTmax stages + reachedTav stages history j₀/Real.sqrt p)
          = (1000*((m:ℝ))^2*(vtTmax stages + reachedTav stages history j₀/Real.sqrt p))*(1:ℝ) := by
            ring
        _ ≤ (1000*((m:ℝ))^2*(vtTmax stages + reachedTav stages history j₀/Real.sqrt p))
            *Real.sqrt ((m:ℝ)) :=
            mul_le_mul_of_nonneg_left hs1
              (mul_nonneg (by positivity : (0:ℝ) ≤ 1000*((m:ℝ))^2) hVnn)
        _ = 1000*((m:ℝ))^2*Real.sqrt ((m:ℝ))
            *(vtTmax stages + reachedTav stages history j₀/Real.sqrt p) := by ring)
  have hTT : (recordDrivenTotalTime m ω : ℝ) ≤ 1000000000000000000*((m:ℝ))^6
      *Real.sqrt ((m:ℝ))*(vtTmax stages + reachedTav stages history j₀/Real.sqrt p) := by
    have hvTnn : (0:ℝ) ≤ vtTmax stages := by
      unfold vtTmax; exact pow_nonneg (by norm_num) _
    have hUnn : (0:ℝ) ≤ vtTmax stages + reachedTav stages history j₀/Real.sqrt p := by
      have : (0:ℝ) ≤ reachedTav stages history j₀/Real.sqrt p :=
        div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      linarith
    have hU1 : (2:ℝ)^m ≤ vtTmax stages + reachedTav stages history j₀/Real.sqrt p := by
      have heq : (2:ℝ)^m ≤ vtTmax stages := by rw [hmdef]; exact le_rfl
      have hTnn : (0:ℝ) ≤ reachedTav stages history j₀ := by
        unfold reachedTav; exact Real.sqrt_nonneg _
      have hXnn : (0:ℝ) ≤ reachedTav stages history j₀/Real.sqrt p :=
        div_nonneg hTnn (Real.sqrt_nonneg _)
      linarith
    have hkey : (1:ℝ) ≤ ((m:ℝ))^2*Real.sqrt ((m:ℝ)) := by
      have hs1 : (1:ℝ) ≤ Real.sqrt ((m:ℝ)) := by
        have := Real.sqrt_le_sqrt (show (1:ℝ) ≤ (m:ℝ) by linarith)
        simpa using! this
      have hm2 : (1:ℝ) ≤ ((m:ℝ))^2 := by
        have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hm1R 2
        rwa [one_pow] at h
      nlinarith [hs1, hm2]
    have hsumUB : (dataVtWordTime (cascadeWord (recordDrivenSchedule m ω) m) : ℝ)+((2:ℝ)^m)
        ≤ 1001*((m:ℝ))^2*Real.sqrt ((m:ℝ))
          *(vtTmax stages + reachedTav stages history j₀/Real.sqrt p) := by
      have h2 := hTmU
      nlinarith [hU1, hUnn, hkey, mul_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) 2)
        (Real.sqrt_nonneg ((m:ℝ)))]
    have hestUB : (recordDrivenEstimateTime m ω : ℝ) ≤ 12018006000000000*((m:ℝ))^6
      *Real.sqrt ((m:ℝ))*(vtTmax stages + reachedTav stages history j₀/Real.sqrt p) := by
      have h3 := hestT.trans (mul_le_mul_of_nonneg_left hsumUB
        (by positivity : (0:ℝ) ≤ ((m:ℝ)+1)*(2001*((m:ℝ)))*(3000000000*((m:ℝ))^2)))
      have hp5nn : (0:ℝ) ≤ ((m:ℝ))^5 := pow_nonneg (by positivity) _
      have hprod : ((m:ℝ)+1)*((m:ℝ))^5 ≤ 2*((m:ℝ))^6 := by
        nlinarith [hm1R, hp5nn]
      have hsplit : ((m:ℝ)+1)*(2001*((m:ℝ)))*(3000000000*((m:ℝ))^2)*(1001*((m:ℝ))^2
          *Real.sqrt ((m:ℝ))*(vtTmax stages + reachedTav stages history j₀/Real.sqrt p))
          = 6009003000000000*((m:ℝ)+1)*((m:ℝ))^5*Real.sqrt ((m:ℝ))
            *(vtTmax stages + reachedTav stages history j₀/Real.sqrt p) := by ring
      rw [hsplit] at h3
      have h4 := mul_le_mul_of_nonneg_left hprod
        (mul_nonneg (show (0:ℝ) ≤ 6009003000000000 by norm_num)
          (mul_nonneg (Real.sqrt_nonneg (m : ℝ)) hUnn))
      rw [show 6009003000000000*((m:ℝ)+1)*((m:ℝ))^5*Real.sqrt ((m:ℝ))
          *(vtTmax stages + reachedTav stages history j₀/Real.sqrt p)
          = (6009003000000000*(((m:ℝ)+1)*((m:ℝ))^5))*Real.sqrt ((m:ℝ))
            *(vtTmax stages + reachedTav stages history j₀/Real.sqrt p) from by ring] at h3
      rw [show 12018006000000000*((m:ℝ))^6*Real.sqrt ((m:ℝ))
          *(vtTmax stages + reachedTav stages history j₀/Real.sqrt p)
          = (6009003000000000*(2*((m:ℝ))^6))*Real.sqrt ((m:ℝ))
            *(vtTmax stages + reachedTav stages history j₀/Real.sqrt p) from by ring] at *
      exact h3.trans (by convert! h4 using 1 <;> ring)
    have houtUB : (dataVtWordTime (recordDrivenOutputWord m ω) : ℝ) ≤ 1000*((m:ℝ))^2
      *Real.sqrt ((m:ℝ))*(vtTmax stages + reachedTav stages history j₀/Real.sqrt p) := by
      have h2 := hOT
      refine h2.trans ?_
      have hs1 : (1:ℝ) ≤ Real.sqrt ((m:ℝ)) := by
        have := Real.sqrt_le_sqrt (show (1:ℝ) ≤ (m:ℝ) by linarith)
        simpa using! this
      calc 1000*((m:ℝ))^2*(vtTmax stages + reachedTav stages history j₀/Real.sqrt p)
          = (1000*((m:ℝ))^2*(vtTmax stages + reachedTav stages history j₀/Real.sqrt p))*(1:ℝ) := by
            ring
        _ ≤ (1000*((m:ℝ))^2*(vtTmax stages + reachedTav stages history j₀/Real.sqrt p))
            *Real.sqrt ((m:ℝ)) :=
            mul_le_mul_of_nonneg_left hs1
              (mul_nonneg (by positivity : (0:ℝ) ≤ 1000*((m:ℝ))^2) hUnn)
        _ = 1000*((m:ℝ))^2*Real.sqrt ((m:ℝ))
            *(vtTmax stages + reachedTav stages history j₀/Real.sqrt p) := by ring
    have hUsqrtNN : (0:ℝ) ≤ Real.sqrt ((m:ℝ))
        *(vtTmax stages + reachedTav stages history j₀/Real.sqrt p) :=
      mul_nonneg (Real.sqrt_nonneg _) hUnn
    unfold recordDrivenTotalTime
    rw [Nat.cast_add]
    have hp2 : ((m:ℝ))^2 ≤ ((m:ℝ))^6 := by
      have hn : (m:ℕ)^2 ≤ m^6 :=
        Nat.pow_le_pow_right (by omega : (0:ℕ) < m) (by omega : (2:ℕ) ≤ 6)
      exact_mod_cast hn
    have hX : (0:ℝ) ≤ ((m:ℝ))^6*Real.sqrt ((m:ℝ))
        *(vtTmax stages + reachedTav stages history j₀/Real.sqrt p) :=
      mul_nonneg (mul_nonneg (pow_nonneg (by positivity) _) (Real.sqrt_nonneg _)) hUnn
    have hconst : (12018006000000000+(1000:ℝ)) ≤ 1000000000000000000 := by norm_num
    nlinarith [hestUB, houtUB, hp2, hX, hUsqrtNN, hconst]
  exact ⟨hsucc, hrunle, hray, hOT, hTT⟩

end Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
