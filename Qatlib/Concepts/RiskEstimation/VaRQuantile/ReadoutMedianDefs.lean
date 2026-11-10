/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.VaRQuantile.ReadoutMedianFiniteSubgoalStat
import Qatlib.Concepts.RiskEstimation.CDFEstimation.CDFActualFiniteSubgoalQuan
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.SqEstimation.HierarchicalSQ
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.RiskEstimation.CDFEstimation
open Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Matrix
open scoped Classical BigOperators ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Qatlib.Concepts.RiskEstimation.VaRQuantile

theorem risk_closure_event {X : Type} [Fintype X] [DecidableEq X] (p : FinDist X) (E : X → Prop) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (closurePMF p) E = ENNReal.ofReal (Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass p E) := by
  classical
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass
  rw [tsum_fintype, Finset.sum_filter]
  simp_rw [closurePMF_apply]
  rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => by split_ifs <;> first | exact p.nonneg x | positivity)]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : E x <;> simp [hx]

theorem risk_median_tail {M : ℕ} (p : FinDist (Fin M)) (r : ℕ) (mu e : ℝ)
    (he : 0 ≤ e) (hgood : 8/Real.pi^2 ≤ Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass p (fun z => |aeEstimate M z-mu| ≤ e)) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (riskMedianPMF p r) (fun z => e < |z-mu|) ≤ ENNReal.ofReal ((8/9:ℝ)^r) := by
  classical
  have hp : (2/3:ℝ) ≤ 8/Real.pi^2 := by
    apply (le_div_iff₀ (by positivity : (0:ℝ) < Real.pi^2)).mpr
    nlinarith [Real.pi_pos, Real.pi_lt_d2]
  have hc :=
      Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass_complement p
      (fun z => |aeEstimate M z-mu| ≤ e)
  simp only [not_le] at hc
  have hb :
      Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass p
      (fun z => e < |aeEstimate M z-mu|) ≤ 1/3 := by linarith
  have hm :=
      Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.sorted_median_failure p
      (aeEstimate M) r mu e he hb
  unfold riskMedianPMF
  rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map, risk_closure_event]
  apply ENNReal.ofReal_le_ofReal
  exact hm

theorem risk_mean_good {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j : I) (f : I → ℝ) (M : ℕ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (hf : ∀ i, f i ∈ Set.Icc (0:ℝ) 1) (hM : 2 ≤ M) :
    8/Real.pi^2 ≤ Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass (meanLaw M A j f hA hf hM)
      (fun z => |aeEstimate M z-(∑ i, BornProb (A *ᵥ Ket j) i*f i)| ≤ Real.pi/M+Real.pi^2/(M:ℝ)^2) := by
  let B := payoffPreparation A f
  let S := Finset.univ.filter (fun p : I × Bool => p.2 = true)
  let mu := ∑ i, BornProb (A *ᵥ Ket j) i*f i
  have hB := payoffPreparation_mem_unitaryGroup A f hA hf
  have hmass : MeasureProb (B *ᵥ Ket (j,false)) S = mu :=
      (payoff_actual_rotation_and_mean A j f hA hf).2
  have hmu0 : 0 ≤ mu := hmass ▸ measureProb_nonneg _ _
  have hmu1 : mu ≤ 1 := hmass ▸ measureProb_le_one (normalized_applyGate hB (normalized_ket _)) _
  have hs : Real.sqrt (mu*(1-mu)) ≤ 1/2 := by
    nlinarith [Real.sq_sqrt (mul_nonneg hmu0 (by linarith : 0 ≤ 1-mu)),
      sq_nonneg (mu-1/2), Real.sqrt_nonneg (mu*(1-mu))]
  have hMr : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hw : 2*Real.pi*Real.sqrt (mu*(1-mu))/(M:ℝ) ≤ Real.pi/M := by
    apply (div_le_div_iff_of_pos_right hMr).mpr; nlinarith [Real.pi_pos]
  have hg := quantum_mean_actual_ae_accuracy M hM A j f hA hf
  apply hg.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro z hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp hz).2.trans (add_le_add hw le_rfl)⟩
  · intro z _ _; exact FinDist.nonneg _ _
end Qatlib.Concepts.RiskEstimation.VaRQuantile
