/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.Postselection.HHLUnknownSuccessContract
import Qatlib.Concepts.HhlAlgorithms.Postselection.RationalHHLNoiseRetry
import Qatlib.Concepts.HhlAlgorithms.Postselection.FreshTrials
import Qatlib.Concepts.QlsReadoutSpec.LowRankHHL.LowRankHHLConsumers

/-!
# Rational HHL retries and unknown-success amplification

`numericRetry` records first-success trials and their query, gate, and preparation costs for
rational HHL. The consumer theorems combine computed precision and oracle-noise budgets with
least-squares postselection and fresh-trial state selection in the setting of
[HarrowHassidimLloyd2009].

The unknown-success construction verifies finite seed sampling, a mixed amplification window,
sixteen-trial success, and explicit resource counts, using the amplitude-amplification framework
of [BrassardEtAl2002].

## Main statements

* `rational_hhl_parameter_selected_consumer`: computed parameters give postselection error at
  most `(1 / 2)^k` and quantitative retry guarantees.
* `mixed_window_avg`: the sampled amplification depths have average success at least `1 / 8`.
* `rational_hhl_unknown_success_schedule`: the finite computed unknown-success contract holds.

## References

* [Harrow et al., 2009][HarrowHassidimLloyd2009]
* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.NativeNumerics.LayeredMean
open Qatlib.Concepts.QlsReadoutSpec.LowRankHHL
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.HhlAlgorithms.GridExactHHL
open Qatlib.Concepts.HhlAlgorithms.RationalProgram
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram
open Qatlib.Concepts.HhlAlgorithms.UniformHHL
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Concepts.MonteCarloMean.PayoffRotation
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
namespace Qatlib.Concepts.HhlAlgorithms.Postselection
open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal

/-- The first-success retry law, recording success, trial count, fixed gates, preparations, and
data-query cost for the rational HHL program. -/
noncomputable def numericRetry {I : Type} [Fintype I] [DecidableEq I]
    (ψ : QState I) (hψ : Normalized ψ) (S : Finset I) (M R : ℕ) :
    CostedLaw (Bool×ℕ×ℕ×ℕ) :=
  (uniformHHLFirstSuccess (uniformHHLFlagTrialLaw ψ hψ S) R).map
    (fun z => ((z.1,z.2,z.2*(4*(M-1)+6),z.2),z.2*(2*(M-1))))

/-- If each trial succeeds with probability at least `p > 0`, at most `R` fresh trials succeed
with probability at least `1 - (1 - p)^R` and expected data-query cost at most `2 * (M - 1)
/ p`. Every supported outcome records the stated gate, preparation, and query counts. -/
theorem rational_hhl_actual_noisy_retry_resources : ∀ (I : Type) [Fintype I] [DecidableEq I] (ψ : QState I)
  (hψ : Normalized ψ) (S : Finset I) (M R : ℕ) (p : ℝ),
  0 < p → p≤MeasureProb ψ S →
  let law := numericRetry ψ hψ S M R
  (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event law (fun z => z.1.1=true)).toReal≥1-(1-p)^R ∧
  Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost law≤ENNReal.ofReal (2*((M-1:ℕ):ℝ)/p) ∧
  (∀ z∈law.support, z.1.2.1≤R ∧ z.1.2.2.1=z.1.2.1*(4*(M-1)+6) ∧
    z.1.2.2.2=z.1.2.1 ∧ z.2=z.1.2.1*(2*(M-1))) := by

  intro I _ _ ψ hψ S M R p hp hple
  (try dsimp only)
  have hμ : 0 < MeasureProb ψ S := hp.trans_le hple
  have hμ1 := measureProb_le_one hψ S
  refine ⟨?_, ?_, ?_⟩
  · unfold numericRetry
    rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map, uniformHHLFirstSuccess_success, uniformHHLFlagTrialLaw_true,
      ENNReal.toReal_ofReal (measureProb_nonneg _ _)]
    have hpow : (1-MeasureProb ψ S)^R ≤ (1-p)^R :=
      pow_le_pow_left₀ (by linarith) (by linarith) R
    linarith
  · unfold numericRetry
    rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
    simp only [Nat.cast_mul]
    have he : ∀ (q : PMF (Bool × ℕ)) (c : ℝ≥0∞),
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation q (fun z => (z.2 : ℝ≥0∞)*c) =
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation q (fun z => (z.2 : ℝ≥0∞))*c := by
      intro q c
      simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation,
          ← ENNReal.tsum_mul_right, mul_assoc]
    rw [he]
    have ht : (uniformHHLFlagTrialLaw ψ hψ S) true ≠ 0 := by
      rw [uniformHHLFlagTrialLaw_true]
      exact ne_of_gt (ENNReal.ofReal_pos.mpr hμ)
    have hb := uniformHHLFirstSuccess_expected_le (uniformHHLFlagTrialLaw ψ hψ S) ht R
    rw [uniformHHLFlagTrialLaw_true] at hb
    have hi : (ENNReal.ofReal (MeasureProb ψ S))⁻¹ ≤ (ENNReal.ofReal p)⁻¹ :=
      ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal hple)
    have h := mul_le_mul_left (hb.trans hi) ((2*(M-1) : ℕ) : ℝ≥0∞)
    rw [ENNReal.ofReal_div_of_pos hp, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_natCast]
    norm_num only [ENNReal.ofReal_ofNat, Nat.cast_mul, Nat.cast_ofNat]
    simpa only [Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv, mul_comm] using! h

  · intro z hz
    obtain ⟨w, hw, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
    exact ⟨uniformHHLFirstSuccess_attempts _ R w hw, rfl, rfl, rfl⟩

/-- A fresh-trial history of positive mass containing a success selects exactly the
postmeasurement state `PostMeasure ψ S`. -/
theorem rational_hhl_fresh_selected_quantum_output : ∀ (I : Type) [Fintype I] [DecidableEq I] (ψ : QState I)
  (S : Finset I) (R : ℕ) (os : FreshOutcomes R), Normalized ψ →
  0 < freshHistoryMass (Projector S) ψ R os → firstFreshSuccess R os≠none →
  selectedFreshState (Projector S) ψ R os=some (PostMeasure ψ S) := by

  intro I _ _ ψ S R os _hψ hmass hsome
  cases hi : firstFreshSuccess R os with
  | none => exact (hsome hi).elim
  | some i =>
    have htrue := firstFreshSuccess_true hi
    have ht : ProjectiveBranchMass (Projector S) true ψ = MeasureProb ψ S := by
      unfold ProjectiveBranchMass
      rw [projectiveBranch_projector]
      simpa only [MeasureProb, BornProb] using! sum_normSq_collapse ψ S
    have hm : 0 < MeasureProb ψ S := by
      by_contra h
      have hzero : MeasureProb ψ S = 0 := le_antisymm (not_lt.mp h) (measureProb_nonneg _ _)
      have hfi : ProjectiveBranchMass (Projector S) (freshOutcomeAt os i) ψ = 0 := by
        rw [htrue, ht, hzero]
      rw [freshHistoryMass_eq_prod, Finset.prod_eq_zero (Finset.mem_univ i) hfi] at hmass
      exact (lt_irrefl 0) hmass
    apply selectedFreshState_eq _ hi
    unfold ProjectiveConditionalState
    rw [projectiveBranch_projector]
    exact conditionalState_collapse hm

/-- The computed grid, precision, and noise budget give a normalized rational HHL output with
success probability at least `(d * theta / 2)^2` and postselection error at most `(1 /
2)^k`. The same output satisfies the fresh-retry probability, expected-query, and
selected-state guarantees. -/
theorem rational_hhl_parameter_selected_consumer
    (D : ℕ) (eig : Fin D → ℝ) (V B W : Operator D) (j : Fin D) (d theta : ℚ) (k : ℕ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (hB : B ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hW : W ∈ Matrix.unitaryGroup (Fin D) ℂ) (hd : 0 < d) (hd1 : d ≤ 1/4)
    (ht : 0 < theta) (ht1 : theta ≤ 1)
    (heig : ∀ i, eig i=0 ∨ ((d : ℝ) ≤ |eig i| ∧ |eig i| ≤ 1/4))
    (hover : (theta : ℝ) ≤ leastSquaresOverlap (continuousHHLMatrix eig V) (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j))
    (hnoise : ‖W-continuousHHLOracle eig V‖ ≤ (numericHHLNoise d theta k : ℝ)) :
    ∃ hM : 2 ≤ numericHHLGrid d theta k,
      let M := numericHHLGrid d theta k
      let out := rationalHHLRun M hM W d (numericHHLBits d theta k) B j
      let S := flagSuccessSet D M
      let p := ((d : ℝ)*(theta : ℝ)/2)^2
      ∃ hn : Normalized out,
        p ≤ MeasureProb out S ∧
        ‖toEuclidean_fromVec (PostMeasure out S-
          uniformHHLSolutionTarget M hM eig V B j)‖ ≤ (1/2 : ℝ)^k ∧
        (∀ R : ℕ,
          (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (numericRetry out hn S M R) (fun z => z.1.1=true)).toReal ≥ 1-(1-p)^R ∧
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (numericRetry out hn S M R) ≤ ENNReal.ofReal (2*((M-1 : ℕ) : ℝ)/p)) ∧
        (∀ (R : ℕ) (os : FreshOutcomes R),
          0 < freshHistoryMass (Projector S) out R os → firstFreshSuccess R os ≠ none →
          selectedFreshState (Projector S) out R os = some (PostMeasure out S)) := by
  have hg := rational_hhl_native_joint_precision_budget d theta k hd hd1 ht ht1
  (try dsimp only at hg)
  let M := numericHHLGrid d theta k
  let bits := numericHHLBits d theta k
  let eta := numericHHLAccuracy d theta k
  let δ := (numericHHLNoise d theta k : ℝ)
  let E : ℝ := (eta : ℝ)+32/2^bits+2*((M-1 : ℕ) : ℝ)*δ
  let τ :=
      leastSquaresOverlap (continuousHHLMatrix eig V)
      (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have htR : 0 < (theta : ℝ) := by exact_mod_cast ht
  have hM : 2 ≤ M := hg.2.2.1
  have heta : 0 < (eta : ℝ) := by exact_mod_cast hg.1
  have heta1 : (eta : ℝ) ≤ 1 := by exact_mod_cast hg.2.1
  have hδ : 0 ≤ δ := by
    change (0 : ℝ) ≤ (numericHHLNoise d theta k : ℝ)
    exact Rat.cast_nonneg.mpr hg.2.2.2.2.1.le
  have hbudget : 4096/((d : ℝ)^2*(eta : ℝ)^4) ≤ (M : ℝ) := by
    exact_mod_cast hg.2.2.2.1
  have hE : E ≤ (d : ℝ)*(theta : ℝ)*(1/2 : ℝ)^k/2 := hg.2.2.2.2.2
  have hhalf : (1/2 : ℝ)^k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hdθ : 0 < (d : ℝ)*(theta : ℝ) := mul_pos hdR htR
  have hτ : (d : ℝ)*(theta : ℝ) ≤ (d : ℝ)*τ := mul_le_mul_of_nonneg_left hover hdR.le
  have hEhalf : E ≤ (d : ℝ)*(theta : ℝ)/2 := by
    have h := mul_le_mul_of_nonneg_left hhalf hdθ.le
    linarith
  have hgap : E < (d : ℝ)*τ := by linarith
  have hg1 := rational_hhl_noisy_full_workspace_and_legality D M bits hM eig V B W j d eta δ
    hV hB hW hd heta heta1 hδ heig hbudget hnoise
  have hg2 := rational_hhl_noisy_actual_ls_gap D M bits hM eig V B W j d eta δ
    hV hB hW hd heta heta1 hδ heig hbudget hnoise hgap
  let out := rationalHHLRun M hM W d bits B j
  let S := flagSuccessSet D M
  let p : ℝ := ((d : ℝ)*(theta : ℝ)/2)^2
  have hp : 0 < p := sq_pos_of_pos (by positivity)
  have hsuccess : p ≤ MeasureProb out S := by
    apply le_trans _ hg2.1
    dsimp only [p]
    nlinarith
  have herr : ‖toEuclidean_fromVec (PostMeasure out S-
      uniformHHLSolutionTarget M hM eig V B j)‖ ≤ (1/2 : ℝ)^k := by
    apply hg2.2.trans
    apply (div_le_iff₀ (lt_of_lt_of_le hdθ hτ)).mpr
    have hh := mul_le_mul_of_nonneg_right hτ (by positivity : 0 ≤ (1/2 : ℝ)^k)
    linarith
  refine ⟨hM, hg1.1, hsuccess, herr, ?_, ?_⟩
  · intro R
    have h := rational_hhl_actual_noisy_retry_resources _ out hg1.1 S M R p hp hsuccess
    exact ⟨h.1, h.2.1⟩
  · intro R os hm hs
    exact rational_hhl_fresh_selected_quantum_output _ out S R os hg1.1 hm hs

/-- For the three-dimensional signed, inconsistent example, the computed parameters give success
probability at least `1 / 4096` and postselection error at most `(1 / 2)^k`. The resulting
retry law satisfies the stated probability and expected-query bounds and selects the same
postmeasurement state. -/
theorem rational_hhl_signed_inconsistent_noisy_example (k : ℕ) (W : Operator 3)
    (hW : W ∈ Matrix.unitaryGroup (Fin 3) ℂ)
    (hnoise : ‖W-continuousHHLOracle lowRankExampleSpectrum (1 : Operator 3)‖ ≤
      (numericHHLNoise (1/16) (1/2) k : ℝ)) :
    ∃ hM : 2 ≤ numericHHLGrid (1/16) (1/2) k,
      let M := numericHHLGrid (1/16) (1/2) k
      let out :=
          rationalHHLRun M hM W (1/16) (numericHHLBits (1/16) (1/2) k) lowRankExamplePrepare 0
      let S := flagSuccessSet 3 M
      ∃ hn : Normalized out,
        (1/4096 : ℝ) ≤ MeasureProb out S ∧
        ‖toEuclidean_fromVec (PostMeasure out S-uniformHHLSuccessEmbed M hM (Qatlib.Foundations.PureStateMath.Ket (1 : Fin 3)))‖ ≤
          (1/2 : ℝ)^k ∧
        (∀ R : ℕ,
          (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (numericRetry out hn S M R) (fun z => z.1.1=true)).toReal ≥
            1-(1-(1/4096 : ℝ))^R ∧
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (numericRetry out hn S M R) ≤
            ENNReal.ofReal (8192*((M-1 : ℕ) : ℝ))) ∧
        (∀ (R : ℕ) (os : FreshOutcomes R), 0 < freshHistoryMass (Projector S) out R os →
          firstFreshSuccess R os ≠ none → selectedFreshState (Projector S) out R os =
            some (PostMeasure out S)) := by
  have h := rational_hhl_parameter_selected_consumer 3 lowRankExampleSpectrum 1 lowRankExamplePrepare W 0
    (1/16) (1/2) k (Submonoid.one_mem _) lowRankExamplePrepare_unitary hW
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using! lowRankExample_promise)
    (by simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using! lowRankExample_overlap) hnoise
  obtain ⟨hM, hn, hmass, herr, hretry, hfresh⟩ := h
  have hp : (((1/16 : ℚ) : ℝ)*((1/2 : ℚ) : ℝ)/2)^2 = (1/4096 : ℝ) := by norm_num
  rw [hp] at hmass hretry
  rw [lowRankExample_target] at herr
  refine ⟨hM, hn, hmass, herr, ?_, hfresh⟩
  intro R
  refine ⟨(hretry R).1, ?_⟩
  calc
    _ ≤ ENNReal.ofReal (2*((numericHHLGrid (1/16) (1/2) k-1 : ℕ) : ℝ)/(1/4096 : ℝ)) := (hretry R).2
    _ = _ := by congr 1; ring

/-- For an input supported on zero eigenvalues, oracle error at most `δ` bounds the rational HHL
success probability by `4 * (M - 1) * δ`. -/
theorem rational_hhl_noisy_kernel_upper_bound (D M bits : ℕ) (hM : 2 ≤ M)
    (eig : Fin D → ℝ) (V B W : Operator D) (j : Fin D) (d : ℚ) (δ : ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (hB : B ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hW : W ∈ Matrix.unitaryGroup (Fin D) ℂ) (hd : 0 < d)
    (hzero : ∀ i, eig i ≠ 0 → (Vᴴ *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) i=0)
    (hnoise : ‖W-continuousHHLOracle eig V‖ ≤ δ) :
    MeasureProb (rationalHHLRun M hM W d bits B j) (flagSuccessSet D M) ≤
      4*((M-1 : ℕ) : ℝ)*δ := by
  have hU := continuous_hhl_oracle_unitary eig V hV
  have hbase := rational_hhl_exact_zero_range_branch D M bits hM eig V B j d hV hB hd hzero
  have hn := rationalHHLRun_oracle_noise M hM (continuousHHLOracle eig V) W B j d bits hU hW hB hd
  have hm := measureProb_sub_le_two_mul_l2
    (rationalHHLRun M hM W d bits B j)
    (rationalHHLRun M hM (continuousHHLOracle eig V) d bits B j) (flagSuccessSet D M)
    (rationalHHLRun_normalized M hM W B j d bits hW hB hd)
    (rationalHHLRun_normalized M hM _ B j d bits hU hB hd)
  rw [hbase, sub_zero, abs_of_nonneg (measureProb_nonneg _ _)] at hm
  have he : ‖toEuclidean_fromVec (rationalHHLRun M hM W d bits B j-
      rationalHHLRun M hM (continuousHHLOracle eig V) d bits B j)‖ ≤ 2*((M-1 : ℕ) : ℝ)*δ :=
    hn.trans (mul_le_mul_of_nonneg_left hnoise (by positivity))
  linarith

/-- The rational HHL table contains `M` entries, and its two square-root computations per entry
use exactly `2 * M * bits` bracket iterations in total. -/
theorem rational_hhl_numeric_table_work (M bits : ℕ) (d : ℚ) (hd : 0 < d) :
    (rationalHHLTable M d bits).size = M ∧
    (∑ y : Fin M,
      ((rationalSqrtBracket ((rationalHHLGamma d (rationalHHLDecode M y))^2) bits).2.2 +
      (rationalSqrtBracket (1-(rationalHHLGamma d (rationalHHLDecode M y))^2) bits).2.2)) =
      2*M*bits :=
  rational_hhl_paid_table_arithmetic_and_precision M bits d (32/(2 : ℝ)^bits)
    hd (by positivity) le_rfl

end Qatlib.Concepts.HhlAlgorithms.Postselection

set_option autoImplicit false
open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Concepts.HhlAlgorithms.Postselection.HHLUnknown.Probe

open Qatlib

set_option autoImplicit false
open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- Twice the sampling window equals `2^(seedBits d theta + 1)`. -/
private theorem two_mul_window (d theta : ℚ) :
    2 * window d theta = 2 ^ (seedBits d theta + 1) := by
  simp only [window, pow_succ]
  ring

/-- The binary encoding equivalence between `b` Boolean bits and `Fin (2^b)`. -/
private def seedEquiv (b : ℕ) : (Fin b → Bool) ≃ Fin (2 ^ b) :=
  (Equiv.piCongrRight fun _ : Fin b => finTwoEquiv.symm).trans
    (finFunctionFinEquiv (m := 2) (n := b))

/-- The value of `seedEquiv` is the sum of the input bits weighted by powers of two. -/
private theorem seedEquiv_val (b : ℕ) (x : Fin b → Bool) :
    ((seedEquiv b x : Fin (2 ^ b)) : ℕ) =
      ∑ i : Fin b, (if x i then 1 else 0) * 2 ^ i.val := by
  rw [seedEquiv, Equiv.trans_apply, finFunctionFinEquiv_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Equiv.piCongrRight_apply, Pi.map_apply]
  congr 1
  cases x i <;> rfl

/-- The seed obtained from Boolean bits is their binary encoding transported to the window index
type. -/
private theorem seedOfBits_eq (d theta : ℚ) (x : Fin (seedBits d theta + 1) → Bool) :
    seedOfBits d theta x =
      finCongr (two_mul_window d theta).symm (seedEquiv (seedBits d theta + 1) x) := by
  apply Fin.ext
  rw [finCongr_apply, Fin.val_cast]
  change (∑ i : Fin (seedBits d theta + 1), (if x i then 2 ^ i.val else 0)) %
      (2 * window d theta) = _
  have hsum : (∑ i : Fin (seedBits d theta + 1), (if x i then 2 ^ i.val else 0)) =
      ∑ i : Fin (seedBits d theta + 1), (if x i then 1 else 0) * 2 ^ i.val := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : x i <;> simp [h]
  rw [hsum, seedEquiv_val]
  have hlt : (∑ i : Fin (seedBits d theta + 1),
      (if x i then 1 else 0) * 2 ^ i.val) < 2 * window d theta := by
    rw [two_mul_window]
    have h := (seedEquiv (seedBits d theta + 1) x).isLt
    rwa [seedEquiv_val] at h
  rw [Nat.mod_eq_of_lt hlt]

/-- The map from seed bits to indices in the doubled sampling window is bijective. -/
theorem seedOfBits_bijective (d theta : ℚ) :
    Function.Bijective (seedOfBits d theta) := by
  have h : (seedOfBits d theta) =
      fun x => finCongr (two_mul_window d theta).symm (seedEquiv (seedBits d theta + 1) x) := by
    funext x
    exact seedOfBits_eq d theta x
  rw [h]
  exact ((seedEquiv (seedBits d theta + 1)).trans
    (finCongr (two_mul_window d theta).symm)).bijective

/-- The sampling window is at least one. -/
theorem one_le_window (d theta : ℚ) : 1 ≤ window d theta := by
  simp only [window]
  exact Nat.one_le_two_pow

/-- The sampling window is at most twice `max 1 ⌈4 / (d * theta)⌉₊`. -/
theorem window_le (d theta : ℚ) :
    window d theta ≤ 2 * max 1 ⌈4/(d*theta)⌉₊ := by
  simp only [window, seedBits]
  set C := max 1 ⌈4/(d*theta)⌉₊
  by_cases hC : C = 1
  · rw [hC, Nat.clog_one_right]
    norm_num
  · have hC1 : 1 < C := by
      have : 1 ≤ C := le_max_left _ _
      omega
    have hpos : 0 < Nat.clog 2 C := Nat.clog_pos (by norm_num) hC1
    have h := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hC1
    have hsplit : 2 ^ Nat.clog 2 C = 2 ^ (Nat.clog 2 C).pred * 2 := by
      rw [← pow_succ]
      congr 1
      exact (Nat.succ_pred_eq_of_pos hpos).symm
    rw [hsplit]
    calc 2 ^ (Nat.clog 2 C).pred * 2 ≤ C * 2 :=
          (Nat.mul_lt_mul_of_pos_right h (by norm_num)).le
      _ = 2 * C := by ring

/-- For positive `d` and `theta`, the sampling window is at least `4 / (d * theta)`. -/
theorem four_div_le_window (d theta : ℚ) (hd : 0 < d) (ht : 0 < theta) :
    (4/(d*theta) : ℚ) ≤ window d theta := by
  have hdθ : 0 < d*theta := mul_pos hd ht
  have hceil : (4/(d*theta) : ℚ) ≤ (⌈4/(d*theta)⌉₊ : ℚ) := Nat.le_ceil _
  have hle : (⌈4/(d*theta)⌉₊ : ℚ) ≤ (window d theta : ℚ) := by
    have h2 : (⌈4/(d*theta)⌉₊ : ℕ) ≤ max 1 ⌈4/(d*theta)⌉₊ := le_max_right _ _
    have h3 : (max 1 ⌈4/(d*theta)⌉₊ : ℕ) ≤ 2 ^ Nat.clog 2 (max 1 ⌈4/(d*theta)⌉₊) :=
      Nat.le_pow_clog (by norm_num) _
    rw [window, seedBits]
    exact_mod_cast h2.trans h3
  exact hceil.trans hle

/-- The rational HHL rotation table has exactly `M` entries. -/
private theorem table_size (M bits : ℕ) (d : ℚ) (hd : 0 < d) :
    (rationalHHLTable M d bits).size = M :=
  (rational_hhl_numeric_table_work M bits d hd).1

/-- Looking up a valid phase index in the rational HHL table returns its computed rational
rotation parameters. -/
private theorem table_getElem (M bits : ℕ) (d : ℚ) (y : Fin M) :
    (rationalHHLTable M d bits)[y.val]? = some (rationalHHLCS d (rationalHHLDecode M y) bits) := by
  simp only [rationalHHLTable, List.getElem?_toArray, List.getElem?_ofFn]
  rw [dite_eq_left y.isLt]

set_option autoImplicit false
open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator

open Qatlib

variable {I : Type} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in

/-- Evaluating the inverse of a prepared instruction gives the conjugate transpose of its
evaluation. -/
theorem preparedInstruction_inverseStep (U B : Matrix I I ℂ) (c : PreparedStep I) :
    preparedInstruction U B (inverseStep c) = (preparedInstruction U B c)ᴴ := by
  cases c <;> simp [inverseStep, preparedInstruction]

/-- Evaluating an inverse prepared word gives the conjugate transpose of the original word's
evaluation. -/
theorem evaluatePrepared_inverseWord (U B : Matrix I I ℂ) (cs : List (PreparedStep I)) :
    evaluatePrepared U B (inverseWord cs) = (evaluatePrepared U B cs)ᴴ := by
  induction cs with
  | nil => simp [inverseWord, evaluatePrepared]
  | cons c cs ih =>
      have hstep : inverseWord (c :: cs) = inverseWord cs ++ [inverseStep c] := by
        simp only [inverseWord, List.reverse_cons, List.map_append, List.map_singleton]
      rw [hstep, evaluatePrepared_append, ih]
      cases c <;>
        simp only [evaluatePrepared, preparedInstruction, mul_one, inverseStep,
          Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

/-- Evaluating `k` concatenated copies of a prepared block gives the `k`th power of its
evaluation. -/
theorem evaluatePrepared_flatten_replicate (U B : Matrix I I ℂ)
    (block : List (PreparedStep I)) (k : ℕ) :
    evaluatePrepared U B (List.replicate k block |>.flatten)
      = (evaluatePrepared U B block)^k := by
  induction k with
  | zero => simp [evaluatePrepared]
  | succ k ih =>
      rw [List.replicate_succ, List.flatten_cons, evaluatePrepared_append, ih, pow_succ']

/-- The preparation, initial-state reflection, inverse preparation, and marking word evaluates
to `preparedAAIterate`. -/
theorem evaluatePrepared_amplifiedBlock (U B : Matrix I I ℂ) (cs : List (PreparedStep I))
    (j : I) (S : Finset I) :
    evaluatePrepared U B (cs ++ [.gate (ReflectionAbout (outerProduct (Qatlib.Foundations.PureStateMath.Ket j)))] ++
        inverseWord cs ++ [.gate (preparedMark S)]) =
      preparedAAIterate (evaluatePrepared U B cs) j S := by
  simp only [List.append_assoc, evaluatePrepared_append, evaluatePrepared_inverseWord,
    evaluatePrepared, preparedInstruction, mul_one, preparedAAIterate, Matrix.mul_assoc]

/-- An amplified prepared word evaluates to the `k`th power of its amplification iterate
followed by the preparation. -/
theorem evaluatePrepared_amplified (U B : Matrix I I ℂ) (cs : List (PreparedStep I))
    (j : I) (S : Finset I) (k : ℕ) :
    evaluatePrepared U B (amplified cs j S k) =
      (preparedAAIterate (evaluatePrepared U B cs) j S)^k * evaluatePrepared U B cs := by
  rw [amplified, evaluatePrepared_append, evaluatePrepared_flatten_replicate,
    evaluatePrepared_amplifiedBlock]

set_option autoImplicit false
open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator

open Qatlib

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The number of forward data-oracle instructions in an adjoint circuit. -/
def fwdCount {I : Type} (cs : List (AdjointStep I)) : ℕ :=
  cs.countP (fun s => match s with | .forward => true | _ => false)

/-- The number of backward data-oracle instructions in an adjoint circuit. -/
def bwdCount {I : Type} (cs : List (AdjointStep I)) : ℕ :=
  cs.countP (fun s => match s with | .backward => true | _ => false)

/-- The Boolean predicate recognizing a forward data-oracle instruction. -/
def isDataFwd {I : Type} : PreparedStep I → Bool
  | .dataForward => true | _ => false
/-- The Boolean predicate recognizing a backward data-oracle instruction. -/
def isDataBwd {I : Type} : PreparedStep I → Bool
  | .dataBackward => true | _ => false
/-- The Boolean predicate recognizing a forward input-preparation instruction. -/
def isInpFwd {I : Type} : PreparedStep I → Bool
  | .prepareForward => true | _ => false
/-- The Boolean predicate recognizing a backward input-preparation instruction. -/
def isInpBwd {I : Type} : PreparedStep I → Bool
  | .prepareBackward => true | _ => false

omit [Fintype I] [DecidableEq I] in

/-- The forward data-oracle count equals the number of instructions satisfying `isDataFwd`. -/
theorem dataForwardCalls_eq_countP (cs : List (PreparedStep I)) :
    dataForwardCalls cs = cs.countP (isDataFwd (I := I)) := rfl

omit [Fintype I] [DecidableEq I] in

/-- The backward data-oracle count equals the number of instructions satisfying `isDataBwd`. -/
theorem dataBackwardCalls_eq_countP (cs : List (PreparedStep I)) :
    dataBackwardCalls cs = cs.countP (isDataBwd (I := I)) := rfl

omit [Fintype I] [DecidableEq I] in

/-- The forward input-preparation count equals the number of instructions satisfying `isInpFwd`. -/
theorem inputForwardCalls_eq_countP (cs : List (PreparedStep I)) :
    inputForwardCalls cs = cs.countP (isInpFwd (I := I)) := rfl

omit [Fintype I] [DecidableEq I] in

/-- The backward input-preparation count equals the number of instructions satisfying
`isInpBwd`. -/
theorem inputBackwardCalls_eq_countP (cs : List (PreparedStep I)) :
    inputBackwardCalls cs = cs.countP (isInpBwd (I := I)) := rfl

omit [Fintype I] [DecidableEq I] in

/-- The adjoint query count is the sum of its forward and backward query counts. -/
theorem adjointQueryCount_eq (cs : List (AdjointStep I)) :
    adjointQueryCount cs = fwdCount cs + bwdCount cs := by
  induction cs with
  | nil => simp [adjointQueryCount, fwdCount, bwdCount]
  | cons c cs ih =>
      cases c <;> simp [adjointQueryCount, fwdCount, bwdCount, ih] <;> omega

omit [Fintype I] [DecidableEq I] in

/-- Taking the adjoint circuit exchanges its backward query count with the forward count. -/
theorem fwdCount_adjointCircuit (cs : List (AdjointStep I)) :
    fwdCount (Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit cs) = bwdCount cs := by
  induction cs with
  | nil => simp [Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit, fwdCount, bwdCount]
  | cons c cs ih =>
      have h : fwdCount (Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit cs ++ [adjointInstruction c]) =
          fwdCount (Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit cs) + fwdCount [adjointInstruction c] := by
        simp [fwdCount, List.countP_append, List.countP_singleton]
      rw [Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit, h, ih]
      cases c <;>
        simp [adjointInstruction, fwdCount, bwdCount]

omit [Fintype I] [DecidableEq I] in

/-- Taking the adjoint circuit exchanges its forward query count with the backward count. -/
theorem bwdCount_adjointCircuit (cs : List (AdjointStep I)) :
    bwdCount (Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit cs) = fwdCount cs := by
  induction cs with
  | nil => simp [Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit, fwdCount, bwdCount]
  | cons c cs ih =>
      have h : bwdCount (Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit cs ++ [adjointInstruction c]) =
          bwdCount (Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit cs) + bwdCount [adjointInstruction c] := by
        simp [bwdCount, List.countP_append, List.countP_singleton]
      rw [Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit, h, ih]
      cases c <;>
        simp [adjointInstruction, fwdCount, bwdCount]

omit [Fintype I] [DecidableEq I] in

/-- Counting a predicate after embedding adjoint instructions into prepared instructions equals
counting its pullback on the original circuit. -/
theorem countP_map_preparedOfAdjoint (p : PreparedStep I → Bool) (cs : List (AdjointStep I)) :
    (cs.map preparedOfAdjoint).countP p =
      cs.countP (fun s => match s with
        | .gate V => p (.gate V) | .forward => p (.dataForward) | .backward => p (.dataBackward)) := by
  rw [List.countP_map]
  apply List.countP_congr
  intro c _
  cases c <;> rfl

/-- Embedding an adjoint circuit as a prepared word preserves its forward data-oracle count. -/
theorem dataForwardCalls_map (cs : List (AdjointStep I)) :
    dataForwardCalls (cs.map preparedOfAdjoint) = fwdCount cs := by
  rw [dataForwardCalls, countP_map_preparedOfAdjoint, fwdCount]
  apply List.countP_congr
  intro c _
  cases c <;> simp

/-- Embedding an adjoint circuit as a prepared word preserves its backward data-oracle count. -/
theorem dataBackwardCalls_map (cs : List (AdjointStep I)) :
    dataBackwardCalls (cs.map preparedOfAdjoint) = bwdCount cs := by
  rw [dataBackwardCalls, countP_map_preparedOfAdjoint, bwdCount]
  apply List.countP_congr
  intro c _
  cases c <;> simp

omit [Fintype I] [DecidableEq I] in

/-- Counting a predicate on an inverse word equals counting its pullback under `inverseStep` on
the original word. -/
theorem countP_inverseWord (p q : PreparedStep I → Bool)
    (h : ∀ x, p (inverseStep x) = q x) (cs : List (PreparedStep I)) :
    (inverseWord cs).countP p = cs.countP q := by
  rw [inverseWord, List.countP_map, show (p ∘ inverseStep) = q from funext h]
  exact List.countP_reverse

/-- The inverse word has as many forward data calls as the original word has backward data
calls. -/
theorem dataForwardCalls_inverseWord (cs : List (PreparedStep I)) :
    dataForwardCalls (inverseWord cs) = dataBackwardCalls cs := by
  rw [dataForwardCalls_eq_countP, dataBackwardCalls_eq_countP,
    countP_inverseWord isDataFwd isDataBwd (by intro x; cases x <;> rfl)]

/-- The inverse word has as many backward data calls as the original word has forward data
calls. -/
theorem dataBackwardCalls_inverseWord (cs : List (PreparedStep I)) :
    dataBackwardCalls (inverseWord cs) = dataForwardCalls cs := by
  rw [dataBackwardCalls_eq_countP, dataForwardCalls_eq_countP,
    countP_inverseWord isDataBwd isDataFwd (by intro x; cases x <;> rfl)]

/-- The inverse word has as many forward preparation calls as the original word has backward
preparation calls. -/
theorem inputForwardCalls_inverseWord (cs : List (PreparedStep I)) :
    inputForwardCalls (inverseWord cs) = inputBackwardCalls cs := by
  rw [inputForwardCalls_eq_countP, inputBackwardCalls_eq_countP,
    countP_inverseWord isInpFwd isInpBwd (by intro x; cases x <;> rfl)]

/-- The inverse word has as many backward preparation calls as the original word has forward
preparation calls. -/
theorem inputBackwardCalls_inverseWord (cs : List (PreparedStep I)) :
    inputBackwardCalls (inverseWord cs) = inputForwardCalls cs := by
  rw [inputBackwardCalls_eq_countP, inputForwardCalls_eq_countP,
    countP_inverseWord isInpBwd isInpFwd (by intro x; cases x <;> rfl)]

omit [Fintype I] [DecidableEq I] in

/-- Each forward and backward data and input call count is additive under word concatenation. -/
theorem piecewise_counts_append (cs ds : List (PreparedStep I)) :
    dataForwardCalls (cs ++ ds) = dataForwardCalls cs + dataForwardCalls ds ∧
    dataBackwardCalls (cs ++ ds) = dataBackwardCalls cs + dataBackwardCalls ds ∧
    inputForwardCalls (cs ++ ds) = inputForwardCalls cs + inputForwardCalls ds ∧
    inputBackwardCalls (cs ++ ds) = inputBackwardCalls cs + inputBackwardCalls ds :=
  ⟨List.countP_append, List.countP_append, List.countP_append, List.countP_append⟩

omit [Fintype I] [DecidableEq I] in

/-- The prepared data-query count is the sum of forward and backward data calls. -/
theorem dataQueries_split (cs : List (PreparedStep I)) :
    preparedDataQueries cs = dataForwardCalls cs + dataBackwardCalls cs := by
  induction cs with
  | nil => simp [preparedDataQueries, dataForwardCalls, dataBackwardCalls]
  | cons c cs ih =>
      cases c <;> simp [preparedDataQueries, dataForwardCalls, dataBackwardCalls, ih] <;> omega

omit [Fintype I] [DecidableEq I] in

/-- The prepared input-query count is the sum of forward and backward preparation calls. -/
theorem inputQueries_split (cs : List (PreparedStep I)) :
    preparedInputQueries cs = inputForwardCalls cs + inputBackwardCalls cs := by
  induction cs with
  | nil => simp [preparedInputQueries, inputForwardCalls, inputBackwardCalls]
  | cons c cs ih =>
      cases c <;> simp [preparedInputQueries, inputForwardCalls, inputBackwardCalls, ih] <;> omega

end Qatlib.Concepts.HhlAlgorithms.Postselection.HHLUnknown.Probe

open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Concepts.HhlAlgorithms.Postselection.HHLUnknown.Probe

open Qatlib

variable {I : Type} [Fintype I] [DecidableEq I]

/-- At amplification depth zero, the success probability equals that of the prepared state. -/
private theorem successMass_depth_zero (A : Matrix I I ℂ) (j : I) (S : Finset I) :
    MeasureProb (Run (preparedMark S) (preparedAACircuit A j 0) (Qatlib.Foundations.PureStateMath.Ket j)) S =
      MeasureProb (preparedAAState A j) S := by
  simp [preparedAACircuit, RepeatCircuit, preparedAAState]

/-- If `sin θ = sqrt a`, `α^2 ≤ a < 1 / 2`, and the angle lies in the first quadrant, then `α ≤
sin (2 * θ)`. -/
private theorem sin_two_ge_alpha (a α θ : ℝ) (ha0 : α^2 ≤ a) (hα : 0 < α)
    (ha1 : a < 1/2) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi/2)
    (hsin : Real.sin θ = Real.sqrt a) : α ≤ Real.sin (2*θ) := by
  have ha0le : 0 ≤ a := by nlinarith [sq_nonneg α]
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩
  have hprob : a = (Real.sin θ)^2 := by rw [hsin, Real.sq_sqrt ha0le]
  have hcosHalf : 1/2 ≤ Real.cos θ := by
    have ht := Real.sin_sq_add_cos_sq θ
    rw [← hprob] at ht
    nlinarith
  have hsin2 : Real.sqrt a ≤ Real.sin (2*θ) := by
    rw [Real.sin_two_mul, hsin]
    nlinarith [Real.sqrt_nonneg a]
  have hαsqrt : α ≤ Real.sqrt a := (Real.le_sqrt hα.le ha0le).mpr ha0
  exact hαsqrt.trans hsin2

/-- Uniformly sampling the mixed amplification window gives average success probability at least
`1 / 8` when the window times the positive amplitude lower bound is at least one. -/
theorem mixed_window_avg {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (m : ℕ) (α : ℝ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (hm : 0 < m) (hα : 0 < α)
    (ha0 : α^2 ≤ MeasureProb (preparedAAState A j) S)
    (hwin : 1 ≤ (m:ℝ) * α) :
    (1/8:ℝ) ≤ (∑ s : Fin (2*m),
        MeasureProb (Run (preparedMark S) (preparedAACircuit A j (depth m s)) (Qatlib.Foundations.PureStateMath.Ket j)) S) /
      (2*m : ℝ) := by
  let a := MeasureProb (preparedAAState A j) S
  let f : ℕ → ℝ := fun k =>
    MeasureProb (Run (preparedMark S) (preparedAACircuit A j k) (Qatlib.Foundations.PureStateMath.Ket j)) S
  let g : ℕ → ℝ := fun s => f (if s < m then 0 else s - m)
  have hf0 : f 0 = a := successMass_depth_zero A j S
  have hmR : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have h2mR : (0:ℝ) < 2*(m:ℝ) := by positivity
  have hWa : 0 ≤ ∑ x ∈ Finset.range m, f x :=
    Finset.sum_nonneg (fun x _ => measureProb_nonneg _ _)

  have hreindex : (∑ s : Fin (2*m),
      MeasureProb (Run (preparedMark S) (preparedAACircuit A j (depth m s)) (Qatlib.Foundations.PureStateMath.Ket j)) S) =
      ∑ x ∈ Finset.range m, g x + ∑ x ∈ Finset.range m, g (m + x) := by
    have hcongr : (∑ s : Fin (2*m),
        MeasureProb (Run (preparedMark S) (preparedAACircuit A j (depth m s)) (Qatlib.Foundations.PureStateMath.Ket j)) S) =
        ∑ s : Fin (2*m), g s := by
      apply Finset.sum_congr rfl
      intro s _
      show f (depth m s) = g s
      rfl
    rw [hcongr, Fin.sum_univ_eq_sum_range g (2*m), show 2*m = m + m from by omega,
      Finset.sum_range_add]
  have hga : ∀ x ∈ Finset.range m, g x = a := by
    intro x hx
    have hxlt : x < m := Finset.mem_range.mp hx
    show f (if x < m then 0 else x - m) = a
    rw [ite_eq_left hxlt, hf0]
  have hgb : ∀ x ∈ Finset.range m, g (m + x) = f x := by
    intro x _
    have hnot : ¬ (m + x < m) := by omega
    show f (if m + x < m then 0 else m + x - m) = f x
    rw [ite_eq_right hnot, Nat.add_sub_cancel_left]
  have hsplit : (∑ s : Fin (2*m),
      MeasureProb (Run (preparedMark S) (preparedAACircuit A j (depth m s)) (Qatlib.Foundations.PureStateMath.Ket j)) S) =
      (m:ℝ) * a + ∑ x ∈ Finset.range m, f x := by
    rw [hreindex,
      Finset.sum_congr rfl hga, Finset.sum_congr rfl hgb,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hsplit]
  by_cases hhalf : (1/2:ℝ) ≤ a
  · rw [le_div_iff₀ h2mR]
    have hquarter : (1/8:ℝ) * (2*(m:ℝ)) = (m:ℝ) * (1/4) := by ring
    rw [hquarter]
    nlinarith [mul_le_mul_of_nonneg_left hhalf hmR.le, hWa]
  · have ha1 : a < 1/2 := lt_of_not_ge hhalf
    have haPos : 0 < a := by nlinarith [pow_pos hα 2]
    have ha0le : 0 ≤ a := le_of_lt haPos
    let θ := Real.arcsin (Real.sqrt a)
    have hθ0 : 0 < θ := Real.arcsin_pos.mpr (Real.sqrt_pos.mpr haPos)
    have hroot1 : Real.sqrt a < 1 := by
      simpa only [Real.sqrt_one] using!
        Real.sqrt_lt_sqrt ha0le (show a < 1 by linarith)
    have hθ1 : θ < Real.pi/2 := Real.arcsin_lt_pi_div_two.mpr hroot1
    have hsin : Real.sin θ = Real.sqrt a :=
      Real.sin_arcsin (by linarith [Real.sqrt_nonneg a]) hroot1.le
    have hprob : a = (Real.sin θ)^2 := by rw [hsin, Real.sq_sqrt ha0le]
    have hαsin : α ≤ Real.sin (2*θ) :=
      sin_two_ge_alpha a α θ ha0 hα ha1 hθ0 hθ1 hsin
    have hmature : 1 ≤ (m:ℝ) * Real.sin (2*θ) :=
      hwin.trans (mul_le_mul_of_nonneg_left hαsin hmR.le)
    have hu := prepared_aa_uniform_success_lower A j S θ m hA hm hθ0 hθ1 hprob hmature
    have hWlow : (m:ℝ) * (1/4) ≤ ∑ x ∈ Finset.range m, f x := by
      have hrange : (∑ i : Fin m, f i.val) = ∑ x ∈ Finset.range m, f x :=
        Fin.sum_univ_eq_sum_range f m
      rw [hrange] at hu
      rw [le_div_iff₀ hmR] at hu
      linarith
    rw [le_div_iff₀ h2mR]
    have hquarter : (1/8:ℝ) * (2*(m:ℝ)) = (m:ℝ) * (1/4) := by ring
    rw [hquarter]
    nlinarith [hWlow, mul_nonneg hmR.le ha0le]

end Qatlib.Concepts.HhlAlgorithms.Postselection.HHLUnknown.Probe

namespace Qatlib.Concepts.HhlAlgorithms.Postselection.HHLUnknown.Probe

open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- Applying the evaluated amplified word to the initial basis state agrees with the prepared
amplitude-amplification run. -/
theorem amplified_run {I : Type} [Fintype I] [DecidableEq I] (U B : Matrix I I ℂ)
    (cs : List (PreparedStep I)) (j : I) (S : Finset I) (k : ℕ)
    (hA : evaluatePrepared U B cs ∈ Matrix.unitaryGroup I ℂ) :
    ApplyGate (evaluatePrepared U B (amplified cs j S k)) (Qatlib.Foundations.PureStateMath.Ket j) =
      Run (preparedMark S) (preparedAACircuit (evaluatePrepared U B cs) j k) (Qatlib.Foundations.PureStateMath.Ket j) := by
  rw [evaluatePrepared_amplified,
    (prepared_aa_actual_circuit (evaluatePrepared U B cs) j S k hA).2.2.2]
  rw [applyGate_mul, preparedAAState]

/-- Every state selected by a retry trace is the postmeasurement state of one of its candidate
outputs. -/
theorem selected_is_postMeasure {I : Type} [Fintype I] [DecidableEq I] {m : ℕ}
    (out : Fin (2*m) → QState I) (S : Finset I) (r : ℕ) (tr : Trace m r) (φ : QState I)
    (h : selected out S r tr = some φ) :
    ∃ s : Fin (2*m), φ = PostMeasure (out s) S := by
  induction r generalizing φ with
  | zero => cases tr; simp [selected] at h
  | succ r ih =>
      rcases tr with ⟨s, tail⟩
      cases tail with
      | none =>
          rw [selected] at h
          exact ⟨s, (Option.some.inj h).symm⟩
      | some tail => exact ih tail φ h

/-- The true-branch mass of the coordinate projector is the measurement probability of its index
set. -/
theorem projectiveBranchMass_projector_true {I : Type} [Fintype I] [DecidableEq I]
    (S : Finset I) (ψ : QState I) :
    ProjectiveBranchMass (Projector S) true ψ = MeasureProb ψ S := by
  unfold ProjectiveBranchMass
  rw [projectiveBranch_projector]
  simpa only [MeasureProb, BornProb] using! sum_normSq_collapse ψ S

/-- Every retry trace has nonnegative weight. -/
theorem weight_nonneg {I : Type} [Fintype I] [DecidableEq I] (m : ℕ)
    (out : Fin (2*m) → QState I) (S : Finset I) :
    ∀ (r : ℕ) (tr : Trace m r), 0 ≤ weight m out S r tr := by
  intro r
  induction r with
  | zero => intro tr; simp [weight]
  | succ r ih =>
      intro tr
      rw [weight]
      refine mul_nonneg ?_ ?_
      · positivity
      · rcases tr with ⟨s, tail⟩
        cases tail with
        | none => exact projectiveBranchMass_nonneg (Projector S) true (out s)
        | some tail =>
            exact mul_nonneg (projectiveBranchMass_nonneg (Projector S) false (out s)) (ih tail)

/-- A selected state on a trace of positive weight is the postmeasurement state of a candidate
with positive success probability. -/
theorem weight_pos_selected {I : Type} [Fintype I] [DecidableEq I] (m : ℕ) (hm : 0 < m)
    (out : Fin (2*m) → QState I) (S : Finset I) :
    ∀ (r : ℕ) (tr : Trace m r) (φ : QState I), selected out S r tr = some φ →
      0 < weight m out S r tr → ∃ s : Fin (2*m), φ = PostMeasure (out s) S ∧ 0 < MeasureProb (out s) S := by
  intro r
  induction r with
  | zero => intro tr φ hsel _; cases tr; simp [selected] at hsel
  | succ r ih =>
      intro tr φ hsel hpos
      rcases tr with ⟨s, tail⟩
      have hfac : (0 : ℝ) < (1/(2*m : ℝ)) := by
        have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
        positivity
      cases tail with
      | none =>
          rw [selected] at hsel
          have hφ : φ = PostMeasure (out s) S := (Option.some.inj hsel).symm
          refine ⟨s, hφ, ?_⟩
          rw [weight, projectiveBranchMass_projector_true] at hpos
          exact pos_of_mul_pos_right hpos hfac.le
      | some tail =>
          have hw : 0 < weight m out S r tail := by
            rw [weight] at hpos
            have h1 : 0 < ProjectiveBranchMass (Projector S) false (out s) *
                weight m out S r tail := pos_of_mul_pos_right hpos hfac.le
            exact pos_of_mul_pos_right h1 (projectiveBranchMass_nonneg (Projector S) false (out s))
          exact ih tail φ hsel hw

/-- A state selected by a trace of positive weight is normalized. -/
theorem selected_normalized_of_weight_pos {I : Type} [Fintype I] [DecidableEq I]
    (m : ℕ) (hm : 0 < m) (out : Fin (2*m) → QState I) (S : Finset I) (r : ℕ) (tr : Trace m r)
    (φ : QState I) (hpos : 0 < weight m out S r tr)
    (hsel : selected out S r tr = some φ) :
    Normalized φ := by
  obtain ⟨s, hφ, hmass⟩ := weight_pos_selected m hm out S r tr φ hsel hpos
  rw [hφ]
  exact normalized_postMeasure hmass

/-- A state selected by a sixteen-trial trace of positive weight is normalized. -/
theorem selected_normalized_sixteen {I : Type} [Fintype I] [DecidableEq I]
    (m : ℕ) (hm : 0 < m) (out : Fin (2*m) → QState I) (S : Finset I) (tr : Trace m 16)
    (φ : QState I) (hpos : 0 < weight m out S 16 tr)
    (hsel : selected out S 16 tr = some φ) :
    Normalized φ :=
  selected_normalized_of_weight_pos m hm out S 16 tr φ hpos hsel

end Qatlib.Concepts.HhlAlgorithms.Postselection.HHLUnknown.Probe

noncomputable section
open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Classical BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Concepts.HhlAlgorithms.Postselection.HHLUnknown.Probe

open Qatlib

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Counting a predicate on `k` concatenated copies of a block multiplies the block's count by
`k`. -/
theorem countP_flatten_replicate {α : Type} (p : α → Bool) (block : List α) (k : ℕ) :
    (List.replicate k block).flatten.countP p = k * block.countP p := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [List.replicate_succ, List.flatten_cons, List.countP_append, ih]
      ring

/-- The Boolean predicate recognizing a fixed-gate instruction in a prepared word. -/
def isGate {I : Type} : PreparedStep I → Bool
  | .gate _ => true
  | _ => false

omit [Fintype I] [DecidableEq I] in

/-- The prepared fixed-gate count equals the number of instructions satisfying `isGate`. -/
theorem preparedFixedGates_eq_countP (cs : List (PreparedStep I)) :
    preparedFixedGates cs = cs.countP (isGate (I := I)) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      cases c <;> simp [preparedFixedGates, isGate, ih]

/-- Inverting a prepared word preserves its fixed-gate count. -/
theorem preparedFixedGates_inverseWord (cs : List (PreparedStep I)) :
    preparedFixedGates (inverseWord cs) = preparedFixedGates cs := by
  rw [preparedFixedGates_eq_countP, preparedFixedGates_eq_countP]
  exact countP_inverseWord isGate isGate (by intro x; cases x <;> rfl) cs

/-- One amplification block consisting of preparation, the initial-state reflection, inverse
preparation, and marking. -/
def aaBlock (cs : List (PreparedStep I)) (j : I) (S : Finset I) : List (PreparedStep I) :=
  cs ++ [.gate (ReflectionAbout (outerProduct (Qatlib.Foundations.PureStateMath.Ket j)))] ++ inverseWord cs ++
    [.gate (preparedMark S)]

/-- The amplified word consists of `k` copies of `aaBlock` followed by the original preparation
word. -/
theorem amplified_eq (cs : List (PreparedStep I)) (j : I) (S : Finset I) (k : ℕ) :
    amplified cs j S k = (List.replicate k (aaBlock cs j S)).flatten ++ cs := rfl

/-- The predicate count in an amplification block is the sum of counts from the preparation and
its inverse plus contributions from the two reflections. -/
theorem aaBlock_countP_raw (p : PreparedStep I → Bool) (cs : List (PreparedStep I))
    (j : I) (S : Finset I) :
    (aaBlock cs j S).countP p =
      cs.countP p + (inverseWord cs).countP p +
        (if p (.gate (ReflectionAbout (outerProduct (Qatlib.Foundations.PureStateMath.Ket j)))) then 1 else 0) +
        (if p (.gate (preparedMark S)) then 1 else 0) := by
  simp only [aaBlock, List.countP_append, List.countP_singleton]
  omega

/-- A predicate that rejects both reflections counts only the preparation and inverse
preparation in an amplification block. -/
theorem aaBlock_countP (p : PreparedStep I → Bool) (cs : List (PreparedStep I))
    (j : I) (S : Finset I)
    (hR : p (.gate (ReflectionAbout (outerProduct (Qatlib.Foundations.PureStateMath.Ket j)))) = false)
    (hM : p (.gate (preparedMark S)) = false) :
    (aaBlock cs j S).countP p = cs.countP p + (inverseWord cs).countP p := by
  rw [aaBlock_countP_raw, hR, hM]
  simp

/-- One amplification block combines forward and backward calls in each direction and contains
twice the preparation's fixed gates plus two reflections. -/
theorem aaBlock_counts (cs : List (PreparedStep I)) (j : I) (S : Finset I) :
    dataForwardCalls (aaBlock cs j S) = dataForwardCalls cs + dataBackwardCalls cs ∧
    dataBackwardCalls (aaBlock cs j S) = dataBackwardCalls cs + dataForwardCalls cs ∧
    inputForwardCalls (aaBlock cs j S) = inputForwardCalls cs + inputBackwardCalls cs ∧
    inputBackwardCalls (aaBlock cs j S) = inputBackwardCalls cs + inputForwardCalls cs ∧
    preparedFixedGates (aaBlock cs j S) = 2 * preparedFixedGates cs + 2 := by
  have hDF : dataForwardCalls (aaBlock cs j S) =
      dataForwardCalls cs + dataBackwardCalls cs := by
    rw [show dataForwardCalls (aaBlock cs j S) =
        (aaBlock cs j S).countP (isDataFwd (I := I)) from
      (dataForwardCalls_eq_countP _).symm,
      aaBlock_countP (isDataFwd (I := I)) cs j S (by rfl) (by rfl),
      show (inverseWord cs).countP (isDataFwd (I := I)) = dataBackwardCalls cs from
        countP_inverseWord isDataFwd isDataBwd (by intro x; cases x <;> rfl) cs |>.trans
          (dataBackwardCalls_eq_countP cs).symm,
      show cs.countP (isDataFwd (I := I)) = dataForwardCalls cs from
        (dataForwardCalls_eq_countP cs).symm]
  have hDB : dataBackwardCalls (aaBlock cs j S) =
      dataBackwardCalls cs + dataForwardCalls cs := by
    rw [show dataBackwardCalls (aaBlock cs j S) =
        (aaBlock cs j S).countP (isDataBwd (I := I)) from
      (dataBackwardCalls_eq_countP _).symm,
      aaBlock_countP (isDataBwd (I := I)) cs j S (by rfl) (by rfl),
      show (inverseWord cs).countP (isDataBwd (I := I)) = dataForwardCalls cs from
        countP_inverseWord isDataBwd isDataFwd (by intro x; cases x <;> rfl) cs |>.trans
          (dataForwardCalls_eq_countP cs).symm,
      show cs.countP (isDataBwd (I := I)) = dataBackwardCalls cs from
        (dataBackwardCalls_eq_countP cs).symm]
  have hIF : inputForwardCalls (aaBlock cs j S) =
      inputForwardCalls cs + inputBackwardCalls cs := by
    rw [show inputForwardCalls (aaBlock cs j S) =
        (aaBlock cs j S).countP (isInpFwd (I := I)) from
      (inputForwardCalls_eq_countP _).symm,
      aaBlock_countP (isInpFwd (I := I)) cs j S (by rfl) (by rfl),
      show (inverseWord cs).countP (isInpFwd (I := I)) = inputBackwardCalls cs from
        countP_inverseWord isInpFwd isInpBwd (by intro x; cases x <;> rfl) cs |>.trans
          (inputBackwardCalls_eq_countP cs).symm,
      show cs.countP (isInpFwd (I := I)) = inputForwardCalls cs from
        (inputForwardCalls_eq_countP cs).symm]
  have hIB : inputBackwardCalls (aaBlock cs j S) =
      inputBackwardCalls cs + inputForwardCalls cs := by
    rw [show inputBackwardCalls (aaBlock cs j S) =
        (aaBlock cs j S).countP (isInpBwd (I := I)) from
      (inputBackwardCalls_eq_countP _).symm,
      aaBlock_countP (isInpBwd (I := I)) cs j S (by rfl) (by rfl),
      show (inverseWord cs).countP (isInpBwd (I := I)) = inputForwardCalls cs from
        countP_inverseWord isInpBwd isInpFwd (by intro x; cases x <;> rfl) cs |>.trans
          (inputForwardCalls_eq_countP cs).symm,
      show cs.countP (isInpBwd (I := I)) = inputBackwardCalls cs from
        (inputBackwardCalls_eq_countP cs).symm]
  have hF : preparedFixedGates (aaBlock cs j S) = 2 * preparedFixedGates cs + 2 := by
    rw [preparedFixedGates_eq_countP, aaBlock_countP_raw]
    simp only [isGate, ↓reduceIte]
    rw [show (inverseWord cs).countP isGate = preparedFixedGates cs from
          (preparedFixedGates_eq_countP _).symm |>.trans
            (preparedFixedGates_inverseWord cs),
        show cs.countP isGate = preparedFixedGates cs from
          (preparedFixedGates_eq_countP cs).symm]
    ring
  exact ⟨hDF, hDB, hIF, hIB, hF⟩

/-- The predicate count of an amplified word is `k` times the block count plus the original
word's count. -/
theorem amplified_countP (p : PreparedStep I → Bool) (cs : List (PreparedStep I))
    (j : I) (S : Finset I) (k : ℕ) :
    (amplified cs j S k).countP p = k * (aaBlock cs j S).countP p + cs.countP p := by
  rw [amplified_eq, List.countP_append, countP_flatten_replicate]

/-- The forward and backward data and preparation counts, and the fixed-gate count, of an
amplified word are given by the explicit linear formulas in `k`. -/
theorem amplified_counts (cs : List (PreparedStep I)) (j : I) (S : Finset I) (k : ℕ) :
    dataForwardCalls (amplified cs j S k) =
      k * (dataForwardCalls cs + dataBackwardCalls cs) + dataForwardCalls cs ∧
    dataBackwardCalls (amplified cs j S k) =
      k * (dataBackwardCalls cs + dataForwardCalls cs) + dataBackwardCalls cs ∧
    inputForwardCalls (amplified cs j S k) =
      k * (inputForwardCalls cs + inputBackwardCalls cs) + inputForwardCalls cs ∧
    inputBackwardCalls (amplified cs j S k) =
      k * (inputBackwardCalls cs + inputForwardCalls cs) + inputBackwardCalls cs ∧
    preparedFixedGates (amplified cs j S k) =
      k * (2 * preparedFixedGates cs + 2) + preparedFixedGates cs := by
  obtain ⟨bDF, bDB, bIF, bIB, bF⟩ := aaBlock_counts cs j S
  have hDF : dataForwardCalls (amplified cs j S k) =
      k * (dataForwardCalls cs + dataBackwardCalls cs) + dataForwardCalls cs := by
    rw [show dataForwardCalls (amplified cs j S k) =
        (amplified cs j S k).countP (isDataFwd (I := I)) from
      (dataForwardCalls_eq_countP _).symm, amplified_countP,
      show (aaBlock cs j S).countP (isDataFwd (I := I)) =
        dataForwardCalls (aaBlock cs j S) from (dataForwardCalls_eq_countP _).symm,
      bDF,
      show cs.countP (isDataFwd (I := I)) = dataForwardCalls cs from
        (dataForwardCalls_eq_countP cs).symm]
  have hDB : dataBackwardCalls (amplified cs j S k) =
      k * (dataBackwardCalls cs + dataForwardCalls cs) + dataBackwardCalls cs := by
    rw [show dataBackwardCalls (amplified cs j S k) =
        (amplified cs j S k).countP (isDataBwd (I := I)) from
      (dataBackwardCalls_eq_countP _).symm, amplified_countP,
      show (aaBlock cs j S).countP (isDataBwd (I := I)) =
        dataBackwardCalls (aaBlock cs j S) from (dataBackwardCalls_eq_countP _).symm,
      bDB,
      show cs.countP (isDataBwd (I := I)) = dataBackwardCalls cs from
        (dataBackwardCalls_eq_countP cs).symm]
  have hIF : inputForwardCalls (amplified cs j S k) =
      k * (inputForwardCalls cs + inputBackwardCalls cs) + inputForwardCalls cs := by
    rw [show inputForwardCalls (amplified cs j S k) =
        (amplified cs j S k).countP (isInpFwd (I := I)) from
      (inputForwardCalls_eq_countP _).symm, amplified_countP,
      show (aaBlock cs j S).countP (isInpFwd (I := I)) =
        inputForwardCalls (aaBlock cs j S) from (inputForwardCalls_eq_countP _).symm,
      bIF,
      show cs.countP (isInpFwd (I := I)) = inputForwardCalls cs from
        (inputForwardCalls_eq_countP cs).symm]
  have hIB : inputBackwardCalls (amplified cs j S k) =
      k * (inputBackwardCalls cs + inputForwardCalls cs) + inputBackwardCalls cs := by
    rw [show inputBackwardCalls (amplified cs j S k) =
        (amplified cs j S k).countP (isInpBwd (I := I)) from
      (inputBackwardCalls_eq_countP _).symm, amplified_countP,
      show (aaBlock cs j S).countP (isInpBwd (I := I)) =
        inputBackwardCalls (aaBlock cs j S) from (inputBackwardCalls_eq_countP _).symm,
      bIB,
      show cs.countP (isInpBwd (I := I)) = inputBackwardCalls cs from
        (inputBackwardCalls_eq_countP cs).symm]
  have hF : preparedFixedGates (amplified cs j S k) =
      k * (2 * preparedFixedGates cs + 2) + preparedFixedGates cs := by
    rw [preparedFixedGates_eq_countP, amplified_countP,
      show (aaBlock cs j S).countP isGate = preparedFixedGates (aaBlock cs j S) from
        (preparedFixedGates_eq_countP _).symm, bF,
      show cs.countP isGate = preparedFixedGates cs from
        (preparedFixedGates_eq_countP cs).symm]
  exact ⟨hDF, hDB, hIF, hIB, hF⟩

/-- Inverting a valid prepared circuit preserves validity. -/
theorem preparedCircuitValid_inverseWord (cs : List (PreparedStep I))
    (hcs : PreparedCircuitValid cs) : PreparedCircuitValid (inverseWord cs) := by
  intro c hc
  rw [inverseWord, List.mem_map] at hc
  obtain ⟨d, hd, rfl⟩ := hc
  have hd' : d ∈ cs := List.mem_reverse.mp hd
  cases d with
  | gate V => exact adjoint_unitary (hcs _ hd')
  | dataForward => trivial
  | dataBackward => trivial
  | prepareForward => trivial
  | prepareBackward => trivial

/-- Concatenating two valid prepared circuits gives a valid prepared circuit. -/
theorem preparedCircuitValid_append (cs ds : List (PreparedStep I))
    (hcs : PreparedCircuitValid cs) (hds : PreparedCircuitValid ds) :
    PreparedCircuitValid (cs ++ ds) := by
  intro c hc
  rcases List.mem_append.mp hc with h | h
  · exact hcs c h
  · exact hds c h

/-- Concatenating any number of copies of a valid prepared block preserves validity. -/
theorem preparedCircuitValid_flatten_replicate (block : List (PreparedStep I)) (k : ℕ)
    (hblock : PreparedCircuitValid block) :
    PreparedCircuitValid (List.replicate k block).flatten := by
  intro c hc
  obtain ⟨t, ht, hct⟩ := List.mem_flatten.mp hc
  rw [(List.mem_replicate.mp ht).2] at hct
  exact hblock c hct

/-- An instruction belongs to an amplification block exactly when it belongs to the preparation
or its inverse, or is one of the two reflections. -/
theorem mem_aaBlock (cs : List (PreparedStep I)) (j : I) (S : Finset I)
    (c : PreparedStep I) :
    c ∈ aaBlock cs j S ↔
      c ∈ cs ∨ c = .gate (ReflectionAbout (outerProduct (Qatlib.Foundations.PureStateMath.Ket j))) ∨
        c ∈ inverseWord cs ∨ c = .gate (preparedMark S) := by
  simp only [aaBlock, List.mem_append, List.mem_singleton]
  tauto

/-- An amplification block built from a valid prepared circuit is valid. -/
theorem preparedCircuitValid_amplifiedBlock (cs : List (PreparedStep I))
    (hcs : PreparedCircuitValid cs) (j : I) (S : Finset I) :
    PreparedCircuitValid (aaBlock cs j S) := by
  intro c hc
  rcases (mem_aaBlock cs j S c).mp hc with h | h | h | h
  · exact hcs c h
  · subst h
    exact outerProduct_reflection_unitary (normalized_ket j)
  · exact preparedCircuitValid_inverseWord cs hcs c h
  · subst h
    exact (prepared_aa_reflection_and_access (1 : Matrix I I ℂ) j S
      (Matrix.unitaryGroup I ℂ).one_mem).1

/-- Amplifying a valid prepared circuit preserves validity. -/
theorem preparedCircuitValid_amplified (cs : List (PreparedStep I))
    (hcs : PreparedCircuitValid cs) (j : I) (S : Finset I) (k : ℕ) :
    PreparedCircuitValid (amplified cs j S k) := by
  rw [amplified_eq]
  exact preparedCircuitValid_append _ _
    (preparedCircuitValid_flatten_replicate _ _ (preparedCircuitValid_amplifiedBlock cs hcs j S))
    hcs

/-- An amplified circuit built from the stated HHL base counts is valid and satisfies the
explicit data, input, fixed-gate, and directional-call formulas. -/
theorem amplified_resources (cs : List (PreparedStep I)) (hcs : PreparedCircuitValid cs)
    (j₀ : I) (S : Finset I) (k M : ℕ)
    (hD : preparedDataQueries cs = 2 * (M - 1)) (hI : preparedInputQueries cs = 1)
    (hF : preparedFixedGates cs = 4 * (M - 1) + 5)
    (hDF : dataForwardCalls cs = M - 1) (hDB : dataBackwardCalls cs = M - 1)
    (hIF : inputForwardCalls cs = 1) (hIB : inputBackwardCalls cs = 0) :
    PreparedCircuitValid (amplified cs j₀ S k) ∧
    preparedDataQueries (amplified cs j₀ S k) = (2 * k + 1) * (2 * (M - 1)) ∧
    preparedInputQueries (amplified cs j₀ S k) = 2 * k + 1 ∧
    dataForwardCalls (amplified cs j₀ S k) = (2 * k + 1) * (M - 1) ∧
    dataBackwardCalls (amplified cs j₀ S k) = (2 * k + 1) * (M - 1) ∧
    inputForwardCalls (amplified cs j₀ S k) = k + 1 ∧
    inputBackwardCalls (amplified cs j₀ S k) = k ∧
    preparedFixedGates (amplified cs j₀ S k) = (2 * k + 1) * (4 * (M - 1) + 5) + 2 * k := by
  obtain ⟨aDF, aDB, aIF, aIB, aF⟩ := amplified_counts cs j₀ S k
  have hD' : dataForwardCalls cs + dataBackwardCalls cs = 2 * (M - 1) := by
    rw [← dataQueries_split, hD]
  have hI' : inputForwardCalls cs + inputBackwardCalls cs = 1 := by
    rw [← inputQueries_split, hI]
  refine ⟨preparedCircuitValid_amplified cs hcs j₀ S k, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have eDF := aDF; have eDB := aDB
    rw [hDF, hDB] at eDF eDB
    rw [dataQueries_split, eDF, eDB]
    ring
  · have eIF := aIF; have eIB := aIB
    rw [hIF, hIB] at eIF eIB
    rw [inputQueries_split, eIF, eIB]
    ring
  · rw [aDF, hD', hDF]; ring
  · have eDB := aDB; rw [hDF, hDB] at eDB
    rw [eDB]; ring
  · rw [aIF, hI', hIF]; ring
  · have eIB := aIB; rw [hIF, hIB] at eIB
    rw [eIB]; ring
  · rw [aF, hF]; ring

end Qatlib.Concepts.HhlAlgorithms.Postselection.HHLUnknown.Probe

noncomputable section
open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Concepts.HhlAlgorithms.Postselection.HHLUnknown.Probe

open Qatlib

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The true-branch mass of a coordinate projector equals the corresponding measurement
probability. -/
private theorem tl_pbm_true (ψ : QState I) (S : Finset I) :
    ProjectiveBranchMass (Projector S) true ψ = MeasureProb ψ S := by
  unfold ProjectiveBranchMass
  rw [projectiveBranch_projector]
  simpa only [MeasureProb, BornProb] using! sum_normSq_collapse ψ S

/-- For a normalized state, the false-branch mass is one minus the measurement probability. -/
private theorem tl_pbm_false {ψ : QState I} (hψ : Normalized ψ) (S : Finset I) :
    ProjectiveBranchMass (Projector S) false ψ = 1 - MeasureProb ψ S := by
  have h := projectiveBranchMass_add (projector_isOrthogonalProjector S) ψ
  rw [measureProb_univ hψ, tl_pbm_true ψ S] at h
  linarith

/-- If `m > 0`, then the real number `2 * m` is positive. -/
private theorem tl_two_m_pos {m : ℕ} (hm : 0 < m) : (0:ℝ) < 2*(m:ℝ) := by
  have : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  linarith

/-- Summing values with uniform weight `1 / (2 * m)` equals their sum divided by `2 * m`. -/
private theorem tl_scalar_some (m : ℕ) (f : Fin (2*m) → ℝ) :
    (∑ s : Fin (2*m), (1/(2*(m:ℝ))) * f s) = (∑ s, f s) / (2*(m:ℝ)) := by
  rw [← Finset.mul_sum]
  ring

/-- For `m > 0`, the uniform average of `1 - f` is one minus the uniform average of `f`. -/
private theorem tl_scalar_none {m : ℕ} (hm : 0 < m) (f : Fin (2*m) → ℝ) :
    (∑ s : Fin (2*m), (1/(2*(m:ℝ))) * (1 - f s)) = 1 - (∑ s, f s) / (2*(m:ℝ)) := by
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  have hN : (∑ _ : Fin (2*m), (1:ℝ)) = 2*(m:ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  rw [hN]
  have hcN : (1/(2*(m:ℝ))) * (2*(m:ℝ)) = 1 := by
    rw [one_div, inv_mul_cancel₀]
    exact ne_of_gt (tl_two_m_pos hm)
  rw [mul_sub, hcN]
  ring

/-- The total weight of all retry traces of length at most `r`. -/
private def Total (m : ℕ) (out : Fin (2*m) → QState I) (S : Finset I) (r : ℕ) : ℝ :=
  ∑ tr : Trace m r, weight m out S r tr

/-- The total weight of retry traces that select no output state. -/
private def NoneMass (m : ℕ) (out : Fin (2*m) → QState I) (S : Finset I) (r : ℕ) : ℝ :=
  ∑ tr : Trace m r, if (selected out S r tr).isNone then weight m out S r tr else 0

/-- The total weight of retry traces that select an output state. -/
private def SomeMass (m : ℕ) (out : Fin (2*m) → QState I) (S : Finset I) (r : ℕ) : ℝ :=
  ∑ tr : Trace m r, if (selected out S r tr).isSome then weight m out S r tr else 0

/-- A trace stopping successfully at its first seed has weight equal to the seed's success
probability divided by `2 * m`. -/
private theorem tl_weight_none_avg {m : ℕ} {out : Fin (2*m) → QState I} {S : Finset I}
    (r : ℕ) (s : Fin (2*m)) :
    weight m out S (r+1) (s, none) = (1/(2*(m:ℝ))) * MeasureProb (out s) S := by
  simp only [weight]
  rw [tl_pbm_true]

/-- A trace continuing after its first seed has weight equal to the uniform seed weight times
its failure probability times the tail weight. -/
private theorem tl_weight_some_avg {m : ℕ} {out : Fin (2*m) → QState I} {S : Finset I}
    (h1 : ∀ s : Fin (2*m), Normalized (out s)) (r : ℕ) (s : Fin (2*m)) (tail : Trace m r) :
    weight m out S (r+1) (s, some tail) =
      (1/(2*(m:ℝ))) * ((1 - MeasureProb (out s) S) * weight m out S r tail) := by
  simp only [weight]
  rw [tl_pbm_false (h1 s) S]

/-- A trace stopping at the first seed selects that seed's postmeasurement state. -/
private theorem tl_selected_none {m : ℕ} {out : Fin (2*m) → QState I} {S : Finset I}
    (r : ℕ) (s : Fin (2*m)) :
    selected out S (r+1) (s, none) = some (PostMeasure (out s) S) := by
  rw [selected]

/-- A trace continuing past the first seed selects the same state as its tail. -/
private theorem tl_selected_some {m : ℕ} {out : Fin (2*m) → QState I} {S : Finset I}
    (r : ℕ) (s : Fin (2*m)) (tail : Trace m r) :
    selected out S (r+1) (s, some tail) = selected out S r tail := by
  rw [selected]

/-- The total weight of zero-trial traces is one. -/
private theorem tl_total_zero {m : ℕ} {out : Fin (2*m) → QState I} {S : Finset I} :
    Total m out S 0 = 1 := by
  unfold Total
  change (∑ _ : PUnit, (1:ℝ)) = 1
  simp

/-- The failure mass of zero-trial traces is one. -/
private theorem tl_none_zero {m : ℕ} {out : Fin (2*m) → QState I} {S : Finset I} :
    NoneMass m out S 0 = 1 := by
  unfold NoneMass
  change (∑ _ : PUnit, (if (none : Option (QState I)).isNone then (1:ℝ) else 0)) = 1
  simp

/-- The total trace weight after one more trial is the average success probability plus the
average failure probability times the previous total weight. -/
private theorem tl_total_succ_avg {m : ℕ} {out : Fin (2*m) → QState I} {S : Finset I}
    (hm : 0 < m) (h1 : ∀ s : Fin (2*m), Normalized (out s)) (r : ℕ) :
    Total m out S (r+1) =
      (∑ s : Fin (2*m), MeasureProb (out s) S)/(2*(m:ℝ)) +
      (1 - (∑ s : Fin (2*m), MeasureProb (out s) S)/(2*(m:ℝ))) * Total m out S r := by
  unfold Total
  change (∑ x : Fin (2*m) × Option (Trace m r), weight m out S (r+1) x) =
    (∑ s : Fin (2*m), MeasureProb (out s) S)/(2*(m:ℝ)) +
    (1 - (∑ s : Fin (2*m), MeasureProb (out s) S)/(2*(m:ℝ))) *
      (∑ tr : Trace m r, weight m out S r tr)
  simp only [Fintype.sum_prod_type, Fintype.sum_option]
  trans ∑ s : Fin (2*m), ((1/(2*(m:ℝ))) * MeasureProb (out s) S +
      ((1/(2*(m:ℝ))) * (1 - MeasureProb (out s) S)) *
        (∑ tr : Trace m r, weight m out S r tr))
  · apply Finset.sum_congr rfl
    intro s _
    congr 1
    · rw [tl_weight_none_avg r s]
    · trans ∑ tail : Trace m r,
          (1/(2*(m:ℝ))) * ((1 - MeasureProb (out s) S) * weight m out S r tail)
      · apply Finset.sum_congr rfl
        intro tail _
        exact tl_weight_some_avg h1 r s tail
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro tail _
        ring
  · rw [Finset.sum_add_distrib, ← Finset.sum_mul,
      tl_scalar_some m (fun s => MeasureProb (out s) S),
      tl_scalar_none hm (fun s => MeasureProb (out s) S)]

/-- Each additional trial multiplies the no-output mass by the average failure probability. -/
private theorem tl_none_succ_avg {m : ℕ} {out : Fin (2*m) → QState I} {S : Finset I}
    (hm : 0 < m) (h1 : ∀ s : Fin (2*m), Normalized (out s)) (r : ℕ) :
    NoneMass m out S (r+1) =
      (1 - (∑ s : Fin (2*m), MeasureProb (out s) S)/(2*(m:ℝ))) * NoneMass m out S r := by
  unfold NoneMass
  change (∑ x : Fin (2*m) × Option (Trace m r),
      (if (selected out S (r+1) x).isNone then weight m out S (r+1) x else 0)) =
    (1 - (∑ s : Fin (2*m), MeasureProb (out s) S)/(2*(m:ℝ))) *
      (∑ tr : Trace m r, if (selected out S r tr).isNone then weight m out S r tr else 0)
  simp only [Fintype.sum_prod_type, Fintype.sum_option]
  trans ∑ s : Fin (2*m), ((1/(2*(m:ℝ))) * (1 - MeasureProb (out s) S)) *
      (∑ tr : Trace m r, if (selected out S r tr).isNone then weight m out S r tr else 0)
  · apply Finset.sum_congr rfl
    intro s _
    have hz : (if (selected out S (r+1) (s, none)).isNone then
        weight m out S (r+1) (s, none) else 0) = 0 := by
      rw [tl_selected_none r s]; simp
    rw [hz, zero_add]
    trans ∑ tail : Trace m r, ((1/(2*(m:ℝ))) * (1 - MeasureProb (out s) S)) *
        (if (selected out S r tail).isNone then weight m out S r tail else 0)
    · apply Finset.sum_congr rfl
      intro tail _
      rw [tl_selected_some r s tail, tl_weight_some_avg h1 r s tail]
      cases selected out S r tail with
      | none => split_ifs <;> ring
      | some φ => split_ifs <;> ring
    · rw [Finset.mul_sum]
  · rw [← Finset.sum_mul, tl_scalar_none hm (fun s => MeasureProb (out s) S)]

/-- For normalized candidate states and a nonempty seed window, the total trace weight is one at
every trial count. -/
private theorem tl_total_eq_one_avg {m : ℕ} {out : Fin (2*m) → QState I} {S : Finset I}
    (hm : 0 < m) (h1 : ∀ s : Fin (2*m), Normalized (out s)) :
    ∀ r : ℕ, Total m out S r = 1 := by
  intro r
  induction r with
  | zero => exact tl_total_zero
  | succ r ih =>
      rw [tl_total_succ_avg hm h1 r, ih]
      ring

/-- For normalized candidates, the no-output mass after `r` trials is the `r`th power of one
minus their average success probability. -/
private theorem tl_noneMass_eq_avg {m : ℕ} {out : Fin (2*m) → QState I} {S : Finset I}
    (hm : 0 < m) (h1 : ∀ s : Fin (2*m), Normalized (out s)) :
    ∀ r : ℕ, NoneMass m out S r =
      (1 - (∑ s : Fin (2*m), MeasureProb (out s) S)/(2*(m:ℝ)))^r := by
  intro r
  induction r with
  | zero => rw [tl_none_zero, pow_zero]
  | succ r ih =>
      rw [tl_none_succ_avg hm h1 r, ih, pow_succ]
      ring

/-- Every trace weight is nonnegative when all candidate output states are normalized. -/
private theorem tl_weight_nonneg_avg {m : ℕ} {out : Fin (2*m) → QState I} {S : Finset I}
    (h1 : ∀ s : Fin (2*m), Normalized (out s)) :
    ∀ (r : ℕ) (tr : Trace m r), 0 ≤ weight m out S r tr := by
  intro r
  induction r with
  | zero => intro tr; simp [weight]
  | succ r ih =>
      intro tr
      rcases tr with ⟨s, o⟩
      cases o with
      | none =>
          rw [tl_weight_none_avg r s]
          exact mul_nonneg (by positivity) (measureProb_nonneg (out s) S)
      | some tail =>
          rw [tl_weight_some_avg h1 r s tail]
          exact mul_nonneg (by positivity)
            (mul_nonneg (sub_nonneg.mpr (measureProb_le_one (h1 s) S)) (ih tail))

/-- The selected-output mass and no-output mass sum to the total trace weight. -/
private theorem tl_some_add_none (m : ℕ) (out : Fin (2*m) → QState I) (S : Finset I) (r : ℕ) :
    SomeMass m out S r + NoneMass m out S r = Total m out S r := by
  unfold SomeMass NoneMass Total
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro tr _
  cases selected out S r tr with
  | none => simp
  | some φ => simp

/-- Sixteen fresh trials with average success probability at least `1 / 8` form a normalized
nonnegative trace law with failure mass `(1 - pbar)^16`. Their success mass is at least `1 -
(7 / 8)^16 ≥ 2 / 3`. -/
theorem trace_law_avg {I : Type} [Fintype I] [DecidableEq I] (m : ℕ)
    (out : Fin (2*m) → QState I) (S : Finset I) (hm : 0 < m)
    (h1 : ∀ s : Fin (2*m), Normalized (out s))
    (h8 : (1/8 : ℝ) ≤ (∑ s : Fin (2*m), MeasureProb (out s) S) / (2*m : ℝ)) :
    let pbar := (∑ s : Fin (2*m), MeasureProb (out s) S) / (2*m : ℝ)
    (∀ tr : Trace m 16, 0 ≤ weight m out S 16 tr) ∧
    (∑ tr : Trace m 16, weight m out S 16 tr) = 1 ∧
    (∑ tr : Trace m 16, if (selected out S 16 tr).isNone then weight m out S 16 tr else 0) =
      (1 - pbar)^16 ∧
    (1 - (7/8:ℝ)^16 ≤
        ∑ tr : Trace m 16, if (selected out S 16 tr).isSome then weight m out S 16 tr else 0) ∧
    (2/3 : ℝ) ≤ 1 - (7/8:ℝ)^16 := by
  change (∀ tr : Trace m 16, 0 ≤ weight m out S 16 tr) ∧
    (∑ tr : Trace m 16, weight m out S 16 tr) = 1 ∧
    (∑ tr : Trace m 16, if (selected out S 16 tr).isNone then weight m out S 16 tr else 0) =
      (1 - (∑ s : Fin (2*m), MeasureProb (out s) S) / (2*(m:ℝ)))^16 ∧
    (1 - (7/8:ℝ)^16 ≤
        ∑ tr : Trace m 16, if (selected out S 16 tr).isSome then weight m out S 16 tr else 0) ∧
    (2/3 : ℝ) ≤ 1 - (7/8:ℝ)^16
  have htot : Total m out S 16 = 1 := tl_total_eq_one_avg hm h1 16
  have hnone : NoneMass m out S 16 =
      (1 - (∑ s : Fin (2*m), MeasureProb (out s) S) / (2*(m:ℝ)))^16 :=
    tl_noneMass_eq_avg hm h1 16
  have hsome : SomeMass m out S 16 =
      1 - (1 - (∑ s : Fin (2*m), MeasureProb (out s) S) / (2*(m:ℝ)))^16 := by
    have h := tl_some_add_none m out S 16
    rw [htot, hnone] at h
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fun tr => tl_weight_nonneg_avg h1 16 tr
  · exact htot
  · change NoneMass m out S 16 =
      (1 - (∑ s : Fin (2*m), MeasureProb (out s) S) / (2*(m:ℝ)))^16
    exact hnone
  · change 1 - (7/8:ℝ)^16 ≤ SomeMass m out S 16
    rw [hsome]
    have hsum_le : (∑ s : Fin (2*m), MeasureProb (out s) S) ≤ 2*(m:ℝ) := by
      calc (∑ s : Fin (2*m), MeasureProb (out s) S) ≤ ∑ _ : Fin (2*m), (1:ℝ) :=
            Finset.sum_le_sum (fun s _ => measureProb_le_one (h1 s) S)
        _ = 2*(m:ℝ) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            push_cast
            ring
    have h2mpos : (0:ℝ) < 2*(m:ℝ) := tl_two_m_pos hm
    have hPle : (∑ s : Fin (2*m), MeasureProb (out s) S) / (2*(m:ℝ)) ≤ 1 :=
      (div_le_one h2mpos).mpr hsum_le
    have hbase_nn : (0:ℝ) ≤ 1 - (∑ s : Fin (2*m), MeasureProb (out s) S) / (2*(m:ℝ)) := by
      linarith
    have hbase_le : 1 - (∑ s : Fin (2*m), MeasureProb (out s) S) / (2*(m:ℝ)) ≤ 7/8 := by
      linarith
    have hpow := pow_le_pow_left₀ hbase_nn hbase_le 16
    linarith
  · norm_num

end Qatlib.Concepts.HhlAlgorithms.Postselection.HHLUnknown.Probe

namespace Qatlib.Concepts.HhlAlgorithms.Postselection.HHLUnknown.Probe

open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Collapsing a state to an index set commutes with complex scalar multiplication. -/
private theorem collapse_smul (c : ℂ) (v : QState I) (S : Finset I) :
    Collapse (c • v) S = c • Collapse v S := by
  show (Projector S : Matrix I I ℂ) *ᵥ (c • v) = c • ((Projector S : Matrix I I ℂ) *ᵥ v)
  rw [Matrix.mulVec_smul]

/-- Collapsing a sum to an index set equals the sum of the collapsed states. -/
private theorem collapse_add (u v : QState I) (S : Finset I) :
    Collapse (u + v) S = Collapse u S + Collapse v S := by
  show (Projector S : Matrix I I ℂ) *ᵥ (u + v) =
    (Projector S : Matrix I I ℂ) *ᵥ u + (Projector S : Matrix I I ℂ) *ᵥ v
  rw [Matrix.mulVec_add]

/-- Collapsing a difference to an index set equals the difference of the collapsed states. -/
private theorem collapse_sub (u v : QState I) (S : Finset I) :
    Collapse (u - v) S = Collapse u S - Collapse v S := by
  show (Projector S : Matrix I I ℂ) *ᵥ (u - v) =
    (Projector S : Matrix I I ℂ) *ᵥ u - (Projector S : Matrix I I ℂ) *ᵥ v
  rw [Matrix.mulVec_sub]

/-- Collapsing twice to the same index set equals collapsing once. -/
private theorem collapse_idem (v : QState I) (S : Finset I) :
    Collapse (Collapse v S) S = Collapse v S := by
  show (Projector S : Matrix I I ℂ) *ᵥ ((Projector S : Matrix I I ℂ) *ᵥ v) =
    (Projector S : Matrix I I ℂ) *ᵥ v
  rw [Matrix.mulVec_mulVec, projector_mul_self]

omit [DecidableEq I] in

/-- Applying a matrix gate distributes over addition of states. -/
private theorem gate_add (U : Matrix I I ℂ) (x y : QState I) :
    ApplyGate U (x + y) = ApplyGate U x + ApplyGate U y := Matrix.mulVec_add U x y

omit [DecidableEq I] in

/-- Applying a matrix gate commutes with complex scalar multiplication. -/
private theorem gate_smul (U : Matrix I I ℂ) (c : ℂ) (x : QState I) :
    ApplyGate U (c • x) = c • ApplyGate U x := Matrix.mulVec_smul U c x

/-- A linear combination of two combinations of `bad` and `good` collects into the stated
coefficients of those vectors. -/
private theorem comb {V : Type} [AddCommMonoid V] [Module ℂ V] (bad good : V)
    (r1 r2 c1 c2 c3 c4 : ℂ) :
    r1 • (c1 • bad + c2 • good) + r2 • (c3 • bad + c4 • good)
      = (r1*c1 + r2*c3) • bad + (r1*c2 + r2*c4) • good := by
  have e1 : r1 • (c1 • bad + c2 • good) = (r1*c1) • bad + (r1*c2) • good := by
    rw [smul_add, smul_smul, smul_smul]
  have e2 : r2 • (c3 • bad + c4 • good) = (r2*c3) • bad + (r2*c4) • good := by
    rw [smul_add, smul_smul, smul_smul]
  rw [e1, e2, add_smul, add_smul]
  ac_rfl

/-- The successful component of an amplified state is a complex scalar multiple of the original
prepared state's successful component. -/
theorem amplified_collapse_smul (A : Matrix I I ℂ) (j₀ : I) (S : Finset I) (k : ℕ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    ∃ r : ℂ, Collapse (Run (preparedMark S) (preparedAACircuit A j₀ k) (Qatlib.Foundations.PureStateMath.Ket j₀)) S
      = r • Collapse (preparedAAState A j₀) S := by
  have key : ∀ k : ℕ, ∃ c g : ℂ,
      ApplyGate ((preparedAAIterate A j₀ S)^k) (preparedAAState A j₀)
        = c • (preparedAAState A j₀ - Collapse (preparedAAState A j₀) S)
          + g • Collapse (preparedAAState A j₀) S := by
    intro k
    induction k with
    | zero =>
        refine ⟨1, 1, ?_⟩
        rw [pow_zero, applyGate_one, one_smul, one_smul]
        exact (sub_add_cancel (preparedAAState A j₀) (Collapse (preparedAAState A j₀) S)).symm
    | succ k ih =>
        obtain ⟨c, g, hkg⟩ := ih
        rw [pow_succ', applyGate_mul, hkg, gate_add, gate_smul, gate_smul]
        obtain ⟨hb, hg⟩ := prepared_aa_two_component_step A j₀ S hA
        rw [hb, hg]
        exact ⟨_, _, comb _ _ _ _ _ _ _ _⟩
  rw [(prepared_aa_actual_circuit A j₀ S k hA).2.2.2]
  obtain ⟨c, g, hcg⟩ := key k
  refine ⟨g, ?_⟩
  rw [hcg, collapse_add, collapse_smul, collapse_smul, collapse_sub, collapse_idem,
    sub_self, smul_zero, zero_add]

set_option maxHeartbeats 2000000 in

/-- Whenever the amplified success probability is positive, its postmeasurement state differs
from the original postmeasurement state by a scalar of norm one. -/
theorem amplified_postMeasure_phase (A : Matrix I I ℂ) (j₀ : I) (S : Finset I) (k : ℕ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (hpos : 0 < MeasureProb (Run (preparedMark S) (preparedAACircuit A j₀ k) (Qatlib.Foundations.PureStateMath.Ket j₀)) S) :
    ∃ z : ℂ, ‖z‖ = 1 ∧
      PostMeasure (Run (preparedMark S) (preparedAACircuit A j₀ k) (Qatlib.Foundations.PureStateMath.Ket j₀)) S
        = z • PostMeasure (preparedAAState A j₀) S := by
  obtain ⟨r, hr⟩ := amplified_collapse_smul A j₀ S k hA
  have hsplit : MeasureProb (Run (preparedMark S) (preparedAACircuit A j₀ k) (Qatlib.Foundations.PureStateMath.Ket j₀)) S
      = ‖r‖^2 * MeasureProb (preparedAAState A j₀) S := by
    have h2 : ∀ i : I, ‖((r : ℂ) • Collapse (preparedAAState A j₀) S) i‖^2
        = ‖r‖^2 * ‖(Collapse (preparedAAState A j₀) S) i‖^2 := by
      intro i
      have hentry : ((r : ℂ) • Collapse (preparedAAState A j₀) S) i
          = r * (Collapse (preparedAAState A j₀) S) i := rfl
      rw [hentry, norm_mul, mul_pow]
    calc MeasureProb (Run (preparedMark S) (preparedAACircuit A j₀ k) (Qatlib.Foundations.PureStateMath.Ket j₀)) S
        = ∑ i, ‖(Collapse (Run (preparedMark S) (preparedAACircuit A j₀ k) (Qatlib.Foundations.PureStateMath.Ket j₀)) S) i‖^2 :=
          (sum_normSq_collapse _ S).symm
      _ = ∑ i, ‖((r : ℂ) • Collapse (preparedAAState A j₀) S) i‖^2 := by
          rw [hr]
      _ = ‖r‖^2 * ∑ i, ‖(Collapse (preparedAAState A j₀) S) i‖^2 := by
          rw [Finset.sum_congr rfl (fun i _ => h2 i), Finset.mul_sum]
      _ = ‖r‖^2 * MeasureProb (preparedAAState A j₀) S := by
          rw [sum_normSq_collapse]
  have hPb0 : 0 < MeasureProb (preparedAAState A j₀) S := by
    rcases lt_or_ge 0 (MeasureProb (preparedAAState A j₀) S) with h | h
    · exact h
    · have hnn : 0 ≤ MeasureProb (preparedAAState A j₀) S := measureProb_nonneg _ _
      have h0 : MeasureProb (preparedAAState A j₀) S = 0 := le_antisymm h hnn
      rw [hsplit, h0] at hpos
      simp at hpos
  have hr0 : ‖r‖ ≠ 0 := by
    intro h
    rw [h] at hsplit
    simp at hsplit
    exact absurd hsplit hpos.ne'
  have hsqrtPr : Real.sqrt (MeasureProb (Run (preparedMark S) (preparedAACircuit A j₀ k)
      (Qatlib.Foundations.PureStateMath.Ket j₀)) S) = ‖r‖ * Real.sqrt (MeasureProb (preparedAAState A j₀) S) := by
    rw [hsplit, Real.sqrt_mul (sq_nonneg ‖r‖), Real.sqrt_sq (norm_nonneg r)]
  refine ⟨r * (((Real.sqrt (MeasureProb (preparedAAState A j₀) S))/(Real.sqrt
    (MeasureProb (Run (preparedMark S) (preparedAACircuit A j₀ k) (Qatlib.Foundations.PureStateMath.Ket j₀)) S)) : ℝ) : ℂ),
    ?_, ?_⟩
  · have hnp : (‖r‖ * Real.sqrt (MeasureProb (preparedAAState A j₀) S)) ≠ 0 :=
      mul_ne_zero hr0 (Real.sqrt_pos_of_pos hPb0).ne'
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div,
      abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _), hsqrtPr]
    field_simp
  · have hcast : (((Real.sqrt (MeasureProb (preparedAAState A j₀) S))/(Real.sqrt
        (MeasureProb (Run (preparedMark S) (preparedAACircuit A j₀ k) (Qatlib.Foundations.PureStateMath.Ket j₀)) S)) : ℝ) : ℂ)
        = ((Real.sqrt (MeasureProb (preparedAAState A j₀) S) : ℂ)) *
          ((Real.sqrt (MeasureProb (Run (preparedMark S) (preparedAACircuit A j₀ k)
            (Qatlib.Foundations.PureStateMath.Ket j₀)) S) : ℂ))⁻¹ := by
      push_cast
      field_simp
    have hz : (r * (((Real.sqrt (MeasureProb (preparedAAState A j₀) S))/(Real.sqrt
        (MeasureProb (Run (preparedMark S) (preparedAACircuit A j₀ k) (Qatlib.Foundations.PureStateMath.Ket j₀)) S)) : ℝ) : ℂ))
        * ((Real.sqrt (MeasureProb (preparedAAState A j₀) S) : ℂ))⁻¹
        = ((Real.sqrt (MeasureProb (Run (preparedMark S) (preparedAACircuit A j₀ k)
          (Qatlib.Foundations.PureStateMath.Ket j₀)) S) : ℂ))⁻¹ * r := by
      rw [hcast]
      have h1 : ((Real.sqrt (MeasureProb (preparedAAState A j₀) S) : ℂ)) ≠ 0 := by
        exact_mod_cast (Real.sqrt_pos_of_pos hPb0).ne'
      have h2 : ((Real.sqrt (MeasureProb (Run (preparedMark S) (preparedAACircuit A j₀ k)
          (Qatlib.Foundations.PureStateMath.Ket j₀)) S) : ℂ)) ≠ 0 := by
        exact_mod_cast (Real.sqrt_pos_of_pos hpos).ne'
      field_simp
    funext i
    have hL : (PostMeasure (Run (preparedMark S) (preparedAACircuit A j₀ k) (Qatlib.Foundations.PureStateMath.Ket j₀)) S) i
        = ((Real.sqrt (MeasureProb (Run (preparedMark S) (preparedAACircuit A j₀ k)
          (Qatlib.Foundations.PureStateMath.Ket j₀)) S) : ℂ))⁻¹ * (r * (Collapse (preparedAAState A j₀) S) i) := by
      show ((Real.sqrt (MeasureProb (Run (preparedMark S) (preparedAACircuit A j₀ k)
        (Qatlib.Foundations.PureStateMath.Ket j₀)) S) : ℂ))⁻¹ * (Collapse (Run (preparedMark S) (preparedAACircuit A j₀ k)
        (Qatlib.Foundations.PureStateMath.Ket j₀)) S) i = _
      rw [hr]
      rfl
    rw [hL]
    show ((Real.sqrt (MeasureProb (Run (preparedMark S) (preparedAACircuit A j₀ k)
      (Qatlib.Foundations.PureStateMath.Ket j₀)) S) : ℂ))⁻¹ * (r * (Collapse (preparedAAState A j₀) S) i) =
      (r * (((Real.sqrt (MeasureProb (preparedAAState A j₀) S))/(Real.sqrt
        (MeasureProb (Run (preparedMark S) (preparedAACircuit A j₀ k) (Qatlib.Foundations.PureStateMath.Ket j₀)) S)) : ℝ) : ℂ)) *
      (((Real.sqrt (MeasureProb (preparedAAState A j₀) S) : ℂ))⁻¹ *
        (Collapse (preparedAAState A j₀) S) i)
    conv_rhs => rw [← mul_assoc, hz]
    ring

end Qatlib.Concepts.HhlAlgorithms.Postselection.HHLUnknown.Probe

open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Concepts.HhlAlgorithms.Postselection.HHLUnknown.Probe

open Qatlib

/-- A retry trace with trial bound `r` records at most `r` history entries. -/
private theorem history_length_le (m : ℕ) :
    ∀ (r : ℕ) (tr : Trace m r), (history (m := m) r tr).length ≤ r := by
  intro r
  induction r with
  | zero => intro tr; simp [history]
  | succ r ih =>
      intro tr
      rcases tr with ⟨s, o⟩
      cases o with
      | none => simp [history]
      | some tail =>
          simp only [history, List.length_cons]
          exact Nat.succ_le_succ (ih tail)

/-- Every depth encoded by a seed in the doubled window is at most `m - 1`. -/
private theorem depth_le (m : ℕ) (s : Fin (2*m)) : depth m s ≤ m - 1 := by
  simp only [depth]
  split_ifs with h
  · omega
  · have := s.isLt; omega

/-- If every mapped natural number is at most `C`, their list sum is at most the list length
times `C`. -/
private theorem sum_map_le {β : Type} (l : List β) (f : β → ℕ) (C : ℕ)
    (h : ∀ b, f b ≤ C) : (l.map f).sum ≤ l.length * C := by
  induction l with
  | nil => simp
  | cons b l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      calc f b + (l.map f).sum ≤ C + l.length * C := Nat.add_le_add (h b) ih
        _ = (l.length + 1) * C := by ring

/-- A constant natural factor can be taken outside a sum over a mapped list. -/
private theorem sum_map_mul_const {β : Type} (l : List β) (g : β → ℕ) (K : ℕ) :
    (l.map (fun b => g b * K)).sum = K * (l.map g).sum := by
  induction l with
  | nil => simp
  | cons b l ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      ring

/-- Pointwise equal natural-valued functions give equal maps of any list. -/
private theorem map_eq_of_pointwise {β : Type} (l : List β) (f g : β → ℕ)
    (h : ∀ b, f b = g b) : l.map f = l.map g :=
  List.map_congr_left (fun b _ => h b)

/-- The fixed-gate cost at any sampled depth is bounded by the cost expression at depth `m - 1`. -/
private theorem fixed_term_le (m M : ℕ) (hm : 0 < m) (s : Fin (2*m)) :
    (2*depth m s+1)*(4*(M-1)+5) + 2*depth m s ≤
      (2*m-1)*(4*(M-1)+5) + 2*(m-1) := by
  have hd := depth_le m s
  have h1 : 2*depth m s + 1 ≤ 2*m-1 := by omega
  have h2 : 2*depth m s ≤ 2*(m-1) := Nat.mul_le_mul_left 2 hd
  exact Nat.add_le_add (Nat.mul_le_mul_right _ h1) h2

/-- Every sixteen-trial trace satisfies the stated history-length, input-query, data-query,
fixed-gate, and seed-bit bounds under the per-seed resource formulas. -/
theorem trace_resources {I : Type} [Fintype I] [DecidableEq I]
    (m M : ℕ) (words : Fin (2*m) → List (PreparedStep I)) (hm : 0 < m)
    (seedExtra : ℕ)
    (hin : ∀ s : Fin (2*m), preparedInputQueries (words s) = 2*(depth m s) + 1)
    (hdat : ∀ s : Fin (2*m),
      preparedDataQueries (words s) = (2*(depth m s) + 1) * (2*(M-1)))
    (hfix : ∀ s : Fin (2*m),
      preparedFixedGates (words s) = (2*(depth m s) + 1)*(4*(M-1)+5) + 2*(depth m s)) :
    ∀ tr : Trace m 16,
      (history (m := m) 16 tr).length ≤ 16 ∧
      (totalInput (m := m) words tr) ≤ 16*(2*m-1) ∧
      (totalData (m := m) words tr) = (2*(M-1))*(totalInput (m := m) words tr) ∧
      (totalFixed (m := m) words tr) ≤
        16*((2*m-1)*(4*(M-1)+5)+2*(m-1)) ∧
      (history (m := m) 16 tr).length*(seedExtra+1) ≤ 16*(seedExtra+1) := by
  intro tr
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact history_length_le m 16 tr
  · have hterm : ∀ z : Fin (2*m) × Bool,
        preparedInputQueries (words z.1) ≤ 2*m - 1 := by
      intro z
      have hd := depth_le m z.1
      rw [hin z.1]
      omega
    calc (totalInput (m := m) words tr)
        = ((history (m := m) 16 tr).map
            (fun z => preparedInputQueries (words z.1))).sum := rfl
      _ ≤ (history (m := m) 16 tr).length * (2*m-1) :=
            sum_map_le _ _ _ hterm
      _ ≤ 16 * (2*m-1) :=
            Nat.mul_le_mul_right _ (history_length_le m 16 tr)
  · have hlin : (history (m := m) 16 tr).map
        (fun z => preparedDataQueries (words z.1)) =
        (history (m := m) 16 tr).map
          (fun z => (2*(depth m z.1)+1) * (2*(M-1))) :=
      map_eq_of_pointwise _ _ _ (fun z => hdat z.1)
    have hinmap : (history (m := m) 16 tr).map
        (fun z => preparedInputQueries (words z.1)) =
        (history (m := m) 16 tr).map (fun z => 2*(depth m z.1)+1) :=
      map_eq_of_pointwise _ _ _ (fun z => hin z.1)
    show ((history (m := m) 16 tr).map
        (fun z => preparedDataQueries (words z.1))).sum =
      (2*(M-1)) * ((history (m := m) 16 tr).map
        (fun z => preparedInputQueries (words z.1))).sum
    rw [hlin, hinmap, sum_map_mul_const]
  · have hterm : ∀ z : Fin (2*m) × Bool,
        preparedFixedGates (words z.1) ≤
          (2*m-1)*(4*(M-1)+5) + 2*(m-1) := by
      intro z
      rw [hfix z.1]
      exact fixed_term_le m M hm z.1
    calc (totalFixed (m := m) words tr)
        = ((history (m := m) 16 tr).map
            (fun z => preparedFixedGates (words z.1))).sum := rfl
      _ ≤ (history (m := m) 16 tr).length *
            ((2*m-1)*(4*(M-1)+5) + 2*(m-1)) := sum_map_le _ _ _ hterm
      _ ≤ 16 * ((2*m-1)*(4*(M-1)+5) + 2*(m-1)) :=
            Nat.mul_le_mul_right _ (history_length_le m 16 tr)
  · exact Nat.mul_le_mul_right _ (history_length_le m 16 tr)

end Qatlib.Concepts.HhlAlgorithms.Postselection.HHLUnknown.Probe

namespace Qatlib.Concepts.HhlAlgorithms.Postselection.HHLUnknown.Probe

open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- Counting query instructions with `countP` equals `QueryCount`. -/
private theorem queryCount_eq_countP {I : Type} (C : Circuit I) :
    C.countP (fun s => match s with | .query => true | _ => false) = QueryCount C := by
  induction C with
  | nil => rfl
  | cons s C ih => cases s <;> simp [QueryCount, ih]

/-- For a nonempty phase grid, the counted QPE word uses exactly `M - 1` forward queries. -/
private theorem qpe_fwd (D M : ℕ) (hM : 0 < M) :
    fwdCount (countedQPEWord D M) = M - 1 := by
  have hqc : QueryCount (countedPhaseCircuit (I := Bool × Fin D) M) = M - 1 :=
    (counted_offgrid_qpe_clean_flag (I := Bool × Fin D) M hM
      (1 : Matrix (Bool × Fin D) (Bool × Fin D) ℂ) 0).2.1
  have e1 : fwdCount (countedQPEWord D M) =
      fwdCount ((countedPhaseCircuit (I := Bool × Fin D) M).map stepToAdjoint) := by
    unfold countedQPEWord
    simp only [fwdCount, List.countP_reverse]
  have e2 : fwdCount ((countedPhaseCircuit (I := Bool × Fin D) M).map stepToAdjoint) =
      QueryCount (countedPhaseCircuit (I := Bool × Fin D) M) := by
    simp only [fwdCount]
    rw [List.countP_map, ← queryCount_eq_countP]
    apply List.countP_congr
    intro s _
    cases s <;> rfl
  rw [e1, e2]
  exact hqc

/-- The counted QPE word contains no backward queries. -/
private theorem qpe_bwd (D M : ℕ) :
    bwdCount (countedQPEWord D M) = 0 := by
  have e1 : bwdCount (countedQPEWord D M) =
      bwdCount ((countedPhaseCircuit (I := Bool × Fin D) M).map stepToAdjoint) := by
    unfold countedQPEWord
    simp only [bwdCount, List.countP_reverse]
  have e2 : bwdCount ((countedPhaseCircuit (I := Bool × Fin D) M).map stepToAdjoint) = 0 := by
    simp only [bwdCount]
    rw [List.countP_map]
    apply List.countP_eq_zero.mpr
    intro s _
    cases s <;> simp [stepToAdjoint]
  rw [e1, e2]

/-- The number of forward queries is additive under circuit concatenation. -/
private theorem fwdCount_append {I : Type} (cs ds : List (AdjointStep I)) :
    fwdCount (cs ++ ds) = fwdCount cs + fwdCount ds := by
  simp only [fwdCount, List.countP_append]

/-- The number of backward queries is additive under circuit concatenation. -/
private theorem bwdCount_append {I : Type} (cs ds : List (AdjointStep I)) :
    bwdCount (cs ++ ds) = bwdCount cs + bwdCount ds := by
  simp only [bwdCount, List.countP_append]

/-- The rational HHL core has `2 * (M - 1)` queries, `4 * (M - 1) + 5` fixed gates, and `M - 1`
queries in each direction. -/
private theorem core_counts (D M bits : ℕ) (d : ℚ) (hM : 0 < M) :
    adjointQueryCount (core D M bits d) = 2*(M-1) ∧
    adjointGateCount (core D M bits d) = 4*(M-1)+5 ∧
    fwdCount (core D M bits d) = M-1 ∧
    bwdCount (core D M bits d) = M-1 := by
  have hq := countedQPEWord_counts D M hM
  have hfw := qpe_fwd D M hM
  have hbw := qpe_bwd D M
  have hfA : fwdCount (Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit (countedQPEWord D M)) = 0 := by
    rw [fwdCount_adjointCircuit, hbw]
  have hbA : bwdCount (Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit (countedQPEWord D M)) = M - 1 := by
    rw [bwdCount_adjointCircuit, hfw]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [core, adjointQueryCount_append, adjointQueryCount_append,
      adjointQueryCount_adjointCircuit, hq.1]
    simp only [adjointQueryCount]
    omega
  · rw [core, adjointGateCount_append, adjointGateCount_append,
      adjointGateCount_adjointCircuit, hq.2]
    simp only [adjointGateCount]
    omega
  · rw [core, fwdCount_append, fwdCount_append,
      show fwdCount ([.gate (countedHHLLiftGate (rationalHHLFlag d bits))] :
        List (AdjointStep (Space D M))) = 0 from rfl, hfA, hfw]
    omega
  · rw [core, bwdCount_append, bwdCount_append,
      show bwdCount ([.gate (countedHHLLiftGate (rationalHHLFlag d bits))] :
        List (AdjointStep (Space D M))) = 0 from rfl, hbA, hbw]
    omega

/-- The rational HHL base word has the stated data, preparation, and fixed-gate counts, with `M
- 1` data calls in each direction and one forward preparation. -/
private theorem base_counts (D M bits : ℕ) (d : ℚ) (hM : 0 < M) :
    preparedDataQueries (base D M bits d) = 2*(M-1) ∧
    preparedInputQueries (base D M bits d) = 1 ∧
    preparedFixedGates (base D M bits d) = 4*(M-1)+5 ∧
    dataForwardCalls (base D M bits d) = M-1 ∧
    dataBackwardCalls (base D M bits d) = M-1 ∧
    inputForwardCalls (base D M bits d) = 1 ∧
    inputBackwardCalls (base D M bits d) = 0 := by
  have hc := core_counts D M bits d hM
  have htrial := preparedTrial_counts (core D M bits d)
  have hsplit := piecewise_counts_append ((core D M bits d).map preparedOfAdjoint)
    ([.prepareForward] : List (PreparedStep (Space D M)))
  have hzeroF : dataForwardCalls
      ([.prepareForward] : List (PreparedStep (Space D M))) = 0 := rfl
  have hzeroB : dataBackwardCalls
      ([.prepareForward] : List (PreparedStep (Space D M))) = 0 := rfl
  have honeI : inputForwardCalls
      ([.prepareForward] : List (PreparedStep (Space D M))) = 1 := rfl
  have hzeroI : inputBackwardCalls
      ([.prepareForward] : List (PreparedStep (Space D M))) = 0 := rfl
  have hIF0 : inputForwardCalls ((core D M bits d).map preparedOfAdjoint) = 0 := by
    rw [inputForwardCalls_eq_countP, countP_map_preparedOfAdjoint,
      List.countP_eq_zero.mpr (by intro x _; cases x <;> simp [isInpFwd])]
  have hIB0 : inputBackwardCalls ((core D M bits d).map preparedOfAdjoint) = 0 := by
    rw [inputBackwardCalls_eq_countP, countP_map_preparedOfAdjoint,
      List.countP_eq_zero.mpr (by intro x _; cases x <;> simp [isInpBwd])]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show base D M bits d = preparedTrial (core D M bits d) from rfl, htrial.1, hc.1]
  · rw [show base D M bits d = preparedTrial (core D M bits d) from rfl, htrial.2.1]
  · rw [show base D M bits d = preparedTrial (core D M bits d) from rfl, htrial.2.2, hc.2.1]
  · show dataForwardCalls (((core D M bits d).map preparedOfAdjoint) ++
      [.prepareForward]) = M-1
    rw [hsplit.1, hzeroF, dataForwardCalls_map, hc.2.2.1]
    omega
  · show dataBackwardCalls (((core D M bits d).map preparedOfAdjoint) ++
      [.prepareForward]) = M-1
    rw [hsplit.2.1, hzeroB, dataBackwardCalls_map, hc.2.2.2]
    omega
  · show inputForwardCalls (((core D M bits d).map preparedOfAdjoint) ++
      [.prepareForward]) = 1
    rw [hsplit.2.2.1, honeI, hIF0]
  · show inputBackwardCalls (((core D M bits d).map preparedOfAdjoint) ++
      [.prepareForward]) = 0
    rw [hsplit.2.2.2, hzeroI, hIB0]

end Qatlib.Concepts.HhlAlgorithms.Postselection.HHLUnknown.Probe

namespace Qatlib.Concepts.HhlAlgorithms.Postselection

open Qatlib
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

set_option maxHeartbeats 1000000 in

/-- Establishes `FiniteComputedUnknownSuccess` for the rational HHL schedule, including finite
seed sampling, amplification, retry selection, and resource accounting; see
[BrassardEtAl2002]. -/
theorem rational_hhl_unknown_success_schedule :
    Qatlib.Concepts.HhlAlgorithms.Postselection.FiniteComputedUnknownSuccess := by
  intro D eig V B W j d theta k hV hB hW hd0 hd14 ht0 ht1 heig hover hnoise
  obtain ⟨hM, _hnrm, hple, herr, -, -⟩ := rational_hhl_parameter_selected_consumer
    D eig V B W j d theta k hV hB hW hd0 hd14 ht0 ht1 heig hover hnoise
  refine ⟨hM, ?_⟩
  (try dsimp only)
  set M := numericHHLGrid d theta k with hMg
  set bits := numericHHLBits d theta k with hbitsg
  set m := window d theta with hmg
  set S := flagSuccessSet D M with hSg
  set cs := base D M bits d with hcsg
  set A := evaluatePrepared (countedHHLOracleLift W) (inputLift B) cs with hAg
  have hM0 : 0 < M := by omega
  have h1m : 1 ≤ m := HHLUnknown.Probe.one_le_window d theta
  have hm : 0 < m := by omega

  have hwf : WellFormedAdjointCircuit (core D M bits d) := by
    have hq := countedQPEWord_wellFormed D M hM0
    simp only [core, WellFormedAdjointCircuit.append_iff,
      WellFormedAdjointCircuit.gate_cons_iff, WellFormedAdjointCircuit.nil, and_true]
    exact ⟨⟨hq.adjointCircuit, countedHHLLiftGate_unitary (rationalHHLFlag_unitary d bits)⟩, hq⟩
  have hcsvalid : PreparedCircuitValid cs := preparedTrial_valid hwf
  have hA : A ∈ Matrix.unitaryGroup (Space D M) ℂ :=
    PreparedCircuitValid.evaluate_unitary hcsvalid (countedHHLOracleLift_unitary hW)
      (countedHHLLiftGate_unitary (countedHHLPrepMain_unitary hB))

  have hAeq : A = evaluate (countedHHLOracleLift W) (rationalHHLWord M d bits B) := by
    show evaluatePrepared (countedHHLOracleLift W) (inputLift B) (base D M bits d) = _
    have hword : rationalHHLWord M d bits B =
        core D M bits d ++ [.gate (inputLift (D := D) (M := M) B)] := by
      simp only [rationalHHLWord, core, inputLift, List.append_assoc]
    rw [hword, evaluate_append]
    simp only [evaluate, instructionMatrix, mul_one]
    rw [show base D M bits d = preparedTrial (core D M bits d) from rfl,
      Qatlib.Concepts.LchsSimulation.StaticLchs.evaluate_preparedTrial]
  have hket : Qatlib.Foundations.PureStateMath.Ket (source hM j) = TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M))
      (TensorState (Qatlib.Foundations.PureStateMath.Ket false) (TensorState (Qatlib.Foundations.PureStateMath.Ket false) (Qatlib.Foundations.PureStateMath.Ket j))) := by
    rw [show source hM j = (⟨0, by omega⟩, (false, (false, j))) from rfl]
    rw [← tensorState_ket_ket, ← tensorState_ket_ket, ← tensorState_ket_ket]
  have h9 : A *ᵥ Qatlib.Foundations.PureStateMath.Ket (source hM j) = rationalHHLRun M hM W d bits B j := by
    rw [hAeq, hket, rationalHHLRun]

  have hbase7 := HHLUnknown.Probe.base_counts D M bits d hM0
  have resources : ∀ s : Fin (2*m),
      PreparedCircuitValid (amplified cs (source hM j) S (depth m s)) ∧
      preparedDataQueries (amplified cs (source hM j) S (depth m s)) =
        (2*depth m s+1)*(2*(M-1)) ∧
      preparedInputQueries (amplified cs (source hM j) S (depth m s)) = 2*depth m s+1 ∧
      dataForwardCalls (amplified cs (source hM j) S (depth m s)) = (2*depth m s+1)*(M-1) ∧
      dataBackwardCalls (amplified cs (source hM j) S (depth m s)) = (2*depth m s+1)*(M-1) ∧
      inputForwardCalls (amplified cs (source hM j) S (depth m s)) = depth m s+1 ∧
      inputBackwardCalls (amplified cs (source hM j) S (depth m s)) = depth m s ∧
      preparedFixedGates (amplified cs (source hM j) S (depth m s)) =
        (2*depth m s+1)*(4*(M-1)+5)+2*depth m s :=
    fun s => HHLUnknown.Probe.amplified_resources cs hcsvalid (source hM j) S (depth m s) M
      hbase7.1 hbase7.2.1 hbase7.2.2.1 hbase7.2.2.2.1 hbase7.2.2.2.2.1
      hbase7.2.2.2.2.2.1 hbase7.2.2.2.2.2.2
  have hout_run : ∀ s : Fin (2*m), output hM W B j d bits (depth m s) =
      Run (preparedMark S) (preparedAACircuit A (source hM j) (depth m s)) (Qatlib.Foundations.PureStateMath.Ket (source hM j)) :=
    fun s => HHLUnknown.Probe.amplified_run (countedHHLOracleLift W) (inputLift B) cs
      (source hM j) S (depth m s) hA
  have hwordU : ∀ s : Fin (2*m), evaluatePrepared (countedHHLOracleLift W) (inputLift B)
      (amplified cs (source hM j) S (depth m s)) ∈ Matrix.unitaryGroup (Space D M) ℂ :=
    fun s => PreparedCircuitValid.evaluate_unitary (resources s).1
      (countedHHLOracleLift_unitary hW) (countedHHLLiftGate_unitary (countedHHLPrepMain_unitary hB))
  have hnorm : ∀ s : Fin (2*m), Normalized (output hM W B j d bits (depth m s)) :=
    fun s => normalized_applyGate (hwordU s) (normalized_ket (source hM j))

  have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd0
  have htR : (0:ℝ) < (theta:ℝ) := by exact_mod_cast ht0
  have hdt : (0:ℝ) < (d:ℝ)*(theta:ℝ) := by positivity
  have ha0 : ((d:ℝ)*(theta:ℝ)/2)^2 ≤ MeasureProb (preparedAAState A (source hM j)) S := by
    rw [show preparedAAState A (source hM j) = A *ᵥ Qatlib.Foundations.PureStateMath.Ket (source hM j) from rfl, h9]
    exact hple
  have hα0 : (0:ℝ) < (d:ℝ)*(theta:ℝ)/2 := by positivity
  have h4 : ((4/(d*theta) : ℚ) : ℝ) ≤ (m:ℝ) := by
    exact_mod_cast HHLUnknown.Probe.four_div_le_window d theta hd0 ht0
  have h4cast : ((4/(d*theta) : ℚ) : ℝ) = 4/((d:ℝ)*(theta:ℝ)) := by
    push_cast
    ring
  have hwin : 1 ≤ (m:ℝ) * ((d:ℝ)*(theta:ℝ)/2) := by
    rw [h4cast] at h4
    have hnn : (0:ℝ) ≤ (d:ℝ)*(theta:ℝ)/2 :=
      div_nonneg (mul_nonneg hdR.le htR.le) (by norm_num)
    have hmul := mul_le_mul_of_nonneg_right h4 hnn
    have h42 : (4:ℝ)/((d:ℝ)*(theta:ℝ)) * ((d:ℝ)*(theta:ℝ)/2) = 2 := by
      field_simp
      ring
    rw [h42] at hmul
    linarith
  have havg := HHLUnknown.Probe.mixed_window_avg A (source hM j) S m ((d:ℝ)*(theta:ℝ)/2)
    hA hm hα0 ha0 hwin
  have h11 : (1/8:ℝ) ≤
      (∑ s : Fin (2*m), MeasureProb (output hM W B j d bits (depth m s)) S)/(2*m : ℝ) := by
    have hsum : (∑ s : Fin (2*m), MeasureProb (output hM W B j d bits (depth m s)) S) =
        (∑ s : Fin (2*m), MeasureProb
          (Run (preparedMark S) (preparedAACircuit A (source hM j) (depth m s))
            (Qatlib.Foundations.PureStateMath.Ket (source hM j))) S) :=
      Finset.sum_congr rfl (fun s _ => by rw [hout_run s])
    rw [hsum]
    exact havg

  have htl := HHLUnknown.Probe.trace_law_avg m
    (fun s : Fin (2*m) => output hM W B j d bits (depth m s)) S hm hnorm h11

  have htr := HHLUnknown.Probe.trace_resources m M
    (fun s : Fin (2*m) => amplified cs (source hM j) S (depth m s)) hm (seedBits d theta)
    (fun s => (resources s).2.2.1) (fun s => (resources s).2.1)
    (fun s => (resources s).2.2.2.2.2.2.2)

  refine ⟨HHLUnknown.Probe.seedOfBits_bijective d theta,
    HHLUnknown.Probe.one_le_window d theta,
    HHLUnknown.Probe.window_le d theta,
    HHLUnknown.Probe.four_div_le_window d theta hd0 ht0,
    (rational_hhl_numeric_table_work M bits d hd0).1,
    rationalHHLTable_get M d bits,
    (rational_hhl_numeric_table_work M bits d hd0).2,
    hA, h9, ?_, h11, htl.1, htl.2.1, htl.2.2.1, htl.2.2.2.1, htl.2.2.2.2,
    fun tr => htr tr, ?_⟩
  · intro s
    exact ⟨(resources s).1, hnorm s, hout_run s, (resources s).2.1, (resources s).2.2.1,
      (resources s).2.2.2.1, (resources s).2.2.2.2.1, (resources s).2.2.2.2.2.1,
      (resources s).2.2.2.2.2.2.1, (resources s).2.2.2.2.2.2.2⟩
  · intro tr φ hpos hsel
    refine ⟨HHLUnknown.Probe.selected_normalized_sixteen m hm
      (fun s : Fin (2*m) => output hM W B j d bits (depth m s)) S tr φ hpos hsel, ?_⟩
    obtain ⟨s, hφ, hprob⟩ := HHLUnknown.Probe.weight_pos_selected m hm
      (fun s : Fin (2*m) => output hM W B j d bits (depth m s)) S 16 tr φ hsel hpos
    subst hφ
    show ∃ z : ℂ, ‖z‖ = 1 ∧ ‖toEuclidean_fromVec (z • PostMeasure
      (output hM W B j d bits (depth m s)) S -
      uniformHHLSolutionTarget M hM eig V B j)‖ ≤ (1/2 : ℝ)^k
    rw [hout_run s] at hprob ⊢
    obtain ⟨z1, hz1n, hz1eq⟩ := HHLUnknown.Probe.amplified_postMeasure_phase A (source hM j) S
      (depth m s) hA hprob
    have hz1ne : z1 ≠ 0 := by
      intro h
      rw [h] at hz1n
      simp at hz1n
    refine ⟨z1⁻¹, ?_, ?_⟩
    · rw [norm_inv, hz1n, inv_one]
    · rw [hz1eq, show preparedAAState A (source hM j) = A *ᵥ Qatlib.Foundations.PureStateMath.Ket (source hM j) from rfl,
        smul_smul, inv_mul_cancel₀ hz1ne, one_smul, h9]
      exact herr

end Qatlib.Concepts.HhlAlgorithms.Postselection
