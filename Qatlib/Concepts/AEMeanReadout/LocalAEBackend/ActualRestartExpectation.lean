/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.SearchStopping
import Qatlib.Concepts.LchsSimulation.StaticLchs.BitSampledPreparedSearch
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Search
import Qatlib.Concepts.FairRandomBits.GeometricRetry

/-!
# Expected costs of Born-distributed restart search

This module connects measured amplitude amplification trials to a geometric stopping law and an
explicit record of rounds, iterations, and paid costs. It proves exact expectations for positive
success probability and derives small-amplitude limits for the selected restart depth, within
the amplitude amplification setting of [BrassardEtAl2002].

## Main statements

* `born_restart`: establishes the measured restart specification and its cost identities.
* `prepared_family_limits`: transfers the scaled expectation limits to families of prepared
  states.
* `frontier1`: collects the restart specification, asymptotic costs, and optimal-angle bounds.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.StoppingCore.BranchCostCore.GeneralExecution

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Qatlib.Concepts.FairRandomBits.GeometricRetry
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend.ActualRestartExpectation
open Qatlib
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open Qatlib
open scoped Classical ENNReal BigOperators Topology
set_option warningAsError false

/-- The Boolean success law obtained by measuring a prepared amplitude amplification trial at
depth `j` and testing membership in `S`. -/
noncomputable def trialCoin {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (j : ℕ) : PMF Bool :=
  (preparedAATrial A hA j₀ S (⟨j, Nat.lt_succ_self j⟩ : Fin (j+1))).map
    (fun x => decide (x.1.1 ∈ S))

/-- Mapping a probability mass function to the indicator of `E` assigns to `true` exactly the
event mass of `E`. -/
theorem map_true {α : Type} (p : PMF α) (E : α → Prop) [DecidablePred E] :
    (p.map (fun x => decide (E x))) true = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p E := by
  rw [PMF.map_apply]
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
  apply tsum_congr
  intro a
  by_cases ha : E a <;> simp [ha]

/-- The success mass of `trialCoin` is the Born probability of `S` after the depth-`j` prepared
amplification circuit. -/
theorem trialCoin_true {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (j : ℕ) :
    trialCoin A hA j₀ S j true =
      ENNReal.ofReal (MeasureProb (Run (preparedMark S) (preparedAACircuit A j₀ j) (Qatlib.Foundations.PureStateMath.Ket j₀)) S) := by
  rw [trialCoin, map_true]
  exact (prepared_aa_trial_actual_metadata A j₀ S hA (⟨j, Nat.lt_succ_self j⟩ : Fin (j+1))).2.2

/-- If the initial marked probability is `sin² θ` with `0 < θ < π/2`, the depth-`j` success mass
is `sin² ((2*j+1)*θ)`. -/
theorem trialCoin_angle {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (j : ℕ) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi/2)
    (hprob : MeasureProb (preparedAAState A j₀) S = (Real.sin θ)^2) :
    trialCoin A hA j₀ S j true = ENNReal.ofReal ((Real.sin ((2*(j:ℝ)+1)*θ))^2) := by
  rw [trialCoin_true, prepared_aa_born_success A j₀ S θ j hA hθ0 hθ1 hprob]

/-- Two maps agreeing on the support of a probability mass function have equal pushforwards. -/
theorem map_congr_support {α β : Type} (p : PMF α) (f g : α → β)
    (h : ∀ x∈p.support,f x=g x) : p.map f=p.map g := by
  ext b
  rw [PMF.map_apply,PMF.map_apply]
  apply tsum_congr
  intro x
  by_cases hx : p x=0
  · simp [hx]
  · rw [h x ((PMF.mem_support_iff p x).mpr hx)]

/-- The measured retry transition that halts on a marked outcome and charges `step` per
amplification iteration plus initialization and verification costs. -/
noncomputable def bornRetryNext {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (j step init verify : ℕ) : Unit → PMF ((Bool ⊕ Unit) × ℕ) := fun _ =>
  (preparedAATrial A hA j₀ S (⟨j,Nat.lt_succ_self j⟩ : Fin (j+1))).map fun x =>
    (if x.1.1∈S then .inl true else .inr (),step*x.2+init+verify)

/-- The measured retry transition equals the Boolean branch retry transition with success law
`trialCoin` and constant per-trial fee `step*j+init+verify`. -/
theorem bornRetryNext_eq {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (j step init verify : ℕ) : bornRetryNext A hA j₀ S j step init verify=
      branchRetryNext (trialCoin A hA j₀ S j) (step*j+init+verify) (step*j+init+verify) := by
  funext u
  unfold bornRetryNext branchRetryNext trialCoin
  rw [PMF.map_comp]
  apply map_congr_support
  intro x hx
  have h := ((prepared_aa_trial_actual_metadata A j₀ S hA
    (⟨j,Nat.lt_succ_self j⟩ : Fin (j+1))).2.1 x hx).1
  by_cases hm : x.1.1∈S <;> simp [hm,h]

/-- The two masses of a Boolean probability mass function sum to one. -/
theorem coin_sum (coin : PMF Bool) : coin false + coin true = 1 := by
  simpa only [tsum_bool] using! coin.tsum_coe

/-- The complement of the false mass of a Boolean law is its true mass. -/
theorem one_sub_false (coin : PMF Bool) : 1 - coin false = coin true := by
  exact (ENNReal.eq_sub_of_add_eq (coin.apply_ne_top false)
    (by simpa only [add_comm] using! coin_sum coin)).symm

/-- The geometric law for the number of failures before the first success, with mass `coin false
^ n * coin true`. -/
noncomputable def stopPMF (coin : PMF Bool) (hp : 0 < coin true) : PMF ℕ := by
  refine ⟨fun n => (coin false)^n * coin true, ?_⟩
  have ht : (∑' n : ℕ, (coin false)^n * coin true) = 1 := by
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, one_sub_false,
      ENNReal.inv_mul_cancel hp.ne' (coin.apply_ne_top true)]
  rw [← ht]
  exact ENNReal.summable.hasSum

/-- The geometric mass at `n` equals the mass of first halting successfully at round `n+1` in
the unit-cost retry process. -/
theorem stopPMF_actual (coin : PMF Bool) (hp : 0 < coin true) (n : ℕ) :
    stopPMF coin hp n = branchHaltJoint (branchRetryNext coin 1 1) (.inr ()) true (n+1) := by
  simpa only [Nat.mul_one] using!
    (branch_cost_geometric_retry_exact_receipt coin 1 1 (by omega) (by omega) n).symm

/-- The expected number of trials under the geometric stopping law is the reciprocal of the
success probability. -/
theorem stopPMF_mean (coin : PMF Bool) (hp : 0 < coin true) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (stopPMF coin hp) (fun n => (n+1 : ℝ≥0∞)) =
      1 / coin true := by
  have hpaid := branch_cost_geometric_retry_expected_paid_cost coin 1 1 (by omega) (by omega) hp
  have hpstep := branchRetry_positive coin 1 1 (by omega) (by omega)
  have he := (general_unbounded_actual_expected_time (BranchClock Unit Bool) Bool
    (branchClockNext (branchRetryNext coin 1 1)) (branchClockEmbed (.inr ()))).1
  simp_rw [branchClock_bridge _ hpstep] at he
  rw [hpaid.1, mul_zero, add_zero, tsum_bool] at he
  have hf (k : ℕ) : branchHaltJoint (branchRetryNext coin 1 1) (.inr ()) false k = 0 :=
    branchRetry_false coin 1 1 k k
  simp only [hf, mul_zero, tsum_zero, zero_add] at he
  have hreceipt := branchRetry_tsum_receipts coin 1 1 (by omega) (by omega)
    (fun k => (k : ℝ≥0∞))
  have heq : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (stopPMF coin hp) (fun n => (n+1 : ℝ≥0∞)) =
      ∑' k : ℕ, (k : ℝ≥0∞) * branchHaltJoint (branchRetryNext coin 1 1) (.inr ()) true k := by
    rw [hreceipt]
    unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation stopPMF
    apply tsum_congr
    intro n
    change ((coin false)^n*coin true)*((n:ℝ≥0∞)+1) =
      (((n*1+1 : ℕ):ℝ≥0∞))*(coin false)^n*coin true
    simp only [Nat.mul_one, Nat.cast_add, Nat.cast_one]
    ring
  rw [heq, ← he, hpaid.2, Nat.cast_one, one_mul]
  rw [← ENNReal.div_self hp.ne' (coin.apply_ne_top true), ← ENNReal.add_div, add_comm (coin true),
      coin_sum]
  rw [ENNReal.div_self hp.ne' (coin.apply_ne_top true)]

/-- A fixed fee `c` per geometric trial has expected total cost `c / coin true`. -/
theorem stopPMF_cost (coin : PMF Bool) (hp : 0 < coin true) (c : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (stopPMF coin hp) (fun n => (c : ℝ≥0∞) * (n+1)) =
      (c : ℝ≥0∞) / coin true := by
  rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_const_mul, stopPMF_mean,
      one_div, div_eq_mul_inv]

/-- The joint law of trial count, total amplification iterations, and total paid fee for a
geometric restart process. -/
noncomputable def records (coin : PMF Bool) (hp : 0 < coin true)
    (j step init verify : ℕ) : PMF (ℕ × ℕ × ℕ) :=
  (stopPMF coin hp).map (fun n =>
    (n+1, j*(n+1), (step*j+init+verify)*(n+1)))

/-- The expected iteration and fee components of `records` are `j / coin true` and
`(step*j+init+verify) / coin true`, respectively. -/
theorem records_expectations (coin : PMF Bool) (hp : 0 < coin true)
    (j step init verify : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (records coin hp j step init verify) (fun r => (r.2.1 : ℝ≥0∞)) =
      (j : ℝ≥0∞)/coin true ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (records coin hp j step init verify) (fun r => (r.2.2 : ℝ≥0∞)) =
      ((step*j+init+verify : ℕ) : ℝ≥0∞)/coin true := by
  constructor
  · unfold records
    rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using! stopPMF_cost coin hp j
  · unfold records
    rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using!
      stopPMF_cost coin hp (step*j+init+verify)

/-- If the success mass is zero, the retry process has nontermination mass one. -/
theorem zero_success_never (coin : PMF Bool) (hp : coin true = 0) :
    generalNeverMass (branchClockNext (branchRetryNext coin 1 1)) (branchClockEmbed (.inr ())) = 1 := by
  have ht := branchRetry_tsum_receipts coin 1 1 (by omega) (by omega) (fun _ => 1)
  simp only [one_mul, hp, mul_zero, tsum_zero] at ht
  have hf (k : ℕ) : branchHaltJoint (branchRetryNext coin 1 1) (.inr ()) false k = 0 :=
    branchRetry_false coin 1 1 k k
  have hn := (branch_cost_output_pending_never_conservation Unit Bool
    (branchRetryNext coin 1 1) (branchRetry_positive coin 1 1 (by omega) (by omega)) (.inr ())).1
  rw [tsum_bool] at hn
  simpa only [hf, tsum_zero, ht, zero_add] using! hn

/-- The extended nonnegative expected unbounded running time of the unit-cost Boolean retry
process. -/
noncomputable def meanRounds (coin : PMF Bool) : ℝ≥0∞ :=
  generalUnboundedTime (branchClockNext (branchRetryNext coin 1 1)) (branchClockEmbed (.inr ()))

/-- The constant fee `c` multiplied by the extended expected number of retry rounds. -/
noncomputable def meanFee (coin : PMF Bool) (c : ℕ) : ℝ≥0∞ := (c : ℝ≥0∞)*meanRounds coin

/-- Zero success probability gives infinite expected retry rounds. -/
theorem zero_success_infinite_rounds (coin : PMF Bool) (hp : coin true=0) : meanRounds coin=⊤ := by
  have h := (general_unbounded_actual_expected_time (BranchClock Unit Bool) Bool
    (branchClockNext (branchRetryNext coin 1 1)) (branchClockEmbed (.inr ()))).1
  rw [zero_success_never coin hp,mul_one,add_top] at h
  exact h

/-- Positive success probability gives expected retry rounds equal to its reciprocal. -/
theorem meanRounds_eq (coin : PMF Bool) (hp : 0 < coin true) : meanRounds coin=1/coin true := by
  have h := (branch_cost_geometric_retry_expected_paid_cost coin 1 1 (by omega) (by omega) hp).2
  simp only [Nat.cast_one] at h
  change meanRounds coin=1+(1 : ℝ≥0∞)*coin false/coin true at h
  rw [h,one_mul]
  calc
    _ = coin true/coin true+coin false/coin true := by rw [ENNReal.div_self hp.ne' (coin.apply_ne_top true)]
    _ = (coin true+coin false)/coin true := by rw [ENNReal.add_div]
    _ = 1/coin true := by rw [add_comm (coin true),coin_sum]

/-- For positive success probability, the expected fee is `c / coin true`. -/
theorem meanFee_eq (coin : PMF Bool) (hp : 0 < coin true) (c : ℕ) :
    meanFee coin c=(c : ℝ≥0∞)/coin true := by
  rw [meanFee,meanRounds_eq coin hp,one_div,div_eq_mul_inv]

/-- The iteration and fee expectations of the joint record law agree with their corresponding
`meanFee` values. -/
theorem records_meanFee (coin : PMF Bool) (hp : 0 < coin true) (j step init verify : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (records coin hp j step init verify) (fun r => (r.2.1 : ℝ≥0∞))=meanFee coin j ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (records coin hp j step init verify) (fun r => (r.2.2 : ℝ≥0∞))=
      meanFee coin (step*j+init+verify) := by
  rw [meanFee_eq coin hp j,meanFee_eq coin hp (step*j+init+verify)]
  exact records_expectations coin hp j step init verify

/-- The mass of the record for `n+1` trials equals the successful first-halting mass at that
round. -/
theorem records_actual_mass (coin : PMF Bool) (hp : 0 < coin true) (j step init verify n : ℕ) :
    records coin hp j step init verify (n+1,j*(n+1),(step*j+init+verify)*(n+1))=
      branchHaltJoint (branchRetryNext coin 1 1) (.inr ()) true (n+1) := by
  rw [records,PMF.map_apply,tsum_eq_single n]
  · simpa only [if_pos rfl] using! stopPMF_actual coin hp n
  · intro k hk
    have hne : (n+1,j*(n+1),(step*j+init+verify)*(n+1)) ≠
        (k+1,j*(k+1),(step*j+init+verify)*(k+1)) := by
      intro he
      have he' := congrArg Prod.fst he
      omega
    simp only [if_neg hne]

/-- With positive success mass and positive per-trial fee, the measured paid retry process
terminates with probability one and its expected time equals `meanFee`. -/
theorem born_retry_paid {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (j step init verify : ℕ) (hp : 0 < trialCoin A hA j₀ S j true)
    (hc : 0 < step*j+init+verify) :
    generalNeverMass (branchClockNext (bornRetryNext A hA j₀ S j step init verify)) (branchClockEmbed (.inr ()))=0 ∧
    generalUnboundedTime (branchClockNext (bornRetryNext A hA j₀ S j step init verify)) (branchClockEmbed (.inr ()))=
      meanFee (trialCoin A hA j₀ S j) (step*j+init+verify) := by
  rw [bornRetryNext_eq]
  let coin := trialCoin A hA j₀ S j
  let c := step*j+init+verify
  have h := branch_cost_geometric_retry_expected_paid_cost coin c c hc hc hp
  have hu : meanRounds coin=1+coin false/coin true := by
    simpa only [Nat.cast_one,one_mul] using!
      (branch_cost_geometric_retry_expected_paid_cost coin 1 1 (by omega) (by omega) hp).2
  refine ⟨h.1,h.2.trans ?_⟩
  calc
    _ = (c : ℝ≥0∞)*(1+coin false/coin true) := by simp only [div_eq_mul_inv]; ring
    _ = _ := by rw [← hu]; rfl

/-- The success law of the two-dimensional rotation example at angle `θ` and amplification depth
`j`. -/
noncomputable def angleCoin (θ : ℝ) (j : ℕ) : PMF Bool :=
  trialCoin (Qatlib.Concepts.AEMeanReadout.LocalAEBackend.smallRotation θ) (Qatlib.Concepts.AEMeanReadout.LocalAEBackend.smallRotation_unitary θ) 0 {1} j

/-- For `0 < θ < π/2`, the true mass of `angleCoin` equals the extended nonnegative value of
`restartSuccessMass θ j`. -/
theorem angleCoin_true (θ : ℝ) (j : ℕ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi/2) :
    angleCoin θ j true=ENNReal.ofReal (restartSuccessMass θ j) :=
  trialCoin_angle _ _ _ _ j θ hθ0 hθ1 (Qatlib.Concepts.AEMeanReadout.LocalAEBackend.smallRotation_success θ)

/-- The real value of the extended expected fee for the rotation example. -/
noncomputable def expectedFee (θ : ℝ) (j c : ℕ) : ℝ := (meanFee (angleCoin θ j) c).toReal

/-- For an interior angle and positive restart success mass, the real expected fee is `c /
restartSuccessMass θ j`. -/
theorem expectedFee_eq (θ : ℝ) (j c : ℕ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi/2)
    (hp : 0 < restartSuccessMass θ j) : expectedFee θ j c=(c : ℝ)/restartSuccessMass θ j := by
  have hcoin : 0 < angleCoin θ j true := by
    rw [angleCoin_true θ j hθ0 hθ1]; exact ENNReal.ofReal_pos.mpr hp
  rw [expectedFee,meanFee_eq _ hcoin,angleCoin_true θ j hθ0 hθ1,ENNReal.toReal_div,
    ENNReal.toReal_natCast,ENNReal.toReal_ofReal hp.le]

/-- For positive restart success mass, the expected iteration fee equals the restart profile at
integer depth `j`. -/
theorem expected_iterations_profile (θ : ℝ) (j : ℕ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi/2)
    (hp : 0 < restartSuccessMass θ j) : expectedFee θ j j=restartProfile θ (j : ℝ) := by
  exact expectedFee_eq θ j j hθ0 hθ1 hp

/-- A prepared trial with marked probability `sin² θ` has the same real expected restart fee as
the rotation example when its depth has positive success mass. -/
theorem trial_meanFee_eq {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (θ : ℝ) (j c : ℕ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi/2)
    (hprob : MeasureProb (preparedAAState A j₀) S=(Real.sin θ)^2)
    (hp : 0 < restartSuccessMass θ j) :
    (meanFee (trialCoin A hA j₀ S j) c).toReal=expectedFee θ j c := by
  have he : trialCoin A hA j₀ S j true=ENNReal.ofReal (restartSuccessMass θ j) :=
    trialCoin_angle A hA j₀ S j θ hθ0 hθ1 hprob
  have hc : 0 < trialCoin A hA j₀ S j true := by rw [he]; exact ENNReal.ofReal_pos.mpr hp
  rw [expectedFee_eq θ j c hθ0 hθ1 hp,meanFee_eq _ hc,he,ENNReal.toReal_div,
    ENNReal.toReal_natCast,ENNReal.toReal_ofReal hp.le]

/-- The specification relating a measured restart law to exact expected iterations and fees,
first-halting masses, circuit counts, and paid unbounded execution time. -/
def BornRestartSpec {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (θ : ℝ) (j step init verify : ℕ) : Prop :=
  let coin := trialCoin A hA j₀ S j
  ∃ hp : 0 < coin true,
    (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (records coin hp j step init verify) (fun r => (r.2.1 : ℝ≥0∞))).toReal=
      (j : ℝ)/restartSuccessMass θ j ∧
    (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (records coin hp j step init verify) (fun r => (r.2.2 : ℝ≥0∞))).toReal=
      ((step*j+init+verify : ℕ) : ℝ)/restartSuccessMass θ j ∧
    (∀ n,records coin hp j step init verify (n+1,j*(n+1),(step*j+init+verify)*(n+1))=
      branchHaltJoint (branchRetryNext coin 1 1) (.inr ()) true (n+1)) ∧
    generalNeverMass (branchClockNext (branchRetryNext coin 1 1)) (branchClockEmbed (.inr ()))=0 ∧
    QueryCount (preparedAACircuit A j₀ j)=j ∧ GateCount (preparedAACircuit A j₀ j)=3*j+1 ∧
    (0 < step*j+init+verify →
      generalUnboundedTime (branchClockNext (bornRetryNext A hA j₀ S j step init verify))
        (branchClockEmbed (.inr ()))=
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (records coin hp j step init verify) (fun r => (r.2.2 : ℝ≥0∞)))

/-- A prepared trial with marked probability `sin² θ` and positive depth-`j` success mass
satisfies `BornRestartSpec` for the given cost parameters. -/
theorem born_restart {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (θ : ℝ) (j step init verify : ℕ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi/2)
    (hprob : MeasureProb (preparedAAState A j₀) S=(Real.sin θ)^2)
    (hp : 0 < restartSuccessMass θ j) : BornRestartSpec A hA j₀ S θ j step init verify := by
  let coin := trialCoin A hA j₀ S j
  have he : coin true=ENNReal.ofReal (restartSuccessMass θ j) :=
    trialCoin_angle A hA j₀ S j θ hθ0 hθ1 hprob
  have hc : 0 < coin true := by rw [he]; exact ENNReal.ofReal_pos.mpr hp
  have hi := records_expectations coin hc j step init verify
  have hC := prepared_aa_actual_circuit A j₀ S j hA
  refine ⟨hc,?_,?_,records_actual_mass coin hc j step init verify,
    (branch_cost_geometric_retry_expected_paid_cost coin 1 1 (by omega) (by omega) hc).1,
    hC.2.1,hC.2.2.1,?_⟩
  · rw [hi.1,he,ENNReal.toReal_div,ENNReal.toReal_natCast,ENNReal.toReal_ofReal hp.le]
  · rw [hi.2,he,ENNReal.toReal_div,ENNReal.toReal_natCast,ENNReal.toReal_ofReal hp.le]
  · intro hprice
    exact (born_retry_paid A hA j₀ S j step init verify hc hprice).2.trans
      (records_meanFee coin hc j step init verify).2.symm

/-- The integer restart optimum selected within `restartWindowDepth θ`. -/
noncomputable def selectedDepth (θ : ℝ) : ℕ := restartIntegerOptimum θ (restartWindowDepth θ)

/-- As `θ` tends to zero from above, the success mass at the selected depth tends to `sin²
(restartOptimalAngle/2)`. -/
theorem selected_success_tendsto :
    Filter.Tendsto (fun θ : ℝ => restartSuccessMass θ (selectedDepth θ))
      (𝓝[>] 0) (𝓝 (Real.sin (restartOptimalAngle/2)^2)) := by
  have hθ : Filter.Tendsto (fun θ : ℝ => θ) (𝓝[>] 0) (𝓝 0) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  have harg := (clause36_integer_optimum_tendsto.const_mul (2 : ℝ)).add hθ
  have hconst : 2*restartScaledOptimum+0=restartOptimalAngle/2 := by rw [restartScaledOptimum]; ring
  have hfun : (fun θ : ℝ => 2*((selectedDepth θ : ℝ)*θ)+θ)=
      (fun θ : ℝ => (2*(selectedDepth θ : ℝ)+1)*θ) := by funext θ; ring
  change Filter.Tendsto (fun θ : ℝ => 2*((selectedDepth θ : ℝ)*θ)+θ)
    (𝓝[>] 0) (𝓝 (2*restartScaledOptimum+0)) at harg
  rw [hfun,hconst] at harg
  have hs := (Real.continuous_sin.tendsto (restartOptimalAngle/2)).comp harg
  simpa only [restartSuccessMass] using! hs.pow 2

/-- The limiting success mass `sin² (restartOptimalAngle/2)` is strictly positive. -/
theorem limit_success_pos : 0 < Real.sin (restartOptimalAngle/2)^2 := by
  obtain ⟨hl,hu⟩ := restartOptimalAngle_bounds
  apply sq_pos_of_pos
  apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [Real.pi_pos]

/-- For all sufficiently small positive angles, the angle is interior and the selected depth has
positive restart success mass. -/
theorem selected_valid_eventually : ∀ᶠ θ : ℝ in 𝓝[>] 0,
    0 < θ ∧ θ < Real.pi/2 ∧ 0 < restartSuccessMass θ (selectedDepth θ) := by
  have hθ : Filter.Tendsto (fun θ : ℝ => θ) (𝓝[>] 0) (𝓝 0) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  have hsmall := hθ.eventually (eventually_lt_nhds (by positivity : (0:ℝ) < Real.pi/2))
  have hp := selected_success_tendsto.eventually (eventually_gt_nhds limit_success_pos)
  filter_upwards [self_mem_nhdsWithin,hsmall,hp] with θ h0 h1 h2
  exact ⟨h0,h1,h2⟩

/-- As `θ` tends to zero from above, `θ` times the selected expected fee tends to `step *
restartScaledExpectation`. -/
theorem expected_fee_tendsto (step init verify : ℕ) :
    Filter.Tendsto (fun θ : ℝ => θ*expectedFee θ (selectedDepth θ) (step*selectedDepth θ+init+verify))
      (𝓝[>] 0) (𝓝 ((step : ℝ)*restartScaledExpectation)) := by
  have hθ : Filter.Tendsto (fun θ : ℝ => θ) (𝓝[>] 0) (𝓝 0) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  have hratio : Filter.Tendsto (fun θ : ℝ => θ/restartSuccessMass θ (selectedDepth θ))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_div] using! hθ.div selected_success_tendsto limit_success_pos.ne'
  have hbase := (clause36_expected_iterations_tendsto.const_mul (step : ℝ)).add
    (hratio.const_mul ((init : ℝ)+(verify : ℝ)))
  have heq : (fun θ : ℝ => θ*expectedFee θ (selectedDepth θ) (step*selectedDepth θ+init+verify))
      =ᶠ[𝓝[>] 0] (fun θ : ℝ => (step : ℝ)*(θ*restartProfile θ (selectedDepth θ : ℝ))+
        ((init : ℝ)+(verify : ℝ))*(θ/restartSuccessMass θ (selectedDepth θ))) := by
    filter_upwards [selected_valid_eventually] with θ h
    rw [expectedFee_eq θ (selectedDepth θ) _ h.1 h.2.1 h.2.2]
    simp only [Nat.cast_add,Nat.cast_mul]
    dsimp only [restartProfile,Qatlib.Concepts.SearchStopping.RestartLaw.restartExpectedIterations,restartSuccessMass]
    ring
  simpa only [mul_zero,add_zero,selectedDepth] using! hbase.congr' heq.symm

/-- The arcsine maps the right-hand limit at zero to the right-hand limit at zero. -/
theorem source_angle_tendsto : Filter.Tendsto Real.arcsin (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa only [Real.arcsin_zero] using!
      (Real.continuous_arcsin.tendsto 0).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact (Real.arcsin_pos).mpr hs

/-- As the source amplitude `s` tends to zero from above, `s` times the selected expected fee at
angle `arcsin s` tends to `step * restartScaledExpectation`. -/
theorem expected_fee_source_tendsto (step init verify : ℕ) :
    Filter.Tendsto (fun s : ℝ => s*expectedFee (Real.arcsin s) (selectedDepth (Real.arcsin s))
      (step*selectedDepth (Real.arcsin s)+init+verify))
      (𝓝[>] 0) (𝓝 ((step : ℝ)*restartScaledExpectation)) := by
  have hs : Filter.Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  have hratio : Filter.Tendsto (fun s : ℝ => s/restartSuccessMass (Real.arcsin s) (selectedDepth (Real.arcsin s)))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_div] using!
        hs.div (selected_success_tendsto.comp source_angle_tendsto) limit_success_pos.ne'
  have hbase := (clause36_source_expectation_asymptotic.const_mul (step : ℝ)).add
    (hratio.const_mul ((init : ℝ)+(verify : ℝ)))
  have heq : (fun s : ℝ => s*expectedFee (Real.arcsin s) (selectedDepth (Real.arcsin s))
      (step*selectedDepth (Real.arcsin s)+init+verify))
      =ᶠ[𝓝[>] 0] (fun s : ℝ => (step : ℝ)*(s*restartProfile (Real.arcsin s)
        (selectedDepth (Real.arcsin s) : ℝ))+((init : ℝ)+(verify : ℝ))*
          (s/restartSuccessMass (Real.arcsin s) (selectedDepth (Real.arcsin s)))) := by
    filter_upwards [source_angle_tendsto.eventually selected_valid_eventually] with s h
    rw [expectedFee_eq (Real.arcsin s) (selectedDepth (Real.arcsin s)) _ h.1 h.2.1 h.2.2]
    simp only [Nat.cast_add,Nat.cast_mul]
    dsimp only [restartProfile,Qatlib.Concepts.SearchStopping.RestartLaw.restartExpectedIterations,restartSuccessMass]
    ring
  simpa only [mul_zero,add_zero,selectedDepth] using! hbase.congr' heq.symm

/-- For a family with marked probability `sin² θ`, the selected real expected fee has the stated
scaled limit in both angle and source-amplitude coordinates. -/
theorem prepared_family_limits (I : ℝ → Type) [∀ θ,Fintype (I θ)] [∀ θ,DecidableEq (I θ)]
    (A : ∀ θ,Matrix (I θ) (I θ) ℂ) (hA : ∀ θ,A θ ∈ Matrix.unitaryGroup (I θ) ℂ)
    (j₀ : ∀ θ,I θ) (S : ∀ θ,Finset (I θ))
    (hprob : ∀ θ,0 < θ → θ < Real.pi/2 → MeasureProb (preparedAAState (A θ) (j₀ θ)) (S θ)=(Real.sin θ)^2)
    (step init verify : ℕ) :
    Filter.Tendsto (fun θ : ℝ => θ*(meanFee (trialCoin (A θ) (hA θ) (j₀ θ) (S θ) (selectedDepth θ))
      (step*selectedDepth θ+init+verify)).toReal) (𝓝[>] 0) (𝓝 ((step : ℝ)*restartScaledExpectation)) ∧
    Filter.Tendsto (fun s : ℝ => s*(meanFee (trialCoin (A (Real.arcsin s)) (hA (Real.arcsin s))
      (j₀ (Real.arcsin s)) (S (Real.arcsin s)) (selectedDepth (Real.arcsin s)))
      (step*selectedDepth (Real.arcsin s)+init+verify)).toReal)
      (𝓝[>] 0) (𝓝 ((step : ℝ)*restartScaledExpectation)) := by
  constructor
  · apply (expected_fee_tendsto step init verify).congr'
    filter_upwards [selected_valid_eventually] with θ h
    rw [trial_meanFee_eq (A θ) (hA θ) (j₀ θ) (S θ) θ _ _ h.1 h.2.1 (hprob θ h.1 h.2.1) h.2.2]
  · apply (expected_fee_source_tendsto step init verify).congr'
    filter_upwards [source_angle_tendsto.eventually selected_valid_eventually] with s h
    rw [trial_meanFee_eq (A (Real.arcsin s)) (hA (Real.arcsin s)) (j₀ (Real.arcsin s))
      (S (Real.arcsin s)) (Real.arcsin s) _ _ h.1 h.2.1 (hprob _ h.1 h.2.1) h.2.2]

/-- Collects the measured restart specification, both selected-cost limits, and the equation and
rational bounds for `restartOptimalAngle`. -/
theorem frontier1 (step init verify : ℕ) :
    (∀ (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ)
      (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I) (θ : ℝ) (j : ℕ),
      0 < θ → θ < Real.pi/2 → MeasureProb (preparedAAState A j₀) S=(Real.sin θ)^2 →
      0 < restartSuccessMass θ j → BornRestartSpec A hA j₀ S θ j step init verify) ∧
    Filter.Tendsto (fun θ : ℝ => θ*expectedFee θ (selectedDepth θ) (step*selectedDepth θ+init+verify))
      (𝓝[>] 0) (𝓝 ((step : ℝ)*restartScaledExpectation)) ∧
    Filter.Tendsto (fun s : ℝ => s*expectedFee (Real.arcsin s) (selectedDepth (Real.arcsin s))
      (step*selectedDepth (Real.arcsin s)+init+verify))
      (𝓝[>] 0) (𝓝 ((step : ℝ)*restartScaledExpectation)) ∧
    (Real.tan (restartOptimalAngle/2)=restartOptimalAngle ∧
      (233112 : ℝ)/100000 < restartOptimalAngle ∧ restartOptimalAngle < (233113 : ℝ)/100000) := by
  refine ⟨?_,expected_fee_tendsto step init verify,expected_fee_source_tendsto step init verify,restartOptimalAngle_spec⟩
  intro I _ _ A hA j₀ S θ j h0 h1 hprob hp
  exact born_restart A hA j₀ S θ j step init verify h0 h1 hprob hp

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend.ActualRestartExpectation
