/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPowerSimon97.Recovery.ExpectedOracleRecoveryRestrictedSimo
import Qatlib.Papers.QPowerSimon97.Recovery.ExpectedTimeRestrictedSimo

/-!
# Verified retry conclusions for Simon's Theorem 3.2

This module packages correctness, termination, and expected-cost statements for the verified
Simon retry process into `Theorem32Conclusion` [Simon1997]. The theorem `simonTheorem32`
establishes this package under `BooleanSimonPromise`, while the remaining results expose the
trial ledger and expected sample and query bounds.

## Main statements

* `Theorem32Conclusion`: The conjunction of verified-trial soundness, almost-sure recovery,
  geometric retry tails, and expected sample, query-time, and classical-operation bounds for
  Simon's Theorem 3.2.
* `simonTheorem32`: Under `BooleanSimonPromise`, establishes the verified correctness,
  termination, and expected-cost package `Theorem32Conclusion`. This is the packaged formal
  conclusion for [Simon, Theorem 3.2][Simon1997].
* `simonTheorem32ExpectedQueries`: Under the Simon promise, charging `n + 3` queries per retry
  gives an unbounded expected charge at most `2 * (n + 3)`.

## References

* [Simon, 1997][Simon1997]
-/

set_option warningAsError false

open Qatlib.Concepts.AbelianDecoders.SimonDecoding
open Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian
open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Concepts.WalshMoment.Forrelation
open Qatlib.Concepts.PauliClifford.ExactRank
open Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.HspRecovery.Distinguisher
open Qatlib.Papers.QPowerSimon97.Recovery

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QPowerSimon97.Recovery

open Qatlib
open scoped Classical ENNReal

/-- The conjunction of verified-trial soundness, almost-sure recovery, geometric retry tails,
and expected sample, query-time, and classical-operation bounds for Simon's Theorem 3.2. -/
def Theorem32Conclusion (n : ℕ) (R : Type) [AddCommGroup R] [Fintype R] [DecidableEq R]
    (f : BooleanVec n → R) (s : Reg n) (Tf : ℕ → ℕ) : Prop :=
  (∀ t : Reg n, t ≠ s → simonVerifiedTrial f (some t) = 0) ∧
  generalNeverMass (simonVerifiedRetryKernel f) (Sum.inr ()) = 0 ∧
  (∑' K : ℕ, haltJoint (simonVerifiedRetryKernel f) (Sum.inr ()) s K) = 1 ∧
  generalUnboundedTime (simonVerifiedRetryKernel f) (Sum.inr ()) ≤ 2 ∧
  (∀ K : ℕ, generalPendingMass (simonVerifiedRetryKernel f) (Sum.inr ()) K ≤
    (1 / 2 : ℝ≥0∞) ^ K) ∧
  (∀ fuel : ℕ,
    expectedCost (weightedRunFor (simonVerifiedRetryKernel f) (fun _ => n + 1) fuel
      (Sum.inr ())) ≤ ((2 * (n + 1) : ℕ) : ℝ≥0∞)) ∧
  (∀ fuel : ℕ,
    expectedCost (weightedRunFor (simonVerifiedRetryKernel f) (fun _ => (n + 3) * Tf n) fuel
      (Sum.inr ())) ≤ ((2 * ((n + 3) * Tf n) : ℕ) : ℝ≥0∞)) ∧
  simonClassicalExpectedLimit f ≤ ((2 * simonBlockOpsBound n : ℕ) : ℝ≥0∞)

/-- A decoded run with `n + 1` samples records `n + 1` queries, `2 * (n + 1)` Hadamard charges,
and `n + 1` sample charges. -/
theorem simonTrialLedger (n : ℕ) (R : Type) [AddCommGroup R] [Fintype R]
    [DecidableEq R] (f : BooleanVec n → R) :
    (simonDecodedRun f (n + 1)).2.1 = n + 1 ∧
    (simonDecodedRun f (n + 1)).2.2.1 = 2 * (n + 1) ∧
    (simonDecodedRun f (n + 1)).2.2.2 = n + 1 := by
  have h := (simon_verified_actual_oracle_and_decoder_ledgers n R f 0).2.1
  refine ⟨?_, ?_, ?_⟩ <;> rw [h]

/-- Under the Simon promise, every fuel-bounded retry run charged `n + 1` per trial has expected
cost at most `2 * (n + 1)`. -/
theorem simonExpectedSamples (n : ℕ) (R : Type) [AddCommGroup R] [Fintype R]
    [DecidableEq R] (f : BooleanVec n → R) (s : Reg n)
    (hf : BooleanSimonPromise f (regBooleanEquiv n s)) :
    ∀ fuel : ℕ,
      expectedCost (weightedRunFor (simonVerifiedRetryKernel f) (fun _ => n + 1) fuel
        (Sum.inr ())) ≤ ((2 * (n + 1) : ℕ) : ℝ≥0∞) := by
  have htime := (simon_verified_unbounded_expected_queries_and_cutoff n R f s hf).2.1
  intro fuel
  rw [weightedRunFor_const_charge_expected_cost,
    (general_unbounded_actual_expected_time Unit (Reg n) (simonVerifiedRetryKernel f)
      (Sum.inr ())).2.2 fuel]
  calc
    ((n + 1 : ℕ) : ℝ≥0∞) *
        ∑ t ∈ Finset.range fuel,
          generalPendingMass (simonVerifiedRetryKernel f) (Sum.inr ()) t
        ≤ ((n + 1 : ℕ) : ℝ≥0∞) *
            generalUnboundedTime (simonVerifiedRetryKernel f) (Sum.inr ()) :=
      mul_le_mul_right (ENNReal.sum_le_tsum (Finset.range fuel)) _
    _ ≤ ((n + 1 : ℕ) : ℝ≥0∞) * 2 := mul_le_mul_right htime _
    _ = ((2 * (n + 1) : ℕ) : ℝ≥0∞) := by push_cast; ring

/-- Under `BooleanSimonPromise`, establishes the verified correctness, termination, and
expected-cost package `Theorem32Conclusion`. This is the packaged formal conclusion for
[Simon, Theorem 3.2][Simon1997]. -/
theorem simonTheorem32 (n : ℕ) (R : Type) [AddCommGroup R] [Fintype R] [DecidableEq R]
    (f : BooleanVec n → R) (s : Reg n) (Tf : ℕ → ℕ)
    (hf : BooleanSimonPromise f (regBooleanEquiv n s)) :
    Theorem32Conclusion n R f s Tf := by
  have hsound := simon_verified_actual_trial_success_and_soundness n R f s hf
  have hunb := simon_verified_unbounded_expected_queries_and_cutoff n R f s hf
  have htime := expectedTimeRestricted n R f s Tf hf
  exact ⟨hsound.2.1, hunb.1, hunb.2.2.1, hunb.2.1, hunb.2.2.2.2,
    simonExpectedSamples n R f s hf, htime.2.2.1, htime.2.2.2⟩

/-- Under the Simon promise, charging `n + 3` queries per retry gives an unbounded expected
charge at most `2 * (n + 3)`. -/
theorem simonTheorem32ExpectedQueries (n : ℕ) (R : Type) [AddCommGroup R]
    [Fintype R] [DecidableEq R] (f : BooleanVec n → R) (s : Reg n)
    (hf : BooleanSimonPromise f (regBooleanEquiv n s)) :
    ((n + 3 : ℕ) : ℝ≥0∞) *
        generalUnboundedTime (simonVerifiedRetryKernel f) (Sum.inr ()) ≤
      ((2 * (n + 3) : ℕ) : ℝ≥0∞) :=
  (simon_verified_unbounded_expected_queries_and_cutoff n R f s hf).2.2.2.1

end Qatlib.Papers.QPowerSimon97.Recovery
