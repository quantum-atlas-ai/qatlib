/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedInstrument.ClockBridge.MixedInstrumentClock

/-!
# Nondisturbing retry instruments and execution costs

This module constructs `nondisturbingRetryInstrument`, whose success branch applies a unitary
and whose failure branch preserves the conditional state. `mixedRetryEvent_exact` gives its
finite geometric cost distribution, with separate results for success probabilities zero and one
and for sequential unitary outputs. Quantum instruments provide the measurement framework
described in [Watrous2018].

## Main statements

* `nondisturbingRetryInstrument`: The Boolean instrument with success branch `p` times unitary
  conjugation by `U` and failure branch `1 - p` times the identity, for `0 ≤ p ≤ 1`.
* `mixedRetryEvent_exact`: With positive success and failure costs, the halting mass after `n`
  steps is the sum of geometric weights `p * (1 - p) ^ h` at costs `good + h * bad` for `h < n`.
* `mixedRetry_zero_never`: At zero success probability and positive branch costs, the never
  halting mass is one and the unbounded execution time is infinite.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.StoppingCore.BranchCostCore.GeneralExecution
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution

set_option autoImplicit false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.MixedInstrument.ClockBridge

namespace Qatlib.Concepts.MixedInstrument.RetryConsumers
open Matrix
open scoped ComplexOrder Classical BigOperators ENNReal

/-- For strictly positive branch prices, the joint halting mass at cost `k` equals the mass at
the same output and clock value after `k` clock steps. -/
theorem mixed_instrument_same_path_cost_cutoff :
    ∀ (C L O : Type) [Fintype L] (D : ℕ)
      (I : C → Instrument L D D) (dest : C → L → O ⊕ C) (price : C → L → ℕ),
      (∀ c l, 0 < price c l) → ∀ (s : C × ClockDensity D)
      (o : O × ClockDensity D) (k : ℕ),
      branchHaltJoint (mixedNext I dest price) (.inr s) o k =
        (runFor (branchClockNext (mixedNext I dest price)) k
          (branchClockEmbed (.inr s))) (.inl o,k) := by
  intro C L O _ D I dest price hp s o k
  exact (branchClock_bridge (mixedNext I dest price)
    (mixedNext_positive I dest price hp) (.inr s) o k).symm

/-- Multiplying a completely positive complex linear map by a nonnegative real scalar preserves
complete positivity. -/
private theorem mixed_cp_scale {D : ℕ} (T : Operator D →ₗ[ℂ] Operator D)
    (hT : CompletelyPositive T) (a : ℝ) (ha : 0 ≤ a) :
    CompletelyPositive ((a : ℂ) • T) := by
  intro r A hA
  have he : ChannelAmplification ((a : ℂ) • T) r A =
      (a : ℂ) • ChannelAmplification T r A := by
    ext x y
    simp [ChannelAmplification]
  rw [he]
  exact (hT r A hA).smul (RCLike.nonneg_iff.mpr ⟨ha, rfl⟩)

/-- The Boolean instrument with success branch `p` times unitary conjugation by `U` and failure
branch `1 - p` times the identity, for `0 ≤ p ≤ 1`. -/
noncomputable def nondisturbingRetryInstrument {D : ℕ} (U : Operator D)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    Instrument Bool D D :=
  Instrument.ofBranches
    (fun b => if b then (p : ℂ) • conjBranch U else ((1-p : ℝ) : ℂ) • LinearMap.id)
    (by
      intro b
      cases b
      · exact mixed_cp_scale LinearMap.id (QuantumChannel.id D).completelyPositive (1-p)
          (by linarith)
      · exact mixed_cp_scale (conjBranch U) (completelyPositive_conjBranch U) p hp)
    (by
      intro X
      simp only [Fintype.sum_bool, Bool.false_eq_true, if_false, if_true,
        LinearMap.smul_apply, LinearMap.id_apply, Matrix.trace_add, Matrix.trace_smul,
        trace_conjBranch_unitary U hU, smul_eq_mul]
      push_cast
      ring)

/-- The success and failure branches of the retry instrument are respectively `p` times unitary
conjugation and `1 - p` times the input operator. -/
theorem nondisturbingRetryInstrument_branch {D : ℕ} (U : Operator D)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (X : Operator D) :
    (nondisturbingRetryInstrument U hU p hp hp1).branch true X = (p : ℂ) • (U*X*Uᴴ) ∧
    (nondisturbingRetryInstrument U hU p hp hp1).branch false X = ((1-p : ℝ) : ℂ) • X := by
  constructor <;> rfl

/-- On a density input, the retry instrument assigns probabilities `p` and `1 - p` to success
and failure. -/
theorem nondisturbingRetryInstrument_prob {D : ℕ} (U : Operator D)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (ρ : ClockDensity D) (b : Bool) :
    instrumentProb (nondisturbingRetryInstrument U hU p hp hp1) ρ.val b =
      if b then p else 1-p := by
  have htr : Matrix.trace (U * ρ.val * Uᴴ) = 1 :=
    (trace_conjBranch_unitary U hU ρ.val).trans ρ.property.2
  cases b <;> simp [htr, instrumentProb, nondisturbingRetryInstrument, Instrument.ofBranches,
    Matrix.trace_smul, ρ.property.2]

/-- Conditioning on failure in the retry instrument leaves the density state unchanged. -/
theorem nondisturbingRetryInstrument_failure_state {D : ℕ} (U : Operator D)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (ρ : ClockDensity D) :
    clockConditional (nondisturbingRetryInstrument U hU p hp hp1) ρ false = ρ := by
  apply Subtype.ext
  unfold clockConditional
  split_ifs with h
  · (try dsimp only)
    rw [Instrument.conditionalState, nondisturbingRetryInstrument_prob]
    change (((1-p : ℝ) : ℂ)⁻¹) • (((1-p : ℝ) : ℂ) • ρ.val) = ρ.val
    rw [smul_smul, inv_mul_cancel₀, one_smul]
    have hpq : 0 < 1-p := by simpa only [nondisturbingRetryInstrument_prob, Bool.false_eq_true,
      if_false] using h
    exact_mod_cast ne_of_gt hpq
  · rfl

/-- For positive success probability, the conditional success state is the unitary conjugate of
the input density state. -/
theorem nondisturbingRetryInstrument_success_state {D : ℕ} (U : Operator D)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (ρ : ClockDensity D) :
    (clockConditional (nondisturbingRetryInstrument U hU p hp.le hp1) ρ true).val =
      U * ρ.val * Uᴴ := by
  have h : 0 < instrumentProb (nondisturbingRetryInstrument U hU p hp.le hp1) ρ.val true := by
    simpa only [nondisturbingRetryInstrument_prob, if_true] using hp
  rw [clockConditional, dif_pos h]
  (try dsimp only)
  rw [Instrument.conditionalState, nondisturbingRetryInstrument_prob]
  change (p : ℂ)⁻¹ • ((p : ℂ) • (U * ρ.val * Uᴴ)) = _
  rw [smul_smul, inv_mul_cancel₀ (by exact_mod_cast ne_of_gt hp), one_smul]

/-- The mixed execution step that halts on success, retries on failure, and charges the
respective costs `good` and `bad`. -/
noncomputable def mixedRetryNext {D : ℕ} (U : Operator D)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (good bad : ℕ) :=
  mixedNext (fun _ : Unit => nondisturbingRetryInstrument U hU p hp hp1)
    (fun _ b => if b then Sum.inl () else Sum.inr ())
    (fun _ b => if b then good else bad)

/-- The probability of having halted at total cost `k` after `n` retry steps from the density
state `ρ`. -/
noncomputable def mixedRetryEvent {D : ℕ} (U : Operator D)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (good bad n : ℕ) (ρ : ClockDensity D) (k : ℕ) : ℝ≥0∞ :=
  Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (branchCostRun (mixedRetryNext U hU p hp hp1 good bad) n (.inr ((),ρ)))
    (fun z => z.2=k ∧ ∃ ρ' : ClockDensity D, z.1=.inl ((),ρ'))

/-- The next retry event splits into a failed attempt followed by the remaining run and an
immediate success at cost `good`. -/
theorem mixedRetryEvent_succ {D : ℕ} (U : Operator D)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (good bad n : ℕ) (ρ : ClockDensity D) (k : ℕ) :
    mixedRetryEvent U hU p hp hp1 good bad (n+1) ρ k =
      ENNReal.ofReal (1-p) *
        (if bad ≤ k then mixedRetryEvent U hU p hp hp1 good bad n ρ (k-bad) else 0) +
      (if k=good then ENNReal.ofReal p else 0) := by
  classical
  unfold mixedRetryEvent mixedRetryNext
  rw [mixedHaltEvent_succ]
  simp only [Fintype.sum_bool, Bool.false_eq_true, if_false, if_true,
    nondisturbingRetryInstrument_prob, nondisturbingRetryInstrument_failure_state,
    true_and]
  rw [add_comm]
  congr 1
  by_cases h : good ≤ k
  · simp only [if_pos h]
    by_cases he : k=good
    · simp [he]
    · simp [he, Ne.symm he]
  · have he : k ≠ good := by omega
    simp [h, he]

/-- With positive success and failure costs, the halting mass after `n` steps is the sum of
geometric weights `p * (1 - p) ^ h` at costs `good + h * bad` for `h < n`. -/
theorem mixedRetryEvent_exact {D : ℕ} (U : Operator D)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (good bad : ℕ) (hg : 0 < good) (_hb : 0 < bad) (n : ℕ) (ρ : ClockDensity D) (k : ℕ) :
    mixedRetryEvent U hU p hp hp1 good bad n ρ k =
      ∑ h ∈ Finset.range n, if k=good+h*bad then
        ENNReal.ofReal p * (ENNReal.ofReal (1-p))^h else 0 := by
  classical
  induction n generalizing k with
  | zero => simp [mixedRetryEvent, branchCostRun, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event]
  | succ n ih =>
    rw [mixedRetryEvent_succ, Finset.sum_range_succ']
    simp only [Nat.zero_mul, Nat.add_zero, pow_zero, mul_one]
    congr 1
    by_cases hfit : bad ≤ k
    · rw [if_pos hfit, ih, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      have he : k-bad=good+h*bad ↔ k=good+(h+1)*bad := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      simp only [he]
      split_ifs
      · rw [pow_succ']
        ring
      · simp
    · rw [if_neg hfit, mul_zero]
      symm
      apply Finset.sum_eq_zero
      intro h _
      rw [if_neg (by rw [Nat.add_mul, Nat.one_mul]; omega)]

/-- For positive success probability and branch costs, there exists a nondisturbing retry
instrument with the stated unitary branches and exact finite geometric distribution of
halting costs. -/
theorem mixed_instrument_nondisturbing_retry_consumer :
    ∀ (D : ℕ) (U : Operator D) (p : ℝ) (good bad : ℕ),
      U ∈ Matrix.unitaryGroup (Fin D) ℂ → 0 < p → p ≤ 1 → 0 < good → 0 < bad →
      ∃ I : Instrument Bool D D,
        (∀ X : Operator D,
          I.branch true X = (p : ℂ) • (U*X*Uᴴ) ∧
          I.branch false X = ((1-p : ℝ) : ℂ) • X) ∧
        ∀ (ρ : ClockDensity D) (j k : ℕ),
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (branchCostRun
            (mixedNext (fun _ : Unit => I) (fun _ b => if b then .inl () else .inr ())
              (fun _ b => if b then good else bad)) (j+1) (.inr ((),ρ)))
            (fun z => z.2=k ∧ ∃ ρ' : ClockDensity D, z.1=.inl ((),ρ')) =
          ∑ h ∈ Finset.range (j+1), if k=good+h*bad then
            ENNReal.ofReal p * (ENNReal.ofReal (1-p))^h else 0 := by
  intro D U p good bad hU hp hp1 hg hb
  refine ⟨nondisturbingRetryInstrument U hU p hp.le hp1,
    fun X => nondisturbingRetryInstrument_branch U hU p hp.le hp1 X, ?_⟩
  intro ρ j k
  exact mixedRetryEvent_exact U hU p hp.le hp1 good bad hg hb (j+1) ρ k

/-- Every supported halted state is the unitary conjugate of the initial state, and every
supported pending state equals the initial state, when `p > 0`. -/
theorem mixedRetry_supported_state {D : ℕ} (U : Operator D)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (good bad n : ℕ) (ρ : ClockDensity D)
    (z : ((Unit × ClockDensity D) ⊕ (Unit × ClockDensity D)) × ℕ)
    (hz : branchCostRun (mixedRetryNext U hU p hp.le hp1 good bad) n (.inr ((),ρ)) z ≠ 0) :
    match z.1 with
    | .inl out => out.2.val = U * ρ.val * Uᴴ
    | .inr s => s.2 = ρ := by
  classical
  have hs := (PMF.mem_support_iff _ _).mpr hz
  clear hz
  induction n generalizing z with
  | zero =>
    have he : z = (.inr ((),ρ),0) := by
      simpa only [branchCostRun, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret,
          PMF.mem_support_pure_iff] using hs
    subst z
    rfl
  | succ n ih =>
    simp only [branchCostRun, branchCostTick,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind] at hs
    obtain ⟨r, hr, hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hs
    obtain ⟨w, hw, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
    change r ∈ (mixedNext
      (fun _ : Unit => nondisturbingRetryInstrument U hU p hp.le hp1)
      (fun _ b => if b then .inl () else .inr ())
      (fun _ b => if b then good else bad) ((),ρ)).support at hr
    obtain ⟨v, hv, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
    obtain ⟨b, hb, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hv
    cases b with
    | false =>
      simp only [Bool.false_eq_true, if_false, Sum.map_inr,
        nondisturbingRetryInstrument_failure_state] at hw ⊢
      exact ih w hw
    | true =>
      simp only [if_true, Sum.map_inl, branchCostRun_halted, PMF.mem_support_pure_iff] at hw
      subst w
      exact nondisturbingRetryInstrument_success_state U hU p hp hp1 ρ

/-- When success has probability one and both branch costs are positive, every nonempty retry
run halts with unit mass at cost `good`. -/
theorem mixedRetry_one_success {D : ℕ} (U : Operator D)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) (good bad : ℕ)
    (hg : 0 < good) (hb : 0 < bad) (ρ : ClockDensity D) (j k : ℕ) :
    mixedRetryEvent U hU 1 (by norm_num) le_rfl good bad (j+1) ρ k =
      if k=good then 1 else 0 := by
  rw [mixedRetryEvent_exact U hU 1 (by norm_num) le_rfl good bad hg hb]
  simp only [sub_self, ENNReal.ofReal_zero, ENNReal.ofReal_one]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro h _ hne
    simp [zero_pow hne]
  · simp

/-- When success has probability zero and both branch costs are positive, every halting cost
event has zero mass. -/
theorem mixedRetry_zero_success {D : ℕ} (U : Operator D)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) (good bad : ℕ)
    (hg : 0 < good) (hb : 0 < bad) (ρ : ClockDensity D) (n k : ℕ) :
    mixedRetryEvent U hU 0 le_rfl (by norm_num) good bad n ρ k = 0 := by
  rw [mixedRetryEvent_exact U hU 0 le_rfl (by norm_num) good bad hg hb]
  simp

/-- At zero success probability, `n` steps deterministically remain pending in the initial
density state with cost `n * bad`. -/
theorem mixedRetry_zero_run {D : ℕ} (U : Operator D)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) (good bad n : ℕ) (ρ : ClockDensity D) :
    branchCostRun (mixedRetryNext U hU 0 le_rfl (by norm_num) good bad) n (.inr ((),ρ)) =
      PMF.pure (.inr ((),ρ), n*bad) := by
  classical
  have hcoin : instrumentPMF (nondisturbingRetryInstrument U hU 0 le_rfl (by norm_num))
      ρ.property = PMF.pure false := by
    ext b
    cases b <;> simp [instrumentPMF_apply, nondisturbingRetryInstrument_prob, PMF.pure_apply]
  have hnext : mixedRetryNext U hU 0 le_rfl (by norm_num) good bad ((),ρ) =
      PMF.pure (.inr ((),ρ),bad) := by
    simp [mixedRetryNext, mixedNext, mixedReceipt, hcoin, PMF.pure_map,
      nondisturbingRetryInstrument_failure_state]
  induction n with
  | zero => simp [branchCostRun, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret]
  | succ n ih =>
    rw [branchCostRun, branchCostTick, hnext,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind, PMF.pure_bind, ih]
    simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge, PMF.pure_map]
    congr 1
    apply Prod.ext
    · rfl
    · rw [Nat.add_mul, Nat.one_mul]
      omega

/-- At zero success probability and positive branch costs, the never halting mass is one and the
unbounded execution time is infinite. -/
theorem mixedRetry_zero_never {D : ℕ} (U : Operator D)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) (good bad : ℕ)
    (hg : 0 < good) (hb : 0 < bad) (ρ : ClockDensity D) :
    generalNeverMass
      (branchClockNext (mixedRetryNext U hU 0 le_rfl (by norm_num) good bad))
      (branchClockEmbed (.inr ((),ρ))) = 1 ∧
    generalUnboundedTime
      (branchClockNext (mixedRetryNext U hU 0 le_rfl (by norm_num) good bad))
      (branchClockEmbed (.inr ((),ρ))) = ⊤ := by
  let next := mixedRetryNext U hU 0 le_rfl (by norm_num) good bad
  have hp : ∀ s cfg k, next s (cfg,k) ≠ 0 → 1 ≤ k :=
    mixedNext_positive _ _ _ (by intro c b; cases b <;> assumption)
  have hz : ∀ out k, branchHaltJoint next (.inr ((),ρ)) out k = 0 := by
    intro out k
    simp [branchHaltJoint, next, mixedRetry_zero_run, PMF.pure_apply]
  have hn := (branch_cost_output_pending_never_conservation _ _ next hp (.inr ((),ρ))).1
  simp only [hz, tsum_zero, zero_add] at hn
  refine ⟨hn, ?_⟩
  have he := (general_unbounded_actual_expected_time _ _
    (branchClockNext next) (branchClockEmbed (.inr ((),ρ)))).1
  rw [hn, mul_one, add_top] at he
  exact he

/-- Two certain success stages apply the combined unitary `V * U`, and each stage has unit
halting mass at its specified success cost. -/
theorem mixedRetry_sequential_unitary_output {D : ℕ} (U V : Operator D)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (ρ : ClockDensity D) (good₁ bad₁ good₂ bad₂ : ℕ)
    (hg₁ : 0 < good₁) (hb₁ : 0 < bad₁) (hg₂ : 0 < good₂) (hb₂ : 0 < bad₂) :
    let σ := clockConditional (nondisturbingRetryInstrument U hU 1 (by norm_num) le_rfl) ρ true
    let τ := clockConditional (nondisturbingRetryInstrument V hV 1 (by norm_num) le_rfl) σ true
    τ.val = (V*U) * ρ.val * (V*U)ᴴ ∧
      mixedRetryEvent U hU 1 (by norm_num) le_rfl good₁ bad₁ 1 ρ good₁ = 1 ∧
      mixedRetryEvent V hV 1 (by norm_num) le_rfl good₂ bad₂ 1 σ good₂ = 1 := by
  (try dsimp only)
  refine ⟨?_, ?_, ?_⟩
  · rw [nondisturbingRetryInstrument_success_state V hV 1 (by norm_num) le_rfl,
      nondisturbingRetryInstrument_success_state U hU 1 (by norm_num) le_rfl]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  · simpa only [if_pos rfl] using! mixedRetry_one_success U hU good₁ bad₁ hg₁ hb₁ ρ 0 good₁
  · simpa only [if_pos rfl] using! mixedRetry_one_success V hV good₂ bad₂ hg₂ hb₂
      (clockConditional (nondisturbingRetryInstrument U hU 1 (by norm_num) le_rfl) ρ true) 0 good₂

end Qatlib.Concepts.MixedInstrument.RetryConsumers
