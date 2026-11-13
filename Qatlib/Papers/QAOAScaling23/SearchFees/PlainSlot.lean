/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.SearchFees.FeeRecurrence

/-!
# Plain search trial laws and fees

The unit-window experiment samples the prepared state without amplification or finite-coin
rejection. The module identifies its exact Born masses, failure probability, and five resource
fees, including immediate success when the marked mass is one.

This development accompanies the study of QAOA-assisted minimum finding in [ShaydulinEtAl2024].

## Main statements

* `plain_failure`: With exact validation, the plain-trial failure probability is one minus the
  prepared-state marked mass in extended nonnegative reals.
* `plain_five_fees`: A plain trial has expected phase-query and bit fees zero, and expected
  validation, preparation, and macro-gate fees one.

## References

* [Shaydulin et al., 2024][ShaydulinEtAl2024]
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open scoped Classical ENNReal
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
open Qatlib.Concepts.WalkSearch.QuantumAccess
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
namespace Qatlib.Papers.QAOAScaling23.SearchFees
variable {I:Type} [Fintype I] [DecidableEq I]

/-- Running zero amplification iterations prepares exactly `preparedAAState U seed`. -/
theorem zero_run (U:Matrix I I ℂ) (seed:I) (S:Finset I) :
    Run (preparedMark S) (preparedAACircuit U seed 0) (Ket seed)=preparedAAState U seed := by
  simp [preparedAACircuit,RepeatCircuit,Run,preparedAAState]

/-- The finite-coin rejection mass for the unit window with zero sampled bits is zero. -/
theorem plain_reject_zero : coinRejectMass (Nat.clog 2 1) 1=0 := by
  norm_num [coinRejectMass]

/-- A plain sampled trial returns candidate `i` with its prepared-state Born probability. -/
theorem plain_candidate_point (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I) (i:I) :
    event (preparedAASampled U hU seed S (Nat.clog 2 1) 1 3) (fun out=>∃g,out.1=some (i,g))=
      ENNReal.ofReal (BornProb (preparedAAState U seed) i) := by
  have he (out:Option (I×ℕ)×ℕ×ℕ) :
      (∃g,out.1=some (i,g))↔∃a,out.1=some a ∧ a.1=i := by
    constructor
    · rintro ⟨g,hg⟩;exact ⟨(i,g),hg,rfl⟩
    · rintro ⟨a,ha,h⟩;exact ⟨a.2,by simpa only [← h] using ha⟩
  rw [event_congr he,preparedAASampled,finite_coin_attempt_event]
  have hc(j:Fin 1) : event (finiteCoinRun (Nat.clog 2 1) 1 3) (fun out=>out.1=Sum.inl j)=1 := by
    rw [(finite_coin_return_and_pending _ _ _ (by norm_num) (by norm_num)).2 j,plain_reject_zero]
    norm_num
  simp_rw [hc,one_mul,Qatlib.Papers.QAOAScaling23.SearchPrimitive.trial_point]
  simp only [Fin.sum_univ_one,Fin.val_zero,zero_run]

/-- The probability that a plain sampled trial produces a marked candidate equals the
prepared-state marked mass. -/
theorem plain_marked_mass (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I) :
    event (preparedAASampled U hU seed S (Nat.clog 2 1) 1 3)
      (fun out=>∃y g,out.1=some (y,g) ∧ y∈S)=ENNReal.ofReal (MeasureProb (preparedAAState U seed) S) := by
  rw [prepared_aa_sampled_success U seed S hU _ _ _ (by norm_num) (by norm_num),plain_reject_zero]
  simp only [zero_pow (by norm_num : (3:ℕ)≠0),tsub_zero,Nat.cast_one,div_one,one_mul,
    Fin.sum_univ_one,Fin.val_zero,zero_run]

/-- A plain sampled trial has zero probability of producing no candidate. -/
theorem plain_pending_zero (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I) :
    event (preparedAASampled U hU seed S (Nat.clog 2 1) 1 3) (fun out=>out.1=none)=0 := by
  rw [preparedAASampled,finite_coin_attempt_pending,(finite_coin_return_and_pending _ _ _ (by norm_num) (by norm_num)).1,
    plain_reject_zero]
  norm_num

/-- With exact validation, the plain-trial failure probability is one minus the prepared-state
marked mass in extended nonnegative reals. -/
theorem plain_failure (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I)
    (valid:I→Bool) (hvalid:∀y,valid y=true↔y∈S) :
    fail U hU seed S valid 1=1-ENNReal.ofReal (MeasureProb (preparedAAState U seed) S) := by
  have h := event_compl (preparedAASampled U hU seed S (Nat.clog 2 1) 1 3) (searchSlotFail valid)
  rw [slot_success_event_congr U hU seed S valid 1 hvalid,plain_marked_mass] at h
  exact ENNReal.eq_sub_of_add_eq ENNReal.ofReal_ne_top h

/-- A plain trial has expected phase-query and bit fees zero, and expected validation,
preparation, and macro-gate fees one. -/
theorem plain_five_fees (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I) :
    slot U hU seed S .phase 1=0 ∧ slot U hU seed S .bits 1=0 ∧
      slot U hU seed S .validation 1=1 ∧ slot U hU seed S .prepare 1=1 ∧ slot U hU seed S .gates 1=1 := by
  have h3 :=
      prepared_aa_sampled_three_ledgers U seed S hU (Nat.clog 2 1) 1 3 (by norm_num) (by norm_num)
  have hp :=
      (prepared_aa_sampled_input_access_ledger U seed S hU (Nat.clog 2 1) 1 3 (by norm_num) (by norm_num)).1
  have hbits := (finite_coin_actual_bit_cost (Nat.clog 2 1) 1 3 (by norm_num)).2
  have hv : expectation (preparedAASampled U hU seed S (Nat.clog 2 1) 1 3)
      (fun out=>((if out.1.isSome then 1 else 0:ℕ):ℝ≥0∞))=1 := by
    have he := event_compl (preparedAASampled U hU seed S (Nat.clog 2 1) 1 3) (fun out=>out.1=none)
    rw [plain_pending_zero,zero_add] at he
    rw [← he]
    apply expectation_congr
    intro out
    rcases out with ⟨a,b,c⟩
    cases a <;>simp
  simp only [plain_reject_zero,zero_pow (by norm_num : (3:ℕ)≠0),tsub_zero,Nat.sub_self,Nat.cast_zero,
    mul_zero,ENNReal.zero_div,one_mul,zero_add,Nat.cast_one] at h3 hp
  simp only [Nat.clog_one_right,Nat.cast_zero,zero_mul] at hbits
  refine ⟨h3.2.1,h3.1.trans hbits,hv,?_,?_⟩
  · change expectation (preparedAASampled U hU seed S (Nat.clog 2 1) 1 3)
      (fun out:Option (I×ℕ)×ℕ×ℕ=>((if out.1.isSome then 2*out.2.2+1 else 0:ℕ):ℝ≥0∞))=1
    refine (expectation_congr (fun out:Option (I×ℕ)×ℕ×ℕ=>?_)).trans hp
    rcases out with ⟨a,b,c⟩
    cases a <;>rfl
  · change expectation (preparedAASampled U hU seed S (Nat.clog 2 1) 1 3)
      (fun out:Option (I×ℕ)×ℕ×ℕ=>(((out.1.map fun y=>y.2).getD 0:ℕ):ℝ≥0∞))=1
    refine (expectation_congr (fun out:Option (I×ℕ)×ℕ×ℕ=>?_)).trans h3.2.2
    rcases out with ⟨a,b,c⟩
    cases a <;>rfl

/-- With exact validation and marked mass one, a plain trial has failure probability zero. -/
theorem plain_Q_one (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I)
    (valid:I→Bool) (hvalid:∀y,valid y=true↔y∈S) (hQ:MeasureProb (preparedAAState U seed) S=1) :
    fail U hU seed S valid 1=0 := by rw [plain_failure U hU seed S valid hvalid,hQ];simp
end Qatlib.Papers.QAOAScaling23.SearchFees
