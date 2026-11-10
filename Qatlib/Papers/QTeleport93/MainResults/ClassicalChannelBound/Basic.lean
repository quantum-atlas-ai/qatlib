/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.NoSignalCode.QuantumMessageCount
import Qatlib.Concepts.QuditTeleport.CommLowerBound.CommBoundRestrictedTele
import Qatlib.Concepts.QuditTeleport.MessagingBounds.PrearrivalMessageGuessingTele
import Qatlib.Concepts.QuditTeleport.MessagingBounds.RedundantCodingReliability
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.QuditTeleport.CommLowerBound
open Qatlib.Concepts.QuditTeleport.MessagingBounds
open Qatlib.Concepts.QuditTeleport.QdLoccModel
open Matrix
open scoped Classical BigOperators ComplexOrder

namespace Qatlib.Papers.QTeleport93.MainResults.ClassicalChannelBound

theorem c003_bell_merged_branch_no_go : CommBoundMergeNoGoBell :=
  commBoundMergeNoGoBell

theorem c003_bell_message_injective_two_bits : CommBoundMessageInjectiveBell :=
  commBoundMessageInjectiveBell

theorem c003_qudit_merged_branch_no_go : CommBoundMergeNoGoQudit :=
  commBoundMergeNoGoQudit

theorem c003_qudit_message_injective : CommBoundMessageInjectiveQudit :=
  commBoundMessageInjectiveQudit

theorem c003_restricted_lower_bound : CommBoundRestricted :=
  commBoundRestricted

theorem c003_two_bits_necessary_bell
    (κ : Type) [Fintype κ] (m : Bool × Bool → κ) (Cm : κ → Operator 2)
    (hU : ∀ a, Cm a ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hrec : ∀ ρ : Operator 2,
      (∑ o : Bool × Bool, conjBranch (Cm (m o) * teleportBranchKraus o) ρ) = ρ) :
    Function.Injective m ∧ 4 ≤ Fintype.card κ := by
  have h := commBoundMessageInjectiveBell κ m Cm hU hrec
  refine ⟨h.1, ?_⟩
  simpa using h.2

theorem c003_two_log_bits_necessary
    (n k : ℕ) [NeZero n] (m : Fin n × Fin n → Fin (2 ^ k))
    (Cm : Fin (2 ^ k) → Operator n)
    (hU : ∀ a, Cm a ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hrec : ∀ ρ : Operator n,
      (∑ w : Fin n × Fin n, conjBranch (Cm (m w) * quditBranchKraus n w) ρ) = ρ) :
    Function.Injective m ∧ n * n ≤ 2 ^ k := by
  have h := commBoundMessageInjectiveQudit n (Fin (2 ^ k)) m Cm hU hrec
  refine ⟨h.1, ?_⟩
  simpa using h.2

theorem c003_bit_length_lower_bound
    (n k : ℕ) [NeZero n] (m : Fin n × Fin n → Fin (2 ^ k))
    (Cm : Fin (2 ^ k) → Operator n)
    (hU : ∀ a, Cm a ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hrec : ∀ ρ : Operator n,
      (∑ w : Fin n × Fin n, conjBranch (Cm (m w) * quditBranchKraus n w) ρ) = ρ) :
    Nat.clog 2 (n * n) ≤ k :=
  Nat.clog_le_of_le_pow (b := 2) (x := n * n) (y := k)
    (c003_two_log_bits_necessary n k m Cm hU hrec).2

theorem c003_prearrival_guessing : PrearrivalMessageGuessing :=
  prearrivalMessageGuessing

theorem c003_redundant_coding : RedundantCodingReliability :=
  redundantCodingReliability

theorem c003_guess_succeeds_above_quarter
    (κ : Type) [Fintype κ] [DecidableEq κ] (m : Bool × Bool → κ)
    (hm : ¬ Function.Injective m) :
    ∃ guess : κ,
      (1 / 2 : ℝ) ≤ ((Finset.univ.filter (fun o => m o = guess)).card : ℝ) / 4 ∧
      (1 / 4 : ℝ) < ((Finset.univ.filter (fun o => m o = guess)).card : ℝ) / 4 :=
  prearrivalMessageGuessing κ m hm

theorem c003_quantum_code_messages
    (n : ℕ) [NeZero n] {M : Type} [Fintype M] {d : ℕ}
    (τ : (Fin n × Fin n) → M → Operator d) (σ : Operator d)
    (E : M → Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt.FinitePOVM
      (Fin n × Fin n) d)
    (hτ : ∀ x m, (τ x m).PosSemidef)
    (hsum : ∀ x, ∑ m, τ x m = σ)
    (htrace : Matrix.trace σ = 1)
    (hexact : ∀ x, ∑ m, (Matrix.trace ((E m).effect x * τ x m)).re = 1) :
    n * n ≤ Fintype.card M := by
  simpa using
    Qatlib.Concepts.QuditTeleport.NoSignalCode.quantum_assemblage_message_count
      (0, 0) τ σ E hτ hsum htrace hexact

theorem c003_quantum_code_bits
    (n k : ℕ) [NeZero n] {d : ℕ}
    (τ : (Fin n × Fin n) → Fin (2 ^ k) → Operator d) (σ : Operator d)
    (E : Fin (2 ^ k) → Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt.FinitePOVM
      (Fin n × Fin n) d)
    (hτ : ∀ x m, (τ x m).PosSemidef)
    (hsum : ∀ x, ∑ m, τ x m = σ)
    (htrace : Matrix.trace σ = 1)
    (hexact : ∀ x, ∑ m, (Matrix.trace ((E m).effect x * τ x m)).re = 1) :
    Nat.clog 2 (n * n) ≤ k := by
  apply Nat.clog_le_of_le_pow
  simpa using c003_quantum_code_messages n τ σ E hτ hsum htrace hexact

end Qatlib.Papers.QTeleport93.MainResults.ClassicalChannelBound
