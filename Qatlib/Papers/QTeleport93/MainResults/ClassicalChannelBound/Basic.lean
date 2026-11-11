/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.NoSignalCode.QuantumMessageCount
import Qatlib.Concepts.QuditTeleport.CommLowerBound.CommBoundRestrictedTele
import Qatlib.Concepts.QuditTeleport.MessagingBounds.PrearrivalMessageGuessingTele
import Qatlib.Concepts.QuditTeleport.MessagingBounds.RedundantCodingReliability

/-!
# Classical message bounds for teleportation

This module collects communication bounds for the Bell and qudit protocols associated with
[BennettEtAl1993Teleportation]. Exact recovery by unitary corrections forces distinct outcomes
to have distinct messages, giving four labels for a qubit and `n * n` labels for a qudit.

The results also expose the guessing and repetition arguments and a more general bound for
positive operator assemblages with a common normalized sum. `c003_quantum_code_messages` gives
the alphabet bound, while `c003_quantum_code_bits` expresses it using `Nat.clog`.

## Main statements

* `c003_restricted_lower_bound` bundles the Bell and qudit merging and injectivity bounds.
* `c003_bit_length_lower_bound` bounds fixed bit length for unitary correction protocols.
* `c003_guess_succeeds_above_quarter` gives a repeated message with guessing probability at
  least one half.
* `c003_quantum_code_messages` and `c003_quantum_code_bits` give assemblage communication
  bounds.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

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

/-- Merging two distinct Bell outcomes under a common correction fails to give half the identity
map on some operator with a finite reference. -/
theorem c003_bell_merged_branch_no_go : CommBoundMergeNoGoBell :=
  commBoundMergeNoGoBell

/-- Exact Bell teleportation with unitary message dependent corrections forces an injective
outcome encoding and at least four message labels. -/
theorem c003_bell_message_injective_two_bits : CommBoundMessageInjectiveBell :=
  commBoundMessageInjectiveBell

/-- For positive dimension, merging two distinct qudit outcomes under a common correction fails
to give `2 / n^2` times the identity on some finite reference extension. -/
theorem c003_qudit_merged_branch_no_go : CommBoundMergeNoGoQudit :=
  commBoundMergeNoGoQudit

/-- Exact qudit teleportation with unitary message dependent corrections forces an injective
outcome encoding and at least `n * n` message labels. -/
theorem c003_qudit_message_injective : CommBoundMessageInjectiveQudit :=
  commBoundMessageInjectiveQudit

/-- Collects the Bell and qudit results excluding merged branches and requiring injective
messages for exact unitary correction recovery. -/
theorem c003_restricted_lower_bound : CommBoundRestricted :=
  commBoundRestricted

/-- If unitary corrections indexed by `m` recover every qubit operator, then `m` is injective
and its finite alphabet has at least four elements. -/
theorem c003_two_bits_necessary_bell
    (κ : Type) [Fintype κ] (m : Bool × Bool → κ) (Cm : κ → Operator 2)
    (hU : ∀ a, Cm a ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hrec : ∀ ρ : Operator 2,
      (∑ o : Bool × Bool, conjBranch (Cm (m o) * teleportBranchKraus o) ρ) = ρ) :
    Function.Injective m ∧ 4 ≤ Fintype.card κ := by
  have h := commBoundMessageInjectiveBell κ m Cm hU hrec
  refine ⟨h.1, ?_⟩
  simpa using h.2

/-- Exact recovery of every qudit operator by unitary corrections indexed by `k` bit labels
forces an injective encoding and `n * n ≤ 2 ^ k`. -/
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

/-- Under exact qudit recovery by unitary corrections, a `k` bit message alphabet satisfies
`Nat.clog 2 (n * n) ≤ k`. -/
theorem c003_bit_length_lower_bound
    (n k : ℕ) [NeZero n] (m : Fin n × Fin n → Fin (2 ^ k))
    (Cm : Fin (2 ^ k) → Operator n)
    (hU : ∀ a, Cm a ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hrec : ∀ ρ : Operator n,
      (∑ w : Fin n × Fin n, conjBranch (Cm (m w) * quditBranchKraus n w) ρ) = ρ) :
    Nat.clog 2 (n * n) ≤ k :=
  Nat.clog_le_of_le_pow (b := 2) (x := n * n) (y := k)
    (c003_two_log_bits_necessary n k m Cm hU hrec).2

/-- A noninjective encoding of four uniformly distributed Bell outcomes has a message that can
be guessed with probability at least one half, exceeding one quarter. -/
theorem c003_prearrival_guessing : PrearrivalMessageGuessing :=
  prearrivalMessageGuessing

/-- If a binary statistic has different expectations under two finite distributions,
sufficiently many independent samples make both midpoint threshold error probabilities
arbitrarily small. -/
theorem c003_redundant_coding : RedundantCodingReliability :=
  redundantCodingReliability

/-- A noninjective map from the four Bell outcomes has a fiber containing at least half the
outcomes, so guessing that message succeeds with probability greater than one quarter. -/
theorem c003_guess_succeeds_above_quarter
    (κ : Type) [Fintype κ] [DecidableEq κ] (m : Bool × Bool → κ)
    (hm : ¬ Function.Injective m) :
    ∃ guess : κ,
      (1 / 2 : ℝ) ≤ ((Finset.univ.filter (fun o => m o = guess)).card : ℝ) / 4 ∧
      (1 / 4 : ℝ) < ((Finset.univ.filter (fun o => m o = guess)).card : ℝ) / 4 :=
  prearrivalMessageGuessing κ m hm

/-- Positive operator assemblages with a common trace one sum and exact message dependent POVM
decoding of `n * n` labels require at least `n * n` messages [BennettEtAl1993Teleportation]. -/
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

/-- Exact POVM decoding of `n * n` labels from positive assemblages with a common normalized sum
requires `Nat.clog 2 (n * n) ≤ k` for a `k` bit message alphabet
[BennettEtAl1993Teleportation]. -/
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
