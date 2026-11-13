/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetworkDefs
import Qatlib.Concepts.QuditTeleport.TeleportCore.BellTeleportationInstrument
import Qatlib.Concepts.QuditTeleport.TeleportCore.CountedQuditTeleportation

/-!
# Execution laws for finite measurement networks

`networkInstrument` and `networkBranch` give instrument and transcript semantics for finite
adaptive networks. The module proves complete positivity, trace nonincrease, preservation of
reference marginals after summing branches, and exact resource identities for teleportation and
classical transmission.

It also constructs unitary feed-forward networks and bounds one-way guessing success by the
message count or binary-tree depth. The instrument framework follows the standard
quantum-information setting of [Watrous2018], with teleportation as in
[BennettEtAl1993Teleportation].

## Main statements

* `network_laws` and `network_reference_laws`: branch and reference-system guarantees.
* `network_resource_invariants`: exact gate, measurement, pair, and bit accounting.
* `feedForwardNetwork_branch`: outcome-dependent unitary conjugation.
* `oneWay_uniform_bits_success_le`: uniform guessing success bounded by `2 ^ C / Fintype.card
  X`.
* `g6`: the conditional-unitary and reference-teleportation specification.

## References

* [Watrous, 2018][Watrous2018]
* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

open Qatlib.Foundations.PureStateMath
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Concepts.AdaptiveCP.BranchTrace

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.QuditTeleport.TeleportCore

namespace Qatlib.Concepts.MbqcFlow.FlowDecision

open Matrix
open Qatlib
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetworkDefs

/-- The conditional-unitary instrument, reference-preserving qudit teleportation formulas, and
entanglement-ledger equivalence satisfy `Clause8Claim`; see [BennettEtAl1993Teleportation]
for the teleportation setting. -/
theorem g6 : Clause8Claim := by
  refine ⟨?_, ?_, ?_⟩
  · intro O _ _ D E I U hU
    let J : Instrument O D E :=
      Instrument.ofBranches
        (fun o => (conjBranch (U o)).comp (I.branch o))
        (fun o => (completelyPositive_conjBranch (U o)).comp (I.cp o))
        (by
          intro A
          calc Matrix.trace (∑ o, ((conjBranch (U o)).comp (I.branch o)) A)
              = ∑ o, Matrix.trace (conjBranch (U o) (I.branch o A)) := by
                rw [Matrix.trace_sum]
                rfl
            _ = ∑ o, Matrix.trace (I.branch o A) :=
                Finset.sum_congr rfl fun o _ => trace_conjBranch_unitary (U o) (hU o) (I.branch o A)
            _ = Matrix.trace (∑ o, I.branch o A) := (Matrix.trace_sum _ _).symm
            _ = Matrix.trace A := I.total A)
    refine ⟨J, ?_, ?_, ?_, ?_⟩
    · intro o ρ
      rfl
    · intro ρ
      exact J.forget_apply ρ
    · intro R ρ
      exact J.referenceMarginal ρ
    · intro ρ o hρ hz
      exact (instrumentProb_eq_zero_iff J hρ o).mp hz
  · intro n _ R ρ o
    refine ⟨quditActualReferenceCore_uniform n R o ρ, ?_, ?_⟩
    · exact tensorLeft_eq_smul ((1 : ℂ) / (n : ℂ) ^ 2)
        (fun ρ' => quditCorrectedInstrument_branch n ρ' o) ρ
    · simp only [quditActualReferenceCore_uniform, ← Finset.sum_smul,
        qudit_uniform_scalar_sum, one_smul]
  · intro L
    rfl

end Qatlib.Concepts.MbqcFlow.FlowDecision

namespace Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetwork

open Matrix
open scoped ComplexOrder
open Qatlib
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetworkDefs

/-- The one-outcome instrument whose unique branch is the identity map on operators of dimension
`D`. -/
noncomputable def terminalInstrument (D : ℕ) : Instrument Unit D D :=
  Instrument.ofBranches (fun _ => LinearMap.id)
    (fun _ => (QuantumChannel.id D).completelyPositive)
    (by intro A; simp)

/-- The instrument obtained by recursively executing a finite network, using feed-forward
composition at measurement and teleportation nodes. -/
noncomputable def networkInstrument {D E : ℕ} (P : FiniteNetwork D E) :
    Instrument P.Transcript D E :=
  match P with
  | .done D => terminalInstrument D
  | .measure _ I next => I.feedForward (fun o => networkInstrument (next o))
  | .send _ next => networkInstrument next
  | .teleport (n := n) hn _ _ next =>
      letI := hn
      (quditCorrectedInstrument n).feedForward (fun o => networkInstrument (next o))

/-- The linear map for a fixed network transcript, formed by composing the selected measurement
and corrected-teleportation branches. -/
noncomputable def networkBranch {D E : ℕ} (P : FiniteNetwork D E) :
    P.Transcript → (Operator D →ₗ[ℂ] Operator E) :=
  match P with
  | .done _ => fun _ => LinearMap.id
  | .measure _ I next => fun t => (networkBranch (next t.1) t.2).comp (I.branch t.1)
  | .send _ next => networkBranch next
  | .teleport (n := n) hn _ _ next =>
      letI := hn
      fun t => (networkBranch (next t.1) t.2).comp ((quditCorrectedInstrument n).branch t.1)

/-- The branch of the recursively constructed network instrument equals the explicitly composed
transcript map. -/
theorem networkInstrument_branch {D E : ℕ} (P : FiniteNetwork D E)
    (t : P.Transcript) : (networkInstrument P).branch t = networkBranch P t := by
  induction P with
  | done D => rfl
  | measure s I next ih =>
      exact congrArg (fun T => T.comp (I.branch t.1)) (ih t.1 t.2)
  | send bits next ih => exact ih t
  | teleport hn width fits next ih =>
      exact congrArg (fun T => T.comp ((quditCorrectedInstrument _).branch t.1)) (ih t.1 t.2)

/-- The output operator and resource record for a fixed network transcript and input operator. -/
noncomputable def networkExecution {D E : ℕ} (P : FiniteNetwork D E)
    (t : P.Transcript) (ρ : Operator D) : Operator E × ExecutionResources :=
  (networkBranch P t ρ, P.resources t)

/-- Every transcript branch is completely positive and trace nonincreasing, and forgetting the
transcript sums all branch maps. -/
theorem network_laws {D E : ℕ} (P : FiniteNetwork D E) :
    (∀ t, CompletelyPositive (networkBranch P t)) ∧
    (∀ t, TraceNonIncreasing (networkBranch P t)) ∧
    (∀ ρ, (networkInstrument P).forget.map ρ = ∑ t, networkBranch P t ρ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t
    rw [← networkInstrument_branch]
    exact (networkInstrument P).cp t
  · intro t
    rw [← networkInstrument_branch]
    exact (networkInstrument P).tni t
  · intro ρ
    simp only [Instrument.forget_apply, networkInstrument_branch]

/-- With an arbitrary reference system, the sum of network branches preserves the reference
marginal. Each branch preserves positivity, does not increase trace on positive input, and
vanishes when its real trace is zero. -/
theorem network_reference_laws {D E : ℕ} (P : FiniteNetwork D E) (R : ℕ) :
    (∀ ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ,
      partialTraceFirst (∑ t, tensorLeft (networkBranch P t) ρ) = partialTraceFirst ρ) ∧
    (∀ (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ), ρ.PosSemidef →
      ∀ t, (tensorLeft (networkBranch P t) ρ).PosSemidef ∧
        (Matrix.trace (tensorLeft (networkBranch P t) ρ)).re ≤ (Matrix.trace ρ).re ∧
        ((Matrix.trace (tensorLeft (networkBranch P t) ρ)).re = 0 →
          tensorLeft (networkBranch P t) ρ = 0)) := by
  constructor
  · intro ρ
    simp only [← networkInstrument_branch]
    exact (networkInstrument P).referenceMarginal ρ
  · intro ρ hρ t
    have hp := tensorLeft_posSemidef ((network_laws P).1 t) hρ
    refine ⟨hp, ?_, ?_⟩
    · rw [← networkInstrument_branch]
      exact (networkInstrument P).tensorLeft_tni hρ t
    · intro hz
      apply (Matrix.PosSemidef.trace_eq_zero_iff hp).mp
      exact Complex.ext hz (RCLike.nonneg_iff.mp hp.trace_nonneg).2

/-- A teleportation-node branch applies the actual corrected qudit teleportation branch before
executing the selected continuation. -/
theorem teleport_node_execution {n E : ℕ} [hn : NeZero n]
    (width : ℕ) (fits : n ≤ 2 ^ width) (next : Fin n × Fin n → FiniteNetwork n E)
    (o : Fin n × Fin n) (t : (next o).Transcript) (ρ : Operator n) :
    networkBranch (.teleport hn width fits next) ⟨o, t⟩ ρ =
      networkBranch (next o) t (quditActualBranchCore n o ρ) := by
  change networkBranch (next o) t ((quditCorrectedInstrument n).branch o ρ) = _
  congr 1
  rw [quditCorrectedInstrument_branch, quditActualBranchCore_uniform]

/-- The resource record of a teleportation node adds its pair dimension, Bell-pair count,
implementation gates and measurement, and encoded-message length to those of the
continuation. -/
theorem teleport_node_resources {n E : ℕ} [hn : NeZero n]
    (width : ℕ) (fits : n ≤ 2 ^ width) (next : Fin n × Fin n → FiniteNetwork n E)
    (o : Fin n × Fin n) (t : (next o).Transcript) :
    (FiniteNetwork.teleport hn width fits next).resources ⟨o, t⟩ =
      { (next o).resources t with
        freshPairDimensions := n :: ((next o).resources t).freshPairDimensions
        bellPairsPrepared := (if n = 2 then 1 else 0) + ((next o).resources t).bellPairsPrepared
        matrixGates := 6 + ((next o).resources t).matrixGates
        macroMeasurements := 1 + ((next o).resources t).macroMeasurements
        classicalBits := 2 * width + ((next o).resources t).classicalBits } := by
  have hc := quditProgramLeaf_counts n o
  simp only [FiniteNetwork.resources, FiniteNetwork.events, eventResources, hc.2.2.1,
    hc.2.2.2.1, (quditMessage_decode n width fits o).1]

/-- The prepared teleportation frame has the resource-state amplitude exactly when the input
register matches `j`. -/
theorem teleport_prepared_pair (n : ℕ) [NeZero n] (r : QuditTriple n) (j : Fin n) :
    quditPreparedFrame n (quditRegisterEquiv n r) j =
      if r.1.1 = j then quditResource n (r.1.2, r.2) else 0 :=
  quditPreparedFrame_resource n r j

/-- Event resources count dimension-two pairs as Bell pairs, six matrix gates and one macro
measurement per fresh pair, and the total length of all transmitted words as classical bits. -/
theorem event_resource_invariants (es : List NetworkEvent) :
    (eventResources es).bellPairsPrepared = (eventResources es).freshPairDimensions.count 2 ∧
    (eventResources es).matrixGates = 6 * (eventResources es).freshPairDimensions.length ∧
    (eventResources es).macroMeasurements = (eventResources es).freshPairDimensions.length ∧
    (eventResources es).classicalBits = ((transmittedWords es).map List.length).sum := by
  induction es with
  | nil => simp [eventResources, transmittedWords]
  | cons e es ih =>
      cases e with
      | instrument s o => simpa [eventResources, transmittedWords] using ih
      | transmit bits =>
          simpa [eventResources, transmittedWords] using
            And.intro ih.1 (And.intro ih.2.1 (And.intro ih.2.2.1 (congrArg (bits.length + ·) ih.2.2.2)))
      | teleport n hn o =>
          letI := hn
          have hc := quditProgramLeaf_counts n o
          simp only [eventResources, hc.2.2.1, hc.2.2.2.1]
          simp only [List.count_cons, List.length_cons]
          simp only [transmittedWords, List.filterMap_cons] at ih ⊢
          refine ⟨?_, ?_, ?_, ih.2.2.2⟩
          · rw [ih.1]
            by_cases h : n = 2
            · subst n; simp [Nat.add_comm]
            · simp [h]
          · rw [ih.2.1]
            omega
          · rw [ih.2.2.1]
            omega

/-- The resource record of each network transcript satisfies the Bell-pair, six-gates-per-pair,
one-measurement-per-pair, and transmitted-bit accounting identities. -/
theorem network_resource_invariants {D E : ℕ} (P : FiniteNetwork D E)
    (t : P.Transcript) :
    (P.resources t).bellPairsPrepared = (P.resources t).freshPairDimensions.count 2 ∧
    (P.resources t).matrixGates = 6 * (P.resources t).freshPairDimensions.length ∧
    (P.resources t).macroMeasurements = (P.resources t).freshPairDimensions.length ∧
    (P.resources t).classicalBits = ((transmittedWords (P.events t)).map List.length).sum :=
  event_resource_invariants (P.events t)

/-- The one-outcome instrument given by conjugation with the unitary matrix `U`. -/
noncomputable def unitaryInstrument {D : ℕ} (U : Operator D)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) : Instrument (Fin 1) D D :=
  Instrument.ofBranches (fun _ => conjBranch U)
    (fun _ => completelyPositive_conjBranch U)
    (by intro A; simpa using trace_conjBranch_unitary U hU A)

/-- The finite network that measures with `I`, applies the unitary selected by the outcome, and
terminates. -/
noncomputable def feedForwardNetwork {D E s : ℕ} (I : Instrument (Fin s) D E)
    (U : Fin s → Operator E) (hU : ∀ o, U o ∈ Matrix.unitaryGroup (Fin E) ℂ) :
    FiniteNetwork D E :=
  .measure s I fun o =>
    .measure 1 (unitaryInstrument (U o) (hU o)) (fun _ => .done E)

/-- A feed-forward network branch conjugates the corresponding instrument output by its
outcome-selected unitary. -/
theorem feedForwardNetwork_branch {D E s : ℕ} (I : Instrument (Fin s) D E)
    (U : Fin s → Operator E) (hU : ∀ o, U o ∈ Matrix.unitaryGroup (Fin E) ℂ)
    (o : Fin s) (ρ : Operator D) :
    networkBranch (feedForwardNetwork I U hU) ⟨o, 0, ()⟩ ρ =
      U o * I.branch o ρ * (U o)ᴴ := rfl

/-- Forgetting a feed-forward network transcript sums the instrument branches conjugated by
their outcome-selected unitaries. -/
theorem feedForwardNetwork_forget {D E s : ℕ} (I : Instrument (Fin s) D E)
    (U : Fin s → Operator E) (hU : ∀ o, U o ∈ Matrix.unitaryGroup (Fin E) ℂ)
    (ρ : Operator D) :
    (networkInstrument (feedForwardNetwork I U hU)).forget.map ρ =
      ∑ o, U o * I.branch o ρ * (U o)ᴴ := by
  rw [(network_laws _).2.2]
  change (∑ t : (o : Fin s) × (_ : Fin 1) × Unit,
    U t.1 * I.branch t.1 ρ * (U t.1)ᴴ) = _
  simp only [Fintype.sum_sigma]
  simp

end Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetwork

namespace Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetwork

open Matrix
open Qatlib
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetworkDefs
open scoped ComplexOrder

/-- Decoding the encoded path of a binary message tree returns that path. -/
theorem messageTree_decode_encode (T : BinaryMessageTree) (t : T.Path) :
    T.decode (T.encode t) = some t := by
  induction T with
  | leaf => cases t; rfl
  | fork l r ihl ihr =>
      cases t with
      | inl p => simp [BinaryMessageTree.encode, BinaryMessageTree.decode, ihl p]
      | inr p => simp [BinaryMessageTree.encode, BinaryMessageTree.decode, ihr p]

/-- The encoded length of any message-tree path is at most the tree depth. -/
theorem messageTree_word_length (T : BinaryMessageTree) (t : T.Path) :
    (T.encode t).length ≤ T.depth := by
  induction T with
  | leaf => cases t; exact Nat.le_refl 0
  | fork l r ihl ihr =>
      cases t with
      | inl p =>
          exact Nat.succ_le_succ ((ihl p).trans (Nat.le_max_left _ _))
      | inr p =>
          exact Nat.succ_le_succ ((ihr p).trans (Nat.le_max_right _ _))

/-- A binary message tree has at most `2 ^ T.depth` paths. -/
theorem messageTree_card_le (T : BinaryMessageTree) :
    Fintype.card T.Path ≤ 2 ^ T.depth := by
  induction T with
  | leaf => exact Nat.le_refl 1
  | fork l r ihl ihr =>
      change Fintype.card (l.Path ⊕ r.Path) ≤ 2 ^ (max l.depth r.depth + 1)
      rw [Fintype.card_sum]
      have hl := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_max_left l.depth r.depth)
      have hr := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_max_right l.depth r.depth)
      calc
        _ ≤ 2 ^ max l.depth r.depth + 2 ^ max l.depth r.depth :=
          Nat.add_le_add (ihl.trans hl) (ihr.trans hr)
        _ = _ := by rw [pow_succ]; omega

/-- Summing Bob's conditional states over all messages yields his original marginal,
independently of Alice's input. -/
theorem oneWay_no_signalling {X : Type} [Fintype X] {T : BinaryMessageTree}
    {A E B F : ℕ} (P : OneWayGuessingProtocol X T A E B F)
    (σ : Matrix (Fin A × Fin B) (Fin A × Fin B) ℂ) (x : X) :
    ∑ t, P.bobState σ x t = partialTraceFirst σ := by
  have he : partialTraceFirst (∑ t, tensorLeft ((P.alice x).branch t) σ) =
      ∑ t, P.bobState σ x t := by
    ext i j
    simp only [OneWayGuessingProtocol.bobState, partialTraceFirst, Matrix.traceLeft,
      Matrix.of_apply, Matrix.sum_apply]
    exact Finset.sum_comm
  rw [← he]
  exact (P.alice x).referenceMarginal σ

/-- The probability of a fixed instrument outcome is additive over a finite sum of input
operators. -/
private theorem instrumentProb_sum_input {O K : Type} [Fintype O] [Fintype K]
    {B F : ℕ} (J : Instrument O B F) (states : K → Operator B) (o : O) :
    instrumentProb J (∑ k, states k) o = ∑ k, instrumentProb J (states k) o := by
  simp [instrumentProb, map_sum, Matrix.trace_sum, Complex.re_sum]

/-- For positive semidefinite shared input, Bob's success contribution from one message is
bounded by applying the same guessing instrument to his unconditioned marginal. -/
theorem oneWay_branch_le_blind {X : Type} [Fintype X] {T : BinaryMessageTree}
    {A E B F : ℕ} (P : OneWayGuessingProtocol X T A E B F)
    (σ : Matrix (Fin A × Fin B) (Fin A × Fin B) ℂ) (hσ : σ.PosSemidef)
    (x : X) (t : T.Path) :
    instrumentProb (P.bob t) (P.bobState σ x t) x ≤
      instrumentProb (P.bob t) (partialTraceFirst σ) x := by
  have hpos (m : T.Path) : (P.bobState σ x m).PosSemidef :=
    (tensorLeft_posSemidef ((P.alice x).cp m) hσ).traceLeft
  calc
    _ ≤ ∑ m, instrumentProb (P.bob t) (P.bobState σ x m) x :=
      Finset.single_le_sum (fun m _ => instrumentProb_nonneg (P.bob t) (hpos m) x)
        (Finset.mem_univ t)
    _ = _ := by rw [← instrumentProb_sum_input, oneWay_no_signalling]

/-- If the nonnegative prior weights are at most `p`, success on a shared density operator is at
most the number of message-tree paths times `p`. -/
theorem oneWay_success_le {X : Type} [Fintype X] {T : BinaryMessageTree}
    {A E B F : ℕ} (P : OneWayGuessingProtocol X T A E B F)
    (σ : Matrix (Fin A × Fin B) (Fin A × Fin B) ℂ) (hσ : σ.PosSemidef)
    (htrace : Matrix.trace σ = 1) (prior : X → ℝ) (p : ℝ)
    (hprior : ∀ x, 0 ≤ prior x) (hmax : ∀ x, prior x ≤ p) :
    P.success σ prior ≤ (Fintype.card T.Path : ℝ) * p := by
  have hβ : (partialTraceFirst σ).PosSemidef := hσ.traceLeft
  have hmass (t : T.Path) : ∑ x, instrumentProb (P.bob t) (partialTraceFirst σ) x = 1 := by
    rw [sum_instrumentProb, Matrix.traceLeft_trace, htrace]
    rfl
  calc
    P.success σ prior = ∑ t, ∑ x,
        prior x * instrumentProb (P.bob t) (P.bobState σ x t) x :=
      Finset.sum_comm
    _ ≤ ∑ t, ∑ x, p * instrumentProb (P.bob t) (partialTraceFirst σ) x := by
      apply Finset.sum_le_sum
      intro t _
      apply Finset.sum_le_sum
      intro x _
      exact (mul_le_mul_of_nonneg_left (oneWay_branch_le_blind P σ hσ x t) (hprior x)).trans
        (mul_le_mul_of_nonneg_right (hmax x) (instrumentProb_nonneg (P.bob t) hβ x))
    _ = (Fintype.card T.Path : ℝ) * p := by
      simp only [← Finset.mul_sum, hmass, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- If the message-tree depth is at most `C` and the nonnegative prior weights are bounded by
nonnegative `p`, guessing success is at most `2 ^ C * p`. -/
theorem oneWay_bits_success_le {X : Type} [Fintype X] {T : BinaryMessageTree}
    {A E B F : ℕ} (P : OneWayGuessingProtocol X T A E B F)
    (σ : Matrix (Fin A × Fin B) (Fin A × Fin B) ℂ) (hσ : σ.PosSemidef)
    (htrace : Matrix.trace σ = 1) (prior : X → ℝ) (p : ℝ) (hp : 0 ≤ p)
    (hprior : ∀ x, 0 ≤ prior x) (hmax : ∀ x, prior x ≤ p) (C : ℕ) (hC : T.depth ≤ C) :
    P.success σ prior ≤ (2 : ℝ) ^ C * p := by
  have hc : Fintype.card T.Path ≤ 2 ^ C :=
    (messageTree_card_le T).trans (Nat.pow_le_pow_right (by decide) hC)
  exact (oneWay_success_le P σ hσ htrace prior p hprior hmax).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hp)

end Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetwork

namespace Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetwork
open Matrix
open Qatlib
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetworkDefs
open scoped ComplexOrder

/-- The uniform prior on a nonempty finite type has total weight one. -/
theorem uniform_guessing_prior_total (X : Type) [Fintype X] [Nonempty X] :
    (∑ _x : X, (1 / (Fintype.card X : ℝ))) = 1 := by
  have hn : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [hn]

/-- With a uniform input prior and message-tree depth at most `C`, guessing success is at most
`2 ^ C / Fintype.card X`. -/
theorem oneWay_uniform_bits_success_le {X : Type} [Fintype X] [Nonempty X]
    {T : BinaryMessageTree} {A E B F : ℕ} (P : OneWayGuessingProtocol X T A E B F)
    (σ : Matrix (Fin A × Fin B) (Fin A × Fin B) ℂ) (hσ : σ.PosSemidef)
    (htrace : Matrix.trace σ = 1) (C : ℕ) (hC : T.depth ≤ C) :
    P.success σ (fun _ => 1 / (Fintype.card X : ℝ)) ≤ (2 : ℝ) ^ C / Fintype.card X := by
  have hn : 0 < (Fintype.card X : ℝ) := by exact_mod_cast Fintype.card_pos
  simpa only [div_eq_mul_inv, one_mul] using
    oneWay_bits_success_le P σ hσ htrace (fun _ => 1 / (Fintype.card X : ℝ))
      (1 / (Fintype.card X : ℝ)) (le_of_lt (one_div_pos.mpr hn))
      (fun _ => le_of_lt (one_div_pos.mpr hn)) (fun _ => le_refl _) C hC

/-- Perfect guessing with message-tree depth at most `C` requires a prior-weight upper bound `p`
of at least the reciprocal of `2 ^ C`. -/
theorem oneWay_perfect_guessing_necessary {X : Type} [Fintype X] {T : BinaryMessageTree}
    {A E B F : ℕ} (P : OneWayGuessingProtocol X T A E B F)
    (σ : Matrix (Fin A × Fin B) (Fin A × Fin B) ℂ) (hσ : σ.PosSemidef)
    (htrace : Matrix.trace σ = 1) (prior : X → ℝ) (p : ℝ) (hp : 0 ≤ p)
    (hprior : ∀ x, 0 ≤ prior x) (hmax : ∀ x, prior x ≤ p) (C : ℕ) (hC : T.depth ≤ C)
    (hperfect : P.success σ prior = 1) : ((2 : ℝ) ^ C)⁻¹ ≤ p := by
  have h := oneWay_bits_success_le P σ hσ htrace prior p hp hprior hmax C hC
  rw [hperfect] at h
  have hd : (1 : ℝ) / 2 ^ C ≤ p := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
  simpa only [one_div] using hd

end Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetwork
