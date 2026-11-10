/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetworkLOCCDefs
open Qatlib.Foundations.PureStateMath
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.AdaptiveCP.BranchTrace

open Qatlib.Concepts.QuditTeleport.TeleportCore

namespace Qatlib.Concepts.MbqcFlow.FlowDecision
namespace MeasurementNetworkLOCC

open Matrix
open Qatlib
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetworkDefs
open Qatlib
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetwork
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetworkLOCCDefs
open scoped Classical BigOperators ComplexOrder

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

theorem clause6_party_locality :
    ∀ {D E : ℕ} (P : FiniteNetwork D E) (pl : PartyPlan P) (p : Party) (t : P.Transcript)
      (a : PartyAction), a ∈ pl.localRecord p t → a.owner = p := by
  intro D E P pl p t a ha
  exact localRecord_owner pl p t a ha

theorem clause6_trace_partition :
    ∀ {D E : ℕ} (P : FiniteNetwork D E) (pl : PartyPlan P) (t : P.Transcript)
      (a : PartyAction), a ∈ pl.actions t → a ∈ pl.localRecord a.owner t := by
  intro D E P pl t a ha
  exact actions_localRecord pl t a ha

theorem clause6_exclusive_consumption :
    ∀ {D E : ℕ} (P : FiniteNetwork D E) (pl : PartyPlan P) (t : P.Transcript)
      (p q : Party), (pl.consumedSlots t p q).Nodup := by
  intro D E P pl t p q
  exact consumedSlots_nodup pl t p q

theorem clause6_supply_feasible :
    ∀ {D E : ℕ} (P : FiniteNetwork D E) (pl : PartyPlan P) (t : P.Transcript)
      (sup : EPRSupply) (p q : Party), pl.presharedUsed t p q ≤ sup.available p q →
      (pl.consumedSlots t p q).length ≤ sup.available p q := by
  intro D E P pl t sup p q h
  exact presharedUsed_le_available pl t sup p q h

theorem clause6_split_cost :
    ∀ {D E : ℕ} (P : FiniteNetwork D E) (pl : PartyPlan P) (t : P.Transcript) (d : ℕ),
      (pl.cost t d).macroGates = 6 * (pl.cost t d).macroMeasurements := by
  intro D E P pl t d
  exact cost_macro_gates pl t d

theorem clause6_input_loading_cost :
    ∀ (n : ℕ) [NeZero n] (o : Fin n × Fin n),
      (entangledInputLoading n).gates = (quditProgramLeaf n o).gates ∧
        (entangledInputLoading n).measurements = (quditProgramLeaf n o).measurements := by
  intro n _ o
  exact loading_cost_is_separate n o

theorem clause6_loaded_input :
    ∀ {n E : ℕ} [NeZero n] (U : Operator n) (width : ℕ) (fits : n ≤ 2 ^ width)
      (next : Fin n × Fin n → FiniteNetwork n E) (o : Fin n × Fin n)
      (t : (next o).Transcript) (ρ : Operator n),
      networkBranch (.teleport (inferInstance : NeZero n) width fits next) ⟨o, t⟩
          (U * ρ * Uᴴ)
        = networkBranch (next o) t (quditActualBranchCore n o (U * ρ * Uᴴ)) := by
  intro n E _ U width fits next o t ρ
  exact loadedInput_teleport_branch U width fits next o t ρ

theorem clause6_complete :
    (∀ {D E : ℕ} (P : FiniteNetwork D E) (pl : PartyPlan P) (p : Party) (t : P.Transcript)
      (a : PartyAction), a ∈ pl.localRecord p t → a.owner = p) ∧
    (∀ {D E : ℕ} (P : FiniteNetwork D E) (pl : PartyPlan P) (t : P.Transcript)
      (a : PartyAction), a ∈ pl.actions t → a ∈ pl.localRecord a.owner t) ∧
    (∀ {D E : ℕ} (P : FiniteNetwork D E) (pl : PartyPlan P) (t : P.Transcript)
      (p q : Party), (pl.consumedSlots t p q).Nodup) ∧
    (∀ {D E : ℕ} (P : FiniteNetwork D E) (pl : PartyPlan P) (t : P.Transcript) (d : ℕ),
      (pl.cost t d).macroGates = 6 * (pl.cost t d).macroMeasurements) ∧
    (∀ (n : ℕ) [NeZero n] (o : Fin n × Fin n),
      (entangledInputLoading n).gates = (quditProgramLeaf n o).gates) ∧
    (∀ {O : Type} [Fintype O] {D E : ℕ} (I : Instrument O D E) (U : O → Operator E)
        (hU : ∀ o, U o ∈ Matrix.unitaryGroup (Fin E) ℂ) (o : O) (ρ : Operator D),
        (conditionalUnitaryInstrument I U hU).branch o ρ
          = (U o) * (I.branch o ρ) * (U o)ᴴ) ∧
    (∀ {O : Type} [Fintype O] {D E : ℕ} (B : O → (Operator D →ₗ[ℂ] Operator E))
        (hTP : ∀ A, Matrix.trace (∑ o, B o A) = Matrix.trace A) (R : ℕ)
        (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ),
        partialTraceFirst (∑ o, tensorLeft (B o) ρ) = partialTraceFirst ρ) ∧
    (∀ (n : ℕ) [NeZero n] (R : ℕ) (ρ : Matrix (Fin n × Fin R) (Fin n × Fin R) ℂ)
        (o : Fin n × Fin n),
        tensorLeft ((quditCorrectedInstrument n).branch o) ρ = (1 / (n : ℂ) ^ 2) • ρ) ∧
    (∀ {D E : ℕ} (P : FiniteNetwork D E) (pl : PartyPlan P) (t : P.Transcript),
        pl.presharedCount t + pl.freshCount t = pl.teleportCount t) := by
  refine ⟨clause6_party_locality, clause6_trace_partition, clause6_exclusive_consumption,
    clause6_split_cost, ?_, ?_, ?_, ?_, ?_⟩
  · intro n _ o
    exact entangledInputLoading_gates n o
  · exact fun I U hU o ρ => conditionalUnitaryInstrument_branch I U hU o ρ
  · exact fun B hTP R ρ => referenceMarginal_of_total B hTP ρ
  · exact fun n _ R ρ o => qudit_correction_reference (n := n) (R := R) (ρ := ρ) (o := o)
  · exact fun P pl t => preshared_fresh_split_total P pl t

theorem clause7_complete_tree :
    ∀ (k : ℕ), (completeTree k).depth = k ∧
      Fintype.card (completeTree k).Path = 2 ^ k ∧
      (∀ t : (completeTree k).Path, ((completeTree k).encode t).length = k) := by
  intro k
  refine ⟨completeTree_depth k, completeTree_card k, ?_⟩
  intro t
  exact completeTree_encode_length k t

theorem oneWay_completeTree_success_le {X : Type} [Fintype X] [Nonempty X]
    {A E B F : ℕ} {C : ℕ} (P : OneWayGuessingProtocol X (completeTree C) A E B F)
    (σ : Matrix (Fin A × Fin B) (Fin A × Fin B) ℂ) (hσ : σ.PosSemidef)
    (htrace : Matrix.trace σ = 1) :
    P.success σ (fun _ => 1 / (Fintype.card X : ℝ)) ≤ (2 : ℝ) ^ C / Fintype.card X := by
  have hC : (completeTree C).depth ≤ C := by rw [completeTree_depth]
  exact oneWay_uniform_bits_success_le P σ hσ htrace C hC

theorem teleportType_letterCount (width : ℕ) :
    Fintype.card (completeTree (2 * width)).Path = (2 ^ width) ^ 2 := by
  rw [completeTree_card, ← pow_mul, Nat.mul_comm]

theorem clause7_communication_accounting :
    ∀ {D E F : ℕ} (T : BinaryMessageTree)
      (I : Instrument (Fin (Fintype.card T.Path)) D E) (next : FiniteNetwork E F)
      (o : Fin (Fintype.card T.Path)) (t' : next.Transcript),
      ((messageNetwork T I next).resources ⟨o, t'⟩).classicalBits =
        (T.encode ((Fintype.equivFin T.Path).symm o)).length
          + (next.resources t').classicalBits := by
  intro D E F T I next o t'
  exact messageNetwork_bits T I next o t'

theorem clause7_message_budget :
    ∀ {D E F : ℕ} (T : BinaryMessageTree)
      (_I : Instrument (Fin (Fintype.card T.Path)) D E) (_next : FiniteNetwork E F)
      (o : Fin (Fintype.card T.Path)),
      (T.encode ((Fintype.equivFin T.Path).symm o)).length ≤ T.depth := by
  intro D E F T I next o
  exact messageNetwork_word_le_depth T I next o

theorem clause7_redundancy_amplification :
    ∀ (r : ℕ) (w : List Bool), (redundantEncode r w).length = r * w.length := by
  intro r w
  exact redundantEncode_length r w

theorem clause7_multiround_collapse :
    ∀ {X : Type} [Fintype X] {k : ℕ} (P : MultiRoundGuess X k) (x y : X),
      (∀ i, P.alice x i = P.alice y i) →
      (List.finRange k).flatMap (P.alice x) = (List.finRange k).flatMap (P.alice y) := by
  intro X _ k P x y h
  exact MultiRoundGuess.concatenated_eq_of_same_words P x y h

theorem clause7_reindexing_bridge {O P : Type} [Fintype O] [Fintype P] {D E : ℕ}
    (I : Instrument O D E) (e : O ≃ P) :
    (∀ (p : P), (instrumentReindex I e).branch p = I.branch (e.symm p)) ∧
    (∀ (A : Operator D),
        Matrix.trace (∑ p, (instrumentReindex I e).branch p A) = Matrix.trace A) ∧
    (∀ (ρ : Operator D), (instrumentReindex I e).forget.map ρ = I.forget.map ρ) :=
  ⟨fun p => instrumentReindex_branch I e p,
   fun A => instrumentReindex_total I e A,
   fun ρ => instrumentReindex_forget I e ρ⟩

theorem clause7_real_protocol_bound {X : Type} [Fintype X] [Nonempty X]
    {T : BinaryMessageTree} {A E B F : ℕ} {s : ℕ} (P : FinGuessProtocol X T A E B F s)
    (σ : Matrix (Fin A × Fin B) (Fin A × Fin B) ℂ) (hσ : σ.PosSemidef)
    (htrace : Matrix.trace σ = 1) (C : ℕ) (hC : T.depth ≤ C) :
    P.toTree.success σ (fun _ => 1 / (Fintype.card X : ℝ)) ≤ (2 : ℝ) ^ C / Fintype.card X :=
  FinGuessProtocol.success_le P σ hσ htrace C hC

theorem clause7_general_message_bound {X : Type} [Fintype X] [Nonempty X]
    {M : Type} [Fintype M] {A E B F : ℕ} (P : MessageGuessProtocol X M A E B F)
    (σ : Matrix (Fin A × Fin B) (Fin A × Fin B) ℂ) (hσ : σ.PosSemidef)
    (htrace : Matrix.trace σ = 1) :
    P.success σ (fun _ => 1 / (Fintype.card X : ℝ))
      ≤ (Fintype.card M : ℝ) * (1 / (Fintype.card X : ℝ)) :=
  MessageGuessProtocol.uniform_success_le P σ hσ htrace

theorem clause7_post_processing_bound {X : Type} [Fintype X] [Nonempty X]
    {M : Type} [Fintype M] {T : BinaryMessageTree} {A E B F : ℕ}
    (P : MessageGuessProtocol X M A E B F) (m : M → T.Path) (bob : T.Path → Instrument X B F)
    (σ : Matrix (Fin A × Fin B) (Fin A × Fin B) ℂ) (hσ : σ.PosSemidef)
    (htrace : Matrix.trace σ = 1) (C : ℕ) (hC : T.depth ≤ C) :
    (P.coarsen m bob).success σ (fun _ => 1 / (Fintype.card X : ℝ))
      ≤ (2 : ℝ) ^ C * (1 / (Fintype.card X : ℝ)) :=
  MessageGuessProtocol.coarsen_tree_success_le P m bob σ hσ htrace C hC

theorem clause7_counterexample_boundary :
    (∀ (i : Fin 6), (counterWords i).length ≤ 2) ∧
    ¬ PrefixFree counterWords ∧
    2 ^ 2 < Fintype.card (Fin 6) :=
  ⟨counterWords_length_le, counterWords_not_prefixFree, counterWords_card_gt⟩

theorem clause7_complete :
    (∀ (k : ℕ), (completeTree k).depth = k) ∧
    (∀ (k : ℕ), Fintype.card (completeTree k).Path = 2 ^ k) ∧
    (∀ {D E F : ℕ} (T : BinaryMessageTree)
      (I : Instrument (Fin (Fintype.card T.Path)) D E) (next : FiniteNetwork E F)
      (o : Fin (Fintype.card T.Path)) (t' : next.Transcript),
      ((messageNetwork T I next).resources ⟨o, t'⟩).classicalBits =
        (T.encode ((Fintype.equivFin T.Path).symm o)).length
          + (next.resources t').classicalBits) ∧
    (∀ (r : ℕ) (w : List Bool), (redundantEncode r w).length = r * w.length) ∧
    (∀ {O P : Type} [Fintype O] [Fintype P] {D E : ℕ} (I : Instrument O D E) (e : O ≃ P)
        (p : P), (instrumentReindex I e).branch p = I.branch (e.symm p)) ∧
    (∀ {X : Type} [Fintype X] [Nonempty X] {T : BinaryMessageTree} {A E B F : ℕ} {s : ℕ}
        (P : FinGuessProtocol X T A E B F s)
        (σ : Matrix (Fin A × Fin B) (Fin A × Fin B) ℂ) (hσ : σ.PosSemidef)
        (htrace : Matrix.trace σ = 1) (C : ℕ) (hC : T.depth ≤ C),
        P.toTree.success σ (fun _ => 1 / (Fintype.card X : ℝ)) ≤ (2 : ℝ) ^ C / Fintype.card X) ∧
    (∀ {X : Type} [Fintype X] [Nonempty X] {M : Type} [Fintype M] {A E B F : ℕ}
        (P : MessageGuessProtocol X M A E B F)
        (σ : Matrix (Fin A × Fin B) (Fin A × Fin B) ℂ) (hσ : σ.PosSemidef)
        (htrace : Matrix.trace σ = 1),
        P.success σ (fun _ => 1 / (Fintype.card X : ℝ))
          ≤ (Fintype.card M : ℝ) * (1 / (Fintype.card X : ℝ))) ∧
    (∀ {X : Type} [Fintype X] [Nonempty X] {M : Type} [Fintype M]
        {T : BinaryMessageTree} {A E B F : ℕ} (P : MessageGuessProtocol X M A E B F)
        (m : M → T.Path) (bob : T.Path → Instrument X B F)
        (σ : Matrix (Fin A × Fin B) (Fin A × Fin B) ℂ) (hσ : σ.PosSemidef)
        (htrace : Matrix.trace σ = 1) (C : ℕ) (hC : T.depth ≤ C),
        (P.coarsen m bob).success σ (fun _ => 1 / (Fintype.card X : ℝ))
          ≤ (2 : ℝ) ^ C * (1 / (Fintype.card X : ℝ))) ∧
    ((∀ (i : Fin 6), (counterWords i).length ≤ 2) ∧ ¬ PrefixFree counterWords ∧
        2 ^ 2 < Fintype.card (Fin 6)) := by
  refine ⟨completeTree_depth, completeTree_card, ?_, redundantEncode_length, ?_, ?_, ?_, ?_, ?_⟩
  · intro D E F T I next o t'
    exact messageNetwork_bits T I next o t'
  · exact fun I e p => instrumentReindex_branch I e p
  · exact fun P σ hσ htrace C hC => clause7_real_protocol_bound P σ hσ htrace C hC
  · exact fun P σ hσ htrace => clause7_general_message_bound P σ hσ htrace
  · exact fun P m bob σ hσ htrace C hC => clause7_post_processing_bound P m bob σ hσ htrace C hC
  · exact clause7_counterexample_boundary

theorem clause6_general_conditional_unitary {O : Type} [Fintype O] {D E : ℕ}
    (I : Instrument O D E) (U : O → Operator E)
    (hU : ∀ o, U o ∈ Matrix.unitaryGroup (Fin E) ℂ) :
    (∀ (o : O) (ρ : Operator D),
        (conditionalUnitaryInstrument I U hU).branch o ρ = (U o) * (I.branch o ρ) * (U o)ᴴ) ∧
    (∀ (ρ : Operator D),
        (conditionalUnitaryInstrument I U hU).forget.map ρ
          = ∑ o, (U o) * (I.branch o ρ) * (U o)ᴴ) ∧
    (∀ (R : ℕ) (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ),
        partialTraceFirst (∑ o, tensorLeft ((conditionalUnitaryInstrument I U hU).branch o) ρ)
          = partialTraceFirst ρ) ∧
    (∀ (ρ : Operator D) (o : O), ρ.PosSemidef →
        instrumentProb (conditionalUnitaryInstrument I U hU) ρ o = 0 →
          (conditionalUnitaryInstrument I U hU).branch o ρ = 0) :=
  ⟨fun o ρ => conditionalUnitaryInstrument_branch I U hU o ρ,
   fun ρ => conditionalUnitaryInstrument_forget I U hU ρ,
   fun R ρ => conditionalUnitaryInstrument_reference I U hU R ρ,
   fun ρ o hρ hz => conditionalUnitaryInstrument_zero I U hU ρ o hρ hz⟩

theorem clause6_general_transport {O : Type} [Fintype O] {D E : ℕ}
    (B : O → (Operator D →ₗ[ℂ] Operator E))
    (hTP : ∀ A, Matrix.trace (∑ o, B o A) = Matrix.trace A) :
    (∀ (R : ℕ) (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ),
        partialTraceFirst (∑ o, tensorLeft (B o) ρ) = partialTraceFirst ρ) ∧
    (∀ (hCP : ∀ o, CompletelyPositive (B o)) (R : ℕ)
        (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) (hρ : ρ.PosSemidef) (o : O),
        (Matrix.trace (tensorLeft (B o) ρ)).re ≤ (Matrix.trace ρ).re) :=
  ⟨fun R ρ => referenceMarginal_of_total B hTP ρ,
   fun hCP R ρ hρ o => tensorLeft_tni_of_total B hCP hTP hρ o⟩

theorem clause6_qudit_reference {n : ℕ} [NeZero n] (R : ℕ)
    (ρ : Matrix (Fin n × Fin R) (Fin n × Fin R) ℂ) :
    (∀ (o : Fin n × Fin n),
        tensorLeft ((quditCorrectedInstrument n).branch o) ρ = (1 / (n : ℂ) ^ 2) • ρ) ∧
    ((∑ o : Fin n × Fin n, tensorLeft ((quditCorrectedInstrument n).branch o) ρ) = ρ) :=
  ⟨fun o => qudit_correction_reference (n := n) (R := R) (ρ := ρ) (o := o),
   qudit_correction_reference_total (n := n) (R := R) (ρ := ρ)⟩

theorem clause6_entanglement_accounting {D E : ℕ} (P : FiniteNetwork D E) (pl : PartyPlan P)
    (t : P.Transcript) :
    pl.presharedCount t + pl.freshCount t = pl.teleportCount t ∧
    (pl.entanglementLedger t).sharedEprUsed + (pl.entanglementLedger t).eprCreated
      = (pl.entanglementLedger t).teleportSteps ∧
    (P.resources t).freshPairDimensions
      = (P.events t).filterMap (fun e => match e with
          | .teleport n _ _ => some n
          | _ => none) :=
  ⟨preshared_fresh_split_total P pl t, entanglementLedger_law pl t,
    fresh_pair_dimensions_eq P t⟩

end MeasurementNetworkLOCC
