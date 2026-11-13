/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FiniteLocc.LOCCProgram.MeasurementNetworkDefs
import Qatlib.Concepts.FiniteLocc.LOCCProgram.MeasurementNetwork

/-!
# Corrected instruments and bounded message codes

This module proves trace, positivity, and reference-marginal properties of record-conditioned
corrected instruments, and verifies injective pair-slot ledgers. The instrument and
communication setting is described in [Wilde2017].

For message codes, `PrefixFreeCode` yields a finite alphabet bound, which is applied to a
message-guessing protocol. Fixed-width teleportation codes are injective and prefix-free under
the width condition; redundant fixed-width codes preserve these properties for positive
redundancy, while `frozenRedundantWords` supplies a variable-length counterexample.

## Main statements

* `clause6_forgetting_transport`: forgetting corrected outcomes preserves the reference
  marginal.
* `clause6_shared_accounting`: the canonical ledger costs `2 * pairs + records`.
* `clause7_general_letter_count`: a prefix-free code of maximum length `C` has at most `2 ^ C`
  messages.
* `clause7_protocol_letter_count_bound`: the code bound controls uniform-prior guessing success.

## References

* [Wilde, 2017][Wilde2017]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetworkLOCC
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetworkLOCCDefs
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.FiniteLocc.LOCCProgram
open Qatlib.Concepts.FiniteLocc.LOCCProgram.MeasurementNetwork

namespace Qatlib.Concepts.FiniteLocc.LOCCProgram.MeasurementNetworkRefined

open Qatlib
open Qatlib.Concepts.FiniteLocc.LOCCProgram.LocalResourceNetworkDefs
open Matrix
open scoped BigOperators ComplexOrder

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- A complete record-conditioned Kraus family defines completely positive instrument branches
whose sum preserves trace. -/
theorem clause6_record_instrument {D s : ℕ} (K : RecordConditionedFamily D s)
    (hK : K.complete) :
    (∀ k, CompletelyPositive ((K.instrument hK).branch k)) ∧
    (∀ A : Operator D, Matrix.trace (∑ k, (K.instrument hK).branch k A) = Matrix.trace A) := by
  refine ⟨fun k => ?_, fun A => K.instrument_total hK A⟩
  simp only [RecordConditionedFamily.instrument, Instrument.ofBranches]
  exact completelyPositive_conjBranch (K.kraus k)

/-- Expands a corrected branch both as successive Kraus and correction conjugations and as
conjugation by their product. -/
theorem clause6_corrected_branch {D s : ℕ} (K : RecordConditionedFamily D s)
    (hK : K.complete) (hU : K.correct_unitary) (ρ : Operator D) (k : Fin s) :
    (K.corrected hK hU).branch k ρ
      = (K.correct k) * ((K.kraus k) * ρ * (K.kraus k)ᴴ) * (K.correct k)ᴴ ∧
    K.localBranch hK hU ρ k
      = ((K.correct k) * (K.kraus k)) * ρ * ((K.correct k) * (K.kraus k))ᴴ :=
  ⟨RecordConditionedFamily.corrected_branch K hK hU ρ k,
   RecordConditionedFamily.localBranch_eq K hK hU ρ k⟩

/-- Summing all corrected local branches leaves the reference marginal unchanged. -/
theorem clause6_forgetting_transport {D R s : ℕ} (K : RecordConditionedFamily D s)
    (hK : K.complete) (hU : K.correct_unitary) (ρ : LocalJoint D R) :
    partialTraceFirst (K.forget hK hU ρ) = partialTraceFirst ρ := by
  change partialTraceFirst
      (∑ o, tensorLeft ((conditionalUnitaryInstrument (K.instrument hK) K.correct hU).branch o) ρ)
      = partialTraceFirst ρ
  exact conditionalUnitaryInstrument_reference (K.instrument hK) K.correct hU R ρ

/-- On a positive semidefinite joint input, the real trace of each corrected branch is at most
the real trace of the input. -/
theorem clause6_trace_nonincrease {D R s : ℕ} (K : RecordConditionedFamily D s)
    (hK : K.complete) (hU : K.correct_unitary) {ρ : LocalJoint D R}
    (hρ : ρ.PosSemidef) (k : Fin s) :
    (Matrix.trace (K.branch hK hU ρ k)).re ≤ (Matrix.trace ρ).re := by
  change (Matrix.trace
      (tensorLeft ((conditionalUnitaryInstrument (K.instrument hK) K.correct hU).branch k) ρ)).re
      ≤ (Matrix.trace ρ).re
  exact conditionalUnitaryInstrument_tni (K.instrument hK) K.correct hU R hρ k

/-- A corrected branch of a positive semidefinite input is zero whenever its instrument
probability is zero. -/
theorem clause6_zero_mass {D s : ℕ} (K : RecordConditionedFamily D s) (hK : K.complete)
    (hU : K.correct_unitary) (ρ : Operator D) (k : Fin s) (hρ : ρ.PosSemidef)
    (hz : instrumentProb (K.corrected hK hU) ρ k = 0) :
    (K.corrected hK hU).branch k ρ = 0 :=
  conditionalUnitaryInstrument_zero (K.instrument hK) K.correct hU ρ k hρ hz

/-- The canonical ledger has total price `2 * pairs + records`, factory charge equal to the EPR
factory gate-list length, and correction charge `records`. -/
theorem clause6_shared_accounting {records pairs : ℕ} (h : records ≤ pairs) :
    (canonicalLedger records pairs h).price = 2 * pairs + records ∧
    (canonicalLedger records pairs h).factoryGates = (eprFactoryGates pairs).length ∧
    (canonicalLedger records pairs h).correctionGates = records := by
  refine ⟨?_, ?_, rfl⟩
  · simp [CorrectedNetworkLedger.price, canonicalLedger]
  · simp [canonicalLedger, eprFactoryGates_length]

/-- Injectivity of a corrected-network ledger's slot assignment implies `records ≤ pairs`. -/
theorem clause6_ledger_feasible {records pairs : ℕ}
    (L : CorrectedNetworkLedger records pairs) : records ≤ pairs := by
  have h := Fintype.card_le_of_injective L.slot L.slot_injective
  simpa using h

/-- The canonical ledger with `n ^ 2` records and pairs has price `3 * n ^ 2`. -/
theorem clause6_qudit_ledger (n : ℕ) :
    (canonicalLedger (n ^ 2) (n ^ 2) (by omega)).price = 3 * n ^ 2 := by
  simp [CorrectedNetworkLedger.price, canonicalLedger]
  ring

/-- If a list has length `n` and agrees entrywise with a list of length at least `n`, it equals
the latter's first `n` entries. -/
private theorem take_eq_of_agree {α : Type} {l₁ l₂ : List α} {n : ℕ}
    (hlen : l₁.length = n) (hle : n ≤ l₂.length)
    (hag : ∀ (i : ℕ) (h₁ : i < l₁.length) (h₂ : i < l₂.length), l₁[i] = l₂[i]) :
    l₁ = l₂.take n := by
  have htake : l₁.take n = l₁ := (List.take_eq_self_iff l₁).mpr (by omega)
  have hlen2 : (l₂.take n).length = n := by
    rw [List.length_take]
    exact min_eq_left hle
  have hlen1 : (l₁.take n).length = n := by
    rw [List.length_take]
    exact min_eq_left (by omega)
  have hlen2 : (l₂.take n).length = n := by
    rw [List.length_take]
    exact min_eq_left hle
  have heq : l₁ = l₂.take n := by
    rw [← htake]
    refine List.ext_getElem (by omega) ?_
    intro i h1 h2
    rw [List.getElem_take (h := h1), List.getElem_take (h := h2)]
    exact hag i (by omega) (by omega)
  exact heq

/-- For a prefix-free code with lengths bounded by `C`, equality of its false-padded extensions
to `Fin C` implies equality of messages. -/
private theorem codeExtension_injective {M : Type} (w : M → List Bool) {C : ℕ}
    (hle : ∀ m, (w m).length ≤ C) (hp : PrefixFree w) {m₁ m₂ : M}
    (h : codeExtension w C m₁ = codeExtension w C m₂) : m₁ = m₂ := by
  by_contra hne
  have hlen₁ : (w m₁).length ≤ (w m₂).length ∨ (w m₂).length ≤ (w m₁).length :=
    le_total (w m₁).length (w m₂).length
  have hag : ∀ (i : ℕ) (h₁ : i < (w m₁).length) (h₂ : i < (w m₂).length),
      (w m₁)[i] = (w m₂)[i] := by
    intro i h₁ h₂
    have hiC : i < C := lt_of_lt_of_le h₁ (hle m₁)
    have heq := congrFun h ⟨i, hiC⟩
    have h1 : (w m₁).getD i false = (w m₁)[i] := List.getD_eq_getElem _ _ h₁
    have h2 : (w m₂).getD i false = (w m₂)[i] := List.getD_eq_getElem _ _ h₂
    simp only [codeExtension] at heq
    rw [h1, h2] at heq
    exact heq
  rcases hlen₁ with hord | hord
  · have hpref : w m₁ <+: w m₂ := by
      rw [List.prefix_iff_eq_take]
      exact take_eq_of_agree (hlen := rfl) (by omega) hag
    exact hp m₁ m₂ hne hpref
  · have hpref : w m₂ <+: w m₁ := by
      rw [List.prefix_iff_eq_take]
      exact take_eq_of_agree (hlen := rfl) (by omega)
        (fun i h₁ h₂ => (hag i h₂ h₁).symm)
    exact hp m₂ m₁ (Ne.symm hne) hpref

/-- An injective code whose words all have the same length is prefix-free. -/
private theorem prefixFree_of_injective_fixed {M : Type} (w : M → List Bool) {C : ℕ}
    (hlen : ∀ m, (w m).length = C) (hinj : Function.Injective w) : PrefixFree w := by
  intro a b hab h
  have hne : w a ≠ w b := fun h' => hab (hinj h')
  have ht : w a = (w b).take (w a).length := (List.prefix_iff_eq_take).mp h
  have htake : (w b).take (w a).length = w b := by
    rw [hlen a]
    exact (List.take_eq_self_iff (w b)).mpr (by rw [hlen b])
  rw [htake] at ht
  exact hne ht

/-- A finite message alphabet with a prefix-free binary code of maximum length `C` has
cardinality at most `2 ^ C`. -/
theorem clause7_general_letter_count {M : Type} [Fintype M] {C : ℕ}
    (K : PrefixFreeCode M C) : Fintype.card M ≤ 2 ^ C := by
  have hinj : Function.Injective (codeExtension K.word C) :=
    fun m₁ m₂ h => codeExtension_injective K.word K.word_le K.prefix_free h
  calc Fintype.card M ≤ Fintype.card (Fin C → Bool) :=
        Fintype.card_le_of_injective (codeExtension K.word C) hinj
    _ = 2 ^ C := by rw [Fintype.card_pi_const, Fintype.card_bool]

/-- When `n ≤ 2 ^ k`, equal teleportation codewords imply equal pairs of measurement outcomes. -/
theorem clause7_real_message_injective {n k : ℕ} (hw : n ≤ 2 ^ k) {o₁ o₂ : Fin n × Fin n}
    (h : teleportTypeCode n k o₁ = teleportTypeCode n k o₂) : o₁ = o₂ := by
  have h1 := quditMessage_decode n k hw o₁
  have h2 := quditMessage_decode n k hw o₂
  have h' : quditMessage n k o₁ = quditMessage n k o₂ := h
  rw [← h'] at h2
  exact Option.some.inj (h1.2.symm.trans h2.2)

/-- When `n ≤ 2 ^ k`, each teleportation outcome codeword has length `2 * k`. -/
theorem clause7_real_message_length {n k : ℕ} (hw : n ≤ 2 ^ k) (o : Fin n × Fin n) :
    (teleportTypeCode n k o).length = 2 * k := by
  exact (quditMessage_decode n k hw o).1

/-- When `n ≤ 2 ^ k`, the teleportation outcome code is prefix-free. -/
theorem clause7_real_message_prefix_free {n k : ℕ} (hw : n ≤ 2 ^ k) :
    PrefixFree (teleportTypeCode n k) := by
  refine prefixFree_of_injective_fixed (C := 2 * k) _ ?_
    (fun o₁ o₂ h => clause7_real_message_injective hw h)
  intro o
  exact clause7_real_message_length hw o

/-- The alphabet of pairs of outcomes in `Fin n` has cardinality `n ^ 2`. -/
theorem clause7_real_record_count (n : ℕ) : Fintype.card (Fin n × Fin n) = n ^ 2 := by
  rw [Fintype.card_prod, Fintype.card_fin, pow_two]

/-- When `n ≤ 2 ^ k`, the teleportation outcome alphabet has at most `2 ^ (2 * k)` elements. -/
theorem clause7_real_letter_count {n k : ℕ} (hw : n ≤ 2 ^ k) :
    Fintype.card (Fin n × Fin n) ≤ 2 ^ (2 * k) := by
  have K : PrefixFreeCode (Fin n × Fin n) (2 * k) :=
    { word := teleportTypeCode n k
      word_le := fun o => by
        have h := clause7_real_message_length hw o
        omega
      prefix_free := clause7_real_message_prefix_free hw }
  exact clause7_general_letter_count K

/-- Encoding a `w`-bit message with redundancy parameter `r` produces a word of length `r * w`. -/
theorem clause7_redundant_code_length {r w : ℕ} (m : Fin (2 ^ w)) :
    (redundantFixedWidth r w m).length = r * w := by
  simp [redundantFixedWidth, quditEncode, List.length_ofFn]

/-- For positive redundancy, equality of redundant fixed-width codewords implies equality of
messages. -/
theorem clause7_redundant_code_injective {r w : ℕ} (hr : 0 < r) {m₁ m₂ : Fin (2 ^ w)}
    (h : redundantFixedWidth r w m₁ = redundantFixedWidth r w m₂) : m₁ = m₂ := by
  have hdecode : ∀ m : Fin (2 ^ w),
      quditDecodeNat (quditEncode (r * w) m.val) = m.val := by
    intro m
    refine quditDecodeNat_exact _ _ ?_
    have h1 : m.val < 2 ^ w := m.isLt
    have h2 : 2 ^ w ≤ 2 ^ (r * w) := by
      have hlt : w ≤ r * w := by nlinarith
      exact Nat.pow_le_pow_right (n := 2) (by omega) hlt
    exact lt_of_lt_of_le h1 h2
  rw [redundantFixedWidth, redundantFixedWidth] at h
  have h'' := congrArg quditDecodeNat h
  rw [hdecode m₁, hdecode m₂] at h''
  exact Fin.ext h''

/-- Redundant fixed-width encoding is prefix-free whenever the redundancy parameter is positive. -/
theorem clause7_redundant_code_prefix_free {r w : ℕ} (hr : 0 < r) :
    PrefixFree (redundantFixedWidth r w) := by
  refine prefixFree_of_injective_fixed (C := r * w) _ ?_
    (fun m₁ m₂ h => clause7_redundant_code_injective hr h)
  intro m
  exact clause7_redundant_code_length m

/-- Defines two words by redundantly encoding the one-bit and two-bit all-false words with
redundancy two. -/
def frozenRedundantWords : Fin 2 → List Bool
  | 0 => redundantEncode 2 [false]
  | 1 => redundantEncode 2 [false, false]

/-- The two words in `frozenRedundantWords` do not form a prefix-free code. -/
theorem clause7_frozen_redundant_not_prefix_free :
    ¬ PrefixFree frozenRedundantWords := by
  intro h
  exact (h 0 1 (by decide)) (by simp [frozenRedundantWords, redundantEncode])

/-- Positive redundancy can only increase the real-valued bound `2 ^ C * (1 / N)` when `C` is
replaced by `r * C`. -/
theorem clause7_redundant_bound_degrades {N C r : ℕ} (hr : 0 < r) :
    (2 : ℝ) ^ C * (1 / (N : ℝ)) ≤ (2 : ℝ) ^ (r * C) * (1 / (N : ℝ)) := by
  have h1 : (1 / (N : ℝ)) ≥ 0 := by positivity
  have h2 : (2 : ℝ) ^ C ≤ (2 : ℝ) ^ (r * C) := by
    have hlt : C ≤ r * C := by nlinarith
    have hn : (2 : ℕ) ^ C ≤ (2 : ℕ) ^ (r * C) :=
      Nat.pow_le_pow_right (n := 2) (by omega) hlt
    exact_mod_cast hn
  exact mul_le_mul_of_nonneg_right h2 h1

/-- For a normalized positive shared state and a prefix-free code of maximum length `C`,
uniform-prior message-guessing success is at most `2 ^ C` divided by the input alphabet
size. -/
theorem clause7_protocol_letter_count_bound {X : Type} [Fintype X] [Nonempty X]
    {M : Type} [Fintype M] {A E B F : ℕ} (P : MessageGuessProtocol X M A E B F)
    (σ : Matrix (Fin A × Fin B) (Fin A × Fin B) ℂ) (hσ : σ.PosSemidef)
    (htrace : Matrix.trace σ = 1) {C : ℕ} (K : PrefixFreeCode M C) :
    P.success σ (fun _ => 1 / (Fintype.card X : ℝ))
      ≤ (2 : ℝ) ^ C * (1 / (Fintype.card X : ℝ)) := by
  have h1 := clause7_general_message_bound P σ hσ htrace
  have h2 : (Fintype.card M : ℝ) ≤ 2 ^ C := by
    exact_mod_cast clause7_general_letter_count K
  have h3 : 0 ≤ (1 / (Fintype.card X : ℝ)) := by positivity
  calc P.success σ (fun _ => 1 / (Fintype.card X : ℝ))
      ≤ (Fintype.card M : ℝ) * (1 / (Fintype.card X : ℝ)) := h1
    _ ≤ (2 : ℝ) ^ C * (1 / (Fintype.card X : ℝ)) :=
        mul_le_mul_of_nonneg_right h2 h3

/-- Collects total-trace preservation, corrected-branch semantics, reference-marginal
preservation, branch trace and zero-probability properties, and canonical-ledger prices. -/
theorem clause6_endpoint :
    (∀ {D s : ℕ} (K : RecordConditionedFamily D s) (hK : K.complete),
        (∀ A : Operator D, Matrix.trace (∑ k, (K.instrument hK).branch k A) = Matrix.trace A)) ∧
    (∀ {D s : ℕ} (K : RecordConditionedFamily D s) (hK : K.complete) (hU : K.correct_unitary)
        (ρ : Operator D) (k : Fin s),
        (K.corrected hK hU).branch k ρ
          = (K.correct k) * ((K.kraus k) * ρ * (K.kraus k)ᴴ) * (K.correct k)ᴴ) ∧
    (∀ {D R s : ℕ} (K : RecordConditionedFamily D s) (hK : K.complete)
        (hU : K.correct_unitary) (ρ : LocalJoint D R),
        partialTraceFirst (K.forget hK hU ρ) = partialTraceFirst ρ) ∧
    (∀ {D R s : ℕ} (K : RecordConditionedFamily D s) (hK : K.complete)
        (hU : K.correct_unitary) {ρ : LocalJoint D R} (hρ : ρ.PosSemidef) (k : Fin s),
        (Matrix.trace (K.branch hK hU ρ k)).re ≤ (Matrix.trace ρ).re) ∧
    (∀ {D s : ℕ} (K : RecordConditionedFamily D s) (hK : K.complete) (hU : K.correct_unitary)
        (ρ : Operator D) (k : Fin s) (hρ : ρ.PosSemidef),
        instrumentProb (K.corrected hK hU) ρ k = 0 →
          (K.corrected hK hU).branch k ρ = 0) ∧
    (∀ {records pairs : ℕ} (h : records ≤ pairs),
        (canonicalLedger records pairs h).price = 2 * pairs + records) ∧
    (∀ {records pairs : ℕ} (L : CorrectedNetworkLedger records pairs), records ≤ pairs) ∧
    (∀ (n : ℕ), (canonicalLedger (n ^ 2) (n ^ 2) (by omega)).price = 3 * n ^ 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro D s K hK A
    exact (clause6_record_instrument K hK).2 A
  · intro D s K hK hU ρ k
    exact (clause6_corrected_branch K hK hU ρ k).1
  · intro D R s K hK hU ρ
    exact clause6_forgetting_transport K hK hU ρ
  · intro D R s K hK hU ρ hρ k
    exact clause6_trace_nonincrease K hK hU hρ k
  · intro D s K hK hU ρ k hρ hz
    exact clause6_zero_mass K hK hU ρ k hρ hz
  · intro records pairs h
    exact (clause6_shared_accounting h).1
  · intro records pairs L
    exact clause6_ledger_feasible L
  · intro n
    exact clause6_qudit_ledger n

/-- Collects prefix-free alphabet bounds, teleportation-code injectivity, redundant fixed-width
code properties, the frozen-word counterexample, and monotonicity of the redundancy bound. -/
theorem clause7_endpoint :
    (∀ {M : Type} [Fintype M] {C : ℕ} (K : PrefixFreeCode M C),
        Fintype.card M ≤ 2 ^ C) ∧
    (∀ {n k : ℕ} (hw : n ≤ 2 ^ k), Fintype.card (Fin n × Fin n) ≤ 2 ^ (2 * k)) ∧
    (∀ {n k : ℕ} (hw : n ≤ 2 ^ k), PrefixFree (teleportTypeCode n k)) ∧
    (∀ {n k : ℕ} (hw : n ≤ 2 ^ k) {o₁ o₂ : Fin n × Fin n},
        teleportTypeCode n k o₁ = teleportTypeCode n k o₂ → o₁ = o₂) ∧
    (∀ {r w : ℕ} (hr : 0 < r), PrefixFree (redundantFixedWidth r w)) ∧
    (∀ {r w : ℕ} (m : Fin (2 ^ w)), (redundantFixedWidth r w m).length = r * w) ∧
    (¬ PrefixFree frozenRedundantWords) ∧
    (∀ {N C r : ℕ} (hr : 0 < r),
        (2 : ℝ) ^ C * (1 / (N : ℝ)) ≤ (2 : ℝ) ^ (r * C) * (1 / (N : ℝ))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro M inst C K
    exact clause7_general_letter_count K
  · intro n k hw
    exact clause7_real_letter_count hw
  · intro n k hw
    exact clause7_real_message_prefix_free hw
  · intro n k hw o₁ o₂ h
    exact clause7_real_message_injective hw h
  · intro r w hr
    exact clause7_redundant_code_prefix_free hr
  · intro r w m
    exact clause7_redundant_code_length m
  · exact clause7_frozen_redundant_not_prefix_free
  · intro N C r hr
    exact clause7_redundant_bound_degrades hr

end Qatlib.Concepts.FiniteLocc.LOCCProgram.MeasurementNetworkRefined
