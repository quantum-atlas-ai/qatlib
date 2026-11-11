/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LocalHam06.MainResults.QmaCompletenessNormalized

/-!
# A normalized history-Hamiltonian encoding of QMA circuits

The circuit-to-Hamiltonian encoding is five-local and Hermitian, with each
embedded term bounded in operator norm. Its term count is explicit and its
binary description has polynomial length. Accepting witnesses give a low
energy state, while a circuit soundness bound gives a uniform lower energy
bound. The endpoint collects these encoding guarantees.

The Hamiltonian-complexity setting is [KempeKitaevRegev2006] and
[Kitaev, Shen & Vyalyi, *Classical and Quantum Computation*][KitaevShenVyalyi2002].
This module concerns the five-local history encoding; two-local gadgets are
handled elsewhere in this paper family.
-/
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Papers.LocalHam06.MainResults
open Qatlib  Qatlib.Concepts.QmaCompleteness.HistoryHam Matrix
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Papers.LocalHam06.MainResults
open Qatlib.Papers.LocalHam06.MainResults
open Qatlib.Concepts.TensorRegisters.RegisterModel
open scoped Classical
set_option autoImplicit false
noncomputable section

/-- The normalized history encoding contains `C.gates.length + C.initZeroWires.card + 1 +
C.gates.length^2` terms. -/
theorem normalizedEncoding_count (C : QmaHistoryCircuit) :
    (normalizedEncoding C).terms.length=C.gates.length+C.initZeroWires.card+1+C.gates.length^2 := by
  change ((outputTerms C.qubits (qmaClause2Bits C) C.gates C.initZeroWires C.outputWire).map toLhTerm).length=_
  rw [List.length_map,outputTerms_length]

/-- The bit encoding of the normalized history Hamiltonian has length at most `2000000 *
(C.gates.length + C.qubits + 1)^3`. -/
theorem normalizedEncoding_bitlength (C : QmaHistoryCircuit) :
    (qmaClause3ToBits (normalizedEncoding C)).length ≤ 2000000*(C.gates.length+C.qubits+1)^3 := by
  have h:=scaledEncoding_bitlength_polynomial C.qubits C.gates C.initZeroWires C.outputWire
  simpa only [qmaClause2Bits,Nat.add_comm] using! h

/-- The normalized encoded Hamiltonian has a normalized state with energy at most the scaled
completeness bound. -/
def EncodedYes (C : QmaHistoryCircuit) (a : ℝ) : Prop :=
  ∃η : QState (Reg (normalizedEncoding C).qubitCount),Normalized η ∧
    energy (lhHamiltonian (normalizedEncoding C)) η ≤ scale C*qmaClause2YesBound C a

/-- Every normalized state of the encoded Hamiltonian has energy at least `scale C * min
(qmaClause2NoBound C ε) 1`. -/
def EncodedNo (C : QmaHistoryCircuit) (ε : ℝ) : Prop :=
  ∀η : QState (Reg (normalizedEncoding C).qubitCount),Normalized η →
    scale C*min (qmaClause2NoBound C ε) 1 ≤ energy (lhHamiltonian (normalizedEncoding C)) η

/-- A legal normalized circuit input accepted with probability at least `a` yields the encoded
yes-energy condition. -/
theorem normalized_yes (C : QmaHistoryCircuit) (a : ℝ)
    (hyes : ∃φ : QState (Reg C.qubits),QmaInitLegal C φ ∧ Normalized φ ∧
      a ≤ qmaHistoryAcceptProb C φ) : EncodedYes C a := by
  obtain ⟨ψ,hψ,hE⟩:=actual_full_yes C a hyes
  refine ⟨fun x => ψ (flattenEquiv C.gates.length C.qubits x),flattened_normalized C ψ hψ,?_⟩
  exact (normalized_energy_transport C ψ).trans_le
    (mul_le_mul_of_nonneg_left hE (scale_pos C).le)

/-- An acceptance bound `ε` on all legal normalized circuit inputs yields the encoded no-energy
condition. -/
theorem normalized_no (C : QmaHistoryCircuit) (ε : ℝ)
    (hsound : ∀φ : QState (Reg C.qubits),QmaInitLegal C φ → Normalized φ →
      qmaHistoryAcceptProb C φ ≤ ε) : EncodedNo C ε := by
  intro η hη
  let ψ : QState (Phys C):=fun p => η ((flattenEquiv C.gates.length C.qubits).symm p)
  have hψ : Normalized ψ :=
    (mass_reindex (flattenEquiv C.gates.length C.qubits) η).trans hη
  have hE:=actual_full_no_min C ε hsound ψ hψ
  have ht:=normalized_energy_transport C ψ
  have ht' : energy (lhHamiltonian (normalizedEncoding C)) η=
      scale C*energy (fullHamiltonian C) ψ := by
    simpa only [ψ,Equiv.symm_apply_apply] using! ht
  exact (mul_le_mul_of_nonneg_left hE (scale_pos C).le).trans_eq ht'.symm

/-- Assemble locality, term normalization, polynomial description length, and
the yes/no energy guarantees for the history encoding. For the reduction
framework, see [Kempe, Kitaev & Regev][KempeKitaevRegev2006]. -/
theorem frontier1 (C : QmaHistoryCircuit) :
    lhLocal 5 (normalizedEncoding C) ∧ lhHermitian (normalizedEncoding C) ∧
    (∀t∈(normalizedEncoding C).terms,
      ‖Matrix.toEuclideanCLM (𝕜:=ℂ) (lhEmbedTerm (normalizedEncoding C).width t)‖ ≤ 1) ∧
    (normalizedEncoding C).terms.length=C.gates.length+C.initZeroWires.card+1+C.gates.length^2 ∧
    (qmaClause3ToBits (normalizedEncoding C)).length ≤ 2000000*(C.gates.length+C.qubits+1)^3 ∧
    (∀a : ℝ,(∃φ : QState (Reg C.qubits),QmaInitLegal C φ ∧ Normalized φ ∧
      a ≤ qmaHistoryAcceptProb C φ) → EncodedYes C a) ∧
    (∀ε : ℝ,(∀φ : QState (Reg C.qubits),QmaInitLegal C φ → Normalized φ →
      qmaHistoryAcceptProb C φ ≤ ε) → EncodedNo C ε) :=
  ⟨(normalizedEncoding_schema C).1,(normalizedEncoding_schema C).2.1,
    (normalizedEncoding_schema C).2.2,normalizedEncoding_count C,normalizedEncoding_bitlength C,
    normalized_yes C,normalized_no C⟩

end
end Qatlib.Papers.LocalHam06.MainResults
