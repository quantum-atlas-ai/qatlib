/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LocalHam06.MainResults.QmaCompletenessNative
import Qatlib.Papers.LocalHam06.MainResults.QmaCompletenessPhysical
import Qatlib.Papers.LocalHam06.MainResults.QmaCompletenessPadding
import Qatlib.Concepts.QueryComplexity.DegreeMethod.QmaCompletenessNativeBoundary
import Qatlib.Concepts.QueryComplexity.DegreeMethod.QmaCompletenessNativeEnergy
import Qatlib.Concepts.QueryComplexity.DegreeMethod.QmaCompletenessEntryBounds
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Papers.LocalHam06.MainResults.NativeOutput

namespace Qatlib.Papers.LocalHam06.MainResults
open Qatlib  Qatlib.Concepts.QmaCompleteness.HistoryHam Matrix
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Papers.LocalHam06.MainResults
open scoped Classical
set_option autoImplicit false
noncomputable section

theorem propagation_lower (C : QmaHistoryCircuit) (i : Fin C.gates.length)
    (ψ : QState (Phys C)) :
    -(32:ℝ)*mass ψ ≤ energy (physicalPropagation i (qmaRoundedGates C (qmaClause2Bits C) i)) ψ := by
  let g:=qmaGateAt C.gates i.val
  have hb : 1 ≤ qmaClause2Bits C:=by unfold qmaClause2Bits; omega
  exact local_table_lower (qmaClause2Bits C+1) (propagationTerm C.qubits (qmaClause2Bits C) i g)
    (physicalPropagation i (qmaRoundedGate C.qubits (qmaClause2Bits C) g))
    (propagationTerm_local _ _ _ _) (propagationTerm_value _ _ _ _)
    (physicalPropagation_entry_norm i _ (qmaRoundedGate_entry_norm_le_two g _ hb)) ψ

theorem input_lower (C : QmaHistoryCircuit) (j : Fin C.qubits) (ψ : QState (Phys C)) :
    -(32:ℝ)*mass ψ ≤ energy (physicalInput j) ψ := by
  have hv:=boundaryTerm_value C.gates.length C.qubits (qmaClause2Bits C) false j
  simp only [boundaryTarget,Bool.false_eq_true,if_false] at hv
  exact local_table_lower (qmaClause2Bits C+1)
    (boundaryTerm C.gates.length C.qubits (qmaClause2Bits C) false j) (physicalInput j)
    ((boundaryTerm_local _ _ _ _ _).trans (by omega)) hv (physicalInput_entry_norm j) ψ

theorem output_lower (C : QmaHistoryCircuit) (ψ : QState (Phys C)) :
    -(32:ℝ)*mass ψ ≤ energy (physicalOutput C.outputWire) ψ := by
  have hv:=boundaryTerm_value C.gates.length C.qubits (qmaClause2Bits C) true C.outputWire
  simp only [boundaryTarget,if_true] at hv
  exact local_table_lower (qmaClause2Bits C+1)
    (boundaryTerm C.gates.length C.qubits (qmaClause2Bits C) true C.outputWire)
    (physicalOutput C.outputWire) ((boundaryTerm_local _ _ _ _ _).trans (by omega)) hv
    (physicalOutput_entry_norm C.outputWire) ψ

theorem rest_lower (C : QmaHistoryCircuit) (ψ : QState (Phys C)) :
    -restK C*mass ψ ≤ energy (rest C) ψ := by
  have ht : ∀H∈(termPairs C).map Prod.fst,∀φ : QState (Phys C),
      -(32:ℝ)*mass φ ≤ energy H φ := by
    intro H hH φ
    obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hH
    simp only [termPairs,List.mem_append,List.mem_map,List.mem_singleton] at hp
    rcases hp with (⟨i,_,rfl⟩|⟨j,_,rfl⟩)|rfl
    · exact propagation_lower C i φ
    · exact input_lower C j φ
    · exact output_lower C φ
  simpa only [List.length_map,restLength_exact,restK,rest] using
    matrixSum_lower _ ht ψ

theorem actual_full_no_min (C : QmaHistoryCircuit) (ε : ℝ)
    (hsound : ∀φ : QState (Reg C.qubits),QmaInitLegal C φ → Normalized φ →
      qmaHistoryAcceptProb C φ ≤ ε) (η : QState (Phys C)) (hη : Normalized η) :
    min (qmaClause2NoBound C ε) 1 ≤ energy (fullHamiltonian C) η := by
  have hLegal : ∀ψ : QState (Abs C),Normalized ψ →
      min (qmaClause2NoBound C ε) 1 ≤ energy (legalHamiltonian C) ψ := by
    intro ψ hψ
    exact (min_le_left _ _).trans (((clause2Aux_twoWay C).2.1 ε hsound) ψ hψ)
  exact full_space_lower (rest C) (legalHamiltonian C) (rest_sector C) (rest_frame C)
    (min (qmaClause2NoBound C ε) 1) (restK C) (clockJ C)
    (by unfold restK; positivity) (by unfold clockJ; rfl) (min_le_right _ _)
    hLegal (rest_lower C) η hη

theorem noCut_le_one (C : QmaHistoryCircuit) : noCut C ≤ 1 := by
  have hn : 0 ≤ (C.gates.length:ℝ):=Nat.cast_nonneg _
  have hd : 1 ≤ ((C.gates.length:ℝ)+1)^3:=one_le_pow₀ (by linarith)
  have hden : 1 ≤ (2:ℝ)^12*((C.gates.length:ℝ)+1)^3:=by nlinarith
  simpa only [noCut,one_div_one] using
    one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hden

theorem padded_full_contract (C : QmaHistoryCircuit) (a ε : ℝ)
    (hε : ε ≤ 1/4)
    (ha : 1-a ≤ 1/((2:ℝ)^14*(((paid64 C).gates.length:ℝ)+1)^2)) :
    ((∃φ : QState (Reg C.qubits),QmaInitLegal C φ ∧ Normalized φ ∧
        a ≤ qmaHistoryAcceptProb C φ) →
      ∃η : QState (Phys (paid64 C)),Normalized η ∧
        energy (fullHamiltonian (paid64 C)) η ≤ yesCut (paid64 C)) ∧
    ((∀φ : QState (Reg C.qubits),QmaInitLegal C φ → Normalized φ →
        qmaHistoryAcceptProb C φ ≤ ε) →
      ∀η : QState (Phys (paid64 C)),Normalized η →
        noCut (paid64 C) ≤ energy (fullHamiltonian (paid64 C)) η) ∧
    0<yesCut (paid64 C) ∧ noCut (paid64 C)-yesCut (paid64 C)=yesCut (paid64 C) := by
  have hm : 64 ≤ (paid64 C).gates.length:=by rw [paid64_length]; omega
  refine ⟨?_,?_,(cut_gap (paid64 C)).1,(cut_gap (paid64 C)).2⟩
  · intro hyes
    obtain ⟨η,hη,hE⟩:=actual_full_yes (paid64 C) a (paid64_yes C a hyes)
    exact ⟨η,hη,hE.trans (yesBound_le_cut (paid64 C) a hm ha)⟩
  · intro hsound η hη
    apply (le_min (noBound_ge_cut (paid64 C) ε hm hε) (noCut_le_one (paid64 C))).trans
    exact actual_full_no_min (paid64 C) ε (paid64_sound C ε hsound) η hη

end
end Qatlib.Papers.LocalHam06.MainResults
