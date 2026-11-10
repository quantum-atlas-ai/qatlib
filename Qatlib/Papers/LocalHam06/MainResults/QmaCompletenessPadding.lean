/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QmaCompleteness.HistoryHam.QmaCompletenessRefined
import Mathlib.Tactic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.QmaCompleteness.HistoryHam

set_option autoImplicit false
namespace Qatlib.Papers.LocalHam06.MainResults
open Qatlib  Qatlib.Concepts.QmaCompleteness.HistoryHam
open scoped Classical

def padHalf (C : QmaHistoryCircuit) : List FiniteGateCode :=
  List.replicate 32 (.h C.outputWire.val)

def padWord (C : QmaHistoryCircuit) : List FiniteGateCode :=
  padHalf C ++ finiteWordAdjoint (padHalf C)

theorem padHalf_legal (C : QmaHistoryCircuit) :
    finiteWordLegal C.qubits (padHalf C) = true := by
  simp [padHalf, finiteWordLegal, finiteCodeLegal, C.outputWire.isLt]

theorem padWord_legal (C : QmaHistoryCircuit) :
    finiteWordLegal C.qubits (padWord C) = true := by
  have hh := padHalf_legal C
  have ha := (finite_gate_word_paid_adjoint_semantics C.qubits (padHalf C)
    (0 : QState (Reg C.qubits)) hh).1
  simp only [padWord, finiteWordLegal, List.all_append, Bool.and_eq_true]
  exact ⟨hh, ha⟩

theorem padWord_length (C : QmaHistoryCircuit) : (padWord C).length = 64 := by
  simp [padWord, padHalf, finiteWordAdjoint]

theorem padWord_run (C : QmaHistoryCircuit) (ψ : QState (Reg C.qubits)) :
    Run (1 : Matrix (Reg C.qubits) (Reg C.qubits) ℂ)
      (finiteCodeCircuit C.qubits (padWord C)) ψ = ψ := by
  exact (finite_gate_word_paid_adjoint_semantics C.qubits (padHalf C)
    ψ (padHalf_legal C)).2.2.1

theorem padWord_gateCount (C : QmaHistoryCircuit) :
    GateCount (finiteCodeCircuit C.qubits (padWord C)) = 64 := by
  simpa [padHalf] using! (finite_gate_word_paid_adjoint_semantics C.qubits
    (padHalf C) (0 : QState (Reg C.qubits)) (padHalf_legal C)).2.2.2

def paid64 (C : QmaHistoryCircuit) : QmaHistoryCircuit where
  qubits := C.qubits
  gates := C.gates ++ padWord C
  legal := by
    have hc := C.legal
    have hp := padWord_legal C
    simp only [finiteWordLegal, List.all_append, Bool.and_eq_true]
    exact ⟨hc, hp⟩
  initZeroWires := C.initZeroWires
  outputWire := C.outputWire

theorem paid64_length (C : QmaHistoryCircuit) :
    (paid64 C).gates.length = C.gates.length + 64 := by
  simp only [paid64, List.length_append, padWord_length]

theorem paid64_run (C : QmaHistoryCircuit) (ψ : QState (Reg C.qubits)) :
    Run (1 : Matrix (Reg C.qubits) (Reg C.qubits) ℂ)
      (finiteCodeCircuit C.qubits (paid64 C).gates) ψ =
    Run (1 : Matrix (Reg C.qubits) (Reg C.qubits) ℂ)
      (finiteCodeCircuit C.qubits C.gates) ψ := by
  change Run (1 : Matrix (Reg C.qubits) (Reg C.qubits) ℂ)
    (finiteCodeCircuit C.qubits (C.gates ++ padWord C)) ψ = _
  rw [finiteCodeCircuit, List.map_append, run_append]
  exact padWord_run C _

theorem paid64_initLegal (C : QmaHistoryCircuit) (ψ : QState (Reg C.qubits)) :
    QmaInitLegal (paid64 C) ψ ↔ QmaInitLegal C ψ := Iff.rfl

theorem paid64_acceptance (C : QmaHistoryCircuit) (ψ : QState (Reg C.qubits)) :
    qmaHistoryAcceptProb (paid64 C) ψ = qmaHistoryAcceptProb C ψ := by
  unfold qmaHistoryAcceptProb
  change MeasureProb (Run 1 (finiteCodeCircuit C.qubits (paid64 C).gates) ψ)
    (Finset.univ.filter (fun z => z C.outputWire))=_
  rw [paid64_run]

theorem paid64_sound (C : QmaHistoryCircuit) (ε : ℝ)
    (hsound : ∀ φ : QState (Reg C.qubits),
      QmaInitLegal C φ → Normalized φ → qmaHistoryAcceptProb C φ ≤ ε) :
    ∀ φ : QState (Reg (paid64 C).qubits),
      QmaInitLegal (paid64 C) φ → Normalized φ →
        qmaHistoryAcceptProb (paid64 C) φ ≤ ε := by
  intro φ hL hN
  rw [paid64_acceptance]
  exact hsound φ ((paid64_initLegal C φ).mp hL) hN

theorem paid64_yes (C : QmaHistoryCircuit) (a : ℝ)
    (hyes : ∃ φ : QState (Reg C.qubits),
      QmaInitLegal C φ ∧ Normalized φ ∧ a ≤ qmaHistoryAcceptProb C φ) :
    ∃ φ : QState (Reg (paid64 C).qubits),
      QmaInitLegal (paid64 C) φ ∧ Normalized φ ∧
        a ≤ qmaHistoryAcceptProb (paid64 C) φ := by
  obtain ⟨φ,hL,hN,hA⟩ := hyes
  refine ⟨φ,(paid64_initLegal C φ).mpr hL,hN,?_⟩
  rw [paid64_acceptance]
  exact hA

theorem cubic_tail (m : ℕ) (hm : 64 ≤ m) :
    (2 : ℝ)^14 * ((m : ℝ)+1)^3 ≤ (2 : ℝ)^(m+2) := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      have hkR : (64 : ℝ) ≤ k := by exact_mod_cast hk
      have hprod : 0 ≤ ((k : ℝ)-3) * ((k : ℝ)^2+3*k+3) :=
        mul_nonneg (by linarith) (by positivity)
      have hstep : ((k : ℝ)+2)^3 ≤ 2*((k : ℝ)+1)^3 := by nlinarith
      have hmul := mul_le_mul_of_nonneg_left hstep
        (by positivity : (0 : ℝ) ≤ 2^14)
      have hi := mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ) ≤ 2)
      have he : (2 : ℝ)^((k+1)+2) = 2*(2 : ℝ)^(k+2) := by
        rw [show (k+1)+2=(k+2)+1 by omega, pow_succ]
        ring
      push_cast
      rw [he]
      nlinarith

theorem tiny_tail (n m : ℕ) (hm : 64 ≤ m) :
    qmaTiny (n+m+2) ≤ 1 / ((2 : ℝ)^14 * ((m : ℝ)+1)^3) := by
  have hpow : (2 : ℝ)^(m+2) ≤ (2 : ℝ)^(n+m+2) :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have hden := (cubic_tail m hm).trans hpow
  have hrecip := one_div_le_one_div_of_le
    (by positivity : (0 : ℝ) < (2 : ℝ)^14 * ((m : ℝ)+1)^3) hden
  simpa only [qmaTiny, inv_pow, one_div] using! hrecip

noncomputable def yesCut (C : QmaHistoryCircuit) : ℝ :=
  1 / ((2 : ℝ)^13 * ((C.gates.length : ℝ)+1)^3)

noncomputable def noCut (C : QmaHistoryCircuit) : ℝ :=
  1 / ((2 : ℝ)^12 * ((C.gates.length : ℝ)+1)^3)

theorem noBound_ge_cut (C : QmaHistoryCircuit) (ε : ℝ)
    (hm : 64 ≤ C.gates.length) (hε : ε ≤ 1/4) :
    noCut C ≤ qmaClause2NoBound C ε := by
  let d : ℝ := (C.gates.length : ℝ)+1
  have hd : 0 < d := by dsimp [d]; positivity
  have ht : qmaTiny (C.qubits+C.gates.length+2) ≤ 1 / ((2 : ℝ)^14*d^3) :=
    tiny_tail C.qubits C.gates.length hm
  have hnum : (1/2 : ℝ) ≤ 1-2*ε := by linarith
  have hlead : (1/2 : ℝ) / ((2 : ℝ)^10*d^3) ≤
      (1-2*ε) / ((2 : ℝ)^10*d^3) :=
    div_le_div_of_nonneg_right hnum (by positivity)
  have hadd : 1 / ((2 : ℝ)^12*d^3) + 1 / ((2 : ℝ)^14*d^3) =
      5 / ((2 : ℝ)^14*d^3) := by
    field_simp [hd.ne']
    ring
  have hsmall : 5 / ((2 : ℝ)^14*d^3) ≤ (1/2 : ℝ) / ((2 : ℝ)^10*d^3) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    norm_num
    nlinarith [pow_pos hd 3]
  change 1 / ((2 : ℝ)^12*d^3) ≤
    (1-2*ε) / ((2 : ℝ)^10*d^3) - qmaTiny (C.qubits+C.gates.length+2)
  apply (le_sub_iff_add_le).2
  calc
    1 / ((2 : ℝ)^12*d^3) + qmaTiny (C.qubits+C.gates.length+2) ≤
        1 / ((2 : ℝ)^12*d^3) + 1 / ((2 : ℝ)^14*d^3) := add_le_add_right ht _
    _ = 5 / ((2 : ℝ)^14*d^3) := hadd
    _ ≤ (1/2 : ℝ) / ((2 : ℝ)^10*d^3) := hsmall
    _ ≤ (1-2*ε) / ((2 : ℝ)^10*d^3) := hlead

theorem yesBound_le_cut (C : QmaHistoryCircuit) (a : ℝ)
    (hm : 64 ≤ C.gates.length)
    (ha : 1-a ≤ 1 / ((2 : ℝ)^14*((C.gates.length : ℝ)+1)^2)) :
    qmaClause2YesBound C a ≤ yesCut C := by
  let d : ℝ := (C.gates.length : ℝ)+1
  have hd : 0 < d := by dsimp [d]; positivity
  have ht : qmaTiny (C.qubits+C.gates.length+2) ≤ 1 / ((2 : ℝ)^14*d^3) :=
    tiny_tail C.qubits C.gates.length hm
  have hy : (1-a)/d ≤ (1 / ((2 : ℝ)^14*d^2))/d :=
    div_le_div_of_nonneg_right ha hd.le
  have he : (1 / ((2 : ℝ)^14*d^2))/d = 1 / ((2 : ℝ)^14*d^3) := by
    field_simp [hd.ne']
  rw [he] at hy
  change (1-a)/d + qmaTiny (C.qubits+C.gates.length+2) ≤ 1 / ((2 : ℝ)^13*d^3)
  calc
    (1-a)/d + qmaTiny (C.qubits+C.gates.length+2) ≤
        1 / ((2 : ℝ)^14*d^3) + 1 / ((2 : ℝ)^14*d^3) := add_le_add hy ht
    _ = 1 / ((2 : ℝ)^13*d^3) := by
      field_simp [hd.ne']
      ring

theorem cut_gap (C : QmaHistoryCircuit) :
    0 < yesCut C ∧ noCut C - yesCut C = yesCut C := by
  have hd : ((C.gates.length : ℝ)+1) ≠ 0 := by positivity
  constructor
  · unfold yesCut
    positivity
  · unfold noCut yesCut
    field_simp [hd]
    ring

theorem padded_actual_clause2_contract (C : QmaHistoryCircuit) (a ε : ℝ)
    (hε : ε ≤ 1/4)
    (ha : 1-a ≤ 1 / ((2 : ℝ)^14 * (((paid64 C).gates.length : ℝ)+1)^2)) :
    ((∃ φ : QState (Reg C.qubits),
        QmaInitLegal C φ ∧ Normalized φ ∧ a ≤ qmaHistoryAcceptProb C φ) →
      ∃ η : QState (Fin ((paid64 C).gates.length+1) × Reg C.qubits), Normalized η ∧
        qmaEnergy (qmaHistoryHamiltonian (paid64 C)
          (qmaRoundedGates (paid64 C) (qmaClause2Bits (paid64 C)))) η ≤ yesCut (paid64 C)) ∧
    ((∀ φ : QState (Reg C.qubits), QmaInitLegal C φ → Normalized φ →
        qmaHistoryAcceptProb C φ ≤ ε) →
      ∀ η : QState (Fin ((paid64 C).gates.length+1) × Reg C.qubits), Normalized η →
        noCut (paid64 C) ≤ qmaEnergy (qmaHistoryHamiltonian (paid64 C)
          (qmaRoundedGates (paid64 C) (qmaClause2Bits (paid64 C)))) η) ∧
    0 < yesCut (paid64 C) ∧
    noCut (paid64 C) - yesCut (paid64 C) = yesCut (paid64 C) := by
  have hm : 64 ≤ (paid64 C).gates.length := by rw [paid64_length]; omega
  refine ⟨?_,?_,(cut_gap (paid64 C)).1,(cut_gap (paid64 C)).2⟩
  · intro hyes
    obtain ⟨η,hη,hE⟩ := (clause2Aux_twoWay (paid64 C)).1 a (paid64_yes C a hyes)
    exact ⟨η,hη,hE.trans (yesBound_le_cut (paid64 C) a hm ha)⟩
  · intro hsound η hη
    exact (noBound_ge_cut (paid64 C) ε hm hε).trans
      (((clause2Aux_twoWay (paid64 C)).2.1 ε (paid64_sound C ε hsound)) η hη)

end Qatlib.Papers.LocalHam06.MainResults
