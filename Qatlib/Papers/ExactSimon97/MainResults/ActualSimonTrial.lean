/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ExactSimon97.MainResults.SimonSubroutine
import Qatlib.Concepts.HspRecovery.Reduction.CountedSimonDecoder
import Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteThermal.FiniteThermalUniformH
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Concepts.WalkFind.UniformThree
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian
open Qatlib.Concepts.HspRecovery.Distinguisher
open Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.UniformBqp.FiniteGateWord.FiniteThermalCircuits
open Qatlib.Concepts.WalshMoment.Forrelation
open Qatlib.Concepts.PauliClifford.ExactRank
open Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel

namespace Qatlib.Papers.ExactSimon97.MainResults

def spectatorWord {n : ℕ} {R : Type} [Fintype R] [DecidableEq R]
    (gs : List FiniteGateCode) : Circuit (BoolVec n × R) :=
  gs.map fun g => Step.gate (TensorGate
    (relabelGate (regBooleanEquiv n) (finiteCodeMatrix n g)) (1 : Matrix R R ℂ))

theorem spectatorWord_run {n : ℕ} {R : Type} [Fintype R] [DecidableEq R]
    (gs : List FiniteGateCode) (O : Matrix (BoolVec n × R) (BoolVec n × R) ℂ)
    (ψ : QState (BoolVec n × R)) :
    Run O (spectatorWord gs) ψ = ApplyGate (TensorGate
      (relabelGate (regBooleanEquiv n) (finiteCodeWordMatrix n gs)) (1 : Matrix R R ℂ)) ψ := by
  induction gs generalizing ψ with
  | nil => simp [spectatorWord, finiteCodeWordMatrix, Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel.relabelGate_one, tensorGate_one, applyGate_one]
  | cons g gs ih =>
    simp only [spectatorWord, List.map_cons, run_gate]
    change Run O (spectatorWord gs) _ = _
    rw [ih, finite_phase_word_cons, Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel.relabelGate_mul, ← Matrix.one_mul (1 : Matrix R R ℂ),
      ← tensorGate_mul, applyGate_mul]
    simp only [Matrix.one_mul]

theorem spectatorWord_resources {n : ℕ} {R : Type} [Fintype R] [DecidableEq R]
    (gs : List FiniteGateCode) (hg : finiteWordLegal n gs = true) :
    IsUnitaryCircuit (spectatorWord (n := n) (R := R) gs) ∧
    GateCount (spectatorWord (n := n) (R := R) gs) = gs.length ∧
    QueryCount (spectatorWord (n := n) (R := R) gs) = 0 := by
  have hall : ∀ g ∈ gs, finiteCodeLegal n g = true := List.all_eq_true.mp hg
  induction gs with
  | nil => simp [spectatorWord]
  | cons g gs ih =>
    have ht : finiteWordLegal n gs = true := List.all_eq_true.mpr fun a ha => hall a (by simp [ha])
    obtain ⟨hu, hc, hq⟩ := ih ht (fun a ha => hall a (by simp [ha]))
    refine ⟨?_, ?_, ?_⟩
    · rw [spectatorWord, List.map_cons, isUnitaryCircuit_gate]
      exact ⟨tensorGate_unitary ((Qatlib.Concepts.GateVocabulary.GateVocab.relabelGate_mem_unitaryGroup _ _).2
        (finiteCodeMatrix_unitary n g (hall g (by simp)))) (Submonoid.one_mem _), hu⟩
    · simpa only [spectatorWord, List.map_cons, gateCount_gate, List.length_cons] using
        congrArg (· + 1) hc
    · simpa only [spectatorWord, List.map_cons, queryCount_gate] using hq

def actualSimonTrial {R : Type} [Fintype R] [DecidableEq R] (n : ℕ) : Circuit (BoolVec n × R) :=
  spectatorWord (thermalUniformHWord (List.finRange n)) ++ [Step.query] ++
    spectatorWord (thermalUniformHWord (List.finRange n))

theorem actualSimonTrial_run {n : ℕ} {R : Type} [AddCommGroup R] [Fintype R] [DecidableEq R]
    (ρ : BoolVec n → R) (ψ : QState (BoolVec n × R)) :
    Run (AddOracle ρ) (actualSimonTrial n) ψ = Run (AddOracle ρ) (simonPreparedCircuit n) ψ := by
  have hF : relabelGate (regBooleanEquiv n) (HadamardN n) =
      fourierGate (booleanCharacterEquiv n).toEquiv := by
    rw [hadamardN_eq_booleanFourierGate_submatrix]
    ext x y
    simp [relabelGate]
  simp only [actualSimonTrial, run_append, spectatorWord_run, thermalUniformHWord_all,
    run_query, run_nil, simonPreparedCircuit, hiddenSubgroupSamplingCircuit, run_gate]
  rw [hF]

theorem actualSimonTrial_resources (n : ℕ) {R : Type} [Fintype R] [DecidableEq R] :
    IsUnitaryCircuit (actualSimonTrial (R := R) n) ∧
    GateCount (actualSimonTrial (R := R) n) = 2*n ∧
    QueryCount (actualSimonTrial (R := R) n) = 1 := by
  obtain ⟨hu, hc, hq⟩ := spectatorWord_resources (R := R)
    (thermalUniformHWord (List.finRange n)) (thermalUniformHWord_legal _)
  have hl : (thermalUniformHWord (List.finRange n)).length = n := by simp [thermalUniformHWord]
  rw [hl] at hc
  simp only [actualSimonTrial, isUnitaryCircuit_append, gateCount_append, queryCount_append,
    isUnitaryCircuit_query, isUnitaryCircuit_nil, gateCount_query, gateCount_nil,
    queryCount_query, queryCount_nil, hc, hq, hu, and_self, Nat.add_zero, Nat.zero_add]
  simpa only [hl, and_true, true_and] using (show n + n = 2 * n by omega)

theorem actualSimonTrial_uniform {n : ℕ} {R : Type} [AddCommGroup R] [Fintype R] [DecidableEq R]
    (ρ : BoolVec n → R) (H0 : Submodule (ZMod 2) (BoolVec n))
    (hρ : FulfillsPromise ρ H0) (S : Finset (Reg n)) :
    MarginalProbLeft (Run (AddOracle ρ) (actualSimonTrial n) (Ket (0, 0)))
      (S.map (regBooleanEquiv n).toEmbedding) =
    ∑ y ∈ S, if regBooleanEquiv n y ∈ booleanOrthogonal H0.toAddSubgroup then
      1/(Fintype.card (characterAnnihilator H0.toAddSubgroup) : ℝ) else 0 := by
  rw [actualSimonTrial_run, (simon_actual_preparation_and_quantum_cost ρ 0).2.2.2.1]
  exact marginalProbLeft_hiddenSubgroupSampling_booleanReg ρ H0.toAddSubgroup hρ S

def sourceOrthogonalEquiv {n : ℕ} (H0 : Submodule (ZMod 2) (BoolVec n)) :
    ortho H0 ≃ booleanOrthogonal H0.toAddSubgroup where
  toFun x := ⟨x.1, fun h => x.2 h.1 h.2⟩
  invFun x := ⟨x.1, fun h hh => x.2 ⟨h, hh⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem sourceOrthogonal_card {n : ℕ} (H0 : Submodule (ZMod 2) (BoolVec n)) :
    Fintype.card (characterAnnihilator H0.toAddSubgroup) = Nat.card (ortho H0) := by
  rw [Nat.card_congr ((sourceOrthogonalEquiv H0).trans
    (booleanOrthogonalCharacterEquiv H0.toAddSubgroup).toEquiv), Nat.card_eq_fintype_card]

theorem theorem3_actual_source_event {n : ℕ} {R : Type} [AddCommGroup R] [Fintype R] [DecidableEq R]
    (ρ : BoolVec n → R) (H0 : Submodule (ZMod 2) (BoolVec n))
    (hρ : FulfillsPromise ρ H0) (S : Finset (Reg n)) :
    MarginalProbLeft (Run (AddOracle ρ) (actualSimonTrial n) (Ket (0, 0)))
      (S.map (regBooleanEquiv n).toEmbedding) =
    ∑ y ∈ S, uniformOnSub (ortho H0) (regBooleanEquiv n y) := by
  rw [actualSimonTrial_uniform ρ H0 hρ S, sourceOrthogonal_card]
  apply Finset.sum_congr rfl
  intro y _
  have he : regBooleanEquiv n y ∈ booleanOrthogonal H0.toAddSubgroup ↔
      regBooleanEquiv n y ∈ ortho H0 := by
    constructor
    · intro h x hx
      exact h ⟨x, hx⟩
    · intro h x
      exact h x.1 x.2
  simp only [uniformOnSub, he, one_div]

theorem actualSimonTrial_valid {n : ℕ} {R : Type} [AddCommGroup R] [Fintype R] [DecidableEq R]
    (ρ : BoolVec n → R) :
    AddOracle ρ ∈ Matrix.unitaryGroup (BoolVec n × R) ℂ ∧
    IsUnitaryCircuit (actualSimonTrial (R := R) n) :=
  ⟨addOracle_unitary ρ, (actualSimonTrial_resources n).1⟩

end Qatlib.Papers.ExactSimon97.MainResults
