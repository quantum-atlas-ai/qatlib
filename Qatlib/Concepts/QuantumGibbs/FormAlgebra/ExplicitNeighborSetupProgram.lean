/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.QuantumGibbs.FormAlgebra.GeneralWalkAccess
public import Qatlib.Concepts.QuantumGibbs.FormAlgebra.GraphNeighborProgramConstruction

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AmplitudeCore.InvFreePhase Qatlib.Concepts.QuantumGibbs.FormAlgebra Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout Qatlib.Concepts.WalkSearch.TwoLevelLower Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.LCU Qatlib.Concepts.BlockEncoding.LinearCombination Qatlib.Concepts.BlockEncoding.StateBlockEncoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription Qatlib.Concepts.GateVocabulary.LocalReflectionGates Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Qatlib.Concepts.PauliClifford.ExactRank Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.PhaseGeometry.Phase

open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CopyEvolution.Discriminate Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.WalkSearch.TwoLevelLower

open Qatlib.Concepts.GraphEnergy.ZeroEnergy
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.WalkSearch.CountedWalk
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.WalkSearch.Spectral

namespace Qatlib.Concepts.QuantumGibbs.FormAlgebra
namespace CertifiedStage
namespace GraphAccessSetup

open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.QuantumGibbs.FormAlgebra.GeneralWalkAccessDefs
open scoped Classical BigOperators Matrix.Norms.L2Operator

set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {I : Type*} [Fintype I] [DecidableEq I]

structure RowAccess (P : I → I → ℝ) (j : I) where

  prep : Matrix (I × I) (I × I) ℂ

  unitary : prep ∈ Matrix.unitaryGroup (I × I) ℂ

  frame : ∀ i, prep *ᵥ TensorState (Ket i) (Ket j) = SzegedyIsometry P *ᵥ Ket i

namespace RowAccess

variable {P : I → I → ℝ} {j : I}

/-- Applying the adjoint row preparation after the preparation recovers the original clean
tensor basis state. -/
theorem clean_recovery (R : RowAccess P j) (i : I) :
    R.prepᴴ *ᵥ (R.prep *ᵥ TensorState (Ket i) (Ket j)) = TensorState (Ket i) (Ket j) := by
  have h : R.prepᴴ * R.prep = 1 := by
    have hstar := R.unitary
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hstar
    exact hstar
  calc R.prepᴴ *ᵥ (R.prep *ᵥ TensorState (Ket i) (Ket j))
      = (R.prepᴴ * R.prep) *ᵥ TensorState (Ket i) (Ket j) :=
        Matrix.mulVec_mulVec _ R.prepᴴ R.prep
    _ = 1 *ᵥ TensorState (Ket i) (Ket j) := by rw [h]
    _ = TensorState (Ket i) (Ket j) := Matrix.one_mulVec _

/-- Evaluating the counted Szegedy word with valid row access implements the Szegedy walk of the
transition matrix. -/
theorem prepared_walk (R : RowAccess P j) (hP : IsTransitionMatrix P) :
    evaluate R.prep (countedSzegedyWord j) = SzegedyWalk P :=
  counted_szegedy_actual_walk_semantics P j R.prep hP R.unitary R.frame

omit [Fintype I] [DecidableEq I] in
/-- The counted Szegedy word uses four adjoint-counted queries and four adjoint-counted gates. -/
theorem step_cost [Fintype I] [DecidableEq I] (j : I) :
    adjointQueryCount (countedSzegedyWord j) = 4 ∧
      adjointGateCount (countedSzegedyWord j) = 4 :=
  ⟨(counted_szegedy_actual_word_and_counts j).2.1,
    (counted_szegedy_actual_word_and_counts j).2.2⟩

/-- Repeating the counted Szegedy word implements the corresponding walk power with four queries
and four gates per repetition. -/
theorem repeated_walk (R : RowAccess P j) (hP : IsTransitionMatrix P) (m : ℕ) :
    evaluate R.prep ((List.replicate m (countedSzegedyWord j)).flatten) = (SzegedyWalk P) ^ m ∧
      adjointQueryCount ((List.replicate m (countedSzegedyWord j)).flatten) = 4 * m ∧
      adjointGateCount ((List.replicate m (countedSzegedyWord j)).flatten) = 4 * m :=
  counted_szegedy_repetition_semantics_resources P j R.prep m hP R.unitary R.frame

/-- Replacing the row preparation by a unitary within distance `δ` changes the repeated walk by
at most four times the repetition count times `δ`. -/
theorem prepared_walk_error (R : RowAccess P j) (hP : IsTransitionMatrix P)
    (V : Matrix (I × I) (I × I) ℂ) (hV : V ∈ Matrix.unitaryGroup (I × I) ℂ)
    (m : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) (hVU : ‖V - R.prep‖ ≤ δ) :
    ‖evaluate V ((List.replicate m (countedSzegedyWord j)).flatten) - (SzegedyWalk P) ^ m‖
      ≤ (4 * m : ℕ) * δ :=
  counted_szegedy_noisy_update_operator_error P j R.prep V m δ hP R.unitary hV R.frame hδ hVU

end RowAccess

open Qatlib

def zeroRecord (a : ℕ) : Reg a := fun _ => false

/-- The binary encoding of zero is the zero record. -/
lemma binaryEnc_zero (a : ℕ) : binaryEnc a (0 : Fin (2 ^ a)) = zeroRecord a := by
  funext i
  simp [binaryEnc, zeroRecord]

def pairEnc (a : ℕ) (p : Fin (2 ^ a) × Fin (2 ^ a)) : Reg (a + a) :=
  regCatLocal (binaryEnc a p.1) (binaryEnc a p.2)

/-- The first half of the pair encoding contains the bits of the first coordinate. -/
lemma pairEnc_apply_lt (a : ℕ) (p : Fin (2 ^ a) × Fin (2 ^ a)) (i : Fin (a + a))
    (hi : i.val < a) : pairEnc a p i = p.1.val.testBit i.val :=
  regCat_binaryEnc_lt (a := a) (x := p.1) (y := p.2) hi

/-- The second half of the pair encoding contains the bits of the second coordinate. -/
lemma pairEnc_apply_ge (a : ℕ) (p : Fin (2 ^ a) × Fin (2 ^ a)) (i : Fin (a + a))
    (hi : a ≤ i.val) : pairEnc a p i = p.2.val.testBit (i.val - a) :=
  regCat_binaryEnc_ge (a := a) (x := p.1) (y := p.2) hi

/-- The pair encoding is injective. -/
lemma pairEnc_injective (a : ℕ) : Function.Injective (pairEnc a) := by
  intro p q h
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · have : Subsingleton (Fin (2 ^ 0)) := by rw [pow_zero]; infer_instance
    exact Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  · have h1 : p.1 = q.1 := by
      apply binaryEnc_injective ha
      funext i
      have hw := congrFun h (Fin.castAdd a i)
      rw [pairEnc_apply_lt a p (Fin.castAdd a i) (by simp),
        pairEnc_apply_lt a q (Fin.castAdd a i) (by simp)] at hw
      exact hw
    have h2 : p.2 = q.2 := by
      apply binaryEnc_injective ha
      funext i
      have hw := congrFun h (Fin.natAdd a i)
      rw [pairEnc_apply_ge a p (Fin.natAdd a i) (by simp),
        pairEnc_apply_ge a q (Fin.natAdd a i) (by simp)] at hw
      simpa using! hw
    exact Prod.ext h1 h2

/-- The pair encoding is bijective. -/
lemma pairEnc_bijective (a : ℕ) : Function.Bijective (pairEnc a) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨pairEnc_injective a, ?_⟩
  rw [Fintype.card_prod, Fintype.card_fin, card_reg, ← Nat.pow_add]

noncomputable def pairEquiv (a : ℕ) : Fin (2 ^ a) × Fin (2 ^ a) ≃ Reg (a + a) :=
  Equiv.ofBijective (pairEnc a) (pairEnc_bijective a)

/-- The pair equivalence agrees with the pair encoding on every pair. -/
@[simp] lemma pairEquiv_apply (a : ℕ) (p : Fin (2 ^ a) × Fin (2 ^ a)) :
    pairEquiv a p = pairEnc a p := rfl

noncomputable def relabelWordStep {H K : Type*} (e : H ≃ K) :
    AdjointStep H → AdjointStep K
  | AdjointStep.gate U => AdjointStep.gate (relabelGate e U)
  | AdjointStep.forward => AdjointStep.forward
  | AdjointStep.backward => AdjointStep.backward

/-- Relabeling a gate step gives the step formed from the relabeled gate. -/
@[simp] lemma relabelWordStep_gate {H K : Type*} (e : H ≃ K) (U : Matrix H H ℂ) :
    relabelWordStep e (AdjointStep.gate U) = AdjointStep.gate (relabelGate e U) := rfl

noncomputable def circuitWord {H : Type*} (C : Circuit H) : List (AdjointStep H) :=
  C.reverse.map (fun s => match s with
    | Step.gate U => AdjointStep.gate U
    | Step.query => AdjointStep.forward)

/-- Evaluating the word of a circuit with identity oracle and applying it to a state agrees with
running the original circuit. -/
theorem run_eq_evaluate_circuitWord {H : Type*} [Fintype H] [DecidableEq H]
    (C : Circuit H) (ψ : QState H) :
    evaluate (1 : Matrix H H ℂ) (circuitWord C) *ᵥ ψ = Run 1 C ψ := by
  induction C generalizing ψ with
  | nil => simp [circuitWord, evaluate]
  | cons s C ih =>
    cases s with
    | gate U =>
      rw [show circuitWord (Step.gate U :: C)
          = circuitWord C ++ [AdjointStep.gate U] by
            simp [circuitWord, List.reverse_cons, List.map_append]]
      rw [evaluate_append]
      simp only [evaluate, instructionMatrix, Matrix.mul_one]
      rw [← Matrix.mulVec_mulVec, ih]
      rfl
    | query =>
      rw [show circuitWord (Step.query :: C)
          = circuitWord C ++ [AdjointStep.forward] by
            simp [circuitWord, List.reverse_cons, List.map_append]]
      rw [evaluate_append]
      simp only [evaluate, instructionMatrix, Matrix.mul_one]
      rw [ih]
      simp [Run]

/-- Relabeling every step of a word preserves its adjoint query count. -/
lemma adjointQueryCount_map_relabel {H K : Type*} (e : H ≃ K)
    (cs : List (AdjointStep H)) :
    adjointQueryCount (cs.map (relabelWordStep e)) = adjointQueryCount cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    cases c with
    | gate U => simp [relabelWordStep, adjointQueryCount, ih]
    | forward => simp [relabelWordStep, adjointQueryCount, ih]
    | backward => simp [relabelWordStep, adjointQueryCount, ih]

/-- Relabeling every step of a word preserves its adjoint gate count. -/
lemma adjointGateCount_map_relabel {H K : Type*} (e : H ≃ K)
    (cs : List (AdjointStep H)) :
    adjointGateCount (cs.map (relabelWordStep e)) = adjointGateCount cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    cases c with
    | gate U => simp [relabelWordStep, adjointGateCount, ih]
    | forward => simp [relabelWordStep, adjointGateCount, ih]
    | backward => simp [relabelWordStep, adjointGateCount, ih]

/-- The adjoint query count of a circuit word equals the original circuit query count. -/
lemma adjointQueryCount_circuitWord {H : Type*} (C : Circuit H) :
    adjointQueryCount (circuitWord C) = QueryCount C := by
  induction C with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U =>
      rw [show circuitWord (Step.gate U :: C)
          = circuitWord C ++ [AdjointStep.gate U] by
            simp [circuitWord, List.reverse_cons, List.map_append]]
      rw [adjointQueryCount_append, ih]
      rfl
    | query =>
      rw [show circuitWord (Step.query :: C)
          = circuitWord C ++ [AdjointStep.forward] by
            simp [circuitWord, List.reverse_cons, List.map_append]]
      rw [adjointQueryCount_append, ih]
      rfl

/-- The adjoint gate count of a circuit word equals the original circuit gate count. -/
lemma adjointGateCount_circuitWord {H : Type*} (C : Circuit H) :
    adjointGateCount (circuitWord C) = GateCount C := by
  induction C with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U =>
      rw [show circuitWord (Step.gate U :: C)
          = circuitWord C ++ [AdjointStep.gate U] by
            simp [circuitWord, List.reverse_cons, List.map_append]]
      rw [adjointGateCount_append, ih]
      rfl
    | query =>
      rw [show circuitWord (Step.query :: C)
          = circuitWord C ++ [AdjointStep.forward] by
            simp [circuitWord, List.reverse_cons, List.map_append]]
      rw [adjointGateCount_append, ih]
      rfl

/-- Relabeling a basis ket gives the ket at the relabeled index. -/
lemma relabelState_ket {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K]
    [DecidableEq K] (e : H ≃ K) (i : H) : relabelState e (Ket i) = Ket (e i) := by
  funext j
  change (Ket i) (e.symm j) = Ket (e i) j
  change (if e.symm j = i then (1 : ℂ) else 0) = (if j = e i then (1 : ℂ) else 0)
  by_cases h : e.symm j = i
  · rw [ite_eq_left h, ite_eq_left ((Equiv.symm_apply_eq e).mp h)]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h ((Equiv.symm_apply_eq e).mpr h'))]

/-- Relabeling states commutes with finite sums. -/
lemma relabelState_sum {H K κ : Type*} (e : H ≃ K) (s : Finset κ) (f : κ → QState H) :
    relabelState e (∑ k ∈ s, f k) = ∑ k ∈ s, relabelState e (f k) := by
  funext j
  simp [relabelState, Finset.sum_apply]

/-- Relabeling a state commutes with complex scalar multiplication. -/
lemma relabelState_smul {H K : Type*} (e : H ≃ K) (c : ℂ) (v : QState H) :
    relabelState e (c • v) = c • relabelState e v := rfl

/-- Evaluating a relabeled word with identity oracle gives the relabeling of the original
evaluated gate. -/
theorem evaluate_map_relabelWordStep {H K : Type*} [Fintype H] [DecidableEq H]
    [Fintype K] [DecidableEq K] (e : H ≃ K) (cs : List (AdjointStep H)) :
    evaluate (1 : Matrix K K ℂ) (cs.map (relabelWordStep e))
      = relabelGate e (evaluate (1 : Matrix H H ℂ) cs) := by
  induction cs with
  | nil =>
    rw [List.map_nil, evaluate, evaluate, CircuitRelabel.relabelGate_one]
  | cons c cs ih =>
    cases c with
    | gate U =>
      simp only [List.map_cons, relabelWordStep_gate, evaluate, instructionMatrix]
      rw [ih, ← CircuitRelabel.relabelGate_mul]
    | forward =>
      simp only [List.map_cons, relabelWordStep, evaluate, instructionMatrix,
        Matrix.one_mul, ih]
    | backward =>
      simp only [List.map_cons, relabelWordStep, evaluate, instructionMatrix,
        Matrix.conjTranspose_one, Matrix.one_mul, ih]

/-- A word consisting entirely of unitary gates evaluates to a unitary matrix. -/
theorem evaluate_unitary_of_gates {H : Type*} [Fintype H] [DecidableEq H]
    (cs : List (AdjointStep H))
    (h : ∀ c ∈ cs, ∃ V : Matrix H H ℂ,
      c = AdjointStep.gate V ∧ V ∈ Matrix.unitaryGroup H ℂ) :
    evaluate (1 : Matrix H H ℂ) cs ∈ Matrix.unitaryGroup H ℂ := by
  induction cs with
  | nil => exact (Matrix.unitaryGroup H ℂ).one_mem
  | cons c cs ih =>
    obtain ⟨V, rfl, hV⟩ := h c (by simp)
    have hcs : ∀ c' ∈ cs, ∃ V : Matrix H H ℂ,
        c' = AdjointStep.gate V ∧ V ∈ Matrix.unitaryGroup H ℂ := by
      intro c' hc'
      exact h c' (by simp [hc'])
    simp only [evaluate, instructionMatrix]
    exact (Matrix.unitaryGroup H ℂ).mul_mem hV (ih hcs)

noncomputable def bipartiteSetupWord (a : ℕ) :
    List (AdjointStep (Fin (2 ^ a) × Fin (2 ^ a))) :=
  (circuitWord (finiteCodeCircuit (a + a) (coherentRowWord a))).map
    (relabelWordStep (pairEquiv a).symm)

noncomputable def bipartitePrep (a : ℕ) :
    Matrix (Fin (2 ^ a) × Fin (2 ^ a)) (Fin (2 ^ a) × Fin (2 ^ a)) ℂ :=
  evaluate 1 (bipartiteSetupWord a)

/-- The bipartite preparation is the relabeling of the evaluated finite-code circuit for the
coherent row word. -/
lemma bipartitePrep_eq_relabel (a : ℕ) :
    bipartitePrep a
      = relabelGate (pairEquiv a).symm
          (evaluate (1 : Matrix (Reg (a + a)) (Reg (a + a)) ℂ)
            (circuitWord (finiteCodeCircuit (a + a) (coherentRowWord a)))) := by
  rw [bipartitePrep, bipartiteSetupWord, evaluate_map_relabelWordStep]

/-- The circuit generated by a finite gate-code list consists entirely of gate steps. -/
lemma finiteCodeCircuit_gateOnly {n : ℕ} (gs : List FiniteGateCode) :
    ∀ s ∈ finiteCodeCircuit n gs, ∃ U : Matrix (Reg n) (Reg n) ℂ, s = Step.gate U := by
  intro s hs
  simp only [finiteCodeCircuit, List.mem_map] at hs
  obtain ⟨g, _, rfl⟩ := hs
  exact ⟨_, rfl⟩

/-- Converting a circuit consisting entirely of gates to a word produces only gate steps. -/
lemma circuitWord_gateOnly {H : Type*} (C : Circuit H)
    (h : ∀ s ∈ C, ∃ U : Matrix H H ℂ, s = Step.gate U) :
    ∀ c ∈ circuitWord C, ∃ V : Matrix H H ℂ, c = AdjointStep.gate V := by
  intro c hc
  simp only [circuitWord, List.mem_map] at hc
  obtain ⟨s, hs, rfl⟩ := hc
  rw [List.mem_reverse] at hs
  cases s with
  | gate U => exact ⟨U, rfl⟩
  | query =>
    obtain ⟨U, hU⟩ := h Step.query hs
    cases hU

/-- The word of a unitary circuit consisting entirely of gates contains only unitary gate steps. -/
lemma circuitWord_mem_unitary {H : Type*} [Fintype H] [DecidableEq H] (C : Circuit H)
    (hg : ∀ s ∈ C, ∃ U : Matrix H H ℂ, s = Step.gate U) (hC : IsUnitaryCircuit C) :
    ∀ c ∈ circuitWord C, ∃ V : Matrix H H ℂ,
      c = AdjointStep.gate V ∧ V ∈ Matrix.unitaryGroup H ℂ := by
  intro c hc
  simp only [circuitWord, List.mem_map] at hc
  obtain ⟨s, hs, rfl⟩ := hc
  rw [List.mem_reverse] at hs
  cases s with
  | gate U => exact ⟨U, rfl, hC U hs⟩
  | query =>
    obtain ⟨U, hU⟩ := hg Step.query hs
    cases hU

/-- The finite-code circuit of the coherent row word is unitary for positive register size. -/
lemma coherentRowWord_circuit_unitary (a : ℕ) (ha : 0 < a) :
    IsUnitaryCircuit (finiteCodeCircuit (a + a) (coherentRowWord a)) :=
  (finite_gate_description_rejection_unitarity_and_counts (a + a)
    (coherentRowWord a)).2 (coherentRowWord_legal ha) |>.1

/-- The bipartite row preparation is unitary for positive register size. -/
theorem bipartitePrep_unitary (a : ℕ) (ha : 0 < a) :
    bipartitePrep a ∈ Matrix.unitaryGroup (Fin (2 ^ a) × Fin (2 ^ a)) ℂ := by
  have hword := circuitWord_mem_unitary
    (finiteCodeCircuit (a + a) (coherentRowWord a))
    (finiteCodeCircuit_gateOnly (coherentRowWord a))
    (coherentRowWord_circuit_unitary a ha)
  apply evaluate_unitary_of_gates
  intro c hc
  simp only [bipartiteSetupWord, List.mem_map] at hc
  obtain ⟨c0, hc0, rfl⟩ := hc
  obtain ⟨V, rfl, hV⟩ := hword c0 hc0
  exact ⟨relabelGate (pairEquiv a).symm V, rfl,
    (relabelGate_mem_unitaryGroup (pairEquiv a).symm V).mpr hV⟩

/-- The bipartite setup word uses zero queries and one more gate than the register size. -/
theorem bipartiteSetupWord_cost (a : ℕ) (ha : 0 < a) :
    adjointQueryCount (bipartiteSetupWord a) = 0 ∧
      adjointGateCount (bipartiteSetupWord a) = a + 1 := by
  obtain ⟨hQ, hG⟩ := finiteCodeCircuit_counts (a + a) (coherentRowWord a)
  have hq : adjointQueryCount (circuitWord
      (finiteCodeCircuit (a + a) (coherentRowWord a))) = 0 := by
    rw [adjointQueryCount_circuitWord, hQ]
  have hg : adjointGateCount (circuitWord
      (finiteCodeCircuit (a + a) (coherentRowWord a))) = a + 1 := by
    rw [adjointGateCount_circuitWord, hG, coherentRowWord_length ha]
  refine ⟨?_, ?_⟩
  · rw [bipartiteSetupWord, adjointQueryCount_map_relabel, hq]
  · rw [bipartiteSetupWord, adjointGateCount_map_relabel, hg]

/-- The adjoint bipartite setup word uses zero queries and one more gate than the register size. -/
theorem bipartiteSetupWord_adjoint_cost (a : ℕ) (ha : 0 < a) :
    adjointQueryCount (adjointCircuit (bipartiteSetupWord a)) = 0 ∧
      adjointGateCount (adjointCircuit (bipartiteSetupWord a)) = a + 1 := by
  rw [adjointQueryCount_adjointCircuit, adjointGateCount_adjointCircuit]
  exact bipartiteSetupWord_cost a ha

/-- The pair equivalence maps a pair with zero second coordinate to the corresponding clean
row-index record. -/
lemma pairEquiv_zero_frame (a : ℕ) (x : Fin (2 ^ a)) :
    pairEquiv a (x, (0 : Fin (2 ^ a))) = rowIndexRec a x 0 ⟨0, by simp⟩ := by
  rw [pairEquiv_apply, pairEnc, binaryEnc_zero]
  funext i
  by_cases hi : i.val < a
  · rw [regCat_apply_lt hi, rowIndexRec, ite_eq_left hi]
    rfl
  · rw [regCat_apply_ge (le_of_not_gt hi), rowIndexRec, ite_eq_right hi]
    simp [zeroRecord]

/-- The bipartite preparation maps a vertex ket with a clean second register to the
corresponding Szegedy isometry column. -/
theorem bipartitePrep_frame (a : ℕ) (ha : 0 < a) (x : Fin (2 ^ a)) :
    bipartitePrep a *ᵥ TensorState (Ket x) (Ket (0 : Fin (2 ^ a)))
      = SzegedyIsometry (regularKernel (bipartiteGraph a) ((2 ^ (a - 1) : ℕ) : ℝ)) *ᵥ Ket x := by
  rw [tensorState_ket_ket]
  rw [bipartitePrep_eq_relabel, relabelGate_mulVec_apply, relabelState_ket]
  simp only [Equiv.symm_symm]
  rw [pairEquiv_zero_frame]
  rw [run_eq_evaluate_circuitWord, coherentRowWord_run ha x, relabelState_sum]
  have hterm : ∀ k : Fin (2 ^ (a - 1)),
      relabelState (pairEquiv a).symm
        (((Real.sqrt 2 : ℂ)⁻¹) ^ (a - 1) • Ket (rowFinalRec ha x k))
      = ((Real.sqrt 2 : ℂ)⁻¹) ^ (a - 1) • Ket (x, bipartiteNeighbor ha x k) := by
    intro k
    rw [relabelState_smul, relabelState_ket]
    have hidx : (pairEquiv a).symm (rowFinalRec ha x k) = (x, bipartiteNeighbor ha x k) := by
      rw [rowFinalRec_regCat]
      change (pairEquiv a).symm (pairEnc a (x, bipartiteNeighbor ha x k)) = _
      exact (pairEquiv a).symm_apply_apply _
    rw [hidx]
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  rw [show (∑ k : Fin (2 ^ (a - 1)),
        ((Real.sqrt 2 : ℂ)⁻¹) ^ (a - 1) • Ket (x, bipartiteNeighbor ha x k))
      = ∑ y ∈ nbFin a x,
        ((Real.sqrt 2 : ℂ)⁻¹) ^ (a - 1) • Ket (x, y) from
      sum_bipartiteNeighbor_eq_nbFin ha x
        (fun y => ((Real.sqrt 2 : ℂ)⁻¹) ^ (a - 1) • Ket (x, y))]
  rw [szegedyIsometry_bipartite_column a ha x, amplitude_eq a]

noncomputable def bipartiteRowAccess (a : ℕ) (ha : 0 < a) :
    RowAccess (regularKernel (bipartiteGraph a) ((2 ^ (a - 1) : ℕ) : ℝ))
      (0 : Fin (2 ^ a)) where
  prep := bipartitePrep a
  unitary := bipartitePrep_unitary a ha
  frame := bipartitePrep_frame a ha

/-- The adjoint setup word recovers the clean tensor basis state after bipartite preparation. -/
theorem bipartiteSetup_clean_recovery (a : ℕ) (ha : 0 < a) (x : Fin (2 ^ a)) :
    evaluate (1 : Matrix (Fin (2 ^ a) × Fin (2 ^ a)) (Fin (2 ^ a) × Fin (2 ^ a)) ℂ)
        (adjointCircuit (bipartiteSetupWord a))
        *ᵥ (bipartitePrep a *ᵥ TensorState (Ket x) (Ket (0 : Fin (2 ^ a))))
      = TensorState (Ket x) (Ket (0 : Fin (2 ^ a))) := by
  rw [evaluate_adjointCircuit]
  exact RowAccess.clean_recovery (bipartiteRowAccess a ha) x

section GenericRowPrep

noncomputable def rankOne (w : I → ℂ) : Matrix I I ℂ :=
  Matrix.vecMulVec w (fun i => star (w i))

omit [Fintype I] [DecidableEq I] in

/-- The rank-one operator `rankOne` is self-adjoint. -/
lemma rankOne_star (w : I → ℂ) : star (rankOne w) = rankOne w := by
  rw [Matrix.star_eq_conjTranspose, rankOne, Matrix.conjTranspose_vecMulVec]
  congr 1
  funext i
  simp

omit [DecidableEq I] in

/-- The square of `rankOne` is itself multiplied by the squared norm of its defining vector. -/
lemma rankOne_mul (w : I → ℂ) :
    rankOne w * rankOne w = ((∑ i, star (w i) * w i) : ℂ) • rankOne w := by
  rw [rankOne, Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul]
  rfl

omit [DecidableEq I] in

/-- The sum of complex conjugate self-products is fixed by conjugation. -/
lemma star_sum_self (w : I → ℂ) :
    star (∑ i, star (w i) * w i) = ∑ i, star (w i) * w i := by
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [star_mul, star_star]

noncomputable def rowHouseholder (w : I → ℂ) : Matrix I I ℂ :=
  1 - ((2 : ℂ) / (∑ i, star (w i) * w i)) • rankOne w

/-- The row Householder matrix is self-adjoint. -/
lemma rowHouseholder_star (w : I → ℂ) : star (rowHouseholder w) = rowHouseholder w := by
  rw [rowHouseholder, star_sub, star_one, star_smul, rankOne_star]
  congr 2
  rw [star_div₀, star_sum_self]
  norm_num

/-- The row Householder matrix squares to the identity when its defining vector has nonzero
squared norm. -/
lemma rowHouseholder_mul_self (w : I → ℂ)
    (hs : (∑ i, star (w i) * w i) ≠ 0) :
    rowHouseholder w * rowHouseholder w = 1 := by
  set s : ℂ := ∑ i, star (w i) * w i with hsv
  set c : ℂ := 2 / s with hc
  set P : Matrix I I ℂ := rankOne w with hP
  have hPP : P * P = s • P := by
    rw [hP]
    exact rankOne_mul w
  have hcs : c * s = 2 := by
    rw [hc]
    field_simp
  rw [rowHouseholder]
  calc (1 - c • P) * (1 - c • P)
      = (1 - c • P) - (1 - c • P) * (c • P) := by rw [Matrix.mul_sub, Matrix.mul_one]
    _ = 1 - c • P - ((c • P) - (c • P) * (c • P)) := by
        rw [Matrix.sub_mul, Matrix.one_mul]
    _ = 1 - c • P - c • P + (c • P) * (c • P) := by abel
    _ = 1 - c • P - c • P + (c * c) • (P * P) := by
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    _ = 1 - c • P - c • P + (c * c) • (s • P) := by rw [hPP]
    _ = 1 - c • P - c • P + (c * (c * s)) • P := by
        rw [smul_smul, mul_assoc]
    _ = 1 - c • P - c • P + (c * 2) • P := by rw [hcs]
    _ = 1 - c • P - c • P + (2 * c) • P := by rw [mul_comm c 2]
    _ = 1 := by
        rw [show (2 * c) • P = c • P + c • P by rw [← add_smul]; congr 1; ring]
        abel

/-- The row Householder matrix is unitary when its defining vector has nonzero squared norm. -/
theorem rowHouseholder_unitary (w : I → ℂ)
    (hs : (∑ i, star (w i) * w i) ≠ 0) :
    rowHouseholder w ∈ Matrix.unitaryGroup I ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  rw [rowHouseholder_star]
  exact rowHouseholder_mul_self w hs

end GenericRowPrep

section GenericRowFrame

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Summing a vector against a basis ket selects the corresponding coordinate. -/
lemma sum_mul_ket (v : I → ℂ) (j0 : I) :
    (∑ i, v i * Ket j0 i) = v j0 := by
  rw [Finset.sum_eq_single j0]
  · simp [Qatlib.Foundations.PureStateMath.Ket]
  · intro b _ hb
    simp [Qatlib.Foundations.PureStateMath.Ket, hb]
  · intro h
    exact absurd (Finset.mem_univ j0) h

/-- Summing a conjugated vector against a basis ket selects the conjugate of the corresponding
coordinate. -/
lemma sum_star_mul_ket (v : I → ℂ) (j0 : I) :
    (∑ i, star (v i) * Ket j0 i) = star (v j0) := by
  rw [Finset.sum_eq_single j0]
  · simp [Qatlib.Foundations.PureStateMath.Ket]
  · intro b _ hb
    simp [Qatlib.Foundations.PureStateMath.Ket, hb]
  · intro h
    exact absurd (Finset.mem_univ j0) h

/-- Summing a vector against a conjugated basis ket selects the corresponding coordinate. -/
lemma sum_ket_star_ket (v : I → ℂ) (j0 : I) :
    (∑ i, star (Ket j0 i) * v i) = v j0 := by
  rw [Finset.sum_eq_single j0]
  · simp [Qatlib.Foundations.PureStateMath.Ket]
  · intro b _ hb
    simp [Qatlib.Foundations.PureStateMath.Ket, hb]
  · intro h
    exact absurd (Finset.mem_univ j0) h

/-- A basis ket has squared norm one. -/
lemma sum_star_ket_ket (j0 : I) :
    (∑ i, star (Ket j0 i) * Ket j0 i) = 1 := by
  rw [Finset.sum_eq_single j0]
  · simp [Qatlib.Foundations.PureStateMath.Ket]
  · intro b _ hb
    simp [Qatlib.Foundations.PureStateMath.Ket, hb]
  · intro h
    exact absurd (Finset.mem_univ j0) h

/-- The rank-one operator applied to a basis ket is its defining vector scaled by the conjugate
of the selected coordinate. -/
lemma rankOne_mulVec_ket (w : I → ℂ) (j0 : I) :
    rankOne w *ᵥ Ket j0 = star (w j0) • w := by
  rw [rankOne, Matrix.vecMulVec_mulVec]
  rw [show ((fun i => star (w i)) ⬝ᵥ Ket j0) = star (w j0) from by
    rw [dotProduct]
    exact sum_star_mul_ket w j0]
  exact IsCentralScalar.op_smul_eq_smul _ _

/-- For a real unit vector, its squared distance from a basis ket is two minus twice the
selected coordinate. -/
lemma sub_ket_length (v : I → ℂ) (j0 : I)
    (hreal : ∀ i, star (v i) = v i)
    (hunit : (∑ i, star (v i) * v i) = 1) :
    (∑ i, star ((v - Ket j0) i) * (v - Ket j0) i) = 2 - 2 * v j0 := by
  have hsum1 : (∑ i, star (v i) * Ket j0 i) = star (v j0) := sum_star_mul_ket v j0
  have hsum2 : (∑ i, star (Ket j0 i) * v i) = v j0 := sum_ket_star_ket v j0
  have hsum3 : (∑ i, star (Ket j0 i) * Ket j0 i) = 1 := sum_star_ket_ket j0
  have hexp : ∀ i, star (v i - Ket j0 i) * (v i - Ket j0 i)
      = star (v i) * v i - star (v i) * Ket j0 i - star (Ket j0 i) * v i
        + star (Ket j0 i) * Ket j0 i := by
    intro i
    rw [star_sub]
    ring
  calc (∑ i, star ((v - Ket j0) i) * (v - Ket j0) i)
      = ∑ i, (star (v i) * v i - star (v i) * Ket j0 i - star (Ket j0 i) * v i
          + star (Ket j0 i) * Ket j0 i) := by
        apply Finset.sum_congr rfl
        intro i _
        exact hexp i
    _ = (∑ i, star (v i) * v i) - (∑ i, star (v i) * Ket j0 i)
          - (∑ i, star (Ket j0 i) * v i) + (∑ i, star (Ket j0 i) * Ket j0 i) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    _ = 1 - star (v j0) - v j0 + 1 := by
        rw [hunit, hsum1, hsum2, hsum3]
    _ = 2 - 2 * v j0 := by
        rw [hreal j0]
        ring

/-- The Householder matrix defined by a real unit vector minus a basis ket maps that ket to the
vector when the selected coordinate differs from one. -/
theorem rowHouseholder_frame (v : I → ℂ) (j0 : I)
    (hreal : ∀ i, star (v i) = v i)
    (hunit : (∑ i, star (v i) * v i) = 1)
    (hne : v j0 ≠ 1) :
    rowHouseholder (v - Ket j0) *ᵥ Ket j0 = v := by
  set w : I → ℂ := v - Ket j0 with hw
  have hsw : (∑ i, star (w i) * w i) = 2 - 2 * v j0 := by
    rw [hw]
    exact sub_ket_length v j0 hreal hunit
  have hPe : rankOne w *ᵥ Ket j0 = (v j0 - 1) • w := by
    rw [rankOne_mulVec_ket]
    have hwj : w j0 = v j0 - 1 := by simp [hw, Qatlib.Foundations.PureStateMath.Ket]
    rw [hwj, star_sub, hreal j0]
    norm_num
  rw [rowHouseholder, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hPe]
  rw [smul_smul]
  have hc : (2 : ℂ) / (2 - 2 * v j0) * (v j0 - 1) = -1 := by
    have hden : (2 - 2 * v j0 : ℂ) = 2 * (1 - v j0) := by ring
    rw [hden]
    have h1 : (1 - v j0 : ℂ) ≠ 0 := by
      intro h
      exact hne (sub_eq_zero.mp h).symm
    field_simp
    ring
  rw [hsw, hc, neg_one_smul]
  rw [hw]
  abel

noncomputable def doubledRowPrep (v : I → I → ℂ) (j0 : I) : Matrix (I × I) (I × I) ℂ :=
  Matrix.reindex (Equiv.prodComm I I) (Equiv.prodComm I I)
    (Matrix.blockDiagonal (fun x => rowHouseholder (v x - Ket j0)))

/-- The doubled row preparation is unitary for real unit rows whose selected coordinates all
differ from one. -/
theorem doubledRowPrep_unitary (v : I → I → ℂ) (j0 : I)
    (hreal : ∀ x i, star (v x i) = v x i)
    (hunit : ∀ x, (∑ i, star (v x i) * v x i) = 1)
    (hne : ∀ x, v x j0 ≠ 1) :
    doubledRowPrep v j0 ∈ Matrix.unitaryGroup (I × I) ℂ := by
  have hblock : ∀ x, rowHouseholder (v x - Ket j0) * rowHouseholder (v x - Ket j0) = 1 := by
    intro x
    refine rowHouseholder_mul_self _ ?_
    rw [sub_ket_length (v x) j0 (hreal x) (hunit x)]
    intro h
    have h2 : (2 : ℂ) * (1 - v x j0) = 0 := by
      rw [show (2 : ℂ) * (1 - v x j0) = 2 - 2 * v x j0 by ring, h]
    rcases mul_eq_zero.mp h2 with h3 | h3
    · norm_num at h3
    · exact hne x (sub_eq_zero.mp h3).symm
  rw [doubledRowPrep, Matrix.reindex_apply, Matrix.mem_unitaryGroup_iff']
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix]
  rw [show (Matrix.blockDiagonal fun x => rowHouseholder (v x - Ket j0))ᴴ
      = Matrix.blockDiagonal (fun x => (rowHouseholder (v x - Ket j0))ᴴ)
      from Matrix.blockDiagonal_conjTranspose _]
  rw [Matrix.submatrix_mul_equiv]
  rw [← Matrix.blockDiagonal_mul]
  rw [show (fun x => (rowHouseholder (v x - Ket j0))ᴴ * rowHouseholder (v x - Ket j0))
      = (fun _ => 1) by
    funext x
    rw [← Matrix.star_eq_conjTranspose]
    rw [rowHouseholder_star]
    exact hblock x]
  rw [show (fun _ => (1 : Matrix I I ℂ)) = 1 from rfl, Matrix.blockDiagonal_one]
  exact Matrix.submatrix_one_equiv _

/-- A block-diagonal matrix applied to a basis ket yields the selected column within the
selected block and zero outside that block. -/
lemma blockDiagonal_mulVec_ket {o m : Type*} [Fintype o] [Fintype m] [DecidableEq o]
    [DecidableEq m] (M : o → Matrix m m ℂ) (x : o) (j0 : m) :
    Matrix.blockDiagonal M *ᵥ Ket (j0, x)
      = fun p : m × o => if p.2 = x then M x p.1 j0 else 0 := by
  ext p
  obtain ⟨j, x'⟩ := p
  rw [Matrix.mulVec, dotProduct, ← Finset.univ_product_univ, Finset.sum_product,
    Finset.sum_comm]
  rw [Finset.sum_eq_single x]
  · rw [Finset.sum_eq_single j0]
    · rw [Matrix.blockDiagonal_apply]
      by_cases hx : x' = x
      · simp [Qatlib.Foundations.PureStateMath.Ket, hx]
      · simp [Qatlib.Foundations.PureStateMath.Ket, hx]
    · intro b _ hb
      simp [Qatlib.Foundations.PureStateMath.Ket, hb]
    · intro h
      exact absurd (Finset.mem_univ j0) h
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro y _
    have hk : Qatlib.Foundations.PureStateMath.Ket (j0, x) (y, b) = 0 := by
      simp only [Qatlib.Foundations.PureStateMath.Ket]
      rw [ite_eq_right]
      intro hcon
      exact hb (congrArg Prod.snd hcon)
    rw [hk, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ x) h

/-- If each row Householder matrix prepares its row vector, the doubled row preparation prepares
that vector while preserving the first register. -/
theorem doubledRowPrep_frame (v : I → I → ℂ) (j0 : I)
    (hframe : ∀ x, rowHouseholder (v x - Ket j0) *ᵥ Ket j0 = v x) (x : I) :
    doubledRowPrep v j0 *ᵥ TensorState (Ket x) (Ket j0)
      = fun p => if p.1 = x then v x p.2 else 0 := by
  have hcomp : (Ket (x, j0) ∘ ⇑(Equiv.prodComm I I).symm.symm) = Ket (j0, x) := by
    funext p
    obtain ⟨a, b⟩ := p
    simp only [Function.comp, Equiv.symm_symm, Equiv.prodComm_apply, Prod.swap_prod_mk,
      Qatlib.Foundations.PureStateMath.Ket]
    by_cases h : a = j0 ∧ b = x
    · have h1 : (b, a) = (x, j0) := Prod.ext_iff.mpr ⟨h.2, h.1⟩
      have h2 : (a, b) = (j0, x) := Prod.ext_iff.mpr ⟨h.1, h.2⟩
      rw [ite_eq_left h1, ite_eq_left h2]
    · have h1 : (b, a) ≠ (x, j0) :=
        fun hh => h ⟨(Prod.ext_iff.mp hh).2, (Prod.ext_iff.mp hh).1⟩
      have h2 : (a, b) ≠ (j0, x) :=
        fun hh => h ⟨(Prod.ext_iff.mp hh).1, (Prod.ext_iff.mp hh).2⟩
      rw [ite_eq_right h1, ite_eq_right h2]
  have hts : TensorState (Ket x) (Ket j0) = Ket (x, j0) := by
    funext p
    obtain ⟨a, b⟩ := p
    simp only [tensorState_apply, Qatlib.Foundations.PureStateMath.Ket]
    by_cases ha : a = x <;> by_cases hb : b = j0 <;> simp [ha, hb, Prod.ext_iff]
  rw [hts, doubledRowPrep, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
  rw [hcomp, blockDiagonal_mulVec_ket]
  funext p
  obtain ⟨a, b⟩ := p
  have hscalar : ∀ y, rowHouseholder (v x - Ket j0) y j0 = v x y := by
    intro y
    have h := congrFun (hframe x) y
    rw [Matrix.mulVec, dotProduct, sum_mul_ket] at h
    exact h
  simp only [Function.comp, hscalar]
  by_cases ha : a = x
  · simp [ha]
  · simp [ha]

end GenericRowFrame

section PairPreparation

variable {N : ℕ}

noncomputable def pairAmp (N : ℕ) : ℂ := ((Real.sqrt (pairDegree N))⁻¹ : ℝ)

/-- The pair-neighbor amplitude `pairAmp` is fixed by conjugation. -/
lemma pairAmp_star (N : ℕ) : star (pairAmp N) = pairAmp N := by
  unfold pairAmp
  rw [Complex.star_def, Complex.conj_ofReal]

/-- The pair-neighbor amplitude differs from one when `N` is at least three. -/
lemma pairAmp_ne_one (hN : 3 ≤ N) : pairAmp N ≠ 1 := by
  have hpos : (0 : ℝ) < pairDegree N := by
    unfold pairDegree
    have : (0 : ℕ) < 2 * (N - 2) := by omega
    exact_mod_cast this
  have htwo : (2 : ℝ) ≤ pairDegree N := by
    unfold pairDegree
    have : 2 ≤ 2 * (N - 2) := by omega
    exact_mod_cast this
  intro h
  have hreal : ((Real.sqrt (pairDegree N))⁻¹ : ℝ) = 1 := Complex.ofReal_injective h
  have hsqrt : Real.sqrt (pairDegree N) = 1 := by
    simpa using! congrArg (fun r : ℝ => r⁻¹) hreal
  have hone : pairDegree N = 1 := by
    nth_rewrite 1 [← Real.sq_sqrt hpos.le]
    rw [hsqrt]
    norm_num
  linarith

noncomputable def pairRowVec (N : ℕ) (x : PairVertex N) : PairVertex N → ℂ :=
  ∑ p : PairRowIndex x, pairAmp N • Qatlib.Foundations.PureStateMath.Ket (pairRowOracle x p)

/-- The pair row vector equals `pairAmp` on neighbors and zero elsewhere. -/
lemma pairRowVec_apply {N : ℕ} (x y : PairVertex N) :
    pairRowVec N x y = if y ∈ pairNeighbours N x then pairAmp N else 0 := by
  unfold pairRowVec
  rw [Finset.sum_apply]
  by_cases hy : y ∈ pairNeighbours N x
  · obtain ⟨p0, hp0⟩ := pairRowOracle_surj x y hy
    rw [ite_eq_left hy]
    rw [Finset.sum_eq_single p0]
    · simp [hp0]
    · intro p _ hp
      have hne : y ≠ pairRowOracle x p := by
        intro h
        exact hp (pairRowOracle_injective x (h.symm.trans hp0.symm))
      simp [Qatlib.Foundations.PureStateMath.Ket, hne]
    · intro h
      exact absurd (Finset.mem_univ p0) h
  · rw [ite_eq_right hy]
    apply Finset.sum_eq_zero
    intro p _
    have hmem := pairRowOracle_mem_neighbours x p
    have hne : y ≠ pairRowOracle x p := fun h => hy (h ▸ hmem)
    simp [Qatlib.Foundations.PureStateMath.Ket, hne]

/-- Every coordinate of the pair row vector is fixed by conjugation. -/
lemma pairRowVec_real {N : ℕ} (x y : PairVertex N) :
    star (pairRowVec N x y) = pairRowVec N x y := by
  rw [pairRowVec_apply]
  by_cases hy : y ∈ pairNeighbours N x
  · rw [ite_eq_left hy]
    exact pairAmp_star N
  · rw [ite_eq_right hy]
    simp

/-- The pair row vector has squared norm one when `N` is at least three. -/
lemma pairRowVec_norm {N : ℕ} (hN : 3 ≤ N) (x : PairVertex N) :
    (∑ y, star (pairRowVec N x y) * pairRowVec N x y) = 1 := by
  have hterm : ∀ y, star (pairRowVec N x y) * pairRowVec N x y
      = if y ∈ pairNeighbours N x then star (pairAmp N) * pairAmp N else 0 := by
    intro y
    rw [pairRowVec_apply]
    by_cases hy : y ∈ pairNeighbours N x <;> simp [hy]
  rw [Finset.sum_congr rfl (fun y _ => hterm y)]
  rw [← Finset.sum_filter]
  rw [show (Finset.univ.filter (fun y => y ∈ pairNeighbours N x))
      = pairNeighbours N x from by
    ext y
    simp]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((pairNeighbours N x).card : ℂ) = (pairDegree N : ℂ) := by
    rw [pairNeighbours_card, x.2, pairVertex_outside_card]
    unfold pairDegree
    norm_num
  have hpos : (0 : ℝ) < pairDegree N := by
    unfold pairDegree
    have : (0 : ℕ) < 2 * (N - 2) := by omega
    exact_mod_cast this
  have hstar : star (pairAmp N) * pairAmp N = ((pairDegree N)⁻¹ : ℂ) := by
    rw [pairAmp_star]
    unfold pairAmp
    rw [← Complex.ofReal_mul]
    rw [show ((Real.sqrt (pairDegree N))⁻¹ * (Real.sqrt (pairDegree N))⁻¹ : ℝ)
        = (pairDegree N)⁻¹ by
      rw [← mul_inv, Real.mul_self_sqrt (le_of_lt hpos)]]
    rw [Complex.ofReal_inv]
  rw [hcard, hstar]
  have hne : (pairDegree N : ℂ) ≠ 0 := by
    unfold pairDegree
    have : (0 : ℕ) < 2 * (N - 2) := by omega
    have : (0 : ℝ) < ((2 * (N - 2) : ℕ) : ℝ) := by exact_mod_cast ‹(0:ℕ) < 2*(N-2)›
    exact_mod_cast ne_of_gt this
  field_simp

noncomputable def pairClean (hN : 3 ≤ N) : PairVertex N := pairMarked hN

/-- The pair row vector at the clean vertex differs from one when `N` is at least three. -/
lemma pairRowVec_ne_one {N : ℕ} (hN : 3 ≤ N) (x : PairVertex N) :
    pairRowVec N x (pairClean hN) ≠ 1 := by
  rw [pairRowVec_apply]
  by_cases hy : pairClean hN ∈ pairNeighbours N x
  · rw [ite_eq_left hy]
    exact pairAmp_ne_one hN
  · rw [ite_eq_right hy]
    norm_num

/-- Computes a pair-graph Szegedy isometry column as the neighbor amplitude on pairs with the
prescribed first coordinate and zero otherwise. -/
lemma szegedy_pair_column_entry {N : ℕ} (hN : 3 ≤ N) (x a b : PairVertex N) :
    (SzegedyIsometry (regularKernel (pairGraph N) (pairDegree N)) *ᵥ Ket x) (a, b)
      = if a = x then (if b ∈ pairNeighbours N x then pairAmp N else 0) else 0 := by
  by_cases ha : a = x
  · rw [ha, ite_eq_left rfl]
    by_cases hb : b ∈ pairNeighbours N x
    · rw [szegedyIsometry_pairGraph_apply hN x b, ite_eq_left hb, ite_eq_left hb]
      unfold pairAmp
      rw [Complex.ofReal_inv]
    · rw [szegedyIsometry_pairGraph_apply hN x b, ite_eq_right hb, ite_eq_right hb]
  · rw [mulVec_ket_column, szegedyIsometry_apply_pair, ite_eq_right ha, ite_eq_right ha]

/-- The tensor product of a vertex ket and its pair row vector equals the corresponding
pair-graph Szegedy isometry column. -/
theorem pairRowVec_eq_column {N : ℕ} (hN : 3 ≤ N) (x : PairVertex N) :
    TensorState (Ket x) (pairRowVec N x)
      = SzegedyIsometry (regularKernel (pairGraph N) (pairDegree N)) *ᵥ Ket x := by
  funext p
  obtain ⟨a, b⟩ := p
  rw [szegedy_pair_column_entry hN x a b]
  simp only [tensorState_apply, Qatlib.Foundations.PureStateMath.Ket]
  by_cases ha : a = x
  · rw [ite_eq_left ha, one_mul, ite_eq_left ha, pairRowVec_apply]
  · rw [ite_eq_right ha, ite_eq_right ha, zero_mul]

noncomputable def pairRowAccess {N : ℕ} (hN : 3 ≤ N) :
    RowAccess (regularKernel (pairGraph N) (pairDegree N)) (pairClean hN) where
  prep := doubledRowPrep (pairRowVec N) (pairClean hN)
  unitary := by
    refine doubledRowPrep_unitary (pairRowVec N) (pairClean hN) ?_ ?_ ?_
    · intro x i
      exact pairRowVec_real x i
    · intro x
      exact pairRowVec_norm hN x
    · intro x
      exact pairRowVec_ne_one hN x
  frame := by
    intro x
    rw [doubledRowPrep_frame (pairRowVec N) (pairClean hN) ?_ x]
    · have hts : (fun p => if p.1 = x then pairRowVec N x p.2 else 0)
          = TensorState (Ket x) (pairRowVec N x) := by
        funext p
        obtain ⟨a, b⟩ := p
        simp [tensorState_apply, Qatlib.Foundations.PureStateMath.Ket]
      rw [hts]
      exact pairRowVec_eq_column hN x
    · intro y
      exact rowHouseholder_frame (pairRowVec N y) (pairClean hN)
        (fun i => pairRowVec_real y i) (pairRowVec_norm hN y) (pairRowVec_ne_one hN y)

/-- For `N` at least three, establishes the pair-graph transition kernel, unitary clean
preparation, Szegedy walk implementation, and four-query and four-gate costs per step. -/
theorem pairFrontier {N : ℕ} (hN : 3 ≤ N) :
    IsTransitionMatrix (regularKernel (pairGraph N) (pairDegree N)) ∧
    ((pairRowAccess hN).prep ∈ Matrix.unitaryGroup (PairVertex N × PairVertex N) ℂ) ∧
    (∀ x, (pairRowAccess hN).prep *ᵥ TensorState (Ket x) (Ket (pairClean hN))
      = SzegedyIsometry (regularKernel (pairGraph N) (pairDegree N)) *ᵥ Ket x) ∧
    (evaluate (pairRowAccess hN).prep (countedSzegedyWord (pairClean hN))
      = SzegedyWalk (regularKernel (pairGraph N) (pairDegree N))) ∧
    (∀ x, (pairRowAccess hN).prepᴴ
        *ᵥ ((pairRowAccess hN).prep *ᵥ TensorState (Ket x) (Ket (pairClean hN)))
      = TensorState (Ket x) (Ket (pairClean hN))) ∧
    adjointQueryCount (countedSzegedyWord (pairClean hN)) = 4 ∧
    adjointGateCount (countedSzegedyWord (pairClean hN)) = 4 ∧
    (∀ m, evaluate (pairRowAccess hN).prep
        ((List.replicate m (countedSzegedyWord (pairClean hN))).flatten)
      = (SzegedyWalk (regularKernel (pairGraph N) (pairDegree N))) ^ m) ∧
    (∀ m, adjointQueryCount
        ((List.replicate m (countedSzegedyWord (pairClean hN))).flatten) = 4 * m) ∧
    (∀ m, adjointGateCount
        ((List.replicate m (countedSzegedyWord (pairClean hN))).flatten) = 4 * m) := by
  have hP := pairGraph_nonLazyKernel_isTransition hN
  refine ⟨hP, (pairRowAccess hN).unitary, (pairRowAccess hN).frame, ?_,
    (fun x => RowAccess.clean_recovery (pairRowAccess hN) x),
    (RowAccess.step_cost (pairClean hN)).1, (RowAccess.step_cost (pairClean hN)).2,
    ?_, ?_, ?_⟩
  · exact RowAccess.prepared_walk (pairRowAccess hN) hP
  · intro m
    exact (RowAccess.repeated_walk (pairRowAccess hN) hP m).1
  · intro m
    exact (RowAccess.repeated_walk (pairRowAccess hN) hP m).2.1
  · intro m
    exact (RowAccess.repeated_walk (pairRowAccess hN) hP m).2.2

end PairPreparation

structure GraphAccessSetupAccount (a : ℕ) (ha : 0 < a) : Prop where

  transition : IsTransitionMatrix (regularKernel (bipartiteGraph a) ((2 ^ (a - 1) : ℕ) : ℝ))

  prep_unitary : bipartitePrep a ∈ Matrix.unitaryGroup (Fin (2 ^ a) × Fin (2 ^ a)) ℂ

  frame : ∀ x : Fin (2 ^ a),
    bipartitePrep a *ᵥ TensorState (Ket x) (Ket (0 : Fin (2 ^ a)))
      = SzegedyIsometry (regularKernel (bipartiteGraph a) ((2 ^ (a - 1) : ℕ) : ℝ)) *ᵥ Ket x

  walk : evaluate (bipartitePrep a)
      (countedSzegedyWord (0 : Fin (2 ^ a)))
    = SzegedyWalk (regularKernel (bipartiteGraph a) ((2 ^ (a - 1) : ℕ) : ℝ))

  clean : ∀ x : Fin (2 ^ a),
    evaluate (1 : Matrix (Fin (2 ^ a) × Fin (2 ^ a)) (Fin (2 ^ a) × Fin (2 ^ a)) ℂ)
        (adjointCircuit (bipartiteSetupWord a))
        *ᵥ (bipartitePrep a *ᵥ TensorState (Ket x) (Ket (0 : Fin (2 ^ a))))
      = TensorState (Ket x) (Ket (0 : Fin (2 ^ a)))

  setup_query : adjointQueryCount (bipartiteSetupWord a) = 0

  setup_gate : adjointGateCount (bipartiteSetupWord a) = a + 1

  setup_inverse_gate : adjointGateCount (adjointCircuit (bipartiteSetupWord a)) = a + 1

  step_query : adjointQueryCount (countedSzegedyWord (0 : Fin (2 ^ a))) = 4

  step_gate : adjointGateCount (countedSzegedyWord (0 : Fin (2 ^ a))) = 4

  check_gate : ((bipartiteCheckBlocks a ha).flatMap blockWord).length = 1

  steps_walk : ∀ m : ℕ,
    evaluate (bipartitePrep a)
        ((List.replicate m (countedSzegedyWord (0 : Fin (2 ^ a)))).flatten)
      = (SzegedyWalk (regularKernel (bipartiteGraph a) ((2 ^ (a - 1) : ℕ) : ℝ))) ^ m

  steps_query : ∀ m : ℕ,
    adjointQueryCount ((List.replicate m (countedSzegedyWord (0 : Fin (2 ^ a)))).flatten)
      = 4 * m

  steps_gate : ∀ m : ℕ,
    adjointGateCount ((List.replicate m (countedSzegedyWord (0 : Fin (2 ^ a)))).flatten)
      = 4 * m

/-- For positive register size, establishes the bipartite graph setup account, including clean
preparation, walk implementation, and setup and repeated-step costs. -/
theorem frontier1 (a : ℕ) (ha : 0 < a) : GraphAccessSetupAccount a ha := by
  have hP := bipartite_nonLazyKernel_isTransition a ha
  obtain ⟨hSq, hSg⟩ := bipartiteSetupWord_cost a ha
  obtain ⟨_, hIg⟩ := bipartiteSetupWord_adjoint_cost a ha
  obtain ⟨hWq, hWg⟩ := RowAccess.step_cost (0 : Fin (2 ^ a))
  refine ⟨hP, bipartitePrep_unitary a ha, bipartitePrep_frame a ha, ?_, ?_,
    hSq, hSg, hIg, hWq, hWg, ?_, ?_, ?_, ?_⟩
  · exact RowAccess.prepared_walk (bipartiteRowAccess a ha) hP
  · intro x
    exact bipartiteSetup_clean_recovery a ha x
  · exact (bipartite_setup_update_check_ledger a ha 0).2.1
  · intro m
    exact (RowAccess.repeated_walk (bipartiteRowAccess a ha) hP m).1
  · intro m
    exact (RowAccess.repeated_walk (bipartiteRowAccess a ha) hP m).2.1
  · intro m
    exact (RowAccess.repeated_walk (bipartiteRowAccess a ha) hP m).2.2

end GraphAccessSetup
end CertifiedStage
end Qatlib.Concepts.QuantumGibbs.FormAlgebra
