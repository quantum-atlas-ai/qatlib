/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.QMAvsQCMA25.Forrelation.PhaseBitCircuitTransportStat
public import Qatlib.Concepts.CompressedQuery.CompressOracle.CompressedOracle

@[expose] public section
open Qatlib.Concepts.CompressedQuery.CompressOracle Qatlib.Concepts.QmaCompleteness.WitnessSampler Qatlib.Concepts.QmaCompleteness.WitnessSampler.SeparatingQMAFromQCMAWithAClassicalOracle2025 Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.QmaCompleteness.WitnessSampler
open Qatlib.Concepts.CompressedQuery.CompressOracle

namespace Qatlib.Papers.QMAvsQCMA25.Forrelation

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Matrix

section G2

variable {n : ℕ}

/-- Applying the Forrelation phase oracle for `S` equals applying its bit oracle between two
Hadamard gates on the `S` control. -/
private theorem applyGate_forrPhaseOracleS (S : Reg n → Bool) (W : Type)
    [Fintype W] [DecidableEq W] (φ : QState (ForrSpace n W)) :
    ApplyGate (forrPhaseOracleS n S W) φ
      = ApplyGate (hadamardSControl n W)
          (ApplyGate (forrBitOracleS n S W)
            (ApplyGate (hadamardSControl n W) φ)) := by
  have h : (controlHadamard (I := Reg n) (W := (Reg n × Bool) × W))
      * workspacePhaseOracle (W := (Reg n × Bool) × W) S
      * controlHadamard (I := Reg n) (W := (Reg n × Bool) × W)
      = workspaceBitOracle (W := (Reg n × Bool) × W) S :=
    controlHadamard_mul_phase_mul_controlHadamard (f := S)
  have hself : (controlHadamard (I := Reg n) (W := (Reg n × Bool) × W))
      * controlHadamard (I := Reg n) (W := (Reg n × Bool) × W) = 1 :=
    controlHadamard_mul_self

  have hrun : ∀ χ : QState (ForrSpace n W),
      ApplyGate (controlHadamard (I := Reg n) (W := (Reg n × Bool) × W))
        (ApplyGate (forrPhaseOracleS n S W)
          (ApplyGate (controlHadamard (I := Reg n) (W := (Reg n × Bool) × W)) χ))
      = ApplyGate (forrBitOracleS n S W) χ := by
    intro χ
    rw [← applyGate_mul, ← applyGate_mul]
    exact congrArg (fun M => ApplyGate M χ) h

  have hH : ∀ χ : QState (ForrSpace n W),
      ApplyGate (controlHadamard (I := Reg n) (W := (Reg n × Bool) × W))
        (ApplyGate (controlHadamard (I := Reg n) (W := (Reg n × Bool) × W)) χ) = χ := by
    intro χ
    rw [← applyGate_mul, hself, applyGate_one]

  have key := hrun (ApplyGate (controlHadamard (I := Reg n) (W := (Reg n × Bool) × W)) φ)
  rw [hH] at key

  have key2 : ApplyGate (controlHadamard (I := Reg n) (W := (Reg n × Bool) × W))
      (ApplyGate (controlHadamard (I := Reg n) (W := (Reg n × Bool) × W))
        (ApplyGate (forrPhaseOracleS n S W) φ))
    = ApplyGate (controlHadamard (I := Reg n) (W := (Reg n × Bool) × W))
        (ApplyGate (forrBitOracleS n S W)
          (ApplyGate (controlHadamard (I := Reg n) (W := (Reg n × Bool) × W)) φ)) :=
    congrArg (ApplyGate (controlHadamard (I := Reg n) (W := (Reg n × Bool) × W))) key
  rw [hH] at key2
  exact key2

/-- Applying the Forrelation phase oracle for `U` equals applying its bit oracle between two
Hadamard gates on the `U` control. -/
private theorem applyGate_forrPhaseOracleU (U : Reg n → Bool) (W : Type)
    [Fintype W] [DecidableEq W] (φ : QState (ForrSpace n W)) :
    ApplyGate (forrPhaseOracleU n U W) φ
      = ApplyGate (hadamardUControl n W)
          (ApplyGate (forrBitOracleU n U W)
            (ApplyGate (hadamardUControl n W) φ)) := by
  have h : (controlHadamard (I := Reg n) (W := W))
      * workspacePhaseOracle (W := W) U
      * controlHadamard (I := Reg n) (W := W)
      = workspaceBitOracle (W := W) U :=
    controlHadamard_mul_phase_mul_controlHadamard (f := U)
  have hself : (controlHadamard (I := Reg n) (W := W))
      * controlHadamard (I := Reg n) (W := W) = 1 :=
    controlHadamard_mul_self

  have hT : ∀ χ : QState (ForrSpace n W),
      ApplyGate (TensorGate (1 : Matrix (Reg n × Bool) (Reg n × Bool) ℂ)
          (controlHadamard (I := Reg n) (W := W)))
        (ApplyGate (TensorGate (1 : Matrix (Reg n × Bool) (Reg n × Bool) ℂ)
            (workspacePhaseOracle (W := W) U))
          (ApplyGate (TensorGate (1 : Matrix (Reg n × Bool) (Reg n × Bool) ℂ)
              (controlHadamard (I := Reg n) (W := W))) χ))
      = ApplyGate (TensorGate (1 : Matrix (Reg n × Bool) (Reg n × Bool) ℂ)
          (workspaceBitOracle (W := W) U)) χ := by
    intro χ
    rw [← applyGate_mul, ← applyGate_mul]
    rw [tensorGate_mul, tensorGate_mul, Matrix.one_mul, Matrix.one_mul]
    exact congrArg
        (fun M => ApplyGate (TensorGate (1 : Matrix (Reg n × Bool) (Reg n × Bool) ℂ) M) χ) h
  have hH : ∀ χ : QState (ForrSpace n W),
      ApplyGate (TensorGate (1 : Matrix (Reg n × Bool) (Reg n × Bool) ℂ)
          (controlHadamard (I := Reg n) (W := W)))
        (ApplyGate (TensorGate (1 : Matrix (Reg n × Bool) (Reg n × Bool) ℂ)
            (controlHadamard (I := Reg n) (W := W))) χ) = χ := by
    intro χ
    rw [← applyGate_mul, tensorGate_mul, Matrix.one_mul, hself, tensorGate_one, applyGate_one]
  have key := hT (ApplyGate (TensorGate (1 : Matrix (Reg n × Bool) (Reg n × Bool) ℂ)
      (controlHadamard (I := Reg n) (W := W))) φ)
  rw [hH] at key
  have key2 : ApplyGate (TensorGate (1 : Matrix (Reg n × Bool) (Reg n × Bool) ℂ)
        (controlHadamard (I := Reg n) (W := W)))
      (ApplyGate (TensorGate (1 : Matrix (Reg n × Bool) (Reg n × Bool) ℂ)
          (controlHadamard (I := Reg n) (W := W)))
        (ApplyGate (forrPhaseOracleU n U W) φ))
    = ApplyGate (TensorGate (1 : Matrix (Reg n × Bool) (Reg n × Bool) ℂ)
        (controlHadamard (I := Reg n) (W := W)))
      (ApplyGate (forrBitOracleU n U W)
        (ApplyGate (TensorGate (1 : Matrix (Reg n × Bool) (Reg n × Bool) ℂ)
            (controlHadamard (I := Reg n) (W := W))) φ)) :=
    congrArg (ApplyGate (TensorGate (1 : Matrix (Reg n × Bool) (Reg n × Bool) ℂ)
      (controlHadamard (I := Reg n) (W := W)))) key
  rw [hH] at key2
  exact key2

/-- Phase-to-bit circuit transport preserves the number of `S` queries. -/
private theorem transport_queryCountS {I : Type} (hS hU : Matrix I I ℂ) :
    ∀ C : TOCircuit I, TOQueryCountS (transportPhaseToBit hS hU C) = TOQueryCountS C
  | [] => rfl
  | TOStep.gate G :: C => by
      show TOQueryCountS (transportPhaseToBit hS hU C) = TOQueryCountS C
      exact transport_queryCountS hS hU C
  | TOStep.queryS :: C => by
      show TOQueryCountS (transportPhaseToBit hS hU C) + 1 = TOQueryCountS C + 1
      rw [transport_queryCountS hS hU C]
  | TOStep.queryU :: C => by
      show TOQueryCountS (transportPhaseToBit hS hU C) = TOQueryCountS C
      exact transport_queryCountS hS hU C

/-- Phase-to-bit circuit transport preserves the number of `U` queries. -/
private theorem transport_queryCountU {I : Type} (hS hU : Matrix I I ℂ) :
    ∀ C : TOCircuit I, TOQueryCountU (transportPhaseToBit hS hU C) = TOQueryCountU C
  | [] => rfl
  | TOStep.gate G :: C => by
      show TOQueryCountU (transportPhaseToBit hS hU C) = TOQueryCountU C
      exact transport_queryCountU hS hU C
  | TOStep.queryS :: C => by
      show TOQueryCountU (transportPhaseToBit hS hU C) = TOQueryCountU C
      exact transport_queryCountU hS hU C
  | TOStep.queryU :: C => by
      show TOQueryCountU (transportPhaseToBit hS hU C) + 1 = TOQueryCountU C + 1
      rw [transport_queryCountU hS hU C]

/-- The Hadamard gate on the `S` control is unitary. -/
private theorem hadamardSControl_unitary (W : Type) [Fintype W] [DecidableEq W] :
    hadamardSControl n W ∈ Matrix.unitaryGroup (ForrSpace n W) ℂ := by
  unfold hadamardSControl
  exact tensorGate_unitary (tensorGate_unitary (Submonoid.one_mem _) hadamard_unitary)
    (Submonoid.one_mem _)

/-- The Hadamard gate on the `U` control is unitary. -/
private theorem hadamardUControl_unitary (W : Type) [Fintype W] [DecidableEq W] :
    hadamardUControl n W ∈ Matrix.unitaryGroup (ForrSpace n W) ℂ := by
  unfold hadamardUControl
  exact tensorGate_unitary (Submonoid.one_mem _)
    (tensorGate_unitary (tensorGate_unitary (Submonoid.one_mem _) hadamard_unitary)
      (Submonoid.one_mem _))

/-- Phase-to-bit transport with unitary inserted gates preserves circuit unitarity. -/
private theorem transport_isUnitary {I : Type} [Fintype I] [DecidableEq I]
    (hS hU : Matrix I I ℂ)
    (hSunit : hS ∈ Matrix.unitaryGroup I ℂ) (hUunit : hU ∈ Matrix.unitaryGroup I ℂ) :
    ∀ C : TOCircuit I, IsUnitaryTOCircuit C → IsUnitaryTOCircuit (transportPhaseToBit hS hU C)
  | [], _ => by
      intro G hG
      cases hG
  | TOStep.gate G :: C, h => by
      intro G' hG'
      have hmem : G' = G ∨ TOStep.gate G' ∈ transportPhaseToBit hS hU C := by
        simpa [transportPhaseToBit] using hG'
      rcases hmem with rfl | hmem
      · exact h _ (by simp)
      · exact transport_isUnitary hS hU hSunit hUunit C
          (fun U hU' => h U (List.mem_cons_of_mem _ hU')) G' hmem
  | TOStep.queryS :: C, h => by
      intro G' hG'
      have hmem : G' = hS ∨ G' = hS ∨ TOStep.gate G' ∈ transportPhaseToBit hS hU C := by
        simpa [transportPhaseToBit] using hG'
      rcases hmem with rfl | rfl | hmem
      · exact hSunit
      · exact hSunit
      · exact transport_isUnitary hS hU hSunit hUunit C
          (fun U hU' => h U (List.mem_cons_of_mem _ hU')) G' hmem
  | TOStep.queryU :: C, h => by
      intro G' hG'
      have hmem : G' = hU ∨ G' = hU ∨ TOStep.gate G' ∈ transportPhaseToBit hS hU C := by
        simpa [transportPhaseToBit] using hG'
      rcases hmem with rfl | rfl | hmem
      · exact hUunit
      · exact hUunit
      · exact transport_isUnitary hS hU hSunit hUunit C
          (fun U hU' => h U (List.mem_cons_of_mem _ hU')) G' hmem

/-- Running a circuit with the Forrelation phase oracles equals running its Hadamard-transported
circuit with the corresponding bit oracles. -/
private theorem run_transport (S U : Reg n → Bool) (W : Type) [Fintype W] [DecidableEq W]
    (C : TOCircuit (ForrSpace n W)) (ψ : QState (ForrSpace n W)) :
    TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C ψ
      = TORun (forrBitOracleS n S W) (forrBitOracleU n U W)
          (transportPhaseToBit (hadamardSControl n W) (hadamardUControl n W) C) ψ := by
  induction C generalizing ψ with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate G =>
      show TORun _ _ C (ApplyGate G ψ) = TORun _ _ (transportPhaseToBit _ _ C) (ApplyGate G ψ)
      exact ih _
    | queryS =>
      show TORun _ _ C (ApplyGate (forrPhaseOracleS n S W) ψ)
        = TORun _ _ (transportPhaseToBit _ _ C)
            (ApplyGate (hadamardSControl n W)
              (ApplyGate (forrBitOracleS n S W)
                (ApplyGate (hadamardSControl n W) ψ)))
      rw [applyGate_forrPhaseOracleS]
      exact ih _
    | queryU =>
      show TORun _ _ C (ApplyGate (forrPhaseOracleU n U W) ψ)
        = TORun _ _ (transportPhaseToBit _ _ C)
            (ApplyGate (hadamardUControl n W)
              (ApplyGate (forrBitOracleU n U W)
                (ApplyGate (hadamardUControl n W) ψ)))
      rw [applyGate_forrPhaseOracleU]
      exact ih _

/-- Phase-to-bit circuit transport preserves all event probabilities and both oracle query
counts, and preserves circuit unitarity. -/
theorem phaseBitCircuitTransport : PhaseBitCircuitTransport := by
  intro n W _ _ S U C ψ E
  have hrun := run_transport S U W C ψ
  have hS := transport_queryCountS (hadamardSControl n W) (hadamardUControl n W) C
  have hU := transport_queryCountU (hadamardSControl n W) (hadamardUControl n W) C
  have hunit : IsUnitaryTOCircuit C →
      IsUnitaryTOCircuit (transportPhaseToBit (hadamardSControl n W) (hadamardUControl n W) C) :=
    transport_isUnitary (hadamardSControl n W) (hadamardUControl n W)
      (hadamardSControl_unitary W) (hadamardUControl_unitary W) C
  refine ⟨?_, hS, hU, hunit⟩
  rw [hrun]

end G2

end Qatlib.Papers.QMAvsQCMA25.Forrelation
