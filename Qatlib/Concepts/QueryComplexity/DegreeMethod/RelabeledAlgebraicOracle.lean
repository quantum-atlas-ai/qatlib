/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel
import Qatlib.Concepts.HspRecovery.CyclicRecovery.AlgebraicOracle
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Concepts.HspRecovery.CyclicRecovery

open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Foundations.InstrumentCore.Measurement

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open Matrix

set_option autoImplicit false

variable {I R : Type*}

noncomputable def swappedAddOracleCircuit {I R : Type*}
    [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]
    (A : Matrix I I ℂ) : Circuit (R × I) :=
  relabelCircuit (Equiv.prodComm I R)
    [Step.gate (TensorGate A (1 : Matrix R R ℂ)), Step.query]

noncomputable def swappedAddOracleRun {I R : Type*}
    [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R] [AddCommGroup R]
    (f : I → R) (A : Matrix I I ℂ) (ψ : QState I) : QState (R × I) :=
  Run (relabelGate (Equiv.prodComm I R) (AddOracle f))
    (swappedAddOracleCircuit A)
    (relabelState (Equiv.prodComm I R) (TensorState ψ (Ket 0)))

theorem finset_prodComm_map {I R : Type*} [Fintype I] [DecidableEq I] [Fintype R]
    [DecidableEq R] (T : Finset R) :
    ((Finset.univ : Finset I) ×ˢ T).map (Equiv.prodComm I R).toEmbedding
      = T ×ˢ (Finset.univ : Finset I) := by
  ext p
  rcases p with ⟨z, x⟩
  rw [Finset.mem_map]
  simp only [Finset.mem_product]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨_, hb⟩, h⟩
    have h' : (b, a) = (z, x) := h
    have hbz : b = z := congrArg Prod.fst h'
    subst hbz
    exact ⟨hb, Finset.mem_univ _⟩
  · rintro ⟨hz, _⟩
    exact ⟨(x, z), ⟨Finset.mem_univ _, hz⟩, rfl⟩

theorem swappedAddOracleRun_eq {I R : Type*} [Fintype I] [DecidableEq I] [Fintype R]
    [DecidableEq R] [AddCommGroup R] (f : I → R) (A : Matrix I I ℂ) (ψ : QState I) :
    swappedAddOracleRun f A ψ
      = relabelState (Equiv.prodComm I R)
          (Run (AddOracle f) [Step.gate (TensorGate A (1 : Matrix R R ℂ)), Step.query]
            (TensorState ψ (Ket 0))) :=
  (run_relabelCircuit_readout (Equiv.prodComm I R) (AddOracle f)
    [Step.gate (TensorGate A (1 : Matrix R R ℂ)), Step.query] (TensorState ψ (Ket 0))
    (Finset.univ : Finset (I × R))).1

theorem run_prepare_addOracle {I R : Type*} [Fintype I] [DecidableEq I] [Fintype R]
    [DecidableEq R] [AddCommGroup R] (f : I → R) (A : Matrix I I ℂ) (ψ : QState I) :
    Run (AddOracle f) [Step.gate (TensorGate A (1 : Matrix R R ℂ)), Step.query]
        (TensorState ψ (Ket 0))
      = Run (AddOracle f) [Step.query] (TensorState (ApplyGate A ψ) (Ket 0)) := by
  simp only [run_gate, run_addOracle_query, applyGate_tensorGate, applyGate_one]

theorem run_prepare_addOracle_apply {I R : Type*} [Fintype I] [DecidableEq I] [Fintype R]
    [DecidableEq R] [AddCommGroup R] (f : I → R) (A : Matrix I I ℂ) (ψ : QState I)
    (x : I) (z : R) :
    Run (AddOracle f) [Step.gate (TensorGate A (1 : Matrix R R ℂ)), Step.query]
        (TensorState ψ (Ket 0)) (x, z)
      = if z = f x then ApplyGate A ψ x else 0 := by
  rw [run_prepare_addOracle, run_addOracle_zero_apply]

theorem swappedAddOracleRun_readout {I R : Type*} [Fintype I] [DecidableEq I] [Fintype R]
    [DecidableEq R] [AddCommGroup R] (f : I → R) (A : Matrix I I ℂ) (ψ : QState I)
    (x : I) (z : R) (T : Finset R) :
    swappedAddOracleRun f A ψ (z, x) =
        (if z = f x then ApplyGate A ψ x else 0) ∧
      MarginalProbLeft (swappedAddOracleRun f A ψ) T =
        MeasureProb (ApplyGate A ψ) (Finset.univ.filter fun y => f y ∈ T) := by
  constructor
  · rw [swappedAddOracleRun_eq, relabelState_apply, run_prepare_addOracle,
      run_addOracle_zero_apply]
    simp only [Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap]
  · unfold MarginalProbLeft
    rw [swappedAddOracleRun_eq, run_prepare_addOracle,
      ← finset_prodComm_map (I := I) (R := R) T, measureProb_relabelState]
    exact marginalProbRight_run_addOracle_zero f (ApplyGate A ψ) T

theorem swappedAddOracleRun_resources {I R : Type*} [Fintype I] [DecidableEq I]
    [Fintype R] [DecidableEq R] [AddCommGroup R] (f : I → R) (A : Matrix I I ℂ)
    (ψ : QState I) :
    QueryCount (swappedAddOracleCircuit (R := R) A) = 1 ∧
      GateCount (swappedAddOracleCircuit (R := R) A) = 1 ∧
      Size (swappedAddOracleCircuit (R := R) A) = 2 ∧
      (A ∈ Matrix.unitaryGroup I ℂ →
        IsUnitaryCircuit (swappedAddOracleCircuit (R := R) A)) ∧
      (A ∈ Matrix.unitaryGroup I ℂ → Normalized ψ →
        Normalized (swappedAddOracleRun f A ψ)) := by
  have hcounts := (relabelCircuit_legality_resources (Equiv.prodComm I R)
    [Step.gate (TensorGate A (1 : Matrix R R ℂ)), Step.query]).2
  refine ⟨hcounts.1.trans (by simp [QueryCount]),
    hcounts.2.1.trans (by simp [GateCount]),
    hcounts.2.2.trans (by simp [Size]), ?_, ?_⟩
  · intro hA
    have hleg := (relabelCircuit_legality_resources (Equiv.prodComm I R)
      [Step.gate (TensorGate A (1 : Matrix R R ℂ)), Step.query]).1
    refine hleg.mpr ?_
    rw [isUnitaryCircuit_gate]
    exact ⟨tensorGate_unitary hA (Submonoid.one_mem _), by simp⟩
  · intro hA hψ
    have horacle : relabelGate (Equiv.prodComm I R) (AddOracle f)
        ∈ Matrix.unitaryGroup (R × I) ℂ :=
      (relabelGate_mem_unitaryGroup (Equiv.prodComm I R) (AddOracle f)).2 (addOracle_unitary f)
    have hCleg : IsUnitaryCircuit (swappedAddOracleCircuit (R := R) A) := by
      simp only [swappedAddOracleCircuit, relabelCircuit, List.map_cons, relabelStep]
      rw [isUnitaryCircuit_gate]
      exact ⟨(relabelGate_mem_unitaryGroup (Equiv.prodComm I R)
        (TensorGate A (1 : Matrix R R ℂ))).2 (tensorGate_unitary hA (Submonoid.one_mem _)),
        by simp⟩
    show Normalized (Run (relabelGate (Equiv.prodComm I R) (AddOracle f))
      (swappedAddOracleCircuit (R := R) A)
      (relabelState (Equiv.prodComm I R) (TensorState ψ (Ket 0))))
    exact IsUnitaryCircuit.normalized_run hCleg horacle
      (normalized_relabelState (Equiv.prodComm I R)
        (normalized_tensorState hψ (normalized_ket (0 : R))))

end Qatlib.Concepts.QueryComplexity.DegreeMethod
