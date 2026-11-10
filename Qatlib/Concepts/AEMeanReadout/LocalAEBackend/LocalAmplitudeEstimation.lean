/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.LocalOffGridReadout
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeCountingConsumers
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.QftPreparation.LocalQFTImplementation

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend

open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

open scoped Classical Matrix.Norms.L2Operator

set_option autoImplicit false
set_option linter.unusedVariables false

variable {I : Type} [Fintype I] [DecidableEq I]

theorem two_le_two_pow {n : ℕ} (hn : 1 ≤ n) : 2 ≤ 2^n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.pow_add, Nat.pow_one]
  calc (2 : ℕ) = 2*1 := by ring
    _ ≤ 2*2^k := Nat.mul_le_mul le_rfl Nat.one_le_two_pow

theorem two_pow_real_eq_cast (n : ℕ) : (2^n : ℝ) = ((2^n : ℕ) : ℝ) := by
  rw [Nat.cast_pow, Nat.cast_ofNat]

omit [Fintype I] [DecidableEq I] in

theorem relabelGate_sub {J : Type*} [Fintype J] [DecidableEq J] (e : I ≃ J)
    (A B : Matrix I I ℂ) : relabelGate e A - relabelGate e B = relabelGate e (A - B) := by
  ext i j
  simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sub_apply]

theorem relabelGate_roundtrip (n : ℕ) (U : Matrix (Fin (2^n)) (Fin (2^n)) ℂ) :
    relabelGate (bitVecEquiv n) (relabelGate (bitVecEquiv n).symm U) = U := by
  have h := relabelGate_relabelGate (bitVecEquiv n).symm U
  rwa [Equiv.symm_symm] at h

theorem measureProb_ideal_eq_aeLaw_sum (M : ℕ) (hM : 0 < M) (hM2 : 2 ≤ M)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (P : Fin M → Prop) :
    MeasureProb (phaseFlagEmbed M (qpeOutput M (preparedAAIterate A j S) (preparedAAState A j)))
      (Finset.univ.filter (fun p : Fin M × (Bool × I) => P p.1))
      = ∑ z ∈ Finset.univ.filter P, (aeLaw M A j S hA hM2).prob z := by
  have h1 : MeasureProb (phaseFlagEmbed M (qpeOutput M (preparedAAIterate A j S)
          (preparedAAState A j)))
      (Finset.univ.filter (fun p : Fin M × (Bool × I) => P p.1))
      = MeasureProb (Run (aeControlledGate M (preparedMark S)) (countedAECircuit M A j)
          (TensorState (Ket (⟨0, hM⟩ : Fin M)) (TensorState (Ket false) (Ket j))))
        (Finset.univ.filter (fun p : Fin M × (Bool × I) => P p.1)) :=
    congrArg (fun v => MeasureProb v (Finset.univ.filter
      (fun p : Fin M × (Bool × I) => P p.1))) (countedAE_output M hM A j S).symm
  rw [h1]
  exact (aeLaw_event M hM2 A j S hA P).symm

noncomputable def localAEGateMatrix (n : ℕ) (g : LocalQFTGate n) :
    Matrix (Fin (2^n) × (Bool × I)) (Fin (2^n) × (Bool × I)) ℂ :=
  TensorGate (relabelGate (bitVecEquiv n) (localGateMatrix g))
    (1 : Matrix (Bool × I) (Bool × I) ℂ)

theorem localAEGateMatrix_unitary (n : ℕ) (g : LocalQFTGate n) :
    localAEGateMatrix (I := I) n g ∈ Matrix.unitaryGroup (Fin (2^n) × (Bool × I)) ℂ :=
  tensorGate_unitary
    ((relabelGate_mem_unitaryGroup (bitVecEquiv n) (localGateMatrix g)).mpr
      (localGateMatrix_unitary g)) (Matrix.unitaryGroup (Bool × I) ℂ).one_mem

noncomputable def localAETableCircuit (n : ℕ) (gs : List (LocalQFTGate n)) :
    Circuit (Fin (2^n) × (Bool × I)) :=
  gs.map fun g => Step.gate (localAEGateMatrix (I := I) n g)

theorem localAETableCircuit_isUnitary (n : ℕ) (gs : List (LocalQFTGate n)) :
    IsUnitaryCircuit (localAETableCircuit n gs :
      Circuit (Fin (2^n) × (Bool × I))) := by
  induction gs with
  | nil => exact isUnitaryCircuit_nil
  | cons g gs ih =>
      exact (isUnitaryCircuit_gate _ _).mpr ⟨localAEGateMatrix_unitary n g, ih⟩

omit [Fintype I] in

theorem localAETableCircuit_counts (n : ℕ) (gs : List (LocalQFTGate n)) :
    QueryCount (localAETableCircuit n gs : Circuit (Fin (2^n) × (Bool × I))) = 0 ∧
    GateCount (localAETableCircuit n gs : Circuit (Fin (2^n) × (Bool × I)))
      = gs.length := by
  induction gs with
  | nil => exact ⟨rfl, rfl⟩
  | cons g gs ih => exact ⟨ih.1, congrArg (fun x => x + 1) ih.2⟩

noncomputable def localAEBackendMatrix (n : ℕ) (gs : List (LocalQFTGate n)) :
    Matrix (Fin (2^n) × (Bool × I)) (Fin (2^n) × (Bool × I)) ℂ :=
  TensorGate (relabelGate (bitVecEquiv n) (localProgramMatrix gs))
    (1 : Matrix (Bool × I) (Bool × I) ℂ)

theorem localAETableCircuit_run (n : ℕ) (gs : List (LocalQFTGate n))
    (O : Matrix (Fin (2^n) × (Bool × I)) (Fin (2^n) × (Bool × I)) ℂ)
    (ψ : QState (Fin (2^n) × (Bool × I))) :
    Run O (localAETableCircuit n gs) ψ = ApplyGate (localAEBackendMatrix n gs) ψ := by
  induction gs generalizing ψ with
  | nil =>
      show ψ = ApplyGate (TensorGate (relabelGate (bitVecEquiv n) 1)
        (1 : Matrix (Bool × I) (Bool × I) ℂ)) ψ
      rw [CircuitRelabel.relabelGate_one, tensorGate_one, applyGate_one]
  | cons g gs ih =>
      show Run O (Step.gate (localAEGateMatrix n g) :: localAETableCircuit n gs) ψ = _
      rw [run_gate, ih, ← applyGate_mul]
      congr 1
      show localAEBackendMatrix n gs * localAEGateMatrix n g
          = localAEBackendMatrix n (g :: gs)
      simp only [localAEBackendMatrix, localAEGateMatrix, localProgramMatrix_cons]
      rw [tensorGate_mul, CircuitRelabel.relabelGate_mul, one_mul]

theorem localAEBackend_error (n b : ℕ) :
    ‖localAEBackendMatrix (I := I) n (approxLocalQFT n b)
        - TensorGate (QFTMatrix (2^n)) (1 : Matrix (Bool × I) (Bool × I) ℂ)‖
      ≤ Real.pi*(n:ℝ)/2^(b+1) ∧
    ‖localAEBackendMatrix (I := I) n (localProgramAdjoint (approxLocalQFT n b))
        - TensorGate (QFTMatrix (2^n))ᴴ (1 : Matrix (Bool × I) (Bool × I) ℂ)‖
      ≤ Real.pi*(n:ℝ)/2^(b+1) := by
  obtain ⟨herrF, herrB⟩ := approxLocalQFT_operator_error n b
  have hone : ‖(1 : Matrix (Bool × I) (Bool × I) ℂ)‖ ≤ 1 :=
    l2_norm_one_le (I := Bool × I)
  have hkey : ∀ (X : Matrix (Reg n) (Reg n) ℂ) (Y : Matrix (Fin (2^n)) (Fin (2^n)) ℂ),
      ‖TensorGate (relabelGate (bitVecEquiv n) X - Y)
          (1 : Matrix (Bool × I) (Bool × I) ℂ)‖
        ≤ ‖X - relabelGate (bitVecEquiv n).symm Y‖ := by
    intro X Y
    rw [show relabelGate (bitVecEquiv n) X - Y
          = relabelGate (bitVecEquiv n) (X - relabelGate (bitVecEquiv n).symm Y) from by
        rw [← relabelGate_sub, relabelGate_roundtrip]]
    calc ‖TensorGate (relabelGate (bitVecEquiv n) (X - relabelGate (bitVecEquiv n).symm Y))
          (1 : Matrix (Bool × I) (Bool × I) ℂ)‖
        = ‖X - relabelGate (bitVecEquiv n).symm Y‖
            * ‖(1 : Matrix (Bool × I) (Bool × I) ℂ)‖ := by
          rw [l2_norm_tensorGate, l2_norm_relabelGate]
      _ ≤ ‖X - relabelGate (bitVecEquiv n).symm Y‖ * 1 :=
          mul_le_mul_of_nonneg_left hone (norm_nonneg _)
      _ = ‖X - relabelGate (bitVecEquiv n).symm Y‖ := mul_one _
  constructor
  · rw [localAEBackendMatrix, tensorGate_sub_left]
    exact (hkey (localProgramMatrix (approxLocalQFT n b)) (QFTMatrix (2^n))).trans herrF
  · rw [localAEBackendMatrix, tensorGate_sub_left]
    refine (hkey (localProgramMatrix (localProgramAdjoint (approxLocalQFT n b)))
      (QFTMatrix (2^n))ᴴ).trans ?_
    rw [← relabelGate_conjTranspose]
    exact herrB

noncomputable def localAEForwardCircuit (n b : ℕ) :
    Circuit (Fin (2^n) × (Bool × I)) :=
  localAETableCircuit n (approxLocalQFT n b)

noncomputable def localAEBackwardCircuit (n b : ℕ) :
    Circuit (Fin (2^n) × (Bool × I)) :=
  localAETableCircuit n (localProgramAdjoint (approxLocalQFT n b))

def localAEFourierGates (n b : ℕ) : ℕ := 2 * (approxLocalQFT n b).length

noncomputable def localAEFlagWord (M : ℕ) (A : Matrix I I ℂ) (j : I) :
    Circuit (Fin M × (Bool × I)) :=
  (aeFlagAccessWord (I := I) M).map (aeAccessInstruction M A j)

omit [Fintype I] in

theorem countedAECircuit_split (M : ℕ) (A : Matrix I I ℂ) (j : I) :
    countedAECircuit M A j =
      [Step.gate (TensorGate (1 : Matrix (Fin M) (Fin M) ℂ)
        (TensorGate (1 : Matrix Bool Bool ℂ) A))]
      ++ [Step.gate (TensorGate (QFTMatrix M) (1 : Matrix (Bool × I) (Bool × I) ℂ))]
      ++ localAEFlagWord M A j
      ++ [Step.gate (TensorGate (QFTMatrix M)ᴴ (1 : Matrix (Bool × I) (Bool × I) ℂ))] := by
  rw [countedAECircuit, aeAccessWord_split]
  simp only [List.map_cons, List.map_append, aeAccessInstruction]
  rfl

theorem localAEFlagWord_counts (M : ℕ) (hM : 0 < M) (A : Matrix I I ℂ) (j : I) :
    QueryCount (localAEFlagWord M A j) = M - 1 ∧
    GateCount (localAEFlagWord M A j) = 5*(M-1) := by
  have hledger := prepared_ae_access_ledger M hM A j
  rw [countedAECircuit_split] at hledger
  obtain ⟨h1, h2, -, -⟩ := hledger
  simp only [queryCount_append, queryCount_gate, queryCount_nil, Nat.zero_add] at h1
  simp only [gateCount_append, gateCount_gate, gateCount_nil, Nat.zero_add] at h2
  omega

noncomputable def localAECircuit (n b : ℕ) (A : Matrix I I ℂ) (j : I) :
    Circuit (Fin (2^n) × (Bool × I)) :=
  [Step.gate (TensorGate (1 : Matrix (Fin (2^n)) (Fin (2^n)) ℂ)
    (TensorGate (1 : Matrix Bool Bool ℂ) A))]
  ++ localAEForwardCircuit n b
  ++ localAEFlagWord (2^n) A j
  ++ localAEBackwardCircuit n b

noncomputable def localAEState (n b : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I) :
    QState (Fin (2^n) × (Bool × I)) :=
  Run (aeControlledGate (2^n) (preparedMark S)) (localAECircuit n b A j)
    (TensorState (Ket (⟨0, by positivity⟩ : Fin (2^n))) (TensorState (Ket false) (Ket j)))

theorem localAECircuit_run_any (n b : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (ψ : QState (Fin (2^n) × (Bool × I))) :
    Run (aeControlledGate (2^n) (preparedMark S)) (localAECircuit n b A j) ψ
      = ApplyGate (localAEBackendMatrix n (localProgramAdjoint (approxLocalQFT n b)))
        (Run (aeControlledGate (2^n) (preparedMark S)) (localAEFlagWord (2^n) A j)
          (ApplyGate (localAEBackendMatrix n (approxLocalQFT n b))
            (ApplyGate (TensorGate (1 : Matrix (Fin (2^n)) (Fin (2^n)) ℂ)
              (TensorGate (1 : Matrix Bool Bool ℂ) A)) ψ))) := by
  show Run _ ([Step.gate (TensorGate (1 : Matrix (Fin (2^n)) (Fin (2^n)) ℂ)
      (TensorGate (1 : Matrix Bool Bool ℂ) A))]
    ++ localAEForwardCircuit n b ++ localAEFlagWord (2^n) A j
    ++ localAEBackwardCircuit n b) ψ = _
  rw [run_append, run_append, run_append]
  simp only [run_gate, run_nil]
  rw [localAEForwardCircuit, localAETableCircuit_run, localAEBackwardCircuit,
    localAETableCircuit_run]

theorem countedAECircuit_run_any (M : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (ψ : QState (Fin M × (Bool × I))) :
    Run (aeControlledGate M (preparedMark S)) (countedAECircuit M A j) ψ
      = ApplyGate (TensorGate (QFTMatrix M)ᴴ (1 : Matrix (Bool × I) (Bool × I) ℂ))
        (Run (aeControlledGate M (preparedMark S)) (localAEFlagWord M A j)
          (ApplyGate (TensorGate (QFTMatrix M) (1 : Matrix (Bool × I) (Bool × I) ℂ))
            (ApplyGate (TensorGate (1 : Matrix (Fin M) (Fin M) ℂ)
              (TensorGate (1 : Matrix Bool Bool ℂ) A)) ψ))) := by
  rw [countedAECircuit_split, run_append, run_append, run_append]
  simp only [run_gate, run_nil]

theorem localAE_state_diff (n b : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hM : 0 < 2^n) :
    localAEState n b A j S
        - phaseFlagEmbed (2^n) (qpeOutput (2^n) (preparedAAIterate A j S)
            (preparedAAState A j))
      = ApplyGate (localAEBackendMatrix n (localProgramAdjoint (approxLocalQFT n b)))
          (Run (aeControlledGate (2^n) (preparedMark S)) (localAEFlagWord (2^n) A j)
            (ApplyGate (localAEBackendMatrix n (approxLocalQFT n b))
              (ApplyGate (TensorGate (1 : Matrix (Fin (2^n)) (Fin (2^n)) ℂ)
                (TensorGate (1 : Matrix Bool Bool ℂ) A))
                (TensorState (Ket (⟨0, hM⟩ : Fin (2^n)))
                  (TensorState (Ket false) (Ket j))))))
        - ApplyGate (TensorGate (QFTMatrix (2^n))ᴴ (1 : Matrix (Bool × I) (Bool × I) ℂ))
          (Run (aeControlledGate (2^n) (preparedMark S)) (localAEFlagWord (2^n) A j)
            (ApplyGate (TensorGate (QFTMatrix (2^n)) (1 : Matrix (Bool × I) (Bool × I) ℂ))
              (ApplyGate (TensorGate (1 : Matrix (Fin (2^n)) (Fin (2^n)) ℂ)
                (TensorGate (1 : Matrix Bool Bool ℂ) A))
                (TensorState (Ket (⟨0, hM⟩ : Fin (2^n)))
                  (TensorState (Ket false) (Ket j)))))) := by
  rw [localAEState, show phaseFlagEmbed (2^n) (qpeOutput (2^n) (preparedAAIterate A j S)
        (preparedAAState A j))
      = Run (aeControlledGate (2^n) (preparedMark S)) (countedAECircuit (2^n) A j)
        (TensorState (Ket (⟨0, hM⟩ : Fin (2^n))) (TensorState (Ket false) (Ket j))) from
    (countedAE_output (2^n) hM A j S).symm,
    localAECircuit_run_any, countedAECircuit_run_any]

theorem local_ae_actual_compilation_resources (n b : ℕ) (hn : 1 ≤ n)
    (A : Matrix I I ℂ) (j : I) :
    QueryCount (localAECircuit n b A j) = 2^n - 1 ∧
    GateCount (localAECircuit n b A j) = 5*(2^n-1)+1+localAEFourierGates n b ∧
    localAEFourierGates n b = 2*(approxLocalQFT n b).length ∧
    localAEFourierGates n b ≤ 2*(n+n*(b+1)+n/2) := by
  have hM : 0 < 2^n := by positivity
  have hflag := localAEFlagWord_counts (2^n) hM A j
  have hfwdc := localAETableCircuit_counts (I := I) n (approxLocalQFT n b)
  have hbwdc := localAETableCircuit_counts (I := I)
    n (localProgramAdjoint (approxLocalQFT n b))
  have hlen : (localProgramAdjoint (approxLocalQFT n b)).length
      = (approxLocalQFT n b).length := by simp [localProgramAdjoint]
  have hbwdl : GateCount (localAETableCircuit n (localProgramAdjoint (approxLocalQFT n b))) =
      (approxLocalQFT n b).length := hbwdc.2.trans hlen
  have hfour : localAEFourierGates n b = 2*(approxLocalQFT n b).length := rfl
  show QueryCount (([Step.gate (TensorGate (1 : Matrix (Fin (2^n)) (Fin (2^n)) ℂ)
      (TensorGate (1 : Matrix Bool Bool ℂ) A))]
    ++ localAETableCircuit n (approxLocalQFT n b) ++ localAEFlagWord (2^n) A j
    ++ localAETableCircuit n (localProgramAdjoint (approxLocalQFT n b)) :
      Circuit (Fin (2^n) × (Bool × I)))) = _ ∧
    GateCount (([Step.gate (TensorGate (1 : Matrix (Fin (2^n)) (Fin (2^n)) ℂ)
      (TensorGate (1 : Matrix Bool Bool ℂ) A))]
    ++ localAETableCircuit n (approxLocalQFT n b) ++ localAEFlagWord (2^n) A j
    ++ localAETableCircuit n (localProgramAdjoint (approxLocalQFT n b)) :
      Circuit (Fin (2^n) × (Bool × I)))) = _ ∧ _ ∧ _
  rw [queryCount_append, queryCount_append, queryCount_append, gateCount_append,
    gateCount_append, gateCount_append]
  simp only [queryCount_gate, queryCount_nil, gateCount_gate, gateCount_nil,
    Nat.zero_add]
  refine ⟨by omega, by omega, rfl, ?_⟩
  show 2*(approxLocalQFT n b).length ≤ 2*(n+n*(b+1)+n/2)
  have hgc := (localDyadicProgram_run_adjoint_cost n (approxLocalQFT n b)
    (Ket (ZeroStr n))).2.2.2.2.2.2.1
  have hbound := (approxLocalQFT_actual_filter_and_cost n b).2.2.2.1
  exact Nat.mul_le_mul (le_refl 2) (hgc.symm.trans_le hbound)

theorem localAEFlagWord_isUnitary (n : ℕ) (hn : 1 ≤ n) (A : Matrix I I ℂ) (j : I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    IsUnitaryCircuit (localAEFlagWord (2^n) A j :
      Circuit (Fin (2^n) × (Bool × I))) := by
  intro U hU
  refine (prepared_ae_expanded_access_and_output (2^n) (two_le_two_pow hn) A j ∅
    hA).2.2.1 U ?_
  rw [countedAECircuit_split, List.mem_append, List.mem_append, List.mem_append]
  tauto

theorem localAECircuit_isUnitary (n b : ℕ) (hn : 1 ≤ n) (A : Matrix I I ℂ) (j : I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    IsUnitaryCircuit (localAECircuit n b A j :
      Circuit (Fin (2^n) × (Bool × I))) := by
  have h1 : IsUnitaryCircuit [Step.gate (TensorGate (1 : Matrix (Fin (2^n)) (Fin (2^n)) ℂ)
      (TensorGate (1 : Matrix Bool Bool ℂ) A))] :=
    (isUnitaryCircuit_gate _ _).mpr
      ⟨tensorGate_unitary (Matrix.unitaryGroup (Fin (2^n)) ℂ).one_mem
        (tensorGate_unitary (Matrix.unitaryGroup Bool ℂ).one_mem hA),
        isUnitaryCircuit_nil⟩
  have h2 : IsUnitaryCircuit (localAEForwardCircuit n b :
      Circuit (Fin (2^n) × (Bool × I))) :=
    localAETableCircuit_isUnitary n (approxLocalQFT n b)
  have h3 := localAEFlagWord_isUnitary n hn A j hA
  have h4 : IsUnitaryCircuit (localAEBackwardCircuit n b :
      Circuit (Fin (2^n) × (Bool × I))) :=
    localAETableCircuit_isUnitary n (localProgramAdjoint (approxLocalQFT n b))
  exact (isUnitaryCircuit_append _ _).mpr ⟨(isUnitaryCircuit_append _ _).mpr ⟨
    (isUnitaryCircuit_append _ _).mpr ⟨h1, h2⟩, h3⟩, h4⟩

theorem local_backend_output_error {J : Type*} [Fintype J] [DecidableEq J]
    (O F T F' T' : Matrix J J ℂ) (W : Circuit J) (x₀ : QState J)
    (hO : O ∈ Matrix.unitaryGroup J ℂ) (hW : IsUnitaryCircuit W)
    (hF' : F' ∈ Matrix.unitaryGroup J ℂ) (hT : T ∈ Matrix.unitaryGroup J ℂ)
    (hnorm : Normalized x₀) :
    ‖toEuclidean_fromVec (ApplyGate T' (Run O W (ApplyGate T x₀))
        - ApplyGate F' (Run O W (ApplyGate F x₀)))‖
      ≤ ‖T - F‖ + ‖T' - F'‖ := by
  have h1 : ‖toEuclidean_fromVec (ApplyGate T x₀ - ApplyGate F x₀)‖ ≤ ‖T - F‖ := by
    have hsub : ApplyGate T x₀ - ApplyGate F x₀ = ApplyGate (T - F) x₀ := by
      show T *ᵥ x₀ - F *ᵥ x₀ = (T - F) *ᵥ x₀
      rw [Matrix.sub_mulVec]
    rw [hsub]
    calc ‖toEuclidean_fromVec (ApplyGate (T - F) x₀)‖
        ≤ ‖T - F‖ * ‖toEuclidean_fromVec x₀‖ := norm_applyGate_le _ _
      _ = ‖T - F‖ := by
          rw [(normalized_iff_norm_toEuclidean_fromVec x₀).mp hnorm, mul_one]
  have hTn : Normalized (ApplyGate T x₀) := normalized_applyGate hT hnorm
  have hmid : ‖toEuclidean_fromVec (Run O W (ApplyGate T x₀)
        - Run O W (ApplyGate F x₀))‖ ≤ ‖T - F‖ := by
    rw [← run_sub O W (ApplyGate T x₀) (ApplyGate F x₀)]
    exact (norm_run_le O hO hW _).trans h1
  have h2 : ‖toEuclidean_fromVec (ApplyGate (T' - F')
        (Run O W (ApplyGate T x₀)))‖ ≤ ‖T' - F'‖ := by
    calc ‖toEuclidean_fromVec (ApplyGate (T' - F') (Run O W (ApplyGate T x₀)))‖
        ≤ ‖T' - F'‖ * ‖toEuclidean_fromVec (Run O W (ApplyGate T x₀))‖ :=
          norm_applyGate_le _ _
      _ = ‖T' - F'‖ * 1 := by
          rw [(normalized_iff_norm_toEuclidean_fromVec (Run O W (ApplyGate T x₀))).mp
            (hW.normalized_run hO hTn)]
      _ = ‖T' - F'‖ := mul_one _
  have hsplit : ApplyGate T' (Run O W (ApplyGate T x₀))
        - ApplyGate F' (Run O W (ApplyGate F x₀))
      = ApplyGate F' (Run O W (ApplyGate T x₀) - Run O W (ApplyGate F x₀))
        + ApplyGate (T' - F') (Run O W (ApplyGate T x₀)) := by
    show T' *ᵥ (Run O W (T *ᵥ x₀)) - F' *ᵥ (Run O W (F *ᵥ x₀))
        = F' *ᵥ (Run O W (T *ᵥ x₀) - Run O W (F *ᵥ x₀))
          + (T' - F') *ᵥ (Run O W (T *ᵥ x₀))
    rw [Matrix.mulVec_sub, Matrix.sub_mulVec]
    abel
  rw [hsplit]
  have hsum := norm_add_le (toEuclidean_fromVec (ApplyGate F'
    (Run O W (ApplyGate T x₀) - Run O W (ApplyGate F x₀))))
    (toEuclidean_fromVec (ApplyGate (T' - F') (Run O W (ApplyGate T x₀))))
  rw [show toEuclidean_fromVec (ApplyGate F' (Run O W (ApplyGate T x₀)
        - Run O W (ApplyGate F x₀)))
      + toEuclidean_fromVec (ApplyGate (T' - F') (Run O W (ApplyGate T x₀)))
      = toEuclidean_fromVec (ApplyGate F' (Run O W (ApplyGate T x₀)
          - Run O W (ApplyGate F x₀))
        + ApplyGate (T' - F') (Run O W (ApplyGate T x₀))) from rfl] at hsum
  rw [norm_applyGate_of_mem_unitaryGroup hF'] at hsum
  exact hsum.trans (add_le_add hmid h2)

set_option maxHeartbeats 1000000 in

theorem local_ae_whole_state_error (n b : ℕ) (hn : 1 ≤ n) (A : Matrix I I ℂ) (j : I)
    (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    Normalized (localAEState n b A j S) ∧
    ‖toEuclidean_fromVec (localAEState n b A j S
        - phaseFlagEmbed (2^n) (qpeOutput (2^n) (preparedAAIterate A j S)
            (preparedAAState A j)))‖
      ≤ Real.pi*(n:ℝ)/(2^b:ℝ) := by
  have hM : 0 < 2^n := by positivity
  have hInputnorm : Normalized (TensorState (Ket (⟨0, hM⟩ : Fin (2^n)))
      (TensorState (Ket false) (Ket j))) :=
    normalized_tensorState (normalized_ket _) (normalized_tensorState (normalized_ket _)
      (normalized_ket _))
  have hOU : (aeControlledGate (2^n) (preparedMark S))
      ∈ Matrix.unitaryGroup (Fin (2^n) × (Bool × I)) ℂ :=
    tensorGate_unitary (Matrix.unitaryGroup (Fin (2^n)) ℂ).one_mem
      (controlOracle_unitary (prepared_aa_reflection_and_access A j S hA).1)
  have hCircU := localAECircuit_isUnitary n b hn A j hA
  have hx₀n : Normalized (ApplyGate (TensorGate (1 : Matrix (Fin (2^n)) (Fin (2^n)) ℂ)
      (TensorGate (1 : Matrix Bool Bool ℂ) A))
      (TensorState (Ket (⟨0, hM⟩ : Fin (2^n))) (TensorState (Ket false) (Ket j)))) :=
    normalized_applyGate
      (tensorGate_unitary (Matrix.unitaryGroup (Fin (2^n)) ℂ).one_mem
        (tensorGate_unitary (Matrix.unitaryGroup Bool ℂ).one_mem hA)) hInputnorm
  refine ⟨hCircU.normalized_run hOU hInputnorm, ?_⟩
  obtain ⟨herrF, herrB⟩ := localAEBackend_error (I := I) n b
  have hLpmU := (localDyadicProgram_run_adjoint_cost n (approxLocalQFT n b)
    (Ket (ZeroStr n))).2.2.2.2.1
  have hF'U : (TensorGate (QFTMatrix (2^n))ᴴ (1 : Matrix (Bool × I) (Bool × I) ℂ))
      ∈ Matrix.unitaryGroup (Fin (2^n) × (Bool × I)) ℂ :=
    tensorGate_unitary (conjTranspose_mem_unitaryGroup (qftMatrix_unitary hM))
      (Matrix.unitaryGroup (Bool × I) ℂ).one_mem
  have hTU : (localAEBackendMatrix n (approxLocalQFT n b))
      ∈ Matrix.unitaryGroup (Fin (2^n) × (Bool × I)) ℂ :=
    tensorGate_unitary
      ((relabelGate_mem_unitaryGroup (bitVecEquiv n)
        (localProgramMatrix (approxLocalQFT n b))).mpr hLpmU)
      (Matrix.unitaryGroup (Bool × I) ℂ).one_mem
  have hWU := localAEFlagWord_isUnitary n hn A j hA
  have hfinal : Real.pi*(n:ℝ)/2^(b+1) + Real.pi*(n:ℝ)/2^(b+1)
      = Real.pi*(n:ℝ)/(2^b:ℝ) := by
    rw [pow_succ (2:ℝ) b]
    field_simp
    norm_num
  rw [localAE_state_diff n b A j S hM]
  refine le_trans (local_backend_output_error
    (J := Fin (2^n) × (Bool × I))
    (aeControlledGate (2^n) (preparedMark S))
    (TensorGate (QFTMatrix (2^n)) (1 : Matrix (Bool × I) (Bool × I) ℂ))
    (localAEBackendMatrix n (approxLocalQFT n b))
    (TensorGate (QFTMatrix (2^n))ᴴ (1 : Matrix (Bool × I) (Bool × I) ℂ))
    (localAEBackendMatrix n (localProgramAdjoint (approxLocalQFT n b)))
    (localAEFlagWord (2^n) A j)
    (ApplyGate (TensorGate (1 : Matrix (Fin (2^n)) (Fin (2^n)) ℂ)
      (TensorGate (1 : Matrix Bool Bool ℂ) A))
      (TensorState (Ket (⟨0, hM⟩ : Fin (2^n))) (TensorState (Ket false) (Ket j))))
    hOU hWU hF'U hTU hx₀n) ?_
  rw [← hfinal]
  exact add_le_add herrF herrB

omit [DecidableEq I] in

theorem local_ae_bhmt_event_filter_cast (n : ℕ) (a : ℝ) :
    (Finset.univ.filter (fun p : Fin (2^n) × (Bool × I) =>
        |aeEstimate (2^n) p.1 - a| ≤ 2*Real.pi*Real.sqrt (a*(1-a))/((2^n : ℕ) : ℝ)
          + Real.pi^2/(((2^n : ℕ) : ℝ))^2))
      = Finset.univ.filter (fun p : Fin (2^n) × (Bool × I) =>
          |aeEstimate (2^n) p.1 - a| ≤ 2*Real.pi*Real.sqrt (a*(1-a))/(2^n : ℝ)
            + Real.pi^2/(2^n : ℝ)^2) := by
  apply Finset.filter_congr
  intro p _
  simp only [Nat.cast_pow, Nat.cast_ofNat]

theorem local_ae_actual_bhmt_event (n b : ℕ) (hn : 1 ≤ n) (A : Matrix I I ℂ) (j : I)
    (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    let a := MeasureProb (preparedAAState A j) S
    let E := Finset.univ.filter (fun p : Fin (2^n) × (Bool × I) =>
      |aeEstimate (2^n) p.1 - a| ≤ 2*Real.pi*Real.sqrt (a*(1-a))/(2^n:ℝ)
        + Real.pi^2/(2^n:ℝ)^2)
    MeasureProb (localAEState n b A j S) E
      ≥ 8/Real.pi^2 - 2*Real.pi*(n:ℝ)/(2^b:ℝ) := by
  have hM : 0 < 2^n := by positivity
  have hM2 : 2 ≤ 2^n := two_le_two_pow hn
  obtain ⟨hnormX, herr⟩ := local_ae_whole_state_error n b hn A j S hA
  have hOU : (aeControlledGate (2^n) (preparedMark S))
      ∈ Matrix.unitaryGroup (Fin (2^n) × (Bool × I)) ℂ :=
    tensorGate_unitary (Matrix.unitaryGroup (Fin (2^n)) ℂ).one_mem
      (controlOracle_unitary (prepared_aa_reflection_and_access A j S hA).1)
  have hC := prepared_ae_expanded_access_and_output (2^n) hM2 A j S hA
  have hYnorm : Normalized (phaseFlagEmbed (2^n) (qpeOutput (2^n)
      (preparedAAIterate A j S) (preparedAAState A j))) := by
    rw [show phaseFlagEmbed (2^n) (qpeOutput (2^n) (preparedAAIterate A j S)
        (preparedAAState A j))
        = Run (aeControlledGate (2^n) (preparedMark S)) (countedAECircuit (2^n) A j)
          (TensorState (Ket (⟨0, hM⟩ : Fin (2^n))) (TensorState (Ket false) (Ket j))) from
      (countedAE_output (2^n) hM A j S).symm]
    exact hC.2.2.1.normalized_run hOU
      (normalized_tensorState (normalized_ket _)
        (normalized_tensorState (normalized_ket _) (normalized_ket _)))
  have hsuccess := (prepared_ae_bhmt_error_and_endpoints (2^n) hM2 A j S hA).1
  have hmassEq := measureProb_ideal_eq_aeLaw_sum (2^n) hM hM2 A j S hA
    (fun z : Fin (2^n) => |aeEstimate (2^n) z - MeasureProb (preparedAAState A j) S|
      ≤ 2*Real.pi*Real.sqrt (MeasureProb (preparedAAState A j) S
          *(1-MeasureProb (preparedAAState A j) S))/((2^n : ℕ) : ℝ)
        + Real.pi^2/(((2^n : ℕ) : ℝ))^2)
  show MeasureProb (localAEState n b A j S)
      (Finset.univ.filter (fun p : Fin (2^n) × (Bool × I) =>
        |aeEstimate (2^n) p.1 - MeasureProb (preparedAAState A j) S|
          ≤ 2*Real.pi*Real.sqrt (MeasureProb (preparedAAState A j) S
              *(1-MeasureProb (preparedAAState A j) S))/(2^n:ℝ)
            + Real.pi^2/(2^n:ℝ)^2))
    ≥ 8/Real.pi^2 - 2*Real.pi*(n:ℝ)/(2^b:ℝ)
  rw [← local_ae_bhmt_event_filter_cast n (MeasureProb (preparedAAState A j) S)]
  have hpt := measureProb_sub_le_two_mul_l2 (localAEState n b A j S)
    (phaseFlagEmbed (2^n) (qpeOutput (2^n) (preparedAAIterate A j S) (preparedAAState A j)))
    (Finset.univ.filter (fun p : Fin (2^n) × (Bool × I) =>
      |aeEstimate (2^n) p.1 - MeasureProb (preparedAAState A j) S|
        ≤ 2*Real.pi*Real.sqrt (MeasureProb (preparedAAState A j) S
            *(1-MeasureProb (preparedAAState A j) S))/((2^n : ℕ) : ℝ)
          + Real.pi^2/(((2^n : ℕ) : ℝ))^2)) hnormX hYnorm
  have hlower := (abs_le.mp hpt).1
  have hYlb : MeasureProb (phaseFlagEmbed (2^n) (qpeOutput (2^n)
          (preparedAAIterate A j S) (preparedAAState A j)))
        (Finset.univ.filter (fun p : Fin (2^n) × (Bool × I) =>
          |aeEstimate (2^n) p.1 - MeasureProb (preparedAAState A j) S|
            ≤ 2*Real.pi*Real.sqrt (MeasureProb (preparedAAState A j) S
                *(1-MeasureProb (preparedAAState A j) S))/((2^n : ℕ) : ℝ)
              + Real.pi^2/(((2^n : ℕ) : ℝ))^2))
      ≥ 8/Real.pi^2 := by
    rw [hmassEq]
    exact hsuccess
  set N := ‖toEuclidean_fromVec (localAEState n b A j S
      - phaseFlagEmbed (2^n) (qpeOutput (2^n) (preparedAAIterate A j S)
        (preparedAAState A j)))‖ with hNdef
  set X := MeasureProb (localAEState n b A j S)
    (Finset.univ.filter (fun p : Fin (2^n) × (Bool × I) =>
      |aeEstimate (2^n) p.1 - MeasureProb (preparedAAState A j) S|
        ≤ 2*Real.pi*Real.sqrt (MeasureProb (preparedAAState A j) S
            *(1-MeasureProb (preparedAAState A j) S))/((2^n : ℕ) : ℝ)
          + Real.pi^2/(((2^n : ℕ) : ℝ))^2)) with hXdef
  set Y := MeasureProb (phaseFlagEmbed (2^n) (qpeOutput (2^n)
      (preparedAAIterate A j S) (preparedAAState A j)))
    (Finset.univ.filter (fun p : Fin (2^n) × (Bool × I) =>
      |aeEstimate (2^n) p.1 - MeasureProb (preparedAAState A j) S|
        ≤ 2*Real.pi*Real.sqrt (MeasureProb (preparedAAState A j) S
            *(1-MeasureProb (preparedAAState A j) S))/((2^n : ℕ) : ℝ)
          + Real.pi^2/(((2^n : ℕ) : ℝ))^2)) with hYdef
  have hkey : 2*N ≤ 2*(Real.pi*(n:ℝ)/(2^b:ℝ)) := by linarith [herr]
  have hXlb : X ≥ Y - 2*N := by linarith [hlower]
  calc X ≥ Y - 2*N := hXlb
    _ ≥ 8/Real.pi^2 - 2*N := by linarith [hYlb]
    _ ≥ 8/Real.pi^2 - 2*(Real.pi*(n:ℝ)/(2^b:ℝ)) := by linarith [hkey]
    _ = 8/Real.pi^2 - 2*Real.pi*(n:ℝ)/(2^b:ℝ) := by ring

theorem local_ae_exact_backend_and_zero_consumer (n b : ℕ) (hn : 1 ≤ n)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hnb : n ≤ b+2) :
    localAEState n b A j S
      = phaseFlagEmbed (2^n) (qpeOutput (2^n) (preparedAAIterate A j S)
          (preparedAAState A j)) ∧
    (A ∈ Matrix.unitaryGroup I ℂ → MeasureProb (preparedAAState A j) S = 0 →
      MeasureProb (localAEState n b A j S)
        (Finset.univ.filter (fun p : Fin (2^n) × (Bool × I) => p.1.val = 0)) = 1) := by
  have hM : 0 < 2^n := by positivity
  have hM2 : 2 ≤ 2^n := two_le_two_pow hn
  have hexact : approxLocalQFT n b = localQFT n :=
    (approxLocalQFT_actual_filter_and_cost n b).2.2.2.2 hnb
  have hTF : localAEBackendMatrix (I := I) n (approxLocalQFT n b)
      = TensorGate (QFTMatrix (2^n)) (1 : Matrix (Bool × I) (Bool × I) ℂ) := by
    rw [localAEBackendMatrix, hexact, localProgramMatrix_localQFT, relabelGate_roundtrip]
  have hT'F' : localAEBackendMatrix (I := I) n (localProgramAdjoint (approxLocalQFT n b))
      = TensorGate (QFTMatrix (2^n))ᴴ (1 : Matrix (Bool × I) (Bool × I) ℂ) := by
    rw [localAEBackendMatrix, hexact,
      (localDyadicProgram_run_adjoint_cost n (localQFT n) (Ket (ZeroStr n))).2.1,
      ← relabelGate_conjTranspose, localProgramMatrix_localQFT, relabelGate_roundtrip]
  have h1 : localAEState n b A j S
      = phaseFlagEmbed (2^n) (qpeOutput (2^n) (preparedAAIterate A j S)
          (preparedAAState A j)) := by
    have hd := localAE_state_diff n b A j S hM
    rw [hTF, hT'F', sub_self] at hd
    exact eq_of_sub_eq_zero hd
  refine ⟨h1, ?_⟩
  intro hA ha
  rw [h1]
  have hfilter : (Finset.univ.filter (fun p : Fin (2^n) × (Bool × I) => p.1.val = 0))
      = Finset.univ.filter (fun p : Fin (2^n) × (Bool × I) => p.1 = ⟨0, hM⟩) := by
    apply Finset.filter_congr
    intro p _
    simp only [Fin.ext_iff]
  rw [hfilter]
  have hend := (prepared_ae_bhmt_error_and_endpoints (2^n) hM2 A j S hA).2.1 ha
  have hpr : (aeLaw (2^n) A j S hA hM2).prob (⟨0, hM⟩ : Fin (2^n))
      = MeasureProb (phaseFlagEmbed (2^n) (qpeOutput (2^n) (preparedAAIterate A j S)
            (preparedAAState A j)))
        (Finset.univ.filter (fun p : Fin (2^n) × (Bool × I) => p.1 = ⟨0, hM⟩)) :=
    congrArg (fun v => MeasureProb v (Finset.univ.filter
      (fun p : Fin (2^n) × (Bool × I) => p.1 = (⟨0, hM⟩ : Fin (2^n)))))
      (countedAE_output (2^n) hM A j S)
  rw [← hpr]
  exact hend

theorem local_ae_counting_consumer (N n b : ℕ) (hN : 0 < N) (hn : 1 ≤ n)
    (S : Finset (Fin N)) :
    let A := QFTMatrix N
    let j : Fin N := ⟨0, hN⟩
    let E := Finset.univ.filter (fun p : Fin (2^n) × (Bool × Fin N) =>
      |(N:ℝ)*aeEstimate (2^n) p.1-(S.card:ℝ)|
        ≤ 2*Real.pi*Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card))/(2^n:ℝ)
          +(N:ℝ)*Real.pi^2/(2^n:ℝ)^2)
    MeasureProb (localAEState n b A j S) E
      ≥ 8/Real.pi^2 - 2*Real.pi*(n:ℝ)/(2^b:ℝ) := by
  have hM : 0 < 2^n := by positivity
  have hM2 : 2 ≤ 2^n := two_le_two_pow hn
  have hqftU : QFTMatrix N ∈ Matrix.unitaryGroup (Fin N) ℂ := qftMatrix_unitary hN
  have hnN : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hmass : MeasureProb (preparedAAState (QFTMatrix N) (⟨0,hN⟩ : Fin N)) S
      = (S.card:ℝ)/(N:ℝ) := prepared_qft_mark_mass N hN S
  have hsqrt : (N:ℝ)*Real.sqrt ((S.card:ℝ)/(N:ℝ)*(1-(S.card:ℝ)/(N:ℝ)))
      = Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card)) := by
    have he : (N:ℝ)^2*((S.card:ℝ)/(N:ℝ)*(1-(S.card:ℝ)/(N:ℝ)))
        = (S.card:ℝ)*((N:ℝ)-S.card) := by field_simp [hnN.ne']
    have h := Real.sqrt_mul (sq_nonneg (N:ℝ))
      ((S.card:ℝ)/(N:ℝ)*(1-(S.card:ℝ)/(N:ℝ)))
    rw [he, Real.sqrt_sq_eq_abs, abs_of_pos hnN] at h
    exact h.symm
  have hcount : ∀ z : Fin (2^n),
      (|aeEstimate (2^n) z - (S.card:ℝ)/(N:ℝ)|
          ≤ 2*Real.pi*Real.sqrt ((S.card:ℝ)/(N:ℝ)*(1-(S.card:ℝ)/(N:ℝ)))
            /((2^n : ℕ) : ℝ)
          + Real.pi^2/(((2^n : ℕ) : ℝ))^2) →
      (|(N:ℝ)*aeEstimate (2^n) z-(S.card:ℝ)|
          ≤ 2*Real.pi*Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card))/(2^n:ℝ)
            +(N:ℝ)*Real.pi^2/(2^n:ℝ)^2) := by
    intro z hz
    have h := mul_le_mul_of_nonneg_left hz hnN.le
    have habs : |(N:ℝ)*aeEstimate (2^n) z-(S.card:ℝ)|
        = (N:ℝ)*|aeEstimate (2^n) z-(S.card:ℝ)/(N:ℝ)| := by
      have he : (N:ℝ)*(aeEstimate (2^n) z-(S.card:ℝ)/(N:ℝ))
          = (N:ℝ)*aeEstimate (2^n) z-(S.card:ℝ) := by field_simp [hnN.ne']
      rw [← he, abs_mul, abs_of_pos hnN]
    rw [← habs] at h
    have he : (N:ℝ)*(2*Real.pi*Real.sqrt ((S.card:ℝ)/(N:ℝ)*(1-(S.card:ℝ)/(N:ℝ)))
          /((2^n : ℕ) : ℝ)+Real.pi^2/(((2^n : ℕ) : ℝ))^2)
        = 2*Real.pi*Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card))/((2^n : ℕ) : ℝ)
          +(N:ℝ)*Real.pi^2/(((2^n : ℕ) : ℝ))^2 := by
      calc _ = 2*Real.pi*((N:ℝ)*Real.sqrt
            ((S.card:ℝ)/(N:ℝ)*(1-(S.card:ℝ)/(N:ℝ))))/((2^n : ℕ) : ℝ)
            +(N:ℝ)*Real.pi^2/(((2^n : ℕ) : ℝ))^2 := by ring
        _ = 2*Real.pi*Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card))/((2^n : ℕ) : ℝ)
            +(N:ℝ)*Real.pi^2/(((2^n : ℕ) : ℝ))^2 := by rw [hsqrt]
    rw [he] at h
    rw [two_pow_real_eq_cast]
    exact h
  obtain ⟨hnormX, herr⟩ := local_ae_whole_state_error n b hn (QFTMatrix N)
    (⟨0, hN⟩ : Fin N) S hqftU
  have hOU : (aeControlledGate (2^n) (preparedMark S))
      ∈ Matrix.unitaryGroup (Fin (2^n) × (Bool × Fin N)) ℂ :=
    tensorGate_unitary (Matrix.unitaryGroup (Fin (2^n)) ℂ).one_mem
      (controlOracle_unitary (prepared_aa_reflection_and_access (QFTMatrix N)
        (⟨0, hN⟩ : Fin N) S hqftU).1)
  have hC := prepared_ae_expanded_access_and_output (2^n) hM2 (QFTMatrix N)
    (⟨0, hN⟩ : Fin N) S hqftU
  have hYnorm : Normalized (phaseFlagEmbed (2^n) (qpeOutput (2^n)
      (preparedAAIterate (QFTMatrix N) (⟨0, hN⟩ : Fin N) S)
      (preparedAAState (QFTMatrix N) (⟨0, hN⟩ : Fin N)))) := by
    rw [show phaseFlagEmbed (2^n) (qpeOutput (2^n)
        (preparedAAIterate (QFTMatrix N) (⟨0, hN⟩ : Fin N) S)
        (preparedAAState (QFTMatrix N) (⟨0, hN⟩ : Fin N)))
        = Run (aeControlledGate (2^n) (preparedMark S)) (countedAECircuit (2^n)
          (QFTMatrix N) (⟨0, hN⟩ : Fin N))
          (TensorState (Ket (⟨0, hM⟩ : Fin (2^n))) (TensorState (Ket false)
            (Ket (⟨0, hN⟩ : Fin N)))) from
      (countedAE_output (2^n) hM (QFTMatrix N) (⟨0, hN⟩ : Fin N) S).symm]
    exact hC.2.2.1.normalized_run hOU
      (normalized_tensorState (normalized_ket _)
        (normalized_tensorState (normalized_ket _) (normalized_ket _)))
  have hsuccess := amplitude_counting_actual_consumer N (2^n) hN hM2 S
  show MeasureProb (localAEState n b (QFTMatrix N) (⟨0, hN⟩ : Fin N) S)
      (Finset.univ.filter (fun p : Fin (2^n) × (Bool × Fin N) =>
        |(N:ℝ)*aeEstimate (2^n) p.1-(S.card:ℝ)|
          ≤ 2*Real.pi*Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card))/(2^n:ℝ)
            +(N:ℝ)*Real.pi^2/(2^n:ℝ)^2))
    ≥ 8/Real.pi^2 - 2*Real.pi*(n:ℝ)/(2^b:ℝ)
  have hEq := measureProb_ideal_eq_aeLaw_sum (2^n) hM hM2 (QFTMatrix N)
    (⟨0, hN⟩ : Fin N) S hqftU
    (fun z : Fin (2^n) => |aeEstimate (2^n) z - (S.card:ℝ)/(N:ℝ)|
      ≤ 2*Real.pi*Real.sqrt ((S.card:ℝ)/(N:ℝ)*(1-(S.card:ℝ)/(N:ℝ)))/((2^n : ℕ) : ℝ)
        + Real.pi^2/(((2^n : ℕ) : ℝ))^2)
  have hsuccess2 : ∑ z ∈ Finset.univ.filter (fun z : Fin (2^n) =>
        |aeEstimate (2^n) z - (S.card:ℝ)/(N:ℝ)|
          ≤ 2*Real.pi*Real.sqrt ((S.card:ℝ)/(N:ℝ)*(1-(S.card:ℝ)/(N:ℝ)))/((2^n : ℕ) : ℝ)
            + Real.pi^2/(((2^n : ℕ) : ℝ))^2),
        (aeLaw (2^n) (QFTMatrix N) (⟨0, hN⟩ : Fin N) S hqftU hM2).prob z
      ≥ 8/Real.pi^2 := by
    have h := (prepared_ae_bhmt_error_and_endpoints (2^n) hM2 (QFTMatrix N)
      (⟨0, hN⟩ : Fin N) S hqftU).1
    rw [hmass] at h
    exact h
  have hset : (Finset.univ.filter (fun p : Fin (2^n) × (Bool × Fin N) =>
        |aeEstimate (2^n) p.1 - (S.card:ℝ)/(N:ℝ)|
          ≤ 2*Real.pi*Real.sqrt ((S.card:ℝ)/(N:ℝ)*(1-(S.card:ℝ)/(N:ℝ)))
            /((2^n : ℕ) : ℝ)
          + Real.pi^2/(((2^n : ℕ) : ℝ))^2))
      ⊆ Finset.univ.filter (fun p : Fin (2^n) × (Bool × Fin N) =>
        |(N:ℝ)*aeEstimate (2^n) p.1-(S.card:ℝ)|
          ≤ 2*Real.pi*Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card))/(2^n:ℝ)
            +(N:ℝ)*Real.pi^2/(2^n:ℝ)^2) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact hcount p.1 hp
  have hpt := measureProb_sub_le_two_mul_l2 (localAEState n b (QFTMatrix N)
    (⟨0, hN⟩ : Fin N) S)
    (phaseFlagEmbed (2^n) (qpeOutput (2^n) (preparedAAIterate (QFTMatrix N)
      (⟨0, hN⟩ : Fin N) S) (preparedAAState (QFTMatrix N) (⟨0, hN⟩ : Fin N))))
    (Finset.univ.filter (fun p : Fin (2^n) × (Bool × Fin N) =>
      |(N:ℝ)*aeEstimate (2^n) p.1-(S.card:ℝ)|
        ≤ 2*Real.pi*Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card))/(2^n:ℝ)
          +(N:ℝ)*Real.pi^2/(2^n:ℝ)^2)) hnormX hYnorm
  have hlower := (abs_le.mp hpt).1
  have hYA : MeasureProb (phaseFlagEmbed (2^n) (qpeOutput (2^n)
          (preparedAAIterate (QFTMatrix N) (⟨0, hN⟩ : Fin N) S)
          (preparedAAState (QFTMatrix N) (⟨0, hN⟩ : Fin N))))
        (Finset.univ.filter (fun p : Fin (2^n) × (Bool × Fin N) =>
          |aeEstimate (2^n) p.1 - (S.card:ℝ)/(N:ℝ)|
            ≤ 2*Real.pi*Real.sqrt ((S.card:ℝ)/(N:ℝ)*(1-(S.card:ℝ)/(N:ℝ)))
              /((2^n : ℕ) : ℝ)
            + Real.pi^2/(((2^n : ℕ) : ℝ))^2))
      ≥ 8/Real.pi^2 := by
    rw [hEq]
    exact hsuccess2
  have hYlb : MeasureProb (phaseFlagEmbed (2^n) (qpeOutput (2^n)
          (preparedAAIterate (QFTMatrix N) (⟨0, hN⟩ : Fin N) S)
          (preparedAAState (QFTMatrix N) (⟨0, hN⟩ : Fin N))))
        (Finset.univ.filter (fun p : Fin (2^n) × (Bool × Fin N) =>
          |(N:ℝ)*aeEstimate (2^n) p.1-(S.card:ℝ)|
            ≤ 2*Real.pi*Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card))/(2^n:ℝ)
              +(N:ℝ)*Real.pi^2/(2^n:ℝ)^2))
      ≥ 8/Real.pi^2 :=
    le_trans hYA (measureProb_mono (phaseFlagEmbed (2^n) (qpeOutput (2^n)
      (preparedAAIterate (QFTMatrix N) (⟨0, hN⟩ : Fin N) S)
      (preparedAAState (QFTMatrix N) (⟨0, hN⟩ : Fin N)))) hset)
  set N' := ‖toEuclidean_fromVec (localAEState n b (QFTMatrix N) (⟨0, hN⟩ : Fin N) S
      - phaseFlagEmbed (2^n) (qpeOutput (2^n) (preparedAAIterate (QFTMatrix N)
        (⟨0, hN⟩ : Fin N) S) (preparedAAState (QFTMatrix N) (⟨0, hN⟩ : Fin N))))‖
    with hN'def
  set X' := MeasureProb (localAEState n b (QFTMatrix N) (⟨0, hN⟩ : Fin N) S)
    (Finset.univ.filter (fun p : Fin (2^n) × (Bool × Fin N) =>
      |(N:ℝ)*aeEstimate (2^n) p.1-(S.card:ℝ)|
        ≤ 2*Real.pi*Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card))/(2^n:ℝ)
          +(N:ℝ)*Real.pi^2/(2^n:ℝ)^2)) with hXdef
  set Y' := MeasureProb (phaseFlagEmbed (2^n) (qpeOutput (2^n)
      (preparedAAIterate (QFTMatrix N) (⟨0, hN⟩ : Fin N) S)
      (preparedAAState (QFTMatrix N) (⟨0, hN⟩ : Fin N))))
    (Finset.univ.filter (fun p : Fin (2^n) × (Bool × Fin N) =>
      |(N:ℝ)*aeEstimate (2^n) p.1-(S.card:ℝ)|
        ≤ 2*Real.pi*Real.sqrt ((S.card:ℝ)*((N:ℝ)-S.card))/(2^n:ℝ)
          +(N:ℝ)*Real.pi^2/(2^n:ℝ)^2)) with hYdef
  have hkey : 2*N' ≤ 2*(Real.pi*(n:ℝ)/(2^b:ℝ)) := by linarith [herr]
  have hXlb : X' ≥ Y' - 2*N' := by linarith [hlower]
  calc X' ≥ Y' - 2*N' := hXlb
    _ ≥ 8/Real.pi^2 - 2*N' := by linarith [hYlb]
    _ ≥ 8/Real.pi^2 - 2*(Real.pi*(n:ℝ)/(2^b:ℝ)) := by linarith [hkey]
    _ = 8/Real.pi^2 - 2*Real.pi*(n:ℝ)/(2^b:ℝ) := by ring

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
