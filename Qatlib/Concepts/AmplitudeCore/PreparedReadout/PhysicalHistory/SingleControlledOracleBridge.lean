/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.BinaryClockSignalWord
import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel
import Qatlib.Concepts.LocalMachine.LocalTransport.ControlledQueryCircuit
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.NativeAnd
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.SingleControlledOracleBridge

open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.QspSimulation.JacobiAnger
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory
open scoped Classical BigOperators

abbrev Labels := Bool × Bool
abbrev Logical (H : Type*) := Labels × H
abbrev Physical (H : Type*) := Labels × (Bool × H)

variable {H : Type*} [Fintype H] [DecidableEq H]

private noncomputable abbrev matmul {X Y Z : Type*} [Fintype Y]
    (A : Matrix X Y ℂ) (B : Matrix Y Z ℂ) : Matrix X Z ℂ :=
  @HMul.hMul (Matrix X Y ℂ) (Matrix Y Z ℂ) (Matrix X Z ℂ)
    Matrix.instHMulOfFintypeOfMulOfAddCommMonoid A B

def andFlip (x : Physical H) : Physical H :=
  (x.1, (x.2.1 ^^ (x.1.1 && x.1.2), x.2.2))

omit [Fintype H] [DecidableEq H] in

theorem andFlip_involutive : Function.Involutive (andFlip (H := H)) := by
  rintro ⟨⟨a,b⟩,s,i⟩
  cases a <;> cases b <;> cases s <;> rfl

noncomputable def compute : Matrix (Physical H) (Physical H) ℂ := permMatrix andFlip

theorem compute_unitary : compute (H := H) ∈ Matrix.unitaryGroup (Physical H) ℂ :=
  permMatrix_unitary andFlip_involutive

theorem compute_adjoint : (compute (H := H))ᴴ = compute :=
  permMatrix_conjTranspose andFlip_involutive

theorem compute_square : compute (H := H) * compute = 1 :=
  permMatrix_mul_self andFlip_involutive

noncomputable def frame : Matrix (Physical H) (Logical H) ℂ :=
  fun x y => if x.1 = y.1 ∧ x.2.1 = false then (1 : Matrix H H ℂ) x.2.2 y.2 else 0

noncomputable def computedFrame : Matrix (Physical H) (Logical H) ℂ :=
  fun x y => if x.1 = y.1 ∧ x.2.1 = (y.1.1 && y.1.2)
    then (1 : Matrix H H ℂ) x.2.2 y.2 else 0

theorem frame_mulVec (ψ : QState (Logical H)) (ab : Labels) (s : Bool) (i : H) :
    (frame *ᵥ ψ) (ab,(s,i)) = if s then 0 else ψ (ab,i) := by
  rcases ab with ⟨a,b⟩
  cases a <;> cases b <;> cases s <;>
    simp [frame, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Matrix.one_apply, ite_mul]

set_option maxHeartbeats 400000 in

theorem frame_isometry : matmul ((frame (H := H))ᴴ) frame = 1 := by
  ext ⟨⟨a,b⟩,i⟩ ⟨⟨c,d⟩,j⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [matmul, frame, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Matrix.one_apply, mul_ite] <;>
    simp only [eq_comm]

private theorem compute_mul {I : Type*} (M : Matrix (Physical H) I ℂ) :
    matmul compute M = fun x y => M (andFlip x) y := by
  ext x y
  change ApplyGate (permMatrix andFlip) (fun z => M z y) x = M (andFlip x) y
  exact applyGate_permMatrix andFlip_involutive _ _

theorem compute_frame : matmul (compute (H := H)) frame = computedFrame := by
  rw [compute_mul (frame (H := H))]
  ext ⟨⟨a,b⟩,s,i⟩ ⟨⟨c,d⟩,j⟩
  cases a <;> cases b <;> cases c <;> cases d <;> cases s <;>
    simp [andFlip, frame, computedFrame, Matrix.one_apply]

theorem uncompute_frame : matmul (compute (H := H)) computedFrame = frame := by
  calc
    _ = matmul compute (matmul compute frame) := by rw [compute_frame]
    _ = matmul (compute * compute) frame := (Matrix.mul_assoc _ _ _).symm
    _ = frame := by rw [compute_square]; exact Matrix.one_mul _

noncomputable def supplied (U : Matrix H H ℂ) : Matrix (Physical H) (Physical H) ℂ :=
  parallelOracle (J := Labels) (controlOracle U)

omit [Fintype H] in

theorem supplied_adjoint (U : Matrix H H ℂ) : (supplied U)ᴴ = supplied Uᴴ := by
  simp only [supplied, parallelOracle_adjoint, controlOracle_adjoint]

theorem supplied_unitary {U : Matrix H H ℂ} (hU : U ∈ Matrix.unitaryGroup H ℂ) :
    supplied U ∈ Matrix.unitaryGroup (Physical H) ℂ :=
  parallelOracle_unitary (controlOracle_unitary hU)

noncomputable def reference (U : Matrix H H ℂ) : Matrix (Logical H) (Logical H) ℂ :=
  select (fun ab : Labels => if ab.1 && ab.2 then U else 1)

omit [Fintype H] in

theorem reference_eq_nested (U : Matrix H H ℂ) :
    reference U = (controlOracle (controlOracle U)).submatrix
      (fun x : Logical H => (x.1.1,(x.1.2,x.2)))
      (fun x : Logical H => (x.1.1,(x.1.2,x.2))) := by
  ext ⟨⟨a,b⟩,i⟩ ⟨⟨c,d⟩,j⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [reference, controlOracle, select, Matrix.one_apply]

private def computedPoint (y : Logical H) : Physical H :=
  (y.1,(y.1.1 && y.1.2,y.2))

omit [Fintype H] in

private theorem computedFrame_column (x : Physical H) (y : Logical H) :
    computedFrame x y = if x = computedPoint y then 1 else 0 := by
  rcases x with ⟨ab,s,i⟩
  rcases y with ⟨cd,j⟩
  by_cases h₁ : ab = cd <;> by_cases h₂ : s = (cd.1 && cd.2) <;>
    by_cases h₃ : i = j <;>
    simp [computedFrame, computedPoint, Matrix.one_apply, Prod.mk.injEq, h₁, h₂, h₃]

omit [Fintype H] in

private theorem computedFrame_row (x : Physical H) (y : Logical H) :
    computedFrame x y = if x.2.1 = (x.1.1 && x.1.2)
      then (if y = (x.1,x.2.2) then 1 else 0) else 0 := by
  rw [computedFrame_column]
  rcases x with ⟨ab,s,i⟩
  rcases y with ⟨cd,j⟩
  by_cases hab : ab = cd
  · subst cd
    by_cases hs : s = (ab.1 && ab.2) <;> by_cases hij : i = j <;>
      simp [computedPoint, Prod.mk.injEq, hs, hij, eq_comm]
  · have hba : cd ≠ ab := Ne.symm hab
    simp [computedPoint, Prod.mk.injEq, hab, hba]

theorem supplied_computedFrame (U : Matrix H H ℂ) :
    matmul (supplied U) computedFrame = matmul computedFrame (reference U) := by
  ext x y
  calc
    _ = supplied U x (computedPoint y) := by
      change (∑ z : Physical H, supplied U x z * computedFrame z y) = _
      simp only [computedFrame_column]
      simp
    _ = if x.2.1 = (x.1.1 && x.1.2)
        then reference U (x.1,x.2.2) y else 0 := by
      rcases x with ⟨ab,s,i⟩
      rcases y with ⟨cd,j⟩
      by_cases hab : ab = cd
      · subst cd
        by_cases hs : s = (ab.1 && ab.2)
        · subst s
          simp [supplied, parallelOracle, controlOracle, select, computedPoint, reference]
        · simp [supplied, parallelOracle, controlOracle, select, computedPoint, hs]
      · simp [supplied, parallelOracle, controlOracle, select, computedPoint, reference, hab]
    _ = matmul computedFrame (reference U) x y := by
      change _ = ∑ z : Logical H, computedFrame x z * reference U z y
      simp only [computedFrame_row]
      by_cases hs : x.2.1 = (x.1.1 && x.1.2) <;> simp [hs]

noncomputable def word (backward : Bool) : List (AdjointStep (Physical H)) :=
  [.gate compute, if backward then .backward else .forward, .gate compute]

theorem word_wellFormed (backward : Bool) :
    WellFormedAdjointCircuit (word (H := H) backward) := by
  cases backward <;> simp [word, WellFormedAdjointCircuit.gate_cons_iff,
    WellFormedAdjointCircuit.forward_cons_iff, WellFormedAdjointCircuit.backward_cons_iff,
    compute_unitary]

omit [Fintype H] in

theorem word_counts (backward : Bool) :
    adjointQueryCount (word (H := H) backward) = 1 ∧
    adjointGateCount (word (H := H) backward) = 2 := by
  cases backward <;> exact ⟨rfl,rfl⟩

theorem word_intertwining (U : Matrix H H ℂ) (backward : Bool) :
    matmul (evaluate (supplied U) (word backward)) frame =
      matmul frame (reference (if backward then Uᴴ else U)) := by
  have core (V : Matrix H H ℂ) :
      matmul (compute * (supplied V * compute)) frame = matmul frame (reference V) := by
    calc
      _ = matmul compute (matmul (supplied V) (matmul compute frame)) := by
        simp only [matmul, Matrix.mul_assoc]
      _ = matmul compute (matmul computedFrame (reference V)) := by
        rw [compute_frame, supplied_computedFrame]
      _ = matmul (matmul compute computedFrame) (reference V) :=
        (Matrix.mul_assoc _ _ _).symm
      _ = matmul frame (reference V) := by rw [uncompute_frame]
  cases backward
  · simpa [word, evaluate, instructionMatrix] using! core U
  · simpa [word, evaluate, instructionMatrix, supplied_adjoint] using! core Uᴴ

theorem word_coherent (U : Matrix H H ℂ) (backward : Bool) (ψ : QState (Logical H)) :
    evaluate (supplied U) (word backward) *ᵥ (frame *ᵥ ψ) =
      frame *ᵥ (reference (if backward then Uᴴ else U) *ᵥ ψ) := by
  calc
    _ = matmul (evaluate (supplied U) (word backward)) frame *ᵥ ψ :=
      Matrix.mulVec_mulVec ψ _ _
    _ = matmul frame (reference (if backward then Uᴴ else U)) *ᵥ ψ := by
      rw [word_intertwining]
    _ = _ := (Matrix.mulVec_mulVec ψ _ _).symm

theorem word_unitary {U : Matrix H H ℂ} (hU : U ∈ Matrix.unitaryGroup H ℂ)
    (backward : Bool) :
    evaluate (supplied U) (word backward) ∈ Matrix.unitaryGroup (Physical H) ℂ :=
  (word_wellFormed backward).evaluate_unitary (supplied_unitary hU)

theorem word_literal_adjoint (backward : Bool) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit (word (H := H) backward) = word (!backward) := by
  cases backward <;> simp [word, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit,
      adjointInstruction, compute_adjoint]

theorem inverse_semantics (U : Matrix H H ℂ) (backward : Bool) :
    evaluate (supplied U) (word (!backward)) =
      (evaluate (supplied U) (word backward))ᴴ := by
  rw [← word_literal_adjoint, evaluate_adjointCircuit]

def nativeRead : (Reg 3 × H) ≃ Physical H where
  toFun x := ((x.1 0,x.1 1),(x.1 2,x.2))
  invFun x := (AndCoordinates.bits x.1.1 x.1.2 x.2.1,x.2.2)
  left_inv := by
    rintro ⟨x,i⟩
    change (AndCoordinates.bits (x 0) (x 1) (x 2),i) = (x,i)
    apply Prod.ext
    · funext w
      fin_cases w <;> rfl
    · rfl
  right_inv := by rintro ⟨⟨a,b⟩,s,i⟩; rfl

private theorem update_bits (a b s t : Bool) :
    Function.update (AndCoordinates.bits a b s) 2 t =
      AndCoordinates.bits a b t := by
  funext w
  fin_cases w <;> simp [AndCoordinates.bits, Function.update]

private theorem bits_eq_iff (a b s c d t : Bool) :
    AndCoordinates.bits a b s = AndCoordinates.bits c d t ↔
      a = c ∧ b = d ∧ s = t := by
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1, congrFun h 2⟩
  · rintro ⟨rfl,rfl,rfl⟩
    rfl

private theorem native_entry (x y : Reg 3) :
    AndNetwork.matrix AndNetwork.controlledCNOT x y =
      if x = Function.update y 2 (y 2 ^^ (y 0 && y 1)) then 1 else 0 := by
  have h := congrFun (AndNetwork.controlledCNOT_basis y) x
  rw [run_reflectionCompile] at h
  change ApplyGate (AndNetwork.matrix
    AndNetwork.controlledCNOT) (Qatlib.Foundations.PureStateMath.Ket y) x = _ at h
  simpa [ApplyGate, Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket] using! h

omit [Fintype H] in

theorem compute_eq_native :
    compute (H := H) = relabelGate nativeRead
      (TensorGate (AndNetwork.matrix
        AndNetwork.controlledCNOT) (1 : Matrix H H ℂ)) := by
  ext ⟨⟨a,b⟩,s,i⟩ ⟨⟨c,d⟩,t,j⟩
  change (if ((a,b),(s,i)) = ((c,d),(t ^^ (c && d),j)) then (1 : ℂ) else 0) =
    AndNetwork.matrix AndNetwork.controlledCNOT
      (AndCoordinates.bits a b s) (AndCoordinates.bits c d t) *
      (if i = j then 1 else 0)
  rw [native_entry]
  change (if ((a,b),(s,i)) = ((c,d),(t ^^ (c && d),j)) then (1 : ℂ) else 0) =
    (if AndCoordinates.bits a b s =
      Function.update (AndCoordinates.bits c d t) 2 (t ^^ (c && d))
      then 1 else 0) * (if i = j then 1 else 0)
  simp only [update_bits, bits_eq_iff, Prod.mk.injEq]
  split_ifs <;> simp_all

theorem known_native_resources :
    reflectionLegal AndNetwork.controlledCNOT ∧
    2 * AndNetwork.controlledCNOT.length = 30 ∧
    QueryCount (reflectionCompile AndNetwork.controlledCNOT) = 0 := by
  exact ⟨AndNetwork.controlledCNOT_legal,
    by rw [AndNetwork.controlledCNOT_length],
    queryCount_reflectionCompile _⟩

end Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.SingleControlledOracleBridge
