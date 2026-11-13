/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.BinaryClockSignalWord
import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel
import Qatlib.Concepts.LocalMachine.LocalTransport.ControlledQueryCircuit
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.NativeAnd

/-!
# A single-controlled-oracle bridge

`word` implements a doubly controlled logical oracle using a clean workspace bit, one query to a
supplied singly controlled oracle, and conjunction computation followed by uncomputation.
`frame` and `computedFrame` describe the clean and computed subspaces.

The module proves coherent action, inverse semantics, unitarity, and exact query counts, and
identifies the conjunction gate with a native three-bit network. Controlled gates and reversible
workspace computation are discussed in [NielsenChuang2010].

## Main statements

* `word_intertwining`: identifies the logical action on the clean frame.
* `word_counts`: counts one query and two fixed gates.
* `known_native_resources`: records legality and the native conjunction-network resources.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false

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

/-- The pair of Boolean control labels. -/
abbrev Labels := Bool × Bool
/-- The logical register consisting of two control labels and the system `H`. -/
abbrev Logical (H : Type*) := Labels × H
/-- The physical register obtained by adding a Boolean workspace bit to the logical register. -/
abbrev Physical (H : Type*) := Labels × (Bool × H)

variable {H : Type*} [Fintype H] [DecidableEq H]

/-- Matrix multiplication with an explicitly selected finite-index multiplication instance. -/
private noncomputable abbrev matmul {X Y Z : Type*} [Fintype Y]
    (A : Matrix X Y ℂ) (B : Matrix Y Z ℂ) : Matrix X Z ℂ :=
  @HMul.hMul (Matrix X Y ℂ) (Matrix Y Z ℂ) (Matrix X Z ℂ)
    Matrix.instHMulOfFintypeOfMulOfAddCommMonoid A B

/-- Toggle the workspace bit by the conjunction of the two control bits, preserving the labels
and system. -/
def andFlip (x : Physical H) : Physical H :=
  (x.1, (x.2.1 ^^ (x.1.1 && x.1.2), x.2.2))

omit [Fintype H] [DecidableEq H] in

/-- The workspace conjunction toggle is an involution. -/
theorem andFlip_involutive : Function.Involutive (andFlip (H := H)) := by
  rintro ⟨⟨a,b⟩,s,i⟩
  cases a <;> cases b <;> cases s <;> rfl

/-- The permutation matrix that computes the conjunction into the workspace bit. -/
noncomputable def compute : Matrix (Physical H) (Physical H) ℂ := permMatrix andFlip

/-- The conjunction computation matrix is unitary. -/
theorem compute_unitary : compute (H := H) ∈ Matrix.unitaryGroup (Physical H) ℂ :=
  permMatrix_unitary andFlip_involutive

/-- The conjunction computation matrix is self-adjoint. -/
theorem compute_adjoint : (compute (H := H))ᴴ = compute :=
  permMatrix_conjTranspose andFlip_involutive

/-- Applying the conjunction computation twice gives the identity. -/
theorem compute_square : compute (H := H) * compute = 1 :=
  permMatrix_mul_self andFlip_involutive

/-- The matrix embedding a logical state with its workspace bit initialized to `false`. -/
noncomputable def frame : Matrix (Physical H) (Logical H) ℂ :=
  fun x y => if x.1 = y.1 ∧ x.2.1 = false then (1 : Matrix H H ℂ) x.2.2 y.2 else 0

/-- The matrix embedding a logical state with its workspace bit set to the conjunction of its
control labels. -/
noncomputable def computedFrame : Matrix (Physical H) (Logical H) ℂ :=
  fun x y => if x.1 = y.1 ∧ x.2.1 = (y.1.1 && y.1.2)
    then (1 : Matrix H H ℂ) x.2.2 y.2 else 0

/-- The clean frame preserves logical amplitudes at workspace value `false` and vanishes at
workspace value `true`. -/
theorem frame_mulVec (ψ : QState (Logical H)) (ab : Labels) (s : Bool) (i : H) :
    (frame *ᵥ ψ) (ab,(s,i)) = if s then 0 else ψ (ab,i) := by
  rcases ab with ⟨a,b⟩
  cases a <;> cases b <;> cases s <;>
    simp [frame, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Matrix.one_apply, ite_mul]

set_option maxHeartbeats 400000 in

/-- The clean frame is an isometry: its adjoint composed with itself is the identity. -/
theorem frame_isometry : matmul ((frame (H := H))ᴴ) frame = 1 := by
  ext ⟨⟨a,b⟩,i⟩ ⟨⟨c,d⟩,j⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [matmul, frame, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Matrix.one_apply, mul_ite] <;>
    simp only [eq_comm]

/-- Left multiplication by `compute` permutes matrix rows by `andFlip`. -/
private theorem compute_mul {I : Type*} (M : Matrix (Physical H) I ℂ) :
    matmul compute M = fun x y => M (andFlip x) y := by
  ext x y
  change ApplyGate (permMatrix andFlip) (fun z => M z y) x = M (andFlip x) y
  exact applyGate_permMatrix andFlip_involutive _ _

/-- Computing the conjunction on the clean frame yields `computedFrame`. -/
theorem compute_frame : matmul (compute (H := H)) frame = computedFrame := by
  rw [compute_mul (frame (H := H))]
  ext ⟨⟨a,b⟩,s,i⟩ ⟨⟨c,d⟩,j⟩
  cases a <;> cases b <;> cases c <;> cases d <;> cases s <;>
    simp [andFlip, frame, computedFrame, Matrix.one_apply]

/-- Computing the conjunction on `computedFrame` restores the clean frame. -/
theorem uncompute_frame : matmul (compute (H := H)) computedFrame = frame := by
  calc
    _ = matmul compute (matmul compute frame) := by rw [compute_frame]
    _ = matmul (compute * compute) frame := (Matrix.mul_assoc _ _ _).symm
    _ = frame := by rw [compute_square]; exact Matrix.one_mul _

/-- The supplied singly controlled oracle acting in parallel over the two label bits. -/
noncomputable def supplied (U : Matrix H H ℂ) : Matrix (Physical H) (Physical H) ℂ :=
  parallelOracle (J := Labels) (controlOracle U)

omit [Fintype H] in

/-- Taking the adjoint of the supplied oracle is equivalent to supplying `Uᴴ`. -/
theorem supplied_adjoint (U : Matrix H H ℂ) : (supplied U)ᴴ = supplied Uᴴ := by
  simp only [supplied, parallelOracle_adjoint, controlOracle_adjoint]

/-- The supplied controlled oracle is unitary whenever `U` is unitary. -/
theorem supplied_unitary {U : Matrix H H ℂ} (hU : U ∈ Matrix.unitaryGroup H ℂ) :
    supplied U ∈ Matrix.unitaryGroup (Physical H) ℂ :=
  parallelOracle_unitary (controlOracle_unitary hU)

/-- The logical oracle applying `U` exactly when both control labels are true. -/
noncomputable def reference (U : Matrix H H ℂ) : Matrix (Logical H) (Logical H) ℂ :=
  select (fun ab : Labels => if ab.1 && ab.2 then U else 1)

omit [Fintype H] in

/-- The logical reference oracle is the doubly controlled oracle after reassociating its
registers. -/
theorem reference_eq_nested (U : Matrix H H ℂ) :
    reference U = (controlOracle (controlOracle U)).submatrix
      (fun x : Logical H => (x.1.1,(x.1.2,x.2)))
      (fun x : Logical H => (x.1.1,(x.1.2,x.2))) := by
  ext ⟨⟨a,b⟩,i⟩ ⟨⟨c,d⟩,j⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [reference, controlOracle, select, Matrix.one_apply]

/-- The physical basis point associated with a logical point and its computed conjunction bit. -/
private def computedPoint (y : Logical H) : Physical H :=
  (y.1,(y.1.1 && y.1.2,y.2))

omit [Fintype H] in

/-- Each column of `computedFrame` is the basis vector at `computedPoint`. -/
private theorem computedFrame_column (x : Physical H) (y : Logical H) :
    computedFrame x y = if x = computedPoint y then 1 else 0 := by
  rcases x with ⟨ab,s,i⟩
  rcases y with ⟨cd,j⟩
  by_cases h₁ : ab = cd <;> by_cases h₂ : s = (cd.1 && cd.2) <;>
    by_cases h₃ : i = j <;>
    simp [computedFrame, computedPoint, Matrix.one_apply, Prod.mk.injEq, h₁, h₂, h₃]

omit [Fintype H] in

/-- A row of `computedFrame` is nonzero precisely when its workspace bit equals the conjunction
of its labels, and then selects the corresponding logical point. -/
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

/-- The supplied oracle on the computed frame intertwines with the logical doubly controlled
reference oracle. -/
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

/-- The compute-query-uncompute word, choosing a forward or backward oracle query according to
`backward`. -/
noncomputable def word (backward : Bool) : List (AdjointStep (Physical H)) :=
  [.gate compute, if backward then .backward else .forward, .gate compute]

/-- The compute-query-uncompute word is a well-formed adjoint circuit. -/
theorem word_wellFormed (backward : Bool) :
    WellFormedAdjointCircuit (word (H := H) backward) := by
  cases backward <;> simp [word, WellFormedAdjointCircuit.gate_cons_iff,
    WellFormedAdjointCircuit.forward_cons_iff, WellFormedAdjointCircuit.backward_cons_iff,
    compute_unitary]

omit [Fintype H] in

/-- The bridge word uses exactly one oracle query and two fixed gates. -/
theorem word_counts (backward : Bool) :
    adjointQueryCount (word (H := H) backward) = 1 ∧
    adjointGateCount (word (H := H) backward) = 2 := by
  cases backward <;> exact ⟨rfl,rfl⟩

/-- On the clean frame, the bridge word implements the reference oracle for `U` or `Uᴴ`
according to its direction. -/
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

/-- The bridge word acts coherently on every embedded logical state as the directed reference
oracle. -/
theorem word_coherent (U : Matrix H H ℂ) (backward : Bool) (ψ : QState (Logical H)) :
    evaluate (supplied U) (word backward) *ᵥ (frame *ᵥ ψ) =
      frame *ᵥ (reference (if backward then Uᴴ else U) *ᵥ ψ) := by
  calc
    _ = matmul (evaluate (supplied U) (word backward)) frame *ᵥ ψ :=
      Matrix.mulVec_mulVec ψ _ _
    _ = matmul frame (reference (if backward then Uᴴ else U)) *ᵥ ψ := by
      rw [word_intertwining]
    _ = _ := (Matrix.mulVec_mulVec ψ _ _).symm

/-- The evaluated bridge word is unitary when the supplied system oracle is unitary. -/
theorem word_unitary {U : Matrix H H ℂ} (hU : U ∈ Matrix.unitaryGroup H ℂ)
    (backward : Bool) :
    evaluate (supplied U) (word backward) ∈ Matrix.unitaryGroup (Physical H) ℂ :=
  (word_wellFormed backward).evaluate_unitary (supplied_unitary hU)

/-- The literal adjoint circuit is obtained by reversing the direction flag. -/
theorem word_literal_adjoint (backward : Bool) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit (word (H := H) backward) = word (!backward) := by
  cases backward <;> simp [word, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit,
      adjointInstruction, compute_adjoint]

/-- Flipping the direction flag evaluates to the adjoint of the original bridge operator. -/
theorem inverse_semantics (U : Matrix H H ℂ) (backward : Bool) :
    evaluate (supplied U) (word (!backward)) =
      (evaluate (supplied U) (word backward))ᴴ := by
  rw [← word_literal_adjoint, evaluate_adjointCircuit]

/-- The equivalence identifying three native Boolean wires and `H` with the physical control and
workspace registers. -/
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

/-- Updating the third coordinate of `AndCoordinates.bits` replaces only its workspace bit. -/
private theorem update_bits (a b s t : Bool) :
    Function.update (AndCoordinates.bits a b s) 2 t =
      AndCoordinates.bits a b t := by
  funext w
  fin_cases w <;> simp [AndCoordinates.bits, Function.update]

/-- Two three-bit coordinate functions are equal exactly when their corresponding bits are
equal. -/
private theorem bits_eq_iff (a b s c d t : Bool) :
    AndCoordinates.bits a b s = AndCoordinates.bits c d t ↔
      a = c ∧ b = d ∧ s = t := by
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1, congrFun h 2⟩
  · rintro ⟨rfl,rfl,rfl⟩
    rfl

/-- The native controlled-CNOT matrix toggles its target bit by the conjunction of its two
controls. -/
private theorem native_entry (x y : Reg 3) :
    AndNetwork.matrix AndNetwork.controlledCNOT x y =
      if x = Function.update y 2 (y 2 ^^ (y 0 && y 1)) then 1 else 0 := by
  have h := congrFun (AndNetwork.controlledCNOT_basis y) x
  rw [run_reflectionCompile] at h
  change ApplyGate (AndNetwork.matrix
    AndNetwork.controlledCNOT) (Qatlib.Foundations.PureStateMath.Ket y) x = _ at h
  simpa [ApplyGate, Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket] using! h

omit [Fintype H] in

/-- The conjunction computation is the relabeled native controlled-CNOT matrix tensored with the
identity on `H`. -/
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

/-- The native conjunction network is legal, has combined compute and uncompute length 30, and
its compiled circuit uses no oracle queries. -/
theorem known_native_resources :
    reflectionLegal AndNetwork.controlledCNOT ∧
    2 * AndNetwork.controlledCNOT.length = 30 ∧
    QueryCount (reflectionCompile AndNetwork.controlledCNOT) = 0 := by
  exact ⟨AndNetwork.controlledCNOT_legal,
    by rw [AndNetwork.controlledCNOT_length],
    queryCount_reflectionCompile _⟩

end Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.SingleControlledOracleBridge
