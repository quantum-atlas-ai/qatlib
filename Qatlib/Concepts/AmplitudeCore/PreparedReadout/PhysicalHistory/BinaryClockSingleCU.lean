/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.BinaryClockSignalWord
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.BinaryClockSignalCost
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.SingleControlledOracleBridge
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanSubstitution
import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel

/-!
# Lowering binary clock words to one controlled oracle

This module transports the controlled-oracle bridge into the binary clock register layout.
`body` implements the nested signal oracle using one supplied controlled-oracle query and two
explicit gates.

`lower` substitutes this bridge into an arbitrary signal word, preserving its action on the
initialized frame. `instructions` specializes the construction to midpoint simulation, retaining
the error and query bounds from quantum signal processing [LowChuang2017].

## Main statements

* `lower_intertwining`: the lowered word agrees with the original word on the bridge frame.
* `lower_resources`: lowering preserves queries and adds two gates per query.
* `instructions_full_output_error`: lowered midpoint simulation retains the framed error bound.

## References

* [Low and Chuang, 2017][LowChuang2017]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.BinaryClockSingleCU

open Matrix
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
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
open scoped Classical BigOperators Kronecker Matrix.Norms.L2Operator

/-- The binary clock signal simulator register before adding the bridge ancilla. -/
abbrev Old (q : ℕ) (H : Type) := BinaryClockSignalWord.Physical q H
/-- The binary clock signal simulator register with one additional Boolean bridge ancilla. -/
abbrev New (q : ℕ) (H : Type) := Bool × Old q H
/-- The clock and two simulator flags left untouched by the controlled-oracle bridge. -/
abbrev Spectators (q : ℕ) := Reg q × (Bool × Bool)

noncomputable local instance oldDecidableEq (q : ℕ) (H : Type) [DecidableEq H] :
    DecidableEq (Old q H) :=
  inferInstanceAs (DecidableEq (Reg q × (Bool × (Bool × (Bool × (Bool × H))))))

noncomputable local instance newDecidableEq (q : ℕ) (H : Type) [DecidableEq H] :
    DecidableEq (New q H) :=
  @instDecidableEqProd Bool (Old q H) inferInstance (oldDecidableEq q H)

/-- Rectangular complex matrix multiplication with its finite intermediate index type specified
explicitly. -/
private noncomputable abbrev matmul {X Y Z : Type*} [Fintype Y]
    (A : Matrix X Y ℂ) (B : Matrix Y Z ℂ) : Matrix X Z ℂ :=
  @HMul.hMul (Matrix X Y ℂ) (Matrix Y Z ℂ) (Matrix X Z ℂ)
    Matrix.instHMulOfFintypeOfMulOfAddCommMonoid A B

/-- Rearrange the old simulator coordinates into spectator registers and the logical bridge
register. -/
def oldRead (q : ℕ) (H : Type) :
    Old q H ≃ Spectators q × SingleControlledOracleBridge.Logical H where
  toFun
    | (clock,(e,(a,(b,(c,i))))) => ((clock,(a,c)),((e,b),i))
  invFun
    | ((clock,(a,c)),((e,b),i)) => (clock,(e,(a,(b,(c,i)))))
  left_inv := by rintro ⟨clock,e,a,b,c,i⟩; rfl
  right_inv := by rintro ⟨⟨clock,a,c⟩,⟨e,b⟩,i⟩; rfl

/-- Rearrange the enlarged simulator coordinates into spectator registers and the physical
bridge register. -/
def coordinates (q : ℕ) (H : Type) :
    New q H ≃ Spectators q × SingleControlledOracleBridge.Physical H where
  toFun
    | (t,(clock,(e,(a,(b,(c,i)))))) => ((clock,(a,c)),((e,b),(t,i)))
  invFun
    | ((clock,(a,c)),((e,b),(t,i))) => (t,(clock,(e,(a,(b,(c,i))))))
  left_inv := by rintro ⟨t,clock,e,a,b,c,i⟩; rfl
  right_inv := by rintro ⟨⟨clock,a,c⟩,⟨e,b⟩,t,i⟩; rfl

section Body

variable {H : Type} [Fintype H] [DecidableEq H]

/-- Extend a bridge matrix by the spectator identity and relabel it into the enlarged simulator
coordinates. -/
noncomputable def lift (q : ℕ)
    (M : Matrix (SingleControlledOracleBridge.Physical H)
      (SingleControlledOracleBridge.Physical H) ℂ) : Matrix (New q H) (New q H) ℂ :=
  relabelGate (coordinates q H).symm (parallelOracle (J := Spectators q) M)

/-- The supplied single controlled oracle lifted into the enlarged binary clock register. -/
noncomputable def oracle (q : ℕ) (U : Matrix H H ℂ) : Matrix (New q H) (New q H) ℂ :=
  lift q (SingleControlledOracleBridge.supplied U)

/-- The lifted controlled-oracle bridge word for the false bridge-ancilla initialization. -/
noncomputable def body (q : ℕ) : List (AdjointStep (New q H)) :=
  phaseLiftWord (lift q) (SingleControlledOracleBridge.word false)

/-- Lifting the identity bridge matrix gives the identity enlarged simulator matrix. -/
private theorem lift_one (q : ℕ) : lift q (1 : Matrix
    (SingleControlledOracleBridge.Physical H) (SingleControlledOracleBridge.Physical H) ℂ) = 1 := by
  simp only [lift, parallelOracle, parallel_select_one, CircuitRelabel.relabelGate_one]

/-- Lifting bridge matrices preserves multiplication. -/
private theorem lift_mul (q : ℕ) (M N : Matrix
    (SingleControlledOracleBridge.Physical H) (SingleControlledOracleBridge.Physical H) ℂ) :
    lift q (M * N) = lift q M * lift q N := by
  unfold lift
  rw [← CircuitRelabel.relabelGate_mul]
  congr 1
  exact (parallel_select_mul _ _).symm

/-- Relabeling a matrix commutes with conjugate transpose. -/
private theorem relabel_adjoint {X Y : Type} (e : X ≃ Y) (M : Matrix X X ℂ) :
    relabelGate e Mᴴ = (relabelGate e M)ᴴ := by
  ext x y
  rfl

omit [Fintype H] [DecidableEq H] in

/-- Lifting a bridge matrix commutes with conjugate transpose. -/
private theorem lift_adjoint (q : ℕ) (M : Matrix
    (SingleControlledOracleBridge.Physical H) (SingleControlledOracleBridge.Physical H) ℂ) :
    lift q Mᴴ = (lift q M)ᴴ := by
  unfold lift
  rw [← parallelOracle_adjoint, relabel_adjoint]

/-- Lifting a unitary bridge matrix gives a unitary matrix on the enlarged simulator register. -/
theorem lift_unitary (q : ℕ) {M : Matrix (SingleControlledOracleBridge.Physical H)
    (SingleControlledOracleBridge.Physical H) ℂ}
    (hM : M ∈ Matrix.unitaryGroup _ ℂ) : lift q M ∈ Matrix.unitaryGroup _ ℂ :=
  (relabelGate_mem_unitaryGroup (coordinates q H).symm _).2 (parallelOracle_unitary hM)

/-- The supplied enlarged-register oracle is unitary when `U` is unitary. -/
theorem oracle_unitary (q : ℕ) {U : Matrix H H ℂ} (hU : U ∈ Matrix.unitaryGroup H ℂ) :
    oracle q U ∈ Matrix.unitaryGroup _ ℂ :=
  lift_unitary q (SingleControlledOracleBridge.supplied_unitary hU)

/-- The lifted controlled-oracle bridge body is well formed. -/
theorem body_wellFormed (q : ℕ) : WellFormedAdjointCircuit (body (H := H) q) :=
  phaseLiftWord_wellFormed (lift q) (fun _ h => lift_unitary q h)
    (SingleControlledOracleBridge.word_wellFormed false)

omit [Fintype H] in

/-- The bridge body uses exactly one oracle query and two explicit gates. -/
theorem body_counts (q : ℕ) : adjointQueryCount (body (H := H) q) = 1 ∧
    adjointGateCount (body (H := H) q) = 2 := by
  have hc := phaseLiftWord_counts (lift (H := H) q)
    (SingleControlledOracleBridge.word (H := H) false)
  exact ⟨hc.1.trans (SingleControlledOracleBridge.word_counts false).1,
    hc.2.trans (SingleControlledOracleBridge.word_counts false).2⟩

/-- The lifted bridge body's evaluation equals the lift of the original bridge word's
evaluation. -/
theorem body_evaluate (q : ℕ) (U : Matrix H H ℂ) :
    evaluate (oracle q U) (body q) =
      lift q (evaluate (SingleControlledOracleBridge.supplied U)
        (SingleControlledOracleBridge.word false)) :=
  phaseLiftWord_evaluate (lift q) (lift_one q) (lift_mul q) (lift_adjoint q)
    (SingleControlledOracleBridge.supplied U) (SingleControlledOracleBridge.word false)

/-- The bridge initialization frame extended by the identity on all spectator registers. -/
noncomputable def canonicalFrame (q : ℕ) :
    Matrix (Spectators q × SingleControlledOracleBridge.Physical H)
      (Spectators q × SingleControlledOracleBridge.Logical H) ℂ :=
  (1 : Matrix (Spectators q) (Spectators q) ℂ) ⊗ₖ SingleControlledOracleBridge.frame

omit [Fintype H] in

/-- The canonical frame has entry one exactly on the false bridge-ancilla fiber with matching
logical and spectator labels. -/
private theorem canonicalFrame_entry (q : ℕ) (j k : Spectators q)
    (ab cd : SingleControlledOracleBridge.Labels) (t : Bool) (i l : H) :
    canonicalFrame q (j,(ab,(t,i))) (k,(cd,l)) =
      if t = false ∧ (j,(ab,i)) = (k,(cd,l)) then 1 else 0 := by
  by_cases hj : j = k <;> by_cases hab : ab = cd <;>
    by_cases ht : t = false <;> by_cases hi : i = l <;>
    simp [canonicalFrame, SingleControlledOracleBridge.frame,
      Prod.mk.injEq, hj, hab, ht, hi]

omit [Fintype H] in

/-- Reindexing the canonical bridge frame into the old and new layouts gives the standard
false-ancilla frame. -/
theorem frame_transport (q : ℕ) :
    Matrix.reindex (coordinates q H).symm (oldRead q H).symm (canonicalFrame q) =
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame (H := Old q H) := by
  ext ⟨t,⟨clock,e,a,b,c,i⟩⟩ ⟨clock',e',a',b',c',l⟩
  change canonicalFrame q ((clock,(a,c)),((e,b),(t,i)))
      ((clock',(a',c')),((e',b'),l)) = _
  rw [canonicalFrame_entry]
  have heq :
      ((clock,(a,c)),((e,b),i)) = ((clock',(a',c')),((e',b'),l)) ↔
      (clock,(e,(a,(b,(c,i))))) = (clock',(e',(a',(b',(c',l))))) := by
    constructor
    · intro hread
      apply (oldRead q H).injective
      exact hread
    · intro hphysical
      exact congrArg (oldRead q H) hphysical
  simp only [heq, Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame,
      encodingFiber, Matrix.of_apply]

omit [Fintype H] in

/-- The bridge reference oracle, extended by spectators and relabeled, equals the nested binary
clock signal oracle. -/
theorem reference_transport (q : ℕ) (U : Matrix H H ℂ) :
    relabelGate (oldRead q H).symm
      (parallelOracle (J := Spectators q) (SingleControlledOracleBridge.reference U)) =
      BinaryClockSignalWord.nestedOracle q U := by
  ext ⟨clock,e,a,b,c,i⟩ ⟨clock',e',a',b',c',l⟩
  cases e <;> cases e' <;> cases b <;> cases b' <;>
    simp [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, oldRead,
      BinaryClockSignalWord.nestedOracle, BinaryClockSignalWord.signalOracle,
      parallelOracle, controlOracle, select, SingleControlledOracleBridge.reference,
      TensorGate, Matrix.one_apply, Prod.mk.injEq,
      ite_and, ite_mul, mul_ite]
  all_goals split_ifs <;> simp_all

/-- Left multiplication by a relabeled square matrix commutes with simultaneous row and column
reindexing of a rectangular matrix. -/
private theorem reindex_left {X X' Y Y' : Type} [Fintype X] [Fintype X']
    (e : X ≃ X') (f : Y ≃ Y') (M : Matrix X X ℂ) (R : Matrix X Y ℂ) :
    matmul (relabelGate e M) (Matrix.reindex e f R) = Matrix.reindex e f (matmul M R) := by
  exact Matrix.submatrix_mul_equiv M R e.symm e.symm f.symm

/-- Right multiplication by a relabeled square matrix commutes with simultaneous row and column
reindexing of a rectangular matrix. -/
private theorem reindex_right {X X' Y Y' : Type} [Fintype Y] [Fintype Y']
    (e : X ≃ X') (f : Y ≃ Y') (R : Matrix X Y ℂ) (M : Matrix Y Y ℂ) :
    matmul (Matrix.reindex e f R) (relabelGate f M) = Matrix.reindex e f (matmul R M) := by
  exact Matrix.submatrix_mul_equiv R M e.symm f.symm f.symm

/-- On the canonical frame, the spectator-extended bridge evaluation agrees with the
spectator-extended reference oracle. -/
private theorem canonical_forward (q : ℕ) (U : Matrix H H ℂ) :
    matmul (parallelOracle (J := Spectators q)
      (evaluate (SingleControlledOracleBridge.supplied U)
        (SingleControlledOracleBridge.word false))) (canonicalFrame q) =
    matmul (canonicalFrame q)
      (parallelOracle (J := Spectators q) (SingleControlledOracleBridge.reference U)) := by
  have hd := SingleControlledOracleBridge.word_intertwining U false
  change matmul (evaluate (SingleControlledOracleBridge.supplied U)
      (SingleControlledOracleBridge.word false)) SingleControlledOracleBridge.frame =
    matmul SingleControlledOracleBridge.frame (SingleControlledOracleBridge.reference U) at hd
  unfold matmul at hd
  simp only [parallelOracle_eq_kronecker, canonicalFrame, matmul]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hd]

/-- The evaluated bridge body intertwines the nested signal oracle through the false-ancilla
frame. -/
theorem body_forward (q : ℕ) (U : Matrix H H ℂ) :
    matmul (evaluate (oracle q U) (body q)) Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame =
      matmul Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame (BinaryClockSignalWord.nestedOracle q U) := by
  let B := evaluate (SingleControlledOracleBridge.supplied U)
    (SingleControlledOracleBridge.word false)
  let O := parallelOracle (J := Spectators q) (SingleControlledOracleBridge.reference U)
  let e := (coordinates q H).symm
  let f := (oldRead q H).symm
  calc
    _ = matmul (relabelGate e (parallelOracle (J := Spectators q) B))
        (Matrix.reindex e f (canonicalFrame q)) := by
      exact congrArg₂ (fun M R => matmul M R)
        (body_evaluate q U) (frame_transport q).symm
    _ = Matrix.reindex e f
        (matmul (parallelOracle (J := Spectators q) B) (canonicalFrame q)) :=
      reindex_left e f _ _
    _ = Matrix.reindex e f (matmul (canonicalFrame q) O) := by
      rw [canonical_forward]
    _ = matmul (Matrix.reindex e f (canonicalFrame q)) (relabelGate f O) :=
      (reindex_right e f _ _).symm
    _ = _ := by rw [frame_transport, reference_transport]

/-- Replace oracle instructions in an old-register word by the bridge body, lifting its gates to
the enlarged register. -/
noncomputable def lower (q : ℕ) (cs : List (AdjointStep (Old q H))) :
    List (AdjointStep (New q H)) := Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.instructions (body q) cs

/-- For unitary `U`, the lowered word intertwines the original nested-oracle evaluation through
the bridge frame. -/
theorem lower_intertwining (q : ℕ) (U : Matrix H H ℂ)
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (cs : List (AdjointStep (Old q H))) :
    matmul (evaluate (oracle q U) (lower q cs)) Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame =
      matmul Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame (evaluate (BinaryClockSignalWord.nestedOracle q U) cs) :=
  Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.intertwining (oracle q U) (BinaryClockSignalWord.nestedOracle q U)
    (body q) cs (oracle_unitary q hU) (BinaryClockSignalWord.nestedOracle_unitary q U hU)
    (body_wellFormed q) (body_forward q U)

/-- For unitary `U`, a lowered word acts on every framed state exactly as the original word acts
before framing. -/
theorem lower_coherent (q : ℕ) (U : Matrix H H ℂ) (hU : U ∈ Matrix.unitaryGroup H ℂ)
    (cs : List (AdjointStep (Old q H))) (ψ : QState (Old q H)) :
    evaluate (oracle q U) (lower q cs) *ᵥ (Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame *ᵥ ψ) =
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame *ᵥ (evaluate (BinaryClockSignalWord.nestedOracle q U) cs *ᵥ ψ) :=
  Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.coherent (oracle q U) (BinaryClockSignalWord.nestedOracle q U)
    (body q) cs (oracle_unitary q hU) (BinaryClockSignalWord.nestedOracle_unitary q U hU)
    (body_wellFormed q) (body_forward q U) ψ

/-- Lowering a well-formed word preserves well-formedness and its query count, and adds two
explicit gates per query. -/
theorem lower_resources (q : ℕ) (U : Matrix H H ℂ) (cs : List (AdjointStep (Old q H)))
    (hcs : WellFormedAdjointCircuit cs) :
    WellFormedAdjointCircuit (lower q cs) ∧
      adjointQueryCount (lower q cs) = adjointQueryCount cs ∧
      adjointGateCount (lower q cs) = adjointGateCount cs + 2 * adjointQueryCount cs := by
  have hr :=
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.resources (oracle q U)
      (body q) cs (body_wellFormed q) hcs
  simpa only [lower, (body_counts (H := H) q).1, (body_counts (H := H) q).2,
    one_mul] using! hr

/-- The adjoint lowered word is well formed, preserves the original query count, and has the
original gate count plus two gates per query. -/
theorem inverse_resources (q : ℕ) (U : Matrix H H ℂ) (cs : List (AdjointStep (Old q H)))
    (hcs : WellFormedAdjointCircuit cs) :
    WellFormedAdjointCircuit (adjointCircuit (lower q cs)) ∧
      adjointQueryCount (adjointCircuit (lower q cs)) = adjointQueryCount cs ∧
      adjointGateCount (adjointCircuit (lower q cs)) =
        adjointGateCount cs + 2 * adjointQueryCount cs := by
  have hr := Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.inverse_resources (oracle q U) (body q) cs
    (body_wellFormed q) hcs
  simpa only [lower, (body_counts (H := H) q).1, (body_counts (H := H) q).2,
    one_mul] using! hr

/-- For unitary `U` and a well-formed original word, the adjoint lowered evaluation intertwines
the original adjoint evaluation through the bridge frame. -/
theorem lower_inverse_intertwining (q : ℕ) (U : Matrix H H ℂ)
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (cs : List (AdjointStep (Old q H)))
    (hcs : WellFormedAdjointCircuit cs) :
    matmul (evaluate (oracle q U) (adjointCircuit (lower q cs))) Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame =
      matmul Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame
        (evaluate (BinaryClockSignalWord.nestedOracle q U) (adjointCircuit cs)) :=
  Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.inverse_intertwining (oracle q U) (BinaryClockSignalWord.nestedOracle q U)
    (body q) cs (oracle_unitary q hU) (BinaryClockSignalWord.nestedOracle_unitary q U hU)
    (body_wellFormed q) hcs (body_forward q U)

end Body

section Actual

variable {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

/-- Lower the complete binary clock signal word to the supplied single controlled oracle. -/
noncomputable def instructions (q : ℕ) (F : Matrix H I ℂ) (τ : ℚ) (k : ℕ) :
    List (AdjointStep (New q H)) :=
  lower q (BinaryClockSignalWord.instructions q F τ k)

/-- Compose the bridge's false-ancilla frame with the binary clock signal word's common frame. -/
noncomputable def initialFrame (q : ℕ) (F : Matrix H I ℂ) :
    Matrix (New q H) (Reg q × I) ℂ :=
  matmul Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame (BinaryClockSignalWord.commonFrame q F)

/-- The lowered simulator's initial frame is an isometry for the stated projected unitary
encoding. -/
theorem initialFrame_isometry (q : ℕ) (A : Matrix I I ℂ) (U : Matrix H H ℂ)
    (F : Matrix H I ℂ) (hA : A.IsHermitian) (h : ProjectedUnitaryEncoding A U F F) :
    IsIsometry (initialFrame q F) :=
  Qatlib.Concepts.BlockEncoding.EncodingCore.IsIsometry.mul Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame_isometry
    (BinaryClockSignalWord.commonFrame_isometry q A U F hA h)

/-- The lowered midpoint word approximates the dyadic target on its initial frame within
`(q+1)*2⁻ᵏ` times the input norm. -/
theorem instructions_full_output_error (q : ℕ) (A : Matrix I I ℂ) (U : Matrix H H ℂ)
    (F : Matrix H I ℂ) (τ : ℚ) (k : ℕ)
    (hA : A.IsHermitian) (h : ProjectedUnitaryEncoding A U F F)
    (Ψ : QState (Reg q × I)) :
    ‖toEuclidean_fromVec
      (evaluate (oracle q U) (instructions q F τ k) *ᵥ (initialFrame q F *ᵥ Ψ) -
        initialFrame q F *ᵥ
          (BinaryClockSignalWord.target q A τ (DyadicClockPulses.axes q) *ᵥ Ψ))‖ ≤
      ((q + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ k * ‖toEuclidean_fromVec Ψ‖ := by
  let V := BinaryClockSignalWord.target q A τ (DyadicClockPulses.axes q)
  have hi (φ : QState (Reg q × I)) : initialFrame q F *ᵥ φ =
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame *ᵥ (BinaryClockSignalWord.commonFrame q F *ᵥ φ) :=
    (Matrix.mulVec_mulVec φ _ _).symm
  have hr := lower_coherent q U h.unitary (BinaryClockSignalWord.instructions q F τ k)
    (BinaryClockSignalWord.commonFrame q F *ᵥ Ψ)
  have hs :
      evaluate (oracle q U) (instructions q F τ k) *ᵥ (initialFrame q F *ᵥ Ψ) -
        initialFrame q F *ᵥ (V *ᵥ Ψ) =
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame *ᵥ
        (evaluate (BinaryClockSignalWord.nestedOracle q U)
          (BinaryClockSignalWord.instructions q F τ k) *ᵥ
            (BinaryClockSignalWord.commonFrame q F *ᵥ Ψ) -
          BinaryClockSignalWord.commonFrame q F *ᵥ (V *ᵥ Ψ)) := by
    rw [hi Ψ, hi (V *ᵥ Ψ)]
    change evaluate (oracle q U) (lower q (BinaryClockSignalWord.instructions q F τ k)) *ᵥ
        (Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame *ᵥ (BinaryClockSignalWord.commonFrame q F *ᵥ Ψ)) - _ = _
    rw [hr, Matrix.mulVec_sub]
  change ‖toEuclidean_fromVec
    (evaluate (oracle q U) (instructions q F τ k) *ᵥ (initialFrame q F *ᵥ Ψ) -
      initialFrame q F *ᵥ (V *ᵥ Ψ))‖ ≤ _
  rw [hs,
      isometry_mulVec_norm Qatlib.Concepts.AmplitudeCore.PreparedReadout.CleanOracleSubstitution.frame_isometry]
  simpa only [V, BinaryClockSignalWord.instructions, DyadicClockPulses.axes_length] using!
    BinaryClockSignalWord.program_full_output_error q A U F τ k
      (DyadicClockPulses.axes q) hA h Ψ

/-- The lowered midpoint word is well formed, preserves the signal word's query count, and adds
two gates per signal query. -/
theorem instructions_resources (q : ℕ) (A : Matrix I I ℂ) (U : Matrix H H ℂ)
    (F : Matrix H I ℂ) (τ : ℚ) (k : ℕ)
    (hA : A.IsHermitian) (h : ProjectedUnitaryEncoding A U F F) :
    WellFormedAdjointCircuit (instructions q F τ k) ∧
      adjointQueryCount (instructions q F τ k) =
        adjointQueryCount (BinaryClockSignalWord.instructions q F τ k) ∧
      adjointGateCount (instructions q F τ k) =
        adjointGateCount (BinaryClockSignalWord.instructions q F τ k) +
          2 * adjointQueryCount (BinaryClockSignalWord.instructions q F τ k) :=
  lower_resources q U _ (BinaryClockSignalWord.instructions_resources q A U F τ k hA h).1

/-- The lowered midpoint word evaluates to a unitary matrix for the stated Hermitian encoding. -/
theorem instructions_unitary (q : ℕ) (A : Matrix I I ℂ) (U : Matrix H H ℂ)
    (F : Matrix H I ℂ) (τ : ℚ) (k : ℕ)
    (hA : A.IsHermitian) (h : ProjectedUnitaryEncoding A U F F) :
    evaluate (oracle q U) (instructions q F τ k) ∈ Matrix.unitaryGroup _ ℂ :=
  (instructions_resources q A U F τ k hA h).1.evaluate_unitary (oracle_unitary q h.unitary)

/-- The lowered midpoint word satisfies the explicit query bound
`27*((q+1)+2*|τ|)*(128*(k+clog₂(rMax τ)+16)+1)`. -/
theorem instructions_query_bound (q : ℕ) (A : Matrix I I ℂ) (U : Matrix H H ℂ)
    (F : Matrix H I ℂ) (τ : ℚ) (k : ℕ)
    (hA : A.IsHermitian) (h : ProjectedUnitaryEncoding A U F F) :
    (adjointQueryCount (instructions q F τ k) : ℚ) ≤
      27 * (((q + 1 : ℕ) : ℚ) + 2 * |τ|) *
        (128 * ((k + Nat.clog 2 (BinaryClockSignalCost.rMax τ) + 16 : ℕ) : ℚ) + 1) := by
  rw [(instructions_resources q A U F τ k hA h).2.1]
  exact BinaryClockSignalCost.instructions_query_bound q A U F τ k hA h

end Actual

end Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.BinaryClockSingleCU
