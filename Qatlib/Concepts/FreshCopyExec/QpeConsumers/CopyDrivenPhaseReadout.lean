/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.Discriminate.ControlledCopyEvolution
import Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.ReferenceError.DensityToRaw
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.FreshCopyExec.QpeConsumers

open Matrix
open Qatlib
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open scoped Classical ComplexOrder

set_option autoImplicit false

noncomputable def copyQPERegisterEquiv (D M : ℕ) :
    Fin M × (Bool × Fin D) ≃ Fin M × Fin (2 * D) :=
  Equiv.prodCongr (Equiv.refl (Fin M)) (controlDataEquiv D)

noncomputable def copyQPEQuery (D M n : ℕ) (ρ : Operator D)
    (X : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ) :
    Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ :=
  relabelGate (copyQPERegisterEquiv D M).symm
    (ChannelAmplification (controlledCopyRunMap ρ Real.pi n) M
      (relabelGate (copyQPERegisterEquiv D M) X))

noncomputable def copyQPEProgram (D M n : ℕ) (ρ : Operator D) :
    Circuit (Fin M × (Bool × Fin D)) →
      Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ →
      Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ
  | [], X => X
  | Step.gate U :: C, X => copyQPEProgram D M n ρ C (MatrixMap.conj U X)
  | Step.query :: C, X => copyQPEProgram D M n ρ C (copyQPEQuery D M n ρ X)

noncomputable def copyQPEIdealProgram (D M : ℕ) (ρ : Operator D) :
    Circuit (Fin M × (Bool × Fin D)) →
      Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ →
      Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ
  | [], X => X
  | Step.gate U :: C, X => copyQPEIdealProgram D M ρ C (MatrixMap.conj U X)
  | Step.query :: C, X => copyQPEIdealProgram D M ρ C
      (MatrixMap.conj (TensorGate (1 : Operator M)
        (controlOracle (hamiltonianEvolution ρ Real.pi))) X)

noncomputable def copyQPEInput (D M : ℕ) (ρ : Operator D) :
    Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ :=
  if hM : 0 < M then
    TensorGate (outerProduct (Ket (⟨0, hM⟩ : Fin M)))
      (TensorGate (outerProduct (Ket false)) ρ)
  else 0

noncomputable def copyQPEOutput (D M n : ℕ) (ρ : Operator D) :
    Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ :=
  copyQPEProgram D M n ρ (countedPhaseCircuit M) (copyQPEInput D M ρ)

noncomputable def copyQPEIdealOutput (D M : ℕ) (ρ : Operator D) :
    Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ :=
  copyQPEIdealProgram D M ρ (countedPhaseCircuit M) (copyQPEInput D M ρ)

noncomputable def copyQPELabelMass (D M : ℕ)
    (X : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ)
    (z : Fin M) : ℝ :=
  (Matrix.trace (X.submatrix (fun p => (z, p)) (fun p => (z, p)))).re

theorem copyQPELabelMass_nonneg (D M : ℕ)
    (X : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ)
    (hX : X.PosSemidef) (z : Fin M) : 0 ≤ copyQPELabelMass D M X z :=
  (RCLike.nonneg_iff.mp (hX.submatrix (fun p => (z, p))).trace_nonneg).1

theorem copyQPELabelMass_sum (D M : ℕ)
    (X : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ) :
    (∑ z, copyQPELabelMass D M X z) = (Matrix.trace X).re := by
  simp only [copyQPELabelMass, Matrix.trace, Matrix.diag_apply,
    Matrix.submatrix_apply, Fintype.sum_prod_type, Complex.re_sum]

def copyQPEProgramResources {I : Type*} (n : ℕ) : Circuit I → ℕ × ℕ × ℕ × ℕ
  | [] => (0, 0, 0, 0)
  | Step.gate _ :: C => copyQPEProgramResources n C
  | Step.query :: C =>
      let r := copyQPEProgramResources n C
      (r.1 + n, r.2.1 + n, r.2.2.1 + n, r.2.2.2)

noncomputable def copyQPEResources (D M n : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  copyQPEProgramResources n (countedPhaseCircuit (I := Fin D) M)

noncomputable def copyQPEFixedMacros (D M : ℕ) : ℕ :=
  GateCount (countedPhaseCircuit (I := Fin D) M)

theorem copyQPEProgramResources_eq {I : Type*} (n : ℕ) (C : Circuit I) :
    copyQPEProgramResources n C =
      (QueryCount C * n, QueryCount C * n, QueryCount C * n, 0) := by
  induction C with
  | nil => simp [copyQPEProgramResources, QueryCount]
  | cons s C ih =>
    cases s <;> simp [copyQPEProgramResources, QueryCount, ih, Nat.add_mul]

theorem copy_qpe_same_path_fresh_resource_counts
    (D M n : ℕ) (hM : 2 ≤ M) (_hn : 0 < n) :
    copyQPEResources D M n =
      ((M - 1) * n, (M - 1) * n, (M - 1) * n, 0) := by
  have h := counted_offgrid_qpe_clean_flag M (by omega)
    (1 : Operator D) (0 : QState (Fin D))
  rw [copyQPEResources, copyQPEProgramResources_eq, h.2.1]

theorem copyQPEFixedMacros_eq (D M : ℕ) (hM : 0 < M) :
    copyQPEFixedMacros D M = 2 * (M - 1) + 2 := by
  exact (counted_offgrid_qpe_clean_flag M hM
    (1 : Operator D) (0 : QState (Fin D))).2.2.1

private theorem copy_relabel_positive {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) {X : Matrix I I ℂ} (hX : X.PosSemidef) :
    (relabelGate e X).PosSemidef := hX.submatrix e.symm

private theorem copy_relabel_trace {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (X : Matrix I I ℂ) :
    Matrix.trace (relabelGate e X) = Matrix.trace X := by
  simp only [Matrix.trace, Matrix.diag_apply, relabelGate_apply']
  exact Equiv.sum_comp e.symm (fun i => X i i)

theorem copyQPEQuery_positive_trace (D M n : ℕ) (ρ : Operator D)
    (hρ : IsDensityOperator ρ)
    (X : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ)
    (hX : X.PosSemidef) :
    (copyQPEQuery D M n ρ X).PosSemidef ∧
      Matrix.trace (copyQPEQuery D M n ρ X) = Matrix.trace X := by
  have hmap := controlledCopyRun_map ρ hρ Real.pi n
  unfold copyQPEQuery
  rw [← hmap]
  constructor
  · exact copy_relabel_positive _
      ((controlledCopyRun ρ hρ Real.pi n).completelyPositive M _
        (copy_relabel_positive _ hX))
  · rw [copy_relabel_trace, amplification_trace _
      (controlledCopyRun ρ hρ Real.pi n).tracePreserving, copy_relabel_trace]

theorem copyQPEProgram_positive_trace (D M n : ℕ) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (C : Circuit (Fin M × (Bool × Fin D)))
    (hC : IsUnitaryCircuit C)
    (X : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ)
    (hX : X.PosSemidef) :
    (copyQPEProgram D M n ρ C X).PosSemidef ∧
      Matrix.trace (copyQPEProgram D M n ρ C X) = Matrix.trace X := by
  induction C generalizing X with
  | nil => exact ⟨hX, rfl⟩
  | cons s C ih =>
    cases s with
    | query =>
      have hq := copyQPEQuery_positive_trace D M n ρ hρ X hX
      have ht := ih (isUnitaryCircuit_query C |>.mp hC) _ hq.1
      exact ⟨ht.1, ht.2.trans hq.2⟩
    | gate U =>
      obtain ⟨hU, hC'⟩ := (isUnitaryCircuit_gate U C).mp hC
      have ht := ih hC' (MatrixMap.conj U X) (hX.mul_mul_conjTranspose_same U)
      refine ⟨ht.1, ht.2.trans ?_⟩
      change Matrix.trace (U * X * Uᴴ) = Matrix.trace X
      rw [Matrix.trace_mul_cycle]
      have hu : Uᴴ * U = 1 := by
        simpa only [Matrix.star_eq_conjTranspose] using
          (Matrix.mem_unitaryGroup_iff').mp hU
      rw [hu, Matrix.one_mul]

theorem copyQPEInput_density (D M : ℕ) (hM : 0 < M) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) :
    (copyQPEInput D M ρ).PosSemidef ∧ Matrix.trace (copyQPEInput D M ρ) = 1 := by
  rw [copyQPEInput, dif_pos hM]
  constructor
  · exact (outerProduct_posSemidef _).kronecker
      ((outerProduct_posSemidef _).kronecker hρ.1)
  · rw [Qatlib.Foundations.PureStateMath.BornBridge.trace_tensorGate, Qatlib.Foundations.PureStateMath.BornBridge.trace_tensorGate,
      (outerProduct_density (normalized_ket (⟨0, hM⟩ : Fin M))).2,
      (outerProduct_density (normalized_ket false)).2, hρ.2]
    simp

theorem copyQPEOutput_density (D M n : ℕ) (hM : 0 < M) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) :
    (copyQPEOutput D M n ρ).PosSemidef ∧ Matrix.trace (copyQPEOutput D M n ρ) = 1 := by
  have hC := (counted_offgrid_qpe_clean_flag M hM
    (1 : Operator D) (0 : QState (Fin D))).2.2.2
  have hX := copyQPEInput_density D M hM ρ hρ
  have h := copyQPEProgram_positive_trace D M n ρ hρ _ hC _ hX.1
  exact ⟨h.1, h.2.trans hX.2⟩

private theorem copyQPE_ideal_gate_relabel (D M : ℕ) (ρ : Operator D) :
    relabelGate (copyQPERegisterEquiv D M)
      (TensorGate (1 : Operator M) (controlOracle (hamiltonianEvolution ρ Real.pi))) =
      TensorGate (1 : Operator M) (copyControlledEvolution ρ Real.pi) := by
  ext ⟨a,i⟩ ⟨b,j⟩
  rfl

private theorem copyQPE_relabel_conj {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (U X : Matrix I I ℂ) :
    relabelGate e (MatrixMap.conj U X) =
      MatrixMap.conj (relabelGate e U) (relabelGate e X) := by
  let f := Matrix.reindexAlgEquiv ℂ ℂ e
  have hs : f Uᴴ = (f U)ᴴ := by ext i j; rfl
  change f (U * X * Uᴴ) = f U * f X * (f U)ᴴ
  rw [map_mul, map_mul, hs]

private theorem copyQPE_relabel_sub {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (X Y : Matrix I I ℂ) :
    relabelGate e (X - Y) = relabelGate e X - relabelGate e Y :=
  (Matrix.reindexAlgEquiv ℂ ℂ e).map_sub X Y

private theorem copyQPE_relabel_round {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (X : Matrix J J ℂ) :
    relabelGate e (relabelGate e.symm X) = X := by
  ext i j
  simp only [relabelGate_apply', Equiv.symm_symm, Equiv.apply_symm_apply]

private theorem copyQPEQuery_sub (D M n : ℕ) (ρ : Operator D)
    (X Y : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ) :
    copyQPEQuery D M n ρ (X - Y) = copyQPEQuery D M n ρ X - copyQPEQuery D M n ρ Y := by
  unfold copyQPEQuery
  rw [copyQPE_relabel_sub, amplification_sub, copyQPE_relabel_sub]

private theorem copyQPEQuery_contraction (D M n : ℕ) (ρ : Operator D)
    (hρ : IsDensityOperator ρ)
    (X : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ) (hX : X.IsHermitian) :
    (copyQPEQuery D M n ρ X).traceNorm ≤ X.traceNorm := by
  let e := copyQPERegisterEquiv D M
  have hY : (relabelGate e X).IsHermitian := hX.submatrix e.symm
  have hmap := controlledCopyRun_map ρ hρ Real.pi n
  have ha := channel_reference_hermitian_preserving (controlledCopyRun ρ hρ Real.pi n) hY
  unfold copyQPEQuery
  rw [← hmap, traceNorm_relabel_hermitian _ _ ha]
  have h := channel_reference_hermitian_trace_contraction (controlledCopyRun ρ hρ Real.pi n) hY
  exact h.trans_eq (traceNorm_relabel_hermitian e X hX)

theorem copyQPEQuery_error (D M n : ℕ) (hn : 0 < n) (ρ : Operator D)
    (hρ : IsDensityOperator ρ)
    (X : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ) (hX : X.PosSemidef) :
    Matrix.traceNorm (copyQPEQuery D M n ρ X -
      MatrixMap.conj (TensorGate (1 : Operator M)
        (controlOracle (hamiltonianEvolution ρ Real.pi))) X) ≤
      8 * Real.pi ^ 2 / (n : ℝ) * (Matrix.trace X).re := by
  let e := copyQPERegisterEquiv D M
  let V := TensorGate (1 : Operator M) (controlOracle (hamiltonianEvolution ρ Real.pi))
  let Y := relabelGate e X
  have hY : Y.PosSemidef := hX.submatrix e.symm
  have hA := (copyQPEQuery_positive_trace D M n ρ hρ X hX).1
  have hB : (MatrixMap.conj V X).PosSemidef := hX.mul_mul_conjTranspose_same V
  have hnorm := traceNorm_relabel_hermitian e
    (copyQPEQuery D M n ρ X - MatrixMap.conj V X) (hA.isHermitian.sub hB.isHermitian)
  have hshape : relabelGate e (copyQPEQuery D M n ρ X - MatrixMap.conj V X) =
      ChannelAmplification (controlledCopyRun ρ hρ Real.pi n).map M Y -
        MatrixMap.conj (TensorGate (1 : Operator M) (copyControlledEvolution ρ Real.pi)) Y := by
    rw [copyQPE_relabel_sub, copyQPEQuery, copyQPE_relabel_round,
      ← controlledCopyRun_map, copyQPE_relabel_conj, copyQPE_ideal_gate_relabel]
  rw [hshape] at hnorm
  calc
    _ = _ := hnorm.symm
    _ ≤ 8 * Real.pi ^ 2 / (n : ℝ) * (Matrix.trace Y).re :=
      controlled_copy_fresh_global_error D M n hn ρ hρ Real.pi Y hY
    _ = _ := by rw [copy_relabel_trace]

private theorem copyQPE_conj_trace {I : Type*} [Fintype I] [DecidableEq I]
    (U X : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) :
    Matrix.trace (MatrixMap.conj U X) = Matrix.trace X := by
  change Matrix.trace (U * X * Uᴴ) = Matrix.trace X
  rw [Matrix.trace_mul_cycle]
  have hu : Uᴴ * U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff').mp hU
  rw [hu, Matrix.one_mul]

private theorem copyQPE_conj_difference_norm {I : Type*} [Fintype I] [DecidableEq I]
    (U A B : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) :
    (MatrixMap.conj U A - MatrixMap.conj U B).traceNorm = (A - B).traceNorm := by
  rw [← (MatrixMap.conj U).map_sub]
  have hh : Uᴴ * U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff').mp hU
  letI : DecidableEq I := Classical.decEq I
  have hu : U.Isometry := by
    change Uᴴ * U = 1
    convert hh using 1 <;> first
      | exact Subsingleton.elim _ _
      | (ext i j; simp [Matrix.one_apply])
  change (U * (A - B) * Uᴴ).traceNorm = (A - B).traceNorm
  rw [Matrix.traceNorm_isometry_right hu, Matrix.traceNorm_isometry_left hu]

theorem copyQPEProgram_input_and_access_error (D M n : ℕ) (hn : 0 < n)
    (ρ : Operator D) (hρ : IsDensityOperator ρ)
    (C : Circuit (Fin M × (Bool × Fin D))) (hC : IsUnitaryCircuit C)
    (A B : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (copyQPEProgram D M n ρ C A - copyQPEIdealProgram D M ρ C B).traceNorm ≤
      (A - B).traceNorm +
        (8 * Real.pi ^ 2 / (n : ℝ)) * (QueryCount C : ℝ) * (Matrix.trace B).re := by
  let V := TensorGate (1 : Operator M) (controlOracle (hamiltonianEvolution ρ Real.pi))
  have hV : V ∈ Matrix.unitaryGroup (Fin M × (Bool × Fin D)) ℂ :=
    tensorGate_unitary (Submonoid.one_mem _)
      (controlOracle_unitary (hamiltonianEvolution_unitary hρ.1.isHermitian Real.pi))
  induction C generalizing A B with
  | nil => simp [copyQPEProgram, copyQPEIdealProgram, QueryCount]
  | cons s C ih =>
    cases s with
    | gate U =>
      obtain ⟨hU, hC'⟩ := (isUnitaryCircuit_gate U C).mp hC
      have h := ih hC' (MatrixMap.conj U A) (MatrixMap.conj U B)
        (hA.mul_mul_conjTranspose_same U) (hB.mul_mul_conjTranspose_same U)
      rw [copyQPE_conj_trace U B hU, copyQPE_conj_difference_norm U A B hU] at h
      exact h
    | query =>
      have hC' := (isUnitaryCircuit_query C).mp hC
      have hA' := (copyQPEQuery_positive_trace D M n ρ hρ A hA).1
      have hB' : (MatrixMap.conj V B).PosSemidef := hB.mul_mul_conjTranspose_same V
      have h := ih hC' _ _ hA' hB'
      rw [copyQPE_conj_trace V B hV] at h
      have he : copyQPEQuery D M n ρ A - MatrixMap.conj V B =
          (copyQPEQuery D M n ρ A - copyQPEQuery D M n ρ B) +
            (copyQPEQuery D M n ρ B - MatrixMap.conj V B) := by abel
      have hc : (copyQPEQuery D M n ρ A - copyQPEQuery D M n ρ B).traceNorm ≤
          (A - B).traceNorm := by
        rw [← copyQPEQuery_sub]
        exact copyQPEQuery_contraction D M n ρ hρ _ (hA.isHermitian.sub hB.isHermitian)
      have hl := copyQPEQuery_error D M n hn ρ hρ B hB
      have ht := (Matrix.traceNorm_add_le _ _).trans (add_le_add hc hl)
      rw [← he] at ht
      have hsum := h.trans (add_le_add ht (le_refl _))
      exact hsum.trans_eq (by simp only [QueryCount, Nat.cast_add, Nat.cast_one]; ring)

theorem copy_qpe_actual_program_state_error
    (D M n : ℕ) (hM : 2 ≤ M) (hn : 0 < n) (ρ : Operator D) (hρ : IsDensityOperator ρ) :
    (copyQPEOutput D M n ρ).PosSemidef ∧ Matrix.trace (copyQPEOutput D M n ρ) = 1 ∧
      Matrix.traceNorm (copyQPEOutput D M n ρ - copyQPEIdealOutput D M ρ) ≤
        8 * (M - 1 : ℕ) * Real.pi ^ 2 / (n : ℝ) := by
  have hM0 : 0 < M := by omega
  have hC := counted_offgrid_qpe_clean_flag M hM0 (1 : Operator D) (0 : QState (Fin D))
  have hX := copyQPEInput_density D M hM0 ρ hρ
  have hout := copyQPEOutput_density D M n hM0 ρ hρ
  refine ⟨hout.1, hout.2, ?_⟩
  have h := copyQPEProgram_input_and_access_error D M n hn ρ hρ _ hC.2.2.2
    (copyQPEInput D M ρ) (copyQPEInput D M ρ) hX.1 hX.1
  rw [hC.2.1, hX.2, sub_self, Matrix.traceNorm_zero, Complex.one_re, mul_one, zero_add] at h
  exact h.trans_eq (by ring)

end Qatlib.Concepts.FreshCopyExec.QpeConsumers
