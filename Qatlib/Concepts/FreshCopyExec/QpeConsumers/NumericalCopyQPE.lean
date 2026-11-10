/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FreshCopyExec.QpeConsumers.NumericalControlledCopy
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.LocalCopyQPEConsumers
set_option warningAsError false
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.ReferenceError.DensityToRaw
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

noncomputable def numericCopyRun (n : ℕ) (rho : Operator (2^n)) (b k : ℕ) :
    Operator (2*(2^n)) → Operator (2*(2^n)) := (numericCopyFinStep n rho b k)^[2^b]
noncomputable def numericCopyQPEQuery (n M b k : ℕ) (rho : Operator (2^n))
    (X : Matrix (Fin M × (Bool × Fin (2^n))) (Fin M × (Bool × Fin (2^n))) ℂ) :=
  relabelGate (copyQPERegisterEquiv (2^n) M).symm
    (numericAmplification (numericCopyRun n rho b k) M
      (relabelGate (copyQPERegisterEquiv (2^n) M) X))
noncomputable def numericCopyQPEProgram (n M b k : ℕ) (rho : Operator (2^n)) :
    Circuit (Fin M × (Bool × Fin (2^n))) →
    Matrix (Fin M × (Bool × Fin (2^n))) (Fin M × (Bool × Fin (2^n))) ℂ →
    Matrix (Fin M × (Bool × Fin (2^n))) (Fin M × (Bool × Fin (2^n))) ℂ
  | [],X => X
  | Step.gate U :: C,X => numericCopyQPEProgram n M b k rho C (MatrixMap.conj U X)
  | Step.query :: C,X => numericCopyQPEProgram n M b k rho C (numericCopyQPEQuery n M b k rho X)
noncomputable def numericCopyQPEOutput (n M b k : ℕ) (rho : Operator (2^n)) :=
  numericCopyQPEProgram n M b k rho (countedPhaseCircuit M) (copyQPEInput (2^n) M rho)

theorem numericCopyRun_power (n b k : ℕ) (rho : Operator (2^n)) (s : ℕ) (X : Operator (2*(2^n))) :
    (numericCopyFinStep n rho b k)^[s] X =
      copyMapPower (controlledCopyChannelMap rho (copyPhaseEffectiveAngle b k)) s X := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [Function.iterate_succ_apply',ih,numericCopyFinStep_eq]
    rfl

theorem numericAmplification_run (n b k r : ℕ) (rho : Operator (2^n))
    (X : Matrix (Fin r × Fin (2*(2^n))) (Fin r × Fin (2*(2^n))) ℂ) :
    numericAmplification (numericCopyRun n rho b k) r X =
      ChannelAmplification (copyMapPower (controlledCopyChannelMap rho (copyPhaseEffectiveAngle b k)) (2^b)) r X := by
  ext x y
  simp only [numericAmplification,numericCopyRun,numericCopyRun_power,ChannelAmplification,Matrix.of_apply]

theorem numeric_channel_power_error {D : ℕ} (T S : QuantumChannel D D) (ε : ℝ)
    (hs : ∀ (r : ℕ) (X : Matrix (Fin r × Fin D) (Fin r × Fin D) ℂ),X.PosSemidef →
      (ChannelAmplification T.map r X-ChannelAmplification S.map r X).traceNorm ≤ ε*(Matrix.trace X).re)
    (s r : ℕ) (X : Matrix (Fin r × Fin D) (Fin r × Fin D) ℂ) (hX : X.PosSemidef) :
    (ChannelAmplification (copyChannelPower T s).map r X-
      ChannelAmplification (copyChannelPower S s).map r X).traceNorm ≤ (s:ℝ)*ε*(Matrix.trace X).re := by
  induction s with
  | zero => simp [copyChannelPower,QuantumChannel.id]
  | succ s ih =>
    let A := ChannelAmplification (copyChannelPower T s).map r X
    let B := ChannelAmplification (copyChannelPower S s).map r X
    have hA : A.PosSemidef := (copyChannelPower T s).completelyPositive r X hX
    have hB : B.PosSemidef := (copyChannelPower S s).completelyPositive r X hX
    have hBt : Matrix.trace B = Matrix.trace X :=
        amplification_trace _ (copyChannelPower S s).tracePreserving r X
    have hrecT : ChannelAmplification (copyChannelPower T (s+1)).map r X = ChannelAmplification T.map r A := by
      ext ⟨a,i⟩ ⟨b,j⟩; rfl
    have hrecS : ChannelAmplification (copyChannelPower S (s+1)).map r X = ChannelAmplification S.map r B := by
      ext ⟨a,i⟩ ⟨b,j⟩; rfl
    have he : ChannelAmplification T.map r A-ChannelAmplification S.map r B =
        ChannelAmplification T.map r (A-B)+(ChannelAmplification T.map r B-ChannelAmplification S.map r B) := by
      rw [amplification_sub]; abel
    rw [hrecT,hrecS,he]
    have hc := channel_reference_hermitian_trace_contraction T (hA.isHermitian.sub hB.isHermitian)
    have hl := hs r B hB
    rw [hBt] at hl
    have ht := (Matrix.traceNorm_add_le _ _).trans (add_le_add hc hl)
    exact (ht.trans (add_le_add ih le_rfl)).trans_eq (by push_cast; ring)

theorem numeric_relabel_trace {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : I ≃ J) (X : Matrix I I ℂ) : Matrix.trace (relabelGate e X) = Matrix.trace X := by
  unfold Matrix.trace
  exact e.symm.sum_comp (fun i => X i i)

theorem numeric_relabel_sub {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : I ≃ J) (X Y : Matrix I I ℂ) : relabelGate e (X-Y) = relabelGate e X-relabelGate e Y :=
  (Matrix.reindexAlgEquiv ℂ ℂ e).map_sub X Y

noncomputable def numericChannelQuery (D M : ℕ) (T : QuantumChannel (2*D) (2*D))
    (X : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ) :=
  relabelGate (copyQPERegisterEquiv D M).symm
    (ChannelAmplification T.map M (relabelGate (copyQPERegisterEquiv D M) X))

theorem numericChannelQuery_positive_trace (D M : ℕ) (T : QuantumChannel (2*D) (2*D))
    (X : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ) (hX : X.PosSemidef) :
    (numericChannelQuery D M T X).PosSemidef ∧ Matrix.trace (numericChannelQuery D M T X) = Matrix.trace X := by
  have hY := T.completelyPositive M _ (hX.submatrix (copyQPERegisterEquiv D M).symm)
  refine ⟨hY.submatrix (copyQPERegisterEquiv D M),?_⟩
  unfold numericChannelQuery
  rw [numeric_relabel_trace,amplification_trace T.map T.tracePreserving,numeric_relabel_trace]

theorem numericChannelQuery_contraction (D M : ℕ) (T : QuantumChannel (2*D) (2*D))
    (X : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ) (hX : X.IsHermitian) :
    (numericChannelQuery D M T X).traceNorm ≤ X.traceNorm := by
  have hY : (relabelGate (copyQPERegisterEquiv D M) X).IsHermitian :=
      hX.submatrix (copyQPERegisterEquiv D M).symm
  have hA := channel_reference_hermitian_preserving T hY
  unfold numericChannelQuery
  rw [traceNorm_relabel_hermitian _ _ hA]
  exact (channel_reference_hermitian_trace_contraction T hY).trans_eq
    (traceNorm_relabel_hermitian _ X hX)

theorem numericChannelQuery_sub (D M : ℕ) (T : QuantumChannel (2*D) (2*D))
    (X Y : Matrix (Fin M × (Bool × Fin D)) (Fin M × (Bool × Fin D)) ℂ) :
    numericChannelQuery D M T (X-Y) = numericChannelQuery D M T X-numericChannelQuery D M T Y := by
  unfold numericChannelQuery
  rw [numeric_relabel_sub,amplification_sub,numeric_relabel_sub]

theorem numericCopyQPEQuery_channel (n M b k : ℕ) (rho : Operator (2^n)) (hrho : IsDensityOperator rho)
    (X : Matrix (Fin M × (Bool × Fin (2^n))) (Fin M × (Bool × Fin (2^n))) ℂ) :
    numericCopyQPEQuery n M b k rho X = numericChannelQuery (2^n) M
      (copyChannelPower (controlledCopyChannel rho hrho (copyPhaseEffectiveAngle b k)) (2^b)) X := by
  unfold numericCopyQPEQuery numericChannelQuery
  rw [numericAmplification_run,copyChannelPower_map]
  rfl

theorem localCopyQPEQuery_channel (n M b : ℕ) (rho : Operator (2^n)) (hrho : IsDensityOperator rho)
    (X : Matrix (Fin M × (Bool × Fin (2^n))) (Fin M × (Bool × Fin (2^n))) ℂ) :
    localCopyQPEQuery n M (2^b) rho X = numericChannelQuery (2^n) M
      (copyChannelPower (controlledCopyChannel rho hrho (Real.pi/(2^b:ℕ))) (2^b)) X := by
  unfold localCopyQPEQuery numericChannelQuery
  rw [localCopyRunMap_eq,copyChannelPower_map]
  rfl

theorem numericCopyQPEQuery_error (n M b k : ℕ) (rho : Operator (2^n)) (hrho : IsDensityOperator rho)
    (X : Matrix (Fin M × (Bool × Fin (2^n))) (Fin M × (Bool × Fin (2^n))) ℂ) (hX : X.PosSemidef) :
    (numericCopyQPEQuery n M b k rho X-localCopyQPEQuery n M (2^b) rho X).traceNorm ≤
      4*(2^b:ℕ)*((2:ℝ)⁻¹)^k*(Matrix.trace X).re := by
  let T := copyChannelPower (controlledCopyChannel rho hrho (copyPhaseEffectiveAngle b k)) (2^b)
  let S := copyChannelPower (controlledCopyChannel rho hrho (Real.pi/(2^b:ℕ))) (2^b)
  let Y := relabelGate (copyQPERegisterEquiv (2^n) M) X
  have hy : Y.PosSemidef := hX.submatrix (copyQPERegisterEquiv (2^n) M).symm
  have hdiff : (ChannelAmplification T.map M Y-ChannelAmplification S.map M Y).IsHermitian :=
    (T.completelyPositive M Y hy).isHermitian.sub (S.completelyPositive M Y hy).isHermitian
  have he := numeric_channel_power_error
    (controlledCopyChannel rho hrho (copyPhaseEffectiveAngle b k))
    (controlledCopyChannel rho hrho (Real.pi/(2^b:ℕ))) (4*((2:ℝ)⁻¹)^k)
    (fun r Z hZ => numericCopy_reference_error n b k r rho hrho Z hZ) (2^b) M Y hy
  rw [numericCopyQPEQuery_channel n M b k rho hrho,localCopyQPEQuery_channel n M b rho hrho]
  unfold numericChannelQuery
  rw [← numeric_relabel_sub]
  change (relabelGate (copyQPERegisterEquiv (2^n) M).symm
    (ChannelAmplification T.map M Y-ChannelAmplification S.map M Y)).traceNorm ≤ _
  rw [traceNorm_relabel_hermitian _ _ hdiff]
  exact he.trans_eq (by rw [numeric_relabel_trace]; ring)

theorem numeric_conj_trace {I : Type} [Fintype I] [DecidableEq I]
    (U X : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) :
    Matrix.trace (MatrixMap.conj U X) = Matrix.trace X := by
  change Matrix.trace (U*X*Uᴴ) = Matrix.trace X
  rw [Matrix.trace_mul_cycle]
  have hu : Uᴴ*U = 1 := by simpa only [Matrix.star_eq_conjTranspose] using! hU.1
  rw [hu,Matrix.one_mul]

theorem numeric_conj_difference_norm {I : Type} [Fintype I] [DecidableEq I]
    (U A B : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) :
    (MatrixMap.conj U A-MatrixMap.conj U B).traceNorm = (A-B).traceNorm := by
  rw [← (MatrixMap.conj U).map_sub]
  have hh : Uᴴ*U = 1 := by simpa only [Matrix.star_eq_conjTranspose] using! hU.1
  letI : DecidableEq I := Classical.decEq I
  have hu : U.Isometry := by
    change Uᴴ*U = 1
    convert! hh using 1; first
      | exact Subsingleton.elim _ _
      | (ext i j; simp [Matrix.one_apply])
  change (U*(A-B)*Uᴴ).traceNorm = (A-B).traceNorm
  rw [Matrix.traceNorm_isometry_right hu,Matrix.traceNorm_isometry_left hu]

theorem numericCopyQPEProgram_error (n M b k : ℕ) (rho : Operator (2^n)) (hrho : IsDensityOperator rho)
    (C : Circuit (Fin M × (Bool × Fin (2^n)))) (hC : IsUnitaryCircuit C)
    (A B : Matrix (Fin M × (Bool × Fin (2^n))) (Fin M × (Bool × Fin (2^n))) ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (numericCopyQPEProgram n M b k rho C A-localCopyQPEProgram n M (2^b) rho C B).traceNorm ≤
      (A-B).traceNorm+(4*(2^b:ℕ)*((2:ℝ)⁻¹)^k)*(QueryCount C:ℝ)*(Matrix.trace B).re := by
  let T := copyChannelPower (controlledCopyChannel rho hrho (copyPhaseEffectiveAngle b k)) (2^b)
  let S := copyChannelPower (controlledCopyChannel rho hrho (Real.pi/(2^b:ℕ))) (2^b)
  induction C generalizing A B with
  | nil => simp [numericCopyQPEProgram,localCopyQPEProgram,QueryCount]
  | cons g C ih =>
    cases g with
    | gate U =>
      obtain ⟨hU,hC'⟩ := (isUnitaryCircuit_gate U C).mp hC
      have hi := ih hC' (MatrixMap.conj U A) (MatrixMap.conj U B)
        (hA.mul_mul_conjTranspose_same U) (hB.mul_mul_conjTranspose_same U)
      rw [numeric_conj_trace U B hU,numeric_conj_difference_norm U A B hU] at hi
      exact hi
    | query =>
      have hC' := (isUnitaryCircuit_query C).mp hC
      have hnum (X) := numericCopyQPEQuery_channel n M b k rho hrho X
      have hlocal (X) := localCopyQPEQuery_channel n M b rho hrho X
      have hA' : (numericCopyQPEQuery n M b k rho A).PosSemidef := by
        rw [hnum]; exact (numericChannelQuery_positive_trace (2^n) M T A hA).1
      have hB' : (localCopyQPEQuery n M (2^b) rho B).PosSemidef := by
        rw [hlocal]; exact (numericChannelQuery_positive_trace (2^n) M S B hB).1
      have hBt : Matrix.trace (localCopyQPEQuery n M (2^b) rho B) = Matrix.trace B := by
        rw [hlocal]; exact (numericChannelQuery_positive_trace (2^n) M S B hB).2
      have hi := ih hC' _ _ hA' hB'
      rw [hBt] at hi
      have hc : (numericCopyQPEQuery n M b k rho A-numericCopyQPEQuery n M b k rho B).traceNorm ≤
          (A-B).traceNorm := by
        rw [hnum,hnum,← numericChannelQuery_sub]
        exact numericChannelQuery_contraction (2^n) M T _ (hA.isHermitian.sub hB.isHermitian)
      have he : numericCopyQPEQuery n M b k rho A-localCopyQPEQuery n M (2^b) rho B =
          (numericCopyQPEQuery n M b k rho A-numericCopyQPEQuery n M b k rho B)+
          (numericCopyQPEQuery n M b k rho B-localCopyQPEQuery n M (2^b) rho B) := by abel
      have hl := numericCopyQPEQuery_error n M b k rho hrho B hB
      have ht := (Matrix.traceNorm_add_le _ _).trans (add_le_add hc hl)
      rw [← he] at ht
      exact (hi.trans (add_le_add ht le_rfl)).trans_eq
          (by simp only [QueryCount,Nat.cast_add,Nat.cast_one]; ring)

theorem numerical_copy_qpe_actual_program_error : ∀ (n M b k : ℕ) (rho : Operator (2^n)), 2 ≤ M → IsDensityOperator rho →
  Matrix.traceNorm (numericCopyQPEOutput n M b k rho-localCopyQPEOutput n M (2^b) rho) ≤
    4*(M-1)*(2^b:ℕ)*((2:ℝ)⁻¹)^k := by
  intro n M b k rho hM hrho
  have hs := counted_offgrid_qpe_clean_flag M (by omega) (1:Operator (2^n)) (0:QState (Fin (2^n)))
  have hin := copyQPEInput_density (2^n) M (by omega) rho hrho
  have h := numericCopyQPEProgram_error n M b k rho hrho (countedPhaseCircuit M) hs.2.2.2
    (copyQPEInput (2^n) M rho) (copyQPEInput (2^n) M rho) hin.1 hin.1
  rw [sub_self,Matrix.traceNorm_zero,hin.2,Complex.one_re,hs.2.1] at h
  simpa only [zero_add,mul_one,numericCopyQPEOutput,localCopyQPEOutput] using!
    h.trans_eq (by rw [Nat.cast_sub (by omega : 1 ≤ M),Nat.cast_one]; ring)

theorem numericCopyQPEQuery_positive_trace (n M b k : ℕ) (rho : Operator (2^n))
    (hrho : IsDensityOperator rho)
    (X : Matrix (Fin M × (Bool × Fin (2^n))) (Fin M × (Bool × Fin (2^n))) ℂ)
    (hX : X.PosSemidef) :
    (numericCopyQPEQuery n M b k rho X).PosSemidef ∧
      Matrix.trace (numericCopyQPEQuery n M b k rho X) = Matrix.trace X := by
  simpa only [numericCopyQPEQuery_channel n M b k rho hrho] using!
    numericChannelQuery_positive_trace (2^n) M
      (copyChannelPower (controlledCopyChannel rho hrho (copyPhaseEffectiveAngle b k)) (2^b)) X hX

theorem numericCopyQPEProgram_positive_trace (n M b k : ℕ) (rho : Operator (2^n))
    (hrho : IsDensityOperator rho) (C : Circuit (Fin M × (Bool × Fin (2^n))))
    (hC : IsUnitaryCircuit C)
    (X : Matrix (Fin M × (Bool × Fin (2^n))) (Fin M × (Bool × Fin (2^n))) ℂ)
    (hX : X.PosSemidef) :
    (numericCopyQPEProgram n M b k rho C X).PosSemidef ∧
      Matrix.trace (numericCopyQPEProgram n M b k rho C X) = Matrix.trace X := by
  induction C generalizing X with
  | nil => exact ⟨hX, rfl⟩
  | cons g C ih =>
    cases g with
    | query =>
      have hq := numericCopyQPEQuery_positive_trace n M b k rho hrho X hX
      have ht := ih (isUnitaryCircuit_query C |>.mp hC) _ hq.1
      exact ⟨ht.1, ht.2.trans hq.2⟩
    | gate U =>
      obtain ⟨hU, hC'⟩ := (isUnitaryCircuit_gate U C).mp hC
      have ht := ih hC' (MatrixMap.conj U X) (hX.mul_mul_conjTranspose_same U)
      exact ⟨ht.1, ht.2.trans (numeric_conj_trace U X hU)⟩

theorem numericCopyQPEOutput_density (n M b k : ℕ) (hM : 0 < M)
    (rho : Operator (2^n)) (hrho : IsDensityOperator rho) :
    (numericCopyQPEOutput n M b k rho).PosSemidef ∧
      Matrix.trace (numericCopyQPEOutput n M b k rho) = 1 := by
  have hC := (counted_offgrid_qpe_clean_flag M hM
    (1 : Operator (2^n)) (0 : QState (Fin (2^n)))).2.2.2
  have hX := copyQPEInput_density (2^n) M hM rho hrho
  have h := numericCopyQPEProgram_positive_trace n M b k rho hrho _ hC _ hX.1
  exact ⟨h.1, h.2.trans hX.2⟩

theorem numerical_copy_qpe_actual_label_law (n M b k : ℕ) (hM : 0 < M)
    (rho : Operator (2^n)) (hrho : IsDensityOperator rho) :
    (∀ z : Fin M, 0 ≤ copyQPELabelMass (2^n) M (numericCopyQPEOutput n M b k rho) z) ∧
      (∑ z, copyQPELabelMass (2^n) M (numericCopyQPEOutput n M b k rho) z) = 1 ∧
      (∀ E : Finset (Fin M),
        0 ≤ (∑ z ∈ E, copyQPELabelMass (2^n) M (numericCopyQPEOutput n M b k rho) z) ∧
          (∑ z ∈ E, copyQPELabelMass (2^n) M (numericCopyQPEOutput n M b k rho) z) ≤ 1) := by
  have hd := numericCopyQPEOutput_density n M b k hM rho hrho
  have hn (z : Fin M) :
      0 ≤ copyQPELabelMass (2^n) M (numericCopyQPEOutput n M b k rho) z :=
    copyQPELabelMass_nonneg (2^n) M _ hd.1 z
  have hs : (∑ z, copyQPELabelMass (2^n) M (numericCopyQPEOutput n M b k rho) z) = 1 := by
    rw [copyQPELabelMass_sum, hd.2, Complex.one_re]
  refine ⟨hn, hs, ?_⟩
  intro E
  refine ⟨Finset.sum_nonneg (fun z _ => hn z), ?_⟩
  calc
    _ ≤ ∑ z, copyQPELabelMass (2^n) M (numericCopyQPEOutput n M b k rho) z :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E) (fun z _ _ => hn z)
    _ = 1 := hs

theorem numerical_copy_qpe_actual_event_error (n M b k : ℕ) (rho : Operator (2^n))
    (E : Finset (Fin M)) (hM : 2 ≤ M) (hrho : IsDensityOperator rho) :
    |(∑ z ∈ E, copyQPELabelMass (2^n) M (numericCopyQPEOutput n M b k rho) z) -
      (∑ z ∈ E, copyQPELabelMass (2^n) M (localCopyQPEOutput n M (2^b) rho) z)| ≤
        2*(M-1)*(2^b:ℕ)*((2:ℝ)⁻¹)^k := by
  have hn := (numericCopyQPEOutput_density n M b k (by omega) rho hrho).2
  have hl : Matrix.trace (localCopyQPEOutput n M (2^b) rho) = 1 := by
    rw [localCopyQPEOutput_eq]
    exact (copyQPEOutput_density (2^n) M (2^b) (by omega) rho hrho).2
  have he := copyQPELabelMass_event_error_of_trace_eq (2^n) M E
    (numericCopyQPEOutput n M b k rho) (localCopyQPEOutput n M (2^b) rho) (hn.trans hl.symm)
  have hs := numerical_copy_qpe_actual_program_error n M b k rho hM hrho
  exact (he.trans (div_le_div_of_nonneg_right hs (by norm_num : (0:ℝ) ≤ 2))).trans_eq
    (by ring)

theorem numerical_copy_qpe_actual_spectral_error_refined : ∀ (n M b k : ℕ) (rho V : Operator (2^n)) (eig : Fin (2^n) → ℝ)
    (E : Finset (Fin M)), 2 ≤ M → IsDensityOperator rho →
  V ∈ Matrix.unitaryGroup (Fin (2^n)) ℂ →
  rho = V*Matrix.diagonal (fun i => (eig i:ℂ))*Vᴴ → (∀ i,0 ≤ eig i) →
  |(∑ z ∈ E,copyQPELabelMass (2^n) M (numericCopyQPEOutput n M b k rho) z)-
    (∑ i,eig i*(∑ z ∈ E,‖qpeKernel M (-eig i/2) z‖^2))| ≤
    8*(M-1)*Real.pi^2/(2^b:ℕ)+2*(M-1)*(2^b:ℕ)*((2:ℝ)⁻¹)^k
 := by
  intro n M b k rho V eig E hM hrho hV hd heig
  have hnum := numerical_copy_qpe_actual_event_error n M b k rho E hM hrho
  have hexact :=
      local_copy_qpe_actual_spectral_event_consumer n M (2^b) rho V eig E hM
      (by positivity) hrho hV hd heig
  have ht := (abs_sub_le
    (∑ z ∈ E,copyQPELabelMass (2^n) M (numericCopyQPEOutput n M b k rho) z)
    (∑ z ∈ E,copyQPELabelMass (2^n) M (localCopyQPEOutput n M (2^b) rho) z)
    (∑ i,eig i*(∑ z ∈ E,‖qpeKernel M (-eig i/2) z‖^2))).trans (add_le_add hnum hexact)
  exact ht.trans_eq (by rw [Nat.cast_sub (by omega : 1 ≤ M),Nat.cast_one]; ring)

theorem numerical_copy_qpe_actual_spectral_error : ∀ (n M b k : ℕ) (rho V : Operator (2^n)) (eig : Fin (2^n) → ℝ)
    (E : Finset (Fin M)), 2 ≤ M → IsDensityOperator rho →
  V ∈ Matrix.unitaryGroup (Fin (2^n)) ℂ →
  rho = V*Matrix.diagonal (fun i => (eig i:ℂ))*Vᴴ → (∀ i,0 ≤ eig i) →
  |(∑ z ∈ E,copyQPELabelMass (2^n) M (numericCopyQPEOutput n M b k rho) z)-
    (∑ i,eig i*(∑ z ∈ E,‖qpeKernel M (-eig i/2) z‖^2))| ≤
    8*(M-1)*Real.pi^2/(2^b:ℕ)+4*(M-1)*(2^b:ℕ)*((2:ℝ)⁻¹)^k
 := by
  intro n M b k rho V eig E hM hrho hV hd heig
  have h := numerical_copy_qpe_actual_spectral_error_refined n M b k rho V eig E hM hrho hV hd heig
  have hm : 0 ≤ (M:ℝ)-1 := by
    have hM' : (1:ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
    linarith
  have hn : 0 ≤ ((M:ℝ)-1)*(2^b:ℕ)*((2:ℝ)⁻¹)^k := by positivity
  exact h.trans (by nlinarith)

def numericCopyResources {I : Type*} (n b : ℕ) : Circuit I → ℕ × ℕ × ℕ × ℕ
  | [] => (0,0,0,0)
  | Step.gate _ :: C => numericCopyResources n b C
  | Step.query :: C =>
    let r := numericCopyResources n b C
    (r.1+(2^b)*(36*n+4),r.2.1+2^b,r.2.2.1+2^b,r.2.2.2)
def copyBudgetExponent (M p : ℕ) := Nat.clog 2 (max 1 (256*(M-1)*2^p))
def copyBudgetPhasePrecision (M b p : ℕ) := p+Nat.clog 2 (max 1 (8*(M-1)*2^b))

theorem numericCopyResources_eq {I : Type} (n b : ℕ) (C : Circuit I) :
    numericCopyResources n b C = (QueryCount C*(2^b)*(36*n+4),QueryCount C*(2^b),QueryCount C*(2^b),0) := by
  induction C with
  | nil => simp [numericCopyResources,QueryCount]
  | cons g C ih => cases g <;> simp [numericCopyResources,QueryCount,ih,Nat.add_mul]

theorem numericCopy_budget_error (M p : ℕ) (hM : 2 ≤ M) :
    let b := copyBudgetExponent M p
    let k := copyBudgetPhasePrecision M b p
    8*(M-1)*Real.pi^2/(2^b:ℕ)+4*(M-1)*(2^b:ℕ)*((2:ℝ)⁻¹)^k ≤ ((2:ℝ)⁻¹)^p := by
  (try dsimp only)
  let b := copyBudgetExponent M p
  let c := Nat.clog 2 (max 1 (8*(M-1)*2^b))
  have hs : 256*(M-1)*2^p ≤ 2^b :=
    (Nat.le_max_right _ _).trans (Nat.le_pow_clog (by decide) _)
  have hc : 8*(M-1)*2^b ≤ 2^c :=
    (Nat.le_max_right _ _).trans (Nat.le_pow_clog (by decide) _)
  have hsR : 256*((M:ℝ)-1)*(2:ℝ)^p ≤ (2:ℝ)^b := by
    have h := Nat.cast_le (α := ℝ).mpr hs
    simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_sub (by omega : 1 ≤ M),Nat.cast_one] using! h
  have hcR : 8*((M:ℝ)-1)*(2:ℝ)^b ≤ (2:ℝ)^c := by
    have h := Nat.cast_le (α := ℝ).mpr hc
    simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_sub (by omega : 1 ≤ M),Nat.cast_one] using! h
  have hmR : 0 ≤ (M:ℝ)-1 := by
    have hm : (1:ℝ) ≤ M := by exact_mod_cast (show (1:ℕ) ≤ M by omega)
    linarith
  have hp : (0:ℝ) < (2:ℝ)^p := by positivity
  have hb : (0:ℝ) < (2:ℝ)^b := by positivity
  have hcp : (0:ℝ) < (2:ℝ)^c := by positivity
  have hpi : Real.pi^2 ≤ 16 := by nlinarith [Real.pi_pos,Real.pi_lt_four]
  have hA : 8*((M:ℝ)-1)*Real.pi^2/(2:ℝ)^b ≤ 1/(2*(2:ℝ)^p) := by
    rw [div_le_div_iff₀ hb (by positivity)]
    have hh := mul_le_mul_of_nonneg_left hpi (show 0 ≤ 16*((M:ℝ)-1)*(2:ℝ)^p by positivity)
    nlinarith
  have hN : 4*((M:ℝ)-1)*(2:ℝ)^b*((2:ℝ)⁻¹)^(p+c) ≤ 1/(2*(2:ℝ)^p) := by
    rw [inv_pow,inv_eq_one_div,pow_add]
    rw [show 4*((M:ℝ)-1)*(2:ℝ)^b*(1/((2:ℝ)^p*(2:ℝ)^c)) =
      (4*((M:ℝ)-1)*(2:ℝ)^b)/((2:ℝ)^p*(2:ℝ)^c) by ring]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hh := mul_le_mul_of_nonneg_left hcR hp.le
    nlinarith
  change 8*((M:ℝ)-1)*Real.pi^2/(2^b:ℕ)+
    4*((M:ℝ)-1)*(2^b:ℕ)*((2:ℝ)⁻¹)^(p+c) ≤ ((2:ℝ)⁻¹)^p
  push_cast
  have he : 1/(2*(2:ℝ)^p)+1/(2*(2:ℝ)^p) = ((2:ℝ)⁻¹)^p := by
    rw [inv_pow,inv_eq_one_div]
    ring
  exact (add_le_add hA hN).trans_eq he

theorem numerical_copy_qpe_computed_budget_and_resources : ∀ (n M p : ℕ) (rho V : Operator (2^n)) (eig : Fin (2^n) → ℝ)
    (E : Finset (Fin M)), 2 ≤ M → IsDensityOperator rho →
  V ∈ Matrix.unitaryGroup (Fin (2^n)) ℂ →
  rho = V*Matrix.diagonal (fun i => (eig i:ℂ))*Vᴴ → (∀ i,0 ≤ eig i) →
  let b := copyBudgetExponent M p
  let k := copyBudgetPhasePrecision M b p
  |(∑ z ∈ E,copyQPELabelMass (2^n) M (numericCopyQPEOutput n M b k rho) z)-
    (∑ i,eig i*(∑ z ∈ E,‖qpeKernel M (-eig i/2) z‖^2))| ≤ ((2:ℝ)⁻¹)^p ∧
  numericCopyResources n b (countedPhaseCircuit (I := Fin (2^n)) M) =
    ((M-1)*(2^b)*(36*n+4),(M-1)*(2^b),(M-1)*(2^b),0) ∧
  copyQPEFixedMacros (2^n) M = 2*(M-1)+2
 := by
  intro n M p rho V eig E hM hrho hV hd heig
  (try dsimp only)
  refine ⟨(numerical_copy_qpe_actual_spectral_error n M _ _ rho V eig E hM hrho hV hd heig).trans
    (numericCopy_budget_error M p hM),?_,copyQPEFixedMacros_eq (2^n) M (by omega)⟩
  have hs := counted_offgrid_qpe_clean_flag M (by omega) (1:Operator (2^n)) (0:QState (Fin (2^n)))
  rw [numericCopyResources_eq,hs.2.1]

end Qatlib.Concepts.FreshCopyExec.QpeConsumers
