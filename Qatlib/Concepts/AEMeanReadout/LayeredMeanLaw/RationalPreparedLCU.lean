/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Rat.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Qatlib.Concepts.AEMeanReadout.LayeredMeanLaw.RationalWeightPreparation
import Qatlib.Concepts.BlockEncoding.EncodingCore.AncillaErrorLaws

/-!
# Rationally prepared linear combinations of unitaries

This module constructs `rationalWeightLCUWord` from rational weight preparation and a SELECT
operation. It proves unitarity, exact query and gate counts, and an operator norm bound for the
normalized weighted sum, using the preparation and compression framework for linear combinations
of unitaries described in [GilyenSuLowWiebe2019].

## Main statements

* `rational_weight_actual_lcu_error_and_accesses`: gives one SELECT query, `2*n` fixed gates,
  and error at most `64*n/2^k`.
* `rational_weight_quarter_three_quarter_lcu_consumer`: specializes to the combination of the
  identity and Pauli X with weights one quarter and three quarters.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.AEMeanReadout.LayeredMeanLaw
open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open scoped Classical BigOperators Matrix.Norms.L2Operator
set_option autoImplicit false
set_option maxHeartbeats 2000000
/-- Matrix multiplication with the finite intermediate index made explicit. -/
private noncomputable def weightMatrixMul {M N P : Type} [Fintype N]
    (A : Matrix M N ℂ) (B : Matrix N P ℂ) : Matrix M P ℂ :=
  @HMul.hMul _ _ _ Matrix.instHMulOfFintypeOfMulOfAddCommMonoid A B
local infixl:70 " *ₘ " => weightMatrixMul

/-- The preparation, SELECT, and inverse-preparation circuit word for rational weights, written
in the evaluation convention of `AdjointStep`. -/
noncomputable def rationalWeightLCUWord {n : ℕ} (I : Type) [Fintype I] [DecidableEq I]
    (w : Option (Fin n) → ℚ) (k : ℕ) :=
  adjointCircuit (rationalWeightLiftWord I w k) ++ [.forward] ++ rationalWeightLiftWord I w k

/-- Evaluating a reversed list of gates tensored with the identity equals the tensor lift of
their evaluation. -/
theorem weight_lift_evaluate {n : ℕ} (I : Type) [Fintype I] [DecidableEq I]
    (g : Fin n → Matrix (Option (Fin n)) (Option (Fin n)) ℂ) (l : List (Fin n))
    (O : Matrix (Option (Fin n) × I) (Option (Fin n) × I) ℂ) :
    evaluate O ((l.map (fun j => AdjointStep.gate (TensorGate (g j) (1 : Matrix I I ℂ)))).reverse) =
    TensorGate (evaluate 1 ((l.map (fun j => AdjointStep.gate (g j))).reverse)) (1 : Matrix I I ℂ) := by
  induction l with
  | nil => simp [evaluate, tensorGate_one]
  | cons j l ih =>
    simp only [List.map_cons, List.reverse_cons, evaluate_append, evaluate,
      instructionMatrix, Matrix.mul_one, ih]
    rw [tensorGate_mul, Matrix.one_mul]

/-- Applying `P` to the preparation register of `prepareLift a` gives `prepareLift (P *ᵥ a)`. -/
theorem weight_tensor_prepareLift {J I : Type} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] (P : Matrix J J ℂ) (a : QState J) :
    TensorGate P (1 : Matrix I I ℂ) *ₘ prepareLift a = prepareLift (P *ᵥ a) := by
  unfold weightMatrixMul
  ext ⟨j,i⟩ k
  by_cases hik : i = k
  · subst k
    simp [Matrix.mul_apply, TensorGate, prepareLift, Fintype.sum_prod_type,
      Matrix.mulVec, dotProduct]
  · simp [Matrix.mul_apply, TensorGate, prepareLift, Fintype.sum_prod_type, hik]

/-- For nonnegative rational weights of positive total mass, the target preparation yields the
normalized weighted sum of the matrices `U a`. -/
theorem weight_target_lcu {n : ℕ} (I : Type) [Fintype I] [DecidableEq I]
    (w : Option (Fin n) → ℚ) (hw : ∀ a, 0 ≤ w a)
    (hZ : 0 < rationalWeightMass w) (U : Option (Fin n) → Matrix I I ℂ) :
    lcuMatrix (rationalWeightTarget w) U =
      ∑ a, (((w a/rationalWeightMass w : ℚ) : ℂ)) • U a := by
  unfold lcuMatrix
  apply Finset.sum_congr rfl
  intro a _
  have hq : (0 : ℝ) ≤ ((w a/rationalWeightMass w : ℚ) : ℝ) := by
    exact_mod_cast div_nonneg (hw a) hZ.le
  have hs := Real.sq_sqrt hq
  have he : star (rationalWeightTarget w a)*rationalWeightTarget w a =
      ((w a/rationalWeightMass w : ℚ) : ℂ) := by
    simp only [rationalWeightTarget, Complex.star_def, Complex.conj_ofReal,
      ← pow_two]
    exact_mod_cast hs
  rw [he]

/-- Conjugating a unitary `T` by unitaries `P` and `Q` changes it by at most `2*‖P-Q‖` in
operator norm. -/
theorem weight_sandwich_error {H : Type} [Fintype H] [DecidableEq H]
    (P Q T : Matrix H H ℂ) (hP : P ∈ Matrix.unitaryGroup H ℂ)
    (hQ : Q ∈ Matrix.unitaryGroup H ℂ) (hT : T ∈ Matrix.unitaryGroup H ℂ) :
    ‖Pᴴ*T*P-Qᴴ*T*Q‖ ≤ 2*‖P-Q‖ := by
  have hnP := l2_norm_unitary_le_one hP
  have hnQ := l2_norm_unitary_le_one hQ
  have hnT := l2_norm_unitary_le_one hT
  have hleft : ‖Pᴴ*T-Qᴴ*T‖ ≤ ‖P-Q‖ := by
    rw [← Matrix.sub_mul, ← Matrix.conjTranspose_sub]
    calc
      _ ≤ ‖(P-Q)ᴴ‖*‖T‖ := norm_mul_le _ _
      _ ≤ ‖P-Q‖ := by rw [Matrix.l2_opNorm_conjTranspose]; nlinarith [norm_nonneg (P-Q)]
  have hright : ‖Qᴴ*T‖ ≤ 1 := l2_norm_unitary_le_one
    ((Matrix.unitaryGroup H ℂ).mul_mem (adjoint_unitary hQ) hT)
  apply (l2_norm_mul_sub_mul_le _ _ _ _).trans
  calc
    _ ≤ ‖P-Q‖*1+1*‖P-Q‖ := add_le_add
      (mul_le_mul hleft hnP (norm_nonneg _) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right hright (norm_nonneg _))
    _ = _ := by ring

/-- Compression by the same isometry on both sides does not increase the operator norm of a
matrix difference. -/
theorem weight_compress_error {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (F : Matrix H I ℂ) (hF : IsIsometry F)
    (A B : Matrix H H ℂ) : ‖compress F A F-compress F B F‖ ≤ ‖A-B‖ := by
  have hFn := isometry_norm_le hF
  have hFt : ‖Fᴴ‖ ≤ 1 := by rw [Matrix.l2_opNorm_conjTranspose]; exact hFn
  have he : compress F A F-compress F B F = Fᴴ*(A-B)*F := by
    simp only [compress, Matrix.mul_sub, Matrix.sub_mul]
  rw [he]
  calc
    _ ≤ ‖Fᴴ*(A-B)‖*‖F‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖Fᴴ‖*‖A-B‖)*‖F‖ := mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ ≤ (1*‖A-B‖)*1 := mul_le_mul
      (mul_le_mul_of_nonneg_right hFt (norm_nonneg _)) hFn (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- A reversed list of fixed gates has no oracle queries and has gate count equal to the list
length. -/
theorem weight_lift_counts {H J : Type} (g : J → Matrix H H ℂ) (l : List J) :
    adjointQueryCount ((l.map (fun j => AdjointStep.gate (g j))).reverse) = 0 ∧
    adjointGateCount ((l.map (fun j => AdjointStep.gate (g j))).reverse) = l.length := by
  induction l with
  | nil => simp [adjointQueryCount, adjointGateCount]
  | cons j l ih =>
    simp [List.reverse_cons, adjointQueryCount_append, adjointGateCount_append,
      adjointQueryCount, adjointGateCount, ih]

/-- The tensor-lifted rational weight preparation word is a well-formed adjoint circuit. -/
theorem rationalWeightLiftWord_wellFormed {n : ℕ} (I : Type) [Fintype I] [DecidableEq I]
    (w : Option (Fin n) → ℚ) (k : ℕ) :
    WellFormedAdjointCircuit (rationalWeightLiftWord I w k) := by
  intro V hV
  simp only [rationalWeightLiftWord, List.mem_reverse, List.mem_ofFn] at hV
  obtain ⟨j, hj⟩ := hV
  cases hj
  exact tensorGate_unitary (rationalWeightGate_unitary w k j) (by simp)

/-- For nonnegative rational weights of positive mass and unitary summands, the LCU word is well
formed and unitary, with one query and `2*n` fixed gates. Its compression equals the LCU of
the prepared state and approximates the normalized weighted sum within `64*n/2^k`. -/
theorem rational_weight_actual_lcu_error_and_accesses : ∀ (n k : ℕ)
    (I : Type) [Fintype I] [DecidableEq I]
    (w : Option (Fin n) → ℚ) (U : Option (Fin n) → Matrix I I ℂ),
    (∀ a, 0 ≤ w a) → 0 < rationalWeightMass w →
    (∀ a, U a ∈ Matrix.unitaryGroup I ℂ) →
    let W := rationalWeightLCUWord I w k;
    let A := evaluate (select U) W;
    let F := prepareLift (I := I) (Ket (none : Option (Fin n)));
    WellFormedAdjointCircuit W ∧
    A ∈ Matrix.unitaryGroup (Option (Fin n) × I) ℂ ∧
    adjointQueryCount W = 1 ∧ adjointGateCount W = 2*n ∧
    compress F A F = lcuMatrix (rationalWeightPrepare w k *ᵥ Ket none) U ∧
    ‖compress F A F - ∑ a, (((w a / rationalWeightMass w : ℚ) : ℂ)) • U a‖ ≤ 64*(n : ℝ)/2^k := by
  intro n k I _ _ w U hw hZ hU
  (try dsimp only)
  let P := TensorGate (rationalWeightPrepare w k) (1 : Matrix I I ℂ)
  let Q := TensorGate (idealWeightPrepare w) (1 : Matrix I I ℂ)
  let T := select U
  let F := prepareLift (I := I) (Ket (none : Option (Fin n)))
  have hlift : evaluate T (rationalWeightLiftWord I w k) = P := by
    have h := weight_lift_evaluate I (rationalWeightGate w k)
      (List.ofFn (fun j : Fin n => j)) T
    simpa only [List.map_ofFn, Function.comp_def, rationalWeightLiftWord,
      P, rationalWeightPrepare, rationalWeightWord] using h
  have hword : evaluate T (rationalWeightLCUWord I w k) = Pᴴ*T*P := by
    rw [rationalWeightLCUWord, evaluate_append, evaluate_append, evaluate_adjointCircuit,
      hlift]
    simp [evaluate, instructionMatrix, Matrix.mul_assoc]
  have hwf := rationalWeightLiftWord_wellFormed I w k
  have hwfW : WellFormedAdjointCircuit (rationalWeightLCUWord I w k) := by
    exact (hwf.adjointCircuit.append (by simp [WellFormedAdjointCircuit])).append hwf
  have hc := weight_lift_counts
    (fun j => TensorGate (rationalWeightGate w k j) (1 : Matrix I I ℂ))
    (List.ofFn (fun j : Fin n => j))
  simp only [List.map_ofFn, Function.comp_def, List.length_ofFn] at hc
  change adjointQueryCount (rationalWeightLiftWord I w k) = 0 ∧
    adjointGateCount (rationalWeightLiftWord I w k) = n at hc
  obtain ⟨_, hprep, herr⟩ := rational_weight_numerical_word_unitary_and_error n k w hw
  obtain ⟨hideal, hexact, _⟩ := rational_weight_ideal_preparation_exact n w hw hZ
  have hP : P ∈ Matrix.unitaryGroup _ ℂ := tensorGate_unitary hprep (by simp)
  have hQ : Q ∈ Matrix.unitaryGroup _ ℂ := tensorGate_unitary hideal (by simp)
  have hT : T ∈ Matrix.unitaryGroup _ ℂ := select_unitary U hU
  have hF : IsIsometry F := prepareLift_isIsometry _ (by
    simp [Ket, Fintype.sum_option])
  have hsand (R : Matrix (Option (Fin n)) (Option (Fin n)) ℂ) :
      compress F ((TensorGate R (1 : Matrix I I ℂ))ᴴ*T*TensorGate R 1) F =
      lcuMatrix (R *ᵥ Ket none) U := by
    rw [show compress F ((TensorGate R (1 : Matrix I I ℂ))ᴴ*T*TensorGate R 1) F =
      compress (TensorGate R 1 *ₘ F) T (TensorGate R 1 *ₘ F) by
        simp [compress, weightMatrixMul, Matrix.conjTranspose_mul, Matrix.mul_assoc]]
    rw [weight_tensor_prepareLift, prepare_select_compress]
  have hPQ : ‖P-Q‖ ≤ 32*(n : ℝ)/2^k := by
    dsimp only [P, Q]
    rw [tensorGate_sub_left, l2_norm_tensorGate]
    exact (mul_le_mul_of_nonneg_left (l2_norm_one_le (I := I)) (norm_nonneg _)).trans
        (by simpa using herr)
  refine ⟨hwfW, hwfW.evaluate_unitary hT, ?_, ?_, ?_, ?_⟩
  · simp [rationalWeightLCUWord, adjointQueryCount_append, adjointQueryCount_adjointCircuit,
      adjointQueryCount, hc.1]
  · simp [rationalWeightLCUWord, adjointGateCount_append, adjointGateCount_adjointCircuit,
      adjointGateCount, hc.2, two_mul]
  · rw [hword]; exact hsand _
  · rw [hword, ← weight_target_lcu I w hw hZ U, ← hexact, ← hsand (idealWeightPrepare w)]
    exact (weight_compress_error F hF _ _).trans
      ((weight_sandwich_error P Q T hP hQ hT).trans
        ((mul_le_mul_of_nonneg_left hPQ (by norm_num)).trans_eq (by ring)))

/-- The probability of returning to preparation label `j` equals the total squared norm after
compression to that label. -/
theorem weight_pivot_probability {J I : Type} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] (A : Matrix (J×I) (J×I) ℂ) (j : J) (x : I) :
    MeasureProb (A *ᵥ Ket (j,x)) (Finset.univ.filter (fun p : J×I => p.1=j)) =
    MeasureProb (compress (prepareLift (I := I) (Ket j)) A (prepareLift (I := I) (Ket j)) *ᵥ Ket x) Finset.univ := by
  have hentry (i y : I) : compress (prepareLift (I := I) (Ket j)) A
      (prepareLift (I := I) (Ket j)) i y = A (j,i) (j,y) := by
    simp [compress, Matrix.mul_apply, Matrix.conjTranspose_apply, prepareLift,
      Ket, Fintype.sum_prod_type, mul_ite, ite_mul, apply_ite]
  simp only [MeasureProb, BornProb, Finset.sum_filter, Matrix.mulVec_single, Ket]
  rw [Fintype.sum_prod_type]
  simp [hentry, Matrix.mulVec, dotProduct, Ket, mul_ite]

/-- The rational LCU for weights one and three approximates `(1/4) • 1 + (3/4) • PauliX` within
`64/2^k`. On the specified input, the return probability differs from `5/8` by at most
`128/2^k`. -/
theorem rational_weight_quarter_three_quarter_lcu_consumer : ∀ (k : ℕ),
    let w : Option (Fin 1) → ℚ := fun a => if a=none then 1 else 3;
    let U : Option (Fin 1) → Matrix Bool Bool ℂ := fun a => if a=none then 1 else PauliX;
    let A := evaluate (select U) (rationalWeightLCUWord Bool w k);
    let F := prepareLift (I := Bool) (Ket (none : Option (Fin 1)));
    |MeasureProb (A *ᵥ Ket (none,false))
      (Finset.univ.filter (fun a : Option (Fin 1)×Bool => a.1=none))-5/8| ≤ 128/(2 : ℝ)^k ∧
    ‖compress F A F-((1/4 : ℂ) • (1 : Matrix Bool Bool ℂ)+(3/4 : ℂ) • PauliX)‖ ≤ 64/(2 : ℝ)^k := by
  intro k
  (try dsimp only)
  let w : Option (Fin 1) → ℚ := fun a => if a=none then 1 else 3
  let U : Option (Fin 1) → Matrix Bool Bool ℂ := fun a => if a=none then 1 else PauliX
  let A := evaluate (select U) (rationalWeightLCUWord Bool w k)
  let F := prepareLift (I := Bool) (Ket (none : Option (Fin 1)))
  let C : Matrix Bool Bool ℂ := (1/4 : ℂ) • 1+(3/4 : ℂ) • PauliX
  have hw : ∀ a, 0 ≤ w a := by intro a; dsimp [w]; split_ifs <;> norm_num
  have hZ : rationalWeightMass w = 4 := by
    simp [rationalWeightMass, Fintype.sum_option, w]
    norm_num
  have hU : ∀ a, U a ∈ Matrix.unitaryGroup Bool ℂ := by
    intro a; dsimp [U]; split_ifs; simp; exact pauliX_unitary
  obtain ⟨_, hA, _, _, _, he⟩ := rational_weight_actual_lcu_error_and_accesses
    1 k Bool w U hw (by rw [hZ]; norm_num) hU
  have htarget : (∑ a, (((w a/rationalWeightMass w : ℚ) : ℂ)) • U a) = C := by
    simp [Fintype.sum_option, w, U, hZ, C]
  rw [htarget] at he
  norm_num only [Nat.cast_one, mul_one] at he
  have hF : IsIsometry F := prepareLift_isIsometry _ (by simp [Ket])
  have hD : ‖compress F A F‖ ≤ 1 := l2_norm_compress_le_one hF hA hF
  have hC : ‖C‖ ≤ 1 := by
    calc
      _ ≤ ‖(1/4 : ℂ) • (1 : Matrix Bool Bool ℂ)‖+‖(3/4 : ℂ) • PauliX‖ := norm_add_le _ _
      _ ≤ 1 := by rw [norm_smul, norm_smul]; norm_num [l2_norm_one_eq, CStarRing.norm_of_mem_unitary pauliX_unitary]
  have hp := measureProb_sub_le_l2 (compress F A F *ᵥ Ket false) (C *ᵥ Ket false) Finset.univ
  have hv := l2_norm_mulVec_fromVec_le (compress F A F-C) (Ket false)
  have hn : ‖toEuclidean_fromVec (Ket false)‖ = 1 :=
    (normalized_iff_norm_toEuclidean_fromVec _).mp (normalized_ket false)
  rw [hn, mul_one] at hv
  have hdv := l2_norm_mulVec_fromVec_le (compress F A F) (Ket false)
  have hcv := l2_norm_mulVec_fromVec_le C (Ket false)
  rw [hn, mul_one] at hdv hcv
  rw [← Matrix.sub_mulVec] at hp
  have hprob : MeasureProb (C *ᵥ Ket false) Finset.univ = 5/8 := by
    norm_num [C, MeasureProb, BornProb, Matrix.mulVec, dotProduct,
      PauliX, permMatrix, Ket, Fintype.sum_bool, Complex.norm_def]
  refine ⟨?_, he⟩
  rw [weight_pivot_probability A none false]
  rw [← hprob]
  exact hp.trans ((mul_le_mul
    (show ‖toEuclidean_fromVec (compress F A F *ᵥ Ket false)‖+
      ‖toEuclidean_fromVec (C *ᵥ Ket false)‖ ≤ 2 by linarith)
    (hv.trans he) (norm_nonneg _) (by norm_num)).trans_eq (by ring))

end Qatlib.Concepts.AEMeanReadout.LayeredMeanLaw
